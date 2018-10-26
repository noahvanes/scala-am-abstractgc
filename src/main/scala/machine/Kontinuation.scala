import scalaz.Scalaz._
import Util.MapStrict

trait Frame {
  def subsumes(that: Frame): Boolean = {
    this.equals(that)
  }
  def references[Addr : Address] = refs.asInstanceOf[Set[Addr]]
  val refs: Set[_]
}

trait KontAddress[A]

case class Kont[KontAddr: KontAddress](frame: Frame, next: KontAddr) {
  def subsumes(that: Kont[KontAddr]) = that match {
    case Kont(frame2, next2) => frame.subsumes(frame2) && next.equals(next2)
    case _ => false
  }
  lazy val storedHash = (frame,next).hashCode()
  override def hashCode = storedHash
}

object Kont {
  implicit object KontGraphNode extends GraphNode[(_,Set[Kont[_]]),Unit] {
    override def label(node: Tuple2[_, Set[Kont[_]]]): String = s"${node._1} -> ${node._2}"
  }
}

abstract class KontStore[KontAddr : KontAddress] {
  def keys: Iterable[KontAddr]
  def lookup(a: KontAddr): Set[Kont[KontAddr]]
  def extend(a: KontAddr, kont: Kont[KontAddr]): KontStore[KontAddr]
  def join(that: KontStore[KontAddr]): KontStore[KontAddr]
  def forall(p: ((KontAddr, Set[Kont[KontAddr]])) => Boolean): Boolean
  def subsumes(that: KontStore[KontAddr]): Boolean
  def fastEq(that: KontStore[KontAddr]): Boolean = this == that
}

case class BasicKontStore[KontAddr : KontAddress](content: Map[KontAddr, Set[Kont[KontAddr]]]) extends KontStore[KontAddr] {
  def keys = content.keys
  def lookup(a: KontAddr) = content.getOrElse(a, Set())
  override def toString = content.toString
  def extend(a: KontAddr, kont: Kont[KontAddr]) = /* Profiler.logRes(s"$this.extend($a, $kont)") */{
    this.copy(content = content + (a -> (lookup(a) + kont)))
  } /* { x => x.toString } */
  def join(that: KontStore[KontAddr]) = /* Profiler.logRes(s"$this.join($that)") */ {
    if (that.isInstanceOf[BasicKontStore[KontAddr]]) {
      this.copy(content = content |+| that.asInstanceOf[BasicKontStore[KontAddr]].content)
    } else {
      throw new Exception(s"Incompatible continuation stores: ${this.getClass.getSimpleName} and ${that.getClass.getSimpleName}")
    }
  } /* { x => x.toString } */
  def forall(p: ((KontAddr, Set[Kont[KontAddr]])) => Boolean) = content.forall(p)
  def subsumes(that: KontStore[KontAddr]) =
    that.forall({ case (a, ks) =>
      ks.forall((k1) => lookup(a).exists(k2 => k2.subsumes(k1)))
    })
}

case class GCKontStore[Addr : Address, KontAddr : KontAddress](content: Map[KontAddr, Set[Kont[KontAddr]]] = Map[KontAddr, Set[Kont[KontAddr]]](),
                                                               refs: Map[KontAddr,Set[KontAddr]] = Map[KontAddr,Set[KontAddr]]().withDefaultValue(Set()),
                                                               vrefs: Map[KontAddr,Set[Addr]] = Map[KontAddr,Set[Addr]]().withDefaultValue(Set())) extends KontStore[KontAddr] {

  def mark(adr: KontAddr, marked: Set[KontAddr], addrs: Set[Addr]): (Set[KontAddr],Set[Addr]) =
    refs(adr).foldLeft(marked+adr, addrs++vrefs(adr))((acc,ref) => {
      if (acc._1.contains(ref)) { acc } else { mark(ref,acc._1,acc._2) }
    })

  def collect(root: KontAddr): (GCKontStore[Addr,KontAddr],Set[Addr]) = {
    val (marked,addrs) = mark(root,Set(),Set())
    val updatedContent = content.filterKeysStrict(marked)
    val updatedRefs = refs.filterKeysStrict(marked).withDefaultValue(Set())
    val updatedVRefs = vrefs.filterKeysStrict(marked).withDefaultValue(Set())
    (GCKontStore(updatedContent, updatedRefs, updatedVRefs), addrs)
  }

  def keys = content.keys
  def lookup(adr: KontAddr) = content(adr)
  def forall(p: ((KontAddr, Set[Kont[KontAddr]])) => Boolean) = content.forall(p)

  def extend(adr: KontAddr, kont: Kont[KontAddr]): GCKontStore[Addr,KontAddr] = {
    val adrRefs = refs(adr)
    val adrVRefs = vrefs(adr)
    val adrCnts = content.get(adr).getOrElse(Set())
    this.copy(content = content + (adr -> (adrCnts + kont)),
              refs = refs + (adr -> (adrRefs + kont.next)),
              vrefs = vrefs + (adr -> (adrVRefs ++ kont.frame.references)))
  }

  /* TODO */

  def join(that: KontStore[KontAddr]) = throw new Exception("NYI: GCKontStore.join(KontStore[KontAddr])")
  def subsumes(that: KontStore[KontAddr]) = throw new Exception("NYI: GCKontStore.subsumes(KontStore[KontAddr])")

  /* PERFORMANCE OPTIMIZATION */

  override def equals(that: Any): Boolean = that match {
    case kstore : GCKontStore[Addr,KontAddr] => this.content == kstore.content
    case _ => false
  }

  lazy val storedHashCode = content.hashCode
  override def hashCode = storedHashCode
}


case class RefCountingKontStore[Addr : Address, KontAddr : KontAddress]
  (content: Map[KontAddr, (Set[Kont[KontAddr]],Set[KontAddr],Set[Addr])] = Map[KontAddr, (Set[Kont[KontAddr]],Set[KontAddr],Set[Addr])](),
   counts: Map[KontAddr,Int] = Map[KontAddr,Int]().withDefaultValue(0),
   hc: Int = 0) extends KontStore[KontAddr] {

  private def decRefUpdate(adr: KontAddr, counts: Map[KontAddr,Int], deleted: List[KontAddr], decremented: Set[KontAddr], addrs: List[Addr]):  (Map[KontAddr,Int], List[KontAddr], Set[KontAddr], List[Addr]) = {
    val newCount = counts(adr) - 1
    if (newCount == 0) {
      content.get(adr) match {
        case None =>
          (counts, deleted, decremented, addrs)
        case Some((_,kaddrs,vrefs)) =>
          kaddrs.foldLeft((counts, adr::deleted, decremented, addrs++vrefs))((acc,ref) => decRefUpdate(ref,acc._1,acc._2,acc._3,acc._4))
      }
    } else {
      (counts + (adr -> newCount), deleted, decremented + adr, addrs)
    }
  }

  private def decRef(adr: KontAddr): (RefCountingKontStore[Addr,KontAddr],List[Addr],Set[KontAddr]) = {
    val (updatedCounts,deleted,decremented,addrs) = decRefUpdate(adr,counts,List(),Set(),List())
    val updatedHC = deleted.foldLeft(hc)((acc,ref) => {
      val konts = content.get(ref).map(_._1).getOrElse(Iterable.empty)
      konts.foldLeft(acc)((acc2,cnt) => acc2 - cnt.hashCode())
    })
    (RefCountingKontStore(content--deleted, updatedCounts--deleted, updatedHC), addrs, decremented--deleted)
  }

  private def incRef(adr: KontAddr): RefCountingKontStore[Addr,KontAddr] =
    this.copy(counts = counts + (adr -> (counts(adr) + 1)))

  def changeRoot(oldR: KontAddr, newR: KontAddr): (RefCountingKontStore[Addr,KontAddr],Iterable[Addr]) = if (oldR == newR) { (this, Iterable.empty) } else {
    val (kstore,addrs,decremented) = incRef(newR).decRef(oldR)
    val potentialGCR = decremented - newR
    (kstore,addrs)
  }

  def keys = content.keys
  def lookup(adr: KontAddr) = content(adr)._1
  def forall(p: ((KontAddr, Set[Kont[KontAddr]])) => Boolean) = content.forall(n => p(n._1,n._2._1))

  def extend(adr: KontAddr, kont: Kont[KontAddr]) = extendRC(adr,kont)._1
  def extendRC(adr: KontAddr, kont: Kont[KontAddr]): (RefCountingKontStore[Addr,KontAddr],Iterable[Addr]) = content.get(adr) match {
    case None =>
      val kontRefs = kont.frame.references
      val updatedContent = content + (adr->(Set(kont),Set(kont.next)-adr,kontRefs))
      val updatedCounts  = counts  + (kont.next -> (counts(kont.next) + 1))
      val updatedHC      = hc      + kont.hashCode()
      (RefCountingKontStore(updatedContent, updatedCounts, updatedHC), kontRefs)
    case Some((konts,_,_)) if konts.contains(kont) =>
      (this, Iterable.empty)
    case Some((konts,kaddrs,addrs)) =>
      val updatedHC = hc + kont.hashCode()
      val (updatedCounts,updatedKaddrs) = if (kont.next == adr || kaddrs.contains(kont.next)) { (counts, kaddrs) } else { (counts+(kont.next->(counts(kont.next)+1)), kaddrs+kont.next) }
      val (addedAddrs,updatedAddrs) = kont.frame.references.foldLeft((List[Addr](), addrs))((acc,ref) =>  if (addrs.contains(ref)) { acc } else (ref::acc._1,acc._2+ref))
      (RefCountingKontStore(content+(adr->(konts+kont,updatedKaddrs,updatedAddrs)),updatedCounts,updatedHC), addedAddrs)
  }

  /* TODO */

  def join(that: KontStore[KontAddr]) = throw new Exception("NYI: RefCountingKontStore.join(KontStore[Addr,KontAddr])")
  def subsumes(that: KontStore[KontAddr]) = throw new Exception("NYI: RefCountingKontStore.subsumes(KontStore[Addr,KontAddr])")

  /* PERFORMANCE OPTIMIZATION */

  override def equals(that: Any): Boolean = that match {
    case kstore : RefCountingKontStore[Addr,KontAddr] => this.hc == kstore.hc && this.content == kstore.content
    case _ => false
  }

  override def hashCode = hc

  /* DEBUGGING */

  def toFile(path: String, root: KontAddr) = {
    val kstore = this
    implicit val kontNode = new GraphNode[KontAddr,Unit] {
      override def label(adr: KontAddr): String = s"${adr}"
      override def tooltip(adr: KontAddr): String = s"${kstore.counts(adr)}"
      override def color(adr: KontAddr): Color = if (adr == root) Colors.Green else adr match {
        case _ : AAMRefCounting[_,_,_,_]#CallAddress => Colors.Yellow
        case _ => Colors.White
      }
    }
    val initG = Graph.empty[KontAddr,Unit,Unit]
    val fullG = content.keys.foldLeft(initG)((acc,adr) => acc.addEdges(content(adr)._2.map(succ => (adr,(),succ))))
    GraphDOTOutput.toFile(fullG,())(path)
  }

  def toPng(path: String, root: KontAddr): Unit = {
    import sys.process._
    import java.io.File
    val tempFile = "temp.dot"
    toFile(tempFile, root)
    s"dot -Tpng ${tempFile} -o ${path}".!
    new File(tempFile).delete()
  }

  def containsIsolatedCycle(root: KontAddr): Boolean = {
    var marked = Set[KontAddr]()
    var todo = List[KontAddr](root)
    while (!todo.isEmpty) {
      val next = todo.head
      todo = todo.tail
      if(!marked.contains(next)) {
        marked += next
        content.get(next).map(d => todo ++= d._2)
      }
    }
    return (content--marked).size > 0
  }
}

case class TimestampedKontStore[KontAddr : KontAddress](content: Map[KontAddr, Set[Kont[KontAddr]]], timestamp: Int) extends KontStore[KontAddr] {
  def keys = content.keys
  def lookup(a: KontAddr) = content.getOrElse(a,Set())
  override def toString = content.toString
  def extend(a: KontAddr, kont: Kont[KontAddr]) = /* Profiler.logRes(s"$this.extend($a, $kont)") */ {
    content.get(a) match {
    case Some(konts) if konts.contains(kont) => this
    case Some(konts) => {
      // println(s"Joining $kont with $konts, increasing timestamp to ${timestamp + 1}")
      this.copy(content = content + (a -> (konts + kont)), timestamp = timestamp + 1)
    }
    case None => this.copy(content = content + (a -> Set(kont)), timestamp = timestamp + 1)
    }
  } /* { x => x.toString } */
  def join(that: KontStore[KontAddr]) = /* Profiler.logRes(s"$this.join($that)") */ {
    if (that.isInstanceOf[TimestampedKontStore[KontAddr]]) {
      if (that.asInstanceOf[TimestampedKontStore[KontAddr]].timestamp >= timestamp) {
        that
      } else {
        this
      }
    } else {
      throw new Exception(s"Incompatible continuation stores: ${this.getClass.getSimpleName} and ${that.getClass.getSimpleName}")
    }
  } /* { x => x.toString } */
  def forall(p: ((KontAddr, Set[Kont[KontAddr]])) => Boolean) = content.forall(p)
  def subsumes(that: KontStore[KontAddr]) = if (that.isInstanceOf[TimestampedKontStore[KontAddr]]) {
    timestamp >= that.asInstanceOf[TimestampedKontStore[KontAddr]].timestamp
  } else {
    that.forall({ case (a, ks) =>
      ks.forall((k1) => lookup(a).exists(k2 => k2.subsumes(k1)))
    })
  }
  override def fastEq(that: KontStore[KontAddr]) = if (that.isInstanceOf[TimestampedKontStore[KontAddr]]) {
    timestamp == that.asInstanceOf[TimestampedKontStore[KontAddr]].timestamp
  } else {
    false
  }
}

object KontStore {
  def empty[KontAddr : KontAddress]: KontStore[KontAddr] =
    new BasicKontStore[KontAddr](Map())
  def refCountStore[Addr : Address, KontAddr : KontAddress]: RefCountingKontStore[Addr,KontAddr] =
    new RefCountingKontStore[Addr,KontAddr]
  def gcStore[Addr : Address, KontAddr : KontAddress]: GCKontStore[Addr,KontAddr] =
    new GCKontStore[Addr,KontAddr](Map(), Map().withDefaultValue(Set()), Map().withDefaultValue(Set()))
}
