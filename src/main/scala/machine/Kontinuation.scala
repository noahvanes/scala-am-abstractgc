import scalaz.Scalaz._
import Util.MapStrict
import core.DisjointSet

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

case class BasicKontStore[KontAddr : KontAddress](content: Map[KontAddr, Set[Kont[KontAddr]]], hc: Int = 0) extends KontStore[KontAddr] {
  def keys = content.keys
  def lookup(a: KontAddr) = content.getOrElse(a, Set())
  override def toString = content.toString
  def extend(a: KontAddr, kont: Kont[KontAddr]) = /* Profiler.logRes(s"$this.extend($a, $kont)") */{
    val konts = lookup(a)
    val updatedHC = if (konts.contains(kont)) { hc } else { hc + kont.hashCode() }
    this.copy(content = content + (a -> (konts + kont)), hc = updatedHC)
  } /* { x => x.toString } */
  def join(that: KontStore[KontAddr]) = ???
  def forall(p: ((KontAddr, Set[Kont[KontAddr]])) => Boolean) = content.forall(p)
  def subsumes(that: KontStore[KontAddr]) =
    that.forall({ case (a, ks) =>
      ks.forall((k1) => lookup(a).exists(k2 => k2.subsumes(k1)))
    })
  override lazy val hashCode = hc
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
  (root: KontAddr,
   content: Map[KontAddr, (Set[Kont[KontAddr]],Set[KontAddr],Set[Addr])] = Map[KontAddr, (Set[Kont[KontAddr]],Set[KontAddr],Set[Addr])](),
   froms: Map[KontAddr,Set[KontAddr]] = Map[KontAddr,Set[KontAddr]]().withDefaultValue(Set[KontAddr]()),
   ds: DisjointSet[KontAddr] = DisjointSet[KontAddr](),
   hc: Int = 0)
  extends KontStore[KontAddr] {

  def changeRoot(newRoot: KontAddr): (RefCountingKontStore[Addr,KontAddr],Iterable[Addr]) = {
    var vdeleted = List[Addr]()
    var updatedFroms = this.froms
    var updatedContent = content
    var updatedHC = hc
    var updatedDS = ds
    val toDecrement = scala.collection.mutable.Queue[KontAddr](this.root)
    while(toDecrement.nonEmpty) {
      val addr = toDecrement.dequeue
      val addrFroms = updatedFroms(addr)
      if (addrFroms.isEmpty && addr != newRoot) {
        // DEALLOC
        val (konts,kaddrs,vrefs) = this.content(addr)
        updatedContent = updatedContent - addr
        updatedDS = updatedDS - addr
        konts foreach { kont => updatedHC = updatedHC - kont.hashCode() }
        vdeleted = vdeleted ++ vrefs
        kaddrs foreach { to =>
          val updatedToFroms = updatedFroms(to) - addr
          updatedFroms = updatedFroms.updated(to,updatedToFroms)
          toDecrement.enqueue(to)
        }
      }
    }
    val updatedKStore = RefCountingKontStore(newRoot,updatedContent,updatedFroms,updatedDS,updatedHC)
    (updatedKStore, vdeleted)
  }

  def keys = content.keys
  def lookup(adr: KontAddr) = content(adr)._1
  def forall(p: ((KontAddr, Set[Kont[KontAddr]])) => Boolean) = content.forall(n => p(n._1,n._2._1))

  def extend(adr: KontAddr, kont: Kont[KontAddr]) = extendRC(adr,kont)._1
  def extendRC(adr: KontAddr, kont: Kont[KontAddr]): (RefCountingKontStore[Addr,KontAddr],Iterable[Addr]) = content.get(adr) match {
    case None =>
      val kontRefs       = kont.frame.references
      val updatedContent = content + (adr -> (Set(kont),Set(kont.next),kontRefs))
      val updatedFroms   = froms + (kont.next -> (froms(kont.next) + adr))
      val updatedHC      = hc + kont.hashCode()
      val updatedKstore  = this.copy(content=updatedContent, froms=updatedFroms, hc=updatedHC)
      (updatedKstore, kontRefs)
    case Some((konts,_,_)) if konts.contains(kont) =>
      (this, Iterable.empty)
    case Some((konts,kaddrs,addrs)) =>
      val updatedHC = hc + kont.hashCode()
      val (updatedFroms,updatedKaddrs, updatedDS) = if (kaddrs.contains(kont.next)) {
        (froms, kaddrs, ds)
      } else {
        (froms+(kont.next->(froms(kont.next)+adr)), kaddrs+kont.next, detectCycle(adr, kont.next))
      }
      val (addedAddrs,updatedAddrs) = kont.frame.references.foldLeft((List[Addr](), addrs))((acc,ref) =>  if (addrs.contains(ref)) { acc } else (ref::acc._1,acc._2+ref))
      val updatedContent = content + (adr->(konts+kont,updatedKaddrs,updatedAddrs))
      val updatedKontStore = this.copy(content=updatedContent, froms=updatedFroms, ds=updatedDS, hc=updatedHC)
      (updatedKontStore, addedAddrs)
  }

  // NOTE: currently unused, but could serve as an inspiration for forward search in value store
  private def findPathsFwd(curr: KontAddr, addr: KontAddr, visited: Set[KontAddr]): Set[KontAddr]  = {
    if (curr == addr) {
      visited
    } else {
      val succs = content.get(curr) match {
        case Some((_,succs,_)) => succs
        case None => Set()
      }
      succs.filterNot(visited).flatMap(succ => findPathsFwd(succ,addr,visited+succ))
    }
  }

  private def detectCycle(from: KontAddr, to: KontAddr): DisjointSet[KontAddr] = {
    var updatedDS = this.ds
    var visited = Set[KontAddr](from)
    val addrs = scala.collection.mutable.Queue[KontAddr](from)
    while (addrs.nonEmpty) {
      val addr = addrs.dequeue
      val prevs = froms(addr)
      updatedDS = updatedDS.merge(addr,to)
      prevs.filterNot(visited) foreach { prv =>
        addrs.enqueue(prv)
        visited = visited + prv
      }
    }
    return updatedDS
  }

  /* TODO */

  def join(that: KontStore[KontAddr]) = throw new Exception("NYI: RefCountingKontStore.join(KontStore[KontAddr])")
  def subsumes(that: KontStore[KontAddr]) = throw new Exception("NYI: RefCountingKontStore.subsumes(KontStore[KontAddr])")

  /* PERFORMANCE OPTIMIZATION */

  override def equals(that: Any): Boolean = that match {
    case kstore : RefCountingKontStore[Addr,KontAddr] => this.hc == kstore.hc && this.content == kstore.content
    case _ => false
  }

  override def hashCode = hc

  /* DEBUGGING */

  def toFileSCC(path: String) = {
    var available = List(Colors.Red, Colors.Green, Colors.Pink, Colors.Black, Colors.Yellow)
    var colors = Map[KontAddr,Color]().withDefaultValue(Colors.White)
    var clscounts = Map[KontAddr,Int]().withDefaultValue(0)
    content.keys.foreach { adr =>
      val cls = ds.find(adr)
      val newCount = clscounts(cls) + 1
      clscounts = clscounts + (cls -> newCount)
      if (newCount == 2) {
       colors = colors + (cls -> available.head)
       available = available.tail
      }
    }
    implicit val kontNode = new GraphNode[KontAddr,Unit] {
      override def label(adr: KontAddr): String = s"$adr"
      override def color(adr: KontAddr): Color = colors(ds.find(adr))
    }
    val initG = Graph.empty[KontAddr,Unit,Unit]
    val fullG = content.keys.foldLeft(initG)((acc,adr) => acc.addEdges(content(adr)._2.map(succ => (adr,(),succ))))
    GraphDOTOutput.toFile(fullG,())(path)
  }

  def toFile(path: String, root: KontAddr) = {
    val kstore = this
    implicit val kontNode = new GraphNode[KontAddr,Unit] {
      override def label(adr: KontAddr): String = s"$adr"
      override def color(adr: KontAddr): Color = if (adr == root) { Colors.Green } else { Colors.White }
    }
    val initG = Graph.empty[KontAddr,Unit,Unit]
    val fullG = content.keys.foldLeft(initG)((acc,adr) => acc.addEdges(content(adr)._2.map(succ => (adr,(),succ))))
    GraphDOTOutput.toFile(fullG,())(path)
  }

  def toPngSCC(path: String) = {
    import sys.process._
    import java.io.File
    val tempFile = "temp.dot"
    toFileSCC(tempFile)
    s"dot -Tpng ${tempFile} -o ${path}".!
    new File(tempFile).delete()
  }

  def toPng(path: String, root: KontAddr): Unit = {
    import sys.process._
    import java.io.File
    val tempFile = "temp.dot"
    toFile(tempFile, root)
    s"dot -Tpng ${tempFile} -o ${path}".!
    new File(tempFile).delete()
  }

  private def transclo(k: KontAddr): Set[KontAddr] = {
    var transclo = Set[KontAddr]()
    var todo = List[KontAddr](k)
    while (!todo.isEmpty) {
      val next = todo.head
      todo = todo.tail
      if(!transclo.contains(next)) {
        transclo += next
        content.get(next).map(d => todo ++= d._2)
      }
    }
    return transclo
  }

  def garbage(root: KontAddr): Set[KontAddr] = {
    val marked = transclo(root)
    val unmarked = content--marked
    unmarked.keys.toSet
  }

  def reachable(from: KontAddr, to: KontAddr): Boolean = transclo(from).contains(to)

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
  def refCountStore[Addr : Address, KontAddr : KontAddress](root: KontAddr): RefCountingKontStore[Addr,KontAddr] =
    new RefCountingKontStore[Addr,KontAddr](root, content = Map(root->(Set(),Set(),Set())))
  def gcStore[Addr : Address, KontAddr : KontAddress]: GCKontStore[Addr,KontAddr] =
    new GCKontStore[Addr,KontAddr](Map(), Map().withDefaultValue(Set()), Map().withDefaultValue(Set()))
}