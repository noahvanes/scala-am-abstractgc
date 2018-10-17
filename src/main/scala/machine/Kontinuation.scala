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

case class RefCountingKontStore[Addr : Address, KontAddr : KontAddress](content: Map[KontAddr, Set[Kont[KontAddr]]] = Map[KontAddr, Set[Kont[KontAddr]]](),
                                                                        counts: Map[KontAddr,Int] = Map[KontAddr,Int]().withDefaultValue(0),
                                                                        refs: Map[KontAddr,Set[KontAddr]] = Map[KontAddr,Set[KontAddr]]().withDefaultValue(Set()),
                                                                        vrefs: Map[KontAddr,Set[Addr]] = Map[KontAddr,Set[Addr]]().withDefaultValue(Set()),
                                                                        hc: Int = 0) extends KontStore[KontAddr] {

  private def decRefUpdate(adr: KontAddr, counts: Map[KontAddr,Int], deleted: List[KontAddr], decremented: List[Addr], candidates: Set[KontAddr]): (Map[KontAddr,Int],List[KontAddr],List[Addr],Set[KontAddr]) = {
    val newCount = counts(adr) - 1
    if (newCount == 0) {
      refs(adr).foldLeft((counts, adr :: deleted, decremented++vrefs(adr), candidates))((acc,ref) => decRefUpdate(ref,acc._1,acc._2,acc._3,acc._4))
    } else {
      (counts + (adr -> newCount), deleted, decremented, candidates + adr)
    }
  }

  private def decRef(adr: KontAddr): (RefCountingKontStore[Addr,KontAddr],List[Addr],Set[KontAddr]) = {
    val (updatedCounts,deleted,addrs,decremented) = decRefUpdate(adr,counts,List(),List(),Set())
    val updatedHC = deleted.foldLeft(hc)((acc,ref) => {
      val konts = content.get(ref).getOrElse(Iterable.empty)
      konts.foldLeft(acc)((acc2,cnt) => acc2 - cnt.hashCode())
    })
    (RefCountingKontStore(content--deleted, updatedCounts--deleted, refs--deleted, vrefs--deleted, updatedHC), addrs, decremented--deleted)
  }

  private def incRef(adr: KontAddr): RefCountingKontStore[Addr,KontAddr] =
    this.copy(counts = counts + (adr -> (counts(adr) + 1)))

  def changeRoot(oldR: KontAddr, newR: KontAddr): (RefCountingKontStore[Addr,KontAddr],Iterable[Addr]) = if (oldR == newR) { (this, Iterable.empty) } else {
    val (kstore,addrs,decremented) = incRef(newR).decRef(oldR)
    val potentialGCR = decremented - newR
    (kstore,addrs)
  }

  def keys = content.keys
  def lookup(adr: KontAddr) = content(adr)
  def forall(p: ((KontAddr, Set[Kont[KontAddr]])) => Boolean) = content.forall(p)

  def extend(adr: KontAddr, kont: Kont[KontAddr]) = extendRC(adr,kont)._1
  def extendRC(adr: KontAddr, kont: Kont[KontAddr]): (RefCountingKontStore[Addr,KontAddr],Iterable[Addr]) = content.get(adr) match {
    case None => {
      val kontRefs = kont.frame.references
      (RefCountingKontStore(content+(adr->Set(kont)), counts+(kont.next->(counts(kont.next)+1)), refs+(adr->Set(kont.next)), vrefs+(adr->kontRefs), hc+kont.hashCode()), kontRefs)
    }
    case Some(konts) if konts.contains(kont) => (this, Iterable.empty)
    case Some(konts) => {
      val updatedContent = content + (adr -> (konts + kont))
      val updatedHC = hc + kont.hashCode()
      val adrRefs = refs(adr)
      val adrVRefs = vrefs(adr)
      val (updatedCounts,updatedRefs) = if (adrRefs.contains(kont.next)) { (counts,refs) } else { (counts+(kont.next->(counts(kont.next)+1)), refs+(adr->(adrRefs+kont.next))) }
      val (updatedVRefs,added) = kont.frame.references.foldLeft((adrVRefs,List[Addr]()))((acc,ref) => {
        if (adrVRefs.contains(ref)) { acc } else (acc._1 + ref, ref :: acc._2)
      })
      (RefCountingKontStore(updatedContent,updatedCounts,updatedRefs, vrefs + (adr -> updatedVRefs), updatedHC), added)
    }
  }

  /* TODO */

  def join(that: KontStore[KontAddr]) = throw new Exception("NYI: RefCountingKontStore.join(KontStore[Addr,KontAddr])")
  def subsumes(that: KontStore[KontAddr]) = throw new Exception("NYI: RefCountingKontStore.subsumes(KontStore[Addr,KontAddr])")

  /* PERFORMANCE OPTIMIZATION */
  override def equals(that: Any): Boolean = that match {
    case kstore : RefCountingKontStore[Addr,KontAddr] => this.content == kstore.content
    case _ => false
  }

  override def hashCode = hc
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
