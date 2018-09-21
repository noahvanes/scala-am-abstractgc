import scalaz.Scalaz._

trait Frame {
  def subsumes(that: Frame): Boolean = {
    this.equals(that)
  }
}
trait KontAddress[A]

case class Kont[KontAddr: KontAddress](frame: Frame, next: KontAddr) {
  def subsumes(that: Kont[KontAddr]) = that match {
    case Kont(frame2, next2) => frame.subsumes(frame2) && next.equals(next2)
    case _ => false
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

case class GCKontStore[KontAddr : KontAddress](root: KontAddr, content: Map[KontAddr, Set[Kont[KontAddr]]], refs: Map[KontAddr,Set[KontAddr]]) extends KontStore[KontAddr] {

  def changeRoot(r: KontAddr): GCKontStore[KontAddr] = this.copy(root = r)

  def mark(adr: KontAddr, marked: Set[KontAddr]): Set[KontAddr] =
    refs(adr).foldLeft(marked + adr)((acc,ref) => if (acc.contains(ref)) { acc } else { acc ++ mark(ref,acc) })

  def collect(): GCKontStore[KontAddr] = {
    val marked = mark(root,Set())
    val updatedContent = content.filterKeys(marked)
    val updatedRefs = refs.filterKeys(marked).withDefaultValue(Set())
    this.copy(content = updatedContent, refs = updatedRefs)
  }

  def keys = content.keys
  def lookup(adr: KontAddr) = content(adr)
  def forall(p: ((KontAddr, Set[Kont[KontAddr]])) => Boolean) = content.forall(p)

  def extendCollect(adr: KontAddr, kont: Kont[KontAddr]): GCKontStore[KontAddr] =
    if (content.contains(adr)) {  // risk of zombie creation
      collect().extend(adr,kont)
    } else {
      extend(adr,kont)
    }

  def extend(adr: KontAddr, kont: Kont[KontAddr]): GCKontStore[KontAddr] = {
    val adrRefs = refs(adr)
    val adrCnts = content.get(adr).getOrElse(Set())
    if (adrRefs.contains(kont.next)) {
      this.copy(content = content + (adr -> (adrCnts + kont)))
    } else {
      this.copy(content = content + (adr -> (adrCnts + kont)),
                refs = refs + (adr -> (adrRefs + kont.next)))
    }
  }

  /* TODO */

  def join(that: KontStore[KontAddr]) = throw new Exception("NYI: GCKontStore.join(KontStore[KontAddr])")
  def subsumes(that: KontStore[KontAddr]) = throw new Exception("NYI: GCKontStore.subsumes(KontStore[KontAddr])")

}

case class RefCountingKontStore[KontAddr : KontAddress](content: Map[KontAddr, Set[Kont[KontAddr]]] = Map[KontAddr, Set[Kont[KontAddr]]](),
                                                        counts: Map[KontAddr,Int] = Map[KontAddr,Int]().withDefaultValue(0),
                                                        refs: Map[KontAddr,Set[KontAddr]] = Map[KontAddr,Set[KontAddr]]().withDefaultValue(Set())) extends KontStore[KontAddr] {

  private def decRefUpdate(adr: KontAddr, content: Map[KontAddr,Set[Kont[KontAddr]]], counts: Map[KontAddr,Int], refs: Map[KontAddr,Set[KontAddr]]): (Map[KontAddr,Set[Kont[KontAddr]]],Map[KontAddr,Int],Map[KontAddr,Set[KontAddr]]) = {
    val newCount = counts(adr) - 1
    if (newCount == 0) {
      refs(adr).foldLeft((content - adr, counts - adr, refs - adr))((acc,ref) => decRefUpdate(ref,acc._1,acc._2,acc._3))
    } else {
      (content, counts + (adr -> newCount), refs)
    }
  }

  def decRef(adr: KontAddr): RefCountingKontStore[KontAddr] = {
    val (updatedContent,updatedCounts,updatedRefs) = decRefUpdate(adr,content,counts,refs)
    this.copy(content = updatedContent, counts = updatedCounts, refs = updatedRefs)
  }

  def addRef(adr: KontAddr): RefCountingKontStore[KontAddr] =
    this.copy(counts = counts + (adr -> (counts(adr) + 1)))

  def keys = content.keys
  def lookup(adr: KontAddr) = content(adr)
  def forall(p: ((KontAddr, Set[Kont[KontAddr]])) => Boolean) = content.forall(p)

  def extend(adr: KontAddr, kont: Kont[KontAddr]): RefCountingKontStore[KontAddr] = {
    val adrRefs = refs(adr)
    val adrCnts = content.get(adr).getOrElse(Set())
    if (adrRefs.contains(kont.next)) {
      this.copy(content = content + (adr -> (adrCnts + kont)))
    } else {
      this.copy(content = content + (adr -> (adrCnts + kont)),
                counts = counts + (kont.next -> (counts(kont.next) + 1)),
                refs = refs + (adr -> (adrRefs + kont.next)))
    }
  }

  /* TODO */

  def join(that: KontStore[KontAddr]) = throw new Exception("NYI: RefCountingKontStore.join(KontStore[KontAddr])")
  def subsumes(that: KontStore[KontAddr]) = throw new Exception("NYI: RefCountingKontStore.subsumes(KontStore[KontAddr])")
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
  def refCountStore[KontAddr : KontAddress]: RefCountingKontStore[KontAddr] =
    new RefCountingKontStore[KontAddr]
  def gcStore[KontAddr : KontAddress](root: KontAddr): GCKontStore[KontAddr] =
    new GCKontStore[KontAddr](root, Map(), Map().withDefaultValue(Set()))
}
