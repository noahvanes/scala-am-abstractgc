package core

case class DisjointSet[A]
  (var tree: Map[A,A]   = Map[A,A]().withDefault(a => a),
   val rank: Map[A,Int] = Map[A,Int]().withDefaultValue(0),
   val next: Map[A, A]  = Map[A, A](),
   val last: Map[A, A]  = Map[A, A]().withDefault(a => a)) {

  // MARK: Core methods
  
  def find(a: A): A = {
    val parent = tree(a)
    if (parent == a) {
      a
    } else {
      val root = find(parent)
      tree = tree.updated(a,root)
      root
    }
  }

  def union(r1: A, r2: A): DisjointSet[A] = if (r1 == r2) { this } else {
    val rank1 = rank(r1)
    val rank2 = rank(r2)
    if (rank1 < rank2) {
      attach(r1, r2)
    } else if (rank1 > rank2) {
      attach(r2, r1)
    } else {
      attach(r1, r2, rank.updated(r2,rank2+1))
    }
  }

  def allOf(r: A): List[A] = next.get(r) match {
    case None       => List(r)
    case Some(nxt)  => r :: allOf(nxt) 
  }

  private def attach(sub: A, to: A, updatedRanks: Map[A, Int] = rank): DisjointSet[A] =
    DisjointSet(tree = tree.updated(sub, to),
                rank = updatedRanks,
                next = next.updated(last(to), sub),
                last = last.updated(to, last(sub)))

  def singleton(r: A): Boolean = (rank(r) == 0)

  // MARK: Convencience methods

  def merge(a1: A, a2: A): DisjointSet[A] = union(find(a1), find(a2))
  def equiv(a1: A, a2: A): Boolean        = find(a1) == find(a2)
  def allEquiv(a: A)                      = allOf(find(a))
  def removeEquiv(a: A)                   = this -- allEquiv(a)

  // MARK: "Unsafe" methods (i.e. must be applied to _all_ elements in the SCC)

  def -(elem: A): DisjointSet[A]              = DisjointSet(tree = tree-elem,   rank=rank-elem,   next=next-elem,   last=last-elem)
  def --(elems: Iterable[A]): DisjointSet[A]  = DisjointSet(tree = tree--elems, rank=rank--elems, next=next--elems, last=last--elems)


  // MARK: Debugging

  def allSets(): List[Set[A]] = {
    val perCls = tree.groupBy(p => find(p._1)).toList.map(_._2)
    perCls.map(m => m.keys.toSet ++ m.values.toSet)
  }
}