package core

import scala.collection.mutable

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

  def roots(): Set[A] =
    tree.filter { case (adr, par) => adr == par }
        .keySet

  def allSets(): Set[Set[A]] = 
    roots().map(allOf(_).toSet)
}

// Adapted from https://gist.github.com/fbaierl/86df1072911de2a634696e7a819278fa
object Tarjan {

  /**
    * The algorithm takes a directed graph as input and produces a partition of the graph's vertices into the graph's strongly connected components.
    * @param nodes the nodes of the graph (as an Iterable)
    * @param edges the edges of the graph (as a function)
    * @param initialDs: [optional] the initial (default: empty) disjoint set of vertices
    * @return the strongly connected components of g (as a DisjointSet)
    */
  def apply[A](nodes: Iterable[A], edges: A => Iterable[A], initialDs: DisjointSet[A] = DisjointSet[A]()): DisjointSet[A] = {
    var ds      = initialDs 
    var s       = List.empty[A]
    val s_set   = mutable.Set.empty[A]
    val index   = mutable.Map.empty[A, Int]
    val lowlink = mutable.Map.empty[A, Int]
    // visiting a single node
    def visit(v: A): Unit = {
      val idx    = index.size
      val len    = s_set.size 
      index(v)   = idx
      lowlink(v) = idx
      s          = v :: s 
      s_set      += v
      for (w <- edges(v)) {
        if (!index.contains(w)) {
          visit(w)
          lowlink(v) = math.min(lowlink(v), lowlink(w))
        } else if (s_set(w)) {
          lowlink(v) = math.min(lowlink(v), index(w))
        }
      }
      if (lowlink(v) == index(v)) {
        do {
          val node = s.head 
          s        = s.tail
          s_set    -= node
          ds       = ds.merge(node, v)
        } while (s_set.size != len)
      }
    }
    // start visiting from every node in the graph
    for (v <- nodes) {
      if (!index.contains(v)) 
        visit(v)
    }
    // return the updated disjoint set 
    ds
  }
}