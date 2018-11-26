package core

case class CGraph[N](edges: Map[N,Set[N]] = Map[N,Set[N]]().withDefaultValue(Set()),
                     ds: DisjointSet[N] = DisjointSet[N](),
                     in: Map[N,List[N]] = Map[N,List[N]]().withDefaultValue(List())) {

  def addEdge(from: N, to: N): CGraph[N] = {
    val updatedEdges = edges + (from -> (edges(from) + to))
    var (updatedEq, updatedDS,updatedIn) = detectCycle(from,to)
    if (!updatedEq) {
      val toCls = ds.find(to)
      updatedIn = in + (toCls -> (from :: in(toCls)))
    }
    CGraph(updatedEdges, updatedDS, updatedIn)
  }

  private def detectCycle(from: N, to: N): (Boolean,DisjointSet[N],Map[N,List[N]]) = {

    var updatedDS = this.ds
    var incoming = List[N]()
    var visited = Set[N]()

    val target = ds.find(to)
    def reachable(current: N): Boolean = {
      val cls = ds.find(current)
      if (cls == target) {
        true
      } else if (visited(cls)) {
        updatedDS.equiv(cls, target)
      } else {
        visited = visited + cls
        val (canReach, cantReach) = in(cls).partition(reachable)
        if (canReach.nonEmpty) {  // current node can reach target
          updatedDS = updatedDS.merge(cls, target)
          incoming = incoming ++ cantReach
          true
        } else {                  // current node can't reach target
          false
        }
      }
    }

    val updatedEq = reachable(from)
    val updatedIn = if (updatedEq) {
      incoming = incoming ++ in(target)
      in + (updatedDS.find(target) -> incoming)
    } else {
      in
    }
    (updatedEq, updatedDS, updatedIn)
  }

  def equiv(x: N, y: N): Boolean = ds.equiv(x,y)

  def nodes(): Set[N] = edges.keys.toSet ++ edges.values.toSet.flatten

  def scc() = {
    val nodes = this.nodes()
    nodes.groupBy(ds.find(_))
  }
}

object CGraphTest {

  def main(args: Array[String]): Unit = {
    val graph = CGraph[Int]()
        .addEdge(0,6)
        .addEdge(0,1)
        .addEdge(0,5)
        .addEdge(2,0)
        .addEdge(2,3)
        .addEdge(3,5)
        .addEdge(3,2)
        .addEdge(4,3)
        .addEdge(4,2)
        .addEdge(4,11)
        .addEdge(5,4)
        .addEdge(6,4)
        .addEdge(6,9)
        .addEdge(7,6)
        .addEdge(7,8)
        .addEdge(8,7)
        .addEdge(8,9)
        .addEdge(9,10)
        .addEdge(9,11)
        .addEdge(10,12)
        .addEdge(11,12)
        .addEdge(12,9)

    val scc = graph.scc()
    val sccIn = scc.map(p => (p._1,graph.in(p._1)))
    println(s"SCC: $scc")
    println(s"SCC-IN: $sccIn")
  }
}
