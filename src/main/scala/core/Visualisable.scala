trait Visualisable[N] {

  def nodes(): Set[N]
  def edges(): Set[(N,N)]
}
