import core._

class LockstepMachine[Exp : Expression, Abs : JoinLattice, Addr : Address, Time : Timestamp] {

    val machineGC = new MachineAAMGC[Exp, Abs, Addr, Time]
    val machineRC = new MachineAAMARCplusplus[Exp, Abs, Addr, Time]

    def equiv(s1: machineGC.State, s2: machineRC.State): Boolean = 
        s1.control == s2.control

    def project(s: machineGC.State): machineRC.State = {
        machineRC.State(
            project(s.control), 
            project(s.store), 
            project(s.kstore, s.a),
            project(s.a), 
            s.t
        )
    }

    def project(c: machineGC.Control): machineRC.Control =
        c match {
            case machineGC.ControlEval(exp, env)       => machineRC.ControlEval(exp, env)
            case machineGC.ControlKont(kon)            => machineRC.ControlKont(kon)
            case machineGC.ControlCall(fn, fexp, args) => machineRC.ControlCall(fn, fexp, args)
            case machineGC.ControlError(err)           => machineRC.ControlError(err)
        }
        
    def project(sto: GCStore[Addr, Abs]): RefCountingStore[Addr, Abs] = {
        val content = sto.content.map { case (adr, (vlu, cnt)) => (adr, (vlu, cnt, sto.refs(adr))) }
        val hc = sto.content.values.map(_._1.hashCode).sum
        val ds = Tarjan(content.keys, (adr:Addr) => content(adr)._3)
        RefCountingStore(
            content,
            ???,        // in
            ds,         // ds
            ???,        // rootRefs
            ???,        // toCheck
            hc          // hc
        )
    }

    def project(k: Kont[machineGC.KontAddr]): Kont[machineRC.KontAddr] = 
        Kont(k.frame, project(k.next))

    def project(kstore: GCKontStore[Addr, machineGC.KontAddr], root: machineGC.KontAddr): RefCountingKontStore[Addr, machineRC.KontAddr] = {
        val content = kstore.content.foldLeft(Map[machineRC.KontAddr, (Set[Kont[machineRC.KontAddr]],Set[machineRC.KontAddr],Set[Addr])]()) {
            case (acc, (k, v)) =>
                acc + (project(k) -> ((v.map(project), kstore.refs(k).map(project), kstore.vrefs(k))))
        }
        val ds = Tarjan(content.keys, (adr: machineRC.KontAddr) => content(adr)._2)
        val in = content.foldLeft(Map[machineRC.KontAddr, machineRC.KontAddr]()) {
            case (acc, (k, (_,kaddrs,_))) => 
                kaddrs.foldLeft(acc)((acc, kaddr) => acc + (ds.find(kaddr) -> k))
        }
        val hc = content.values.foldLeft(0)((acc, konts) => acc + konts._1.toList.map(_.hashCode).sum)
        RefCountingKontStore(project(root), content, in, ds, hc)
    }

    def project(a: machineGC.KontAddr): machineRC.KontAddr = 
        a match {
            case machineGC.NormalKontAddress(exp, t) => machineRC.NormalKontAddress(exp, t)
            case machineGC.HaltKontAddress           => machineRC.HaltKontAddress
        } 

    case class State(s1: machineGC.State, s2: machineRC.State) {
        assert(equiv(s1, s2))
        def step(sem: Semantics[Exp,Abs,Addr,Time]): Set[State] = {
            val succs1 = s1.step(sem)
            val succs2 = s2.step(sem)
            assert(succs1.size == succs2.size) 
            succs1.foldLeft(Set[State]()) { (acc, ss1) =>
                ???
            }
        }
        
    }

    object State {
        def inject(exp: Exp, envBindings: Iterable[(String, Addr)], storeBindings: Iterable[(Addr, Abs)]): State =
            State(machineGC.State.inject(exp, envBindings, storeBindings),
                  machineRC.State.inject(exp, envBindings, storeBindings)) 
    }

    def compare(exp: Exp, sem: Semantics[Exp,Abs,Addr,Time]) = {
        val s0 = State.inject(exp, Iterable.empty, sem.initialStore)
        val worklist = scala.collection.mutable.Queue[State](s0)
        val visited = scala.collection.mutable.Set[State]()
        while (!worklist.isEmpty) {
            val s = worklist.dequeue
            if (visited.add(s)) {
                val succs = s.step(sem)
                worklist ++= succs
            }  
        }
    }
}