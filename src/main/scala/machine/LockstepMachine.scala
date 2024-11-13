import core._

class LockstepMachine[Exp : Expression, Abs : JoinLattice, Addr : Address, Time : Timestamp] {

    val machineGC = new MachineAAMGC[Exp, Abs, Addr, Time]
    val machineRC = new MachineAAMARCplusplus[Exp, Abs, Addr, Time]

    def project(s: machineRC.State): machineGC.State = {
        machineGC.State(
            project(s.control), 
            project(s.store),
            project(s.kstore),
            project(s.adr), 
            s.t
        )
    }

    def project(a: machineRC.KontAddr): machineGC.KontAddr = 
        a match {
            case machineRC.NormalKontAddress(exp, t)    => machineGC.NormalKontAddress(exp, t)
            case machineRC.HaltKontAddress              => machineGC.HaltKontAddress
        }

    def project(sto: RefCountingStore[Addr, Abs]): GCStore[Addr, Abs] =
        GCStore(sto.content.map({ case (a, (v,c,_)) => (a, (v,c)) }),
                sto.content.map({ case (a, (_,_,r)) => (a, r) }))

    def project(c: machineRC.Control): machineGC.Control =
        c match {
            case machineRC.ControlEval(exp, env)       => machineGC.ControlEval(exp, env)
            case machineRC.ControlKont(kon)            => machineGC.ControlKont(kon)
            case machineRC.ControlCall(fn, fexp, args) => machineGC.ControlCall(fn, fexp, args)
            case machineRC.ControlError(err)           => machineGC.ControlError(err)
        }

    def project(k: Kont[machineRC.KontAddr]): Kont[machineGC.KontAddr] = 
        Kont(k.frame, project(k.next))

    def project(kstore: RefCountingKontStore[Addr, machineRC.KontAddr]): GCKontStore[Addr, machineGC.KontAddr] =
        GCKontStore(kstore.content.map({ case (k,(v,_,_)) => (project(k), v.map(project)) }), 
                    kstore.content.map({ case (k,(_,r,_)) => (project(k), r.map(project)) }).withDefaultValue(Set()),
                    kstore.content.map({ case (k,(_,_,r)) => (project(k), r) }).withDefaultValue(Set()))

    def initialState(exp: Exp, sem: Semantics[Exp,Abs,Addr,Time]) = {
        val s0 = machineRC.State.inject(exp, Iterable.empty, sem.initialStore)
        val s0_gcA = project(s0)
        val s0_gcB = machineGC.State.inject(exp, Iterable.empty, sem.initialStore)
        if (s0_gcA != s0_gcB) {
            println()
            println()
            println(s0_gcA)
            println()
            println()
            println(s0_gcB)
            throw new RuntimeException(s"Initial states are not equal")
        }
        s0
    }

    def step(st: machineRC.State, sem: Semantics[Exp,Abs,Addr,Time]) = {
        val st_gc = project(st)
        val succs = st.step(sem)
        val succs_gcA = succs.map(project)
        val succs_gcB = st_gc.step(sem)
        if (succs_gcA != succs_gcB) {
            println(st)
            println(Differ.calcDiff(succs_gcA.head.store.content, succs_gcB.head.store.content))
            throw new RuntimeException("Step is not the same")
        }
        succs 
    }

    def compare(exp: Exp, sem: Semantics[Exp,Abs,Addr,Time]) = {
        val s0 = initialState(exp, sem)
        val worklist = scala.collection.mutable.Queue[machineRC.State](s0)
        val visited = scala.collection.mutable.Set[machineRC.State]()
        while (!worklist.isEmpty) {
            val s = worklist.dequeue
            if (visited.add(s)) {
                val succs = step(s, sem)
                worklist ++= succs
            }  
        }
    }
}