# Usage

This version of the Scala-AM framework has been set up in such a way that one can easily run a variety of experiments to evaluate and compare several approaches to abstract garbage collection. Specifically, one can configure and run `src/main/scala/Main.scala` to execute a set of benchmarks, which outputs the results to a CSV-file in the top-level folder `output`. Detailed instructions on how to run the experiments and reproduce the results found in our ECOOP'19 companion [paper](https://soft.vub.ac.be/~noahves/ecoop2019arc/ecooop2019arc.pdf) can be found [here](https://soft.vub.ac.be/~noahves/ecoop2019arc/ecoop2019arc-artifact-manual.pdf).

# About Scala-AM

The goal of the Scala-AM framework is to experiment with abstract machines and language semantics.
Scala-AM is initially based on the theoretical framework of Abstracting Abstract Machines (Van Horn & Might, 2010).
For more information on the framework, look [here](https://github.com/acieroid/scala-am) or consult the following publications:
  - Scala-AM: A Modular Static Analysis Framework, SCAM 2016, [pdf](http://soft.vub.ac.be/Publications/2016/vub-soft-tr-16-07.pdf), [doi](https://zenodo.org/badge/latestdoi/23603/acieroid/scala-am).
  - Building a Modular Static Analysis Framework in Scala, [pdf](http://soft.vub.ac.be/Publications/2016/vub-soft-tr-16-13.pdf).
  - Mailbox abstractions for static analysis of actor programs, ECOOP 2017, [pdf](http://drops.dagstuhl.de/opus/volltexte/2017/7254/pdf/LIPIcs-ECOOP-2017-25.pdf).

# Abstract Reference Counting

This fork extends Scala-AM with a proof-of-concept implementation of abstract reference counting.
Currently, this implementation is provided as a separate machine abstraction in `src/main/scala/machine/AAMRefCounting.scala` (or `src/main/scala/machine/AAMRefCountingVanilla.scala` for an implementation without cycle detection).
As such - thanks to the modularity of Scala-AM - it can be directly configured with various context-sensitivities (e.g. the k-CFA family) and abstract domains (e.g. using a typelattice or a lattice in the k-points-to family). 

In addition, implementations are provided of "traditional" abstract garbage collection using tracing GC in `src/main/scala/machine/AAMGC.scala` (which applies abstract GC at every transition) and `src/main/scala/machine/AAMGCAlt.scala` (which applies abstract GC at every join in the store).

Note that, at this point, all our machine abstractions only support a limited subset of Scheme, as the input expression first needs to be preprocessed to compute free variables and to inline references to primitives, which is beneficial to the efficiency of abstract garbage collection.

For more information on abstract garbage collection, consult the following publication:
- Might, M., & Shivers, O. (2006, September). Improving flow analyses via ΓCFA: Abstract garbage collection and counting. In ACM SIGPLAN Notices (Vol. 41, No. 9, pp. 13-25). ACM, [pdf](http://matt.might.net/papers/might2006gcfa.pdf).
