import scalaz.Scalaz._
import scalaz._

/**
 * Semantics for ANF Scheme (abstract grammar defined in ANF.scala)
 */
class ANFSemantics[Abs : IsSchemeLattice, Addr : Address, Time : Timestamp](primitives: Primitives[Addr, Abs])
    extends Semantics[ANFExp, Abs, Addr, Time] {
  /** ANF Scheme only has three types of continuation frames: halt, let, and letrec */
  trait ANFFrame extends Frame {
    val refs = ???
  }
  case class FrameLet(v: Identifier, body: ANFExp, env: Environment[Addr]) extends ANFFrame {
    override def toString = s"FrameLet($v)"
  }
  case class FrameLetrec(v: Identifier, a: Addr, body: ANFExp, env: Environment[Addr]) extends ANFFrame {
    override def toString = s"FrameLetrec($v)"
  }

  type Actions = Set[Action[ANFExp, Abs, Addr]]

  /** Performs evaluation of an atomic expression, returning either an error or the produced value */
  def atomicEval(e: ANFAtomicExp, env: Environment[Addr], store: Store[Addr, Abs]): MayFail[(Abs, Set[Effect[Addr]])] = e match {
    case lam: ANFLambda => (IsSchemeLattice[Abs].inject[ANFExp, Addr]((lam, env)), Effect.none).point[MayFail]
    case ANFVar(variable) => env.lookup(variable.name) match {
      case Some(a) => store.lookup(a) match {
        case Some(v) => (v, Set(Effect.readVariable(a))).point[MayFail]
        case None => UnboundAddress(a.toString)
      }
      case None => UnboundVariable(variable)
    }
    case ANFValue(ValueString(s), _) => (IsSchemeLattice[Abs].inject(s), Effect.none).point[MayFail]
    case ANFValue(ValueInteger(n), _) => (IsSchemeLattice[Abs].inject(n), Effect.none).point[MayFail]
    case ANFValue(ValueReal(n), _) => (IsSchemeLattice[Abs].inject(n), Effect.none).point[MayFail]
    case ANFValue(ValueBoolean(b), _) => (IsSchemeLattice[Abs].inject(b), Effect.none).point[MayFail]
    case ANFValue(v, _) => NotSupported(s"Unhandled value: ${v}")
  }

  def stepEval(e: ANFExp, env: Environment[Addr], store: Store[Addr, Abs], t: Time) = e match {
    /* To step an atomic expression, performs atomic evaluation on it */
    case ae: ANFAtomicExp => for { (v, effs) <- atomicEval(ae, env, store) } yield Action.value(v, store, effs)
    /* Function call is the interesting case */
    case ANFFuncall(f, args, _) =>
      val init : MayFail[(List[(ANFExp, Abs)], Set[Effect[Addr]])] = MayFailSuccess((List(), Set()))
      /* We first atomically evaluate every argument (since we're in ANF, they should
       * all be atomic). */
      val argsveffs = args.foldLeft(init)((acc, arg) => for {
        (l, effects) <- acc
        (v, effects2) <- atomicEval(arg, env, store)
      } yield ((arg, v) :: l, effects ++ effects2))
      /* We then evaluate the operator (note that the order of evaluation of the
         * operator or operands does not matter, since they are all atomic,
         * and atomic expressions cannot perform store updates). */
      for {
        (argsv, effects) <- argsveffs
        (fv, effects2) <- atomicEval(f, env, store)
      } yield {
        /* For every value of the operand, we call the contained closure and primitive */
        val fromClo: Actions = IsSchemeLattice[Abs].getClosures[ANFExp, Addr](fv).map({
          case (ANFLambda(args, body, pos), env) => if (args.length == argsv.length) {
            /* To call a closure, bind the arguments and step into the function */
            bindArgs(args.zip(argsv.reverseMap(_._2)), env, store, t) match {
              case (env2, store) => Action.stepIn(f, (ANFLambda(args, body, pos), env), body, env2, store, argsv, effects)
            }
          } else {
            Action.error(ArityError(f.toString, args.length, argsv.length))
          }
          case (lambda, _) => Action.error(TypeError(lambda.toString, "operator", "closure", "not a closure"))
        })
        val fromPrim: Actions = IsSchemeLattice[Abs].getPrimitives(fv).flatMap(prim =>
          /* To call a primitive, apply the call method with the given arguments and the store */
          for { (res, store2, effects3) <- prim.call(f, argsv, store, t) }
          yield Action.value(res, store, effects ++ effects2 ++ effects3))
        if (fromClo.isEmpty && fromPrim.isEmpty) {
          Set(Action.error(TypeError(fv.toString, "operator", "function", "not a function")))
        } else {
          fromClo ++ fromPrim
        }
      }
    /* To evaluate (if cond cons alt), evaluate cond (which is atomic), and
     * depending on the result, either step into cons or alt, or in both */
    case ANFIf(cond, cons, alt, _) => for {
      (v, effects) <- atomicEval(cond, env, store)
    } yield {
      val t: Actions = Action.eval(cons, env, store, effects)
      val f: Actions = Action.eval(alt, env, store, effects)
      if (IsSchemeLattice[Abs].isTrue(v) && IsSchemeLattice[Abs].isFalse(v)) { t ++ f } else if (IsSchemeLattice[Abs].isTrue(v)) { t } else if (IsSchemeLattice[Abs].isFalse(v)) { f } else { Action.none }
    }
    /* To evaluate a let, first evaluaprograms.te the binding */
    case ANFLet(variable, exp, body, pos) =>
      Action.push(FrameLet(variable, body, env), exp, env, store)
    /* Same for letrec, but we need to bind the variable to an undefined value first */
    case ANFLetrec(variable, exp, body, pos) => {
      val vara = Address[Addr].variable(variable, JoinLattice[Abs].bottom, t)
      val env1 = env.extend(variable.name, vara)
      val store1 = store.extend(vara, JoinLattice[Abs].bottom)
      Action.push(FrameLetrec(variable, vara, body, env1), exp, env1, store1)
    }
    /* A set! needs to update the value of a variable in the store */
    case ANFSet(variable, value, _) => env.lookup(variable.name) match {
      case Some(vara) => for {
        (v, effects) <- atomicEval(value, env, store)
      } yield Action.value(v, store.update(vara, v), effects + Effect.writeVariable(vara))
      case None => Action.error(UnboundVariable(variable))
    }
    /* A quoted identifier is a value */
    case ANFQuoted(SExpId(Identifier(sym, _)), _) => Action.value(IsSchemeLattice[Abs].injectSymbol(sym), store)
    /* A quoted s-expression is more complicated to evaluate, as it may require
     * store allocation and is therefore not atomic. We don't deal with them in
     * ANF (they can always be converted into calls to cons). */
    case ANFQuoted(sexp, _) => Action.error(NotSupported("quoted expressions not yet handled in ANF"))
  }

  def stepKont(v: Abs, frame: Frame, store: Store[Addr, Abs], t: Time) = frame match {
    /* Allocate the variable and bind it to the reached value */
    case FrameLet(variable, body, env) => {
      val vara = Address[Addr].variable(variable, v, t)
      Action.eval(body, env.extend(variable.name, vara), store.extend(vara, v))
    }
    /* Just bind the variable to the reached value, since it has already been allocated */
    case FrameLetrec(variable, vara, body, env) =>
      Action.eval(body, env, store.update(vara, v))
  }

  def parse(program: String): ANFExp = ANF.parse(program)
  override def initialBindings = primitives.bindings
}
