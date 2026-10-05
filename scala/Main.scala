package simplean

import simplean.rt.Stack

/** Runs the example programs through the code extracted from Lean:
  * the type checker (`checkProg`), the reference interpreter (`evalProg`) and
  * the compiler + VM (`run(compileProg(P), fuel, VMState_init)`).
  *
  * Prints one line per program in exactly the format of
  * `scripts/expected.lean`, whose `#eval` output is `scala/expected.txt`.
  */
object Main:
  def showTy(t: Ty): String = t match
    case Ty.int()   => "int"
    case Ty.str()   => "str"
    case Ty.list(e) => s"list(${showTy(e)})"

  def listElems(v: Val): Option[List[Val]] = v match
    case Val.nil(_)       => Some(Nil)
    case Val.cons(hd, tl) => listElems(tl).map(hd :: _)
    case _                => None

  def showVal(v: Val): String = v match
    case Val.int(n) => n.toString
    case Val.str(s) => "\"" + s + "\""
    case _ =>
      listElems(v) match
        case Some(vs) => vs.map(showVal).mkString("[", ", ", "]")
        case None =>
          v match
            case Val.cons(hd, tl) => s"cons(${showVal(hd)}, ${showVal(tl)})"
            case _                => "?"

  def showRes(r: Res[Val]): String = r match
    case Res.timeout() => "timeout"
    case Res.err()     => "err"
    case Res.ok(v)     => s"ok(${showVal(v)})"

  def showOpt[A](f: A => String)(o: Option[A]): String = o match
    case None    => "None"
    case Some(a) => s"Some(${f(a)})"

  val table: List[(String, Prog, Int)] = List(
    ("fact", Examples_factProg, 100),
    ("factRec", Examples_factRecProg, 200),
    ("fib", Examples_fibProg, 100),
    ("parity", Examples_parityProg, 200),
    ("sumRange", Examples_sumRangeProg, 100),
    ("reverse", Examples_reverseProg, 100),
    ("flatten", Examples_flattenProg, 200),
    ("str", Examples_strProg, 100),
    ("illAddStr", Examples_illAddStr, 10),
    ("illUndeclared", Examples_illUndeclared, 10),
    ("illRedecl", Examples_illRedecl, 10),
    ("illArity", Examples_illArity, 10)
  )

  def line(name: String, p: Prog, fuel: Int): String =
    val check = showOpt(showTy)(checkProg(p))
    val eval  = showRes(evalProg(p, BigInt(fuel)))
    val vm    = showOpt(showVal)(run(compileProg(p), BigInt(2000), VMState_init))
    s"$name: check=$check eval=$eval vm=$vm"

  def main(args: Array[String]): Unit =
    // Extracted code is fuel-bounded, non-tail recursion: give it a deep stack.
    Stack.run(256) {
      table.foreach((n, p, fuel) => println(line(n, p, fuel)))
    }
