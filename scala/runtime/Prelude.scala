package simplean.rt

/** Hand-written runtime prelude for Lens-extracted code.
  *
  * Part of the TCB: Lean's `Nat`/`Int` map to `BigInt` with Lean's exact
  * semantics — truncated `Nat` subtraction, division/modulo by zero = 0.
  * The `Int` division/modulo flavor is pinned empirically against `#eval`
  * on the pinned toolchain (v4.34.1): `(-7)/2 = -4`, `(-7)%2 = 1`,
  * `7/(-2) = -3`, `7%(-2) = 1`, `x/0 = 0`, `x%0 = x` — Euclidean.
  */
object Prelude:
  def natSub(a: BigInt, b: BigInt): BigInt = (a - b).max(0)
  def natDiv(a: BigInt, b: BigInt): BigInt = if b == 0 then 0 else a / b
  def natMod(a: BigInt, b: BigInt): BigInt = if b == 0 then a else a % b

  /** Lean `Int` division — **Euclidean** (`Int.ediv`): `(-7)/2 = -4`,
    * `7/(-2) = -3`, `x/0 = 0`. Scala `BigInt./` is T-division, hence the
    * correction.
    */
  def intDiv(a: BigInt, b: BigInt): BigInt =
    if b == 0 then 0
    else
      val q = a / b
      if a % b < 0 then (if b > 0 then q - 1 else q + 1) else q

  /** Lean `Int` modulo — **Euclidean** (`Int.emod`): remainder ≥ 0 for
    * b ≠ 0; `x % 0 = x`.
    */
  def intMod(a: BigInt, b: BigInt): BigInt =
    if b == 0 then a
    else
      val r = a % b
      if r < 0 then r + b.abs else r

  /** Lean `Int.toNat`: negatives clamp to `0`. */
  def intToNat(a: BigInt): BigInt = if a < 0 then 0 else a

  /** Lean `String.length` counts Unicode scalar values, not UTF-16 units. */
  def strLength(s: String): BigInt = BigInt(s.codePointCount(0, s.length))

  /** Lean `xs[i]?` on lists (`List.getElem?`): `none` when out of range. */
  def listGet[A](xs: List[A], i: BigInt): Option[A] =
    if i < 0 || !i.isValidInt then None else xs.lift(i.toInt)

  /** Lean `List.take n xs` with a `Nat` count. */
  def listTake[A](n: BigInt, xs: List[A]): List[A] =
    if n <= 0 then Nil else if n >= xs.length then xs else xs.take(n.toInt)

  /** Lean `List.drop n xs` with a `Nat` count. */
  def listDrop[A](n: BigInt, xs: List[A]): List[A] =
    if n <= 0 then xs else if n >= xs.length then Nil else xs.drop(n.toInt)

  final case class LensPanic(msg: String) extends RuntimeException(msg)
  def panic[A](msg: String): A = throw LensPanic(msg)

  /** Lean `String.toList`: Unicode-scalar (codepoint) decomposition.
    * Lean `Char` extracts as a BigInt codepoint — NOT a Scala `Char`,
    * which is a UTF-16 code unit and wrong for astral characters.
    */
  def stringToList(s: String): List[BigInt] =
    s.codePoints().toArray.toList.map(BigInt(_))

  /** Inverse of `stringToList`. */
  def listToString(cs: List[BigInt]): String =
    val sb = new java.lang.StringBuilder
    cs.foreach(cp => sb.appendCodePoint(cp.toInt))
    sb.toString

object Stack:
  /** Run `f` on a fresh thread with an explicit stack size in MB.
    *
    * Extracted code is fuel-bounded, non-tail structural recursion; deep
    * inputs need deep stacks even when the JVM was launched with defaults.
    */
  def run[A](sizeMB: Int)(f: => A): A =
    var result: Either[Throwable, A] = Left(IllegalStateException("simplean-deep-stack thread did not run"))
    val t = Thread(
      null,
      () => result = try Right(f) catch { case e: Throwable => Left(e) },
      "simplean-deep-stack",
      sizeMB.toLong * 1024 * 1024
    )
    t.start()
    t.join()
    result match
      case Right(a) => a
      case Left(e)  => throw e
