import Simplean.Semantics

/-!
# 例プログラム

AST を直接書く。チュートリアルとテストの両方で使う。
-/

namespace Simplean.Examples

-- ANCHOR: fact
/-- 反復版の階乗：`let r = 1; while 0 < n { r := r * n; n := n - 1 }; r` -/
def factIter : FunDef where
  name := "fact"
  params := [("n", .int)]
  ret := .int
  body :=
    .seq (.decl "r" .int (.lit 1))
      (.while (.binop .lt (.lit 0) (.var "n"))
        (.seq (.assign "r" (.binop .mul (.var "r") (.var "n")))
              (.assign "n" (.binop .sub (.var "n") (.lit 1)))))
  result := .var "r"

/-- `fact(10)` -/
def factProg : Prog := { funs := [factIter], main := .call "fact" [.lit 10] }
-- ANCHOR_END: fact

-- ANCHOR: factRec
/-- 再帰版の階乗：`let r = 1; if n <= 0 then skip else r := n * factRec(n - 1); r` -/
def factRec : FunDef where
  name := "factRec"
  params := [("n", .int)]
  ret := .int
  body :=
    .seq (.decl "r" .int (.lit 1))
      (.ite (.binop .le (.var "n") (.lit 0)) .skip
        (.assign "r" (.binop .mul (.var "n")
          (.call "factRec" [.binop .sub (.var "n") (.lit 1)]))))
  result := .var "r"

def factRecProg : Prog := { funs := [factRec], main := .call "factRec" [.lit 10] }
-- ANCHOR_END: factRec

/-- 反復版のフィボナッチ。ループ本体の中で `t` を宣言している。 -/
def fib : FunDef where
  name := "fib"
  params := [("n", .int)]
  ret := .int
  body :=
    .seq (.decl "a" .int (.lit 0))
      (.seq (.decl "b" .int (.lit 1))
        (.while (.binop .lt (.lit 0) (.var "n"))
          (.seq (.decl "t" .int (.binop .add (.var "a") (.var "b")))
            (.seq (.assign "a" (.var "b"))
              (.seq (.assign "b" (.var "t"))
                (.assign "n" (.binop .sub (.var "n") (.lit 1))))))))
  result := .var "a"

/-- `fib(20) = 6765` -/
def fibProg : Prog := { funs := [fib], main := .call "fib" [.lit 20] }

-- ANCHOR: parity
/-- 相互再帰：偶奇判定。 -/
def isEven : FunDef where
  name := "isEven"
  params := [("n", .int)]
  ret := .int
  body :=
    .seq (.decl "r" .int (.lit 0))
      (.ite (.binop .eq (.var "n") (.lit 0)) (.assign "r" (.lit 1))
        (.assign "r" (.call "isOdd" [.binop .sub (.var "n") (.lit 1)])))
  result := .var "r"

def isOdd : FunDef where
  name := "isOdd"
  params := [("n", .int)]
  ret := .int
  body :=
    .seq (.decl "r" .int (.lit 0))
      (.ite (.binop .eq (.var "n") (.lit 0)) (.assign "r" (.lit 0))
        (.assign "r" (.call "isEven" [.binop .sub (.var "n") (.lit 1)])))
  result := .var "r"

/-- `isEven(10) = 1` -/
def parityProg : Prog := { funs := [isEven, isOdd], main := .call "isEven" [.lit 10] }
-- ANCHOR_END: parity

-- ANCHOR: lists
/-- リストの総和。 -/
def sumList : FunDef where
  name := "sum"
  params := [("xs", .list .int)]
  ret := .int
  body :=
    .seq (.decl "s" .int (.lit 0))
      (.while (.unop .not (.unop .isNil (.var "xs")))
        (.seq (.assign "s" (.binop .add (.var "s") (.unop .head (.var "xs"))))
              (.assign "xs" (.unop .tail (.var "xs")))))
  result := .var "s"

/-- `range(n) = [0, 1, …, n-1]` -/
def range : FunDef where
  name := "range"
  params := [("n", .int)]
  ret := .list .int
  body :=
    .seq (.decl "acc" (.list .int) (.nil .int))
      (.while (.binop .lt (.lit 0) (.var "n"))
        (.seq (.assign "n" (.binop .sub (.var "n") (.lit 1)))
              (.assign "acc" (.binop .cons (.var "n") (.var "acc")))))
  result := .var "acc"

/-- `sum(range(10)) = 45` -/
def sumRangeProg : Prog :=
  { funs := [sumList, range], main := .call "sum" [.call "range" [.lit 10]] }

/-- リストの反転。 -/
def reverse : FunDef where
  name := "reverse"
  params := [("xs", .list .int)]
  ret := .list .int
  body :=
    .seq (.decl "acc" (.list .int) (.nil .int))
      (.while (.unop .not (.unop .isNil (.var "xs")))
        (.seq (.assign "acc" (.binop .cons (.unop .head (.var "xs")) (.var "acc")))
              (.assign "xs" (.unop .tail (.var "xs")))))
  result := .var "acc"

/-- リスト `[1, 2, 3]` の式。 -/
def list123 : Expr :=
  .binop .cons (.lit 1) (.binop .cons (.lit 2) (.binop .cons (.lit 3) (.nil .int)))

/-- `reverse([1, 2, 3]) = [3, 2, 1]` -/
def reverseProg : Prog := { funs := [reverse], main := .call "reverse" [list123] }

/-- リストの連結（`reverse` を使う）。 -/
def append : FunDef where
  name := "append"
  params := [("xs", .list .int), ("ys", .list .int)]
  ret := .list .int
  body :=
    .seq (.decl "r" (.list .int) (.var "ys"))
      (.seq (.decl "rx" (.list .int) (.call "reverse" [.var "xs"]))
        (.while (.unop .not (.unop .isNil (.var "rx")))
          (.seq (.assign "r" (.binop .cons (.unop .head (.var "rx")) (.var "r")))
                (.assign "rx" (.unop .tail (.var "rx"))))))
  result := .var "r"

/-- リストのリストを平坦化する（`List[List[Int]]` の例）。 -/
def flatten : FunDef where
  name := "flatten"
  params := [("xss", .list (.list .int))]
  ret := .list .int
  body :=
    .seq (.decl "acc" (.list .int) (.nil .int))
      (.while (.unop .not (.unop .isNil (.var "xss")))
        (.seq (.assign "acc" (.call "append" [.var "acc", .unop .head (.var "xss")]))
              (.assign "xss" (.unop .tail (.var "xss")))))
  result := .var "acc"

/-- `flatten([[1, 2], [], [3]]) = [1, 2, 3]` -/
def flattenProg : Prog :=
  { funs := [reverse, append, flatten]
    main := .call "flatten"
      [.binop .cons (.binop .cons (.lit 1) (.binop .cons (.lit 2) (.nil .int)))
        (.binop .cons (.nil .int)
          (.binop .cons (.binop .cons (.lit 3) (.nil .int)) (.nil (.list .int))))] }
-- ANCHOR_END: lists

-- ANCHOR: strings
/-- 文字列の繰り返し。 -/
def repeatStr : FunDef where
  name := "repeat"
  params := [("s", .str), ("n", .int)]
  ret := .str
  body :=
    .seq (.decl "r" .str (.strLit ""))
      (.while (.binop .lt (.lit 0) (.var "n"))
        (.seq (.assign "r" (.binop .concat (.var "r") (.var "s")))
              (.assign "n" (.binop .sub (.var "n") (.lit 1)))))
  result := .var "r"

/-- `repeat("ab", 3) ++ toStr(fact(5)) = "ababab120"` -/
def strProg : Prog :=
  { funs := [repeatStr, factIter]
    main := .binop .concat (.call "repeat" [.strLit "ab", .lit 3])
                           (.unop .toStr (.call "fact" [.lit 5])) }
-- ANCHOR_END: strings

-- ANCHOR: ill
/-- 型エラー：整数と文字列の加算。 -/
def illAddStr : Prog := { funs := [], main := .binop .add (.lit 1) (.strLit "a") }

/-- 型エラー：未宣言の変数。 -/
def illUndeclared : Prog := { funs := [], main := .var "x" }

/-- 型エラー：引数名と同じ名前の再宣言。 -/
def illRedecl : Prog :=
  { funs := [{ name := "f", params := [("x", .int)], ret := .int
               body := .decl "x" .int (.lit 1), result := .var "x" }]
    main := .call "f" [.lit 0] }

/-- 型エラー：引数の個数が違う。 -/
def illArity : Prog := { funs := [factIter], main := .call "fact" [.lit 1, .lit 2] }
-- ANCHOR_END: ill

end Simplean.Examples
