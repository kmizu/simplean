import Simplean

/-!
# 演習 2：for 文を糖衣構文として足す

`for x in 0 ..< n { body }` を `while` に展開する関数を書き、
展開後のプログラムが型付けを保つことを示す。
-/

namespace Exercises

open Simplean

/-- `x := 0; while x < n { body; x := x + 1 }` に展開する。 -/
def forLoop (x : String) (n : Expr) (body : Stmt) : Stmt :=
  .seq (.decl x .int (.lit 0))
    (.while (.binop .lt (.var x) n)
      (.seq body (.assign x (.binop .add (.var x) (.lit 1)))))

/-- 展開後の文の型付け：`x` が未宣言で `n : int`、本体が `x` を宣言した文脈で型付けできれば、
全体も型付けできる。 -/
theorem forLoop_ty {P : Prog} {Γ Γ' : Ctx} {x : String} {n : Expr} {body : Stmt}
    (hx : AList.lookup Γ x = none) (hn : ExprTy P Γ n .int)
    (hbody : StmtTy P (AList.update Γ x .int) body Γ') :
    ∃ Γ'', StmtTy P Γ (forLoop x n body) Γ'' := by
  sorry

end Exercises
