import Simplean.Ops
import Simplean.Res

/-!
# 参照意味論：fuel 付き definitional interpreter

再帰呼び出しのたびに fuel を 1 消費する。fuel が尽きれば `timeout`、
型の合わない演算や未定義変数は `err`。
-/

namespace Simplean

-- ANCHOR: eval
mutual

/-- 式の評価。 -/
def evalE (P : Prog) : Nat → Env → Expr → Res Val
  | 0, _, _ => .timeout
  | _ + 1, _, .lit n => .ok (.int n)
  | _ + 1, _, .strLit s => .ok (.str s)
  | _ + 1, ρ, .var x => Res.ofOption (AList.lookup ρ x)
  | _ + 1, _, .nil t => .ok (.nil t)
  | n + 1, ρ, .unop op e => do
      let v ← evalE P n ρ e
      Res.ofOption (applyUn op v)
  | n + 1, ρ, .binop op e₁ e₂ => do
      let v₁ ← evalE P n ρ e₁
      let v₂ ← evalE P n ρ e₂
      Res.ofOption (applyBin op v₁ v₂)
  | n + 1, ρ, .call f args => do
      let vs ← evalArgs P n ρ args
      match P.findFun f with
      | none => .err
      | some fd =>
        if vs.length = fd.params.length then do
          let ρ' ← execS P n (bindParams (fd.params.map (·.1)) vs) fd.body
          evalE P n ρ' fd.result
        else .err

/-- 引数列の評価（左から右）。 -/
def evalArgs (P : Prog) : Nat → Env → List Expr → Res (List Val)
  | 0, _, _ => .timeout
  | _ + 1, _, [] => .ok []
  | n + 1, ρ, e :: es => do
      let v ← evalE P n ρ e
      let vs ← evalArgs P n ρ es
      pure (v :: vs)

/-- 文の実行。更新後の環境を返す。 -/
def execS (P : Prog) : Nat → Env → Stmt → Res Env
  | 0, _, _ => .timeout
  | _ + 1, ρ, .skip => .ok ρ
  | n + 1, ρ, .decl x _ e => do
      let v ← evalE P n ρ e
      pure (AList.update ρ x v)
  | n + 1, ρ, .assign x e => do
      let v ← evalE P n ρ e
      pure (AList.update ρ x v)
  | n + 1, ρ, .seq s₁ s₂ => do
      let ρ₁ ← execS P n ρ s₁
      execS P n ρ₁ s₂
  | n + 1, ρ, .ite c s₁ s₂ => do
      let v ← evalE P n ρ c
      match v with
      | .int k => if k = 0 then execS P n ρ s₂ else execS P n ρ s₁
      | _ => .err
  | n + 1, ρ, .while c body => do
      let v ← evalE P n ρ c
      match v with
      | .int k =>
        if k = 0 then pure ρ
        else do
          let ρ₁ ← execS P n ρ body
          execS P n ρ₁ (.while c body)
      | _ => .err

end
-- ANCHOR_END: eval

-- ANCHOR: evalProg
/-- プログラムの実行：空の環境で main 式を評価する。 -/
def evalProg (P : Prog) (fuel : Nat) : Res Val := evalE P fuel [] P.main
-- ANCHOR_END: evalProg

end Simplean
