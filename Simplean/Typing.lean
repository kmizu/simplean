import Simplean.Ops

/-!
# 型付け規則

式・引数列・文の型付けを帰納的述語で定義する（仕様）。
決定手続き（型検査器）は `Checker.lean`。
-/

namespace Simplean

-- ANCHOR: exprty
mutual

/-- 文脈 `Γ` の下で式 `e` は型 `t` を持つ。 -/
inductive ExprTy (P : Prog) : Ctx → Expr → Ty → Prop where
  | lit {Γ : Ctx} (n : Int) : ExprTy P Γ (.lit n) .int
  | strLit {Γ : Ctx} (s : String) : ExprTy P Γ (.strLit s) .str
  | var {Γ : Ctx} {x : String} {t : Ty} :
      AList.lookup Γ x = some t → ExprTy P Γ (.var x) t
  | nil {Γ : Ctx} (t : Ty) : ExprTy P Γ (.nil t) (.list t)
  | unop {Γ : Ctx} {op : UnOp} {e : Expr} {t t' : Ty} :
      ExprTy P Γ e t → unopTy op t = some t' → ExprTy P Γ (.unop op e) t'
  | binop {Γ : Ctx} {op : BinOp} {e₁ e₂ : Expr} {t₁ t₂ t : Ty} :
      ExprTy P Γ e₁ t₁ → ExprTy P Γ e₂ t₂ → binopTy op t₁ t₂ = some t →
      ExprTy P Γ (.binop op e₁ e₂) t
  | call {Γ : Ctx} {f : String} {args : List Expr} {fd : FunDef} :
      P.findFun f = some fd → ArgsTy P Γ args (fd.params.map (·.2)) →
      ExprTy P Γ (.call f args) fd.ret

/-- 引数列の型付け。 -/
inductive ArgsTy (P : Prog) : Ctx → List Expr → List Ty → Prop where
  | nil {Γ : Ctx} : ArgsTy P Γ [] []
  | cons {Γ : Ctx} {e : Expr} {es : List Expr} {t : Ty} {ts : List Ty} :
      ExprTy P Γ e t → ArgsTy P Γ es ts → ArgsTy P Γ (e :: es) (t :: ts)

end
-- ANCHOR_END: exprty

-- ANCHOR: stmtty
/-- 文脈 `Γ` の下で文 `s` を検査すると、後続の文脈は `Γ'` になる。 -/
inductive StmtTy (P : Prog) : Ctx → Stmt → Ctx → Prop where
  | skip {Γ : Ctx} : StmtTy P Γ .skip Γ
  | decl {Γ : Ctx} {x : String} {t : Ty} {e : Expr} :
      AList.lookup Γ x = none → ExprTy P Γ e t →
      StmtTy P Γ (.decl x t e) (AList.update Γ x t)
  | assign {Γ : Ctx} {x : String} {t : Ty} {e : Expr} :
      AList.lookup Γ x = some t → ExprTy P Γ e t → StmtTy P Γ (.assign x e) Γ
  | seq {Γ Γ₁ Γ₂ : Ctx} {s₁ s₂ : Stmt} :
      StmtTy P Γ s₁ Γ₁ → StmtTy P Γ₁ s₂ Γ₂ → StmtTy P Γ (.seq s₁ s₂) Γ₂
  | ite {Γ Γ₁ Γ₂ : Ctx} {c : Expr} {s₁ s₂ : Stmt} :
      ExprTy P Γ c .int → StmtTy P Γ s₁ Γ₁ → StmtTy P Γ s₂ Γ₂ →
      StmtTy P Γ (.ite c s₁ s₂) Γ
  | while {Γ Γ₁ : Ctx} {c : Expr} {body : Stmt} :
      ExprTy P Γ c .int → StmtTy P Γ body Γ₁ → StmtTy P Γ (.while c body) Γ
-- ANCHOR_END: stmtty

-- ANCHOR: progok
/-- 関数定義が正しく型付けされている：引数を文脈にして本体を検査し、結果式が戻り型を持つ。 -/
def FunOk (P : Prog) (fd : FunDef) : Prop :=
  ∃ Γ', StmtTy P fd.params fd.body Γ' ∧ ExprTy P Γ' fd.result fd.ret

/-- プログラムの全関数が正しく型付けされている。 -/
def ProgOk (P : Prog) : Prop := ∀ fd ∈ P.funs, FunOk P fd
-- ANCHOR_END: progok

-- ANCHOR: ctx_mono
/-- 文を検査しても、既にあった束縛は型を変えない（再宣言禁止のおかげ）。 -/
theorem ctx_mono {P : Prog} {Γ Γ' : Ctx} {s : Stmt} (h : StmtTy P Γ s Γ') :
    ∀ x t, AList.lookup Γ x = some t → AList.lookup Γ' x = some t := by
  induction h with
  | skip => intros; assumption
  | decl hx _ =>
    intro y t hy
    simp only [AList.update, AList.lookup_cons]
    split
    · rename_i hxy; subst hxy; rw [hx] at hy; cases hy
    · exact hy
  | assign => intros; assumption
  | seq _ _ ih₁ ih₂ => intro y t hy; exact ih₂ y t (ih₁ y t hy)
  | ite => intros; assumption
  | «while» => intros; assumption
-- ANCHOR_END: ctx_mono

end Simplean
