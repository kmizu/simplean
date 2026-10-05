import Simplean.Typing

/-!
# 型検査器

`Typing.lean` の規則を決定手続きにしたもの。`typeOf_sound` などで
「検査器が受理したら規則で型付けできる」ことを示す。
-/

namespace Simplean

-- ANCHOR: typeOf
mutual

/-- 式の型を計算する。型付けできなければ `none`。 -/
def typeOf (P : Prog) (Γ : Ctx) : Expr → Option Ty
  | .lit _ => some .int
  | .strLit _ => some .str
  | .var x => AList.lookup Γ x
  | .nil t => some (.list t)
  | .unop op e => do
      let t ← typeOf P Γ e
      unopTy op t
  | .binop op e₁ e₂ => do
      let t₁ ← typeOf P Γ e₁
      let t₂ ← typeOf P Γ e₂
      binopTy op t₁ t₂
  | .call f args => do
      let ts ← typeOfArgs P Γ args
      let fd ← P.findFun f
      if ts = fd.params.map (·.2) then some fd.ret else none

/-- 引数列の型を計算する。 -/
def typeOfArgs (P : Prog) (Γ : Ctx) : List Expr → Option (List Ty)
  | [] => some []
  | e :: es => do
      let t ← typeOf P Γ e
      let ts ← typeOfArgs P Γ es
      some (t :: ts)

end
-- ANCHOR_END: typeOf

-- ANCHOR: checkStmt
/-- 文を検査し、後続の文脈を返す。 -/
def checkStmt (P : Prog) : Ctx → Stmt → Option Ctx
  | Γ, .skip => some Γ
  | Γ, .decl x t e =>
      match AList.lookup Γ x, typeOf P Γ e with
      | none, some t' => if t' = t then some (AList.update Γ x t) else none
      | _, _ => none
  | Γ, .assign x e =>
      match AList.lookup Γ x, typeOf P Γ e with
      | some t, some t' => if t' = t then some Γ else none
      | _, _ => none
  | Γ, .seq s₁ s₂ => do
      let Γ₁ ← checkStmt P Γ s₁
      checkStmt P Γ₁ s₂
  | Γ, .ite c s₁ s₂ =>
      match typeOf P Γ c, checkStmt P Γ s₁, checkStmt P Γ s₂ with
      | some .int, some _, some _ => some Γ
      | _, _, _ => none
  | Γ, .while c body =>
      match typeOf P Γ c, checkStmt P Γ body with
      | some .int, some _ => some Γ
      | _, _ => none
-- ANCHOR_END: checkStmt

-- ANCHOR: checkProg
/-- 関数定義を検査する。 -/
def checkFun (P : Prog) (fd : FunDef) : Bool :=
  match checkStmt P fd.params fd.body with
  | some Γ' => typeOf P Γ' fd.result == some fd.ret
  | none => false

/-- プログラムを検査し、main の型を返す。 -/
def checkProg (P : Prog) : Option Ty :=
  if P.funs.all (checkFun P) then typeOf P [] P.main else none
-- ANCHOR_END: checkProg

-- ANCHOR: typeOf_sound
mutual

/-- 検査器が型を返せば、その型付けは規則で導ける。 -/
theorem typeOf_sound {P : Prog} {Γ : Ctx} :
    ∀ {e : Expr} {t : Ty}, typeOf P Γ e = some t → ExprTy P Γ e t
  | .lit _, _, h => by
    rw [typeOf] at h; cases h; exact .lit _
  | .strLit _, _, h => by
    rw [typeOf] at h; cases h; exact .strLit _
  | .var _, _, h => by
    rw [typeOf] at h; exact .var h
  | .nil _, _, h => by
    rw [typeOf] at h; cases h; exact .nil _
  | .unop op e, t, h => by
    rw [typeOf] at h
    obtain ⟨t₁, h₁, hop⟩ := Option.bind_eq_some_iff.mp h
    exact .unop (typeOf_sound h₁) hop
  | .binop op e₁ e₂, t, h => by
    rw [typeOf] at h
    obtain ⟨t₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨t₂, h₂, hop⟩ := Option.bind_eq_some_iff.mp h
    exact .binop (typeOf_sound h₁) (typeOf_sound h₂) hop
  | .call f args, t, h => by
    rw [typeOf] at h
    obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨fd, hfd, hret⟩ := Option.bind_eq_some_iff.mp h
    split at hret
    · rename_i heq
      cases hret
      subst heq
      exact .call hfd (typeOfArgs_sound hts)
    · cases hret

/-- 引数列についても同様。 -/
theorem typeOfArgs_sound {P : Prog} {Γ : Ctx} :
    ∀ {es : List Expr} {ts : List Ty}, typeOfArgs P Γ es = some ts → ArgsTy P Γ es ts
  | [], _, h => by
    rw [typeOfArgs] at h; cases h; exact .nil
  | e :: es, ts, h => by
    rw [typeOfArgs] at h
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ts', hts, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .cons (typeOf_sound ht) (typeOfArgs_sound hts)

end
-- ANCHOR_END: typeOf_sound

/-- 文の検査器の健全性。 -/
theorem checkStmt_sound {P : Prog} :
    ∀ {s : Stmt} {Γ Γ' : Ctx}, checkStmt P Γ s = some Γ' → StmtTy P Γ s Γ'
  | .skip, Γ, Γ', h => by
    rw [checkStmt] at h; cases h; exact .skip
  | .decl x t e, Γ, Γ', h => by
    simp only [checkStmt] at h
    split at h
    · rename_i hx hty
      split at h
      · rename_i heq; cases h; subst heq; exact .decl hx (typeOf_sound hty)
      · cases h
    · cases h
  | .assign x e, Γ, Γ', h => by
    simp only [checkStmt] at h
    split at h
    · rename_i hx hty
      split at h
      · rename_i heq; cases h; subst heq; exact .assign hx (typeOf_sound hty)
      · cases h
    · cases h
  | .seq s₁ s₂, Γ, Γ', h => by
    rw [checkStmt] at h
    obtain ⟨Γ₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    exact .seq (checkStmt_sound h₁) (checkStmt_sound h₂)
  | .ite c s₁ s₂, Γ, Γ', h => by
    simp only [checkStmt] at h
    split at h
    · rename_i hc h₁ h₂
      cases h
      exact .ite (typeOf_sound hc) (checkStmt_sound h₁) (checkStmt_sound h₂)
    · cases h
  | .while c body, Γ, Γ', h => by
    simp only [checkStmt] at h
    split at h
    · rename_i hc hb
      cases h
      exact .while (typeOf_sound hc) (checkStmt_sound hb)
    · cases h

theorem checkFun_sound {P : Prog} {fd : FunDef} (h : checkFun P fd = true) : FunOk P fd := by
  unfold checkFun at h
  split at h
  · rename_i Γ' hΓ'
    exact ⟨Γ', checkStmt_sound hΓ', typeOf_sound (by simpa using h)⟩
  · cases h

-- ANCHOR: checkProg_sound
/-- 検査器がプログラムを受理したら、全関数が正しく型付けされ、main は返された型を持つ。 -/
theorem checkProg_sound {P : Prog} {t : Ty} (h : checkProg P = some t) :
    ProgOk P ∧ ExprTy P [] P.main t := by
  unfold checkProg at h
  split at h
  · rename_i hall
    refine ⟨fun fd hfd => checkFun_sound ?_, typeOf_sound h⟩
    exact List.all_eq_true.mp hall fd hfd
  · cases h
-- ANCHOR_END: checkProg_sound

end Simplean
