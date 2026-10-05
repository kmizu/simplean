import Simplean.Semantics
import Simplean.VMLemmas

/-!
# コンパイラ正当性（式と引数列）

参照意味論で式が値 `v` に評価されるなら、コンパイルしたコードを VM で走らせると
`v` がスタックに積まれた状態に到達する（forward simulation）。fuel に関する帰納法。
-/

namespace Simplean

-- ANCHOR: tableok
/-- VM の関数表が元のプログラムと整合している：各関数の入口にその関数のコードがある。 -/
def TableOk (P : Prog) (vmP : VMProg) : Prop :=
  ∀ f fd, P.findFun f = some fd →
    ∃ entry, AList.lookup vmP.table f = some ⟨entry, fd.params.map (·.1)⟩ ∧
      CodeAt vmP.code entry (compileFun fd)
-- ANCHOR_END: tableok

-- ANCHOR: simall
/-- fuel `n` までのシミュレーション：式・引数列・文。 -/
def SimAll (P : Prog) (vmP : VMProg) (n : Nat) : Prop :=
  (∀ ρ e v pc σ F, evalE P n ρ e = .ok v → CodeAt vmP.code pc (compileExpr e) →
      Reaches vmP ⟨pc, σ, ρ, F⟩ ⟨pc + (compileExpr e).length, v :: σ, ρ, F⟩) ∧
  (∀ ρ es vs pc σ F, evalArgs P n ρ es = .ok vs → CodeAt vmP.code pc (compileArgs es) →
      Reaches vmP ⟨pc, σ, ρ, F⟩ ⟨pc + (compileArgs es).length, vs.reverse ++ σ, ρ, F⟩) ∧
  (∀ ρ s ρ' pc σ F, execS P n ρ s = .ok ρ' → CodeAt vmP.code pc (compileStmt s) →
      Reaches vmP ⟨pc, σ, ρ, F⟩ ⟨pc + (compileStmt s).length, σ, ρ', F⟩)
-- ANCHOR_END: simall

-- ANCHOR: simE
/-- 式：fuel を 1 進める。 -/
theorem simE_succ {P : Prog} {vmP : VMProg} (hT : TableOk P vmP) {n : Nat}
    (ih : SimAll P vmP n) :
    ∀ ρ e v pc σ F, evalE P (n + 1) ρ e = .ok v → CodeAt vmP.code pc (compileExpr e) →
      Reaches vmP ⟨pc, σ, ρ, F⟩ ⟨pc + (compileExpr e).length, v :: σ, ρ, F⟩ := by
  obtain ⟨ihE, ihA, ihS⟩ := ih
  intro ρ e v pc σ F hev hc
  cases e with
  | lit k =>
    simp only [evalE, Res.ok.injEq] at hev
    subst hev
    exact (Reaches.single (step_push hc)).cast rfl (by state_eq)
  | strLit s =>
    simp only [evalE, Res.ok.injEq] at hev
    subst hev
    exact (Reaches.single (step_push hc)).cast rfl (by state_eq)
  | var x =>
    simp only [evalE] at hev
    cases hl : AList.lookup ρ x with
    | none => rw [hl] at hev; simp at hev
    | some w =>
      rw [hl] at hev
      simp at hev
      subst hev
      exact (Reaches.single (step_load hc hl)).cast rfl (by state_eq)
  | nil t =>
    simp only [evalE, Res.ok.injEq] at hev
    subst hev
    exact (Reaches.single (step_push hc)).cast rfl (by state_eq)
  | unop op e₁ =>
    simp only [evalE] at hev
    cases h₁ : evalE P n ρ e₁ with
    | timeout => rw [h₁] at hev; simp at hev
    | err => rw [h₁] at hev; simp at hev
    | ok v₁ =>
      rw [h₁] at hev
      simp only [Res.bind_ok] at hev
      cases hw : applyUn op v₁ with
      | none => rw [hw] at hev; simp at hev
      | some w =>
        rw [hw] at hev
        simp at hev
        subst hev
        simp only [compileExpr] at hc
        refine (ihE _ _ _ _ _ _ h₁ hc.append_left).trans ?_
        exact (Reaches.single (step_unop hc.append_right hw)).cast rfl (by state_eq)
  | binop op e₁ e₂ =>
    simp only [evalE] at hev
    cases h₁ : evalE P n ρ e₁ with
    | timeout => rw [h₁] at hev; simp at hev
    | err => rw [h₁] at hev; simp at hev
    | ok v₁ =>
      rw [h₁] at hev
      simp only [Res.bind_ok] at hev
      cases h₂ : evalE P n ρ e₂ with
      | timeout => rw [h₂] at hev; simp at hev
      | err => rw [h₂] at hev; simp at hev
      | ok v₂ =>
        rw [h₂] at hev
        simp only [Res.bind_ok] at hev
        cases hw : applyBin op v₁ v₂ with
        | none => rw [hw] at hev; simp at hev
        | some w =>
          rw [hw] at hev
          simp at hev
          subst hev
          simp only [compileExpr, List.append_assoc] at hc
          have hc₁ := hc.append_left
          have hc₂ := hc.append_right.append_left
          have hc₃ := hc.append_right.append_right
          refine (ihE _ _ _ _ _ _ h₁ hc₁).trans ?_
          refine (ihE _ _ _ _ _ _ h₂ hc₂).trans ?_
          exact (Reaches.single (step_binop hc₃ hw)).cast rfl (by state_eq)
  | call f args =>
    simp only [evalE] at hev
    cases hargs : evalArgs P n ρ args with
    | timeout => rw [hargs] at hev; simp at hev
    | err => rw [hargs] at hev; simp at hev
    | ok vs =>
      rw [hargs] at hev
      simp only [Res.bind_ok] at hev
      cases hfd : P.findFun f with
      | none => rw [hfd] at hev; simp at hev
      | some fd =>
        rw [hfd] at hev
        dsimp only at hev
        split at hev
        · rename_i hlen
          cases hb : execS P n (bindParams (fd.params.map (·.1)) vs) fd.body with
          | timeout => rw [hb] at hev; simp at hev
          | err => rw [hb] at hev; simp at hev
          | ok ρ' =>
            rw [hb] at hev
            simp only [Res.bind_ok] at hev
            obtain ⟨entry, htbl, hcode⟩ := hT f fd hfd
            simp only [compileExpr] at hc
            have hcA := hc.append_left
            have hcC := hc.append_right
            simp only [compileFun, List.append_assoc] at hcode
            have hcS := hcode.append_left
            have hcR := hcode.append_right.append_left
            have hcRet := hcode.append_right.append_right
            have hk : vs.reverse.length = (fd.params.map (·.1)).length := by
              simp [hlen]
            refine (ihA _ _ _ _ _ _ hargs hcA).trans ?_
            have hstep := step_call (σ := vs.reverse ++ σ) (ρ := ρ) (F := F) hcC htbl
            rw [List.take_left' hk, List.drop_left' hk, List.reverse_reverse] at hstep
            refine (Reaches.single hstep).trans ?_
            refine (ihS _ _ _ _ _ _ hb hcS).trans ?_
            refine (ihE _ _ _ _ _ _ hev hcR).trans ?_
            exact (Reaches.single (step_ret hcRet)).cast rfl (by state_eq)
        · rename_i hne
          simp at hev
-- ANCHOR_END: simE

-- ANCHOR: simA
/-- 引数列：fuel を 1 進める。値は左から順に push される。 -/
theorem simA_succ {P : Prog} {vmP : VMProg} {n : Nat} (ih : SimAll P vmP n) :
    ∀ ρ es vs pc σ F, evalArgs P (n + 1) ρ es = .ok vs → CodeAt vmP.code pc (compileArgs es) →
      Reaches vmP ⟨pc, σ, ρ, F⟩ ⟨pc + (compileArgs es).length, vs.reverse ++ σ, ρ, F⟩ := by
  obtain ⟨ihE, ihA, _⟩ := ih
  intro ρ es vs pc σ F hev hc
  cases es with
  | nil =>
    simp only [evalArgs, Res.ok.injEq] at hev
    subst hev
    exact (Reaches.refl _ _).cast rfl (by state_eq)
  | cons e es =>
    simp only [evalArgs] at hev
    cases h₁ : evalE P n ρ e with
    | timeout => rw [h₁] at hev; simp at hev
    | err => rw [h₁] at hev; simp at hev
    | ok v =>
      rw [h₁] at hev
      simp only [Res.bind_ok] at hev
      cases h₂ : evalArgs P n ρ es with
      | timeout => rw [h₂] at hev; simp at hev
      | err => rw [h₂] at hev; simp at hev
      | ok vs' =>
        rw [h₂] at hev
        simp at hev
        subst hev
        simp only [compileArgs] at hc
        refine (ihE _ _ _ _ _ _ h₁ hc.append_left).trans ?_
        exact (ihA _ _ _ _ (v :: σ) _ h₂ hc.append_right).cast rfl (by state_eq)
-- ANCHOR_END: simA

end Simplean
