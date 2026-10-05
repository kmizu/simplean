import Simplean.Soundness
import Simplean.Checker
import Simplean.Correctness.Stmt

/-!
# 決定性と統合定理

fuel を増やしても成功した結果は変わらない（単調性）。よって「ある fuel で値 `v` に評価される」
という意味論は部分関数であり、決定的。最後に型健全性とコンパイラ正当性を束ねる。
-/

namespace Simplean

-- ANCHOR: monoall
/-- fuel `n` での成功は fuel `n + 1` でも同じ結果になる（式・引数列・文）。 -/
def MonoAll (P : Prog) (n : Nat) : Prop :=
  (∀ ρ e v, evalE P n ρ e = .ok v → evalE P (n + 1) ρ e = .ok v) ∧
  (∀ ρ es vs, evalArgs P n ρ es = .ok vs → evalArgs P (n + 1) ρ es = .ok vs) ∧
  (∀ ρ s ρ', execS P n ρ s = .ok ρ' → execS P (n + 1) ρ s = .ok ρ')
-- ANCHOR_END: monoall

theorem monoE_succ {P : Prog} {n : Nat} (ih : MonoAll P n) :
    ∀ ρ e v, evalE P (n + 1) ρ e = .ok v → evalE P (n + 1 + 1) ρ e = .ok v := by
  obtain ⟨ihE, ihA, ihS⟩ := ih
  intro ρ e v h
  cases e with
  | lit k => simpa [evalE] using h
  | strLit s => simpa [evalE] using h
  | var x => simpa [evalE] using h
  | nil t => simpa [evalE] using h
  | unop op e₁ =>
    simp only [evalE] at h ⊢
    cases h₁ : evalE P n ρ e₁ with
    | timeout => rw [h₁] at h; simp at h
    | err => rw [h₁] at h; simp at h
    | ok v₁ =>
      rw [h₁] at h
      rw [ihE _ _ _ h₁]
      exact h
  | binop op e₁ e₂ =>
    simp only [evalE] at h ⊢
    cases h₁ : evalE P n ρ e₁ with
    | timeout => rw [h₁] at h; simp at h
    | err => rw [h₁] at h; simp at h
    | ok v₁ =>
      rw [h₁] at h
      rw [ihE _ _ _ h₁]
      simp only [Res.bind_ok] at h ⊢
      cases h₂ : evalE P n ρ e₂ with
      | timeout => rw [h₂] at h; simp at h
      | err => rw [h₂] at h; simp at h
      | ok v₂ =>
        rw [h₂] at h
        rw [ihE _ _ _ h₂]
        exact h
  | call f args =>
    simp only [evalE] at h ⊢
    cases hargs : evalArgs P n ρ args with
    | timeout => rw [hargs] at h; simp at h
    | err => rw [hargs] at h; simp at h
    | ok vs =>
      rw [hargs] at h
      rw [ihA _ _ _ hargs]
      simp only [Res.bind_ok] at h ⊢
      cases hfd : P.findFun f with
      | none => rw [hfd] at h; simp at h
      | some fd =>
        rw [hfd] at h
        dsimp only at h ⊢
        split at h
        · rename_i hlen
          split
          · cases hb : execS P n (bindParams (fd.params.map (·.1)) vs) fd.body with
            | timeout => rw [hb] at h; simp at h
            | err => rw [hb] at h; simp at h
            | ok ρ' =>
              rw [hb] at h
              rw [ihS _ _ _ hb]
              simp only [Res.bind_ok] at h ⊢
              exact ihE _ _ _ h
          · rename_i hne
            exact absurd hlen hne
        · simp at h

theorem monoA_succ {P : Prog} {n : Nat} (ih : MonoAll P n) :
    ∀ ρ es vs, evalArgs P (n + 1) ρ es = .ok vs → evalArgs P (n + 1 + 1) ρ es = .ok vs := by
  obtain ⟨ihE, ihA, _⟩ := ih
  intro ρ es vs h
  cases es with
  | nil => simpa [evalArgs] using h
  | cons e es =>
    simp only [evalArgs] at h ⊢
    cases h₁ : evalE P n ρ e with
    | timeout => rw [h₁] at h; simp at h
    | err => rw [h₁] at h; simp at h
    | ok v =>
      rw [h₁] at h
      rw [ihE _ _ _ h₁]
      simp only [Res.bind_ok] at h ⊢
      cases h₂ : evalArgs P n ρ es with
      | timeout => rw [h₂] at h; simp at h
      | err => rw [h₂] at h; simp at h
      | ok vs' =>
        rw [h₂] at h
        rw [ihA _ _ _ h₂]
        exact h

theorem monoS_succ {P : Prog} {n : Nat} (ih : MonoAll P n) :
    ∀ ρ s ρ', execS P (n + 1) ρ s = .ok ρ' → execS P (n + 1 + 1) ρ s = .ok ρ' := by
  obtain ⟨ihE, _, ihS⟩ := ih
  intro ρ s ρ' h
  cases s with
  | skip => simpa [execS] using h
  | decl x t e =>
    simp only [execS] at h ⊢
    cases h₁ : evalE P n ρ e with
    | timeout => rw [h₁] at h; simp at h
    | err => rw [h₁] at h; simp at h
    | ok v =>
      rw [h₁] at h
      rw [ihE _ _ _ h₁]
      exact h
  | assign x e =>
    simp only [execS] at h ⊢
    cases h₁ : evalE P n ρ e with
    | timeout => rw [h₁] at h; simp at h
    | err => rw [h₁] at h; simp at h
    | ok v =>
      rw [h₁] at h
      rw [ihE _ _ _ h₁]
      exact h
  | seq s₁ s₂ =>
    simp only [execS] at h ⊢
    cases h₁ : execS P n ρ s₁ with
    | timeout => rw [h₁] at h; simp at h
    | err => rw [h₁] at h; simp at h
    | ok ρ₁ =>
      rw [h₁] at h
      rw [ihS _ _ _ h₁]
      simp only [Res.bind_ok] at h ⊢
      exact ihS _ _ _ h
  | ite c s₁ s₂ =>
    simp only [execS] at h ⊢
    cases h₁ : evalE P n ρ c with
    | timeout => rw [h₁] at h; simp at h
    | err => rw [h₁] at h; simp at h
    | ok v =>
      rw [h₁] at h
      rw [ihE _ _ _ h₁]
      simp only [Res.bind_ok] at h ⊢
      cases v with
      | str s => simp at h
      | nil t => simp at h
      | cons a b => simp at h
      | int k =>
        dsimp only at h ⊢
        split at h
        · rename_i hk
          split
          · exact ihS _ _ _ h
          · rename_i hk'; exact absurd hk hk'
        · rename_i hk
          split
          · rename_i hk'; exact absurd hk' hk
          · exact ihS _ _ _ h
  | «while» c body =>
    simp only [execS] at h ⊢
    cases h₁ : evalE P n ρ c with
    | timeout => rw [h₁] at h; simp at h
    | err => rw [h₁] at h; simp at h
    | ok v =>
      rw [h₁] at h
      rw [ihE _ _ _ h₁]
      simp only [Res.bind_ok] at h ⊢
      cases v with
      | str s => simp at h
      | nil t => simp at h
      | cons a b => simp at h
      | int k =>
        dsimp only at h ⊢
        split at h
        · rename_i hk
          split
          · exact h
          · rename_i hk'; exact absurd hk hk'
        · rename_i hk
          split
          · rename_i hk'; exact absurd hk' hk
          · cases hb : execS P n ρ body with
            | timeout => rw [hb] at h; simp at h
            | err => rw [hb] at h; simp at h
            | ok ρ₁ =>
              rw [hb] at h
              rw [ihS _ _ _ hb]
              simp only [Res.bind_ok] at h ⊢
              exact ihS _ _ _ h

-- ANCHOR: fuel_mono
/-- fuel 単調性：任意の fuel で成り立つ。 -/
theorem fuel_mono (P : Prog) : ∀ n, MonoAll P n
  | 0 =>
    ⟨fun _ _ _ h => by simp [evalE] at h,
     fun _ _ _ h => by simp [evalArgs] at h,
     fun _ _ _ h => by simp [execS] at h⟩
  | n + 1 =>
    ⟨monoE_succ (fuel_mono P n), monoA_succ (fuel_mono P n), monoS_succ (fuel_mono P n)⟩

theorem evalE_mono {P : Prog} {ρ : Env} {e : Expr} {v : Val} {n m : Nat} (hnm : n ≤ m)
    (h : evalE P n ρ e = .ok v) : evalE P m ρ e = .ok v := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact (fuel_mono P _).1 _ _ _ ih
-- ANCHOR_END: fuel_mono

-- ANCHOR: det
/-- 決定性：fuel の与え方が違っても、成功した結果は一致する。 -/
theorem evalE_det {P : Prog} {ρ : Env} {e : Expr} {v v' : Val} {n m : Nat}
    (h : evalE P n ρ e = .ok v) (h' : evalE P m ρ e = .ok v') : v = v' := by
  have h₁ := evalE_mono (Nat.le_max_left n m) h
  have h₂ := evalE_mono (Nat.le_max_right n m) h'
  rw [h₁] at h₂
  cases h₂
  rfl

theorem evalProg_det {P : Prog} {v v' : Val} {n m : Nat}
    (h : evalProg P n = .ok v) (h' : evalProg P m = .ok v') : v = v' :=
  evalE_det h h'
-- ANCHOR_END: det

-- ANCHOR: final
/-- 統合定理：正しく型付けされたプログラムが値を返すなら、その値は main の型を持ち、
コンパイルして VM で実行しても同じ値で停止する。 -/
theorem final {P : Prog} {t : Ty} {n : Nat} {v : Val} (hP : ProgOk P)
    (hm : ExprTy P [] P.main t) (h : evalProg P n = .ok v) :
    HasType v t ∧ ∃ k, run (compileProg P) k VMState.init = some v :=
  ⟨evalProg_hasType hP hm h, main_correct h⟩

/-- VM がどんな fuel で何を返しても、それは参照意味論の結果と一致する（停止する実行について）。 -/
theorem vm_result_unique {P : Prog} {n k : Nat} {v v' : Val} (h : evalProg P n = .ok v)
    (hvm : run (compileProg P) k VMState.init = some v') : v' = v := by
  obtain ⟨k', hk'⟩ := main_correct h
  exact run_det hvm hk'

/-- 型検査器を通ったプログラムについての版。 -/
theorem final_checked {P : Prog} {t : Ty} {n : Nat} {v : Val} (hc : checkProg P = some t)
    (h : evalProg P n = .ok v) :
    HasType v t ∧ ∃ k, run (compileProg P) k VMState.init = some v :=
  final (checkProg_sound hc).1 (checkProg_sound hc).2 h
-- ANCHOR_END: final

end Simplean
