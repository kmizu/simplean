import Simplean.Semantics
import Simplean.Typing

/-!
# 型健全性

正しく型付けされたプログラムは、fuel が尽きることはあっても型エラー（`err`）にはならず、
値を返すならその値は予測された型を持つ。fuel に関する帰納法で示す。
-/

namespace Simplean

-- ANCHOR: envok
/-- 環境 `ρ` が文脈 `Γ` に適合する：`Γ` の各変数は `ρ` に束縛があり、その型の値を持つ。 -/
def EnvOk (Γ : Ctx) (ρ : Env) : Prop :=
  ∀ x t, AList.lookup Γ x = some t → ∃ v, AList.lookup ρ x = some v ∧ HasType v t
-- ANCHOR_END: envok

theorem EnvOk.empty : EnvOk [] [] := by
  intro x t hx; simp at hx

/-- 文脈を縮めても適合は保たれる。 -/
theorem EnvOk.mono {Γ Γ' : Ctx} {ρ : Env} (h : EnvOk Γ' ρ)
    (hsub : ∀ x t, AList.lookup Γ x = some t → AList.lookup Γ' x = some t) : EnvOk Γ ρ :=
  fun x t hx => h x t (hsub x t hx)

/-- 変数宣言：文脈と環境を同時に伸ばす。 -/
theorem EnvOk.update {Γ : Ctx} {ρ : Env} {x : String} {t : Ty} {v : Val}
    (h : EnvOk Γ ρ) (hv : HasType v t) : EnvOk (AList.update Γ x t) (AList.update ρ x v) := by
  intro y t' hy
  by_cases hxy : x = y
  · subst hxy
    rw [AList.lookup_update_self] at hy
    cases hy
    exact ⟨v, AList.lookup_update_self _ _ _, hv⟩
  · rw [AList.lookup_update_other _ _ _ _ hxy] at hy
    rw [AList.lookup_update_other _ _ _ _ hxy]
    exact h y t' hy

/-- 代入：文脈が持つ型の値で更新しても適合は保たれる。 -/
theorem EnvOk.assign {Γ : Ctx} {ρ : Env} {x : String} {t : Ty} {v : Val}
    (h : EnvOk Γ ρ) (hx : AList.lookup Γ x = some t) (hv : HasType v t) :
    EnvOk Γ (AList.update ρ x v) := by
  intro y t' hy
  by_cases hxy : x = y
  · subst hxy
    rw [hx] at hy
    cases hy
    exact ⟨v, AList.lookup_update_self _ _ _, hv⟩
  · rw [AList.lookup_update_other _ _ _ _ hxy]
    exact h y t' hy

/-- 引数の束縛：引数の値が引数の型を持てば、引数の文脈に適合する環境ができる。 -/
theorem EnvOk.bindParams : ∀ {ps : List (String × Ty)} {vs : List Val},
    HasTypes vs (ps.map (·.2)) → EnvOk ps (bindParams (ps.map (·.1)) vs)
  | [], _, _ => by
    intro x t hx; simp at hx
  | (y, t₀) :: ps, vs, h => by
    cases vs with
    | nil => simp only [List.map] at h; cases h
    | cons v vs =>
      simp only [List.map] at h
      cases h with
      | cons hv hvs =>
        intro x t hx
        simp only [List.map, bindParams_cons]
        by_cases hxy : y = x
        · subst hxy
          simp at hx
          subst hx
          exact ⟨v, by simp, hv⟩
        · simp only [AList.lookup_cons, hxy, ↓reduceIte] at hx ⊢
          exact EnvOk.bindParams hvs x t hx

-- ANCHOR: soundall
/-- fuel `n` までの健全性：式・引数列・文の三つを束ねた命題。 -/
def SoundAll (P : Prog) (n : Nat) : Prop :=
  (∀ Γ ρ e t, ExprTy P Γ e t → EnvOk Γ ρ → Res.Ok (HasType · t) (evalE P n ρ e)) ∧
  (∀ Γ ρ es ts, ArgsTy P Γ es ts → EnvOk Γ ρ → Res.Ok (HasTypes · ts) (evalArgs P n ρ es)) ∧
  (∀ Γ ρ s Γ', StmtTy P Γ s Γ' → EnvOk Γ ρ → Res.Ok (EnvOk Γ') (execS P n ρ s))
-- ANCHOR_END: soundall

-- ANCHOR: soundE
/-- 式：fuel を 1 進める。 -/
theorem soundE_succ {P : Prog} (hP : ProgOk P) {n : Nat} (ih : SoundAll P n) :
    ∀ Γ ρ e t, ExprTy P Γ e t → EnvOk Γ ρ → Res.Ok (HasType · t) (evalE P (n + 1) ρ e) := by
  obtain ⟨ihE, ihA, ihS⟩ := ih
  intro Γ ρ e t hT hρ
  cases hT with
  | lit n => simp [evalE]; constructor
  | strLit s => simp [evalE]; constructor
  | var hx =>
    obtain ⟨v, hv, hvt⟩ := hρ _ _ hx
    simp [evalE, hv]; exact hvt
  | nil t => simp [evalE]; constructor
  | unop he hop =>
    simp only [evalE]
    refine (ihE _ _ _ _ he hρ).bind fun v hv => ?_
    obtain ⟨v', hv', hvt⟩ := applyUn_sound hop hv
    exact Res.Ok.ofOption hv' hvt
  | binop he₁ he₂ hop =>
    simp only [evalE]
    refine (ihE _ _ _ _ he₁ hρ).bind fun v₁ hv₁ => ?_
    refine (ihE _ _ _ _ he₂ hρ).bind fun v₂ hv₂ => ?_
    obtain ⟨v, hv, hvt⟩ := applyBin_sound hop hv₁ hv₂
    exact Res.Ok.ofOption hv hvt
  | call hfd hargs =>
    simp only [evalE]
    refine (ihA _ _ _ _ hargs hρ).bind fun vs hvs => ?_
    rw [hfd]
    dsimp only
    have hlen : vs.length = _ := hvs.length_eq
    rw [List.length_map] at hlen
    split
    · obtain ⟨Γ', hbody, hres⟩ := hP _ (Prog.findFun_mem hfd)
      refine (ihS _ _ _ _ hbody (EnvOk.bindParams hvs)).bind fun ρ' hρ' => ?_
      exact ihE _ _ _ _ hres hρ'
    · rename_i hne
      exact absurd hlen hne
-- ANCHOR_END: soundE

/-- 引数列：fuel を 1 進める。 -/
theorem soundA_succ {P : Prog} {n : Nat} (ih : SoundAll P n) :
    ∀ Γ ρ es ts, ArgsTy P Γ es ts → EnvOk Γ ρ → Res.Ok (HasTypes · ts) (evalArgs P (n + 1) ρ es) := by
  obtain ⟨ihE, ihA, _⟩ := ih
  intro Γ ρ es ts hT hρ
  cases hT with
  | nil => simp [evalArgs]; constructor
  | cons he hes =>
    simp only [evalArgs]
    refine (ihE _ _ _ _ he hρ).bind fun v hv => ?_
    refine (ihA _ _ _ _ hes hρ).bind fun vs hvs => ?_
    simp only [Res.pure_eq, Res.Ok_ok]
    exact .cons hv hvs

-- ANCHOR: soundS
/-- 文：fuel を 1 進める。 -/
theorem soundS_succ {P : Prog} {n : Nat} (ih : SoundAll P n) :
    ∀ Γ ρ s Γ', StmtTy P Γ s Γ' → EnvOk Γ ρ → Res.Ok (EnvOk Γ') (execS P (n + 1) ρ s) := by
  obtain ⟨ihE, _, ihS⟩ := ih
  intro Γ ρ s Γ' hT hρ
  cases hT with
  | skip => simpa [execS] using hρ
  | decl hx he =>
    simp only [execS]
    refine (ihE _ _ _ _ he hρ).bind fun v hv => ?_
    simp only [Res.pure_eq, Res.Ok_ok]
    exact hρ.update hv
  | assign hx he =>
    simp only [execS]
    refine (ihE _ _ _ _ he hρ).bind fun v hv => ?_
    simp only [Res.pure_eq, Res.Ok_ok]
    exact hρ.assign hx hv
  | seq h₁ h₂ =>
    simp only [execS]
    refine (ihS _ _ _ _ h₁ hρ).bind fun ρ₁ hρ₁ => ?_
    exact ihS _ _ _ _ h₂ hρ₁
  | ite hc h₁ h₂ =>
    simp only [execS]
    refine (ihE _ _ _ _ hc hρ).bind fun v hv => ?_
    cases hv with
    | int k =>
      dsimp only
      split
      · exact (ihS _ _ _ _ h₂ hρ).mono fun ρ' hρ' => hρ'.mono (ctx_mono h₂)
      · exact (ihS _ _ _ _ h₁ hρ).mono fun ρ' hρ' => hρ'.mono (ctx_mono h₁)
  | «while» hc hb =>
    have hT₀ := StmtTy.while hc hb
    simp only [execS]
    refine (ihE _ _ _ _ hc hρ).bind fun v hv => ?_
    cases hv with
    | int k =>
      dsimp only
      split
      · simpa using hρ
      · refine (ihS _ _ _ _ hb hρ).bind fun ρ₁ hρ₁ => ?_
        exact ihS _ _ _ _ hT₀ (hρ₁.mono (ctx_mono hb))
-- ANCHOR_END: soundS

-- ANCHOR: soundness
/-- 型健全性：任意の fuel で成り立つ。 -/
theorem soundness {P : Prog} (hP : ProgOk P) : ∀ n, SoundAll P n
  | 0 =>
    ⟨fun _ _ _ _ _ _ => by simp [evalE],
     fun _ _ _ _ _ _ => by simp [evalArgs],
     fun _ _ _ _ _ _ => by simp [execS]⟩
  | n + 1 =>
    ⟨soundE_succ hP (soundness hP n),
     soundA_succ (soundness hP n),
     soundS_succ (soundness hP n)⟩
-- ANCHOR_END: soundness

-- ANCHOR: corollaries
/-- 正しく型付けされたプログラムは型エラーを起こさない。 -/
theorem evalProg_no_err {P : Prog} {t : Ty} (hP : ProgOk P) (hm : ExprTy P [] P.main t)
    (n : Nat) : evalProg P n ≠ .err := by
  have h := (soundness hP n).1 [] [] P.main t hm EnvOk.empty
  intro heq
  rw [evalProg] at heq
  rw [heq] at h
  simp at h

/-- 正しく型付けされたプログラムが値を返せば、その値は main の型を持つ。 -/
theorem evalProg_hasType {P : Prog} {t : Ty} {v : Val} (hP : ProgOk P)
    (hm : ExprTy P [] P.main t) {n : Nat} (h : evalProg P n = .ok v) : HasType v t := by
  have hs := (soundness hP n).1 [] [] P.main t hm EnvOk.empty
  rw [evalProg] at h
  rw [h] at hs
  simpa using hs
-- ANCHOR_END: corollaries

end Simplean
