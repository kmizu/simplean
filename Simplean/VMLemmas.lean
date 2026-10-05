import Simplean.Compiler

/-!
# VM の補題

到達可能性 `Reaches`、コード配置 `CodeAt`、命令ごとの 1 ステップ補題、
`run` の単調性と決定性。コンパイラ正当性の証明の道具箱。
-/

namespace Simplean

-- ANCHOR: reaches
/-- 状態 `s` から有限ステップで `s'` に到達する。 -/
def Reaches (vmP : VMProg) (s s' : VMState) : Prop := ∃ k, stepN vmP k s = some s'

theorem stepN_add (vmP : VMProg) (k₁ k₂ : Nat) (s : VMState) :
    stepN vmP (k₁ + k₂) s = (stepN vmP k₁ s >>= stepN vmP k₂) := by
  induction k₁ generalizing s with
  | zero => simp [stepN]
  | succ k ih =>
    rw [Nat.succ_add]
    simp only [stepN]
    cases step vmP s with
    | none => simp
    | some s' => simp [ih]

theorem Reaches.refl (vmP : VMProg) (s : VMState) : Reaches vmP s s := ⟨0, rfl⟩

theorem Reaches.trans {vmP : VMProg} {s₁ s₂ s₃ : VMState}
    (h₁ : Reaches vmP s₁ s₂) (h₂ : Reaches vmP s₂ s₃) : Reaches vmP s₁ s₃ := by
  obtain ⟨k₁, h₁⟩ := h₁
  obtain ⟨k₂, h₂⟩ := h₂
  exact ⟨k₁ + k₂, by rw [stepN_add, h₁]; simpa using h₂⟩

theorem Reaches.single {vmP : VMProg} {s s' : VMState} (h : step vmP s = some s') :
    Reaches vmP s s' :=
  ⟨1, by simp [stepN, h]⟩

/-- 始点と終点を等しい状態に書き換える。 -/
theorem Reaches.cast {vmP : VMProg} {s₀ s₀' s₁ s₁' : VMState} (h : Reaches vmP s₀ s₁)
    (h₀ : s₀ = s₀') (h₁ : s₁ = s₁') : Reaches vmP s₀' s₁' := by
  subst h₀ h₁; exact h
-- ANCHOR_END: reaches

-- ANCHOR: codeat
/-- 命令列 `c` がコード `C` の番地 `pc` から置かれている。 -/
def CodeAt (C : List Instr) (pc : Nat) (c : List Instr) : Prop :=
  ∃ pre post, C = pre ++ c ++ post ∧ pre.length = pc

theorem CodeAt.fetch {C : List Instr} {pc : Nat} {i : Instr} {c : List Instr}
    (h : CodeAt C pc (i :: c)) : C[pc]? = some i := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  simp

theorem CodeAt.append_left {C : List Instr} {pc : Nat} {c₁ c₂ : List Instr}
    (h : CodeAt C pc (c₁ ++ c₂)) : CodeAt C pc c₁ := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact ⟨pre, c₂ ++ post, by simp, rfl⟩

theorem CodeAt.append_right {C : List Instr} {pc : Nat} {c₁ c₂ : List Instr}
    (h : CodeAt C pc (c₁ ++ c₂)) : CodeAt C (pc + c₁.length) c₂ := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact ⟨pre ++ c₁, post, by simp, by simp⟩

theorem CodeAt.cast {C : List Instr} {pc pc' : Nat} {c : List Instr}
    (h : CodeAt C pc c) (hpc : pc = pc') : CodeAt C pc' c := by
  subst hpc; exact h
-- ANCHOR_END: codeat

-- ANCHOR: step_lemmas
theorem step_push {vmP : VMProg} {pc : Nat} {σ : List Val} {ρ : Env} {F : List Frame} {v : Val}
    (h : CodeAt vmP.code pc [.push v]) :
    step vmP ⟨pc, σ, ρ, F⟩ = some ⟨pc + 1, v :: σ, ρ, F⟩ := by
  simp [step, h.fetch]

theorem step_load {vmP : VMProg} {pc : Nat} {σ : List Val} {ρ : Env} {F : List Frame}
    {x : String} {v : Val} (h : CodeAt vmP.code pc [.load x]) (hv : AList.lookup ρ x = some v) :
    step vmP ⟨pc, σ, ρ, F⟩ = some ⟨pc + 1, v :: σ, ρ, F⟩ := by
  simp [step, h.fetch, hv]

theorem step_store {vmP : VMProg} {pc : Nat} {σ : List Val} {ρ : Env} {F : List Frame}
    {x : String} {v : Val} (h : CodeAt vmP.code pc [.store x]) :
    step vmP ⟨pc, v :: σ, ρ, F⟩ = some ⟨pc + 1, σ, AList.update ρ x v, F⟩ := by
  simp [step, h.fetch]

theorem step_unop {vmP : VMProg} {pc : Nat} {σ : List Val} {ρ : Env} {F : List Frame}
    {op : UnOp} {v w : Val} (h : CodeAt vmP.code pc [.unop op]) (hw : applyUn op v = some w) :
    step vmP ⟨pc, v :: σ, ρ, F⟩ = some ⟨pc + 1, w :: σ, ρ, F⟩ := by
  simp [step, h.fetch, hw]

theorem step_binop {vmP : VMProg} {pc : Nat} {σ : List Val} {ρ : Env} {F : List Frame}
    {op : BinOp} {v₁ v₂ w : Val} (h : CodeAt vmP.code pc [.binop op])
    (hw : applyBin op v₁ v₂ = some w) :
    step vmP ⟨pc, v₂ :: v₁ :: σ, ρ, F⟩ = some ⟨pc + 1, w :: σ, ρ, F⟩ := by
  simp [step, h.fetch, hw]

theorem step_jmp {vmP : VMProg} {pc : Nat} {σ : List Val} {ρ : Env} {F : List Frame} {ofs : Int}
    (h : CodeAt vmP.code pc [.jmp ofs]) :
    step vmP ⟨pc, σ, ρ, F⟩ = some ⟨jumpTarget pc ofs, σ, ρ, F⟩ := by
  simp [step, h.fetch]

theorem step_jz_zero {vmP : VMProg} {pc : Nat} {σ : List Val} {ρ : Env} {F : List Frame}
    {ofs : Int} (h : CodeAt vmP.code pc [.jz ofs]) :
    step vmP ⟨pc, .int 0 :: σ, ρ, F⟩ = some ⟨jumpTarget pc ofs, σ, ρ, F⟩ := by
  simp [step, h.fetch]

theorem step_jz_nonzero {vmP : VMProg} {pc : Nat} {σ : List Val} {ρ : Env} {F : List Frame}
    {ofs : Int} {k : Int} (h : CodeAt vmP.code pc [.jz ofs]) (hk : k ≠ 0) :
    step vmP ⟨pc, .int k :: σ, ρ, F⟩ = some ⟨pc + 1, σ, ρ, F⟩ := by
  simp [step, h.fetch, hk]

theorem step_call {vmP : VMProg} {pc : Nat} {σ : List Val} {ρ : Env} {F : List Frame}
    {f : String} {entry : Nat} {params : List String} (h : CodeAt vmP.code pc [.call f])
    (hf : AList.lookup vmP.table f = some ⟨entry, params⟩) :
    step vmP ⟨pc, σ, ρ, F⟩ =
      some ⟨entry, σ.drop params.length, bindParams params (σ.take params.length).reverse,
            ⟨pc + 1, ρ⟩ :: F⟩ := by
  simp [step, h.fetch, hf]

theorem step_ret {vmP : VMProg} {pc : Nat} {σ : List Val} {ρ : Env} {F : List Frame}
    {v : Val} {fr : Frame} (h : CodeAt vmP.code pc [.ret]) :
    step vmP ⟨pc, v :: σ, ρ, fr :: F⟩ = some ⟨fr.retPc, v :: σ, fr.locals, F⟩ := by
  simp [step, h.fetch]
-- ANCHOR_END: step_lemmas

-- ANCHOR: run_lemmas
theorem step_eq_none_of_halt {vmP : VMProg} {s : VMState} (h : vmP.code[s.pc]? = some .halt) :
    step vmP s = none := by
  simp [step, h]

theorem not_halt_of_step {vmP : VMProg} {s s₁ : VMState} (hs : step vmP s = some s₁) :
    vmP.code[s.pc]? ≠ some .halt := by
  intro h
  rw [step_eq_none_of_halt h] at hs
  cases hs

/-- 1 ステップ進めても `run` の結果は変わらない。 -/
theorem run_succ_of_step {vmP : VMProg} {s s₁ : VMState} {n : Nat} (hs : step vmP s = some s₁) :
    run vmP (n + 1) s = run vmP n s₁ := by
  rw [run, ite_eq_right_of_eq_false _ _ (eq_false (not_halt_of_step hs)), hs]
  rfl

theorem run_of_stepN {vmP : VMProg} :
    ∀ {k : Nat} {s s' : VMState}, stepN vmP k s = some s' → ∀ j, run vmP (k + j) s = run vmP j s'
  | 0, s, s', h, j => by
    simp [stepN] at h
    subst h
    simp
  | k + 1, s, s', h, j => by
    simp only [stepN] at h
    cases hs : step vmP s with
    | none => rw [hs] at h; simp at h
    | some s₁ =>
      rw [hs] at h
      simp at h
      rw [show k + 1 + j = (k + j) + 1 by omega, run_succ_of_step hs]
      exact run_of_stepN h j

theorem run_of_reaches {vmP : VMProg} {s s' : VMState} (h : Reaches vmP s s') (j : Nat) :
    ∃ k, run vmP k s = run vmP j s' := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + j, run_of_stepN hk j⟩

theorem run_halt {vmP : VMProg} {pc : Nat} {σ : List Val} {ρ : Env} {F : List Frame} {v : Val}
    (h : vmP.code[pc]? = some .halt) : run vmP 1 ⟨pc, v :: σ, ρ, F⟩ = some v := by
  rw [run, ite_eq_left_of_eq_true _ _ (eq_true h)]
  rfl

/-- fuel を増やしても成功した結果は変わらない。 -/
theorem run_mono {vmP : VMProg} :
    ∀ {k : Nat} {s : VMState} {v : Val}, run vmP k s = some v → run vmP (k + 1) s = some v
  | 0, s, v, h => by simp [run] at h
  | k + 1, s, v, h => by
    by_cases hh : vmP.code[s.pc]? = some .halt
    · rw [run, ite_eq_left_of_eq_true _ _ (eq_true hh)] at h
      rw [run, ite_eq_left_of_eq_true _ _ (eq_true hh)]
      exact h
    · cases hs : step vmP s with
      | none =>
        rw [run, ite_eq_right_of_eq_false _ _ (eq_false hh), hs] at h
        change none = some v at h
        cases h
      | some s₁ =>
        rw [run_succ_of_step hs] at h
        rw [run_succ_of_step hs]
        exact run_mono h

theorem run_le {vmP : VMProg} {k k' : Nat} {s : VMState} {v : Val} (hk : k ≤ k')
    (h : run vmP k s = some v) : run vmP k' s = some v := by
  induction hk with
  | refl => exact h
  | step _ ih => exact run_mono ih

/-- VM の結果は fuel の与え方に依らない（決定性）。 -/
theorem run_det {vmP : VMProg} {s : VMState} {k k' : Nat} {v v' : Val}
    (h : run vmP k s = some v) (h' : run vmP k' s = some v') : v = v' := by
  have h₁ := run_le (Nat.le_max_left k k') h
  have h₂ := run_le (Nat.le_max_right k k') h'
  rw [h₁] at h₂
  cases h₂
  rfl
-- ANCHOR_END: run_lemmas

/-- VM 状態の等式を、長さ計算とジャンプ先の算術で閉じる。 -/
macro "state_eq" : tactic =>
  `(tactic| ((try simp only [VMState.mk.injEq, jumpTarget, List.length_append, List.length_singleton,
      List.length_cons, List.length_nil, List.reverse_cons, List.reverse_nil, List.append_assoc,
      List.singleton_append, List.cons_append, List.nil_append, List.append_nil,
      compileStmt, compileExpr, compileArgs, compileFun, eq_self_iff_true, and_true, true_and,
      and_self]); (try omega)))

end Simplean
