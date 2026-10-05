import Simplean.Correctness.Expr

/-!
# コンパイラ正当性（文とプログラム）

文のシミュレーション（if / while のジャンプ）、関数表の整合性、そして
プログラム全体の定理 `main_correct`。
-/

namespace Simplean

-- ANCHOR: simS
/-- 文：fuel を 1 進める。文の実行はスタックを変えない。 -/
theorem simS_succ {P : Prog} {vmP : VMProg} {n : Nat} (ih : SimAll P vmP n) :
    ∀ ρ s ρ' pc σ F, execS P (n + 1) ρ s = .ok ρ' → CodeAt vmP.code pc (compileStmt s) →
      Reaches vmP ⟨pc, σ, ρ, F⟩ ⟨pc + (compileStmt s).length, σ, ρ', F⟩ := by
  obtain ⟨ihE, _, ihS⟩ := ih
  intro ρ s ρ' pc σ F hex hc
  cases s with
  | skip =>
    simp only [execS, Res.ok.injEq] at hex
    subst hex
    exact (Reaches.refl _ _).cast rfl (by state_eq)
  | decl x t e =>
    simp only [execS] at hex
    cases h₁ : evalE P n ρ e with
    | timeout => rw [h₁] at hex; simp at hex
    | err => rw [h₁] at hex; simp at hex
    | ok v =>
      rw [h₁] at hex
      simp at hex
      subst hex
      simp only [compileStmt] at hc
      refine (ihE _ _ _ _ _ _ h₁ hc.append_left).trans ?_
      exact (Reaches.single (step_store hc.append_right)).cast rfl (by state_eq)
  | assign x e =>
    simp only [execS] at hex
    cases h₁ : evalE P n ρ e with
    | timeout => rw [h₁] at hex; simp at hex
    | err => rw [h₁] at hex; simp at hex
    | ok v =>
      rw [h₁] at hex
      simp at hex
      subst hex
      simp only [compileStmt] at hc
      refine (ihE _ _ _ _ _ _ h₁ hc.append_left).trans ?_
      exact (Reaches.single (step_store hc.append_right)).cast rfl (by state_eq)
  | seq s₁ s₂ =>
    simp only [execS] at hex
    cases h₁ : execS P n ρ s₁ with
    | timeout => rw [h₁] at hex; simp at hex
    | err => rw [h₁] at hex; simp at hex
    | ok ρ₁ =>
      rw [h₁] at hex
      simp only [Res.bind_ok] at hex
      simp only [compileStmt] at hc
      refine (ihS _ _ _ _ _ _ h₁ hc.append_left).trans ?_
      exact (ihS _ _ _ _ _ _ hex hc.append_right).cast rfl (by state_eq)
  | ite c s₁ s₂ =>
    simp only [execS] at hex
    cases h₁ : evalE P n ρ c with
    | timeout => rw [h₁] at hex; simp at hex
    | err => rw [h₁] at hex; simp at hex
    | ok v =>
      rw [h₁] at hex
      simp only [Res.bind_ok] at hex
      cases v with
      | str s => simp at hex
      | nil t => simp at hex
      | cons a b => simp at hex
      | int k =>
        dsimp only at hex
        simp only [compileStmt, List.append_assoc] at hc
        have hcC := hc.append_left
        have hcJz := hc.append_right.append_left
        have hc' := hc.append_right.append_right
        have hc₁ := hc'.append_left
        have hcJmp := hc'.append_right.append_left
        have hc₂ := hc'.append_right.append_right
        split at hex
        · rename_i hk
          subst hk
          refine (ihE _ _ _ _ _ _ h₁ hcC).trans ?_
          refine (Reaches.single (step_jz_zero hcJz)).trans ?_
          exact (ihS _ _ _ _ σ F hex hc₂).cast (by state_eq) (by state_eq)
        · rename_i hk
          refine (ihE _ _ _ _ _ _ h₁ hcC).trans ?_
          refine (Reaches.single (step_jz_nonzero hcJz hk)).trans ?_
          refine (ihS _ _ _ _ _ _ hex hc₁).trans ?_
          exact (Reaches.single (step_jmp hcJmp)).cast rfl (by state_eq)
  | «while» c body =>
    have hc₀ := hc
    simp only [execS] at hex
    cases h₁ : evalE P n ρ c with
    | timeout => rw [h₁] at hex; simp at hex
    | err => rw [h₁] at hex; simp at hex
    | ok v =>
      rw [h₁] at hex
      simp only [Res.bind_ok] at hex
      cases v with
      | str s => simp at hex
      | nil t => simp at hex
      | cons a b => simp at hex
      | int k =>
        dsimp only at hex
        simp only [compileStmt, List.append_assoc] at hc
        have hcC := hc.append_left
        have hcJz := hc.append_right.append_left
        have hc' := hc.append_right.append_right
        have hcB := hc'.append_left
        have hcJmp := hc'.append_right
        split at hex
        · rename_i hk
          subst hk
          simp at hex
          subst hex
          refine (ihE _ _ _ _ _ _ h₁ hcC).trans ?_
          exact (Reaches.single (step_jz_zero hcJz)).cast rfl (by state_eq)
        · rename_i hk
          cases hb : execS P n ρ body with
          | timeout => rw [hb] at hex; simp at hex
          | err => rw [hb] at hex; simp at hex
          | ok ρ₁ =>
            rw [hb] at hex
            simp only [Res.bind_ok] at hex
            refine (ihE _ _ _ _ _ _ h₁ hcC).trans ?_
            refine (Reaches.single (step_jz_nonzero hcJz hk)).trans ?_
            refine (ihS _ _ _ _ _ _ hb hcB).trans ?_
            refine (Reaches.single (step_jmp hcJmp)).trans ?_
            exact (ihS _ _ _ _ σ F hex hc₀).cast (by state_eq) rfl
-- ANCHOR_END: simS

-- ANCHOR: compile_correct
/-- コンパイラ正当性：任意の fuel で成り立つ。 -/
theorem compile_correct {P : Prog} {vmP : VMProg} (hT : TableOk P vmP) : ∀ n, SimAll P vmP n
  | 0 =>
    ⟨fun _ _ _ _ _ _ h => by simp [evalE] at h,
     fun _ _ _ _ _ _ h => by simp [evalArgs] at h,
     fun _ _ _ _ _ _ h => by simp [execS] at h⟩
  | n + 1 =>
    ⟨simE_succ hT (compile_correct hT n),
     simA_succ (compile_correct hT n),
     simS_succ (compile_correct hT n)⟩
-- ANCHOR_END: compile_correct

-- ANCHOR: tableok_proof
/-- `compileFuns` が作る関数表は、各関数の入口にその関数のコードを指す。 -/
theorem compileFuns_ok :
    ∀ (fds : List FunDef) (pos : Nat) (pre post : List Instr), pre.length = pos →
      ∀ f fd, fds.find? (fun fd => fd.name == f) = some fd →
        ∃ entry, AList.lookup (compileFuns fds pos).1 f = some ⟨entry, fd.params.map (·.1)⟩ ∧
          CodeAt (pre ++ (compileFuns fds pos).2 ++ post) entry (compileFun fd)
  | [], _, _, _, _, _, _, h => by simp at h
  | fd₀ :: fds, pos, pre, post, hpre, f, fd, h => by
    by_cases hname : fd₀.name = f
    · have heq : fd₀ = fd := by
        rw [List.find?_cons_of_pos (by simp [hname])] at h
        exact Option.some.inj h
      subst heq
      refine ⟨pos, ?_, ?_⟩
      · simp [compileFuns, hname]
      · exact ⟨pre, (compileFuns fds (pos + (compileFun fd₀).length)).2 ++ post,
          by simp [compileFuns], hpre⟩
    · have h' : fds.find? (fun fd => fd.name == f) = some fd := by
        rwa [List.find?_cons_of_neg (by simp [hname])] at h
      obtain ⟨entry, htbl, hcode⟩ :=
        compileFuns_ok fds (pos + (compileFun fd₀).length) (pre ++ compileFun fd₀) post
          (by simp [hpre]) f fd h'
      refine ⟨entry, ?_, ?_⟩
      · simp [compileFuns, hname, htbl]
      · simpa [compileFuns, List.append_assoc] using hcode

theorem compileProg_tableOk (P : Prog) : TableOk P (compileProg P) := by
  intro f fd hfd
  obtain ⟨entry, htbl, hcode⟩ :=
    compileFuns_ok P.funs (compileExpr P.main ++ [Instr.halt]).length (compileExpr P.main ++ [Instr.halt]) []
      rfl f fd hfd
  exact ⟨entry, htbl, by simpa [compileProg] using hcode⟩
-- ANCHOR_END: tableok_proof

-- ANCHOR: main_correct
/-- プログラム全体：参照意味論が `v` を返すなら、VM も `v` で停止する。 -/
theorem main_correct {P : Prog} {n : Nat} {v : Val} (h : evalProg P n = .ok v) :
    ∃ k, run (compileProg P) k VMState.init = some v := by
  have hcMain : CodeAt (compileProg P).code 0 (compileExpr P.main) :=
    ⟨[], [Instr.halt] ++ (compileFuns P.funs (compileExpr P.main ++ [Instr.halt]).length).2,
      by simp [compileProg], rfl⟩
  have hcHalt : CodeAt (compileProg P).code (compileExpr P.main).length [Instr.halt] :=
    ⟨compileExpr P.main, (compileFuns P.funs (compileExpr P.main ++ [Instr.halt]).length).2,
      by simp [compileProg], rfl⟩
  obtain ⟨k, hk⟩ := (compile_correct (compileProg_tableOk P) n).1 [] P.main v 0 [] [] h hcMain
  refine ⟨k + 1, ?_⟩
  show run (compileProg P) (k + 1) ⟨0, [], [], []⟩ = some v
  rw [run_of_stepN hk 1]
  simp only [Nat.zero_add]
  exact run_halt hcHalt.fetch
-- ANCHOR_END: main_correct

end Simplean
