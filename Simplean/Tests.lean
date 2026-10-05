import Simplean.Examples
import Simplean.Compiler
import Simplean.Determinism

/-!
# テスト

`decide` で参照意味論の結果を機械検査する。名前付き定理にしておくと
`#print axioms` で使った公理を確認できる。
-/

namespace Simplean.Tests

open Simplean.Examples

-- ANCHOR: eval_tests
theorem fact_eval : evalProg factProg 100 = .ok (.int 3628800) := by decide
theorem factRec_eval : evalProg factRecProg 200 = .ok (.int 3628800) := by decide
theorem fib_eval : evalProg fibProg 100 = .ok (.int 6765) := by decide
theorem parity_eval : evalProg parityProg 200 = .ok (.int 1) := by decide
theorem sumRange_eval : evalProg sumRangeProg 100 = .ok (.int 45) := by decide
theorem reverse_eval :
    evalProg reverseProg 100 = .ok (.cons (.int 3) (.cons (.int 2) (.cons (.int 1) (.nil .int)))) := by
  decide
theorem flatten_eval :
    evalProg flattenProg 200 = .ok (.cons (.int 1) (.cons (.int 2) (.cons (.int 3) (.nil .int)))) := by
  decide
theorem str_eval : evalProg strProg 100 = .ok (.str "ababab120") := by decide
-- ANCHOR_END: eval_tests

/-- 型の合わないプログラムは実行時に `err` になる（定理が排除するのはこの状況）。 -/
theorem illAddStr_eval : evalProg illAddStr 10 = .err := by decide
theorem illUndeclared_eval : evalProg illUndeclared 10 = .err := by decide
theorem illArity_eval : evalProg illArity 10 = .err := by decide

-- ANCHOR: vm_tests
/-- コンパイルして VM で走らせても同じ結果になる。 -/
theorem fact_vm : run (compileProg factProg) 2000 .init = some (.int 3628800) := by decide +kernel
theorem factRec_vm : run (compileProg factRecProg) 2000 .init = some (.int 3628800) := by decide +kernel
theorem fib_vm : run (compileProg fibProg) 2000 .init = some (.int 6765) := by decide +kernel
theorem parity_vm : run (compileProg parityProg) 2000 .init = some (.int 1) := by decide +kernel
theorem sumRange_vm : run (compileProg sumRangeProg) 2000 .init = some (.int 45) := by decide +kernel
theorem reverse_vm :
    run (compileProg reverseProg) 2000 .init
      = some (.cons (.int 3) (.cons (.int 2) (.cons (.int 1) (.nil .int)))) := by
  decide +kernel
theorem flatten_vm :
    run (compileProg flattenProg) 2000 .init
      = some (.cons (.int 1) (.cons (.int 2) (.cons (.int 3) (.nil .int)))) := by
  decide +kernel
theorem str_vm : run (compileProg strProg) 2000 .init = some (.str "ababab120") := by decide +kernel
-- ANCHOR_END: vm_tests

-- ANCHOR: checker_tests
/-- 型検査器：正しいプログラムは main の型を返し、不正なプログラムは拒否する。 -/
theorem fact_check : checkProg factProg = some .int := by decide
theorem flatten_check : checkProg flattenProg = some (.list .int) := by decide
theorem str_check : checkProg strProg = some .str := by decide
theorem illAddStr_check : checkProg illAddStr = none := by decide
theorem illUndeclared_check : checkProg illUndeclared = none := by decide
theorem illRedecl_check : checkProg illRedecl = none := by decide
theorem illArity_check : checkProg illArity = none := by decide
-- ANCHOR_END: checker_tests

-- ANCHOR: hastype_example
/-- `[1]` は `List[Int]` を持つ：規則を下から上へたどった証明。 -/
example : HasType (.cons (.int 1) (.nil .int)) (.list .int) :=
  .cons (.int 1) (.nil .int)
-- ANCHOR_END: hastype_example

-- ANCHOR: final_example
/-- 階乗プログラムについての完全な保証：型検査を `decide` で、評価結果をテストの定理で渡す。 -/
example : HasType (.int 3628800) .int ∧
    ∃ k, run (compileProg factProg) k VMState.init = some (.int 3628800) :=
  final_checked fact_check fact_eval
-- ANCHOR_END: final_example

-- ANCHOR: axioms
/-! ## 使った公理の確認

`#print axioms` の出力を `#guard_msgs` で固定する。`sorryAx` や `Lean.ofReduceBool` が
混ざればビルドが失敗する。 -/

/-- info: 'Simplean.soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms soundness

/-- info: 'Simplean.checkProg_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkProg_sound

/-- info: 'Simplean.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compile_correct

/-- info: 'Simplean.main_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms main_correct

/-- info: 'Simplean.evalProg_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evalProg_det

/-- info: 'Simplean.final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms final

/-- info: 'Simplean.final_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms final_checked

/-- info: 'Simplean.vm_result_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vm_result_unique

/-- info: 'Simplean.Tests.fact_vm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fact_vm
-- ANCHOR_END: axioms

end Simplean.Tests
