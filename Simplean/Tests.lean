import Simplean.Examples
import Simplean.Compiler

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

end Simplean.Tests
