import Simplean

/-!
# Ground truth for `scala/expected.txt`

Evaluates every example program with Lean's own `#eval` (reference
interpreter `evalProg`, type checker `checkProg`, and the compiled program on
the VM `run (compileProg P)`) and prints one line per program in exactly the
format `scala/Main.scala` prints. Regenerate with

```
lake env lean scripts/expected.lean > scala/expected.txt
```

Fuel values match `Simplean/Tests.lean` (interpreter) and `2000` steps for
the VM.
-/

namespace Simplean.Expected

open Simplean Simplean.Examples

def showTy : Ty → String
  | .int => "int"
  | .str => "str"
  | .list t => s!"list({showTy t})"

partial def listElems : Val → Option (List Val)
  | .nil _ => some []
  | .cons hd tl => (listElems tl).map (hd :: ·)
  | _ => none

partial def showVal (v : Val) : String :=
  match v with
  | .int n => toString n
  | .str s => "\"" ++ s ++ "\""
  | _ =>
    match listElems v with
    | some vs => "[" ++ ", ".intercalate (vs.map showVal) ++ "]"
    | none =>
      match v with
      | .cons hd tl => s!"cons({showVal hd}, {showVal tl})"
      | _ => "?"

def showRes : Res Val → String
  | .timeout => "timeout"
  | .err => "err"
  | .ok v => s!"ok({showVal v})"

def showOpt {α : Type} (f : α → String) : Option α → String
  | none => "None"
  | some a => s!"Some({f a})"

def line (name : String) (P : Prog) (fuel : Nat) : String :=
  s!"{name}: check={showOpt showTy (checkProg P)} eval={showRes (evalProg P fuel)} " ++
    s!"vm={showOpt showVal (run (compileProg P) 2000 .init)}"

def table : List (String × Prog × Nat) :=
  [("fact", factProg, 100), ("factRec", factRecProg, 200), ("fib", fibProg, 100),
   ("parity", parityProg, 200), ("sumRange", sumRangeProg, 100), ("reverse", reverseProg, 100),
   ("flatten", flattenProg, 200), ("str", strProg, 100),
   ("illAddStr", illAddStr, 10), ("illUndeclared", illUndeclared, 10),
   ("illRedecl", illRedecl, 10), ("illArity", illArity, 10)]

def render : String :=
  "\n".intercalate (table.map fun (n, P, fuel) => line n P fuel)

end Simplean.Expected

#eval IO.print (Simplean.Expected.render ++ "\n")
