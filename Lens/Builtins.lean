import Lean
import Lens.Core

/-!
# Builtin mapping tables (the hand-audited part of the TCB)

Maps a *minimal* whitelist of Lean core constants onto Scala equivalents.
Everything else our code touches is either extracted as an ordinary decl or
rejected fail-loud. Semantics pinned empirically against `#eval` on the pinned
toolchain (v4.34.1; see `scripts/scala-check.sh` for the differential test):

- `Nat` subtraction truncates; `Nat`/`Int` division/modulo by zero = 0 / identity
- `Int` default `/`, `%` are **Euclidean** (`ediv`/`emod`) — remainder ≥ 0.
  Scala `BigInt` `/`/`%` are T-division, so these go through `RT.intDiv`/`RT.intMod`.
- `Int.toNat` clamps negatives to `0`; `Nat.cast : Nat → Int` is the identity at `BigInt`.
- `String.length` counts Unicode scalars (`RT.strLength`), not UTF-16 units.
- `List.take`/`drop`/`getElem?` take `Nat` (BigInt) indices (`RT.listTake` etc.).
-/

namespace Lens.Builtins

open Lean

/-- Coarse type discriminator for dispatching heterogeneous ops. -/
inductive Kind where
  | nat | int | str | bool | char | list | option | other
  deriving Inhabited, BEq

def kindOf (t : Expr) : Kind :=
  match t.consumeMData.getAppFn with
  | .const ``Nat _ => .nat
  | .const ``Int _ => .int
  | .const ``String _ => .str
  | .const ``Bool _ => .bool
  | .const ``Char _ => .char
  | .const ``List _ => .list
  | .const ``Option _ => .option
  | _ => .other

/-- Heterogeneous-operator entry: `arity` counts ALL elaborated args
(type + instance + value); `typeArgIdx` is dispatched on; `valueArgs` are the
argument positions that become Scala operands. -/
structure OpEntry where
  arity : Nat
  typeArgIdx : Nat
  valueArgs : List Nat
  key : Kind → Option String
  /-- Position of the elaborated instance argument, validated against
  `canonicalInsts` (review finding: dispatch must not be instance-blind —
  a custom `HAdd Nat Nat Nat` instance must NOT silently get `+`). -/
  instArgIdx : Option Nat := none

/-- `HAdd.hAdd : {α β γ} → [inst] → α → β → γ` and friends. -/
def hetBinOp (key : Kind → Option String) : OpEntry :=
  { arity := 6, typeArgIdx := 0, valueArgs := [4, 5], key, instArgIdx := some 3 }

/-- Plain `Nat.add : Nat → Nat → Nat`-style entry (no instance argument). -/
def monoBinOp (k : String) : OpEntry :=
  { arity := 2, typeArgIdx := 0, valueArgs := [0, 1], key := fun _ => some k }

/-- Plain unary `Int.toNat : Int → Nat`-style entry. -/
def monoUnOp (k : String) : OpEntry :=
  { arity := 1, typeArgIdx := 0, valueArgs := [0], key := fun _ => some k }

/-- `List.f : {α} → List α → …` with `n` value arguments (no instance). -/
def polyOp (nTypes nVals : Nat) (k : String) : OpEntry :=
  { arity := nTypes + nVals, typeArgIdx := 0,
    valueArgs := (List.range nVals).map (· + nTypes), key := fun _ => some k }

/-- Constants allowed to appear inside a whitelisted operator's instance
argument (canonical core instances only; names probed against v4.34.1). -/
def canonicalInsts : List Name :=
  [``instHAdd, ``instHSub, ``instHMul, ``instHDiv, ``instHMod,
   ``instHAppendOfAppend,
   ``instAddNat, ``instSubNat, ``instMulNat, ``Nat.instDiv, ``Nat.instMod,
   ``Int.instAdd, ``Int.instSub, ``Int.instMul, ``Int.instDiv, ``Int.instMod,
   ``Int.instNegInt, ``instAppendString, ``List.instAppend, ``List,
   ``instOfNatNat, ``instOfNat,
   ``Monad.toBind, ``Applicative.toPure, ``Monad.toApplicative, ``Except.instMonad, ``Except,
   ``instBEqOfDecidableEq, ``instDecidableEqNat, ``instDecidableEqBool,
   ``instDecidableEqString, ``Int.instDecidableEq, ``Nat.decEq,
   ``instLTNat, ``instLENat, ``Int.instLTInt, ``Int.instLEInt,
   ``instNatCastInt, ``instToStringInt, ``instToStringNat, ``instToStringString,
   ``List.instGetElem?NatLtLength,
   ``Nat, ``Int, ``String, ``Bool, ``Char, ``OfNat]

/-- An instance term is canonical when every constant it mentions is either
a whitelisted core instance or a mere TYPE (inductive/ctor — instance terms
carry type arguments like `List Instr`, and user types there are harmless;
what must never appear is an unknown instance FUNCTION). -/
def isCanonicalInst (env : Lean.Environment) (e : Lean.Expr) : Bool :=
  e.getUsedConstants.all fun n =>
    canonicalInsts.contains n ||
    (match env.find? n with
     | some (.inductInfo _) | some (.ctorInfo _) => true
     | _ => false)

/-- `BEq` instance heads that are structural whenever their component
instances are (`a == b` ↔ `a = b`). `DecidableEq`-typed constants are accepted
by type, not by name (see `Translate.isStructuralBEqInst`). -/
def structuralBEqInsts : List Name :=
  [``instBEqOfDecidableEq, ``Option.instBEq, ``List.instBEq, ``instBEqProd]

def opTable : List (Name × OpEntry) :=
  [ (``HAdd.hAdd, hetBinOp fun | .nat | .int => some "add" | _ => none),
    (``HSub.hSub, hetBinOp fun | .nat => some "natSub" | .int => some "sub" | _ => none),
    (``HMul.hMul, hetBinOp fun | .nat | .int => some "mul" | _ => none),
    (``HDiv.hDiv, hetBinOp fun | .nat => some "natDiv" | .int => some "intDiv" | _ => none),
    (``HMod.hMod, hetBinOp fun | .nat => some "natMod" | .int => some "intMod" | _ => none),
    (``HAppend.hAppend, hetBinOp fun | .str => some "strAppend" | .list => some "listAppend" | _ => none),
    (``Neg.neg, { arity := 3, typeArgIdx := 0, valueArgs := [2],
                  key := fun | .int => some "neg" | _ => none,
                  instArgIdx := some 1 }),
    (``Nat.add, monoBinOp "add"), (``Nat.mul, monoBinOp "mul"),
    (``Nat.sub, monoBinOp "natSub"), (``Nat.div, monoBinOp "natDiv"),
    (``Nat.mod, monoBinOp "natMod"),
    (``Int.add, monoBinOp "add"), (``Int.mul, monoBinOp "mul"),
    (``Int.sub, monoBinOp "sub"), (``Int.neg, monoUnOp "neg"),
    (``Int.ediv, monoBinOp "intDiv"), (``Int.emod, monoBinOp "intMod"),
    (``String.append, monoBinOp "strAppend"),
    (``Nat.beq, monoBinOp "eq"), (``Nat.blt, monoBinOp "lt"), (``Nat.ble, monoBinOp "le"),
    (``Int.natAbs, monoUnOp "intAbs"),
    (``Nat.repr, monoUnOp "toStr"),
    (``Int.repr, monoUnOp "toStr"),
    -- `↑n : Int` — identity at the BigInt level.
    (``Nat.cast, { arity := 3, typeArgIdx := 0, valueArgs := [2],
                   key := fun | .int | .nat => some "intOfNat" | _ => none, instArgIdx := some 1 }),
    (``NatCast.natCast, { arity := 3, typeArgIdx := 0, valueArgs := [2],
                          key := fun | .int | .nat => some "intOfNat" | _ => none, instArgIdx := some 1 }),
    (``Int.toNat, monoUnOp "intToNat"),
    (``ToString.toString, { arity := 3, typeArgIdx := 0, valueArgs := [2],
                            key := fun | .int | .nat => some "toStr" | .str => some "idStr" | _ => none,
                            instArgIdx := some 1 }),
    (``String.length, monoUnOp "strLength"),
    -- Char is represented as a BigInt codepoint, so toNat is the identity.
    (``Char.toNat, monoUnOp "charToNat"),
    (``String.toList, monoUnOp "stringToList"),
    (``String.ofList, monoUnOp "listToString"),
    -- Bool connectives (Lean's are strict, Scala's short-circuit: equivalent on pure code).
    (``Bool.and, monoBinOp "and"), (``Bool.or, monoBinOp "or"), (``Bool.not, monoUnOp "not"),
    (``and, monoBinOp "and"), (``or, monoBinOp "or"), (``not, monoUnOp "not"),
    -- List
    (``List.length, polyOp 1 1 "listLength"),
    (``List.map, polyOp 2 2 "listMap"),          -- (f, xs)
    (``List.zip, polyOp 2 2 "listZip"),
    (``List.take, polyOp 1 2 "listTake"),        -- (n, xs)
    (``List.drop, polyOp 1 2 "listDrop"),        -- (n, xs)
    (``List.reverse, polyOp 1 1 "listReverse"),
    (``List.find?, polyOp 1 2 "listFind"),       -- (p, xs)
    (``List.filter, polyOp 1 2 "listFilter"),    -- (p, xs)
    (``List.all, polyOp 1 2 "listAll"),          -- (xs, p)
    (``List.any, polyOp 1 2 "listAny"),          -- (xs, p)
    (``List.head?, polyOp 1 1 "listHead"),
    (``List.isEmpty, polyOp 1 1 "listIsEmpty"),
    (``List.append, polyOp 1 2 "listAppend"),
    -- `xs[i]?` on lists (the only `GetElem?` instance whitelisted).
    (``GetElem?.getElem?, { arity := 7, typeArgIdx := 0, valueArgs := [5, 6],
                            key := fun | .list => some "listGet" | _ => none, instArgIdx := some 4 }),
    -- Option
    (``Option.bind, polyOp 2 2 "optBind"),       -- (o, f)
    (``Option.map, polyOp 2 2 "optMap"),         -- (f, o)
    (``Option.getD, polyOp 1 2 "optGetD"),
    (``Option.isSome, polyOp 1 1 "optIsSome"),
    (``Option.isNone, polyOp 1 1 "optIsNone") ]

def findOp (n : Name) : Option OpEntry :=
  (opTable.find? (·.1 == n)).map (·.2)

/-- `Decidable`-instance heads that appear as the instance argument of `ite`.
Used only as a fallback when the decided proposition itself cannot be read
off the instance's type (`Translate.transDecInst`). -/
def decInstTable : List (Name × String) :=
  [ (``instDecidableEqBool, "eq"),
    (``instDecidableEqNat, "eq"),
    (``instDecidableEqString, "eq"),
    (``Int.instDecidableEq, "eq"),
    (``Nat.decEq, "eq"),
    (``Nat.decLt, "lt"),
    (``Nat.decLe, "le"),
    (``Int.decLt, "lt"),
    (``Int.decLe, "le") ]

def findDecInst (n : Name) : Option String :=
  (decInstTable.find? (·.1 == n)).map (·.2)

/-- Builtin TYPE heads: Lean type constant → (Scala id, expected #args). -/
def typeTable : List (Name × (MS.QualId × Nat)) :=
  [ (``List, (["List"], 1)),
    (``Option, (["Option"], 1)),
    (``Except, (["Either"], 2)) ]

def findType (n : Name) : Option (MS.QualId × Nat) :=
  (typeTable.find? (·.1 == n)).map (·.2)

/-- Builtin CONSTRUCTORS: Lean ctor → printer key.
`numParams` type params are dropped; remaining args become operands. -/
structure CtorEntry where
  numParams : Nat
  numFields : Nat
  key : String

def ctorTable : List (Name × CtorEntry) :=
  [ -- Builtin-represented numeric constructors (BigInt level)
    (``Int.ofNat, ⟨0, 1, "intOfNat"⟩),
    (``Int.negSucc, ⟨0, 1, "intNegSucc"⟩),
    (``Nat.succ, ⟨0, 1, "natSucc"⟩),
    (``Nat.zero, ⟨0, 0, "natZero"⟩),
    (``List.nil, ⟨1, 0, "nil"⟩),
    (``List.cons, ⟨1, 2, "cons"⟩),
    (``Option.none, ⟨1, 0, "none"⟩),
    (``Option.some, ⟨1, 1, "some"⟩),
    (``Except.error, ⟨2, 1, "left"⟩),
    (``Except.ok, ⟨2, 1, "right"⟩),
    (``Prod.mk, ⟨2, 2, "tuple2"⟩) ]

def findCtor (n : Name) : Option CtorEntry :=
  (ctorTable.find? (·.1 == n)).map (·.2)

/-- Types whose Lean constructor representation must NEVER leak into
generated code (they map to Scala builtins). Constructor patterns on them
are fail-loud; constructor applications go through `ctorTable`. -/
def builtinReprTypes : List Name :=
  [``Nat, ``Int, ``Char, ``String, ``Bool, ``Unit, ``PUnit]

/-- Monad-class projections whose instance argument is resolved by `whnf` at
`instances` transparency to the concrete implementation (`Res.bind`,
`Option.bind`, `Res.ok`, `some`, …). The number is the count of leading
type + instance arguments to reduce under. -/
def monadOps : List (Name × Nat) :=
  [ (``Bind.bind, 4), (``Pure.pure, 3), (``Functor.map, 4),
    (``Seq.seq, 4), (``SeqLeft.seqLeft, 4), (``SeqRight.seqRight, 4) ]

def findMonadOp (n : Name) : Option Nat :=
  (monadOps.find? (·.1 == n)).map (·.2)

end Lens.Builtins
