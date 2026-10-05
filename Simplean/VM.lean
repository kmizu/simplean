import Simplean.Ops

/-!
# スタック VM

命令列・状態・1 ステップ実行 `step`・実行 `run` を定義する。
ジャンプは相対番地。関数呼び出しはフレームを積み、`ret` で戻る。
-/

namespace Simplean

-- ANCHOR: instr
/-- VM の命令。 -/
inductive Instr where
  | push (v : Val)
  | load (x : String)
  | store (x : String)
  | unop (op : UnOp)
  | binop (op : BinOp)
  | jmp (ofs : Int)
  | jz (ofs : Int)
  | call (f : String)
  | ret
  | halt
  deriving DecidableEq, Repr
-- ANCHOR_END: instr

-- ANCHOR: vmstate
/-- 関数表の項目：入口番地と引数名。 -/
structure FunInfo where
  entry : Nat
  params : List String
  deriving DecidableEq, Repr

/-- VM プログラム：命令列と関数表。 -/
structure VMProg where
  code : List Instr
  table : AList FunInfo
  deriving Repr

/-- 呼び出しフレーム：戻り番地と呼び出し元のローカル変数。 -/
structure Frame where
  retPc : Nat
  locals : Env
  deriving DecidableEq, Repr

/-- VM の状態。 -/
structure VMState where
  pc : Nat
  stack : List Val
  locals : Env
  frames : List Frame
  deriving DecidableEq, Repr

/-- 初期状態。 -/
def VMState.init : VMState := ⟨0, [], [], []⟩
-- ANCHOR_END: vmstate

/-- 相対ジャンプの飛び先：次の命令の番地にオフセットを足す。 -/
def jumpTarget (pc : Nat) (ofs : Int) : Nat := ((pc : Int) + 1 + ofs).toNat

-- ANCHOR: step
/-- 1 命令実行する。`halt`、不正なスタック、範囲外の pc では `none`。 -/
def step (vmP : VMProg) (s : VMState) : Option VMState :=
  match vmP.code[s.pc]? with
  | none => none
  | some i =>
    match i, s.stack with
    | .push v, σ => some { s with pc := s.pc + 1, stack := v :: σ }
    | .load x, σ => do
        let v ← AList.lookup s.locals x
        some { s with pc := s.pc + 1, stack := v :: σ }
    | .store x, v :: σ =>
        some { s with pc := s.pc + 1, stack := σ, locals := AList.update s.locals x v }
    | .unop op, v :: σ => do
        let w ← applyUn op v
        some { s with pc := s.pc + 1, stack := w :: σ }
    | .binop op, v₂ :: v₁ :: σ => do
        let w ← applyBin op v₁ v₂
        some { s with pc := s.pc + 1, stack := w :: σ }
    | .jmp ofs, _ => some { s with pc := jumpTarget s.pc ofs }
    | .jz ofs, .int k :: σ =>
        some { s with pc := if k = 0 then jumpTarget s.pc ofs else s.pc + 1, stack := σ }
    | .call f, σ => do
        let fi ← AList.lookup vmP.table f
        let k := fi.params.length
        some { pc := fi.entry, stack := σ.drop k,
               locals := bindParams fi.params (σ.take k).reverse,
               frames := ⟨s.pc + 1, s.locals⟩ :: s.frames }
    | .ret, v :: σ =>
        match s.frames with
        | fr :: frs => some { pc := fr.retPc, stack := v :: σ, locals := fr.locals, frames := frs }
        | [] => none
    | _, _ => none
-- ANCHOR_END: step

/-- `k` ステップ実行する。 -/
def stepN (vmP : VMProg) : Nat → VMState → Option VMState
  | 0, s => some s
  | k + 1, s => do
      let s' ← step vmP s
      stepN vmP k s'

-- ANCHOR: run
/-- 最大 `fuel` ステップ実行し、`halt` に到達したらスタックトップを返す。 -/
def run (vmP : VMProg) : Nat → VMState → Option Val
  | 0, _ => none
  | fuel + 1, s =>
    if vmP.code[s.pc]? = some .halt then s.stack.head?
    else do
      let s' ← step vmP s
      run vmP fuel s'
-- ANCHOR_END: run

end Simplean
