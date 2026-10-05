import Simplean.Syntax

/-!
# 演算子の型と意味

`unopTy` / `binopTy` が演算子の型付け、`applyUn` / `applyBin` が意味。
インタプリタと VM の両方がこの定義を共有する。
-/

namespace Simplean

-- ANCHOR: unopTy
/-- 単項演算子の型：引数の型から結果の型。型が合わなければ `none`。 -/
def unopTy : UnOp → Ty → Option Ty
  | .neg, .int => some .int
  | .not, .int => some .int
  | .head, .list t => some t
  | .tail, .list t => some (.list t)
  | .isNil, .list _ => some .int
  | .len, .list _ => some .int
  | .strLen, .str => some .int
  | .toStr, .int => some .str
  | _, _ => none
-- ANCHOR_END: unopTy

-- ANCHOR: binopTy
/-- 二項演算子の型。`eq` は同じ型どうし、`cons` は要素と同じ要素型のリスト。 -/
def binopTy : BinOp → Ty → Ty → Option Ty
  | .add, .int, .int => some .int
  | .sub, .int, .int => some .int
  | .mul, .int, .int => some .int
  | .div, .int, .int => some .int
  | .mod, .int, .int => some .int
  | .lt, .int, .int => some .int
  | .le, .int, .int => some .int
  | .and, .int, .int => some .int
  | .or, .int, .int => some .int
  | .eq, t₁, t₂ => if t₁ = t₂ then some .int else none
  | .concat, .str, .str => some .str
  | .cons, t, .list t' => if t = t' then some (.list t) else none
  | _, _, _ => none
-- ANCHOR_END: binopTy

/-- 真偽値を `Int` の `1` / `0` で表す。 -/
def ofBool (b : Bool) : Val := .int (if b then 1 else 0)

/-- リスト値の長さ。リストでない値は `0`。 -/
def Val.length : Val → Nat
  | .cons _ tl => tl.length + 1
  | _ => 0

-- ANCHOR: applyUn
/-- 単項演算子の意味。型が合わない値には `none`。 -/
def applyUn : UnOp → Val → Option Val
  | .neg, .int n => some (.int (-n))
  | .not, .int n => some (ofBool (n == 0))
  | .head, .nil t => some t.default
  | .head, .cons hd _ => some hd
  | .tail, .nil t => some (.nil t)
  | .tail, .cons _ tl => some tl
  | .isNil, .nil _ => some (ofBool true)
  | .isNil, .cons _ _ => some (ofBool false)
  | .len, .nil _ => some (.int 0)
  | .len, .cons hd tl => some (.int ((Val.cons hd tl).length : Nat))
  | .strLen, .str s => some (.int (s.length : Nat))
  | .toStr, .int n => some (.str (toString n))
  | _, _ => none
-- ANCHOR_END: applyUn

-- ANCHOR: applyBin
/-- 二項演算子の意味。除算は Lean の全域 `Int` 除算（`x / 0 = 0`）。 -/
def applyBin : BinOp → Val → Val → Option Val
  | .add, .int a, .int b => some (.int (a + b))
  | .sub, .int a, .int b => some (.int (a - b))
  | .mul, .int a, .int b => some (.int (a * b))
  | .div, .int a, .int b => some (.int (a / b))
  | .mod, .int a, .int b => some (.int (a % b))
  | .lt, .int a, .int b => some (ofBool (decide (a < b)))
  | .le, .int a, .int b => some (ofBool (decide (a ≤ b)))
  | .and, .int a, .int b => some (ofBool (a != 0 && b != 0))
  | .or, .int a, .int b => some (ofBool (a != 0 || b != 0))
  | .eq, v₁, v₂ => some (ofBool (v₁ == v₂))
  | .concat, .str a, .str b => some (.str (a ++ b))
  | .cons, v, w => some (.cons v w)
  | _, _, _ => none
-- ANCHOR_END: applyBin

/-- 関数の引数名と値を束ねて環境にする。 -/
def bindParams (names : List String) (vs : List Val) : Env := names.zip vs

@[simp] theorem bindParams_nil (vs : List Val) : bindParams [] vs = [] := rfl

@[simp] theorem bindParams_cons (y : String) (ys : List String) (v : Val) (vs : List Val) :
    bindParams (y :: ys) (v :: vs) = (y, v) :: bindParams ys vs := rfl

-- ANCHOR: hastypes
/-- 値の列が型の列を持つ。 -/
inductive HasTypes : List Val → List Ty → Prop where
  | nil : HasTypes [] []
  | cons {v : Val} {t : Ty} {vs : List Val} {ts : List Ty} :
      HasType v t → HasTypes vs ts → HasTypes (v :: vs) (t :: ts)
-- ANCHOR_END: hastypes

theorem HasTypes.length_eq {vs : List Val} {ts : List Ty} (h : HasTypes vs ts) :
    vs.length = ts.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem ofBool_hasType (b : Bool) : HasType (ofBool b) .int := by
  unfold ofBool; constructor

-- ANCHOR: applyUn_sound
/-- 演算子の型付けが通れば、意味も定義されていて結果は予測した型を持つ。 -/
theorem applyUn_sound {op : UnOp} {t t' : Ty} {v : Val}
    (hop : unopTy op t = some t') (hv : HasType v t) :
    ∃ v', applyUn op v = some v' ∧ HasType v' t' := by
  cases op <;> cases hv <;> simp_all [unopTy, applyUn] <;> subst_vars <;>
    (repeat' first | assumption | exact Ty.default_hasType _ | exact ofBool_hasType _ | constructor)
-- ANCHOR_END: applyUn_sound

theorem applyBin_sound {op : BinOp} {t₁ t₂ t : Ty} {v₁ v₂ : Val}
    (hop : binopTy op t₁ t₂ = some t) (h₁ : HasType v₁ t₁) (h₂ : HasType v₂ t₂) :
    ∃ v, applyBin op v₁ v₂ = some v ∧ HasType v t := by
  cases op <;> cases h₁ <;> cases h₂ <;> simp_all [binopTy, applyBin] <;> (try cases hop) <;>
    subst_vars <;> (repeat' first | assumption | exact ofBool_hasType _ | constructor)

end Simplean
