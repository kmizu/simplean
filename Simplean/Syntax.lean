import Simplean.AList

/-!
# 構文

Simplean の型・値・式・文・関数定義・プログラムを定義する。
-/

namespace Simplean

-- ANCHOR: ty
/-- 型：整数、文字列、リスト。 -/
inductive Ty where
  | int
  | str
  | list (elem : Ty)
  deriving DecidableEq, Repr
-- ANCHOR_END: ty

-- ANCHOR: val
/-- 実行時の値。リストは cons セルで表し、空リストは要素型を持つ。 -/
inductive Val where
  | int (n : Int)
  | str (s : String)
  | nil (elem : Ty)
  | cons (hd tl : Val)
  deriving DecidableEq, Repr
-- ANCHOR_END: val

-- ANCHOR: hastype
/-- 値 `v` が型 `t` を持つ、という関係。 -/
inductive HasType : Val → Ty → Prop where
  | int (n : Int) : HasType (.int n) .int
  | str (s : String) : HasType (.str s) .str
  | nil (t : Ty) : HasType (.nil t) (.list t)
  | cons {v w : Val} {t : Ty} :
      HasType v t → HasType w (.list t) → HasType (.cons v w) (.list t)
-- ANCHOR_END: hastype

-- ANCHOR: default
/-- 各型の既定値。空リストに `head` を適用したときに返る。 -/
def Ty.default : Ty → Val
  | .int => .int 0
  | .str => .str ""
  | .list t => .nil t

theorem Ty.default_hasType (t : Ty) : HasType t.default t := by
  cases t <;> constructor
-- ANCHOR_END: default

-- ANCHOR: ops
/-- 単項演算子。 -/
inductive UnOp where
  | neg | not | head | tail | isNil | len | strLen | toStr
  deriving DecidableEq, Repr

/-- 二項演算子。 -/
inductive BinOp where
  | add | sub | mul | div | mod | lt | le | eq | and | or | concat | cons
  deriving DecidableEq, Repr
-- ANCHOR_END: ops

-- ANCHOR: expr
/-- 式。関数呼び出しの引数は式のリスト。 -/
inductive Expr where
  | lit (n : Int)
  | strLit (s : String)
  | var (x : String)
  | nil (elem : Ty)
  | unop (op : UnOp) (e : Expr)
  | binop (op : BinOp) (e₁ e₂ : Expr)
  | call (f : String) (args : List Expr)
  deriving Repr
-- ANCHOR_END: expr

-- ANCHOR: stmt
/-- 文。条件は `Int` で、`0` が偽、それ以外が真。 -/
inductive Stmt where
  | skip
  | decl (x : String) (t : Ty) (e : Expr)
  | assign (x : String) (e : Expr)
  | seq (s₁ s₂ : Stmt)
  | ite (cond : Expr) (thenB elseB : Stmt)
  | while (cond : Expr) (body : Stmt)
  deriving Repr
-- ANCHOR_END: stmt

-- ANCHOR: fundef
/-- 関数定義。本体の文を実行してから結果式を評価する。 -/
structure FunDef where
  name : String
  params : List (String × Ty)
  ret : Ty
  body : Stmt
  result : Expr
  deriving Repr

/-- プログラム：関数定義の列と、空の環境で評価する main 式。 -/
structure Prog where
  funs : List FunDef
  main : Expr
  deriving Repr
-- ANCHOR_END: fundef

/-- 実行時環境：名前 → 値。 -/
abbrev Env := AList Val

/-- 型文脈：名前 → 型。 -/
abbrev Ctx := AList Ty

/-- 名前で関数定義を探す（先頭一致）。 -/
def Prog.findFun (P : Prog) (f : String) : Option FunDef :=
  P.funs.find? (fun fd => fd.name == f)

theorem Prog.findFun_mem {P : Prog} {f : String} {fd : FunDef}
    (h : P.findFun f = some fd) : fd ∈ P.funs :=
  List.mem_of_find?_eq_some h

end Simplean
