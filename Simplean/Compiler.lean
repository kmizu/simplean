import Simplean.VM

/-!
# コンパイラ

式・文・関数・プログラムを VM の命令列に変換する。
-/

namespace Simplean

-- ANCHOR: compileExpr
mutual

/-- 式のコンパイル：評価後、値がスタックトップに 1 個増える。 -/
def compileExpr : Expr → List Instr
  | .lit n => [.push (.int n)]
  | .strLit s => [.push (.str s)]
  | .var x => [.load x]
  | .nil t => [.push (.nil t)]
  | .unop op e => compileExpr e ++ [.unop op]
  | .binop op e₁ e₂ => compileExpr e₁ ++ compileExpr e₂ ++ [.binop op]
  | .call f args => compileArgs args ++ [.call f]

/-- 引数列のコンパイル：左から順に push する（最後の引数がトップ）。 -/
def compileArgs : List Expr → List Instr
  | [] => []
  | e :: es => compileExpr e ++ compileArgs es

end
-- ANCHOR_END: compileExpr

-- ANCHOR: compileStmt
/-- 文のコンパイル：実行後、スタックは元のまま。 -/
def compileStmt : Stmt → List Instr
  | .skip => []
  | .decl x _ e => compileExpr e ++ [.store x]
  | .assign x e => compileExpr e ++ [.store x]
  | .seq s₁ s₂ => compileStmt s₁ ++ compileStmt s₂
  | .ite c s₁ s₂ =>
    let c₁ := compileStmt s₁
    let c₂ := compileStmt s₂
    compileExpr c ++ [.jz (c₁.length + 1)] ++ c₁ ++ [.jmp c₂.length] ++ c₂
  | .while c body =>
    let cc := compileExpr c
    let cb := compileStmt body
    cc ++ [.jz (cb.length + 1)] ++ cb ++ [.jmp (-(cc.length + cb.length + 2 : Int))]
-- ANCHOR_END: compileStmt

-- ANCHOR: compileFun
/-- 関数のコンパイル：本体、結果式、`ret`。 -/
def compileFun (fd : FunDef) : List Instr :=
  compileStmt fd.body ++ compileExpr fd.result ++ [.ret]

/-- 関数列を番地 `pos` から順に並べ、関数表とコードを返す。 -/
def compileFuns : List FunDef → Nat → AList FunInfo × List Instr
  | [], _ => ([], [])
  | fd :: fds, pos =>
    let c := compileFun fd
    let rest := compileFuns fds (pos + c.length)
    ((fd.name, ⟨pos, fd.params.map (·.1)⟩) :: rest.1, c ++ rest.2)

/-- プログラムのコンパイル：main のコード、`halt`、その後に関数本体を並べる。 -/
def compileProg (P : Prog) : VMProg :=
  let mainCode := compileExpr P.main ++ [.halt]
  let rest := compileFuns P.funs mainCode.length
  { code := mainCode ++ rest.2, table := rest.1 }
-- ANCHOR_END: compileFun

end Simplean
