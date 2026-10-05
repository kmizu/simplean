# 演習

演習の雛形は `Exercises/` にあります。本体の `Simplean` ライブラリとは別のライブラリなので、`sorry` を残したまま `lake build Exercises` でビルドできます（CI は本体に `sorry` が無いことだけを検査します）。

## 演習 1：Bool 型を足す

```lean
{{#include ../../Exercises/Bool.lean}}
```

まず雛形の二つの `sorry` を埋めてください。`ofBool` は `Ops.lean` の定義です。`cases b` で場合分けすれば、どちらも `simp` か `rfl` で閉じるはずです。

そのうえで、本格的な演習です。`Ty.bool` と `Val.bool` を追加し、

- 比較演算 `lt`/`le`/`eq` と `isNil`、`not`/`and`/`or` の結果を `Bool` にする
- `ite`/`while` の条件を `Bool` 型に変える
- `unopTy`/`binopTy`/`applyUn`/`applyBin`、`HasType`、`Ty.default` を更新する

変更のたびに `lake build --wfail` を走らせてください。型健全性・コンパイラ正当性の証明がどこで止まるか——それが「設計変更が証明に与える影響」を体で覚える一番の方法です。ヒント：`soundS_succ` の `ite`/`while` で `cases hv` が返す形が変わります。

## 演習 2：for 文

```lean
{{#include ../../Exercises/ForLoop.lean}}
```

`forLoop x n body` は `for` 文を `while` に展開する**糖衣構文**です。新しい構文を言語に足すのではなく、既存の構文への変換として定義しているので、意味論もコンパイラも証明も変える必要がありません。

`forLoop_ty` は「展開後の文が型付けできる」ことを示す演習です。`StmtTy.seq`、`StmtTy.decl`、`StmtTy.while`、`StmtTy.assign`、`ExprTy.binop` を順に組み立ててください。`x` が宣言済みの文脈 `AList.update Γ x .int` で `n` の型付けを使うには、`ExprTy` の文脈を広げる補題（weakening）が必要になるかもしれません。それ自体を補題として証明するのも良い演習です。

## 演習 3：出力

`print e` という文を足し、実行結果に**出力の列**を含めてみましょう。

- `Res` を `Res (α × List Val)` にするか、`execS` の結果を「環境と出力」の組にする
- VM に `print` 命令を足し、状態に出力列を持たせる
- コンパイラ正当性の主張を「同じ値で止まり、**同じ出力**をする」に拡張する

観測可能な振る舞いが「最終値」だけでなく「途中の出力」にも広がるので、forward simulation の主張がより実践的になります。

## 演習 4：ピープホール最適化

コンパイラが出す命令列には、`push (int 0); load "n"; binop lt` のような決まった形が繰り返し現れます。たとえば

- `push v; store x` → （`x` が後で読まれないなら削除）
- `jmp 0` → 削除

といった局所的な書き換え（ピープホール最適化）を関数 `peephole : List Instr → List Instr` として定義し、「最適化しても `run` の結果は変わらない」を証明してみましょう。相対ジャンプを使っているので、命令を削除するとジャンプのオフセットがずれます。どのオフセットを直す必要があるかを考えると、相対ジャンプの長所と短所が見えてきます。

## 演習 5：逆向きのシミュレーション

第 12 章で述べた、証明していないことに挑む演習です。まず小さく、

> 式のコード `compileExpr e` を `pc` から実行して `pc + |compileExpr e|` に到達したなら、スタックには値が 1 つ積まれていて、その値に `e` は評価される

を、関数呼び出しを含まない式について証明してみてください。`call` を含めるには、VM の実行列を分解する一般的な補題が必要になります。
