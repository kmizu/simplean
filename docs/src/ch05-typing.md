# 型付け規則と型検査器

この章では二つのものを作ります。

1. **型付け規則**：「式 `e` は文脈 `Γ` の下で型 `t` を持つ」を帰納的述語で定義する——これが**仕様**
2. **型検査器**：規則に従って型を計算する関数——これが**実装**

そして「実装が仕様を満たす」ことを証明します。この「仕様と実装を分けて、両者をつなぐ定理を証明する」パターンは、この本全体を貫く構えです。

## 演算子の型

まず演算子の型を関数として与えます。

```lean
{{#include ../../Simplean/Ops.lean:unopTy}}
```

```lean
{{#include ../../Simplean/Ops.lean:binopTy}}
```

`unopTy op t` は「`op` を型 `t` の値に適用したときの結果の型」、型が合わなければ `none` です。`eq` は同じ型どうしなら何でも比較でき、`cons` は要素と同じ要素型のリストにだけ付けられます。

## 式の型付け

```lean
{{#include ../../Simplean/Typing.lean:exprty}}
```

`ExprTy P Γ e t` が「プログラム `P`（関数表のため）と文脈 `Γ` の下で、式 `e` は型 `t` を持つ」です。規則を一つずつ読みます。

- `lit`/`strLit`：リテラルはその型
- `var`：`Γ` で `x` を探して型が見つかればそれ
- `nil`：`nil t` は `list t`
- `unop`/`binop`：引数の型から `unopTy`/`binopTy` で結果の型を決める
- `call`：関数 `f` を `P` から探し、引数の式の列が引数の型の列（`fd.params.map (·.2)`）を持てば、戻り型 `fd.ret`

`ExprTy` と `ArgsTy`（引数列の型付け）は互いを参照するので、`mutual … end` で囲んだ**相互帰納的**な定義になっています。

## 文の型付け

文は環境を変えるので、型付けの形も変わります。「文脈 `Γ` の下で文 `s` を検査すると、**後続の文脈**は `Γ'` になる」と読みます。

```lean
{{#include ../../Simplean/Typing.lean:stmtty}}
```

- `skip`：文脈は変わらない
- `decl`：`x` が**まだ宣言されていない**ことを要求し、`x : t` を文脈に加える
- `assign`：`x` が宣言済みで、式の型が一致すること。文脈は変わらない
- `seq`：`s₁` の後続文脈で `s₂` を検査する
- `ite`：条件は `int`。両方の枝を検査するが、**枝の中の宣言は外に漏れない**（結論の文脈は `Γ` のまま）
- `while`：条件は `int`。本体を検査するが、結論の文脈は `Γ` のまま

### 再宣言を禁止する理由

`decl` の前提 `AList.lookup Γ x = none` が無いと何が起きるか考えてみます。

```text
let x : Int = 1;
if 1 { let x : String = "a" } else { skip };
x := x + 1      -- x は Int のはず……
```

`if` の枝の中で `x` を文字列として再宣言すると、実行時の環境では `x` の値が `"a"` に置き換わります。しかし型文脈は枝を抜けると元の `x : Int` に戻るので、次の行は型検査を通り、実行時に型エラーになります。

再宣言を禁止すれば、文脈にある名前の値が別の型に変わることは決してありません。これを定理として述べたのが次の補題です。

```lean
{{#include ../../Simplean/Typing.lean:ctx_mono}}
```

「文を検査しても、`Γ` に既にあった束縛の型は `Γ'` でも変わらない」。証明は `StmtTy` の導出に関する帰納法で、`decl` の場合だけ場合分けが要ります（宣言した名前が探している名前と同じなら、前提 `hx` と矛盾する）。この補題は第 9 章で `ite`/`while` の枝を抜けるときに使います。

## 関数とプログラムの型付け

```lean
{{#include ../../Simplean/Typing.lean:progok}}
```

関数は、引数リストをそのまま初期文脈にして本体を検査し、その後続文脈で結果の式が戻り型を持てばよい。プログラムは全関数がそうなっていればよい。`main` の型付けは別に `ExprTy P [] P.main t` として述べます。

## 型検査器

規則をそのまま関数に書き下します。

```lean
{{#include ../../Simplean/Checker.lean:typeOf}}
```

```lean
{{#include ../../Simplean/Checker.lean:checkStmt}}
```

```lean
{{#include ../../Simplean/Checker.lean:checkProg}}
```

`typeOf` は `do` 記法で失敗を伝播し、`checkStmt` は `match` で複数の条件を同時に確かめています。不正なプログラムの例を用意してあります。

```lean
{{#include ../../Simplean/Examples.lean:ill}}
```

検査器の結果はテストとして固定してあります。正しいプログラムは `main` の型を返し、不正な四つはどれも `none` です。

```lean
{{#include ../../Simplean/Tests.lean:checker_tests}}
```

## 検査器の健全性

ここからが Lean らしいところです。「検査器が型 `t` を返したら、規則の意味でも `e : t` である」を証明します。

```lean
{{#include ../../Simplean/Checker.lean:typeOf_sound}}
```

証明は式の構造に関する再帰で、`typeOf` の各ケースを `rw [typeOf] at h` で展開し、`Option.bind_eq_some_iff`（「`do` が `some` を返したなら、各段階も `some` だった」）で分解し、対応する `ExprTy` の規則を適用します。`call` の `List Expr` に対しては `typeOfArgs_sound` を再帰的に呼びます。`induction` tactic が使えない入れ子の帰納型でも、**定理を再帰関数として書く**ことで構造帰納法ができるのです。

文とプログラムについても同様です。

```lean
{{#include ../../Simplean/Checker.lean:checkProg_sound}}
```

`checkProg P = some t` が示せれば（具体的なプログラムなら `by decide` や `by rfl` で示せます）、`ProgOk P` と `ExprTy P [] P.main t` が手に入り、第 9 章・第 11 章の定理がすべて使えるようになります。

### 完全性は証明していない

逆向き——「規則で `e : t` が導けるなら、検査器も `some t` を返す」（完全性）——は証明していません。この言語では型が式の形から一意に決まるので実際には成り立ちますが、今回必要なのは「検査器を通ったら安全」という方向だけです。証明する性質は、使う分だけに絞るのが実践的です。

次の章では、プログラムに**意味**を与えます。
