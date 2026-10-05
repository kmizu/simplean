# Lean 4 速習

この章では、Simplean のソースを読むために必要な Lean 4 の機能を、実際に Simplean に出てくる形で紹介します。細部は後の章でもう一度出てくるので、ここでは雰囲気をつかんでください。

## `inductive`：データ型を定義する

Lean 4 で新しいデータ型を作る基本は `inductive`（帰納型）です。これは「この型の値は、次のコンストラクタのどれかで作られる」という宣言です。Simplean の型 `Ty` はこうなっています。

```lean
{{#include ../../Simplean/Syntax.lean:ty}}
```

- `int` と `str` は引数を持たないコンストラクタ
- `list (elem : Ty)` は `Ty` を一つ受け取るコンストラクタ。`Ty.list Ty.int` が「整数のリスト」の型です

`deriving DecidableEq, Repr` は、「等しいかどうかを判定する手続き」と「表示方法」を自動生成する指示です。これがあると `if t₁ = t₂ then … else …` と書けたり、`#eval` で値を表示できたりします。

コンストラクタは `Ty.int` のようにフルネームで書けますが、型が分かっている文脈では `.int` と省略できます。この本のコードは省略形を多用します。

## `structure`：レコード型

名前付きのフィールドを持つ型は `structure` で作ります。関数定義を表す `FunDef` です。

```lean
{{#include ../../Simplean/Syntax.lean:fundef}}
```

値を作るときは `{ name := "fact", params := [("n", .int)], ret := .int, body := …, result := … }` と書くか、`where` 構文を使います。フィールドは `fd.name` のようにドットで読めます。

## 関数とパターンマッチ

関数は `def` で定義します。引数のパターンで場合分けするのが基本形です。

```lean
{{#include ../../Simplean/Syntax.lean:default}}
```

最初の `def Ty.default` は「型ごとの既定値」です。`| .int => .int 0` は「引数が `Ty.int` なら `Val.int 0` を返す」と読みます。Lean はパターンが**すべての場合を網羅しているか**を検査し、漏れがあればエラーにします。

その直後の `theorem` は、後で説明する「証明」です。`def` と `theorem` が同じファイルに並んでいるのが Lean の特徴です。

## 再帰と停止性

Lean の関数は**必ず停止する**ことが要求されます。これは、Lean が証明の道具でもあるからです。停止しない関数を許すと、矛盾が証明できてしまいます。

多くの再帰関数は、引数の構造が小さくなる**構造的再帰**なので、Lean が自動的に停止性を認めます。連想リストの検索はその例です。

```lean
{{#include ../../Simplean/AList.lean:lookup}}
```

リストの先頭を一つ外して再帰しているので、必ず停止します。

しかしインタプリタは、`while` ループや再帰関数を含むプログラムを実行するので、一般には停止しません。これを Lean で書くための工夫が **fuel（燃料）** です。第 6 章で詳しく扱います。

## `Option` と `do` 記法

失敗するかもしれない計算は `Option α` で表します。値があれば `some a`、なければ `none` です。連続して失敗しうる計算を書くときは `do` 記法を使います。

```lean
{{#include ../../Simplean/Checker.lean:typeOf}}
```

`let t ← typeOf P Γ e` は「`typeOf P Γ e` が `some t` なら `t` を取り出して続行、`none` なら全体を `none` にする」という意味です。Haskell の `Maybe` モナド、Rust の `?` 演算子と同じ発想です。

## `Prop` と `Bool`：命題と真偽値

Lean には「真偽値」が二種類あります。

- `Bool`：計算で求まる `true` / `false`。`if` の条件に使う
- `Prop`：**命題**。「`x` は `y` より大きい」のような主張そのもの。証明の対象

たとえば `HasType v t`（値 `v` が型 `t` を持つ）は `Prop` です。これは計算では**なく**、「`v` が `t` を持つ理由（証明）」を構成するための規則の集まりとして定義されます。

```lean
{{#include ../../Simplean/Syntax.lean:hastype}}
```

このような `inductive … : … → Prop` を**帰納的述語**と呼びます。「`HasType (.int n) .int` はコンストラクタ `int` で証明できる」「`HasType (.cons v w) (.list t)` を証明するには、`v : t` と `w : list t` の証明が必要」と読みます。第 4 章・第 5 章の主役です。

## `theorem` と tactic

命題を証明するには `theorem 名前 : 命題 := 証明` と書きます。証明は `by` に続けて **tactic**（戦術）を並べて書くのが普通です。

```lean
{{#include ../../Simplean/AList.lean:lookup_update}}
```

`simp [update]` は「`update` の定義を展開して、簡約（simplification）で片づけろ」という指示です。Lean がゴールを閉じられなければエラーになり、閉じられればそれが証明です。**証明が通った時点で、その命題は（Lean の信頼する範囲で）正しい**と保証されます。

この本で頻出する tactic は次のとおりです（付録 A に一覧）。

| tactic | 意味 |
|---|---|
| `intro x` | 「任意の `x` について」を仮定として取り込む |
| `cases h` | 仮定 `h` をコンストラクタごとに場合分け |
| `induction n` | `n` に関する帰納法 |
| `simp [...]` | 定義や補題で簡約 |
| `rw [h]` | 等式 `h` で書き換え |
| `exact e` | ゴールにぴったり合う証明 `e` を与える |
| `omega` | 自然数・整数の線形算術を自動で解く |
| `decide` | 決定可能な命題を計算で判定する |
| `constructor` | ゴールの帰納的述語のコンストラクタを適用 |

## `#eval` と `decide`：動かして確かめる

定義した関数は `#eval` で即座に実行できます。そして、具体的なプログラムについての主張は `decide` で**証明**できます。

```lean
{{#include ../../Simplean/Tests.lean:eval_tests}}
```

`theorem fact_eval : evalProg factProg 100 = .ok (.int 3628800) := by decide` は、「階乗プログラムを fuel 100 で評価すると 3628800 になる」ことを、Lean のカーネルに**計算させて**証明しています。テストと証明の境目がないのが Lean の面白いところです。

## 名前空間と `open`

Simplean の定義はすべて `namespace Simplean` の中にあります。外から使うときは `Simplean.evalProg` と書くか、`open Simplean` で接頭辞を省略します。例プログラムは `Simplean.Examples`、テストは `Simplean.Tests` にあります。

次の章から、いよいよ Simplean を定義していきます。
