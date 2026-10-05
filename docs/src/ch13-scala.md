# Scala 3 への抽出

ここまでのインタプリタ・型検査器・コンパイラ・VM は、すべて Lean 4 の関数でした。この章では、それらを **Scala 3 のソースコードとして機械的に取り出し**ます。Coq の Extraction に当たる作業です。

## なぜ抽出するのか

証明した対象は Lean の定義です。同じ処理系を別の言語で手書きすると、その手書きの版については何も証明していないことになります。定義から機械的に生成すれば、「証明した定義」と「動かすコード」の距離を、抽出器 1 つぶんに縮められます。

## Lens

Lean 4 には標準の抽出機構がありません。そこで、[kmizu/lean4-peg](https://github.com/kmizu/lean4-peg) で作られた Lean → Scala 3 の抽出器 **Lens** をこのリポジトリに取り込み（`Lens/`）、Simplean 向けに拡張しました。

Lens の仕組みは次のとおりです。

1. コンパイル済みのモジュール（`.olean`）を読み込み、指定した定義から依存関係をたどる
2. 帰納型は `sealed trait` と case class に、構造体は `final case class` に変換する
3. 関数の本体は Lean が生成する**等式補題**（パターンごとの定義式）から取り出し、`match` 式に変換する
4. `Nat`/`Int` は `BigInt` に写し、除算などは Lean と同じ意味の実行時関数（`scala/runtime/Prelude.scala`）を呼ぶ

Simplean のために足した主な変換規則は、任意のモナドの `do` 記法（`Res` と `Option`）、`DecidableEq` による `if t₁ = t₂`、`List.zip`/`take`/`drop`/`find?` などの組み込み、`Nat` と `Int` の変換です。**Simplean 側の定義は一行も変えていません。**

## 抽出する

```sh
lake build Lens extract
lake exe extract --out scala/generated/Simplean.scala
```

生成されるのは 450 行ほどの Scala 3 ファイルです。式の評価関数はこうなります（一部）。

```scala
def evalE(P: Prog, x1: BigInt, x2: List[(String, Val)], x3: Expr): Res[Val] =
  ((x1, x3) match {
    case (_g0, x4) if _g0 == BigInt(0) => Res.timeout[Val]()
    case (_g0, Expr.lit(n_1)) if _g0 >= 1 => { val n = _g0 - 1; Res.ok[Val](Val.int(n_1)) }
    case (_g0, Expr.`var`(x_3)) if _g0 >= 1 =>
      { val n = _g0 - 1; Res_ofOption[Val](AList_lookup[Val](x2, x_3)) }
    case (_g0, Expr.unop(op, e)) if _g0 >= 1 =>
      { val n = _g0 - 1
        Res_bind[Val, Val](evalE(P, n, x2, e), ((v: Val) => Res_ofOption[Val](applyUn(op, v)))) }
    ...
  })
```

第 6 章の `evalE` と見比べてください。fuel のパターン `0` と `n + 1` がガード付きの `case` に、`do` 記法が `Res_bind` の呼び出しに、ほぼ一対一で対応しています。人間が書く Scala としては冗長ですが、「Lean の定義をそのまま写した」ことが読み取れる形です。

## Lean と突き合わせる

抽出器そのものは証明されていません。そこで、抽出した Scala を実際に動かして Lean の結果と比べます。

```sh
scripts/scala-check.sh
```

このスクリプトは次のことをします。

1. 抽出器をビルドして、Scala を抽出し直す
2. 抽出結果が `tests/golden/Simplean.scala`（golden ファイル）と一致するか確かめる
3. `scala-cli` でコンパイルして `scala/Main.scala` を実行する
4. 出力を `scala/expected.txt` と比べる。こちらは Lean 自身の `#eval` で生成した正解（`scripts/expected.lean`）

出力は次のようになります。型検査（`check`）、参照意味論（`eval`）、VM（`vm`）の三つを、12 個の例プログラムについて並べています。

```text
fact: check=Some(int) eval=ok(3628800) vm=Some(3628800)
factRec: check=Some(int) eval=ok(3628800) vm=Some(3628800)
fib: check=Some(int) eval=ok(6765) vm=Some(6765)
parity: check=Some(int) eval=ok(1) vm=Some(1)
sumRange: check=Some(int) eval=ok(45) vm=Some(45)
reverse: check=Some(list(int)) eval=ok([3, 2, 1]) vm=Some([3, 2, 1])
flatten: check=Some(list(int)) eval=ok([1, 2, 3]) vm=Some([1, 2, 3])
str: check=Some(str) eval=ok("ababab120") vm=Some("ababab120")
illAddStr: check=None eval=err vm=None
illUndeclared: check=None eval=err vm=None
illRedecl: check=None eval=ok(1) vm=Some(1)
illArity: check=None eval=err vm=Some(2)
scala-check: OK (12 programs match Lean)
```

## 最後の 2 行が教えてくれること

不正なプログラムの結果が面白いので、読み解いておきます。

- **`illRedecl`**（引数と同じ名前の再宣言）は、型検査では拒否されますが、実行すると `ok(1)` を返します。再宣言を禁止しているのは「実行時に必ず失敗するから」ではなく、**型健全性の証明の不変条件（`ctx_mono`）を保つため**でした（第 5 章）。型検査は「安全だと証明できるもの」だけを通すので、実際には動くプログラムを拒否することがあります
- **`illArity`**（引数が 1 個多い呼び出し）は、インタプリタでは `err`、VM では `Some(2)` です。インタプリタは引数個数を検査しますが、VM は関数表の個数だけスタックから取るので、余分な引数をスタックに残したまま動いてしまいます。**型検査を通らないプログラムでは、インタプリタと VM が食い違う**のです

二つ目は、コンパイラ正当性の定理の前提を思い出させてくれます。定理は「インタプリタが `ok v` を返すなら VM も `v` で止まる」でした。インタプリタが `err` の場合については、何も言っていません。そして型健全性が「正しく型付けされていれば `err` にならない」を保証するので、型検査を通ったプログラムではこの食い違いは起こりません。二つの定理が互いの穴を埋めている様子が、この 1 行に現れています。

## 信頼の範囲

この章で足した保証は、証明ではなく**テスト**です。

- 抽出器 Lens は証明されていません。変換規則の誤りは golden ファイルの差分レビューと実行結果の比較で見つけます
- Scala コンパイラと JVM も信頼の基盤に入ります
- `BigInt` を使っているので整数の意味は Lean と同じですが、再帰が深いプログラムでは JVM のスタックが先に尽きます

また、抽出した `compileFuns` は再帰呼び出しを 2 回ずつ行う形になっていて、関数の数に対して指数的に遅くなります（Lean の等式補題が `let` を展開してしまうため）。例プログラムの規模では問題になりませんが、実用にするなら抽出器側で `let` を保存する改良が要ります。
