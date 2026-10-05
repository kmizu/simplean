# 意味論：fuel 付きインタプリタ

プログラムの「意味」を決める最も直接的な方法は、インタプリタを書くことです。Lean でそれをやると、インタプリタがそのまま**数学的な定義**になり、その上で定理を証明できます。この方法を **definitional interpreter** と呼びます。

## 停止性という壁

第 2 章で述べたように、Lean の関数は必ず停止しなければなりません。しかし Simplean には `while` と再帰関数があり、停止しないプログラムが書けます。

```text
while 1 { skip }
```

これを素直に評価する関数は Lean では定義できません。

解決策は **fuel（燃料）** です。評価関数に自然数 `n` を渡し、再帰呼び出しのたびに 1 ずつ減らします。`0` になったら「燃料切れ」として打ち切ります。燃料は必ず減るので、Lean は停止性を認めてくれます。

燃料切れは失敗の一種ですが、**型エラーとは区別**します。「正しく型付けされたプログラムは型エラーを起こさない」と言いたいので、燃料切れと型エラーを同じ `none` にしてしまうわけにはいかないからです。

## 結果の型 `Res`

```lean
{{#include ../../Simplean/Res.lean:res}}
```

`timeout`（燃料切れ）、`err`（型エラー）、`ok a`（成功）の三択です。`Monad` インスタンスを与えているので、`do` 記法が使えます。`bind` は失敗をそのまま伝播し、成功なら続きを実行します。

## 演算子の意味

演算子の意味は `Option Val` を返す関数です。`none` が型エラーに対応します。

```lean
{{#include ../../Simplean/Ops.lean:applyUn}}
```

```lean
{{#include ../../Simplean/Ops.lean:applyBin}}
```

いくつか注意点があります。

- 除算 `div`/`mod` は Lean の `Int` の除算そのままです。Lean では `x / 0 = 0` と定義されているので、ゼロ除算も失敗しません
- `eq` は `DecidableEq Val` を使った構造的等価性で、`Int` の `1`/`0` を返します
- `cons` はどんな値にも適用できます（型検査がおかしな組み合わせを排除します）

そして第 5 章の `unopTy`/`binopTy` との整合性が、次の補題です。

```lean
{{#include ../../Simplean/Ops.lean:applyUn_sound}}
```

「演算子の型付けが通り、引数が正しい型の値なら、演算は失敗せず、結果は予測された型を持つ」。証明は演算子と値で総当たりに場合分けして `simp_all` に投げる 1 行です。型健全性の証明で演算を扱う部分は、すべてこの補題（と `applyBin_sound`）に押し込んであります。

## 評価関数

いよいよ本体です。

```lean
{{#include ../../Simplean/Semantics.lean:eval}}
```

三つの関数が `mutual` ブロックで相互再帰しています。すべて第一引数の fuel に関する構造的再帰で、`n + 1` の場合に `n` を渡して再帰します。

### 式 `evalE`

- リテラルと `nil` はそのまま値に
- `var x`：環境を探す。見つからなければ `err`（`Res.ofOption` が `none` を `err` に写す）
- `unop`/`binop`：部分式を評価し、`applyUn`/`applyBin` を適用
- `call f args`：
  1. 引数の式を左から順に評価（`evalArgs`）
  2. 関数 `f` を探す。無ければ `err`
  3. **引数の個数が合うか確認**し、合わなければ `err`
  4. 引数名と値を束ねて新しい環境を作り（`bindParams`）、本体の文を実行
  5. その環境で結果の式を評価

呼び出し先は**呼び出し元の環境を見ません**。引数だけから始まる新しい環境で実行します。

引数の個数検査は、型検査を通ったプログラムでは常に成功するので、一見不要に見えます。しかし第 10 章のコンパイラ正当性では、この検査が**無いと定理が偽になる**のです。VM は関数表の引数個数だけスタックから値を取り出すので、インタプリタ側で `zip` が黙って余分な引数を捨てると、両者の挙動がずれてしまいます。

### 文 `execS`

- `decl`/`assign`：式を評価して環境を更新。実行時の振る舞いは同じ
- `seq`：順に実行
- `ite`：条件を評価し、`int k` なら `k = 0` で分岐。`int` 以外なら `err`
- `while`：条件を評価し、`int 0` なら終了。それ以外なら本体を実行して、**同じ fuel `n` で** `while` 自身を再評価

`while` の再帰呼び出しが `n`（`n + 1` より 1 小さい）で行われているのが、fuel 帰納法の鍵です。ループを 1 回まわるごとに fuel が 1 減るので、「`n + 1` の場合は `n` の場合から導く」という帰納法が、ループ本体の実行と残りのループに同時に適用できます。

### プログラム

```lean
{{#include ../../Simplean/Semantics.lean:evalProg}}
```

空の環境で `main` を評価するだけです。

## 動かす

```lean
#eval evalProg Examples.factProg 100     -- Res.ok (Val.int 3628800)
#eval evalProg Examples.factProg 5       -- Res.timeout
#eval evalProg Examples.illAddStr 10     -- Res.err
```

fuel が足りなければ `timeout`、型が合わなければ `err` です。`timeout` と `err` が区別されていることを確認してください。

テストは定理として書いてあります。

```lean
{{#include ../../Simplean/Tests.lean:eval_tests}}
```

`by decide` は、Lean のカーネルに `evalProg factProg 100` を実際に計算させ、`.ok (.int 3628800)` と等しいことを確認します。fuel が 100 や 200 なのは「十分大きければよい」からで、使わなかった分の fuel にコストはかかりません。

## 例プログラムを読む

再帰版の階乗と、相互再帰の例です。`if` の枝で代入し、結果の式で変数を返す、という Simplean 流の書き方に注目してください。

```lean
{{#include ../../Simplean/Examples.lean:factRec}}
```

```lean
{{#include ../../Simplean/Examples.lean:parity}}
```

リストと文字列の例もあります。`List[List[Int]]` を平坦化する `flatten` では、`.nil (.list .int)` が「リストのリストの空リスト」、`.nil .int` が「整数の空リスト」です。

```lean
{{#include ../../Simplean/Examples.lean:lists}}
```

```lean
{{#include ../../Simplean/Examples.lean:strings}}
```

## fuel は意味を変えないか

「fuel の与え方で結果が変わるなら、これは意味論と呼べないのではないか」という疑問は正当です。答えは第 11 章にあります。**fuel を増やしても、成功した結果は変わらない**（単調性）ことを証明し、そこから「ある fuel で値 `v` が出るなら、どの fuel でも値が出る限り `v` である」（決定性）を導きます。

次の章では、同じプログラムを別の方法——スタック VM——で実行します。
