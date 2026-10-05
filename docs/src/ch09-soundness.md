# 証明 1：型健全性

**型健全性**（type soundness）は、型システムに関する最も基本的な定理です。

> 正しく型付けされたプログラムは、実行時に型エラーを起こさない。

Simplean での正確な形は次のとおりです。

- `ProgOk P`（全関数が正しく型付け）かつ `ExprTy P [] P.main t`（main が型 `t`）なら、
- どんな fuel `n` でも `evalProg P n ≠ .err`、
- かつ `evalProg P n = .ok v` なら `HasType v t`。

燃料切れ（`timeout`）は許します。型システムは停止性については何も言わないからです。

## 主張を述べるための道具

### `Res.Ok`

「結果は型エラーではなく、成功したならその値は性質 `Q` を満たす」を一つの述語にまとめます。

```lean
{{#include ../../Simplean/Res.lean:resok}}
```

`timeout` なら無条件に真、`err` なら偽、`ok a` なら `Q a`。この述語の良いところは、`do` 記法の `bind` を越えて伝わることです。

```lean
{{#include ../../Simplean/Res.lean:ok_bind}}
```

「`r` が `Ok Q` で、`Q` を満たす任意の `a` について続き `f a` が `Ok R` なら、`r >>= f` は `Ok R`」。評価関数の各ケースは `do` で書かれているので、この補題を段数ぶん重ねれば証明の骨格ができます。

### `EnvOk`

第 4 章で見た「環境が文脈に適合する」です。

```lean
{{#include ../../Simplean/Soundness.lean:envok}}
```

必要な補題は四つあります（`Soundness.lean` の冒頭）。

- `EnvOk.mono`：文脈を縮めても適合は保たれる（`ctx_mono` と組み合わせて使う）
- `EnvOk.update`：`x : t` を文脈に加え、`x` に `t` の値を入れれば、適合は保たれる（`decl`）
- `EnvOk.assign`：文脈が `x : t` と言っていて `t` の値で更新すれば、適合は保たれる（`assign`）
- `EnvOk.bindParams`：引数の値が引数の型を持てば、引数の文脈に適合する環境ができる（関数呼び出し）

## 主張を束ねる

評価関数は三つ（式・引数列・文）が相互再帰しているので、証明も三つの主張を同時に進めます。

```lean
{{#include ../../Simplean/Soundness.lean:soundall}}
```

`SoundAll P n` は「fuel `n` で、式・引数列・文のそれぞれについて健全性が成り立つ」です。

## fuel に関する帰納法

証明の全体像はこうです。

1. `SoundAll P 0`：fuel 0 では評価は常に `timeout` なので、`Res.Ok` は無条件に真
2. `SoundAll P n → SoundAll P (n + 1)`：これを三つの補題 `soundE_succ`・`soundA_succ`・`soundS_succ` に分けて示す

```lean
{{#include ../../Simplean/Soundness.lean:soundness}}
```

`soundness` は再帰関数として書かれています。`| n + 1 => ⟨soundE_succ hP (soundness hP n), …⟩` が「`n` の場合（再帰呼び出し）から `n + 1` の場合を作る」帰納法のステップです。Lean は fuel が減っていることを見て、この再帰を認めます。

### なぜ式の構造ではなく fuel なのか

普通に考えると「式の構造に関する帰納法」をしたくなります。しかし

- `while` は、本体を実行した後に**同じ** `while` 文を再び実行します。構造帰納法では「同じ文」に対する帰納法の仮定が使えません
- `call` は、別の関数の本体（式の部分式ではない）を評価します

fuel 帰納法なら、「fuel が 1 小さい評価については、**どんな**式・文についても成り立つ」が仮定として手に入ります。`while` も `call` も、fuel を 1 消費して再帰しているので、この仮定がそのまま使えます。第 3 章で触れた「`List Expr` に `induction` が使えない」問題も、構造帰納法を使わないので関係なくなります。

## 式の場合を読む

```lean
{{#include ../../Simplean/Soundness.lean:soundE}}
```

証明の流れを追います。

1. `obtain ⟨ihE, ihA, ihS⟩ := ih`：帰納法の仮定を三つに分解
2. `intro … hT hρ`：型付け `hT : ExprTy P Γ e t` と適合 `hρ : EnvOk Γ ρ` を仮定に取る
3. `cases hT with …`：**型付けの導出**で場合分け。式 `e` の形は型付け規則から自動的に決まる

各ケース：

- `lit`/`strLit`/`nil`：`simp [evalE]` で評価を展開すると `Res.Ok _ (.ok (.int n))` になり、`constructor` が `HasType.int` を適用
- `var`：適合 `hρ` から「`x` の値があり、型を持つ」を取り出し、評価を展開
- `unop`：`refine (ihE … he hρ).bind fun v hv => ?_` で「部分式の評価は `Ok`」を使い、残るゴール「`applyUn op v` の結果が `Ok`」を `applyUn_sound` で閉じる
- `binop`：同じことを 2 回
- `call`：引数列の帰納法の仮定 `ihA`、関数の正しさ `hP`（`ProgOk` から本体の型付けを取り出す）、`EnvOk.bindParams`、そして本体の文と結果の式にそれぞれ `ihS`・`ihE` を使う。`split` は引数個数検査の `if` を場合分けし、個数が合わない枝は `HasTypes.length_eq` から矛盾

`hρ _ _ hx` のような下線は「Lean に推論させる」印です。型付けの仮定 `hx` を渡せば、変数名と型は決まります。

## 文の場合を読む

```lean
{{#include ../../Simplean/Soundness.lean:soundS}}
```

- `decl`：評価が `Ok` なら、`EnvOk.update` で新しい文脈と環境の適合を示す
- `assign`：`EnvOk.assign`
- `seq`：`s₁` の後の環境について `ihS` を使い、その結果でもう一度 `ihS`
- `ite`：条件の値 `v` は `HasType v .int` なので、`cases hv` で `v = .int k` が分かる。`split` で `k = 0` を場合分けし、選ばれた枝に `ihS`。枝の後続文脈 `Γ₁` から元の `Γ` に戻すのに `ctx_mono`（第 5 章）と `EnvOk.mono` を使う
- `while`：条件が `0` なら環境はそのまま。そうでなければ本体に `ihS`、続いて**同じ `while` 文**に `ihS`。帰納法の仮定は fuel `n` の**任意の文**について成り立つので、これが許される。`have hT₀ := StmtTy.while hc hb` は、`cases` で分解してしまう前に `while` 文全体の型付けを取っておくためのもの

`«while»` と書かれているのは、`while` が Lean の予約語だからです。コンストラクタの名前としては使えますが、tactic の分岐名として書くときは `«…»` で囲みます。

## 系

主定理から、冒頭で述べた形を取り出します。

```lean
{{#include ../../Simplean/Soundness.lean:corollaries}}
```

`EnvOk.empty`（空の文脈に空の環境は適合する）で `main` の評価に `soundness` を適用し、結果で場合分けするだけです。

## 振り返り

この証明が通ったとき、Lean は何を保証したのでしょうか。

- `evalE`/`execS` のどのケースにも、型検査をすり抜ける型エラーの経路がない
- 演算子の型付け表（`unopTy`/`binopTy`）と意味（`applyUn`/`applyBin`）が食い違っていない
- 変数のスコープ規則（再宣言禁止、枝のスコープ）が実行時の環境と整合している

逆に言えば、どれか一つを間違えると証明が通りません。たとえば `decl` の `AList.lookup Γ x = none` を外すと、`ctx_mono` が証明できなくなり、`ite` のケースで止まります。試してみる価値があります。

次の章では、同じ fuel 帰納法でコンパイラの正当性を証明します。
