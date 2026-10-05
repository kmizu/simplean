# 証明 2：コンパイラ正当性

**コンパイラ正当性**は、「コンパイルしてもプログラムの意味が変わらない」という定理です。Simplean での形は次のとおりです。

> インタプリタが `evalProg P n = .ok v` を返すなら、`compileProg P` を VM で実行すると `v` で停止する。

このように「元の実行 1 つに対して、変換後の実行が存在する」ことを示す形を **forward simulation**（前向きシミュレーション）と呼びます。CompCert など実用的な検証済みコンパイラも、基本はこの形です。

## 道具

### 到達可能性 `Reaches`

```lean
{{#include ../../Simplean/VMLemmas.lean:reaches}}
```

`Reaches vmP s s'` は「`s` から有限ステップで `s'` へ行ける」です。反射律、推移律、1 ステップの三つで組み立てます。`Reaches.cast` は「等しい状態に書き換える」だけの補題ですが、証明の最後で番地の算術（`pc + (a + b)` と `pc + a + b` の違いなど）を吸収するために頻繁に使います。

### コードの配置 `CodeAt`

```lean
{{#include ../../Simplean/VMLemmas.lean:codeat}}
```

`CodeAt C pc c` は「命令列 `c` が `C` の番地 `pc` から置かれている」。`c₁ ++ c₂` が置かれていれば、`c₁` は `pc` から、`c₂` は `pc + |c₁|` から置かれている（`append_left`/`append_right`）。コンパイラが `++` でコードを組み立てているので、この二つでコードを分解していけます。

### 命令ごとの 1 ステップ補題

```lean
{{#include ../../Simplean/VMLemmas.lean:step_lemmas}}
```

「番地 `pc` に `push v` があるなら、状態 `⟨pc, σ, ρ, F⟩` の次は `⟨pc + 1, v :: σ, ρ, F⟩`」といった補題を命令ごとに用意します。証明はどれも `simp [step, h.fetch, …]` の 1 行で、`step` の定義を展開するだけです。

## 主張

```lean
{{#include ../../Simplean/Correctness/Expr.lean:tableok}}
```

```lean
{{#include ../../Simplean/Correctness/Expr.lean:simall}}
```

`TableOk` は「VM の関数表が元のプログラムと整合している」。各関数について、表の入口番地にその関数のコードが置かれていることを言います。

`SimAll P vmP n` が本体です。式についての部分を読むと、

> fuel `n` で `e` が `v` に評価され、`compileExpr e` が番地 `pc` に置かれているなら、状態 `⟨pc, σ, ρ, F⟩` から `⟨pc + |compileExpr e|, v :: σ, ρ, F⟩` へ到達する。

**任意の** `pc`、`σ`、`F` について成り立つのがポイントです。どこに置かれていても、スタックの下に何があっても、何段の呼び出しの中にいても、式のコードは「値を 1 つ積んで、コードの長さぶん進む」。この一般性のおかげで、部分式のコードが別の場所に置かれていても帰納法の仮定が使えます。

注意：**この定理は型付けを仮定していません。** 評価が `.ok v` を返したこと自体が、「すべての演算が成功した」ことを含んでいるからです。型健全性とコンパイラ正当性は独立した定理で、最後（第 11 章）に合流します。

## 式の場合

```lean
{{#include ../../Simplean/Correctness/Expr.lean:simE}}
```

第 9 章と同じ fuel 帰納法ですが、場合分けの対象が違います。第 9 章は型付けの導出（`cases hT`）でしたが、こちらには型付けの仮定が無いので、`cases e` で式の形を直接場合分けし、評価 `hev` を `cases h₁ : evalE P n ρ e₁ with` で分解します（`timeout`/`err` の枝は `hev` と矛盾するので `simp at hev` で消えます）。

- `binop`：`hc : CodeAt C pc (c₁ ++ c₂ ++ [binop op])` を `List.append_assoc` で右結合に直してから、`append_left`/`append_right` で三つに分解。`c₁` に帰納法の仮定 → `c₂` に帰納法の仮定（スタックは `v₁ :: σ`）→ `step_binop`。`Reaches.trans` でつなぐ
- `call`：引数のコードに `ihA`、`step_call`、本体の文に `ihS`、結果の式に `ihE`、`step_ret`。`step_call` が取り出す引数 `(vs.reverse ++ σ).take k` を `vs.reverse` に戻すのに `List.take_left'`（長さが一致すれば先頭部分がそのまま取れる）を使う。ここで第 6 章の**引数個数検査**（`hlen`）が長さの一致を保証している

最後の `(…).cast rfl (by state_eq)` は、到達した状態の番地 `pc + |c₁| + |c₂| + 1` と、主張の `pc + |c₁ ++ c₂ ++ [binop]|` が同じであることを示します。`state_eq` は `VMLemmas.lean` の末尾で定義した小さな tactic マクロで、リストの長さを展開して `omega` に渡すだけです。

```lean
{{#include ../../Simplean/Correctness/Expr.lean:simA}}
```

引数列は「先頭の式を評価して積み、残りを `v :: σ` の上で評価する」。結果のスタック `(v :: vs').reverse ++ σ = vs'.reverse ++ v :: σ` は `state_eq` がリストの補題で整えます。

## 文の場合

```lean
{{#include ../../Simplean/Correctness/Stmt.lean:simS}}
```

- `ite`：条件の値が `int k` であることを `cases v` で確認（他の形なら評価が `err` で矛盾）。`split at hex` で `k = 0` を場合分け。`k = 0` なら `step_jz_zero` で else 節の先頭へ飛び、`ihS`。飛び先の番地 `jumpTarget (pc + |cc|) (|c₁| + 1)` が else 節の番地と一致することは `state_eq`（`jumpTarget` を展開して `omega`）が示す。`k ≠ 0` なら `step_jz_nonzero` で落ちて then 節に `ihS`、`step_jmp` で末尾へ
- `while`：`k = 0` なら `step_jz_zero` でループを抜ける。そうでなければ本体に `ihS`、`step_jmp` で**先頭へ戻り**、そこで `while` 文全体に対する帰納法の仮定 `ihS … hex hc₀` を使う。`hc₀` は `simp` で分解する前の `hc` を取っておいたもの。ここでも「fuel が 1 小さい任意の文」という仮定の形が決定的に効く

## 束ねる

```lean
{{#include ../../Simplean/Correctness/Stmt.lean:compile_correct}}
```

第 9 章の `soundness` と同じ形です。

## 関数表の整合性

`compile_correct` は `TableOk` を仮定していました。`compileProg` が実際にそれを満たすことを示します。

```lean
{{#include ../../Simplean/Correctness/Stmt.lean:tableok_proof}}
```

`compileFuns_ok` は関数列に関する帰納法です。「ここまでに置いたコード `pre` の長さが現在の番地 `pos`」を不変条件として持ち回り、探している関数が先頭ならその場で、そうでなければ `pre ++ compileFun fd₀` を新しい `pre` にして再帰します。関数表の検索 `AList.lookup` と関数定義の検索 `List.find?` がどちらも**先頭一致**なので、同名の関数があっても同じものが選ばれます。

## プログラム全体

```lean
{{#include ../../Simplean/Correctness/Stmt.lean:main_correct}}
```

`compileProg P` のコードは「`main` のコード、`halt`、関数群」なので、`main` のコードは番地 0 に、`halt` は番地 `|compileExpr P.main|` に置かれています。`compile_correct` で `⟨0, [], [], []⟩` から `⟨|main|, [v], [], []⟩` へ到達し、そこで `run_halt` が `v` を返します。`run_of_stepN` は「`k` ステップで `s'` に到達したなら、`run (k + j) s = run j s'`」という、到達可能性と `run` をつなぐ補題です。

## 何を証明し、何を証明していないか

証明したのは「インタプリタが**止まって値を返す**なら、VM も止まって同じ値を返す」です。VM は決定的（`step` は関数）なので、この場合 VM の実行はただ一つに決まり、途中で不正な状態になることもありません（第 11 章 `vm_result_unique`）。

証明していないのは、インタプリタが**止まらない**（どんな fuel でも `timeout`）ときに VM も止まらないこと、そして「VM が止まったらインタプリタも止まる」という逆向きです。第 12 章で詳しく述べます。
