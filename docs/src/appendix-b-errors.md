# 付録 B：エラーメッセージの読み方

Lean のエラーメッセージは、慣れると証明の最短ルートを教えてくれるガイドになります。この本を書く過程で実際に出たものを中心に、読み方をまとめます。

## `unsolved goals`

```text
error: unsolved goals
vmP : VMProg
s s₁ : VMState
hs : step vmP s = some s₁
⊢ (match vmP.code[s.pc]? with
    | some Instr.halt => s.stack.head?
    | x => run vmP n s₁) =
    run vmP n s₁
```

tactic ブロックが終わったのにゴールが残っています。`⊢` の下が残ったゴールです。この例では `match` が残っていて、`vmP.code[s.pc]?` が `some .halt` でないことを Lean がまだ知らないと分かります。対処は、その事実を仮定として与える（`not_halt_of_step hs`）か、`match` を `if` に書き直して `rw` で処理するか、でした。

## `Type mismatch`

```text
error: Type mismatch
  bindParams hvs x t hx
has type
  ∃ v, AList.lookup (bindParams (List.map … ps) vs) x = some v ∧ …
but is expected to have type
  ∃ v_1, AList.lookup (bindParams (y :: List.map … ps) (v :: vs)) x = some v_1 ∧ …
```

渡した証明の型と、求められている型が違います。`has type` と `but is expected` を見比べると、`bindParams (y :: …) (v :: vs)` が `(y, v) :: bindParams … vs` に展開されていないことが分かります。対処は、展開の等式（`bindParams_cons`）を先に `simp only` で適用することでした。

## `simp made no progress`

`simp` が何も書き換えられませんでした。たいていは、

- 書き換えたい式が、補題の左辺と**構文的に**一致していない（`rw` と同じ注意）
- 展開したい定義が `simp` の対象に入っていない

です。Infoview でゴールを見て、どの部分を書き換えたいのかを確認し、必要な補題を `simp [...]` に足します。

## `This simp argument is unused`

逆に、`simp [a, b, c]` の `b` が使われなかったという**警告**です。`--wfail` ではエラー扱いになります。素直に削ってください。

## `Did not find an occurrence of the pattern`

```text
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  run (compileProg P) (k + 1) { pc := 0, stack := [], locals := [], frames := [] }
in the target expression
  run (compileProg P) (k + 1) VMState.init = some v
```

`rw` は**構文的な一致**を要求します。`VMState.init` と `⟨0, [], [], []⟩` は定義上等しいのに、見た目が違うので失敗しました。`show` で見た目を揃えるか、`unfold VMState.init` してから `rw` します。

## `Dependent elimination failed`

```text
error: Tactic `cases` failed with a nested error:
Dependent elimination failed: Failed to solve equation
  some t = match typeOf P Γ e₁, … with …
```

`cases h` で `h : a = b` を分解しようとしたが、`b` がコンストラクタで始まっていない（`match` が残っている）ので、`a` と比べられません。対処は、先に `match` の対象（`typeOf P Γ e₁`）で `cases h₁ : … with` して `match` を還元することです。

## `maximum recursion depth has been reached`

`decide` で VM を 2000 ステップ走らせたときに出ました。通常の `decide` は先にエラボレータの簡約で真偽を求めるので、そこで再帰の深さの上限に当たります。`decide +kernel` に変えると解決します。

## `has been deprecated`

```text
warning: `if_pos` has been deprecated: Use `ite_eq_left` instead
```

標準ライブラリの補題名が変わりました。メッセージが新しい名前を教えてくれます。ただし新しい補題の引数の形が違うことがあるので、`#check` で確認してください。この本では `if_pos`/`if_neg` を避け、証明の中の `if` は `split` で場合分けし、`run` の補題だけは新しい名前の `ite_eq_left_of_eq_true`/`ite_eq_right_of_eq_false` で書き換えています。

## `unexpected token 'while'; expected '_' or identifier`

`while` は Lean の予約語なので、`cases h with | while … => …` の分岐名として書けません。`| «while» … => …` と書きます（第 9 章）。

## `Invalid dotted identifier notation`

`.halt` のような省略形は、期待される型が分かる場所でしか使えません。`[.halt]` のようにリストの要素型が決まらない場合は `[Instr.halt]` と書きます。

## 読み方の一般原則

1. **最初のエラーだけを見る。** 後続のエラーは最初のものの巻き添えであることが多い
2. **`⊢` の下（ゴール）を読む。** 何を示せばよいかが書いてある
3. **仮定の名前を見る。** `h✝` のように `✝` が付いた仮定は名前がないので、`rename_i` で名前を付けてから使う
4. **Infoview でカーソルを 1 行ずつ動かす。** どの tactic でゴールがどう変わったかが分かる
