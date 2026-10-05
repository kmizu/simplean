# 証明 3：決定性と検査器の健全性

この章では、残っていた三つのことを片づけ、最後に全部をつなぎます。

1. fuel の与え方に依らず結果が決まること（意味論の決定性）
2. VM の結果も fuel に依らないこと
3. 型健全性・コンパイラ正当性・検査器の健全性を一つの定理に束ねること

## fuel 単調性

第 6 章の疑問——「fuel で結果が変わるなら意味論と呼べるのか」——に答えます。

```lean
{{#include ../../Simplean/Determinism.lean:monoall}}
```

```lean
{{#include ../../Simplean/Determinism.lean:fuel_mono}}
```

「fuel `n` で `ok v` なら fuel `n + 1` でも `ok v`」。証明は三たび fuel 帰納法で、各ケースは「部分評価が `ok` なら帰納法の仮定で fuel を増やしても `ok`、あとは同じ」の繰り返しです（`Determinism.lean` の `monoE_succ`/`monoA_succ`/`monoS_succ`）。`evalE_mono` は `n ≤ m` の形に一般化したもので、`Nat.le` に関する帰納法です。

## 決定性

```lean
{{#include ../../Simplean/Determinism.lean:det}}
```

fuel `n` で `v`、fuel `m` で `v'` が出たなら、両方を `max n m` まで増やせば同じ fuel での結果になり、関数なので一致します。したがって「ある fuel で値が出る」という関係は**部分関数**です。これが「fuel 付きインタプリタは意味論として正当である」ことの根拠です。

## VM の決定性

VM 側にも同じ性質があります。

```lean
{{#include ../../Simplean/VMLemmas.lean:run_lemmas}}
```

`run_mono` は「fuel を 1 増やしても結果は変わらない」、`run_det` はそこから導かれる決定性です。`run_of_stepN` は第 10 章で使った、到達可能性と `run` をつなぐ補題です。

`vm_result_unique`（`Determinism.lean`）は、`main_correct` と `run_det` を合わせたもので、「VM がどんな fuel で何を返しても、それは参照意味論の結果と一致する」と言います。VM が途中で不正な状態になって別の値を返す、ということは起きません——元のプログラムが停止する限り。

## 統合定理

```lean
{{#include ../../Simplean/Determinism.lean:final}}
```

`final` は、第 9 章の `evalProg_hasType` と第 10 章の `main_correct` を並べただけです。定理の内容が二つの独立した証明の積になっていることが、証明項の形（`⟨…, …⟩`）からそのまま見えます。

`final_checked` は型検査器を通ったプログラムについての版で、`checkProg_sound`（第 5 章）で前提を作っています。具体的なプログラムについては、

```lean
example : HasType (.int 3628800) .int ∧
    ∃ k, run (compileProg Examples.factProg) k VMState.init = some (.int 3628800) :=
  final_checked (by decide) Tests.fact_eval
```

のように、`checkProg factProg = some .int` を `decide` で、`evalProg factProg 100 = .ok …` をテストの定理で渡せば、階乗プログラムについての完全な保証が手に入ります。

## 何に依存しているか：`#print axioms`

Lean の証明は、最終的にいくつかの**公理**に依存します。`#print axioms` でそれを表示できます。

```lean
{{#include ../../Simplean/Tests.lean:axioms}}
```

`#guard_msgs in` は「次のコマンドの出力が、直前のコメントと一致すること」を検査するコマンドです。一致しなければビルドが失敗するので、公理の集合をテストとして固定できます。

出てくる公理は三つだけです。

- `propext`：命題の外延性（同値な命題は等しい）
- `Classical.choice`：選択公理
- `Quot.sound`：商型の健全性

これらは Lean の標準ライブラリが日常的に使う、数学的に標準的な公理です。もし証明のどこかに `sorry`（証明の省略）があれば `sorryAx` が、`native_decide`（コンパイルした実行結果を信じる）を使えば `Lean.ofReduceBool` が現れます。この本の証明にはどちらもありません。`decide +kernel` も、カーネルが自分で計算して確かめるだけなので公理を増やしません。

## 証明全体の構造

ここまでの定理の依存関係をまとめます。

```text
 Ops.applyUn_sound ─┐
 Typing.ctx_mono  ──┼→ Soundness.soundness ──→ evalProg_hasType ─┐
 EnvOk.*          ──┘                                            │
                                                                 ├→ Determinism.final
 VMLemmas.step_*  ─┐                                             │
 VMLemmas.CodeAt.* ┼→ Correctness.compile_correct ─┐             │
 Compiler         ─┘                               ├→ main_correct ┘
 compileFuns_ok ───────────────→ compileProg_tableOk ┘
 Checker.typeOf_sound → checkProg_sound → final_checked
 Determinism.fuel_mono → evalE_det → evalProg_det
```

次の章では、この図に**含まれていない**ものを正直に書きます。
