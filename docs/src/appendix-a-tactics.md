# 付録 A：tactic チートシート

この本の証明で使った tactic を、使い方の形で並べます。「ゴール」は今示すべき命題、「仮定」は使える前提です。

## ゴールと仮定を動かす

| tactic | 何をするか | この本での使い方 |
|---|---|---|
| `intro x y h` | `∀ x y, P → Q` のゴールから `x`, `y`, `h : P` を仮定に取り、ゴールを `Q` にする | 定理の冒頭 |
| `exact e` | ゴールにぴったり合う証明 `e` を与えて閉じる | `exact ihE _ _ _ _ hres hρ'` |
| `refine e` | `e` の中の `?_` を新しいゴールとして残す `exact` | `refine (… ).bind fun v hv => ?_` |
| `have h := e` / `have h : P := by …` | 補助的な事実を仮定に加える | `have hT₀ := StmtTy.while hc hb` |
| `obtain ⟨a, b, c⟩ := h` | `∃` や `∧` の仮定を分解して名前を付ける | `obtain ⟨ihE, ihA, ihS⟩ := ih` |
| `show P` | ゴールを（定義上等しい）`P` の形に書き直す | `VMState.init` を `⟨0, [], [], []⟩` に |
| `rename_i h` | 名前の付いていない仮定（`h✝`）に名前を付ける | `split` の後の条件 |
| `subst h` | `h : x = e` で `x` を `e` に置き換える | `subst hev` |

## 場合分けと帰納法

| tactic | 何をするか | この本での使い方 |
|---|---|---|
| `cases h with \| c₁ … => … \| c₂ … => …` | `h` をコンストラクタごとに場合分け | `cases hT with \| lit n => … \| var hx => …` |
| `cases h : e with …` | 式 `e` の値で場合分けし、`h : e = …` を残す | `cases h₁ : evalE P n ρ e₁ with` |
| `induction h with …` | `h` に関する帰納法（帰納法の仮定が付く） | `ctx_mono`、`stepN_add` |
| `split` / `split at h` | `if` や `match` で場合分け | 引数個数検査の `if` |
| `by_cases h : P` | `P` が成り立つ場合と成り立たない場合に分ける | `by_cases hxy : x = y` |
| `rcases` / `match` | より柔軟な分解 | — |

**fuel 帰納法**は `induction` ではなく、定理を再帰関数として書く形で行いました（`soundness`、`compile_correct`、`fuel_mono`）。`| 0 => …` と `| n + 1 => … (soundness hP n) …` のパターンです。

## 書き換えと簡約

| tactic | 何をするか | 注意 |
|---|---|---|
| `rw [h]` / `rw [h] at h'` | 等式 `h : a = b` で `a` を `b` に書き換える | 左辺が**そのまま**現れている必要がある |
| `rw [f]` | 関数 `f` の定義（等式補題）で 1 段展開 | `rw [typeOf] at h` |
| `simp [l₁, l₂]` | 補題と定義で簡約し、閉じられれば閉じる | 何が起きたか追えなくなったら `simp only` に |
| `simp only [l₁] at h ⊢` | 指定した補題**だけ**で簡約 | 証明を安定させたいとき |
| `simpa using h` | 簡約してから `h` で閉じる | `simpa [evalE] using h` |
| `dsimp only` | 定義上の簡約だけ（`match` の還元など） | `match (some fd) with …` を還元 |
| `unfold f` | 定義を展開 | `unfold checkFun at h` |

`simp` に渡す補題が使われなかったと警告されたら、削ってください。この本は `--wfail`（警告をエラーに）でビルドしているので、不要な補題は許されません。

## 自動化

| tactic | 何をするか |
|---|---|
| `omega` | 自然数・整数の線形算術（`+`、定数倍、`≤`、`Int.toNat`、型変換）を自動で解く |
| `decide` | 決定可能な命題を計算で判定して閉じる（`decide +kernel` はカーネルに直接評価させる） |
| `rfl` | 両辺が定義上等しい等式を閉じる |
| `trivial` | `True` などの自明なゴール |
| `constructor` | ゴールの帰納的述語の、最初に合うコンストラクタを適用 |
| `assumption` | 仮定の中にゴールと一致するものがあれば閉じる |
| `contradiction` | 仮定の矛盾（`False`、`none = some _` など）から閉じる |
| `absurd h hn` | `h : P` と `hn : ¬P` から何でも導く（`exact absurd h hn`） |

## 組み合わせ

| 記法 | 意味 |
|---|---|
| `t₁ <;> t₂` | `t₁` が作った**すべての**ゴールに `t₂` を適用 |
| `try t` | `t` が失敗しても続行 |
| `first \| t₁ \| t₂` | `t₁` を試し、失敗したら `t₂` |
| `repeat' t` | 可能な限り繰り返す |
| `all_goals t` | 残っている全ゴールに `t` |
| `·` | ゴールを一つ選んでブロックで証明（インデントで範囲を示す） |

`applyUn_sound` の証明 `cases op <;> cases hv <;> simp_all […] <;> subst_vars <;> (repeat' first | …)` は、これらを組み合わせて数十ケースを 1 行で片づけています。

## 自分でマクロを作る

```lean
macro "state_eq" : tactic =>
  `(tactic| ((try simp only [...]); (try omega)))
```

同じ tactic 列を何度も書くなら、`macro` で名前を付けられます（`VMLemmas.lean` 末尾の `state_eq`）。
