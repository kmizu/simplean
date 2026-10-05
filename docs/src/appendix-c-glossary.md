# 付録 C：用語集

| 用語 | 英語 | 意味 |
|---|---|---|
| 抽象構文木 | AST, abstract syntax tree | プログラムを木構造のデータとして表したもの。第 3 章 |
| 帰納型 | inductive type | コンストラクタの有限個の組み合わせで値が作られる型。`inductive` |
| 帰納的述語 | inductive predicate | `Prop` を返す帰納型。推論規則の集まり。`HasType`、`ExprTy` |
| 入れ子の帰納型 | nested inductive | 定義の中で `List 自分自身` などを使う帰納型。`Expr.call` |
| 相互帰納 | mutual induction / mutual recursion | 複数の型や関数が互いを参照する定義。`mutual … end` |
| 構造的再帰 | structural recursion | 引数の構造が小さくなる再帰。Lean が自動で停止性を認める |
| fuel（燃料） | fuel | 停止しないかもしれない計算を、回数の上限つきで定義する技法。第 6 章 |
| 全域 | total | すべての入力に対して結果が定義されている |
| definitional interpreter | — | 言語の意味を、その言語のインタプリタとして定義する方法 |
| 型健全性 | type soundness | 型検査を通ったプログラムは実行時に型エラーを起こさない。第 9 章 |
| 型文脈 | typing context | 変数名から型への対応。`Γ`（ガンマ） |
| 環境 | environment | 変数名から値への対応。`ρ`（ロー） |
| 適合 | — | 環境が型文脈と整合していること。`EnvOk` |
| 健全性（検査器の） | soundness | 検査器が受理したものは仕様でも正しい |
| 完全性（検査器の） | completeness | 仕様で正しいものは検査器も受理する（本書では未証明） |
| forward simulation | 前向きシミュレーション | 元の実行 1 つに対し、変換後の実行が存在することを示す証明の形。第 10 章 |
| 決定性 | determinism | 同じ入力からは同じ結果しか出ない |
| 単調性（fuel の） | monotonicity | fuel を増やしても成功した結果は変わらない。第 11 章 |
| 相対ジャンプ | relative jump | 現在位置からのオフセットで飛び先を指定するジャンプ |
| フレーム | frame | 関数呼び出しの戻り先などを保存する記録 |
| オペランドスタック | operand stack | 演算の対象となる値を積むスタック |
| tactic | — | 証明を進めるための命令。付録 A |
| ゴール | goal | 今示すべき命題。Infoview で `⊢` の後に表示される |
| 公理 | axiom | 証明なしに認める命題。`#print axioms` で確認。第 11 章 |
| `Prop` | — | 命題の型。証明の対象 |
| `Bool` | — | 真偽値の型。計算の対象 |
| `Option α` | — | 値があるか無いか。`some a` / `none` |
| `do` 記法 | do-notation | モナドの計算を手続き風に書く構文 |
| カーネル | kernel | Lean の証明を最終的に検査する小さなプログラム |
| `decide` | — | 決定可能な命題を計算で判定する tactic。`+kernel` でカーネルに評価させる |
| `sorry` | — | 証明の省略。残っていると `sorryAx` 公理に依存する |
