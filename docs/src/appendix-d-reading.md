# 付録 D：参考文献

## Lean 4 を学ぶ

- **Theorem Proving in Lean 4**（Avigad, de Moura, Kong, Ullrich）— Lean 4 の公式入門書。依存型と証明の基礎。本書と同じ mdBook 由来の構成で、章立ての雰囲気が似ています。
  [lean-lang.org/theorem_proving_in_lean4](https://lean-lang.org/theorem_proving_in_lean4/)
- **Functional Programming in Lean**（David Thrane Christiansen）— Lean 4 を**プログラミング言語**として学ぶ本。`do` 記法、型クラス、構造的再帰と停止性の説明が丁寧です。本書の第 2 章・第 6 章の背景として最適。
  [lean-lang.org/functional_programming_in_lean](https://lean-lang.org/functional_programming_in_lean/)
- **Mathematics in Lean**（Avigad, Massot）— 数学寄りですが、tactic の使い方の説明が実践的です。
  [leanprover-community.github.io/mathematics_in_lean](https://leanprover-community.github.io/mathematics_in_lean/)
- **Lean 4 公式ドキュメント / Lean Language Reference** — 言語仕様。`#guard_msgs`、`decide +kernel` などコマンドの正確な説明はここで。
  [lean-lang.org/doc](https://lean-lang.org/doc/)

## 言語処理系の検証

- **Concrete Semantics with Isabelle/HOL**（Nipkow, Klein）— 小さな命令型言語 IMP の意味論・型システム・コンパイラ正当性を Isabelle で行う教科書。本書の構成はこの本の第 3 章・第 8 章（コンパイラ）に大きく影響を受けています。Lean ではなく Isabelle ですが、証明の構造はそのまま対応します。
  [concrete-semantics.org](http://concrete-semantics.org/)
- **Software Foundations**（Pierce ほか）— Coq による型システムと意味論の教科書。第 2 巻 *Programming Language Foundations* の「Imp」「Types」「Stlc」の章が本書の第 3〜9 章に対応します。
  [softwarefoundations.cis.upenn.edu](https://softwarefoundations.cis.upenn.edu/)
- **Xavier Leroy, "Mechanized semantics" 講義ノート**（Collège de France / Marktoberdorf）— IMP をスタック機械にコンパイルし、相対ジャンプと `code_at` 述語で正当性を証明する、本書第 10 章の直接の手本です。
- **Xavier Leroy, "Formal verification of a realistic compiler"**（CACM 2009）— CompCert の概説。forward simulation、ターゲットの決定性、小ステップ意味論の役割が説明されています。第 12 章の比較はこの論文に基づきます。

## 設計の選択について

- fuel 付きの意味論と、それに対する健全性の証明は、Amin & Rompf, *Type Soundness Proofs with Definitional Interpreters*（POPL 2017）で体系的に論じられています。本書の第 6 章・第 9 章の方針はこの論文の路線です。
- 型健全性を「進行と保存」（progress and preservation）で証明する古典的な方法は、Wright & Felleisen, *A Syntactic Approach to Type Soundness*（1994）に始まります。本書は小ステップ意味論を持たないので、この形は採っていません。

## このプロジェクト

- ソースコード：[github.com/kmizu/simplean](https://github.com/kmizu/simplean)
- Scala 3 への抽出に使った Lens：[github.com/kmizu/lean4-peg](https://github.com/kmizu/lean4-peg)
