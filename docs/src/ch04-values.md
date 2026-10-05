# 値・環境・HasType

## 値

プログラムを実行すると出てくる**値**を定義します。

```lean
{{#include ../../Simplean/Syntax.lean:val}}
```

整数と文字列はそのままです。リストは Lisp 風の **cons セル**で表します。`[1, 2, 3]` は `cons (int 1) (cons (int 2) (cons (int 3) (nil .int)))` です。

### なぜ `List Val` を使わないのか

`list (elems : List Val)` と書くほうが自然に見えます。しかしこれも入れ子の帰納型になり、`Val` の上で何かを証明するときに扱いにくくなります。cons セル表現なら `Val` は普通の帰納型で、`cases v` も `induction v` も自由に使えます。

### なぜ `nil` が型を持つのか

`head`（先頭要素）を空リストに適用したらどうなるべきでしょうか。Simplean では**例外を投げず、要素型の既定値を返す**ことにしました。

```lean
{{#include ../../Simplean/Syntax.lean:default}}
```

`head (nil t) = t.default`、`tail (nil t) = nil t` です。実行時に「この空リストの要素型は何か」が分からないと既定値が決められないので、`nil` 自身に要素型を持たせています。

この選択のおかげで、Simplean の意味論は**全域**（total）になります。実行時に起こりうる失敗は「型の合わない値に演算を適用した」という**型エラー**だけです。そして第 9 章の型健全性は、まさにその型エラーが起こらないことを示します。「空リストの head」を実行時エラーにする設計も可能ですが、その場合は「型健全性＝型エラーが起きない、ただし空リスト例外は起きうる」という、少し弱い主張になります。

`Ty.default_hasType` は「既定値は確かにその型の値である」という小さな定理で、証明は `cases t <;> constructor`——「`t` で場合分けして、それぞれ `HasType` のコンストラクタを適用」——の 1 行です。

## HasType：値が型を持つ

「値 `v` は型 `t` を持つ」という関係を、帰納的述語として定義します。

```lean
{{#include ../../Simplean/Syntax.lean:hastype}}
```

これは次の**推論規則**を Lean で書いたものです。

```text
──────────────────── (int)      ──────────────────── (str)
HasType (int n) int             HasType (str s) str

──────────────────────── (nil)
HasType (nil t) (list t)

HasType v t    HasType w (list t)
──────────────────────────────── (cons)
HasType (cons v w) (list t)
```

横線の上が前提、下が結論です。`cons` の規則は「`v` が `t` を持ち、`w` が `t` のリストなら、`cons v w` も `t` のリスト」と読みます。

重要なのは、**`cons (int 1) (str "a")` のような値には、どんな型も付かない**ことです。`cons` の規則は末尾が `list t` であることを要求するからです。`Val` としては表現できても、`HasType` の意味では「型のない値」です。型健全性（第 9 章）は、正しく型付けされたプログラムからはこういう値が決して生まれないことを保証します。

### 証明を書いてみる

`HasType (.cons (.int 1) (.nil .int)) (.list .int)` を証明するには、規則を下から上へたどります。

```lean
{{#include ../../Simplean/Tests.lean:hastype_example}}
```

`HasType.cons` に、`HasType.int 1`（`.int 1` と略記）と `HasType.nil .int` を渡しています。証明がデータ（木）として書けるのが、帰納的述語の良いところです。tactic で書くなら `by constructor <;> constructor` です。

### 値の列

関数呼び出しでは、引数の値の列と型の列を対応させる必要があります。

```lean
{{#include ../../Simplean/Ops.lean:hastypes}}
```

`HasTypes [v₁, v₂] [t₁, t₂]` は「`v₁ : t₁` かつ `v₂ : t₂`」です。外部ライブラリ（Batteries / Mathlib）には同じ役割の `List.Forall₂` がありますが、依存を増やさないよう自前で定義しています。

## 環境：名前から値へ

変数の値を記録する**環境**は、名前と値の組のリストです。型検査で使う**型文脈**も、名前と型の組のリストです。両方を同じ `AList` で表します。

```lean
{{#include ../../Simplean/AList.lean:lookup}}
```

```lean
{{#include ../../Simplean/AList.lean:update}}
```

`update` は**先頭に追加するだけ**です。古い束縛は後ろに残りますが、`lookup` は先頭一致なので新しいほうが見えます。実際の VM はスロットを上書きしますが、ここでは証明を単純にすることを優先しています。環境に関して必要な補題はこの二つだけです。

```lean
{{#include ../../Simplean/AList.lean:lookup_update}}
```

「束縛した名前を探せばその値が返る」「別の名前は影響を受けない」。どちらも `simp` で一撃です。

## 環境が文脈に適合する

型健全性の証明で中心になるのが、「環境 `ρ` が型文脈 `Γ` に適合している」という関係です。先に見ておきましょう。

```lean
{{#include ../../Simplean/Soundness.lean:envok}}
```

「`Γ` が `x : t` と言っているなら、`ρ` には `x` の値があり、その値は `t` を持つ」。これが、型検査（静的）と実行（動的）をつなぐ橋です。第 9 章で、この関係がプログラムの実行を通して保たれることを示します。

次の章では、式と文に型を付ける規則を定義します。
