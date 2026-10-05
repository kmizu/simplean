# コンパイラ

AST を VM の命令列に変換します。コンパイラそのものは短い関数ですが、「どんな不変条件を保っているか」を言葉にしておくと、第 10 章の証明がそのまま読めるようになります。

## 式

```lean
{{#include ../../Simplean/Compiler.lean:compileExpr}}
```

式のコードの**不変条件**：実行前のスタックが `σ` なら、実行後は `v :: σ`（値が 1 つ増えるだけで、下は変わらない）。

- リテラルと変数は 1 命令
- `unop`：部分式のコードの後に `unop op`
- `binop`：左、右の順にコードを並べ、最後に `binop op`。右が後に積まれるので、スタックトップが右オペランドになる
- `call`：引数のコードを左から順に並べ、最後に `call f`

引数列のコードの不変条件：実行後のスタックは `vs.reverse ++ σ`。最後の引数がトップに来ます。`step` の `call` が `take k` して `reverse` していたのは、この順序を元に戻すためです。

## 文

```lean
{{#include ../../Simplean/Compiler.lean:compileStmt}}
```

文のコードの不変条件：**スタックは変わらず**、ローカル変数だけが変わる。

`decl` と `assign` は同じコードになります（式を評価して `store`）。違いは型検査だけでした。

### if の配置

```text
      ┌─ compileExpr c
      │  jz (|c₁| + 1)     ── 偽なら else 節の先頭へ
      ├─ c₁ (then 節)
      │  jmp |c₂|          ── then 節が終わったら末尾へ
      ├─ c₂ (else 節)
      └─ （末尾）
```

`jz` の飛び先は「`jz` の次の命令」から `|c₁| + 1` 進んだ所、つまり `jmp` を飛び越えて `c₂` の先頭です。`jmp` の飛び先は「`jmp` の次」から `|c₂|` 進んだ所、つまり末尾です。

### while の配置

```text
   ┌──→ compileExpr c
   │     jz (|cb| + 1)     ── 偽ならループを抜ける
   │     cb (本体)
   └──── jmp (-(|cc| + |cb| + 2))   ── 先頭へ戻る
         （末尾）
```

後ろ向きのジャンプは負のオフセットです。`jmp` の次の番地から `|cc| + |cb| + 2` 戻ると、ちょうど `compileExpr c` の先頭です（`+2` は `jz` と `jmp` 自身の分）。

オフセットの計算は間違えやすい所ですが、第 10 章の証明では `omega`（整数の線形算術を解く tactic）が全部確かめてくれます。実際、この本を書いている途中でオフセットを 1 間違えたら、証明がそこで止まります。

## 関数とプログラム

```lean
{{#include ../../Simplean/Compiler.lean:compileFun}}
```

関数のコードは「本体の文、結果の式、`ret`」。文はスタックを変えず、式が戻り値を 1 つ積み、`ret` がそれを持って呼び出し元へ戻ります。

`compileFuns` は関数を順番に並べながら、各関数の入口番地を関数表に記録します。`compileProg` は `main` の式、`halt`、その後に全関数のコードという配置です。`main` は番地 0 から始まるので、VM の初期状態は `pc = 0` です。

## 実際のコードを見る

階乗プログラムをコンパイルした結果です。

```text
 0: push (int 10)
 1: call "fact"
 2: halt
 3: push (int 1)        ← fact の入口（関数表: fact ↦ entry 3, params ["n"]）
 4: store "r"
 5: push (int 0)        ← ループ先頭：条件 0 < n
 6: load "n"
 7: binop lt
 8: jz 9                ← 偽なら 8 + 1 + 9 = 18 へ
 9: load "r"
10: load "n"
11: binop mul
12: store "r"
13: load "n"
14: push (int 1)
15: binop sub
16: store "n"
17: jmp (-13)           ← 17 + 1 - 13 = 5 へ（ループ先頭）
18: load "r"            ← 結果の式
19: ret
```

`main` は `push 10; call "fact"; halt` の 3 命令です。`call` でフレームを積んで番地 3 へ飛び、ループを 10 回まわり、`ret` で番地 2 に戻って `halt` します。

`if` の例も見てみます。`if c { x := 1 } else { x := 2 }` は次のとおりです。

```text
0: load "c"
1: jz 3        ← 1 + 1 + 3 = 5（else 節）へ
2: push (int 1)
3: store "x"
4: jmp 2       ← 4 + 1 + 2 = 7（末尾）へ
5: push (int 2)
6: store "x"
```

自分で確かめるには、`Simplean/Playground.lean` の次の二行を評価してください。

```lean
#eval (compileProg factProg).code
#eval (compileProg factProg).table
```

## インタプリタと VM は本当に一致するのか

テスト（第 7 章末尾）では一致していました。しかしテストは有限個のプログラムしか見ていません。「**どんな**プログラムでも、インタプリタが値を返すなら VM も同じ値で止まる」と言うには、証明が必要です。それが第 10 章です。

その前に、第 9 章で型健全性を証明します。こちらのほうが構造が単純で、fuel 帰納法の練習になります。
