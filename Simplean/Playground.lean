import Simplean.Determinism
import Simplean.Examples

/-!
# 遊び場

チュートリアルの `#eval` を試すためのファイル。必要な import と `open` が済んでいるので、
このファイルの末尾に式を書き足せば、そのまま評価できる。
-/

open Simplean Simplean.Examples

-- ANCHOR: playground
#eval evalProg factProg 100          -- 参照意味論：10! = 3628800
#eval evalProg factProg 5            -- fuel 不足：timeout
#eval evalProg illAddStr 10          -- 型エラー：err
#eval checkProg factProg             -- 型検査：some int
#eval checkProg illAddStr            -- 型検査：none
#eval (compileProg factProg).code    -- コンパイル結果の命令列
#eval (compileProg factProg).table   -- 関数表
#eval run (compileProg factProg) 1000 .init   -- VM で実行
-- ANCHOR_END: playground
