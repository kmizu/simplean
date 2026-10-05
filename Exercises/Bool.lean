import Simplean

/-!
# 演習 1：Bool 型を足す

`Ty.bool` と `Val.bool` を追加し、比較演算の結果を `Bool` にする設計を考える。
この雛形では、まず「真偽値を Int で表す現在の設計」の性質を確かめることから始める。

`sorry` を埋めていこう。
-/

namespace Exercises

open Simplean

/-- `ofBool` は常に `0` か `1` を返す。 -/
theorem ofBool_zero_or_one (b : Bool) : ofBool b = .int 0 ∨ ofBool b = .int 1 := by
  sorry

/-- `not` を 2 回適用すると元の真偽値に戻る（Int 表現の上で）。 -/
theorem not_not (b : Bool) :
    (applyUn .not (ofBool b)).bind (applyUn .not) = some (ofBool b) := by
  sorry

end Exercises
