/-!
# 評価結果 `Res`

fuel 付きインタプリタの結果。`timeout`（fuel 切れ）と `err`（型エラー）を区別する。
-/

namespace Simplean

-- ANCHOR: res
/-- 評価結果：fuel 切れ、型エラー、成功。 -/
inductive Res (α : Type) where
  | timeout
  | err
  | ok (a : α)
  deriving DecidableEq, Repr

namespace Res

variable {α β : Type}

/-- 失敗はそのまま伝播し、成功なら続きを実行する。 -/
def bind : Res α → (α → Res β) → Res β
  | .timeout, _ => .timeout
  | .err, _ => .err
  | .ok a, f => f a

instance : Monad Res where
  pure := Res.ok
  bind := Res.bind
-- ANCHOR_END: res

@[simp] theorem bind_ok (a : α) (f : α → Res β) : (Res.ok a >>= f) = f a := rfl
@[simp] theorem bind_err (f : α → Res β) : ((Res.err : Res α) >>= f) = .err := rfl
@[simp] theorem bind_timeout (f : α → Res β) : ((Res.timeout : Res α) >>= f) = .timeout := rfl
@[simp] theorem pure_eq (a : α) : (pure a : Res α) = .ok a := rfl

/-- `Option` の失敗（型が合わない演算など）を `err` に写す。 -/
def ofOption : Option α → Res α
  | none => .err
  | some a => .ok a

@[simp] theorem ofOption_none : ofOption (none : Option α) = .err := rfl
@[simp] theorem ofOption_some (a : α) : ofOption (some a) = .ok a := rfl

-- ANCHOR: resok
/-- 結果が「型エラーではなく、成功していれば `Q` を満たす」。fuel 切れは許す。 -/
def Ok (Q : α → Prop) : Res α → Prop
  | .timeout => True
  | .err => False
  | .ok a => Q a
-- ANCHOR_END: resok

@[simp] theorem Ok_timeout (Q : α → Prop) : Ok Q .timeout := trivial
@[simp] theorem Ok_err (Q : α → Prop) : Ok Q .err ↔ False := Iff.rfl
@[simp] theorem Ok_ok (Q : α → Prop) (a : α) : Ok Q (.ok a) ↔ Q a := Iff.rfl

-- ANCHOR: ok_bind
/-- `Ok` は `bind` を越えて伝わる。 -/
theorem Ok.bind {Q : α → Prop} {R : β → Prop} {r : Res α} {f : α → Res β}
    (h₁ : Ok Q r) (h₂ : ∀ a, Q a → Ok R (f a)) : Ok R (r >>= f) := by
  cases r with
  | timeout => simp
  | err => simp at h₁
  | ok a => simpa using h₂ a h₁
-- ANCHOR_END: ok_bind

theorem Ok.ofOption {Q : α → Prop} {o : Option α} {a : α} (h : o = some a) (hQ : Q a) :
    Ok Q (ofOption o) := by
  subst h; simpa using hQ

theorem Ok.mono {Q R : α → Prop} {r : Res α} (h : Ok Q r) (hQR : ∀ a, Q a → R a) : Ok R r := by
  cases r with
  | timeout => simp
  | err => simp at h
  | ok a => exact hQR a h

end Res

end Simplean
