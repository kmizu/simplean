/-!
# 連想リスト

環境（名前 → 値）と型文脈（名前 → 型）を同じ表現で扱う。
`List (String × α)` の先頭が最新の束縛。
-/

namespace Simplean

/-- 名前から `α` への連想リスト。先頭が最新の束縛。 -/
abbrev AList (α : Type) := List (String × α)

namespace AList

variable {α : Type}

-- ANCHOR: lookup
/-- 先頭一致で `x` の束縛を探す。見つからなければ `none`。 -/
def lookup : AList α → String → Option α
  | [], _ => none
  | (y, v) :: rest, x => if y = x then some v else lookup rest x
-- ANCHOR_END: lookup

-- ANCHOR: update
/-- `x` を `v` に束縛する。古い束縛は影に隠れる（上書きではなく先頭に追加）。 -/
def update (ρ : AList α) (x : String) (v : α) : AList α := (x, v) :: ρ
-- ANCHOR_END: update

@[simp] theorem lookup_nil (x : String) : lookup ([] : AList α) x = none := rfl

@[simp] theorem lookup_cons (y : String) (v : α) (rest : AList α) (x : String) :
    lookup ((y, v) :: rest) x = if y = x then some v else lookup rest x := rfl

-- ANCHOR: lookup_update
/-- 束縛した直後にその名前を探すと、束縛した値が返る。 -/
@[simp] theorem lookup_update_self (ρ : AList α) (x : String) (v : α) :
    lookup (update ρ x v) x = some v := by
  simp [update]

/-- 別の名前の束縛は変わらない。 -/
theorem lookup_update_other (ρ : AList α) (x y : String) (v : α) (h : x ≠ y) :
    lookup (update ρ x v) y = lookup ρ y := by
  simp [update, h]
-- ANCHOR_END: lookup_update

end AList

end Simplean
