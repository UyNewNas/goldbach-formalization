
Examples:
 * `(1, 2).map (· + 1) (· * 3) = (2, 6)`
 * `(1, 2).map toString (· * 3) = ("1", 6)`
-/
@[implicit_reducible] def Prod.map {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂}
    (f : α₁ → α₂) (g : β₁ → β₂) : α₁ × β₁ → α₂ × β₂
  | (a, b) => (f a, g b)

@[simp] theorem Prod.map_apply (f : α → β) (g : γ → δ) (x) (y) :
    Prod.map f g (x, y) = (f x, g y) := rfl

-- We add `@[grind =]` to these in `Init.Data.Prod`.
@[simp] theorem Prod.map_fst (f : α → β) (g : γ → δ) (x) : (Prod.map f g x).1 = f x.1 := rfl
@[simp] theorem Prod.map_snd (f : α → β) (g : γ → δ) (x) : (Prod.map f g x).2 = g x.2 := rfl

/-! # Dependent products -/

