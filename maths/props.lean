import Mathlib
import Mathlib.Data.Multiset.ZeroCons

def commute {α} (f : α → α → α) (β : Type) : Prop :=
  ∃ g : (Multiset β → β),
  ∃ F : α → β,
  ∃ F' : β → α,
  ∀ x y : α,
  F' (F x) = x ∧ f x y = F' (g {F x, F y})

def commute' {α} (f : α → α → α) : Prop :=
  ∀ x y : α, f x y = f y x

def fold {α}
  (h : (f : α → α → α) → (a : α) → (b : α) → f a b = f b a)
  (f : α → α → α) (e : α) (xs : Multiset α) : α :=
  Multiset.recOn xs e (by
  intro a m c
  exact (f a c)) (by sorry)

def ident (n : Nat) : Nat := n

example : (∀ f : Nat → Nat → Nat, ∃ α : Type, commute' f ↔ commute f α) := by
  intro f
  use Nat
  rw [commute, commute']
  apply Iff.intro
  intro h
  have h2 : ∀ (f : Nat → Nat → Nat) (a b : Nat), f a b = f b a := by intro a b; exact h a b
  use (fold h2 f 0)
  have hid n : ident n = n := by rfl
  use ident
  use ident
  intro x y
  rw [hid x, hid x, hid y, hid (fold h2 f 0 {x, y})]
  constructor
  rfl
  have hfold e k : fold h2 f e k = Multiset.recOn k e (by
  intro a m
  apply f
  exact e) (by
  intro a a' m b
  rfl) := by sorry


example {α β} : ∀ p : α → β → Prop, ((∀ x : α, ∃ y : β, p x y) ↔ ∃ f : α → β, ∀ x : α, p x (f x)) := by
  intro p
  constructor
  · intro h
    contrapose! h
    have ha : Nonempty α ∨ ¬Nonempty α := by grind
    have hb : Nonempty β ∨ ¬Nonempty β := by grind
    cases ha
    case inl ha =>
      have a : α := by apply Classical.choice ha
      cases hb
      case inl hb =>
        have b : β := by apply Classical.choice hb
        have f : α → β := by
          intro a'
          use b
        specialize h f
        contrapose! h
        intro x
        specialize h x
        contrapose! h
        intro y

  intro h x
  rcases h with ⟨f, h⟩
  use f x
  contrapose! h
  use x
