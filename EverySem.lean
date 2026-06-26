import Mathlib

def every0 {α} (p q : α → Prop) : Prop := ∀ x, p x → q x

def every1 {α} : Set α → Set α → Prop := (· ⊆ ·)

def r {α} (p : α → Prop) : Set α := { x | p x }

example {α} {dog barks : α → Prop} :
  every0 dog barks ↔ every1 (r dog) (r barks)
  := by rw [every0, every1, r, r, Set.setOf_subset_setOf]
