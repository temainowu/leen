import Mathlib

@[simp]
def ex {α} (p s : α → Prop) : Prop := ∃ a : α, s a ∧ p a

@[simp]
def al {α} (p s : α → Prop) : Prop := ∀ a : α, s a → p a

@[simp]
def i (p : α → Prop) (x : Prop) (a : α) : Prop := p a → x

theorem left_adj :
  ∀ (p x : α → Prop) (y : Prop), (ex p x → y) ↔ (∀ a, x a → (i p y) a) := by
    intro p x y
    simp

theorem right_adj :
  ∀ (p y : α → Prop) (x : Prop), (∀ a, (i p x) a → y a) ↔ (x → al p y) := by
    intro p x y
    simp
    constructor
    · intro h y'
      sorry
    intro h a hp
    specialize h (hp (by
      apply h

    ))

---

@[simp]
def Model {α} (T : (α → Prop) → Prop) (x : α) : Prop := ∀ p, T p → p x 

@[simp]
def Ther {α} (S : α → Prop) (p : α → Prop) : Prop := ∀ x, S x → p x 

example : ∀ (S : α → Prop) (T : (α → Prop) → Prop), 
  (∀ x, S x → Model T x) ↔ (∀ p, Ther S p → T p) := by
  simp! 
  intro S T
  constructor 
  · intro hSM p hÞ
    sorry
  intro hÞT x hS p hT
  sorry
