import Mathlib

/-
theorem dist_ge0 {α} [Dist α] : ∀ a b : α, 0 ≤ dist b a := by
  intro a b
  have inst : Dist α := by assumption
  sorry

theorem dist_0_of_eq {α} [Dist α] : ∀ a b : α, a = b → 0 = dist b a := by
  intro a b
  sorry

theorem dist_comm' {α} [Dist α] : ∀ a b : α, dist a b = dist b a := by
  intro a b
  sorry
-/

class M α extends HSub α α ℝ, Dist α where
  h0 : ∀ a b, dist a b = |a - b|
  h1 : ∀ a, 0 = a - a
  h2 : ∀ a b, dist a b = dist b a

class M0 α extends M α, Zero α where
  μ := dist 0
  eqdef : ∀ x, μ x = dist 0 x := by
    intro x
    rfl

@[simp]
instance : M0 ℝ where
  dist a b := |a - b|
  h0 := by simp
  h1 := by simp
  h2 := by grind

theorem h : ∀ x : ℝ, M0.μ x = |x| := by simp

noncomputable instance : Group ℝ where
  inv_mul_cancel := by
    intro a
    sorry

instance : MulLeftStrictMono ℝ where
  elim :=

/-
class Limit.{u,v} (α : Type u) (β : Type v) extends M.{v} β, M0.{u} α where
  isLimit (ord : α → ℝ) (f : α → β) (L : β) :
    ∀ ε : ℝ,
      0 < ε →
      ∃ N : α,
        ∀ n : α,
          ord N < ord n →
          dist (f n) L < ε
  isLimitVal (L : β) (f : α → β) (a : α⊕Bool) : Prop := match a with
    | Sum.inl a => isLimit ((fun x => (1 : ℝ)/x) ∘ dist a) f L
    | Sum.inr true => isLimit μ f L
    | Sum.inr false => isLimit μ f L
-/

@[simp]
def limit {α β} [M α] [M β] (f : α → β) (a : α ⊕ Bool) (L : β) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : α, ∀ n : α, 0 < dif n N → dist (f n) L < ε
    where dif := match a with
      | Sum.inl a => fun x y => dist a y - dist a x
      | Sum.inr true => fun x y => x - y
      | Sum.inr false => fun x y => y - x

theorem my_lim : limit (fun x : ℝ => x) (Sum.inl 0) 0 := by
  simp!
  intro ε hε
  use ε
  intro n hn
  rw [abs_of_pos hε] at hn
  exact hn

theorem my_lim0 : limit (fun x : ℝ => 1/x) (Sum.inr ⊤) 0 := by
  simp!
  intro ε hε
  use ε⁻¹
  intro n hn
  have h1 : ∀ x y : ℝ, x⁻¹ < y ↔ y⁻¹ < x := by
    intro x y
    constructor
    · intro h
      apply lt_of_inv_lt_inv
      rw [inv_inv]
      exact h
    intro h
    apply lt_of_inv_lt_inv
    rw [inv_inv]
    exact h
  rw [h1, lt_abs]
  apply Or.inl
  exact hn
