import Mathlib

instance : Dist ℝ where
  dist x y := |x - y|


def limit {α β} [LT α] [Dist β] (f : α → β) (L : β) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : α, ∀ n : α, n > N → dist (f n) L < ε

noncomputable def invers (x : ℝ) : ℝ :=
  1 / x

open MeasureTheory intervalIntegral

noncomputable instance : Group ℝ where
  mul := (· * ·)
  mul_assoc := by intros; rw [mul_assoc]
  one := 1
  one_mul := by intro x; rw [one_mul]
  mul_one := by intro x; rw [mul_comm, one_mul]
  inv := invers
  inv_mul_cancel := by intros; simp [invers]; rw [inv_mul_cancel]
  div_eq_mul_inv := by intros; simp [invers]; rfl

example : (limit invers) (0 : ℝ) := by
  rw [limit]
  intro ε hε
  use invers ε
  intro n hn
  simp
  simp [invers]
  simp [invers] at hn
  have h (x : ℝ) a b : x > 0 → a > b → a * x > b * x := by
    intro h1 h2
    simp
    rw [mul_comm b x, mul_comm a x]
    exact mul_lt_mul_of_pos_left h2 h1
  contrapose! h
  use ε
  use ε⁻¹
  use (n * ε⁻¹)
  constructor
  exact hε
  rw [inv_mul_cancel ε]
  contrapose! h


-- (infinite total order with addition identity > m:measurable) > m

---

noncomputable def funct (f : ℤ → ℝ) (x : ℝ) : ℝ :=
  if x - Int.floor x = 0 then f (Int.floor x) else sorry

noncomputable def line (f : ℤ → ℝ) (x : ℝ) : ℝ :=
  if x - Int.floor x = 0 then f (Int.floor x) else
    (f (n+1) - f n) * x + (n+1)* f (n) - n * f (n+1)
      where n := Int.floor x

theorem smoothF :
  ∃ F G : (ℤ → ℝ) → ℝ → ℝ,
  ∀ f : ℤ → ℝ,
  (∀ n : ℤ, f n = G f n ∧ f n = F f n)
  ∧ (∀ x : ℝ, ∃ n : ℤ, (n < x ∧ x < n + 1) →
  G f x = (f (n + 1) - f n) * x + (n + 1) * f (n) - n * f (n+1))
  ∧ (∀ n : ℤ, (∫ x in n..(n+1), F f x) = ∫ x in n..(n+1), G f x)
  ∧ (ContDiff ℝ ⊤ (F f)) := by
  use funct
  use line
  intro f
  constructor
  intro n
  constructor
  simp [line]
  simp [funct]
  constructor
  intro x
  use Int.floor x
  intro h0
  simp [line]
  sorry
  constructor
  intro n
  sorry
  simp [ContDiff, AnalyticOnNhd, AnalyticAt, HasFPowerSeriesAt]
  repeat constructor
  simp
  simp [funct]
  sorry
  intro m hm x
  simp [HasFDerivAt, ContinuousMultilinearMap.curryLeft]
  sorry
  intro m hm
  sorry
  intro i x
  sorry
  intro x
  simp [FormalMultilinearSeries]
  intro n
  sorry

-- Integers under multiplication are bigger than naturals under multiplication

-- instance : AddGroup ℕ where

instance {α} [Add α] : LE (Set α) where
  le a b := ∃ f : α → α, (∀ x ∈ b, ∀ y ∈ b, (f x + f y) = f (x + y))
                      ∧ (∃ x ∈ b, ∃ y ∈ b, f x = f y ∧ x ≠ y)
                      ∧ (∀ n ∈ a, ∃ x ∈ b, f x = n)

example : ℕ ≤ ℤ ∧ ¬ℤ ≤ ℕ

example : (∃ f : ℤ → ℕ, (∀ x y : ℤ, (f x * f y) = f (x * y))
                      ∧ (∃ x y : ℤ, f x = f y ∧ x ≠ y)
                      ∧ (∀ n : ℕ, ∃ x : ℤ, f x = n))
       ∧ (¬∃ f : ℕ → ℤ, (∀ x y : ℕ, (f x * f y) = f (x * y))
                      ∧ (∃ x y : ℕ, f x = f y ∧ x ≠ y)
                      ∧ (∀ n : ℤ, ∃ x : ℕ, f x = n)) := by
      constructor
      · use (fun x => |x|.toNat)
        constructor
        · intro x y
          simp [Int.toNat_mul]
        constructor
        · use -1
          use 1
          simp
        intro n
        use (Int.ofNat n)
        simp
      simp
      intro f h0 m n h1 h2

-- example {N : Type u} {X Y : Type v} : (∃ (g : N → X ⊕ Y), True) → (∃ (K : Type n) (J : Type m) (C : Type z) (f : C × (K → X) × (J → Y)), m + n = u) := by sorry
