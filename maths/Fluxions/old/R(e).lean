import Mathlib

theorem cases0 : ∀ x : ℚ, x = 0 ∨ x ≠ 0 := by grind

def div : List ℚ → List ℚ → Option (List ℚ)
  | _, [] => none
  | [], _ => some []
  | xs, [y] => some (List.map (· / y) xs)
  | xs, y :: ys => if y = 0 then div (0 :: xs) ys else none

def gcd : List ℚ → List ℚ → List ℚ
  | [], [] => []


structure 𝔽 where
  n : List ℚ
  d : List ℚ
  h0 : d ≠ []
  h1 : ∀ x, div n x = none ∨ div d x = none
  h2 : n.getLast? ≠ some 0
  h3 : d.getLast h0 ≠ 0

@[simp]
def zipWith {α β} [Zero α] (f : α → α → β) (a : List α) (b : List α) : List β :=
  match (generalizing := true) a, b with
    | [], [] => []
    | x :: xs, [] => f x 0 :: zipWith f xs []
    | [], y :: ys => f 0 y :: zipWith f [] ys
    | x :: xs, y :: ys => f x y :: zipWith f xs ys
termination_by a.length + b.length

@[match_pattern]
instance : Zero (List ℚ) where
  zero := []

@[simp]
instance : CommSemiring (List ℚ) where
  add := zipWith (· + ·)
  mul := zipWith (· * ·)
  zero := 0
  one := [1]
  nsmul n := List.map (n * ·)
  zero_add := by
    intro a
    cases a
    · rw [Zero.zero.eq_def]
  add_comm := by sorry
  mul_assoc := by sorry
  mul_one := by sorry
  one_mul := by sorry
  left_distrib := by sorry
  right_distrib := by sorry

namespace 𝔽

instance : Field 𝔽 where

end 𝔽
