import Mathlib

def limit (f : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N < n → |L - f n| < ε

theorem limx : ∀x : ℝ, 0 ≤ x → limit (fun a => ⌊a*x⌋/a) x := by
  intro x hx ε hε
  use 0
  intro n hn
  simp!
  induction n
  case zero => simp! at hn
  case succ n ih =>
    sorry
