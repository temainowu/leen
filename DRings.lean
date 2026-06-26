import Mathlib

structure SemiDivisionRing α extends Ring α where
  h a : (∀ x, a * x ≠ 1) ↔ ∃ c, c * a = 0

structure QuasiDivisionRing α extends Ring α where
  p : α → Prop
  h a : (∀ x, a * x ≠ 1) ↔ p a
