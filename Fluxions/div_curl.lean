import Mathlib

noncomputable instance (n) : Norm (Vector ℝ n) where
  norm v := √ (Vector.foldr (· + ·) 0 (Vector.map (· ^ 2) v))

noncomputable instance (n) : Dist (Vector ℝ n) where
  dist v u := ‖v - u‖

structure SO n where
  x : Vector ℝ n
  h : ‖x‖ = 1

def islimit {α} [Dist α] (a : ℕ → α) (L : α) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N < n → dist (a n) L < ε

instance {n} : HMul ℝ (Vector ℝ n) (Vector ℝ n) where
  hMul r v := Vector.map (r * ·) v

noncomputable def seq_aux {n : ℕ}
  (f : Vector ℝ n → Vector ℝ n)
  (x : Vector ℝ n) (d : SO n) (i : ℕ) : Vector ℝ n :=
  (↑i : ℝ) * ((f (x + (1/(↑i : ℝ) * d.x))) - f x)

structure BalD n where
  D : (Vector ℝ n → Vector ℝ n) →
  Vector ℝ n → SO n → Option (Vector ℝ n)
  hex
    (f : Vector ℝ n → Vector ℝ n)
    (x : Vector ℝ n)
    (dx : SO n) : (∃ l, islimit (seq_aux f x dx) l) → D f x dx ≠ none
  heq
    (f : Vector ℝ n → Vector ℝ n)
    (x : Vector ℝ n)
    (dx : SO n) : match (D f x dx) with
    | none => True
    | some l => islimit (seq_aux f x dx) l

def diverge {n} (i : BalD n)
  (f : Vector ℝ n → Vector ℝ n) (x : Vector ℝ n) : Option ℝ
  := 
    if none ∈ { i.D f x dx | dx : SO n} then none else some (
      ∫ z in 0..0, i.D f x
    )

def curl {n} (i : BalD n)
  (f : Vector ℝ n → Vector ℝ n) (x : Vector ℝ n) : Option (Vector ℝ n)
  := 
    if none ∈ { i.D f x dx | dx : SO n} then none else some (
      0
    )




-- how do I calculate the
-- div and curl of some (f : Vector ℝ n → Vector ℝ n)
-- given only (D f)
-- I think the div is just integrating the balls
