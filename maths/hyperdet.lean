import Mathlib

structure MatrixT (m n : ℕ) where
  mat : List (List ℚ)
  col : mat.length = n
  row : ∀ i : ℕ, if h : i < n
               then (mat[i]'(by rw [col]; exact h : i < mat.length)).length = m
               else true

def allZero : List ℚ → Prop
  | [] => true
  | x :: xs => x = 0 ∧ allZero xs

def qsmul : ℚ → List ℚ → List ℚ
  | _, [] => []
  | q, x :: xs => q * x :: qsmul q xs

def size (x : List ℚ) : ℝ :=
 (List.foldr (fun a b : ℚ => a * a + b) 0 x)^(1/2)

def inList : α → List α → Prop
  | _, [] => false
  | x, y :: ys => x = y ∨ inList x ys

def decidableAllZero (x : List ℚ) : Decidable (allZero x) := by
  induction x
  case nil =>
    apply isTrue
    simp!
  case cons x xs ih =>
    have h : x = 0 ∨ x ≠ 0 := by grind
    simp!
    have decidable_and : ∀ p q, Decidable p → Decidable q → Decidable (p ∧ q) := by
      intro p q hp hq
      cases hp
      · apply isFalse
        grind
      cases hq
      · apply isFalse
        grind
      apply isTrue
      grind
    apply decidable_and
    ·
      rw [←DecidableEq.eq_def x 0]
    exact ih


def det {m n} (mat : MatrixT m n) : Hyperreal :=
  match (generalizing := true) mat.mat with
    | [] => 0
    | [x] => size x
    | x :: xs => if h : allZero x then ε * det ⟨xs, mat.col, mat.row⟩ else
                 if ∃ x', inList x' xs ∧ ∃ q, x = qsmul q x' then ε * q * det ⟨xs, mat.col, mat.row⟩ else
                  (List.foldr (fun a b : ℚ => a * a + b) 0 x)^(1/2) * det ⟨xs, mat.col, mat.row⟩

/-
{f : ℝ → ℝ | ∃a∈ℝ.∃b∈ℝ.∃d≥0. (a,a+d)∩(b,b+d) = ∅
                       ∧ ∀x∈(0,d). f(a + x) = b + x
                                 ∧ f(b + x) = a + x
                       ∧ ∀x∈(ℝ-((a,a+d)∪(b,b+d))). f(x) = x}
-/

@[simp]
def isCompofSwap (f : ℝ → ℝ) : ℕ → Prop
  | 0 => ∃ a b d : ℝ,
          (a < b) ∧
          (0 ≤ d) ∧
          (d ≤ b - a) ∧
          (∀x > 0, x < d → f (a + x) = b + x ∧ f (b + x) = a + x) ∧
          (∀x, (x < a) ∨ (a + d < x ∧ x < b) ∨ (b + d < x) → f x = x)
  | Nat.succ n => ∃ g h : ℝ → ℝ, f = g ∘ h ∧
                    isCompofSwap h n ∧
                  ∃ a b d : ℝ,
                    (a < b) ∧
                    (0 ≤ d) ∧
                    (d ≤ b - a) ∧
                    (∀x > 0, x < d → g (a + x) = b + x ∧ g (b + x) = a + x) ∧
                    (∀x, (x < a) ∨ (a + d < x ∧ x < b) ∨ (b + d < x) → g x = x)

structure SwapFuncs where
  f : ℝ → ℝ
  h : ∃ n, isCompofSwap f n

namespace SwapFuncs

instance : Group SwapFuncs where
  mul
    | ⟨xf, xh⟩, ⟨yf, yh⟩ => ⟨xf ∘ yf, by
      rcases xh with ⟨nx, xh⟩
      rcases yh with ⟨ny, yh⟩
      rw [isCompofSwap.eq_def] at xh
      cases nx
      case zero =>
        simp! at xh
        use (Nat.succ ny)
        simp
        use xf
        use yf
      case succ n =>
        simp! at xh
        rcases xh with ⟨xf1, xf2, xh⟩
        use (Nat.succ (max n ny))
        simp
        use xf1
        use (xf2 ∘ yf)
        constructor
        · rw [←Function.comp_assoc, ←xh.left]
        constructor
        · have h : ∃ m, n = ny + m ∨ ny = n + m := by
            use (max (n - ny) (ny - n))
            grind
          rcases h with ⟨m,h⟩
          cases h
          case inl h =>
            rw [h]
            rw [h] at xh
            simp
            sorry
          case inr h => sorry
        exact xh.right.right
      ⟩

end SwapFuncs
