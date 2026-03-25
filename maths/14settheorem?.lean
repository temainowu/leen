import Mathlib

def limit (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N < n → abs ((a n) - L) < ε

def i (s : Set ℝ) : Set ℝ := { x | x ∉ s }

def k (s : Set ℝ) : Set ℝ := { x | ∃ a, (∀ n : ℕ, a n ∈ s) ∧ limit a x}

theorem ii : i ∘ i = id := by sorry

theorem kk : k ∘ k = k := by sorry

theorem kikikik : k ∘ i ∘ k ∘ i ∘ k ∘ i ∘ k = k ∘ i ∘ k := by sorry

def FSTH := Bool ⊕ (Bool × Fin 3 × Bool)

instance : One FSTH where
  one := Sum.inl ⊥

instance : Zero FSTH where
  zero := Sum.inl ⊤

def aux : Fin 3 → Fin 3 → Fin 3
  | 0, 0 => 1
  | 0, 1 => 2
  | 0, 2 => 0
  | 1, 0 => 1
  | 2, 0 => 0
  | 1, 1 =>

instance : Mul FSTH where
  mul
    | 1, x => x
    | x, 1 => x
    | 0, 0 => 1
    | 0, Sum.inr (a,x,b) => Sum.inr (¬a,x,b)
    | Sum.inr (a,x,b), 0 => Sum.inr (a,x,¬b)
    | Sum.inr (⊥,x,⊥), Sum.inr (⊥,y,⊥) =>

inductive ftsþ
  | E | K  | IK  | KIK  | IKIK  | KIKIK  | IKIKIK
  | I | KI | IKI | KIKI | IKIKI | KIKIKI | IKIKIKI

namespace ftsþ

 K IK KI IKI
 KIK IKIK KIKI IKIKI
 KIKIK IKIKIK KIKIKI IKIKIKI



instance : One ftsþ where
  one := E

def ftsþm : Monoid ftsþ where
  mul
    | E, x => x
    | x, E => x
    | I, K => IK
    | I, IK => K
    | I, KIK => IKIK
    | I, IKIK => KIK
    | I, KIKIK => IKIKIK
    | I, I => E
    | I, KI => IKI
    | I, IKI => KI


end fstþ
