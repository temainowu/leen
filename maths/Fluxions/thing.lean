import Mathlib

class Nice α extends Add α, Mul α, One α, Dist α, Zero α where
  -- mul_zero : ∀ x : α, x * 0 = 0
  zero_mul : ∀ x : α, 0 * x = 0
  -- mul_one : ∀ x : α, x * 1 = x
  one_mul : ∀ x : α, 1 * x = x
  add_zero : ∀ x : α, x + 0 = x
  zero_add : ∀ x : α, 0 + x = x
  pow : α → ℕ → α
  pow_zero : ∀ x : α, pow x 0 = 1
  pow_succ : ∀ x : α, ∀ n : ℕ, pow x (Nat.succ n) = (pow x n) * x
  dist_self : ∀ x : α, dist x x = 0
  dist_ne : ∀ x y : α, x ≠ y → 0 < dist x y

def sum {α} [Nice α] (x : α) (seq : ℕ → α) : ℕ → α
  | 0 => seq 0
  | Nat.succ n =>
      (seq (Nat.succ n) * Nice.pow x (Nat.succ n)) + (sum x seq n)

def lim_sum {α} [Nice α] (x : α) (seq : ℕ → α) (L : α) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N < n → dist (sum x seq n) L < ε

def ident_seq {α} [Nice α] : ℕ → α
  | 0 => 0
  | 1 => 1
  | Nat.succ (Nat.succ _) => 0

def ident_sum {α} [Nice α] (x : α) : ℕ → α := sum x ident_seq

lemma ident_lim {α} [Nice α] (x : α) : lim_sum x ident_seq x := by
  rw [lim_sum]
  intro ε hε
  use 0
  intro n hn
  cases n
  case zero => contradiction
  case succ n =>
    induction n
    case zero =>
      rw [sum,
          ident_seq,
          Nice.one_mul,
          Nice.pow_succ,
          Nice.pow_zero,
          Nice.one_mul,
          sum,
          ident_seq,
          Nice.add_zero,
          Nice.dist_self]
      exact hε
    case succ n ih =>
      specialize ih (by simp)
      rw [sum,
          ident_seq,
          Nice.zero_mul,
          Nice.zero_add]
      exact ih

-- I imagine I need more assumtions for taylorness
def taylorness {α} [Nice α] : Prop := ∀ f : α → α, ∃ seq : ℕ → α, ∀ x : α,
  lim_sum x seq (f x)

@[simp]
instance : Dist Bool where
  dist
    | ⊤, ⊤ => 0
    | ⊥, ⊥ => 0
    | ⊤, ⊥ => 1
    | ⊥, ⊤ => 1

@[simp]
def pow : Bool → ℕ → Bool
  | _, 0 => ⊤
  | x, Nat.succ _ => x == ⊤

@[simp]
instance NiceBools : Nice Bool where
  zero_mul := by simp
  one_mul := by simp
  add_zero := by simp
  zero_add := by simp
  pow := pow
  pow_zero x := by rfl
  pow_succ x n := by
    cases n
    · simp!
      rw [(by rfl : true = 1)]
      rfl
    simp!
    cases x
    · rfl
    rfl
  dist_self := by
    simp!
    constructor
    · rfl
    rfl
  dist_ne := by
    simp!
    rw [(by rfl : dist false true = 1),
        (by rfl : dist true false = 1)]
    simp

lemma bool_pow : @Nice.pow Bool NiceBools = pow := by rfl

def not_bool_seq : ℕ → Bool
  | 0 => 1
  | 1 => 1
  | Nat.succ (Nat.succ _) => 0

lemma bool_func_enumeration {p : (Bool → Bool) → Prop} : (
  p id ∧
  p Bool.not ∧
  p (fun _ ↦ ⊤) ∧
  p (fun _ ↦ ⊥) ) → (∀ f, p f) := by
      intro ⟨hi,hn,ht,hf⟩ f
      sorry

def true_bool_seq : ℕ → Bool
  | 0 => 1
  | Nat.succ _ => 0

def false_bool_seq : ℕ → Bool
  | _ => 0

theorem Bools_have_taylorness : @taylorness Bool NiceBools := by
  apply bool_func_enumeration
  constructor
  · use ident_seq
    exact ident_lim
  constructor
  · use not_bool_seq
    intro x ε hε
    use 1
    intro n hn
    cases n
    case zero => contradiction
    case succ n =>
      cases n
      case zero => contradiction
      case succ n =>
        rw [sum, not_bool_seq, zero_mul, zero_add]
        induction n
        case zero =>
          rw [sum, not_bool_seq, one_mul, bool_pow, pow, sum, not_bool_seq]
          cases x
          · simp!
            rw [(by rfl : false + 1 = 1)]
            simp!
            exact hε
          simp!
          rw [(by rfl : true + 1 = 0)]
          simp!
          exact hε
        case succ n ih =>
          specialize ih (by simp)
          rw [sum, not_bool_seq, zero_mul, zero_add]
          exact ih
  constructor
  · use true_bool_seq
    intro x ε hε
    use 0
    intro n
    cases n
    case zero => simp
    case succ n =>
      rw [sum, true_bool_seq, zero_mul, zero_add]
      intro h
      induction n
      case zero =>
        rw [sum, true_bool_seq]
        simp!
        exact hε
      case succ n ih =>
        specialize ih (by simp)
        rw [sum, true_bool_seq, zero_mul, zero_add]
        exact ih
  use false_bool_seq
  intro x ε hε
  use 0
  intro n
  cases n
  case zero => simp
  case succ n =>
    rw [sum, false_bool_seq, zero_mul, zero_add]
    intro h
    induction n
    case zero =>
      rw [sum, false_bool_seq]
      simp!
      exact hε
    case succ n ih =>
      specialize ih (by simp)
      rw [sum, false_bool_seq, zero_mul, zero_add]
      exact ih
