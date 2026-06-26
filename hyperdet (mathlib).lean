import Mathlib

@[simp]
def t : ℕ → Type
  | 0 => Unit
  | Nat.succ n => Option (t n)

def decidableEqTN (n : ℕ) : DecidableEq (t n) := by
  rw [DecidableEq]
  intro a b
  induction n
  case zero =>
    apply isTrue
    rfl
  case succ n ih =>
    cases a
    case none =>
      cases b
      · apply isTrue
        rfl
      apply isFalse
      simp
    case some a =>
    cases b
    case none =>
      apply isFalse
      simp
    case some b =>
      specialize ih a b
      cases ih
      case isFalse =>
        apply isFalse
        grind
      case isTrue =>
        apply isTrue
        congr

@[simp]
def finsetTN_aux (n : ℕ) : Multiset (t n) := match n with
  | 0 => ({()} : Multiset Unit)
  | Nat.succ n => (none ::ₘ (some <$> (finsetTN_aux n)))

@[simp]
def finsetTN (n : ℕ) : Finset (t n) :=
  @Multiset.toFinset
    (t n)
    (decidableEqTN n)
    (finsetTN_aux n)

def fintypeTN (n : ℕ) : Fintype (t n) where
  elems := finsetTN n
  complete := by
    intro x
    induction n
    case zero =>
      simp!
      rfl
    case succ n ih =>
      simp!
      cases x
      case none =>
        apply Or.inl
        rfl
      case some x =>
        apply Or.inr
        use x
        constructor
        · specialize ih x
          simp! at ih
          exact ih
        rfl

def det' {α} [CommRing α] (n : ℕ) (m : Matrix (t n) (t n) α) : α :=
  @Matrix.det _ (decidableEqTN n) (fintypeTN n) α _ m
