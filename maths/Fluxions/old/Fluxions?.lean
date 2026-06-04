import Mathlib

inductive Basis where
  | I
  | O (n : ℕ)
  | E (n : ℕ)
deriving DecidableEq

namespace Basis

@[simp]
def size : Basis → ℕ
  | I => 0
  | O n => n + 1
  | E n => n + 1

@[match_pattern]
def logω : Basis → ℤ
  | I => 0
  | O n => Int.ofNat (Nat.succ n)
  | E n => Int.negSucc n

instance : LT Basis where
  lt
    | I, O _ => true
    | I, _ => false
    | E x, E y => y < x
    | E _, _ => true
    | O x, O y => x < y
    | O _, _ => false

@[match_pattern]
instance : One Basis where one := I

def mul : Basis → Basis → Basis
  | 1, y => y
  | x, 1 => x
  | E x, E y => E (x + y + 1)
  | O x, O y => O (x + y + 1)
  | O 0, E 0 => 1
  | O 0, E m => E (m - 1)
  | O (Nat.succ n), E 0 => O n
  | O (Nat.succ n), E (Nat.succ m) => mul (O n) (E m)
  | E 0, O 0 => 1
  | E 0, O (Nat.succ m) => O m
  | E (Nat.succ n), O 0 => E n
  | E (Nat.succ n), O (Nat.succ m) => mul (E n) (O m)
termination_by x y => size x + size y
decreasing_by
  · simp
    grind
  simp
  grind

@[ext]
structure 𝔽 α where
  s : α
  v : Basis
deriving DecidableEq

@[simp]
def hadd {α} [Add α] (x : 𝔽 α) : List (𝔽 α) → List (𝔽 α)
  | [] => [x]
  | v :: vs => if logω x.v = logω v.v
               then hadd ⟨(x.s + v.s),v.v⟩ vs
               else v :: hadd x vs

theorem add_nempty {α} [Add α] : ∀ (x : 𝔽 α) y, hadd x y ≠ [] := by
  intro x y
  cases y
  · simp
  case cons y ys =>
    simp
    cases x.v
    · grind
    · grind
    grind

theorem add_nempty' {α} [Add α] : ∀ (x : 𝔽 α) y, ∃ x' y', hadd x y = x' :: y' := by
  intro x y
  have h := add_nempty x y
  cases y
  · simp
  case cons y ys =>
    simp
    cases x.v
    · grind
    · grind
    grind


@[simp]
def add_list {α} [Add α] : List (𝔽 α) → List (𝔽 α) → List (𝔽 α)
  | [], [] => []
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, ys => add_list xs (hadd x ys)

@[simp]
def rem_dupl {α} [Add α] : List (𝔽 α) → List (𝔽 α)
  | [] => []
  | x :: xs => hadd x xs

@[simp]
def to_multiset {α} : List α → Multiset α
  | [] => {}
  | x :: xs => x ::ₘ to_multiset xs

def to_finset {α : Type u} [Add α] (x : List (𝔽 α)) : Finset (𝔽 α) where
  val := to_multiset (rem_dupl x)
  nodup := by
    induction x
    · simp
    case cons x xs ih =>
      simp
      cases xs
      · simp
      case cons x1 xs =>
        simp at *
        cases x1
        case mk s v =>
        simp
        let n := x.v.logω
        let m := v.logω
        rw [(by rfl : x.v.logω = n), (by rfl : v.logω = m)] at *
        induction m generalizing n
        · induction n
          · simp
            induction xs generalizing s
            · simp
            case cons x' xs hx =>
              have h := hx s


        have h1 := add_nempty' x1 xs
        contrapose! h1
        intro x' y'
        contrapose! h1
        rw [h1] at ih
        rw [h1]
        simp



        · simp at *

have h1 : ∀ s, (to_multiset (hadd { s := s, v := v } xs)).Nodup := by
          intro s'
          induction xs
          · simp
          case cons x2 xs hx' =>
            simp at *
            let n := x2.v.logω
            let m := v.logω
            rw [(by rfl : x2.v.logω = n), (by rfl : v.logω = m)] at *
            sorry


instance : Mul Basis where
  mul := mul

def add {α} [Add α] : 𝔽 α → 𝔽 α → 𝔽 α
  | [], [] => []
  | [(x,I)], [(y,I)] => [(x+y,I)]
  | [(x,E n)], [(y,E m)] => if n = m then [(x+y,E n)] else (x,E n) :: [(y,E m)]
