import Mathlib

structure Rational where
  sign : Bool
  val : List ℤ
  h : val.getLast? ≠ some 0

def fact : ℕ → ℕ
  | 0 => 1
  | Nat.succ n => n.succ * fact n

def p (n : ℕ) : ℕ :=
  ∑ i : Fin (n ^ 2 + 1), (1 - ((∑ j : Fin (i.1 + 1), ((fact (j.1 - 1)) ^ 2 % j.1)) - n))

def aux : ℕ → List α → List (ℕ × α)
  | _, [] => []
  | n, x :: xs => (n,x) :: aux n.succ xs

def mapPlace {α β} (f : ℕ × α → β) (xs : List α) : List β := f <$> aux 0 xs

def pow : ℕ → ℤ → ℚ
  | 0, _ => 0
  | b, Int.ofNat p => b ^ p
  | b, Int.negSucc p => mkRat 1 (b ^ p.succ)

def sign : Bool → ℤ
  | ⊤ => 1
  | ⊥ => -1

def toQ (q : Rational) : ℚ :=
  sign q.sign * List.foldr (· * ·) 1 (mapPlace (fun (a,b) ↦ pow (p a) b) q.val)

def equal : Bool → Bool → Bool
  | ⊤, ⊤ => ⊤
  | ⊥, ⊥ => ⊤
  | _, _ => ⊥

/-
@[simp]
def zipWith0 {α β} [Zero α] (f : α → α → β) (a : List α) (b : List α) : List β :=
  a.zipWithAll (fun x y => f (x.getD 0) (y.getD 0)) b

#eval [-1] + [2,3]

example : ∀ x y : List ℤ, zipWith0 (· + ·) x y = x + y := by
  intro x y
  simp!
  induction x generalizing y
  case nil => rfl
  case cons x xs ih =>
    cases y
    case nil => rfl
    case cons y ys =>
      simp!
      exact ih ys
-/

@[simp]
def allZero : List ℤ → Prop
  | [] => True
  | 0 :: xs => allZero xs
  | _ => False

instance decAllZero {xs : List ℤ} : Decidable (allZero xs) := by
  induction xs
  case nil => apply isTrue ; simp
  case cons x xs ih =>
    cases x
    case ofNat x =>
      cases x
      case zero =>
        cases ih
        case isFalse ih =>
          apply isFalse
          simp!
          exact ih
        case isTrue ih =>
          apply isTrue
          simp!
          exact ih
      case succ x =>
        apply isFalse
        rw [allZero]
        · simp
        · simp
        grind
    case negSucc x =>
      apply isFalse
      simp!

@[simp]
def norm : List ℤ → List ℤ
  | [] => []
  | 0 :: xs => if allZero xs then [] else (0 :: norm xs)
  | x :: xs => if allZero xs then [x] else (x :: norm xs)

theorem decide_true' {α p} [Decidable p] : p → ∀ t e : α, (if p then t else e) = t := by grind

theorem decide_false' {α p} [Decidable p] : ¬p → ∀ t e : α, (if p then t else e) = e := by grind

lemma norm_nozero : ∀ xs, (norm xs).getLast? ≠ some 0 := by
  intro xs
  induction xs
  case nil => simp
  case cons x xs ih =>
    have h : allZero xs ∨ ¬allZero xs := by grind
    cases x
    case ofNat x =>
      cases x
      case zero =>
        simp
        cases h
        case inl h =>
          rw [decide_true']
          simp
        case inr h =>
          rw [decide_false', List.getLast?_cons]
          cases xs
          case nil => simp at h
          case cons x xs =>
            rw [allZero] at h


def mul (x y : Rational) : Rational where
  sign := equal x.sign y.sign
  val := norm (x.val + y.val)
  h := by
