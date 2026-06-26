import Mathlib

@[simp]
def isEven : ℕ → Prop
  | 0 => True
  | 1 => False
  | Nat.succ (Nat.succ n) => isEven n

structure EvenN where
  number : ℕ
  is_even : isEven number

def add2 : EvenN → EvenN
  | ⟨a, a_is_even⟩ => {
    number := a + 2
    is_even := by
      rw [isEven]
      assumption
  }

lemma add2' : ∀ n : ℕ, isEven n → isEven (n + 2) := by
  intro n h
  rw [isEven]
  assumption

@[simp]
instance : Zero EvenN := ⟨0, by simp⟩

@[simp]
def Esucc (x : EvenN) : EvenN := {
  number := x.number.succ.succ
  is_even := by simp! ; exact x.is_even
}

theorem even_induction (p : EvenN → Prop)
  (zero : p 0)
  (suc2 : ∀ a, p a → p (Esucc a)) :
    ∀ a : EvenN, p a
  | ⟨0, h⟩ => zero
  | ⟨Nat.succ (Nat.succ x), h⟩ => by
    apply suc2 ⟨x, by rw [isEven] at h ; exact h⟩
    apply even_induction
    case zero => exact zero
    case suc2 => exact suc2

def add (a b : EvenN) : EvenN := {
    number := a.number + b.number
    is_even := by
      revert a b
      apply even_induction
      case zero =>
        apply even_induction
        case zero => simp
        case suc2 =>
          intro a h
          simp!
          simp! at h
          exact h
      case suc2 =>
        intro a ih b
        rw [add_comm]
        simp!
        rw [add_comm]
        apply ih
  }
