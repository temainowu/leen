import Mathlib

def F (α : Type) [Ring α] := α → α

namespace F

@[simp]
instance [Ring α] : Zero (F α) := ⟨fun _ ↦ 0⟩

@[simp]
instance [Ring α] : One (F α) := ⟨fun _ ↦ 1⟩

@[simp]
instance [Ring α] : Neg (F α) := ⟨fun f x ↦ - f x⟩

@[simp]
instance [Ring α] : Add (F α) := ⟨fun f g x ↦ f x + g x⟩

@[simp]
instance [Ring α] : Mul (F α) := ⟨fun f g x ↦ f x * g x⟩

@[simp]
instance [Ring α] (n : ℕ) : OfNat (F α) n := ⟨fun _ ↦ n⟩

@[simp]
def nsmul [Ring α] (n : ℕ) (f : F α) := OfNat.ofNat n * f

@[simp]
instance [Ring α] : Ring (F α) where
  nsmul := nsmul
  zsmul
    | Int.ofNat n, f => nsmul n f
    | Int.negSucc n, f => Neg.neg (nsmul n.succ f)
  add_assoc a b c := by
    apply funext
    intro x
    rw [instHAdd]
    simp!
    rw [add_assoc]
  zero_add f := by
    rw [Zero.toOfNat0, instHAdd]
    simp
  add_zero f := by
    rw [Zero.toOfNat0, instHAdd]
    simp
  add_comm f g := by
    apply funext
    intro x
    rw [instHAdd]
    simp!
    rw [add_comm]
  left_distrib f g h := by
    apply funext
    intro x
    rw [instHAdd, instHMul]
    simp!
    rw [left_distrib]
  right_distrib f g h := by
    apply funext
    intro x
    rw [instHAdd, instHMul]
    simp!
    rw [right_distrib]
  zero_mul f := by
    rw [Zero.toOfNat0, instHMul]
    simp
  mul_zero f := by
    rw [Zero.toOfNat0, instHMul]
    simp
  mul_assoc f g h := by
    apply funext
    intro x
    rw [instHMul]
    simp!
    rw [mul_assoc]
  one_mul f := by
    rw [One.toOfNat1, instHMul]
    simp
  mul_one f := by
    rw [One.toOfNat1, instHMul]
    simp
  neg_add_cancel f := by
    rw [instHAdd, instNeg]
    simp
    rfl
  nsmul_zero f := by
    dsimp
    rw [instHMul]
    simp
    rfl
  nsmul_succ n f := by
    apply funext
    intro x
    dsimp
    rw [instOfNatNat, instHMul, instHAdd, instHAdd, instAddNat]
    simp!
    rw [right_distrib, one_mul]
  zsmul_zero' f := by
    dsimp
    rw [instOfNatNat, HMul.hMul, instHMul]
    simp
    rfl
  zsmul_succ' n f := by
    apply funext
    intro x
    dsimp
    rw [instOfNatNat, instHMul, instHAdd, instHAdd, instAddNat]
    simp!
    rw [right_distrib, one_mul]

end F
