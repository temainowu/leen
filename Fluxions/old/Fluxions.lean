import Mathlib

-- Class Defs

class FreeAddCommSemiring.{u} (α : Type u) extends
  AddCommMagma α,
  AddSemigroup α,
  CommMagma α,
  Semigroup α,
  MulOneClass α,
  HMul ℕ α α where
  left_distrib : ∀ x y z : α, x * (y + z) = x * y + x * z
  one_hMul : ∀ (x : α), (1 : ℕ) * x = x

class PosNegSet α extends Neg α, LT α, Add α where
  posv : α → Prop
  negv (x : α) : Prop := posv (-x)
  posv_iff_nnegv : ∀ x : α, (posv x ↔ ¬negv x) ∨ (∀ y, y + x = y)
  posv_add : ∀ x y, posv x → posv y → posv (x + y)
  negv_add : ∀ x y, negv x → negv y → negv (x + y)

class OpsWithQ α extends HAdd ℚ α α, HMul ℚ α α, HPow α ℚ α

instance : PosNegSet ℚ where
  posv := (0 < ·)
  posv_iff_nnegv := by grind
  posv_add := by grind
  negv_add := by grind

-- Suc

inductive Suc (α : Type u) where
  | Ø
  | S (x : α)

class ToSuc α where toSuc : α → Suc α

namespace Suc

@[simp]
instance {α} : Zero (Suc α) where zero := Ø

@[simp]
instance {α} [One α] : One (Suc α) where
  one := S 1

@[simp]
instance {α} [Add α] : Add (Suc α) where
  add x y := match (generalizing := true) x, y with
    | 0, y => y
    | x, 0 => x
    | S x, S y => S (x+y)

@[simp]
instance {α} [Mul α] : Mul (Suc α) where
  mul x y := match (generalizing := true) x, y with
    | 0, _ => 0
    | _, 0 => 0
    | S x, S y => S (x*y)

@[simp]
instance {α β} [HMul β α α] : HMul (Suc β) (Suc α) (Suc α) where
  hMul x y := match (generalizing := true) x, y with
    | 0, _ => 0
    | _, 0 => 0
    | S x, S y => S (x*y)

@[simp]
theorem one_def {α} [One α] : (1 : Suc α) = S 1 := by rfl

@[simp]
theorem zero_add_def {α} [Add α] (y : Suc α) : 0 + y = y := by rfl

@[simp]
theorem add_zero_def {α} [Add α] (x : α) : S x + 0 = S x := by rfl

@[simp]
theorem add_def {α} [Add α] (x y : α) : S x + S y = S (x + y) := by rfl

@[simp]
theorem zero_mul_def {α} [Mul α] (y : Suc α) : 0 * y = 0 := by rfl

@[simp]
theorem mul_zero_def {α} [Mul α] (x : α) : S x * 0 = 0 := by rfl

@[simp]
theorem mul_def {α} [Mul α] (x y : α) : S x * S y = S (x * y) := by rfl

@[simp]
theorem add_comm_def {α} [AddCommMagma α] : ∀ (a b : Suc α), a + b = b + a
    | 0, 0 => by simp
    | 0, S _ => by simp
    | S _, 0 => by simp
    | S _, S _ => by
      simp
      apply add_comm

@[simp]
theorem mul_comm_def {α} [CommMagma α] : ∀ (a b : Suc α), a * b = b * a
    | 0, 0 => by simp
    | 0, S _ => by simp
    | S _, 0 => by simp
    | S _, S _ => by
      simp
      apply mul_comm

-- ToSuc instances

@[simp]
instance : ToSuc ℕ where
  toSuc
    | 0 => 0
    | x => S x

@[simp]
instance : ToSuc ℤ where
  toSuc
    | 0 => 0
    | x => S x

@[simp]
theorem nattoSuc_zero_def : ToSuc.toSuc (0 : ℕ) = 0 := by rfl

@[simp]
theorem inttoSuc_zero_def : ToSuc.toSuc (0 : ℤ) = 0 := by rfl

@[simp]
theorem nattoSuc_succ_def n : ToSuc.toSuc (Nat.succ n : ℕ) = S (Nat.succ n) := by rfl

@[simp]
theorem inttoSuc_succ_def n : ToSuc.toSuc (Int.ofNat (Nat.succ n))
  = S (Int.ofNat (Nat.succ n)) := by rfl

@[simp]
theorem inttoSuc_pred_def n : ToSuc.toSuc (Int.negSucc n)
  = S (Int.negSucc n) := by rfl

@[simp]
def nsmul {α} [Add α] : ℕ → Suc α → Suc α
  | 0, _ => 0
  | _, 0 => 0
  | Nat.succ n, x => x + nsmul n x

-- Suc has properties:

@[simp]
instance {α} [FreeAddCommSemiring α] : CommSemiring (Suc α) where
  mul := (· * ·)
  zero_add := zero_add_def
  add_zero := by
    intro a
    rw [add_comm_def a 0]
    apply zero_add_def
  nsmul := nsmul
  nsmul_succ
    | 0, 0 => by simp
    | 0, S x => by simp
    | Nat.succ n, 0 => by simp
    | Nat.succ n, S x => by simp
  add_comm := add_comm_def
  add_assoc
    | _, 0, 0 => by simp
    | 0, _, 0 => by simp
    | 0, 0, _ => by simp
    | S _, S _, 0 => by simp
    | S _, 0, S _ => by simp
    | 0, S _, S _ => by simp
    | S _, S _, S _ => by
      simp only [add_def, add_assoc]
  mul_comm := mul_comm_def
  mul_assoc
    | 0, 0, 0 => by simp
    | S _, 0, 0 => by simp
    | 0, S _, 0 => by simp
    | 0, 0, S _ => by simp
    | S _, S _, 0 => by simp
    | S _, 0, S _ => by simp
    | 0, S _, S _ => by simp
    | S _, S _, S _ => by
      simp only [mul_def, mul_assoc]
  zero_mul := zero_mul_def
  mul_zero
    | 0 => by simp
    | S _ => by simp
  mul_one
    | 0 => by simp
    | S _ => by simp
  one_mul
    | 0 => by simp
    | S _ => by simp
  left_distrib
    | 0, _, _ => by simp only [zero_mul_def, zero_add_def]
    | S _, 0, _ => by simp only [mul_zero_def, zero_add_def]
    | S _, S _, 0 => by simp
    | S _, S _, S _ => by simp [FreeAddCommSemiring.left_distrib]
  right_distrib
    | 0, _, _ => by simp only [zero_mul_def, zero_add_def]
    | S _, 0, 0 => by simp
    | S _, 0, S _ => by simp
    | S _, S _, 0 => by simp
    | S _, S _, S _ => by
      rw [mul_comm_def]
      simp [FreeAddCommSemiring.left_distrib, mul_comm]

instance {α} [PosNegSet α] : LT (Suc α) where
  lt
    | 0, 0 => false
    | 0, S y => PosNegSet.posv y
    | S x, 0 => PosNegSet.negv x
    | S x, S y => x < y

def eq {α} : Suc α → Suc α → Prop
  | Ø, Ø => true
  | S _, Ø => false
  | Ø, S _ => false
  | S x, S y => x = y

@[simp]
def eq.eqv {α} : Equivalence (eq : Suc α → Suc α → Prop) where
  refl := by
    intro x
    cases x
    · rw [eq]
    rw [eq]
  symm := by
    intro x y h
    cases x
    · cases y
      · rw [eq]
      rw [eq] at h
      simp at h
    cases y
    · rw [eq] at h
      simp at h
    rw [h, eq]
  trans := by
    intro x y z hxy hyz
    cases x
    · cases z
      · rw [eq]
      cases y
      · rw [eq, eq, hyz] at *
      rw [eq, eq, ←hyz, hxy] at *
    cases z
    · cases y
      · rw [eq, eq, hxy] at *
      rw [eq, hxy, hyz] at *
    cases y
    · rw [eq] at hxy
      simp at hxy
    rw [eq, hxy, hyz] at *

instance instSetoid {α} : Setoid (Suc α) where
  r := eq
  iseqv := eq.eqv

-- Rank zero Fluxions:

namespace R0

def Flux := List ∘ Suc

@[simp]
instance {α} : Zero (Flux α) := ⟨[]⟩

@[simp]
def eq {α} : Flux α → Flux α → Prop
  | [], [] => true
  | x :: xs, [] => Suc.eq x 0 ∧ eq xs []
  | [], y :: ys => Suc.eq y 0 ∧ eq [] ys
  | x :: xs, y :: ys => Suc.eq x y ∧ eq xs ys
termination_by xs ys => xs.length + ys.length

@[simp]
def eq.eqv {α} : Equivalence (eq : Flux α → Flux α → Prop) where
  refl := by
    intro x
    induction x
    · rw [eq]
    rw [eq]
    constructor
    · apply Suc.eq.eqv.refl
    grind
  symm := by
    intro x y h
    induction x generalizing y
    · induction y
      · exact h
      rw [eq, eq] at *
      constructor
      · exact h.1
      grind
    cases y
    · rw [eq, eq] at *
      constructor
      · exact h.1
      grind
    rw [eq] at *
    constructor
    · apply Suc.eq.eqv.symm h.1
    grind
  trans := by
    intro x y z
    induction x generalizing y z
    · induction y generalizing z
      case nil => simp
      case cons y ys hy =>
        rw [eq] at *
        intro hxy hyz
        cases z
        case nil => rw [eq]
        case cons z zs =>
          simp only [eq] at *
          constructor
          · apply Suc.eq.eqv.trans (Suc.eq.eqv.symm hyz.1) hxy.1
          apply hy hxy.2 hyz.2
    case cons x xs hx =>
      intro hxy hyz
      cases z
      case nil =>
        cases y
        case nil =>
          simp only [eq] at *
          exact hxy
        case cons y ys =>
          simp only [eq] at *
          constructor
          · apply Suc.eq.eqv.trans hxy.1 hyz.1
          apply hx hxy.2 hyz.2
      case cons z zs =>
        cases y
        case nil =>
          simp only [eq] at *
          constructor
          · apply Suc.eq.eqv.trans hxy.1 (Suc.eq.eqv.symm hyz.1)
          apply hx hxy.2 hyz.2
        case cons y ys =>
          simp only [eq] at *
          constructor
          · apply Suc.eq.eqv.trans hxy.1 hyz.1
          apply hx hxy.2 hyz.2

instance instSetoid {α} : Setoid (Flux α) where
  r := eq
  iseqv := eq.eqv

-- Actual Fluxions !!!

@[ext]
structure Fluxion α where
  r : ℤ
  v : Flux α

namespace Fluxion

@[match_pattern]
instance {α} : Zero (Fluxion α) := ⟨0,[]⟩

@[simp]
theorem zero_rank_def {α} : r (0 : Fluxion α) = 0 := by rfl

@[simp]
theorem zero_list_def {α} : v (0 : Fluxion α) = [] := by rfl

@[simp]
def eq {α} : Fluxion α → Fluxion α → Prop
  | ⟨_, []⟩, ⟨_, []⟩ => true
  | ⟨_, xs⟩, ⟨_, []⟩ => R0.eq xs []
  | ⟨_, []⟩, ⟨_, ys⟩ => R0.eq ys []
  | ⟨n, xs⟩, ⟨m, ys⟩ => (R0.eq xs [] ∧ R0.eq ys []) ∨ ((n = m) ∧ R0.eq xs ys)

def eq.eqv {α} : Equivalence (eq : Fluxion α → Fluxion α → Prop) where
  refl := by
    intro x
    cases x
    case mk r x =>
      cases x
      case nil => simp
      case cons x xs =>
        simp
        apply Or.inr
        constructor
        · apply Suc.eq.eqv.refl
        apply R0.eq.eqv.refl
  symm := by
    intro x y h
    cases x
    case mk rx x =>
    cases y
    case mk ry y =>
    induction x generalizing y
    case nil =>
      cases y
      case nil => simp
      case cons y ys =>
        simp at *
        exact h
    case cons x xs hx =>
      cases y
      case nil =>
        simp at *
        exact h
      case cons y ys =>
        simp [R0.eq] at *
        cases h
        case inl h =>
          apply Or.inl
          constructor
          · exact h.2
          exact h.1
        case inr h =>
          apply Or.inr
          constructor
          · exact (symm h.1)
          constructor
          · exact (Suc.eq.eqv.symm h.2.1)
          exact (R0.eq.eqv.symm h.2.2)
  trans := by
    intro x y z hxy hyz
    cases x
    case mk rx x =>
    cases y
    case mk ry y =>
    cases z
    case mk rz z =>
    cases x
    case nil =>
      cases z
      case nil => simp
      case cons z zs =>
        simp at *
        cases y
        case nil =>
          simp at *
          exact hyz
        case cons y ys =>
          simp at *
          cases hyz
          case inl h =>
            exact h.2
          case inr h =>
            constructor
            · apply Suc.eq.eqv.trans (Suc.eq.eqv.symm h.2.1) hxy.1
            apply R0.eq.eqv.trans (R0.eq.eqv.symm h.2.2) hxy.2
    case cons x xs =>
      cases z
      case nil =>
        cases y
        case nil =>
          simp at *
          exact hxy
        case cons y ys =>
          simp at *
          cases hxy
          case inl h =>
            exact h.1
          case inr h =>
            constructor
            · apply Suc.eq.eqv.trans h.2.1 hyz.1
            apply R0.eq.eqv.trans h.2.2 hyz.2
      case cons z zs =>
        simp at *
        cases y
        case nil =>
          simp at *
          apply Or.inl
          constructor
          · exact hxy
          exact hyz
        case cons y ys =>
          simp at *
          cases hxy
          case inl hxy =>
            apply Or.inl
            cases hyz
            case inl hyz =>
              constructor
              · exact hxy.1
              exact hyz.2
            case inr hyz =>
              constructor
              · exact hxy.1
              constructor
              · apply Suc.eq.eqv.trans (Suc.eq.eqv.symm hyz.2.1) hxy.2.1
              apply R0.eq.eqv.trans (R0.eq.eqv.symm hyz.2.2) hxy.2.2
          case inr hxy =>
            cases hyz
            case inl hyz =>
              apply Or.inl
              constructor
              · constructor
                · apply Suc.eq.eqv.trans hxy.2.1 hyz.1.1
                apply R0.eq.eqv.trans hxy.2.2 hyz.1.2
              exact hyz.2
            case inr hyz =>
              apply Or.inr
              constructor
              · apply Trans.trans hxy.1 hyz.1
              constructor
              · apply Suc.eq.eqv.trans hxy.2.1 hyz.2.1
              apply R0.eq.eqv.trans hxy.2.2 hyz.2.2

instance instSetoid {α} : Setoid (Fluxion α) where
  r := eq
  iseqv := eq.eqv

@[simp]
def finiteSet {α} : Fluxion α → Multiset ℤ
  | ⟨_, []⟩ => {}
  | ⟨r, 0 :: xs⟩ => finiteSet ⟨(r-1), xs⟩
  | ⟨r, x :: xs⟩ => r ::ₘ finiteSet ⟨(r-1), xs⟩
termination_by x => x.v.length

theorem finset_lt {α} : ∀ r r' (xs : Flux α), r' < r → r ∉ finiteSet ⟨r', xs⟩ := by
  intro r r' xs hr
  induction xs generalizing r'
  case nil => simp
  case cons x xs ih =>
    cases x
    case Ø =>
      rw [finiteSet]
      apply ih (r'-1) (Int.lt_trans (by simp : r' - 1 < r') hr)
    case S x =>
      simp
      constructor
      · contrapose! hr
        rw [hr]
      apply ih (r'-1) (Int.lt_trans (by simp : r' - 1 < r') hr)

@[simp]
def finset {α} (x : Fluxion α) : Finset ℤ where
  val := finiteSet x
  nodup := by
    cases x
    case mk r x =>
    induction x generalizing r
    case nil => simp
    case cons x xs hx =>
      cases x
      case Ø =>
        simp
        apply hx
      case S x =>
        simp
        constructor
        · apply finset_lt
          simp
        apply hx

@[simp]
def getElem {α} : Flux α → ℤ → Suc α
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, Int.ofNat (Nat.succ n) => getElem xs n
  | _, Int.negSucc _ => 0

theorem sub_iff_comp :
  ∀ (a b : ℤ) (f : ℤ → Prop), f (a - b) →
      (a = b ∧ f 0)
    ∨ (a < b ∧ ∃ n : ℕ, f (Int.negSucc n) ∧ n = b - a - 1)
    ∨ (b < a ∧ ∃ n : ℕ, f (Int.ofNat (Nat.succ n)) ∧ n = a - b - 1) := by
  intro a b f
  have trich := Int.lt_trichotomy a b
  intro h
  induction a generalizing b
  case zero =>
    induction b
    case zero =>
      simp at *
      exact h
    case succ b hb =>
      cases b
      case zero =>
        simp at *
        exact h
      case succ b =>
        simp at *
        cases trich
        case inl t =>
          apply Or.inr
          apply Or.inl
          constructor
          · exact t
          use (b + 1)
          constructor
          · have k : (Int.negSucc (b + 1)) = (-1 + (-1 + -↑b)) := by grind
            rw [k]
            exact h
          rfl
        case inr t =>
          cases t
          case inl t => grind
          case inr t => grind
    case pred b _ =>
      simp at *
      grind
  case succ a ha =>
    specialize ha (b - 1)
    grind
  case pred a ha =>
    specialize ha (b + 1)
    grind

def F {α} [FreeAddCommSemiring α] (x : Fluxion α)
  : AddMonoidAlgebra (Suc α) ℤ where
  support := finset x
  toFun := fun n ↦ getElem x.v (x.r-n)
  mem_support_toFun := by
    intro n
    cases x
    case mk r v =>
    rw [finset, Finset.mem_mk]
    induction v generalizing r n
    · simp
    case cons x xs ih =>
      constructor
      · intro h h0
        apply sub_iff_comp r n (fun z ↦ getElem (x :: xs) z = 0) at h0
        contrapose! h0
        constructor
        · intro h1
          contrapose! h
          cases x
          · rw [getElem] at h
            rw [finiteSet, h1]
            apply finset_lt
            simp
          simp at *
        constructor
        · intro h1 n'
          contrapose! h
          apply finset_lt
          exact h1
        simp only [getElem]
        intro h0 n' h1
        contrapose! h1
        rw [h1]
        rw [(by grind : r - n - 1 = r - 1 - n)]
        rw [←propext (ih n (r - 1))]
        cases x
        · rw [finiteSet] at h
          exact h
        simp only [finiteSet, Multiset.mem_cons] at h
        cases h
        case inl h => grind
        case inr h => exact h
      intro h
      apply sub_iff_comp r n (fun z ↦ ¬getElem (x :: xs) z = 0) at h
      contrapose! h
      constructor
      · simp at *
        intro h0
        rw [h0] at h
        cases x
        · rfl
        case S x => simp at h
      constructor
      · intro h0 n' h1
        contrapose! h1
        simp
      intro h0 n' h1
      contrapose! h1
      simp
      rw [h1]
      have niff : ∀ a b, ((a ↔ b) = ((¬a) ↔ (¬b))) := by grind
      specialize ih n (r - 1)
      rw [niff] at ih
      rw [(by grind : r - n - 1 = r - 1 - n)]
      simp at ih
      rw [←propext ih]
      contrapose! h
      cases x
      · simp
        exact h
      simp
      apply Or.inr
      exact h

structure Flux α where
  x [FreeAddCommSemiring α] := AddMonoidAlgebra (Suc α) ℤ

-- notation "𝔽 " α => AddMonoidAlgebra (Suc α) ℤ

-- instance {α} [FreeAddCommSemiring α] : Zero (𝔽 α) := ⟨fun _ => 0⟩

def leq {α} [PosNegSet α] : Fluxion α → Fluxion α → Prop
  | ⟨_,[]⟩, ⟨_,[]⟩ => true
  | ⟨_,[]⟩, ⟨m,0::ys⟩ => leq 0 ⟨m-1,ys⟩
  | ⟨_,[]⟩, ⟨_,y::_⟩ => 0 < y
  | ⟨n,0::xs⟩, ⟨_,[]⟩ => leq ⟨n-1,xs⟩ 0
  | ⟨_,x::_⟩, ⟨_,[]⟩ => x < 0
  | ⟨n,0::xs⟩, ⟨m,0::ys⟩ => leq ⟨n-1,xs⟩ ⟨m-1,ys⟩
  | ⟨n,0::_⟩, ⟨m,y::_⟩ => n ≤ m ∨ (n = m ∧ 0 < y)
  | ⟨n,x::_⟩, ⟨m,0::_⟩ => n ≤ m ∨ (n = m ∧ x < 0)
  | ⟨n,x::xs⟩, ⟨m,y::ys⟩ => n ≤ m ∨ (n = m ∧ (x < y ∨ (x = y ∧ leq ⟨n-1,xs⟩ ⟨m-1,ys⟩)))
termination_by x y => x.v.length + y.v.length

instance {α} [PosNegSet α] : LE (Fluxion α) where
  le := leq

@[simp]
def zipWith {α β} [Zero α] (f : α → α → β) (a : List α) (b : List α) : List β :=
  match a, b with
    | [], [] => []
    | x :: xs, [] => f x 0 :: zipWith f xs []
    | [], y :: ys => f 0 y :: zipWith f [] ys
    | x :: xs, y :: ys => f x y :: zipWith f xs ys
termination_by a.length + b.length

def add {α} [FreeAddCommSemiring α] : Fluxion α → Fluxion α → Fluxion α
  | ⟨n, xs⟩, ⟨m, ys⟩ => if n = m then ⟨n, zipWith (· + ·) xs ys⟩ else ⟨n, xs⟩

-- Calculus

def d {α} [One α] (f : Fluxion α → Fluxion α) (x : α) : Fluxion α :=
  f ((⟨0,[S x]⟩ : Fluxion α) + (⟨0,[0,1]⟩ : Fluxion α)) + f ⟨0,[-S x]⟩

-- Showing them:

@[simp]
def printNat (b : List Char) : Bool → ℕ → ℕ → List Char
  | true, 0, 0 => []
  | false, _, 0 => [b[0]!]
  | _, 0, z => [b[z]!]
  | false, Nat.succ n, z => if (b.length)^(n) ≤ z ∧ z < (b.length)^(n+1)
           then (b)[z / (b.length)^n]! :: printNat b true n (z % (b.length)^n)
           else printNat b false n z
  | true, Nat.succ n, z => if (b.length)^(n) ≤ z ∧ z < (b.length)^(n+1)
           then (b)[z / (b.length)^n]! :: printNat b true n (z % (b.length)^n)
           else b[0]! :: printNat b true n z

@[simp]
def printInt (b : List Char) (z : ℤ) : List Char :=
  match (generalizing := true) z with
  | 0 => [b[0]!]
  | 1 => [b[1]!]
  | Int.negSucc 0 => ['-',b[1]!]
  | Int.negSucc z => '-' :: printNat b false (Nat.succ z) (Nat.succ z)
  | Int.ofNat z => printNat b false z z

@[simp]
def print_aux {α} [One α] [BEq α] (f : α → List Char) (b : List Char) (x : α) : Bool → List Char
  | true => if x == 1 then [] else f x
  | false => if x == 1 then [b[0]!] else f x

@[simp]
def print' {α} [One α] [BEq α] (f : α → List Char) (b : List Char) (t : Bool)
  : Fluxion α → List Char
  | ⟨_, []⟩ => (print_aux f b 1 t)
  | ⟨_, [0]⟩ => (print_aux f b 1 t)
  | ⟨0, [S x]⟩ => (print_aux f b x t)
  | ⟨Int.ofNat 1, [S x]⟩ => (print_aux f b x t) ++ ['ω']
  | ⟨Int.ofNat r, [S x]⟩ => (print_aux f b x t) ++ 'ω'::'^':: printInt b r
  | ⟨-1, [S x]⟩ => (print_aux f b x t) ++ ['ε']
  | ⟨Int.negSucc r, [S x]⟩ => (print_aux f b x t) ++ 'ε'::'^':: printInt b (r+5)
  | ⟨r, 0 :: xs⟩ => print' f b t ⟨r-1, xs⟩
  | ⟨0, S x :: xs⟩ => f x ++ ' '::'+'::' ':: print' f b true ⟨Int.negSucc 0, xs⟩
  | ⟨Int.ofNat 1, S x :: xs⟩ => (print_aux f b x t) ++ 'ω'::' '::'+'::' '
      :: print' f b true ⟨0, xs⟩
  | ⟨Int.ofNat r, S x :: xs⟩ =>
    (print_aux f b x t) ++ 'ω'::'^':: printInt b r ++ ' '::'+'::' '
      :: print' f b true ⟨r-1, xs⟩
  | ⟨-1, S x :: xs⟩ => (print_aux f b x t) ++ 'ε'::' '::'+'::' '
      :: print' f b true ⟨Int.negSucc 1, xs⟩
  | ⟨Int.negSucc r, S x :: xs⟩ =>
    (print_aux f b x t) ++ 'ε'::'^':: printInt b (r-1) ++ ' '::'+'::' '
      :: print' f b true ⟨Int.negSucc (r+1), xs⟩
termination_by x => x.v.length

@[simp]
def print (x : Fluxion ℤ) :=
  String.ofList (print' (printInt ['0','1','2','3','4','5']) ['0','1','2','3','4','5'] false x)

#eval print ⟨3, List.map ToSuc.toSuc [2,0,1,-7,-1,3,88]⟩

end Fluxion

end R0

end Suc
