import Mathlib

@[ext]
structure Flux α where
  x : α
  es : List α
  os : List α

namespace Flux

@[simp]
def zipWith {α β} [Zero α] (f : α → α → β) (a : List α) (b : List α) : List β :=
  match a, b with
    | [], [] => []
    | x :: xs, [] => f x 0 :: zipWith f xs []
    | [], y :: ys => f 0 y :: zipWith f [] ys
    | x :: xs, y :: ys => f x y :: zipWith f xs ys
termination_by a.length + b.length

/-
@[simp]
theorem zipWith_nil_right {α} (f : α → α → α) (xs : List α) : zipWith f xs [] = xs :=
  by cases xs <;> rfl

@[simp]
theorem zipWith_nil_left {α} (f : α → α → α) (ys : List α) : zipWith f [] ys = ys :=
  by cases ys <;> rfl

@[simp]
theorem zipWith_cons {α} (f : α → α → α) (x : α) (y : α) (xs ys : List α) :
  zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys :=
  by rfl

theorem zipWith_assoc {α} (f : α → α → α)
  (xs ys zs : List α) :
  (∀ x y z, f x (f y z) = f (f x y) z) →
  zipWith f xs (zipWith f ys zs) =
  zipWith f (zipWith f xs ys) zs :=
  by
    induction xs generalizing ys zs
    case nil =>
      simp
    case cons x xs ih =>
      cases ys
      case nil =>
        simp
      case cons y ys =>
        cases zs
        case nil =>
          simp
        case cons z zs =>
          intro h
          simp only [zipWith_cons, List.cons.injEq]
          constructor
          · exact h x y z
          apply ih
          exact h

def zipWith_comm {α} (f : α → α → α)
  (xs ys : List α) :
  (∀ x y, f x y = f y x) →
  zipWith f xs ys = zipWith f ys xs := by
    induction xs generalizing ys
    case nil =>
      simp
    case cons x xs ih =>
      cases ys
      case nil =>
        simp
      case cons y ys =>
        intro h
        simp only [zipWith_cons, List.cons.injEq]
        constructor
        · exact h x y
        apply ih
        exact h
-/

@[simp]
def fold {α} (f : α → α → α) (e : α) : List α → α
  | [] => e
  | [x] => x
  | x :: xs => f x (fold f e xs)

@[simp]
instance {α} [Zero α] : Zero (Flux α) :=
  ⟨⟨0,[],[]⟩⟩

instance {α} [BEq α] [Zero α] : BEq (List α) where
  beq x y := fold (· ∧ ·) True (zipWith (· == ·) x y)

def List.eq {α} [Zero α] : List α → List α → Prop
  | [], [] => true
  | x :: xs, [] => x = 0 ∧ List.eq xs []
  | [], y :: ys => y = 0 ∧ List.eq [] ys
  | x :: xs, y :: ys => x = y ∧ List.eq xs ys

instance {α} [BEq α] : BEq (Flux α) where
  beq x y := x.x == y.x ∧ x.es == y.es ∧ x.os == y.os

@[simp]
def allZero {α} [BEq α] [Zero α] : List α → Bool
  | [] => True
  | x :: xs => x == 0 ∧ allZero xs

@[simp]
def removeZero {α} [BEq α] [Zero α] : List α → List α
  | [] => []
  | e :: es => if (allZero (e::es) : Bool) then [] else e :: removeZero es

@[simp]
theorem removeZero_nil {α} [BEq α] [Zero α] : removeZero ([] : List α) = [] := by rfl

@[simp]
theorem removeZero_allZero {α} [BEq α] [Zero α] (e : α) (es : List α) (h : allZero (e::es)) :
  removeZero (e :: es) = [] := by
    simp at *
    constructor
    · exact h.1
    exact h.2

@[simp]
theorem removeZero_notAllZero {α} [BEq α] [Zero α] (e : α) (es : List α) (h : ¬ allZero (e::es)) :
  removeZero (e :: es) = e :: removeZero es := by
    simp at *
    exact h

@[simp]
def norm {α} [BEq α] [Zero α] (x : Flux α) : Flux α :=
  ⟨x.x, removeZero x.es, removeZero x.os⟩

@[simp]
def eq {α} [BEq α] [Zero α] (a b : Flux α) : Prop :=
  match a, b with
  | ⟨x, es, os⟩, ⟨x', es', os'⟩ => x = x'
    ∧ removeZero es = removeZero es'
    ∧ removeZero os = removeZero os'

def eq.eqv {α} [BEq α] [Zero α] :
    Equivalence (eq : Flux α → Flux α → Prop) where
  refl := by
    intro x
    cases x
    case mk x xes xos =>
      simp
  symm := by
    intro x y h
    rw [eq] at *
    constructor
    · symm
      exact h.1
    constructor
    · symm
      exact h.2.1
    symm
    exact h.2.2
  trans := by
    intro x y z hxy hyz
    rw [eq] at *
    constructor
    · rw [Trans.trans hxy.1 hyz.1]
    constructor
    · rw [Trans.trans hxy.2.1 hyz.2.1]
    rw [Trans.trans hxy.2.2 hyz.2.2]

instance instSetoid {α} [BEq α] [Zero α] : Setoid (Flux α) where
  r := eq
  iseqv := eq.eqv

def Ion (α : Type) [BEq α] [Zero α] : Type := Quotient (instSetoid : Setoid (Flux α))

@[simp]
instance {α} [One α] : One (Flux α) :=
  ⟨⟨1,[],[]⟩⟩

@[simp]
instance {α} [Neg α] : Neg (Flux α) :=
  ⟨fun x ↦
    ⟨-x.x, List.map (- ·) x.es, List.map (- ·) x.os⟩
  ⟩

@[simp]
instance {α} [Zero α] [Add α] : Add (Flux α) :=
  ⟨fun a b ↦
    ⟨a.x + b.x,
     zipWith (· + ·) a.es b.es,
     zipWith (· + ·) a.os b.os⟩
  ⟩

@[simp]
def mult {α} [Zero α] [Add α] [Mul α] : List α → List α → List α
  | _, [] => []
  | [], _ => []
  | x :: xs, y :: ys => fold (· + ·) 0 (zipWith (· * ·) (x::xs) (y::ys)) :: mult xs ys

@[simp]
instance {α} [Zero α] [Add α] [Mul α] : Mul (Flux α) :=
  ⟨fun ⟨x,es,os⟩ ⟨x',es',os'⟩ ↦
    ⟨(x * x') +
    (fold (· + ·) 0 (zipWith (· * ·) es os')) +
    (fold (· + ·) 0 (zipWith (· * ·) os es')),
    zipWith (· + ·) (mult es (x'::os')) (mult es' (x::os)),
    zipWith (· + ·) (mult os (x'::es')) (mult os' (x::es))⟩
  ⟩

@[simp]
theorem zero_def {α} [Zero α] : (0 : Flux α) = ⟨0,[],[]⟩ := by rfl

@[simp]
theorem one_def {α} [One α] : (1 : Flux α) = ⟨1,[],[]⟩ := by rfl

@[simp]
theorem neg_def {α} [Neg α] (x : Flux α) :
  -x = ⟨-x.x, List.map (- ·) x.es, List.map (- ·) x.os⟩ := by rfl

@[simp]
theorem add_def {α} [Zero α] [Add α] (x y : Flux α) :
  x + y = ⟨x.x + y.x, zipWith (· + ·) x.es y.es, zipWith (· + ·) x.os y.os⟩ := by rfl

@[simp]
theorem mul_def {α} [Zero α] [Add α] [Mul α] (x y : Flux α) :
  x * y = ⟨(x.x * y.x) +
    (fold (· + ·) 0 (zipWith (· * ·) x.es y.os)) +
    (fold (· + ·) 0 (zipWith (· * ·) x.os y.es)),
    zipWith (· + ·) (mult x.es (y.x::y.os)) (mult y.es (x.x::x.os)),
    zipWith (· + ·) (mult x.os (y.x::y.es)) (mult y.os (x.x::x.es))⟩ := by rfl

namespace Ion

@[simp]
def mk {α} [BEq α] [Zero α] (x : Flux α) : Ion α := Quotient.mk _ x

@[simp]
def lift {α β} [BEq α] [Zero α]
  (f : Flux α → β) :
  Ion α → β :=
  Quotient.lift (f ∘ norm) ((by
      intro a b h
      simp only [eq, norm] at *
      rw [h.1, h.2.1, h.2.2]
    ) : ∀ a b, eq a b → f a.norm = f b.norm)

@[simp]
def lift' {α β} [BEq α] [Zero α]
  (f : Flux α → β) (h : ∃ g, f = g ∘ norm) :
  Ion α → β :=
  Quotient.lift (f) ((by
      intro a b h0
      contrapose! h
      intro g
      contrapose! h
      simp only [eq, h, Function.comp_apply, norm] at *
      rw [h0.1, h0.2.1, h0.2.2]
    ) : ∀ a b, eq a b → f a = f b)

@[simp]
def lifted {α} [BEq α] [Zero α] : Ion α → Flux α := lift id

theorem lifted_mk {α} [BEq α] [Zero α] (x : Ion α) :
  mk x.lifted = x := by sorry

theorem lift_f {α β} [BEq α] [Zero α] :
  ∀ (f : Flux α → β) (x : Ion α), lift f (x) = (f x.lifted) := by
    intros f x
    simp
    sorry

theorem lift_theorem {α β} [BEq α] [Zero α] :
  ∀ (f : Flux α → β) (x : Ion α), lift f x = f x.lifted := by
    sorry

def lift_prop {α} [BEq α] [Zero α]
  (p : Flux α → Prop) (h : (f : Flux α) → p f.norm) :
  (x : Ion α) → lift p x := by sorry

instance {α} [BEq α] [Zero α] : BEq (Ion α) where
  beq := lift (fun y ↦ lift (fun x ↦ x == y))

@[simp]
def initial {α} : List α → List α
  | [] => []
  | [_] => []
  | e :: es => e :: (Flux.Ion.initial es)

theorem init_shrink {α} (xs : List α) : (initial xs).length <= xs.length :=
  by
    induction xs
    case nil =>
      simp
    case cons x xs ih =>
      cases xs
      case nil =>
        simp
      case cons y ys =>
        rw [List.length_cons]
        apply Nat.succ_le_succ
        exact ih

@[simp]
instance {α} [BEq α] [Zero α] : Zero (Ion α) := ⟨mk 0⟩

@[simp]
instance {α} [BEq α] [Zero α] [One α] : One (Ion α) := ⟨mk 1⟩

@[simp]
instance {α} [BEq α] [Zero α] [Neg α] : Neg (Ion α) :=
  ⟨mk ∘ (Flux.Ion.lift (- ·))⟩

@[simp]
instance {α} [BEq α] [Zero α] [Add α] : Add (Ion α) :=
  ⟨Flux.Ion.lift (fun f ↦ Flux.Ion.lift (mk ∘ (f + ·)))⟩

@[simp]
instance {α} [BEq α] [Zero α] [Add α] [Mul α] : Mul (Ion α) :=
  ⟨Flux.Ion.lift (fun f ↦ Flux.Ion.lift (mk ∘ (f * ·)))⟩

@[simp]
def elem_eq_if_list_eq {α} : ∀ (xs ys : List α) (i : ℕ), xs=ys → xs[i]?=ys[i]? := by
        intros xs ys i h
        rw [h]

@[simp]
instance {α} [BEq α] [Zero α] [Add α] : LE (Ion α) where
  le a b := ∃ c : Ion α, b = a + c

instance {α} [BEq α] [CommRing α] : CommRing (Ion α) where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)
  nsmul n := Flux.Ion.lift (fun x ↦ mk ⟨n * x.x, List.map (n * ·) x.es, List.map (n * ·) x.os⟩)
  zsmul n := Flux.Ion.lift (fun x ↦ mk ⟨n * x.x, List.map (n * ·) x.es, List.map (n * ·) x.os⟩)
  add_assoc := by
    intro a b c
    simp [instHAdd, Add.add]
    sorry
  zero_add := by
    have h (x : Flux α) : (0 + x = x) := by
    intro a
    specialize h a.lifted

  add_zero := by sorry
  add_comm := by sorry
  left_distrib := by sorry
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry
  one_mul := by sorry
  mul_one := by sorry
  mul_comm := by sorry
  neg_add_cancel := by
    intro a
    simp
