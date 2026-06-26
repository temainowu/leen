import Mathlib

class GroupAction γ α extends
  Group γ,
  HMul γ α α
  where
  one_act : ∀ x : α, (1 : γ) * x = x
  act : ∀ (f g : γ) (x : α), g * f * x = g * (f * x)
  use_group : Inhabited α → ∃ x : α, ∀ g h : γ, g ≠ h → g * x ≠ h * x

/-
@[simp]
instance {α γ} [Group α] [GroupAction γ α] : HMul α γ α where
  hMul x g := x * (g * (1 : α))

theorem gact_assoc {γ α} [Group α] [GroupAction γ α] : ∀ (x y : α) (g : γ), x * g * y = x * (g * y) := by
  intro x y g
  simp
  sorry
-/

theorem act_eq_iff_eq_inv {α γ} [GroupAction γ α] :
  ∀ (a b : α) (g : γ), g * a = b ↔ a = g⁻¹ * b := by
    intro a b g
    constructor
    · intro h
      rw [←h, ←GroupAction.act, inv_mul_cancel, GroupAction.one_act]
    intro h
    rw [h, ←GroupAction.act, mul_inv_cancel, GroupAction.one_act]


inductive one | I

namespace one

instance : Group one where
  mul | I, I => I
  mul_assoc := by
    intro a b c
    cases a
    cases b
    cases c
    rfl
  one := I
  one_mul := by
    intro a
    cases a
    rfl
  mul_one := by
    intro a
    cases a
    rfl
  inv := id
  inv_mul_cancel := by
    intro a
    cases a
    rfl

instance {α} : GroupAction one α where
  hMul | I, x => x
  one_act := by simp
  act := by
    intro f g x
    cases f
    cases g
    simp
  use_group := by
    intro h
    use (default : α)
    intro g h hgh
    cases g
    cases h
    contrapose! hgh
    simp

instance QuotientEqv {γ α} [GroupAction γ α] : Equivalence (fun x y : α => ∃ f : γ, x = f * y) where
  refl := by
    intro x
    use 1
    rw [GroupAction.one_act]
  symm := by
    intro x y h
    rcases h with ⟨f, h⟩
    use f⁻¹
    rw [h,
       ←GroupAction.act,
        inv_mul_cancel,
        GroupAction.one_act]
  trans := by
    intro x y z hxy hyz
    rcases hxy with ⟨f, hxy⟩
    rcases hyz with ⟨g, hyz⟩
    use (f * g)
    rw [GroupAction.act,
       ←hyz,
       ←hxy]

theorem groupact_lin {α γ} [Group α] [GroupAction γ α] : ∀ (a b : α) (g : γ), g * (a * b) = a * (g * b) := by
  intro a b g
  have h0 := @GroupAction.one_act γ α (by case _ h => exact h) (a * b)
  have h1 := GroupAction.act 1 g (a * b)
  apply (act_eq_iff_eq_inv (a * b) (a * (g * b)) g).2



@[simp]
def div.{u,v} (γ : Type u) (α : Type v) [GroupAction γ α] : Setoid α where
  r x y := ∃ f : γ, x = f * y
  iseqv := QuotientEqv.{u,v}

@[simp]
def giv {α} γ (x : α) [GroupAction γ α] := Quotient.mk (div γ α) x

def surjective {α β} (f : α → β) := ∀ y : β, ∃ x : α, f x = y

def injective {α β} (f : α → β) := ∀ x y : α, f x = f y → x = y

def bijective {α β} (f : α → β) := injective f ∧ surjective f

def homomorphism {α β} (f : α → β) [Mul α] [Mul β] := ∀ x y : α, f (x * y) = f x * f y

instance {α γ} [GroupAction γ α] [Group α] : Group (Quotient (div γ α)) where
  mul a b := Quotient.lift (fun x : α => @Quotient.lift α (Quotient (div γ α)) (div γ α) (fun y : α => giv γ (x * y)) (by
    intro y z h
    simp
    rw [←Quotient.eq_iff_equiv] at h
    simp [Quotient.eq] at *
    rcases h with ⟨f, h⟩
    use f
    symm at h
    rw [act_eq_iff_eq_inv] at h
    rw [h]
    sorry
    ) (a)) (by
    intro x y h
    simp [Quotient.eq]
    congr
    sorry
  ) b
  mul_assoc := by
    intro x y z
    apply Quotient.inductionOn₃ x y z
    intro a b c
    simp
    rw [mul_assoc]
  one := Quotient.mk (div (Setoid α)) 1
  one_mul := by
    intro x
    congr
    apply Quotient.inductionOn x
    intro a
    simp
    rw [one_mul]
  mul_one := by
    intro x
    apply Quotient.inductionOn x
    intro a
    simp
    rw [mul_one]
  inv := fun x => Quotient.mk (div (Setoid α)) (x.1⁻¹)
  inv_mul_cancel := by
    intro x
    apply Quotient.inductionOn x
    intro a
    simp
    rw [inv_mul_cancel]

/-
example : ∀ α, ∃ f :Quotient (div one α) → α, bijective f := by
  intro α
  use Unit
  apply Quotient.inductionOn
  intro x
  simp
-/

instance {α β} [Group α] [Group β] : Group (α×β) where
  mul | (a₁, b₁), (a₂, b₂) => (a₁ * a₂, b₁ * b₂)
  mul_assoc := by
    intro a b c
    cases a
    cases b
    cases c
    simp [mul_assoc]
  one := (1, 1)
  one_mul := by
    intro a
    cases a
    simp [one_mul]
  mul_one := by
    intro a
    cases a
    simp [mul_one]
  inv | (a, b) => (a⁻¹, b⁻¹)
  inv_mul_cancel := by
    intro a
    cases a
    simp [inv_mul_cancel]
  div_eq_mul_inv := by
    intro a b
    cases a
    cases b
    simp [div_eq_mul_inv]

example {α β} [Group α] [Group β] [GroupAction β α] : ∀ f : α → β, homomorphism f → surjective f → ∃ g : α → β×(Quotient (div β α)), homomorphism g ∧ bijective g := by
  intro f h0 h1
  use λ x => (f x, giv β x)
  constructor
  · intro x y
    simp
    constructor
    · rw [homomorphism] at h0
      exact h0 x y
    sorry
  constructor
  · intro y z h
    contrapose! h
    simp
    intro h2
    contrapose! h
    rw [surjective] at h1
    sorry
  simp [surjective] at *
  intro x y
  specialize h1 x
  rcases h1 with ⟨z,h1⟩
  use z
  constructor
  · exact h1
  sorry

---

instance {α} : Zero (Set α) where zero := {}

-- structure S'.{u} where

def Str.{u} (n m : ℕ) : Set (((o : Sort n) → (α : Type u)) → (β : Sort m)) where

structure S.{u,v} (α : Type v) where
  u : Type u
  n : Set (u → u → α)

def Magma α := S α

def Relate.{u} := S.{u} Bool

@[simp]
def isHomomorphic {α β} : S α → S β → Prop
  | ⟨a, opa⟩, ⟨b, opb⟩ =>
    ∃ h : (a → b) × (α → β), (
        (∀ x : b, ∃ y : a, x = h.1 y) ∧
         ∀ x : β, ∃ y : α, x = h.2 y) ∧
    ∀ (x y : a) z f,
      (f ∈ opa) → (
    ∃ (g : b → b → β),
      (g ∈ opb) ∧ (
        z = f x y → h.2 z = g (h.1 x) (h.1 y)
    ))

@[simp]
def homomorphismZN : ℤ → ℕ := fun x => match x with
  | Int.ofNat n => n
  | Int.negSucc n => n + 1

theorem homoZN : isHomomorphic ⟨ℤ, {(· * ·)}⟩ ⟨ℕ, {(· * ·)}⟩ := by
  simp
  use homomorphismZN
  use homomorphismZN
  constructor
  · constructor
    · intro x
      use Int.ofNat x
      simp
    intro x
    use Int.ofNat x
    simp
  intro x y
  cases x
  case ofNat x =>
    cases y
    case ofNat y =>
      simp

    case negSucc y =>

  case negSucc x => sorry


---


inductive Two : Type 1
  | X
  | I

namespace Two

@[match_pattern]
instance : Mul Two where mul
  | X, X => X
  | X, I => I
  | I, X => I
  | I, I => X

@[simp]
instance : Group Two where
  mul := (· * ·)
  mul_assoc := by
    intro a b c
    cases a
    · cases b
      · cases c
        · rfl
        rfl
      cases c
      · rfl
      rfl
    cases b
    · cases c
      · rfl
      rfl
    cases c
    · rfl
    rfl
  one := X
  one_mul := by
    intro a
    cases a
    · rfl
    rfl
  mul_one := by
    intro a
    cases a
    · rfl
    rfl
  inv := (X * ·)
  inv_mul_cancel := by
    intro a
    cases a
    · rfl
    rfl

instance : GroupAction Two ℤ where
  hMul
    | X => id
    | I => (- ·)
  one_act := by simp
  act := by
    intro f g x
    cases f
    · cases g
      · rfl
      rfl
    cases g
    · rfl
    simp
  use_group := by
    intro h
    use (default : ℤ)
    intro g h hgh
    cases g
    · cases h
      · contrapose! hgh
        rfl
      simp
    cases h
    · contrapose! hh
      rfl
    contrapose! hgh
    rfl

def homom : ULift (giv Two (0:ℤ)) → ℕ :=




end Two
