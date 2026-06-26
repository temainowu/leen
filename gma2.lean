import Mathlib

structure GMA2 α n m where
  bin : Fin n → α → α → α
  rel : Fin m → α → α → Prop

structure Morph {α β} {n m n' m'} (M0 : GMA2 α n m) (M1 : GMA2 β n' m') where
  f : α → β
  fbin : Fin n → Fin n'
  frel : Fin m → Fin m'
  hbin : ∀ (x y z : α) (i : Fin n),
    M0.bin i x y = z → M1.bin (fbin i) (f x) (f y) = f z
  hrel : ∀ (x y : α) (i : Fin m),
    M0.rel i x y → M1.rel (frel i) (f x) (f y)
  fbin_surj : ∀ i' : Fin n', ∃ i : Fin n, fbin i = i'
  frel_surj : ∀ i' : Fin m', ∃ i : Fin m, frel i = i'

@[simp]
def Nat_add_mul_le : GMA2 ℕ 2 1 where
  bin
    | 0 => (· + ·)
    | 1 => (· * ·)
  rel | 0 => (· ≤ ·)

@[simp]
def Bool_or_and_imp : GMA2 Bool 2 1 where
  bin
    | 0 => (· ∨ ·)
    | 1 => (· ∧ ·)
  rel | 0 => (· → ·)

def homo1 : Morph Nat_add_mul_le Bool_or_and_imp where
  f | 0 => false
    | n => true
  fbin := id
  frel := id
  hbin := by
    intro x y z i
    rcases i with ⟨i,hi⟩
    cases i
    case zero => simp ; grind
    case succ i =>
      cases i
      case zero =>
        simp
        cases x
        · grind
        grind
      case succ i => grind
  hrel := by
    intro x y i
    rcases i with ⟨i,hi⟩
    cases i
    · simp ; grind
    grind
  fbin_surj := by simp
  frel_surj := by simp

def homoRefl {α n m} {M : GMA2 α n m} : Morph M M where
  f := id
  fbin := id
  frel := id
  hbin := by simp
  hrel := by simp
  fbin_surj := by simp
  frel_surj := by simp

def surj {α β} (f : α → β) : Prop := ∀ y : β, ∃ x : α, f x = y

@[simp]
def permute {α n m} (M0 : GMA2 α n m) (pbin : Fin n → Fin n) (prel : Fin m → Fin m)
  (_ : surj pbin) (_ : surj prel) : GMA2 α n m where
  bin n := M0.bin (pbin n)
  rel m := M0.rel (prel m)

def homoPerm {α n m} {M : GMA2 α n m} {pb pr hb hr}
  : Morph (permute M pb pr hb hr) M where
  f := id
  fbin := pb
  frel := pr
  hbin := by simp
  hrel := by simp
  fbin_surj := hb
  frel_surj := hr
