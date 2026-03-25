import Mathlib

structure Func α β where
  f : Set (α × β)
  dom := α
  cod := β
  natdom := {a : α | ∃ b : β, (a,b) ∈ f}
  natcod := {b : β | ∃ a : α, (a,b) ∈ f}
  npar := ∀ a : α, a ∈ natdom
  surj := ∀ b : β, b ∈ natcod
  func := ∀ a ∈ natdom, ∃ b : β, {x : β | (a,x) ∈ f} = {b}
  inj  := ∀ b ∈ natcod, ∃ a : α, {x : α | (x,b) ∈ f} = {a}
  apply (a : α) (in_dom : a ∈ natdom) (is_func : func) : β
  apply_applies : ∀ a in_d is_f, {apply a in_d is_f} = {x : β | (a,x) ∈ f}
  image (a : α) (in_dom : a ∈ natdom) : Set β
  image_images : ∀ a in_d, image a in_d = {x : β | (a,x) ∈ f}

def square : Func ℕ ℕ where
  f := {(n,n*n) | n : ℕ}
  apply a _ _ := a*a
  apply_applies := by simp
  image a _ := {a*a}
  image_images := by simp

@[simp]
def dec : Func ℕ ℕ where
  f := {(n+1,n) | n : ℕ}
  apply a _ _ := a-1
  apply_applies := by
    intro a
    cases a
    case zero => simp
    case succ a => simp
  image
    | 0, _ => {}
    | Nat.succ n, _ => {n}
  image_images := by
    intro a
    cases a
    case zero => simp
    case succ a => simp

@[simp]
def get_unique {α} [Inhabited α] (x : Set α) (h : ∃ a, x = {a}) : α := by
  rcases h with ⟨a,h⟩
  exact a

def inverse {α β} (F : Func α β) : Func β α where
  f := (fun (a,b) => (b,a)) '' F.f
  apply b in_d is_f := get_unique {x : α | (x, b) ∈ F.f} (by
    specialize is_f b in_d
    simp! at is_f
    exact is_f)
  image b _ := {x : α | (x, b) ∈ F.f}
  apply_applies := by
    intro a ha h
    specialize h a ha
    simp! at ha h
    rcases h with ⟨b,h⟩
    congr
  image_images := by simp

theorem square_num : ∀ n h0 h1, square.apply n h0 h1 = n*n := by
  intro n h0 h1
  rfl

theorem dec_num : ∀ n h0 h1, dec.apply n h0 h1 = n-1 := by
  intro n h0 h1
  rfl
