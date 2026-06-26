import Mathlib

/-inductive Power_aux (α : Type) (n : ℕ) where
  | zero : α → α → n = 0 → Power_aux α n
  | succ : α → (Power_aux α (n - 1)) → n > 0 → Power_aux α n

def Power : Type → ℕ → Type
  | _, 0 => Unit
  | x, 1 => x
  | x, Nat.succ (Nat.succ n) => Power_aux x n-/

inductive Power.{u} : ℕ → Type u → Type (u + 1) where
  | zer {α} : Power 0 α
  | one {α} : α → Power 1 α
  | con {n α} : α → (Power (n - 1) α) → n > 1 → Power n α

def phead {α n} {h : n > 0} : Power n α → α
  | Power.zer => by contradiction
  | Power.one x => x
  | Power.con x xs h => x

structure Cyc i n where
  p : Fin (Nat.succ n)
  x : Power i ℤ

def fe : Fin 0 → Empty := by
  intro x
  rcases x with ⟨x,h⟩
  simp at h

def ef : Empty → Fin 0 := by
  intro x
  apply Empty.elim
  exact x

def embedON (i n : ℕ) : Ordinal := n * Ordinal.omega0 ^ i

def add {α n} [Add α] : Power n α → Power n α → Power n α
  | Power.zer, _ => Power.zer
  | Power.one x, Power.one y => Power.one (x + y)
  | Power.con x xs hx, Power.con y ys hy => Power.con (x + y) (add xs ys) (by exact hx)

def pure {n} {α : Type u} : α → Power n α
  | x => match n with
    | 0 => Power.zer
    | 1 => Power.one x
    | n + 2 => Power.con x (pure x) (by simp)

instance {n} : Monad (Power n) where
  pure := pure
  bind := match n with
  | 0 => fun _ _ ↦ Power.zer
  | 1 => fun (Power.one x) f ↦ f x
  | _ + 2 => fun (Power.con x _ _) f ↦ (f x)

def mapPower {n α} (f : α → α) : Power n α → Power n α
  | Power.zer => Power.zer
  | Power.one x => Power.one (f x)
  | Power.con x xs h => Power.con (f x) (mapPower f xs) h

def mapBopPower {n α} (f : α → α → α) : Power n α → Power n α → Power n α
  | Power.zer, _ => Power.zer
  | Power.one x, Power.one y => Power.one (f x y)
  | Power.con x xs h, Power.con y ys _ => Power.con (f x y) (mapBopPower f xs ys) h

lemma add_eq_mBP_add {n α} [i : Add α] :
  (add : Power n α → Power n α → Power n α)
  = mapBopPower (· + ·) := by
  apply funext
  intro x
  apply funext
  intro y
  induction n
  case zero =>
    cases x
    case zer => rw [add.eq_def, mapBopPower.eq_def]
    case con => contradiction
  case succ n ih =>
    rw [add.eq_def, mapBopPower.eq_def]
    cases n
    case zero =>
      cases x
      case one x =>
        cases y
        case one y => simp
        case con => contradiction
      case con => contradiction
    case succ n =>
      cases x
      case con hx x xs =>
        cases y
        case con hy y ys =>
          simp!
          specialize ih xs ys
          exact ih

 /-
  match n, xs, ys with
    | 2, Power.one x', Power.one y' => Power.con (x + y) (Power.one (x' + y')) (by sorry)
    | Nat.succ (Nat.succ (Nat.succ n)), Power.con x' xs hx', Power.con y' ys hy' =>
        Power.con (x + y) (Power.con (x' + y'))
    fun (((x : α),(xs : Power α n)) : Power α n.succ) ((y : α),ys) ↦ ⟨x + y, add xs ys⟩
-/

instance {α n} [Add α] : Add (Power n α) where
  add := mapBopPower (· + ·)

instance {α n} [Mul α] : Mul (Power n α) where
  mul := mapBopPower (· * ·)

@[simp]
lemma add_def {n α} [i : Add α] : (@instAddPower α n i).1 = mapBopPower (· + ·) := by rfl

@[simp]
lemma mul_def {n α} [i : Mul α] : (@instMulPower α n i).1 = mapBopPower (· * ·) := by rfl

instance {i n} : Add (Cyc i n) where
  add
   | ⟨p, x⟩, ⟨q, y⟩ => ⟨p + q, x + y⟩

instance {i n} : Zero (Cyc i n) where
  zero := {
    p := 0
    x := 0
  }

def epi {i' n' i n} (f : Cyc i' n' → Cyc i n) : Prop :=
  (∀ x y : Cyc i' n', f (x + y) = f x + f y) ∧
  (∀ y : Cyc i n, ∃ x : Cyc i' n', f x = y)

lemma hom_thing : ∀ i n i' n',
  (∃ f : Cyc i' n' → Cyc i n, epi f) →
  embedON i n ≤ embedON i' n' := by
  intro i n i' n' h
  rcases h with ⟨f, ⟨hom,sur⟩⟩
  rw [embedON, embedON]
  cases i
  case zero =>
    cases i'
    case zero =>
      cases n
      case zero => simp
      case succ n =>
        simp!




instance
