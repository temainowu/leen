import Mathlib

def Exp (α : Type) : ℕ → Type
  | 0 => Unit
  | 1 => α
  | Nat.succ n => α × Exp α n

@[simp]
def mem : (n : ℕ) → Exp α n → α → Prop
  | 0, _, _ => False
  | 1, e, x => x = e
  | Nat.succ (Nat.succ n), e, x => x = e.1 ∨ mem (Nat.succ n) e.2 x

@[simp]
instance {α : Type} {n : ℕ} : Membership α (Exp α n) where
  mem e x := mem n e x

@[simp]
instance {α I : Type} : Membership α (Set (Exp α 0 → I → α)) where
  mem e x := (fun () _ ↦ x) ∈ e

inductive P where
  | atom : Bool → P
  | Or : P → P → P
  | And : P → P → P
  | Not : P → P
  | Impl : P → P → P
deriving DecidableEq

@[simp]
def interpret : P → Prop
  | P.atom b => b
  | P.Or x y => interpret x ∨ interpret y
  | P.And x y => interpret x ∧ interpret y
  | P.Not x => ¬ interpret x
  | P.Impl x y => interpret x → interpret y

structure Context (α I : Type) where
  Syn : (n : ℕ) → Set (Exp α n → I → α)
  Sem : α → Prop
-- Context represents a formal language
-- α is a type that represents statements in the language
-- Syn stores all the axioms and derivational rules in the language
-- these can be indexed by the type I for efficient generalizations of statement
-- Sem interprets all statements of type α as propositions.

@[simp]
def Axioms {α I} (L : Context α I) : Set (Exp α 0 → I → α) := L.Syn 0

@[simp]
def proves {α I : Type} (L : Context α I) : ℕ → α → Prop
  | 0, x => x ∈ Axioms L
  | Nat.succ gas, x => ∃ (n : ℕ) (i : I), ∃ f ∈ L.Syn n, ∃ (ante : Exp α n),
    (∀ a ∈ ante, proves L gas a) ∧ f ante i = x

def extend {α I} (L : Context α I) (x : α) : Context α I := {
      Syn
        | 0 => Axioms L ∪ {fun () _ ↦ x}
        | Nat.succ n => L.Syn n.succ
      Sem := L.Sem
  }

notation:40 Γ " ⊢ " p " in " n => proves Γ n p

notation:40 Γ " ⊢ " p => ∃ n, proves Γ n p

notation:40 Γ " ⊨ " p => Context.Sem Γ p

infix:50 " ▷ " => extend

def sound {α I} (Γ : Context α I) := ∀ p, (Γ ⊢ p) → Γ ⊨ p

def complete {α I} (Γ : Context α I) := ∀ p, (Γ ⊨ p) → Γ ⊢ p

def mySystem : Context P Unit where
  Syn
    | 0 => {fun () () ↦ P.atom ⊤}
    | 1 => {fun v () ↦ P.Not (P.Not v)}
    | 2 => {fun ⟨a,b⟩  () ↦ match a with
      | P.Impl q p => if q = b then p else P.atom ⊤ -- modus ponens
      | _ => P.atom ⊤
    }
    | _ => {}
  Sem := interpret

lemma reflex {α I} : ∀ (Γ : Context α I) (p : α), Γ ▷ p ⊢ p in 0 := by
  unfold extend proves Axioms instMembershipSetForallExpOfNatNatForall
  simp

def Trivial : Context Unit Unit where
  Syn
    | 0 => {fun () () ↦ ()}
    | _ => {}
  Sem _ := True

lemma Trivial_sound : sound Trivial := by
  intro p h
  rw [Trivial]
  simp

lemma Trivial_complete : complete Trivial := by
  intro p h
  use 0
  rw [Trivial]
  simp

/-
lemma mySystem_is_sound : sound mySystem := by
  unfold mySystem
  intro p h
  rcases h with ⟨n,h⟩
  simp at *
  cases p
  case atom p =>
    cases p
    case false =>
      cases n
      case zero =>
        simp at h
        rw [funext_iff, funext_iff] at h
        specialize h () ()
        simp at h
      case succ n =>
        cases n
        case zero =>
          simp at h
          rcases h with ⟨n,i,f,h1,ante,h2,h3⟩
          cases n
          case zero =>
            simp at *
            rw [funext_iff] at h1
            specialize h1 ante
            rw [funext_iff] at h1
            specialize h1 i
            rw [h3] at h1
            contradiction
          case succ n =>
            simp at *
          specialize h2 (P.atom ⊤)
-/
