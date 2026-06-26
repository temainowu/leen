import Mathlib

/-
lemma lt_mul : ∀ a b c : ℕ, 1 < a → 0 < b → b ≤ c → b < c * a := by
  intro a b c ha hb hc
  cases b
  case zero => contradiction
  case succ b =>
  cases a
  case zero => contradiction
  case succ a =>
  cases a
  case zero => contradiction
  case succ a =>
  cases c
  case zero => contradiction
  case succ c =>
  induction c generalizing a b
  case zero =>
    simp! at hc
    rw [hc]
    simp!
  case succ c ih =>
    rw [add_mul]
    apply Nat.add_lt_add
    · cases b
      case zero => simp!
      case succ b =>
      apply ih b
      · simp
      · exact ha
      simp! at hc
      simp!
      exact hc
    simp

lemma lt_pow : ∀ a b : ℕ, 1 < a → 1 < b → b < b ^ a := by
  intro a b ha hb
  cases a
  case zero => contradiction
  case succ a =>
  induction a generalizing b
  case zero => contradiction
  case succ a ih =>
    rw [Nat.pow_succ]
    apply lt_mul
    case _ => exact hb
    case _ => apply lt_trans (by simp) hb
    case _ =>
      cases a
      case zero => simp
      case succ a =>
        apply Nat.le_pow
        simp
-/

def enum {m n : ℕ} (i : Fin (m.succ ^ n)) : Vector (Fin m.succ) n := match m, n, i with
  | 0, 0, _ => ⟨#[],by simp⟩
  | 0, Nat.succ n, _ => ⟨(⟨0,by simp⟩ :: (@enum 0 n 0).1.toList).toArray ,by simp⟩
  | m, 0, _ => ⟨#[],by simp⟩ -- ⟨i.1,by rcases i with ⟨i,l⟩; simp at l; exact l⟩
  | m, Nat.succ n, ⟨j,l⟩ =>
    ⟨(⟨j / (m.succ ^ n), Nat.div_lt_of_lt_mul l⟩ ::
     (@enum m n ⟨i % (m.succ ^ n), Nat.mod_lt i (by simp)⟩).1.toList).toArray, by simp⟩

lemma eq_of_div_eq_div : ∀ a b n : ℕ, 0 < n → a / n = b / n → a = b := by
  intro a b n hn hab
  sorry

lemma nat_div_mul : ∀ a b c : ℕ, a / (b * c) = (a / b) / c := by 
  intro a b c 
  cases a 
  case zero => simp 
  case succ a => simp


lemma enum_inj {m n : ℕ} : ∀ a b : Fin (m.succ ^ n), a = b ↔ enum a = enum b := by
  intro a b
  constructor
  · intro h
    congr
  rcases a with ⟨a,ha⟩
  rcases b with ⟨b,hb⟩
  rw [enum.eq_def, enum.eq_def]
  induction n generalizing m
  case zero =>
    cases m
    case zero =>
      revert hb ha
      simp!
      grind
    case succ m =>
      revert hb ha
      simp!
      grind
  case succ n ih =>
    cases m
    case zero =>
      revert hb ha
      simp!
      grind
    case succ m =>
      simp!
      intro h0 h1
      simp! at ih
      specialize @ih (m + 1) (by
        rw [Nat.pow_succ] at ha
        sorry
      ) (by
        sorry
      )
      apply ih
      cases n
      case zero => simp
      case succ n =>
        simp
        constructor
        · rw [Nat.pow_succ, @div_mul ℕ {
            inv := sorry

          } a ((m + 1 + 1) ^ n) (m + 1 + 1)] at h0

      case _ =>
        cases n
        case zero => simp
        case succ n => sorry
      case _ =>





instance {m n : ℕ} : Fintype (Vector (Fin m) n) where
  elems := {
    val := match m with
      | 0 => {}
      | Nat.succ m => enum <$> (_ : Fintype (Fin (m.succ ^ n))).elems.val
    nodup := by
      cases m
      case zero => simp
      case succ m =>
        simp!
  }

def cube {m n : ℕ} : Finset (Vector (Fin m) n) := ({ (_ : Vector (Fin m) n) | True } : Finset (Vector (Fin m) n))

def sum {m n : ℕ} (x : Vector (Fin m) n) : ℕ := Vector.foldr (fun ⟨a,_⟩ b ↦ a + b) 0 x

instance {m n : ℕ} : Add (Vector (Fin m) n) where
  add x y := sum x

def x (m n c : ℕ) : Vector (Fin m) n
