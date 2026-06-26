import Mathlib

theorem decite_true {α p} [inst : Decidable p] :
  ∀ (h : p) (t : p → α) (e : ¬p → α), (if h0 : p then t h0 else e h0) = t h := by
    intro h t e
    cases inst
    case isFalse =>
      contradiction
    case isTrue =>
      rw [dite]

theorem decite_false {α p} [inst : Decidable p] :
  ∀ (h : ¬p) (t : p → α) (e : ¬p → α), (if h0 : p then t h0 else e h0) = e h := by
    intro h t e
    cases inst
    case isFalse =>
      rw [dite]
    case isTrue =>
      contradiction

structure Basis where
  N : ℕ
  Q : ℕ
  R : ℕ

def Basis.lt : Basis → Basis → Prop
  | ⟨n,q,r⟩, ⟨n0,q0,r0⟩ =>
    if _ : r < r0 then True else
    if _ : r0 < r then False else
    if _ : q < q0 then True else
    if _ : q0 < q then False else n < n0

instance : LT Basis where
  lt := Basis.lt

instance (a b : Basis) : Decidable (a < b) := by
  rcases a with ⟨na,qa,ra⟩
  rcases b with ⟨nb,qb,rb⟩
  unfold LT.lt instLTBasis Basis.lt
  have hrt := ra.decLt rb
  have hqt := qa.decLt qb
  have hrf := rb.decLt ra
  have hqf := qb.decLt qa
  dsimp only []
  cases hrt
  case isTrue hrt =>
    apply isTrue
    rw [decite_true]
    · simp
    exact hrt
  case isFalse hrt =>
    rw [decite_false]
    · cases hrf
      case isTrue hrf =>
        rw [decite_true]
        · apply isFalse
          simp
        exact hrf
      case isFalse hrf =>
        rw [decite_false]
        cases hqt
        case isTrue hqt =>
          rw [decite_true]
          · apply isTrue
            simp
          exact hqt
        case isFalse hqt =>
          rw [decite_false]
          · cases hqf
            case isTrue hqf =>
              rw [decite_true]
              · apply isFalse
                simp
              exact hqf
            case isFalse hqf =>
              rw [decite_false]
              · exact Nat.decLt na nb
              exact hqf
          exact hqt
        exact hrf
    exact hrt

structure Blade where
  m : ℝ
  b : Basis
  h : 0 < m

def Blade.lt : Blade → Blade → Prop
  | ⟨m,b,_⟩, ⟨m0,b0,_⟩ =>
    if b < b0 then True else
    if b0 < b then False else m < m0

instance : LT Blade where
  lt := Blade.lt

structure Scale where
  vec : List Blade
  h : ∀ (i : ℕ) (hi : i + 1 < vec.length), vec[i].b < vec[i+1].b

def Scale.lt : Scale → Scale → Prop
  | ⟨[], h⟩, ⟨[], h0⟩ => False
  | ⟨x :: xs, h⟩, ⟨[], h0⟩ => False
  | ⟨[], h⟩, ⟨y :: ys, h0⟩ => True
  | ⟨x :: xs, h⟩, ⟨y :: ys, h0⟩ => x < y ∨ Scale.lt ⟨xs, by
            intro i hi
            specialize h i.succ (by simp! ; exact hi)
            simp! at h
            exact h⟩ ⟨ys, by
            intro i hi
            specialize h0 i.succ (by simp! ; exact hi)
            simp! at h
            exact h0⟩

instance : LT Scale where
  lt := Scale.lt

instance : Zero Scale where
  zero := ⟨[], by
    intro i hi
    simp at hi
  ⟩

set_option trace.Meta.synthInstance true

def μ (s : Set ℝ) : Scale :=
  if s = {} then 0 else
  if s = { x | sInf s < x ∧ x < sSup s} then ⟨[⟨sSup s - sInf s, ⟨0,0,1⟩, by
    sorry
  ⟩], by
    intro i hi
    simp at hi
  ⟩ else
  if s = { x | sInf s < x ∧ x < sSup s ∧ ∃ z : ℚ, x = ↑z} then ⟨[⟨sSup s - sInf s, ⟨0,1,0⟩, by
    sorry
  ⟩], by
    intro i hi
    simp at hi
  ⟩ else
  if s = { x | sInf s ≤ x ∧ x ≤ sSup s ∧ ∃ z : ℤ, x = ↑z} then ⟨[⟨(sSup s - sInf s).succ, ⟨0,0,0⟩, by
    sorry
  ⟩], by
    intro i hi
    simp at hi
  ⟩ else
  if ∃ a b : Set ℝ, a ∩ b = ∅ ∧ a ∪ b = s then μ a + μ b else {}
