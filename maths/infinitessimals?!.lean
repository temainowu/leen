import Mathlib

theorem decite_true {α p} [Decidable p] :
  ∀ (h : p) (t : p → α) (e : ¬p → α), (if h0 : p then t h0 else e h0) = t h := by grind

theorem decite_false {α p} [Decidable p] :
  ∀ (h : ¬p) (t : p → α) (e : ¬p → α), (if h0 : p then t h0 else e h0) = e h := by grind


structure Rdec where
  s : Set ℝ
  no_nil : ∃ x, x ∈ s
  no_lob : ∀ x y : ℝ, y ∈ s → x ≤ y → x ∈ s
  no_max : ∀ x ∈ s, ∃ y ∈ s, x < y

structure Rsuc where
  s : Set ℝ
  no_nil : ∃ x, x ∈ s
  no_upb : ∀ x y : ℝ, y ∈ s → y ≤ x → x ∈ s
  no_min : ∀ x ∈ s, ∃ y ∈ s, y < x

inductive F where
  | r : ℝ    → F
  | s : Rdec → F
  | i : Rsuc → F

inductive G where
  | r : ℝ → G
  | s : ℝ → G
  | i : ℝ → G

noncomputable def toG : F → G
  | F.r x => G.r x
  | F.s x => G.s (sSup x.s)
  | F.i x => G.i (sInf x.s)

def toF : G → F
  | G.r x => F.r x
  | G.s x => F.s ⟨{v | v < x}, by
    use x - 1
    simp!
  , by
    intro a b h h0
    rw [Set.mem_setOf]
    rw [Set.mem_setOf] at h
    have h1 := le_trans h0 (le_of_lt h)
    have h2 : a = b ∨ a ≠ b := by grind
    cases h2
    case inl h2 =>
      rw [h2]
      exact h
    case inr h2 => grind
  , by
    intro a ha
    use ((a+x)/2)
    simp!
    constructor
    · ring_nf
      have h : (a * (1 / 2) + x * (1 / 2)) + (-(x * (1 / 2))) < x + (-(x * (1 / 2))) := by
        ring_nf
        rw [Set.mem_setOf] at ha
        grind
      exact lt_of_add_lt_add_right h
    ring_nf
    have h : a + (-(a * (1 / 2))) < (a * (1 / 2) + x * (1 / 2)) + (-(a * (1 / 2))) := by
      ring_nf
      rw [Set.mem_setOf] at ha
      grind
    exact lt_of_add_lt_add_right h⟩
  | G.i x => F.i ⟨{v | x < v}, by
    use x + 1
    simp!
  , by grind, by
    intro a ha
    use ((a+x)/2)
    grind⟩

structure H where
  r : ℝ
  e : Option Bool

def GtoH : G → H
  | G.r x => ⟨x, none⟩
  | G.s x => ⟨x, some ⊤⟩
  | G.i x => ⟨x, some ⊥⟩

def HtoG : H → G
  | ⟨x, none⟩ => G.r x
  | ⟨x, some ⊤⟩ => G.s x
  | ⟨x, some ⊥⟩ => G.i x

theorem sets_eq {α} : ∀ (x y : Set α), x = y ↔ ∀ z, z ∈ x ↔ z ∈ y := by
  intro x y
  constructor
  · intro hxy z
    constructor
    · intro hx
      rw [←hxy]
      exact hx
    intro hy
    rw [hxy]
    exact hy
  intro h
  grind

@[simp]
def x_maxim : F → Prop
  | F.r _ => False
  | F.s ⟨x,_,_,_⟩ => x = @Set.univ ℝ
  | F.i ⟨x,_,_,_⟩ => x = @Set.univ ℝ

theorem LUB_unique {s : Set ℝ} {x y : ℝ} : IsLUB s x → IsLUB s y → x = y := by
  intro hx hy
  have hx2' := @hx.2 y hy.1
  have hy2' := @hy.2 x hx.1
  grind

theorem GLB_unique {s : Set ℝ} {x y : ℝ} : IsGLB s x → IsGLB s y → x = y := by
  intro hx hy
  have hx2' := @hx.2 y hy.1
  have hy2' := @hy.2 x hx.1
  grind

example : (∀ x, toF (toG x) = x ∨ x_maxim x) ∧ (∀ x, toG (toF x) = x) := by
  unfold toF toG
  constructor
  · intro x
    cases x
    case r x => simp!
    case s x =>
      rcases x with ⟨x,hn,hb,hm⟩
      have h2 : x = @Set.univ ℝ ∨ x ≠ @Set.univ ℝ := by grind
      cases h2
      case inl h2 =>
        apply Or.inr
        simp!
        exact h2
      case inr h2 =>
        apply Or.inl
        simp!
        rw [sets_eq]
        rcases hn with ⟨v,hn⟩
        have h0 := @Real.isLUB_sSup x (by use v) (by
          unfold BddAbove upperBounds
          have h0 : ∃ u, u ∉ x := by grind
          rcases h0 with ⟨u,hu⟩
          use u
          simp!
          intro a ha
          contrapose! hb
          use u
          use a
          constructor
          · exact ha
          constructor
          · exact le_of_lt hb
          exact hu)
        intro z
        rw [Set.mem_setOf]
        constructor
        · intro h
          contrapose! h0
          rw [IsLUB, IsLeast, not_and]
          intro h1
          rw [lowerBounds, Set.notMem_setOf_iff, not_forall]
          use z
          rw [Classical.not_imp]
          constructor
          · intro a ha
            contrapose! h0
            exact hb z a ha (le_of_lt h0)
          rw [not_le]
          exact h
        intro h
        have h1 := hb z
        have h3 := hm z h
        rcases h3 with ⟨y,h11,h12⟩
        contrapose! h0
        rw [IsLUB, IsLeast, not_and]
        intro h3
        rw [lowerBounds, Set.notMem_setOf_iff, not_forall]
        use z
        rw [Classical.not_imp]
        constructor
        · intro a ha
          apply le_of_lt
          contrapose! hb
          use sSup x
          use z
          constructor
          · exact h
          constructor
          · exact h0
          rw [upperBounds] at h3
          contrapose! h3
          specialize hm (sSup x) h3
          simp!
          rcases hm with ⟨y,hm⟩
          use y
        have h4 : sSup x ∉ x := by
          contrapose! h3
          specialize hm (sSup x) h3
          rcases hm with ⟨y,hm⟩
          rw [upperBounds]
          simp!
          use y
        contrapose! h4
        exact hb (sSup x) z h h0
    case i x =>
      rcases x with ⟨x,hn,hb,hm⟩
      have h2 : x = @Set.univ ℝ ∨ x ≠ @Set.univ ℝ := by grind
      cases h2
      case inl h2 =>
        apply Or.inr
        simp!
        exact h2
      case inr h2 =>
        apply Or.inl
        simp!
        rw [sets_eq]
        rcases hn with ⟨v,hn⟩
        have h0 := @Real.isGLB_sInf x (by use v) (by
          have h0 : ∃ u, u ∉ x := by grind
          rcases h0 with ⟨u,hu⟩
          use u
          intro a ha
          contrapose! hb
          use u
          use a
          constructor
          · exact ha
          constructor
          · exact le_of_lt hb
          exact hu)
        intro z
        rw [Set.mem_setOf]
        constructor
        · intro h
          contrapose! h0
          rw [IsGLB, IsGreatest, not_and]
          intro h1
          rw [upperBounds, Set.notMem_setOf_iff, not_forall]
          use z
          rw [Classical.not_imp]
          constructor
          · intro a ha
            contrapose! h0
            exact hb z a ha (le_of_lt h0)
          rw [not_le]
          exact h
        intro h
        have h1 := hb z
        have h3 := hm z h
        rcases h3 with ⟨y,h11,h12⟩
        contrapose! h0
        rw [IsGLB, IsGreatest, not_and]
        intro h3
        rw [upperBounds, Set.notMem_setOf_iff, not_forall]
        use z
        rw [Classical.not_imp]
        constructor
        · intro a ha
          apply le_of_lt
          contrapose! hb
          use sInf x
          use z
          constructor
          · exact h
          constructor
          · exact h0
          rw [lowerBounds] at h3
          contrapose! h3
          specialize hm (sInf x) h3
          simp!
          rcases hm with ⟨y,hm⟩
          use y
        have h4 : sInf x ∉ x := by
          contrapose! h3
          specialize hm (sInf x) h3
          rcases hm with ⟨y,hm⟩
          rw [lowerBounds]
          simp!
          use y
        contrapose! h4
        exact hb (sInf x) z h h0
  intro x
  cases x
  case r x => simp!
  case s x =>
    simp!
    have h : {v | v < x}.Nonempty ∧ BddAbove {v | v < x} := by
      constructor
      · use x-1
        rw [Set.mem_setOf]
        simp!
      use x
      intro a ha
      exact le_of_lt ha
    have h0 : IsLUB {v | v < x} x := by
      constructor
      · intro a ha
        exact le_of_lt ha
      intro a ha
      specialize @ha ((x + a) / 2)
      grind
    have h3 := Real.isLUB_sSup h.1 h.2
    exact LUB_unique h3 h0
  case i x =>
    simp!
    have h : {v | x < v}.Nonempty ∧ BddBelow {v | x < v} := by
      constructor
      · use x + 1
        rw [Set.mem_setOf]
        simp!
      use x
      intro a ha
      exact le_of_lt ha
    have h0 : IsGLB {v | x < v} x := by
      constructor
      · intro a ha
        exact le_of_lt ha
      intro a ha
      specialize @ha ((x + a) / 2)
      grind
    have h3 := Real.isGLB_sInf h.1 h.2
    exact GLB_unique h3 h0

namespace H

def adde : Option Bool → Option Bool → Option Bool
  | none, y => y
  | x, none => x
  | some ⊤, some ⊤ => some ⊤
  | some ⊥, some ⊥ => some ⊥
  | some ⊤, some ⊥ => none
  | some ⊥, some ⊤ => none

def nege : Option Bool → Option Bool
  | none => none
  | some x => some ¬x

noncomputable def signe (x : H) : Option Bool :=
  match compare x.r 0 with
  | Ordering.eq => x.e
  | Ordering.lt => adde (some ⊥) x.e
  | Ordering.gt => adde (some ⊤) x.e

instance : Add H where
  add x y := ⟨x.r + y.r, adde x.e y.e⟩

noncomputable instance : Field H where
  zero := ⟨0,none⟩
  one := ⟨1,none⟩
  add := instAdd.1
  neg x := ⟨-x.r, nege x.e⟩
  mul x y := ⟨x.r * y.r, adde (signe x) (signe y)⟩
  nsmul n x := ⟨n * x.r, x.e⟩
  zsmul n x := ⟨n * x.r, x.e⟩
  qsmul n x := ⟨n * x.r, x.e⟩
  inv x := ⟨x.r⁻¹, nege x.e⟩
  add_assoc := by
    have h : ∀ x y : H, x + y = ⟨x.r + y.r, adde x.e y.e⟩ := by
      intro x y
      rfl
    intro a b c
    rw [h a b, h b c, h a _, h _ c]
    simp!
    constructor
    · rw [add_assoc]
    cases a.e
    · simp!
    case some a =>
      cases b.e
      · simp!
      case some b =>
        cases c.e
        · cases a
          · cases b
            · simp!
            simp!
          cases b
          · simp!
          simp!
        case some c =>
          cases a
          · cases b
            · cases c
              · simp!
              sorry
            cases c
            · simp!
            sorry
          cases b
          · cases c
            · sorry
            simp!
          cases c
          · sorry
          simp!





end H
