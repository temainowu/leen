import Mathlib

@[simp]
def lowerBound (x : ℝ*) (s : Set ℝ*) : Prop := ∀ y ∈ s, x ≤ y

@[simp]
def upperBound (x : ℝ*) (s : Set ℝ*) : Prop := ∀ y ∈ s, y ≤ x

@[simp]
def supremum (x : ℝ*) (s : Set ℝ*) : Prop := ∀ y ∈ s, ∀ z ∉ s, y ≤ z → y ≤ x ∧ x ≤ z

structure Sup where
  s : Set ℝ*
  lack_supremum : ¬∃ x : ℝ*, supremum x s
  bound_above   :  ∃ x : ℝ*, upperBound x s
  nbound_below  : ∀ x y : ℝ*, y ∈ s → x ≤ y → x ∈ s

inductive ExtHypR where
  | hyp : ℝ*  → ExtHypR
  | sup : Sup → ExtHypR

namespace ExtHypR

theorem sup_inhabited (s : Sup) : ∃ x, x ∈ s.s := by
  have hls := s.lack_supremum
  have hba := s.bound_above
  rcases hba with ⟨u, hba⟩
  rw [not_exists] at hls
  specialize hls u
  rw [supremum, not_forall] at hls
  rcases hls with ⟨x, hls⟩
  rw [Classical.not_imp] at hls
  use x
  exact hls.left

theorem sup_unbound (s : Sup) : ¬∃ x : ℝ*, lowerBound x s.s := by
  rcases sup_inhabited s with ⟨y,hy⟩
  cases s
  case mk s hls hba hnb =>
  simp! at hy
  rw [not_exists]
  intro x
  simp!
  have h : x ∈ s ∨ x ∉ s := by grind
  cases h
  case inl h =>
    use x-1
    constructor
    · have h0 := hnb (x-1) x h
      apply h0
      simp
    simp
  case inr h =>
    use y
    constructor
    · exact hy
    have h0 := hnb x y hy
    contrapose! h0
    constructor
    · exact h0
    exact h

def lt : ExtHypR → ExtHypR → Prop
  | hyp x, hyp y => x < y
  | hyp x, sup s => ∃ y ∈ s.s, x ≤ y
  | sup s, hyp x => upperBound x s.s
  | sup s', sup s => ∃ y ∈ s.s, upperBound y s'.s

def le : ExtHypR → ExtHypR → Prop
  | hyp x, hyp y => x ≤ y
  | hyp x, sup s => ∃ y ∈ s.s, x ≤ y
  | sup s, hyp x => upperBound x s.s
  | sup s', sup s => (sup s' = sup s) ∨ ∃ y ∈ s.s, upperBound y s'.s

instance : LT ExtHypR where
  lt := lt

instance : LE ExtHypR where
  le := le

@[simp]
noncomputable def add : ExtHypR → ExtHypR → ExtHypR
    | hyp x, hyp y => hyp (x + y)
    | sup ⟨xs, xls, xba, xnb⟩, sup ⟨ys, yls, yba, ynb⟩ => sup ⟨(fun (a,b) => a + b) '' (xs ×ˢ ys),
                          by
                            have h : ∀ sx sy, supremum sx xs ∧ supremum sy ys → supremum (sx + sy) ((fun (a,b) ↦ a + b) '' xs ×ˢ ys) := by
                              simp
                              intro sx sy hxs hys y hy z hz hyz
                              constructor
                              · contrapose! hxs
                                use y

                            have xls1 := xls
                            contrapose! xls1
                            rcases xls1 with ⟨s,xls1⟩

                            use s
                            simp!
                            intro y hy z hz hyz
                            have yls1 := yls
                            contrapose! yls1
                            use s
                            simp!
                            intro y' hy' z' hz' hyz'
                            contrapose! xls1
                            rw [supremum, not_forall]
                            have h0 {α} : ∀ (x : α) (y : Set α), {x} ⊆ y → x ∈ y := by simp
                            use (y+y')
                            rw [Classical.not_imp]
                            constructor
                            · apply h0
                              have h1 : {y+y'} = (fun a ↦ a.1 + a.2) '' {(y,y')} := by simp
                              rw [h1]
                              have h3 {α β} : ∀ (x : α) (y : Set α) (f : α → β), {x} ⊆ y → f '' {x} ⊆ f '' y := by
                                intro x a f h
                                grind
                              apply h3 (y,y') (xs ×ˢ ys) (fun a ↦ a.1 + a.2)
                              simp
                              constructor
                              · exact hy
                              exact hy'
                            rw [not_forall]
                            use |z|+|z'|
                            simp
                            constructor
                            · sorry
                            constructor
                            · grind
                            intro h
                            apply lt_trans
                            constructor
                            ·
                          , by
                            sorry
                          , by
                            sorry
                          ⟩
    | hyp x, sup y => sup ⟨(x + ·) '' y.s,
                          by sorry,
                          by sorry,
                          by sorry⟩
    | sup y, hyp x => sup ⟨(x + ·) '' y.s,
                          by sorry,
                          by sorry,
                          by sorry⟩

noncomputable def mul : ExtHypR → ExtHypR → ExtHypR
    | hyp x, hyp y => hyp (x * y)
    | sup ⟨xs, xls, xba, xnb⟩, sup ⟨ys, yls, yba, ynb⟩ => sup ⟨(fun (a,b) => a * b) <$> (xs ×ˢ ys),
                          by
                            sorry
                          , by
                            sorry
                          , by
                            sorry
                          ⟩
    | hyp x, sup y => sup ⟨(x * ·) <$> y.s,
                          by sorry,
                          by sorry,
                          by sorry⟩
    | sup y, hyp x => sup ⟨(x * ·) <$> y.s,
                          by sorry,
                          by sorry,
                          by sorry⟩

@[simp]
noncomputable instance : Add ExtHypR where
  add := add

@[simp]
noncomputable instance : Mul ExtHypR where
  mul := mul

noncomputable instance : Neg ExtHypR where
  neg
    | hyp x => hyp (-x)
    | sup s@⟨xs, xls, xba, xnb⟩ => sup ⟨((-·) '' xs)ᶜ
                    , by
                        rw [not_exists] at *
                        simp! at *
                        intro z
                        specialize xls (-z)
                        rcases xls with ⟨y, hy, w, hw, hyw, xls⟩
                        use -w
                        constructor
                        · rw [neg_neg]
                          exact hw
                        use y
                        constructor
                        · exact hy
                        simp
                        grind
                    , by
                        next h0 =>
                        rcases sup_inhabited s with ⟨x,hx⟩
                        rw [h0] at hx
                        simp! at hx
                        use -x
                        simp!
                        intro y hy
                        contrapose! hy
                        apply xnb (-y) x hx
                        grind
                    , by
                        simp!
                        intro x y hy hyx
                        contrapose! hy
                        apply xnb (-y) (-x) hy
                        grind
                    ⟩

@[simp]
noncomputable instance : Field ExtHypR where
  zero := hyp 0
  one := hyp 1
  zero_add := by
    intro a
    cases a
    case hyp a => sorry
    case sup a => sorry
  nsmul n
    | hyp x => hyp (n * x)
    | sup ⟨xs, xls, xba, xnb⟩ => sup ⟨((n * ·) '' xs),
                                      by
                                        rw [not_exists]
                                        intro x
                                        simp! at *
                                        rcases xba with ⟨u, xba⟩
                                        have h := xba (-u)
                                        use -u
                                        constructor
                                        · sorry
                                        use (n*u)
                                        constructor
                                        · sorry
                                        constructor
                                        · sorry
                                        sorry
                                      , by
                                        sorry
                                      , by
                                        sorry
                                      ⟩

/-
def compare (x : ExtHypR) (y : ExtHypR) [Decidable (x < y)] [Decidable (x = y)] : Ordering :=
  if x = y then Ordering.eq else
  if x < y then Ordering.lt else Ordering.gt

instance : Ord ExtHypR where
  compare x y := @compare x y (by
    sorry
    ) (by
    sorry
    )

noncomputable def μ : MeasurableSpace ℝ → ExtHypR
  | x => sorry
-/


end ExtHypR
