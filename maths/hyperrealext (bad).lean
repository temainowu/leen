import Mathlib

@[simp]
def lowerBound (x : ℝ*) (s : Set ℝ*) : Prop := ∀ y ∈ s, x ≤ y

@[simp]
def upperBound (x : ℝ*) (s : Set ℝ*) : Prop := ∀ y ∈ s, y ≤ x

@[simp]
def supremum (x : ℝ*) (s : Set ℝ*) : Prop := ∀ y ∈ s, ∀ z ∉ s, y ≤ z → y ≤ x ∧ x ≤ z

@[simp]
def infimum (x : ℝ*) (s : Set ℝ*) : Prop := ∀ y ∈ s, ∀ z ∉ s, z ≤ y → z ≤ x ∧ x ≤ y

structure Sup where
  s : Set ℝ*
  lack_supremum : ¬∃ x : ℝ*, supremum x s
  bound_above   :  ∃ x : ℝ*, upperBound x s
  nbound_below  : ∀ x y : ℝ*, y ∈ s → x ≤ y → x ∈ s

structure Inf where
  i : Set ℝ*
  lack_infimum : ¬∃ x : ℝ*, infimum x i
  bound_below  :  ∃ x : ℝ*, lowerBound x i
  nbound_above : ∀ x y : ℝ*, y ∈ i → y ≤ x → x ∈ i

inductive ExtHypR where
  | hyp : ℝ*  → ExtHypR
  | sup : Sup → ExtHypR
  | inf : Inf → ExtHypR

namespace ExtHypR

/-
def empty : Sup where
  s := {}
  lack_supremum := by simp --< lack_supremum implies that s ≠ {}
  bound_above := by simp
  nbound_below := by simp
-/

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

theorem inf_inhabited (i : Inf) : ∃ x, x ∈ i.i := by
  have hli := i.lack_infimum
  have hbb := i.bound_below
  rcases hbb with ⟨u, hbb⟩
  rw [not_exists] at hli
  specialize hli u
  rw [infimum, not_forall] at hli
  rcases hli with ⟨x, hli⟩
  rw [Classical.not_imp] at hli
  use x
  exact hli.left

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

theorem inf_unbound (i : Inf) : ¬∃ x : ℝ*, upperBound x i.i := by
  rcases inf_inhabited i with ⟨y,hy⟩
  cases i
  case mk i hli hbb hna =>
  simp! at hy
  rw [not_exists]
  intro x
  simp!
  have h : x ∈ i ∨ x ∉ i := by grind
  cases h
  case inl h =>
    use x+1
    constructor
    · have h0 := hna (x+1) x h
      apply h0
      simp
    simp
  case inr h =>
    use y
    constructor
    · exact hy
    have h0 := hna x y hy
    contrapose! h0
    constructor
    · exact h0
    exact h

@[simp]
def comp : ExtHypR → ExtHypR
  | hyp x => hyp x
  | sup ⟨s, hls, hba, hnb⟩ => inf ⟨sᶜ,
                  (by
                    rw [not_exists]
                    intro x
                    rw [infimum, not_forall]
                    rw [not_exists] at hls
                    specialize hls x
                    rw [supremum, not_forall] at hls
                    rcases hls with ⟨x1,hls⟩
                    rw [Classical.not_imp] at hls
                    rcases hls with ⟨h0, h1⟩
                    rw [not_forall] at h1
                    rcases h1 with ⟨x2, h1⟩
                    use x2
                    rw [Classical.not_imp] at *
                    constructor
                    · exact h1.left
                    rw [not_forall]
                    use x1
                    rw [Classical.not_imp]
                    constructor
                    · rw [Set.mem_compl_iff, not_not]
                      exact h0
                    exact h1.right
                  ), (by
                    rcases sup_inhabited ⟨s, hls, hba, hnb⟩ with ⟨x,h⟩
                    use x
                    rw [lowerBound]
                    intro y h0
                    have h1 := hnb y x h
                    contrapose! h0
                    rw [Set.mem_compl_iff, not_not]
                    apply h1
                    exact le_of_lt h0
                  ), (by
                    intro a b h0 h1
                    simp! at *
                    contrapose! hls
                    have h2 := hnb b a hls h1
                    contrapose! h2
                    exact h0
                  )
                  ⟩
  | inf ⟨i, hli, hbb, hna⟩ => sup ⟨iᶜ,
                  by
                    rw [not_exists]
                    intro x
                    rw [supremum, not_forall]
                    rw [not_exists] at hli
                    specialize hli x
                    rw [infimum, not_forall] at hli
                    rcases hli with ⟨x1, hli⟩
                    rw [Classical.not_imp] at hli
                    rcases hli with ⟨h0, h1⟩
                    rw [not_forall] at h1
                    rcases h1 with ⟨x2, h1⟩
                    use x2
                    rw [Classical.not_imp] at *
                    constructor
                    · exact h1.left
                    rw [not_forall]
                    use x1
                    rw [Classical.not_imp]
                    constructor
                    · rw [Set.mem_compl_iff, not_not]
                      exact h0
                    exact h1.right,
                  by
                    rcases inf_inhabited ⟨i, hli, hbb, hna⟩ with ⟨x,h⟩
                    use x
                    rw [upperBound]
                    intro y h0
                    have h1 := hna y x h
                    rw [Set.mem_compl_iff] at h0
                    contrapose! h0
                    apply h1
                    exact le_of_lt h0,
                  by
                    intro a b h0 h1
                    simp! at *
                    contrapose! hli
                    have h2 := hna b a hli h1
                    contrapose! h2
                    exact h0
                  ⟩


/- nbound__s make this unnecessary:
@[simp]
def eq : ExtHypR → ExtHypR → Prop
  | hyp x, hyp y => x = y
  | sup x, sup y => (∀ u : ℝ*, upperBound u x.s ↔ upperBound u y.s)
  | inf x, inf y => (∀ u : ℝ*, lowerBound u x.i ↔ lowerBound u y.i)
  | _, _ => False

def eq.eqv : Equivalence eq where
  refl := by
    intro x
    simp
    cases x
    · simp
    · simp
    simp
  symm := by
    intro x y h
    simp only [eq] at *
    cases x
    · cases y
      · grind
      · simp at h
      simp at h
    · cases y
      · simp at h
      · grind
      simp at h
    cases y
    · simp at h
    · simp at h
    grind
  trans := by
    intro x y z hxy hyz
    cases x
    · cases y
      · cases z
        · simp at *
          grind
        · simp at hyz
        simp at hyz
      · simp at hxy
      simp at hxy
    · cases y
      · simp at hxy
      · cases z
        · simp at hyz
        · rw [eq] at *
          intro u
          specialize hxy u
          specialize hyz u
          constructor
          · intro h
            apply hyz.1
            apply hxy.1
            exact h
          intro h
          apply hxy.2
          apply hyz.2
          exact h
        simp at hyz
      simp at hxy
    cases y
    · simp at hxy
    · simp at hxy
    cases z
    · simp at hyz
    · simp at hyz
    rw [eq] at *
    intro u
    specialize hxy u
    specialize hyz u
    constructor
    · intro h
      apply hyz.1
      apply hxy.1
      exact h
    intro h
    apply hxy.2
    apply hyz.2
    exact h

instance : Setoid ExtHypR where
  r := eq
  iseqv := eq.eqv
-/

@[simp]
def eq :  ExtHypR → ExtHypR → Prop
  | hyp x, hyp y => x = y
  | sup x, sup y => x.s = y.s
  | inf x, inf y => x.i = y.i
  | sup x, inf y => x.s = y.iᶜ
  | inf x, sup y => x.i = y.sᶜ
  | _, _ => False

def eq.eqv : Equivalence eq where
  refl := by
    intro x
    simp
    cases x
    · simp
    · simp
    simp
  symm := by
    intro x y h
    simp only [eq] at *
    cases x
    · cases y
      · grind
      · simp at h
      simp at h
    · cases y
      · simp at h
      · grind
      simp! at *
      rw [h]
      simp
    cases y
    · simp at h
    · simp! at *
      rw [h]
      simp
    grind
  trans := by
    intro x y z hxy hyz
    cases x
    · cases y
      · cases z
        · simp at *
          grind
        · simp at hyz
        simp at hyz
      · simp at hxy
      simp at hxy
    · cases y
      · simp at hxy
      · cases z
        · simp at hyz
        · rw [eq] at *
          rw [hxy, hyz]
        rw [eq, eq] at *
        rw [hxy, hyz]
      cases z
      · simp at hyz
      · rw [eq] at *
        rw [hxy, hyz]
        simp
      rw [eq, eq] at *
      rw [hxy, hyz]
    cases y
    · simp at hxy
    · cases z
      · simp at hyz
      · rw [eq, eq] at *
        rw [hxy, hyz]
      rw [eq] at *
      rw [hxy, hyz]
      simp
    cases z
    · simp at hyz
    · rw [eq, eq] at *
      rw [hxy, hyz]
    rw [eq] at *
    rw [hxy, hyz]

instance : Setoid ExtHypR where
  r := eq
  iseqv := eq.eqv

def lt : ExtHypR → ExtHypR → Prop
  | hyp x, hyp y => x < y
  | hyp x, sup s => ∃ y ∈ s.s, x ≤ y
  | inf i, hyp x => ∃ y ∈ i.i, y ≤ x
  | hyp x, inf i => lowerBound x i.i
  | sup s, hyp x => upperBound x s.s
  | sup s', sup s => ∃ y ∈ s.s, upperBound y s'.s
  | inf i, inf i' => ∃ y ∈ i.i, lowerBound y i'.i
  | sup s, inf i  => ∀ y ∈ s.s, lowerBound y i.i
  | inf i, sup s  => ∃ y ∈ i.i, ∃ y' ∈ s.s, y ≤ y'

def le : ExtHypR → ExtHypR → Prop
  | hyp x, hyp y => x ≤ y
  | hyp x, sup s => ∃ y ∈ s.s, x ≤ y
  | inf i, hyp x => ∃ y ∈ i.i, y ≤ x
  | hyp x, inf i => lowerBound x i.i
  | sup s, hyp x => upperBound x s.s
  | sup s', sup s => eq (sup s') (sup s) ∨ ∃ y ∈ s.s, upperBound y s'.s
  | inf i, inf i' => eq (inf i') (inf i) ∨ ∃ y ∈ i.i, lowerBound y i'.i
  | sup s, inf i  => ∀ y ∈ s.s, lowerBound y i.i
  | inf i, sup s  => ∃ y ∈ i.i, ∃ y' ∈ s.s, y ≤ y'

instance : LT ExtHypR where
  lt := lt

instance : LE ExtHypR where
  le := le

def compare (x : ExtHypR) (y : ExtHypR) [Decidable (x < y)] [Decidable (x = y)] : Ordering :=
  if x = y then Ordering.eq else
  if x < y then Ordering.lt else Ordering.gt

@[simp]
def term_aux : ExtHypR → ExtHypR → ℕ
  | hyp _, _ => 0
  | _, hyp _ => 0
  | sup _, sup _ => 0
  | inf _, inf _ => 0
  | sup _, inf _ => 1
  | inf _, sup _ => 1

@[simp]
def add : ExtHypR → ExtHypR → ExtHypR
    | hyp x, hyp y => hyp (x + y)
    | sup ⟨xs, xls, xba, xnb⟩, sup ⟨ys, yls, yba, ynb⟩ => sup ⟨(fun (a,b) => a + b) '' (xs ×ˢ ys),
                          by
                            simp
                            intro a
                            rcases sup_inhabited ⟨xs, xls, xba, xnb⟩ with ⟨x, hx⟩
                            rcases sup_inhabited ⟨ys, yls, yba, ynb⟩ with ⟨y, hy⟩
                            use (x + y)
                            rcases xba with ⟨ux, xba⟩
                            rcases yba with ⟨uy, yba⟩
                            constructor
                            · sorry
                            use (ux + uy)
                            constructor
                            · sorry
                            simp at *
                            constructor
                            · sorry
                            intro h
                            sorry
                          , by
                            sorry
                          , by
                            sorry
                          ⟩
    | inf x, inf y => inf ⟨(fun (a,b) => a + b) '' (x.i ×ˢ y.i),
                          by sorry,
                          by sorry,
                          by sorry⟩
    | hyp x, sup y => sup ⟨(x + ·) '' y.s,
                          by sorry,
                          by sorry,
                          by sorry⟩
    | sup y, hyp x => sup ⟨(x + ·) '' y.s,
                          by sorry,
                          by sorry,
                          by sorry⟩
    | hyp x, inf y => inf ⟨(x + ·) '' y.i,
                          by sorry,
                          by sorry,
                          by sorry⟩
    | inf y, hyp x => inf ⟨(x + ·) '' y.i,
                          by sorry,
                          by sorry,
                          by sorry⟩
    | sup x, inf y => add (sup x) (comp (inf y))
    | inf y, sup x => add (inf y) (comp (sup x))
termination_by x y => term_aux x y
decreasing_by
  · simp
  simp

def mul : ExtHypR → ExtHypR → ExtHypR
    | hyp x, hyp y => hyp (x * y)
    | sup ⟨xs, xls, xba, xnb⟩, sup ⟨ys, yls, yba, ynb⟩ => sup ⟨(fun (a,b) => a * b) <$> (xs ×ˢ ys),
                          by
                            sorry
                          , by
                            sorry
                          , by
                            sorry
                          ⟩
    | inf x, inf y => inf ⟨(fun (a,b) => a * b) <$> (x.i ×ˢ y.i),
                          by sorry,
                          by sorry,
                          by sorry⟩
    | hyp x, sup y => sup ⟨(x * ·) <$> y.s,
                          by sorry,
                          by sorry,
                          by sorry⟩
    | sup y, hyp x => sup ⟨(x * ·) <$> y.s,
                          by sorry,
                          by sorry,
                          by sorry⟩
    | hyp x, inf y => inf ⟨(x * ·) <$> y.i,
                          by sorry,
                          by sorry,
                          by sorry⟩
    | inf y, hyp x => inf ⟨(x * ·) <$> y.i,
                          by sorry,
                          by sorry,
                          by sorry⟩
    | sup x, inf y => mul (sup x) (comp (inf y))
    | inf y, sup x => mul (inf y) (comp (sup x))
termination_by x y => term_aux x y
decreasing_by
  · simp
  simp

theorem add_commutes : ∀ x y, eq (add (sup x) (inf y)) (add (inf y) (sup x)) := by
  intro x y
  cases x
  case mk xs xls xba xnb =>
  cases y
  case mk yi yli ybb yna =>
  simp only [eq, add, comp, Set.image_prod]


instance : Add ExtHypR where
  add := add

noncomputable instance : Neg ExtHypR where
  neg
    | hyp x => hyp (-x)
    | sup ⟨xs, xls, xba, xnb⟩ => inf ⟨(-·) '' xs
                    , by
                        rw [not_exists] at *
                        simp! at *
                        intro z
                        specialize xls (-z)
                        rcases xls with ⟨y, hy, w, hw, hyw, xls⟩
                        use y
                        constructor
                        · exact hy
                        use -w
                        constructor
                        · rw [neg_neg]
                          exact hw
                        simp
                        grind
                    , by
                        rcases xba with ⟨u,xba⟩
                        use -u
                        simp!
                        exact xba
                    , by
                        simp!
                        intro x y hy hyx
                        apply xnb (-x) y hy
                        grind
                    ⟩
    | inf ⟨xi, xli, xbb, xna⟩ => sup ⟨(-·) '' xi
                    , by
                        rw [not_exists] at *
                        intro x
                        specialize xli (-x)
                        simp! at *
                        rcases xli with ⟨y, hy, w, hw, hyw, xli⟩
                        use y
                        constructor
                        · exact hy
                        use -w
                        constructor
                        · rw [neg_neg]
                          exact hw
                        simp
                        grind
                    , by
                        rcases xbb with ⟨u,xbb⟩
                        use -u
                        simp!
                        exact xbb
                    , by
                        simp!
                        intro x y hy hxy
                        apply xna (-x) y hy
                        grind
                    ⟩

noncomputable instance : Field ExtHypR where
  zero := hyp 0
  one := hyp 1
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
    | inf ⟨xi, xli, xbb, xna⟩ => inf ⟨((n * ·) '' xi), by sorry, by sorry, by sorry⟩

/-
instance : Ord ExtHypR where
  compare x y := @compare x y (by
    sorry
    ) (by
    sorry
    )
-/

noncomputable def μ : MeasurableSpace ℝ → ExtHypR
  | x => sorry

end ExtHypR
