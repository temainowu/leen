import Mathlib

def Moduel α v [Add v] [AddMonoid α] [Monoid α] [DecidableEq α] [DecidableEq v] := v →₀ α

-- zero_add

lemma nodup_filter {α} : ∀ (x : Multiset α) p [DecidablePred p],
  x.Nodup → (Multiset.filter p x).Nodup := by
  intro x p i h
  apply @Multiset.nodup_of_le _ _ _ (Multiset.filter_le p x) h

instance {α v} [Add v] [AddMonoid α] [Monoid α] [DecidableEq α] [DecidableEq v] :
  Add (Moduel α v) where
  add x y := {
    support := {
      val := Multiset.filter (fun z ↦ x.toFun z + y.toFun z ≠ 0) (x.support.val ∪ y.support.val)
      nodup := by
        apply nodup_filter
        rw [Multiset.nodup_union]
        constructor
        · exact x.support.nodup
        exact y.support.nodup
      }
    toFun z := x.toFun z + y.toFun z
    mem_support_toFun z := by
      constructor
      · intro h
        simp! at h
        cases h
        case inl h => exact h.2
        case inr h => exact h.2
      intro h
      simp!
      have hx : @DFunLike.coe (v →₀ α) v (fun x ↦ α) Finsupp.instFunLike x z = x.toFun z := by rfl
      have hy : @DFunLike.coe (v →₀ α) v (fun x ↦ α) Finsupp.instFunLike y z = y.toFun z := by rfl
      rw [hx, hy]
      cases @or_not (x.toFun z = 0)
      case inl hx0 =>
        cases @or_not (y.toFun z = 0)
        case inl hy0 =>
          rw [hx0, hy0] at h
          simp at h
        case inr hy0 =>
          rw [hx0]
          simp!
          exact hy0
      case inr hx0 =>
        apply Or.inl
        constructor
        · exact hx0
        exact h
  }

lemma mod_eq {α v} [Add v] [AddMonoid α] [Monoid α] [DecidableEq α] [DecidableEq v] :
  ∀ x y : Moduel α v, x.support.val = y.support.val → x.toFun = y.toFun → x = y := by
  intro ⟨⟨xs,xn⟩,xf,hx⟩ ⟨⟨ys,yn⟩,yf,hy⟩ h0 h1
  congr

@[simp]
lemma toFun_add {α v} [Add v] [AddMonoid α] [Monoid α] [DecidableEq α] [DecidableEq v] :
  ∀ x y : Moduel α v, (x + y).toFun = fun z ↦ x.toFun z + y.toFun z := by intros ; rfl

@[simp]
lemma support_val_add {α v} [Add v] [AddMonoid α] [Monoid α] [DecidableEq α] [DecidableEq v] :
  ∀ x y : Moduel α v, (x + y).support.val =
    Multiset.filter (fun z ↦ x.toFun z + y.toFun z ≠ 0)
                    (x.support.val ∪ y.support.val) := by intros ; rfl

lemma add_comm_of_zero {α} [AddMonoid α] : ∀ x y : α, x = 0 ∨ y = 0 → x + y = y + x := by
  intro x y h
  cases h
  case inl h =>
    rw [h]
    simp
  case inr h =>
    rw [h]
    simp

lemma mod_add_comm {α v} [Add v] [AddMonoid α] [Monoid α] [DecidableEq α] [DecidableEq v] :
  ∀ x y : Moduel α v, x.support.val ∩ y.support.val = {} → x + y = y + x := by
  intro ⟨⟨xs,xn⟩,xf,hx⟩ ⟨⟨ys,yn⟩,yf,hy⟩
  simp!
  intro h
  apply mod_eq
  · simp
    rw [Multiset.union_comm]
    congr
    apply funext
    intro z
    unfold
    constructor
  simp!
  apply funext
  intro z
  apply add_comm_of_zero
  specialize hx z
  specialize hy z
  contrapose! h
  rw [←hy, ←hx] at h
  simp! at h
  sorry
