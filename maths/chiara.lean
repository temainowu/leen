import Mathlib

def limit (a : ℕ → ℝ) (l : ℝ) : Prop := ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |a n - l| < ε

theorem ther : ∀ a : ℕ → ℝ,
  (∃ b, ∀ n, a n < b) →
  (∀ n m, n ≤ m → a n ≤ a m) →
  (∃ l, limit a l) := by
    intro a bounded increasing
    let S := {a n | n : ℕ}
    have hS : BddAbove S := by
      rcases bounded with ⟨b,hb⟩
      use b
      intro x hx
      rcases hx with ⟨n,hn⟩
      rw [←hn]
      exact le_of_lt (hb n)
    have hS_LUB := Real.isLUB_sSup (by
      use a 0
      use 0
    ) hS
    let l := sSup S
    have hl : l = sSup S := by rfl
    use l
    rw [limit]
    intro ε hε
    have hN : ∃ N, l - ε < a N := by
      have h0 : ∀ x, x ∈ S → ∃ N, x = a N := by
        intro x hx
        grind
      have h1 : ¬IsLUB S (l - ε) := by
        have h3 := hS_LUB.2
        contrapose! h3
        rw [lowerBounds, Set.mem_setOf, not_forall]
        use l - ε
        rw [Classical.not_imp]
        constructor
        · exact h3.1
        rw [hl, le_sub_self_iff, not_le]
        exact hε
      contrapose! h1
      constructor
      · intro x hx
        rcases hx with ⟨n,hx⟩
        rw [←hx]
        apply h1
      intro x hx
      apply le_trans (by grind : l - ε ≤ l)
      unfold IsLUB IsLeast at hS_LUB
      have h3 := hS_LUB.2
      contrapose! h3
      rw [lowerBounds, Set.mem_setOf, not_forall]
      use x
      rw [Classical.not_imp]
      constructor
      · exact hx
      grind
    rcases hN with ⟨N,hN⟩
    use N
    intro n hn
    have hnN := increasing N n hn
    have hlεn : l - ε < a n := by grind
    have hnl : a n ≤ l := Set.mem_setOf.1 hS_LUB.1 (by use n)
    grind
