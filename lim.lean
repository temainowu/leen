import Mathlib

theorem decide_false' {α p} [Decidable p] :
  ∀ (h : ¬p) (t : p → α) (e : ¬p → α), (if h0 : p then t h0 else e h0) = e h := by grind

def limit {α β} [LT α] [Dist β] (f : α → β) (L : β) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : α, ∀ n : α, N < n → dist (f n) L < ε

theorem ratCast_inv_comm : ∀ q : ℚ, (↑q : ℝ)⁻¹ = ↑(q⁻¹) := by
  intro q
  rcases q with ⟨n,d,dnz,red⟩
  simp!

theorem ratCast_mul : ∀ x y : ℚ, (↑(x * y) : ℝ) = (↑x : ℝ) * (↑y : ℝ) := by simp

theorem natCast_ratCast : ∀ n : ℕ, (↑n : ℝ) = (↑(↑n : ℚ) : ℝ) := by simp

theorem natCast_intCast : ∀ n : ℕ, (↑n : ℝ) = (↑(↑n : ℤ) : ℝ) := by simp

theorem ratnat_mkrat : ∀ m : ℕ, (↑m : ℚ) = Rat.mk' ↑m 1 (by simp) (by simp) := by
  have h1 : ∀ m : ℕ, (↑m : ℚ) = Rat.ofInt ↑m := by
    intro m
    rw [Nat.cast, Rat.instNatCast, NatCast.natCast]
  intro m
  rw [h1, Rat.ofInt]

theorem lt_trans_le_right {a b c : ℝ} : a < b → b ≤ c → a < c := by grind

theorem lt_trans_le_left {a b c : ℝ} : a ≤ b → b < c → a < c := by grind

theorem le_mul : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ a * b := by
      intro a b ha hb
      sorry

theorem lt_mul : ∀ a b : ℝ, 0 < a → 0 < b → 0 < a * b := by
      intro a b ha hb
      sorry

theorem natCast_le : ∀ a : ℤ, 0 ≤ a → ↑a.toNat ≤ a := by simp

-- theorem floor_def : ∀ x : ℝ, 0 ≤ x → ∃ d : ℝ, 0 ≤ d ∧ d < 1 ∧ d ≤ x ∧ x - d = ↑⌊x⌋ := by sorry

theorem le_castZ {a b : ℤ} : a ≤ b ↔ (↑a : ℝ) ≤ ↑b := by simp

theorem le_castQ {a b : ℚ} : a ≤ b ↔ (↑a : ℝ) ≤ ↑b := by simp!

theorem lt_castNQ {a b : ℕ} : a < b ↔ (↑a : ℚ) < ↑b := by simp!

-- theorem right_adjoint : ∀ f : ℕ → ℕ, ∃ g : ℕ → ℕ, ∀ a b : ℕ, f a ≤ b ↔ a ≤ g b := by
--   intro f
--   sorry

theorem left_adjoint : ∀ f : ℕ → ℕ, (∀ a b : ℕ, a ≤ b → f a ≤ f b) →
  ∃ g : ℕ → ℕ, (∀ a b : ℕ, a ≤ f b ↔ g a ≤ b) := by
  intro f h
  use 

theorem inv_mul_cancelRat (a : ℚ) (ha : a.num ≠ 0) : a⁻¹ * a = 1 := by
    rcases a with ⟨n,d,nz,rd⟩
    induction n
    case zero => simp! at ha
    case succ n ih =>
      sorry


theorem halfsex :  ∃ f : ℕ → ℕ,
                  ∀ ε : ℚ, 0 < ε →
                  ∃ N : ℕ,
                  ∀ n : ℕ, N < n →
                    1/2 - ((↑n : ℚ).inv * f n) < ε
                := by
  rcases left_adjoint (fun x => 2 * x) (by simp) with ⟨g,hg⟩
  use g
  intro ε hε
  use g ⌊ε⌋.toNat
  intro n hn
  have hn' := le_of_lt hn
  rw [←hg] at hn'

  ∀r∈ℝ,0≤r → (⌊xr⌋∈ℕ) ∧ lim(x→∞)(⌊xr⌋/x)=y



theorem ratsex :  ∀ x : ℚ, 0 ≤ x → x < 1 →
                  ∃ f : ℕ → ℕ,
                  ∀ ε : ℚ, 0 < ε →
                  ∃ N : ℕ,
                  ∀ n : ℕ, N < n →
                    x - ((↑n : ℚ).inv * f n) < ε
                := by
  intro x hx0 hx1
  use (fun n => ⌊x * n⌋.toNat)
  intro ε hε
  use ⌈ε.inv⌉.toNat
  intro n hn
  have h : 0 ≤ (↑n : ℚ) := by simp
  revert h
  apply lt_of_mul_lt_mul_of_nonneg_left
  ring_nf
  have mul_inv : ∀ q : ℚ, q ≠ 0 → q * q.inv = 1 := by
    intro q hq
    cases q
    case div n d nz re =>
      rw [Rat.inv]
      simp!
      rw [decide_false' (by
        simp!
        ring_nf
        have h : 0 < (↑d:ℚ) := by
          cases d
          case zero => simp! at nz
          case succ d =>
            rw [(by rfl : (0:ℚ) = ↑(0:ℕ)), ←lt_castNQ]
            simp
        revert h
        apply le_of_mul_le_mul_of_pos_right
        simp!
        rw [mul_assoc, @inv_mul_cancel ℚ _ (↑d)]
        grind

      )]
  rw [mul_inv]
  simp!
  sorry



theorem realsex : ∀ x : ℝ, 0 ≤ x → x < 1 →
                  ∃ f : ℕ → ℕ,
                  ∀ ε : ℚ, 0 < ε →
                  ∃ N : ℕ,
                  ∀ n : ℕ, N < n →
                    x - ((f n) / n) < ε
                := by
  intro x hx0 hx1
  use (fun n => ⌊x * n⌋.toNat)
  intro ε hε
  use ⌈(ε⁻¹ * x - ↑⌊ε⁻¹ * x⌋.toNat)*ε⁻¹⌉.toNat
  intro n hn
  simp!
  have h : 0 ≤ (↑n : ℝ) := by simp
  revert h
  apply lt_of_mul_lt_mul_of_nonneg_left
  ring_nf
  nth_rewrite 5 [natCast_ratCast]
  rw [ratCast_inv_comm]
  nth_rewrite 2 [mul_comm]
  rw [←mul_assoc]
  nth_rewrite 2 [natCast_ratCast]
  have h : ∀ q : ℚ, q⁻¹ = q.inv := by
    intro q
    rw [Inv.inv, Rat.instInv]
  have inv_mul : ∀ q : ℚ, q ≠ 0 → q.inv * q = 1 := by grind
  rw [←ratCast_mul, h, inv_mul]
  simp!
  rw [Int.toNat_lt (by
    have h := Int.le_ceil ((ε⁻¹ * x - ↑⌊ε⁻¹ * x⌋.toNat) * ε⁻¹)
    apply le_castZ.2
    revert h
    apply le_trans
    simp!
    apply le_mul
    · simp!
      have h3 := Int.floor_le (ε⁻¹ * x)
      revert h3
      simp!
      apply le_trans
      rw [natCast_intCast]
      apply le_castZ.1
      apply natCast_le
      rw [Int.le_floor]
      simp!
      apply le_mul
      · simp!
        exact le_of_lt hε
      exact hx0
    simp!
    exact le_of_lt hε)] at hn
  apply le_of_lt at hn
  rw [Int.ceil_le] at hn
  contrapose! hn
  have h1 := le_of_lt hε
  rw [le_castQ, (by simp : (↑(0 : ℚ) : ℝ) = 0)] at h1
  revert h1
  apply lt_of_mul_lt_mul_of_nonneg_right
  simp!
  apply lt_trans_le_left hn
  rw [mul_assoc, ratCast_inv_comm, ←ratCast_mul, h ε, inv_mul ε (by grind)]
  simp!
  have h0 : ∀ x y a b : ℝ, b < a → x < y → x - a < y - b := by grind
  apply h0
  · simp!
    constructor
    · have h1 : ∀ a b : ℝ, a < b → ⌊a⌋ < ⌊b⌋ := by
        intro a b hab
        sorry
      apply h1
      apply mul_lt_mul
      · sorry
      · rfl
      · sorry
      sorry
    sorry
  · apply mul_lt_mul
    · sorry
    · rfl
    · sorry
    grind
  sorry
