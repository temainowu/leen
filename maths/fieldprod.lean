import Mathlib

-- Bool + is ∨
-- Bool * is ∧

theorem decide_true' {α p} [inst : Decidable p] : p → ∀ t e : α, (if p then t else e) = t := by
  intro h t e
  cases inst
  case isFalse => contradiction
  case isTrue => rfl

theorem decide_false' {α p} [inst : Decidable p] : ¬p → ∀ t e : α, (if p then t else e) = e := by
  intro h t e
  cases inst
  case isFalse => rfl
  case isTrue => contradiction

instance : Add (Fin 3) where
  add
    | ⟨0,_⟩, x => x
    | x, ⟨0,_⟩ => x
    | ⟨1,_⟩, ⟨1,_⟩ => 2
    | ⟨2,_⟩, ⟨1,_⟩ => 0
    | ⟨1,_⟩, ⟨2,_⟩ => 0
    | ⟨2,_⟩, ⟨2,_⟩ => 1
    | ⟨Nat.succ (Nat.succ (Nat.succ n)),hn⟩, _ => by contradiction
    | _, ⟨Nat.succ (Nat.succ (Nat.succ n)),hn⟩ => by contradiction

instance : Mul (Fin 3) where
  mul
    | ⟨0,_⟩, _ => 0
    | _, ⟨0,_⟩ => 0
    | ⟨1,_⟩, x => x
    | x, ⟨1,_⟩ => x
    | ⟨2,_⟩, ⟨2,_⟩ => 1
    | ⟨Nat.succ (Nat.succ (Nat.succ n)),hn⟩, _ => by contradiction
    | _, ⟨Nat.succ (Nat.succ (Nat.succ n)),hn⟩ => by contradiction

instance : Add (Fin 2) where
  add
    | ⟨0,_⟩, x => x
    | x, ⟨0,_⟩ => x
    | ⟨1,_⟩, ⟨1,_⟩ => 0
    | ⟨Nat.succ (Nat.succ n),hn⟩, _ => by contradiction
    | _, ⟨Nat.succ (Nat.succ n),hn⟩ => by contradiction

instance : Mul (Fin 2) where
  mul
    | ⟨0,_⟩, _ => 0
    | _, ⟨0,_⟩ => 0
    | ⟨1,_⟩, ⟨1,_⟩ => 1
    | ⟨Nat.succ (Nat.succ n), hn⟩, _ => by contradiction
    | _, ⟨Nat.succ (Nat.succ n),hn⟩ => by contradiction

@[simp]
instance : Div (Fin 2) where
  div
    | ⟨0,_⟩, _ => 0
    | _, ⟨0,_⟩ => 0
    | ⟨1,_⟩, ⟨1,_⟩ => 1
    | ⟨Nat.succ (Nat.succ n), hn⟩, _ => by contradiction
    | _, ⟨Nat.succ (Nat.succ n),hn⟩ => by contradiction

@[simp]
lemma zero_div_2 {x : Fin 2} : 0 / x = 0 := by rfl

lemma augh {a b : ℕ} : (↑a + 1) % 2 = (↑b : ℤ) → (a + 1) % 2 = b := by
  intro h
  rw [←@Nat.cast_inj ℤ]
  simp!
  exact h

instance : Field (Fin 2) where
  div_eq_mul_inv
    | ⟨a,ha⟩, ⟨b,hb⟩ => by
      cases a
      case zero => simp
      case succ a =>
        cases a
        · simp!
          cases b
          case zero => rfl
          case succ b =>
            cases b
            · rfl
            contradiction
        contradiction
  inv := id
  mul_inv_cancel := by
    intro ⟨a,ha⟩
    cases a
    case _ => simp
    case _ a =>
      simp
      cases a
      case zero => simp
      case succ a =>
        rw [Nat.succ_lt_succ_iff,
            Nat.succ_lt_succ_iff] at ha
        simp at ha
  inv_zero := by simp
  nnqsmul
    | ⟨⟨_,_,_,_⟩,_⟩, 0 => 0
    | ⟨⟨n,d,_,_⟩,_⟩, 1 => {
        val := (n % 2).natAbs / (d % 2),
        isLt := by
          cases @or_not (Nat.instDvd.1 2 d)
          case inl h =>
            rw [Nat.instDvd, Dvd.dvd] at h
            simp! at h
            rcases h with ⟨c,hc⟩
            rw [hc]
            simp
          case inr h =>
            simp! at h
            rw [h]
            simp!
            rw [Int.natAbs_emod]
            · cases n
              case ofNat h0 n h1 h2 =>
                simp!
                apply Nat.mod_lt
                simp
              case negSucc h0 n h1 h2 =>
                cases @or_not (Int.instDvd.1 2 (Int.negSucc n))
                case inl h =>
                  rw [decide_true']
                  · simp!
                    apply Nat.mod_lt
                    simp
                  apply Or.inr
                  exact h
                case inr h =>
                  rw [decide_false']
                  · simp!
                    simp! at h
                    apply augh at h
                    rw [h]
                    simp
                  simp!
                  simp! at h
                  exact h
            simp
      }

  qsmul
    | _, 0 => 0
    | ⟨n,d,_,_⟩, 1 => {
        val := (n % 2).natAbs / (d % 2),
        isLt := by
          cases @or_not (Nat.instDvd.1 2 d)
          case inl h =>
            rw [Nat.instDvd, Dvd.dvd] at h
            simp! at h
            rcases h with ⟨c,hc⟩
            rw [hc]
            simp
          case inr h =>
            simp! at h
            rw [h]
            simp!
            rw [Int.natAbs_emod]
            · cases n
              case ofNat h1 n h2 =>
                simp!
                apply Nat.mod_lt
                simp
              case negSucc h1 n h2 =>
                cases @or_not (Int.instDvd.1 2 (Int.negSucc n))
                case inl h =>
                  rw [decide_true']
                  · simp!
                    apply Nat.mod_lt
                    simp
                  apply Or.inr
                  exact h
                case inr h =>
                  rw [decide_false']
                  · simp!
                    simp! at h
                    apply augh at h
                    rw [h]
                    simp
                  simp!
                  simp! at h
                  exact h
            simp
      }
  nnqsmul_def := by
    intro ⟨⟨n,d,h0,h1⟩,h⟩ ⟨a,ah⟩
    unfold NNRat.cast
           NNRatCast.nnratCast
           NNRat.castRec
           Nat.cast
           NatCast.natCast
           Nat.unaryCast
    simp!
    cases a
    case zero => simp
    case succ a =>
      cases a
      case succ a => contradiction
      case zero =>
        simp!
        cases @or_not (Nat.instDvd.1 2 d)
        case inl hd =>
          rw [@Nat.mod_eq_zero_of_dvd 2 d]
          rw [Nat.instDvd, Dvd.dvd] at h
          simp! at h
          rcases h with ⟨c,hc⟩
          rw [hc]
          simp
        case inr hd =>
        cases n
        case negSucc n =>
          unfold Rat.instLE Rat.blt at h
          simp at h
        case ofNat n =>
          cases n
          case zero =>
            simp!
          case succ n =>
            cases n
            case zero =>
              simp!
              cases d
              case zero => contradiction
              case succ d =>
                cases d
                case zero =>
                  simp!
                case succ d =>
                  simp! at h
            simp!

        rw [((by
          induction n
          case zero => simp!
          case succ n ih =>
            simp
            -- have h {a b : ℕ} {h} : a = b → (↑a + 1 + 1).natAbs.unaryCast = (⟨a + 1 + 1, h⟩ : Fin 2) := by rfl
            rw [Int.natAbs_add_of_nonneg,
                Int.natAbs_add_of_nonneg,
                Int.natAbs_natCast]
            simp!
            congr
            rw [@Nat.cast_add _ _ _ 1,
                @Nat.unaryCast (Fin 2) _ _ _]
            simp!

            simp
         ) : (Int.ofNat (n + 1)).natAbs.unaryCast = ⟨Nat.succ n,_⟩)]
        rcases (Int.ofNat (n + 1)).natAbs.unaryCast with ⟨Nat.succ n',hn⟩
        rcases d.unaryCast with ⟨d',hd⟩
        cases n'
        case zero =>
          cases d'
          case zero => simp






instance : Field (Fin 3)

def Q2 : ℚ → Bool
  | ⟨n,d,h0,h1⟩ => (n % 2 == 1)

lemma Q2_homo : ∀ x y,
    (Q2 (x + y) = (Q2 x || Q2 y))
  ∧ (Q2 (x * y) = (Q2 x && Q2 y)) := by
  intro x y
  rcases x with ⟨xn,xd,hx,hxr⟩
  rcases y with ⟨yn,yd,hy,hyr⟩
  constructor
  · repeat rw [Q2.eq_def]
    sorry
  sorry

theorem dum {α} [inst : Field α] : ¬∃ (f : α → Bool) (g : α → Fin 3),
  ∀ x y : α,
    f (x + y) = (f x || f y)
  ∧ f (x * y) = (f x && f y)
  ∧ g (x + y) = (g x + g y)
  ∧ g (x * y) = (g x * g y) := by
    simp!
    intro f g
    use 0
    use 1
    simp
    intro h0 h1
    rw [h1]
