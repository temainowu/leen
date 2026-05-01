import Mathlib

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

theorem decite_true {α p} [inst : Decidable p] :
  ∀ (h : p) (t : p → α) (e : ¬p → α), (if h0 : p then t h0 else e h0) = t h := by
  intro h t e
  cases inst
  case isFalse => contradiction
  case isTrue => rfl

theorem decite_false {α p} [inst : Decidable p] :
  ∀ (h : ¬p) (t : p → α) (e : ¬p → α), (if h0 : p then t h0 else e h0) = e h := by
  intro h t e
  cases inst
  case isFalse => rfl
  case isTrue => contradiction

lemma decite {α p} [inst : Decidable p] (f : α → Prop) :
  ∀ (t : p → α) (e : ¬p → α),
    (∀ (x : p), f (t x)) → (∀ (y : ¬p), f (e y)) → f (if h0 : p then t h0 else e h0) := by
  intro t e ht he
  cases inst
  case isFalse h =>
    specialize he h
    rw [dite]
    exact he
  case isTrue h =>
    specialize ht h
    rw [dite]
    exact ht

@[simp]
def zipWith0 {α β} [Zero α] (f : α → α → β) (a : List α) (b : List α) : List β :=
  a.zipWithAll (fun x y => f (x.getD 0) (y.getD 0)) b

@[simp]
lemma zipWith0_cons_cons [Zero α] :
  ∀ (f : α → α → β) (x y : α) xs ys, zipWith0 f (x :: xs) (y :: ys) =
  f x y :: zipWith0 f xs ys := by simp

@[simp]
theorem zipWith0_nil_eq_map_left {α β} [Zero α] : ∀ (f : α → α → β) (ys : List α),
    zipWith0 f [] ys = ys.map (f 0) := by simp!

@[simp]
theorem zipWith0_nil_eq_map_right {α β} [Zero α] : ∀ (f : α → α → β) (xs : List α),
    zipWith0 f xs [] = xs.map (fun x => f x 0) := by simp!

theorem length_zipWith0 {α β} [Zero α] : ∀ (f : α → α → β) (xs ys : List α),
    (zipWith0 f xs ys).length = max xs.length ys.length := by
  intro f xs ys
  simp!
  induction xs generalizing ys
  case nil => simp!
  case cons x xs ih =>
    cases ys
    case nil => simp!
    case cons y ys =>
      simp!
      specialize ih ys
      exact ih

lemma getLast?_zipWith0 [Zero α] : ∀ (f : α → α → β) x y xs ys,
  (zipWith0 f (x :: xs) (y :: ys)).getLast? = some (f (xs.getLast?.getD x) 0) ∨
  (zipWith0 f (x :: xs) (y :: ys)).getLast? = some (f 0 (ys.getLast?.getD y)) ∨
  (zipWith0 f (x :: xs) (y :: ys)).getLast? = some (f (xs.getLast?.getD x) (ys.getLast?.getD y))
  := by
    intro f x y xs ys
    simp
    induction xs generalizing x y ys
    case nil =>
      apply Or.inr
      cases ys
      case nil =>
        apply Or.inr
        rfl
      case cons y' ys =>
        apply Or.inl
        induction ys generalizing y'
        case nil => rfl
        case cons y'' ys ih =>
          simp!
          simp! at ih
          rw [ih y'']
    case cons x' xs ih =>
      cases ys
      case nil =>
        specialize ih x' 0 []
        rw [List.zipWithAll_nil, List.getLast?_nil] at ih
        simp only [Option.getD_some, Option.getD_none] at ih
        simp
        cases ih
        case inl ih =>
          rw [ih]
          apply Or.inl
          rw [List.getLast?_cons]
          rfl
        case inr ih =>
          cases ih
          case inl ih =>
            rw [ih]
            induction xs generalizing x'
            case nil =>
              apply Or.inl
              rw [←ih]
              rfl
            case cons x'' xs hx =>
              specialize hx x''
              apply hx
              exact ih
          case inr ih =>
            rw [ih]
            rw [List.getLast?_cons]
            simp
      case cons y' ys =>
        specialize ih x' y' ys
        cases ih
        case inl ih =>
          rw [List.zipWithAll_cons_cons, List.getLast?_cons_cons]
          repeat rw [Option.getD_some]
          rw [ih]
          rw [List.getLast?_cons]
          simp
        case inr ih =>
          cases ih
          case inl ih =>
            rw [List.zipWithAll_cons_cons, List.getLast?_cons_cons]
            repeat rw [Option.getD_some]
            rw [ih]
            apply Or.inr
            apply Or.inl
            rw [List.getLast?_cons]
            rfl
          case inr ih =>
            rw [List.zipWithAll_cons_cons, List.getLast?_cons_cons]
            repeat rw [Option.getD_some]
            rw [ih]
            apply Or.inr
            apply Or.inr
            rw [List.getLast?_cons, List.getLast?_cons]
            rfl

lemma zipWith0_comm {α β} [Zero α] {f : α → α → β} {a : List α} {b : List α}
  (h : ∀ x y, f x y = f y x) : zipWith0 f a b = zipWith0 f b a := by
  induction a generalizing b
  case nil =>
    simp!
    intro a ha
    apply h
  case cons a as ih =>
    cases b
    case nil =>
      simp!
      constructor
      · apply h
      intro a ha
      apply h
    case cons b bs =>
      rw [zipWith0_cons_cons, zipWith0_cons_cons]
      congr 1
      · apply h
      apply ih

lemma intsub_eq_nat_of_lt : ∀ a b : ℤ, a < b → ∃ c, b - a = Int.ofNat (Nat.succ c) := by
    intro a b h
    use (b - a - 1).toNat
    simp!
    rw [Nat.cast_sub]
    · simp!
      exact Int.le_of_lt h
    unfold Int.toNat
    have h : ∃ c, b - a = c := by use b - a
    rcases h with ⟨c,hc⟩
    rw [hc]
    cases c
    case ofNat c =>
      dsimp
      cases c
      · rw [←Int.add_left_inj a] at hc
        simp! at hc
        rw [hc] at h
        simp at h
      simp
    case negSucc c =>
      rw [←Int.add_left_inj a] at hc
      simp! at hc
      rw [hc] at h
      simp at h

lemma getLast_of_getElem {α : Type} {x : α} {xs : List α} :
  ∀ h, (x :: xs).getLast h = (x :: xs)[xs.length]'(by simp) := by
  intro h
  induction xs generalizing x
  case nil => simp
  case cons x' xs ih =>
    simp!
    apply ih

@[reducible]
def fluxh (r : ℤ) (v : List ℚ) : Prop := (v = [] → r = 0) ∧ v.head? ≠ some 0 ∧ v.getLast? ≠ some 0

--

structure RankList where
  r : ℤ
  v : List ℚ

namespace RankList

@[simp]
def remLeadZero : List ℚ → List ℚ
  | [] => []
  | x :: xs => if x = 0 then remLeadZero xs else x :: xs

lemma head?_rlz : ∀ xs, (remLeadZero xs).head? ≠ some 0 := by
  intro xs
  induction xs
  case nil => simp
  case cons x xs ih =>
    cases @or_not (x = 0)
    case inl h =>
      rw [h]
      rw [remLeadZero]
      simp!
      exact ih
    case inr h =>
      simp!
      rw [decide_false']
      · simp!
        exact h
      exact h

lemma getLast?_rlz : ∀ xs, (remLeadZero xs).getLast? = xs.getLast? ∨
  (remLeadZero xs).getLast? = none := by
    intro xs
    induction xs
    case nil => simp
    case cons x xs ih =>
      have h : x = 0 ∨ x ≠ 0 := or_not
      cases h
      case inl h =>
        simp!
        rw [decide_true']
        · simp! at ih
          cases ih
          case inl ih =>
            rw [ih]
            cases xs
            · simp
            simp!
          case inr ih =>
            rw [ih]
            simp
        exact h
      case inr h =>
        simp!
        rw [decide_false']
        · simp!
        exact h

lemma length_rlz : ∀ xs, (remLeadZero xs).length ≤ xs.length := by
  intro xs
  induction xs
  case nil => simp
  case cons x xs ih =>
    have h : x = 0 ∨ x ≠ 0 := or_not
    cases h
    case inl h =>
      rw [h]
      apply le_trans ih
      simp
    case inr h =>
      simp!
      rw [decide_false']
      · simp
      exact h

lemma length_rlz_of_head_eq_0 : ∀ x xs, x = 0 → (remLeadZero (x :: xs)).length < (x :: xs).length := by
  intro x xs h
  rw [h]
  induction xs
  case nil => simp
  case cons x xs ih =>
    have h : x = 0 ∨ x ≠ 0 := or_not
    cases h
    case inl h =>
      rw [h]
      apply lt_trans ih
      simp
    case inr h =>
      simp!
      rw [decide_false']
      · simp
      exact h

lemma rlz_map :
  ∀ xs f, (∀ x, f x = 0 ↔ x = 0) → remLeadZero (List.map f xs) = List.map f (remLeadZero xs) := by
  intro xs f hf
  induction xs
  case nil => simp
  case cons x xs ih =>
    simp!
    cases @or_not (f x = 0)
    case inl h =>
      rw [decide_true' h, decide_true']
      · exact ih
      rw [←hf]
      exact h
    case inr h =>
      rw [decide_false' h, decide_false']
      · simp
      rw [←hf]
      exact h

@[simp]
def rlzCount : List ℚ → ℕ
  | [] => 0
  | x :: xs => if x = 0 then rlzCount xs + 1 else 0

lemma rlzCount_nil : ∀ xs, remLeadZero xs = [] → rlzCount xs = xs.length := by
  intro xs
  induction xs
  case nil => simp
  case cons x xs ih =>
    have h : x = 0 ∨ x ≠ 0 := or_not
    simp!
    cases h
    case inl h =>
      rw [decide_true', decide_true']
      · simp!
        exact ih
      · exact h
      exact h
    case inr h =>
      rw [decide_false', decide_false']
      · simp
      · exact h
      exact h

lemma rlzCount_cons : ∀ xs, remLeadZero xs ≠ [] → rlzCount xs ≤ xs.length := by
  intro xs
  induction xs
  case nil => simp
  case cons x xs ih =>
    have h : x = 0 ∨ x ≠ 0 := or_not
    simp!
    cases h
    case inl h =>
      rw [decide_true', decide_true']
      · simp!
        exact ih
      · exact h
      exact h
    case inr h =>
      rw [decide_false', decide_false']
      · simp
      · exact h
      exact h

lemma rlzCount_map :
  ∀ (xs : List ℚ) f, (∀ x, f x = 0 ↔ x = 0) → rlzCount (List.map f xs) = rlzCount xs := by
  intro xs f h
  induction xs
  case nil => simp
  case cons x xs ih =>
    simp!
    cases @or_not (f x = 0)
    case inl hx =>
      rw [decide_true' hx, decide_true' ((h x).1 hx)]
      congr
    case inr hx =>
      rw [decide_false' hx, decide_false']
      rw [←h]
      exact hx

@[simp]
def remTrailZero : List ℚ → List ℚ
  | [] => []
  | xs => if xs.getLast? = some 0 then remTrailZero xs.dropLast else xs
termination_by xs => xs.length
decreasing_by
  cases xs
  · simp at *
  simp

lemma back_induction :
  ∀ (p : List α → Prop) (nil : p []) (cons : ∀ x xs, p xs → p (xs ++ [x])), ∀ xs, p xs := by
  intro p nil cons xs
  have hy : ∃ ys : List α, xs = ys.reverse := by use xs.reverse ; simp
  rcases hy with ⟨ys,hy⟩
  rw [hy]
  induction ys generalizing xs
  case nil => simp! ; exact nil
  case cons y ys ih =>
    simp!
    apply cons
    specialize ih ys.reverse
    apply ih
    rfl

lemma length_rtz : ∀ xs, (remTrailZero xs).length ≤ xs.length := by
  apply back_induction
  case nil => simp
  case cons =>
    intro x xs ih
    have h : x = 0 ∨ x ≠ 0 := or_not
    cases h
    case inl h =>
      simp!
      rw [decide_true']
      · apply le_trans ih
        simp
      exact h
    case inr h =>
      simp!
      rw [decide_false']
      · simp
      exact h

lemma head?_rtz : ∀ xs, (remTrailZero xs).head? = xs.head? ∨
  (remTrailZero xs).head? = none := by
  apply back_induction
  case nil => simp
  case cons =>
    intro x xs ih
    simp!
    have h : x = 0 ∨ x ≠ 0 := or_not
    cases h
    case inl h =>
      rw [decide_true']
      · cases ih
        case inl ih =>
          rw [ih]
          cases xs
          · simp!
          simp!
        case inr ih =>
          cases xs
          case nil => simp!
          case cons x' xs =>
            simp! at ih
            apply Or.inr
            rw [←ih]
            simp!
      exact h
    case inr h =>
      rw [decide_false']
      · simp
      exact h

lemma getLast?_rtz : ∀ xs, (remTrailZero xs).getLast? ≠ some 0 := by
  apply back_induction
  case nil => simp
  case cons =>
    intro x xs ih
    simp!
    have h : x = 0 ∨ x ≠ 0 := or_not
    cases h
    case inl h =>
      rw [decide_true']
      · exact ih
      exact h
    case inr h =>
      rw [decide_false']
      · simp!
        exact h
      exact h

lemma getElem_append_of_lt :
  ∀ (xs ys : List ℚ) (i : ℕ) (hi : i < xs.length),
    (xs ++ ys)[i]'(by apply lt_of_lt_of_le hi ; simp) = xs[i] := by
  intro xs ys i hi
  induction xs generalizing i
  case nil => simp at hi
  case cons x xs ih =>
    cases i
    case zero => simp
    case succ i =>
      simp!
      apply ih

lemma mrgph : ∀ x xs i hi (p : ℚ → Prop),
  (∀ hi' : i < xs.length, p xs[i]) → (i = xs.length → p x) → p ((xs ++ [x])[i]'hi) := by
  intro x xs i hi p c1 c2
  cases @or_not (i = xs.length)
  case inl h =>
    induction xs generalizing i
    case nil =>
      apply c2 at h
      simp!
      exact h
    case cons x' xs ih =>
      simp! at h ih
      cases i
      case zero => simp at h
      case succ i =>
        simp!
        cases i
        · cases xs
          · simp!
            simp! at c2
            exact c2
          simp at h
        case succ i =>
          specialize ih (i + 1)
          apply ih
          · rw [←h] ; simp
          · intro hi'
            simp! at h
            rw [h] at hi'
            simp at hi'
          · intro h0
            apply c2
            simp!
            exact h0
          simp! at h
          exact h
  case inr h =>
    have h0 : i < xs.length := by
      apply lt_of_le_of_ne
      · rw [List.length_append] at hi
        simp! at hi
        apply Nat.le_of_lt_succ
        exact hi
      exact h
    rw [getElem_append_of_lt]
    · apply c1
    exact h0

lemma rlz_ne_nil (xs : List ℚ) : xs.getLast? ≠ some 0 → (remLeadZero xs ≠ [] ↔ xs ≠ []) := by
  intro h0
  rw [remLeadZero.eq_def]
  cases xs
  case nil => simp
  case cons x xs =>
    simp!
    apply decite (fun a ↦ a ≠ [])
    · intro h1
      cases xs
      case _ =>
        rw [h1] at h0
        simp at h0
      case _ x' xs =>
        rw [RankList.rlz_ne_nil]
        · simp
        rw [List.getLast?_cons_cons] at h0
        exact h0
    intro h1
    simp

lemma rlz_eq_nil : ∀ xs : List ℚ, remLeadZero xs = [] → ∀ (i : ℕ) hi, xs[i]'hi = 0 := by
  intro xs h i hi
  induction xs generalizing i
  case nil => simp at hi
  case cons x xs ih =>
    cases i
    case zero =>
      simp! at h
      cases @or_not (x = 0)
      case inl hx =>
        rw [hx]
        rfl
      case inr hx =>
        rw [decide_false' hx] at h
        contradiction
    case succ i =>
      simp!
      apply ih
      cases @or_not (x = 0)
      case inl hx =>
        rw [hx] at h
        simp! at h
        exact h
      case inr hx =>
        simp! at h
        rw [decide_false' hx] at h
        contradiction

lemma add_dec_aux {xs : List ℚ} : xs ≠ [] → (remLeadZero xs.tail).length < xs.length := by
  intro hx
  have h := length_rlz_of_head_eq_0 0 xs.tail
  cases xs
  · simp at hx
  simp! at h
  exact h

def add' : RankList → RankList → RankList
  | ⟨xr, xs⟩, ⟨yr, ys⟩ =>
    if x0 : xs = []
      then ⟨yr,ys⟩
      else
    if y0 : ys = []
      then ⟨xr,xs⟩
      else
    if rlt : xr < yr
      then ⟨yr, ys.head y0 :: (add' ⟨xr, xs⟩ ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩).v⟩
      else
    if req : yr < xr
      then ⟨xr, xs.head x0 :: (add' ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩ ⟨yr, ys⟩).v⟩
      else
    if hhead : xs.head x0 + ys.head y0 = 0
      then if xnil : xs.tail ≠ []
           then if ynil : ys.tail ≠ []
                then add' ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩
                          ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩
                else ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩
           else if ynil : ys.tail ≠ []
                then ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩
                else ⟨0, []⟩
      else ⟨xr,
            (xs.head x0 + ys.head y0)
            :: (add' ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩
                     ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩).v⟩
termination_by x y => x.v.length + y.v.length
decreasing_by
  · apply Nat.add_lt_add_of_le_of_lt
    · rfl
    apply add_dec_aux y0
  · apply Nat.add_lt_add_of_lt_of_le
    · apply add_dec_aux x0
    rfl
  · apply Nat.add_lt_add_of_lt_of_le
    · apply add_dec_aux x0
    apply le_of_lt
    apply add_dec_aux y0
  apply Nat.add_lt_add_of_lt_of_le
  · apply add_dec_aux x0
  apply le_of_lt
  apply add_dec_aux y0


def add : RankList → RankList → RankList
  | ⟨xr, xs⟩, ⟨yr, ys⟩ =>
    if x0 : xs = []
      then ⟨yr,ys⟩
      else
    if y0 : ys = []
      then ⟨xr,xs⟩
      else
    if hhead : xs.head x0 + ys.head y0 = 0
      then if xnil : xs.tail ≠ []
           then if ynil : ys.tail ≠ []
                then add ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩
                         ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩
                else ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩
           else if ynil : ys.tail ≠ []
                then ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩
                else ⟨0, []⟩
      else
    if htail : xs.getLast x0 + ys.getLast y0 = 0
      then if xnil : RankList.remTrailZero xs.dropLast ≠ []
           then if ynil : RankList.remTrailZero ys.dropLast ≠ []
                then add ⟨xr, remTrailZero xs.dropLast⟩
                         ⟨yr, remTrailZero ys.dropLast⟩
                else ⟨xr, remTrailZero xs.dropLast⟩
           else if ynil : RankList.remTrailZero ys.dropLast ≠ []
                then ⟨yr, remTrailZero ys.dropLast⟩
                else ⟨0,[]⟩
      else
    if rlt : xr < yr
      then ⟨yr, zipWith0 (· + ·) (List.replicate (yr-xr).toNat 0 ++ xs) ys⟩
      else
    if req : xr = yr
      then ⟨xr, zipWith0 (· + ·) xs ys⟩
      else ⟨xr, zipWith0 (· + ·) xs (List.replicate (xr-yr).toNat 0 ++ ys)⟩
termination_by x y => y.v.length + x.v.length
decreasing_by
  · apply Nat.add_lt_add_of_lt_of_le
    · apply lt_of_le_of_lt (length_rlz _)
      cases ys
      · simp at y0
      simp
    apply le_trans (length_rlz _)
    simp
  apply Nat.add_lt_add_of_le_of_lt
  · apply le_trans (length_rtz _)
    simp
  apply lt_of_le_of_lt (length_rtz _)
  cases xs
  · simp at x0
  simp

lemma add_comm' (xr yr : ℤ) (xs ys : List ℚ) (xh : fluxh xr xs) (yh : fluxh yr ys) :
  add ⟨xr,xs⟩ ⟨yr,ys⟩ = add ⟨yr,ys⟩ ⟨xr,xs⟩ := by
  rcases xh with ⟨xh0,xh1,xh2⟩
  rcases yh with ⟨yh0,yh1,yh2⟩
  rw [add]
  cases xs
  case nil =>
    simp!
    rw [RankList.add]
    simp!
    simp! at xh0 yh0
    intro h
    have h0 := yh0 h
    rw [xh0, h0, h]
    simp
  case cons x xs =>
    cases ys
    case nil =>
      simp!
      rw [RankList.add]
      simp
    case cons y ys =>
      rw [decite_false, decite_false]
      · cases @or_not (x + y = 0)
        case inl hhead =>
          rw [decite_true]
          · cases @or_not (xs = [])
            case inl xnil =>
              rw [decite_false]
              · cases @or_not (ys = [])
                case inl ynil =>
                  rw [decite_false]
                  · rw [RankList.add,
                        decite_false,
                        decite_false,
                        decite_true,
                        decite_false,
                        decite_false]
                    · simp!
                      exact xnil
                    · simp!
                      exact ynil
                    · simp!
                      rw [add_comm]
                      exact hhead
                    · simp
                    simp
                  simp!
                  exact ynil
                case inr ynil =>
                  rw [decite_true]
                  · rw [RankList.add,
                        decite_false,
                        decite_false,
                        decite_true,
                        decite_true,
                        decite_false]
                    · simp!
                      exact xnil
                    · simp!
                      exact ynil
                    · simp!
                      rw [add_comm]
                      exact hhead
                    · simp
                    simp
                  simp!
                  exact ynil
              simp!
              exact xnil
            case inr xnil =>
              rw [decite_true]
              · cases @or_not (ys = [])
                case inl ynil =>
                  rw [decite_false]
                  · rw [RankList.add,
                        decite_false,
                        decite_false,
                        decite_true,
                        decite_false,
                        decite_true]
                    · simp!
                      exact xnil
                    · simp!
                      exact ynil
                    · simp!
                      rw [add_comm]
                      exact hhead
                    · simp!
                    simp!
                  simp!
                  exact ynil
                case inr ynil =>
                  rw [decite_true]
                  · nth_rewrite 2 [RankList.add]
                    rw [decite_false,
                        decite_false,
                        decite_true,
                        decite_true,
                        decite_true]
                    · simp!
                      apply add_comm'
                      · unfold fluxh
                        simp!
                        constructor
                        · intro h
                          apply rlz_eq_nil at h
                          cases xs
                          case nil => simp! at xnil
                          case cons x' xs =>
                            specialize h xs.length (by simp)
                            contrapose! xh2
                            simp!
                            rw [←h]
                            apply getLast_of_getElem
                        constructor
                        · apply head?_rlz
                        cases getLast?_rlz xs
                        case _ h =>
                          rw [h]
                          simp at xh2
                          cases xs
                          · simp!
                          rw [List.getLast?_cons_cons] at xh2
                          exact xh2
                        case _ h =>
                          rw [h]
                          simp
                      unfold fluxh
                      simp!
                      constructor
                      · intro h
                        apply rlz_eq_nil at h
                        cases ys
                        case nil => simp! at ynil
                        case cons y' ys =>
                          specialize h ys.length (by simp)
                          contrapose! yh2
                          simp!
                          rw [←h]
                          apply getLast_of_getElem
                      constructor
                      · apply head?_rlz
                      cases getLast?_rlz ys
                      case _ h =>
                        rw [h]
                        simp at yh2
                        cases ys
                        · simp!
                        rw [List.getLast?_cons_cons] at yh2
                        exact yh2
                      case _ h =>
                        rw [h]
                        simp
                    · simp!
                      exact xnil
                    · simp!
                      exact ynil
                    · simp!
                      rw [add_comm]
                      exact hhead
                    · simp
                    simp
                  simp!
                  exact ynil
              simp!
              exact xnil
          simp!
          exact hhead
        case inr hhead =>
          rw [decite_false]
          · cases @or_not ((x :: xs).getLast _ + (y :: ys).getLast _ = 0)
            case inl htail =>
              rw [decite_true htail]
              cases @or_not (remTrailZero (x :: xs).dropLast = [])
              case inl xnil =>
                rw [decite_false]
                · cases @or_not (remTrailZero (y :: ys).dropLast = [])
                  case inl ynil =>
                    rw [decite_false]
                    · rw [RankList.add,
                          decite_false,
                          decite_false,
                          decite_false,
                          decite_true,
                          decite_false,
                          decite_false]
                      · simp!
                        exact xnil
                      · simp!
                        exact ynil
                      · rw [add_comm]
                        exact htail
                      simp!
                      rw [add_comm]
                      exact hhead
                    simp!
                    exact ynil
                  case inr ynil =>
                    rw [decite_true ynil,
                        RankList.add,
                        decite_false,
                        decite_false,
                        decite_false,
                        decite_true,
                        decite_true ynil,
                        decite_false]
                    · simp!
                      exact xnil
                    · rw [add_comm]
                      exact htail
                    rw [add_comm]
                    simp!
                    exact hhead
                simp!
                exact xnil
              case inr xnil =>
                rw [decite_true xnil]
                cases @or_not (remTrailZero (y :: ys).dropLast = [])
                case inl ynil =>
                  rw [decite_false]
                  · rw [RankList.add,
                        decite_false,
                        decite_false,
                        decite_false,
                        decite_true,
                        decite_false,
                        decite_true]
                    · simp!
                      exact xnil
                    · simp!
                      exact ynil
                    · rw [add_comm]
                      exact htail
                    simp!
                    rw [add_comm]
                    exact hhead
                  simp!
                  exact ynil
                case inr ynil =>
                  rw [decite_true ynil,]
                  nth_rewrite 2 [RankList.add]
                  rw [decite_false,
                      decite_false,
                      decite_false,
                      decite_true,
                      decite_true ynil,
                      decite_true xnil]
                  · apply add_comm'
                    · unfold fluxh
                      simp!
                      constructor
                      · intro h
                        contradiction
                      constructor
                      · cases head?_rtz (x :: xs).dropLast
                        case inl h =>
                          rw [h]
                          cases xs
                          · simp!
                          simp!
                          simp! at xh1
                          exact xh1
                        case inr h =>
                          rw [h]
                          simp
                      apply getLast?_rtz
                    unfold fluxh
                    simp!
                    constructor
                    · intro h
                      contradiction
                    constructor
                    · cases head?_rtz (y :: ys).dropLast
                      case inl h =>
                        rw [h]
                        cases ys
                        · simp!
                        simp!
                        simp! at yh1
                        exact yh1
                      case inr h =>
                        rw [h]
                        simp
                    apply getLast?_rtz
                  · rw [add_comm]
                    exact htail
                  rw [add_comm]
                  simp!
                  exact hhead
            case inr htail =>
              rw [decite_false htail]
              cases @or_not (xr < yr)
              case inl rlt =>
                rw [decite_true rlt,
                    RankList.add,
                    decite_false,
                    decite_false,
                    decite_false,
                    decite_false,
                    decite_false,
                    decite_false]
                · congr 1
                  apply zipWith0_comm add_comm
                · apply Int.ne_of_gt rlt
                · simp!
                  apply le_of_lt rlt
                · rw [add_comm]
                  exact htail
                simp!
                rw [add_comm]
                exact hhead
              case inr rlt =>
                rw [decite_false rlt]
                cases @or_not (xr = yr)
                case inl req =>
                  rw [decite_true req,
                      RankList.add,
                      decite_false,
                      decite_false,
                      decite_false,
                      decite_false,
                      decite_false,
                      decite_true (symm req)]
                  · congr 1
                    apply zipWith0_comm add_comm
                  · rw [req]
                    simp
                  · rw [add_comm]
                    exact htail
                  simp!
                  rw [add_comm]
                  exact hhead
                case inr req =>
                  rw [decite_false req,
                      RankList.add,
                      decite_false,
                      decite_false,
                      decite_false,
                      decite_false,
                      decite_true]
                  · congr 1
                    apply zipWith0_comm add_comm
                  · apply lt_of_le_of_ne
                    · simp! at rlt
                      exact rlt
                    contrapose! req
                    rw [req]
                  · rw [add_comm]
                    exact htail
                  simp!
                  rw [add_comm]
                  exact hhead
          simp!
          exact hhead
      · simp!
      simp!
termination_by xs.length + ys.length
decreasing_by
  · case _ _ _ _ _ _ _ _ _ _ _ _ _ _ xdef _ _ ydef _ _ _ _ _ _ =>
    unfold fluxh at *
    rw [xdef, ydef]
    apply Nat.add_lt_add_of_lt_of_le
    · apply lt_of_le_of_lt (RankList.length_rlz _)
      simp
    apply le_trans (RankList.length_rlz _)
    simp
  case _ _ _ _ _ _ _ _ _ _ _ _ _ _ xdef _ _ ydef _ _ _ _ _ _ _ _ =>
  rw [xdef, ydef]
  apply Nat.add_lt_add_of_le_of_lt
  · apply le_trans (RankList.length_rtz _)
    simp
  apply lt_of_le_of_lt (RankList.length_rtz _)
  simp

/-
def add_fold (xs : List (List ℚ))
    (h : ∃ n : ℕ, ∀ (i : ℕ) (hxs : i < xs.length), (xs[i]'hxs).length = n) : List ℚ :=
  match xs with
    | [] => []
    | xs :: [] => xs
    | [] :: xss => add_fold xss (by
      rcases h with ⟨n,h⟩
      use n
      intro i hxs
      specialize h (i + 1) (by
        simp!
        exact hxs)
      simp! at h
      exact h)
    | (x :: xs) :: (xs' :: xss) => x ::
      add_fold (zipWith0 (· + ·) xs xs' :: xss) (by
      rcases h with ⟨n,h⟩
      use n
      intro i hxs
      have h' := h (i+1) (by
        simp!
        simp! at hxs
        exact hxs)
      cases i
      case zero =>
        simp! at h'
        rw [List.getElem_cons_zero, length_zipWith0, h']
        specialize h 0 (by simp!)
        simp! at h
        cases n
        case zero => simp! at h
        case succ n =>
          rw [Nat.add_right_cancel h]
          simp!
      case succ i =>
        simp!
        simp! at h'
        exact h'
    )
termination_by xs.length

@[simp]
def cart : List ℚ → List ℚ → List (List (ℚ×ℚ))
  | [], _ => []
  | _, [] => []
  | x :: xs, ys => ((fun a => (x,a)) <$> ys) :: cart xs ys

lemma length_getElem_cart : ∀ xs ys i (h : i < (cart xs ys).length),
    ((cart xs ys)[i]'h).length = ys.length := by
  intro xs ys i h
  induction xs generalizing ys i
  case nil => simp! at h
  case cons x xs ih =>
    cases ys
    case nil => simp! at h
    case cons y ys =>
      simp! at h
      simp!
      cases i
      case zero => simp!
      case succ i =>
        simp!
        specialize ih (y :: ys) i (by grind)
        rw [ih]
        simp!

def mul (x y : RankList) : RankList :=
  if hx : x.v = [] then ⟨0,[]⟩ else
  if hy : y.v = [] then ⟨0,[]⟩ else
  ⟨x.r + y.r, add_fold (List.map (List.map (Function.uncurry (· * ·))) (cart x.v y.v)) (by
    use y.v.length
    intro i hxs
    rw [List.getElem_map, List.length_map, length_getElem_cart])⟩
-/

lemma neg_rlz : ∀ xs : List ℚ, (RankList.remLeadZero xs) = [] → (- ·) <$> xs = xs := by
  intro xs h
  apply RankList.rlz_eq_nil at h
  induction xs
  case nil => rfl
  case cons x xs ih =>
    simp!
    have h0 := h 0 (by simp)
    simp! at h0
    rw [h0]
    simp!
    apply ih
    intro i hi
    specialize h i.succ _
    · simp!
      exact hi
    simp! at h
    exact h

@[simp]
def mul : RankList → RankList → RankList
  | ⟨_,_⟩, ⟨_,[]⟩ => ⟨0,[]⟩
  | ⟨_,[]⟩, ⟨_,_⟩ => ⟨0,[]⟩
  | ⟨xr, [x]⟩, ⟨yr,ys⟩ => ⟨xr + yr, (x * ·) <$> ys⟩
  | ⟨xr, x :: x' :: xs⟩, ⟨yr,ys⟩ =>
    if h : x' = 0
    then add ⟨xr + yr, (x * ·) <$> ys⟩ (RankList.mul ⟨xr - (rlzCount (x' :: xs)).succ,
                                                      remLeadZero xs⟩
                                                     ⟨yr, ys⟩)
    else add ⟨xr + yr, (x * ·) <$> ys⟩ (RankList.mul ⟨xr - 1, x' :: xs⟩ ⟨yr, ys⟩)
termination_by x => x.v.length
decreasing_by
  · apply lt_of_le_of_lt (length_rlz xs)
    simp!
    apply Nat.lt_add_right
    apply Nat.lt_succ_of_le
    rfl
  simp

end RankList

@[reducible]
def bop_pres_fluxh (bop : RankList → RankList → RankList) : Prop :=
  ∀ (xr yr : ℤ) (xs ys : List ℚ) (xh : fluxh xr xs) (yh : fluxh yr ys),
  fluxh (bop ⟨xr,xs⟩ ⟨yr,ys⟩).r (bop ⟨xr,xs⟩ ⟨yr,ys⟩).v

structure Fluxion where
  f : RankList
  h : (f.v = [] → f.r = 0) ∧ f.v.head? ≠ some 0 ∧ f.v.getLast? ≠ some 0

namespace Fluxion

instance : Zero Fluxion := ⟨⟨0, []⟩, by simp⟩

instance : One Fluxion := ⟨⟨0, [1]⟩, by simp⟩

theorem addh (xr yr : ℤ) (xs ys : List ℚ) (xh : fluxh xr xs) (yh : fluxh yr ys) :
  ((RankList.add ⟨xr, xs⟩ ⟨yr, ys⟩).v = [] →
   (RankList.add ⟨xr, xs⟩ ⟨yr, ys⟩).r = 0) ∧
   (RankList.add ⟨xr, xs⟩ ⟨yr, ys⟩).v.head? ≠ some 0 ∧
   (RankList.add ⟨xr, xs⟩ ⟨yr, ys⟩).v.getLast? ≠ some 0 := by
  unfold fluxh at *
  rw [RankList.add]
  cases xs
  case nil =>
    rw [decite_true]
    · exact yh
    rfl
  case cons x xs =>
    rw [decite_false]
    · cases ys
      case nil =>
        rw [decite_true]
        · exact xh
        rfl
      case cons y ys =>
        rw [decite_false (by simp)]
        cases @or_not (x + y = 0)
        case inl hhed =>
          rw [decite_true]
          · cases @or_not (xs = [])
            case inl xnil =>
              rw [decite_false]
              · cases @or_not (ys = [])
                case inl ynil =>
                  rw [decite_false]
                  · simp
                  simp!
                  exact ynil
                case inr ynil =>
                  rw [decite_true]
                  · simp!
                    constructor
                    · intro h
                      contrapose! yh
                      simp!
                      intro h0
                      cases ys
                      case nil => contradiction
                      case cons y' ys => rw [List.getLast_cons_cons,
                                             getLast_of_getElem,
                                             RankList.rlz_eq_nil _ h]
                    constructor
                    · apply RankList.head?_rlz
                    cases RankList.getLast?_rlz ys
                    case inl h =>
                      rw [h]
                      cases ys
                      · simp
                      rw [List.getLast?_cons, List.getLast?_cons] at yh
                      rw [List.getLast?_cons]
                      exact yh.2.2
                    case inr h =>
                      rw [h]
                      simp
                  exact ynil
              simp!
              exact xnil
            case inr xnil =>
              rw [decite_true]
              · cases @or_not (ys = [])
                case inl ynil =>
                  rw [decite_false]
                  · simp!
                    constructor
                    · intro h
                      contrapose! xh
                      simp!
                      intro hx
                      cases xs
                      case nil => contradiction
                      case cons x' xs => rw [List.getLast_cons_cons,
                                             getLast_of_getElem,
                                             RankList.rlz_eq_nil _ h]
                    constructor
                    · apply RankList.head?_rlz
                    cases RankList.getLast?_rlz xs
                    case inl h =>
                      rw [h]
                      cases xs
                      · simp
                      rw [List.getLast?_cons, List.getLast?_cons] at xh
                      rw [List.getLast?_cons]
                      exact xh.2.2
                    case inr h =>
                      rw [h]
                      simp
                  simp!
                  exact ynil
                case inr ynil =>
                  rw [decite_true]
                  · apply (addh
                            (xr - ↑((RankList.rlzCount (x :: xs).tail).succ))
                            (yr - ↑((RankList.rlzCount (y :: ys).tail).succ))
                            (RankList.remLeadZero (x :: xs).tail)
                            (RankList.remLeadZero (y :: ys).tail) _ _)
                    · simp!
                      constructor
                      · intro h
                        contrapose! xh
                        simp!
                        intro hx
                        cases xs
                        case nil => contradiction
                        case cons x' xs => rw [List.getLast_cons_cons,
                                              getLast_of_getElem,
                                              RankList.rlz_eq_nil _ h]
                      constructor
                      · apply RankList.head?_rlz
                      cases RankList.getLast?_rlz xs
                      case inl h =>
                        rw [h]
                        cases xs
                        · simp
                        exact xh.2.2
                      case inr h =>
                        rw [h]
                        simp
                    simp!
                    constructor
                    · intro h
                      contrapose! yh
                      simp!
                      intro hy
                      cases ys
                      case nil => contradiction
                      case cons y' ys => rw [List.getLast_cons_cons,
                                             getLast_of_getElem,
                                             RankList.rlz_eq_nil _ h]
                    constructor
                    · apply RankList.head?_rlz
                    cases RankList.getLast?_rlz ys
                    case inl h =>
                      rw [h]
                      cases ys
                      · simp
                      exact yh.2.2
                    case inr h =>
                      rw [h]
                      simp
                  exact ynil
              simp!
              exact xnil
          simp!
          exact hhed
        case inr hhed =>
          rw [decite_false]
          · cases @or_not ((x :: xs).getLast (by simp) + (y :: ys).getLast (by simp) = 0)
            case inl hlas =>
              rw [decite_true]
              · cases @or_not (RankList.remTrailZero (x :: xs).dropLast = [])
                case inl xnil =>
                  rw [decite_false]
                  · cases @or_not (RankList.remTrailZero (y :: ys).dropLast = [])
                    case inl ynil =>
                      rw [decite_false]
                      · simp
                      simp!
                      exact ynil
                    case inr ynil =>
                      rw [decite_true]
                      · simp!
                        constructor
                        · intro h
                          contradiction
                        constructor
                        · cases RankList.head?_rtz (y :: ys).dropLast
                          case inl h =>
                            rw [h]
                            cases ys
                            · simp
                            exact yh.2.1
                          case inr h =>
                            rw [h]
                            simp!
                        apply RankList.getLast?_rtz
                      simp!
                      exact ynil
                  simp!
                  exact xnil
                case inr xnil =>
                  rw [decite_true]
                  · cases @or_not (RankList.remTrailZero (y :: ys).dropLast = [])
                    case inl ynil =>
                      rw [decite_false]
                      · simp!
                        constructor
                        · intro h
                          contradiction
                        constructor
                        · cases RankList.head?_rtz (x :: xs).dropLast
                          case inl h =>
                            rw [h]
                            cases xs
                            · simp
                            exact xh.2.1
                          case inr h =>
                            rw [h]
                            simp
                        apply RankList.getLast?_rtz
                      simp!
                      exact ynil
                    case inr ynil =>
                      rw [decite_true]
                      · apply addh xr yr
                                (RankList.remTrailZero (x :: xs).dropLast)
                                (RankList.remTrailZero (y :: ys).dropLast) _ _
                        · unfold fluxh
                          simp!
                          constructor
                          · intro h
                            contradiction
                          constructor
                          · cases RankList.head?_rtz (x :: xs).dropLast
                            case inl h =>
                              rw [h]
                              cases xs
                              · simp
                              exact xh.2.1
                            case inr h =>
                              rw [h]
                              simp
                          apply RankList.getLast?_rtz
                        unfold fluxh
                        simp!
                        constructor
                        · intro h
                          contradiction
                        constructor
                        · cases RankList.head?_rtz (y :: ys).dropLast
                          case inl h =>
                            rw [h]
                            cases ys
                            · simp
                            exact yh.2.1
                          case inr h =>
                            rw [h]
                            simp
                        apply RankList.getLast?_rtz
                      simp!
                      exact ynil
                  exact xnil
              exact hlas
            case inr hlas =>
              rw [decite_false]
              · have trich := @trichotomous_of ℤ (· < ·) _ xr yr
                cases trich
                case inl trich =>
                  rw [decite_true]
                  · simp!
                    unfold Int.toNat
                    have hofnat := intsub_eq_nat_of_lt xr yr trich
                    rcases hofnat with ⟨c,hc⟩
                    rw [hc]
                    rw [List.replicate_succ,
                        List.cons_append,
                        List.zipWithAll_cons_cons]
                    simp only [reduceCtorEq,
                                IsEmpty.forall_iff,
                                List.head?_cons,
                                ne_eq,
                                Option.some.injEq,
                                true_and] at yh
                    rcases yh with ⟨yh1,yh2⟩
                    simp only [Option.getD_some,
                                zero_add,
                                reduceCtorEq,
                                IsEmpty.forall_iff,
                                List.head?_cons,
                                Option.some.injEq,
                                true_and]
                    constructor
                    · exact yh1
                    rw [←zipWith0.eq_def,
                        List.getLast?_cons]
                    have h : ∃ xs', List.replicate c 0 ++ x :: xs = xs'
                      := by use List.replicate c 0 ++ x :: xs
                    rcases h with ⟨xs',hxs'⟩
                    rw [hxs']
                    cases xs'
                    case nil =>
                      simp!
                      cases ys
                      · simp!
                        exact yh1
                      simp!
                      simp! at yh2
                      exact yh2
                    case cons x' xs' =>
                      cases ys
                      case nil =>
                        rw [←hxs']
                        simp!
                        simp! at xh
                        exact xh.2
                      case cons y' ys =>
                        cases getLast?_zipWith0 HAdd.hAdd x' y' xs' ys
                        case inl h =>
                          rw [h, add_zero, ←List.getLast?_cons, ←hxs']
                          simp!
                          simp! at xh
                          exact xh.2
                        case inr h =>
                          cases h
                          case inl h =>
                            rw [h, zero_add, Option.getD_some]
                            rw [List.getLast?_cons_cons, List.getLast?_cons] at yh2
                            exact yh2
                          case inr h =>
                            rw [h]
                            have h1 : ∀ a b : ℚ,
                              some (a + b) = (some a).getD 0 + (some b).getD 0 := by simp
                            rw [←Option.some_inj,
                                h1,
                                ←List.getLast?_cons,
                                ←hxs',
                                ←List.getLast?_cons]
                            simp!
                            simp! at hlas
                            exact hlas
                  exact trich
                case inr trich =>
                  rw [decite_false]
                  · cases trich
                    case inl trich =>
                      rw [decite_true]
                      · constructor
                        · simp
                        constructor
                        · simp!
                          exact hhed
                        cases getLast?_zipWith0 (fun x1 x2 ↦ x1 + x2) x y xs ys
                        case inl h =>
                          rw [h, add_zero, ←List.getLast?_cons]
                          simp!
                          simp! at xh
                          exact xh.2
                        case inr h =>
                          cases h
                          case inl h =>
                            rw [h, zero_add, ←List.getLast?_cons]
                            simp!
                            simp! at yh
                            exact yh.2
                          case inr h =>
                            rw [h]
                            have h1 : ∀ a b : ℚ,
                              some (a + b) = (some a).getD 0 + (some b).getD 0 := by simp
                            rw [h1, ←List.getLast?_cons, ←List.getLast?_cons]
                            simp!
                            exact hlas
                      exact trich
                    case inr trich =>
                      rw [decite_false]
                      · simp!
                        unfold Int.toNat
                        have hofnat := intsub_eq_nat_of_lt yr xr trich
                        rcases hofnat with ⟨c,hc⟩
                        rw [hc]
                        rw [List.replicate_succ,
                            List.cons_append,
                            List.zipWithAll_cons_cons]
                        simp only [reduceCtorEq,
                                  IsEmpty.forall_iff,
                                  List.head?_cons,
                                  ne_eq,
                                  Option.some.injEq,
                                  true_and] at xh
                        rcases xh with ⟨xh1,xh2⟩
                        simp only [Option.getD_some,
                                    add_zero,
                                    reduceCtorEq,
                                    IsEmpty.forall_iff,
                                    List.head?_cons,
                                    Option.some.injEq,
                                    true_and]
                        constructor
                        · exact xh1
                        rw [←zipWith0.eq_def,
                            List.getLast?_cons]
                        have h : ∃ ys', List.replicate c 0 ++ y :: ys = ys'
                          := by use List.replicate c 0 ++ y :: ys
                        rcases h with ⟨ys',hys'⟩
                        rw [hys']
                        cases ys'
                        case nil =>
                          simp!
                          cases xs
                          · simp!
                            exact xh1
                          simp!
                          simp! at xh2
                          exact xh2
                        case cons y' ys' =>
                          cases xs
                          case nil =>
                            rw [←hys']
                            simp!
                            simp! at yh
                            exact yh.2
                          case cons x' xs =>
                            cases getLast?_zipWith0 HAdd.hAdd x' y' xs ys'
                            case inl h =>
                              rw [h, add_zero, Option.getD_some]
                              rw [List.getLast?_cons_cons, List.getLast?_cons] at xh2
                              exact xh2
                            case inr h =>
                              cases h
                              case inl h =>
                                rw [h, zero_add, ←List.getLast?_cons, ←hys']
                                simp!
                                simp! at yh
                                exact yh.2
                              case inr h =>
                                rw [h]
                                have h1 : ∀ a b : ℚ,
                                  some (a + b) = (some a).getD 0 + (some b).getD 0 := by simp
                                rw [←Option.some_inj,
                                    h1,
                                    ←List.getLast?_cons,
                                    ←List.getLast?_cons,
                                    ←hys']
                                simp!
                                simp! at hlas
                                exact hlas
                      contrapose! trich
                      rw [trich]
                  simp!
                  cases trich
                  case inl trich => rw [trich]
                  case inr trich => exact le_of_lt trich
              exact hlas
          simp!
          exact hhed
termination_by xs.length + ys.length
decreasing_by
  · case _ _ _ _ _ _ _ _ _ _ _ _ _ _ xdef _ _ ydef _ _ _ _ _ _ =>
    unfold fluxh at *
    rw [xdef, ydef]
    apply Nat.add_lt_add_of_lt_of_le
    · apply lt_of_le_of_lt (RankList.length_rlz _)
      simp
    apply le_trans (RankList.length_rlz _)
    simp
  case _ _ _ _ _ _ _ _ _ _ _ _ _ _ xdef _ _ ydef _ _ _ _ _ _ _ _ =>
  rw [xdef, ydef]
  apply Nat.add_lt_add_of_le_of_lt
  · apply le_trans (RankList.length_rtz _)
    simp
  apply lt_of_le_of_lt (RankList.length_rtz _)
  simp

lemma addh' : bop_pres_fluxh RankList.add := addh

def add : Fluxion → Fluxion → Fluxion
  | ⟨⟨xr,xs⟩,xh⟩, ⟨⟨yr,ys⟩,yh⟩ => {
    f := RankList.add ⟨xr,xs⟩ ⟨yr,ys⟩
    h := addh xr yr xs ys xh yh
  }

instance : Add Fluxion where
  add := add

theorem mulh (xr yr : ℤ) (xs ys : List ℚ) (xh : fluxh xr xs) (yh : fluxh yr ys) :
  ((RankList.mul ⟨xr, xs⟩ ⟨yr, ys⟩).v = [] →
   (RankList.mul ⟨xr, xs⟩ ⟨yr, ys⟩).r = 0) ∧
   (RankList.mul ⟨xr, xs⟩ ⟨yr, ys⟩).v.head? ≠ some 0 ∧
   (RankList.mul ⟨xr, xs⟩ ⟨yr, ys⟩).v.getLast? ≠ some 0 := by
  unfold fluxh at *
  rw [RankList.mul.eq_def]
  simp!
  cases xs
  case nil =>
    cases ys
    · simp
    simp
  case cons x xs =>
    cases ys
    case nil => simp
    case cons y ys =>
      cases xs
      case nil =>
        constructor
        · simp!
        constructor
        · simp! at *
          constructor
          · exact xh
          exact yh.1
        rw [List.getLast?_cons] at *
        simp only []
        rw [List.map_cons, List.getLast?_cons]
        simp!
        constructor
        · simp! at xh
          exact xh
        simp! at yh
        exact yh.2
      case cons x' xs =>
        simp at *
        cases @or_not (x' = 0)
        case inl h =>
          rw [decide_true' h]
          apply addh
          · unfold fluxh
            simp
            constructor
            · constructor
              · exact xh.1
              exact yh.1
            rw [List.getLast?_cons] at *
            simp
            constructor
            · exact xh.1
            simp at yh
            exact yh.2
          unfold fluxh
          simp!
          apply mulh
          · unfold fluxh
            simp!
            constructor
            · intro h0
              cases xs
              case nil =>
                simp! at xh
                apply xh.2 at h
                contradiction
              case cons x'' xs =>
                rw [List.getLast?_cons_cons] at xh
                have h1 := RankList.rlz_ne_nil (x'' :: xs) xh.2
                simp only [ne_eq, reduceCtorEq, not_false_eq_true, iff_true] at h1
                contradiction
            constructor
            · apply RankList.head?_rlz
            cases RankList.getLast?_rlz xs
            case inl h0 =>
              rw [h0]
              contrapose! xh
              intro h
              rw [←xh]
              cases xs
              · simp at xh
              rw [List.getLast?_cons_cons]
            case inr h0 =>
              rw [h0]
              simp
          unfold fluxh
          simp
          exact yh
        case inr h =>
          rw [decide_false' h]
          apply addh
          · unfold fluxh
            simp
            constructor
            · constructor
              · exact xh.1
              exact yh.1
            rw [List.getLast?_cons] at *
            simp!
            constructor
            · exact xh.1
            simp! at yh
            exact yh.2
          unfold fluxh
          simp!
          apply mulh
          · unfold fluxh
            simp
            constructor
            · exact h
            exact xh.2
          unfold fluxh
          simp
          exact yh
termination_by xs.length
decreasing_by
  · case _ _ _ _ _ _ _ _ _ _ _ z zs hz _ _ _ _ k ks hk _ _ =>
    rw [hz, hk]
    apply lt_of_le_of_lt (RankList.length_rlz ks)
    simp!
    apply Nat.lt_add_right
    apply Nat.lt_succ_of_le
    rfl
  case _ _ _ _ _ _ _ _ _ _ _ z zs hz _ _ _ _ k ks hk _ _ =>
  rw [hz, hk]
  simp

/-
@[simp]
def mul : Fluxion → Fluxion → Fluxion
  | ⟨⟨xr,xs⟩,xh⟩, ⟨⟨yr,ys⟩,yh⟩ => {
    f := RankList.mul ⟨xr,xs⟩ ⟨yr,ys⟩
    h := mulh xr yr xs ys xh yh
  }-/

def mul (x y : Fluxion) : Fluxion := {
  f := RankList.mul x.f y.f
  h := mulh x.f.r y.f.r x.f.v y.f.v x.h y.h}

instance : Mul Fluxion where
  mul := mul

instance : Neg Fluxion where
  neg | ⟨⟨r,xs⟩,h⟩ => {
    f := {
      r := r
      v := (- ·) <$> xs
    }
    h := by simp! ; exact h
  }

def nsmul (n : ℕ) : Fluxion → Fluxion :=
  if hn : n = 0 then 0 else
  fun ⟨⟨xr,xs⟩,⟨h0,h1,h2⟩⟩ ↦ {
      f := ⟨xr, (n * ·) <$> xs⟩
      h := by
        simp!
        constructor
        · exact h0
        constructor
        · simp! at h1
          intro q hq
          constructor
          · exact hn
          contrapose! h1
          rw [hq, h1]
        simp! at h2
        intro q hq
        constructor
        · exact hn
        contrapose! h2
        rw [hq, h2]
    }

@[simp]
lemma zero_def : (0 : Fluxion) = ⟨⟨0,[]⟩, by simp⟩ := by rfl

@[simp]
lemma one_def : (1 : Fluxion) = ⟨⟨0,[1]⟩, by simp⟩ := by rfl

@[simp]
lemma neg_def (x : Fluxion) : - x = ⟨⟨x.f.r, (- ·) <$> x.f.v⟩, by simp! ; exact x.h⟩ := by rfl

@[simp]
lemma add_def {x y : Fluxion} :
  x + y = ⟨RankList.add x.f y.f, addh x.f.r y.f.r x.f.v y.f.v x.h y.h⟩ := by rfl

@[simp]
lemma mul_def {x y : Fluxion} :
  x * y = ⟨RankList.mul x.f y.f, mulh x.f.r y.f.r x.f.v y.f.v x.h y.h⟩ := by rfl

lemma neg_add_cancel (x : RankList) :
  ∀ (xh : fluxh x.r x.v), (⟨x.r, (- ·) <$> x.v⟩ : RankList).add x = ⟨0,[]⟩ := by
  unfold fluxh
  intro xh
  rcases x with ⟨xr,xs⟩
  simp!
  rw [RankList.add]
  cases xs
  case nil =>
    simp!
    simp! at xh
    exact xh
  case cons x xs =>
    have h0 : List.map (fun x ↦ -x) (x :: xs) ≠ [] := by simp
    have h1 : x :: xs ≠ [] := by simp
    have h2 : (List.map (fun x ↦ -x) (x :: xs)).head h0 + (x :: xs).head h1 = 0 := by simp
    rw [decite_false h0, decite_false h1, decite_true h2]
    cases xs
    case nil => simp
    case cons x' xs =>
      have h3 : RankList.remLeadZero (List.map (fun x ↦ -x) (x :: x' :: xs)).tail ≠ [] := by
        simp only [List.map_cons, List.tail_cons]
        rw [RankList.rlz_ne_nil (-x' :: List.map (fun x ↦ -x) xs)]
        · simp
        rw [List.getLast?_cons, List.getLast?_map]
        rw [List.getLast?_cons_cons, List.getLast?_cons] at xh
        simp at xh
        simp
        exact xh.2
      have h4 : RankList.remLeadZero (x :: x' :: xs).tail ≠ [] := by
        rw [RankList.rlz_ne_nil]
        · simp
        simp at xh
        simp
        exact xh.2
      rw [decite_true h3, decite_true h4]
      have h : ∀ x y : RankList, (⟨y.r, (- ·) <$> y.v⟩ : RankList).add y = ⟨0,[]⟩ → x.r = y.r → x.v = (- ·) <$> y.v → (⟨x.r, x.v⟩ : RankList).add y = ⟨0,[]⟩ := by
        intro x y ha hb hc
        rw [hb, hc]
        exact ha
      apply h {
        r := xr - ↑(RankList.rlzCount (List.map (fun x ↦ -x) (x :: x' :: xs)).tail).succ,
        v := RankList.remLeadZero (List.map (fun x ↦ -x) (x :: x' :: xs)).tail } { r := xr - ↑(RankList.rlzCount (x :: x' :: xs).tail).succ, v := RankList.remLeadZero (x :: x' :: xs).tail }
      · simp only []
        apply neg_add_cancel { r := xr - ↑(RankList.rlzCount (x :: x' :: xs).tail).succ, v := RankList.remLeadZero (x :: x' :: xs).tail }
        unfold fluxh
        simp
        cases @or_not (x' = 0)
        case _ hx =>
          rw [decide_true' hx, decide_true' hx]
          constructor
          · intro h5
            cases xs
            case nil =>
              rw [hx] at xh
              simp at xh
            case cons x'' xs =>
              simp at xh
              have h6 := RankList.rlz_ne_nil (x'' :: xs) xh.2
              simp at h6
              simp at h5
              contradiction
          constructor
          · apply RankList.head?_rlz
          cases RankList.getLast?_rlz xs
          case inl h6 =>
            rw [h6]
            simp at xh
            cases xs
            · simp
            simp at xh
            exact xh.2
          case inr h6 =>
            rw [h6]
            simp
        case _ hx =>
          rw [decide_false' hx, decide_false' hx]
          simp
          constructor
          · exact hx
          simp at xh
          exact xh.2
      · simp
        cases @or_not (x' = 0)
        case _ hx =>
          rw [decide_true' hx, decide_true' hx]
          congr 2
          apply RankList.rlzCount_map
          simp
        case _ hx => rw [decide_false' hx, decide_false' hx]
      simp!
      cases @or_not (x' = 0)
      case _ hx =>
        rw [decide_true' hx, decide_true' hx]
        apply RankList.rlz_map
        simp
      case _ hx =>
        rw [decide_false' hx, decide_false' hx]
        simp
termination_by x.v.length
decreasing_by
  case _ z _ _ _ _ _ _ _ z' zs _ _ =>
  rw [List.length_cons, List.tail_cons]
  apply Nat.lt_succ_of_le
  apply RankList.length_rlz (z' :: zs)

instance : CommRing Fluxion where
  zero_add a := by
    simp!
    congr
    rw [RankList.add]
    simp
  add_zero
  | ⟨⟨ar,as⟩,ah⟩ => by
    simp!
    rw [RankList.add.eq_def]
    cases as
    · simp! at ah
      rw [ah]
      simp
    simp
  zero_mul
  | ⟨⟨ar,as⟩,ah⟩ => by
    simp!
    cases as
    · rw [RankList.mul]
    rw [RankList.mul]
    simp
  mul_zero a := by
    simp!
    rw [RankList.mul]
  one_mul
  | ⟨⟨ar,as⟩,ah⟩ => by
    cases as
    · simp!
      simp! at ah
      exact symm ah
    simp
  neg_add_cancel
  | ⟨a,ah⟩ => by
    simp!
    apply neg_add_cancel a ah
  nsmul := nsmul
  zsmul
    | Int.ofNat n, x => nsmul n x
    | Int.negSucc n, x => -nsmul n.succ x
  add_comm x y := by
    rcases x with ⟨⟨xr,xs⟩,xh⟩
    rcases y with ⟨⟨yr,ys⟩,yh⟩
    simp!
    rw [RankList.add_comm']
    · exact xh
    exact yh
  mul_comm x y := by
    rcases x with ⟨⟨xr,xs⟩,xh⟩
    rcases y with ⟨⟨yr,ys⟩,yh⟩
    simp!
    cases ys
    case nil =>
      cases xs
      · simp!
      simp!
    case cons y ys =>
      cases xs
      case nil => simp!
      case cons x xs =>
        cases xs
        case nil =>
          cases ys
          case nil =>
            simp!
            rw [add_comm, mul_comm]
            simp
          case cons y' ys =>
            simp!
            cases @or_not (y' = 0)
            case inl hy =>
              rw [decide_true' hy, decide_true' hy]
              simp at xh
              rw [hy] at yh
              simp at yh
              rw [RankList.add,
                  decite_false,
                  decite_false]
              · sorry
              · sorry
              simp
            case inr hy =>
              rw [decide_false' hy]
              cases ys
              case nil =>
                simp!
                rw [RankList.add,
                    decite_false,
                    decite_false]





end Fluxion

def F (α : Type) [DivisionRing α] := α → α

namespace F

def apply [DivisionRing α] (f : F α) (x : α) : α := f x

@[simp]
instance [DivisionRing α] : Zero (F α) := ⟨fun _ ↦ 0⟩

@[simp]
instance [DivisionRing α] : One (F α) := ⟨fun _ ↦ 1⟩

@[simp]
instance [DivisionRing α] : Neg (F α) := ⟨fun f x ↦ - f x⟩

@[simp]
instance [DivisionRing α] : Add (F α) := ⟨fun f g x ↦ f x + g x⟩

@[simp]
instance [DivisionRing α] : Mul (F α) := ⟨fun f g x ↦ f x * g x⟩

@[simp]
instance [DivisionRing α] (n : ℕ) : OfNat (F α) n := ⟨fun _ ↦ n⟩

@[simp]
def nsmul [DivisionRing α] (n : ℕ) (f : F α) := OfNat.ofNat n * f

lemma ofnatfst [r : DivisionRing α]
  : ∀ n x, @Nat.cast α r.toAddGroupWithOne.toNatCast n = (instOfNat n).ofNat x := by
  intro n x
  rfl

lemma ofnatsnd [DivisionRing α] : ∀ n, @Nat.unaryCast (F α) _ _ _ n = (instOfNat n).ofNat := by
  intro n
  induction n
  case zero =>
    simp
    rfl
  case succ n ih =>
    simp!
    simp! at ih
    rw [ih]
    rfl

lemma ofnatþrd [r : DivisionRing α] (n : ℕ)
  : (fun (_ : α) ↦ @Nat.cast α r.toAddGroupWithOne.toNatCast n : F α) = (instOfNat n).ofNat := by
  rfl

@[simp]
instance [DivisionRing α] : Ring (F α) where
  nsmul := nsmul
  zsmul
    | Int.ofNat n, f => nsmul n f
    | Int.negSucc n, f => Neg.neg (nsmul n.succ f)
  add_assoc a b c := by
    apply funext
    intro x
    rw [instHAdd]
    simp!
    rw [add_assoc]
  zero_add f := by
    rw [Zero.toOfNat0, instHAdd]
    simp
  add_zero f := by
    rw [Zero.toOfNat0, instHAdd]
    simp
  add_comm f g := by
    apply funext
    intro x
    rw [instHAdd]
    simp!
    rw [add_comm]
  left_distrib f g h := by
    apply funext
    intro x
    rw [instHAdd, instHMul]
    simp!
    rw [left_distrib]
  right_distrib f g h := by
    apply funext
    intro x
    rw [instHAdd, instHMul]
    simp!
    rw [right_distrib]
  zero_mul f := by
    rw [Zero.toOfNat0, instHMul]
    simp
  mul_zero f := by
    rw [Zero.toOfNat0, instHMul]
    simp
  mul_assoc f g h := by
    apply funext
    intro x
    rw [instHMul]
    simp!
    rw [mul_assoc]
  one_mul f := by
    rw [One.toOfNat1, instHMul]
    simp
  mul_one f := by
    rw [One.toOfNat1, instHMul]
    simp
  neg_add_cancel f := by
    rw [instHAdd, instNeg]
    simp
    rfl
  nsmul_zero f := by
    dsimp
    rw [instHMul]
    simp
    rfl
  nsmul_succ n f := by
    apply funext
    intro x
    dsimp
    rw [instOfNatNat, instHMul, instHAdd, instHAdd, instAddNat]
    simp!
    rw [right_distrib, one_mul]
  zsmul_zero' f := by
    dsimp
    rw [instOfNatNat, HMul.hMul, instHMul]
    simp
    rfl
  zsmul_succ' n f := by
    apply funext
    intro x
    dsimp
    rw [instOfNatNat, instHMul, instHAdd, instHAdd, instAddNat]
    simp!
    rw [right_distrib, one_mul]

lemma zero_eq_zero [DivisionRing α] (x : α) : (0 : F α) x = (0 : α) := by
  rw [instOfNat]
  simp

lemma funextex (x : α) : ∀ f g : α → α, f = g → ∃ x, f x = g x := by
  intro f g h
  rw [funext_iff] at h
  specialize h x
  use x

@[simp]
instance [DivisionRing α] : Inv (F α) := ⟨fun f x ↦ (f x)⁻¹⟩

instance [DivisionRing α] : DivisionRing (F α) where
  exists_pair_ne := by
    use (fun _ ↦ 0)
    use (fun _ ↦ 1)
    simp
    intro h
    apply funext_iff.1 at h
    specialize h 1
    simp at h
  mul_inv_cancel f hf := by
    apply funext
    intro x
    rw [instHMul]
    simp
    rw [DivisionRing.mul_inv_cancel]
    · rfl
    sorry
  inv_zero := by
    rw [Zero.toOfNat0]
    simp
  nnqsmul q f := nsmul q.num (F.instDivisionRing.inv (OfNat.ofNat q.den) * f)
  qsmul q f := instRing.zsmul q.num (F.instDivisionRing.inv (OfNat.ofNat q.den) * f)
  nnqsmul_def q f := by
    apply funext
    intro x
    dsimp
    rw [instHMul]
    simp
    rw [←mul_assoc]
    congr
    · rw [ofnatfst q.num x, Nat.cast, NatCast.natCast]
      simp
      rw [ofnatsnd q.num]
      rfl
    revert x
    rw [←funext_iff]
    congr
    · sorry
    nth_rewrite 2 [Nat.cast]
    rw [NatCast.natCast]
    simp
    rw [ofnatsnd, ofnatþrd]

end F

def pow [DivisionRing α] (x : α) : ℤ → α
  | Int.ofNat 0 => 1
  | Int.ofNat (Nat.succ n) => x * pow x n
  | Int.negSucc n => (x * pow x n)⁻¹
termination_by n => |n|.toNat
decreasing_by
  · grind
  grind

def apply [R : DivisionRing α] : RankList → F α
  | ⟨_,[]⟩, _ => 0
  | ⟨r, q :: qs⟩, x => pow (R.qsmul q x) r + apply ⟨r-1,qs⟩ x
termination_by x => x.v.length

def inv (x : Fluxion) {_ : x.f.v.length = 1} : Fluxion :=
  ⟨⟨-x.f.r,x.f.v⟩, by simp! ; exact x.h.1, by simp! ; exact x.h.2.1, by simp! ; exact x.h.2.2⟩

def div (x y : Fluxion) {h : y.f.v.length = 1} : Fluxion := x * @inv y h

theorem apply_add {α} [DivisionRing α] : ∀ f g : Fluxion, @apply α _ (f + g).f = apply f.f + apply g.f := by
  intro f g
  apply funext
  intro x
