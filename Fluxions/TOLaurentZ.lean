import Mathlib

set_option linter.unusedVariables false

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

--- zodd

@[simp]
def odd : Option ℚ → Option ℚ → ℚ
  | none, none => 0
  | none, some y => y
  | some x, none => x
  | some x, some y => x + y

def zodd := List.zipWithAll odd

@[simp]
lemma zodd_nil_left {xs : List ℚ} : zodd [] xs = xs := by rw [zodd] ; cases xs <;> simp

@[simp]
lemma zodd_nil_right {xs : List ℚ} : zodd xs [] = xs := by rw [zodd, List.zipWithAll_nil] ; simp

@[simp]
lemma zodd_cons_cons {x y : ℚ} {xs ys : List ℚ} :
  zodd (x :: xs) (y :: ys) = (x + y) :: zodd xs ys := by
  rw [zodd, List.zipWithAll_cons_cons]
  rfl

lemma zodd_comm {xs ys : List ℚ} : zodd xs ys = zodd ys xs := by
  cases xs
  case nil => simp
  case cons x xs =>
    cases ys
    case nil => simp
    case cons y ys =>
      rw [zodd_cons_cons, zodd_cons_cons]
      congr 1
      · apply add_comm
      apply zodd_comm

lemma zodd_assoc {xs ys zs : List ℚ}
  : zodd (zodd xs ys) zs
  = zodd xs (zodd ys zs) := by
    induction xs generalizing ys zs
    case nil => simp
    case cons x xs ih =>
      cases ys
      case nil => simp
      case cons y ys =>
        cases zs
        case nil => simp
        case cons z zs =>
          simp!
          constructor
          · rw [add_assoc]
          apply ih

@[simp]
theorem List.length_zodd {xs : List ℚ} {ys : List ℚ} :
  (zodd xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys <;> cases ys <;> simp_all

@[simp]
lemma getElem_zodd {xs ys : List ℚ} {i : ℕ} {h} :
  (zodd xs ys)[i]'h = odd xs[i]? ys[i]? := by
  induction i generalizing xs ys
  case zero =>
    cases xs
    case nil =>
      cases ys
      case nil => simp at h
      case cons y ys => simp
    case cons x xs =>
      cases ys
      case nil => simp
      case cons y ys => simp
  case succ i ih =>
    cases xs
    case nil =>
      cases ys
      case nil => simp at h
      case cons y ys =>
        specialize @ih [] ys
        simp! at ih
        simp!
        apply ih
        simp! at h
        exact h
    case cons x xs =>
      cases ys
      case nil =>
        specialize @ih xs []
        simp! at ih
        simp!
        apply ih
        simp! at h
        exact h
      case cons y ys =>
        simp!
        specialize @ih xs ys
        apply ih

@[simp]
def ro {α β γ} (f : Option α → Option β → γ) : Option α → Option β → Option γ
  | none, none => none
  | x, y => some (f x y)

lemma ro_comm {α β} {f : Option α → Option α → β} {x y} (comm : ∀ a b, f a b = f b a) :
  ro f x y = ro f y x := by
  cases x
  case none =>
    cases y
    case none => simp
    case some y => simp! ; apply comm
  case some x =>
    cases y
    case none => simp! ; apply comm
    case some y => simp! ; apply comm

@[simp]
lemma getElem?_zodd {xs ys : List ℚ} {i : ℕ} :
  (zodd xs ys)[i]? = ro odd xs[i]? ys[i]? := by
  induction i generalizing xs ys
  case zero =>
    cases xs
    case nil =>
      cases ys
      case nil => simp
      case cons y ys => simp
    case cons x xs =>
      cases ys
      case nil => simp
      case cons y ys => simp
  case succ i ih =>
    cases xs
    case nil =>
      cases ys
      case nil => simp
      case cons y ys =>
        simp!
        specialize @ih [] ys
        simp! at ih
        exact ih
    case cons x xs =>
      cases ys
      case nil =>
        specialize @ih xs []
        simp! at ih
        simp!
        exact ih
      case cons y ys =>
        simp!
        specialize @ih xs ys
        apply ih

lemma mul_odd {x : ℚ} : ∀ a b : Option ℚ,
  (x * ·) (odd a b) =
  odd (Option.map (x * ·) a) (Option.map (x * ·) b) := by
  intro a b
  cases a
  case none =>
    cases b
    case none => simp
    case some b => simp
  case some a =>
    cases b
    case none => simp
    case some b => simp! ; rw [mul_add]

lemma distrib_zodd {f : ℚ → ℚ} {xs ys : List ℚ}
  (h : ∀ a b : ℚ, f (a + b) = f a + f b)
  : List.map f (zodd xs ys) = zodd (List.map f xs) (List.map f ys) := by
  induction xs generalizing ys
  case nil => simp
  case cons x xs ih =>
    cases ys
    case nil => simp
    case cons y ys =>
      simp!
      constructor
      · rw [h]
      apply ih

-- end zodd

lemma listext? {α} {xs ys : List α} :
  (xs = ys ↔ ∀ (i : ℕ), xs[i]? = ys[i]?) := by
  constructor
  · intro h
    rw [h]
    simp
  intro h
  induction xs generalizing ys
  case nil =>
    specialize h 0
    simp! at h
    rw [h]
  case cons x xs ih =>
    cases ys
    case nil =>
      specialize h 0
      simp at h
    case cons y ys =>
      simp!
      constructor
      · specialize h 0
        simp! at h
        exact h
      apply ih
      intro i
      specialize h (i+1)
      simp! at h
      exact h

lemma listext {α} {xs ys : List α} :
  (xs = ys ↔ (xs.length = ys.length ∧ ∀ (i : ℕ) hx hy, xs[i]'hx = ys[i]'hy)) := by
  cases xs
  case nil =>
    cases ys
    case nil => simp
    case cons y ys => simp
  case cons x xs =>
    cases ys
    case nil => simp
    case cons y ys =>
      constructor
      · intro h
        rw [h]
        simp
      intro h
      rcases h with ⟨hl,h⟩
      simp!
      constructor
      · simp! at h
        specialize h 0 _ _
        · simp
        · simp
        simp! at h
        exact h
      cases xs
      case nil =>
        simp! at hl
        rw [hl]
      case cons x' xs =>
        cases ys
        case nil => simp at hl
        case cons y' ys =>
          rw [listext]
          constructor
          · simp!
            simp! at hl
            exact hl
          intro i hx hy
          specialize h (i+1) _ _
          · simp!
            exact hx
          · simp!
            exact hy
          simp! at h
          exact h

lemma getLast?_of_getElem {α : Type} {x : α} {xs : List α} :
  (x :: xs).getLast? = some ((x :: xs)[xs.length]'(by simp)) := by
  induction xs generalizing x
  case nil => simp
  case cons x' xs ih => apply ih

lemma getD_decide {α : Type} (f : α → Prop) (x : Option α) (y : α) :
  (∀ z, x = some z → f z) → (x = none → f y) → f (x.getD y) := by
  intro hs hn
  cases x
  case none =>
    apply hn
    rfl
  case some z =>
    apply hs
    rfl

@[reducible]
def fluxh (r : ℤ) (v : List ℚ) : Prop := (v = [] → r = 0) ∧ v.head? ≠ some 0 ∧ v.getLast? ≠ some 0

--

structure RankList where
  r : ℤ
  v : List ℚ

namespace RankList

@[simp]
def add_n_zero : ℕ → List ℚ → List ℚ
  | 0, xs => xs
  | Nat.succ n, xs => 0 :: add_n_zero n xs

lemma map_addNZero {f xs n} (h : f 0 = 0) :
  List.map f (add_n_zero n xs) = add_n_zero n (List.map f xs) := by
  cases n
  case zero => simp
  case succ n =>
    simp!
    constructor
    · apply h
    apply map_addNZero h

@[simp]
theorem add_n_zero_getLast? : ∀ n xs, (add_n_zero n xs).getLast?.getD 0 = (xs.getLast?.getD 0) := by
  intro n xs
  induction n
  case zero =>
    simp!
  case succ n ih =>
    rw [add_n_zero, List.getLast?_cons, ih]
    simp!

theorem add_n_zero_getLast?_0 : ∀ xs, (add_n_zero 0 xs).getLast? = xs.getLast? := by simp

theorem add_n_zero_getLast?_of_ne_nil :
    ∀ (n : ℕ) xs, xs ≠ [] → (add_n_zero n xs).getLast? = xs.getLast? := by
  intro n xs hxs
  cases xs
  case nil => simp at hxs
  case cons x xs =>
    cases n
    case zero => simp
    case succ n =>
      rw [add_n_zero,
          List.getLast?_cons,
          add_n_zero_getLast?,
          List.getLast?_cons]
      simp

theorem add_n_zero_getLast?_of_gt_0 :
    ∀ (n : ℕ) xs, 0 < n → (add_n_zero n xs).getLast? = xs.getLast?.getD 0 := by
  intro n xs h
  cases n
  case zero => simp at h
  case succ n =>
    rw [add_n_zero,
        List.getLast?_cons]
    simp

def remLeadZero : List ℚ → List ℚ
  | [] => []
  | x :: xs => if x = 0 then remLeadZero xs else x :: xs

@[simp]
lemma rlz_nil : remLeadZero [] = [] := by rfl

@[simp]
lemma rlz_0 : ∀ xs, remLeadZero (0 :: xs) = remLeadZero xs := by
  intro xs
  rw [remLeadZero]
  simp

lemma head?_rlz : ∀ xs, (remLeadZero xs).head? ≠ some 0 := by
  intro xs
  induction xs
  case nil => rw [remLeadZero] ; simp
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

lemma length_rlz : ∀ xs, (remLeadZero xs).length ≤ xs.length := by
  intro xs
  induction xs
  case nil => rw [remLeadZero]
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

lemma length_rlz_of_head_eq_0 :
  ∀ x xs, x = 0 → (remLeadZero (x :: xs)).length < (x :: xs).length := by
  intro x xs h
  rw [h]
  induction xs
  case nil => rw [remLeadZero] ; simp
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

def rlzCount : List ℚ → ℕ
  | [] => 0
  | x :: xs => if x = 0 then rlzCount xs + 1 else 0

@[simp]
lemma rlzCount_nil : rlzCount [] = 0 := by rw [rlzCount]

@[simp]
lemma rlzCount_0 : ∀ xs, rlzCount (0 :: xs) = rlzCount xs + 1 := by
  intro xs
  rw [rlzCount]
  simp

lemma rlzCount_all0 : ∀ xs, remLeadZero xs = [] → rlzCount xs = xs.length := by
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

def rlmk (r : ℤ) (xs : List ℚ) : RankList := ⟨r - (rlzCount xs).succ, remLeadZero xs⟩

def add'' : RankList → RankList → RankList
  | ⟨_, []⟩, y => y
  | x, ⟨_, []⟩ => x
  | ⟨xr, [x]⟩, ⟨yr, [y]⟩ =>
    if xr = yr
    then if x + y = 0 then ⟨0, []⟩ else ⟨xr, [x + y]⟩
    else if yr < xr
         then ⟨xr, x :: add_n_zero (xr - (yr + 1)).toNat [y]⟩
         else ⟨yr, y :: add_n_zero (yr - (xr + 1)).toNat [x]⟩
  | ⟨xr, [x]⟩, ⟨yr, y :: ys⟩ =>
    if xr = yr
    then if x + y = 0
         then rlmk yr ys
         else ⟨xr, (x + y) :: ys⟩
    else if yr < xr
         then ⟨xr, x :: add_n_zero (xr - (yr + 1)).toNat (y :: ys)⟩
         else ⟨yr, y :: add_n_zero (min (yr - (xr + 1)).toNat (rlzCount ys))
                (add'' ⟨xr, [x]⟩ (rlmk yr ys)).v⟩
  | ⟨xr, x :: xs⟩, ⟨yr, [y]⟩ =>
    if xr = yr
    then if x + y = 0
         then rlmk xr xs
         else ⟨xr, (x + y) :: xs⟩
    else if yr < xr
         then ⟨xr, x :: add_n_zero (min (xr - (yr + 1)).toNat (rlzCount xs))
                (add'' (rlmk xr xs) ⟨yr, [y]⟩).v⟩
         else ⟨yr, y :: add_n_zero (yr - (xr + 1)).toNat (x :: xs)⟩
  | ⟨xr, x :: xs⟩, ⟨yr, y :: ys⟩ =>
    if xr = yr
    then if x + y = 0
         then add'' (rlmk xr xs) (rlmk yr ys)
         else ⟨xr, (x + y) :: add_n_zero (min (rlzCount xs) (rlzCount ys))
                        (add'' (rlmk xr xs) (rlmk yr ys)).v⟩
    else if yr < xr
         then ⟨xr, x :: add_n_zero (min (xr - (yr + 1)).toNat (rlzCount xs))
                        (add'' (rlmk xr xs) ⟨yr,y :: ys⟩).v⟩
         else ⟨yr, y :: add_n_zero (min (yr - (xr + 1)).toNat (rlzCount ys))
                        (add'' ⟨xr,x :: xs⟩ (rlmk yr ys)).v⟩
termination_by x y => x.v.length + y.v.length
decreasing_by
  all_goals (simp! ; try apply add_lt_add_of_lt_of_lt) <;> apply Nat.lt_succ_iff.2 (length_rlz _)

def add' : RankList → RankList → RankList
  | ⟨_, []⟩, y => y
  | x, ⟨_, []⟩ => x
  | ⟨xr, [x]⟩, ⟨yr, [y]⟩ =>
    if xr < yr
    then ⟨yr, y :: add_n_zero (yr - (xr + 1)).toNat [x]⟩
    else if yr < xr
         then ⟨xr, x :: add_n_zero (xr - (yr + 1)).toNat [y]⟩
         else if x + y = 0 then ⟨0, []⟩ else ⟨xr, [x + y]⟩
  | ⟨xr, [x]⟩, ⟨yr, y :: ys⟩ =>
    if xr < yr
    then ⟨yr, y :: add_n_zero (min (yr - (xr + 1)).toNat (rlzCount ys))
      (add' ⟨xr, [x]⟩ ⟨yr - (rlzCount ys).succ, remLeadZero ys⟩).v⟩
    else if yr < xr
         then ⟨xr, x :: add_n_zero (xr - (yr + 1)).toNat (y :: ys)⟩
         else if x + y = 0
              then ⟨yr - (rlzCount ys).succ, remLeadZero ys⟩
              else ⟨xr, (x + y) :: ys⟩
  | ⟨xr, x :: xs⟩, ⟨yr, [y]⟩ =>
    if xr < yr
    then ⟨yr, y :: add_n_zero (yr - (xr + 1)).toNat (x :: xs)⟩
    else if yr < xr
         then ⟨xr, x :: add_n_zero (min (xr - (yr + 1)).toNat (rlzCount xs))
          (add' ⟨xr - (rlzCount xs).succ, remLeadZero xs⟩ ⟨yr, [y]⟩).v⟩
         else if x + y = 0
              then ⟨xr - (rlzCount xs).succ, remLeadZero xs⟩
              else ⟨xr, (x + y) :: xs⟩
  | ⟨xr, x :: xs⟩, ⟨yr, y :: ys⟩ =>
    if xr < yr
    then ⟨yr, y :: add_n_zero (yr - (xr + 1)).toNat
      (add' ⟨xr, x :: xs⟩ ⟨yr - (rlzCount ys).succ, remLeadZero ys⟩).v⟩
    else if yr < xr
         then ⟨xr, x :: add_n_zero (xr - (yr + 1)).toNat
          (add' ⟨xr - (rlzCount xs).succ, remLeadZero xs⟩ ⟨yr, y :: ys⟩).v⟩
         else if x + y = 0
              then add' ⟨xr - (rlzCount xs).succ, remLeadZero xs⟩
                        ⟨yr - (rlzCount ys).succ, remLeadZero ys⟩
              else ⟨xr, (x + y) :: add_n_zero (min (rlzCount xs) (rlzCount ys))
                  (add' ⟨xr - (rlzCount xs).succ, remLeadZero xs⟩
                        ⟨yr - (rlzCount ys).succ, remLeadZero ys⟩).v⟩
termination_by x y => x.v.length + y.v.length
decreasing_by
  all_goals (simp! ; try apply add_lt_add_of_lt_of_lt) <;> apply Nat.lt_succ_iff.2 (length_rlz _)

def add : RankList → RankList → RankList
  | ⟨xr, xs⟩, ⟨yr, ys⟩ =>
    if x0 : xs = []
      then ⟨yr,ys⟩
      else
    if y0 : ys = []
      then ⟨xr,xs⟩
      else
    if rlt : xr < yr
      then if ynil : ys.tail = []
           then ⟨yr, ys.head y0 :: add_n_zero (yr - (xr + 1)).toNat xs⟩
           else ⟨yr, ys.head y0 :: add_n_zero (min (yr - (xr + 1)).toNat (rlzCount ys.tail))
            (add ⟨xr, xs⟩ ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩).v⟩
      else
    if rgt : yr < xr
      then if xnil : xs.tail = []
           then ⟨xr, xs.head x0 :: add_n_zero (xr - (yr + 1)).toNat ys⟩
           else ⟨xr, xs.head x0 :: add_n_zero (min (xr - (yr + 1)).toNat (rlzCount xs.tail))
            (add ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩ ⟨yr, ys⟩).v⟩
      else
    if hhead : xs.head x0 + ys.head y0 = 0
      then if xnil : xs.tail = []
           then if ynil : ys.tail = []
                then ⟨0, []⟩
                else ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩
           else if ynil : ys.tail = []
                then ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩
                else add ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩
                         ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩
      else if xnil : xs.tail = []
           then if ynil : ys.tail = []
                then ⟨xr, [xs.head x0 + ys.head y0]⟩
                else ⟨xr, (xs.head x0 + ys.head y0) :: ys.tail⟩
           else if ynil : ys.tail = []
                then ⟨xr, (xs.head x0 + ys.head y0) :: xs.tail⟩
                else ⟨xr, (xs.head x0 + ys.head y0) ::
                  add_n_zero (min (rlzCount xs.tail) (rlzCount ys.tail))
                  (add ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩
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

#eval add ⟨2,[1,0,2]⟩ ⟨0,[1,0,3]⟩
#eval add ⟨2,[1]⟩ ⟨0,[1,2,3]⟩
#eval add'' ⟨0,[1,0,0,2,3]⟩ ⟨0,[1,0,0,0,0,1,3,2]⟩
#eval add ⟨0,[1,0,0,2,3]⟩ ⟨0,[1,0,0,0,1,3,2]⟩
#eval add ⟨10,[1,0,2,3]⟩ ⟨10,[1,0,0,0,1,3,2]⟩
-- ⟨0, (1 + 1) :: add_n_zero (min 1 3) (add
-- ⟨-2, [2,3]⟩
-- ⟨-4, [1,3,2]⟩).v⟩
#eval add ⟨-2, [2,3]⟩ ⟨-4, [1,3,2]⟩
-- ⟨-2, 2 :: add_n_zero (-2 - (-4 + 1)).toNat
#eval add ⟨-3, [3]⟩ ⟨-4, [1,3,2]⟩

lemma fluxh_recurse (r : ℤ) (x : ℚ) (xs : List ℚ) : xs ≠ [] → fluxh r (x :: xs) →
  fluxh (r - ↑(rlzCount xs).succ) (remLeadZero xs) := by
  unfold fluxh
  intro hx h
  rcases h with ⟨h0,h1,h2⟩
  cases xs
  case nil => contradiction
  case cons x' xs =>
    constructor
    · intro h
      rw [List.getLast?_cons_cons] at h2
      have h' := rlz_ne_nil (x' :: xs) h2
      simp! at h'
      contradiction
    constructor
    · apply head?_rlz
    cases getLast?_rlz (x' :: xs)
    case inl h =>
      rw [h]
      rw [List.getLast?_cons_cons] at h2
      exact h2
    case inr h =>
      rw [h]
      simp

lemma add_comm' (xr yr : ℤ) (xs ys : List ℚ) (xh : fluxh xr xs) (yh : fluxh yr ys) :
  add ⟨xr,xs⟩ ⟨yr,ys⟩ = add ⟨yr,ys⟩ ⟨xr,xs⟩ := by
  unfold fluxh at xh yh
  rw [add]
  cases xs
  case nil =>
    simp!
    rw [RankList.add]
    simp!
    simp! at xh yh
    intro h
    have h0 := yh.1 h
    rw [xh, h0, h]
    simp
  case cons x xs =>
    cases ys
    case nil =>
      simp!
      rw [RankList.add]
      simp
    case cons y ys =>
      rw [decite_false, decite_false]
      · cases @or_not (xr < yr)
        case inl rlt =>
          rw [decite_true rlt]
          cases @or_not (ys = [])
          case inl ynil =>
            rw [decite_true]
            · rw [add,
                  decite_false,
                  decite_false,
                  decite_false,
                  decite_true rlt,
                  decite_true]
              · simp!
                exact ynil
              · simp!
                apply le_of_lt rlt
              simp
            simp!
            exact ynil
          case inr ynil =>
            rw [decite_false]
            · nth_rewrite 2 [add]
              rw [decite_false,
                  decite_false,
                  decite_false,
                  decite_true rlt,
                  decite_false]
              · congr 4
                apply add_comm'
                · exact xh
                apply fluxh_recurse _ y ys ynil yh
              · simp!
                exact ynil
              · simp!
                apply le_of_lt rlt
              · simp
              simp
            simp!
            exact ynil
        case inr rlt =>
          rw [decite_false rlt]
          cases @or_not (yr < xr)
          case inl rgt =>
            rw [decite_true rgt]
            cases @or_not (xs = [])
            case inl xnil =>
              rw [decite_true]
              · rw [add,
                    decite_false,
                    decite_false,
                    decite_true rgt,
                    decite_true]
                · simp!
                  exact xnil
                simp
              simp!
              exact xnil
            case inr xnil =>
              rw [decite_false]
              · nth_rewrite 2 [add]
                rw [decite_false,
                    decite_false,
                    decite_true rgt,
                    decite_false]
                · congr 4
                  apply add_comm'
                  · apply fluxh_recurse _ x xs xnil xh
                  exact yh
                · simp!
                  exact xnil
                · simp!
                simp
              simp!
              exact xnil
          case inr rgt =>
            rw [decite_false rgt]
            cases @or_not (x + y = 0)
            case inl hhead =>
              rw [decite_true]
              · cases @or_not (xs = [])
                case inl xnil =>
                  rw [decite_true]
                  · cases @or_not (ys = [])
                    case inl ynil =>
                      rw [decite_true]
                      · rw [add,
                            decite_false,
                            decite_false,
                            decite_false rgt,
                            decite_false rlt,
                            decite_true,
                            decite_true,
                            decite_true]
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
                      rw [decite_false,
                          add,
                          decite_false,
                          decite_false,
                          decite_false rgt,
                          decite_false rlt,
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
                      · simp
                      · simp
                      simp!
                      exact ynil
                  simp!
                  exact xnil
                case inr xnil =>
                  rw [decite_false]
                  cases @or_not (ys = [])
                  case inl ynil =>
                    rw [decite_true]
                    · rw [add,
                          decite_false,
                          decite_false,
                          decite_false rgt,
                          decite_false rlt,
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
                  case inr ynil =>
                    rw [decite_false]
                    · nth_rewrite 2 [RankList.add]
                      rw [decite_false,
                          decite_false,
                          decite_false rgt,
                          decite_false rlt,
                          decite_true,
                          decite_false,
                          decite_false]
                      · apply add_comm'
                        · apply fluxh_recurse _ x xs xnil xh
                        apply fluxh_recurse _ y ys ynil yh
                      · exact xnil
                      · exact ynil
                      · simp!
                        rw [add_comm]
                        exact hhead
                      · simp
                      · simp
                    exact ynil
                  simp!
                  exact xnil
              simp!
              exact hhead
            case inr hhead =>
              rw [decite_false]
              · cases @or_not (xs = [])
                case inl xnil =>
                  rw [decite_true]
                  · cases @or_not (ys = [])
                    case inl ynil =>
                      rw [decite_true]
                      · rw [add,
                            decite_false,
                            decite_false,
                            decite_false rgt,
                            decite_false rlt,
                            decite_false,
                            decite_true,
                            decite_true]
                        · simp!
                          constructor
                          · apply eq_of_le_of_ge
                            · simp! at rgt
                              exact rgt
                            simp! at rlt
                            exact rlt
                          apply add_comm
                        · exact xnil
                        · exact ynil
                        · simp!
                          rw [add_comm]
                          exact hhead
                        · simp
                        simp
                      exact ynil
                    case inr ynil =>
                      rw [decite_false,
                          add,
                          decite_false,
                          decite_false,
                          decite_false rgt,
                          decite_false rlt,
                          decite_false,
                          decite_false,
                          decite_true]
                      · simp!
                        constructor
                        · apply eq_of_le_of_ge
                          · simp! at rgt
                            exact rgt
                          simp! at rlt
                          exact rlt
                        apply add_comm
                      · exact xnil
                      · exact ynil
                      · simp!
                        rw [add_comm]
                        exact hhead
                      · simp
                      · simp
                      exact ynil
                  exact xnil
                case inr xnil =>
                  rw [decite_false]
                  · cases @or_not (ys = [])
                    case inl ynil =>
                      rw [decite_true]
                      · rw [add,
                            decite_false,
                            decite_false,
                            decite_false rgt,
                            decite_false rlt,
                            decite_false,
                            decite_true,
                            decite_false]
                        · simp!
                          constructor
                          · apply eq_of_le_of_ge
                            · simp! at rgt
                              exact rgt
                            simp! at rlt
                            exact rlt
                          apply add_comm
                        · simp!
                          exact xnil
                        · simp!
                          exact ynil
                        · simp!
                          rw [add_comm]
                          exact hhead
                        · simp
                        simp
                      exact ynil
                    case inr ynil =>
                      rw [decite_false]
                      · nth_rewrite 2 [add]
                        rw [decite_false,
                            decite_false,
                            decite_false rgt,
                            decite_false rlt,
                            decite_false,
                            decite_false,
                            decite_false]
                        · simp!
                          simp! at rlt rgt
                          have hr : yr = xr := eq_of_le_of_ge rlt rgt
                          rw [add_comm, hr]
                          constructor
                          · rfl
                          constructor
                          · rfl
                          congr 1
                          · rw [min_comm]
                          congr 1
                          apply add_comm'
                          · apply fluxh_recurse _ x _ xnil xh
                          rw [←hr]
                          apply fluxh_recurse _ y _ ynil yh
                        · exact xnil
                        · exact ynil
                        · simp!
                          rw [add_comm]
                          exact hhead
                        · simp
                        simp
                      exact ynil
                  exact xnil
              simp!
              exact hhead
      · simp
      simp
termination_by xs.length + ys.length
decreasing_by
  · case _ _ _ _ _ _ _ _ _ _ _ _ _ _ xdef _ _ ydef _ _ _ _ =>
    unfold fluxh at *
    rw [xdef, ydef]
    apply Nat.add_lt_add_of_le_of_lt
    · rfl
    apply add_dec_aux
    simp
  · case _ _ _ _ _ _ _ _ _ _ _ _ _ _ xdef _ _ ydef _ _ _ _ _ _ =>
    rw [xdef, ydef]
    apply Nat.add_lt_add_of_lt_of_le
    · apply add_dec_aux
      simp
    rfl
  · case _ _ _ _ _ _ _ _ _ _ _ _ _ _ xdef _ _ ydef _ _ _ _ _ _ _ _ _ _ =>
    rw [xdef, ydef]
    apply Nat.add_lt_add_of_lt_of_le
    · apply add_dec_aux
      simp
    apply le_of_lt
    apply add_dec_aux
    simp
  case _ _ _ _ _ _ _ _ _ _ _ _ k ks xdef z zs ydef _ _ _ _ _ _ _ _ _ _ =>
  rw [xdef, ydef]
  apply Nat.add_lt_add_of_le_of_lt
  · apply le_of_lt
    have h := @add_dec_aux (k :: ks)
    simp! at h
    apply h
  have h := @add_dec_aux (z :: zs)
  simp! at h
  apply h

def addr : RankList → RankList → ℤ
  | ⟨xr, xs⟩, ⟨yr, ys⟩ =>
    if x0 : xs = [] then yr else
    if y0 : ys = [] then xr else
    if rlt : xr < yr then yr else
    if rgt : yr < xr then xr else
    if hhead : xs.head x0 + ys.head y0 = 0
      then if xnil : xs.tail = []
           then if ynil : ys.tail = []
                then 0
                else yr - (rlzCount ys.tail).succ
           else if ynil : ys.tail = []
                then xr - (rlzCount xs.tail).succ
                else addr ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩
                          ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩
      else xr
termination_by x y => x.v.length + y.v.length
decreasing_by
  apply Nat.add_lt_add_of_le_of_lt
  · apply le_trans (length_rlz xs.tail)
    simp
  apply lt_of_le_of_lt (length_rlz ys.tail)
  cases ys
  · simp at y0
  simp

def addv : RankList → RankList → List ℚ
  | ⟨xr, xs⟩, ⟨yr, ys⟩ =>
    if x0 : xs = []
      then ys
      else
    if y0 : ys = []
      then xs
      else
    if rlt : xr < yr
      then if ynil : ys.tail = []
           then ys.head y0 :: add_n_zero (yr - (xr + 1)).toNat xs
           else ys.head y0 :: add_n_zero (min (yr - (xr + 1)).toNat (rlzCount ys.tail))
            (addv ⟨xr, xs⟩ ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩)
      else
    if rgt : yr < xr
      then if xnil : xs.tail = []
           then xs.head x0 :: add_n_zero (xr - (yr + 1)).toNat ys
           else xs.head x0 :: add_n_zero (min (xr - (yr + 1)).toNat (rlzCount xs.tail))
            (addv ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩ ⟨yr, ys⟩)
      else
    if hhead : xs.head x0 + ys.head y0 = 0
      then if xnil : xs.tail = []
           then if ynil : ys.tail = []
                then []
                else remLeadZero ys.tail
           else if ynil : ys.tail = []
                then remLeadZero xs.tail
                else addv ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩
                          ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩
      else if xnil : xs.tail = []
           then if ynil : ys.tail = []
                then [xs.head x0 + ys.head y0]
                else (xs.head x0 + ys.head y0) :: ys.tail
           else if ynil : ys.tail = []
                then (xs.head x0 + ys.head y0) :: xs.tail
                else (xs.head x0 + ys.head y0) ::
                  add_n_zero (min (rlzCount xs.tail) (rlzCount ys.tail))
                  (addv ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩
                        ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩)
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
    · apply le_of_lt
      apply add_dec_aux y0
  apply Nat.add_lt_add_of_lt_of_le
  · apply add_dec_aux x0
  apply le_of_lt
  apply add_dec_aux y0

lemma odd_comm : ∀ x y, odd x y = odd y x := by
  intro x y ; cases x <;> cases y <;> simp_all! ; apply add_comm

lemma odd_assoc : ∀ x y z, odd (odd x y) z = odd x (odd y z) := by
  intro x y z
  cases x
  case none =>
    cases y
    case none =>
      cases z
      case none => simp
      case some z => simp
    case some y => simp
  case some x =>
    cases y
    case none =>
      cases z
      case none => simp
      case some z => simp
    case some y =>
      cases z
      case none => simp
      case some z =>
        simp!
        apply add_assoc

def oml : Option ℚ → Option ℚ → ℚ
  | none, _ => 0
  | _, none => 0
  | some x, some y => x * y

@[simp]
lemma oml_some_some {x y} : oml (some x) (some y) = x * y := by rw [oml]

def mulv : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys =>
    x * y :: zodd (List.map (x * ·) ys) (mulv xs (y :: ys))
termination_by z => z.length

@[simp]
lemma mulv_l_nil {l} : mulv [] l = [] := by rw [mulv]

@[simp]
lemma mulv_r_nil {l} : mulv l [] = [] := by
  cases l
  · simp
  rw [mulv]
  simp

lemma mulv_cons_cons {x xs y ys} : mulv (x :: xs) (y :: ys) =
  x * y :: (zodd (List.map (x * ·) ys) (mulv xs (y :: ys))) := by rw [mulv]

lemma mulv_singleton {x ys} : mulv [x] ys = List.map (x * ·) ys := by
  cases ys
  case nil => simp
  case cons y ys => simp [mulv]

def mul : RankList → RankList → RankList
  | ⟨_,[]⟩, ⟨_,_⟩ => ⟨0,[]⟩
  | ⟨_,_⟩, ⟨_,[]⟩ => ⟨0,[]⟩
  | ⟨xr,xs⟩, ⟨yr,ys⟩ => ⟨xr + yr, mulv xs ys⟩

instance : Zero RankList where
  zero := ⟨0,[]⟩

@[simp]
lemma zero_def : (0 : RankList) = ⟨0, []⟩ := by rfl

instance : One RankList where
  one := ⟨0,[1]⟩

instance {n} {_ : n ≠ 0} : OfNat RankList n where
  ofNat := ⟨0,[n]⟩

instance : Add RankList where
  add := add

instance : Mul RankList where
  mul := mul

@[simp]
lemma mul_zero {x y} : RankList.mul x ⟨y,[]⟩ = 0 := by
  rcases x with ⟨r,xs⟩
  cases xs
  case nil => simp!
  case cons x xs => simp!

@[simp]
lemma one_def : (1 : RankList) = ⟨0,[1]⟩ := by rfl

@[simp]
lemma mul_def : ∀ x y : RankList, x * y = RankList.mul x y := by intros ; rfl

lemma length_mulv {xs ys} : xs ≠ [] → ys ≠ [] →
  (mulv xs ys).length = xs.length + ys.length - 1 := by
  cases xs
  case nil => simp
  case cons x xs =>
    cases ys
    case nil => simp
    case cons y ys =>
      simp!
      rw [mulv]
      simp!
      cases xs
      case nil => simp ; ring
      case cons x' xs =>
        rw [length_mulv]
        · simp!
          ring
        · simp
        simp

lemma length_mulv_ite {xs ys} : (mulv xs ys).length =
  if xs = [] ∨ ys = [] then 0 else xs.length + ys.length - 1 := by
  cases xs
  case nil => simp
  case cons x xs =>
    cases ys
    case nil => simp
    case cons y ys =>
      simp!
      rw [mulv]
      simp!
      cases xs
      case nil => simp ; ring
      case cons x' xs =>
        rw [length_mulv]
        · simp!
          ring
        · simp
        simp

lemma length_mulv_eq {xs ys} : (mulv xs ys).length =
  (xs.length * ys.length) / (xs.length * ys.length) * (xs.length + ys.length - 1) := by
  cases xs
  case nil => simp
  case cons x xs =>
    cases ys
    case nil => simp
    case cons y ys =>
      simp!
      rw [mulv]
      simp!
      cases xs
      case nil => simp ; ring
      case cons x' xs =>
        rw [length_mulv]
        · simp!
          ring
        · simp
        simp

lemma getLast?_zodd : ∀ (x) (xs ys : List ℚ),
  (x :: xs).length ≤ ys.length →
  (zodd (x :: xs) ys).getLast? =
    some (odd (if (x :: xs).length = ys.length then (x :: xs).getLast? else none) ys.getLast?) := by
  intro x xs ys h
  cases ys
  case nil => contradiction
  case cons y ys =>
  cases @or_not ((x :: xs).length = (y :: ys).length)
  case inl h0 =>
    rw [decide_true' h0]
    induction xs generalizing x y ys
    case nil =>
      cases ys
      case nil => simp
      case cons y' ys => simp at h0
    case cons x' xs ih =>
      cases ys
      case nil => simp at h
      case cons y' ys =>
        specialize ih x' y' ys _ _
        · simp! at h
          simp!
          exact h
        · simp!
          simp! at h0
          exact h0
        rw [List.getLast?_cons_cons,
            List.getLast?_cons_cons,
            zodd_cons_cons,
            List.getLast?_cons,
            ih,
            Option.getD_some]
  case inr h0 =>
    rw [decide_false' h0]
    have h1 := lt_of_le_of_ne h h0
    induction xs generalizing x y ys
    case nil =>
      cases ys
      case nil => simp at h1
      case cons y' ys => simp!
    case cons x' xs ih =>
      cases ys
      case nil => simp at h
      case cons y' ys =>
        cases ys
        case nil =>
          simp! at h0 h
          contradiction
        case cons y'' ys =>
        specialize ih x' y' (y'' :: ys) _ _ _
        · simp!
          simp! at h
          exact h
        · simp!
          simp! at h0
          exact h0
        · simp!
          simp! at h1
          exact h1
        rw [zodd_cons_cons,
            List.getLast?_cons,
            ih,
            Option.getD_some]
        nth_rewrite 2 [List.getLast?_cons_cons]
        rfl

lemma mulv_rec_right {x xs y ys} : mulv (x :: xs) (y :: ys) =
    x * y :: (zodd (List.map (y * ·) xs) (mulv (x :: xs) ys)) := by
  rw [listext?]
  intro i
  induction i generalizing x xs
  case zero => simp [mulv]
  case succ i ih =>
    rw [mulv,
        List.getElem?_cons_succ,
        List.getElem?_cons_succ,
        getElem?_zodd]
    cases xs
    case nil =>
      rw [getElem?_zodd]
      simp! [mulv]
      rw [mulv_singleton, ro_comm odd_comm]
      congr
      rw [List.getElem?_map]
    case cons x' xs =>
      rw [@ih x' xs,
          ←getElem?_zodd]
      congr 1
      case e_a =>
      cases ys
      case nil =>
        simp!
        apply mul_comm
      case cons y' ys =>
        rw [List.map_cons,
            zodd_cons_cons,
            ←zodd_assoc]
        nth_rewrite 2 [zodd_comm, mulv]
        rw [List.map_cons,
            zodd_cons_cons,
            zodd_assoc, add_comm, mul_comm]

lemma mulv_comm {xs ys} : mulv xs ys = mulv ys xs := by
  cases xs
  case nil => simp
  case cons x xs =>
    cases ys
    case nil => simp
    case cons y ys =>
      rw [mulv_rec_right, mul_comm, mulv, mulv_comm]

lemma getLast?_mulv {xs ys} : xs ≠ [] → ys ≠ [] →
  (mulv xs ys).getLast? = some (oml xs.getLast? ys.getLast?) := by
  cases xs
  case nil => simp
  case cons x xs =>
    cases ys
    case nil => simp
    case cons y ys =>
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_const]
      induction xs generalizing x y ys
      case nil =>
        cases ys
        case nil => simp [mulv]
        case cons y' ys =>
          rw [List.getLast?_cons,
              List.getLast?_cons_cons,
              List.getLast?_cons,
              mulv, mulv,
              zodd_nil_right]
          rw [←@List.map_cons,
              List.getLast?_map,
              oml_some_some,
              List.getLast?_cons_cons,
              List.getLast?_cons,
              Option.map_some,
              Option.some_inj]
          rfl
      case cons x' xs ih =>
        cases ys
        case nil =>
          rw [mulv_comm, mulv_singleton,
              List.getLast?_map,
              List.getLast?_cons,
              List.getLast?_cons]
          simp!
          rw [mul_comm]
        case cons y' ys =>
          rw [mulv,
              List.getLast?_cons,
              List.map_cons,
              getLast?_zodd]
          · rw [ih, Option.getD_some,
                List.getLast?_cons_cons,
                length_mulv]
            · simp
            · simp
            simp
          rw [length_mulv]
          · simp
          · simp
          simp

lemma getLast?_mul : ∀ x y : List ℚ,
  x.getLast? ≠ some 0 →
  y.getLast? ≠ some 0 →
  (mulv x y).getLast? ≠ some 0 := by
  intro xs ys hx hy
  induction xs generalizing ys
  case nil => simp
  case cons x xs ih =>
    cases ys
    case nil => simp
    case cons y ys =>
      rw [getLast?_mulv]
      · rw [List.getLast?_cons,
            List.getLast?_cons,
            oml_some_some,
            ne_eq,
            Option.some_inj,
            mul_eq_zero,
            not_or]
        rw [List.getLast?_cons, ne_eq, Option.some_inj] at hx hy
        constructor
        · exact hx
        exact hy
      · simp
      simp

lemma mulv_mul_assoc_left (x) (ys zs) :
  mulv (List.map (fun y ↦ x * y) ys) zs =
  List.map (fun yz ↦ x * yz) (mulv ys zs) := by
    cases ys
    case nil => simp
    case cons y ys =>
      cases zs
      case nil => simp
      case cons z zs =>
        simp!
        rw [mulv, mulv]
        congr 1
        · simp!
          apply mul_assoc
        rw [distrib_zodd (mul_add x),
            mulv_mul_assoc_left,
            List.map_map]
        congr
        funext a
        simp!
        rw [mul_assoc]
termination_by ys.length

-- instance HMul ℚ (List ℚ) (List ℚ) := ⟨fun x ↦ ((x * ·) <$> ·)⟩
-- instance HAdd ℚ (List ℚ) (List ℚ) := ⟨fun x ↦ ((x + ·) <$> ·)⟩
-- instance Mul (List ℚ) := ⟨mulv⟩
-- instance Add (List ℚ) := ⟨zodd⟩
-- x * (ys * zs) = (x * ys) * zs -- mulv_mul_assoc_left
-- (x * y) * zs = x * (y * zs)
-- (x + y) * zs = (x * zs) + (y * zs) -- zodd_mul
-- x * (ys + zs) = x * ys + x * zs
-- xs * (ys + zs) = xs * ys + xs * zs -- zodd_mulv

-- (x + y) * zs = x * zs + y * zs
lemma zodd_mul {x y : ℚ} {zs : List ℚ} :
  List.map ((x + y) * ·) zs = zodd (List.map (x * ·) zs) (List.map (y * ·) zs) := by
  cases zs
  case nil => simp
  case cons z zs =>
    simp!
    constructor
    · apply add_mul
    apply zodd_mul

lemma zodd_mulv {xs ys zs : List ℚ} :
  mulv (zodd xs ys) zs = zodd (mulv xs zs) (mulv ys zs) := by
  induction xs generalizing ys zs
  case nil => simp
  case cons x xs ih =>
    cases ys
    case nil => simp
    case cons y ys =>
      cases zs
      case nil => simp
      case cons z zs =>
        rw [zodd_cons_cons,
            mulv, mulv, mulv,
            zodd_cons_cons]
        congr 1
        case e_head => apply add_mul
        case e_tail =>
          rw [ih, zodd_assoc]
          nth_rewrite 3 [←zodd_assoc]
          nth_rewrite 5 [zodd_comm]
          rw [zodd_assoc]
          nth_rewrite 2 [←zodd_assoc]
          rw [←zodd_mul]

lemma mulv_assoc {xs ys zs} : mulv (mulv xs ys) zs = mulv xs (mulv ys zs) := by
  cases xs
  case nil => simp
  case cons x xs =>
    cases ys
    case nil => simp
    case cons y ys =>
      cases zs
      case nil => simp
      case cons z zs =>
        rw [mulv, mulv, mulv, mulv, mul_assoc,
            distrib_zodd (mul_add x), zodd_assoc,
            zodd_mulv, ←mulv, ←mulv_assoc, mulv_mul_assoc_left]
        congr 2
        simp

theorem r_add_eq_addr (x y : RankList) : (add x y).r = addr x y := by
  rcases x with ⟨xr,xs⟩
  rcases y with ⟨yr,ys⟩
  rw [add, addr]
  cases xs
  case nil => simp
  case cons x xs =>
    have x0 : x :: xs ≠ [] := by simp
    rw [decite_false x0]
    cases ys
    case nil => simp
    case cons y ys =>
      have y0 : y :: ys ≠ [] := by simp
      rw [decite_false y0]
      cases @or_not (xr < yr)
      case inl rlt =>
        rw [decite_true rlt]
        cases ys
        case nil =>
          rw [decite_true]
          · rw [decite_false x0,
                decite_false y0,
                decite_true rlt]
          simp
        case cons y' ys =>
          rw [decite_false]
          · rw [decite_false x0,
                decite_false y0,
                decite_true rlt]
          simp
      case inr rlt =>
        rw [decite_false rlt]
        cases @or_not (yr < xr)
        case inl rgt =>
          rw [decite_true rgt]
          cases xs
          case nil =>
            rw [decite_true]
            · rw [decite_false x0,
                  decite_false y0,
                  decite_false rlt,
                  decite_true rgt]
            simp
          case cons x' xs =>
            rw [decite_false]
            · rw [decite_false x0,
                  decite_false y0,
                  decite_false rlt,
                  decite_true rgt]
            simp
        case inr rgt =>
          rw [decite_false rgt]
          cases @or_not (x + y = 0)
          case inl hhead =>
            rw [decite_true]
            · cases xs
              case nil =>
                rw [decite_true]
                · cases ys
                  case nil =>
                    rw [decite_true]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_true,
                          decite_true,
                          decite_true]
                      · rfl
                      · rfl
                      exact hhead
                    rfl
                  case cons y' ys =>
                    rw [decite_false]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_true,
                          decite_true,
                          decite_false]
                      · simp
                      · rfl
                      exact hhead
                    simp
                rfl
              case cons x' xs =>
                rw [decite_false]
                · cases ys
                  case nil =>
                    rw [decite_true]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_true,
                          decite_false,
                          decite_true]
                      · rfl
                      · simp
                      exact hhead
                    rfl
                  case cons y' ys =>
                    rw [decite_false]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_true,
                          decite_false,
                          decite_false]
                      · apply r_add_eq_addr
                      · simp
                      · simp
                      exact hhead
                    simp
                simp
            exact hhead
          case inr hhead =>
            rw [decite_false]
            · cases xs
              case nil =>
                rw [decite_true]
                · cases ys
                  case nil =>
                    rw [decite_true]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_false]
                      exact hhead
                    rfl
                  case cons y' ys =>
                    rw [decite_false]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_false]
                      exact hhead
                    simp
                rfl
              case cons x' xs =>
                rw [decite_false]
                · cases ys
                  case nil =>
                    rw [decite_true]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_false]
                      exact hhead
                    rfl
                  case cons y' ys =>
                    rw [decite_false]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_false]
                      exact hhead
                    simp
                simp
            exact hhead
termination_by x.v.length + y.v.length
decreasing_by
  case _ d ds _ _ _ c cs _ _ _ _ _ _ _ _ _ b bs _ hd a as _ hc =>
  apply Nat.add_lt_add_of_le_of_lt
  · apply le_trans (length_rlz (b :: bs))
    simp
  apply Nat.lt_succ_of_le
  apply le_trans (length_rlz (a :: as))
  rfl

lemma r_add_of_eq_r {xr yr : ℤ} {xs ys : List ℚ} (xh : fluxh xr xs) (yh : fluxh yr ys)
  (h : xr = yr) : (add ⟨xr, xs⟩ ⟨yr, ys⟩).r = xr := by
  rw [h, add]
  cases xs
  case nil => rw [decite_true rfl]
  case cons x xs =>
    rw [decite_false (by simp)]
    cases ys
    case nil => sorry
    case cons y ys => sorry

theorem v_add_eq_addv (x y : RankList) : (add x y).v = addv x y := by
  rcases x with ⟨xr,xs⟩
  rcases y with ⟨yr,ys⟩
  rw [add, addv]
  cases xs
  case nil => simp
  case cons x xs =>
    have x0 : x :: xs ≠ [] := by simp
    rw [decite_false x0]
    cases ys
    case nil => simp
    case cons y ys =>
      have y0 : y :: ys ≠ [] := by simp
      rw [decite_false y0]
      cases @or_not (xr < yr)
      case inl rlt =>
        rw [decite_true rlt]
        cases ys
        case nil =>
          rw [decite_true]
          · rw [decite_false x0,
                decite_false y0,
                decite_true rlt,
                decite_true]
            rfl
          simp
        case cons y' ys =>
          rw [decite_false]
          · rw [decite_false x0,
                decite_false y0,
                decite_true rlt,
                decite_false]
            · simp!
              congr
              apply v_add_eq_addv
            simp
          simp
      case inr rlt =>
        rw [decite_false rlt]
        cases @or_not (yr < xr)
        case inl rgt =>
          rw [decite_true rgt]
          cases xs
          case nil =>
            rw [decite_true]
            · rw [decite_false x0,
                  decite_false y0,
                  decite_false rlt,
                  decite_true rgt,
                  decite_true]
              rfl
            simp
          case cons x' xs =>
            rw [decite_false]
            · rw [decite_false x0,
                  decite_false y0,
                  decite_false rlt,
                  decite_true rgt,
                  decite_false]
              · simp!
                congr
                apply v_add_eq_addv
              simp
            simp
        case inr rgt =>
          rw [decite_false rgt]
          cases @or_not (x + y = 0)
          case inl hhead =>
            rw [decite_true]
            · cases xs
              case nil =>
                rw [decite_true]
                · cases ys
                  case nil =>
                    rw [decite_true]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_true,
                          decite_true,
                          decite_true]
                      · rfl
                      · rfl
                      exact hhead
                    rfl
                  case cons y' ys =>
                    rw [decite_false]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_true,
                          decite_true,
                          decite_false]
                      · simp
                      · rfl
                      exact hhead
                    simp
                rfl
              case cons x' xs =>
                rw [decite_false]
                · cases ys
                  case nil =>
                    rw [decite_true]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_true,
                          decite_false,
                          decite_true]
                      · rfl
                      · simp
                      exact hhead
                    rfl
                  case cons y' ys =>
                    rw [decite_false]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_true,
                          decite_false,
                          decite_false]
                      · apply v_add_eq_addv
                      · simp
                      · simp
                      exact hhead
                    simp
                simp
            exact hhead
          case inr hhead =>
            rw [decite_false]
            · cases xs
              case nil =>
                rw [decite_true]
                · cases ys
                  case nil =>
                    rw [decite_true]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_false,
                          decite_true]
                      · rfl
                      · rfl
                      exact hhead
                    rfl
                  case cons y' ys =>
                    rw [decite_false]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_false,
                          decite_true]
                      · rfl
                      · rfl
                      exact hhead
                    simp
                rfl
              case cons x' xs =>
                rw [decite_false]
                · cases ys
                  case nil =>
                    rw [decite_true]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_false,
                          decite_false,
                          decite_true]
                      · rfl
                      · simp
                      exact hhead
                    rfl
                  case cons y' ys =>
                    rw [decite_false]
                    · rw [decite_false x0,
                          decite_false y0,
                          decite_false rlt,
                          decite_false rgt,
                          decite_false,
                          decite_false,
                          decite_false]
                      · simp!
                        congr
                        apply v_add_eq_addv
                      · simp
                      · simp
                      exact hhead
                    simp
                simp
            exact hhead
termination_by x.v.length + y.v.length
decreasing_by
  · case _ c cs _ _ b bs _ _ _ _ _ a as _ _ =>
    apply Nat.add_lt_add_of_le_of_lt
    · rfl
    cases @or_not (a = 0)
    case inl h =>
      rw [decide_true' h]
      apply Nat.lt_succ_of_le
      apply le_trans (length_rlz as)
      simp
    case inr h =>
      rw [decide_false' h]
      simp
  · case _ c cs _ _ _ b bs _ _ _ _ _ _ a as _ _ =>
    apply Nat.add_lt_add_of_lt_of_le
    · cases @or_not (a = 0)
      case inl h =>
        rw [decide_true' h]
        apply Nat.lt_succ_of_le
        apply le_trans (length_rlz as)
        simp
      case inr h =>
        rw [decide_false' h]
        simp
    rfl
  · case _ d ds _ _ _ c cs _ _ _ _ _ _ _ _ _ b bs _ _ a as _ _ =>
    apply Nat.add_lt_add_of_le_of_lt
    · apply le_trans (length_rlz (b :: bs))
      simp
    apply Nat.lt_succ_of_le
    apply le_trans (length_rlz (a :: as))
    rfl
  case _ d ds _ _ _ c cs _ _ _ _ _ _ _ _ _ b bs _ _ a as _ _ =>
  apply Nat.add_lt_add_of_le_of_lt
  · apply le_trans (length_rlz (b :: bs))
    simp
  apply Nat.lt_succ_of_le
  apply le_trans (length_rlz (a :: as))
  rfl

lemma add_eq_addr_addv (x y : RankList) : add x y = ⟨addr x y, addv x y⟩
  := by rw [←r_add_eq_addr, ←v_add_eq_addv]

lemma mul_v_eq_nil {xr yr : ℤ} {xs ys : List ℚ} :
  (mul ⟨xr,xs⟩ ⟨yr,ys⟩).v = [] ↔ (xs = [] ∨ ys = []) := by
  constructor
  · intro h
    contrapose! h
    cases xs
    case nil => simp at h
    case cons x xs =>
      cases ys
      case nil => simp at h
      case cons y ys =>
        cases xs
        case nil =>
          simp!
          rw [mulv_singleton]
          simp
        case cons x' xs =>
          simp! [mulv]
  intro h
  cases h
  case inl h =>
    rw [h]
    simp!
  case inr h =>
    rw [h]
    simp!

lemma mul_r {xr yr : ℤ} {xs ys : List ℚ} :
  xs ≠ [] → ys ≠ [] → (mul ⟨xr,xs⟩ ⟨yr,ys⟩).r = xr + yr := by
  cases xs <;> cases ys <;> simp_all [mul]

lemma addv_nil_iff {xr yr xs ys} : xs = [] ∧ ys = [] ↔ addv ⟨xr,xs⟩ ⟨yr,ys⟩ = [] := by
  constructor
  · intro ⟨hx,hy⟩
    rw [hx, hy, addv, decite_true rfl]
  intro h
  constructor
  · contrapose! h
    rw [addv,
        decite_false h]
    cases ys
    case nil => simp! ; exact h
    case cons y ys =>
      rw [decite_false (by simp)]
      cases @or_not (xr = yr)
      case inl hr =>
        rw [hr, decite_false (by simp),
            decite_false (by simp)]


theorem add_assoc' (xr yr zr : ℤ) (xs ys zs : List ℚ)
  (xh : fluxh xr xs) (yh : fluxh yr ys) (zh : fluxh zr zs) :
    add ⟨xr, xs⟩ (add ⟨yr, ys⟩ ⟨zr, zs⟩) = add (add ⟨xr,xs⟩ ⟨yr,ys⟩) ⟨zr,zs⟩ := by
  unfold fluxh at *
  cases xs
  case nil => sorry
  case cons x xs => sorry

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

@[simp]
lemma zero_def : (0 : Fluxion) = ⟨⟨0,[]⟩, by simp⟩ := by rfl

@[simp]
lemma one_def : (1 : Fluxion) = ⟨⟨0,[1]⟩, by simp⟩ := by rfl

theorem addh (xr yr : ℤ) (xs ys : List ℚ) (xh : fluxh xr xs) (yh : fluxh yr ys) :
  ((RankList.add ⟨xr, xs⟩ ⟨yr, ys⟩).v = [] →
   (RankList.add ⟨xr, xs⟩ ⟨yr, ys⟩).r = 0) ∧
   (RankList.add ⟨xr, xs⟩ ⟨yr, ys⟩).v.head? ≠ some 0 ∧
   (RankList.add ⟨xr, xs⟩ ⟨yr, ys⟩).v.getLast? ≠ some 0 := by
  unfold fluxh at xh yh
  rw [RankList.add]
  cases xs
  case nil =>
    simp!
    exact yh
  case cons x xs =>
    cases ys
    case nil => exact xh
    case cons y ys =>
      rw [decite_false, decite_false]
      · cases @or_not (xr < yr)
        case inl rlt =>
          rw [decite_true rlt]
          cases @or_not (ys = [])
          case inl ynil =>
            rw [decite_true]
            · constructor
              · simp
              constructor
              · simp!
                simp! at yh
                exact yh.1
              rw [List.getLast?_cons] at yh
              rw [List.getLast?_cons,
                  RankList.add_n_zero_getLast?_of_ne_nil,
                  List.getLast?_cons]
              · cases xs
                case nil =>
                  simp! at xh
                  simp!
                  exact xh
                case cons x' xs =>
                  simp! at xh
                  simp!
                  exact xh.2
              simp!
            simp!
            exact ynil
          case inr ynil =>
            rw [decite_false]
            · simp only [ne_eq,
                         reduceCtorEq,
                         not_false_eq_true,
                         List.head_cons,
                         List.tail_cons,
                         Nat.succ_eq_add_one,
                         Nat.cast_add,
                         Nat.cast_one,
                         IsEmpty.forall_iff,
                         List.head?_cons,
                         Option.some.injEq,
                         true_and]
              constructor
              · simp! at yh
                exact yh.1
              have h := (addh xr (yr - (↑(RankList.rlzCount ys) + 1))
                              (x :: xs) (RankList.remLeadZero ys) xh
                        (by apply RankList.fluxh_recurse _ y _ ynil yh)).2.2
              rw [List.getLast?_cons]
              apply getD_decide (fun a ↦ ¬(some a) = some 0)
              · intro z hz
                rw [←hz, RankList.add_n_zero_getLast?_of_ne_nil]
                · exact h
                rw [RankList.v_add_eq_addv]
                apply RankList.addv_nil_of_nil
                cases (min (yr - (xr + 1)).toNat (RankList.rlzCount ys))
                case zero => simp! ; exact h
                case succ n =>
                  rw [RankList.add_n_zero_getLast?_of_gt_0]
                  · rw [Option.some_inj]
                    apply getD_decide (fun a ↦ ¬a = 0)
                    · intro k hk
                      rw [hk] at h
                      contrapose! h
                      rw [h]
                    simp!
                    rw [RankList.v_add_eq_addv]

                  simp
                contrapose! h
                rw [←h,
                  (by simp : (
                      (RankList.add ⟨xr, x :: xs⟩ ⟨yr - (↑(RankList.rlzCount ys) + 1), RankList.remLeadZero ys⟩).v.getLast?
                      = (RankList.add_n_zero 0
                      (RankList.add ⟨xr, x :: xs⟩ ⟨yr - (↑(RankList.rlzCount ys) + 1), RankList.remLeadZero ys⟩).v).getLast?))]
                congr 2
                rw [RankList.add_n_zero_getLast?_of_ne_nil]
                · exact h
                rw [RankList.v_add_eq_addv,
                    RankList.addv,
                    decite_false (by simp)]
                cases ys
                case nil =>
                  rw [decite_true (by simp)]
                  simp
                case cons y' ys =>
                  simp!
                  sorry

              intro hn
              simp!
              simp! at yh
              exact yh.1
            simp!
            exact ynil
        case inr rlt =>
          rw [decite_false rlt]
          cases @or_not (yr < xr)
          case inl rgt =>
            rw [decite_true rgt]
            cases @or_not (xs = [])
            case inl xnil =>
              rw [decite_true]
              · simp only [ne_eq,
                           reduceCtorEq,
                           not_false_eq_true,
                           List.head_cons,
                           IsEmpty.forall_iff,
                           List.head?_cons,
                           Option.some.injEq,
                           true_and]
                constructor
                · simp! at xh
                  exact xh.1
                rw [List.getLast?_cons,
                    RankList.add_n_zero_getLast?_of_ne_nil,
                    List.getLast?_cons]
                · simp!
                  apply getD_decide (fun a ↦ ¬a = 0)
                  · intro z hz
                    rw [List.getLast?_cons, hz] at yh
                    simp! at yh
                    exact yh.2
                  intro hn
                  simp! at yh
                  exact yh.1
                simp
              simp!
              exact xnil
            case inr xnil =>
              rw [decite_false]
              · simp only [ne_eq,
                           reduceCtorEq,
                           not_false_eq_true,
                           List.head_cons,
                           List.tail_cons,
                           Nat.succ_eq_add_one,
                           Nat.cast_add,
                           Nat.cast_one,
                           IsEmpty.forall_iff,
                           List.head?_cons,
                           Option.some.injEq,
                           true_and]
                constructor
                · simp! at xh
                  exact xh.1
                have h := (addh (xr - (↑(RankList.rlzCount xs) + 1)) yr
                                (RankList.remLeadZero xs) (y :: ys)
                          (by apply RankList.fluxh_recurse _ x _ xnil xh) yh).2.2
                rw [List.getLast?_cons]
                simp!
                apply getD_decide (fun a ↦ ¬a = 0)
                · intro z hz
                  rw [hz] at h
                  simp! at h
                  exact h
                intro hn
                simp! at xh
                exact xh.1
              simp!
              exact xnil
          case inr rgt =>
            rw [decite_false rgt]
            cases @or_not (x + y = 0)
            case inl hhead =>
              rw [decite_true]
              · cases @or_not (xs = [])
                case inl xnil =>
                  rw [decite_true]
                  · cases @or_not (ys = [])
                    case inl ynil =>
                      rw [decite_true]
                      · simp
                      simp!
                      exact ynil
                    case inr ynil =>
                      rw [decite_false]
                      · simp!
                        apply RankList.fluxh_recurse _ y _ ynil yh
                      simp!
                      exact ynil
                  simp!
                  exact xnil
                case inr xnil =>
                  rw [decite_false]
                  cases @or_not (ys = [])
                  case inl ynil =>
                    rw [decite_true]
                    · simp!
                      apply RankList.fluxh_recurse _ x _ xnil xh
                    simp!
                    exact ynil
                  case inr ynil =>
                    rw [decite_false]
                    · simp!
                      apply addh
                      · apply RankList.fluxh_recurse _ x _ xnil xh
                      apply RankList.fluxh_recurse _ y _ ynil yh
                    exact ynil
                  simp!
                  exact xnil
              simp!
              exact hhead
            case inr hhead =>
              rw [decite_false]
              · cases @or_not (xs = [])
                case inl xnil =>
                  rw [decite_true]
                  · cases @or_not (ys = [])
                    case inl ynil =>
                      rw [decite_true]
                      · simp!
                        exact hhead
                      exact ynil
                    case inr ynil =>
                      rw [decite_false]
                      · simp only [ne_eq,
                                   reduceCtorEq,
                                   not_false_eq_true,
                                   List.head_cons,
                                   List.tail_cons,
                                   IsEmpty.forall_iff,
                                   List.head?_cons,
                                   Option.some.injEq,
                                   true_and]
                        constructor
                        · exact hhead
                        cases ys
                        case nil => simp at ynil
                        case cons y' ys =>
                          rw [List.getLast?_cons_cons]
                          simp only [reduceCtorEq,
                                     IsEmpty.forall_iff,
                                     List.head?_cons,
                                     ne_eq,
                                     Option.some.injEq,
                                     List.getLast?_cons_cons,
                                     true_and] at yh
                          exact yh.2
                      exact ynil
                  exact xnil
                case inr xnil =>
                  rw [decite_false]
                  · cases @or_not (ys = [])
                    case inl ynil =>
                      rw [decite_true]
                      · simp only [ne_eq,
                                   reduceCtorEq,
                                   not_false_eq_true,
                                   List.head_cons,
                                   List.tail_cons,
                                   IsEmpty.forall_iff,
                                   List.head?_cons,
                                   Option.some.injEq,
                                   true_and]
                        constructor
                        · exact hhead
                        cases xs
                        case nil => simp at xnil
                        case cons x' xs =>
                          simp only [reduceCtorEq,
                                     IsEmpty.forall_iff,
                                     List.head?_cons,
                                     ne_eq,
                                     Option.some.injEq,
                                     List.getLast?_cons_cons,
                                     true_and] at xh
                          rw [List.getLast?_cons_cons]
                          exact xh.2
                      exact ynil
                    case inr ynil =>
                      rw [decite_false]
                      · sorry
                        apply addh
                        · unfold fluxh
                          simp!
                          exact hhead
                        apply addh
                        · apply RankList.fluxh_recurse _ x _ xnil xh
                        apply RankList.fluxh_recurse _ y _ ynil yh
                      exact ynil
                  exact xnil
              simp!
              exact hhead
      · simp
      simp
termination_by xs.length + ys.length
decreasing_by
  · case _ _ _ _ _ _ _ _ _ _ _ _ k ks xdef z zs ydef _ _ _ _ =>
    unfold fluxh at *
    rw [xdef, ydef]
    apply Nat.add_lt_add_of_le_of_lt
    · rfl
    have h := @RankList.add_dec_aux (z :: zs)
    simp! at h
    apply h
  · case _ _ _ _ _ _ _ _ _ _ _ _ k ks xdef z zs ydef _ _ _ _ _ _ =>
    rw [xdef, ydef]
    apply Nat.add_lt_add_of_lt_of_le
    · have h := @RankList.add_dec_aux (k :: ks)
      simp! at h
      apply h
    rfl
  · case _ _ _ _ _ _ _ _ _ _ _ _ k ks xdef z zs ydef _ _ _ _ _ _ _ _ _ _ =>
    rw [xdef, ydef]
    apply Nat.add_lt_add_of_lt_of_le
    · have h := @RankList.add_dec_aux (k :: ks)
      simp! at h
      apply h
    apply le_of_lt
    have h := @RankList.add_dec_aux (z :: zs)
    simp! at h
    apply h
  case _ _ _ _ _ _ _ _ _ _ _ _ k ks xdef z zs ydef _ _ _ _ _ _ _ _ _ _ =>
  rw [xdef, ydef]
  apply Nat.add_lt_add_of_le_of_lt
  · apply le_of_lt
    have h := @RankList.add_dec_aux (k :: ks)
    simp! at h
    apply h
  have h := @RankList.add_dec_aux (z :: zs)
  simp! at h
  apply h

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
  cases xs
  case nil => simp!
  case cons x xs =>
    cases ys
    case nil => simp!
    case cons y ys =>
      rw [RankList.mul_r]
      · simp!
        rw [RankList.mulv_cons_cons]
        simp
        simp at yh xh
        constructor
        · constructor
          · exact xh.1
          exact yh.1
        cases ys
        case nil =>
          rw [RankList.mulv_comm,
              RankList.mulv_singleton]
          simp
          rw [List.getLast?_cons,
              List.getLast?_map,
              Option.some_inj,
              mul_comm,
              Option.getD_map,
              mul_eq_zero,
              not_or]
          constructor
          · exact yh.1
          contrapose! xh
          intro h
          cases xs
          case nil =>
            simp! at xh
            contradiction
          case cons x' xs =>
            rw [List.getLast?_cons, Option.some_inj]
            exact xh
        case cons y' ys =>
          rw [List.getLast?_cons,
              List.map_cons,
              Option.some_inj]
          cases xs
          case nil =>
            simp
            rw [List.getLast?_cons,
                List.getLast?_map]
            simp
            constructor
            · exact xh.1
            rw [List.getLast?_cons_cons,
                List.getLast?_cons,
                Option.some_inj] at yh
            exact yh.2
          case cons x' xs =>
            rw [RankList.getLast?_zodd]
            · rw [Option.getD_some,
                  RankList.length_mulv]
              · simp!
                rw [RankList.getLast?_mulv,
                    List.getLast?_cons_cons,
                    List.getLast?_cons,
                    List.getLast?_cons]
                · simp
                  constructor
                  · rw [List.getLast?_cons_cons,
                        List.getLast?_cons,
                        Option.some_inj] at xh
                    exact xh.2
                  rw [List.getLast?_cons_cons,
                      List.getLast?_cons,
                      Option.some_inj] at yh
                  exact yh.2
                · simp
                simp
              · simp
              simp
            rw [RankList.length_mulv]
            · simp
            · simp
            simp
      · simp
      simp

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

@[simp]
lemma neg_def (x : Fluxion) : - x = ⟨⟨x.f.r, (- ·) <$> x.f.v⟩, by simp! ; exact x.h⟩ := by rfl

@[simp]
lemma add_def {x y : Fluxion} :
  x + y = ⟨RankList.add x.f y.f, addh x.f.r y.f.r x.f.v y.f.v x.h y.h⟩ := by rfl

@[simp]
lemma mul_def {x y : Fluxion} :
  x * y = ⟨RankList.mul x.f y.f, mulh x.f.r y.f.r x.f.v y.f.v x.h y.h⟩ := by rfl

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

lemma neg_add_cancel' (x : RankList) :
  ∀ (xh : fluxh x.r x.v), RankList.add ⟨x.r, (- ·) <$> x.v⟩ x = ⟨0,[]⟩ := by
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
    rw [decite_false, decite_false, decite_false, decite_false, decite_true]
    · cases xs
      case nil =>
        rw [decite_true, decite_true]
        · simp
        simp
      case cons x' xs =>
        rw [decite_false, decite_false]
        · simp
          cases @or_not (x' = 0)
          case inl h =>
            rw [h]
            simp!
            rw [RankList.rlz_map,
                RankList.rlzCount_map]
            · apply neg_add_cancel'
               ⟨xr - (↑(RankList.rlzCount xs) + 1 + 1),
                RankList.remLeadZero xs⟩
              have h0 := RankList.fluxh_recurse xr x (x' :: xs) (by simp) xh
              simp! at h0
              rw [decide_true' h, decide_true' h] at h0
              simp!
              exact h0
            · simp
            simp
          case inr h =>
            rw [RankList.rlzCount,
                RankList.rlzCount,
                RankList.remLeadZero,
                RankList.remLeadZero,
                decide_false' h,
                decide_false' h,
                decide_false' _,
                decide_false' _]
            · simp!
              apply neg_add_cancel' ⟨xr - 1, (x' :: xs)⟩
              simp! at xh
              unfold fluxh
              simp!
              constructor
              · exact h
              exact xh.2
            · simp!
              exact h
            simp!
            exact h
        · simp
        simp
    · simp
    · simp
    · simp
    · simp
    simp
termination_by x.v.length
decreasing_by
  · case _ z _ _ _ _ z' zs _ _ _ _ =>
    simp!
    rw [Nat.lt_succ_iff]
    apply le_trans (@RankList.length_rlz zs)
    simp
  simp!

lemma mul_comm' (x y : RankList) (xh : fluxh x.r x.v) (yh : fluxh y.r y.v) :
  RankList.mul x y = RankList.mul y x := by
  rcases x with ⟨xr,xs⟩
  rcases y with ⟨yr,ys⟩
  rw [RankList.mul.eq_def, RankList.mul.eq_def]
  cases ys
  case nil =>
    cases xs
    · simp!
    simp!
  case cons y ys =>
    cases xs
    case nil => simp
    case cons x xs =>
      simp!
      constructor
      · rw [add_comm]
      rw [RankList.mulv_comm]

theorem only_singletons_invertible {x : Fluxion} : (∃ y, x * y = 1) ↔ x.f.v.length = 1 := by
  rcases x with ⟨⟨xr,xs⟩,hx⟩
  cases xs
  case nil => simp!
  case cons x xs =>
    constructor
    · intro h
      rcases h with ⟨⟨⟨yr,ys⟩,hy⟩,h⟩
      cases xs
      case nil => simp!
      case cons x' xs =>
        cases ys
        case nil => simp! at h
        case cons y ys =>
          simp! at h
          have h0 := List.length_eq_of_beq (beq_of_eq h.2)
          rw [RankList.length_mulv (by simp) (by simp),
              List.length_cons, List.length_cons, List.length_cons,
              ←add_assoc, Nat.add_sub_cancel,
              add_comm, ←add_assoc] at h0
          simp! at h0
    intro h
    use ⟨⟨-xr,[1 / x]⟩, by
      simp!
      simp! at hx
      exact hx.1⟩
    cases xs
    case cons x' xs => simp! at h
    case nil =>
      simp! [RankList.mulv]
      simp! at hx
      apply Rat.instDivisionRing.12 _ hx

/-
lemma left_distrib' : ∀ a b c : Fluxion, a * (b + c) = a * b + a * c := by
  cases xs
  case nil =>
    simp!
    rw [RankList.add]
    simp
  case cons x xs =>
    cases ys
    case nil =>
      simp!
      rw [RankList.add]
      simp!
      rw [RankList.add]
      simp
    case cons y ys =>
      cases zs
      case nil =>
        simp!
        rw [RankList.add]
        simp!
        rw [RankList.add]
        simp
        rw [RankList.mulv]
        simp
      case cons z zs =>
        simp!
        rw [RankList.mul,
            RankList.v_add_eq_addv,
            RankList.r_add_eq_addr,
            RankList.mulv,
            RankList.mulv,
            RankList.add,
            RankList.addr,
            RankList.addv]
        · simp!
          cases @or_not (yr < zr)
          case inl h =>
            rw [decide_true' h,
                decide_true' h,
                decide_true' h]
            cases zs
            case nil =>
              simp!
              cases xs
              case nil =>
                simp!
                rw [RankList.mulv,
                    RankList.mulv,
                    zodd_nil_right]
                ring_nf
                rw [RankList.map_addNZero]
                · rw [List.map_cons]
                apply mul_zero
              case cons x' xs =>
                rw [decide_false']
                · sorry
                rw [RankList.mulv]
                simp
-/

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
  | ⟨⟨ar,as⟩,ah⟩ => by simp!
  mul_zero
  | ⟨⟨ar,as⟩,ah⟩ => by
    cases as
    case nil => simp!
    case cons a as => simp!
  one_mul
  | ⟨⟨ar,as⟩,ah⟩ => by
    cases as
    · simp!
      simp! at ah
      exact symm ah
    simp!
    rw [RankList.mulv_singleton]
    simp
  mul_one
  | ⟨⟨ar,as⟩,⟨h0,h1,h2⟩⟩ => by
    cases as
    case nil =>
      simp!
      simp! at h0
      exact symm h0
    case cons a as =>
      simp!
      rw [RankList.mulv_comm,
          RankList.mulv_singleton]
      simp
  neg_add_cancel
  | ⟨a,ah⟩ => by
    simp!
    apply neg_add_cancel' a ah
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
  mul_comm
    | ⟨x,xh⟩, ⟨y,yh⟩ => by
      simp!
      apply mul_comm' x y xh yh
  mul_assoc
    | ⟨⟨xr,xs⟩,xh⟩, ⟨⟨yr,ys⟩,yh⟩, ⟨⟨zr,zs⟩,zh⟩ => by
      simp!
      cases xs
      case nil => simp!
      case cons x xs =>
        cases ys
        case nil => simp!
        case cons y ys =>
          cases zs
          case nil => simp!
          case cons z zs =>
            simp!
            rw [RankList.mulv,
                RankList.mulv]
            simp!
            constructor
            · apply add_assoc
            rw [←RankList.mulv,
                RankList.mulv_assoc,
                ←RankList.mulv]
  add_assoc
    | ⟨⟨xr,xs⟩,xh⟩, ⟨⟨yr,ys⟩,yh⟩, ⟨⟨zr,zs⟩,zh⟩ => by
        simp
        sorry
  left_distrib
    | ⟨⟨xr,xs⟩,xh⟩, ⟨⟨yr,ys⟩,yh⟩, ⟨⟨zr,zs⟩,zh⟩ => by sorry
  right_distrib
    | ⟨⟨xr,xs⟩,xh⟩, ⟨⟨yr,ys⟩,yh⟩, ⟨⟨zr,zs⟩,zh⟩ => by sorry
  nsmul_succ
    | n, ⟨⟨r,xs⟩,⟨h0,h1,h2⟩⟩ => by
      rw [nsmul, decite_false (by simp)]
      simp!
      cases n
      case zero =>
        rw [nsmul, decite_true rfl]
        simp!
        rw [RankList.add, decite_true rfl]
      case succ n =>
        rw [nsmul, decite_false (by simp)]
        simp!
        rw [RankList.add_eq_addr_addv]
        congr
        case e_r =>
          rw [RankList.addr]
          cases xs
          case nil => rw [decite_true (by simp)]
          case cons x xs =>
            rw [decite_false (by simp),
                decite_false (by simp),
                decite_false (by simp),
                decite_false (by simp),
                decite_false]
            · cases xs
              case nil => rw [decite_true (by simp)]
              case cons x' xs =>
                rw [decite_false (by simp),
                    decite_false (by simp)]
                simp!

        case e_v =>
        rw [RankList.add]
        cases xs
        case nil =>
          rw [decite_true (by simp)]
          simp!
        case cons x xs =>
          rw [decite_false (by simp),
              decite_false (by simp),
              decite_false (by simp),
              decite_false (by simp),
              decite_false]
          · cases xs
            case nil =>
              rw [decite_true (by simp),
                  decite_true (by simp)]
              simp!
              rw [add_mul, one_mul]
            case cons x' xs =>
              rw [decite_false (by simp),
                  decite_false (by simp)]






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
  nnqsmul q f := nsmul q.num (F.instInv.inv (OfNat.ofNat q.den) * f)
  qsmul q f := instRing.zsmul q.num (F.instInv.inv (OfNat.ofNat q.den) * f)
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
    sorry
    /-congr
    · sorry
    nth_rewrite 2 [Nat.cast]
    rw [NatCast.natCast]
    simp
    rw [ofnatsnd, ofnatþrd]-/
  qsmul_def := by sorry

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

theorem apply_add {α} [DivisionRing α] :
  ∀ f g : Fluxion, @apply α _ (f + g).f = apply f.f + apply g.f := by
  intro f g
  apply funext
  intro x
  rcases f with ⟨⟨fr,fs⟩,fh⟩
  rcases g with ⟨⟨gr,gs⟩,gh⟩
  simp!
  sorry
