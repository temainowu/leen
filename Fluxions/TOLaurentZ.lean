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

def zodd := List.zipWithAll odd

@[simp]
lemma zodd_nil_left {xs : List ℚ} : zodd [] xs = xs := by rw [zodd] ; cases xs <;> simp

@[simp]
lemma zodd_nil_left' {xs ys : List ℚ} {h : xs = []} : zodd xs ys = ys
  := by rw [h, zodd] ; cases xs <;> simp

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
def addNZero : ℕ → List ℚ → List ℚ
  | 0, xs => xs
  | Nat.succ n, xs => 0 :: addNZero n xs

def addNZero_of_ne0 {n xs} (h : n ≠ 0) : addNZero n xs = 0 :: addNZero (n - 1) xs
  := by cases n ; (· simp at h) ; simp

lemma map_addNZero {f xs n} (h : f 0 = 0) :
  List.map f (addNZero n xs) = addNZero n (List.map f xs) := by
  cases n
  case zero => simp
  case succ n =>
    simp!
    constructor
    · apply h
    apply map_addNZero h

@[simp]
theorem getLast?_addNZero : ∀ n xs, (addNZero n xs).getLast?.getD 0 = (xs.getLast?.getD 0) := by
  intro n xs
  induction n
  case zero =>
    simp!
  case succ n ih =>
    rw [addNZero, List.getLast?_cons, ih]
    simp!

theorem getLast?_addNZero_of_ne_nil :
    ∀ (n : ℕ) xs, xs ≠ [] → (addNZero n xs).getLast? = xs.getLast? := by
  intro n xs hxs
  cases xs
  case nil => simp at hxs
  case cons x xs =>
    cases n
    case zero => simp
    case succ n =>
      rw [addNZero,
          List.getLast?_cons,
          getLast?_addNZero,
          List.getLast?_cons]
      simp

theorem getLast?_addNZero_of_gt_0 :
    ∀ (n : ℕ) xs, 0 < n → (addNZero n xs).getLast? = xs.getLast?.getD 0 := by
  intro n xs h
  cases n
  case zero => simp at h
  case succ n =>
    rw [addNZero,
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


@[simp]
def rankShiftZodd (xr yr : ℤ) (xs ys : List ℚ) : List ℚ :=
  zodd (addNZero (yr - xr).toNat xs) (addNZero (xr - yr).toNat ys)

lemma rankShiftZodd_comm {xr yr xs ys} :
  rankShiftZodd xr yr xs ys = rankShiftZodd yr xr ys xs := by
  rw [rankShiftZodd, rankShiftZodd, zodd_comm]

@[simp]
def normalise : RankList → RankList
  | ⟨_, []⟩ => ⟨0, []⟩
  | ⟨r, x :: xs⟩ => if x = 0 then normalise ⟨r - 1, xs⟩
                             else ⟨r, (remLeadZero (x :: xs).reverse).reverse⟩
termination_by x => x.v.length

lemma normalise_zero_cons {r xs} : normalise ⟨r, 0 :: xs⟩ = normalise ⟨r - 1, xs⟩ := by simp!

lemma nhf_aux {r x xs} (h : x ≠ 0) :
  normalise ⟨r, x :: xs⟩ = ⟨r, (remLeadZero (x :: xs).reverse).reverse⟩ := by
  simp!
  intro h0
  contradiction

lemma rlz_append {x xs ys} (h : x ≠ 0) :
  remLeadZero (ys ++ (x :: xs)) = remLeadZero ys ++ (x :: xs) := by
    induction ys
    case nil =>
      simp!
      intro h1
      contradiction
    case cons y ys ih =>
      simp!
      rw [ih]
      cases @or_not (y = 0)
      case inl hy =>
        rw [hy]
        simp
      case inr hy =>
        rw [decide_false' hy,
            decide_false' hy]
        simp

lemma normalise_has_fluxh (x : RankList) : fluxh (normalise x).r (normalise x).v := by
  unfold fluxh
  rcases x with ⟨r,xs⟩
  cases xs
  case nil => simp
  case cons x xs =>
    cases @or_not (x = 0)
    case inl h =>
      rw [h]
      simp!
      apply normalise_has_fluxh
    case inr h =>
      simp!
      rw [decide_false' h]
      simp!
      rw [rlz_append h,
          List.getLast?_append]
      simp!
      constructor
      · exact h
      apply getD_decide (fun x ↦ ¬x = 0)
      · intro z hz
        contrapose! hz
        rw [hz]
        apply head?_rlz
      intros
      exact h
termination_by x.v.length

@[simp]
def add : RankList → RankList → RankList
  | ⟨_, []⟩, y => y
  | x, ⟨_, []⟩ => x
  | ⟨xr, xs⟩, ⟨yr, ys⟩ => normalise ⟨max xr yr, rankShiftZodd xr yr xs ys⟩

lemma add_comm' (xr yr : ℤ) (xs ys : List ℚ) (xh : fluxh xr xs) (yh : fluxh yr ys) :
  add ⟨xr, xs⟩ ⟨yr, ys⟩ = add ⟨yr, ys⟩ ⟨xr, xs⟩ := by
  unfold fluxh at xh yh
  cases xs
  case nil =>
    cases ys
    case nil =>
      simp! at xh yh
      rw [xh, yh]
    case cons y ys => simp
  case cons x xs =>
    cases ys
    case nil => simp
    case cons y ys =>
      simp!
      rw [zodd_comm, max_comm]

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

theorem add_assoc'
  (xr yr zr : ℤ) (xs ys zs : List ℚ)
  (xh : fluxh xr xs)
  (yh : fluxh yr ys)
  (zh : fluxh zr zs) :
  add ⟨xr,xs⟩ (add ⟨yr,ys⟩ ⟨zr,zs⟩) = add (add ⟨xr,xs⟩ ⟨yr,ys⟩) ⟨zr,zs⟩ := by
  cases xs
  case nil => simp
  case cons x xs =>
    cases ys
    case nil => simp
    case cons y ys =>
      cases zs
      case nil =>
        simp!
        rw [add_comm' _ _ _ _ (normalise_has_fluxh _) zh]
        simp
      case cons z zs =>
        simp!
        sorry

end RankList

@[reducible]
def bop_pres_fluxh (bop : RankList → RankList → RankList) : Prop :=
  ∀ (xr yr : ℤ) (xs ys : List ℚ) (xh : fluxh xr xs) (yh : fluxh yr ys),
  fluxh (bop ⟨xr,xs⟩ ⟨yr,ys⟩).r (bop ⟨xr,xs⟩ ⟨yr,ys⟩).v

lemma addh : bop_pres_fluxh RankList.add := by
  unfold bop_pres_fluxh fluxh
  intro xr yr xs ys hx hy
  cases xs
  case nil =>
    rw [RankList.add]
    simp!
    exact hy
  case cons x xs =>
    cases ys
    case nil =>
      simp!
      simp! at hx
      exact hx
    case cons y ys =>
      simp!
      apply RankList.normalise_has_fluxh

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

lemma normalise_eq_0_of_all0 {r xs} (h : RankList.remLeadZero xs = []) :
  RankList.normalise ⟨r, xs⟩ = (0 : RankList) := by
  cases xs
  case nil => simp
  case cons x xs =>
    cases @or_not (x = 0)
    case inl hx =>
      rw [hx]
      simp!
      rw [hx] at h
      simp! at h
      apply normalise_eq_0_of_all0 h
    case inr hx =>
      simp! at h
      rw [decide_false' hx] at h
      contradiction

lemma nac_aux {xs} : RankList.remLeadZero (zodd (List.map (fun x ↦ -x) xs) xs) = [] := by
  cases xs
  case nil => simp
  case cons x xs =>
    simp!
    apply nac_aux

lemma neg_add_cancel' (x : RankList) :
  ∀ (xh : fluxh x.r x.v), RankList.add ⟨x.r, (- ·) <$> x.v⟩ x = ⟨0,[]⟩ := by
  unfold fluxh
  intro xh
  rcases x with ⟨xr,xs⟩
  cases xs
  case nil =>
    simp! at xh
    rw [xh]
    simp
  case cons x xs =>
    simp!
    simp! at xh
    apply normalise_eq_0_of_all0
    apply nac_aux

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

/-
lemma nsmul_succ_aux {n : ℕ} {r x xs} (h : x ≠ 0) :
  ⟨r, (↑n + 1 + 1) * x :: List.map (fun x ↦ (↑n + 1 + 1) * x) xs⟩ =
  (⟨r, (RankList.remLeadZero (
    (zodd (List.map (fun x ↦ (↑n + 1) * x) xs) xs).reverse ++
      [((↑n : ℚ) + 1) * x + x])).reverse⟩ : RankList) := by
  congr
  induction xs
  case nil =>
    simp!
    rw [decide_false']
    · rw [add_mul, one_mul, List.reverse_singleton]
    nth_rw 2 [←one_mul x]
    rw [←add_mul, mul_eq_zero, not_or]
    constructor
    · rw [(by simp : 1 = (↑(1 : ℕ) : ℚ)),
          ←Rat.natCast_add,
          ←Rat.natCast_add]
      contrapose! h
      rw [Rat.natCast_eq_zero_iff] at h
      simp! at h
    exact h
  case cons x' xs ih =>
    rw [RankList.rlz_append]
    · rw [List.reverse_append,
          List.reverse_singleton,
          List.map_cons,
          List.singleton_append]
      simp!
      rw [add_mul, one_mul]
      simp!


    nth_rw 2 [←one_mul x]
    rw [←add_mul]
    apply mul_ne_zero
    · rw [(by simp : 1 = (↑(1 : ℕ) : ℚ)),
          ←Rat.natCast_add,
          ←Rat.natCast_add]
      contrapose! h
      rw [Rat.natCast_eq_zero_iff] at h
      simp! at h
    exact h
-/


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

instance : CommRing Fluxion where
  zero_add a := by simp
  add_zero
  | ⟨⟨ar,as⟩,ah⟩ => by
    simp!
    cases as
    · simp! at ah
      rw [ah]
      simp!
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
        simp
      case succ n =>
        rw [nsmul, decite_false (by simp)]
        simp!
        cases xs
        case nil => simp
        case cons x xs =>
          simp!
          simp! at h1
          rw [decide_false']
          · apply nsmul_succ_aux


end Fluxion

/-
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

lemma ofnatþrd {α} [r : DivisionRing α] (n : ℕ)
  : (fun (_ : α) ↦ @Nat.cast α r.toAddGroupWithOne.toNatCast n : F α) = (instOfNat n).ofNat := by
  rfl

@[simp]
instance {α} [DivisionRing α] : Ring (F α) where
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

lemma zero_eq_zero {α} [DivisionRing α] (x : α) : (0 : F α) x = (0 : α) := by
  rw [instOfNat]
  simp

lemma funextex {α} (x : α) : ∀ f g : α → α, f = g → ∃ x, f x = g x := by
  intro f g h
  rw [funext_iff] at h
  specialize h x
  use x

@[simp]
instance {α} [DivisionRing α] : Inv (F α) := ⟨fun f x ↦ (f x)⁻¹⟩

instance {α} [DivisionRing α] : DivisionRing (F α) where
  exists_pair_ne := by
    use (fun _ ↦ 0)
    use (fun _ ↦ 1)
    simp!
    intro h
    apply funext_iff.1 at h
    specialize h 1
    simp at h
  mul_inv_cancel f hf := by
    apply funext
    intro x
    rw [instHMul]
    simp!
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
    simp!
    rw [←mul_assoc]
    congr
    · rw [ofnatfst q.num x, Nat.cast, NatCast.natCast]
      simp!
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
-/
