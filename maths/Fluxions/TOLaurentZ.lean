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

lemma id_comp {α β} {f : α → β} {b : β → β} {h : b = id} : (fun a ↦ b a) ∘ f = f := by
  rw [h] ; rfl

lemma length_congr {α} {a b : List α} : a = b → a.length = b.length := by
  intro h ; rw [h]

lemma imp_trans {a b c : Prop} : (a → b) → (b → c) → (a → c) := by
  intro p q A
  specialize p A
  specialize q p
  exact q

@[simp]
theorem List.length_zipWithAll.{u_1, u_2, u_3} {α : Type u_1} {β : Type u_2} {γ : Type u_3}
  {f : Option α → Option β → γ} {l₁ : List α} {l₂ : List β} :
  (List.zipWithAll f l₁ l₂).length = max l₁.length l₂.length := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

@[simp]
lemma getElem_zipWithAll.{u_1, u_2, u_3} {α : Type u_1} {β : Type u_2} {γ : Type u_3}
  {f : Option α → Option β → γ} {xs : List α} {ys : List β} {i : ℕ} {h} :
  (List.zipWithAll f xs ys)[i]'h = f xs[i]? ys[i]? := by
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
lemma getElem?_zipWithAll.{u_1, u_2, u_3} {α : Type u_1} {β : Type u_2} {γ : Type u_3}
  {f : Option α → Option β → γ} {xs : List α} {ys : List β} {i : ℕ} :
  (List.zipWithAll f xs ys)[i]? = ro f xs[i]? ys[i]? := by
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

def add_aux : ℤ → ℚ → RankList → RankList
  | r, x, ⟨yr, ys⟩ =>
    if y0 : ys = []
      then ⟨r,[x]⟩
      else
    if rlt : r < yr
      then if ynil : ys.tail = []
           then ⟨yr, ys.head y0 :: (add_n_zero (yr - (r + 1)).toNat [x])⟩
           else ⟨yr, ys.head y0 ::
            (add_aux r x ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩).v⟩
      else
    if rgt : yr < r
      then ⟨r, x :: (add_n_zero (r - (yr + 1)).toNat ys)⟩
      else
    if hhead : x + ys.head y0 = 0
      then if ynil : ys.tail = []
           then ⟨0, []⟩
           else ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩
      else if ynil : ys.tail = []
           then ⟨r, [x + ys.head y0]⟩
           else ⟨r, (x + ys.head y0) :: ys.tail⟩
termination_by _ _ y => y.v.length
decreasing_by
  cases ys
  case nil => simp at y0
  case cons y ys =>
    simp!
    rw [Nat.lt_succ_iff]
    exact length_rlz ys

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
           then ⟨yr, ys.head y0 :: (add_n_zero (yr - (xr + 1)).toNat xs)⟩
           else ⟨yr, ys.head y0 ::
            (add ⟨xr, xs⟩ ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩).v⟩
      else
    if rgt : yr < xr
      then if xnil : xs.tail = []
           then ⟨xr, xs.head x0 :: (add_n_zero (xr - (yr + 1)).toNat ys)⟩
           else ⟨xr, xs.head x0 ::
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
                else add_aux xr (xs.head x0 + ys.head y0)
                  (add ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩
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
    apply le_of_lt
    apply add_dec_aux y0
  apply Nat.add_lt_add_of_lt_of_le
  · apply add_dec_aux x0
  apply le_of_lt
  apply add_dec_aux y0

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
              · congr 3
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
                · congr 3
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

def add_auxv : ℤ → ℚ → RankList → List ℚ
  | r, x, ⟨yr, ys⟩ =>
    if y0 : ys = []
      then [x]
      else
    if rlt : r < yr
      then if ynil : ys.tail = []
           then ys.head y0 :: (add_n_zero (yr - (r + 1)).toNat [x])
           else ys.head y0 ::
            (add_auxv r x ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩)
      else
    if rgt : yr < r
      then x :: (add_n_zero (r - (yr + 1)).toNat ys)
      else
    if hhead : x + ys.head y0 = 0
      then if ynil : ys.tail = []
           then []
           else remLeadZero ys.tail
      else if ynil : ys.tail = []
           then [x + ys.head y0]
           else (x + ys.head y0) :: ys.tail
termination_by _ _ y => y.v.length
decreasing_by
  cases ys
  case nil => simp at y0
  case cons y ys =>
    simp!
    rw [Nat.lt_succ_iff]
    exact length_rlz ys

def add_auxr : ℤ → ℚ → RankList → ℤ
  | r, x, ⟨yr, ys⟩ =>
    if y0 : ys = [] then r else
    if rlt : r < yr then yr else
    if rgt : yr < r then r else
    if hhead : x + ys.head y0 = 0 then
      if ynil : ys.tail = [] then 0 else yr - (rlzCount ys.tail).succ
    else r

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
      else if xnil : xs.tail = []
           then xr
           else if ynil : ys.tail = []
                then xr
                else (add_auxr xr (xs.head x0 + ys.head y0)
                  (add ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩
                       ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩))
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
           then ys.head y0 :: (add_n_zero (yr - (xr + 1)).toNat xs)
           else ys.head y0 :: (addv ⟨xr, xs⟩ ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩)
      else
    if rgt : yr < xr
      then if xnil : xs.tail = []
           then xs.head x0 :: (add_n_zero (xr - (yr + 1)).toNat ys)
           else xs.head x0 ::
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
                else (add_auxv xr (xs.head x0 + ys.head y0)
                  (add ⟨xr - (rlzCount xs.tail).succ, remLeadZero xs.tail⟩
                       ⟨yr - (rlzCount ys.tail).succ, remLeadZero ys.tail⟩))
termination_by x y => x.v.length + y.v.length
decreasing_by
  · apply Nat.add_lt_add_of_le_of_lt
    · rfl
    apply add_dec_aux y0
  · apply Nat.add_lt_add_of_lt_of_le
    · apply add_dec_aux x0
    rfl
  apply Nat.add_lt_add_of_lt_of_le
  · apply add_dec_aux x0
  apply le_of_lt
  apply add_dec_aux y0

@[simp]
def odd : Option ℚ → Option ℚ → ℚ
  | none, none => 0
  | none, some y => y
  | some x, none => x
  | some x, some y => x + y

lemma odd_comm : ∀ x y, odd x y = odd y x := by
  intro x y ; cases x <;> cases y <;> simp_all! ; apply add_comm

-- lemma odd_assoc : ∀ x y z, odd (odd x)

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
    x * y :: (List.zipWithAll odd (List.map (x * ·) ys) (mulv xs (y :: ys)))
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
  x * y :: (List.zipWithAll odd (List.map (x * ·) ys) (mulv xs (y :: ys))) := by rw [mulv]

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

lemma zWA_l_le_r {α} : ∀ (x) (xs ys : List α) (f : Option α → Option α → α),
  (x :: xs).length ≤ ys.length →
  (List.zipWithAll f (x :: xs) ys).getLast? =
    some (f (if (x :: xs).length = ys.length then (x :: xs).getLast? else none) ys.getLast?) := by
  intro x xs ys f h
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
            List.zipWithAll_cons_cons,
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
      case cons y' ys =>
        rw [List.zipWithAll_cons_cons,
            List.zipWithAll,
            List.map_cons,
            List.getLast?_cons_cons,
            ←@List.map_cons _ _ (fun b ↦ f none (some b)),
            List.getLast?_cons_cons]
        induction ys generalizing y'
        case nil => simp
        case cons y'' ys ih =>
          specialize ih y'' _ _ _
          · simp
          · simp
          · simp
          rw [List.map_cons,
              List.map_cons,
              List.getLast?_cons_cons,
              ←@List.map_cons _ _ (fun b ↦ f none (some b)),
              ih,
              List.getLast?_cons_cons]
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
        rw [List.zipWithAll_cons_cons,
            List.getLast?_cons,
            ih,
            Option.getD_some]
        nth_rewrite 2 [List.getLast?_cons_cons]
        rfl

lemma roodd_assoc : ∀ x y z, ro odd x (ro odd y z) = ro odd (ro odd x y) z := by
  intro x y z ; cases x <;> cases y <;> cases z <;> simp_all! ; rw [add_assoc]

lemma mulv_rec_right {x xs y ys} : mulv (x :: xs) (y :: ys) =
    x * y :: (List.zipWithAll odd (List.map (y * ·) xs) (mulv (x :: xs) ys)) := by
  rw [listext?]
  intro i
  induction i generalizing x xs y ys
  case zero => simp [mulv]
  case succ i ih =>
    rw [mulv]
    simp!
    cases xs
    case nil =>
      simp! [mulv]
      rw [mulv_singleton, ro_comm odd_comm]
      congr
      rw [List.getElem?_map]
    case cons x' xs =>
      rw [@ih x' xs y ys]
      cases ys
      case nil =>
        simp!
        rw [ro_comm odd_comm]
        congr
        rw [id_comp]
        · rw [←List.getElem?_map,
              List.map_cons,
              mul_comm]
        rfl
      case cons y' ys =>
        nth_rewrite 2 [mulv]
        cases i
        case zero =>
          simp!
          rw [add_comm]
          congr 1
          rw [mul_comm]
        case succ i =>
          simp!
          rw [roodd_assoc]
          nth_rewrite 2 [ro_comm odd_comm]
          rw [←roodd_assoc]

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
              List.zipWithAll_nil,
              List.map_map,
              id_comp]
          · rw [←@List.map_cons,
                List.getLast?_map,
                oml_some_some,
                List.getLast?_cons_cons,
                List.getLast?_cons,
                Option.map_some,
                Option.some_inj]
            rfl
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
              zWA_l_le_r]
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

lemma mulv_assoc {xs ys zs} : mulv (mulv xs ys) zs = mulv xs (mulv ys zs) := by
  cases xs
  case nil => simp!
  case cons x xs =>
    cases ys
    case nil => simp!
    case cons y ys =>
      cases zs
      case nil => simp!
      case cons z zs =>
        rw [mulv, mulv, mulv, mulv, mul_assoc]
        congr 1
        grind
        rw [List.map_zipWithAll]
        rw [←@mulv_cons_cons x xs (y * z)]

lemma r_add_eq_addr_aux : ∀ r x y, (add_aux r x y).r = add_auxr r x y := by
  intro r x ⟨yr,ys⟩
  rw [add_aux, add_auxr]
  cases ys
  case nil => simp
  case cons y ys =>
    rw [decite_false]
    · cases @or_not (r < yr)
      case inl rlt =>
        rw [decite_true rlt]
        cases ys
        case nil =>
          rw [decite_true]
          · rw [decite_false,
                decite_true rlt]
            simp
          rfl
        case cons y' ys =>
          rw [decite_false]
          · rw [decite_false,
                decite_true rlt]
            simp
          simp
      case inr rlt =>
        rw [decite_false rlt]
        cases @or_not (yr < r)
        case inl rgt =>
          rw [decite_true rgt]
          rw [decite_false,
              decite_false rlt,
              decite_true rgt]
          simp
        case inr rgt =>
          rw [decite_false rgt]
          cases @or_not (x + y = 0)
          case inl hhead =>
            rw [decite_true]
            · cases ys
              case nil =>
                rw [decite_true]
                · rw [decite_false,
                      decite_false rlt,
                      decite_false rgt,
                      decite_true,
                      decite_true]
                  · rfl
                  · exact hhead
                  simp
                rfl
              case cons y' ys =>
                rw [decite_false]
                · rw [decite_false,
                      decite_false rlt,
                      decite_false rgt,
                      decite_true,
                      decite_false]
                  · simp
                  · exact hhead
                  simp
                simp
            exact hhead
          case inr hhead =>
            rw [decite_false]
            · cases ys
              case nil =>
                rw [decite_true]
                · rw [decite_false,
                      decite_false rlt,
                      decite_false rgt,
                      decite_false]
                  · exact hhead
                  simp
                rfl
              case cons y' ys =>
                rw [decite_false]
                · rw [decite_false,
                      decite_false rlt,
                      decite_false rgt,
                      decite_false]
                  · exact hhead
                  simp
                simp
            exact hhead
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
                          decite_false,
                          decite_true]
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
                      · apply r_add_eq_addr_aux
                      · simp
                      · simp
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

lemma v_add_eq_addv_aux {r x y} : (add_aux r x y).v = add_auxv r x y := by
  rcases y with ⟨yr,ys⟩
  rw [add_aux, add_auxv]
  cases ys
  case nil => simp
  case cons y ys =>
    rw [decite_false]
    · cases @or_not (r < yr)
      case inl rlt =>
        rw [decite_true rlt]
        cases ys
        case nil =>
          rw [decite_true]
          · rw [decite_false,
                decite_true rlt,
                decite_true]
            · rfl
            simp
          rfl
        case cons y' ys =>
          rw [decite_false]
          · rw [decite_false,
                decite_true rlt,
                decite_false]
            · simp!
              apply v_add_eq_addv_aux
            · simp
            simp
          simp
      case inr rlt =>
        rw [decite_false rlt]
        cases @or_not (yr < r)
        case inl rgt =>
          rw [decite_true rgt]
          rw [decite_false,
              decite_false rlt,
              decite_true rgt]
          simp
        case inr rgt =>
          rw [decite_false rgt]
          cases @or_not (x + y = 0)
          case inl hhead =>
            rw [decite_true]
            · cases ys
              case nil =>
                rw [decite_true]
                · rw [decite_false,
                      decite_false rlt,
                      decite_false rgt,
                      decite_true,
                      decite_true]
                  · rfl
                  · exact hhead
                  simp
                rfl
              case cons y' ys =>
                rw [decite_false]
                · rw [decite_false,
                      decite_false rlt,
                      decite_false rgt,
                      decite_true,
                      decite_false]
                  · simp
                  · exact hhead
                  simp
                simp
            exact hhead
          case inr hhead =>
            rw [decite_false]
            · cases ys
              case nil =>
                rw [decite_true]
                · rw [decite_false,
                      decite_false rlt,
                      decite_false rgt,
                      decite_false,
                      decite_true]
                  · rfl
                  · exact hhead
                  simp
                rfl
              case cons y' ys =>
                rw [decite_false]
                · rw [decite_false,
                      decite_false rlt,
                      decite_false rgt,
                      decite_false,
                      decite_false]
                  · simp
                  · exact hhead
                  simp
                simp
            exact hhead
    simp
termination_by y.v.length
decreasing_by
  case _ z _ _ _ _ _ a as _ _ =>
  cases @or_not (a = 0)
  case inl h =>
    rw [decide_true' h]
    apply Nat.lt_succ_of_le
    apply le_trans (length_rlz as)
    simp
  case inr h =>
    rw [decide_false' h]
    simp

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
                      · apply v_add_eq_addv_aux
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
  case _ d ds _ _ _ c cs _ _ _ _ _ _ _ _ _ b bs _ _ a as _ _ =>
  apply Nat.add_lt_add_of_le_of_lt
  · apply le_trans (length_rlz (b :: bs))
    simp
  apply Nat.lt_succ_of_le
  apply le_trans (length_rlz (a :: as))
  rfl

lemma mul_v_eq_nil {xr yr : ℤ} {xs ys : List ℚ} : (mul ⟨xr,xs⟩ ⟨yr,ys⟩).v = [] ↔ (xs = [] ∨ ys = []) := by
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

/-
lemma r_add_le_max {xr yr : ℤ} {xs ys : List ℚ} (xh : fluxh xr xs) (yh : fluxh yr ys) :
  (x0 : xs ≠ []) → (y0 : ys ≠ []) → (add ⟨xr,xs⟩ ⟨yr,ys⟩).r ≠ 0 → (add ⟨xr,xs⟩ ⟨yr,ys⟩).r ≤ max xr yr := by
  rw [r_add_eq_addr]
  cases xs
  case nil => simp
  case cons x xs =>
    cases ys
    case nil => simp
    case cons y ys =>
      intro hx hy add0
      rw [addr,
          decite_false hx,
          decite_false hy]
      apply decite (· ≤ max xr yr)
      · intro h0
        simp!
      intro h0
      simp! at h0
      rw [Int.max_comm, Int.max_def, decide_true' h0]
      apply decite (· ≤ xr)
      · intro h1
        rfl
      intro h1
      simp! at h1
      have h : yr = xr := by apply eq_of_le_of_ge h0 h1
      apply decite (· ≤ xr)
      · intro hhead
        simp! at hhead
        apply decite (· ≤ xr)
        · intro xnil
          apply decite (· ≤ xr)
          · intro ynil
            simp! at xnil ynil
            rw [xnil, ynil, h, addr] at add0
            simp! at add0
            apply add0.1 at hhead
            contradiction
          intro ynil
          rw [h]
          simp!
          apply Int.zero_le_ofNat
        intro xnil
        apply decite (· ≤ xr)
        · intro ynil
          simp!
          apply Int.zero_le_ofNat
        intro ynil
        simp!
        have hrec := r_add_le_max (fluxh_recurse xr x xs xnil xh) (fluxh_recurse yr y ys ynil yh)
        rw [r_add_eq_addr] at hrec
        apply le_trans (hrec _ _ _)
        · rw [h]
          simp!
          constructor
          · apply Int.zero_le_ofNat
          apply Int.zero_le_ofNat
        · sorry
        · sorry
        sorry
      intro hhead
      simp! at hhead
      apply decite (· ≤ xr)
      · intro xnil
        rfl
      intro xnil
      apply decite (· ≤ xr)
      · intro ynil
        rfl
      intro ynil
      rw [add_auxr]
      unfold fluxh at xh
      rw [List.head?_cons] at xh
      have h : x ≠ 0 := by
        have h := xh.2.1
        contrapose! h
        exact Option.some_inj.2 h
      rw [decite_false,
          decite_false,
          decite_true]
      · sorry
      ·
      rw [decide_false' h]
      simp! at xh

lemma r_add_eq_max_of_heads_not_inv {xr yr : ℤ} {xs ys : List ℚ} (xh : fluxh xr xs) (yh : fluxh yr ys) :
  (x0 : xs ≠ []) → (y0 : ys ≠ []) →
  xs.head x0 + ys.head y0 ≠ 0 → (add ⟨xr,xs⟩ ⟨yr,ys⟩).r = max xr yr := by
  rw [r_add_eq_addr]
  cases xs
  case nil => simp
  case cons x xs =>
    cases ys
    case nil => simp
    case cons y ys =>
      simp!
      intro h
      rw [addr,
          decite_false,
          decite_false]
      · apply decite (fun a ↦ a = max xr yr)
        · intro h0
          simp!
          apply le_of_lt h0
        intro h0
        simp! at h0
        rw [Int.max_comm, Int.max_def, decide_true' h0]
        apply decite (· = xr)
        · intro h1
          rfl
        intro h1
        apply decite (· = xr)
        · intro hhead
          simp! at hhead
          contradiction
        · intro hhead
          simp! at hhead
          apply decite (· = xr)
          · intro xnil
            rfl
          intro xnil
          apply decite (· = xr)
          · intro ynil
            rfl
          intro ynil
          rw [add_auxr]
          unfold fluxh at xh
          rw [List.head?_cons] at xh
          have h : x ≠ 0 := by
            have h := xh.2.1
            contrapose! h
            exact Option.some_inj.2 h
          rw [decite_false,
              decite_false,
              decite_true]
          · rw [add_r]
            · sorry
            · apply fluxh_recurse _ x _ xnil xh
            · apply fluxh_recurse _ y _ ynil yh
            · sorry
            · sorry
            simp!

          rw [decide_false' h]
          simp! at xh
        · simp
        simp

        /-
          apply decite (fun a : RankList ↦ a.r = yr)
          · intro h1
            cases ys
            case _ =>
              rw [decite_true]
              simp
            case _ y' ys =>
              rw [decite_false]
              simp
          intro h1
          rw [decite_false]
          · rw [decite_false]
            · cases xs
              case _ =>
                rw [decite_true]
                · cases ys
                  case _ =>
                    rw [decite_true]
                    · simp!
                      simp! at h1
                      apply eq_of_le_of_ge h0 h1
                    simp
                  case _ y' ys =>
                    rw [decite_false]
                    · simp!
                      simp! at h1
                      apply eq_of_le_of_ge h0 h1
                    simp
                simp
              case _ x' xs =>
                rw [decite_false]
                · cases ys
                  case _ =>
                    rw [decite_true]
                    · simp!
                      simp! at h1
                      apply eq_of_le_of_ge h0 h1
                    simp
                  case _ y' ys =>
                    rw [decite_false]
                    · simp only [List.head_cons,
                                 List.tail_cons,
                                 Nat.succ_eq_add_one,
                                 Nat.cast_add,
                                 Nat.cast_one]
                      simp! at h1
                      have h2 := eq_of_le_of_ge h0 h1
                      rw [add_aux]
                      apply decite (fun a : RankList ↦ a.r = yr)
                      · intro h3
                        simp!
                        exact h2
                      intro h3
                      rw [decite_false]
                      · rw [decite_true]
                        · simp!
                          exact h2
                        cases @or_not (x' = 0 ∨ y' = 0 ∨ x' + y' = 0)
                        case _ h =>
                          rw [add_r]
                          · simp!
                            constructor
                            · cases @or_not (x' = 0)
                              case _ hx =>
                                rw [decide_true' hx]
                                apply Int.ofNat_lt_ofNat_of_lt
                                simp
                              case _ hx =>
                                rw [decide_false' hx]
                                simp
                            cases @or_not (y' = 0)
                            case _ hy =>
                              rw [decide_true' hy, h2]
                              simp!
                              apply Int.ofNat_lt_ofNat_of_lt
                              simp
                            case _ hx =>
                              rw [decide_false' hx, h2]
                              simp
                          · apply fluxh_recurse _ x _ (by simp) xh
                          · apply fluxh_recurse _ y _ (by simp) yh
                          · rw [rlz_ne_nil]
                            · simp
                            rcases xh with ⟨hx0,hx1,hx2⟩
                            rw [List.getLast?_cons_cons] at hx2
                            exact hx2
                          · rw [rlz_ne_nil]
                            · simp
                            rcases yh with ⟨hy0,hy1,hy2⟩
                            rw [List.getLast?_cons_cons] at hy2
                            exact hy2
                          cases h
                          case _ h =>
                            simp! at h3
                            rw [decide_true' h, decide_true' h] at h3
                        case _ h =>
                          simp! at h
                          rcases h with ⟨hx,hy,hxy⟩
                          rw [add_r]
                          · simp
                            rw [h2,
                                ←add_zero yr,
                                Int.sub_eq_add_neg,
                                add_assoc]
                            apply Int.add_lt_add_left _ yr
                            rw [←Int.natCast_one,
                                ←Int.natCast_add]
                            apply Int.negSucc_lt_zero
                          · rw [remLeadZero,
                                decide_false' hx]
                            simp
                          · rw [remLeadZero,
                                decide_false' hy]
                            simp
                          contrapose! hxy
                          rw [←hxy]
                          congr
                          · rw [List.head_of_head?_eq_some]
                            rw [remLeadZero,
                                decide_false' hx]
                            simp
                          rw [List.head_of_head?_eq_some]
                          rw [remLeadZero,
                              decide_false' hy]
                          simp
                      simp
                      cases @or_not (x' = 0 ∨ y' = 0 ∨ x' + y' = 0)
                      case _ h => sorry
                      case _ h =>
                        simp! at h
                        rcases h with ⟨hx,hy,hxy⟩
                        rw [add_r]
                        · simp
                          constructor
                          · rw [←Int.natCast_one,
                                ←Int.natCast_add]
                            apply Int.zero_le_ofNat
                          rw [h2,
                              ←add_zero yr,
                              add_assoc]
                          apply Int.add_le_add_left
                          rw [←Int.natCast_one,
                              ←Int.natCast_add]
                          apply Int.zero_le_ofNat
                        · rw [remLeadZero,
                              decide_false' hx]
                          simp
                        · rw [remLeadZero,
                              decide_false' hy]
                          simp
                        contrapose! hxy
                        rw [←hxy]
                        congr
                        · rw [List.head_of_head?_eq_some]
                          rw [remLeadZero,
                              decide_false' hx]
                          simp
                        rw [List.head_of_head?_eq_some]
                        rw [remLeadZero,
                            decide_false' hy]
                        simp
                    simp
                simp
            simp!
            exact h
          simp!
          exact h0
        intro h0
        simp! at h0
        rw [decite_false]
        · rw [decite_true h0]
          cases xs
          case _ =>
            rw [decite_true]
            simp
          case _ x' xs =>
            rw [decite_false]
            simp
        simp!
        apply le_of_lt h0
      · simp
      simp-/

lemma mul_r {xr yr : ℤ} {xs ys : List ℚ} :
  xs ≠ [] → ys ≠ [] → (mul ⟨xr,xs⟩ ⟨yr,ys⟩).r = xr + yr := by
  cases xs <;> cases ys <;> simp_all [mul]
-/

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

lemma add_auxh (xr yr : ℤ) (x : ℚ) (ys : List ℚ) (xh : fluxh xr [x]) (yh : fluxh yr ys) :
  ((RankList.add_aux xr x ⟨yr, ys⟩).v = [] →
   (RankList.add_aux xr x ⟨yr, ys⟩).r = 0) ∧
   (RankList.add_aux xr x ⟨yr, ys⟩).v.head? ≠ some 0 ∧
   (RankList.add_aux xr x ⟨yr, ys⟩).v.getLast? ≠ some 0 := by
  unfold fluxh at xh yh
  rw [RankList.add_aux]
  cases ys
  case nil =>
    rw [decite_true]
    · simp!
      simp! at xh
      exact xh
    rfl
  case cons y ys =>
    rw [decite_false]
    · cases @or_not (xr < yr)
      case inl rlt =>
        rw [decite_true rlt]
        cases ys
        case nil =>
          rw [decite_true]
          · simp
            simp at yh
            constructor
            · exact yh
            rw [List.getLast?_cons]
            simp
            rw [RankList.add_n_zero_getLast?_of_ne_nil]
            · simp!
              simp! at xh
              exact xh
            simp
          simp
        case cons y' ys =>
          rw [decite_false]
          · simp
            constructor
            · simp at yh
              exact yh.1
            simp at yh
            cases @or_not (y' = 0)
            case inl hy =>
              rw [RankList.remLeadZero,
                  RankList.rlzCount,
                  decide_true' hy,
                  decide_true' hy]
              have h := (add_auxh xr (yr - (↑(RankList.rlzCount ys) + 1 + 1)) x (RankList.remLeadZero ys) xh (by
                apply RankList.fluxh_recurse yr y (0 :: ys)
                · simp
                rw [←hy]
                unfold fluxh
                simp
                exact yh
                )).2.2
              rw [List.getLast?_cons]
              simp!
              apply getD_decide (· ≠ 0)
              · intro z hz
                contrapose! hz
                rw [hz]
                exact h
              intro h0
              exact yh.1
            case inr hy =>
              rw [RankList.remLeadZero,
                  RankList.rlzCount,
                  decide_false' hy,
                  decide_false' hy]
              simp
              have h := (add_auxh xr (yr - 1) x (y' :: ys) xh (by
                have h0 := RankList.fluxh_recurse yr y (y' :: ys) (by simp) (by
                  unfold fluxh
                  simp
                  exact yh
                  )
                simp at h0
                rw [RankList.remLeadZero,
                    RankList.rlzCount,
                    decide_false' hy,
                    decide_false' hy] at h0
                exact h0
                )).2.2
              rw [List.getLast?_cons]
              simp!
              apply getD_decide (· ≠ 0)
              · intro z hz
                contrapose! hz
                rw [hz]
                exact h
              intro h0
              exact yh.1
          simp
      case inr hlt =>
        rw [decite_false hlt]
        cases @or_not (yr < xr)
        case inl rgt =>
          rw [decite_true rgt]
          simp
          simp at xh
          constructor
          · exact xh
          simp at yh
          rw [List.getLast?_cons]
          simp!
          apply getD_decide (· ≠ 0)
          · intro z hz
            contrapose! hz
            rw [hz, RankList.add_n_zero_getLast?_of_ne_nil]
            · exact yh.2
            simp
          intro hn
          exact xh
        case inr rgt =>
          rw [decite_false rgt]
          cases @or_not (x + y = 0)
          case inl hhead =>
            rw [decite_true]
            · cases ys
              case nil =>
                rw [decite_true]
                · simp
                simp
              case cons y' ys =>
                rw [decite_false]
                · simp
                  cases @or_not (y' = 0)
                  case inl hy =>
                    rw [RankList.remLeadZero,
                        RankList.rlzCount,
                        decide_true' hy,
                        decide_true' hy]
                    constructor
                    · intro h
                      contrapose! h
                      induction ys generalizing y' yr xr
                      case nil =>
                        simp! at yh
                        apply yh.2 at hy
                        simp at hy
                      case cons y'' ys ih =>
                        simp at h yh
                        cases @or_not (y'' = 0)
                        case inl hy' =>
                          simp
                          rw [RankList.remLeadZero,
                              decide_true' hy']
                          apply ih (xr - 1) (yr - 1) _ _ _ y''
                          · simp
                            exact yh
                          · exact hy'
                          · rw [RankList.rlzCount,
                                decide_true' hy'] at h
                            simp
                            rw [Int.sub_sub, add_comm]
                            exact h
                          · simp!
                            simp! at xh
                            exact xh
                          · simp!
                            simp! at hlt
                            exact hlt
                          simp!
                          simp! at rgt
                          exact rgt
                        case inr hy' =>
                          simp
                          rw [RankList.remLeadZero,
                              decide_false' hy']
                          simp
                    constructor
                    · apply RankList.head?_rlz
                    cases RankList.getLast?_rlz ys
                    case inl h =>
                      rw [h]
                      cases ys
                      case nil => simp
                      case cons y'' ys =>
                        simp at yh
                        exact yh.2
                    case inr h =>
                      rw [h]
                      simp
                  case inr hy =>
                    rw [RankList.remLeadZero,
                        RankList.rlzCount,
                        decide_false' hy]
                    simp!
                    simp! at yh
                    constructor
                    · exact hy
                    exact yh.2
                simp
            exact hhead
          case inr hhead =>
            rw [decite_false]
            · cases ys
              case nil =>
                rw [decite_true]
                · simp
                  exact hhead
                simp
              case cons y' ys =>
                rw [decite_false]
                · simp
                  constructor
                  · exact hhead
                  simp at yh
                  exact yh.2
                simp
            exact hhead
    simp
termination_by ys.length
decreasing_by
  · case _ k ks hy _ _ _ z zs hk _ _ =>
    rw [hy, hk]
    simp!
    rw [Nat.lt_succ_iff]
    apply le_trans (RankList.length_rlz zs)
    simp
  case _ k ks hy _ _ _ z zs hk _ _ =>
  rw [hy, hk]
  simp

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
                rw [hz] at h
                exact h
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
                      · simp!
                        apply add_auxh
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
              id_comp (by rfl),
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
            rw [id_comp (by rfl),
                List.getLast?_cons,
                List.getLast?_map]
            simp
            constructor
            · exact xh.1
            rw [List.getLast?_cons_cons,
                List.getLast?_cons,
                Option.some_inj] at yh
            exact yh.2
          case cons x' xs =>
            rw [RankList.zWA_l_le_r]
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
                  decite_false,
                  decite_false,
                  decite_true,
                  decite_true]
              · simp!
                constructor
                · apply add_comm
                constructor
                · apply mul_comm
                ring_nf
                rfl
              · simp
              · simp
              · simp
              · simp
              simp
            case cons y'' ys =>
              simp!

theorem only_singletons_invertible {x : Fluxion} : (∃ y, x * y = 1) ↔ x.f.v.length = 1 := by
  rcases x with ⟨xr,xs⟩
  cases xs
  case nil => simp!
  case cons x xs =>
    constructor
    · intro h
      rcases h with ⟨⟨yr,ys⟩,h⟩
      cases xs
      case nil => simp!
      case cons x' xs =>
        cases ys
        case nil => simp! at h
        case cons y ys =>
          simp! at h
          have h0 := (@length_congr ℚ (mulv (x :: x' :: xs) (y :: ys)) [1])
          contrapose! h0
          constructor
          · exact h.2
          rw [length_mulv]
          · simp!
            ring_nf
            rw [add_comm 2, add_assoc, add_comm 2, ←add_assoc]
            apply Nat.succ_succ_ne_one
          · simp
          simp
    intro h
    use ⟨-xr,[1 / x]⟩
    cases xs
    case cons x' xs => simp! at h
    case nil =>
      simp! [mulv]
      rw [mul_inv_cancel x]

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
      exact mulv_assoc


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
