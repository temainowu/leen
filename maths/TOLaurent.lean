import Mathlib

class KindaDivRing α extends Ring α
  where
  div : α → α → Option α
  invertible : α → Prop
  div? : (x y : α) → (h : invertible y) → α
  coe : ℕ → α
  invertible_iff_can_div : ∀ x y, invertible y ↔ div x y ≠ none
  can_div_n : ∀ (n : ℕ), n ≠ 0 → invertible (coe n)
  qsmul (q : ℚ) (x : α) : α :=
    div? (zsmul q.num x) (coe q.den) (can_div_n q.den q.3)

-- Generic Useful Functions (probably already exist)

@[simp]
def l {α β} (x : α) : β → α := fun _ => x

-- @[simp]
-- def head' : List ℚ → Option ℚ := (fun x => if x = some 0 then none else x) ∘ List.head?

theorem dich : ∀ q : ℚ, q = 0 ∨ q ≠ 0 := by grind

theorem dich_prop : ∀ p : Prop, p ∨ ¬p := by grind

theorem trich_lt : ∀ a b : ℕ, a < b ∨ b < a ∨ a = b := by grind

@[simp]
def zipWith' {α β} [Zero α] (f : α → α → β) (a : List α) (b : List α) : List β :=
  match (generalizing := true) a, b with
    | [], [] => []
    | x :: xs, [] => f x 0 :: zipWith' f xs []
    | [], y :: ys => f 0 y :: zipWith' f [] ys
    | x :: xs, y :: ys => f x y :: zipWith' f xs ys
termination_by a.length + b.length

@[simp]
def zipWith0 {α β} [Zero α] (f : α → α → β) (a : List α) (b : List α) : List β :=
  a.zipWithAll (fun x y => f (x.getD 0) (y.getD 0)) b

theorem zipWith0_nil_eq_map_left {α β} [Zero α] : ∀ (f : α → α → β) (ys : List α),
    zipWith0 f [] ys = ys.map (f 0) := by simp!

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


theorem zipwitheq : ∀ (f : ℚ → ℚ → ℚ) (xs ys : List ℚ),
    zipWith' f xs ys = zipWith0 f xs ys := by
  intro f xs ys
  induction xs generalizing ys
  case nil =>
    induction ys
    case nil =>
      simp!
    case cons y ys ih =>
      simp!
      rw [ih]
      simp!
  case cons x xs ih =>
    cases ys
    case nil =>
      specialize ih []
      simp!
      rw [ih]
      simp!
    case cons y ys =>
      specialize ih ys
      simp!
      rw [ih]
      simp!

theorem zipwith_empty_iff_both_empty {α β} [Zero α] :
  ∀ (f : α → α → β) (xs ys : List α),
    xs = [] ∧ ys = [] ↔ zipWith0 f xs ys = [] := by
  intro f xs ys
  constructor
  · intro h
    rw [h.1, h.2]
    simp
  intro h
  cases xs
  case nil =>
    cases ys
    case nil => simp
    case cons y ys => simp at h
  case cons x xs =>
    cases ys
    case nil => simp at h
    case cons => simp at h

@[ext]
structure Fluxion where
  r : ℕ
  v : List ℚ
  l0_of_r0 : v.head?.getD 0 = 0 → r = 0
  no_trail : v.getLast? ≠ some 0

namespace Fluxion

@[simp]
instance : Zero Fluxion := ⟨0, [], by simp, by simp⟩

instance : Coe ℚ Fluxion where
  coe x := if h : x = 0 then 0 else ⟨0,[x], by simp, by
              simp!
              exact h⟩

@[simp]
instance : Coe ℕ Fluxion where
  coe x := if h : x = 0 then 0 else ⟨0,[↑x], by simp, by
              simp!
              exact h⟩

theorem coe_nat.eq_def : ∀ n : ℕ, (↑n : Fluxion) = if h : n = 0 then 0 else ⟨0,[↑n], by simp, by
              simp!
              exact h⟩ := by
                intro n
                rfl

theorem v_coe_nat : ∀ n : ℕ, n ≠ 0 → (↑n : Fluxion).v = [↑n] := by
  intro n h
  grind

@[simp]
theorem zero_v : (0 : Fluxion).v = [] := by rfl

@[simp]
theorem zero_r : (0 : Fluxion).r = 0 := by rfl

theorem zero_def : (0 : Fluxion) = ⟨0,[],by simp!, by simp!⟩ := by congr

theorem zero_iff_nil : ∀ x : Fluxion, x.v = [] ↔ x = 0 := by
  intro x
  constructor
  · intro h
    rcases x with ⟨r,v,lr,nt⟩
    congr
    apply lr
    simp! at h
    rw [h]
    simp!
  intro h
  rw [h]
  simp!

@[simp]
theorem is_zero {r lr nt} : (⟨r,[],lr,nt⟩ : Fluxion) = 0 := by
  rw [(zero_iff_nil ⟨r,[],lr,nt⟩).1 (by rfl)]

@[simp]
def remove_leading_zeros (z : List ℚ) : List ℚ :=
  match (generalizing := true) z with
  | [] => []
  | x :: xs => if x = 0 then remove_leading_zeros xs else x :: xs

@[simp]
def remove_trailing_zeros (xs : List ℚ) : List ℚ := (remove_leading_zeros xs.reverse).reverse

theorem getlast_rtz : ∀ xs, (remove_trailing_zeros xs).getLast? ≠ some 0 := by
  intro xs
  simp!
  induction xs.reverse
  case nil => simp
  case cons x xs ih =>
    simp!
    cases dich x
    case inl h =>
      rw [h]
      simp!
      exact ih
    case inr h => grind

theorem head_remains_rtz : ∀ x xs, x ≠ 0 → (remove_trailing_zeros (x :: xs)).head? = some x := by
  intro x xs h
  simp!
  induction xs.reverse
  case nil =>
    simp
    grind
  case cons x' xs' ih =>
    simp!
    grind

@[simp]
def normalise : ℕ × List ℚ → Fluxion
  | ⟨_, []⟩ => 0
  | ⟨0, xs⟩ => ⟨0, remove_trailing_zeros xs, by simp, by exact getlast_rtz xs⟩
  | ⟨Nat.succ n, x :: xs⟩ => if h : x = 0
                             then normalise ⟨n,xs⟩
                             else ⟨Nat.succ n, remove_trailing_zeros (x :: xs), by
    intro h0
    contrapose! h0
    have h1 := head_remains_rtz x xs h
    rw [h1]
    simp!
    exact h
    , by exact getlast_rtz (x :: xs)⟩

instance : Coe (ℕ × List ℚ) Fluxion where
  coe := normalise

@[simp]
def le_aux : List ℚ → List ℚ → Prop
  | [], [] => True
  | [], y::ys => (y = 0 ∧ le_aux [] ys) ∨ 0 < y
  | x::xs, [] => (x = 0 ∧ le_aux xs []) ∨ x < 0
  | x::xs, y::ys => (x = y ∧ le_aux xs ys) ∨ x < y
termination_by x y => x.length + y.length

@[simp]
def lt_aux : List ℚ → List ℚ → Prop
  | [], [] => False
  | [], y::ys => lt_aux [] ys ∨ 0 < y
  | x::xs, [] => lt_aux xs [] ∨ x < 0
  | x::xs, y::ys => (x = y ∧ lt_aux xs ys) ∨ x < y
termination_by x y => x.length + y.length

@[simp]
def sign : Option ℚ → ℤ
  | none => 0
  | some x => if 0 < x then  1 else
              if x < 0 then -1 else 0

@[simp]
def bigness : Fluxion → ℤ
  | ⟨r,v,_,_⟩ => (↑r) * sign (v.head?)

@[simp]
instance : LE Fluxion where
  le x y := (x.r = y.r ∧ le_aux x.v y.v) ∨ (bigness x < bigness y)

@[simp]
instance : LT Fluxion where
  lt x y := (x.r = y.r ∧ lt_aux x.v y.v) ∨ (bigness x < bigness y)

@[simp]
def app_end {α} : List α → α → List α
  | [], a => [a]
  | x :: xs, a => x :: app_end xs a

theorem app_end_neq {α} : ∀ (xs : List α) (a : α), xs ≠ app_end xs a := by
  intro xs a
  induction xs
  · simp
  case cons x xs ih =>
    simp!
    exact ih

theorem app_end_nempty {α} : ∀ (xs : List α) (a : α), [] ≠ app_end xs a := by
  intro xs a
  cases xs
  case nil => simp
  case cons x xs => simp

theorem app_end_getLast? {α} : ∀ (xs : List α) (a : α), (app_end xs a).getLast? = some a := by
  intro xs a
  induction xs
  case nil => simp
  case cons x xs ih =>
    rw [app_end, List.getLast?_cons, ih]
    simp

theorem app_end_head?_nil {α} : ∀ (xs : List α) (a : α), xs = [] →
  (app_end xs a).head? = some a := by
  intro xs a h
  rw [h]
  simp

theorem app_end_head?_cons {α} : ∀ (xs zs : List α) (a z : α) , xs = z :: zs →
  (app_end xs a).head? = some z := by
  intro xs zs a z h
  rw [h]
  simp

theorem x_lt_app_end_x : ∀ (xs : List ℚ) (a : ℚ), 0 < a → lt_aux xs (app_end xs a) := by
  intro xs a ha
  induction xs
  · simp!
    exact ha
  case cons x xs ih =>
    simp!
    exact ih

-- instance : linear_ordered_field Fluxion where

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

theorem add_n_zero_getLast?_0 : ∀ xs, (add_n_zero 0 xs).getLast? = xs.getLast? := by simp!

theorem add_n_zero_getLast?_succ :
    ∀ n xs, xs ≠ [] → (add_n_zero (n+1) xs).getLast? = xs.getLast? := by
  intro n xs hxs
  rw [add_n_zero, List.getLast?_cons, add_n_zero_getLast?]
  cases xs
  case nil => simp! at hxs
  case cons => simp!

theorem lt_of_add_eq : ∀ n m : ℕ, n < m → ∃ c : ℕ, 0 < c ∧ n + c = m := by
  intro n m h
  use (m-n)
  grind

theorem decide_true {α p} [Decidable p] : p → ∀ t e : α, (if p then t else e) = t := by grind

theorem decide_true' {α p} [Decidable p] :
  ∀ (h : p) (t : p → α) (e : ¬p → α), (if h0 : p then t h0 else e h0) = t h := by grind

theorem decide_false {α p} [Decidable p] : ¬p → ∀ t e : α, (if p then t else e) = e := by grind

theorem decide_false' {α p} [Decidable p] :
  ∀ (h : ¬p) (t : p → α) (e : ¬p → α), (if h0 : p then t h0 else e h0) = e h := by grind

/-
theorem decite {α p} [Decidable p] : ∀ (f : α → Prop),
  (p ∨ ¬p) → ∀ t e : α,
  ((p ∧ f t) ∨ (¬p ∧ f e)) →
  f (if _ : p then t else e) := by grind

theorem dite_f {α p} [Decidable p] {x : p → α} {y : ¬p → α} :
  ∀  (f : α → Prop),
  ((∀ h : p, f (x h)) ∧ (∀ h : ¬p, f (y h))) → f (if h : p then x h else y h) := by grind

theorem appl_ite {α β p} {t e : α} [Decidable p] :
  ∀ f : α → β, f (if p then t else e) = if p then f t else f e := by grind

theorem appl_dite {α β p} {t : p → α} {e : ¬p → α} [Decidable p] :
  ∀ f : α → β, f (if h : p then t h else e h) = if h : p then f (t h) else f (e h) := by grind
-/

theorem normalise_dec_rank {n} : ∀ r v, r < n → (normalise (r, v)).r < n := by
    intro r v hr
    induction v generalizing r
    case nil =>
      simp!
      grind
    case cons x xs ih =>
      cases r
      case zero =>
        simp!
        exact hr
      case succ r =>
        simp!
        cases dich x
        case inl hx =>
          rw [decide_true' hx]
          grind
        case inr hx =>
          rw [decide_false' hx]
          simp!
          exact hr

/-
@[simp]
def add : Fluxion → Fluxion → Fluxion
  | ⟨_,[],_,_⟩, ⟨_,[],_,_⟩ => 0
  | x, ⟨_,[],_,_⟩  => x
  | ⟨_,[],_,_⟩, y  => y
  | ⟨xr,x :: xs ,xlr,xnt⟩, ⟨yr,y :: ys ,ylr,ynt⟩  =>
      if xr < yr
      then normalise ⟨yr, (zipWith0 (· + ·) (add_n_zero (yr-xr) (x :: xs)) (y :: ys))⟩
      else if xr > yr
           then add ⟨yr,y :: ys ,ylr,ynt⟩ ⟨xr,x :: xs ,xlr,xnt⟩
           else normalise ⟨xr, (zipWith0 (· + ·) (x :: xs) (y :: ys))⟩
termination_by z => z.r
decreasing_by grind
-/

@[simp]
def add (x y : Fluxion) : Fluxion :=
  match x.v, y.v with
  | [], [] => 0
  | _, []  => x
  | [], _  => y
  | _ :: _, _ :: _ =>
      if h : x.r < y.r
      then normalise ⟨y.r, zipWith0 (· + ·) (add_n_zero (y.r-x.r) x.v) y.v⟩
      else if y.r < x.r
           then add y x
           else normalise ⟨x.r, zipWith0 (· + ·) x.v y.v⟩
termination_by x.r
decreasing_by grind

/-
@[simp]
def add' (x y : Fluxion) : Fluxion :=
  if hx : x.v = [] then y else if hy : y.v = [] then x else
  if y.r = 0 then add' y x else
  if x.r = y.r then
    if hxy : x.v.head hx = - (y.v.head hy)
         then add'
          ⟨x.r-1, remove_leading_zeros x.v.tail, by sorry, by sorry⟩
          ⟨y.r-1, remove_leading_zeros y.v.tail, by sorry, by sorry⟩
         else if x.v.length = y.v.length ∧ x.v.getLast (hx) = - (y.v.getLast (hy))
              then add'
                ⟨x.r-1, (remove_leading_zeros x.v.reverse.tail).reverse, by sorry, by sorry⟩
                ⟨y.r-1, (remove_leading_zeros y.v.reverse.tail).reverse, by sorry, by sorry⟩
              else ⟨y.r, (add_n_zero (y.r-x.r) x.v).zipWithAll
                          (fun x y => x.getD 0 + y.getD 0) y.v , by sorry, by sorry⟩
  else
    if hxy : x.v.head hx = - (y.v.head hy)
         then add'
          ⟨x.r-1, remove_leading_zeros x.v.tail, by sorry, by sorry⟩
          ⟨y.r-1, remove_leading_zeros y.v.tail, by sorry, by sorry⟩
         else if x.v.length = y.v.length ∧ x.v.getLast (hx) = - (y.v.getLast (hy))
              then add'
                ⟨x.r-1, (remove_leading_zeros x.v.reverse.tail).reverse, by sorry, by sorry⟩
                ⟨y.r-1, (remove_leading_zeros y.v.reverse.tail).reverse, by sorry, by sorry⟩
              else ⟨y.r, (add_n_zero (y.r-x.r) x.v).zipWithAll
                          (fun x y => x.getD 0 + y.getD 0) y.v , by sorry, by sorry⟩
-/

@[simp]
def neg : Fluxion → Fluxion
  | ⟨r,v,lr,nt⟩ => ⟨r, (- ·) <$> v, by
      intro h
      apply lr
      cases v
      case nil => simp!
      case cons =>
        simp! at *
        exact h
    , by
      simp!
      exact nt
    ⟩

@[simp]
instance : Add Fluxion where
  add := add

theorem add_def : ∀ x y : Fluxion, x + y = add x y := by
  intro x y
  rfl

@[simp]
instance : Neg Fluxion where
  neg := neg

@[simp]
theorem neg_zero_eq_zero : (-(0 : Fluxion)) = 0 := by rfl

@[simp]
theorem zero_add : ∀ a : Fluxion, 0 + a = a := by
  intro a
  rcases a with ⟨r,v,lr,nt⟩
  cases v
  case nil =>
    rw [add_def, add]
    simp!
  case cons =>
    rw [add_def]
    simp!

@[simp]
theorem add_zero : ∀ a : Fluxion, a + 0 = a := by
  intro a
  rcases a with ⟨r,v,lr,nt⟩
  cases v
  case nil =>
    rw [add_def, add]
    simp!
  case cons =>
    rw [add_def]
    simp!

theorem add_lt : ∀ x y : Fluxion, x.v≠[] → y.v≠[] → x.r < y.r →
  x + y = normalise ⟨y.r, (zipWith0 (· + ·) (add_n_zero (y.r-x.r) x.v) y.v)⟩ := by
    intro x y hx hy hr
    rcases x with ⟨xr,xs,xlr,xnt⟩
    rcases y with ⟨yr,ys,ylr,ynt⟩
    cases xs
    case nil =>
      contrapose! hx
      congr
    case cons x xs =>
      cases ys
      case nil =>
        contrapose! hy
        congr
      case cons y ys =>
        simp! at hr
        rw [add_def, add]
        dsimp
        rw [decide_true hr]

theorem add_gt : ∀ x y : Fluxion, x.v≠[] → y.v≠[] → x.r > y.r →
  x + y = normalise ⟨x.r, (zipWith0 (· + ·) (add_n_zero (x.r-y.r) y.v) x.v)⟩ := by
    intro x y hx hy hr
    rcases x with ⟨xr,xs,xlr,xnt⟩
    rcases y with ⟨yr,ys,ylr,ynt⟩
    cases xs
    case nil =>
      contrapose! hx
      congr
    case cons x xs =>
      cases ys
      case nil =>
        contrapose! hy
        congr
      case cons y ys =>
        simp! at hr
        rw [add_def, add]
        dsimp
        rw [decide_true hr, decide_false (by grind), add]
        dsimp
        rw [decide_true hr]

theorem add_eq : ∀ x y : Fluxion, x.v≠[] → y.v≠[] → x.r = y.r →
  x + y = normalise ⟨x.r, (zipWith0 (· + ·) x.v y.v)⟩ := by
    intro x y hx hy hr
    rcases x with ⟨xr,xs,xlr,xnt⟩
    rcases y with ⟨yr,ys,ylr,ynt⟩
    cases xs
    case nil =>
      contrapose! hx
      congr
    case cons x xs =>
      cases ys
      case nil =>
        contrapose! hy
        congr
      case cons y ys =>
        rw [add_def, add]
        dsimp
        rw [decide_false (by grind), decide_false (by grind)]

theorem add_assoc : ∀ (a b c : Fluxion), a + b + c = a + (b + c) := by
  intro a b c
  rcases a with ⟨ar,av,alr,ant⟩
  rcases b with ⟨br,bv,blr,bnt⟩
  rcases c with ⟨cr,cv,clr,cnt⟩
  cases av
  case nil =>
    cases bv
    case nil =>
      cases cv
      case nil =>
        rw [add_def]
        simp!
      case cons => simp!
    case cons b bs =>
      cases cv
      case nil => simp!
      case cons c cs =>
        rw [(zero_iff_nil (mk ar [] alr ant)).1 (by rfl), zero_add, zero_add]
  case cons a as =>
    cases bv
    case nil =>
      cases cv
      case nil => simp!
      case cons c cs =>
        rw [(zero_iff_nil (mk br [] blr bnt)).1 (by rfl), zero_add, add_zero]
    case cons b bs =>
      cases cv
      case nil =>
        rw [(zero_iff_nil (mk cr [] clr cnt)).1 (by rfl), add_zero, add_zero]
      case cons c cs =>
        have tab := trich_lt ar br
        have tbc := trich_lt br cr
        cases tab
        case inl tab =>
          rw [add_lt ⟨ar,a::as,alr,ant⟩ ⟨br,b::bs,blr,bnt⟩ (by grind) (by grind) tab]
          cases tbc
          case inl tbc =>
            rw [add_lt ⟨br,b::bs,blr,bnt⟩ ⟨cr,c::cs,clr,cnt⟩ (by grind) (by grind) tbc]
            sorry
          case inr tbc => sorry
        case inr tab => sorry

/-
theorem a : ∀ r xs,  normalise (r, 0 :: xs) = normalise (r, xs) := by
  intro r xs
  induction xs
  case nil =>
    simp!
    cases r
    · simp!
    simp!
  case cons x xs ih =>
    cases r
    case zero =>
      simp! at *

    case succ r =>
      simp!



theorem norm_empty : ∀ x, (normalise x).v = [] ↔ List.foldr (· ∧ ·) (True) ((0 = ·) <$> x.2) := by
  intro x
  rcases x with ⟨r,xs⟩
  constructor
  · intro h
    induction xs
    case nil => simp!
    case cons x xs ih =>
      simp!
      constructor
      · sorry
      simp! at ih
      apply ih
      rw [←h, normalise.eq_def]
      cases xs
      case nil =>
        simp!
        exact h
      case cons x0 xs =>
        sorry
  intro h
  induction xs
  case nil => simp!
  case cons x xs ih =>
    simp! at h
    rw [←h.1]
-/

@[simp]
def cart : List ℚ → List ℚ → List (List (ℚ×ℚ))
  | [], _ => []
  | _, [] => []
  | x :: xs, ys => ys.map (fun a => (x,a)) :: cart xs ys

@[simp]
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

#eval add_fold [[0,0,0],[2,4,10],[3,6,15]] (by
  use 3
  intro i hxs
  cases i
  case zero => simp!
  case succ i =>
  cases i
  case zero => simp!
  case succ i =>
  cases i
  case zero => simp!
  case succ i => grind
)

theorem length_recursive_list_f {α β} :
    ∀ (f : List α → List β),
      f [] = [] →
      (∃ g : α → β, ∀ (x : α) (xs : List α), f (x :: xs) = g x :: f xs) →
      ∀ xs, (f xs).length = xs.length := by
  intro f hn hc xs
  induction xs
  case nil =>
    rw [hn]
    rfl
  case cons x xs ih =>
    rcases hc with ⟨g,hc⟩
    specialize hc x xs
    rw [hc, List.length_cons, ih]
    rfl

@[simp]
theorem length_getElem_cart : ∀ xs ys i (h : i < (cart xs ys).length),
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

@[simp]
def list_prod (x y : List ℚ) : List ℚ :=
  add_fold (List.map (List.map (fun (x, y) => x * y)) (cart x y)) (by
    use y.length
    intro i hxs
    rw [List.getElem_map, List.length_map, length_getElem_cart])

#eval list_prod [2,3] [1,2,5]

@[simp]
def my_length : List ℚ → ℕ
  | [] => 0
  | x :: xs => if x = 0 then my_length xs else 1 + my_length xs

theorem my_len_le_len : ∀ xs, my_length xs ≤ xs.length := by
  intro xs
  induction xs
  case nil => simp!
  case cons x xs ih =>
    simp!
    cases dich x
    case inl h =>
      rw [decide_true h]
      apply le_trans ih
      simp!
    case inr h =>
      rw [decide_false h, add_comm]
      apply add_le_add_left
      exact ih

theorem Int.add_le {a b : ℤ} : a ≤ 0 → b ≤ 0 → a + b ≤ 0 := by
  intro ha hb
  induction a
  case zero =>
    simp!
    exact hb
  case succ a ih =>
    grind
  case pred a ih =>
    grind

@[simp]
def option_fold {α} : Option (Option α) → Option α
  | none => none
  | some none => none
  | some (some x) => some x

@[simp]
theorem option_fold_some {α} : ∀ x : Option α, option_fold (some x) = x := by
  intro x
  cases x
  case none => simp!
  case some x => simp!

theorem cart_getLast? : ∀ xs ys, (list_prod xs ys).getLast? = option_fold (xs.getLast?.map (fun x => ys.getLast?.map (x * ·))) := by
  intro xs ys
  induction xs
  case nil => simp!
  case cons x xs ih =>
    cases ys
    case nil => simp!
    case cons y ys =>
      simp!
      sorry


@[simp]
def logω : Fluxion → ℤ
  | ⟨0,v,_,_⟩ => my_length v - v.length
  | ⟨n,_,_,_⟩ => n

def mul (x y : Fluxion) : Fluxion := ⟨(logω x + logω y).toNat,
    add_n_zero (- (logω x + logω y)).toNat
    (list_prod
      (x.v.drop (-(logω x)).toNat)
      (y.v.drop (-(logω y)).toNat)), by
        intro h
        simp!
        have hz : ∃ z, x.logω + y.logω = z  := by use x.logω + y.logω
        rcases hz with ⟨z,hz⟩
        cases z
        case ofNat z =>
          rw [hz] at h
          simp! at h
          simp!
          rcases x with ⟨xr,xv,xlr,xnt⟩
          rcases y with ⟨yr,yv,ylr,ynt⟩
          cases xr
          case zero =>
            cases yr
            case zero =>
              apply Int.add_le
              · simp!
                exact my_len_le_len xv
              simp!
              exact my_len_le_len yv
            case succ yr =>
              simp!
              apply Int.add_le
              · simp!
                exact my_len_le_len xv
              contrapose! h
              simp!
              unfold add_fold List.map cart List.drop
              sorry
          case succ xr => sorry
      , by
        rcases x with ⟨xr,xv,xlr,xnt⟩
        rcases y with ⟨yr,yv,ylr,ynt⟩
        simp!
        rw [logω, logω, Int.toNat_neg_natCast, Int.toNat_neg_natCast, ←Int.neg_add, ←Int.natCast_add, Int.toNat_neg_natCast, add_n_zero_getLast?_0, List.drop_zero, List.drop_zero]

        cases xr
        case zero => sorry
        case succ xr =>
          simp!
          cases xv
          case nil => simp!
          case cons x xs =>
            cases yv
            case nil => simp!
            case cons y ys =>
              simp!

    ⟩


/-
    if hx : x.r = 0
    then if hy : y.r = 0
         then sorry
         else sorry
    else if hy : y.r = 0
         then sorry
         else if hxy : x.r < y.r
              then sorry
              else mul y x
-/

@[simp]
instance : Ring Fluxion where
  one := ↑(1:ℚ)
  zero_add := zero_add
  add_zero := add_zero
  add_assoc := by sorry
  nsmul
    | n, ⟨r,v,lr,nt⟩ => if hn : n = 0 then 0 else ⟨r, (n * ·) <$> v, by
        intro h
        apply lr
        cases v
        case nil => simp!
        case cons x xs =>
          simp!
          simp! at h
          cases h
          case inl h => grind
          case inr h => exact h
      , by
        simp!
        intro x h
        constructor
        · exact hn
        contrapose! nt
        rw [h, nt]
      ⟩
  nsmul_succ := by
    intro n x
    rcases x with ⟨r,v,lr,nt⟩
    simp!
    have hn : n = 0 ∨ ¬n = 0 := by grind
    cases hn
    case inl hn =>
      rw [decide_true' hn, zero_add, hn]
      congr
      simp!
    case inr hn =>
      rw [decide_false' hn, add_def, add]
      simp!
      cases v
      case nil => simp!
      case cons x xs =>
        simp!
        simp! at lr
        congr
        cases dich x
        case inl hx =>
          rw [lr hx]
          simp!
        case inr hx =>
          sorry
  zsmul
    | n, ⟨r,v,lr,nt⟩ => if hn : n = 0 then 0 else ⟨r, (n * ·) <$> v, by
        intro h
        apply lr
        cases v
        case nil => simp!
        case cons x xs =>
          simp!
          simp! at h
          cases h
          case inl h => grind
          case inr h => exact h
      , by
        simp!
        intro x h
        constructor
        · exact hn
        contrapose! nt
        rw [h, nt]
      ⟩
  neg_add_cancel := by
    intro a
    rcases a with ⟨r,v,lr,nt⟩
    cases v
    case nil =>
      rw [(zero_iff_nil (mk r [] lr nt)).1 (by rfl)]
      simp!
    case cons x xs =>
      rw [add_def]
      simp!
      apply (zero_iff_nil (normalise (r, 0 :: zipWith0 (fun x1 x2 ↦ x1 + x2) (List.map (fun x ↦ -x) xs) xs))).1
      induction xs
      case nil =>
        simp!
        cases r
        case zero =>
          simp!
        case succ r =>
          simp!
      case cons x0 xs ih =>
        simp!
        cases r
        case zero =>
          simp!
          sorry
        case succ r => sorry
  add_comm := by
    intro a b
    rcases a with ⟨ar,av,alr,ant⟩
    rcases b with ⟨br,bv,blr,bnt⟩
    rw [add_def, add]
    sorry
  mul := sorry
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

instance : DenselyOrdered Fluxion where
  dense
    | ⟨rx,vx,ntx,lrx⟩, ⟨ry,vy,nty,lry⟩, h => by
      simp! at h
      cases h
      case inl h =>
        rcases h with ⟨h0,h1⟩
        use normalise ⟨rx, zipWith0 (fun x y => (x + y)/2) vx vy⟩
        simp!
        induction vx generalizing vy
        case nil =>
          simp
          sorry
        constructor
        · sorry
        sorry
      case inr h =>
        use ⟨rx, app_end vx 1, by
          intro h
          apply ntx
          cases vx
          · simp!
          simp!
          simp! at h
          exact h, by
            rw [app_end_getLast?]
            simp!⟩
        constructor
        · simp!
          apply Or.inl
          apply x_lt_app_end_x
          simp
        simp!
        apply Or.inr
        cases vx
        case nil =>
          simp! at *
          rw [ntx]
          exact h
        simp!
        simp! at h
        exact h

def f_power {α} (f : α → α) : ℕ → α → α
  | 0 => id
  | Nat.succ n => f ∘ (f_power f n)

def divε : Fluxion → Fluxion
  | ⟨r, v, lr, nt⟩ => if h : r = 0 then match v with
    | [] => 0
    | x :: xs => ⟨r, xs, by
      intro h0
      exact h
    , by
      contrapose! nt
      rw [List.getLast?_cons, nt]
      simp!
    ⟩
   else ⟨r+1, v, by
    intro h0
    contrapose! h
    apply lr
    exact h0
    , nt⟩

def div? (x y : Fluxion) (h : my_length y.v = 1) : Fluxion :=
    if h0 : y.r = 0 then (f_power divε (y.v.length - 1) ⟨x.r,(· / (y.v.getLast (by
      contrapose! h
      rw [h]
      simp!
    ))) <$> x.v,by
      rcases x with ⟨xr,xv,xlr,xnt⟩
      rcases y with ⟨yr,yv,ylr,ynt⟩
      intro h1
      apply xlr
      have h3 : yv ≠ [] := by
        cases yv
        case nil => simp! at h
        case cons => simp!
      have h2 : ∃ z, z ≠ 0 ∧ yv.getLast h3 = z := by
        use (yv.getLast h3)
        constructor
        · grind
        grind
      cases xv
      case nil => simp!
      case cons x xs =>
        simp!
        simp! at h
        rcases h2 with ⟨z,hz,h2⟩
        contrapose! h1
        simp!
        rw [h2]
        grind
    , by
      rcases x with ⟨xr,xv,xlr,xnt⟩
      rcases y with ⟨yr,yv,ylr,ynt⟩
      have h3 : yv ≠ [] := by
        cases yv
        case nil => simp! at h
        case cons => simp!
      rw [Functor.map, List.instFunctor]
      simp!
      intro x hx
      grind
    ⟩) else
    if h1 : y.r ≤ x.r then (normalise ⟨x.r-y.r,(· / (y.v.getLast (by
      rcases y with ⟨yr,yv,ylr,ynt⟩
      cases yv
      case nil => simp! at h
      case cons => simp!
    ))) <$> x.v⟩) else
    (normalise ⟨0, add_n_zero (y.r-x.r) ((· / (y.v.getLast (by
      rcases y with ⟨yr,yv,ylr,ynt⟩
      cases yv
      case nil => simp! at h
      case cons => simp!
    ))) <$> x.v)⟩)

@[simp]
instance [Ring Fluxion] : KindaDivRing Fluxion where
  coe n := if h : n = 0 then 0 else ⟨0,[n],by simp, by
    simp!
    exact h
    ⟩
  div? := div?
  div x y := if h : my_length y.v = 1 then div? x y h else none
  invertible x := my_length x.v = 1
  invertible_iff_can_div := by
    intro x y
    constructor
    · intro h
      have hx : my_length y.v = 1 := by grind
      simp!
      exact hx
    intro h
    rcases y with ⟨r,v,lr,nt⟩
    simp!
    contrapose! h
    simp!
    intro h0
    apply h at h0
    contrapose! h0
    simp!
  can_div_n := by
    intro n h
    cases n
    case zero => simp! at h
    case succ n => congr

def qsmul : ℚ → Fluxion → Fluxion := instKindaDivRingOfRing.qsmul

theorem zero_lt_my_len_of : ∀ xs, xs.getLast?.getD 0 ≠ 0 → 0 < my_length xs := by
  intro xs h
  induction xs
  case nil => simp! at h
  case cons x xs ih =>
    simp!
    cases dich x
    case inl hx =>
      rw [decide_true hx]
      apply ih
      grind
    case inr hx =>
      rw [decide_false hx]
      simp!

def ωnmul : ℤ → Fluxion → Fluxion
  | 0, x => x
  | Nat.succ n, ⟨r,v,lr,nt⟩ => if h : r = 0 then
    let aux := v.length - my_length v
      if hna : n < aux
      then ⟨r, v.drop (n+1), by
        intro h0
        exact h
      , by grind⟩
      else ⟨r+(n+1)-aux, v.drop aux, by
        intro h0
        contrapose! h0
        simp!
        have haux : aux = v.length - my_length v := by rfl
        rw [haux]
        have haux1 : aux < v.length := by
          rw [haux]
          simp!
          constructor
          · sorry
          sorry
        sorry
      , by
        simp!
        have haux : aux = v.length - my_length v := by rfl
        rw [haux]
        contrapose! nt
        rw [←nt]
        induction v
        case nil => simp!
        case cons x xs ih =>
          rw [List.getLast?_drop]
          simp!
          cases dich x
          case inl hx =>
            rw [decide_true hx]
            rw [haux] at hna
            simp! at hna
            rw [decide_true hx] at hna
            apply zero_lt_my_len_of
            rw [List.getLast?_drop] at nt
            let pr := (x :: xs).length ≤ (x :: xs).length - my_length (x :: xs)
            have h2 : pr ∨ ¬pr := by grind
            contrapose! nt
            cases h2
            case _ h2 =>
              rw [decide_true h2]
              simp!
            case _ h2 =>
              contrapose! h2
              have hpr : (pr = ((x :: xs).length ≤ (x :: xs).length - my_length (x :: xs))) := by rfl
              rw [hpr]
              sorry
          case inr hx =>
            rw [decide_false hx]
            simp!
      ⟩
    else ⟨r+n+1,v,by
      contrapose! h
      apply lr
      exact h.1
    , nt⟩
  | Int.negSucc n, ⟨r,v,lr,nt⟩ =>
    if hr : r = 0
    then ⟨r, add_n_zero (n+1) v, by
      intro h
      exact hr
    , by sorry
    ⟩
    else if hnr : n < r then ⟨r-n-1,v,by
      intro h
      contrapose! hr
      apply lr
      exact h
    , nt⟩ else ⟨0, add_n_zero (n-r+1) v, by simp!, by
      contrapose! hr
      apply lr
      sorry
      ⟩


theorem kdiv_support : ∀ x : Fluxion,
  (∃ (q : ℚ) (n : ℕ), (↑q : Fluxion) = (⟨n,[1],by
    intro h
    simp! at h
  , by grind⟩ * x)) ↔
  instKindaDivRingOfRing.invertible x := by
    intro x
    constructor
    · intro h
      simp!
      contrapose! h
      intro q n
      have h0 := dich q
      cases h0
      case inl h0 =>
        rw [decide_true' h0, zero_def]
        sorry
      case inr h0 =>
        rw [decide_false' h0]
        intro h1
        have h2 : q = 1 := by sorry
        sorry
    intro h
    sorry



def power {T : Type} [Ring T] (x : T) : ℕ → T
  | 0 => 1
  | Nat.succ n => x * (power x n)

def auxiliary_function {α} : ℕ → List α → List (ℕ × α)
  | _, [] => []
  | n, x :: xs => (n, x) :: auxiliary_function (n+1) xs

def enum_list {α} : List α → List (ℕ × α) := auxiliary_function 0

def raise (f : List ℚ) (x : Fluxion) : Fluxion :=
  List.foldr (· + ·) 0 ((fun (n,a) => (qsmul a (power x n))) <$> (enum_list f))

def apply (f : List ℚ) (x : ℚ) : ℚ :=
  List.foldr (· + ·) 0 ((fun (n,a) => (a * (power x n))) <$> (enum_list f))

def d (f : List ℚ) : ℚ → Fluxion :=
  fun x => raise f ((↑x : Fluxion) + (⟨0,[0,1], by grind, by grind⟩ : Fluxion)) + (- (raise f x))

def lim : Fluxion → EReal
  | ⟨_, [], _, _⟩ => 0
  | ⟨0, x :: _, _, _⟩ => ↑(↑x : ℝ)
  | ⟨_, x :: _, _, _⟩ => if x > 0 then ⊤ else ⊥

def diff (f : List ℚ) (x : ℚ) : EReal := lim (divε ((d f) x))

-- [0,1] <- identity function
-- apply [0,1] <- actual identity function
-- diff [0,1] <- derivative,

#eval (apply [0,0,1]) <$> [1,2,3,4,5]
#eval (diff [0,0,1]) <$> [1,2,3,4,5]

-- Matrices

/-

structure Dim where
  v : Option (ℕ × ℕ)
  m : ℕ := match v with
    | none => 0
    | some n => n.1 + 1
  n : ℕ := match v with
    | none => 0
    | some n => n.2 + 1

@[simp]
def dim_aux (x : Option (ℕ × ℕ)) : Dim where
  v := x

@[simp]
def dim : ℕ → ℕ → Dim
  | 0, _ => dim_aux none
  | _, 0 => dim_aux none
  | Nat.succ m, Nat.succ n => dim_aux (some (m,n))

theorem nmzero_ornot : ∀ m n, (m = 0 ∨ n = 0) ∨ (m ≠ 0 ∧ n ≠ 0) := by
  intro m n
  cases m
  · simp
  cases n
  · simp
  simp

@[simp]
def nmzero (m n : ℕ) := m = 0 ∨ n = 0

@[simp]
theorem nzero {m n : ℕ} : m = 0 ∨ n = 0 ↔ (dim m n).n = 0 := by
  constructor
  · intro h
    cases m
    case zero => simp
    case succ m =>
      cases n
      case zero => simp
      case succ n => simp at h
  intro h
  cases m
  case zero => simp
  case succ m =>
    cases n
    case zero => simp
    case succ n => simp at h

@[simp]
theorem mzero {m n : ℕ} : m = 0 ∨ n = 0 ↔ (dim m n).m = 0 := by
  constructor
  · intro h
    cases m
    case zero => simp
    case succ m =>
      cases n
      case zero => simp
      case succ n => simp at h
  intro h
  cases m
  case zero => simp
  case succ m =>
    cases n
    case zero => simp
    case succ n => simp at h

structure MatrixT (d : Dim) where
  mat : List (List ℚ)
  col : mat.length = d.n
  row : ∀ (i : ℕ) (h : i < d.n), (mat[i]'(by rw [col]; exact h)).length = d.m

namespace Matrices

/-
theorem empy? (n m : ℕ) (mat : List (List ℚ)) (col : mat.length = n)
  (row : ∀ (i : ℕ) (h : i < n), (mat[i]'(by rw [col]; exact h)).length = m) :
   (n = 0 ↔ m = 0) := by
    constructor
    · intro hn
      cases m
      case zero => rfl
      case succ m =>
        sorry
    intro hm
    induction n generalizing mat
    case zero => rfl
    case succ n ih =>
      contrapose! ih
      cases mat
      case nil => simp! at col
      case cons v vs =>
        use vs
        use (by grind)
        constructor
        · intro i hi
          specialize row (i+1) (by grind)
          simp! at row
          exact row
-/

theorem h {α} : ∀ (x : List α) xs, (x :: xs).transpose.length = x.length := by
  intro x xs
  rw [List.transpose]
  simp!
  rw [List.transpose.go]
  simp!
  induction x generalizing xs
  case nil =>
    induction xs
    case nil =>
      simp!
      rfl
    case cons x' xs ih =>
      rw [←ih]
      simp!




  induction xs generalizing x
  case nil =>
    simp!
    cases x
    case nil => rfl
    case cons v vs =>
      rw [pure, StateT.instMonad]
      simp!
      rw [StateT.pure]
      simp
  case cons x' xs ih =>
    simp!
    cas



def transposeMT {m n} (M : MatrixT (dim m n)) : MatrixT (dim n m) := ⟨List.transpose M.mat, by
  rcases M with ⟨mat,col,row⟩
  simp!
  induction mat generalizing m n
  case nil =>
    cases n
    case zero =>
      rw [List.transpose]
      simp
    case succ n =>
      cases m
      case zero => rfl
      case succ n => simp! at col
  case cons v vs ih =>
    cases m
    case zero => simp at col
    case succ m =>
      cases n
      case zero => simp at col
      case succ n =>
        simp!
        simp! at col row
        sorry



  , by
  rcases M with ⟨mat,col,row⟩
  intro i hi
  cases n
  case zero => simp at hi
  case succ n =>
    simp!
    cases m
    case zero => simp at hi
    case succ m =>
      simp!

      have h := row i (by
        simp at *
      )

  ⟩

-- example {n} : ∀ s : List (MatrixT n 1), s.length = n → ∃ m ∈ (SO n), ∀ t ∈ (((· = 0) ∘ head ∘ m) <$> s), t := by sorry

theorem list_ne_of_length_ne {α} : ∀ x y : List α, x.length ≠ y.length → x ≠ y := by
  intro x y h
  contrapose! h
  congr

theorem pifffoffofp {p} : (p → False) → (p ↔ False) := by
  intro h
  constructor
  · exact h
  simp!

@[simp]
def repeatxn {α} (x : α) : ℕ → List α
  | 0 => []
  | Nat.succ n => x :: repeatxn x n

theorem length_repeatxn {α} : ∀ (x : α) n, (repeatxn x n).length = n := by
  intro x n
  induction n
  case zero => rfl
  case succ n ih =>
    simp!
    exact ih

theorem getElem_repeatxn {α} : ∀ (x : α) n i (h : i < (repeatxn x n).length),
    (repeatxn x n)[i]'h = x := by
  intro x n i hi
  induction n generalizing i
  case zero => simp! at hi
  case succ n ih =>
    simp!
    cases i
    case zero => rfl
    case succ i =>
      simp!
      simp! at hi
      exact ih i hi

instance {m n} : Zero (MatrixT (dim m n)) where
  zero := ⟨repeatxn (repeatxn 0 m.succ) n, by rw [length_repeatxn], by
        intro i hi
        rw [getElem_repeatxn, length_repeatxn]⟩

@[simp]
def dot (x y : List ℚ) (_ : x.length = y.length) : ℚ :=
  List.foldr (· + ·) 0 (List.zipWith (· * ·) x y)

@[simp]
def map_dot (x : List ℚ) (ys : List (List ℚ))
  (h : ∀ (i : ℕ) (h : i < ys.length), ys[i].length = x.length) : List ℚ := match ys with
    | [] => []
    | y :: ys => dot x y (symm (h 0 (by simp))) :: map_dot x ys (by
      intro i hi
      exact h (i+1) (by simp! ; exact hi)
    )

@[simp]
def dotM (x y : List (List ℚ))
  (h : ∀ (i j : ℕ)
    (hi : i < x.length)
    (hj : j < y.length),
      x[i].length = y[j].length) : List (List ℚ) := match x, y with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => map_dot x ys (by
    intro i hi
    specialize h 0 (i+1) (by simp) (by grind)
    symm
    exact h) :: dotM xs ys (by
      intro i j hi hj
      exact h (i+1) (j+1) (by simp! ; exact hi) (by simp! ; exact hj))

theorem length_dotM : ∀ x y h, (y = [] ↔ x = []) → (dotM x y h).length = y.length := by
  intro x y h h0
  induction y generalizing x
  case nil =>
    cases x
    case nil => simp
    case cons => simp! at h0
  case cons y ys ih =>
    simp! at h0
    cases x
    case nil => simp! at h0
    case cons x xs =>
      simp!
      specialize ih xs (by
        intro i j hi hj
        exact h (i+1) (j+1) (by grind) (by grind))
      apply ih

def dotMT {n m w} : MatrixT (dim m n) → MatrixT (dim m w) → MatrixT (dim n w)
  | ⟨xmat,xcol,xrow⟩, ⟨ymat,ycol,yrow⟩ => ⟨dotM xmat ymat (by
    intro i j hi hj
    rw [xcol] at hi
    rw [ycol] at hj
    rw [xrow i hi, yrow j hj]
    cases m
    case zero => simp
    case succ m =>
      cases n
      case zero =>
        cases w
        case zero => simp
        case succ w => simp at hi
      case succ n =>
        cases w
        case zero => simp at hj
        case succ w => simp), by
    cases nmzero_ornot n w
    case inl hnw =>
      rw [nzero.1 hnw]
      simp!
      cases hnw
      case inl hn =>
        rw [←(@nzero m n)] at xcol
      have hmn : (nmzero m n) := by
        cases hnw
        case inl hn =>
          rw [hn]
          simp!
        case inr hw =>
          rw [hw]
          simp!
      cas


    , by sorry⟩


def det_aux {m n} : MatrixT (dim m n) → ℚ
  | ⟨mat,col,row⟩ => match n with
    | 0 => 1
    | 1 => (mat[0]'(by rw [col] ; simp))[0]'(by
          specialize row 0 (by simp)
          rw [row]
          apply Nat.zero_lt_of_ne_zero
          grind)
    | 2 =>
    | Nat.succ n => n

def SO (n : ℕ) (M : MatrixT (dim n n)) : Prop := match n with
  | 0 => M.mat = [[1]]
  |

def det {m n} (M : MatrixT (dim m n)) : Fluxion := match n with
    | 0 => 1
    | 1 => if hmat : det_aux M = 0 then 1 else ⟨1, [det_aux M,1], by
          rw [List.head?_cons, Option.getD_some, pifffoffofp one_ne_zero, imp_false]
          exact hmat, by simp⟩

    | Nat.succ n => sorry

end Matrices
-/

def det {n : Type u} [DecidableEq n] [Fintype n] (M : Matrix n n ℚ) : Fluxion := match u with
  | 0 => 1
  | 1 => if h : M.det = 0 then 1 else ⟨1, [M.det,1], by
    intro h0
    contrapose! h0
    rw [List.head?_cons, Option.getD_some]
    exact h, by simp⟩
  | 2 => if h : M.det = 0 

end Fluxion

/-

@[simp]
def finiteSet : Fluxion → List ℤ
  | ⟨_, []⟩ => {}
  | ⟨r, x :: xs⟩ => if h : x = 0 then finiteSet ⟨(r-1), xs⟩ else r :: finiteSet ⟨(r-1), xs⟩
termination_by x => x.v.length

def getElem : List ℚ → ℤ → ℚ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, Int.ofNat (Nat.succ n) => getElem xs n
  | _, Int.negSucc _ => 0

theorem finset_lt : ∀ r r' (xs : List ℚ), r' < r → r ∉ finiteSet ⟨r', xs⟩ := by
  intro r r' xs hr
  induction xs generalizing r'
  case nil => simp
  case cons x xs ih =>
    simp
    have h : x = 0 ∨ x ≠ 0 := by grind
    cases h
    case inl h => grind
    case inr h => grind

@[simp]
def finset (x : Fluxion) : Finset ℤ where
  val := finiteSet x
  nodup := by
    cases x
    case mk r x =>
    induction x generalizing r
    case nil => simp
    case cons x xs hx =>
      simp only [finiteSet]
      have h : x = 0 ∨ x ≠ 0 := by grind
      cases h
      case inl h =>
        simp [h]
        apply hx
      case inr h =>
        simp only [h, reduceDIte, Multiset.nodup_cons]
        constructor
        · apply finset_lt
          simp
        apply hx

@[simp]
def std : Fluxion → ℚ
  | ⟨_,[]⟩ => 0
  | ⟨0,x :: _⟩ => x
  | ⟨Nat.succ n, _ :: xs⟩ => std ⟨n, xs⟩
  | ⟨Int.negSucc _, _⟩ => 0
termination_by x => x.2.length
decreasing_by simp

def diff (f : Fluxion → Fluxion) : Fluxion → Fluxion := fun x => divε ((d f) x)

end Fluxion

@[simp]
def 𝔽 := LaurentPolynomial ℚ

notation "ω" => (LaurentPolynomial.T : ℤ → 𝔽)

notation "QtoF" => (LaurentPolynomial.C : ℚ → 𝔽)

namespace 𝔽

def to𝔽 : Fluxion → 𝔽
  | ⟨_, []⟩ => 0
  | ⟨0, x :: xs⟩ => (QtoF x : 𝔽) + (to𝔽 ⟨r-1,xs⟩)
  | ⟨r, x :: xs⟩ => (QtoF x * ω r) + (to𝔽 ⟨r-1,xs⟩)

noncomputable instance : Zero 𝔽 where
  zero := QtoF 0

-- match (finiteSet x).map (λ r => getElem x.2 (x.1-r)) with

/-
  (by
  intro a h
  cases x
  case mk r xs =>
    simp at *
    have trich := Int.lt_trichotomy a r
    cases trich
    case inl t => sorry
    case inr t =>
      cases t
      case inr t =>
        apply finset_lt a r xs at t
        contrapose! h
        simp at *
  )
-/

instance : LE 𝔽 where
  le
    | x, y => sorry

end 𝔽
-/
