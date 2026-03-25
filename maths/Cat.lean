import Mathlib

-- (bad?) Definition of Category

structure Cat.{u} where
  C0 : Type u
  C1 : Type u
  C2 : Type u
  (dom cod : C1 → C0)
  ident : C0 → C1
  (left rite comp : C2 → C1)
  pair (a b : C1) : (dom a = cod b) → C2
  -- are any of ↓these↓ provable from the others? idfk
  -- ident_dom/cod is provable from ident_lid/rid, but the latter relies on the former
  -- if I did this:
  -- ident_lid : ∀ x h, comp (pair (ident (cod x)) x h) = x
  -- then I could remove ident_dom/cod I think?
  ident_dom : ∀ x, dom (ident x) = x
  ident_cod : ∀ x, cod (ident x) = x
  C2_ok : ∀ p : C2, dom (left p) = cod (rite p)
  dom_comp : ∀ p, dom (comp p) = dom (rite p)
  cod_comp : ∀ p, cod (comp p) = cod (left p)
  left_pair : ∀ a b h, left (pair a b h) = a
  rite_pair : ∀ a b h, rite (pair a b h) = b
  ident_lid : ∀ x, comp (pair (ident (cod x)) x (by rw [ident_dom])) = x
  ident_rid : ∀ x, comp (pair x (ident (dom x)) (by rw [ident_cod])) = x
  -- pair and (left × rite × C2_ok) are inverses

structure Cat'.{u} where
  C0 : Type u
  C1 : Type u
  C2 : Type u
  (dom cod : C1 → C0)
  ident : C0 → C1
  (left rite comp : C2 → C1)
  pair (a b : C1) : (dom a = cod b) → C2
  C2_ok : ∀ p : C2, dom (left p) = cod (rite p)
  dom_comp : ∀ p, dom (comp p) = dom (rite p)
  cod_comp : ∀ p, cod (comp p) = cod (left p)
  left_pair : ∀ a b h, left (pair a b h) = a
  rite_pair : ∀ a b h, rite (pair a b h) = b
  ident_lid : ∀ x h, comp (pair (ident (cod x)) x h) = x
  ident_rid : ∀ x h, comp (pair x (ident (dom x)) h) = x

lemma ident_dom_provable (C : Cat') : ∀ x, C.dom (C.ident x) = x := by
  intro x
  have hl := C.ident_lid
  have hr := C.ident_rid
  have hdc := C.dom_comp
  have hrp := C.rite_pair
  specialize hl (C.ident x)
  specialize hr (C.ident x)
  specialize hrp (C.ident x) (C.ident x)
  sorry -- probably not provable actually idk

-- lemma ident_cod_provable (C : Cat') : ∀ x, C.cod (C.ident x) = x := by sorry

-- oh heck, need another field
--

-- Example of Natural numbers as a poset Category

structure Poset1 α [Preorder α] where
  m : α
  n : α
  h : m ≤ n

structure Poset2 α [Preorder α] where
  m : α
  n : α
  p : α
  hmn : m ≤ n
  hnp : n ≤ p

@[simp]
def NatPoset : Cat where
  C0 := ℕ
  C1 := Poset1 ℕ
  C2 := Poset2 ℕ
  dom x := x.m
  cod x := x.n
  ident x := ⟨x, x, le_refl x⟩
  ident_dom := by intros ; rfl
  ident_cod := by intros ; rfl
  left p := ⟨p.n,p.p,p.hnp⟩
  rite p := ⟨p.m,p.n,p.hmn⟩
  comp p := ⟨p.m,p.p,le_trans p.hmn p.hnp⟩
  pair a b h := ⟨b.m,a.m,a.n,by rw [h] ; exact b.h,a.h⟩
  C2_ok := by intros ; rfl
  dom_comp := by intros ; rfl
  cod_comp := by intros ; rfl
  left_pair := by intros ; rfl
  rite_pair := by intros ; congr
  ident_lid x := by rfl
  ident_rid x := by rfl

@[simp]
def Poset α [Preorder α] : Cat where
  C0 := α
  C1 := Poset1 α
  C2 := Poset2 α
  dom x := x.m
  cod x := x.n
  ident x := ⟨x, x, le_refl x⟩
  ident_dom := by intros ; rfl
  ident_cod := by intros ; rfl
  left p := ⟨p.n,p.p,p.hnp⟩
  rite p := ⟨p.m,p.n,p.hmn⟩
  comp p := ⟨p.m,p.p,le_trans p.hmn p.hnp⟩
  pair a b h := ⟨b.m,a.m,a.n,by rw [h] ; exact b.h,a.h⟩
  C2_ok := by intros ; rfl
  dom_comp := by intros ; rfl
  cod_comp := by intros ; rfl
  left_pair := by intros ; rfl
  rite_pair := by intros ; congr
  ident_lid x := by rfl
  ident_rid x := by rfl

-- Coproduct category

@[simp] -- useful auxiliary function for coprod cats:
def mst {α β γ δ} (f : α → β) (g : γ → δ) : (α ⊕ γ) → (β ⊕ δ)
  | Sum.inl x => Sum.inl (f x)
  | Sum.inr x => Sum.inr (g x)

def coprod (C : Cat) (D : Cat) : Cat where
  C0 := C.C0 ⊕ D.C0
  C1 := C.C1 ⊕ D.C1
  C2 := C.C2 ⊕ D.C2
  dom := mst C.dom D.dom
  cod := mst C.cod D.cod
  left := mst C.left D.left
  rite := mst C.rite D.rite
  comp := mst C.comp D.comp
  ident := mst C.ident D.ident
  pair
    | Sum.inl a, Sum.inl b, h => Sum.inl (C.pair a b (by simp! at h ; exact h))
    | Sum.inr a, Sum.inr b, h => Sum.inr (D.pair a b (by simp! at h ; exact h))
    | Sum.inl a, Sum.inr b, h => Sum.inl (C.pair a a (by simp! at h))
    | Sum.inr a, Sum.inl b, h => Sum.inr (D.pair a a (by simp! at h))
  C2_ok := by
    intro p
    cases p
    case inl p =>
      simp!
      exact C.C2_ok p
    case inr p =>
      simp!
      exact D.C2_ok p
  dom_comp := by
    intro p
    cases p
    case inl p =>
      simp!
      exact C.dom_comp p
    case inr p =>
      simp!
      exact D.dom_comp p
  cod_comp := by
    intro p
    cases p
    case inl p =>
      simp!
      exact C.cod_comp p
    case inr p =>
      simp!
      exact D.cod_comp p
  left_pair := by
    intro a b h
    cases a
    case inl a =>
      cases b
      case inl b =>
        simp!
        simp! at h
        exact C.left_pair a b h
      case inr b => simp! at h
    case inr a =>
      cases b
      case inl b => simp! at h
      case inr b =>
        simp!
        simp! at h
        exact D.left_pair a b h
  rite_pair := by
    intro a b h
    cases a
    case inl a =>
      cases b
      case inl b =>
        simp!
        simp! at h
        exact C.rite_pair a b h
      case inr b => simp! at h
    case inr a =>
      cases b
      case inl b => simp! at h
      case inr b =>
        simp!
        simp! at h
        exact D.rite_pair a b h
  ident_dom := by
    intro x
    cases x
    case inl x =>
      simp!
      exact C.ident_dom x
    case inr x =>
      simp!
      exact D.ident_dom x
  ident_cod := by
    intro x
    cases x
    case inl x =>
      simp!
      exact C.ident_cod x
    case inr x =>
      simp!
      exact D.ident_cod x
  ident_lid x := by
    cases x
    case inl x =>
      simp!
      exact C.ident_lid x
    case inr x =>
      simp!
      exact D.ident_lid x
  ident_rid x := by
    cases x
    case inl x =>
      simp!
      exact C.ident_rid x
    case inr x =>
      simp!
      exact D.ident_rid x

instance : Add Cat where
  add := coprod

-- Product Category

@[simp] -- useful auxiliary function for prod cats:
def mpt {α β γ δ} (f : α → β) (g : γ → δ) (x : α × γ) : (β × δ) := ⟨f x.fst, g x.snd⟩

def prod (C : Cat) (D : Cat) : Cat where
  C0 := C.C0 × D.C0
  C1 := C.C1 × D.C1
  C2 := C.C2 × D.C2
  dom := mpt C.dom D.dom
  cod := mpt C.cod D.cod
  left := mpt C.left D.left
  rite := mpt C.rite D.rite
  comp := mpt C.comp D.comp
  pair a b h :=
    ⟨C.pair a.1 b.1 (by simp! at h ; exact h.1),
     D.pair a.2 b.2 (by simp! at h ; exact h.2)⟩
  ident := mpt C.ident D.ident
  C2_ok := by
    intro p
    simp!
    exact ⟨C.C2_ok p.1, D.C2_ok p.2⟩
  dom_comp := by
    intro p
    simp!
    exact ⟨C.dom_comp p.1, D.dom_comp p.2⟩
  cod_comp := by
    intro p
    simp!
    exact ⟨C.cod_comp p.1, D.cod_comp p.2⟩
  left_pair := by
    intro a b h
    simp!
    congr
    · exact C.left_pair a.1 b.1 (by simp! at h ; exact h.1)
    exact D.left_pair a.2 b.2 (by simp! at h ; exact h.2)
  rite_pair := by
    intro a b h
    simp!
    congr
    · exact C.rite_pair a.1 b.1 (by simp! at h ; exact h.1)
    exact D.rite_pair a.2 b.2 (by simp! at h ; exact h.2)
  ident_dom := by
    intro x
    rcases x with ⟨x1,x2⟩
    simp!
    exact ⟨C.ident_dom x1, D.ident_dom x2⟩
  ident_cod := by
    intro x
    rcases x with ⟨x1,x2⟩
    simp!
    exact ⟨C.ident_cod x1, D.ident_cod x2⟩
  ident_lid | ⟨x1,x2⟩ => by simp! ; exact ⟨C.ident_lid x1, D.ident_lid x2⟩
  ident_rid | ⟨x1,x2⟩ => by simp! ; exact ⟨C.ident_rid x1, D.ident_rid x2⟩

instance : Mul Cat where
  mul := coprod

-- Opposite Category

def op (C : Cat) : Cat where
  C0 := C.C0
  C1 := C.C1
  C2 := C.C2
  dom := C.cod
  cod := C.dom
  ident := C.ident
  left := C.rite
  rite := C.left
  comp := C.comp
  pair a b h := C.pair b a (symm h)
  ident_dom := C.ident_cod
  ident_cod := C.ident_dom
  C2_ok p := symm (C.C2_ok p)
  dom_comp := C.cod_comp
  cod_comp := C.dom_comp
  left_pair a b h := C.rite_pair b a (symm h)
  rite_pair a b h := C.left_pair b a (symm h)
  ident_lid := C.ident_rid
  ident_rid := C.ident_lid

-- My "Map Category"

-- basically a coproduct category on C and D
-- with added arrows added from a map from C₀ to D₀

structure ArrowAcross (C D : Cat) (F : C.C0 → D.C0) where
  Carrow : C.C1
  Darrow : D.C1
  h : F (C.cod Carrow) = (D.dom Darrow)

structure funct_C2 C D F where
  val : (ArrowAcross C D F × C.C1 ⊕ D.C1 × ArrowAcross C D F) ⊕ C.C2 ⊕ D.C2
  hC : ∀ x y, Sum.inl (Sum.inl (x, y)) = val → C.dom x.Carrow = C.cod y
  hD : ∀ x y, Sum.inl (Sum.inr (x, y)) = val → D.dom x = D.cod y.Darrow

@[simp]
def MapCat (C D : Cat) (F : C.C0 → D.C0) : Cat where
  C0 := C.C0 ⊕ D.C0
  C1 := ArrowAcross C D F ⊕ C.C1 ⊕ D.C1
  C2 := funct_C2 C D F
  dom
    | Sum.inr (Sum.inl x) => Sum.inl (C.dom x)
    | Sum.inr (Sum.inr x) => Sum.inr (D.dom x)
    | Sum.inl x => Sum.inl (C.dom x.Carrow)
  cod
    | Sum.inr (Sum.inl x) => Sum.inl (C.cod x)
    | Sum.inr (Sum.inr x) => Sum.inr (D.cod x)
    | Sum.inl x => Sum.inr (D.cod x.Darrow)
  left x := match x.val with
    | Sum.inl (Sum.inl x) => Sum.inl x.fst
    | Sum.inl (Sum.inr x) => Sum.inr (Sum.inr x.fst)
    | Sum.inr (Sum.inl x) => Sum.inr (Sum.inl (C.left x))
    | Sum.inr (Sum.inr x) => Sum.inr (Sum.inr (D.left x))
  rite x := match x.val with
    | Sum.inl (Sum.inl x) => Sum.inr (Sum.inl x.snd)
    | Sum.inl (Sum.inr x) => Sum.inl x.snd
    | Sum.inr (Sum.inl x) => Sum.inr (Sum.inl (C.rite x))
    | Sum.inr (Sum.inr x) => Sum.inr (Sum.inr (D.rite x))
  comp
    | ⟨Sum.inl (Sum.inl (a,c)),hC,_⟩ => Sum.inl {
        Carrow := C.comp (C.pair a.Carrow c (hC a c (by rfl))),
        Darrow := a.Darrow,
        h := by rw [C.cod_comp, C.left_pair] ; exact a.h}
    | ⟨Sum.inl (Sum.inr (d,a)),_,hD⟩ => Sum.inl {
        Carrow := a.Carrow,
        Darrow := D.comp (D.pair d a.Darrow (hD d a (by rfl))),
        h := by rw [D.dom_comp, D.rite_pair] ; exact a.h}
    | ⟨Sum.inr (Sum.inl x),_,_⟩ => Sum.inr (Sum.inl (C.comp x))
    | ⟨Sum.inr (Sum.inr x),_,_⟩ => Sum.inr (Sum.inr (D.comp x))
  pair
    | Sum.inl x, Sum.inl y => fun h ↦ by contradiction
    | Sum.inl x, Sum.inr (Sum.inr y) => fun h ↦ by contradiction
    | Sum.inr (Sum.inl x), Sum.inl y => fun h ↦ by contradiction
    | Sum.inr (Sum.inl x), Sum.inr (Sum.inr y) => fun h ↦ by contradiction
    | Sum.inr (Sum.inr x), Sum.inr (Sum.inl y) => fun h ↦ by contradiction
    | Sum.inl x, Sum.inr (Sum.inl y) => fun h ↦ {
        val := Sum.inl (Sum.inl (x, y))
      , hC := by grind, hD := by grind}
    | Sum.inr (Sum.inr x), Sum.inl y => fun h ↦ {
        val := Sum.inl (Sum.inr (x, y))
      , hC := by grind, hD := by grind}
    | Sum.inr (Sum.inl x), Sum.inr (Sum.inl y) => fun h ↦ {
        val := Sum.inr (Sum.inl (C.pair x y (by grind)))
      , hC := by grind, hD := by grind}
    | Sum.inr (Sum.inr x), Sum.inr (Sum.inr y) => fun h ↦ {
        val := Sum.inr (Sum.inr (D.pair x y (by grind)))
      , hC := by grind, hD := by grind}
  C2_ok := by
    intro p
    rcases p with ⟨p,hCp,hDp⟩
    cases p
    case inl p =>
      cases p
      case inl p => simp! ; apply hCp ; rfl
      case inr p => simp! ; apply hDp ; rfl
    case inr p =>
      cases p
      case inl p => simp! ; exact C.C2_ok p
      case inr p => simp! ; exact D.C2_ok p
  dom_comp := by
    intro p
    rcases p with ⟨p,hCp,hDp⟩
    cases p
    case inl p =>
      cases p
      case inl p => simp! ; rw [C.dom_comp, C.rite_pair]
      case inr p => rfl
    case inr p =>
      cases p
      case inl p => simp! ; rw [C.dom_comp]
      case inr p => simp! ; rw [D.dom_comp]
  cod_comp := by
    intro p
    rcases p with ⟨p,hCp,hDp⟩
    cases p
    case inl p =>
      cases p
      case inl p => rfl
      case inr p => simp! ; rw [D.cod_comp, D.left_pair]
    case inr p =>
      cases p
      case inl p => simp! ; rw [C.cod_comp]
      case inr p => simp! ; rw [D.cod_comp]
  left_pair := by
    intro a b h
    cases a
    case inl a =>
      cases b
      case inl b => simp! at h
      case inr b =>
        cases b
        case inl b => rfl
        case inr b => simp! at h
    case inr a =>
      cases a
      case inl a =>
        cases b
        case inl b => simp! at h
        case inr b =>
          cases b
          case inl b => simp! ; rw [C.left_pair]
          case inr b => simp! at h
      case inr a =>
        cases b
        case inl b => rfl
        case inr b =>
          cases b
          case inl b => simp! at h
          case inr b => simp! ; rw [D.left_pair]
  rite_pair := by
    intro a b h
    cases a
    case inl a =>
      cases b
      case inl b => simp! at h
      case inr b =>
        cases b
        case inl b => rfl
        case inr b => simp! at h
    case inr a =>
      cases a
      case inl a =>
        cases b
        case inl b => simp! at h
        case inr b =>
          cases b
          case inl b => simp! ; rw [C.rite_pair]
          case inr b => simp! at h
      case inr a =>
        cases b
        case inl b => rfl
        case inr b =>
          cases b
          case inl b => simp! at h
          case inr b => simp! ; rw [D.rite_pair]
  ident
    | Sum.inl x => Sum.inr (Sum.inl (C.ident x))
    | Sum.inr x => Sum.inr (Sum.inr (D.ident x))
  ident_dom x := by
    cases x
    case inl x => simp! ; exact C.ident_dom x
    case inr x => simp! ; exact D.ident_dom x
  ident_cod x := by
    cases x
    case inl x => simp! ; exact C.ident_cod x
    case inr x => simp! ; exact D.ident_cod x
  ident_lid x := by
    cases x
    case inl x =>
      rcases x with ⟨Ca,Da,h⟩
      simp!
      exact D.ident_lid Da
    case inr x =>
      cases x
      case inl x => simp! ; exact C.ident_lid x
      case inr x => simp! ; exact D.ident_lid x
  ident_rid x := by
    cases x
    case inl x =>
      rcases x with ⟨Ca,Da,h⟩
      simp!
      exact C.ident_rid Ca
    case inr x =>
      cases x
      case inl x => simp! ; exact C.ident_rid x
      case inr x => simp! ; exact D.ident_rid x

-- Functors

structure Funct (C D : Cat) where
  F0 : C.C0 → D.C0
  F1 : C.C1 → D.C1
  -- hdom : F0 ∘ C.dom = D.dom ∘ F1
  -- hcod : F0 ∘ C.cod = D.cod ∘ F1
  hdom : ∀ x, D.dom (F1 x) = F0 (C.dom x)
  hcod : ∀ x, D.cod (F1 x) = F0 (C.cod x)
  F2 : C.C2 → D.C2 := fun x => D.pair (F1 (C.left x)) (F1 (C.rite x)) (by
    rw [hdom, hcod]
    congr
    exact C.C2_ok x)

-- Category Isomorphism:

structure iso (C D : Cat) where
  F : Funct C D
  G : Funct D C
  hc0 : ∀ c, G.F0 (F.F0 c) = c
  hd0 : ∀ d, F.F0 (G.F0 d) = d
  hc1 : ∀ a, G.F1 (F.F1 a) = a
  hd1 : ∀ a, F.F1 (G.F1 a) = a
-- is this a sufficient def of category equivalence?

/-
structure iso' (C D : Cat) where
  F : Funct C D
  -- inj0 : ∀ x y, F.F0 x = F.F0 y → x = y
  inj0 (x y : C.C0) : F.F0 x = F.F0 y → x = y
  -- sur0 : ∀ d, ∃ c, d = F.F0 c
  sur0 (d : D.C0) : C.C0
  sur0' (d : D.C0) : (d = F.F0 (sur0 d))
  inj1 : ∀ x y, F.F1 x = F.F1 y → x = y
  -- sur1 : ∀ d, ∃ c, d = F.F1 c
  sur1 : D.C1 → C.C1
  sur1' (d : D.C1) : d = F.F1 (sur1 d)

theorem iso_def_eqv (C D : Cat) : (∃ proof : iso C D, True) ↔ (∃ proof : iso' C D, True) := by
  constructor
  · intro h
    rcases h with ⟨⟨F,G,hc0,hd0,hc1,hd1⟩,_⟩
    use {
      F := F
      inj0 x y h := by grind
      sur0 x := by use (G.F0 x) ; rw [hd0 x]
      inj1 x y h := by grind
      sur1 x := by use (G.F1 x) ; rw [hd1 x]
    }
  intro h
  rcases h with ⟨⟨F,inj0,sur0,inj1,sur1⟩,_⟩
  use {
    F := F
    G := {
      F0 d := by
        specialize sur0 d
        exact Exists.choose sur0
      F1 d := by
        specialize sur1 d
        exact Exists.choose sur1
      hdom := by
        intro x
        sorry
    }

  }
-/

def isom (C D : Cat) : Prop :=
  ∃ (F : Funct C D) (G : Funct D C),
  (∀ c, G.F0 (F.F0 c) = c) ∧
  (∀ d, F.F0 (G.F0 d) = d) ∧
  (∀ a, G.F1 (F.F1 a) = a) ∧
  (∀ a, F.F1 (G.F1 a) = a)

theorem isoisisom (i : iso C D) : isom C D :=
  ⟨i.F, i.G, And.intro i.hc0 (And.intro i.hd0 (And.intro i.hc1 i.hd1))⟩

-- test category with multiple arrows with same dom and cod
-- two objects
-- [representation] = [value] :
-- ⊥ = ⊥
-- ⊤ = ⊤
-- four arrows
-- (⊥,⊤) = ⊥ →₀ ⊤
-- (⊤,⊥) = ⊥ →₁ ⊤
-- (⊥,⊥) = ⊥ →  ⊥
-- (⊤,⊤) = ⊤ →  ⊤
-- six pairs
-- (_,none) means that it is a pair of identity arrows
-- (_,some ⊥) means that one of the arrows is ⊥ →₀ ⊤
-- (_,some ⊤) means that one of the arrows is ⊥ →₁ ⊤
-- (⊤,_) means that one of the arrows is ⊤ → ⊤
-- (⊥,_) means that one of the arrows is ⊥ → ⊥
-- (⊥,none)   = (⊥ →  ⊥, ⊥ →  ⊥)
-- (⊥,some ⊥) = (⊥ →₀ ⊤, ⊥ →  ⊥)
-- (⊥,some ⊤) = (⊥ →₁ ⊤, ⊥ →  ⊥)
-- (⊤,none)   = (⊤ →  ⊤, ⊤ →  ⊤)
-- (⊤,some ⊥) = (⊤ →  ⊤, ⊥ →₀ ⊤)
-- (⊤,some ⊤) = (⊤ →  ⊤, ⊥ →₁ ⊤)

def test : Cat where
  C0 := Bool
  C1 := Bool × Bool
  C2 := Bool × Option Bool
  dom
    | (⊤,⊤) => ⊤
    | _ => ⊥
  cod
    | (⊥,⊥) => ⊥
    | _ => ⊤
  ident x := (x,x)
  left
    | (⊤,_) => (⊤,⊤)
    | (⊥,none) => (⊥,⊥)
    | (⊥,some x) => (x,¬x)
  rite
    | (⊥,_) => (⊥,⊥)
    | (⊤,none) => (⊤,⊤)
    | (⊤,some x) => (x,¬x)
  comp
    | (x,none) => (x,x)
    | (_,some x) => (x,¬x)
  pair
    | (⊥,⊥), (⊤,_), _ => by contradiction
    | (⊥,⊥), (_,⊤), h => by simp at h
    | (⊥,⊥), (⊥,⊥), _ => (⊥,none)
    | (⊥,_), (⊤,⊤), _ => by contradiction
    | (_,⊥), (⊤,⊤), h => by simp at h
    | (⊤,⊤), (⊤,⊤), _ => (⊤,none)
    | (⊤,⊥), (⊥,⊥), _ => (⊥,some ⊤)
    | (⊥,⊤), (⊥,⊥), _ => (⊥,some ⊥)
    | (⊤,⊤), (⊤,⊥), _ => (⊤,some ⊤)
    | (⊤,⊤), (⊥,⊤), _ => (⊤,some ⊥)
  ident_dom x := by
    cases x
    case false => rfl
    case true => rfl
  ident_cod x := by
    cases x
    case false => rfl
    case true => rfl
  C2_ok | (l,r) => by
          cases l
          · cases r
            case none => rfl
            case some x =>
              cases x
              · rfl
              rfl
          cases r
          case none => rfl
          case some x =>
            cases x
            · rfl
            rfl
  dom_comp | (l,r) => by
            cases l
            · cases r
              case none => rfl
              case some x =>
                cases x
                · rfl
                rfl
            cases r
            case none => rfl
            case some x =>
              cases x
              · rfl
              rfl
  cod_comp | (l,r) => by
            cases l
            · cases r
              case none => rfl
              case some x =>
                cases x
                · rfl
                rfl
            cases r
            case none => rfl
            case some x =>
              cases x
              · rfl
              rfl
  left_pair | (a1,a2), (b1,b2), h => by
              cases a1
              · cases a2
                · cases b1
                  · cases b2
                    · rfl
                    contradiction
                  cases b2
                  · contradiction
                  contradiction
                cases b1
                · cases b2
                  · rfl
                  contradiction
                cases b2
                · contradiction
                contradiction
              cases a2
              · cases b1
                · cases b2
                  · rfl
                  contradiction
                cases b2
                · contradiction
                contradiction
              cases b1
              · cases b2
                · contradiction
                rfl
              cases b2
              · rfl
              rfl
  rite_pair | (a1,a2), (b1,b2), h => by
              cases a1
              · cases a2
                · cases b1
                  · cases b2
                    · rfl
                    contradiction
                  cases b2
                  · contradiction
                  contradiction
                cases b1
                · cases b2
                  · rfl
                  contradiction
                cases b2
                · contradiction
                contradiction
              cases a2
              · cases b1
                · cases b2
                  · rfl
                  contradiction
                cases b2
                · contradiction
                contradiction
              cases b1
              · cases b2
                · contradiction
                rfl
              cases b2
              · rfl
              rfl
  ident_lid | ⟨x1,x2⟩ => by
              cases x1
              · cases x2
                · rfl
                rfl
              cases x2
              · rfl
              rfl
  ident_rid | ⟨x1,x2⟩ => by
              cases x1
              · cases x2
                · rfl
                rfl
              cases x2
              · rfl
              rfl

-- Nat Monoid?

def NatMonoid : Cat where
  C0 := Unit
  C1 := ℕ
  C2 := ℕ × ℕ
  dom _ := ()
  cod _ := ()
  ident _ := 0 -- this cannot be anything else ; this made me realise I needed ident_(l/r)id
  left := Prod.fst
  rite := Prod.snd
  comp := Function.uncurry (· + ·)
  pair a b _ := (a,b)
  ident_dom _ := by rfl
  ident_cod _ := by rfl
  C2_ok _ := by rfl
  dom_comp _ := by rfl
  cod_comp _ := by rfl
  left_pair _ _ _ := by rfl
  rite_pair _ _ _ := by rfl
  ident_lid _ := by rw [Function.uncurry_apply_pair, zero_add]
  ident_rid _ := by rw [Function.uncurry_apply_pair, add_zero]

-- 0 Category:

instance : Zero Cat where
  zero := {
    C0 := Empty
    C1 := Empty
    C2 := Empty
    dom := id
    cod := id
    left := id
    rite := id
    comp := id
    pair a b h := a
    C2_ok p := by rfl
    dom_comp p := by rfl
    cod_comp p := by rfl
    left_pair a b h := by rfl
    rite_pair a b h := by rw [h] ; rfl
    ident := id
    ident_dom x := by rfl
    ident_cod x := by rfl
    ident_lid x := by rfl
    ident_rid x := by rfl
  }

-- 1 Category:

instance : One Cat where
  one := {
    C0 := Unit
    C1 := Unit
    C2 := Unit
    dom := id
    cod := id
    left := id
    rite := id
    comp := id
    pair a b h := a
    C2_ok p := by rfl
    dom_comp p := by rfl
    cod_comp p := by rfl
    left_pair a b h := by rfl
    rite_pair a b h := by rfl
    ident := id
    ident_dom x := by rfl
    ident_cod x := by rfl
    ident_lid x := by rfl
    ident_rid x := by rfl
  }

-- 2 Category:

-- two objects
-- [representation] = [value] :
-- ⊥ = ⊥
-- ⊤ = ⊤
-- three arrows
-- none   = ⊥ → ⊤
-- some ⊥ = ⊥ → ⊥
-- some ⊤ = ⊤ → ⊤
-- four pairs
-- (⊤,_) means that one of the arrows is ⊥ → ⊤
-- (⊥,_) means that it is a pair of identity arrows
-- (_,x) means that one of the arrows in the pair is the identity arrow x → x
-- (⊥,⊥) = (⊥ → ⊥, ⊥ → ⊥)
-- (⊥,⊤) = (⊤ → ⊤, ⊤ → ⊤)
-- (⊤,⊥) = (⊥ → ⊤, ⊥ → ⊥)
-- (⊤,⊤) = (⊤ → ⊤, ⊥ → ⊤)

@[simp]
instance : OfNat Cat 2 where
  ofNat := {
    C0 := Bool
    C1 := Option Bool
    C2 := Bool × Bool
    dom
      | none => ⊥
      | some x => x
    cod
      | none => ⊤
      | some x => x
    left
      | (_,⊤) => some ⊤
      | (⊤,⊥) => none
      | (⊥,⊥) => some ⊥
    rite
      | (_,⊥) => some ⊥
      | (⊤,⊤) => none
      | (⊥,⊤) => some ⊤
    comp
      | (⊤,_) => none
      | (_,x) => x
    pair
      | none, _, _ => (⊤,⊥)
      | _, none, _ => (⊤,⊤)
      | some ⊤, _, _ => (⊥,⊤)
      | _, some ⊥, _ => (⊥,⊥)
      | some ⊥, some ⊤, _ => by contradiction
    C2_ok p := by
      rcases p with ⟨ac,on⟩
      cases ac
      · cases on
        · rfl
        rfl
      cases on
      · rfl
      rfl
    dom_comp p := by
      rcases p with ⟨ac,on⟩
      cases ac
      · cases on
        · rfl
        rfl
      cases on
      · rfl
      rfl
    cod_comp p := by
      rcases p with ⟨ac,on⟩
      cases ac
      · cases on
        · rfl
        rfl
      cases on
      · rfl
      rfl
    left_pair a b h := by
      cases a
      case none => rfl
      case some a =>
        cases b
        case none =>
          simp! at h
          simp!
          exact h
        case some b =>
          simp! at h
          cases a
          case false =>
            cases b
            case false => rfl
            case true => simp at h
          case true =>
            cases b
            case false => rfl
            case true => rfl
    rite_pair a b h := by
      cases a
      case none =>
        cases b
        case none => simp at h
        case some b =>
          cases b
          · rfl
          simp at h
      case some a =>
        cases b
        case none => rfl
        case some b =>
          cases a
          · cases b
            · rfl
            simp at h
          cases b
          · simp at h
          rfl
    ident := some
    ident_dom x := by rfl
    ident_cod x := by rfl
    ident_lid x := by
      cases x
      case none => rfl
      case some x =>
        cases x
        · rfl
        rfl
    ident_rid x := by
      cases x
      case none => rfl
      case some x =>
        cases x
        · rfl
        rfl
  }

theorem twoIsPoset : isom (Poset Bool) (2 : Cat) := by apply isoisisom ; exact {
    F := {
      F0 := id
      F1
        | ⟨⊥,⊤,h⟩ => none
        | ⟨⊥,⊥,_⟩ => some ⊥
        | ⟨⊤,⊤,_⟩ => some ⊤
        | ⟨⊤,⊥,_⟩ => by contradiction
      hdom | ⟨x,y,h⟩ => by
            cases x
            · cases y
              · rfl
              rfl
            cases y
            · contradiction
            rfl
      hcod | ⟨x,y,h⟩ => by
            cases x
            · cases y
              · rfl
              rfl
            cases y
            · contradiction
            rfl
    }
    G := {
      F0 := id
      F1
        | none => ⟨⊥, ⊤, by simp⟩
        | some x => ⟨x, x, by rfl⟩
      hdom x := by
        cases x
        · rfl
        rfl
      hcod x := by
        cases x
        · rfl
        rfl
    }
    hc0 c := by rfl
    hd0 d := by rfl
    hc1 | ⟨x,y,h⟩ => by
          cases x
          · cases y
            · rfl
            rfl
          cases y
          · contradiction
          rfl
    hd1 m := by
      cases m
      case none => rfl
      case some m =>
        cases m
        · rfl
        rfl
  }

def CatSucc (C : Cat) : Cat where
  C0 := Option C.C0
  C1 := C.C1 ⊕ Option C.C0
  C2 := C.C2 ⊕ C.C1 ⊕ Option C.C0
  dom
    | Sum.inl x => some (C.dom x)
    | Sum.inr none => none
    | Sum.inr (some x) => x
  cod
    | Sum.inl x => some (C.cod x)
    | Sum.inr _ => none
  ident
    | none => Sum.inr none
    | some x => Sum.inl (C.ident x)
  left
    | Sum.inl x => Sum.inl (C.left x)
    | Sum.inr (Sum.inl x) => Sum.inr (some (C.cod x))
    | Sum.inr (Sum.inr _) => Sum.inr none
  rite
    | Sum.inl x => Sum.inl (C.rite x)
    | Sum.inr (Sum.inl x) => Sum.inl x
    | Sum.inr (Sum.inr x) => Sum.inr x
  comp
    | Sum.inl x => Sum.inl (C.comp x)
    | Sum.inr (Sum.inl x) => Sum.inr (some (C.dom x))
    | Sum.inr (Sum.inr x) => Sum.inr x
  pair
    | Sum.inl a, Sum.inl b, _ => Sum.inl (C.pair a b (by grind))
    | Sum.inl _, Sum.inr _, _ => by contradiction
    | Sum.inr _, b, _ => Sum.inr b
  ident_dom x := by
    cases x
    case none => rfl
    case some x => simp! ; exact C.ident_dom x
  ident_cod x := by
    cases x
    case none => rfl
    case some x => simp! ; exact C.ident_cod x
  C2_ok p := by
    cases p
    case inl p => simp! ; exact C.C2_ok p
    case inr p =>
      cases p
      case inl p => rfl
      case inr p => rfl
  dom_comp p := by
    cases p
    case inl p => simp! ; exact C.dom_comp p
    case inr p =>
      cases p
      case inl p => rfl
      case inr p => rfl
  cod_comp p := by
    cases p
    case inl p => simp! ; exact C.cod_comp p
    case inr p =>
      cases p
      case inl p => rfl
      case inr p => rfl
  left_pair a b h := by
    cases a
    case inl a =>
      cases b
      case inl b => simp! ; exact C.left_pair a b (by grind)
      case inr b => simp! at h
    case inr a =>
      cases a
      case none =>
        cases b
        case inl b => simp! at h
        case inr b => rfl
      case some a =>
        cases b
        case inl b => simp! at h ; simp! ; rw [h]
        case inr b => simp! at h
  rite_pair a b h := by
    cases a
    case inl a =>
      cases b
      case inl b => simp! ; exact C.rite_pair a b (by grind)
      case inr b => simp! at h
    case inr a =>
      cases a
      case none =>
        cases b
        case inl b => rfl
        case inr b => rfl
      case some a =>
        cases b
        case inl b => rfl
        case inr b => rfl
  ident_lid x := by
    cases x
    case inl x => simp! ; exact C.ident_lid x
    case inr x => rfl
  ident_rid x := by
    cases x
    case inl x => simp! ; exact C.ident_rid x
    case inr x =>
      cases x
      case none => rfl
      case some x => simp! ; exact C.ident_dom x

/-
def poset (C : Cat.{u}) :=
  (iso C instZeroCat.zero) ⊕
  ((D : Cat.{u}) × iso C (CatSucc D) × (poset D)) -- my dependent pairs! :<

def inst_aux : ℕ → Cat
  | 0 => instZeroCat.zero
  | 1 => instOneCat.one
  | 2 => instOfNatCatOfNatNat.ofNat
  | Nat.succ n => MapCat (inst_aux n) 1 (fun _ ↦ ())

instance (n : ℕ) : OfNat Cat n where
  ofNat := inst_aux n
-/

instance (n : ℕ) (_ : n > 2) : OfNat Cat n := ⟨Poset (Fin n)⟩

-- homset:

@[simp]
def hom (C : Cat) (d c : C.C0) : Set C.C1 := { x | C.dom x = d ∧ C.cod x = c }

-- there is only one functor F : 1 → 1, this enduces a functor category ofc
-- this functor category is the same as 2:

theorem MapCat_1_1_eq_two : isom 2 (MapCat 1 1 id) := by apply isoisisom ; exact {
  F := {
    F0
      | false => Sum.inl ()
      | true => Sum.inr ()
    F1
      | none => Sum.inl {
        Carrow := ()
        Darrow := ()
        h := by rfl
      }
      | some ⊥ => Sum.inr (Sum.inl ())
      | some ⊤ => Sum.inr (Sum.inr ())
    hdom x := by
      cases x
      case none => rfl
      case some x =>
        cases x
        case false => rfl
        case true => rfl
    hcod x := by
      cases x
      case none => rfl
      case some x =>
        cases x
        case false => rfl
        case true => rfl
    }
  G := {
    F0
      | Sum.inl () => false
      | Sum.inr () => true
    F1
      | Sum.inl _ => none
      | Sum.inr (Sum.inl _) => some ⊥
      | Sum.inr (Sum.inr ()) => some ⊤
    hdom x := by
      cases x
      case inl x => rfl
      case inr x =>
        cases x
        case inl x => rfl
        case inr x => rfl
    hcod x := by
      cases x
      case inl x => rfl
      case inr x =>
        cases x
        case inl x => rfl
        case inr x => rfl
  }
  hc0 c := by
    cases c
    case false => rfl
    case true => rfl
  hd0 d := by
    cases d
    case inl d => rfl
    case inr d => rfl
  hc1 a := by
    cases a
    case none => rfl
    case some a =>
      cases a
      case false => rfl
      case true => rfl
  hd1 a := by
    cases a
    case inl a => rfl
    case inr a =>
      cases a
      case inl a => rfl
      case inr a => rfl
  }

-- adding zero does nothing:

theorem add_zero' (C : Cat) : isom (C + 0) C := by apply isoisisom ; exact {
  G := {
    F0 := Sum.inl
    F1 := Sum.inl
    hdom x := by rfl
    hcod x := by rfl
  }
  F := {
    F0
      | Sum.inl x => x
      | Sum.inr x => by contradiction
    F1
      | Sum.inl x => x
      | Sum.inr x => by contradiction
    hdom x := by
      cases x
      case inl x => rfl
      case inr x => contradiction
    hcod x := by
      cases x
      case inl x => rfl
      case inr x => contradiction
  }
  hd0 c := by rfl
  hc0 d := by
    cases d
    case inl d => rfl
    case inr d => contradiction
  hd1 a := by rfl
  hc1 a := by
    cases a
    case inl a => rfl
    case inr a => contradiction
  }

theorem add_comm' (C D : Cat) : isom (C + D) (D + C) := by apply isoisisom ; exact {
  F := {
    F0
      | Sum.inl x => Sum.inr x
      | Sum.inr x => Sum.inl x
    F1
      | Sum.inl x => Sum.inr x
      | Sum.inr x => Sum.inl x
    hdom x := by
      cases x
      case inl x => rfl
      case inr x => rfl
    hcod x := by
      cases x
      case inl x => rfl
      case inr x => rfl
  }
  G := {
    F0
      | Sum.inl x => Sum.inr x
      | Sum.inr x => Sum.inl x
    F1
      | Sum.inl x => Sum.inr x
      | Sum.inr x => Sum.inl x
    hdom x := by
      cases x
      · rfl
      rfl
    hcod x := by
      cases x
      · rfl
      rfl
  }
  hc0 c := by
    cases c
    · rfl
    rfl
  hd0 c := by
    cases c
    · rfl
    rfl
  hc1 m := by
    cases m
    · rfl
    rfl
  hd1 m :=  by
    cases m
    · rfl
    rfl
}

-- multiplication is commutative:

theorem mul_comm' (C D : Cat) : isom (C * D) (D * C) := by apply isoisisom ; exact {
  F := {
    F0 := Prod.swap
    F1 | (a,b) => (b,a)
    hdom x := by rfl
    hcod x := by rfl
  }
  G := {
    F0 | (a,b) => (b,a)
    F1 | (a,b) => (b,a)
    hdom x := by rfl
    hcod x := by rfl
  }
  hc0 c := by rfl
  hd0 d := by rfl
  hc1 a := by rfl
  hd1 a := by rfl
  }

theorem ofNatMakesSense (m n : ℕ) : isom (Poset (Fin m) + Poset (Fin n)) (Poset (Fin (m + n))) := by
  cases m
  case zero =>
  apply isoisisom ; exact {
  F := {
    F0
      | Sum.inl ⟨x,h⟩ => ⟨x, by apply lt_trans h ; simp⟩
  }
}

-- Nat to 2

def FN2 : Funct NatPoset 2 where
  F0
    | Nat.zero => false
    | Nat.succ _ => true
  F1 | ⟨_,0,_⟩ => some ⊥
     | ⟨0,_,_⟩ => none
     | ⟨_,_,_⟩ => some ⊤
  hdom | ⟨m,n,h⟩ => by
        cases n
        · cases m
          · rfl
          simp at h
        cases m
        · rfl
        rfl
  hcod | ⟨m,n,h⟩ => by
        cases n
        · rfl
        cases m
        · rfl
        rfl

-- nat ⊕ bool with ≤, (· = 0), and → :

@[simp]
def NatWith_le_eq0_imp : Cat := MapCat NatPoset 2 FN2.F0

def Labelling (C : Cat) : Type := C.C1 → Prop

def isLE : Labelling NatWith_le_eq0_imp
  | Sum.inr (Sum.inl _) => True
  | _ => False

def isLE'altConcep : Labelling NatWith_le_eq0_imp
  | Sum.inr _ => True
  | _ => False

def isEq0 : Labelling NatWith_le_eq0_imp
  | Sum.inl x => x.Darrow = some ⊥
  | _ => False

def isImp : Labelling NatWith_le_eq0_imp
  | Sum.inr (Sum.inr _) => True
  | _ => False

def is0toTrue : Labelling NatWith_le_eq0_imp := fun x ↦ ¬ (isLE x ∨ isEq0 x ∨ isImp x)

--

theorem Nat_eq_NatWithInit : isom NatPoset (MapCat 1 NatPoset (fun _ ↦ Nat.zero)) := by
  apply isoisisom ; exact {
  F := {
    F0
      | Nat.zero => Sum.inl ()
      | Nat.succ n => Sum.inr n
    F1
      | ⟨Nat.succ m,0,h⟩ => by contradiction
      | ⟨0,0,_⟩ => Sum.inr (Sum.inl ())
      | ⟨0,Nat.succ n,h⟩ => Sum.inl {
        Carrow := ()
        Darrow := ⟨0,n,by grind⟩
        h := by rfl
        }
      | ⟨Nat.succ m, Nat.succ n, h⟩ => Sum.inr (Sum.inr ⟨m,n,by grind⟩)
    hdom | ⟨m,n,h⟩ => by
          cases m
          · cases n
            · rfl
            rfl
          cases n
          · simp at h
          rfl
    hcod | ⟨m,n,h⟩ => by
          cases m
          · cases n
            · rfl
            rfl
          cases n
          · simp at h
          rfl
  }
  G := {
    F0
      | Sum.inl () => Nat.zero
      | Sum.inr n => Nat.succ n
    F1
      | Sum.inl x => ⟨0, Nat.succ (NatPoset.cod x.Darrow), Nat.zero_le _⟩
      | Sum.inr (Sum.inl ()) => NatPoset.ident Nat.zero
      | Sum.inr (Sum.inr ⟨m,n,h⟩) => ⟨Nat.succ m, Nat.succ n, Nat.succ_le_succ h⟩
    hdom x := by
      cases x
      case inl x => rfl
      case inr x =>
        cases x
        · rfl
        rfl
    hcod x := by
      cases x
      case inl x => rfl
      case inr x =>
        cases x
        · rfl
        rfl
  }
  hc0 c := by
    cases c
    · rfl
    rfl
  hd0 d := by
    cases d
    case inl d => rfl
    case inr d =>
      cases d
      · rfl
      rfl
  hc1 | ⟨m,n,h⟩ => by
        cases m
        · cases n
          · rfl
          rfl
        cases n
        · simp at h
        rfl
  hd1 a := by
    cases a
    case inl a =>
      rcases a with ⟨Ca,Da,ha⟩
      simp!
      constructor
      · rfl
      rcases Da with ⟨m,n,h⟩
      congr
    case inr a =>
      cases a
      · rfl
      rfl
  }

def isTerminal' (C : Cat) (t : C.C0) :=
  ∀ a b : C.C1, C.cod a = t → C.cod b = t → C.dom a = C.dom b → a = b

-- ⊤ is not terminal in NatWith_le_eq0_imp because
-- multiple arrows with cod = ⊤ and same dom exist
-- (⊥ → ⊤) ∘ (0 → ⊥) ≠ (n → ⊤) ∘ (0 → n)
-- (imp ∘ is0) ≠ (is0 ∘ ≤)
-- (imp ∘ is0) 0 = (is0 ∘ ≤) 0

@[simp]
def zerotoTrue : ℕ → NatWith_le_eq0_imp.C1 -- countably infinitely many distinct arrows from 0 to ⊤
  | 0 => Sum.inl ⟨NatPoset.ident Nat.zero, none, by rfl⟩
  | Nat.succ n => Sum.inl ⟨⟨0, n.succ, zero_le n.succ⟩, some ⊤, by rfl⟩

lemma same_dom :
  ∀ m n, NatWith_le_eq0_imp.dom (zerotoTrue m) = NatWith_le_eq0_imp.dom (zerotoTrue n) := by
    intro m n
    cases m
    · cases n
      · rfl
      rfl
    · cases n
      · rfl
      rfl

lemma same_cod :
  ∀ m n, NatWith_le_eq0_imp.cod (zerotoTrue m) = NatWith_le_eq0_imp.cod (zerotoTrue n) := by
    intro m n
    cases m
    · cases n
      · rfl
      rfl
    · cases n
      · rfl
      rfl

lemma not_equal_tho :
  ∀ m n, zerotoTrue m = zerotoTrue n ↔ m = n := by
    intro m n
    cases m
    · cases n
      · simp
      simp
    cases n
    · simp
    simp
-- that's all :3

-- true is terminal in the Category 2 tho:

theorem trueIsTerminalIn2 : isTerminal' 2 true := by
  intro a b ha hb hdom
  cases a
  case none =>
    cases b
    case none => rfl
    case some b =>
      cases b
      case false => contradiction
      case true => contradiction
  case some a =>
    cases b
    case none =>
      cases a
      case false => contradiction
      case true => contradiction
    case some b => congr
