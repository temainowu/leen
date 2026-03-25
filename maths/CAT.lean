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

@[match_pattern, simp]
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

@[match_pattern, simp]
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

@[match_pattern, simp]
instance : Add Cat where
  add := coprod

-- Product Category

@[simp] -- useful auxiliary function for prod cats:
def mpt {α β γ δ} (f : α → β) (g : γ → δ) (x : α × γ) : (β × δ) := ⟨f x.fst, g x.snd⟩

@[match_pattern, simp]
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

@[match_pattern, simp]
instance : Mul Cat where
  mul := prod

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

@[simp]
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

structure wierdIso (C D : Cat) where
  F0 : C.C1 → D.C0
  F1 : C.C2 → D.C1
  G0 : D.C0 → C.C1
  G1 : D.C1 → C.C2
  fg0 : ∀ x, F0 (G0 x) = x
  gf0 : ∀ x, G0 (F0 x) = x
  fg1 : ∀ x, F1 (G1 x) = x
  gf1 : ∀ x, G1 (F1 x) = x

@[simp]
def NatWIso : wierdIso NatMonoid NatPoset where
  F0 := id
  F1 x := ⟨x.snd, x.snd + x.fst, Nat.le_add_right x.snd x.fst⟩
  G0 := id
  G1 x := (x.n - x.m, x.m)
  fg0 x := by rfl
  gf0 x := by rfl
  fg1 | ⟨m,n,h⟩ => by simp! ; rw [add_comm, Nat.sub_add_cancel h]
  gf1 | ⟨m,n⟩ => by simp

lemma NatPosetCod_in_Monoid : ∀ x, NatWIso.F0 (NatMonoid.comp (NatWIso.G1 x)) = NatPoset.cod x := by
  intro x
  simp!
  rw [Nat.sub_add_cancel x.h]

lemma NatPosetDom_in_Monoid : ∀ x, NatWIso.F0 (NatMonoid.rite (NatWIso.G1 x)) = NatPoset.dom x := by
  intro x
  rfl

lemma inj {a b} (f : a → b) : (∃ g : (b → a), ∀ x, g (f x) = x) → ∀ x y, (f x = f y) → (x = y) := by
  intro h x y hxy
  grind

lemma h (wi : wierdIso C D) : ∀ x, wi.F0 (C.comp (wi.G1 x)) = D.cod x := by
  intro x
  apply inj wi.G0 (by use wi.F0 ; exact wi.fg0)
  rw [wi.gf0]
  have h : ∃ y, wi.G1 x = y ∧ x = wi.F1 y := by
    use wi.G1 x
    constructor
    · rfl
    symm
    exact wi.fg1 x
  rcases h with ⟨y,hy1,hy2⟩
  rw [hy1, hy2]
  sorry


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
    | Sum.inl a, Sum.inl b, h => Sum.inl (C.pair a b (by simp! at h ; exact h))
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
      case inl b => simp! ; exact C.left_pair a b (by simp! at h ; exact h)
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
      case inl b => simp! ; exact C.rite_pair a b (by simp! at h ; exact h)
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

@[match_pattern, simp]
instance (n : ℕ) : OfNat Cat n := ⟨Poset (Fin n)⟩

-- homset:

@[simp]
def hom (C : Cat) (d c : C.C0) : Set C.C1 := { x | C.dom x = d ∧ C.cod x = c }

-- adding zero does nothing:

theorem add_zero' {C : Cat} : isom (C + 0) C := by apply isoisisom ; exact {
  G := {
    F0 := Sum.inl
    F1 := Sum.inl
    hdom x := by rfl
    hcod x := by rfl
  }
  F := {
    F0
      | Sum.inl x => x
      | Sum.inr ⟨_,h⟩ => by contradiction
    F1
      | Sum.inl x => x
      | Sum.inr ⟨⟨_,h⟩,_,_⟩ => by contradiction
    hdom x := by
      cases x
      case inl x => rfl
      case inr x => rcases x with ⟨⟨_,h⟩,_,_⟩ ; contradiction
    hcod x := by
      cases x
      case inl x => rfl
      case inr x => rcases x with ⟨⟨_,h⟩,_,_⟩ ; contradiction
  }
  hd0 c := by rfl
  hc0 d := by
    cases d
    case inl d => rfl
    case inr d => rcases d with ⟨_,h⟩ ; contradiction
  hd1 a := by rfl
  hc1 a := by
    cases a
    case inl a => rfl
    case inr a => rcases a with ⟨⟨_,h⟩,_,_⟩ ; contradiction
  }

theorem add_comm' {C D : Cat} : isom (C + D) (D + C) := by apply isoisisom ; exact {
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

theorem isom_trans {A B C : Cat} : isom A B → isom B C → isom A C := by
  intro hab hbc
  rcases hab with ⟨Fab,Gab,hab⟩
  rcases hbc with ⟨Fbc,Gbc,hbc⟩
  apply isoisisom
  exact {
    F := {
      F0 x := Fbc.F0 (Fab.F0 x)
      F1 x := Fbc.F1 (Fab.F1 x)
      hdom x := by rw [Fbc.hdom, Fab.hdom]
      hcod x := by rw [Fbc.hcod, Fab.hcod]
    }
    G := {
      F0 x := Gab.F0 (Gbc.F0 x)
      F1 x := Gab.F1 (Gbc.F1 x)
      hdom x := by rw [Gab.hdom, Gbc.hdom]
      hcod x := by rw [Gab.hcod, Gbc.hcod]
    }
    hc0 c := by simp! ; rw [hbc.1, hab.1]
    hd0 d := by simp! ; rw [hab.2.1, hbc.2.1]
    hc1 m := by simp! ; rw [hbc.2.2.1, hab.2.2.1]
    hd1 m := by simp! ; rw [hab.2.2.2, hbc.2.2.2]
  }

theorem isom_refl {C : Cat} : isom C C := by apply isoisisom ; exact {
  F := {
    F0 := id
    F1 := id
    hdom x := by rfl
    hcod x := by rfl
  }
  G := {
    F0 := id
    F1 := id
    hdom x := by rfl
    hcod x := by rfl
  }
  hc0 c := by rfl
  hd0 d := by rfl
  hc1 m := by rfl
  hd1 m := by rfl
}

-- multiplication is commutative:

theorem mul_comm' (C D : Cat) : isom (C * D) (D * C) := by apply isoisisom ; exact {
  F := {
    F0 | (a,b) => (b,a)
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

-- def add (C D)

theorem mul_one' (C : Cat) : isom (C * 1) C := by apply isoisisom ; exact {
  F := {
    F0 := Prod.fst
    F1 := Prod.fst
    hdom x := by rfl
    hcod x := by rfl
  }
  G := {
    F0 x := (x, ⟨0,by simp⟩)
    F1 x := (x, ⟨0,0,by rfl⟩)
    hdom x := by rfl
    hcod x := by rfl
  }
  hc0 | ⟨c,⟨z,h⟩⟩ => by
        cases z
        · rfl
        contradiction
  hd0 x := by rfl
  hc1 | ⟨m,⟨⟨a,_⟩,⟨b,_⟩,h⟩⟩ => by
        simp!
        congr
        · cases a
          · rfl
          contradiction
        cases b
        · rfl
        contradiction
  hd1 m := by rfl
}

theorem mul_add' (A B C : Cat) : isom (A * (B + C)) ((A * B) + (A * C)) :=
  by apply isoisisom ; exact {
  F := {
    F0
      | ⟨a, Sum.inl b⟩ => Sum.inl (a,b)
      | ⟨a, Sum.inr c⟩ => Sum.inr (a,c)
    F1
      | ⟨a, Sum.inl b⟩ => Sum.inl (a,b)
      | ⟨a, Sum.inr c⟩ => Sum.inr (a,c)
    hdom | ⟨a,bc⟩ => by
          cases bc
          case inl b => rfl
          case inr c => rfl
    hcod | ⟨a,bc⟩ => by
          cases bc
          case inl b => rfl
          case inr c => rfl
  }
  G := {
    F0
      | Sum.inl ⟨a,b⟩ => (a, Sum.inl b)
      | Sum.inr ⟨a,c⟩ => (a, Sum.inr c)
    F1
      | Sum.inl ⟨a,b⟩ => (a, Sum.inl b)
      | Sum.inr ⟨a,c⟩ => (a, Sum.inr c)
    hdom
      | Sum.inl x => by rfl
      | Sum.inr x => by rfl
    hcod
      | Sum.inl x => by rfl
      | Sum.inr x => by rfl
  }
  hc0 | ⟨a,bc⟩ => by
        cases bc
        · rfl
        rfl
  hd0 x := by
    cases x
    · rfl
    rfl
  hc1 | ⟨a,bc⟩ => by
        cases bc
        · rfl
        rfl
  hd1 m := by
    cases m
    · rfl
    rfl
}

structure C1C1 (C D : Cat) (c : C.C0) (d : D.C0) where
  Carrow : C.C1
  Darrow : D.C1
  hc : C.cod Carrow = c
  hd : D.dom Darrow = d


def connect_once (C D : Cat) (c : C.C0) (d : D.C0) : Cat where
  C0 := C.C0 ⊕ D.C0
  C1 := (C.C1 ⊕ D.C1) ⊕ C1C1 C D c d
  C2 := (C.C2 ⊕ D.C2) ⊕ ()
  dom
    | Sum.inl (Sum.inl x) => Sum.inl (C.dom x)
    | Sum.inl (Sum.inr x) => Sum.inr (D.dom x)
    | Sum.inr x => Sum.inl (C.dom x.Carrow)
  cod
    | Sum.inl (Sum.inl x) => Sum.inl (C.cod x)
    | Sum.inl (Sum.inr x) => Sum.inr (D.cod x)
    | Sum.inr x => Sum.inr (D.cod x.Darrow)
  ident
    | Sum.inl x => Sum.inl (Sum.inl (C.ident x))
    | Sum.inr x => Sum.inl (Sum.inr (D.ident x))
  left x := x.left

/-
theorem ofNatDistrAdd (m n : ℕ) : isom ((if h : 0 < n then MapCat (OfNat.ofNat m) (OfNat.ofNat n) (fun _ ↦ ⟨0, h⟩) else OfNat.ofNat m)) (OfNat.ofNat (m + n)) := by
  cases n
  case zero => exact isom_refl
  case succ n =>
    apply isoisisom ; exact {
  F := {
    F0
      | Sum.inl ⟨x,h⟩ => ⟨x, by apply lt_trans h ; simp⟩
      | Sum.inr ⟨x,_⟩ => ⟨m + x, _⟩
    F1
      | Sum.inl ⟨⟨⟨x,_⟩,⟨_,_⟩,_⟩,⟨⟨_,_⟩,⟨y,_⟩,_⟩,c⟩ => ⟨⟨x,_⟩,⟨m + y,_⟩,_⟩
      | Sum.inr (Sum.inl ⟨⟨x,_⟩,⟨y,_⟩,_⟩) => ⟨⟨x,_⟩,⟨y,_⟩,_⟩
      | Sum.inr (Sum.inr ⟨⟨x,_⟩,⟨y,_⟩,_⟩) => ⟨⟨m + x,_⟩,⟨m + y,_⟩,_⟩
    hdom x := by
      cases x
      case inl x =>
        rcases x with ⟨⟨_,_⟩,⟨_,_⟩,_⟩
        simp
      case inr x =>
        cases x
        case inl x =>
          rcases x with ⟨⟨_,_⟩,⟨_,_⟩,_⟩
          simp
        case inr x =>
          rcases x with ⟨⟨_,_⟩,⟨_,_⟩,_⟩
          simp
    hcod x := by
      cases x
      case inl x =>
        rcases x with ⟨⟨_,_⟩,⟨_,_⟩,_⟩
        simp
      case inr x =>
        cases x
        case inl x =>
          rcases x with ⟨⟨_,_⟩,⟨_,_⟩,_⟩
          simp
        case inr x =>
          rcases x with ⟨⟨_,_⟩,⟨_,_⟩,_⟩
          simp
  }
  G := {
    F0 | ⟨x,_⟩ => if h : x < m then Sum.inl ⟨x,h⟩ else Sum.inr ⟨x-m,_⟩
    F1 | ⟨⟨x,_⟩,⟨y,_⟩,_⟩ =>
        if hx : x < m
        then
          if hy : y < m
          then Sum.inr (Sum.inl ⟨⟨x,_⟩,⟨y,_⟩,_⟩)
          else Sum.inl ⟨⟨⟨x,_⟩,⟨m,_⟩,_⟩,⟨⟨0,_⟩,⟨m + y,_⟩,_⟩,_⟩
        else Sum.inr (Sum.inr _)
    hdom x := by
      cases x
  }
}
-/

-- Nat to 2

def FN2 : Funct NatPoset 2 where
  F0
    | Nat.zero => ⟨0, by simp⟩
    | Nat.succ _ => ⟨1, by simp⟩
  F1 | ⟨_,0,_⟩ => ⟨0,0,by rfl⟩
     | ⟨0,_,_⟩ => ⟨0,1,by simp⟩
     | ⟨_,_,_⟩ => ⟨1,1,by rfl⟩
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
  | Sum.inl x => x.Darrow = ⟨0, 0, by rfl⟩
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
      | Nat.zero => Sum.inl ⟨0, by simp⟩
      | Nat.succ n => Sum.inr n
    F1
      | ⟨Nat.succ m,0,h⟩ => by contradiction
      | ⟨0,0,_⟩ => Sum.inr (Sum.inl ⟨0,0,by rfl⟩)
      | ⟨0,Nat.succ n,h⟩ => Sum.inl {
        Carrow := ⟨0,0,by rfl⟩
        Darrow := ⟨0,n,zero_le n⟩
        h := by rfl
        }
      | ⟨Nat.succ m, Nat.succ n, h⟩ => Sum.inr (Sum.inr ⟨m,n,Nat.succ_le_succ_iff.1 h⟩)
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
      | Sum.inl ⟨0,_⟩ => Nat.zero
      | Sum.inr n => Nat.succ n
    F1
      | Sum.inl x => ⟨0, Nat.succ (NatPoset.cod x.Darrow), Nat.zero_le _⟩
      | Sum.inr (Sum.inl _) => NatPoset.ident Nat.zero
      | Sum.inr (Sum.inr ⟨m,n,h⟩) => ⟨Nat.succ m, Nat.succ n, Nat.succ_le_succ h⟩
    hdom x := by
      cases x
      case inl x =>
        rcases x with ⟨⟨⟨m,_⟩,_,_⟩,_,_⟩
        cases m
        · rfl
        contradiction
      case inr x =>
        cases x
        case inl x =>
          rcases x with ⟨⟨m,_⟩,_,_⟩
          cases m
          · rfl
          contradiction
        case inr x => rfl
    hcod x := by
      cases x
      case inl x => rfl
      case inr x =>
        cases x
        case inl x =>
          rcases x with ⟨_,⟨m,_⟩,_⟩
          cases m
          · rfl
          contradiction
        case inr x => rfl
  }
  hc0 c := by
    cases c
    · rfl
    rfl
  hd0 d := by
    cases d
    case inl d =>
      rcases d with ⟨d,_⟩
      cases d
      · rfl
      contradiction
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
      rcases a with ⟨Ca,⟨m,n,h⟩,ha⟩
      simp!
      constructor
      · rcases Ca with ⟨⟨m,_⟩,⟨n,_⟩,_⟩
        congr
        · cases m
          · rfl
          contradiction
        cases n
        · rfl
        contradiction
      congr
    case inr a =>
      cases a
      case inl a =>
        rcases a with ⟨⟨m,_⟩,⟨n,_⟩,_⟩
        simp!
        congr
        · cases m
          · rfl
          contradiction
        cases n
        · rfl
        contradiction
      case inr a => rfl
  }

def isTerminal (C : Cat) (t : C.C0) :=
  ∀ a b : C.C1, C.cod a = t → C.cod b = t → C.dom a = C.dom b → a = b

-- ⊤ is not terminal in NatWith_le_eq0_imp because
-- multiple arrows with cod = ⊤ and same dom exist
-- (⊥ → ⊤) ∘ (0 → ⊥) ≠ (n → ⊤) ∘ (0 → n)
-- (imp ∘ is0) ≠ (is0 ∘ ≤)
-- (imp ∘ is0) 0 = (is0 ∘ ≤) 0

@[simp]
def zerotoTrue : ℕ → NatWith_le_eq0_imp.C1 -- countably infinitely many distinct arrows from 0 to ⊤
  | 0 => Sum.inl ⟨NatPoset.ident Nat.zero, ⟨0, 1, by simp⟩, by rfl⟩
  | Nat.succ n => Sum.inl ⟨⟨0, n.succ, zero_le n.succ⟩, ⟨1, 1, by rfl⟩, by rfl⟩

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

theorem trueIsTerminalIn2 : isTerminal 2 ⟨0, by simp⟩ := by
  intro a b ha hb hdom
  rcases a with ⟨⟨an0,_⟩,⟨an,_⟩,ha⟩
  rcases b with ⟨⟨bn0,_⟩,⟨bn,_⟩,hb⟩
  simp! [OfNat.ofNat] at *
  constructor
  · exact hdom
  grind
