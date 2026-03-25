import Lean
#check Vector
namespace Hoskinson

#eval Lean.versionString

set_option pp.notation true
set_option pp.rawOnError true
set_option hygiene false
set_option maxRecDepth 10000000
set_option maxHeartbeats 10000000

inductive Tp : Type where
  | natural : Tp
  | function : Tp → Tp → Tp
  deriving Repr, Inhabited, DecidableEq, Lean.ToExpr

notation:max "ℕ" => Tp.natural
infixr:70 " ⇒ " => Tp.function

example : Tp := ℕ ⇒ ℕ

inductive TpEnv : Type where
  | empty : TpEnv
  | extend : TpEnv → Tp → TpEnv
  deriving Repr, Inhabited, DecidableEq, Lean.ToExpr

notation:max "∅" => TpEnv.empty
infixl:50 " ▷ " => TpEnv.extend

example : TpEnv := ∅ ▷ ℕ ⇒ ℕ ▷ ℕ
-- ext (ext (Ø) (N → N)) (N)

infix:40  " ∋ " => lookup

inductive lookup : TpEnv → Tp → Type where
  | stop :
       ---------
       Γ ▷ A ∋ A
  | pop :
       Γ ∋ B
       ---------
     → Γ ▷ A ∋ B
  deriving Repr, DecidableEq, Lean.ToExpr

prefix:90 "S" => lookup.pop
notation:max "Z" => lookup.stop

infix:40  " ⊢ " => term

inductive term : TpEnv → Tp → Type where
  | var :
        Γ ∋ A
        ----------
      → Γ ⊢ A
  | lambda :
        Γ ▷ A ⊢ B
        -----------
      → Γ ⊢ A ⇒ B
  | application :
        Γ ⊢ A ⇒ B
      → Γ ⊢ A
        --------
      → Γ ⊢ B
  | zero :
        --------
        Γ ⊢ ℕ
  | succ :
        Γ ⊢ ℕ
        --------
      → Γ ⊢ ℕ
  | case :
        Γ ⊢ ℕ
      → Γ ⊢ A
      → Γ ▷ ℕ ⊢ A
        ---------------
      → Γ ⊢ A
  | mu :
        Γ ▷ A ⊢ A
        --------------
      → Γ ⊢ A
  deriving Repr, DecidableEq, Lean.ToExpr

prefix:90 "# " => term.var
prefix:50 "ƛ " => term.lambda
infixl:70 " ⬝ " => term.application
notation:max "o" => term.zero
postfix:80 " +1" => term.succ
notation:max "casesOn" => term.case
prefix:50 "μ " => term.mu

instance : OfNat (Γ ⊢ ℕ) Nat.zero where
  ofNat := o

instance [OfNat (Γ ⊢ ℕ) n] : OfNat (Γ ⊢ ℕ) (Nat.succ n) where
  ofNat := (OfNat.ofNat n) +1

example : (2 : ∅ ⊢ ℕ) = o +1 +1 := rfl

@[default_instance]
instance : OfNat (Γ ▷ A ∋ A) Nat.zero where
  ofNat := Z

@[default_instance]
instance [OfNat (Γ ∋ B) n] : OfNat (Γ ▷ A ∋ B) (Nat.succ n) where
  ofNat := S (OfNat.ofNat n)

example : (2 : ∅ ▷ ℕ ⇒ ℕ ▷ ℕ ▷ ℕ ∋ ℕ ⇒ ℕ) = S S Z := rfl


/-
class OfNatLookup (Γ : TpEnv) (n : Nat) (A : outParam Tp) where
  ofNatLookup : Γ ∋ A

instance : OfNatLookup (Γ ▷ A) Nat.zero A where
  ofNatLookup := Z

instance [OfNatLookup Γ n B] : OfNatLookup (Γ ▷ A) (Nat.succ n) B where
  ofNatLookup := S (OfNatLookup.ofNatLookup n)

@[default_instance]
instance [OfNatLookup Γ n A] : OfNat (Γ ∋ A) n where
  ofNat := OfNatLookup.ofNatLookup n
-/

-- instance [OfNatLookup Γ n A] : OfNat (Γ ∋ A) n where
--   ofNat := OfNatLookup.ofNatLookup n
-- instance : Coe Nat (Γ ∋ A) where
--   coe n := OfNatLookup.ofNatLookup n

example : (1 : ∅ ▷ ℕ ⇒ ℕ ▷ ℕ ∋ ℕ ⇒ ℕ) = S Z := rfl

def plus : Γ ⊢ ℕ ⇒ ℕ ⇒ ℕ :=
  -- μ ƛ ƛ (casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1))
  μ ƛ ƛ (casesOn (# 0) (# 1) ((# 3 ⬝ # 2 ⬝ # 0) +1))
def two_plus_two : ∅ ⊢ ℕ :=
  plus ⬝ 2 ⬝ 2

def Ch (A : Tp) : Tp := (A ⇒ A) ⇒ A ⇒ A
def suc_c : Γ ⊢ ℕ ⇒ ℕ :=
  ƛ (# Z +1)
-- twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ # "s" · (# "s" · # "z")
def two_c : Γ ⊢ Ch A :=
  -- ƛ ƛ (# S Z ⬝ (# S Z ⬝ # Z))
  ƛ ƛ (# 1 ⬝ (# 1 ⬝ # 0))

-- plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ # "m" · # "s" · (# "n" · # "s" · # "z")
def plus_c : Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A :=
  ƛ ƛ ƛ ƛ (# S S S Z ⬝ # S Z ⬝ (# S S Z ⬝ # S Z ⬝ # Z))
def plus_c' : Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A :=
  ƛ ƛ ƛ ƛ (# (3 : _ ∋ Ch A) ⬝ # 1 ⬝ (# (2 : _ ∋ Ch A) ⬝ # 1 ⬝ # 0))

def two : ∅ ⊢ ℕ := two_c ⬝ suc_c ⬝ 0

def rmap (Γ Δ : TpEnv) : Type :=
  ∀ {A : Tp}, (Γ ∋ A) → (Δ ∋ A)
def smap (Γ Δ : TpEnv) : Type :=
  ∀ {A : Tp}, (Γ ∋ A) → (Δ ⊢ A)
def tmap (Γ Δ : TpEnv) : Type :=
  ∀ {A : Tp}, (Γ ⊢ A) → (Δ ⊢ A)

infix:30 " →ʳ " => rmap
infix:30 " →ˢ " => smap
infix:30 " →ᵗ " => tmap

def ren_ext {Γ Δ : TpEnv} {A :Tp} (ρ : Γ →ʳ Δ) : (Γ ▷ A →ʳ Δ ▷ A)
  | _ , Z  =>  Z
  | _ , S x  =>  S (ρ x)

def ren {Γ Δ : TpEnv} (ρ : Γ →ʳ Δ) : Γ →ᵗ Δ
  | _ , # x => # (ρ x)
  | _ , ƛ N => ƛ (ren (ren_ext ρ) N)
  | _ , L ⬝ M => ren ρ L ⬝ ren ρ M
  | _ , o => o
  | _ , M +1 => ren ρ M +1
  | _ , casesOn L M N => casesOn (ren ρ L) (ren ρ M) (ren (ren_ext ρ) N)
  | _ , μ N => μ (ren (ren_ext ρ) N)

def lift {Γ : TpEnv} {A : Tp} : Γ →ᵗ Γ ▷ A := ren (fun x => S x)

def sub_ext {Γ Δ : TpEnv} {A : Tp} (σ : Γ →ˢ Δ) : (Γ ▷ A →ˢ Δ ▷ A)
  | _ , Z    --=>  # Z
  | _ , S x  =>  lift (σ x)

def sub {Γ Δ : TpEnv} (σ : Γ →ˢ Δ) : Γ →ᵗ Δ
  | _ , # x => σ x
  | _ , ƛ N => ƛ (sub (sub_ext σ) N)
  | _ , L ⬝ M => sub σ L ⬝ sub σ M
  | _ , o => o
  | _ , M +1 => sub σ M +1
  | _ , casesOn L M N => casesOn (sub σ L) (sub σ M) (sub (sub_ext σ) N)
  | _ , μ N => μ (sub (sub_ext σ) N)

def sigma_0 (M : Γ ⊢ A) : Γ ▷ A →ˢ Γ
  | _ , Z    =>  M
  | _ , S x  =>  # x

-- @[reducible]
def subst {Γ : TpEnv} {A B : Tp} (N : Γ ▷ A ⊢ B) (M : Γ ⊢ A) : Γ ⊢ B
  := sub (sigma_0 M) N

example : subst (ƛ (# S Z ⬝ (# S Z ⬝ # Z))) suc_c = (ƛ (suc_c ⬝ (suc_c ⬝ # Z)) : ∅ ⊢ ℕ ⇒ ℕ) := by rfl

inductive Value : Γ ⊢ A → Type where
  | lambda :
      Value (ƛ N)
  | zero :
      Value o
  | succ :
      Value V → Value (V +1)
  deriving Repr, DecidableEq, Lean.ToExpr

open Value

infix:30 " ~> " => reduce

inductive reduce : Γ ⊢ A → Γ ⊢ A → Type where
  | xi_app_1 :
      L ~> L' → L ⬝ M ~> L' ⬝ M
  | xi_app_2 :
      Value V → M ~> M' → V ⬝ M ~> V ⬝ M'
  | beta :
      Value W → (ƛ N) ⬝ W ~> subst N W
  | xi_succ :
      M ~> M' → M +1 ~> M' +1
  | xi_case :
      L ~> L' → casesOn L M N ~> casesOn L' M N
  | beta_zero :
      casesOn o M N ~> M
  | beta_succ :
      Value V → casesOn (V +1) M N ~> subst N V
  | beta_mu :
      μ N ~> subst N (μ N)
  deriving Repr, Lean.ToExpr

open reduce


-- inductive star : (Γ ⊢ A) → (Γ ⊢ A) → Type where
--   | none :
--       star M M
--   | one :
--          (M ~> N)
--          ----------
--        → star M N
--    | two :
--          star L M
--        → star M N
--          ----------
--        → star L N
-- infix:20 "~>*" => star
-- instance : Trans (star : (Γ ⊢ A) → (Γ ⊢ A) → Type)
--                  (star : (Γ ⊢ A) → (Γ ⊢ A) → Type)
--                  (star : (Γ ⊢ A) → (Γ ⊢ A) → Type) where
--   trans := star.two

infix:30 " ~>> "  => reduce_many

inductive reduce_many : Γ ⊢ A → Γ ⊢ A → Type where
  | nil :
      ∀ M, M ~>> M
  | cons :
      ∀ L, L ~> M
         → M ~>> N
           -------
         → L ~>> N
  deriving Repr, Lean.ToExpr

open reduce_many

def one_one : (L ~> M) → (M ~> N) → (L ~>> N)
  | L_to_M, M_to_N => cons _ L_to_M (cons _ M_to_N (nil _))

instance : Trans (.~>.  : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>.  : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>>. : Γ ⊢ A → Γ ⊢ A → Type) where
  trans := one_one

/-
def one_many : (L ~> M) → (M ~>> N) → (L ~>> N)
  | L_to_M, M_to_N => cons _ L_to_M M_to_N

instance : Trans (.~>.  : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>>. : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>>. : Γ ⊢ A → Γ ⊢ A → Type) where
  trans := one_many
-/

def many_one : (L ~>> M) → (M ~> N) → (L ~>> N)
  | nil _, M_to_N  => cons _ M_to_N (nil _)
  | cons _ L_to_P P_to_M , M_to_N => cons _ L_to_P (many_one P_to_M M_to_N)

instance : Trans (.~>>. : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>.  : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>>. : Γ ⊢ A → Γ ⊢ A → Type) where
  trans := many_one

/-
def many_many : (L ~>> M) → (M ~>> N) → (L ~>> N)
  | nil _, M_to_N  => M_to_N
  | cons _ L_to_P P_to_M , M_to_N => cons _ L_to_P (many_many P_to_M M_to_N)

instance : Trans (.~>>. : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>>. : Γ ⊢ A → Γ ⊢ A → Type)
                 (.~>>. : Γ ⊢ A → Γ ⊢ A → Type) where
  trans := many_many
-/

example : two ~> (ƛ (suc_c ⬝ (suc_c ⬝ # Z))) ⬝ 0
    := xi_app_1 (beta lambda)

example : (ƛ (suc_c ⬝ (suc_c ⬝ # Z))) ⬝ (0 : ∅ ⊢ ℕ) ~> suc_c ⬝ (suc_c ⬝ 0)
    := beta zero

example : (suc_c ⬝ (suc_c ⬝ 0) : ∅ ⊢ ℕ) ~> suc_c ⬝ 1
    := xi_app_2 lambda (beta zero)

example : (suc_c ⬝ 1 : ∅ ⊢ ℕ) ~> 2
    := beta (succ zero)

def two_to_2 :=
  calc
    (two_c ⬝ suc_c ⬝ 0 : ∅ ⊢ ℕ)
      ~> (ƛ (suc_c ⬝ (suc_c ⬝ # Z))) ⬝ 0  := xi_app_1 (beta lambda)
    _ ~> (suc_c ⬝ (suc_c ⬝ 0))            := beta zero
    _ ~> suc_c ⬝ 1                        := xi_app_2 lambda (beta zero)
    _ ~> 2                                := beta (succ zero)

example : two ~>> 2 := two_to_2

inductive Progress : Γ ⊢ A → Type where
  | step :
      M ~> N → Progress M
  | done :
      Value V → Progress V
  -- deriving Repr, Lean.ToExpr

open Progress

abbrev progress : ∀ (M : ∅ ⊢ A), Progress M
  | (# x) => by contradiction
  | (ƛ N) => done lambda
  | (L ⬝ M) =>
      match progress L with
        | step L_to_L' => step (xi_app_1 L_to_L')
        | done v =>
            match progress M with
              | step M_to_M' => step (xi_app_2 v M_to_M')
              | done w =>
                  match v with
                    | Value.lambda => step (beta w)
  | o => done zero
  | (M +1) =>
      match progress M with
        | step M_to_M' => step (xi_succ M_to_M')
        | done v => done (succ v)
  | (casesOn L M N) =>
      match progress L with
        | step L_to_L' => step (xi_case L_to_L')
        | done v =>
            match v with
              | Value.zero => step beta_zero
              | Value.succ v => step (beta_succ v)
  | (μ N) => step beta_mu

inductive Finished (N : ∅ ⊢ A) : Type where
  | done : Value N → Finished N
  | out_of_gas : Finished N
  deriving Repr, Lean.ToExpr

open Finished

inductive Evaluation (L : ∅ ⊢ A) : Type where
  | evaluation : (L ~>> N) → Finished N → Evaluation L
  deriving Repr, Lean.ToExpr

open Evaluation

abbrev evaluate (n : Nat) (L : ∅ ⊢ A) : Evaluation L :=
  match n with
    | Nat.zero => evaluation (nil _) out_of_gas
    | Nat.succ n =>
        match progress L with
          | Progress.done v => evaluation (nil _) (done v)
          | @Progress.step _ _ _ M L_to_M =>
              match evaluate n M with
                | evaluation M_to_N f => evaluation (cons L L_to_M M_to_N) f


#eval two
#eval (evaluate 10 two)

example :
  two =
    (ƛ ƛ # S Z ⬝ (# S Z ⬝ # Z)) ⬝ (ƛ # Z +1) ⬝ o
  := by rfl

example :
  (evaluate 10 two) =
    (evaluation
          (cons ((ƛ ƛ # S Z ⬝ (# S Z ⬝ # Z)) ⬝ (ƛ # Z +1) ⬝ o) (beta lambda).xi_app_1
            (cons ((ƛ (ƛ # Z +1) ⬝ ((ƛ # Z +1) ⬝ # Z)) ⬝ o) (beta zero)
              (cons ((ƛ # Z +1) ⬝ ((ƛ # Z +1) ⬝ o)) (xi_app_2 lambda (beta zero))
                (cons ((ƛ # Z +1) ⬝ o +1) (beta zero.succ) (nil (o +1 +1))))))
          (Finished.done zero.succ.succ))

  := by
    rfl

#eval two_plus_two
#eval (evaluate 100 two_plus_two)

example :
  two_plus_two =
    (μ ƛ ƛ casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1)) ⬝ o +1 +1 ⬝ o +1 +1
  := by
    rfl

example :
  evaluate 100 two_plus_two =
    evaluation
    (cons ((μ ƛ ƛ casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1)) ⬝ o +1 +1 ⬝ o +1 +1) beta_mu.xi_app_1.xi_app_1
      (cons
        ((ƛ
              ƛ
                casesOn (# Z) (# S Z)
                  (((μ ƛ ƛ casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1)) ⬝ # S S Z ⬝ # Z) +1)) ⬝
            o +1 +1 ⬝
          o +1 +1)
        (beta zero.succ.succ).xi_app_1
        (cons
          ((ƛ
              casesOn (# Z) (o +1 +1)
                (((μ ƛ ƛ casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1)) ⬝ o +1 +1 ⬝ # Z) +1)) ⬝
            o +1 +1)
          (beta zero.succ.succ)
          (cons
            (casesOn (o +1 +1) (o +1 +1)
              (((μ ƛ ƛ casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1)) ⬝ o +1 +1 ⬝ # Z) +1))
            (beta_succ zero.succ)
            (cons (((μ ƛ ƛ casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1)) ⬝ o +1 +1 ⬝ o +1) +1)
              beta_mu.xi_app_1.xi_app_1.xi_succ
              (cons
                (((ƛ
                        ƛ
                          casesOn (# Z) (# S Z)
                            (((μ ƛ ƛ casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1)) ⬝ # S S Z ⬝ # Z) +1)) ⬝
                      o +1 +1 ⬝
                    o +1) +1)
                (beta zero.succ.succ).xi_app_1.xi_succ
                (cons
                  (((ƛ
                        casesOn (# Z) (o +1 +1)
                          (((μ ƛ ƛ casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1)) ⬝ o +1 +1 ⬝ # Z) +1)) ⬝
                      o +1) +1)
                  (beta zero.succ).xi_succ
                  (cons
                    (casesOn (o +1) (o +1 +1)
                        (((μ ƛ ƛ casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1)) ⬝ o +1 +1 ⬝ # Z) +1) +1)
                    (beta_succ zero).xi_succ
                    (cons (((μ ƛ ƛ casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1)) ⬝ o +1 +1 ⬝ o) +1 +1)
                      beta_mu.xi_app_1.xi_app_1.xi_succ.xi_succ
                      (cons
                        (((ƛ
                                  ƛ
                                    casesOn (# Z) (# S Z)
                                      (((μ ƛ ƛ casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1)) ⬝ # S S Z ⬝
                                          # Z) +1)) ⬝
                                o +1 +1 ⬝
                              o) +1 +1)
                        (beta zero.succ.succ).xi_app_1.xi_succ.xi_succ
                        (cons
                          (((ƛ
                                  casesOn (# Z) (o +1 +1)
                                    (((μ ƛ ƛ casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1)) ⬝ o +1 +1 ⬝
                                        # Z) +1)) ⬝
                                o) +1 +1)
                          (beta zero).xi_succ.xi_succ
                          (cons
                            (casesOn o (o +1 +1)
                                  (((μ ƛ ƛ casesOn (# Z) (# S Z) ((# S S S Z ⬝ # S S Z ⬝ # Z) +1)) ⬝ o +1 +1 ⬝
                                      # Z) +1) +1 +1)
                            beta_zero.xi_succ.xi_succ (nil (o +1 +1 +1 +1))))))))))))))
    (Finished.done zero.succ.succ.succ.succ)
  := by
    rfl

-- code below by Wojciech Nawrocki

/-
open Lean Elab Meta Command in
elab tk:"#reduce_full" t:term : command => do
  withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_reduce do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
      let e ← withTransparency (mode := TransparencyMode.all) <| Meta.reduce e (explicitOnly := false) (skipProofs := false) (skipTypes := false)
      logInfoAt tk e
-/

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Hoskinson.reduce_many.cons]
partial def reduce_many.delabCons : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``reduce_many.cons 7
  let L ← withNaryArg 4 delab
  let M ← withNaryArg 2 delab
  let r ← withNaryArg 5 delab
  let rest ← withNaryArg 6 go
  `(calc
    $L ~> $M := $r
    $rest*
  )
where go : DelabM (TSyntaxArray ``calcStep) := do
  let e ← getExpr
  if e.isAppOfArity' ``reduce_many.nil 3 then
    return #[]
  guard $ e.isAppOfArity' ``reduce_many.cons 7
  let M ← withNaryArg 2 delab
  let r ← withNaryArg 5 delab
  let s ← `(calcStep|_ ~> $M := $r)
  let rest ← withNaryArg 6 go
  return #[s] ++ rest


#eval (evaluate 10 two)
#eval (evaluate 100 two_plus_two)

example :
  evaluate 10 two =
    evaluation
      (calc
        (ƛ ƛ # S Z ⬝ (# S Z ⬝ # Z)) ⬝ (ƛ # Z +1) ⬝ o~>(ƛ (ƛ # Z +1) ⬝ ((ƛ # Z +1) ⬝ # Z)) ⬝ o := (beta lambda).xi_app_1
        _ ~> (ƛ # Z +1) ⬝ ((ƛ # Z +1) ⬝ o) := (beta zero)
        _ ~> (ƛ # Z +1) ⬝ o +1 := (xi_app_2 lambda (beta zero))
        _ ~> o +1 +1 := beta zero.succ)
      (Finished.done zero.succ.succ)
  := by
    rfl



-- set_option pp.notation false


-- Exercise. Add products, as detailed in
--  https://plfa.inf.ed.ac.uk/More/#products
-- Pick suitable notations for introduction and elimination
-- of products that won't conflict.
Hoskinson.lean
18 KB
