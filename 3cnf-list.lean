import Mathlib

inductive P where
  | v : Bool → ℕ → P
  | o : Bool → List P → P

namespace P

instance : Zero P where
  zero := o ⊥ []


instance : One P where
  one := o ⊤ []

@[simp]
def neg : P → P
  | v t n => v (¬t) n
  | o t [] => o (¬t) []
  | o t (x :: xs) => o (¬t) (neg x :: [neg (o t xs)])

instance : Neg P where
  neg := neg

structure Pu where
  v : P
  nn : -(-v) = v

instance : Neg Pu where
  neg x := ⟨-x.v,by rw [x.nn]⟩


end P
