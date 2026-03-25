import Mathlib

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

--

structure RankList where
  r : ℤ
  v : List ℚ

def add (x y : RankList) : RankList :=
  if hx : x.v = [] then y else if hy : y.v = [] then x else if hr : x.r = y.r then
        (if hv : x.v[0]'(by
          revert hx
          cases x.v
          · simp
          simp) + y.v[0]'(by
            revert hy
            cases y.v
            · simp
            simp) = 0 then add ⟨x.r-1, x.v.tail⟩ ⟨y.r-1,y.v⟩
        else ⟨x.r, zipWith0 (· + ·) x.v y.v⟩)
  else if hr : x.r < y.r
       then ⟨y.r,
        zipWith0 (· + ·) y.v (List.replicate (y.r - x.r).toNat 0 ++ x.v)⟩
       else add y x
termination_by (y.r - x.r) + (y.v.length + x.v.length)
decreasing_by
  · simp


structure Fluxion where
  f : RankList
  is_zero : f.v = [] → f.r = 0
  no_lead : f.v.head? ≠ some 0
  no_trail : f.v.getLast? ≠ some 0

namespace Fluxion

instance : Zero Fluxion where
  zero := ⟨⟨0, []⟩, by simp, by simp, by simp⟩

instance : One Fluxion where
  one := ⟨⟨0, [1]⟩, by simp, by simp, by simp⟩

def add (x y : Fluxion) : Fluxion where
  f :=

instance : Add Fluxion where
  add := add

instance : CommRing Fluxion where

end Fluxion
