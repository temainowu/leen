import Mathlib

structure Fluxion α where
  x : List α
  m : ℤ

def lzw {α} (f : α → α → α) : (List α) → (List α) → List α
    | [], [] => []
    |  a, [] => a
    | [], b  => b
    | x :: xs, y :: ys => f x y :: lzw f xs ys

def dn {α} [Zero α] (a : Fluxion α) (b : Fluxion α) : Fluxion α × Fluxion α :=
  match a, b with
    | ⟨xs,m⟩, ⟨ys,m'⟩ => if m < m' then dn ⟨0 :: xs, m + 1⟩ ⟨ys,m'⟩ else
                         if m > m' then dn ⟨xs,m⟩ ⟨0 :: ys, m' + 1⟩ else
                         ⟨a, b⟩
termination_by Int.natAbs (a.m - b.m)

instance {α} : Zero (Fluxion α) := ⟨⟨[],0⟩⟩

instance {α} [One α] : One (Fluxion α) := ⟨⟨[1],0⟩⟩

instance {α} [Neg α] : Neg (List α) :=
  ⟨List.map (- ·)⟩

instance {α} [Neg α] : Neg (Fluxion α) :=
  ⟨fun x ↦ ⟨-x.x, x.m⟩⟩

def fluxionAdd {α} [Zero α] [Add α] (a b : Fluxion α) : Fluxion α :=
  match a, b with
  | ⟨x, m⟩, ⟨x', m'⟩ =>
    if m < m' then fluxionAdd ⟨0 :: x, m+1⟩ ⟨x', m'⟩ else
    if m > m' then fluxionAdd ⟨x, m⟩ ⟨0 :: x', m'+1⟩ else
    ⟨lzw (· + ·) x x', m⟩
termination_by Int.natAbs (a.m - b.m)

def mf {α} (f : α → α → α) (m : List (List α)) : List α :=
  match m with
  | [] => []
  | xs :: [] => xs
  | [] :: xs => mf f xs
  | (x :: xs) :: (ys :: xss) => x :: mf f (lzw f xs ys :: xss)
termination_by m.length

def cp {α} (f : α → α → α) (a : List α) (b : List α) : List (List α) :=
  List.map (fun x ↦ List.map (f x) a) b

def fluxionMul {α} [Zero α] [Add α] [Mul α] (a b : Fluxion α) : Fluxion α :=
  match a, b with
  | ⟨x, m⟩, ⟨x', m'⟩ =>
    if m < m' then fluxionMul ⟨0 :: x, m+1⟩ ⟨x', m'⟩ else
    if m > m' then fluxionMul ⟨x, m⟩ ⟨0 :: x', m'+1⟩ else
    ⟨
      match x, x' with
      | [], [] => []
      |  _, [] => []
      | [], _  => []
      | x :: xs, y :: ys => x * y :: mf (· + ·) (cp (· * ·) xs ys)
    , 2 * m⟩
termination_by Int.natAbs (a.m - b.m)

def fluxionEq {α} [Zero α] [BEq α] (a b : Fluxion α) : Bool :=
  match dn a b with
    | ⟨⟨xs, m⟩, ⟨ys, n⟩⟩ => (xs == ys ∧ m == n)

instance {α} [BEq α] [Zero α] : BEq (Fluxion α) :=
  ⟨fun a b ↦ (fluxionEq a b)⟩

instance {α} [Zero α] [Add α] : Add (Fluxion α) :=
  ⟨fluxionAdd⟩

instance {α} [Zero α] [Add α] [Mul α] : Mul (Fluxion α) :=
  ⟨fluxionMul⟩

instance instField {α} [Field α] : Field (Fluxion α) where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)

/-
instance (Ord n, Num n) => Ord (Fluxion n) where
    x <= y = leq x y

instance (Show n, Ord n, Num n) => Show (Fluxion n) where
    show (F ([],n)) = "0"
    show h@(F (xs,n)) = (tail
                        . tail
                        . tail
                        . unpack
                        . replace (pack " .") (pack " 1.")
                        . replace (pack "  ") (pack " 1 ")
                        . replace (pack " 1") (pack " ")
                        . replace (pack "^1") (pack "")
                        . replace (pack "ε^-") (pack "∞^") -- it's not letting me print ω
                        . replace (pack "ε^0") (pack "")
                        . pack)
                        $ concatMap (\(x,i) ->
                        if x == 0 then ""
                        else (if x < 0 then " - " ++ show (-x) ++ "ε^" ++ show i
                        else " + " ++ show x ++ "ε^" ++ show i)) (zip xs [-n..])

instance (Eq n, Num n) => Num (Fluxion n) where
    F (xs,n) + F (ys,m) | n == m = F (losslessZipWith (+) xs ys,n)
                        | n < m = F (0:xs,n+1) + F (ys,m)
                        | n > m = F (xs,n) + F (0:ys,m+1)
    F (xs,n) - F (ys,m) | n == m = F (losslessZipWith (-) xs ys,n)
                        | n < m = F (0:xs,n+1) - F (ys,m)
                        | n > m = F (xs,n) - F (0:ys,m+1)
    F (xs,n) * F (ys,m) | n == m = F ((matrixFold (+)
                                    . cartProduct (*)
                                    . separate)
                                    (losslessZipWith (,) xs ys)
                                    , 2*n)
                        | n < m = F (0:xs,n+1) * F (ys,m)
                        | n > m = F (xs,n) * F (0:ys,m+1)
    abs (F (xs,n)) = F (xs,0)
    signum (F (0:xs,n)) = signum (F (xs,n-1))
    signum (F (xs,n)) = F ([1],n)
    fromInteger n = F ([fromInteger n],0)

---

-- two implementations of <= for fluxions:

-- mine (worse):
fluxionLEq :: Fluxion Int -> Fluxion Int -> Bool
fluxionLEq (F ([],n)) (F ([],m)) = True
fluxionLEq (F ([],n)) (F (y:ys,m))
    | y /= 0 = y > 0
    | otherwise = fluxionLEq (F ([],0)) (F (ys,m-1))
fluxionLEq (F (x:xs,n)) (F ([],m))
    | x /= 0 = x < 0
    | otherwise = fluxionLEq (F (xs,n-1)) (F ([],0))
fluxionLEq (F (x:xs,n)) (F (y:ys,m))
    | x == 0 = fluxionLEq (F (xs,n-1)) (F (y:ys,m))
    | y == 0 = fluxionLEq (F (x:xs,n)) (F (ys,m-1))
    | n < m = y > 0
    | n > m = x < 0
    | n == m = case () of
       () | x < y -> True
          | x > y -> False
          | otherwise -> fluxionLEq (F (xs,n-1)) (F (ys,m-1))

-- cosmo (https://github.com/cosmobobak)'s (better):

leq :: (Ord n, Num n) => Fluxion n -> Fluxion n -> Bool
leq (F x) (F y) = uncurry (\(xs, _) (ys, _) -> xs <= ys) (doubleNormalise x y)

---
-- (raise (/)) is the same as /' in fluxions.txt
raise :: (b -> b -> c) -> (a -> b) -> (a -> b) -> a -> c
raise op f g x = f x `op` g x

{-
-- characteristic function of a fluxion
p :: Fluxion n -> (Fluxion n -> Fluxion n)
p (F (zs,n)) = raise (*) (^ n) (`p'` zs)
    where
        p' x (n:ns) = F ([n],0) + (F ([p' x ns],0)) / (F ([x],0))
-}

-- the same as d in fluxions.txt
d :: (Eq n, Num n) => (Fluxion n -> Fluxion n) -> (n -> Fluxion n)
d f x = f (F ([x],0) + F ([0,1],0)) - f (F ([x],0))

-- the same as ℜ in fluxions.txt
real :: Num n => Fluxion n -> n
real (F ([],_)) = 0
real (F (x:xs,n)) | n < 0 = 0
                  | n == 0 = x
                  | n > 0 = real (F (xs,n-1))

-- the same as lim in fluxions.txt
lim :: (Num n,Eq n,Ord n,Fractional n) => Fluxion n -> n
lim (F ([],n)) = 0
lim (F (x:xs,0)) = x
lim (F (0:xs,n)) = lim (F (xs,n-1))
lim (F (xs,n)) | n < 0 = 0
               | head xs > 0 = 1/0
               | head xs < 0 = -1/0

-- the same as ∇ in fluxions.txt
diff :: (Eq n, Num n, Fractional n, Ord n) => (Fluxion n -> Fluxion n) -> n -> Maybe n
diff f = fmap lim . divide . raise (:/) (d f) (d id)
-- diff f n = fmap lim (divide (d f n :/ F ([0,1],0)))

-- diff (\x -> 2^x) 2
-- fmap lim (divide (d (\x -> 2^x) 2 :/ F ([0,1],0)))
-- fmap lim (divide ((2^(F ([2],0) + F ([0,1],0)) - 2^(F ([2],0)) ) :/ F ([0,1],0)))
-- fmap lim (divide ((2^(F ([2,1],0)) - 2^(F ([2],0)) ) :/ F ([0,1],0))) 2

-- lim((2^2*2^ε - 2^2)/ε)
-- lim(4*(2^ε - 1)/ε)
-- 4*lim((2^ε - 1)/ε)
-- 4*ln(2)
-- how is the computer supposed to do any of this?

derive :: (Fractional n, Ord n, Enum n) => (Fluxion n -> Fluxion n) -> n -> n -> n -> [n]
derive f a b s = map (fromJust . diff f . (*s)) [a..b]
-- derive (\x -> *function*) *start point* *# of samples* *step size*

-- simplifies RationalFluxions into Fluxions
divide :: (Eq n, Num n, Fractional n) => RationalFluxion n -> Maybe (Fluxion n)
divide (F (xs,n) :/ F (0:ys,m)) = divide (F (xs,n) :/ F (ys,m-1))
divide (F (xs,n) :/ F ([x],0)) = Just (F (map (/ x) xs,n))
divide (F (xs,n) :/ F (ys,0)) | last ys /= 0 = Nothing
                              | otherwise = divide (F (xs,n) :/ F (init ys,0))
divide (F (xs,n) :/ F (ys,m)) = divide (F (xs,n-m) :/ F (ys,0))
-/
