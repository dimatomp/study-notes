data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

-- Arguments in {} are implicit. Compiler will try to infer their values and fail in case of ambiguity.
natrec : {C : Nat -> Set} -> C Zero -> ((x : Nat) -> (y : C x) -> C (Succ x)) -> (n : Nat) -> C n
natrec z s Zero      = z
natrec {t} z s (Succ n') = s n' (natrec {t} z s n')

_+_ : Nat -> Nat -> Nat
a + b = natrec a (\_ -> Succ) b

data Id (C : Set) (a : C) : C -> Set where
  id : Id C a a

id_symm : {C : Set} {a b : C} {p : Id C a b} -> Id C b a
id_symm {p = id} = id

id_trans : {C : Set} {a b c : C} {p1 : Id C a b} {p2 : Id C b c} -> Id C a c
id_trans {p1 = id} {p2 = id} = id

id_func : {C T : Set} {a b : C} {f : C -> T} {p : Id C a b} -> Id T (f a) (f b)
id_func {p = id} = id

zero_neut_right : {n : Nat} -> Id Nat n (n + Zero)
zero_neut_right = id

succ_upper : {a b : Nat} -> Id Nat (a + Succ b) (Succ (a + b))
succ_upper = id

succ_upper2 : {a b : Nat} -> Id Nat (Succ a + b) (Succ (a + b))
succ_upper2 {a} {b} =
  let z12 = zero_neut_right
      z23 = id_func {f = Succ} {p = zero_neut_right}
      zeroProof = id_trans {b = Succ a} {p1 = z12} {p2 = z23}
      -- zeroProof <-> Succ a + Zero = Succ a = Succ (a + Zero)
      p12 b = succ_upper {Succ a} {b}
      p23 b y = id_func {f = Succ} {p = y}
      p34 b = id_func {f = Succ} {id_symm {p = succ_upper {a} {b}}}
      succProof b y = id_trans {p1 = p12 b} {p2 = id_trans {p1 = p23 b y} {p2 = p34 b}}
      -- succProof <-> Succ a + Succ b = Succ (Succ a + b) = Succ (Succ (a + b)) = Succ (a + Succ b)
  in natrec {\n -> Id Nat (Succ a + n) (Succ (a + n))} zeroProof succProof b

succ_carry : {a b : Nat} -> Id Nat (Succ a + b) (a + Succ b)
succ_carry {a} {b} = id_trans {b = Succ (a + b)} {p1 = succ_upper2 {a} {b}} {p2 = id_symm {p = succ_upper {a} {b}}}
-- Succ a + b = Succ (a + b) = a + Succ b

zero_neut_left : {n : Nat} -> Id Nat n (Zero + n)
zero_neut_left {n} =
  let p1 _ y = id_func {f = Succ} {p = y} -- Succ b = Succ (Zero + b)
      p2 b = id_symm {p = succ_upper {a = Zero} {b = b}} -- Succ (Zero + b) = Zero + Succ b
  in natrec {\b -> Id Nat b (Zero + b)} id (\b y -> id_trans {p1 = p1 b y} {p2 = p2 b}) n

plus_commutes : {a b : Nat} -> Id Nat (a + b) (b + a)
plus_commutes {a} {b} =
  let zeroProof = id_trans {p1 = id_symm {p = zero_neut_right}} {p2 = zero_neut_left}
      -- zeroProof <-> n + Zero = n = Zero + n
      p1 n = succ_upper {a} {n}
      p2 _ y = id_func {f = Succ} {p = y}
      p3 n = id_symm {p = succ_upper2 {n} {a}}
      succProof n y = id_trans {p1 = p1 n} {p2 = id_trans {p1 = p2 n y} {p2 = p3 n}}
      -- succProof <-> a + Succ n = Succ (a + n) = Succ (n + a) = Succ n + a
  in natrec {\n -> Id Nat (a + n) (n + a)} zeroProof succProof b

record _/\_ (A : Set) (B : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

uncurry : {A : Set} {B : A -> Set} {C : A /\ B -> Set} -> (f : (x : A) -> (y : B x) -> C (x , y)) (p : A /\ B) -> C p
uncurry f (a , b) = f a b

data _\/_ (A : Set) (B : Set) : Set where
  inl : A -> A \/ B
  inr : B -> A \/ B

record True : Set where
  constructor true

data False : Set where

~_ : Set -> Set
~ A = A -> False

_/=_ : {A : Set} -> (a : A) -> (b : A) -> Set
_/=_ {A} a b = ~(Id A a b)

add_not_not : forall {A} -> A -> ~(~ A)
add_not_not a f = f a

zero_neq_one : ~(Id Nat Zero (Succ Zero))
zero_neq_one () -- No constructor for Id 0 1 available.

for_exist : {A : Set} {B : A -> Set} -> ((a : A) -> ~(B a)) -> ~(A /\ B)
for_exist = uncurry -- What a surprise.

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

head : {A : Set} -> (l : List A) -> {p : l /= []} -> A
head [] {p} with p id
head [] {p} | () -- No constructor for False available.
head (a :: _) = a
