module SortFormalization where

  open import Agda.Primitive

  module Preliminaries where
   
     -- basic type constructors stuff

     id : {A : Set} -> A -> A
     id x = x

     data Empty : Set where

     exFalsum : {A : Set} -> Empty -> A
     exFalsum ()

     data Unit : Set where
       tt : Unit

     record Sigma {a b}(A : Set a)(B : A -> Set b) : Set (a ⊔ b) where
        constructor _,_
        field
          fst : A
          snd : B fst

     open Sigma public

     data _+_ {a b}(A : Set a)(B : Set b) : Set (a ⊔ b) where
       inl : A -> A + B
       inr : B -> A + B

     infixr 3 _*_

     _*_ : forall {a b}(A : Set a)(B : Set b) -> Set (a ⊔ b)
     A * B = Sigma A (\_ -> B)

     uncurry : forall {a b}{A : Set a}{B : Set b}{C : Set (a ⊔ b)} -> (A -> B -> C) -> (A * B) -> C
     uncurry f (a , b) = f a b

     exists : {A : Set} -> (A -> Set) -> Set
     exists = Sigma _

     not : Set -> Set
     not A = A -> Empty

     -- decidability

     data Dec (A : Set) : Set where
       yes : A -> Dec A
       no  : not A -> Dec A

     Decidable : forall {A : Set}(P : A -> A -> Set) -> Set 
     Decidable {A} P = forall (x y : A) -> Dec (P x y)     

     infix 4 _==_
  
     data _==_ {l}{A : Set l} (x : A) : A -> Set l where
       refl : x == x

     {-# BUILTIN EQUALITY _==_ #-}
     {-# BUILTIN REFL refl #-}

     cong : forall {a b}{A : Set a}{B : Set b}(f : A -> B){x y : A} -> x == y -> f x == f y 
     cong f refl = refl

     subst : forall {a b}{A : Set a}{x y : A} -> (P : A -> Set b) -> x == y -> P x == P y
     subst P refl = refl

     sym : forall {a}{A : Set a}{x y : A} -> x == y -> y == x
     sym refl = refl

     _/=_ : forall {l}{A : Set l} -> A -> A -> Set l
     x /= y = x == y -> Empty

     -- functional composition

     infixr 5 _:o_

     _:o_ : forall {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
     f :o g = \ x -> f (g x)

     -- natural numbers

     data Nat : Set where
       zero : Nat
       suc  : Nat -> Nat

     {-# BUILTIN NATURAL Nat #-}

     -- equality test over natural numbers

     sucInj : forall {n m : Nat} -> suc n == suc m -> n == m
     sucInj refl = refl

     eqNatDec : Decidable {A = Nat}(_==_)
     eqNatDec zero zero = yes refl
     eqNatDec zero (suc y) = no (\ ())
     eqNatDec (suc x) zero = no (\ ())
     eqNatDec (suc x) (suc y) with eqNatDec x y
     eqNatDec (suc x) (suc .x) | yes refl = yes refl
     eqNatDec (suc x) (suc y) | no nop = no (nop :o sucInj)

     -- addition

     _+N_ : Nat -> Nat -> Nat
     zero +N m = m
     suc n +N m = suc (n +N m)

     {-# BUILTIN NATPLUS _+N_ #-}

     -- multiplication

     _*N_ : Nat -> Nat -> Nat
     zero *N m = zero
     suc n *N m = m +N (n *N m)

     -- Lists

     infixr 5 _::_

     data List {l}(A : Set l) : Set l where
       []   : List A
       _::_ : A -> List A -> List A

     length : forall {l}{A : Set l} -> List A -> Nat
     length [] = 0
     length (_ :: xs) = suc (length xs)

     -- steroids idiom

     Hidden : forall {l} -> Set l -> Set l
     Hidden A = Unit -> A

     hide : forall {l l'}{A : Set l}{B : A -> Set l'} -> 
            ((x : A) -> B x) -> ((x : A) -> Hidden (B x))
     hide f x unit = f x
     
     reveal : forall {l}{A : Set l} -> Hidden A -> A
     reveal f = f tt

     data Reveal_is_ {l} {A : Set l} (x : Hidden A) (y : A) : Set l where
        [_] : (eq : reveal x == y) -> Reveal x is y

     inspect : forall {l l'}{A : Set l}{B : A -> Set l'}
               (f : (x : A) -> B x)(x : A) -> Reveal (hide f x) is f x
     inspect f x = [ refl ]

  open Preliminaries

  module CountingMonad where

     private 
       module Dummy where
          
          infix 1 _in-time_
          
          data _in-time_ {l}(A : Set l)(n : Nat) : Set l where
            box : A -> A in-time n
     open Dummy public using (_in-time_)
     open Dummy

     unbox : forall {l}{A : Set l}{n} -> A in-time n -> A
     unbox (box x) = x

     infixl 1 _>>=_

     _>>=_ : forall {a b}{A : Set a}{B : Set b}{n m : Nat} -> A in-time n -> (A -> B in-time m) -> B in-time (n +N m)
     box x >>= f = box (unbox (f x))
     
     _=<<_ : forall {a b}{A : Set a}{B : Set b}{n m : Nat} -> (A -> B in-time m) -> A in-time n -> B in-time (n +N m)
     f =<< x =  x >>= f

     infixr 2 _<$>_

     _<$>_ : forall {a b}{A : Set a}{B : Set b}{n : Nat}  -> (A -> B) -> A in-time n -> B in-time n
     f <$> box x = box (f x)
     
     return : forall {l}{A : Set l}{n : Nat} -> A -> A in-time n
     return = box

     bound-== : forall {a}{A : Set a}{m n} -> m == n -> A in-time m -> A in-time n
     bound-== refl b = b

  open CountingMonad


  module BinaryRelation where

    -- homogeneous binary relations

    Rel : forall {a} -> Set a -> (l : Level) -> Set (a ⊔ lsuc l)
    Rel A l = A -> A -> Set l

    -- properties of binary relations

    Reflexive : forall {l}{A : Set l} -> Rel A l -> Set _
    Reflexive _~_  = forall {x} -> x ~ x

    Transitive : forall {l}{A : Set l} -> Rel A l -> Set _
    Transitive _~_ = forall {x y z} -> x ~ y -> y ~ z -> x ~ z

    Antisymmetric : forall {l}{A : Set l} -> Rel A l -> Set _
    Antisymmetric _~_ = forall {x y} -> x ~ y -> y ~ x -> x == y

    -- pre-orders

    record IsPreOrder {l}{A : Set l}(_~_ : Rel A l) : Set l where
      field
         reflexive  : Reflexive _~_
         transitive : Transitive _~_

    -- partial orders

    record IsPartialOrder {l}{A : Set l}(_~_ : Rel A l) : Set l where
      field
        pre-order : IsPreOrder _~_
        antisymmetric : Antisymmetric _~_

  open BinaryRelation


  module NatExtras where
    
    --exponentiation

    _^_ : Nat -> Nat -> Nat
    x ^ zero = 1
    x ^ (suc n) = x *N (x ^ n)

  open NatExtras

  -- permutations 

  module Permutations {l}{A : Set l} where


    -- x <: xs == ys means that ys is equal to xs with x inserted somewhere

    data _<:_==_ (x : A) : List A -> List A -> Set l where
      here  : forall {xs} -> x <: xs == (x :: xs)
      there : forall {y xs xys} -> (p : x <: xs == xys) -> x <: (y :: xs) == (y :: xys) 

    -- proof that a list is permutations of another one

    data IsPermutation : List A -> List A -> Set l where
      []   : IsPermutation [] []
      _::_ : forall {x xs ys xys} -> 
             (p : x <: ys == xys) ->
             (ps : IsPermutation xs ys) ->
             IsPermutation (x :: xs) xys

    id-permutation : forall (xs : List A) -> IsPermutation xs xs
    id-permutation [] = []
    id-permutation (x :: xs) = here :: id-permutation xs


  -- sortedness

  module Sorted {l}{A : Set l}
                   {_<=_ : Rel A l}
                   (isPartialOrder : IsPartialOrder _<=_) where

      open IsPartialOrder isPartialOrder
      open IsPreOrder pre-order
      open Permutations {l}{A}

      -- proofs that x is less than all values in xs

      data _<=*_ (x : A) : List A -> Set l where
        <>   : x <=* []
        _:>_ : forall {y ys} -> x <= y -> x <=* ys -> x <=* (y :: ys)

      -- proofs that a list is sorted.

      data IsSorted : List A -> Set l where
        []   : IsSorted []
        cons : forall {x xs xss} -> x <: xs == xss -> x <=* xs -> IsSorted xs -> IsSorted (x :: xs)

      -- some useful properties

      trans* : forall {x y xs} -> x <= y -> y <=* xs -> x <=* xs
      trans* x<y <> = <>
      trans* x<y (x :> y<ys) = (transitive x<y x) :> (trans* x<y y<ys)


  module Sorting {l}{A : Set l}
                    {_<=_ : Rel A l}
                    (isPartialOrder : IsPartialOrder _<=_)
                    (_<=?_ : forall (x y : A) -> ((x <= y) + (y <= x)) in-time 1) where 

      open Sorted isPartialOrder public
      open Permutations {l}{A}

      -- insertion sorting

      ins : A -> (xs : List A) -> List A in-time (length xs)
      ins x [] = return []
      ins x (y :: ys) = x <=? y >>= \ { (inl x<=y) -> return (x :: (y :: ys)) ;
                                        (inr y<=x) -> _::_ y <$> ins x ys }

      isort : (xs : List A) -> List A in-time (length xs) ^ 2
      isort [] = return []
      isort (x :: xs) = bound-== (sym (lem {!length xs!})) {!!}
                        where
                          lem : forall (n : Nat) -> (((n ^ 2) +N n) +N (n +N 1)) == ((1 +N n) ^ 2)
                          lem n = {!!} 

      insert : forall {xs : List A}(x : A) -> IsSorted xs -> IsSorted (x :: xs) in-time (length xs)
      insert x [] = return (cons here <> [])
      insert x (cons x₂ x₃ xs₁) = {!!}
