module ISort where

  open import Agda.Primitive renaming (_⊔_ to LMax ; lzero to LZero)

  open import Data.Nat renaming (ℕ to Nat ; _≤_ to _<=_)
  open import Data.Nat.Properties
  open import Data.Product renaming (∃ to exists ; _×_ to _:*:_ )
  open import Data.List renaming (_∷_ to _::_)
  open import Data.List.Any
  open import Data.Sum renaming (_⊎_ to _:+:_ ; inj₁ to inl ; inj₂ to inr)

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_) hiding (trans)

  open SemiringSolver
  open Membership-≡

  -- a monad for tracking time

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

     _>>=_ : forall {a b}{A : Set a}{B : Set b}{n m : Nat} -> A in-time n -> (A -> B in-time m) -> B in-time (n + m)
     box x >>= f = box (unbox (f x))

     _=<<_ : forall {a b}{A : Set a}{B : Set b}{n m : Nat} -> (A -> B in-time m) -> A in-time n -> B in-time (n + m)
     f =<< x =  x >>= f

     infixr 2 _<$>_

     _<$>_ : forall {a b}{A : Set a}{B : Set b}{n : Nat}  -> (A -> B) -> A in-time n -> B in-time n
     f <$> box x = box (f x)

     return : forall {l}{A : Set l}{n : Nat} -> A -> A in-time n
     return = box

     bound-== : forall {a}{A : Set a}{m n} -> m == n -> A in-time m -> A in-time n
     bound-== refl b = b

  open CountingMonad

  module Permutations {l}{A : Set l} where

    -- x <: xs == xss is a proof that x is in some place in xs

    data _<:_==_ (x : A) : List A -> List A -> Set l where
      here  : forall {xs} -> x <: xs == (x :: xs)
      there : forall {xs y xys} -> x <: xs == xys -> x <: (y :: xs) == (y :: xys)

    -- proofs of permutations

    data IsPermutation : List A -> List A -> Set l where
      []   : IsPermutation [] []
      _::_ : forall {x xs ys xys} -> x <: xs == xys ->
                                     IsPermutation xs ys ->
                                     IsPermutation (x :: xs) xys

    -- some lemmas

    length-insert : forall {x xs xss} -> x <: xs == xss -> length xss == suc (length xs)
    length-insert here = refl
    length-insert (there p) = cong suc (length-insert p)


  module SortedList {a r}{A : Set a}
                         {_<=_ : Rel A r}
                         (isPartialOrder : IsPartialOrder _==_ _<=_) where

    open IsPartialOrder isPartialOrder
    open Permutations {a}{A}

    -- proofs that a value is less than all others in a list

    data _<*_ (x : A) : List A -> Set (LMax a r) where
      []   : x <* []
      _::_ : forall {y ys} -> x <= y -> x <* ys -> x <* (y :: ys)

    -- a proof that a list is sorted

    data Sorted : List A -> Set (LMax a r) where
      []   : Sorted []
      cons : forall x {xs xss} -> x <: xs == xss -> x <* xs -> Sorted xs -> Sorted xss

    -- some lemmas

    insert-less : forall {x y xs ys} -> y <: ys == xs -> x <= y -> x <* ys -> x <* xs
    insert-less here l ks = l :: ks
    insert-less (there p) l (k :: ks) = k :: insert-less p l ks

    trans* : forall {x y ys} -> x <= y -> y <* ys -> x <* ys
    trans* p [] = []
    trans* p (x :: p') = trans p x :: trans* p p'


  module NatExtras where

    -- simple definition of exponentiation

    _^_ : Nat -> Nat -> Nat
    n ^ zero = 1
    n ^ (suc m) = n * (n ^ m)


  open NatExtras

  module InsertionSort {A : Set}{_<=_ : Rel A LZero}
                       (isPartialOrder : IsPartialOrder _==_ _<=_)
                       (_<?_ : forall (x y : A) -> x <= y :+: y <= x in-time 1) where

    open Permutations {LZero}{A}
    open SortedList isPartialOrder

    insert : forall {xs} -> (x : A) -> Sorted xs -> Sorted (x :: xs) in-time (length xs)
    insert x [] = return (cons x here [] [])
    insert x (cons x' x<xs x<*xs ss) = bound-== (sym (length-insert x<xs))
                                                (x <? x' >>= \
                                                         {
                                                           (inl p) -> return (cons x here (insert-less x<xs p (trans* p x<*xs)) (cons x' x<xs x<*xs ss)) ;
                                                           (inr p) -> cons x' (there x<xs) (p :: x<*xs) <$> insert x ss
                                                         })


    isort : (xs : List A) -> Sorted xs in-time length xs ^ 2
    isort [] = return []
    isort (x :: xs) = bound-== (lem (length xs)) (isort xs >>= insert x >>= return)
                      where
                        lem : forall n -> (n ^ 2 + n) + (n + 1) == (1 + n) ^ 2
                        lem = solve 1 (\ n -> (n :^ 2 :+ n) :+ (n :+ con 1) := (con 1 :+ n) :^ 2) refl
