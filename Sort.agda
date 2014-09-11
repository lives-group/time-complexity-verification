module Sort where

open import Agda.Primitive

open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open SemiringSolver

-- a monad for time complexity tracking


module TickMonad where
  private
    module Dummy where

      data _in-time_ {l}(A : Set l) (n : ℕ) : Set l where
        box : A → A in-time n

  open Dummy public using (_in-time_)
  open Dummy

  unbox : ∀ {n l}{A : Set l} → A in-time n → A
  unbox (box x) = x

  -- applicative

  _<$>_ : ∀ {n l}{A B : Set l} → (A → B) → A in-time n → B in-time n
  f <$> (box x) = box (f x)

  -- monad operations

  return : ∀ {n l}{A : Set l} → A → A in-time n
  return = box

  _>>=_ : ∀ {n m l}{A B : Set l} → A in-time n → (A → B in-time m) → B in-time (n + m)
  (box x) >>= f = box (unbox (f x))

  ap : ∀ {n l}{A B C : Set l} → (A → B → C) in-time n → A → B → C in-time n
  ap f a b = box ((unbox f) a b)


open TickMonad public

module Mininum {l}{A : Set l}{_≤_ : Rel A l}(_<?_ : ∀ x y → (Dec (x ≤ y)) in-time 1)  where

  module Version1 where

    mininum : ∀ (xs : List A) → ((A × List A) ⊎ xs ≡ []) in-time (length xs)
    mininum [] = return (inj₂ refl)
    mininum (x ∷ xs) = subst (λ n → ((A × List A) ⊎ x ∷ xs ≡ []) in-time n)
                             (lem (length xs))
                             ((mininum xs) >>= λ {(inj₁ (v , vs)) → inj₁ <$> ((x <? v) >>= λ {(yes _) → return (x , v ∷ vs) ;
                                                                                             _       → return (v , x ∷ vs) }) ;
                                                  (inj₂ _) → return (inj₁ (x , [])) })
                       where
                         lem : ∀ n → (n + 1) ≡ (1 + n)
                         lem = solve 1 (λ n → n :+ con 1 := con 1 :+ n) refl

  module Version2 where

    open import Data.Vec hiding (_>>=_)

    mininum : ∀ {n}(xs : Vec A (suc n)) → (A × Vec A n) in-time n
    mininum (x ∷ []) = return (x , [])
    mininum {suc n} (x ∷ xs) = subst (λ n → (A × Vec A n) in-time n)
                                     (lemma n)
                                     (mininum xs >>= (λ {(y , ys) → (x <? y) >>= (λ {(yes p) → return (x , subst (λ n → Vec A n) (sym (lemma n)) (y ∷ ys)) ;
                                                                                     (no p ) → return (y , subst (λ n → Vec A n) (sym (lemma n)) (x ∷ ys)) }) }))
                               where
                                 lemma : ∀ n → (n + 1) ≡ (1 + n)
                                 lemma = solve 1 (λ n → n :+ con 1 := con 1 :+ n) refl


    selection-sort : ∀ {n}(xs : Vec A n) → Vec A n in-time (n * n)
    selection-sort [] = return []
    selection-sort {suc n} xs = subst-+ (lemma n) (mininum xs >>= (λ {(y , ys) → selection-sort ys >>= λ zs → return (y ∷ zs) }))
                                where
                                  subst-+ : ∀ {n m k} {B : Set l} → m + k ≡ n → B in-time m → B in-time n
                                  subst-+ {B = B} eq x = subst (λ a → B in-time a) eq (x >>= return)

                                  lemma : ∀ n → n + (n * n + 1) + n ≡ (1 + n) * (1 + n)
                                  lemma = solve 1 (λ n → n :+ (n :* n :+ (con 1)) :+ n := (con 1 :+ n) :* (con 1 :+ n)) refl
