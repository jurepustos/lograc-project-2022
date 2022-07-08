-- in this file we are looking at example of special cases of update monads, reader and writer monad

module Examples where

open import Level                 renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Monad
open import Agda.Builtin.Unit

open import Data.List             using (_∷_; []; List; _++_)
open import Data.List.Properties

import Relation.Binary.PropositionalEquality as Eq
open Eq                           using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect)
open Eq.≡-Reasoning               using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

open import Data.Product          using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)

open import Monoids               using (Monoid; RightAction)
open import UpdateMonad           using (update-monad)
open import ReaderMonad           using (reader-monad)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero

-- we get the reader monad as a special case by using the unit monoid and action
ReaderMonad : (S : Set) → Monad Sets0
ReaderMonad S = update-monad S P A
  where
    P : Monoid {lzero}
    P = record { 
      M        = ⊤ ; 
      ε        = tt ; 
      _⊕_     = λ _ _ → tt ; 
      ε-left   = λ { tt → refl } ; 
      ε-right  = λ { tt → refl } ; 
      ⊕-assoc = λ p₁ p₂ p₃ → refl }
    
    A : RightAction P S
    A = record { 
      _↓_          = λ s _ → s ; 
      ε-identity   = λ s → refl ; 
      homomorphism = λ p₁ p₂ s → refl }

-- we get the writer monad as a special case by using the unit type for state
WriterMonad : (P : Monoid {lzero}) → Monad Sets0
WriterMonad P = update-monad S P A
  where
    S : Set
    S = ⊤

    A : RightAction P S
    A = record { 
      _↓_          = λ _ _ → tt ; 
      ε-identity   = λ { tt → refl } ; 
      homomorphism = λ p₁ p₂ t → refl }

-- by using the trivial action (s ↓ p = s), we get the update monad that 
-- does reader and writer's job separately
TrivialActionUpdateMonad : (S : Set) (P : Monoid {lzero}) → Monad Sets0
TrivialActionUpdateMonad S P = update-monad S P A
  where
    A : RightAction P S
    A = record { 
      _↓_          = λ s _ → s ; 
      ε-identity   = λ x → refl ; 
      homomorphism = λ p₁ p₂ s → refl }

-- a computation takes an initial state to the list of all intermediate states
ConcatMonad : (S : Set) → Monad Sets0
ConcatMonad S = update-monad S P A
  where
    -- lists over S
    S* : Set
    S* = List S

    -- concatenation
    P : Monoid {lzero}
    P = record { 
      M        = S* ;
      ε        = [] ; 
      _⊕_     = λ ss ss' → ss ++ ss' ; 
      ε-left   = λ ss → refl ; 
      ε-right  = λ ss → ++-identityʳ ss ; 
      ⊕-assoc = λ ss ss' ss'' → ++-assoc ss ss' ss'' }

    last : {X : Set} → X → List X → X
    last x [] = x
    last x (x' ∷ xs) = last x' xs

    last-concat : {X : Set} (x : X) (xs xs' : List X) 
                → last x (xs ++ xs') ≡ last (last x xs) xs'
    last-concat x [] [] = refl
    last-concat x (x' ∷ xs) [] rewrite ++-identityʳ xs = refl
    last-concat x [] (x' ∷ xs') = refl
    last-concat x (x' ∷ xs) (x'' ∷ xs') = last-concat x' xs (x'' ∷ xs')

    A : RightAction P S
    A = record { 
      _↓_          = λ s ss → last s ss ; 
      ε-identity   = λ s → refl ; 
      homomorphism = λ ss ss' s → last-concat s ss ss' }


