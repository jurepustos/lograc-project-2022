module StateMonad where

open import Level renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Monad
open import Categories.Functor
open import Categories.NaturalTransformation

open import Function using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                          using (_≡_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning              using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero

-- prod-ext : {A B : Set} {x : B} {f g : A → B} 
--            → f x ≡ g x
--            → ?

state-functor : (S : Set) → Endofunctor Sets0
state-functor S = record { 
  F₀           = λ X → S → S × X ;
  F₁           = λ f st s → proj₁ (st s) , f (proj₂ (st s)) ; 
  identity     = refl ; 
  homomorphism = refl ; 
  F-resp-≈     = λ {A} {B} {f} {g} → λ eq {st} → fun-ext λ s 
                 → cong (λ b → ((proj₁ (st s))) , b) eq }

state-monad : (S : Set) → Monad Sets0
state-monad S = record { 
  F         = state-functor S ; 
  η         = {!   !} ; 
  μ         = {!   !} ; 
  assoc     = {!   !} ; 
  sym-assoc = {!   !} ; 
  identityˡ = {!   !} ; 
  identityʳ = {!   !} }
  