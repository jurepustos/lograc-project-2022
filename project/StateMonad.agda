module StateMonad where

open import Level                 renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Monad
open import Categories.Functor
open import Categories.NaturalTransformation

open import Function              using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                           using (_≡_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning               using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Product          using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero

state-functor : (S : Set) → Endofunctor Sets0
state-functor S = record { 
  F₀           = λ X → S → S × X ;
  F₁           = λ f st → λ s → proj₁ (st s) , f (proj₂ (st s)) ; 
  identity     = refl ; 
  homomorphism = refl ; 
  F-resp-≈     = λ {A} {B} {f} {g} → λ eq {st} 
                 → fun-ext (λ s → cong (λ b → proj₁ (st s) , b) eq) }

state-η : (S : Set) → NaturalTransformation 
          Categories.Functor.id 
          (state-functor S)
state-η S = record { 
  η           = λ X → λ x → λ s → s , x; 
  commute     = λ _ → refl ; 
  sym-commute = λ _ → refl }  

state-µ : (S : Set) → NaturalTransformation 
          (state-functor S ∘F state-functor S) 
          (state-functor S)
state-µ S = record { 
  η           = η-aux ;
  commute     = λ _ → refl ; 
  sym-commute = λ _ → refl }
  where
    η-aux : (X : Set) → (S → Σ S (λ x → S → Σ S (λ x₁ → X))) 
            → S → Σ S (λ x → X)
    η-aux X st s with st s
    η-aux X st s | s' , st' = st' s'

state-monad : (S : Set) → Monad Sets0
state-monad S = record { 
  F         = state-functor S ; 
  η         = state-η S ; 
  μ         = state-µ S ; 
  assoc     = refl ; 
  sym-assoc = refl ; 
  identityˡ = refl ; 
  identityʳ = refl }
   