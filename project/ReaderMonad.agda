module ReaderMonad where

open import Level renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Monad
open import Categories.Functor
open import Categories.NaturalTransformation

open import Function using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                          using (_≡_; refl; sym; trans; cong; subst)
open Eq.≡-Reasoning              using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero

reader-functor : (S : Set) → Endofunctor Sets0
reader-functor S = record { 
  F₀           = λ X → S → X ; 
  F₁           = λ f r → f ∘ r ; 
  identity     = refl ; 
  homomorphism = refl ; 
  F-resp-≈     = λ {A} {B} {f} {g} → (λ eq → fun-ext λ x → eq) }

reader-η : (S : Set) → NaturalTransformation Categories.Functor.id (reader-functor S)
reader-η S = record { 
  η           = λ X → λ x → λ _ → x ; 
  commute     = λ _ → refl ; 
  sym-commute = λ _ → refl }  

reader-µ : (S : Set) → NaturalTransformation 
                       (reader-functor S ∘F reader-functor S) 
                       (reader-functor S)
reader-µ S = record { 
  η           = λ _ → λ r → λ s → r s s ; 
  commute     = λ _ → refl ; 
  sym-commute = λ _ → refl }

reader-monad : (S : Set) → Monad Sets0
reader-monad S = record { 
  F         = reader-functor S ; 
  η         = reader-η S ; 
  μ         = reader-µ S ; 
  assoc     = refl ; 
  sym-assoc = refl ; 
  identityˡ = refl ; 
  identityʳ = refl }
     