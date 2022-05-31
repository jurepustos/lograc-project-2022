module DistributiveLaw where

open import Level                 renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Monad
open import Categories.Functor    using (_∘F_; Endofunctor)
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

record DistributiveLaw : Sets0 where
  field
    Mon₁ : Monad Sets0
    Mon₂ : Monad Sets0
  
  open Monad Mon₁ renaming (F to F₁; η to η₁; μ to μ₁)
  open Monad Mon₂ renaming (F to F₂; η to η₂; μ to μ₂)

  field
    θ : (S : Set) → Endofunctor Sets0

  field
    -- rules here?









 