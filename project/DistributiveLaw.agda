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


record DistributiveLaw : Set (lsuc lzero) where
  field
    Mon₁ : Monad Sets0
    Mon₂ : Monad Sets0
  
  open Category Sets0 using (_≈_)
  open Monad Mon₁ renaming (F to F₁; η to η₁; μ to µ₁)
  open Monad Mon₂ renaming (F to F₂; η to η₂; μ to µ₂)

  field
    θ : NaturalTransformation (F₂ ∘F F₁) (F₁ ∘F F₂)

  module θ = NaturalTransformation θ

  field
    F₂-identity : ∀ {X : Set} → θ.η X ∘ F₂.F₁ (η₁.η X) ≈ η₁.η (F₂.F₀ X)
    F₁-identity : ∀ {X : Set} → θ.η X ∘ η₂.η (F₁.F₀ X) ≈ F₁.F₁ (η₂.η X)
    F₁-transform : ∀ {X : Set} → θ.η X ∘ F₂.F₁ (µ₁.η X) ≈ µ₁.η (F₂.F₀ X) ∘ F₁.F₁ (θ.η X) ∘ θ.η (F₁.F₀ X)
    F₂-transform : ∀ {X : Set} → θ.η X ∘ µ₂.η (F₁.F₀ X) ≈ F₁.F₁ (µ₂.η X) ∘ θ.η (F₂.F₀ X) ∘ F₂.F₁ (θ.η X)

    -- might help to make symmetric versions of rules, like this
    -- sym-rule-3 : ∀ {X : Set} → µ₁.η (F₂.F₀ X) ∘ F₁.F₁ (θ.η X) ∘ θ.η (F₁.F₀ X) ≈ θ.η X ∘ F₂.F₁ (µ₁.η X)








     