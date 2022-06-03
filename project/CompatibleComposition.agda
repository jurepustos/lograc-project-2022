module CompatibleComposition where

open import Level                 renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Monad
open import Categories.Functor    using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation renaming (id to idN)

open import Function              using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                           using (_≡_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning               using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Product          using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero


record CompatibleComposition : Set (lsuc lzero) where
  field
    Mon₁ : Monad Sets0
    Mon₂ : Monad Sets0
  
  open Category Sets0 using (_≈_)
  open Monad Mon₁ renaming (F to F₁; η to η₁; μ to µ₁)
  open Monad Mon₂ renaming (F to F₂; η to η₂; μ to µ₂)

  F : Endofunctor Sets0
  F = F₁ ∘F F₂

  η : NaturalTransformation idF F
  η = η₁ ∘ₕ η₂

  field
    -- η : NaturalTransformation idF F
    µ : NaturalTransformation (F ∘F F) F

  module F = Functor F 
  module η = NaturalTransformation η
  module µ = NaturalTransformation µ

  field
    assoc     : ∀ {X : Set} → µ.η X ∘ F.F₁ (µ.η X) ≈ µ.η X ∘ µ.η (F.F₀ X)
    sym-assoc : ∀ {X : Set} → µ.η X ∘ µ.η (F.F₀ X) ≈ µ.η X ∘ F.F₁ (µ.η X)
    identityˡ : ∀ {X : Set} → µ.η X ∘ F.F₁ (η.η X) ≈ id
    identityʳ : ∀ {X : Set} → µ.η X ∘ η.η (F.F₀ X) ≈ id

    F₁-η₂-morphism : ∀ {X : Set} → η.η X ≈ F₁.F₁ (η₂.η X) ∘ η₁.η X
    F₂-η₁-morphism : ∀ {X : Set} → η.η X ≈ η₁.η (F₂.F₀ X) ∘ η₂.η X
    middle-unity : ∀ {X : Set} → µ.η X ∘ F₁.F₁ (η₂.η (F₁.F₀ (F₂.F₀ X)) ∘ η₁.η (F₂.F₀ X)) ≈ id
  
    -- these rules imply η we have defined above
    -- rule-3 : ∀ {X : Set} → F₁.F₁ (η₂.η X) ∘ µ₁.η X ≈ µ.η X ∘ F₁.F₁ (η₂.η (F₁.F₀ (F₂.F₀ X)) ∘ F₁.F₁ (η₂.η X))
    -- rule-4 : ∀ {X : Set} → η₁.η (F₂.F₀ X) ∘ µ₂.η X ≈ µ.η X ∘ η₁.η (F₂.F₀ (F₁.F₀ (F₂.F₀ X))) ∘ F₂.F₁ (η₁.η (F₂.F₀ X))
    


 