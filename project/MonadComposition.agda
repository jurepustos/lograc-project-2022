-- this file contains definition of compatible composition of two monads
-- and definition of distributive law

module MonadComposition where

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

open Category Sets0 using (_≈_)

-- compatible composition
record CompatibleComposition (Mon₁ Mon₂ : Monad Sets0) : Set (lsuc lzero) where 
  open Monad Mon₁ renaming (F to F₁; η to η₁; μ to μ₁)
  open Monad Mon₂ renaming (F to F₂; η to η₂; μ to μ₂)

  F : Endofunctor Sets0
  F = F₁ ∘F F₂

  η : NaturalTransformation idF F
  η = η₁ ∘ₕ η₂

  -- natural transformation μ
  field
    μ : NaturalTransformation (F ∘F F) F

  module F = Functor F 
  module η = NaturalTransformation η
  module μ = NaturalTransformation μ

  -- conditions
  field    
    assoc     : ∀ {X : Set} → μ.η X ∘ F.F₁ (μ.η X) ≈ μ.η X ∘ μ.η (F.F₀ X)
    sym-assoc : ∀ {X : Set} → μ.η X ∘ μ.η (F.F₀ X) ≈ μ.η X ∘ F.F₁ (μ.η X)
    identityˡ : ∀ {X : Set} → μ.η X ∘ F.F₁ (η.η X) ≈ id
    identityʳ : ∀ {X : Set} → μ.η X ∘ η.η (F.F₀ X) ≈ id

    F₁-η₂-morphism : ∀ {X : Set} → η.η X ≈ NaturalTransformation.η (F₁ ∘ˡ η₂) X ∘ η₁.η X
    F₂-η₁-morphism : ∀ {X : Set} → η.η X ≈ NaturalTransformation.η (η₁ ∘ʳ F₂) X ∘ η₂.η X
    η₁-composition : ∀ {X : Set} → η₁.η (F₂.F₀ X) ∘ μ₂.η X ≈ μ.η X ∘ NaturalTransformation.η (η₁ ∘ₕ (F₂ ∘ˡ (η₁ ∘ʳ F₂))) X
    η₂-composition : ∀ {X : Set} → F₁.F₁ (η₂.η X) ∘ μ₁.η X ≈ μ.η X ∘ NaturalTransformation.η (F₁ ∘ˡ η₂ ∘ₕ F₁ ∘ˡ η₂) X
    middle-unity   : ∀ {X : Set} → μ.η X ∘ NaturalTransformation.η (F₁ ∘ˡ η₂ ∘ₕ η₁ ∘ʳ F₂) X ≈ id
    

-- distributive law
record DistributiveLaw (Mon₁ Mon₂ : Monad Sets0) : Set (lsuc lzero) where  
  open Monad Mon₁ renaming (F to F₁; η to η₁; μ to μ₁)
  open Monad Mon₂ renaming (F to F₂; η to η₂; μ to μ₂)

  -- natural transformation θ
  field
    θ : NaturalTransformation (F₂ ∘F F₁) (F₁ ∘F F₂)

  module θ = NaturalTransformation θ

  -- conditions
  field
    F₂-identity  : ∀ {X : Set} → θ.η X ∘ F₂.F₁ (η₁.η X) ≈ η₁.η (F₂.F₀ X)
    F₁-identity  : ∀ {X : Set} → θ.η X ∘ η₂.η (F₁.F₀ X) ≈ F₁.F₁ (η₂.η X)
    F₁-transform : ∀ {X : Set} → θ.η X ∘ F₂.F₁ (μ₁.η X) ≈ μ₁.η (F₂.F₀ X) ∘ F₁.F₁ (θ.η X) ∘ θ.η (F₁.F₀ X)
    F₂-transform : ∀ {X : Set} → θ.η X ∘ μ₂.η (F₁.F₀ X) ≈ F₁.F₁ (μ₂.η X) ∘ θ.η (F₂.F₀ X) ∘ F₂.F₁ (θ.η X)


        