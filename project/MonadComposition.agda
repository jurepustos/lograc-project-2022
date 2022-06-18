{-# OPTIONS --allow-unsolved-metas #-} 
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

record CompatibleComposition (Mon₁ Mon₂ : Monad Sets0) : Set (lsuc lzero) where 
  open Monad Mon₁ renaming (F to F₁; η to η₁; μ to μ₁)
  open Monad Mon₂ renaming (F to F₂; η to η₂; μ to μ₂)

  F : Endofunctor Sets0
  F = F₁ ∘F F₂

  η : NaturalTransformation idF F
  η = η₁ ∘ₕ η₂

  field
    μ : NaturalTransformation (F ∘F F) F

  module F = Functor F 
  module η = NaturalTransformation η
  module μ = NaturalTransformation μ

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
    
record DistributiveLaw (Mon₁ Mon₂ : Monad Sets0) : Set (lsuc lzero) where  
  open Monad Mon₁ renaming (F to F₁; η to η₁; μ to μ₁)
  open Monad Mon₂ renaming (F to F₂; η to η₂; μ to μ₂)

  field
    θ : NaturalTransformation (F₂ ∘F F₁) (F₁ ∘F F₂)

  module θ = NaturalTransformation θ

  field
    F₂-identity  : ∀ {X : Set} → θ.η X ∘ F₂.F₁ (η₁.η X) ≈ η₁.η (F₂.F₀ X)
    F₁-identity  : ∀ {X : Set} → θ.η X ∘ η₂.η (F₁.F₀ X) ≈ F₁.F₁ (η₂.η X)
    F₁-transform : ∀ {X : Set} → θ.η X ∘ F₂.F₁ (μ₁.η X) ≈ μ₁.η (F₂.F₀ X) ∘ F₁.F₁ (θ.η X) ∘ θ.η (F₁.F₀ X)
    F₂-transform : ∀ {X : Set} → θ.η X ∘ μ₂.η (F₁.F₀ X) ≈ F₁.F₁ (μ₂.η X) ∘ θ.η (F₂.F₀ X) ∘ F₂.F₁ (θ.η X)



module _ (Mon₁ Mon₂ : Monad Sets0) where
  open Monad Mon₁ renaming (F to F₁; η to η₁; μ to μ₁)
  open Monad Mon₂ renaming (F to F₂; η to η₂; μ to μ₂)
  
  DistributiveLaw-CompatibleComposition : DistributiveLaw Mon₁ Mon₂ → CompatibleComposition Mon₁ Mon₂
  DistributiveLaw-CompatibleComposition dist-law = record { 
    μ              = μ' ((μ₁ ∘ₕ μ₂) ∘ᵥ θ' (F₁ ∘ˡ θ ∘ʳ F₂)) ;
    assoc          = {!   !} ; 
    sym-assoc      = {!   !} ; 
    identityˡ      = {!   !} ; 
    identityʳ      = {!   !} ; 
    F₁-η₂-morphism = refl ; 
    F₂-η₁-morphism = λ {X} → η₁.sym-commute {X} (η₂.η X) ; 
    η₁-composition = λ {X} → {!   !} ; 
    η₂-composition = λ {X} → {!   !} ; 
    middle-unity   = {!   !} }
    where 
      open DistributiveLaw dist-law

      θ' : NaturalTransformation (F₁ ∘F (F₂ ∘F F₁) ∘F F₂) (F₁ ∘F (F₁ ∘F F₂) ∘F F₂)
         → NaturalTransformation (F₁ ∘F (F₂ ∘F F₁) ∘F F₂) ((F₁ ∘F F₁) ∘F F₂ ∘F F₂)
      θ' nat = record { 
        η           = NaturalTransformation.η nat ; 
        commute     = NaturalTransformation.commute nat ; 
        sym-commute = NaturalTransformation.sym-commute nat }

      μ' : NaturalTransformation (F₁ ∘F (F₂ ∘F F₁) ∘F F₂) (F₁ ∘F F₂)
         → NaturalTransformation ((F₁ ∘F F₂) ∘F F₁ ∘F F₂) (F₁ ∘F F₂)
      μ' nat = record { 
        η           = NaturalTransformation.η nat ; 
        commute     = NaturalTransformation.commute nat ; 
        sym-commute = NaturalTransformation.sym-commute nat }


  CompatibleComposition-DistributiveLaw : CompatibleComposition Mon₁ Mon₂ → DistributiveLaw Mon₁ Mon₂
  CompatibleComposition-DistributiveLaw composition = record { 
    θ            = θ' (μ ∘ᵥ ((η₁ ∘ʳ F₂) ∘ₕ (F₁ ∘ˡ η₂))) ; 
    F₂-identity  = {!   !} ; 
    F₁-identity  = {!   !} ; 
    F₁-transform = {!   !} ; 
    F₂-transform = {!   !} }
    where 
      open CompatibleComposition composition

      θ' : NaturalTransformation ((idF ∘F F₂) ∘F F₁ ∘F idF) (F₁ ∘F F₂)
         → NaturalTransformation (F₂ ∘F F₁) (F₁ ∘F F₂)
      θ' nat = record { 
        η           = NaturalTransformation.η nat ; 
        commute     = NaturalTransformation.commute nat ; 
        sym-commute = NaturalTransformation.sym-commute nat }

        