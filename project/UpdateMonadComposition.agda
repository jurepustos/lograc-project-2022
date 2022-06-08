module UpdateMonadComposition where

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

open import Monoids               using (Monoid; RightAction)
open import ReaderMonad           using (reader-monad)
open import WriterMonad           using (writer-monad)
open import MonadComposition      using (CompatibleComposition; DistributiveLaw)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero

module DistLawFromAction (S : Set) (P : Monoid {lzero}) (A : RightAction P S) where
  open Monoid P
  open RightAction A
  
  reader : Monad Sets0
  reader = reader-monad S

  writer : Monad Sets0
  writer = writer-monad P

  dist-law : DistributiveLaw reader writer
  dist-law = record { 
    θ            = record { 
      η           = λ _ (p , f) s → p , (f (s ↓ p)) ; 
      commute     = λ _ → refl ; 
      sym-commute = λ _ → refl } ; 
    F₂-identity  = refl ; 
    F₁-identity  = λ {_} {m} →
      fun-ext (λ s → cong₂ (λ p f → p , f) refl (cong m (ε-identity s))) ; 
    F₁-transform = refl ; 
    F₂-transform = λ {_} {m} →
      fun-ext (λ s → cong₂ (λ p f → p , f) refl (cong (proj₂ (proj₂ m)) (homomorphism (proj₁ m) (proj₁ (proj₂ m)) s))) }


module ActionFromDistLaw (S : Set) (P : Monoid {lzero}) where
  open Monoid P
  
  reader : Monad Sets0
  reader = reader-monad S

  writer : Monad Sets0
  writer = writer-monad P

  action : DistributiveLaw reader writer → RightAction P S
  action dist-law = record { 
    _↓_          = λ s p → proj₂ (θ.η S (p , id) s) ; 
    ε-identity   = ε-identity' ; 
    homomorphism = homomorphism' }
    where 
      open DistributiveLaw dist-law

      ε-identity' : (s : S) 
                  → proj₂ (θ.η S (ε , id) s) ≡ s
      ε-identity' s rewrite F₁-identity {S} {id} = refl
    
      homomorphism' : (m₁ m₂ : M) (s : S)
                    → proj₂ (θ.η S (m₁ ⊕ m₂ , id) s) ≡
                      proj₂ (θ.η S (m₂ , id) 
                        (proj₂ (θ.η S (m₁ , id) s)))
      homomorphism' m₁ m₂ s = {!    !}


       