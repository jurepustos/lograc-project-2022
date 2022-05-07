module Interdefinability where

open import Level                 renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Monad

import Relation.Binary.PropositionalEquality as Eq
open Eq                           using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect)

open import Data.Product          using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)

open import Monoids               using (Monoid; RightAction)
open import UpdateMonad           using (update-monad)
open import UpdateMonadAlgebras   using (UpdateMonadAlgebra)
open import MonadAlgebras         using (MonadAlgebra; update-monad-algebra)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero

module _ (X S : Set) (P : Monoid {lzero}) (A : RightAction P S) (UpMonAlg : UpdateMonadAlgebra S P A X) where

  open UpdateMonadAlgebra UpMonAlg
  open RightAction A
  open Monoid P

  module _ (act : (S → M × X) → X) 
           (id : (x : X) → act (λ _ → ε , x) ≡ x) 
           (hom : (x : S → Σ M (λ _ → S → Σ M (λ _ → X))) →
            act (λ s →
              proj₁ (x s) ⊕ proj₁ (proj₂ (x s) (s ↓ proj₁ (x s))) ,
              proj₂ (proj₂ (x s) (s ↓ proj₁ (x s))))
            ≡ act (λ s → proj₁ (x s) , act (proj₂ (x s)))) where

    MonAlg : MonadAlgebra
    MonAlg = update-monad-algebra S P A X act id hom

    open MonadAlgebra MonAlg 

    lookup-equiv : {x : S → Σ M (λ _ → X)} → lookup (λ s → proj₂ (x s)) ≡ α (λ s → ε , proj₂ (x s))
    lookup-equiv = {!   !}

    update-equiv : {p : M} {x : X} → update (p , x) ≡ α (λ _ → p , x)
    update-equiv = {!   !}

    comp-equiv : {x : S → Σ M (λ _ → X)} → α (λ s → x s) ≡ lookup (λ s → update (x s))
    comp-equiv = {!   !}
  