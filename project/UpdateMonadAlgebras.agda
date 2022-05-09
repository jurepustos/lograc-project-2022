module UpdateMonadAlgebras where

open import Level                 renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Monad

import Relation.Binary.PropositionalEquality as Eq
open Eq                           using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect)

open import Data.Product          using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)

open import Monoids               using (Monoid; RightAction)
open import UpdateMonad           using (update-monad)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero

module _ (S : Set) (P : Monoid {lzero}) (A : RightAction P S) where

  U : Monad Sets0
  U = update-monad S P A

  record UpdateMonadAlgebra (X : Set) : Set (lsuc lzero) where
    open Monoid P
    open RightAction A
    open Monad U

    field
      lookup : (S → X) → X
      update : M × X → X

    field
      identity : (x : X) → lookup (λ s → update (ε , x)) ≡ x 
      update-update : (p p' : M) (x : X) → update (p , (update (p' , x))) ≡ update ((p ⊕ p') , x)
      lookup-update-lookup : (ttx : S → M × (S → M × X)) → 
                             lookup (λ s → 
                              update ((proj₁ (ttx s)) , (lookup (λ s' → 
                                proj₂ (proj₂ (ttx s) s'))))) 
                             ≡ lookup (λ s → 
                                update ((proj₁ (ttx s)) , 
                                (proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))))))
                          