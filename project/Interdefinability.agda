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

module _ (X S : Set) (P : Monoid {lzero}) (A : RightAction P S) 
         (UpMonAlg : UpdateMonadAlgebra S P A X) where

  open RightAction A
  open Monoid P

  U : Monad Sets0
  U = update-monad S P A
  

  module _ (act : (S → M × X) → X) 
           (id : (x : X) → act (λ _ → ε , x) ≡ x) 
           (hom : (ttx : S → M × (S → M × X)) →
            act (λ s →
              proj₁ (ttx s) ⊕ proj₁ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))) ,
              proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))))
            ≡ act (λ s → proj₁ (ttx s) , act (proj₂ (ttx s)))) where

    MonAlg : MonadAlgebra
    MonAlg = update-monad-algebra S P A X act id hom

    UpMonAlg-MonAlg : MonadAlgebra
    UpMonAlg-MonAlg = record { 
      Mon            = U ; 
      A              = X ; 
      α              = λ tx → lookup (λ s → update (tx s)) ; 
      η-identity     = fun-ext η-identity-aux ; 
      µ-homomorphism = fun-ext λ ttx → cong lookup 
                        (fun-ext (λ s → cong update (µ-homomorphism-aux ttx s))) }
      where 
        open UpdateMonadAlgebra UpMonAlg

        η-identity-aux : (x : X) → lookup (λ s → update (ε , x)) ≡ x
        η-identity-aux x = identity x

        µ-homomorphism-aux : (ttx : S → M × (S → M × X))
                             (s : S) → 
                             (proj₁ (ttx s) ⊕ proj₁ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))) ,
                              proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))))
                              ≡ (proj₁ (ttx s) , lookup (λ s₁ → update (proj₂ (ttx s) s₁)))
        µ-homomorphism-aux ttx s
          rewrite lookup-update-lookup ttx = {!   !}


    MonAlg-UpMonAlg : UpdateMonadAlgebra S P A X
    MonAlg-UpMonAlg = record { 
      lookup               = λ f → act (λ s → ε , f s) ; 
      update               = λ { (p , x) → act (λ _ → p , x) } ; 
      identity             = identity-aux ; 
      update-update        = λ p p' x → cong act (fun-ext (λ s → update-update-aux p p' x)) ; 
      lookup-update-lookup = λ ttx → cong act (fun-ext λ s → 
                              cong (λ x → ε , x) (cong act (fun-ext (λ s' → 
                              cong (λ x → proj₁ (ttx s) , x) (lookup-update-lookup-aux ttx s s'))))) }
      where
        identity-aux : (x : X) →  act (λ s → ε , act (λ s₁ → ε , x)) ≡ x
        identity-aux x 
          rewrite id x 
          rewrite id x = refl

        update-update-aux : (p p' : M)
                            (x : X) →
                            (p , act (λ _ → p' , x)) ≡ (p ⊕ p' , x)
        update-update-aux p p' x = {!   !}

        lookup-update-lookup-aux : (ttx : S → M × (S → M × X))
                                   (s s' : S) →
                                   act (λ s₁ → ε , proj₂ (proj₂ (ttx s) s₁)) ≡
                                   proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))
        lookup-update-lookup-aux ttx s s' = {!   !}


            