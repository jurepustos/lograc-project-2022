module UpdateMonadAlgebras where

open import Level                 renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Monad

import Relation.Binary.PropositionalEquality as Eq
open Eq                           using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect)
open Eq.≡-Reasoning               using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

open import Data.Product          using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)

open import Monoids               using (Monoid; RightAction)
open import UpdateMonad           using (update-monad)
open import MonadAlgebras         using (MonadAlgebra)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero

module _ (S : Set) (P : Monoid {lzero}) (A : RightAction P S) where

  U : Monad Sets0
  U = update-monad S P A
  
  open Monad U
  open Monoid P
  open RightAction A

  record UpdateMonadAlgebra (X : Set) : Set (lsuc lzero) where
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


  update-monad-algebra : (X : Set) 
                         (act : (S → M × X) → X)
                         (id : (x : X) → act (λ _ → ε , x) ≡ x)
                         (hom : (ttx : S → M × (S → M × X)) →
                          act (λ s →
                            proj₁ (ttx s) ⊕ proj₁ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))) ,
                            proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))))
                            ≡ act (λ s → proj₁ (ttx s) , act (proj₂ (ttx s))))
                         → MonadAlgebra
                        
  update-monad-algebra X act id hom = record { 
    Mon            = U          ;
    A              = X          ; 
    α              = act        ;
    η-identity     = fun-ext id ; 
    µ-homomorphism = fun-ext hom }


  module _ (X : Set) (UpMonAlg : UpdateMonadAlgebra X)
           (act : (S → M × X) → X) 
           (id : (x : X) → act (λ _ → ε , x) ≡ x) 
           (hom : (ttx : S → M × (S → M × X)) →
            act (λ s →
              proj₁ (ttx s) ⊕ proj₁ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))) ,
              proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))))
            ≡ act (λ s → proj₁ (ttx s) , act (proj₂ (ttx s)))) where

    MonAlg : MonadAlgebra
    MonAlg = update-monad-algebra X act id hom

    UpMonAlg-MonAlg : MonadAlgebra
    UpMonAlg-MonAlg = record { 
      Mon            = U ; 
      A              = X ; 
      α              = λ tx → lookup (λ s → update (tx s)) ; 
      η-identity     = fun-ext η-identity-aux ; 
      µ-homomorphism = fun-ext µ-homomorphism-aux }
      where 
        open UpdateMonadAlgebra UpMonAlg

        η-identity-aux : (x : X) → lookup (λ s → update (ε , x)) ≡ x
        η-identity-aux x = identity x

        µ-homomorphism-aux : (ttx : S → M × (S → M × X)) →
                             lookup (λ s →
                              update
                              (proj₁ (ttx s) ⊕ proj₁ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))) ,
                                proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))))
                             ≡ lookup (λ s →
                              update (proj₁ (ttx s) , 
                                lookup (λ s₁ → update (proj₂ (ttx s) s₁))))
        µ-homomorphism-aux ttx = 
          begin
            lookup (λ s → update (proj₁ (ttx s) ⊕ proj₁ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))), proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))))) 
              ≡⟨ cong lookup (fun-ext lookup-inside-aux) ⟩
            lookup (λ s → update (proj₁ (ttx s) , update (proj₁ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))))) 
              ≡⟨ sym (lookup-update-lookup (λ z → proj₁ (ttx z) , (λ z₁ → proj₁ (ttx z₁) , update (proj₂ (ttx z) z₁)))) ⟩           
            lookup (λ s → update (proj₁ (ttx s) , lookup (λ s₁ → update (proj₂ (ttx s) s₁))))
          ∎
            where
              lookup-inside-aux : (s : S) → 
                                    update (proj₁ (ttx s) ⊕ proj₁ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))), proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))) ≡
                                    update (proj₁ (ttx s) , update (proj₁ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))))
              lookup-inside-aux s = 
                begin 
                  update (proj₁ (ttx s) ⊕ proj₁ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))))
                ≡⟨ sym (update-update (proj₁ (ttx s)) (proj₁ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))) (proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))))) ⟩
                  update (proj₁ (ttx s) , update (proj₁ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))))
                ∎ 


    MonAlg-UpMonAlg : UpdateMonadAlgebra X
    MonAlg-UpMonAlg = record { 
      lookup               = lookup-aux ; 
      update               = update-aux ; 
      identity             = identity-aux ; 
      update-update        = update-update-aux ; 
      lookup-update-lookup = lookup-update-lookup-aux }
      where
        open MonadAlgebra MonAlg

        lookup-aux : (S → X) → X
        lookup-aux f = act (λ s → ε , f s)

        update-aux : M × X → X
        update-aux (p , x) = act (λ _ → p , x)

        identity-aux : (x : X) →  act (λ s → ε , act (λ s₁ → ε , x)) ≡ x
        identity-aux x 
          rewrite id x 
          rewrite id x = refl

        update-update-aux : (p p' : M) 
                            (x : X) →
                            act (λ _ → p , 
                              act (λ _ → p' , x)) 
                            ≡ act (λ _ → p ⊕ p' , x)
        update-update-aux p p' x = 
          begin
            act (λ _ → p , act (λ _ → p' , x))
          ≡⟨ sym (hom (λ z → p , (λ z₁ → p' , x))) ⟩
            act (λ _ → p ⊕ p' , x)
          ∎

        lookup-update-lookup-aux : (ttx : S → M × (S → M × X)) →
                                   act (λ s → ε , act (λ _ → proj₁ (ttx s) , act (λ s₁ → ε , proj₂ (proj₂ (ttx s) s₁)))) ≡ 
                                   act (λ s → ε , act (λ _ → proj₁ (ttx s) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))))
        
        lookup-update-lookup-aux ttx = 
          begin
            act(λ s → ε , act (λ _ → proj₁ (ttx s) , act (λ s₁ → ε , proj₂ (proj₂ (ttx s) s₁))))
          ≡⟨ sym (function-comm-aux (λ z → proj₁ (ttx z) , (λ z₁ → proj₁ (ttx z) , proj₂ (proj₂ (ttx z) z₁)))) ⟩
            act(λ _ → ε , act (λ s → proj₁ (ttx s) , act (λ s₁ → ε , proj₂ (proj₂ (ttx s) s₁))))
          ≡⟨ id (act (λ s → proj₁ (ttx s) , act (λ s₁ → ε , proj₂ (proj₂ (ttx s) s₁)))) ⟩
            act(λ s → proj₁ (ttx s) , act (λ s₁ → ε , proj₂ (proj₂ (ttx s) s₁)))
          ≡⟨ sym (hom (λ z → proj₁ (ttx z) , (λ s₁ → ε , proj₂ (proj₂ (ttx z) s₁)))) ⟩
            act (λ s → proj₁ (ttx s) ⊕ ε , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))))
          ≡⟨ sym (id (act (λ s → proj₁ (ttx s) ⊕ ε , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))))) ⟩
            act(λ _ → ε , act (λ s → proj₁ (ttx s) ⊕ ε , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))))
          ≡⟨ cong act (fun-ext unit-multiplication-aux) ⟩
            act(λ _ → ε , act (λ s → proj₁ (ttx s) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))))
          ≡⟨ other-function-comm-aux (λ z → proj₁ (ttx z) , (λ z₁ → proj₁ (ttx z) , proj₂ (proj₂ (ttx z) z₁))) ⟩
            act(λ s → ε , act (λ _ → proj₁ (ttx s) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))))
          ∎
            where
              unit-multiplication-aux : (x : S) →  (ε , act (λ s → proj₁ (ttx s) ⊕ ε , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))))) ≡
                                                                       (ε , act (λ s → proj₁ (ttx s) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))))
              unit-multiplication-aux x = 
                begin
                  ε , act (λ s → proj₁ (ttx s) ⊕ ε , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))))
                ≡⟨ cong₂ _,_ refl (cong act (fun-ext λ x₁ → cong₂ _,_ (ε-right (proj₁ (ttx x₁))) refl )) ⟩
                  ε , act (λ s → proj₁ (ttx s) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))))
                ∎

              function-comm-aux : (ttx : S → M × (S → M × X)) → act(λ _ → ε , act (λ s → proj₁ (ttx s) , act (λ s₁ → ε , proj₂ (proj₂ (ttx s) s₁)))) ≡
                                                                act(λ s → ε , act (λ _ → proj₁ (ttx s) , act (λ s₁ → ε , proj₂ (proj₂ (ttx s) s₁))))
              function-comm-aux ttx = 
                begin
                  act (λ _ → ε , act (λ s → proj₁ (ttx s) , act (λ s₁ → ε , proj₂ (proj₂ (ttx s) s₁))))
                ≡⟨ sym (hom λ z → ε , (λ s → proj₁ (ttx s) , act (λ s₁ → ε , proj₂ (proj₂ (ttx s) s₁))) ) ⟩
                  act (λ s → ε ⊕ proj₁ (ttx (s ↓ ε)) , act (λ s₁ → ε , proj₂ (proj₂ (ttx (s ↓ ε)) s₁)))
                ≡⟨ cong act (fun-ext (λ s → cong₂ _,_ (cong₂ _⊕_ refl (cong proj₁ (cong ttx (ε-identity s)))) (
                        cong act (fun-ext (λ s₁ → cong₂ _,_ refl (cong (λ s → proj₂ (proj₂ (ttx s) s₁)) (ε-identity s)) ))))) ⟩
                  act (λ s → ε ⊕ proj₁ (ttx s) , act (λ s₁ → ε , proj₂ (proj₂ (ttx s) s₁)))
                ≡⟨ hom (λ z → ε , (λ _ → proj₁ (ttx z) , act (λ s₁ → ε , proj₂ (proj₂ (ttx z) s₁)))) ⟩
                  act (λ s → ε , act (λ _ → proj₁ (ttx s) , act (λ s₁ → ε , proj₂ (proj₂ (ttx s) s₁))))
                ∎

              other-function-comm-aux : (ttx : S → M × (S → M × X)) → act(λ _ → ε , act (λ s → proj₁ (ttx s) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))))) ≡
                                                                      act(λ s → ε , act (λ _ → proj₁ (ttx s) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))))
              other-function-comm-aux ttx = 
                begin
                  act (λ _ → ε , act (λ s → proj₁ (ttx s) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))))
                ≡⟨ sym (hom (λ z → ε , (λ s → proj₁ (ttx s) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))))) ⟩
                  act (λ s → ε ⊕ proj₁ (ttx (s ↓ ε)) , proj₂ (proj₂ (ttx (s ↓ ε)) (s ↓ ε ↓ proj₁ (ttx (s ↓ ε)))))
                ≡⟨ cong act (fun-ext (λ s → cong₂ _,_ (cong₂ _⊕_ refl (cong proj₁ (cong ttx (ε-identity s)))) 
                        (cong (λ x →  proj₂ (proj₂ (ttx x) (x ↓ proj₁ (ttx x)))) (ε-identity s)) )) ⟩
                  act (λ s → ε ⊕ proj₁ (ttx s) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s))))
                ≡⟨ hom (λ z → ε , (λ _ → proj₁ (ttx z) , proj₂ (proj₂ (ttx z) (z ↓ proj₁ (ttx z))))) ⟩
                  act (λ s → ε , act (λ _ → proj₁ (ttx s) , proj₂ (proj₂ (ttx s) (s ↓ proj₁ (ttx s)))))
                ∎
 