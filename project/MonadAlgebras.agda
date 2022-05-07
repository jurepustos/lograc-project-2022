module MonadAlgebras where

open import Level                 renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Monad

open import Data.Product          using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)

open import Function              using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                           using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect; [_])

open import UpdateMonad using (update-monad; update-functor)
open import Monoids using (Monoid; RightAction)
open import Categories.Functor

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero

record MonadAlgebra : Set (lsuc lzero) where
  field
    Mon : Monad Sets0
  
  open Monad Mon

  field
    A : Set
    α : F.F₀ A → A

  field
    η-identity : α ∘ η.η A ≡ Function.id
    µ-homomorphism : α ∘ μ.η A ≡ α ∘ F.F₁ α


module _ (S : Set) (P : Monoid {lzero}) (A : RightAction P S) where

  U : Monad Sets0
  U = update-monad S P A
  
  open Monad U
  open Monoid P
  open RightAction A

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


    


        