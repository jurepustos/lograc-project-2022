module UpdateMonad where

open import Level                 renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Monad
open import Categories.Functor
open import Categories.NaturalTransformation

open import Function              using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                           using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect)
open Eq.≡-Reasoning               using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Product          using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)

open import SetMonoid             using (Monoid; RightAct)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero

update-functor : (S : Set) 
               → (P : Monoid {lzero}) 
               → Endofunctor Sets0
               
update-functor S P = record { 
  F₀           = λ X → S → M × X ; 
  F₁           = λ f u → λ s → proj₁ (u s) , f (proj₂ (u s)) ; 
  identity     = refl ; 
  homomorphism = refl ;
  F-resp-≈     = λ {A} {B} {f} {g} → λ eq {u} 
                 → fun-ext (λ s → cong (λ b → proj₁ (u s) , b) eq) }
  where open Monoid P

update-η : (S : Set) 
           → (P : Monoid {lzero}) 
           → NaturalTransformation 
             Categories.Functor.id
             (update-functor S P)
update-η S P = record { 
  η           = λ X → λ x → λ _ → ε , x ; 
  commute     = λ _ → refl ; 
  sym-commute = λ _ → refl }
  where open Monoid P

update-µ : (S : Set) 
           → (P : Monoid {lzero}) 
           → (A : RightAct P S)
           → NaturalTransformation 
             (update-functor S P ∘F update-functor S P)
             (update-functor S P)
             
update-µ S P A = record { 
  η           = η-aux ; 
  commute     = λ _ → refl ; 
  sym-commute = λ _ → refl }
  where 
    open Monoid P
    open RightAct A

    η-aux : (X : Set) 
            → (S → Σ M (λ x → S → Σ M (λ x₁ → X))) 
            → S → Σ M (λ x → X)
    η-aux X u s with u s
    η-aux X u s | p' , u' with u' (s ↓ p')
    ... | p'' , x = (p' ⊕ p'') , x
               
update-monad : (S : Set) 
               → (P : Monoid {lzero}) 
               → (A : RightAct P S) 
               → Monad Sets0

update-monad S P A = record { 
  F         = update-functor S P ; 
  η         = update-η S P ; 
  μ         = update-µ S P A ; 
  assoc     = λ {X} {u} → fun-ext (λ s → update-assoc-aux u s) ; 
  sym-assoc = λ {X} {u} → fun-ext (λ s → sym (update-assoc-aux u s)) ; 
  identityˡ = λ {X} {u} → fun-ext (λ s → update-identityˡ u s) ; 
  identityʳ = λ {X} {u} → fun-ext (λ s → update-identityʳ u s) }
  where
    open Monoid P
    open RightAct A

    update-assoc-aux : {X : Set} →
                       (u : S → Σ M (λ x₁ → S → Σ M (λ x₂ → S → Σ M (λ x₃ → X)))) →
                       (s : S) → 
                       (proj₁ (u s) ⊕
                         (proj₁ (proj₂ (u s) (s ↓ proj₁ (u s))) ⊕
                           proj₁
                           (proj₂ (proj₂ (u s) (s ↓ proj₁ (u s)))
                           (s ↓ proj₁ (u s) ↓ proj₁ (proj₂ (u s) (s ↓ proj₁ (u s))))))
                         ,
                         proj₂
                         (proj₂ (proj₂ (u s) (s ↓ proj₁ (u s)))
                           (s ↓ proj₁ (u s) ↓ proj₁ (proj₂ (u s) (s ↓ proj₁ (u s))))))
                         ≡
                         (proj₁ (u s) ⊕ proj₁ (proj₂ (u s) (s ↓ proj₁ (u s))) ⊕
                         proj₁
                         (proj₂ (proj₂ (u s) (s ↓ proj₁ (u s)))
                           (s ↓ proj₁ (u s) ⊕ proj₁ (proj₂ (u s) (s ↓ proj₁ (u s)))))
                         ,
                         proj₂
                         (proj₂ (proj₂ (u s) (s ↓ proj₁ (u s)))
                           (s ↓ proj₁ (u s) ⊕ proj₁ (proj₂ (u s) (s ↓ proj₁ (u s))))))

    update-assoc-aux u s with u s
    update-assoc-aux u s | p' , u' with u' (s ↓ p')
    update-assoc-aux u s | p' , u' | p'' , u''
      rewrite homomorphism p' p'' s 
      rewrite ⊕-assoc p' p'' (proj₁ (u'' (s ↓ p' ↓ p''))) = refl

    update-identityˡ : {X : Set}
                       (u : S → Σ M (λ x → X))
                       → (s : S)
                       → (proj₁ (u s) ⊕ ε , proj₂ (u s)) ≡ u s
    
    update-identityˡ u s with u s
    ... | p , x rewrite ε-right p = refl

    update-identityʳ : {X : Set}
                       (u : S → Σ M (λ x → X))
                       → (s : S)
                       → (ε ⊕ proj₁ (u (s ↓ ε)) , proj₂ (u (s ↓ ε))) ≡ u s
    update-identityʳ u s 
      rewrite ε-identity s
      rewrite ε-left (proj₁ (u s)) = refl 