module WriterMonad where

open import Level                 renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Monad
open import Categories.Functor
open import Categories.NaturalTransformation

open import Function              using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                           using (_≡_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning               using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Product          using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)

open import SetMonoid             using (Monoid)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero

writer-functor : (P : Monoid {lzero}) → Endofunctor Sets0
writer-functor P = record { 
  F₀           = λ X → M × X ; 
  F₁           = λ f (p , x) → p , f x ; 
  identity     = refl ; 
  homomorphism = refl ; 
  F-resp-≈     = λ {A} {B} {f} {g} 
                 → λ { eq {p , w} → cong (λ b → p , b) eq } }
  where open Monoid P

writer-η : (P : Monoid) → NaturalTransformation 
           Categories.Functor.id 
           (writer-functor P)
writer-η P = record { 
  η           = λ X → λ x → ε , x ; 
  commute     = λ _ → refl ; 
  sym-commute = λ _ → refl }
  where open Monoid P

writer-µ : (P : Monoid) → NaturalTransformation 
           (writer-functor P ∘F writer-functor P) 
           (writer-functor P)
writer-µ P = record { 
  η           = λ X → λ { (p , (p' , x)) → (p ⊕ p') , x } ; 
  commute     = λ _ → refl ; 
  sym-commute = λ _ → refl }
  where open Monoid P

writer-monad : (P : Monoid {lzero}) → Monad Sets0
writer-monad P = record { 
  F         = writer-functor P ; 
  η         = writer-η P ; 
  μ         = writer-µ P ; 
  assoc     = writer-assoc ; 
  sym-assoc = sym writer-assoc ; 
  identityˡ = writer-identityˡ ; 
  identityʳ = writer-identityʳ } 
  where 
    open Monoid P

    writer-assoc : {X : Set} {w : Σ M (λ p → Σ M (λ p' → Σ M (λ p'' → X)))} →
                   (proj₁ w ⊕ (proj₁ (proj₂ w) ⊕ proj₁ (proj₂ (proj₂ w))) ,
                   proj₂ (proj₂ (proj₂ w)))
                   ≡
                   (proj₁ w ⊕ proj₁ (proj₂ w) ⊕ proj₁ (proj₂ (proj₂ w)) ,
                   proj₂ (proj₂ (proj₂ w)))

    writer-assoc {X} {p , (p' , (p'' , x))}
      rewrite ⊕-assoc p p' p''
      = refl

    writer-identityˡ : {X : Set} {w : Σ M (λ x₁ → X)} 
                       → (proj₁ w ⊕ ε , proj₂ w) ≡ w
                       
    writer-identityˡ {X} {p , x} rewrite (ε-right p) = refl

    writer-identityʳ : {X : Set} {w : Σ M (λ x₁ → X)} 
                       → (ε ⊕ proj₁ w , proj₂ w) ≡ w
                       
    writer-identityʳ {X} {p , x} rewrite (ε-left p) = refl
