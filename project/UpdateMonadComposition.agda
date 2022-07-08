-- in this file we are proving, that every compatible composition of the reader
-- monad and the writer monad is an update monad, by proving, that distributive law
-- of these two monads defines an action ↓
-- on the other hand, also distrubutive law is defined by action ↓

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

-- distributive law is determined by action ↓
dist-law-from-action : {S : Set} → {P : Monoid {lzero}} 
            → (A : RightAction P S)
            → DistributiveLaw (reader-monad S) (writer-monad P)
dist-law-from-action {S} {P} A = record { 
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
  where
    open Monoid P
    open RightAction A

-- distributive law defines a ↓ action
action-from-dist-law : {S : Set} → {P : Monoid {lzero}} 
          → DistributiveLaw (reader-monad S) (writer-monad P)
          → RightAction P S
action-from-dist-law {S} {P} dist-law = record { 
  _↓_          = λ s p → proj₂ (θ.η S (p , id) s) ; 
  ε-identity   = ε-identity' ; 
  homomorphism = homomorphism' }
  where 
    open Monoid P
    open DistributiveLaw dist-law

    ε-identity' : (s : S) 
                → proj₂ (θ.η S (ε , id) s) ≡ s
    ε-identity' s rewrite F₁-identity {S} {id} = refl
  
    homomorphism' : (m₁ m₂ : M) (s : S)
                  → proj₂ (θ.η S (m₁ ⊕ m₂ , id) s) ≡
                    proj₂ (θ.η S (m₂ , id) 
                      (proj₂ (θ.η S (m₁ , id) s)))
    homomorphism' m₁ m₂ s = 
      begin
          proj₂ (θ.η S (m₁ ⊕ m₂ , id) s)
        ≡⟨ refl ⟩
          proj₂ ((θ.η S ∘ μ₁.η (T₀.F₀ S)) (m₁ , (m₂ , id)) s)
        ≡⟨ cong (λ fun → proj₂ (fun s)) F₂-transform ⟩
          proj₂ (((T₀.F₁ (μ₁.η S) ∘ θ.η (T₁.F₀ S) ∘ T₁.F₁ (θ.η S)) (m₁ , (m₂ ,  id))) s)
        ≡⟨ refl ⟩ 
          proj₂ (proj₂ (θ.η (Σ M (λ x → S)) (m₁ , θ.η S (m₂ , (λ x → x))) s))
        ≡⟨ refl ⟩
          proj₂ (proj₂ (θ.η (Σ M (λ x → S)) (m₁ , (λ s' → θ.η S (m₂ , id) s')) s))
        ≡⟨ refl ⟩
          proj₂ (proj₂ (θ.η (Σ M (λ x → S)) (m₁ , (λ s' → proj₁ (θ.η S (m₂ , id) s') , proj₂ (θ.η S (m₂ , id) s')) ) s))
        ≡⟨ cong (λ lemma → proj₂ (proj₂ (θ.η (Σ M (λ x → S)) (m₁ , lemma) s))) (fun-ext aux-identity-projection) ⟩
          proj₂ (proj₂ (θ.η (Σ M (λ x → S)) (m₁ , (λ s' → m₂ , proj₂ (θ.η S (m₂ , (λ x → x)) s'))) s))
        ≡⟨ refl ⟩
          proj₂ ((T₀.F₁ (μ₁.η S) ∘ θ.η (T₁.F₀ S)) (m₁ , (λ s' → (m₂ , s' ↓' m₂))) s)
        ≡⟨ refl ⟩
          proj₂ ((T₀.F₁ (μ₁.η S) ∘ (θ.η (T₁.F₀ S) ∘ T₁.F₁ (T₀.F₁ (λ s' → (m₂ , s' ↓' m₂))))) (m₁ , id) s) 
        ≡⟨ cong (λ fun → proj₂ ((T₀.F₁ (μ₁.η S) ∘ fun) (m₁ , id) s)) (fun-ext (λ y → θ.commute (λ s' → (m₂ , s' ↓' m₂)) {y})) ⟩
          proj₂ ((T₀.F₁ (μ₁.η S) ∘ (T₀.F₁ (T₁.F₁ (λ s' → (m₂ , s' ↓' m₂))) ∘ θ.η S)) (m₁ , id) s) 
        ≡⟨ refl ⟩
          proj₂ ((T₀.F₁ (μ₁.η S) ∘ T₀.F₁ (T₁.F₁ (λ s' →  (m₂ , s' ↓' m₂)))) (λ s₁ → (m₁ , (s₁ ↓' m₁))) s) 
        ≡⟨ refl ⟩
          proj₂ (T₀.F₁ (μ₁.η S) (λ s₁ → (m₁ , (m₂ , ((s₁ ↓' m₁) ↓' m₂)))) s)
        ≡⟨ refl ⟩
          proj₂ ((λ (s₁ : S) → ((m₁ ⊕ m₂) , ((s₁ ↓' m₁) ↓' m₂) )) s)
        ≡⟨ refl ⟩
          proj₂ (θ.η S (m₂ , id) (proj₂ (θ.η S (m₁ , id) s)))
      ∎ 
      where
        open Monad (writer-monad P) renaming (F to T₁; η to η₁; μ to μ₁)
        open Monad (reader-monad S) renaming (F to T₀; η to η₀; μ to μ₀)
        
        _↓'_ : S → M → S
        _↓'_ s p = proj₂ (θ.η S (p , id) s)

      -- lemma 8 from the article
        identity-projection : (s : S) (p : M) → p ≡ proj₁ (θ.η S (p , id) s)
        identity-projection s p =
          begin
            p
          ≡⟨ refl ⟩
            proj₁ ((λ s' → (p , s')) s)
          ≡⟨ refl ⟩
            proj₁ ( η₀.η (T₁.F₀ S) (p , s) s )
          ≡⟨ cong (λ fun → proj₁ (fun s)) (sym F₂-identity) ⟩
            proj₁ ((θ.η S ∘ T₁.F₁ (η₀.η S)) ((p , _)) s)
          ≡⟨ refl ⟩
            proj₁ (θ.η S ((p , λ s' → _)) s)
          ≡⟨ refl ⟩
            proj₁ ((θ.η S ∘ T₁.F₁ (T₀.F₁ (λ s' → _))) (p , id) s)
          ≡⟨ cong (λ fun → proj₁ (fun s)) (θ.commute (λ _ → s)) ⟩
            proj₁ ((T₀.F₁ (T₁.F₁ (λ s' → s')) ∘ θ.η S) (p , id) s)
          ≡⟨ refl ⟩
            proj₁ (θ.η S (p , id) s)
          ∎

        aux-identity-projection : (x : S) →
            (proj₁ (θ.η S (m₂ , id) x) , proj₂ (θ.η S (m₂ , id) x)) ≡ (m₂ , proj₂ (θ.η S (m₂ , (λ x₁ → x₁)) x))
        aux-identity-projection x = cong₂ _,_ (sym (identity-projection x m₂)) refl
                  