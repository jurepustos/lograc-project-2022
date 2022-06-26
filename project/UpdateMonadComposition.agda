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
          proj₂ ((T₀.F₁ (μ₁.η S) ∘ θ.η (T₁.F₀ S) ∘ T₁.F₁ (θ.η S)) ((m₁ , (m₂ ,  id))) s)
        ≡⟨ {!   !} ⟩ -- we need lemma 8 for this step
          proj₂ ((T₀.F₁ (μ₁.η S) ∘ θ.η (T₁.F₀ S)) ((m₁ , λ (s₁ : S) → (m₂ , ((s₁ ↓' m₂))))) s) 
        ≡⟨ refl ⟩
          proj₂ ((T₀.F₁ (μ₁.η S) ∘ θ.η (T₁.F₀ S) ∘ T₁.F₁ (T₀.F₁ (λ s' →  (m₂ , s' ↓' m₂)))) ((m₁ , id)) s) 
        ≡⟨ θ-naturality s m₁ m₂ ⟩
          proj₂ ((T₀.F₁ (μ₁.η S) ∘ T₀.F₁ (T₁.F₁ (λ s' →  (m₂ , s' ↓' m₂))) ∘ θ.η S) ((m₁ , id)) s) 
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

        θ-naturality : (s : S) (m₁ m₂ : M) → proj₂ ((T₀.F₁ (μ₁.η S) ∘ θ.η (T₁.F₀ S) ∘ T₁.F₁ (T₀.F₁ (λ s' →  (m₂ , s' ↓' m₂)))) ((m₁ , id)) s) ≡
                            proj₂ ((T₀.F₁ (μ₁.η S) ∘ T₀.F₁ (T₁.F₁ (λ s' →  (m₂ , s' ↓' m₂))) ∘ θ.η S) ((m₁ , id)) s) 
        θ-naturality s m₁ m₂ = 
          begin 
            proj₂((T₀.F₁ (μ₁.η S) ∘  θ.η (T₁.F₀ S) ∘ T₁.F₁ (T₀.F₁ (λ s' → m₂ , (s' ↓' m₂)))) (m₁ , id) s)
          ≡⟨ refl ⟩
            proj₂ ((T₀.F₁ (μ₁.η S) ∘  θ.η (T₁.F₀ S)) (m₁ , (T₀.F₁ (λ s' → m₂ , (s' ↓' m₂)) id)) s)
          ≡⟨ {!   !} ⟩
            proj₂ ((T₀.F₁ (μ₁.η S)) (λ s' → m₁ , (m₂ , (((s' ↓' m₁) ↓' m₂)))) s)
          ≡⟨ refl ⟩
            proj₂ ((T₀.F₁ (μ₁.η S) ∘ T₀.F₁ (T₁.F₁ (λ s' → m₂ , (s' ↓' m₂)))) (λ s' → (m₁ , id (s' ↓' m₁))) s)
          ≡⟨ refl ⟩
            proj₂((T₀.F₁ (μ₁.η S) ∘ T₀.F₁ (T₁.F₁ (λ s' → m₂ , (s' ↓' m₂))) ∘ θ.η S) (m₁ , id) s)
          ∎

           