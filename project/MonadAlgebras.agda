-- this file contains definition of monad algebras

module MonadAlgebras where

open import Level                 renaming (zero to lzero; suc to lsuc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Functor
open import Categories.Monad

open import Data.Product          using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)

open import Function              using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                           using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect; [_])

open import UpdateMonad using (update-monad; update-functor)
open import Monoids using (Monoid; RightAction)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero

record MonadAlgebra (Mon : Monad Sets0) (A : Set) : Set (lsuc lzero) where 
  open Monad Mon

  -- map α
  field
    α : F.F₀ A → A

  -- conditions, that need to be satisfied
  field
    η-identity : α ∘ η.η A ≡ Function.id
    μ-homomorphism : α ∘ μ.η A ≡ α ∘ F.F₁ α



    


        