module UpdateMonadAlgebra where

open import Level                 renaming (zero to lzero; suc to lsuc)

import Relation.Binary.PropositionalEquality as Eq
open Eq                           using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect)

open import Data.Product          using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)

open import Monoids               using (Monoid; RightAction)

record UpdateMonadAlgebra (X S : Set) (P : Monoid {lzero}) (A : RightAction P S) : Set (lsuc lzero) where
  open Monoid P
  open RightAction A
  field
    lookup : (S → X) → X
    update : M → X → X

  field
    identity : {x : X} → lookup (λ s → update ε x) ≡ x 
    update-update : {p p' : M} {x : X} → update p (update p' x) ≡ update (p ⊕ p') x
    lookup-update : {p p' : M} {x : X} → {!   !}