module Monoids where

open import Level renaming (zero to lzero; suc to lsuc)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

record Monoid {l} : Set (lsuc l) where
  infixl 7 _⊕_
  field
    -- carrier type of the monoid
    M       : Set l
    -- identity element (unicode with `\epsilon`)
    ε       : M
    -- binary operation (unicode with `\cdot`)
    _⊕_     : M → M → M
    -- monoid laws
    ε-left  : (m : M) → ε ⊕ m ≡ m
    ε-right : (m : M) → m ⊕ ε ≡ m
    ⊕-assoc : (m₁ m₂ m₃ : M) → (m₁ ⊕ m₂) ⊕ m₃ ≡ m₁ ⊕ (m₂ ⊕ m₃)

record RightAction {l} (Mon : Monoid {l}) (X : Set) : Set (lsuc l) where
  open Monoid Mon

  infixl 6 _↓_
  field
    _↓_          : X → M → X
    ε-identity   : (x : X) → x ↓ ε ≡ x
    homomorphism : (m₁ m₂ : M) (x : X) → x ↓ m₁ ⊕ m₂ ≡ x ↓ m₁ ↓ m₂

