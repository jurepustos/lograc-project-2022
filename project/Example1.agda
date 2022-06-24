-- in this file we are looking at example of special cases of update monads, reader and writer monad

module Example1 where

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
open import ReaderMonad           using (reader-monad)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

Sets0 : Category (lsuc lzero) lzero lzero
Sets0 = Sets lzero

UpdMon-ReadMon : {S : Set} {P : Monoid {lzero}} {A : RightAction P S}
                  → update-monad S P A
                  → reader-monad S 

UpdMon-ReadMon {S} {P} {A} UpdMon = record { 
    F         = ?;         
    η         = ?;
    μ         = ?;
    assoc     = ?;
    sym-assoc = ?;
    identityˡ = ?;
    identityʳ = ? }
        where
          open Monoid P
          open RightAction A

          


