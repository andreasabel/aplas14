-- Imports from the standard library

module Library where

open import Data.List using (List; []; _∷_; map) public
open import Data.Nat
  using    (ℕ; zero; suc; z≤n; s≤s)
  renaming (_≤_ to _≤ℕ_; decTotalOrder to decTotalOrderℕ; _⊔_ to max)
  public
open import Data.Nat.Properties using (_+-mono_) public
open import Data.Product using (_×_; _,_; proj₁; proj₂) public
open import Data.Unit using (⊤) public

open import Function using (_∘_) public

open import Induction.WellFounded using (Acc; acc) public

open import Relation.Binary using (module DecTotalOrder)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_) public
module ≡ = PropEq
open import Relation.Unary using (_∈_; _⊆_) public

module DecTotalOrderℕ = DecTotalOrder decTotalOrderℕ

caseMax : ∀{m n} (P : ℕ → Set)
          → (pn : (m≤n : m ≤ℕ n) → P n)
          → (pm : (n≤m : n ≤ℕ m) → P m)
          → P (max m n)
caseMax {zero } {n    } P pn pm = pn z≤n
caseMax {suc m} {zero } P pn pm = pm z≤n
caseMax {suc m} {suc n} P pn pm = caseMax (P ∘ suc) (pn ∘ s≤s) (pm ∘ s≤s)

n≤sn : ∀{n} → n ≤ℕ suc n
n≤sn = (z≤n {1}) +-mono DecTotalOrderℕ.refl
