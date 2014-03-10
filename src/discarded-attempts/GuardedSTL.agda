
module _ where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)

open import Types

module Sem (TY' : Set) (let TY = ℕ → TY')
    (⟦⊤⟧ : TY)
    (⟦▸⟧ : TY' → TY')
    (⟦1⟧ : TY)
    (_⟦×⟧_ _⟦+⟧_ _⟦→⟧_ : TY → TY → TY)
    (⟦C⟧ : TY → TY)
  where

  mutual
{-
    C⟦_⟧ : ∀ {g} → Ty⁰ g → TY
    C⟦ a ⟧ n = ⟦C⟧ V⟦ a ⟧ n
-}
    V⟦_⟧ : ∀ {g} → Ty⁰ g → TY
    V⟦ var () ⟧ n
    V⟦ 1̂     ⟧ n = ⟦1⟧ n
    V⟦ ▸̂ a   ⟧ zero = ⟦▸⟧ (⟦⊤⟧ zero)
--    V⟦_⟧ {g} (▸̂ a) (suc n) =  ⟦▸⟧ (V⟦_⟧ {suc g} a n)
    V⟦ ▸̂ a   ⟧ (suc n) =  ⟦▸⟧ (V⟦ a ⟧ n)
    V⟦ a ×̂ b ⟧ n = (V⟦ a ⟧ ⟦×⟧ V⟦ b ⟧) n
    V⟦ a +̂ b ⟧ n = (V⟦ a ⟧ ⟦+⟧ V⟦ b ⟧) n
    V⟦ a →̂ b ⟧ n = (V⟦ a ⟧ ⟦→⟧ V⟦ b ⟧) n
--    V⟦_⟧ {suc g} (μ̂ f) n =  V⟦_⟧ {g} (f · (μ̂ f)) n
    V⟦ μ̂ f   ⟧ n =  V⟦ f · (μ̂ f) ⟧ n

