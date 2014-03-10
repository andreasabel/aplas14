module Fix where

open import Library
open import Types
open import Terms

-- μ X. ▸X → A

fix : ∀{g} (a : Ty⁰ g) → Ty⁰ (suc g)
fix a = μ̂ λ g≤g' → (▸̂ vzero) →̂ ty≤K g≤g' (weakTy a)

-- self application

omega' : ∀{g}{Γ : Cxt g}{a : Ty⁰ g} → Tm (cxt↑ Γ) (fix a) → Tm Γ a
omega' x = app ({!cast ? x!}) ((▹ x))

-- omega : ∀{g}{Γ : Cxt g}{a : Ty⁰ ?} → Tm Γ (▸̂ fix a) → Tm Γ (▸̂ a)
-- omega x = {!(▹ (abs (unfold (var zero)))) ∗ x!} ∗ (▹ x)
