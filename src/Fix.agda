module Fix where

open import Library
open import Types
open import Terms

-- μ X. ▸X → A

Fix : (A : Type) → Type
Fix (type a) = type μ̂ λ g≤g' → (▸̂ vzero) →̂ ty≤K g≤g' (weakTy a)

fix : ∀{g} (a : Ty⁰ g) → Ty⁰ (suc g)
fix a = μ̂ λ g≤g' → (▸̂ vzero) →̂ ty≤K g≤g' (weakTy a)

-- self application

omega' : ∀{Γ g}{a : Ty⁰ (suc g)} → Tm Γ (Fix (type a)) → Tm Γ (type a)
omega' x = app ({!unfold x!}) ((▹ x))

omega : ∀{Γ g}{a : Ty⁰ (suc g)} → Tm Γ (▸ fix a) → Tm Γ (▸ a)
omega x = {!(▹ (abs (unfold (var zero)))) ∗ x!} ∗ (▹ x)
