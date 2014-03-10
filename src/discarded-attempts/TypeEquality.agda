module TypeEquality where

open import Library
open import Types

{-
data _≅_ {Δ} : ∀{g g'} (a : Ty Δ g) (b : Ty Δ g') → Set where
  unfold : ∀{g} {f : TyF Δ g} → μ̂ f ≅ (f · μ̂ f)
  fold   : ∀{g} {f : TyF Δ g} → (f · μ̂ f) ≅ μ̂ f
  trans  : ∀{g g' g''}{a : Ty Δ g}{b : Ty Δ g'}{c : Ty Δ g''} →
           a ≅ b → b ≅ c → a ≅ c
  var : ∀{g} (x : TyVar Δ g)    → var x ≅ var x
  ▸̂_  : ∀{g g'}{a : Ty Δ (suc g)}{b : Ty Δ (suc g')} → a ≅ b → ▸̂ a ≅ ▸̂ b
  1̂   : ∀{g g'} → (1̂ {g = g}) ≅ (1̂ {g = g'})
  _×̂_ : ∀{g g'} {a₁ a₂ : Ty Δ g} {b₁ b₂ : Ty Δ g'} →
        a₁ ≅ b₁ → a₂ ≅ b₂ → (a₁ ×̂ a₂) ≅ (b₁ ×̂ b₂)
  _+̂_ : ∀{g g'} {a₁ a₂ : Ty Δ g} {b₁ b₂ : Ty Δ g'} →
        a₁ ≅ b₁ → a₂ ≅ b₂ → (a₁ +̂ a₂) ≅ (b₁ +̂ b₂)
  _→̂_ : ∀{g g'} {a₁ a₂ : Ty Δ g} {b₁ b₂ : Ty Δ g'} →
        a₁ ≅ b₁ → a₂ ≅ b₂ → (a₁ →̂ a₂) ≅ (b₁ →̂ b₂)
  μ̂_  : ∀{g₁ g₂}(f : TyF Δ g₁)(f' : TyF Δ g₂) →
        (∀{g₁' g₂'} (gg₁ : g₁ ≤K g₁') (gg₂ : g₂ ≤K g₂') → f gg₁ ≅ f' gg₂) →
        (μ̂ f) ≅ μ̂ f'
-}

data _≅_ : ∀{Δ Δ'}{g g'} (a : Ty Δ g) (b : Ty Δ' g') → Set where

  unfold : ∀{Δ}{g} {f : TyF Δ g} →
           μ̂ f ≅ (f · μ̂ f)

  fold   : ∀{Δ}{g} {f : TyF Δ g} →
           (f · μ̂ f) ≅ μ̂ f

  trans  : ∀{Δ Δ'}{Δ₀}{g g' g''}{a : Ty Δ g}{b : Ty Δ₀ g'}{c : Ty Δ' g''} →
           a ≅ b → b ≅ c → a ≅ c

  var    : ∀{Δ}{g} (x : TyVar Δ g) →
           var x ≅ var x

  ▸̂_     : ∀{Δ Δ'}{g g'}{a : Ty Δ (suc g)}{b : Ty Δ' (suc g')} →
           a ≅ b → ▸̂ a ≅ ▸̂ b

  1̂      : ∀{Δ Δ'}{g g'} →
           (1̂ {Δ}{g}) ≅ (1̂ {Δ'}{g'})

  _×̂_    : ∀{Δ Δ'}{g g'} {a₁ a₂ : Ty Δ g} {b₁ b₂ : Ty Δ' g'} →
           a₁ ≅ b₁ → a₂ ≅ b₂ → (a₁ ×̂ a₂) ≅ (b₁ ×̂ b₂)

  _+̂_    : ∀{Δ Δ'}{g g'} {a₁ a₂ : Ty Δ g} {b₁ b₂ : Ty Δ' g'} →
           a₁ ≅ b₁ → a₂ ≅ b₂ → (a₁ +̂ a₂) ≅ (b₁ +̂ b₂)

  _→̂_    : ∀{Δ Δ'}{g g'} {a₁ a₂ : Ty Δ g} {b₁ b₂ : Ty Δ' g'} →
           a₁ ≅ b₁ → a₂ ≅ b₂ → (a₁ →̂ a₂) ≅ (b₁ →̂ b₂)

  μ̂_     : ∀{Δ Δ'}{g₁ g₂}(f : TyF Δ g₁)(f' : TyF Δ' g₂) →
           (∀{g₁' g₂'} (gg₁ : g₁ ≤K g₁') (gg₂ : g₂ ≤K g₂') → f gg₁ ≅ f' gg₂) →
           (μ̂ f) ≅ μ̂ f'


