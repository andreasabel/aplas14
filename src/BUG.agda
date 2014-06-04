{-# OPTIONS --copatterns --sized-types #-}

-- Type interpretation and soundness of typing.

module BUG where

open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import SN
--open import SN.AntiSubst
open import SN.AntiRename
open import SAT2

-- Type interpretation

⟦_⟧_ : (a : Ty) (n : ℕ) → SAT a n
⟦ a ×̂ b ⟧ n     = ⟦ a ⟧ n ⟦×⟧ ⟦ b ⟧ n
⟦ a →̂ b ⟧ n     = ⟦ a ⟧ n ⟦→⟧ ⟦ b ⟧ n
⟦ ▸̂ a∞  ⟧ zero  = ⟦▸⟧ _
⟦ ▸̂ a∞  ⟧ suc n = ⟦▸⟧ ⟦ force a∞ ⟧ n

-- Context interpretation (semantic substitutions)

⟦_⟧C : ∀ Γ n {Δ} (σ : Subst Γ Δ) → Set
⟦ Γ ⟧C n σ = ∀ {a} {x : Var Γ a} → σ x ∈ ⟦ a ⟧ n

-- Soundness

sound : ∀ {n a Γ} (t : Tm Γ a) {Δ} {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C n σ) → subst σ t ∈ ⟦ a ⟧ n
sound (var x) {σ = σ} θ = θ x {{!!}} {{!!}}
sound (abs t) θ ρ x = {!!}
sound (app t u ) θ = {!!}
sound (pair t₁ t₂) θ = {!!}
sound (fst t) θ = {!!}
sound (snd t) θ = {!!}
sound (▹ t) θ = {!!}
sound (t ∗ t₁) θ = {!!}
sound (cast eq t) θ = {!!}
