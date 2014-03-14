{-# OPTIONS --copatterns --sized-types #-}

-- Type interpretation and soundness of typing.

module Soundness where

open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import SN
open import SN.AntiSubst
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
⟦ Γ ⟧C n σ = ∀ {a} (x : Var Γ a) → σ x ∈ ⟦ a ⟧ n

-- Soundness

sound : ∀ {n a Γ} (t : Tm Γ a) {Δ} {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C n σ) → subst σ t ∈ ⟦ a ⟧ n
sound (var x) θ = θ x
sound (abs t) θ ρ x = {!!}
sound (app t u ) θ = {!sound t ? ? ?!}
sound {n = n} {a = a ×̂ b} (pair t₁ t₂) θ =  semPair (⟦ a ⟧ n) (⟦ b ⟧ n) (sound t₁ θ) (sound t₂ θ)
sound (fst t) θ = {!!}
sound (snd t) θ = {!!}
sound (▹ t) θ = {!!}
sound (t ∗ t₁) θ = {!!}
sound (cast eq t) θ = {!!}
