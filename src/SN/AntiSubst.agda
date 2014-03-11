{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --show-implicit #-}
{-# OPTIONS --no-termination-check #-} -- too slow

module SN.AntiSubst where

open import Relation.Unary using (_∈_; _⊆_)

open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import SN

-- Converse direction: One can cancel a substitution from an SN term.

mutual

  -- To formulate this, we need heterogeneous SNholes, going from Γ to Δ

  -- unSubstSNh : ∀{n a b m vt Γ Δ} (σ : RenSub {m} vt Γ Δ) {t : Tm Γ b} {E : ECxt Γ a b} {t' : Tm Γ a} →
  --   SNhole n (subst σ t) (λ t' → subst σ (E t')) t' → SNhole n t E t'
  -- unSubstSNh = TODO

  unSubstSNe : ∀{n a m vt Γ Δ} {σ : RenSub {m} vt Γ Δ} {t : Tm Γ a} →
    SNe n (subst σ t) → SNe n t
  unSubstSNe {t = var x}     _                = var x
  unSubstSNe {t = abs _}     (elim 𝒕 ())
  unSubstSNe {t = app _ _}   (elim 𝒕 (appl 𝒖)) = elim (unSubstSNe 𝒕) (appl (unSubstSN 𝒖))
  unSubstSNe {t = pair _ _}  (elim 𝒕 ())
  unSubstSNe {t = fst _}     (elim 𝒕 fst)      = elim (unSubstSNe 𝒕) fst
  unSubstSNe {t = snd _}     (elim 𝒕 snd)      = elim (unSubstSNe 𝒕) snd
  unSubstSNe {t = ▹ _}       (elim 𝒕 ())
  unSubstSNe {t = t ∗ u}     (elim 𝒕 𝑬𝒕)       = {!𝑬𝒕!}
  unSubstSNe {t = cast eq t} (elim 𝒕 ())

  unSubstSN : ∀{n a m vt Γ Δ} {σ : RenSub {m} vt Γ Δ} {t : Tm Γ a} →
    SN n (subst σ t) → SN n t
  unSubstSN {t = var x} _                       = ne (var x)
  unSubstSN {t = abs _} (ne (elim _ ()))
  unSubstSN {t = abs _} (abs 𝒕)                 = abs (unSubstSN 𝒕)
  unSubstSN {t = abs _} (exp (cong () _ _) _)
  unSubstSN {t = app _ _} (ne 𝒏)                = ne (unSubstSNe 𝒏)
  unSubstSN {t = app (var x) t₁} (exp t⇒ 𝒕)     = {!t⇒!}
  unSubstSN {t = app (abs t) t₁} (exp t⇒ 𝒕)     = {!!}
  unSubstSN {t = app (app t t₁) t₂} (exp t⇒ 𝒕)  = {!!}
  unSubstSN {t = app (fst t) t₁} (exp t⇒ 𝒕)     = {!!}
  unSubstSN {t = app (snd t) t₁} (exp t⇒ 𝒕)     = {!!}
  unSubstSN {t = app (cast eq t) t₁} (exp t⇒ 𝒕) = {!!}
  unSubstSN {t = pair _ _} (ne (elim 𝒏 ()))
  unSubstSN {t = pair _ _} (pair 𝒕₁ 𝒕₂)          = pair (unSubstSN 𝒕₁) (unSubstSN 𝒕₂)
  unSubstSN {t = pair t₁ t₂} (exp t⇒ 𝒕)         = {!!}
  unSubstSN {t = fst _} (ne 𝒏)                  = ne (unSubstSNe 𝒏)
  unSubstSN {t = fst t} (exp t⇒ 𝒕)              = {!!}
  unSubstSN {t = snd _} (ne 𝒏)                  = ne (unSubstSNe 𝒏)
  unSubstSN {t = snd t} (exp t⇒ 𝒕)              = {!!}
  unSubstSN {t = ▹ _} (ne (elim 𝒏 ()))
  unSubstSN {t = ▹ _} ▹0                        = ▹0
  unSubstSN {t = ▹ _} (▹ 𝒕)                     = ▹ (unSubstSN 𝒕)
  unSubstSN {t = ▹ t} (exp t⇒ 𝒕)                = {!!}
  unSubstSN {t = _ ∗ _} (ne 𝒏) = ne (unSubstSNe 𝒏)
  unSubstSN {t = t ∗ t₁} (exp t⇒ 𝒕) = {!!}
  unSubstSN {t = cast eq t} 𝒕                   = {!!}

  unSubst⇒ : ∀{n a m vt Γ Δ} {σ : RenSub {m} vt Γ Δ} {t : Tm Γ a} {t' : Tm Δ a} →
    subst σ t ⟨ n ⟩⇒ t' → SN n t' → SN n t
  unSubst⇒ {t = var x} _ _ = ne (var x)
  unSubst⇒ {t = abs _} (cong () _ _) _
  unSubst⇒ {t = app t t₁} x z = {!z!}
  unSubst⇒ {t = pair _ _} (cong () _ _) _
  unSubst⇒ {t = fst (var x)} _ _ = ne (elim (var x) fst)
{-
  unSubst⇒ {vt = `Var} {t = fst (var x)} _ _ = ne (elim (var x) fst)
  unSubst⇒ {vt = `Tm } {σ = σ} {t = fst (var x)} y z with σ x
  unSubst⇒ {n} {a} {._} {`Tm} {Γ} {Δ} {σ} {fst (var x)} y z | var x₁ = ne (elim (var x) fst)
  unSubst⇒ {n} {a} {._} {`Tm} {Γ} {Δ} {σ} {fst (var x)} y z | app u u₁ = ne (elim (var x) fst)
  unSubst⇒ {n} {a} {._} {`Tm} {Γ} {Δ} {σ} {fst (var x)} y z | pair u u₁ = ne (elim (var x) fst)
  unSubst⇒ {n} {a} {._} {`Tm} {Γ} {Δ} {σ} {fst (var x)} y z | fst u = ne (elim (var x) fst)
  unSubst⇒ {n} {a} {._} {`Tm} {Γ} {Δ} {σ} {fst (var x)} y z | snd u = ne (elim (var x) fst)
  unSubst⇒ {n} {a} {._} {`Tm} {Γ} {Δ} {σ} {fst (var x)} y z | cast eq u = ne (elim (var x) fst)
-}
  unSubst⇒ {t = fst (app t t₁)} (cong fst fst x) (ne (elim 𝒏 fst)) = {!!}
  unSubst⇒ {t = fst (app t t₁)} (cong fst fst x) (exp t⇒ z) = {!unSubst⇒ t⇒!}
  unSubst⇒ {t = fst (pair t t₁)} (βfst 𝒖) z = exp (βfst (unSubstSN 𝒖)) (unSubstSN z)
  unSubst⇒ {t = fst (pair _ _)} (cong fst fst (cong () _ _)) _
  unSubst⇒ {t = fst (fst t)} (cong fst fst x) z = {!!}
  unSubst⇒ {t = fst (snd t)} (cong fst fst x) z = {!!}
  unSubst⇒ {t = fst (cast eq t)} x z = {!!}
  unSubst⇒ {t = snd t} x z = {!!}
  unSubst⇒ {t = ▹ _} (cong () _ _) _
  unSubst⇒ {t = t ∗ t₁} x z = {!!}
  unSubst⇒ {t = cast eq t} x z = {!!}


-- Extensionality of SN for function types:
-- If t x ∈ SN then t ∈ SN.

absVarSNe : ∀{Γ a b n}{t : Tm (a ∷ Γ) (a →̂ b)} → app t (var zero) ∈ SNe n → t ∈ SNe n
absVarSNe (elim 𝒏 (appl 𝒖)) = 𝒏

absVarSN : ∀{Γ a b n}{t : Tm (a ∷ Γ) (a →̂ b)} → app t (var zero) ∈ SN n → t ∈ SN n
absVarSN (ne 𝒖)                                                   = ne (absVarSNe 𝒖)
absVarSN (exp (β 𝒖) 𝒕′)                                           = abs (unSubstSN 𝒕′)
absVarSN (exp (cong (appl .(var zero)) (appl .(var zero)) t⇒) 𝒕′) = exp t⇒ (absVarSN 𝒕′)

-- absVarSNe : ∀{Γ a b n}{t : Tm Γ (a →̂ b)} → app (rename suc t) (var zero) ∈ SNe n → t ∈ SNe n
-- absVarSNe (elim 𝒏 (appl 𝒖)) = unSubstSNe 𝒏

-- absVarSN : ∀{Γ a b n}{t : Tm Γ (a →̂ b)} → app (rename suc t) (var zero) ∈ SN n → t ∈ SN n
-- absVarSN (ne 𝒖) = ne (absVarSNe 𝒖)
-- absVarSN (exp t⇒ 𝒕′) = {! t⇒!} -- exp {!!} (absVarSN {!𝒕′!})
-- -- absVarSN (ne (var ())) = {!𝒏!}
-- -- absVarSN (ne (elim {E = .(λ u → app u (var _))} 𝒏 (appl y))) = {!𝒏!}
-- -- absVarSN (exp t⇒ x₁) = {!!}
