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


mutual

  -- Subterm properties of SN (continued).

  -- If app t u ∈ SN then t ∈ SN.

  applSN : ∀{n a b Γ}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} → SN n (app t u) → SN n t
  applSN (ne (elim 𝒏 (appl 𝒖)))               = ne 𝒏
  applSN (exp (β 𝒖) 𝒕)                        = abs (unSubstSN 𝒕)
  applSN (exp (cong (appl u) (appl .u) t⇒) 𝒕) = exp t⇒ (applSN 𝒕)

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
  -- variable case:
  unSubstSN {t = var x}    _            = ne (var x)
  -- constructor cases:
  unSubstSN {t = abs _   } (abs 𝒕)      = abs (unSubstSN 𝒕)
  unSubstSN {t = pair _ _} (pair 𝒕₁ 𝒕₂) = pair (unSubstSN 𝒕₁) (unSubstSN 𝒕₂)
  unSubstSN {t = ▹ _     } ▹0           = ▹0
  unSubstSN {t = ▹ _     } (▹ 𝒕)        = ▹ (unSubstSN 𝒕)
  -- neutral cases:
  unSubstSN                (ne 𝒏)       = ne (unSubstSNe 𝒏)
  -- redex cases:
  unSubstSN                (exp t⇒ 𝒕)   = unSubst⇒ t⇒ 𝒕

{- LONG VERSION:
  -- neutral cases:
  unSubstSN {t = app _ _} (ne 𝒏)        = ne (unSubstSNe 𝒏)
  unSubstSN {t = fst _} (ne 𝒏)          = ne (unSubstSNe 𝒏)
  unSubstSN {t = snd _} (ne 𝒏)          = ne (unSubstSNe 𝒏)
  unSubstSN {t = _ ∗ _} (ne 𝒏)          = ne (unSubstSNe 𝒏)
  unSubstSN {t = cast eq t} (ne 𝒏)      = ne (unSubstSNe 𝒏)
  -- redex cases:
  unSubstSN {t = app _ _ } (exp t⇒ 𝒕)   = unSubst⇒ t⇒ 𝒕
  unSubstSN {t = fst _   } (exp t⇒ 𝒕)   = unSubst⇒ t⇒ 𝒕
  unSubstSN {t = snd _   } (exp t⇒ 𝒕)   = unSubst⇒ t⇒ 𝒕
  unSubstSN {t = _ ∗ _   } (exp t⇒ 𝒕)   = unSubst⇒ t⇒ 𝒕
  unSubstSN {t = cast _ _} (exp t⇒ 𝒕)   = unSubst⇒ t⇒ 𝒕
  -- impossible: constructor becomes neutral
  unSubstSN {t = abs _   } (ne (elim _ ()))
  unSubstSN {t = pair _ _} (ne (elim 𝒏 ()))
  unSubstSN {t = ▹ _     } (ne (elim 𝒏 ()))
  -- impossible: constructor becomes redex
  unSubstSN {t = abs _   } (exp (cong () _ _) _)
  unSubstSN {t = pair _ _} (exp (cong () _ _) _)
  unSubstSN {t = ▹ _     } (exp (cong () _ _) _)
-}

  unSubst⇒ : ∀{n a m vt Γ Δ} {σ : RenSub {m} vt Γ Δ} {t : Tm Γ a} {t' : Tm Δ a} →
    subst σ t ⟨ n ⟩⇒ t' → SN n t' → SN n t
  unSubst⇒ {t = var x} _ _ = ne (var x)
  unSubst⇒ {t = abs _} (cong () _ _) _
  unSubst⇒ {t = app (var x) t₁} x₁ 𝒕 = ne (elim (var x) (appl {!!}))
  unSubst⇒ {t = app (abs t) t₁} (β 𝒖) 𝒕 = exp (β (unSubstSN 𝒖)) (unSubstSN {!𝒕!})
  unSubst⇒ {t = app (abs t) t₁}     (cong  (appl ._) (appl ._) (cong () _ _)) 𝒕
  unSubst⇒ {t = app (app t t₁) t₂}  (cong (appl ._) (appl ._) t⇒) 𝒕 = {!!}
  unSubst⇒ {t = app (fst t) t₁}     (cong (appl ._) (appl ._) t⇒) 𝒕 = {!!}
  unSubst⇒ {t = app (snd t) t₁}     (cong (appl ._) (appl ._) t⇒) 𝒕 = {!!}
  unSubst⇒ {t = app (cast eq t) t₁} (cong (appl ._) (appl ._) t⇒) 𝒕 = {!!}
  unSubst⇒ {t = pair _ _} (cong () _ _) _
  unSubst⇒ {t = fst (var x)} _ _ = ne (elim (var x) fst)
  unSubst⇒ {t = fst (pair _ _)} (βfst 𝒖) 𝒕 = exp (βfst (unSubstSN 𝒖)) (unSubstSN 𝒕)
  unSubst⇒ {t = fst (pair _ _)} (cong fst fst (cong () _ _)) _
  unSubst⇒ {t = fst (app _ _ )} (cong fst fst t⇒) 𝒕 = fstSN (unSubst⇒ t⇒ (fromFstSN 𝒕))
  unSubst⇒ {t = fst (fst _   )} (cong fst fst t⇒) 𝒕 = fstSN (unSubst⇒ t⇒ (fromFstSN 𝒕))
  unSubst⇒ {t = fst (snd _   )} (cong fst fst t⇒) 𝒕 = fstSN (unSubst⇒ t⇒ (fromFstSN 𝒕))
  unSubst⇒ {t = fst (cast _ _)} (cong fst fst t⇒) 𝒕 = fstSN (unSubst⇒ t⇒ (fromFstSN 𝒕))
  unSubst⇒ {t = snd (var x)} _ _ = ne (elim (var x) snd)
  unSubst⇒ {t = snd (pair _ _)} (βsnd 𝒖) 𝒕 = exp (βsnd (unSubstSN 𝒖)) (unSubstSN 𝒕)
  unSubst⇒ {t = snd (pair _ _)} (cong snd snd (cong () _ _)) _
  unSubst⇒ {t = snd (app _ _ )} (cong snd snd t⇒) 𝒕 = sndSN (unSubst⇒ t⇒ (fromSndSN 𝒕))
  unSubst⇒ {t = snd (fst _   )} (cong snd snd t⇒) 𝒕 = sndSN (unSubst⇒ t⇒ (fromSndSN 𝒕))
  unSubst⇒ {t = snd (snd _   )} (cong snd snd t⇒) 𝒕 = sndSN (unSubst⇒ t⇒ (fromSndSN 𝒕))
  unSubst⇒ {t = snd (cast _ _)} (cong snd snd t⇒) 𝒕 = sndSN (unSubst⇒ t⇒ (fromSndSN 𝒕))
  unSubst⇒ {t = ▹ _} (cong () _ _) _
  unSubst⇒ {t = t ∗ t₁} x 𝒕 = {!!}
  unSubst⇒ {t = cast eq t} x 𝒕 = {!!}

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
