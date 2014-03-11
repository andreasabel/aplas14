{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --show-implicit #-}
{-# OPTIONS --no-termination-check #-} -- too slow

module SN.AntiRename where

open import Relation.Unary using (_∈_; _⊆_)

open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import SN


mutual

  -- To formulate this, we need heterogeneous SNholes, going from Γ to Δ

  -- unRenameSNh : ∀{n a b Γ Δ} (ρ : Δ ≤ Γ) {t : Tm Γ b} {E : ECxt Γ a b} {t' : Tm Γ a} →
  --   SNhole n (subst ρ t) (λ t' → subst ρ (E t')) t' → SNhole n t E t'
  -- unRenameSNh = TODO

  unRenameSNe : ∀{n a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a} →
    SNe n (subst ρ t) → SNe n t
  unRenameSNe {t = var x}     _                = var x
  unRenameSNe {t = abs _}     (elim 𝒕 ())
  unRenameSNe {t = app _ _}   (elim 𝒕 (appl 𝒖)) = elim (unRenameSNe 𝒕) (appl (unRenameSN 𝒖))
  unRenameSNe {t = pair _ _}  (elim 𝒕 ())
  unRenameSNe {t = fst _}     (elim 𝒕 fst)      = elim (unRenameSNe 𝒕) fst
  unRenameSNe {t = snd _}     (elim 𝒕 snd)      = elim (unRenameSNe 𝒕) snd
  unRenameSNe {t = ▹ _}       (elim 𝒕 ())
  unRenameSNe {t = t ∗ u}     (elim 𝒕 𝑬𝒕)       = {!𝑬𝒕!}
  unRenameSNe {t = cast eq t} (elim 𝒕 ())

  unRenameSN : ∀{n a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a} →
    SN n (subst ρ t) → SN n t
  -- variable case:
  unRenameSN {t = var x   } _            = ne (var x)
  -- constructor cases:
  unRenameSN {t = abs _   } (abs 𝒕)      = abs (unRenameSN 𝒕)
  unRenameSN {t = pair _ _} (pair 𝒕₁ 𝒕₂) = pair (unRenameSN 𝒕₁) (unRenameSN 𝒕₂)
  unRenameSN {t = ▹ _     } ▹0           = ▹0
  unRenameSN {t = ▹ _     } (▹ 𝒕)        = ▹ (unRenameSN 𝒕)
  -- neutral cases:
  unRenameSN                (ne 𝒏)       = ne (unRenameSNe 𝒏)
  -- redex cases:
  unRenameSN                (exp t⇒ 𝒕)   = unRename⇒ t⇒ 𝒕

  -- NEEDS generalization, maybe t[ρ] ⇒ t' and E[t'] ∈ SN imply E[t] ∈ SN
  unRename⇒ : ∀{n a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a} {t' : Tm Δ a} →
    subst ρ t ⟨ n ⟩⇒ t' → SN n t' → SN n t
  unRename⇒ {t = var x} _ _ = ne (var x)
  unRename⇒ {t = abs _} (cong () _ _) _
  unRename⇒ {t = app (var x) t₁} (cong (appl ._) (appl ._) y) 𝒕 = ne (elim (var x) (appl (unRenameSN (apprSN 𝒕))))
  unRename⇒ {t = app (abs t) t₁} (β 𝒖) 𝒕 = exp (β (unRenameSN 𝒖)) (unRenameSN {!𝒕!})
  unRename⇒ {t = app (abs t) t₁}     (cong  (appl ._) (appl ._) (cong () _ _)) 𝒕
  unRename⇒ {t = app (app t t₁) t₂}  (cong (appl ._) (appl ._) t⇒) 𝒕 = {!!}
  unRename⇒ {t = app (fst t) t₁}     (cong (appl ._) (appl ._) t⇒) 𝒕 = {!!}
  unRename⇒ {t = app (snd t) t₁}     (cong (appl ._) (appl ._) t⇒) 𝒕 = {!!}
  unRename⇒ {t = app (cast eq t) t₁} (cong (appl ._) (appl ._) t⇒) 𝒕 = {!!}
  unRename⇒ {t = pair _ _} (cong () _ _) _
  unRename⇒ {t = fst (var x)} _ _ = ne (elim (var x) fst)
  unRename⇒ {t = fst (pair _ _)} (βfst 𝒖) 𝒕 = exp (βfst (unRenameSN 𝒖)) (unRenameSN 𝒕)
  unRename⇒ {t = fst (pair _ _)} (cong fst fst (cong () _ _)) _
  unRename⇒ {t = fst (app _ _ )} (cong fst fst t⇒) 𝒕 = fstSN (unRename⇒ t⇒ (fromFstSN 𝒕))
  unRename⇒ {t = fst (fst _   )} (cong fst fst t⇒) 𝒕 = fstSN (unRename⇒ t⇒ (fromFstSN 𝒕))
  unRename⇒ {t = fst (snd _   )} (cong fst fst t⇒) 𝒕 = fstSN (unRename⇒ t⇒ (fromFstSN 𝒕))
  unRename⇒ {t = fst (cast _ _)} (cong fst fst t⇒) 𝒕 = fstSN (unRename⇒ t⇒ (fromFstSN 𝒕))
  unRename⇒ {t = snd (var x)} _ _ = ne (elim (var x) snd)
  unRename⇒ {t = snd (pair _ _)} (βsnd 𝒖) 𝒕 = exp (βsnd (unRenameSN 𝒖)) (unRenameSN 𝒕)
  unRename⇒ {t = snd (pair _ _)} (cong snd snd (cong () _ _)) _
  unRename⇒ {t = snd (app _ _ )} (cong snd snd t⇒) 𝒕 = sndSN (unRename⇒ t⇒ (fromSndSN 𝒕))
  unRename⇒ {t = snd (fst _   )} (cong snd snd t⇒) 𝒕 = sndSN (unRename⇒ t⇒ (fromSndSN 𝒕))
  unRename⇒ {t = snd (snd _   )} (cong snd snd t⇒) 𝒕 = sndSN (unRename⇒ t⇒ (fromSndSN 𝒕))
  unRename⇒ {t = snd (cast _ _)} (cong snd snd t⇒) 𝒕 = sndSN (unRename⇒ t⇒ (fromSndSN 𝒕))
  unRename⇒ {t = ▹ _} (cong () _ _) _
  unRename⇒ {t = t ∗ t₁} x 𝒕 = {!!}
  unRename⇒ {t = cast eq t} x 𝒕 = {!!}

-- Extensionality of SN for function types:
-- If t x ∈ SN then t ∈ SN.

absVarSNe : ∀{Γ a b n}{t : Tm (a ∷ Γ) (a →̂ b)} → app t (var zero) ∈ SNe n → t ∈ SNe n
absVarSNe (elim 𝒏 (appl 𝒖)) = 𝒏

absVarSN : ∀{Γ a b n}{t : Tm (a ∷ Γ) (a →̂ b)} → app t (var zero) ∈ SN n → t ∈ SN n
absVarSN (ne 𝒖)                                                   = ne (absVarSNe 𝒖)
absVarSN (exp (β 𝒖) 𝒕′)                                           = abs {!unRenameSN 𝒕′!}
absVarSN (exp (cong (appl .(var zero)) (appl .(var zero)) t⇒) 𝒕′) = exp t⇒ (absVarSN 𝒕′)

-- absVarSNe : ∀{Γ a b n}{t : Tm Γ (a →̂ b)} → app (rename suc t) (var zero) ∈ SNe n → t ∈ SNe n
-- absVarSNe (elim 𝒏 (appl 𝒖)) = unRenameSNe 𝒏

-- absVarSN : ∀{Γ a b n}{t : Tm Γ (a →̂ b)} → app (rename suc t) (var zero) ∈ SN n → t ∈ SN n
-- absVarSN (ne 𝒖) = ne (absVarSNe 𝒖)
-- absVarSN (exp t⇒ 𝒕′) = {! t⇒!} -- exp {!!} (absVarSN {!𝒕′!})
-- -- absVarSN (ne (var ())) = {!𝒏!}
-- -- absVarSN (ne (elim {E = .(λ u → app u (var _))} 𝒏 (appl y))) = {!𝒏!}
-- -- absVarSN (exp t⇒ x₁) = {!!}
