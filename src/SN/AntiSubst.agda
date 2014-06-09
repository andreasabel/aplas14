{-# OPTIONS --copatterns --sized-types #-}

module SN.AntiSubst where

open import Relation.Unary using (_∈_; _⊆_)

open import Library
open import Data.Sum
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import SN





mutual

  -- Subterm properties of SN (continued).

  -- If app t u ∈ SN then t ∈ SN.
  applSN : ∀{i n a b Γ}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} → SN {i} n (app t u) → SN {i} n t
  applSN (ne (elim 𝒏 (appl 𝒖)))               = ne 𝒏
  applSN (exp (β 𝒖) 𝒕)                        = abs (unSubstSN (prop→IndS _ ≡.refl) 𝒕)
  applSN (exp (cong (appl u) (appl .u) t⇒) 𝒕) = exp t⇒ (applSN 𝒕)


  unSubstSNe : ∀{i n a m vt Γ Δ} {σ : RenSub {m} vt Γ Δ} {t : Tm Γ a}{tσ} → IndSubst σ t tσ
               → SNe {i} n tσ → SNe {i} n t
  unSubstSNe (var x x₁)     (var y)           = var x
  unSubstSNe (app is is₁)   (elim 𝒏 (appl 𝒖)) = elim (unSubstSNe is 𝒏) (appl (unSubstSN is₁ 𝒖))
  unSubstSNe (fst is)       (elim {j₁ = j₁} {j₂ = j₂} 𝒏 fst)      = elim {j₁ = j₁} {j₂ = j₂} (unSubstSNe is 𝒏) fst
  unSubstSNe (snd is)       (elim {j₁ = j₁} {j₂ = j₂} 𝒏 snd)      = elim {j₁ = j₁} {j₂ = j₂} (unSubstSNe is 𝒏) snd
  unSubstSNe (is ∗ is₁)     (elim {j₁ = j₁} {j₂ = j₂} 𝒏 (𝒖 ∗l))   = elim {j₁ = j₁} {j₂ = j₂} (unSubstSNe is 𝒏) (unSubstSN is₁ 𝒖 ∗l)
  unSubstSNe ((▹ is) ∗ is₁) (elim {j₁ = j₁} {j₂ = j₂} 𝒏 (∗r 𝒕))   = elim {j₁ = j₁} {j₂ = j₂} (unSubstSNe is₁ 𝒏) (∗r unSubstSN (▹ is) 𝒕)
  unSubstSNe (var x x₁)     (elim 𝒏 _)           = var x
  unSubstSNe ((var x x₁) ∗ is₁) (elim {j₁ = j₁} {j₂ = j₂} 𝒏 (∗r 𝒕)) = elim {j₁ = j₁} {j₂ = j₂} {! (var x) !} {! (ne (unSubstSNe is₁ 𝒏) ∗l) !}

  unSubstSN : ∀{i n a m vt Γ Δ} {σ : RenSub {m} vt Γ Δ} {t : Tm Γ a}{tσ} → IndSubst σ t tσ
               → SN {i} n tσ → SN {i} n t
  unSubstSN (var x x₁)      _      = {! ne (var x) !}
  -- constructor cases:
  unSubstSN (abs t)      (abs 𝒕)      = abs (unSubstSN t 𝒕)
  unSubstSN (pair t₁ t₂) (pair 𝒕₁ 𝒕₂) = pair (unSubstSN t₁ 𝒕₁) (unSubstSN t₂ 𝒕₂)
  unSubstSN (▹ _)        ▹0           = ▹0
  unSubstSN (▹ t)        (▹ 𝒕)        = ▹ (unSubstSN t 𝒕)
  -- neutral cases:
  unSubstSN n            (ne 𝒏)       = ne (unSubstSNe n 𝒏)
  -- redex cases:
  unSubstSN is           (exp t⇒ 𝒕)   = [ (λ x → let p = proj₂ x in {! exp (proj₂ p) (unSubstSN (proj₁ p) 𝒕) !}) , {! ne !} ]′ (unSubst⇒0 is t⇒ 𝒕)
  -- If E t ∈ SN then t ∈ SN.

  unEholeSN : ∀ {i n Γ a b} → {t : Tm Γ a} {E : ECxt Γ b a} {t' : Tm Γ b} → Ehole t E t' → SN {i} n t → SN {i} n t'
  unEholeSN (appl u) 𝒕 = applSN 𝒕
{-
  unEholeSN (appl u) (ne (elim 𝒏 (appl 𝒖)))               = ne 𝒏
  unEholeSN (appl u) (exp (β 𝒖) 𝒕)                        = abs (unSubstSN (prop→IndS _ ≡.refl) 𝒕)
  unEholeSN (appl u) (exp (cong (appl .u) (appl .u) t⇒) 𝒕) = exp t⇒ (applSN 𝒕)
-}
  unEholeSN fst 𝒕 = fromFstSN 𝒕
  unEholeSN snd 𝒕 = fromSndSN 𝒕
  unEholeSN (u ∗l) (ne (elim 𝒏 (𝒖 ∗l))) = ne 𝒏
  unEholeSN (u ∗l) (ne (elim 𝒏 (∗r 𝒕))) = delaySN (λ x → x) 𝒕
  unEholeSN (._ ∗l) (exp β▹ 𝒕) = delaySN applSN 𝒕
  unEholeSN (u ∗l) (exp (cong (.u ∗l) (.u ∗l) t⇒) 𝒕) = exp t⇒ (unEholeSN (_ ∗l) 𝒕)
  unEholeSN (u ∗l) (exp (cong (∗r t) (∗r .t) t⇒) 𝒕) = unEholeSN (_ ∗l) 𝒕
  unEholeSN (∗r t) tx  = ∗rSN tx

  unSubst⇒0 : ∀{i j n m vt a Γ Δ} {σ : RenSub {m} vt Γ Δ}  {t : Tm Γ a} {t' : Tm Δ a}{tρ} → IndSubst σ t tρ
              → i size tρ ⟨ n ⟩⇒ t' → SN {j} n t' → (Σ _ \ s → IndSubst σ s t' × i size t ⟨ n ⟩⇒ s) ⊎ SNe {j} n t
  unSubst⇒0 {σ = ρ} (app {u = u} (abs {t = t} is) is₁) (β 𝒖) 𝒕 = inj₁ (_ , (prop→IndS ρ
                                                                               (≡.trans (≡.sym (sgs-lifts-term {σ = ρ} {u = u} {t = t}))
                                                                                (≡.cong₂ (λ t₁ u₁ → subst (sgs u₁) t₁) (IndS→prop _ is)
                                                                                 (IndS→prop _ is₁)))
                                                                         , β (unSubstSN is₁ 𝒖)))
  unSubst⇒0 ((▹ is) ∗ (▹ is₁))  β▹        𝒕 = inj₁ (▹ app _ _ , (▹ app is is₁) , β▹)
  unSubst⇒0 (fst (pair is is₁)) (βfst 𝒖)  𝒕 = inj₁ (_ , is , βfst (unSubstSN is₁ 𝒖))
  unSubst⇒0 (snd (pair is is₁)) (βsnd 𝒕') 𝒕 = inj₁ (_ , is₁ , βsnd (unSubstSN is 𝒕'))
  unSubst⇒0 (app is is₁)        (cong (appl u') (appl .u') tρ→t') 𝒕
--    = Data.Sum.map (λ x → let s , is , t→s = x in
    = Data.Sum.map (λ x → let s = proj₁ x; is = proj₁ (proj₂ x); t→s = proj₂ (proj₂ x) in
      (app s _) , ((app is is₁) , (cong (appl _) (appl _) t→s))) (λ x → elim x (appl (unSubstSN is₁ (apprSN 𝒕)))) (unSubst⇒0 is tρ→t' (unEholeSN (appl u') 𝒕))
  unSubst⇒0 (fst is)            (cong fst fst tρ→t') 𝒕
    = Data.Sum.map (λ x → let s = proj₁ x; is = proj₁ (proj₂ x); t→s = proj₂ (proj₂ x) in
      (fst s) , ((fst is) , (cong fst fst t→s))) (λ x → elim x fst) (unSubst⇒0 is tρ→t' (unEholeSN fst 𝒕))
  unSubst⇒0 (snd is)            (cong snd snd tρ→t') 𝒕
    = Data.Sum.map (λ x → let s = proj₁ x; is = proj₁ (proj₂ x); t→s = proj₂ (proj₂ x) in
      (snd s) , ((snd is) , (cong snd snd t→s))) (λ x → elim x snd) (unSubst⇒0 is tρ→t' (unEholeSN snd 𝒕))
  unSubst⇒0 (is ∗ is₁)          (cong (u ∗l) (.u ∗l) tρ→t')  𝒕
    = Data.Sum.map (λ x → let s = proj₁ x; is = proj₁ (proj₂ x); t→s = proj₂ (proj₂ x) in
      (s ∗ _) , (is ∗ is₁) , (cong (_ ∗l) (_ ∗l) t→s)) (λ x → elim x (unSubstSN is₁ (∗rSN 𝒕) ∗l)) (unSubst⇒0 is tρ→t' (unEholeSN (u ∗l) 𝒕))
  unSubst⇒0 ((▹ is₀) ∗ is₁)     (cong (∗r t₂) (∗r .t₂) tρ→t') 𝒕
    = Data.Sum.map ((λ x → let s = proj₁ x; is = proj₁ (proj₂ x); t→s = proj₂ (proj₂ x) in
      _ ∗ s , (▹ is₀) ∗ is , cong (∗r _) (∗r _) t→s)) (λ x → elim x (∗r (delaySN (unSubstSN is₀) (unEholeSN (_ ∗l) 𝒕))))
              (unSubst⇒0 is₁ tρ→t' (unEholeSN (∗r t₂) 𝒕))
  unSubst⇒0 (var x x₁)          t⇒                            𝒕 = inj₂ ((var x))
  unSubst⇒0 (app (var x x₁) u₁) (β 𝒖)                         𝒕 = inj₂ ((elim (var x) (appl (unSubstSN u₁ 𝒖))))
  unSubst⇒0 ((▹ t₂) ∗ var x x₁) β▹                            𝒕 = inj₂ ((elim (var x) (∗r unSubstSN (▹ t₂) (delaySN applSN 𝒕))))
  unSubst⇒0 (var x x₁ ∗ u₂)     β▹                            𝒕 = inj₂ ((elim (var x) (unSubstSN u₂ (delaySN apprSN 𝒕) ∗l)))
  unSubst⇒0 (var x x₁ ∗ is₁)    (cong (∗r t₂) (∗r .t₂) tρ→t') 𝒕 = inj₂ (elim (var x) {! (unSubstSN is₁ (exp tρ→t' (∗rSN 𝒕)) ∗l) !})
  unSubst⇒0 (fst (var x is₁))   (βfst 𝒖)                      𝒕 = inj₂ (elim (var x) fst)
  unSubst⇒0 (snd (var x is₁))   (βsnd 𝒕')                     𝒕 = inj₂ (elim (var x) snd)


{-
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
-}
