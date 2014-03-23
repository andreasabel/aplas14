module SN.Congruence where

open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import Reduction
open import SN

mutual
  cong-SNe : ∀ {a a' n Γ Γ'} {t : Tm Γ a} {t′ : Tm Γ' a'} →
                   t ≅T t′ → SNe n t → SNe n t′
  cong-SNe (var [x]) (var x)             = var _
  cong-SNe (app t₁ t₂) (elim 𝒏 (appl 𝒖)) = elim (cong-SNe t₁ 𝒏) (appl (cong-SN t₂ 𝒖))
  cong-SNe (fst t₁) (elim 𝒏 fst)         = elim (cong-SNe t₁ 𝒏) fst
  cong-SNe (snd t₁) (elim 𝒏 snd)         = elim (cong-SNe t₁ 𝒏) snd
  cong-SNe (t₁ ∗ t₂) (elim 𝒏 (𝒖 ∗l))     = elim (cong-SNe t₁ 𝒏) (cong-SN t₂ 𝒖 ∗l)
  cong-SNe (▹ t₂ ∗ t₃) (elim 𝒏 (∗r 𝒕))   = elim (cong-SNe t₃ 𝒏) (∗r cong-SN (▹ t₂) 𝒕) 

  cong-SN : ∀ {a a' n Γ Γ'} {t : Tm Γ a} {t′ : Tm Γ' a'} →
                   t ≅T t′ → SN n t → SN n t′
  cong-SN t₁ (ne 𝒏)                = ne (cong-SNe t₁ 𝒏)
  cong-SN (abs t₁) (abs 𝒕)         = abs (cong-SN t₁ 𝒕)
  cong-SN (pair t₁ t₂) (pair 𝒕 𝒕₁) = pair (cong-SN t₁ 𝒕) (cong-SN t₂ 𝒕₁)
  cong-SN (▹ t₁) ▹0                = ▹0
  cong-SN (▹ t₁) (▹ 𝒕)             = ▹ (cong-SN t₁ 𝒕)
  cong-SN t₁ (exp t⇒ 𝒕)            = exp (proj₁ (proj₂ (cong⇒ t₁ t⇒ 𝒕))) (cong-SN (proj₂ (proj₂ (cong⇒ t₁ t⇒ 𝒕))) 𝒕)


  cong⇒ : ∀ {a a' n Γ Γ'} {t : Tm Γ a} {t′ : Tm Γ' a'} {t′₁ : Tm Γ a}
          (t₁ : t ≅T t′) (t⇒ : t ⟨ n ⟩⇒ t′₁) (𝒕 : SN n t′₁) →
          Σ _ \ tt → t′ ⟨ n ⟩⇒ tt × t′₁ ≅T tt
  cong⇒ (app (abs t₁) t₂) (β 𝒖) 𝒕 = {!!}
  cong⇒ t₁ β▹ 𝒕 = {!!}
  cong⇒ (fst (pair t t₁)) (βfst 𝒖) 𝒕 = _ , βfst (cong-SN t₁ 𝒖) , t
  cong⇒ (snd (pair t₁ t₂)) (βsnd 𝒕) 𝒕₁ = _ , βsnd (cong-SN {!!} {!!}) , {!!}
  cong⇒ t₁ (cong 𝑬𝒕 𝑬𝒕' t⇒) 𝒕 = {!!}