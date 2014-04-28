{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
--{-# OPTIONS --show-implicit #-}
module DeclSN where

open import Data.Sum
open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import TermShape
open import SN
open import NReduction
open import Reduction

data sn {Γ} (n : ℕ) {a} (t : Tm Γ a) : Set where
  acc : (∀ {t'} → t ⟨ n ⟩⇒β t' → sn n t') → sn n t

sn⇒β :  ∀ {Γ} {n : ℕ} {a} {t t' : Tm Γ a} → sn n t → t ⟨ n ⟩⇒β t' → sn n t'
sn⇒β (acc h) r = h r

varsn : ∀ {Γ} {n : ℕ} {a} (x : Var Γ a) → sn n (var x)
varsn x = acc λ { (cong () _ _) }

abssn : ∀ {Γ} {n : ℕ} {a b} {t : Tm (a ∷ Γ) b} → sn n t → sn n (abs t)
abssn (acc f) = acc (λ { {._} (cong abs abs x)  → abssn (f x) })

▹sn : ∀ {Γ} {n : ℕ} {a∞} {t : Tm Γ (force a∞)} → sn n t → sn (suc n) (▹_ {a∞ = a∞} t)
▹sn (acc f) = acc (λ { {._} (cong ▹_ ▹_ x)  → ▹sn (f x) })

Fstsn : ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ a}{u : Tm Γ b} → sn n (pair t u) → sn n t
Fstsn (acc f) = acc (\ x -> Fstsn (f (cong (pairl _) (pairl _) x)))

fstsn : ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ (a ×̂  b)} → sn n t → sn n (fst t)
fstsn t = acc (helper t) where
  helper : ∀ {Γ n a b} {t : Tm Γ (a ×̂ b)} {t' : Tm Γ a}
           → sn n t → fst t ⟨ n ⟩⇒β t' → sn n t'
  helper t       βfst               = Fstsn t
  helper (acc f) (cong fst fst t⇒β) = fstsn (f t⇒β)

pairsn : ∀ {Γ a b n t u}
           → (𝒕 : sn n t) (𝒖 : sn n u)
           → sn {Γ} n {a ×̂ b} (pair t u)
pairsn t u = acc (λ x → helper t u x) where
  helper : ∀ {Γ a b n} {t : Tm Γ a} {u : Tm Γ b}
           {t' : Tm Γ (a ×̂ b)} →
         sn n t → sn n u → pair t u ⟨ n ⟩⇒β t' → sn n t'
  helper (acc f) u₂ (cong (pairl u₁) (pairl .u₁) t⇒) = pairsn (f t⇒) u₂
  helper t₂ (acc f) (cong (pairr t₁) (pairr .t₁) t⇒) = pairsn t₂ (f t⇒)

-- Goal here: prove that sne is closed under application.


appsn : ∀{n Γ a b}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} → sn n t → sn n u → SNe n t →
                 ∀ {t' : Tm Γ b} → app t u ⟨ n ⟩⇒β t' → sn n t'
appsn t₂ u₁ (elim 𝒏 ()) β
appsn (acc t) u₁ 𝒏 (cong (appl u) (appl .u) t⇒) = acc (appsn (t t⇒) u₁ (mapNβSNe t⇒ 𝒏))
appsn t₁ (acc u₁) 𝒏 (cong (appr t) (appr .t) t⇒) = acc (appsn t₁ (u₁ t⇒) 𝒏)

∗1sn : ∀ {n Γ} {a : Ty}{b∞} {t : Tm Γ (▸̂ ((delay (λ {j} → a)) ⇒ b∞))}
         {u : Tm Γ (▸ a)} {Et' : Tm Γ (▸̂ b∞)} →
       sn n t → sn n u → SNe n t ⊎ SNe n u → (t ∗ u) ⟨ n ⟩⇒β Et' → sn n Et'
∗1sn t₂       u₁ (inj₁ (elim e ())) β▹
∗1sn t₂       u₁ (inj₂ (elim e ())) β▹
∗1sn (acc t₁) u₁ e           (cong (u ∗l) (.u ∗l) t⇒) = acc (∗1sn (t₁ t⇒) u₁ (Data.Sum.map (mapNβSNe t⇒) id e))
∗1sn t₁       (acc u) e      (cong (∗r t) (∗r .t) t⇒) = acc (∗1sn t₁ (u t⇒) (Data.Sum.map id (mapNβSNe t⇒) e))

elimsn : ∀{n Γ a b}{E : ECxt Γ a b}{t : Tm Γ a}{Et : Tm Γ b} → sn n t → PCxt (sn n) Et E t → SNe n t →
  ∀ {Et' : Tm Γ b} → Et ⟨ n ⟩⇒β Et' → sn n Et'
elimsn 𝒕 fst      (elim 𝒏 ()) βfst
elimsn 𝒕 fst      𝒏           (cong fst fst Et⇒Et') = fstsn (sn⇒β 𝒕 Et⇒Et')
elimsn 𝒕 snd      (elim 𝒏 ()) βsnd
elimsn 𝒕 snd      𝒏           (cong snd snd Et⇒Et') = {!!}
elimsn 𝒕 (appl 𝒖) 𝒏           t⇒                    = appsn 𝒕 𝒖 𝒏 t⇒
elimsn 𝒕 (𝒖 ∗l)   𝒏           t⇒                    = ∗1sn 𝒕 𝒖 (inj₁ 𝒏) t⇒
elimsn 𝒕 (∗r 𝒕₁)  𝒏           t⇒                    = ∗1sn {!𝒕₁!} 𝒕 (inj₂ 𝒏) t⇒


mutual

  helper : ∀ {Γ n a} {t : Tm Γ a} {j₁ j₂ : Size}
             {t′ : Tm Γ a} →
           t ⟨ n ⟩⇒ t′ → SN n t′ → sn n t
  helper (β 𝒖) t₁ = {!!}
  helper β▹ t₁ = {!!}
  helper (βfst 𝒖) t₁ = fstsn (pairsn (fromSN t₁) (fromSN 𝒖))
  helper (βsnd 𝒕) t₁ = {!!}
  helper (cong (appl u) (appl .u) t⇒) t₂ = {!fstsn!}
  helper (cong fst fst t⇒) t₂ = fstsn (helper t⇒ (fromFstSN t₂))
  helper (cong snd snd t⇒) t₂ = {!!}
  helper (cong (u ∗l) (.u ∗l) t⇒) t₂ = {!!}
  helper (cong (∗r t₁) (∗r .t₁) t⇒) t₂ = {!helper t⇒ (∗rSN t₂)!}

  fromSN : ∀ {i} {Γ} {n : ℕ} {a} {t : Tm Γ a} → SN {i} n t → sn n t
  fromSN (ne 𝒏) = fromSNe 𝒏
  fromSN (abs t₁) = abssn (fromSN t₁)
  fromSN (pair t₁ t₂) = pairsn (fromSN t₁) (fromSN t₂)
  fromSN ▹0 = acc ((λ { (cong () _ _) }))
  fromSN (▹ t₁) = ▹sn (fromSN t₁)
  fromSN (exp t⇒ t₁) = {! helper t⇒ t₁ !}

  fromSNe : ∀ {i Γ n a} {t : Tm Γ a} →
            SNe {i} n t → sn n t
  fromSNe (elim 𝒏 E) = acc (elimsn (fromSNe 𝒏) (mapPCxt fromSN E) (𝒏))
  fromSNe (var x)    = varsn x
