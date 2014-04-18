{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
--{-# OPTIONS --show-implicit #-}
module DeclSN where

open import Data.Sum
open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import SN
open import NReduction
open import Reduction

data sn {Γ} (n : ℕ) {a} (t : Tm Γ a) : Set where
  acc : (∀ {t'} → t ⟨ n ⟩⇒β t' → sn n t') → sn n t

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

open import Data.Empty

mutual
  helper : ∀ {Γ n a} {t : Tm Γ a} {j₁ j₂ : Size}
             {t′ : Tm Γ a} →
           t ⟨ n ⟩⇒ t′ → SN n t′ → sn n t
  helper (β 𝒖) t₁ = {!!}
  helper β▹ t₁ = {!!}
  helper (βfst 𝒖) t₁ = fstsn (pairsn (fromSN t₁) (fromSN 𝒖))
  helper (βsnd 𝒕) t₁ = {!!}
  helper (cong 𝑬𝒕 𝑬𝒕' t⇒) t₂ = {!!}

  fromSN : ∀ {i} {Γ} {n : ℕ} {a} {t : Tm Γ a} → SN {i} n t → sn n t
  fromSN (ne 𝒏) = acc (λ x → ⊥-elim (fromSNe 𝒏 x))
  fromSN (abs t₁) = abssn (fromSN t₁)
  fromSN (pair t₁ t₂) = pairsn (fromSN t₁) (fromSN t₂)
  fromSN ▹0 = acc ((λ { (cong () _ _) }))
  fromSN (▹ t₁) = ▹sn (fromSN t₁)
  fromSN (exp t⇒ t₁) = helper t⇒ t₁

  fromSNe : ∀ {i Γ n a} {t : Tm Γ a} {t' : Tm Γ a} →
            SNe {i} n t → t ⟨ n ⟩⇒β t' → ⊥ 
  fromSNe (elim 𝒏 (appl 𝒖)) β = {!!}
  fromSNe (elim (elim 𝒏 ()) (𝒖 ∗l)) β▹
  fromSNe (elim (elim 𝒏 ()) (∗r 𝒕)) β▹
  fromSNe (elim (elim 𝒏 ()) fst) βfst
  fromSNe (elim (elim 𝒏 ()) snd) βsnd
  fromSNe (elim 𝒏 E1) (cong E2 E3 t⇒) = {! fromSNe 𝒏 t⇒ !}
  fromSNe (var x) (cong () 𝑬𝒕' t⇒)
