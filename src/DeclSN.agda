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

--cong-fst-sn : ∀ {Γ n a j} {b} {t t' : Tm Γ (a ×̂ b)} →
--              t ⟨ n ⟩⇒ t' → sn n (fst t') → sn n (fst t)

-- Goal here: prove that sne is closed under application.

elimsn : ∀{n Γ a b}{E : ECxt Γ a b}{t : Tm Γ a}{Et : Tm Γ b} → sn n t → PCxt (sn n) Et E t → PNe (λ _ → ⊤) t →
  ∀ {Et' : Tm Γ b} → Et ⟨ n ⟩⇒β Et' → sn n Et'
elimsn 𝒕 (appl 𝒖) (elim 𝒏 ()) β
elimsn 𝒕 (𝒖 ∗l) (elim 𝒏 ()) β▹
elimsn 𝒕 (∗r 𝒕₁) (elim 𝒏 ()) β▹
elimsn 𝒕 fst (elim 𝒏 ()) βfst
elimsn 𝒕 snd (elim 𝒏 ()) βsnd
elimsn 𝒕 (appl 𝒖) 𝒏 (cong (appl u) (appl .u) Et⇒Et') = {!acc (elimsn ? (appl 𝒖) ? (cong (appl u) (appl u) ?)) !}
elimsn 𝒕 𝑬𝒕 𝒏 (cong (appr t₂) 𝑬𝒕' Et⇒Et') = {!!}
elimsn 𝒕 𝑬𝒕 𝒏 (cong fst 𝑬𝒕' Et⇒Et') = {!!}
elimsn 𝒕 𝑬𝒕 𝒏 (cong snd 𝑬𝒕' Et⇒Et') = {!!}
elimsn 𝒕 𝑬𝒕 𝒏 (cong (u ∗l) 𝑬𝒕' Et⇒Et') = {!!}
elimsn 𝒕 𝑬𝒕 𝒏 (cong (∗r t₂) 𝑬𝒕' Et⇒Et') = {!!}

snesn : ∀{n Γ a} {t : Tm Γ a} → PNe (sn n) t → sn n t
snesn (var x) = varsn x
snesn (elim 𝒏 𝑬𝒕) = {!snesn 𝒏!}


open import Data.Empty

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
  fromSN (ne 𝒏) = {- mapPNe () 𝒏 -}  fromSNe 𝒏
  fromSN (abs t₁) = abssn (fromSN t₁)
  fromSN (pair t₁ t₂) = pairsn (fromSN t₁) (fromSN t₂)
  fromSN ▹0 = acc ((λ { (cong () _ _) }))
  fromSN (▹ t₁) = ▹sn (fromSN t₁)
  fromSN (exp t⇒ t₁) = helper t⇒ t₁

  fromSNe : ∀ {i Γ n a} {t : Tm Γ a} →
            SNe {i} n t → sn n t
  fromSNe (elim 𝒏 (appl 𝒖)) = {!!}
  fromSNe {t = fst (var x)   } (elim 𝒏 fst) = acc λ{ .{_} (cong fst fst t'⇒β) → fstsn (sn⇒β (fromSNe 𝒏) t'⇒β) }
  fromSNe {t = fst (app t t₁)} (elim 𝒏 fst) = acc λ{ .{_} (cong fst fst t'⇒β) → fstsn (sn⇒β (fromSNe 𝒏) t'⇒β) }
  fromSNe {t = fst (pair t t₁)} (elim (elim 𝒏 ()) fst)
  fromSNe {t = fst (fst t)   } (elim 𝒏 fst) = acc λ{ .{_} (cong fst fst t'⇒β) → fstsn (sn⇒β (fromSNe 𝒏) t'⇒β) }
  fromSNe {t = fst (snd t)   } (elim 𝒏 fst) = acc λ{ .{_} (cong fst fst t'⇒β) → fstsn (sn⇒β (fromSNe 𝒏) t'⇒β) }
  fromSNe (elim 𝒏 snd) = {!!}
  fromSNe (elim 𝒏 (𝒖 ∗l)) = {!!}
  fromSNe (elim 𝒏 (∗r 𝒕)) = {!!}
  fromSNe (var x)  = varsn x

  -- fromSNe : ∀ {i Γ n a} {t : Tm Γ a} {t' : Tm Γ a} →
  --           SNe {i} n t → t ⟨ n ⟩⇒β t' → ⊥
  -- fromSNe (elim 𝒏 (appl 𝒖)) β = {!!}
  -- fromSNe (elim (elim 𝒏 ()) (𝒖 ∗l)) β▹
  -- fromSNe (elim (elim 𝒏 ()) (∗r 𝒕)) β▹
  -- fromSNe (elim (elim 𝒏 ()) fst) βfst
  -- fromSNe (elim (elim 𝒏 ()) snd) βsnd
  -- fromSNe (elim 𝒏 E1) (cong E2 E3 t⇒) = {! fromSNe 𝒏 t⇒ !}
  -- fromSNe (var x) (cong () 𝑬𝒕' t⇒)
