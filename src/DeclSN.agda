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

Sndsn : ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ a}{u : Tm Γ b} → sn n (pair t u) → sn n u
Sndsn (acc f) = acc (\ x -> Sndsn (f (cong (pairr _) (pairr _) x)))

fstsn : ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ (a ×̂  b)} → sn n t → sn n (fst t)
fstsn t = acc (helper t) where
  helper : ∀ {Γ n a b} {t : Tm Γ (a ×̂ b)} {t' : Tm Γ a}
           → sn n t → fst t ⟨ n ⟩⇒β t' → sn n t'
  helper t       βfst               = Fstsn t 
  helper (acc f) (cong fst fst t⇒β) = fstsn (f t⇒β)

sndsn : ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ (a ×̂  b)} → sn n t → sn n (snd t)
sndsn t = acc (helper t) where
  helper : ∀ {Γ n a b} {t : Tm Γ (a ×̂ b)} {t' : Tm Γ b}
           → sn n t → snd t ⟨ n ⟩⇒β t' → sn n t'
  helper t       βsnd               = Sndsn t
  helper (acc f) (cong snd snd t⇒β) = sndsn (f t⇒β)

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
appsn t       u       (elim 𝒏 ()) β
appsn (acc t) 𝒖       𝒏           (cong (appl u) (appl .u) t⇒) = acc (appsn (t t⇒) 𝒖      (mapNβSNe t⇒ 𝒏))
appsn 𝒕       (acc u) 𝒏           (cong (appr t) (appr .t) t⇒) = acc (appsn 𝒕      (u t⇒) 𝒏)

∗sn : ∀ {n Γ} {a : Ty}{b∞} {t : Tm Γ (▸̂ ((delay (λ {j} → a)) ⇒ b∞))}
         {u : Tm Γ (▸ a)} {Et' : Tm Γ (▸̂ b∞)} → sn n t → sn n u → SNe n t ⊎ SNe n u → (t ∗ u) ⟨ n ⟩⇒β Et' → sn n Et'
∗sn t       u       (inj₁ (elim e ())) β▹
∗sn t       u       (inj₂ (elim e ())) β▹
∗sn (acc t) 𝒖       e                  (cong (u ∗l) (.u ∗l) t⇒) = acc (∗sn (t t⇒) 𝒖      (Data.Sum.map (mapNβSNe t⇒) id e))
∗sn 𝒕       (acc u) e                  (cong (∗r t) (∗r .t) t⇒) = acc (∗sn 𝒕      (u t⇒) (Data.Sum.map id (mapNβSNe t⇒) e))

elimsn : ∀ {n Γ a b}{E : ECxt Γ a b}{t : Tm Γ a}{Et : Tm Γ b} → sn n t → PCxt (sn n) Et E t → SNe n t →
         ∀ {Et' : Tm Γ b} → Et ⟨ n ⟩⇒β Et' → sn n Et'
elimsn 𝒕 fst      (elim 𝒏 ()) βfst
elimsn 𝒕 fst      𝒏           (cong fst fst Et⇒Et') = fstsn (sn⇒β 𝒕 Et⇒Et')
elimsn 𝒕 snd      (elim 𝒏 ()) βsnd
elimsn 𝒕 snd      𝒏           (cong snd snd Et⇒Et') = sndsn (sn⇒β 𝒕 Et⇒Et')
elimsn 𝒕 (appl 𝒖) 𝒏           t⇒                    = appsn 𝒕 𝒖 𝒏 t⇒
elimsn 𝒕 (𝒖 ∗l)   𝒏           t⇒                    = ∗sn 𝒕 𝒖 (inj₁ 𝒏) t⇒
elimsn 𝒕 (∗r 𝒕₁)  𝒏           t⇒                    = ∗sn 𝒕₁ 𝒕 (inj₂ 𝒏) t⇒




substβsn : ∀ {i m vt a Γ n} {Δ} {σ ρ : RenSub {m} vt Γ Δ} → (∀ {b} (x : Var Γ b) → vt2tm _ (σ x) ⟨ n ⟩⇒β* vt2tm _ (ρ x))
             → (t : Tm Γ a) → SN {i} n (subst σ t) → SN {i} n (subst ρ t)
substβsn f t x₁ = mapβ*SN (subst⇒β* (λ x → nβ*⇒β* (f x)) t) x₁


antiSubst : ∀ {n Γ a b} {t : Tm (a ∷ Γ) b}{u : Tm Γ a} → sn n (subst (sgs u) t) → sn n t
antiSubst {t = t} (acc f) = acc (λ x → antiSubst (f (NReduction.subst⇒β (sgs _) x)))


mutual
{-
  -- could we just use the beta-shr lemma?
  helper2 : ∀ {i Γ n a} {t th to : Tm Γ a} →
           i size t ⟨ n ⟩⇒ th → {-SN {j} n th →-} sn n th -> t ⟨ n ⟩⇒β to → sn n to
  helper2 th {-SNt-} snt tb with beta-shr (nβ⇒β tb) th 
  helper2 th₁ {-SNt-} snt tb | inj₁ ≡.refl = snt
  helper2 th₁ {-SNt-} snt tb | inj₂ (z , th' , xs) = rec snt z th' xs
    where
      rec : ∀ {i Γ n a} {th to : Tm Γ a} →
        sn n th → (z : Tm Γ a) → SN {i} n / to ⇒ z → th ⇒β* z → sn n to
      rec snt₁ th to⇒ ([]) = {!!}
      rec {n = n} (acc f) th to⇒ (x ∷ []) with split {n} x
      ... | th⇒ = acc (helper2 to⇒ (f th⇒))
      rec {n = n} (acc f) z₁ to⇒ (x ∷ xs₁) with split x
      ... | th⇒ = rec (f th⇒) z₁ to⇒ xs₁
-}

  appsn₂ : ∀ {i n a b Γ} {u : Tm Γ a} {t : Tm (a ∷ Γ) (b)} → sn n t → SN {i} n (subst (sgs u) t) → sn n u → sn n (app (abs t) u) 
  appsn₂ t t[u] u = acc (λ x → help t t[u] u x) where
    help : ∀ {i n a b Γ} {u : Tm Γ a} {t : Tm (a ∷ Γ) b} {t' : Tm Γ b} → sn n t → 
         SN {i} n (subst (u ∷s var) t) →
         sn n u → app (abs t) u ⟨ n ⟩⇒β t' → sn n t'
    help t t[u]∈sn u∈sn β = fromSN t[u]∈sn
    help (acc f1) t[u]∈sn u∈sn (cong (appl u) (appl .u) (cong abs abs t⇒)) = appsn₂ (f1 t⇒) (mapβSN (nβ⇒β (NReduction.subst⇒β (sgs u) t⇒)) t[u]∈sn) u∈sn
    help {i} t t[u]∈sn (acc g) (cong (appr ._) (appr ._) t⇒) = appsn₂ {i} t (mapβ*SN (subst⇒β* {!!} {!!}) t[u]∈sn) (g t⇒)

  helper : ∀ {i j Γ n a} {t th to : Tm Γ a} →
           i size t ⟨ n ⟩⇒ th → SN {j} n th → sn n th -> t ⟨ n ⟩⇒β to → sn n to
  helper (β 𝒖) 𝒕h 𝑡h β = 𝑡h
  helper (cong (appl u) (appl .u) (cong () 𝑬𝒕' t⇒th)) 𝒕h 𝑡h β
  helper β▹ 𝒕h 𝑡h β▹ = 𝑡h
  helper (cong (._ ∗l) (._ ∗l) (cong () 𝑬𝒕' t⇒th)) 𝒕h 𝑡h β▹
  helper (cong (∗r t) (∗r .t) (cong () 𝑬𝒕' t⇒th)) 𝒕h 𝑡h β▹
  helper (βfst 𝒖) 𝒕h 𝑡h βfst = 𝑡h
  helper (cong fst fst (cong () 𝑬𝒕' t⇒th)) 𝒕h 𝑡h βfst
  helper (βsnd 𝒕) 𝒕h 𝑡h βsnd = 𝑡h
  helper (cong snd snd (cong () 𝑬𝒕' t⇒th)) 𝒕h 𝑡h βsnd
  helper (β 𝒖) 𝒕h (acc f) (cong (appl u) (appl .u) (cong abs abs t⇒o)) = appsn₂ (antiSubst (f (NReduction.subst⇒β (sgs u) t⇒o))) 
                                (mapβSN (nβ⇒β (NReduction.subst⇒β (sgs u) t⇒o)) 𝒕h) (fromSN 𝒖)
  helper (β {t = t} 𝒖) 𝒕h 𝑡h (cong (appr ._) (appr ._) t⇒o) 
         = appsn₂ (antiSubst 𝑡h) (substβsn (λ { {._} zero → t⇒o ∷ [] ; (suc x) → [] }) t 𝒕h)
                  (sn⇒β (fromSN 𝒖) t⇒o)
  helper β▹ 𝒕h 𝑡h (cong (._ ∗l) (._ ∗l) (cong ▹_ ▹_ t⇒o)) = {!!}
  helper β▹ 𝒕h 𝑡h (cong (∗r ._) (∗r ._) t⇒o) = {!!}
  helper (βfst 𝒖) 𝒕h 𝑡h (cong fst fst (cong (pairl u) (pairl .u) t⇒o)) = fstsn (pairsn (sn⇒β 𝑡h t⇒o) (fromSN 𝒖))
  helper (βfst 𝒖) 𝒕h 𝑡h (cong fst fst (cong (pairr th) (pairr .th) t⇒o)) = fstsn (pairsn 𝑡h (sn⇒β (fromSN 𝒖) t⇒o))
  helper (βsnd 𝒕) 𝒕h 𝑡h (cong 𝑬𝒕 𝑬𝒕' t⇒o) = {!!}
  helper (cong (appl u) (appl .u) t⇒th) 𝒕h 𝑡h (cong (appl .u) (appl .u) t⇒o) = {!!}
  helper (cong (appl u) (appl .u) t⇒th) 𝒕h 𝑡h (cong (appr t) (appr .t) t⇒o) = {!!}
  helper (cong fst fst t⇒th) 𝒕h 𝑡h (cong fst fst t⇒o) = {!!}
  helper (cong snd snd t⇒th) 𝒕h 𝑡h (cong snd snd t⇒o) = {!!}
  helper (cong (u ∗l) (.u ∗l) t⇒th) 𝒕h 𝑡h (cong (.u ∗l) (.u ∗l) t⇒o) = {!!}
  helper (cong (u ∗l) (.u ∗l) t⇒th) 𝒕h 𝑡h (cong (∗r t) (∗r .t) t⇒o) = {!!}
  helper (cong (∗r t₁) (∗r .t₁) t⇒th) 𝒕h 𝑡h (cong (t ∗l) (.t ∗l) t⇒o) = {!!}
  helper (cong (∗r t₁) (∗r .t₁) t⇒th) 𝒕h 𝑡h (cong (∗r .(▹ t₁)) (∗r .(▹ t₁)) t⇒o) = {!!}

  fromSN : ∀ {i} {Γ} {n : ℕ} {a} {t : Tm Γ a} → SN {i} n t → sn n t
  fromSN (ne 𝒏)       = fromSNe 𝒏
  fromSN (abs t₁)     = abssn (fromSN t₁)
  fromSN (pair t₁ t₂) = pairsn (fromSN t₁) (fromSN t₂)
  fromSN ▹0           = acc ((λ { (cong () _ _) }))
  fromSN (▹ t₁)       = ▹sn (fromSN t₁)
  fromSN (exp t⇒ t₁)  = acc (helper t⇒ t₁ (fromSN t₁))

  fromSNe : ∀ {i Γ n a} {t : Tm Γ a} → SNe {i} n t → sn n t
  fromSNe (elim 𝒏 E) = acc (elimsn (fromSNe 𝒏) (mapPCxt fromSN E) 𝒏)
  fromSNe (var x)    = varsn x
