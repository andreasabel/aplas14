{-# OPTIONS --copatterns --sized-types #-}
--{-# OPTIONS --allow-unsolved-metas #-}

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

subsn : ∀ {Γ Δ} {n n' : ℕ} {a b} {f : Tm Γ a -> Tm Δ b} →
        (g : ∀ {t t' : Tm Γ a} → t ⟨ n ⟩⇒β t' → f t ⟨ n' ⟩⇒β f t') →
        ∀ {t} → sn n' (f t) → sn n t
subsn g (acc ft) = acc (\ t⇒ -> subsn g (ft (g t⇒)))

Fstsn : ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ a}{u : Tm Γ b} → sn n (pair t u) → sn n t
Fstsn p = subsn (\ x -> cong (pairl _) (pairl _) x) p

Sndsn : ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ a}{u : Tm Γ b} → sn n (pair t u) → sn n u
Sndsn = subsn (\ x -> (cong (pairr _) (pairr _) x))

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
antiSubst {t = t} = subsn (λ x → NReduction.subst⇒β (sgs _) x)

subexpsn : ∀ {n Γ a b} (E : ECxt* Γ a b) {t : Tm Γ a} → sn n (E [ t ]*) -> sn n t
subexpsn E = subsn \ x -> cong*2 E x

∗sn₂ : ∀ {Γ b} {a b∞} {z} {t : Tm Γ (a →̂ (force b∞))} {u : Tm Γ a}
       {n} (E : ECxt* Γ (▸̂ b∞) b) →
                     sn (suc n) (E [ z ]*) →
       sn n t → sn n u →

     sn (suc n) (E [ ▹ app t u ]*) →

     sn (suc n) (E [ (▹ t) ∗ (▹ u) ]*)
∗sn₂ E z t u r = acc (λ x → help E z t u r (mkEhole* E) x) where
  help : ∀ {Γ b a b∞} {z : Tm Γ (▸̂ b∞)} {q}
       {t : Tm Γ (a →̂ (force b∞))} {u : Tm Γ a} {n} {t' : Tm Γ b}
       (E : ECxt* Γ (▸̂ b∞) b) →
     sn (suc n) (E [ z ]*) →
     sn n t →
     sn n u →
     sn (suc n) (E [ ▹ app t u ]*) →
     Ehole* q E ((▹ t) ∗ (▹ u))  →  q ⟨ suc n ⟩⇒β t' → sn (suc n) t'
  help E z t u r eq t⇒ with split E eq β▹ t⇒
  help E₁ z₂ t₂ u₂ r₁ eq t⇒ | inj₁ (._ , a₁ , β▹) rewrite hole*→≡ a₁ = r₁
  help E₁ z₂ (acc t₃) u₂ r₁ eq t⇒ | inj₁ (._ , a₁ , cong (._ ∗l) (._ ∗l) (cong ▹_ ▹_ t⇒')) rewrite hole*→≡ a₁ 
    = ∗sn₂ E₁ z₂ (t₃ t⇒') u₂ (sn⇒β r₁ (cong*2 E₁ (cong ▹_ ▹_ (cong (appl _) (appl _) t⇒'))))
  help E₁ z₂ t₃ (acc u₂) r₁ eq t⇒ | inj₁ (._ , a₁ , cong (∗r ._) (∗r ._) (cong ▹_ ▹_ t⇒')) rewrite hole*→≡ a₁ 
    = ∗sn₂ E₁ z₂ t₃ (u₂ t⇒') (sn⇒β r₁ (cong*2 E₁ (cong ▹_ ▹_ (cong (appr _) (appr _) t⇒'))))
  help E₁ (acc z₂) t₂ u₂ r₁ eq t⇒ | inj₂ (Es' , a , g) rewrite hole*→≡ a = ∗sn₂ Es' (z₂ (g _)) t₂ u₂ (sn⇒β r₁ (g _))

fstsn₂ : ∀ {Γ b} {a c} {z} {t : Tm Γ b} {u : Tm Γ a}
       {n} (E : ECxt* Γ b c) →
       sn n (E [ z ]*) →
       sn n t → sn n u →
       sn n (E [ t ]*) →
       sn n (E [ fst (pair t u) ]*)
fstsn₂ E z t u r = acc (λ x → help E z t u r (mkEhole* E) x) where
  help : ∀ {Γ b a c} {z t : Tm Γ b} {u : Tm Γ a} {n} {t' : Tm Γ c}{q}
         (E : ECxt* Γ b c) →
       sn n (E [ z ]*) →
       sn n t →
       sn n u →
       sn n (E [ t ]*) →
       Ehole* q E (fst (pair t u)) →
         q ⟨ n ⟩⇒β t' → sn n t'
  help E z t u r eq t⇒ with split E eq βfst t⇒
  help E₁ z₂ t₂ u₂ r eq t⇒ | inj₁ (t₁ , a₁ , βfst) rewrite hole*→≡ a₁ = r
  help E₁ z₂ (acc t₃) u₂ r₁ eq t⇒ | inj₁ (._ , a₂ , cong fst fst (cong (pairl u₁) (pairl .u₁) t⇒')) 
    rewrite hole*→≡ a₂ = fstsn₂ E₁ z₂ (t₃ t⇒') u₂ (sn⇒β r₁ (cong*2 E₁ t⇒'))
  help E₁ z₂ t₃ (acc u₂) r₁ eq t⇒ | inj₁ (._ , a₂ , cong fst fst (cong (pairr t₁) (pairr .t₁) t⇒')) 
    rewrite hole*→≡ a₂ = fstsn₂ E₁ z₂ t₃ (u₂ t⇒') r₁
  help E₁ (acc z₂) t₂ u₂ r eq t⇒ | inj₂ (Es' , a , g) rewrite hole*→≡ a = fstsn₂ Es' (z₂ (g _)) t₂ u₂ (sn⇒β r (g _))

sndsn₂ : ∀ {Γ b} {a c} {z} {t : Tm Γ b} {u : Tm Γ a}
       {n} (E : ECxt* Γ b c) →
       sn n (E [ z ]*) →
       sn n t → sn n u →
       sn n (E [ t ]*) →
       sn n (E [ snd (pair u t) ]*)
sndsn₂ E z t u r = acc (λ x → help E z t u r (mkEhole* E) x) where
  help : ∀ {Γ b a c} {z t : Tm Γ b} {u : Tm Γ a} {n} {t' : Tm Γ c}{q}
         (E : ECxt* Γ b c) →
       sn n (E [ z ]*) →
       sn n t →
       sn n u →
       sn n (E [ t ]*) →
       Ehole* q E (snd (pair u t)) →
         q ⟨ n ⟩⇒β t' → sn n t'
  help E z t u r eq t⇒ with split E eq βsnd t⇒
  help E₁ z₂ t₂ u₂ r eq t⇒ | inj₁ (t₁ , a₁ , βsnd) rewrite hole*→≡ a₁ = r
  help E₁ z₂ (acc t₃) u₂ r₁ eq t⇒ | inj₁ (._ , a₂ , cong snd snd (cong (pairr u₁) (pairr .u₁) t⇒')) 
    rewrite hole*→≡ a₂ = sndsn₂ E₁ z₂ (t₃ t⇒') u₂ (sn⇒β r₁ (cong*2 E₁ t⇒'))
  help E₁ z₂ t₃ (acc u₂) r₁ eq t⇒ | inj₁ (._ , a₂ , cong snd snd (cong (pairl t₁) (pairl .t₁) t⇒')) 
    rewrite hole*→≡ a₂ = sndsn₂ E₁ z₂ t₃ (u₂ t⇒') r₁
  help E₁ (acc z₂) t₂ u₂ r eq t⇒ | inj₂ (Es' , a , g) rewrite hole*→≡ a = sndsn₂ Es' (z₂ (g _)) t₂ u₂ (sn⇒β r (g _))


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

  appsn₃ : ∀ {i n a b c Γ} {u : Tm Γ a} {t : Tm (a ∷ Γ) b}{Es : ECxt* Γ b c}{x} → sn n (Es [ x ]*) → sn n t → SN {i} n (Es [ subst (sgs u) t ]*) 
           → sn n u → sn n (Es [ app (abs t) u ]*) 
  appsn₃ {Es = Es} x t t[u] u = acc (λ t⇒ → help {Es = Es} x t t[u] u (mkEhole* Es) t⇒) where
    help : ∀ {i n a b c Γ} {u : Tm Γ a} {t : Tm (a ∷ Γ) b} {t' : Tm Γ c} {x}  {z}{Es : ECxt* Γ b c} → sn n (Es [ x ]*) → sn n t → 
         SN {i} n (Es [ subst (u ∷s var) t ]*) →
         sn n u → Ehole* z Es (app (abs t) u) → z ⟨ n ⟩⇒β t' → sn n t'
    help {Es = Es} x t t[u]∈sn u∈sn eq t⇒ with split Es eq β t⇒ 
    help x t₂ t[u]∈sn u∈sn eq t⇒ | inj₁ (._ , a₁ , β) rewrite hole*→≡ a₁ = fromSN t[u]∈sn
    help {Es = Es} x (acc t₃) t[u]∈sn u∈sn eq t⇒ | inj₁ (._ , a₁ , cong (appl u₁) (appl .u₁) (cong abs abs b₁)) rewrite hole*→≡ a₁ 
      = appsn₃ {Es = Es} x (t₃ b₁) (mapNβSN (cong*2 Es (NReduction.subst⇒β (sgs u₁) b₁)) t[u]∈sn) u∈sn
    help {t = t} {Es = Es} x t₃ t[u]∈sn (acc u∈sn) eq t⇒ | inj₁ (._ , a₁ , cong (appr ._) (appr ._) b₁) rewrite hole*→≡ a₁ 
      = appsn₃ {Es = Es} x t₃ (mapβ*SN (cong*4 Es
                                          (subst⇒β* (λ { {._} zero → nβ⇒β b₁ ∷ [] ; (suc n) → [] }) t)) t[u]∈sn) (u∈sn b₁)
    help {x = x} (acc f) t₂ t[u]∈sn u∈sn eq t⇒ | inj₂ (Es' , a , g) rewrite hole*→≡ a 
         = appsn₃ {Es = Es'} (f (g x)) t₂ (mapNβSN (g _) t[u]∈sn) u∈sn


  helperCxt : ∀ {i j Γ n a b} {t th to : Tm Γ a}  → (Es : ECxt* Γ a b)
              →       i size t ⟨ n ⟩⇒ th → SN {j} n (Es [ th ]*) → sn n (Es [ th ]*) -> t ⟨ n ⟩⇒β to → sn n (Es [ to ]*)

  helperCxt E (β 𝒖)    𝒕h 𝑡h β    = 𝑡h
  helperCxt E β▹       𝒕h 𝑡h β▹   = 𝑡h
  helperCxt E (βfst 𝒖) 𝒕h 𝑡h βfst = 𝑡h
  helperCxt E (βsnd 𝒕) 𝒕h 𝑡h βsnd = 𝑡h

  helperCxt E (β         𝒖) 𝒕h 𝑡h (cong (appl  u) (appl .u) (cong abs abs t⇒)) 
    = appsn₃ {Es = E} 𝑡h (sn⇒β (antiSubst (subexpsn E 𝑡h)) t⇒) 
              (mapNβSN (cong*2 E (NReduction.subst⇒β (sgs u) t⇒)) 𝒕h) 
              (fromSN 𝒖)
  helperCxt E (β {t = t} 𝒖) 𝒕h 𝑡h (cong (appr ._) (appr ._)               t⇒)  
    = appsn₃ {Es = E} 𝑡h (antiSubst (subexpsn E 𝑡h)) 
              (mapβ*SN (cong*4 E (subst⇒β* (λ { {._} zero → nβ⇒β t⇒ ∷ [] ; (suc x) → [] }) t)) 𝒕h) 
              (sn⇒β (fromSN 𝒖) t⇒)

  helperCxt E β▹       𝒕h 𝑡h (cong (._ ∗l)   (._ ∗l) (cong ▹_ ▹_ t⇒)) 
     = ∗sn₂ E 𝑡h (sn⇒β (subsn (λ x → cong*2 E (cong ▹_ ▹_ (cong (appl _) (appl _) x))) 𝑡h) t⇒) 
                       (subsn (λ x → cong*2 E (cong ▹_ ▹_ (cong (appr _) (appr _) x))) 𝑡h) 
                 (sn⇒β 𝑡h (cong*2 E (cong ▹_ ▹_ (cong (appl _) (appl _) t⇒))))
  helperCxt E β▹       𝒕h 𝑡h (cong (∗r ._)   (∗r ._) (cong ▹_ ▹_ t⇒)) = ∗sn₂ E 𝑡h 
            (subsn (λ x → cong*2 E (cong ▹_ ▹_ (cong (appl _) (appl _) x))) 𝑡h) 
      (sn⇒β (subsn (λ x → cong*2 E (cong ▹_ ▹_ (cong (appr _) (appr _) x))) 𝑡h) t⇒)
      (sn⇒β 𝑡h (cong*2 E (cong ▹_ ▹_ (cong (appr _) (appr _) t⇒))))

  helperCxt E (βfst 𝒖) 𝒕h 𝑡h (cong fst fst (cong (pairl _) (pairl ._) t⇒)) = fstsn₂ E 𝑡h (sn⇒β (subexpsn E 𝑡h) t⇒) (fromSN 𝒖) (sn⇒β 𝑡h (cong*2 E t⇒))
  helperCxt E (βfst 𝒖) 𝒕h 𝑡h (cong fst fst (cong (pairr _) (pairr ._) t⇒)) = fstsn₂ E 𝑡h (subexpsn E 𝑡h) (sn⇒β (fromSN 𝒖) t⇒) 𝑡h

  helperCxt E (βsnd 𝒖) 𝒕h 𝑡h (cong snd snd (cong (pairr _) (pairr ._) t⇒)) = sndsn₂ E 𝑡h (sn⇒β (subexpsn E 𝑡h) t⇒) (fromSN 𝒖) (sn⇒β 𝑡h (cong*2 E t⇒))
  helperCxt E (βsnd 𝒖) 𝒕h 𝑡h (cong snd snd (cong (pairl _) (pairl ._) t⇒)) = sndsn₂ E 𝑡h (subexpsn E 𝑡h) (sn⇒β (fromSN 𝒖) t⇒) 𝑡h

  helperCxt E (cong (appl u) (appl .u) (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h β
  helperCxt E (cong (._ ∗l)  (._ ∗l)   (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h β▹
  helperCxt E (cong (∗r t)   (∗r .t)   (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h β▹
  helperCxt E (cong fst      fst       (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h βfst
  helperCxt E (cong snd      snd       (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h βsnd

  helperCxt E (cong (appl u) (appl .u) th⇒) 𝒕h 𝑡h (cong (appl .u)    (appl .u)    t⇒) = helperCxt (appl u ∷ E) th⇒ 𝒕h 𝑡h t⇒
  helperCxt E (cong fst      fst       th⇒) 𝒕h 𝑡h (cong fst          fst          t⇒) = helperCxt (fst ∷ E)    th⇒ 𝒕h 𝑡h t⇒
  helperCxt E (cong snd      snd       th⇒) 𝒕h 𝑡h (cong snd          snd          t⇒) = helperCxt (snd ∷ E)    th⇒ 𝒕h 𝑡h t⇒
  helperCxt E (cong (u ∗l)   (.u ∗l)   th⇒) 𝒕h 𝑡h (cong (.u ∗l)      (.u ∗l)      t⇒) = helperCxt (u ∗l ∷ E)   th⇒ 𝒕h 𝑡h t⇒
  helperCxt E (cong (∗r t₁)  (∗r .t₁)  th⇒) 𝒕h 𝑡h (cong (∗r .(▹ t₁)) (∗r .(▹ t₁)) t⇒) = helperCxt (∗r t₁ ∷ E)  th⇒ 𝒕h 𝑡h t⇒

  helperCxt E (cong (appl u) (appl .u) th⇒) 𝒕h (acc 𝑡h) (cong (appr t) (appr .t)           t⇒) 
            = acc (helperCxt [] (E [ cong (appl _) (appl _) th⇒ ]⇒*) (mapNβSN t⇒' 𝒕h) (𝑡h t⇒'))
               where t⇒' = E [ cong (appr _) (appr _)           t⇒  ]⇒β*    

  helperCxt E (cong (u ∗l)   (.u ∗l)   th⇒) 𝒕h (acc 𝑡h) (cong (∗r t)   (∗r .t)             t⇒) 
            = acc (helperCxt [] (E [ cong (_ ∗l)   (_ ∗l)   th⇒ ]⇒*) (mapNβSN t⇒' 𝒕h) (𝑡h t⇒'))
               where t⇒' = E [ cong (∗r _)   (∗r _)             t⇒  ]⇒β*

  helperCxt E (cong (∗r t₁)  (∗r .t₁)  th⇒) 𝒕h (acc 𝑡h) (cong (t ∗l)   (.t ∗l) (cong ▹_ ▹_ t⇒)) 
            = acc (helperCxt [] (E [ cong (∗r _)   (∗r _)   th⇒ ]⇒*) (mapNβSN t⇒' 𝒕h) (𝑡h t⇒')) 
               where t⇒' = E [ cong (_ ∗l)   (_ ∗l) (cong ▹_ ▹_ t⇒) ]⇒β*


  fromSN : ∀ {i} {Γ} {n : ℕ} {a} {t : Tm Γ a} → SN {i} n t → sn n t
  fromSN (ne 𝒏)       = fromSNe 𝒏
  fromSN (abs t₁)     = abssn (fromSN t₁)
  fromSN (pair t₁ t₂) = pairsn (fromSN t₁) (fromSN t₂)
  fromSN ▹0           = acc ((λ { (cong () _ _) }))
  fromSN (▹ t₁)       = ▹sn (fromSN t₁)
  fromSN (exp t⇒ t₁)  = acc (helperCxt [] t⇒ t₁ (fromSN t₁))

  fromSNe : ∀ {i Γ n a} {t : Tm Γ a} → SNe {i} n t → sn n t
  fromSNe (elim 𝒏 E) = acc (elimsn (fromSNe 𝒏) (mapPCxt fromSN E) 𝒏)
  fromSNe (var x)    = varsn x
