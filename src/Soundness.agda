{-# OPTIONS --copatterns --sized-types #-}

-- Type interpretation and soundness of typing.

module Soundness where

open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import SN
open import SN.AntiRename
open import SAT3

-- Type interpretation

infix 3 ⟦_⟧_

⟦_⟧≤ : (a : Ty) {n : ℕ} → SAT≤ a n

⟦_⟧_ : (a : Ty) (n : ℕ) → SAT a n
⟦ a →̂ b ⟧ n  = ⟦ a ⟧≤ {n} ⟦→⟧ ⟦ b ⟧≤ {n}
⟦ a ×̂ b ⟧ n  = (⟦ a ⟧ n) ⟦×⟧ (⟦ b ⟧ n)
⟦ ▸̂ a∞  ⟧ n  = ⟦▸⟧ P n
  where
    P : ∀ n → SATpred (force a∞) n
    P zero = _
    P (suc n₁) = ⟦ force a∞ ⟧ n₁

⟦_⟧≤′ : (a : Ty) {n : ℕ} → ∀ {m} → m ≤′ n → SAT a m

⟦ a ⟧≤ m≤n = ⟦ a ⟧≤′ (≤⇒≤′ m≤n)

⟦_⟧≤′ a .{m}     {m} ≤′-refl = ⟦ a ⟧ m
⟦_⟧≤′ a .{suc n} {m} (≤′-step {n} m≤n) = ⟦ a ⟧≤′ m≤n

in≤′ : (a : Ty) {n : ℕ} → ∀ {m} → (m≤n : m ≤′ n) → SAT.satSet (⟦ a ⟧ m) ⊆ SAT.satSet (⟦ a ⟧≤′ m≤n)
in≤′ a ≤′-refl       𝑡 = 𝑡
in≤′ a (≤′-step m≤n) 𝑡 = in≤′ a m≤n 𝑡

out≤′ : (a : Ty) {n : ℕ} → ∀ {m} → (m≤n : m ≤′ n) → SAT.satSet (⟦ a ⟧≤′ m≤n) ⊆ SAT.satSet (⟦ a ⟧ m)
out≤′ a ≤′-refl 𝑡 = 𝑡
out≤′ a (≤′-step m≤n) 𝑡 = out≤′ a m≤n 𝑡

coerce≤ : (a : Ty) {n n' : ℕ} → ∀ {m} → (m≤n : m ≤ℕ n) (m≤n' : m ≤ℕ n') → SAT.satSet (⟦ a ⟧≤′ (≤⇒≤′ m≤n)) ⊆ SAT.satSet (⟦ a ⟧≤′ (≤⇒≤′ m≤n'))
coerce≤ a ≤1 ≤2 𝑡 = in≤′ a (≤⇒≤′ ≤2) (out≤′ a (≤⇒≤′ ≤1) 𝑡)

map⟦_⟧ : ∀ (a : Ty) → ∀ {m n} → m ≤ℕ n → ∀ {Γ} {t : Tm Γ a} → SAT.satSet (⟦ a ⟧ n) t
                                           → SAT.satSet (⟦ a ⟧ m) t
map⟦_⟧ (a →̂ b) m≤n 𝑡          = λ l l≤m ρ 𝑢 → let l≤n = ≤ℕ.trans l≤m m≤n in
                                  coerce≤ b l≤n l≤m (𝑡 l l≤n ρ (coerce≤ a l≤m l≤n 𝑢))
map⟦_⟧ (a ×̂ b) m≤n (t1 , t2) = map⟦ a ⟧ m≤n t1 , map⟦ b ⟧ m≤n t2
map⟦_⟧ (▸̂ a∞) {m = zero}  m≤n ▹0         = ▹0
map⟦_⟧ (▸̂ a∞) {m = suc m} ()  ▹0
map⟦_⟧ (▸̂ a∞) {m = zero}  m≤n (▹ 𝒕)      = ▹0
map⟦_⟧ (▸̂ a∞) {m = suc m} m≤n (▹ 𝒕)      = ▹ map⟦ force a∞ ⟧ (pred≤ℕ m≤n) 𝒕
map⟦_⟧ (▸̂ a∞)             m≤n (ne 𝒏)     = ne (mapSNe m≤n 𝒏)
map⟦_⟧ (▸̂ a∞)             m≤n (exp t⇒ 𝑡) = exp (map⇒ m≤n t⇒) (map⟦ (▸̂ a∞) ⟧ m≤n 𝑡)

map⟦_⟧∈ : ∀ (a : Ty) → ∀ {m n} → (m ≤ℕ n) → ∀ {Γ} {t : Tm Γ a} → t ∈ (⟦ a ⟧ n)
                                            → t ∈ (⟦ a ⟧ m)
map⟦_⟧∈ a m≤n (↿ 𝑡) = ↿ (map⟦ a ⟧ m≤n 𝑡)

-- Context interpretation (semantic substitutions)

⟦_⟧C : ∀ Γ {n} → ∀ {Δ} (σ : Subst Γ Δ) → Set
⟦ Γ ⟧C {n} σ = ∀ {a} (x : Var Γ a) → σ x ∈ (⟦ a ⟧ n)

Ext : ∀ {a n Δ Γ} {t : Tm Δ a} → (𝒕 : t ∈ (⟦ a ⟧ n)) →
      ∀ {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C σ) → ⟦ a ∷ Γ ⟧C (t ∷s σ)
Ext {a} 𝒕 θ (zero)  = 𝒕
Ext {a} 𝒕 θ (suc x) = θ x

Rename : ∀ {n Δ Δ'} → (ρ : Ren Δ Δ') →
         ∀ {Γ}{σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C {n} σ) →
         ⟦ Γ ⟧C (ρ •s σ)
Rename ρ θ {a} x = ↿ SAT.satRename (⟦ a ⟧ _) ρ (⇃ θ x)

Map : ∀ {m n} → (m≤n : m ≤ℕ n) →
      ∀ {Γ Δ} {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C σ) → ⟦ Γ ⟧C σ
Map m≤n θ {a} x = map⟦ a ⟧∈ m≤n (θ x)

⟦∗⟧ : ∀ {n Γ}{a : Ty} {b∞} {t : Tm Γ (▸̂ ((delay (λ {_} → a)) ⇒ b∞))} {u : Tm Γ (▸ a)}
      → t ∈ (⟦ ▸̂ ((delay (λ {_} → a)) ⇒ b∞) ⟧ n) → u ∈ (⟦ ▸̂ (delay (λ {_} → a)) ⟧ n) → (t ∗ u) ∈ (⟦ ▸̂ b∞ ⟧ n)
⟦∗⟧ (↿ ▹0) (↿ ▹0)       = ↿ exp β▹ ▹0
⟦∗⟧ (↿ ▹0) (↿ ne 𝒏)     = ↿ (ne (elim 𝒏 (∗r ▹0)))
⟦∗⟧ (↿ ▹0) (↿ exp t⇒ 𝑡) = ↿ exp (cong (∗r _) (∗r _) t⇒) (⇃ ⟦∗⟧ (↿ ▹0) (↿ 𝑡))
⟦∗⟧ {a = a} {b∞ = b∞}  (↿ (▹ 𝑡)) (↿ (▹_ {t = u} 𝑢))
 =  ↿ exp β▹
     (▹ ≡.subst (λ t → SAT.satSet (⟦ force b∞ ⟧ _) (app t u))
          renId (out≤′ (force b∞) (≤⇒≤′ ≤ℕ.refl) (𝑡 _ ≤ℕ.refl id (in≤′ a (≤⇒≤′ ≤ℕ.refl) 𝑢))))
⟦∗⟧ {a = a} {b∞ = b∞}  (↿ (▹ 𝒕)) (↿ ne 𝒏) = ↿ ne (elim 𝒏 (∗r (▹ SAT.satSN (⟦ a ⟧≤ ⟦→⟧ ⟦ force b∞ ⟧≤) 𝒕)))
⟦∗⟧ (↿ (▹ 𝑡))    (↿ exp t⇒ 𝑢) = ↿ exp (cong (∗r _) (∗r _) t⇒) (⇃ ⟦∗⟧  (↿ (▹ 𝑡)) (↿ 𝑢))
⟦∗⟧ (↿ ne 𝒏)     (↿ 𝑡) = ↿ ne (elim 𝒏 (SAT.satSN (⟦ _ ⟧ _) 𝑡 ∗l))
⟦∗⟧ (↿ exp t⇒ 𝑡) (↿ 𝑢) = ↿ exp (cong (_ ∗l) (_ ∗l) t⇒) (⇃ ⟦∗⟧ (↿ 𝑡) (↿ 𝑢))


sound : ∀ {n a Γ} (t : Tm Γ a) {Δ} {σ : Subst Γ Δ} → (θ : ⟦ Γ ⟧C {n} σ) → subst σ t ∈ (⟦ a ⟧ n)
sound (var x) θ = θ x
sound (abs t) {σ = σ} θ = ⟦abs⟧ {𝓐 = ⟦ _ ⟧≤} {𝓑 = ⟦ _ ⟧≤} (λ l≤m ρ {u} 𝑢 →
  let open ≡-Reasoning
      eq : subst (u ∷s (ρ •s σ)) t ≡ subst0 u (subst (lifts ρ) (subst (lifts σ) t))
      eq = begin

             subst (u ∷s (ρ •s σ)) t

           ≡⟨ subst-ext (cons-to-sgs u _) t ⟩

              subst (sgs u •s lifts (ρ •s σ)) t

           ≡⟨ subst-∙ _ _ t ⟩

             subst0 u (subst (lifts (ρ •s σ)) t)

           ≡⟨ ≡.cong (subst0 u) (subst-ext (lifts-∙ ρ σ) t) ⟩

             subst0 u (subst (lifts ρ •s lifts σ) t)

           ≡⟨ ≡.cong (subst0 u) (subst-∙ (lifts ρ) (lifts σ) t) ⟩

             subst0 u (subst (lifts ρ) (subst (lifts σ) t))
           ∎
  in (≡.subst (λ tu → tu ∈⟨ l≤m ⟩ (⟦ _ ⟧≤)) eq (↿ in≤′ _ (≤⇒≤′ l≤m) (⇃ sound t (Ext (↿ out≤′ _ (≤⇒≤′ l≤m) (⇃ 𝑢)) ((Rename ρ (Map l≤m θ))))))))

sound {n} (app {a} {b} t u) θ = ↿ out≤′ b (≤⇒≤′ ≤ℕ.refl)
       (⇃ ⟦app⟧ {n} {𝓐 = ⟦ _ ⟧≤} {𝓑 = ⟦ _ ⟧≤} ≤ℕ.refl (sound t θ) (↿ in≤′ a (≤⇒≤′ ≤ℕ.refl) (⇃ sound u θ)))
sound (pair t u) θ = ⟦pair⟧ (sound t θ) (sound u θ)
sound (fst t)    θ = ⟦fst⟧ {𝓐 = ⟦ _ ⟧ _} {𝓑 = ⟦ _ ⟧ _} (sound t θ)
sound (snd t)    θ = ⟦snd⟧ {𝓐 = ⟦ _ ⟧ _} {𝓑 = ⟦ _ ⟧ _} (sound t θ)
sound (t ∗ u)    θ = ⟦∗⟧ (sound t θ) (sound u θ)
sound {zero}  (▹ t) θ = ↿ ▹0
sound {suc n} (▹ t) θ = ↿ (▹ (⇃ sound t (Map n≤sn θ)))
