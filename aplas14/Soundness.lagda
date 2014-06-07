\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}

-- Type interpretation and soundness of typing.

module Soundness where

open import Library
open import InfiniteTypes
open import Terms
open import Substitution
open import SN
open import AntiRename
open import SAT hiding (⟦abs⟧; ⟦app⟧; ⟦fst⟧; ⟦snd⟧)

-- Type interpretation
\end{code}
}
\begin{code}
⟦_⟧≤  : (a : Ty) {n : ℕ} → SAT≤ a n

⟦_⟧_  : (a : Ty) (n : ℕ) → SAT a n
⟦ a  →̂  b  ⟧  n  = ⟦ a ⟧≤ {n}  ⟦→⟧  ⟦ b ⟧≤ {n}
⟦ a  ×̂  b  ⟧  n  = ⟦ a ⟧ n     ⟦×⟧  ⟦ b ⟧ n
⟦ ▸̂ a∞     ⟧  n  = ⟦▸⟧ P n
  where
    P : ∀ n → SATpred (force a∞) n
    P zero     = _
    P (suc n)  = ⟦ force a∞ ⟧ n
\end{code}
\AgdaHide{
\begin{code}
-- _≤′_ is better suited for well-founded recursion.
⟦_⟧≤′ : (a : Ty) {n : ℕ} → ∀ {m} → m ≤′ n → SAT a m

⟦ a ⟧≤ m≤n = ⟦ a ⟧≤′ (≤⇒≤′ m≤n)

⟦_⟧≤′ a .{m}     {m} ≤′-refl           = ⟦ a ⟧ m
⟦_⟧≤′ a .{suc n} {m} (≤′-step {n} m≤n) = ⟦ a ⟧≤′ {n} m≤n
\end{code}
}
\begin{code}
in≤      : ∀ a {n m} (m≤n : m ≤ℕ n) → satSet (⟦ a ⟧ m) ⊆ satSet (⟦ a ⟧≤ m≤n)
out≤     : ∀ a {n m} (m≤n : m ≤ℕ n) → satSet (⟦ a ⟧≤ m≤n) ⊆ satSet (⟦ a ⟧ m)

coerce≤   :  ∀ a {n n' m} (m≤n : m ≤ℕ n) (m≤n' : m ≤ℕ n')
             → satSet (⟦ a ⟧≤ m≤n) ⊆ satSet (⟦ a ⟧≤ m≤n')
\end{code}

\AgdaHide{
\begin{code}

in≤′      : ∀ (a : Ty) {n m} (m≤n : m ≤′ n) → satSet (⟦ a ⟧ m) ⊆ satSet (⟦ a ⟧≤′ m≤n)
out≤′     : ∀ (a : Ty) {n m} (m≤n : m ≤′ n) → satSet (⟦ a ⟧≤′ m≤n) ⊆ satSet (⟦ a ⟧ m)

in≤  a m≤n 𝑡 = in≤′ a (≤⇒≤′ m≤n) 𝑡
out≤ a m≤n 𝑡 = out≤′ a (≤⇒≤′ m≤n) 𝑡

in≤′ a ≤′-refl       𝑡 = 𝑡
in≤′ a (≤′-step m≤n) 𝑡 = in≤′ a m≤n 𝑡

out≤′ a ≤′-refl       𝑡 = 𝑡
out≤′ a (≤′-step m≤n) 𝑡 = out≤′ a m≤n 𝑡

coerce≤ a ≤1 ≤2 𝑡 = in≤ a ≤2 (out≤ a ≤1 𝑡)
\end{code}
}

\begin{code}
map⟦_⟧ : ∀ a {m n} → m ≤ℕ n → satSet (⟦ a ⟧ n) ⊆ satSet (⟦ a ⟧ m)
\end{code}
\AgdaHide{
\begin{code}
map⟦_⟧ (a →̂ b) m≤n 𝑡                        = λ l l≤m ρ 𝑢 → let l≤n = ≤ℕ.trans l≤m m≤n in
                                                coerce≤ b l≤n l≤m (𝑡 l l≤n ρ (coerce≤ a l≤m l≤n 𝑢))
map⟦_⟧ (a ×̂ b) m≤n (t1 , t2)                = map⟦ a ⟧ m≤n t1 , map⟦ b ⟧ m≤n t2
map⟦_⟧ (▸̂ a∞) {m = zero}  m≤n next0         = next0
map⟦_⟧ (▸̂ a∞) {m = suc m} ()  next0
map⟦_⟧ (▸̂ a∞) {m = zero}  m≤n (next 𝒕)      = next0
map⟦_⟧ (▸̂ a∞) {m = suc m} m≤n (next 𝒕)      = next (map⟦ force a∞ ⟧ (pred≤ℕ m≤n) 𝒕)
map⟦_⟧ (▸̂ a∞)             m≤n (ne 𝒏)        = ne (mapSNe m≤n 𝒏)
map⟦_⟧ (▸̂ a∞)             m≤n (exp t⇒ 𝑡)    = exp (map⇒ m≤n t⇒) (map⟦ (▸̂ a∞) ⟧ m≤n 𝑡)

map⟦_⟧∈ : ∀ (a : Ty) → ∀ {m n} → (m ≤ℕ n) → ∀ {Γ} {t : Tm Γ a} → t ∈ (⟦ a ⟧ n)
                                            → t ∈ (⟦ a ⟧ m)
map⟦_⟧∈ a m≤n (↿ 𝑡) = ↿ map⟦ a ⟧ m≤n 𝑡
\end{code}
}

%%-- Context interpretation (semantic substitutions)
\begin{code}
⟦_⟧C : ∀ Γ {n} → ∀ {Δ} (σ : Subst Γ Δ) → Set
⟦ Γ ⟧C {n} σ = ∀ {a} (x : Var Γ a) → σ x ∈ ⟦ a ⟧ n

Ext :  ∀ {a n Δ Γ} {t : Tm Δ a} → (𝒕 : t ∈ ⟦ a ⟧ n) →
       ∀ {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C σ) → ⟦ a ∷ Γ ⟧C (t ∷s σ)
Ext {a} 𝒕 θ (zero)   = 𝒕
Ext {a} 𝒕 θ (suc x)  = θ x

Rename :  ∀ {n Δ Δ'} → (ρ : Ren Δ Δ') →
          ∀ {Γ}{σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C {n} σ) →
          ⟦ Γ ⟧C (ρ •s σ)
Rename ρ θ {a} x = ↿ SAT.satRename (⟦ a ⟧ _) ρ (⇃ θ x)

Map :  ∀ {m n} → (m≤n : m ≤ℕ n) →
       ∀ {Γ Δ} {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C σ) → ⟦ Γ ⟧C σ
Map m≤n θ {a} x = map⟦ a ⟧∈ m≤n (θ x)
\end{code}

\begin{code}
⟦∗⟧ : ∀ {n Γ}{a∞} {b∞} {t : Tm Γ (▸̂ (a∞ ⇒ b∞))} {u : Tm Γ (▸̂ a∞)}
      → t ∈ (⟦ ▸̂ (a∞ ⇒ b∞) ⟧ n) → u ∈ (⟦ ▸̂ a∞ ⟧ n) → (t ∗ u) ∈ (⟦ ▸̂ b∞ ⟧ n)
\end{code}
\AgdaHide{
\begin{code}
⟦∗⟧ (↿ next0) (↿ next0)    = ↿ exp β▸ next0
⟦∗⟧ (↿ next0) (↿ ne 𝒏)     = ↿ (ne (elim 𝒏 ((∗r next0))))
⟦∗⟧ (↿ next0) (↿ exp t⇒ 𝑡) = ↿ exp (cong (∗r _) (∗r _) t⇒) (⇃ ⟦∗⟧ (↿ next0) (↿ 𝑡))
⟦∗⟧ {a∞ = a∞} {b∞ = b∞}  (↿ (next 𝑡)) (↿ (next {t = u} 𝑢))
 =  ↿ exp β▸
     (next (≡.subst (λ t → satSet (⟦ force b∞ ⟧ _) (app t u))
          renId (out≤ (force b∞) ≤ℕ.refl (𝑡 _ ≤ℕ.refl id (in≤ (force a∞) ≤ℕ.refl 𝑢)))))
⟦∗⟧ {a∞ = a∞} {b∞ = b∞}  (↿ (next 𝒕)) (↿ ne 𝒏) = ↿ ne (elim 𝒏 (∗r next (satSN (⟦ force a∞ ⟧≤ ⟦→⟧ ⟦ force b∞ ⟧≤) 𝒕)))
⟦∗⟧ (↿ (next 𝑡))    (↿ exp t⇒ 𝑢) = ↿ exp (cong (∗r _) (∗r _) t⇒) (⇃ ⟦∗⟧  (↿ (next 𝑡)) (↿ 𝑢))
⟦∗⟧ (↿ ne 𝒏)     (↿ 𝑡) = ↿ ne (elim 𝒏 (satSN (⟦ _ ⟧ _) 𝑡 ∗l))
⟦∗⟧ (↿ exp t⇒ 𝑡) (↿ 𝑢) = ↿ exp (cong (_ ∗l) (_ ∗l) t⇒) (⇃ ⟦∗⟧ (↿ 𝑡) (↿ 𝑢))

-- versions specialized for sound
⟦abs⟧  :  ∀{n a b}(let 𝓐 = ⟦ a ⟧≤ {n})(let 𝓑 = ⟦ b ⟧≤ {n}){Γ Γ'}{t : Tm (a ∷ Γ') b} {σ : Subst Γ' Γ} →
          (∀ {m} (m≤n : m ≤ℕ n) {Δ} (ρ : Δ ≤ Γ) {u : Tm Δ a} →
              u ∈⟨ m≤n ⟩ 𝓐 → subst (u ∷s (ρ •s σ)) t ∈⟨ m≤n ⟩ 𝓑 ) → subst σ (abs t) ∈ (𝓐 ⟦→⟧ 𝓑)
(⇃ ⟦abs⟧ {t = t} {σ} 𝒕) m m≤n ρ {u} 𝒖 = SAT≤.satExp ⟦ _ ⟧≤ m≤n (β (SAT≤.satSN ⟦ _ ⟧≤ m≤n 𝒖))
                                        (≡.subst (λ tu → satSet (⟦ _ ⟧≤ m≤n) tu) eq (⇃ 𝒕 m≤n ρ (↿ 𝒖))) 
   where
      open ≡-Reasoning
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


⟦app⟧  :  ∀ {n a b} {Γ}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} →
          t ∈ ⟦ (a →̂ b) ⟧ n → u ∈ ⟦ a ⟧ n → app t u ∈ ⟦ b ⟧ n
⟦app⟧ {n} {a = a} {b = b} 𝑡 𝑢 = ↿ out≤ b ≤ℕ.refl
  (⇃ SAT.⟦app⟧ {n} {𝓐 = ⟦ _ ⟧≤} {𝓑 = ⟦ _ ⟧≤} ≤ℕ.refl 𝑡 (↿ in≤ a ≤ℕ.refl (⇃ 𝑢)))


⟦fst⟧   :   ∀ {n a b} {Γ} {t : Tm Γ (a ×̂  b)}
            → t ∈ ⟦ (a ×̂  b) ⟧ n → fst t ∈ ⟦ a ⟧ n
⟦fst⟧ = SAT.⟦fst⟧ {𝓐 = ⟦ _ ⟧ _} {𝓑 = ⟦ _ ⟧ _}

⟦snd⟧   :   ∀ {n a b} {Γ} {t : Tm Γ (a ×̂  b)}
            → t ∈ ⟦ (a ×̂  b) ⟧ n → snd t ∈ ⟦ b ⟧ n
⟦snd⟧ = SAT.⟦snd⟧ {𝓐 = ⟦ _ ⟧ _} {𝓑 = ⟦ _ ⟧ _}

\end{code}
}



\begin{code}
sound :  ∀ {n a Γ} (t : Tm Γ a) {Δ} {σ : Subst Γ Δ} → 
         (θ : ⟦ Γ ⟧C {n} σ) → subst σ t ∈ ⟦ a ⟧ n
sound (var x) θ = θ x
sound (abs t) θ = ⟦abs⟧ {t = t} λ m≤n ρ {u} 𝑢 →
    ↿ in≤ _ m≤n (⇃ sound t (Ext (↿ out≤ _ m≤n (⇃ 𝑢)) (Rename ρ (Map m≤n θ))))
sound (app t u)   θ  = ⟦app⟧ (sound t θ) (sound u θ)
sound (pair t u)  θ  = ⟦pair⟧ (sound t θ) (sound u θ)
sound (fst t)     θ  = ⟦fst⟧ (sound t θ) 
sound (snd t)     θ  = ⟦snd⟧ (sound t θ) 
sound (t ∗ u)     θ  = ⟦∗⟧ (sound t θ) (sound u θ)
sound {zero}  (next t) θ = ↿ next0
sound {suc n} (next t) θ = ↿ (next (⇃ sound t (Map n≤sn θ)))
\end{code}
