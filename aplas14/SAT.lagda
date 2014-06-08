\AgdaHide{
\begin{code}
-- Saturated sets.

{-# OPTIONS --copatterns --sized-types #-}

module SAT where

open import Library
open import InfiniteTypes
open import Terms
open import Substitution
open import SN
open import AntiRename
open import IndRen
\end{code}
}

As a preliminary towards saturated sets we define sets of well-typed
terms in an arbitrary typing context but fixed type,
\AgdaFunction{TmSet} \AgdaBound{a}. We also define shorthands for set
inclusion and closure under reduction.
\begin{code}
TmSet : (a : Ty) → Set₁
TmSet a = {Γ : Cxt} (t : Tm Γ a) → Set

_⊆_ : ∀{a} (𝑨 𝑨′ : TmSet a) → Set
𝑨 ⊆ 𝑨′ = ∀{Γ}{t : Tm Γ _} → 𝑨 t → 𝑨′ t

Closed : ∀ (n : ℕ) {a} (𝑨 : TmSet a) → Set
Closed n 𝑨 = ∀{Γ}{t t' : Tm Γ _} → t ⟨ n ⟩⇒ t' → 𝑨 t' → 𝑨 t
\end{code}

For each type constructor we define a corresponding operation on
\AgdaFunction{TmSet}s.
The product is simply pointwise through the use of the projections.
\begin{code}
_[×]_ :  ∀{a b} → TmSet a → TmSet b → TmSet (a ×̂ b)
(𝓐 [×] 𝓑) t = 𝓐 (fst t) × 𝓑 (snd t)
\end{code}

For function types we are forced to use a Kripke-style definition,
quantifying over all possible extended contexts \AgdaBound{Δ} makes
\AgdaBound{𝓐} \AgdaFunction{[→]} \AgdaBound{𝓑} closed under renamings.
\begin{code}
_[→]_ : ∀{a b} → TmSet a → TmSet b → TmSet (a →̂ b)
(𝓐 [→] 𝓑) {Γ} t =
  ∀{Δ} (ρ : Δ ≤ Γ) → {u : Tm Δ _} → 𝓐 u → 𝓑 (app (rename ρ t) u)
\end{code}


The \AgdaFunction{TmSet} for the later modality is indexed by the
depth. The first two constructors are for terms in the canonical form
\anext{} \AgdaBound{t}, at depth \tzero{} we impose no restriction on
\AgdaBound{t}, otherwise we use the given set \AgdaBound{𝑨}.
The other two constructors are needed to satisfy the properties we
require of our saturated sets.
\begin{code}
data [▸] {a∞} (𝑨 : TmSet (force a∞)) {Γ} : (n : ℕ) → Tm Γ (▸̂ a∞) → Set where
  next0  :  ∀ {t : Tm Γ (force a∞)}
            → [▸] 𝑨  zero     (next t)
  next   :  ∀ {n}{t : Tm Γ (force a∞)}   (𝒕 : 𝑨 t)
            → [▸] 𝑨  (suc n)  (next t)
  ne     :  ∀ {n}{t : Tm Γ (▸̂ a∞)}      (𝒏 : SNe n t)
            → [▸] 𝑨  n        t
  exp    :  ∀ {n}{t t'  : Tm Γ (▸̂ a∞)}  (t⇒ : t ⟨ n ⟩⇒ t') (𝒕 : [▸] 𝑨 n t')
            → [▸] 𝑨  n        t
\end{code}


The particularity of our saturated sets is that they are indexed by
the depth, which in our case is needed to state the usual properties.
In particular if a term belongs to a saturated set it is also a member
of \AgdaFunction{SN}, which is what we need for strong normalization.
In addition we require them to be closed under renaming, since we are
dealing with terms in a context.
\begin{code}
record IsSAT (n : ℕ) {a} (𝑨 : TmSet a) : Set where
  field
    satSNe     : SNe n ⊆ 𝑨
    satSN      : 𝑨 ⊆ SN n
    satExp     : Closed n 𝑨
    satRename  :  ∀ {Γ Δ} → (ρ : Δ ≤ Γ) → 
                  ∀ {t} → 𝑨 t → 𝑨 (rename ρ t)

record SAT (a : Ty) (n : ℕ) : Set₁ where
  field
    satSet   : TmSet a
    satProp  : IsSAT n satSet
\end{code}
\AgdaHide{
\begin{code}
  open IsSAT satProp public
open SAT public
\end{code}
}

For function types we will also need a notion of a sequence of
saturated sets up to a specified upper bound.
\begin{code}
SAT≤ : (a : Ty) (n : ℕ) → Set₁
SAT≤ a n = ∀ {m} → m ≤ℕ n → SAT a m
\end{code}

\AgdaHide{
\begin{code}
module SAT≤ {a : Ty} {n : ℕ} (𝓐 : SAT≤ a n) {m} (m≤n : m ≤ℕ _) where
  open SAT (𝓐 m≤n) public
\end{code}
}

To help Agda's type inference we also define a record type for
membership of a term into a saturated set.
\AgdaHide{
\begin{code}
-- Elementhood for saturated sets.
-- We use a record to instead of just application to help Agda's unifier.
\end{code}
}
\begin{code}
record _∈_ {a n Γ} (t : Tm Γ a) (𝓐 : SAT a n) : Set where
  constructor ↿_
  field       ⇃_ : satSet 𝓐 t

_∈⟨_⟩_ : ∀ {a n Γ} (t : Tm Γ a) {m} (m≤n : m ≤ℕ n) (𝓐 : SAT≤ a n) → Set
t ∈⟨ m≤n ⟩ 𝓐 = t ∈ 𝓐 m≤n
\end{code}
\AgdaHide{
\begin{code}
open _∈_ public
\end{code}
}

Given the lemmas about \AgdaFunction{SN} shown so far we can lift our
operations on \AgdaFunction{TmSet} to saturated sets and give the
semantic version of our term constructors.

For function types we need another level of Kripke-style
generalization to smaller depths, so that we can maintain antitonicity.
\begin{code}
_⟦→⟧_ : ∀ {n a b} (𝓐 : SAT≤ a n) (𝓑 : SAT≤ b n) → SAT (a →̂ b) n
𝓐 ⟦→⟧ 𝓑 = record
  { satSet  = 𝑪
  -- ...
\end{code}
\AgdaHide{
\begin{code}
  ; satProp = record
    { satSNe = CSNe
    ; satSN  = CSN
    ; satExp = CExp
    ; satRename = λ ρ {t} 𝒕 m m≤n ρ' {u} 𝒖 →
                    ≡.subst (λ t₁ → 𝑩 {m} m≤n (app t₁ u)) (subst-∙ ρ' ρ t)
                    (𝒕 m m≤n (ρ' •s ρ) 𝒖)
    }
  }
\end{code}
}
\begin{code}
  where
    module 𝓐 = SAT≤ 𝓐
    module 𝓑 = SAT≤ 𝓑
    𝑨 = 𝓐.satSet
    𝑩 = 𝓑.satSet

    𝑪 : TmSet (_ →̂ _)
    𝑪 t = ∀ m (m≤n : m ≤ℕ _) → (𝑨 m≤n [→] 𝑩 m≤n) t

    CSN : 𝑪 ⊆ SN _
    CSN 𝒕 =  unRenameSN (prop→Ind suc ≡.refl) (absVarSN
             (𝓑.satSN ≤ℕ.refl (𝒕 _ ≤ℕ.refl suc (𝓐.satSNe ≤ℕ.refl (var zero)))))
\end{code}

The proof of inclusion into \af{SN} first derives that \aic{app}
(\af{rename} \aic{suc} \ab{t}) (\aic{var} \aic{zero}) is in \af{SN}
through the inclusion of neutral terms into \ab{𝓐} and the inclusion
of \ab{𝓑} into \af{SN}, then proceeds to strip away first (\aic{var}
\aic{zero}) and then (\af{rename} \aic{suc}), so that we are left with
the original goal \af{SN} \ab{n} \ab{t}.  Renaming \ab{t} with
\aic{suc} is necessary to be able to introduce the fresh variable
\aic{zero} of type \ab{a}.

\AgdaHide{
\begin{code}
    CSNe : SNe _ ⊆ 𝑪
    CSNe 𝒏 m m≤n ρ 𝒖 =
         𝓑.satSNe m≤n (sneApp (mapSNe m≤n (renameSNe ρ 𝒏)) (𝓐.satSN m≤n 𝒖))

    CExp : ∀{Γ}{t t' : Tm Γ _} → t ⟨ _ ⟩⇒ t' → 𝑪 t' → 𝑪 t
    CExp t⇒ 𝒕 m m≤n ρ 𝒖 = 
       𝓑.satExp m≤n ((cong (appl _) (appl _) (map⇒ m≤n (rename⇒ ρ t⇒)))) (𝒕 m m≤n ρ 𝒖)
\end{code}
}

The types of semantic abstraction and application are somewhat
obfuscated because they need to mention the upper bounds and the
renamings.

\begin{code}
⟦abs⟧  :  ∀ {n a b} {𝓐 : SAT≤ a n} {𝓑 : SAT≤ b n} {Γ} {t : Tm (a ∷ Γ) b} →
          (∀ {m} (m≤n : m ≤ℕ n) {Δ} (ρ : Δ ≤ Γ) {u : Tm Δ a} →
              u ∈⟨ m≤n ⟩ 𝓐 → (subst0 u (subst (lifts ρ) t)) ∈⟨ m≤n ⟩ 𝓑 ) → abs t ∈ (𝓐 ⟦→⟧ 𝓑)
(⇃ ⟦abs⟧ {𝓐 = 𝓐}{𝓑 = 𝓑} 𝒕) m m≤n ρ 𝒖 =  
  SAT≤.satExp 𝓑 m≤n (β (SAT≤.satSN 𝓐 m≤n 𝒖)) (⇃ 𝒕 m≤n ρ (↿ 𝒖)) 

⟦app⟧  :  ∀ {n a b}{𝓐 : SAT≤ a n}{𝓑 : SAT≤ b n}{Γ}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} →
          t ∈ (𝓐 ⟦→⟧ 𝓑) → u ∈⟨ ≤ℕ.refl ⟩ 𝓐 → app t u ∈⟨ ≤ℕ.refl ⟩ 𝓑
⟦app⟧ {𝓑 = 𝓑} {u = u} (↿ 𝒕) (↿ 𝒖) = ≡.subst (λ t → app t u ∈⟨ ≤ℕ.refl ⟩ 𝓑) renId (↿ 𝒕 _ ≤ℕ.refl id 𝒖)
\end{code}

The \af{TmSet} for product types is directly saturated, inclusion into
\af{SN} uses \af{fromFstSN} to derive \af{SN} \ab{n} \ab{t} from the
membership into \af{SN} of \aic{fst} \ab{t}, which follows from the
inclusion of \ab \ab{𝓐} into \af{SN}.
\begin{code}
_⟦×⟧_ : ∀ {n a b} (𝓐 : SAT a n) (𝓑 : SAT b n) → SAT (a ×̂ b) n
𝓐 ⟦×⟧ 𝓑 = record
  { satSet   = satSet 𝓐 [×] satSet 𝓑
  -- ...
\end{code}
\AgdaHide{
\begin{code}
  ; satProp  = record
    { satSNe = CSNe
    ; satSN = CSN
    ; satExp = CExp
    ; satRename = λ ρ x → satRename 𝓐 ρ (proj₁ x) , satRename 𝓑 ρ (proj₂ x)
    }
  }
  where
    𝑨 = satSet 𝓐
    𝑩 = satSet 𝓑
    𝑪 : TmSet _
    𝑪 = 𝑨 [×] 𝑩

    CSNe : SNe _ ⊆ 𝑪
    CSNe 𝒏  =  satSNe 𝓐 (elim 𝒏 fst)
            ,  satSNe 𝓑 (elim 𝒏 snd)

    CSN : 𝑪 ⊆ SN _
    CSN (𝒕 , 𝒖) = bothProjSN (satSN 𝓐 𝒕) (satSN 𝓑 𝒖)

    CExp : ∀{Γ}{t t' : Tm Γ _} → t ⟨ _ ⟩⇒ t' → 𝑪 t' → 𝑪 t
    CExp t⇒ (𝒕 , 𝒖)  =  satExp 𝓐 (cong fst fst t⇒) 𝒕
                     ,  satExp 𝓑 (cong snd snd t⇒) 𝒖
\end{code}
}

\begin{code}
⟦pair⟧  :   ∀ {n a b} {𝓐 : SAT a n} {𝓑 : SAT b n} {Γ} {t₁ : Tm Γ a} {t₂ : Tm Γ b}
            → t₁ ∈ 𝓐 → t₂ ∈ 𝓑 → pair t₁ t₂ ∈ (𝓐 ⟦×⟧ 𝓑)
⇃ ⟦pair⟧ {𝓐 = 𝓐} {𝓑 = 𝓑} (↿ 𝒕) (↿ 𝒖)  =  satExp 𝓐 (βfst (satSN 𝓑 𝒖)) 𝒕 
                                      ,  satExp 𝓑 (βsnd (satSN 𝓐 𝒕)) 𝒖

⟦fst⟧   :   ∀ {n a b} {𝓐 : SAT a n} {𝓑 : SAT b n} {Γ} {t : Tm Γ (a ×̂ b)}
            → t ∈ (𝓐 ⟦×⟧ 𝓑) → fst t ∈ 𝓐
⟦fst⟧ 𝒕 =  ↿ (proj₁ (⇃ 𝒕))

⟦snd⟧   :   ∀ {n a b} {𝓐 : SAT a n} {𝓑 : SAT b n} {Γ} {t : Tm Γ (a ×̂ b)}
            → t ∈ (𝓐 ⟦×⟧ 𝓑) → snd t ∈ 𝓑
⟦snd⟧ 𝒕 =  ↿ (proj₂ (⇃ 𝒕))
\end{code}




The later modality is going to use the saturated set for its type
argument at the preceeding depth, we encode this fact through the type
\AgdaFunction{SATpred}.
\begin{code}
SATpred : (a : Ty) (n : ℕ) → Set₁
SATpred a zero     = ⊤
SATpred a (suc n)  = SAT a n

SATpredSet : {n : ℕ}{a : Ty} → SATpred a n → TmSet a
SATpredSet {zero}   𝓐   = λ _ → ⊤
SATpredSet {suc n}  𝓐   = satSet 𝓐
\end{code}

Since the cases for \af{[▸]\_} are essentially a subset of those for
\af{SN}, the proof of inclusion into \af{SN} goes by induction and the
inclusion of \ab{𝓐} into \af{SN}.
\begin{code}
module _ {a∞ : ∞Ty} where
  private
    a = force a∞

    𝑪 : ∀ {n} (𝓐 : SATpred a n) → TmSet (▸̂ a∞)
    𝑪 {n} 𝓐 = [▸] (SATpredSet 𝓐) n

    CSN : ∀ {n} (𝓐 : SATpred a n) → 𝑪 {n} 𝓐 ⊆ SN n
    CSN 𝓐 next0         = next0
    CSN 𝓐 (next 𝒕)      = next (satSN 𝓐 𝒕)
    CSN 𝓐 (ne 𝒏)        = ne 𝒏
    CSN 𝓐 (exp t⇒ 𝒕)    = exp t⇒ (CSN 𝓐 𝒕)

    CRen :  ∀ {n} (𝓐 : SATpred a n) → ∀ {Γ Δ} (ρ : Γ ≤ Δ) → 
            ∀ {t} → 𝑪 {n} 𝓐 t → 𝑪 {n} 𝓐 (subst ρ t)
    CRen 𝓐 ρ next0         = next0
    CRen 𝓐 ρ (next 𝒕)      = next (satRename 𝓐 ρ 𝒕)
    CRen 𝓐 ρ (ne 𝒏)        = ne (renameSNe ρ 𝒏)
    CRen 𝓐 ρ (exp t⇒ 𝒕)    = exp (rename⇒ ρ t⇒) (CRen 𝓐 ρ 𝒕)

  ⟦▸⟧_ : ∀{n} (𝓐 : SATpred a n) → SAT (▸̂ a∞) n
  ⟦▸⟧_ {n} 𝓐 = record
    { satSet = [▸] (SATpredSet 𝓐) n
    ; satProp = record
      { satSNe = ne
      ; satSN  = CSN 𝓐
      ; satExp = exp
      ; satRename = CRen 𝓐
      }
    }
\end{code}