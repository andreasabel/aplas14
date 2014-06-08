\AgdaHide{
\begin{code}
module ECxtList where

open import Size
open import Library
open import InfiniteTypes
open import Terms
open import Substitution
open import TermShape


\end{code}
}

\begin{code}
_[_]    : ∀ {Γ} {a b} (E : ECxt Γ a b) (t : Tm Γ a) → Tm Γ b

data ECxt* (Γ : Cxt) : Ty → Ty → Set where
  [] : ∀ {a} → ECxt* Γ a a
  _∷_ : ∀ {a₀ a₁ a₂} → ECxt Γ a₀ a₁ → ECxt* Γ a₁ a₂ → ECxt* Γ a₀ a₂

_[_]*   : ∀ {Γ} {a b} (E : ECxt* Γ a b) (t : Tm Γ a) → Tm Γ b

_[_]⇒*  :  ∀ {Γ} {P : ∀{c} → Tm Γ c → Set} {a b} (E : ECxt* Γ a b) {t₁ t₂ : Tm Γ a} →
           P / t₁ ⇒ t₂ → P / E [ t₁ ]* ⇒ E [ t₂ ]*
\end{code}


\AgdaHide{
\begin{code}
E [ t ] = proj₁ (mkEHole E {t})

[] [ t ]* = t
(E ∷ Es) [ t ]* = Es [ E [ t ] ]*

_++*_ : ∀ {Γ a b c} → ECxt* Γ a b → ECxt* Γ b c → ECxt* Γ a c
[] ++* ys = ys
(x ∷ xs) ++* ys = x ∷ (xs ++* ys)

_∷r_ : ∀ {Γ a b c} → ECxt* Γ a b → ECxt Γ b c → ECxt* Γ a c
xs ∷r x = xs ++* (x ∷ [])

data Ehole* {Γ : Cxt} : {a b : Ty} → Tm Γ b → ECxt* Γ a b → Tm Γ a → Set where
  [] : ∀ {a} {t : Tm Γ a} → Ehole* t [] t
  _∷_ : ∀ {a b c t} {E : ECxt Γ b c} {Es : ECxt* Γ a b} {EEst Est}
        → Ehole EEst E Est → Ehole* Est Es t → Ehole* EEst (Es ∷r E) t

_[_]⇒ : ∀ {Γ} {P : ∀{c} → Tm Γ c → Set} {a b} (E : ECxt Γ a b) {t₁ t₂ : Tm Γ a} → P / t₁ ⇒ t₂ → P / E [ t₁ ] ⇒ E [ t₂ ]
E [ t⇒ ]⇒ = cong (proj₂ (mkEHole E)) (proj₂ (mkEHole E)) t⇒

[]       [ t⇒ ]⇒* = t⇒
(E ∷ Es) [ t⇒ ]⇒* = Es [ E [ t⇒ ]⇒ ]⇒*

hole→≡ : ∀ {Γ a b}{Et t}{E : ECxt Γ a b} → (Es : Ehole Et E t) → Et ≡ E [ t ]
hole→≡ (appl u) = ≡.refl
hole→≡ fst = ≡.refl
hole→≡ snd = ≡.refl
hole→≡ (∗l u) = ≡.refl
hole→≡ (∗r t₁) = ≡.refl

lemma : ∀ {Γ b} {a} {t : Tm Γ a} (Es : ECxt* Γ a b)
         {b₁} {E : ECxt Γ b b₁}
         → E [ Es [ t ]* ] ≡ (Es ++* (E ∷ [])) [ t ]*
lemma [] = ≡.refl
lemma (x ∷ Es) = lemma Es

hole*→≡ : ∀ {Γ a b}{Et t}{E : ECxt* Γ a b} → (Es : Ehole* Et E t) → Et ≡ E [ t ]*
hole*→≡ [] = ≡.refl
hole*→≡ {t = t} (_∷_ {Es = Es} x Es₁) rewrite hole→≡ x | hole*→≡ Es₁ = lemma Es

++*-unit : ∀ {Γ a b} → (xs : ECxt* Γ a b) → xs ++* [] ≡ xs
++*-unit [] = ≡.refl
++*-unit (x ∷ xs) = ≡.cong (_∷_ x) (++*-unit xs)
++*-assoc : ∀ {Γ a b c d} → (xs : ECxt* Γ a b) → {ys : ECxt* Γ b c} → {zs : ECxt* Γ c d} → xs ++* (ys ++* zs) ≡ (xs ++* ys) ++* zs
++*-assoc [] = ≡.refl
++*-assoc (x ∷ xs) = ≡.cong (_∷_ x) (++*-assoc xs)

_++h*_ : ∀ {Γ a b c} {Es1 : ECxt* Γ a b} {Es2 : ECxt* Γ b c} → ∀ {t1 t2 t3} → Ehole* t2 Es1 t3 → Ehole* t1 Es2 t2  → Ehole* t1 (Es1 ++* Es2) t3
_++h*_ {Es1 = Es1} xs [] rewrite ++*-unit Es1      = xs
_++h*_ {Es1 = Es1} xs (_∷_ {E = E} {Es = Es} x ys) rewrite ++*-assoc Es1 {Es} {E ∷ []} = x ∷ (xs ++h* ys)


mkEhole* : ∀ {Γ} {a b} (E : ECxt* Γ a b) {t} → Ehole* (E [ t ]*) E t
mkEhole* [] = []
mkEhole* (E ∷ Es) {t} = (proj₂ (mkEHole E) ∷ []) ++h* mkEhole* Es
\end{code}
}
