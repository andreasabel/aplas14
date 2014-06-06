{-# OPTIONS --copatterns #-}

open import Library
open import SizedInfiniteTypes
open import Terms
open import AgdaExamples hiding (omega)

A∞ : ∀{i} → ∞Ty {i}
force A∞ = ▸̂ A∞
A = force A∞

T∞ : ∀{i} → ∞Ty {i}
force T∞ = ▸̂ (T∞ ⇒ A∞)
T = force T∞

omega : Tm [] (T →̂ A)
omega = abs (▸app (≅delay ≅refl)
             (var zero) (next (var zero)))

Omega : Tm [] A
Omega = app omega (next omega)
