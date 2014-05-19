{-# OPTIONS --copatterns #-}
{-# OPTIONS --no-positivity-check #-}
module Model where

open import Size
open import Library

open import SizedInfiniteTypes
open import Terms

mutual
  data Dom {i : Size} : Ty → Set where
    pair : ∀ {a b} → Dom {i} a → Dom {i} b                       → Dom (a ×̂  b)
    abs  : ∀ {a b} → (∀ {j : Size< ↑ i} → Dom {j} a → Dom {j} b) → Dom (a →̂  b)
    ▹_   : ∀ {a∞}  → ∞Dom {i} (force a∞)                         → Dom (▸̂  a∞)

  record ∞Dom {i : Size} (a : Ty) : Set where
    coinductive
    field
      force : ∀ {j : Size< i} → Dom {j} a
      
Env : {i : Size} → Cxt → Set
Env {i} Γ = ∀ {a} → Var Γ a → Dom {i} a 

mutual
  mapDom : ∀ {a}{i}{j : Size< ↑ i} → Dom {i} a → Dom {j} a
  mapDom (pair x y) = pair (mapDom x) (mapDom y)
  mapDom (abs x)     = abs x 
  mapDom (▹ x)       = ▹ ∞mapDom x

  ∞mapDom : ∀ {a}{i}{j : Size< ↑ i} → ∞Dom {i} a → ∞Dom {j} a
  ∞Dom.force (∞mapDom x) = mapDom (∞Dom.force x)

coerce : ∀ {i a} → Dom {i} a → ∞Dom {i} a
∞Dom.force (coerce x) = mapDom x

_[app]_ : ∀ {i a b} → Dom {i} (a →̂ b) → Dom {i} a → Dom {i} b
abs f [app] x = f x

[fst] : ∀ {i a b} (p : Dom {i} (a ×̂ b)) → Dom {i} a
[fst] (pair x y) = x

[snd] : ∀ {i a b} (p : Dom {i} (a ×̂ b)) → Dom {i} b
[snd] (pair x y) = y

_∞[∗]_ : ∀ {i a b} → ∞Dom {i} (a →̂  b) → ∞Dom {i} a → ∞Dom {i} b
∞Dom.force (f ∞[∗] x) = ∞Dom.force f [app] ∞Dom.force x  

_[∗]_ : ∀ {i} {a : Ty} {b∞} → Dom {i} (▸̂ ((delay a) ⇒ b∞)) → Dom {i} (▸ a) → Dom {i} (▸̂ b∞)
▹ f [∗] ▹ x = ▹ (f ∞[∗] x)

eval : ∀ {i Γ a} → Tm Γ a → Env {i} Γ → Dom {i} a
eval (var x)     env = env x
eval (abs t)     env = abs λ x → eval t (λ { {._} zero → x ; (suc v) → mapDom (env v) })
eval (pair t t₁) env = pair (eval t env) (eval t₁ env)
eval (app t t₁)  env = eval t env [app] (eval t₁ env)
eval (fst t)     env = [fst] (eval t env)
eval (snd t)     env = [snd] (eval t env)
eval (▹ t)       env = ▹ coerce (eval t env)
eval (t ∗ t₁)    env = eval t env [∗] eval t₁ env

