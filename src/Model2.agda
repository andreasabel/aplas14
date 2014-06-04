{-# OPTIONS --copatterns #-}
module Model2 where

open import Library hiding (Size)

open import SizedInfiniteTypes
open import Terms
open import Data.Nat

≤′-trans : ∀ {m n o} -> m ≤′ n → n ≤′ o -> m ≤′ o
≤′-trans m≤n ≤′-refl = m≤n
≤′-trans m≤n (≤′-step m≤′n) = ≤′-step (≤′-trans m≤n m≤′n)

Size = ℕ

-- Defining Dom by well-founded recursion.
-- Would be nice to use sized types for this but I failed. -- Andrea
--
-- We need the well-founded kind of recursion because of the kripke
-- construction for arrow types.
-- This should be the same phenomenon we get for our SAT model.
--
-- Then, inspired by the sized types version in Model.agda, we reuse
-- well-founded recursion to have a more uniform interpretation of ▸̂̂
-- in ∞Dom.
mutual
  Dom : ∀ {n : Size} → Ty -> Set
  Dom {n} (a ×̂ b) = Dom {n} a × Dom {n} b
  Dom {n} (a →̂ b) = ∀ {m} (m≤n : m ≤′ n) → Dom≤ m≤n a → Dom≤ m≤n b
  Dom {n} (▸̂ a∞)  = ∞Dom {n} (force a∞) 

  ∞Dom : ∀ {n : Size} → Ty -> Set
  ∞Dom {n} a = ∀ {m} → (m<n : m <′ n) → Dom< m<n a

  Dom≤ : ∀ {n m} → m ≤′ n -> Ty -> Set
  Dom≤ {.m} {m} ≤′-refl     t = Dom {m} t
  Dom≤         (≤′-step le) t = Dom≤ le t

  Dom< : ∀ {n m} → m <′ n -> Ty -> Set
  Dom< {m = m} ≤′-refl t = Dom {m} t
  Dom< (≤′-step le) t = Dom< le t

-- Dom< and Dom≤ are isomorphic to Dom
in< : ∀ {a}{i}{j} → (j<i : j <′ i) → Dom {j} a → Dom< j<i a
in< {a} ≤′-refl       d = d
in< {a} (≤′-step j<i) d = in< {a} j<i d

out< : ∀ {a}{i}{j} → (j≤i : j <′ i) → Dom< j≤i a → Dom {j} a
out< {a} ≤′-refl       d = d
out< {a} (≤′-step j≤i) d = out< {a} j≤i d

in≤ : ∀ {a}{i}{j} → (j≤i : j ≤′ i) → Dom {j} a → Dom≤ j≤i a
in≤ {a} ≤′-refl       d = d
in≤ {a} (≤′-step j≤i) d = in≤ {a} j≤i d

out≤ : ∀ {a}{i}{j} → (j≤i : j ≤′ i) → Dom≤ j≤i a → Dom {j} a
out≤ {a} ≤′-refl       d = d
out≤ {a} (≤′-step j≤i) d = out≤ {a} j≤i d


-- For both Dom< and Dom≤ only the smaller Size matters, the other is just a bound.
Dom≤-irr : ∀ {n n' m} → (m≤n : m ≤′ n) (m≤n' : m ≤′ n') → ∀ {a} →  Dom≤ m≤n a → Dom≤ m≤n' a
Dom≤-irr m≤n m≤n' d = in≤ m≤n' (out≤ m≤n d)

Dom<-irr : ∀ {n n' m} → (m<n : m <′ n) (m<n' : m <′ n') → ∀ {a} →  Dom< m<n a → Dom< m<n' a
Dom<-irr m<n m<n' d = in< m<n' (out< m<n d)


-- Dom as a covariant functor on Size
mapDom : ∀ {a}{i}{j} → j ≤′ i → Dom {i} a → Dom {j} a
mapDom {a ×̂ b} j≤i (x , y) = mapDom {a} j≤i x , mapDom {b} j≤i y
mapDom {a →̂ b} j≤i f       = λ le x → Dom≤-irr (≤′-trans le j≤i) le (f (≤′-trans le j≤i) (Dom≤-irr le (≤′-trans le j≤i) x))
mapDom {▸̂ b}   j≤i thunk   = λ {m} m<n → Dom<-irr (≤′-trans m<n j≤i) m<n (thunk (≤′-trans m<n j≤i))


coerce : ∀ {i a} → Dom {i} a → ∞Dom {i} a
coerce {i} {a} x = λ m<n → in< m<n (mapDom {a} (≤′-trans (≤′-step ≤′-refl) m<n) x)


-- Interpreter

Env : {i : Size} → Cxt → Set
Env {i} Γ = ∀ {a} → Var Γ a → Dom {i} a 

_[app]_ : ∀ {i a b} → Dom {i} (a →̂ b) → Dom {i} a → Dom {i} b
f [app] x = f ≤′-refl x

[fst] : ∀ {i a b} (p : Dom {i} (a ×̂ b)) → Dom {i} a
[fst] (x , y) = x

[snd] : ∀ {i a b} (p : Dom {i} (a ×̂ b)) → Dom {i} b
[snd] (x , y) = y

_∞[∗]_ : ∀ {i a b} → ∞Dom {i} (a →̂  b) → ∞Dom {i} a → ∞Dom {i} b
(f ∞[∗] x) m<n = in< m<n (out< m<n (f m<n) [app] out< m<n (x m<n))

_[∗]_ : ∀ {i} {a : Ty} {b∞} → Dom {i} (▸̂ ((delay a) ⇒ b∞)) → Dom {i} (▸ a) → Dom {i} (▸̂ b∞)
f [∗] x = f ∞[∗] x

eval : ∀ {i Γ a} → Tm Γ a → Env {i} Γ → Dom {i} a
eval (var x)         env = env x
eval (abs t)         env = λ m≤n x → in≤ m≤n (eval t (λ { {._} zero → out≤ m≤n x ; {a} (suc v) → mapDom {a} m≤n (env v) }))
eval (pair t t₁)     env = eval t env , eval t₁ env
eval (app t t₁)      env = eval t env [app] (eval t₁ env)
eval (fst {a} {b} t) env = [fst] {a = a} {b} (eval t env)
eval (snd {a} {b} t) env = [snd] {a = a} {b} (eval t env)
eval (▹ t)           env = coerce (eval t env)
eval (t ∗ t₁)        env = eval t env ∞[∗] eval t₁ env

