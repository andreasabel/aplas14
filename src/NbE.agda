{-# OPTIONS --copatterns #-}
module NbE where

open import SizedInfiniteTypes
open import TermShape
open import Terms
open import Library
open import Data.Sum
open import Substitution
open import Size
mutual
  data Nf (Γ : Cxt) : Ty -> Set where
      abs  : ∀{a b}        (t : Nf (a ∷ Γ) b)        → Nf Γ (a →̂ b)
      pair : ∀{a b}        (t : Nf Γ a) (u : Nf Γ b) → Nf Γ (a ×̂ b)
      ▹_   : ∀{a∞}         (t : ∞Nf Γ (force a∞))    → Nf Γ (▸̂ a∞)
      ne   : ∀{a∞}         (t : Ne Γ (▸̂ a∞))         → Nf Γ (▸̂ a∞)

  data Ne : (Γ : Cxt) → Ty -> Set where
      --- blah

  record ∞Nf (Γ : Cxt) (a : Ty) : Set where
    coinductive
    -- the revenge of the musical notation
    constructor ♯_ 
    field
      ♭ : Nf Γ a

open ∞Nf

mutual
  wtf : ∀ {Γ} a → Nf Γ a
  wtf (a ×̂ a₁) = pair (wtf a) (wtf a₁)
  wtf (a →̂ a₁) = abs (wtf a₁)
  wtf (▸̂ a∞) = ▹ (∞wtf (force a∞))
  
  ∞wtf : ∀ {Γ} a → ∞Nf Γ a
  ♭ (∞wtf a) = wtf a 

  
mutual
  data Delay {i : Size} (a : Set) : Set where
     now : a → Delay a
     later : ∞Delay {i} a → Delay a
     
  record ∞Delay {i : Size} (a : Set) : Set where
    coinductive
    field
      force : ∀ {j : Size< i} → Delay {j} a

mutual
  data Dom {i : Size} : Ty → Set where
    pair : ∀ {a b} → Dom {i} a → Dom {i} b → Dom (a ×̂  b)
    abs : ∀ {Γ a b} → Tm (a ∷ Γ) b → Env {i} Γ → Dom (a →̂  b)
    ▹_ : ∀ {a∞ : ∞Ty} → ∞Dom {i} (force a∞) → Dom (▸̂  a∞)

  record ∞Dom {i : Size} (a : Ty) : Set where
    coinductive
    field
      force : ∀ {j : Size< i} → Delay (Dom {j} a)

  Env : {i : Size} → Cxt -> Set
  Env {i} Γ = ∀ {a} → Var Γ a → Dom {i} a 

-- Dom : Cxt → Ty → Set
-- Dom Γ (a ×̂ a₁) = Dom Γ a × Dom Γ a₁
-- Dom Γ (a →̂ a₁) = ∀ {Δ} → Δ ≤ Γ → Dom Δ a → Dom Δ a₁
-- Dom Γ (▸̂  a∞)  = {!!} -- Rec (♯ Dom Γ (force a∞))
--                 ⊎ Ne Γ (▸̂ a∞)

-- Env : Cxt -> Cxt -> Set
-- Env Δ Γ = ∀ {a} → Var Δ a → Dom Γ a 
mutual
  _>>=_ : ∀ {a b i} → Delay {i} a → (a → Delay {i} b) → Delay {i} b
  now x >>= f = f x
  later x >>= f = later (x ∞>>= f)
  
  _∞>>=_ : ∀ {a b i} → ∞Delay {i} a → (a → Delay {i} b) → ∞Delay {i} b
  ∞Delay.force (m ∞>>= f) = ∞Delay.force m >>= f  

mutual
  eval : ∀ {i j Γ a} → Tm Γ a → Env {i} Γ → Delay {j} (Dom {i} a)
  eval (var x)     env = now (env x)
  eval (abs t)     env = now (abs t env)
  eval (app t t₁)  env = eval t env >>= (λ f → eval t₁ env >>= (λ x → f $ x))
  eval (pair t t₁) env = {!!}
  eval (fst t)     env = {!!}
  eval (snd t)     env = {!!}
  eval (▹ t)       env = now (▹ eval▹ t env)
  eval (t ∗ t₁)    env = eval t env >>= (λ f → eval t₁ env >>= (λ x → f * x))

  eval▹ : ∀ {i Γ a} → Tm Γ a → Env {i} Γ → ∞Dom {i} a
  ∞Dom.force (eval▹ t env) = eval t env
  _$_ : ∀ {i j a a₁}
        (f : Dom {i} (a₁ →̂ a)) → Dom {i} a₁ → Delay {j} (Dom {i} a)
  abs t env $ x = later (∞$ t env x)

  ∞$ : ∀ {i j a a₁ Γ} →
     Tm (a₁ ∷ Γ) a →
     (Env {i} Γ) → Dom {i} a₁ → ∞Delay {j} (Dom {i} a)
  ∞Delay.force (∞$ t env x) = eval t (λ { {._} zero → x ; (suc v) → env v })

  _*_ : ∀ {i j} {a : Ty} {b∞} 
        (f : Dom {i} (▸̂ ((delay a) ⇒ b∞))) → (x : Dom {i} (▸ a))
           → Delay {j} (Dom {i} (▸̂ b∞))
  (▹ f) * (▹ x) = now (▹ (f ∞* x))
  _∞*_ : ∀ {i a b} →
       ∞Dom {i} (a →̂  b) → ∞Dom {i} a → ∞Dom {i} b
  ∞Dom.force (f ∞* x) = ∞Dom.force f >>= (λ f → ∞Dom.force x >>= \ x → f $ x)