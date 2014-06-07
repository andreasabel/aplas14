{-# OPTIONS --copatterns --sized-types #-}

module Examples where

open import Library
open import SizedInfiniteTypes
open import Terms


-- * Examples
------------------------------------------------------------------------

-- Example: fixed-point combinator

Fix_ : Ty → ∞Ty
force Fix A = ▸̂ Fix A →̂ A

selfApp : ∀{Γ A} → Tm Γ (▸̂ Fix A) → Tm Γ (▸ A)
selfApp x = ▹app (≅delay ≅refl) x (▹ x)

Y : ∀{Γ A} → Tm Γ ((▸ A →̂ A) →̂ A)
Y = abs (app L (▹ L))
  where
    f = var (suc v₀)
    x = var v₀
    L = abs (app f (selfApp x))

-- Alternative definition of selfApp

Fix∞_ : ∞Ty → ∞Ty
force Fix∞ A = ▸̂ Fix∞ A →̂ force A

selfApp' : ∀{Γ a∞} → Tm Γ (▸̂ Fix∞ a∞) → Tm Γ (▸̂ a∞)
selfApp' x = ▹app (≅delay ≅refl) x (▹ x)

-- Y' : ∀{Γ}{a∞ : ∞Ty {∞}} → Tm Γ ((▸̂ a∞ →̂ force a∞) →̂ force a∞)
-- Y' = abs {!(app L {!(▹ L)!})!}
--   where L = abs (app (var (suc zero)) (selfApp (var zero)))

-- Example: Streams

mutual
  Stream : Ty → Ty
  Stream A = A ×̂ ▸̂ Stream∞ A

  Stream∞ : Ty → ∞Ty
  force (Stream∞ A) = Stream A

-- Stream constructor

cons : ∀{Γ A} → Tm Γ A → Tm Γ (▸ Stream A) → Tm Γ (Stream A)
cons a s = pair a (cast (▸̂ (≅delay ≅refl)) s)

head : ∀{Γ A} → Tm Γ (Stream A) → Tm Γ A
head s = fst s

tail : ∀{Γ A} → Tm Γ (Stream A) → Tm Γ (▸ Stream A)
tail s = cast (▸̂ (≅delay ≅refl)) (snd s)

-- repeat a = (a , ▹ repeat a)
-- repeat = λ a → Y λ f → cons a f

repeat : ∀{Γ A} → Tm Γ (A →̂ Stream A)
repeat = abs (app Y (abs (cons (var (suc v₀)) (var v₀))))

-- smap f s = cons (f (head s)) (smap f (tail s))
-- smap = λ f → Y λ map → λ s → (f (head s), map <*> tail s)

smap : ∀{Γ A B} → Tm Γ ((A →̂ B) →̂ (Stream A →̂ Stream B))
smap = abs (app Y (abs (abs
  (let f   = var (suc (suc v₀))
       map = var (suc v₀)
       s   = var v₀
   in pair (app f (head s)) (▹app (≅delay ≅refl) map (tail s))))))

-- zipWith f s t = cons (f (head s) (head t)) (zipWith f (tail s) (tail t))
-- zipWith = λ f → Y λ zipWith → λ s t →
--   (f (head s) (head t) , zipWith <*> tail s <*> tail t)

zipWith : ∀{Γ A B C} → Tm Γ ((A →̂ (B →̂ C)) →̂ (Stream A →̂ (Stream B →̂ Stream C)))
zipWith = abs (app Y (abs (abs (abs
  (let f   = var (suc (suc (suc v₀)))
       zw  = var (suc (suc v₀))
       s   = var (suc v₀)
       t   = var v₀
   in pair (app (app f (head s)) (head t))
           (▹app {c∞ = Stream∞ _ ⇒ Stream∞ _} (≅delay ≅refl)
                 (▹app (≅delay ≅refl) zw (tail s))
                 (tail t)))))))

-- Fibonacci stream

module Fib (N : Ty) (n0 n1 : ∀{Γ} → Tm Γ N) (plus : ∀{Γ} → Tm Γ (N →̂ (N →̂  N))) where

  -- fib = Y λ fib → cons n0 (▹ (cons n1
  --   (zipWith plus <$> fib <*> (tail <$> fib)))) -- Ill-typed!
  --
  -- fib = Y λ fib → cons n0 (cons n1 <$>
  --   ((λ s → (zipWith plus <$> fib) <*> s) <$> (tail <$> fib)))

  fib : ∀{Γ} → Tm Γ (Stream N)
  fib {Γ} = app Y (abs
    (let fib  : Tm (_ ∷ Γ) (▸ Stream N)
         fib  = var v₀
         fib₁  : Tm (_ ∷ _ ∷ Γ) (▸ Stream N)
         fib₁  = var (suc v₀)
         adds : Tm (_ ∷ _ ∷ Γ) (Stream N →̂ (Stream N →̂ Stream N))
         adds = app zipWith plus
         addf :  Tm (_ ∷ _ ∷ Γ) (▸ (Stream N →̂ Stream N))
         addf = adds <$> fib₁
         tf   : Tm (_ ∷ Γ) (▸ ▸ Stream N)
         tf   = abs (tail (var v₀)) <$> fib
         aftf : Tm (_ ∷ Γ) (▸ ▸ Stream N)
         aftf = abs (▹app (≅delay ≅refl) addf (var v₀)) <$> tf
     in  cons n0 (abs (cons n1 (var v₀)) <$> aftf)))
