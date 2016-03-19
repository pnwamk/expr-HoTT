{-# OPTIONS --without-K #-}
module hw2 where

open import Level using (_⊔_)
open import Function using (id)
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import Level

infix 4 _≡_

recℕ : ∀ {ℓ} → (C : Set ℓ) → C → (ℕ → C → C) → ℕ → C
recℕ C z f 0 = z
recℕ C z f (suc n) = f n (recℕ C z f n)

indℕ : ∀ {ℓ}
         → (C : ℕ → Set ℓ)
         → C 0
         → ((n : ℕ) → C n → C (suc n))
         → (n : ℕ)
         → C n
indℕ C z f 0 = z
indℕ C z f (suc n) = f n (indℕ C z f n)

------------------------------------------------------------------------------
-- ≡
data _≡_ {ℓ} {A : Set ℓ} : (x y : A) → Set ℓ where
  refl : (x : A) → x ≡ x

rec≡ : {A : Set} →
       (R : A → A → Set) {reflexiveR : {a : A} → R a a} →
       ({x y : A} (p : x ≡ y) → R x y)
rec≡ R {reflR} (refl y) = reflR {y}

------------------------------------------------------------------------------
-- subst
subst : ∀ {ℓ} {A : Set ℓ} {C : A → Set ℓ} →
        ({x y : A} (p : x ≡ y) → C x → C y)
subst (refl x) = id

------------------------------------------------------------------------------
-- ∘ 
_∘_ : {A B C : Set} → (f : B → C) → (g : A → B) → A → C
f ∘ g = (λ a → f (g a))


module Circle1 where
  private
    data S¹* : Set where
      base* : S¹*

  S¹ : Set
  S¹ = S¹*

  base : S¹
  base = base*

  postulate
    loop : base ≡ base

  recS¹ : {C : Set} → (cbase : C) → (cloop : cbase ≡ cbase) → S¹ → C
  recS¹ cbase cloop base* = cbase


--  postulate
--    βrecS¹ : {C : Set} → (cbase : C) → (cloop : cbase ≡ cbase)
--      → ap (recS¹ cbase cloop) loop ≡ cloop


-- indS¹ : {C : S¹ → Set}
--  → (cbase : C base) → (cloop : transport C look cbase ≡ cbase)
--  → apd (indS¹ {C} cbase cloop) loop ≡ cloop
