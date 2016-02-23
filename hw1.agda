{-# OPTIONS --without-K #-}
module hw1 where

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

data _≡_ {ℓ} {A : Set ℓ} : (x y : A) → Set ℓ where
  refl : (x : A) → x ≡ x

rec≡ : {A : Set} →
       (R : A → A → Set) {reflexiveR : {a : A} → R a a} →
       ({x y : A} (p : x ≡ y) → R x y)
rec≡ R {reflR} (refl y) = reflR {y}

subst : ∀ {ℓ} {A : Set ℓ} {C : A → Set ℓ} →
        ({x y : A} (p : x ≡ y) → C x → C y)
subst (refl x) = id

------------------------------------------------------------------------------
-- Exercise 1.1
-- show h ∘ (g ∘ f) = (h ∘ g) ∘ f
------------------------------------------------------------------------------

_∘_ : {A B C : Set} → (f : B → C) → (g : A → B) → A → C
f ∘ g = (λ a → f (g a))

compose≡ : {A B C D : Set}
            → (f : A → B)
            → (g : B → C)
            → (h : C → D)
            → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
compose≡ = λ f g h → refl (λ a → (h (g (f a))))

------------------------------------------------------------------------------
-- Exercise 1.2
-- Derive the recursion principle for products recA×B
-- using only the projections, and verify that the definitional
-- equalities are valid. Do the same for Σ-types.
------------------------------------------------------------------------------
---------------------------------------------------
-- Product Types
data _×_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  pair : A → B → A × B

fst : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → A × B → A
fst (pair a _) = a

snd : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}  -> A × B -> B
snd (pair _ b) = b

rec× : ∀ {ℓ} {A B : Set ℓ}
       → (C : Set ℓ)
       → (A → B → C)
       → A × B → C
rec× c f = λ p -> (f (fst p) (snd p))

fstofab≡a : ∀ {A B : Set}
              (a : A)
              → (b : B)
              → fst (pair a b) ≡ a
fstofab≡a {A} {B} = λ a b → refl a

sndofab≡b : ∀ {A B : Set}
              (a : A)
              → (b : B)
              → snd (pair a b) ≡ b
sndofab≡b {A} {B} = λ a b → refl b


uniq× : ∀ {ℓ₁ ℓ₂}
          {A : Set ℓ₁}
          {B : Set ℓ₂}
          (p : A × B)
          → (pair (fst p) (snd p)) ≡ p
uniq× (pair a b) = refl (pair a b)

rec×g≡g : ∀ {A B C : Set}
            (g : A → B → C)
            (a : A)
            → (b : B)
            → rec× C g (pair a b) ≡ g a b
rec×g≡g {A} {B} {C} = λ g a b → refl (g a b)

recfst : ∀ (A B : Set)
           → fst {B = B} ≡ rec× A (λ a b → a)
recfst A B = refl fst


---------------------------------------------------
-- Sigma Types
data Σ {ℓ₁ ℓ₂} (A : Set ℓ₁)
               (B : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂)
     where dpair : (a : A) → (B a) → Σ A B

dfst : ∀ {A : Set} {B : A → Set} → Σ A B → A
dfst (dpair a _) = a

dsnd : ∀ {A : Set} {B : A → Set} → (p : Σ A B) → (B (dfst p))
dsnd (dpair _ b) = b

dfstofab≡a : ∀ {A : Set}
               {B : A → Set}
               (a : A)
               (b : B a) →
               dfst {B = B} (dpair a b) ≡ a
dfstofab≡a {A} {B} = λ a b → refl a

dsndofab≡a : ∀ {A : Set}
               {B : A → Set}
               (a : A)
               (b : B a) →
               dsnd {B = B} (dpair a b) ≡ b
dsndofab≡a {A} {B} = λ a b → refl b

uniqΣ : ∀ {A : Set}
          {B : A → Set}
          (p : Σ A B)
          → (dpair (dfst p) (dsnd p)) ≡ p
uniqΣ (dpair a b) = refl (dpair a b)


------------------------------------------------------------------------------
-- Exercise 1.3
-- Derive the induction principle for products indA×B,
-- using only the projections and the propositional uniqueness
-- principle uniqA×B. Verify that the definitional equalities are
-- valid. Generalize uniqA×B to Σ-types, and do the same for Σ-types.
------------------------------------------------------------------------------


ind× : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ}
         → (C : (A × B) → Set ℓ)
         → ((a : A) (b : B) → (C (pair a b)))
         → (p : (A × B)) → (C p)
ind× = λ C f → λ p → subst {C = C}
                           (uniq× p)
                           (f (fst p) (snd p))

indΣ' : ∀  {A : Set} {B : A → Set} → (C : Σ A B → Set) → 
        ((a : A) → (b : B a) → C (dpair a b)) → (p : Σ A B) → C p
indΣ' C g s = subst {C = C}
                    (uniqΣ s)
                    (g (dfst s) (dsnd s))


------------------------------------------------------------------------------
--- Exercise 1.4 Given the function iter, derive a function having the
--- type of the recursor recN. Show that the defining equations of the
--- recursor hold propositionally for this function, using the
--- induction principle for Nats.
------------------------------------------------------------------------------

iter : ∀ {ℓ} {C : Set ℓ} → C → (C → C) → ℕ → C
iter c₀ c₊ 0 = c₀
iter c₀ c₊ (suc n) = c₊ (iter c₀ c₊ n)



recℕ' : ∀ {ℓ} → (C : Set ℓ) → C → (ℕ → C → C) → ℕ → C
recℕ' C c₀ f n =
  snd (iter (pair 0 c₀)
            (λ nc →
                  (pair (suc (fst nc))
                        (f (fst nc) (snd nc))))
            n)

-- quick def and sanity check of fact via recℕ
fact = recℕ ℕ 1 (λ n nfact → (suc n) * nfact)
fact1 : fact 0 ≡ 1
fact1 = refl 1
fact5 : fact 5 ≡ 120
fact5 = refl 120

-- quick def and sanity check of fact via recℕ'
fact' = recℕ' ℕ 1 (λ n nfact → (suc n) * nfact)
fact'1 : fact' 0 ≡ 1
fact'1 = refl 1
fact'5 : fact' 5 ≡ 120
fact'5 = refl 120

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f (refl y) = refl (f y)

-- this _is_ valid but I haven't done enough Agda
-- to see how to prove this. I proved it in the Coq HoTT library...
-- https://github.com/andmkent/HoTT/blob/5f9faf5ef4ea21db249d6ad45bcee0adf97f8f9d/contrib/HoTTBookExercises.v#L124
postulate
  punt1 : ∀ {ℓ} (C : Set ℓ) →
           (c₀ : C) →
           (f : (ℕ → C → C)) →
           (n : ℕ) → 
           recℕ C c₀ f (suc n) ≡ recℕ' C c₀ f (suc n)


recℕ≡recℕ' : ∀ {ℓ} (C : Set ℓ) →
           (c₀ : C) →
           (f : (ℕ → C → C)) →
           ((n : ℕ) → recℕ C c₀ f n ≡ recℕ' C c₀ f n)
                                                 
recℕ≡recℕ' {ℓ} C c₀ f n =
  indℕ {ℓ = ℓ}
       (λ n → (((recℕ  {ℓ = ℓ} C c₀ f) n)
                ≡
               ((recℕ' {ℓ = ℓ} C c₀ f) n)))
       (refl c₀)
       (λ n IH → (punt1 C c₀ f n))
       n

------------------------------------------------------------------------------
--- Exercise 1.5 Show that if we define A + B Σ(x:2) rec2(U, A, B,
--- x), then we can give a definition of indA+B for which the
--- definitional equalities stated in §1.7 hold.
------------------------------------------------------------------------------

data 𝟚 : Set where
  true  : 𝟚
  false : 𝟚

rec𝟚 : ∀ {ℓ} → {C : Set ℓ} → C → C → 𝟚 → C
rec𝟚 th el false = el
rec𝟚 th el true = th

if_then_else_ : ∀ {ℓ} {C : Set ℓ} → 𝟚 → C → C → C
if b then X else Y = rec𝟚 X Y b

ind𝟚 : ∀ {ℓ} → {C : 𝟚 → Set ℓ} → C true → C false → (b : 𝟚) → C b
ind𝟚 th el false = el
ind𝟚 th el true = th


bsum : ∀ (A : Set) → (B : Set) → Set
bsum  A B = Σ 𝟚 (rec𝟚 A B)

injbs1 : ∀ (A : Set) → (B : Set) → A → bsum A B
injbs1 A B a =  dpair true a

injbs2 : ∀ (A : Set) → (B : Set) → B → bsum A B
injbs2 A B b =  dpair false b


recΣ : ∀ {ℓ₁ ℓ₂ ℓ₃} → {A : Set ℓ₁} {B : A → Set ℓ₂} → (C : Set ℓ₃) →
       ((a : A) → B a → C) → Σ A B → C
recΣ C g (dpair a b) = g a b

indΣ : ∀ {ℓ₁ ℓ₂ ℓ₃} → {A : Set ℓ₁} {B : A → Set ℓ₂} → (C : Σ A B → Set ℓ₃) → 
        ((a : A) → (b : B a) → C (dpair a b)) → (p : Σ A B) → C p
indΣ C g (dpair a b) = g a b


indbsum : (A : Set) (B : Set) (C : (bsum A B → Set))
           → ((a : A) → (C (injbs1 A B a)))
           → ((b : B) → (C (injbs2 A B b)))
           → (a+b : bsum A B) → (C a+b)
indbsum A B C ca cb = indΣ C (ind𝟚 ca cb)
-- where ind𝟚's C = (λ b →  (t : rec𝟚 A B b) → C (dpair b t))

                                                                                             
indbs1 : ∀ {A B : Set} (P : (bsum A B) → Set)
         → (fa : (a : A) → P (injbs1 A B a))
         → (fb : (b : B) → P (injbs2 A B b))
         → (a : A)
         → indbsum A B P fa fb (injbs1 A B a) ≡ fa a
indbs1 P fa fb x = refl (fa x)

indbs2 : ∀ {A B : Set} (P : (bsum A B) → Set)
         → (fa : (a : A) → P (injbs1 A B a))
         → (fb : (b : B) → P (injbs2 A B b))
         → (b : B)
         → indbsum A B P fa fb (injbs2 A B b) ≡ fb b
indbs2 P fa fb x = refl (fb x)


rec⊎ : ∀ {ℓ₁ ℓ₂ ℓ₃} → {A : Set ℓ₁} {B : Set ℓ₂} →
       (C : Set ℓ₃) → (A → C) → (B → C) → (A ⊎ B → C)
rec⊎ C f g (inj₁ a) = f a
rec⊎ C f g (inj₂ b) = g b


------------------------------------------------------------------------------
--- Exercise 1.10
-- Show that the Ackermann function ack : ℕ → ℕ → ℕ is definable using
-- only recℕ satisfying the following equations:
-- ack(0, m) = succ(m)  -> ack(0) = suc
-- ack(succ(n), 0) = ack(n, 1)  -> ack (suc n) = 
-- ack(succ(n), succ(m)) = ack(n, ack(succ(n), m)).

ack : ℕ → ℕ → ℕ
ack = recℕ (ℕ → ℕ)
           suc
           (λ n ackn → recℕ ℕ (ackn 1) (λ m res → (ackn res)))

acktest00 : ack 0 0 ≡ 1
acktest00 = refl 1

acktest01 : ack 0 1 ≡ 2
acktest01 = refl 2

acktest10 : ack 1 0 ≡ 2
acktest10 = refl 2

acktest11 : ack 1 1 ≡ 3
acktest11 = refl 3

acktest22 : ack 2 2 ≡ 7
acktest22 = refl 7




------------------------------------------------------------------------------
--- Exercise 1.11
-- Show that for any type A, we have ¬¬¬A → ¬A.

¬ : Set → Set
¬ P = P → ⊥


ex11 : ∀ (P : Set) → ¬ (¬ (¬ P)) → ¬ P
ex11 P = λ nnnP → λ P → nnnP (λ nP → nP P)

------------------------------------------------------------------------------
-- Exercise 1.12
-- Using the propositions as types interpretation, derive the following tautologies.
-- (i) If A, then (if B then A).
-- (ii) If A, then not (not A).
-- (iii) If (not A or not B), then not (A and B).

ex12i : ∀ (A : Set) → A → (Set → A)
ex12i = λ A a _ → a

ex12ii : ∀ (A : Set) → A → (¬ (¬ A))
ex12ii = λ A a → λ nA → nA a


ex12iii : ∀ (A B : Set) → (¬ (A ⊎ B)) → (¬ (A × B))
ex12iii = λ A B → λ nAorB → λ AandB → nAorB (inj₁ (fst AandB))

------------------------------------------------------------------------------
-- Exercise 1.13
-- Using propositions-as-types, derive the double negation of the principle of ex-
-- cluded middle, i.e. prove not (not (P or not P)).

ex13 : ∀ (P : Set) → (¬ (¬ (P ⊎ (¬ P))))
ex13 = λ P nPorPnot → nPorPnot (inj₂ (λ P → nPorPnot (inj₁ P))) 

------------------------------------------------------------------------------
-- Exercise 1.16
-- Show that addition of natural numbers is commutative.

ex16 : ∀ (a b c : ℕ) → a + (b + c) ≡ (a + b) + c
ex16 = indℕ (λ a → (b c : ℕ) → a + (b + c) ≡ a + b + c)
            (λ b c → refl (b + c))
            (λ n IHn b c → cong suc (IHn b c))
