module Id1 where

import Level
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Bool using (Bool)
open import Data.Sum using (_⊎_)
open import Data.Nat 
open import Data.Product
open import Data.Vec 
open import Function using (id)

-- Study identity types from first principles

-- As we have seen for the previous types, we need to define the type,
-- its constructors, and then focus on the recursion and induction
-- principles. All computations and all properties of the identity
-- type should be derivable from these (recursion and induction)
-- principles.

------------------------------------------------------------------------------

data _≡_ {A : Set} : (x y : A) → Set where
  refl : (x : A) → x ≡ x

-- We have to write (refl x) for some x. This is different from the
-- Agda library which leaves the 'x' implicit

infix 4 _≡_

{-- 
Convention:
multiplicative          precedence 7
additive                precedence 6
equality and comparison precedence 4 
--}

-- Simple examples

private
  p₁ : 3 ≡ 3
  p₁ = refl 3

  p₂ : 3 * 1 ≡ 1 + 2
  p₂ = refl (4 ∸ 1)
  
-- Let's try to derive the recursion principle for identity
-- types... This type has one constructor just like ⊤ in some sense.
-- Recall the recursion principle for ⊤:
-- rec⊤ : (C : Set) → C → (v : ⊤) → C

-- So at first approximation, the recursion principle for ≡ looks like:

-- 
-- rec≡ : (C : Set) → C → ({A : Set} {x y : A} (p : x ≡ y) → C)
-- 

-- In the case of ⊤, we wanted to map the element of ⊤ to an element
-- of C. For ≡, we also want to map the element of (x ≡ y) to an
-- element of C. Note that the element of (x ≡ y) is some kind of
-- relation between x and y so it makes sense to insist that the
-- target C is also a relation between x and y, i.e., we map relations
-- to relations.

-- So as a second approximation, the recursion principle for ≡ looks like:

--
-- rec≡ : {A : Set} {x y : A} → 
--        (R : A → A → Set) → R x y → (p : x ≡ y) → R x y
-- 

-- In the case of ⊤, the second argument to the recursion operation
-- specified an element of C which would serve as the target for
-- tt. Now in the case of ≡, we want to specify an element of R x y
-- which would be the target of refl. This requires two adjustments:
-- first the second argument of type (R x y) makes no sense in general
-- as we don't want to insist that the relation R is universal (i.e.,
-- holds between arbitrary x and y). Second we must insist that the
-- relation R is reflexive. 

rec≡ : {A : Set} →
       (R : A → A → Set) {reflexiveR : {a : A} → R a a} →
       ({x y : A} (p : x ≡ y) → R x y)
rec≡ R {reflR} (refl y) = reflR {y}

-- A special case of reflexive relations on A is the class of
-- functions from C a -> C a for some predicate C. Let's specialize
-- the above recursion principle to this special case.

rec≡S : {A : Set} {C : A → Set} →
        ({x y : A} (p : x ≡ y) → C x → C y)
rec≡S {C = C} p = rec≡ (λ a b → C a → C b) {id} p
      
-- Or we can prove the specialized version directly (rename to subst)

subst : {A : Set} {C : A → Set} →
        ({x y : A} (p : x ≡ y) → C x → C y)
subst {x = x} {y = .x} (refl .x) = id

-- So the recursion principle for the identity type says
-- equals may be substituted for equals OR 
-- indiscernability of identicals OR 
-- every type family respects equality

-- Examples:

private

  ex₁ : ∀ {n} → (p : n + 0 ≡ n) → (n + 0 > 0) → (n > 0) 
  ex₁ {n} p = subst {C = λ m → m > 0} {n + 0} {n} p

  ex₂ : ∀ {A n} → (p : n + 0 ≡ n) → (Vec A (n + 0)) → (Vec A n)
  ex₂ {A} {n} p = subst {C = λ m → Vec A m} {n + 0} {n} p

  {-- 

  From Data.Nat library:

  data _≤_ : Rel ℕ Level.zero where
    z≤n : ∀ {n}                 → zero  ≤ n
    s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

  --}

  ≤-reflexive : {a : ℕ} → a ≤ a
  ≤-reflexive {zero} = z≤n 
  ≤-reflexive {suc a} = s≤s (≤-reflexive {a}) 

  ex₃ : ∀ {n} → (p : n + 0 ≡ n) → (n + 0 ≤ n)
  ex₃ {n} = rec≡ {ℕ} (_≤_) {≤-reflexive} {n + 0} {n}

------------------------------------------------------------------------------
-- Now let's look at the induction principle for identity types

-- Our usual idiom is to use the same code for the recursion principle
-- and just make the eliminator a dependent function

-- Let's look at rec≡ again

-- rec≡ : {A : Set} →
--        (R : A → A → Set) {reflexiveR : {a : A} → R a a} →
--        ({x y : A} (p : x ≡ y) → R x y)
-- rec≡ R {reflR} (refl y) = reflR {y}

-- The relation R is already dependent on x and y; we just need to
-- make it dependent on p too

ind≡ : {A : Set} → 
       (R : (x : A) → (y : A) → (p : x ≡ y) → Set)
       {reflexiveR : {a : A} → R a a (refl a)} →
       ({x y : A} (p : x ≡ y) → R x y p)
ind≡ R {reflR} (refl y) = reflR {y}

-- Changing some implicit argument to being explicit and vice-versa,
-- and changing names of bound variables we get:

J : {A : Set} →
    (R : {x y : A} → (p : x ≡ y) → Set)
    (r : (a : A) → R (refl a)) →
    ({a b : A} (p : a ≡ b) → R p)
J R r (refl y) = r y

-- Examples

sym : {A : Set} {x y : A} → (x ≡ y) → (y ≡ x)
sym = J (λ {x} {y} p → y ≡ x) (λ a → refl a)

-- Next we want to prove:
-- trans : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
-- if we try to directly use J we discover that the definition of R 
-- (λ {x} {y} p → y ≡ z → x ≡ z)
-- refers to an unbound z

trans' : {A : Set} {x y : A} → (x ≡ y) → ((z : A) → (q : y ≡ z) → (x ≡ z))
trans' {A} = 
  J (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (x ≡ z)))
    (λ a z → id)

-- then

trans : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
trans {A} {x} {y} {z} p q = trans' {A} {x} {y} p z q

-- trans' refl q will simplify to q because we did induction on the first argument

idR : {A : Set} {x y : A} (q : x ≡ y) → trans (refl x) q ≡ q
idR q = refl q

-- but trans' p refl will NOT simplify

-- idL : {A : Set} {x y : A} (p : x ≡ y) → trans p (refl y) ≡ p
-- idL p = refl p -- does not work

-- We can do induction on the right and get the reverse situation
-- OR we can do induction twice and lose BOTH and ONLY get
-- trans refl refl = refl
-- Even though this seems "worse", it is symmetric at least and easy to work is.

trans2' : {A : Set} {x y : A} → (x ≡ y) → ((z : A) → (q : y ≡ z) → (x ≡ z))
trans2' {A} =
  J (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (x ≡ z)))
    (λ a z → J (λ {x'} {y'} q → x' ≡ y') (λ b → refl b))

trans2 : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
trans2 {A} {x} {y} {z} p q = trans2' {A} {x} {y} p z q

idLR : {A : Set} {a : A} → trans2 (refl a) (refl a) ≡ refl a
idLR {A} {a} = refl (refl a)

------------------------------------------------------------------------------

-- If we restrict ourselves to proofs about "points" like numbers,
-- booleans, etc. all we are saying is that if we normalize the
-- calculation for each point they each reduce to same identical
-- result. Things get much more interesting if we start thinking about
-- identity in higher universes... So for example, say we want to
-- prove that groups are the same, in that case we might have to prove
-- that two types are the same etc. Unfortunately J by itself is
-- helpless here... This motivates the univalence axiom to be discussed next...

------------------------------------------------------------------------------
