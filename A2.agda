module A2 where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true; _xor_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.List using (List; []; _++_)
open import Data.Vec using (Vec; []; _∷_) renaming (_++_ to _++V_)

------------------------------------------------------------------------------
-- Ch. 1
-- Theme: for each type, recursion principle and induction principle

------------------------------------------------------------------------------
-- Sec. 1.9
-- ℕ

recℕ : ∀ {ℓ} → (C : Set ℓ) → C → (ℕ → C → C) → ℕ → C
recℕ C z f 0 = z
recℕ C z f (suc n) = f n (recℕ C z f n)

indℕ : ∀ {ℓ} → (C : ℕ → Set ℓ) → C 0 → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
indℕ C z f 0 = z
indℕ C z f (suc n) = f n (indℕ C z f n)

-- Many examples in L.agda

------------------------------------------------------------------------------
-- Sec. 1.7
-- Empty type

-- Ex falso quodlibet

rec⊥ : ∀ {ℓ} → (C : Set ℓ) → ⊥ → C
rec⊥ C ()

ind⊥ : ∀ {ℓ} → (C : ⊥ → Set ℓ) → (v : ⊥) → C v
ind⊥ C ()

-- Examples

⊥→1≡2 : ⊥ → (1 ≡ 2)
⊥→1≡2 = rec⊥ (1 ≡ 2)

⊥→⊤≡⊥ : ⊥ → ⊤
⊥→⊤≡⊥ = rec⊥ ⊤

⊥→⊤≡⊥' : ⊥ → ⊤
⊥→⊤≡⊥' = ind⊥ (λ v → ⊤)

------------------------------------------------------------------------------
-- Sec. 1.5
-- Unit type

rec⊤ : ∀ {ℓ} → (C : Set ℓ) → C → ⊤ → C 
rec⊤ C c tt = c

ind⊤ : ∀ {ℓ} → (C : ⊤ → Set ℓ) → C tt → (u : ⊤) → C u
ind⊤ C c tt = c

-- Example

singleton⊤ : (u : ⊤) → (u ≡ tt)
singleton⊤ = ind⊤ (λ u → u ≡ tt) refl 

------------------------------------------------------------------------------
-- Sec. 1.8
-- Booleans

recBool : ∀ {ℓ} → (C : Set ℓ) → C → C → Bool → C
recBool C el th false = el
recBool C el th true = th

indBool : ∀ {ℓ} → (C : Bool → Set ℓ) → C false → C true → (b : Bool) → C b
indBool C el th false = el
indBool C el th true = th

-- Example

bool2 : (b : Bool) → (b ≡ false) ⊎ (b ≡ true)
bool2 = indBool
          (λ b → (b ≡ false) ⊎ (b ≡ true))
          (inj₁ refl)
          (inj₂ refl)

------------------------------------------------------------------------------
-- Sec. 1.5
-- Product types

rec× : ∀ {ℓ₁ ℓ₂ ℓ₃} → {A : Set ℓ₁} {B : Set ℓ₂} →
      (C : Set ℓ₃) → (A → B → C) → A × B → C
rec× C g (a , b) = g a b

ind× : ∀ {ℓ₁ ℓ₂ ℓ₃} → {A : Set ℓ₁} {B : Set ℓ₂} → (C : A × B → Set ℓ₃) → 
       ((a : A) → (b : B) → C (a , b)) → (p : A × B) → C p
ind× C g ( a , b ) = g a b

-- Examples

fst : {A B : Set} → A × B → A
fst {A} {B} = rec× A (λ a b → a)

snd : {A B : Set} → A × B → B
snd {A} {B} = rec× B (λ a b → b)

surj-pair : ∀ {A B} → (p : A × B) → (fst p , snd p) ≡ p
surj-pair = ind×
              (λ p → (fst p , snd p) ≡ p)
              (λ a b → refl)

-- IMPORTANT:
-- 
-- TO PROVE ANY PROPERTY OF SOMETHING OF TYPE A × B, IT IS SUFFICIENT
-- TO PROVE IT FOR CANONICAL VALUES OF THAT TYPE, i.e. FOR (a , b)
--

_Product_ : (A : Set) → (B : Set) → Set
A Product B = (z : Bool) → recBool Set A B z

pair : {A B : Set} → A → B → A Product B
pair {A} {B} a b = indBool (λ z → recBool Set A B z) a b

------------------------------------------------------------------------------
-- Sigma types (dependent pair type)

recΣ : ∀ {ℓ₁ ℓ₂ ℓ₃} → {A : Set ℓ₁} {B : A → Set ℓ₂} → (C : Set ℓ₃) →
       ((a : A) → B a → C) → Σ A B → C
recΣ C g (a , b) = g a b

indΣ : ∀ {ℓ₁ ℓ₂ ℓ₃} → {A : Set ℓ₁} {B : A → Set ℓ₂} → (C : Σ A B → Set ℓ₃) → 
        ((a : A) → (b : B a) → C (a , b)) → (p : Σ A B) → C p
indΣ C g ( a , b ) = g a b

-- Examples

dfst : {A : Set} {B : A → Set} → Σ A B → A
dfst {A} {B} = recΣ A (λ a b → a)

dsnd : {A : Set} {B : A → Set} → (p : Σ A B) → B (dfst p)
dsnd {A} {B} = indΣ
                 (λ p → B (dfst p))
                 (λ a b → b)

ac : {A B : Set} {R : A → B → Set} →
     ((x : A) → (Σ[ y ∈ B ] (R x y))) →
     (Σ[ f ∈ (A → B) ] ((x : A) → R x (f x)))
ac g = (λ x → dfst (g x)) , (λ x → dsnd (g x))

{-- In English :-)

If for all x, exists y, such that x R y, then
exists f such that for all x, x R f(x)

... this is one type-theoretic "axiom of choice"

--}

Magma : Set₁
Magma = Σ[ A ∈ Set ] (A → A → A)

m₁ m₂ m₃ m₄ m₅ : Magma
m₁ = (ℕ , _+_)
m₂ = (ℕ , _*_)
m₃ = (Bool , _xor_)
m₄ = (List Bool , _++_)
m₅ = (⊥ , λ ())

PointedMagma : Set₁
PointedMagma = Σ[ A ∈ Set ] ((A → A → A) × A)

pm₁ pm₂ pm₃ pm₄ : PointedMagma
pm₁ = (ℕ , _+_ , 0)
pm₂ = (ℕ , _*_ , 1)
pm₃ = (Bool , _xor_ , false)
pm₄ = (List Bool , _++_ , [])

------------------------------------------------------------------------------
-- Sum types (coproducts)

rec⊎ : ∀ {ℓ₁ ℓ₂ ℓ₃} → {A : Set ℓ₁} {B : Set ℓ₂} →
       (C : Set ℓ₃) → (A → C) → (B → C) → (A ⊎ B → C)
rec⊎ C f g (inj₁ a) = f a
rec⊎ C f g (inj₂ b) = g b

ind⊎ : ∀ {ℓ₁ ℓ₂ ℓ₃} → {A : Set ℓ₁} {B : Set ℓ₂} → (C : A ⊎ B → Set ℓ₃) → 
        ((a : A) → C (inj₁ a)) → ((b : B) → C (inj₂ b)) → ((x : A ⊎ B) → C x)
ind⊎ C f g (inj₁ a) = f a
ind⊎ C f g (inj₂ b) = g b

-- Examples

_Union_ : (A : Set) → (B : Set) → Set
A Union B = Σ[ b ∈ Bool ] (recBool Set A B b)

inLeft : {A B : Set} → A → A Union B
inLeft a = (false , a)

inRight : {A B : Set} → B → A Union B
inRight b = (true , b)

------------------------------------------------------------------------------
-- Induction principle for vectors

indVec : ∀ {ℓ} → {A : Set ℓ} → (C : {n : ℕ} → Vec A n → Set) → 
         C [] → 
         ({m : ℕ} → (x : A) → (xs : Vec A m) → C xs → C (x ∷ xs)) → 
         ({n : ℕ} → (xs : Vec A n) → C xs)
indVec C cnil ccons [] = cnil
indVec C cnil ccons (x ∷ xs) = ccons x xs (indVec C cnil ccons xs)

-- Example

[]++v≡v : ∀ {A n} → (v : Vec A n) → [] ++V v ≡ v
[]++v≡v {A} {n} = indVec
                    (λ v → [] ++V v ≡ v)
                    refl
                    (λ x xs p → refl)

postulate
  n+0≡n : ∀ {n} → n + 0 ≡ n

v++[]≡v : ∀ {ℓ} → ∀ {n} {A : Set ℓ} → (v : Vec A n) →
          subst (λ n → Vec A n) n+0≡n (v ++V []) ≡ v
v++[]≡v = {!indVec (λ v → subst (λ n → Vec A n) n+0≡n (v ++V []) ≡ v) ? ?!} 

------------------------------------------------------------------------------
-- Obvious omission from list of types

-- No induction principle for functions

------------------------------------------------------------------------------
-- Propositions as types

{--
Proposition                    Type
--------------------------------------------------
True                           ⊤
False                          ⊥
A and B                        A × B
A or B                         A ⊎ B
If A then B                    A → B
A iff B                        (A → B) × (B → A)
Not A                          A → ⊥
For all x ∈ A, P(x)            (x : A) → P x
Exists x ∈ A, P(x)             Σ[ x ∈ A ] (P x)
--}

¬ : Set → Set
¬ A = A → ⊥

-- Examples

deMorgan₁ : {A B : Set} → (¬ A) × (¬ B) → (¬ (A ⊎ B))
deMorgan₁ (na , nb) (inj₁ a) = na a
deMorgan₁ (na , nb) (inj₂ b) = nb b

deMorgan₂ : {A B : Set} → (¬ (A ⊎ B)) → (¬ A) × (¬ B)
deMorgan₂ n[a⊎b] = ((λ a → n[a⊎b] (inj₁ a)) , (λ b → n[a⊎b] (inj₂ b)))

contra : {A B : Set} →
         (A → B) → (¬ B → ¬ A)
contra      f        nb    a    = nb (f a)

-- 
-- NOTE: ¬ (¬ A) (which is (A → ⊥) → ⊥) is NOT the same as A.
--
-- We cannot prove it BUT there is no harm in adding it as an axiom
-- and working with it if we so choose

postulate
  CTR : {A : Set} → ¬ (¬ A) → A

-- The consequence is that we are not longer fully executable. We lost
-- the computational content of proofs!

pred₁ : {A : Set} {P Q : A → Set} →
        ((a : A) → (P a × Q a)) → (((a : A) → P a) × ((a : A) → Q a))
pred₁ f = ((λ a → proj₁ (f a)) , (λ a → proj₂ (f a))) 

--

Semigroup : Set₁
Semigroup = Σ[ A ∈ Set ] (Σ[ m ∈ (A → A → A) ]
            ((x y z : A) → m x (m y z) ≡ m (m x y) z))

-- First alternative definition 

record Semigroup' : Set₁ where
  field
    magma : Magma -- recall Magma = Σ[ A ∈ Set ] (A → A → A)
    assoc : let (Carrier , op) = magma in
            ((x y z : Carrier) → op x (op y z) ≡ op (op x y) z)

-- Second alternative definition

record Magma' : Set₁ where
  field
    carrier : Set
    op : carrier -> carrier -> carrier

record Semigroup'' (magma : Magma') : Set₁ where
  open Magma' magma
  field
    assoc : ((x y z : carrier) → op x (op y z) ≡ op (op x y) z)

-- Higher-order logic
            
allP : Set₁
allP = ∀ {A a₁ a₂} → (P : A → Set) → (P a₁ → P a₂)

-- Mere proposition

ℕiff⊤ : (ℕ → ⊤) × (⊤ → ℕ)
ℕiff⊤ = ((λ _ → tt) , (λ _ → 0))

-- ℕ and ⊤ are clearly NOT equivalent.
-- 
-- We are only saying that they are "logically equivalent", i.e., that one is
-- inhabited iff the other is inhabited
-- 
-- We also say that WHEN REGARDED AS MERE PROPOSITIONS, ℕ and ⊤
-- represent the same proposition
-- 

------------------------------------------------------------------------------
-- Exercises

-- Do as many of the exercises at the end of Chapter 1 as you can !!!



------------------------------------------------------------------------------

