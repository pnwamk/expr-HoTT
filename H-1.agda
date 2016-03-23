{-# OPTIONS --without-K #-}

module H where

open import Data.Product using (_×_; _,_)
import Relation.Binary.Core as C
import Relation.Binary.PropositionalEquality as P
open P.≡-Reasoning

------------------------------------------------------------------------------
-- Some abbreviations and lemmas about paths

infix  4  _≡_   

_≡_ : ∀ {ℓ} {A : Set ℓ} → (x y : A) → Set ℓ
_≡_ {ℓ} {A} x y = C._≡_ {ℓ} {A} x y

refl : ∀ {ℓ} {A} → (x : A) → x ≡ x
refl {ℓ} {A} x = C.refl {ℓ} {A} {x}

infixr 8 _•_ 

_•_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} →
      (x ≡ y) → (y ≡ z) → (x ≡ z)
_•_ = P.trans      

unitTransR : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → (p ≡ p • refl y) 
unitTransR {x = x} C.refl = refl (refl x)

unitTransL : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ refl x • p) 
unitTransL {x = x} C.refl = refl (refl x)

-- ap, transport, apd at level 1

ap : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} →
     (f : A → B) → {x y : A} → (x ≡ y) → (f x ≡ f y)
ap = P.cong     

transport : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) →
            {x y : A} → (x ≡ y) → B x → B y
transport = P.subst

-- binary version
transport₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} (P : A → B → Set ℓ₃) →
            {x₁ x₂ : A} {y₁ y₂ : B} → (x₁ ≡ x₂) → (y₁ ≡ y₂) →
            P x₁ y₁ → P x₂ y₂
transport₂ = P.subst₂

apd : ∀ {ℓ₁ ℓ₂} → {A : Set ℓ₁} {B : A → Set ℓ₂} →
      (f : (x : A) → B x) → {x y : A} → (p : x ≡ y) →
      transport B p (f x) ≡ f y
apd f C.refl = C.refl

-- ap, transport, apd at level 2

ap² : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} →
      (f : A → B) → {x y : A} {p q : x ≡ y} → (r : p ≡ q) → 
      (ap f p ≡ ap f q)
ap² f C.refl = C.refl      

transport² : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (P : A → Set ℓ₂) →
      {x y : A} {p q : x ≡ y} → (r : p ≡ q) → (u : P x) →
      (transport P p u ≡ transport P q u)
transport² P {p = C.refl} C.refl u = refl u

apd² : ∀ {ℓ₁ ℓ₂} → {A : Set ℓ₁} {B : A → Set ℓ₂} →
      (f : (x : A) → B x) → {x y : A} {p q : x ≡ y} → (r : p ≡ q) →
      apd f p ≡ (transport² B r (f x)) • (apd f q)
apd² f {p = C.refl} C.refl = C.refl 

------------------------------------------------------------------------------
-- Some higher-inductive types from Ch. 6

module S¹ where 

  postulate
    S¹ : Set
    base : S¹
    loop : base ≡ base

  record rec (B : Set) (b : B) (p : b ≡ b) : Set₁ where
    field
      f : S¹ → B
      α : f base ≡ b
      β : transport (λ x → x ≡ x) α (ap f loop) ≡ p

  record ind (P : S¹ → Set) (b : P base) (p : transport P loop b ≡ b) : Set₁ where
    field
      f : (x : S¹) → P x
      α : f base ≡ b
      β : transport (λ x → transport P loop x ≡ x) α (apd f loop) ≡ p

------------------------------------------------------------------------------
-- Interval 

module I where

  postulate
    I : Set
    𝟘 : I
    𝟙 : I
    seg : 𝟘 ≡ 𝟙

  record rec (B : Set) (b₀ b₁ : B) (s : b₀ ≡ b₁) : Set₁ where
    postulate
      f : I → B
      α₀ : f 𝟘 ≡ b₀
      α₁ : f 𝟙 ≡ b₁
      β : transport₂ (λ x y → x ≡ y) α₀ α₁ (ap f seg) ≡ s

  record ind (P : I → Set) (b₀ : P 𝟘) (b₁ : P 𝟙)
             (s : transport P seg b₀ ≡ b₁) : Set₁ where
    postulate
      f : (x : I) → P x
      α₀ : f 𝟘 ≡ b₀
      α₁ : f 𝟙 ≡ b₁
      β : transport₂ (λ x y → transport P seg x ≡ y) α₀ α₁ (apd f seg) ≡ s

------------------------------------------------------------------------------
-- S²

module S² where 

  postulate
    S² : Set
    base : S²
    surf : refl base ≡ refl base

  record rec (B : Set) (b : B) (s : refl b ≡ refl b) : Set₁ where
    postulate
      f : S² → B
      α : f base ≡ b
      β : transport (λ p → refl p ≡ refl p) α (ap² f surf) ≡ s

  record ind (P : S² → Set) (b : P base) 
             (s : refl b ≡ transport² P surf b • (refl b)) : Set₁ where
    postulate
      f : (x : S²) → P x
      α : f base ≡ b
      β : transport
            (λ p → refl p ≡ transport² P surf p • refl p) α (apd² f surf)
          ≡ s

------------------------------------------------------------------------------
-- Suspensions

module Susp (A : Set) where

  postulate
    Σ : Set → Set₁
    N : Σ A
    S : Σ A
    merid : A → (N ≡ S)

------------------------------------------------------------------------------
-- Torus

module T² where

  postulate
    T² : Set
    b  : T²
    p  : b ≡ b
    q  : b ≡ b
    t  : p • q ≡ q • p

------------------------------------------------------------------------------
-- Torus (alternative definition)

module T²' where

  open S¹

  T² : Set
  T² = S¹ × S¹
    
------------------------------------------------------------------------------
-- Torus (second alternative definition)

module T²'' where

  open S¹

  postulate
    T² : Set
    b : T²
    p : b ≡ b
    q : b ≡ b
    h : T²
    f : S¹ → T²
    fb : f base ≡ b
    floop : transport (λ x → x ≡ x) fb (ap f loop) ≡ p • q • P.sym p • P.sym q
    s : (x : S¹) → f x ≡ h

------------------------------------------------------------------------------
