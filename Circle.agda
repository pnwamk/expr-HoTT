{-# OPTIONS --without-K #-}

-- I've been spinning my wheels quite a bit on this proof.

-- I've chatted with several people and feel confident my
-- functions are properly defined, but I'm really struggling
-- to see how to prove they are quasi-inverses (it has been a little
-- reassuring, no one I have talked to has correctly defined
-- the functions initially, hah).

-- At the moment I'm not sure if I'm just missing something obvious in
-- the proof, or if I'm simply going about the proof wrong. I've
-- begun focusing on the eckmann-hilton proof and plan to return to this
-- after that is done.


module Circle where

open import Level using (_⊔_)
open import Data.Product using (Σ; _,_)
open import Function renaming (_∘_ to _○_)
--open import Relation.Binary.PropositionalEquality renaming (_≡_ to _≡_; refl to Eqrefl)
--open import Relation.Binary.EqReasoning

infixr 8  _∘_     -- path composition
infix  4  _≡_     -- propositional equality
infix  4  _∼_     -- homotopy between two functions 
infix  4  _≃_     -- type of equivalences
-- macros from tzaikin for equational rewriting over non-standard ≡
infixr 4 _≡⟨_⟩_ 
infix 4  _∎ 

------------------------------------------------------------------------------
-- A few HoTT primitives

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)

pathInd : ∀ {u ℓ} → {A : Set u} → 
          (C : {x y : A} → x ≡ y → Set ℓ) → 
          (c : (x : A) → C (refl x)) → 
          ({x y : A} (p : x ≡ y) → C p)
pathInd C c (refl x) = c x



-- inverse paths
! : ∀ {u} → {A : Set u} {x y : A} → (x ≡ y) → (y ≡ x)
! = pathInd (λ {x} {y} _ → y ≡ x) refl

-- path composition
_∘_ : ∀ {u} → {A : Set u} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_∘_ {u} {A} {x} {y} {z} p q = 
  pathInd {u}
    (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (x ≡ z)))
    (λ x z q → pathInd (λ {x} {z} _ → x ≡ z) refl {x} {z} q)
    {x} {y} p z q

-- Handy "macros" (from tzaikin)
_∎ : {A : Set} → (p : A) → p ≡ p
p ∎ = refl p

_≡⟨_⟩_ : {A : Set} → {q r : A} → (p : A) → p ≡ q → q ≡ r → p ≡ r
p ≡⟨ α ⟩ β = α ∘ β


-- (x ≡ y) ≡ ((x ≡ y) ∘ (refl y))
unitTransR : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ (p ∘ refl y)) 
unitTransR {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ (p ∘ (refl y))) 
    (λ x → refl (refl x))
    {x} {y} p 

-- (x ≡ y) ≡ ((refl x) ∘ (x ≡ y))
unitTransL : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ refl x ∘ p) 
unitTransL {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ (refl x) ∘ p)
    (λ x → refl (refl x))
    {x} {y} p 

-- !(x ≡ y) ∘ (x ≡ y)  ≡ (refl y)
invTransL : {A : Set} {x y : A} → (p : x ≡ y) → (! p ∘ p ≡ refl y)
invTransL {A} {x} {y} p = 
  pathInd 
    (λ {x} {y} p → ! p ∘ p ≡ refl y)
    (λ x → refl (refl x))
    {x} {y} p

--  (x ≡ y) ∘ !(x ≡ y)  ≡ (refl x)
invTransR : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → (p ∘ ! p ≡ refl x)
invTransR {ℓ} {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ∘ ! p ≡ refl x)
    (λ x → refl (refl x))
    {x} {y} p

-- !!(x ≡ y) ≡ (x ≡ y)
invId : {A : Set} {x y : A} → (p : x ≡ y) → (! (! p) ≡ p)
invId {A} {x} {y} p =
  pathInd 
    (λ {x} {y} p → ! (! p) ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

-- (x ≡ y) and (y ≡ z) ⇒ (x ≡ z)
assocP : {A : Set} {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) →
         (p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
assocP {A} {x} {y} {z} {w} p q r =
  pathInd
    (λ {x} {y} p → (z : A) → (w : A) → (q : y ≡ z) → (r : z ≡ w) → 
      p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
    (λ x z w q r → 
      pathInd
        (λ {x} {z} q → (w : A) → (r : z ≡ w) → 
          (refl x) ∘ (q ∘ r) ≡ ((refl x) ∘ q) ∘ r)
        (λ x w r → 
          pathInd
            (λ {x} {w} r → 
              (refl x) ∘ ((refl x) ∘ r) ≡ 
              ((refl x) ∘ (refl x)) ∘ r)
            (λ x → (refl (refl x)))
            {x} {w} r)
        {x} {z} q w r)
    {x} {y} p z w q r

-- !(p ∘ q) ≡ !q ∘ !p
invComp : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → 
          ! (p ∘ q) ≡ ! q ∘ ! p
invComp {A} {x} {y} {z} p q = 
  pathInd
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → ! (p ∘ q) ≡ ! q ∘ ! p)
    (λ x z q → 
      pathInd 
        (λ {x} {z} q → ! (refl x ∘ q) ≡ ! q ∘ ! (refl x))
        (λ x → refl (refl x)) 
        {x} {z} q)
    {x} {y} p z q


-- (x ≡ y) ⇒ (f x) ≡ (f y)
ap : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A} → 
     (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {ℓ} {ℓ'} {A} {B} {x} {y} f p = 
  pathInd 
    (λ {x} {y} p → f x ≡ f y) 
    (λ x → refl (f x))
    {x} {y} p

-- sort of
-- p:(x ≡ y) ⇒ q:(y ≡ z) ⇒ (((f x) ≡ (f z)) ≡ (((f x) ≡ (f y)) ∘ ((f y) ≡ (f z))))
apfTrans : ∀ {u} → {A B : Set u} {x y z : A} → 
  (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q)
apfTrans {u} {A} {B} {x} {y} {z} f p q = 
  pathInd {u}
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → 
      ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q))
    (λ x z q → 
      pathInd {u}
        (λ {x} {z} q → 
          ap f (refl x ∘ q) ≡ (ap f (refl x)) ∘ (ap f q))
        (λ x → refl (refl (f x)))
        {x} {z} q)
    {x} {y} p z q

-- ap f (! p) ≡ ! (ap f p)
apfInv : ∀ {u} → {A B : Set u} {x y : A} → (f : A → B) → (p : x ≡ y) → 
         ap f (! p) ≡ ! (ap f p) 
apfInv {u} {A} {B} {x} {y} f p =
  pathInd {u}
    (λ {x} {y} p → ap f (! p) ≡ ! (ap f p))
    (λ x → refl (ap f (refl x)))
    {x} {y} p

-- ap g (ap f p) ≡ ap (g ○ f) p
apfComp : {A B C : Set} {x y : A} → (f : A → B) → (g : B → C) → (p : x ≡ y) → 
          ap g (ap f p) ≡ ap (g ○ f) p 
apfComp {A} {B} {C} {x} {y} f g p =
  pathInd 
    (λ {x} {y} p → ap g (ap f p) ≡ ap (g ○ f) p)
    (λ x → refl (ap g (ap f (refl x))))
    {x} {y} p

--  ap id p ≡ p
apfId : {A : Set} {x y : A} → (p : x ≡ y) → ap id p ≡ p
apfId {A} {x} {y} p = 
  pathInd 
    (λ {x} {y} p → ap id p ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

--  (x ≡ y) → P x → P y
transport : ∀ {ℓ ℓ'} → {A : Set ℓ} {x y : A} → 
  (P : A → Set ℓ') → (p : x ≡ y) → P x → P y
transport {ℓ} {ℓ'} {A} {x} {y} P p = 
  pathInd -- on p
    (λ {x} {y} p → (P x → P y))
    (λ _ → id)
    {x} {y} p

-- dependent ap
apd : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : A → Set ℓ'} {x y : A} → (f : (a : A) → B a) → 
  (p : x ≡ y) → (transport B p (f x) ≡ f y)
apd {ℓ} {ℓ'} {A} {B} {x} {y} f p = 
  pathInd 
    (λ {x} {y} p → transport B p (f x) ≡ f y)
    (λ x → refl (f x))
    {x} {y} p

-- Homotopies and equivalences

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkqinv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    h : B → A
    β : (h ○ f) ∼ id

equiv₁ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {f : A → B} → qinv f → isequiv f
equiv₁ (mkqinv qg qα qβ) = mkisequiv qg qα qg qβ
       
_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) isequiv

postulate 
  univalence : {A B : Set} → (A ≡ B) ≃ (A ≃ B)

------------------------------------------------------------------------------
-- Exercise: let's show that the following two definitions of the
-- circle are "the same"

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

  postulate
    βrecS¹ : {C : Set} → (cbase : C) → (cloop : cbase ≡ cbase) → 
      ap (recS¹ cbase cloop) loop ≡ cloop
 
  indS¹ : {C : S¹ → Set} → 
    (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → 
    (circle : S¹) → C circle
  indS¹ cbase cloop base* = cbase

  postulate
    βindS¹ : {C : S¹ → Set} → 
      (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → 
      apd (indS¹ {C} cbase cloop) loop ≡ cloop

open Circle1 public

module Circle2 where
  private 
    data S¹'* : Set where
      south* : S¹'*
      north* : S¹'*

  S¹' : Set
  S¹' = S¹'*

  south : S¹'
  south = south*

  north : S¹'
  north = north*

  postulate 
    east : south ≡ north
    west : south ≡ north

  recS¹' : {C : Set} → 
    (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → S¹' → C
  recS¹' csouth cnorth ceast cwest south* = csouth
  recS¹' csouth cnorth ceast cwest north* = cnorth

  postulate
    βreceastS¹' : {C : Set} → 
      (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → 
      ap (recS¹' csouth cnorth ceast cwest) east ≡ ceast
    βrecwestS¹' : {C : Set} → 
      (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → 
      ap (recS¹' csouth cnorth ceast cwest) west ≡ cwest
 
  indS¹' : {C : S¹' → Set} → 
    (csouth : C south) → (cnorth : C north) → 
    (ceast : transport C east csouth ≡ cnorth) → 
    (cwest : transport C west csouth ≡ cnorth) → 
    (circle : S¹') → C circle
  indS¹' csouth cnorth ceast cwest south* = csouth
  indS¹' csouth cnorth ceast cwest north* = cnorth

  postulate
    βindeastS¹' : {C : S¹' → Set} → 
      (csouth : C south) → (cnorth : C north) → 
      (ceast : transport C east csouth ≡ cnorth) → 
      (cwest : transport C west csouth ≡ cnorth) → 
      apd (indS¹' {C} csouth cnorth ceast cwest) east ≡ ceast
    βindwestS¹' : {C : S¹' → Set} → 
      (csouth : C south) → (cnorth : C north) → 
      (ceast : transport C east csouth ≡ cnorth) → 
      (cwest : transport C west csouth ≡ cnorth) → 
      apd (indS¹' {C} csouth cnorth ceast cwest) west ≡ cwest

open Circle2 public

Smap : S¹ → S¹'
Smap s = recS¹ south (west ∘ (! east)) s

S'map : S¹' → S¹
S'map s = recS¹' {C = S¹} base base (refl base) loop s

S'toS≡id : S¹' -> Set
S'toS≡id = (λ s' → (Smap ○ S'map) s' ≡ id s')

StoS'≡id : S¹ -> Set
StoS'≡id = (λ s → (S'map ○ Smap) s ≡ id s)


Sqinv : qinv Smap
Sqinv = mkqinv S'map
               -- P(s') = (Smap ○ S'map) s' ≡ id s'
               (indS¹'
                 {C = S'toS≡id}
                 (refl south)
                 (transport S'toS≡id east (refl south))
                 ((refl (transport S'toS≡id east (refl south))))
                 -- I've spent several hours exploring how I might
                 -- prove this and I'm completely lost.
                 -- I must be missing something obvious or I'm going about this
                 -- totally wrong =\
                 (transport S'toS≡id west (refl south) ≡⟨ {!!} ⟩
                  transport S'toS≡id east (refl south) ∎))
               -- P(s) = (S'map ○ Smap) s ≡ id s
               (indS¹
                 {C = (λ s → (S'map ○ Smap) s ≡ id s)} -- P
                 (refl base) -- P(base)
                 -- P()
                 (transport StoS'≡id loop (refl base) ≡⟨ {!!} ⟩
                  refl base ∎))
sequiv : S¹ ≃ S¹'
sequiv = (Smap , equiv₁ Sqinv)

spath : S¹ ≡ S¹'
spath with univalence 
... | (_ , eq) = isequiv.g eq sequiv

------------------------------------------------------------------------------
