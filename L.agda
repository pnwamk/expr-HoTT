module L where

open import Data.Nat using (ℕ; suc) -- ; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Product
open import Data.Empty

-- Recursion principle

recℕ : (C : Set) → C → (ℕ → C → C) → ℕ → C
recℕ C c f 0 = c
recℕ C c f (suc n) = f n (recℕ C c f n)

double : ℕ → ℕ
double = recℕ ℕ 0 (λ n r → suc (suc r))

add : ℕ → ℕ → ℕ
add = recℕ (ℕ → ℕ) (λ n → n) (λ m r → λ n → suc (r n))

-- fact : ℕ → ℕ
-- fact = recℕ ℕ 1 (λ n r → suc n * r)

-- Induction principle

indℕ : (C : ℕ → Set) → C 0 → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
indℕ C c f 0 = c
indℕ C c f (suc n) = f n (indℕ C c f n)

add-assoc : (i j k : ℕ) → add i (add j k) ≡ add (add i j) k
add-assoc = indℕ
              (λ i → (j k : ℕ) → add i (add j k) ≡ add (add i j) k)
              (λ j k → refl)
              (λ i i+[j+k]≡[i+j]+k j k → cong suc (i+[j+k]≡[i+j]+k j k))

add-right-unit : (i : ℕ) → add i 0 ≡ i
add-right-unit = indℕ (λ i → add i 0 ≡ i) refl (λ i i+0≡i → cong suc i+0≡i) 

add-suc : (i j : ℕ) → suc (add i j) ≡ add i (suc j)
add-suc = indℕ (λ i → (j : ℕ) → suc (add i j) ≡ add i (suc j))
               (λ j → refl)
               (λ i s[i+j]≡i+s[j] j → cong suc (s[i+j]≡i+s[j] j))

add-comm : (i j : ℕ) → add i j ≡ add j i
add-comm = indℕ
             (λ i → (j : ℕ) → add i j ≡ add j i)
             (λ j → sym (add-right-unit j))
             (λ i i+j≡j+i j → trans (cong suc (i+j≡j+i j)) (add-suc j i))

-- Some type definitions

_≤_ : (i j : ℕ) → Set
i ≤ j = Σ[ k ∈ ℕ ] (add i k ≡ j)

i≤i+j : (i j : ℕ) → i ≤ add i j
i≤i+j = indℕ
          (λ i → (j : ℕ) → i ≤ add i j)
          (λ j → (j , refl))
          (λ i i≤i+j j → (j , refl))

¬ : Set → Set
¬ A = A → ⊥

_<_ : (i j : ℕ) → Set
i < j = (i ≤ j) × ¬ (i ≡ j)

0≠si : (i : ℕ) → ¬ (0 ≡ suc i)
0≠si i = λ ()

0< : (i : ℕ) → (0 < suc i)
0< = indℕ  {!!} {!!} {!!}
