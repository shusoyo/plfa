module plfa.lf.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

--- Associativity
_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

{- 
Associativity 
  target: (m + n) + p ≡ m + (n + p)
  inference rule:

  -------------------------
  (0 + m) + n = 0 + (m + n)

  (p + m) + n = p + (m + n)
  ---------------------------------
  (suc p + m) + n = suc p + (m + n)
-}
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

--- example
+-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
+-assoc-0 n p =
  begin
    (0 + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    0 + (n + p)
  ∎

+-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
+-assoc-1 n p =
  begin
    (1 + n) + p
  ≡⟨⟩
    suc (0 + n) + p
  ≡⟨⟩
    suc ((0 + n) + p)
  ≡⟨ cong suc (+-assoc-0 n p) ⟩
    suc (0 + (n + p))
  ≡⟨⟩
    1 + (n + p)
  ∎

+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
  ≡⟨⟩
    suc (1 + n) + p
  ≡⟨⟩
    suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
  ≡⟨⟩
    2 + (n + p)
  ∎


--- Commutativity

--- lemma 1: identityʳ
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

--- lemma 2: suc extract from right hand
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎
  
--- commutativity proposition
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

--- Corollary: Rearranging
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ sym (+-assoc (m + n) p q) ⟩
    ((m + n) + p) + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    (m + (n + p)) + q
  ∎

{-  
Exercise 1: finite-+-assoc

day 1:
      0 : ℕ

day 2:
      1 : ℕ          (0 + 0) + 0 = 0 + (0 + 0)

day 2:
      2 : ℕ          (0 + 1) + 1 = 0 + (1 + 1)
                     (0 + 1) + 0 = 0 + (1 + 0)
                     (0 + 0) + 1 = 0 + (0 + 1)

day 3:
      3 : ℕ          (0 + 2) + 2 = 0 + (2 + 2)
                     (0 + 2) + 0 = 0 + (2 + 0)
                     (0 + 0) + 2 = 0 + (0 + 2)
                     (1 + 0) + 0 = 1 + (0 + 0)
                     (1 + 1) + 1 = 1 + (1 + 1)
                     (1 + 1) + 0 = 1 + (1 + 0)
                     (1 + 0) + 1 = 1 + (0 + 1)
-}

--- Rewrite
+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

--- Exercise +-swap (recommended)
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p 
  rewrite +-comm (suc m) (n + p) 
    | +-assoc n p (suc m) 
    | +-comm p (suc m) 
  = refl

--- Exercise *-distrib-+ (recommended)
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc p (m * p) (n * p) = refl
{- detail
*-distrib-+ (suc m) n p =
  begin
   (suc (m + n)) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
  ∎
-}

--- Exercise *-assoc (recommended)
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl
{- detail
*-assoc (suc m) n p = begin
    (suc m * n) * p
  ≡⟨⟩
    (n + (m * n)) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + (m * n) * p
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    n * p + m * (n * p)
  ∎
-}

--- Exercise *-comm (practice)
*-0-absorptivityʳ : ∀ (n : ℕ) → n * zero ≡ zero
*-0-absorptivityʳ zero = refl
*-0-absorptivityʳ (suc n) rewrite *-0-absorptivityʳ n = refl

*-suc : ∀ (m n : ℕ) → m * (suc n) ≡ m + (m * n)
*-suc zero n = refl
*-suc (suc m) n 
  rewrite *-suc m n
    | sym (+-assoc n m (m * n))
    | sym (+-assoc m n (m * n))
    | +-comm n m
  = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-0-absorptivityʳ n = refl
*-comm (suc m) n rewrite *-comm m n | *-suc n m = refl

--- Exercise 0∸n≡0 (practice)
0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

--- Exercise ∸-+-assoc (practice)
∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p rewrite 0∸n≡0 n | 0∸n≡0 p | 0∸n≡0 (n + p) = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

--- Exercise +*^ (stretch)
^-distribˡ-+-* : ∀ (m n p : ℕ) →  m ^ (n + p) ≡ (m ^ n) * (m ^ p) 
^-distribˡ-+-* m zero p rewrite +-identityʳ (m ^ p) = refl
^-distribˡ-+-* m (suc n) p 
  rewrite ^-distribˡ-+-* m n p 
    | sym (*-assoc m (m ^ n) (m ^ p))
  = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) 
  rewrite ^-distribʳ-* m n p
    | *-assoc m (m ^ p) (n * (n ^ p))
    | sym (*-assoc (m ^ p) n (n ^ p))
    | *-comm (m ^ p) n
    | *-assoc n (m ^ p) (n ^ p)
    | *-assoc m n (m ^ p * n ^ p)
  = refl
  
^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite *-comm n zero = refl
^-*-assoc m n (suc p)
  rewrite *-comm n (suc p) 
    | ^-*-assoc m n p
    | ^-distribˡ-+-* m n (p * n)
    | *-comm p n
  = refl