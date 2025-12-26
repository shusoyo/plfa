module plfa.lf.Nat where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

--- Addition
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

--- Multiplication
_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

--- Power
_^_ : ℕ → ℕ → ℕ
m ^ zero  = suc (zero)
m ^ suc n = m * (m ^ n)

--- Monus
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

--- Binary
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin
  
inc : Bin → Bin
inc ⟨⟩    = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

_ : inc (inc (inc (inc (inc (⟨⟩ O))))) ≡ ⟨⟩ I O I
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc x) = inc (to x)

_ : to 5 ≡ ⟨⟩ I O I
_ = 
  begin
    inc (to 4)
  ≡⟨⟩
    inc (inc (to 3))
  ≡⟨⟩
    inc (inc (inc (inc (inc (to 0)))))
  ≡⟨⟩
    inc (inc (inc (inc (inc (⟨⟩ O)))))
  ≡⟨⟩
    inc (inc (inc (inc (⟨⟩ I))))
  ≡⟨⟩
    ⟨⟩ I O I
  ∎

from : Bin → ℕ
from ⟨⟩     = 0
from (⟨⟩ O) = 0
from (⟨⟩ I) = 1
from (x  I) = 1 + 2 * (from x)
from (x  O) = 0 + 2 * (from x)

_ : from (⟨⟩ I O I) ≡ 5
_ = refl 