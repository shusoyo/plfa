module plfa.lf.Binary where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

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

from-lemma : ∀ (b : Bin) → from (b I) ≡ 1 + from (b O)
from-lemma ⟨⟩ = refl
from-lemma (b O) = refl
from-lemma (b I) = refl
{- 
inc-between-bin-nat : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
inc-between-bin-nat ⟨⟩ = refl
inc-between-bin-nat (b O) rewrite from-lemma b = refl
inc-between-bin-nat (b I) = {!   !}
 -}
