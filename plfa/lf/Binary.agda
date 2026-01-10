module plfa.lf.Binary where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)

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
from (x  O) = 0 + 2 * (from x)
from (x  I) = 1 + 2 * (from x)

_ : from (⟨⟩ I O I) ≡ 5
_ = refl 

_ : from (to 10) ≡ 10
_ = refl

--- Bin-laws
from-lemma₁ : ∀ (b : Bin) → from (b I) ≡ 1 + from (b O)
from-lemma₁ ⟨⟩ = refl
from-lemma₁ (b O) = refl
from-lemma₁ (b I) = refl

from-lemma₀ : ∀ (b : Bin) → from (b O) ≡ 2 * (from b)
from-lemma₀ ⟨⟩ = refl
from-lemma₀ (b O) = refl
from-lemma₀ (b I) = refl

law₁ : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
law₁ ⟨⟩                            =  refl
law₁ (b O)  rewrite from-lemma₁ b  =  refl
law₁ (b I) 
  rewrite from-lemma₁ b 
    | from-lemma₀ (inc b) 
    | from-lemma₀ b 
    | law₁ b 
    | +-suc (from b) (from b + 0)
  = refl

-- to∘from : ∀ (b : Bin) → to (from b) ≡ b
-- false

from∘to : ∀ (n : ℕ) → from (to n) ≡ n
from∘to zero = refl
from∘to (suc n) rewrite law₁ (to n) | cong suc (from∘to n) = refl

--- Bin-predicates
data One : Bin → Set where
  ⟨⟩I : One (⟨⟩ I)
  _O  : {b : Bin} → One b → One (b O)  
  _I  : {b : Bin} → One b → One (b I)  
  

data Can : Bin → Set where
  zero : Can (⟨⟩ O)
  bin  : {b : Bin} → One b → Can b

inc-one : ∀ {b : Bin}
  → One b
    -----
  → One (inc b)
inc-one ⟨⟩I = ⟨⟩I O
inc-one (ob O) = ob I
inc-one (ob I) = inc-one ob O 

inc-can : ∀ {b : Bin}
  → Can b
    -----------
  → Can (inc b)
inc-can zero     = bin ⟨⟩I
inc-can (bin ob) = bin (inc-one ob)


to-can : ∀ (n : ℕ) → Can (to n)
to-can zero    = zero
to-can (suc n) = inc-can (to-can n)

--- Bin-embedding
open import plfa.lf.Isomorphism using (_≲_)

bin-embedding :  ℕ ≲ Bin
bin-embedding = 
  record 
    { to = to 
    ; from = from 
    ; from∘to = from∘to 
    }
    
--- Bin-isomorphism