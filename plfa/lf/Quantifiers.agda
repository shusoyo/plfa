module plfa.lf.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.lf.Isomorphism using (_≃_; extensionality; ∀-extensionality)
open import Function using (_∘_)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M

--- Exercise ∀-distrib-×
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =  
  record
    { to   = λ{f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩}
    ; from = λ{⟨ f , g ⟩ → λ{x → ⟨ f x , g x ⟩}}
    ; from∘to = λ x → refl
    ; to∘from = λ y → refl
    }
    
--- Exercise ⊎∀-implies-∀⊎
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ f) = inj₁ ∘ f
⊎∀-implies-∀⊎ (inj₂ g) = inj₂ ∘ g

--- Exercise ∀-× 
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

--- 令 B 作为由 Tri 索引的一个类型，也就是说 B : Tri → Set。 
--- 证明 ∀ (x : Tri) → B x 和 B aa × B bb × B cc 是同构的
tri-≃ : ∀ {B : Tri → Set}
  → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
tri-≃ = 
  record
    { to   = λ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
    ; from = λ{tri → 
        λ{aa → tri .proj₁
        ; bb → tri .proj₂ .proj₁
        ; cc → tri .proj₂ .proj₂}
        }
    ; from∘to = λ f → 
        ∀-extensionality (λ{aa → refl; bb → refl; cc → refl})
    ; to∘from = λ tp → refl
    }

--- Existentials
record Σ (A : Set) (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    proj₁ : A
    proj₂ : B proj₁

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → Bx) = Σ[ x ∈ A ] Bx

data Σ′ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩′ : (x : A) → B x → Σ′ A B

proj₁′ : ∀ {A : Set} {B : A → Set} → Σ′ A B → A
proj₁′ ⟨ x , y ⟩′ = x

proj₂′ : ∀ {A : Set} {B : A → Set} → ∀ (w : Σ′ A B) → B (proj₁′ w)
proj₂′ ⟨ x , y ⟩′ = y

_×′_ : Set → Set → Set
A ×′ B = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → refl }
    }
    
--- Exercise ∃-distrib-⊎ (recommended)
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} 
  → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to = λ{(⟨ x , inj₁ Bx ⟩) → inj₁ ⟨ x , Bx ⟩
           ; (⟨ x , inj₂ Cx ⟩) → inj₂ ⟨ x , Cx ⟩}
    ; from = λ{(inj₁ ⟨ x , Bx ⟩) → ⟨ x , inj₁ Bx ⟩
             ; (inj₂ ⟨ x , Cx ⟩) → ⟨ x , inj₂ Cx ⟩}
    ; from∘to = λ{⟨ x , inj₁ x₁ ⟩ → refl
                ; ⟨ x , inj₂ y ⟩ → refl}
    ; to∘from = λ {(inj₁ x) → refl
                 ; (inj₂ y) → refl}
    }

--- Exercise ∃×-implies-×∃
∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , ⟨ Bx , Cx ⟩ ⟩  = ⟨ ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩ ⟩

{- 
×∃-implies-∃× : ∀ {A : Set} {B C : A → Set} 
  → (∃[ x ] B x) × (∃[ x ] C x)
    ---------------------------
  → ∃[ x ] (B x × C x) 
--- is false
-}

∃-⊎ : ∀ {B : Tri → Set}
  → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ = 
  record
    { to = λ{⟨ aa , Bx ⟩ → inj₁ Bx
            ; ⟨ bb , Bx ⟩ → inj₂ (inj₁ Bx)
            ; ⟨ cc , Bx ⟩ → inj₂ (inj₂ Bx)}
    ; from = λ{(inj₁ x) → ⟨ aa , x ⟩
             ; (inj₂ (inj₁ x)) → ⟨ bb , x ⟩
             ; (inj₂ (inj₂ y)) → ⟨ cc , y ⟩}
    ; from∘to = λ{⟨ aa , Bx ⟩ → refl
                ; ⟨ bb , Bx ⟩ → refl
                ; ⟨ cc , Bx ⟩ → refl}
    ; to∘from = λ{(inj₁ x) → refl
                ; (inj₂ (inj₁ x)) → refl
                ; (inj₂ (inj₂ y)) → refl}
    }


--- An existential example
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩


∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)

--- Exercise ∃-even-odd (practice)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)

∃-even′ : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
∃-odd′  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n

∃-even′ ⟨ zero  , refl ⟩ = even-zero
∃-even′ ⟨ suc m , refl ⟩  
  rewrite +-suc m (m + zero)
    | sym (+-identityʳ (m + (m + 0)))
    | sym (+-suc (m + (m + 0)) 0)
  = even-suc (∃-odd′ ⟨ m , refl ⟩)
  
∃-odd′ ⟨ m , refl ⟩ 
  rewrite +-identityʳ m 
    | +-comm (m + m) 1
    | sym (+-identityʳ (m + m)) 
    | +-assoc m m 0 
  = odd-suc (∃-even′ ⟨ m , refl ⟩)
  
open import plfa.lf.Isomorphism using (_⇔_)
open import plfa.lf.Relations using (_≤_; z≤n; s≤s; ≤-refl; +-monoˡ-≤)

--- Exercise ∃-+-≤ (practice)
∃-+-≤-to : ∀ {y z : ℕ} → ∃[ x ] (x + y ≡ z) → y ≤ z
∃-+-≤-to {y} {z} =  λ{⟨ zero , refl ⟩ → ≤-refl; ⟨ suc x , refl ⟩ → +-monoˡ-≤ z≤n}

-- ∃-+-≤-from : ∀ {y z : ℕ} → y ≤ z → ∃[ x ] (x + y ≡ z)
-- ∃-+-≤-from = ? 

--- Existentials, Universals, and Negation
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → refl }
    ; to∘from =  λ{ ∀¬xy → refl }
    }

--- Exercise ∃¬-implies-¬∀ (recommended)
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ = λ{y → ¬Bx (y x)}