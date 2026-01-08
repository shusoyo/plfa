module plfa.lf.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Negation using (contradiction)
open import plfa.lf.Isomorphism using (_≃_; extensionality; _∘_)

--- Negation
¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ ¬A → ¬A x

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x x  =  ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

--- neq
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ () 

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → contradiction x ¬x)

open import plfa.lf.Relations using (_<_; s<s; Trichotomy; forward; equality; flipped)

<-irreflexive : ∀ (n : ℕ) → ¬ n < n
<-irreflexive zero = λ ()
<-irreflexive (suc n) (s<s n<n) = <-irreflexive n n<n

--- proof Mutual exclusion
<⇒¬> : ∀ (m n : ℕ) → m < n → ¬ n < m
<⇒¬> (suc m) (suc n) (s<s m<n) (s<s n<m) = <⇒¬> m n m<n n<m

<⇒¬≡ : ∀ (m n : ℕ) → m < n → ¬ n ≡ m
<⇒¬≡ m       zero                    =  λ ()
<⇒¬≡ zero    (suc n) z<sn            =  λ ()
<⇒¬≡ (suc m) (suc n) (s<s m<n) refl  =  <⇒¬≡ m n m<n refl

≡⇒¬< : ∀ (m n : ℕ) → m ≡ n → ¬ n < m
≡⇒¬< (suc m) n refl (s<s m<m) = ≡⇒¬< m m refl m<m

≡⇒¬> : ∀ (m n : ℕ) → m ≡ n → ¬ m < n
≡⇒¬> m n refl  =  ≡⇒¬< m m refl

>⇒¬< : ∀ (m n : ℕ) → n < m → ¬ m < n
>⇒¬< m zero = λ z ()
>⇒¬< zero (suc n) = λ ()
>⇒¬< (suc m) (suc n) (s<s n<m) (s<s m<n) = >⇒¬< m n n<m m<n

>⇒¬≡ : ∀ (m n : ℕ) → n < m → ¬ n ≡ m
>⇒¬≡ zero n = λ ()
>⇒¬≡ (suc m) zero = λ z ()
>⇒¬≡ (suc m) (suc n) (s<s n<m) refl = >⇒¬≡ m m n<m refl

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-×  = 
  record
    { to = λ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩
    ; from = λ (⟨ fa ,  fb ⟩) → λ{(inj₁ a) → fa a; (inj₂ b) → fb b}
    ; from∘to = λ x → refl
    ; to∘from = λ y → refl
    }

--- ¬ (A × B) ≃ (¬ A) ⊎ (¬ B) ? isomorphism or embedding ?
--- TODO!


--- Excluded middle is irrefutable
postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ (λ x → k (inj₁ x)))

--- Exercise Classical (stretch)
em→peirce : ∀ {A B : Set} 
  → A ⊎ ¬ A 
    -----------------
  → ((A → B) → A) → A
em→peirce (inj₁  a) f  =  a
em→peirce (inj₂ ¬a) f  =  f (λ a → ⊥-elim (¬a a))

peirce→em : ∀ {A B : Set} 
  → ((A → B) → A) → A
    -----------------
  → A ⊎ ¬ A 
peirce→em = λ z → inj₁


em→dne : ∀ {A : Set} → A ⊎ ¬ A → ¬ ¬ A → A
em→dne (inj₁ x) _ = x
em→dne (inj₂ y) f = ⊥-elim (f y)

dne→em : ∀ {A : Set} → ¬ ¬ A → A → A ⊎ ¬ A 
dne→em  = λ z → inj₁

em→impli-disj : ∀ {A B : Set}
  → A ⊎ ¬ A 
    -----------------
  → (A → B) → ¬ A ⊎ B
em→impli-disj (inj₁ x) = λ z → inj₂ (z x)
em→impli-disj (inj₂ y) = λ z → inj₁ y

disj→dem : ∀ {A B : Set}
  → A ⊎ ¬ A 
    ---------------------
  → ¬ (¬ A × ¬ B) → A ⊎ B
disj→dem (inj₁ x) = λ z → inj₁ x
disj→dem {A} {B} (inj₂ ¬a) ¬p =  helper (em {B})
  where
    helper : B ⊎ ¬ B → A ⊎ B
    helper (inj₁ b) = inj₂ b
    helper (inj₂ ¬b) = ⊥-elim (¬p (⟨ ¬a , ¬b ⟩))

--- Exercise Stable (stretch)
Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀ {A : Set} → Stable (¬ A)
¬-stable f a = f (¬¬-intro (a))

stable-stable : ∀ {A B : Set} 
  → Stable A
  → Stable B
  → Stable (A × B) 
stable-stable sa sb ¬¬ab = ⟨ sa (λ z → ¬¬ab (λ (⟨ proj₁ , _ ⟩) → z proj₁)) ,
  sb (λ z → ¬¬ab (λ z₁ → z (z₁ .proj₂))) ⟩
