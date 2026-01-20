module plfa.plf.Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Function.Base using (_∘_)
open import plfa.lf.Isomorphism using (_≃_)
open import plfa.plf.Lambda

--- Values do not reduce
V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ V-ƛ        ()
V¬—→ V-zero     ()
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N

—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V M—→N VM  =  V¬—→ VM M—→N

--- Exercise Canonical-≃ (practice)
infix  4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
    → ∅ , x ⦂ A ⊢ N ⦂ B
      -----------------------------
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero :
      --------------------
      Canonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
    → Canonical V ⦂ `ℕ
      ---------------------
    → Canonical `suc V ⦂ `ℕ

Canonical-≃-well : ∀ {V A} → Canonical V ⦂ A ≃ (∅ ⊢ V ⦂ A) × (Value V)
Canonical-≃-well = record { to = to; from = from ; from∘to = from∘to; to∘from = to∘from } 
  where
    to : ∀ {V A} → Canonical V ⦂ A → (∅ ⊢ V ⦂ A) × (Value V)
    to (C-ƛ x)              = ⟨ ⊢ƛ x , V-ƛ ⟩
    to C-zero               = ⟨ ⊢zero , V-zero ⟩
    to (C-suc x) with to x
    ...        | ⟨ t , v  ⟩ = ⟨ ⊢suc t , V-suc v ⟩
    from : ∀ {V A} → (∅ ⊢ V ⦂ A) × (Value V) → Canonical V ⦂ A 
    from ⟨ ⊢ƛ t , V-ƛ ⟩       = C-ƛ t
    from ⟨ ⊢zero , V-zero ⟩   = C-zero
    from ⟨ ⊢suc t , V-suc v ⟩ = C-suc (from (⟨ t , v ⟩))
    from∘to : ∀ {V A} (x : Canonical V ⦂ A) → from (to x) ≡ x 
    from∘to (C-ƛ x)                     = refl
    from∘to C-zero                      = refl
    from∘to (C-suc x) rewrite from∘to x = refl
    to∘from : ∀ {V A} (x : (∅ ⊢ V ⦂ A) × (Value V)) → to (from x) ≡ x 
    to∘from ⟨ ⊢ƛ t , V-ƛ ⟩                                   = refl
    to∘from ⟨ ⊢zero , V-zero ⟩                               = refl
    to∘from ⟨ ⊢suc t , V-suc v ⟩ rewrite to∘from (⟨ t , v ⟩) = refl
    
--- Progress
data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢ƛ ⊢N)                            =  done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done V-ƛ with progress ⊢M
...   | step M—→M′                          =  step (ξ-·₂ V-ƛ M—→M′)
...   | done VM                             =  step (β-ƛ VM)
progress ⊢zero                              =  done V-zero
progress (⊢suc ⊢M) with progress ⊢M
...  | step M—→M′                           =  step (ξ-suc M—→M′)
...  | done VM                              =  done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→L′                            =  step (ξ-case L—→L′)
... | done (V-zero)                         =  step β-zero
... | done (V-suc VL)                       =  step (β-suc VL)
progress (⊢μ ⊢M)                            =  step β-μ

--- Exercise Progress-≃ (practice)
progress-≃ : ∀ {M} → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
progress-≃ = record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from }
  where
    to : ∀ {M} → Progress M → Value M ⊎ ∃[ N ](M —→ N)
    to (step x) = inj₂ ⟨ _ , x ⟩
    to (done x) = inj₁ x
    from : ∀ {M} → Value M ⊎ ∃[ N ](M —→ N) → Progress M
    from (inj₁ x) = done x
    from (inj₂ ⟨ t , M₁—→t ⟩) = step M₁—→t
    from∘to : ∀ {M} (x : Progress M ) → from (to x) ≡ x
    from∘to (step x) = refl
    from∘to (done x) = refl 
    to∘from : ∀ {M} (x : Value M ⊎ ∃[ N ](M —→ N)) → to (from x) ≡ x
    to∘from (inj₁ x) = refl
    to∘from (inj₂ y) = refl
    
--- Exercise progress′ (practice)
progress′ : ∀ {M A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
progress′ (⊢ƛ ⊢N)                             =  inj₁ V-ƛ
progress′ (⊢L · ⊢M) with progress′ ⊢L 
... | inj₂ ⟨ L′ , L—→L′ ⟩                     =  inj₂ ⟨ _ , ξ-·₁ L—→L′ ⟩
... | inj₁ V-ƛ with progress ⊢M
...   | step M—→M′                            =  inj₂ ⟨ _ , (ξ-·₂ V-ƛ M—→M′) ⟩
...   | done VM                               =  inj₂ ⟨ _ , (β-ƛ VM) ⟩
progress′ ⊢zero                               =  inj₁ V-zero
progress′ (⊢suc ⊢M) with progress′ ⊢M 
... | inj₁ x                                  =  inj₁ (V-suc x)
... | inj₂ y                                  =  inj₂ ⟨ `suc y .proj₁ , ξ-suc (y .proj₂) ⟩
progress′ (⊢case ⊢L ⊢M ⊢N) with progress′ ⊢L
... | inj₁ V-zero                             =  inj₂ ⟨ _ , β-zero ⟩
... | inj₁ (V-suc x)                          =  inj₂ ⟨ _ , β-suc x ⟩
... | inj₂ ⟨ L′ , L—→L′ ⟩                     =  inj₂ ⟨ _ , ξ-case L—→L′ ⟩
progress′ (⊢μ _)                              =  inj₂ ⟨ _ , β-μ ⟩ 

--- Exercise value? (practice)
value? : ∀ {M} → Progress M → Dec (Value M)
value? (done x) = yes x
value? (step x) = no (—→¬V x)

--- Renaming
ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢` ∋w)    =  ⊢` (ρ ∋w)
rename ρ (⊢ƛ ⊢N)    =  ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M)  =  (rename ρ ⊢L) · (rename ρ ⊢M)
rename ρ ⊢zero      =  ⊢zero
rename ρ (⊢suc ⊢M)  =  ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N)
                    =  ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M)    =  ⊢μ (rename (ext ρ) ⊢M)

weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  ρ ()

drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ Z                 =  Z
  ρ (S x≢x Z)         =  contradiction refl x≢x
  ρ (S z≢x (S _ ∋z))  =  S z≢x ∋z

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z                   =  S x≢y Z
  ρ (S z≢x Z)           =  Z
  ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)
  
subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _         =  weaken ⊢V
... | no  x≢y       =  contradiction refl x≢y
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl      =  contradiction refl x≢y
... | no  _         =  ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl      =  ⊢ƛ (drop ⊢N)
... | no  x≢y       =  ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢L · ⊢M)  =  (subst ⊢V ⊢L) · (subst ⊢V ⊢M)
subst ⊢V ⊢zero      =  ⊢zero
subst ⊢V (⊢suc ⊢M)  =  ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl      =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no  x≢y       =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl      =  ⊢μ (drop ⊢M)
... | no  x≢y       =  ⊢μ (subst ⊢V (swap x≢y ⊢M))

--- subst′
subst′ : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ]′ ⦂ B
subst′ {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _         =  weaken ⊢V
... | no  x≢y       =  contradiction refl x≢y
subst′ {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl      =  contradiction refl x≢y
... | no  _         =  ⊢` ∋x
subst′ {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl      =  ⊢ƛ (drop ⊢N)
... | no  x≢y       =  ⊢ƛ (subst′ ⊢V (swap x≢y ⊢N))
subst′ ⊢V (⊢L · ⊢M)  =  (subst′ ⊢V ⊢L) · (subst′ ⊢V ⊢M)
subst′ ⊢V ⊢zero      =  ⊢zero
subst′ ⊢V (⊢suc ⊢M)  =  ⊢suc (subst′ ⊢V ⊢M)
subst′ {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N)  with x ≟ y
... | yes refl      =  ⊢case (subst′ ⊢V ⊢L) (subst′ ⊢V ⊢M) (drop ⊢N)
... | no  x≢y       =  ⊢case (subst′ ⊢V ⊢L) (subst′ ⊢V ⊢M) (subst′ ⊢V (swap x≢y ⊢N))
subst′ {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl      =  ⊢μ (drop ⊢M)
... | no  x≢y       =  ⊢μ (subst′ ⊢V (swap x≢y ⊢M)) 


--- Preservation
preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (⊢` ())
preserve (⊢ƛ ⊢N)                 ()
preserve (⊢L · ⊢M)               (ξ-·₁ L—→L′)     =  (preserve ⊢L L—→L′) · ⊢M
preserve (⊢L · ⊢M)               (ξ-·₂ VL M—→M′)  =  ⊢L · (preserve ⊢M M—→M′)
preserve ((⊢ƛ ⊢N) · ⊢V)          (β-ƛ VV)         =  subst ⊢V ⊢N
preserve ⊢zero                   ()
preserve (⊢suc ⊢M)               (ξ-suc M—→M′)    =  ⊢suc (preserve ⊢M M—→M′)
preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L—→L′)   =  ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
preserve (⊢case ⊢zero ⊢M ⊢N)     (β-zero)         =  ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc VV)       =  subst ⊢V ⊢N
preserve (⊢μ ⊢M)                 (β-μ)            =  subst (⊢μ ⊢M) ⊢M

--- Evaluation
sucμ  =  μ "x" ⇒ `suc (` "x")

_ =
  begin
    sucμ
  —→⟨ β-μ ⟩
    `suc sucμ
  —→⟨ ξ-suc β-μ ⟩
    `suc `suc sucμ
  —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc `suc `suc sucμ
  --  ...
  ∎
  
record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished (N : Term) : Set where

  done :
      Value N
      ----------
    → Finished N

  out-of-gas :
      ----------
      Finished N

data Steps (L : Term) : Set where

  steps : ∀ {N}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {L A}
  → Gas
  → ∅ ⊢ L ⦂ A
    ---------
  → Steps L
eval {L} (gas zero)    ⊢L                     =  steps (L ∎) out-of-gas
eval {L} (gas (suc m)) ⊢L with progress ⊢L
... | done VL                                 =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) (preserve ⊢L L—→M)
...    | steps M—↠N fin                       =  steps (L —→⟨ L—→M ⟩ M—↠N) fin

--- example
⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` ∋x))
  where
  ∋x = Z

_ : eval (gas 3) ⊢sucμ ≡
  steps
   (μ "x" ⇒ `suc ` "x"
   —→⟨ β-μ ⟩
    `suc (μ "x" ⇒ `suc ` "x")
   —→⟨ ξ-suc β-μ ⟩
    `suc (`suc (μ "x" ⇒ `suc ` "x"))
   —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc (`suc (`suc (μ "x" ⇒ `suc ` "x")))
   ∎)
   out-of-gas
_ = refl

_ : eval (gas 100) ⊢2+2 ≡
  steps
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
       ])))
    · `suc (`suc `zero)
    · `suc (`suc `zero)
   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       · ` "m"
       · ` "n")
      ]))
    · `suc (`suc `zero)
    · `suc (`suc `zero)
   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "m"
      · ` "n")
     ])
    · `suc (`suc `zero)
   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "m"
     · `suc (`suc `zero))
    ]
   —→⟨ β-suc (V-suc V-zero) ⟩
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · `suc `zero
     · `suc (`suc `zero))
   —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc
    ((ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     · `suc `zero
     · `suc (`suc `zero))
   —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc
    ((ƛ "n" ⇒
      case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       · ` "m"
       · ` "n")
      ])
     · `suc (`suc `zero))
   —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc
    case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "m"
     · `suc (`suc `zero))
    ]
   —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc
    (`suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · `zero
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc
    (`suc
     ((ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒
        `suc
        ((μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · ` "m"
         · ` "n")
        ]))
      · `zero
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc
    (`suc
     ((ƛ "n" ⇒
       case `zero [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ])
      · `suc (`suc `zero)))
   —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc
    (`suc
     case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "m"
      · `suc (`suc `zero))
     ])
   —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
   ∎)
   (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl

_ : eval (gas 100) ⊢2+2ᶜ ≡
  steps
   ((ƛ "m" ⇒
     (ƛ "n" ⇒
      (ƛ "s" ⇒ (ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z")))))
    · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
    · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
    · (ƛ "n" ⇒ `suc ` "n")
    · `zero
   —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒
     (ƛ "s" ⇒
      (ƛ "z" ⇒
       (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" ·
       (` "n" · ` "s" · ` "z"))))
    · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
    · (ƛ "n" ⇒ `suc ` "n")
    · `zero
   —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒
     (ƛ "z" ⇒
      (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" ·
      ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" · ` "z")))
    · (ƛ "n" ⇒ `suc ` "n")
    · `zero
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒
     (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
     ·
     ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
      · ` "z"))
    · `zero
   —→⟨ β-ƛ V-zero ⟩
    (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
    ·
    ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
     · `zero)
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
     · `zero)
   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    ((ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
     `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    ((ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `zero))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    ((ƛ "n" ⇒ `suc ` "n") · `suc `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    `suc (`suc `zero)
   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `suc (`suc `zero))
   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒ `suc ` "n") · `suc (`suc (`suc `zero))
   —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
    `suc (`suc (`suc (`suc `zero)))
   ∎)
   (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl

⊢2*2 : ∅ ⊢ mul · two · two ⦂ `ℕ
⊢2*2 = ⊢mul · ⊢two · ⊢two

_ : eval (gas 100) ⊢2*2 ≡
  steps
    ((μ "*" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ `zero |suc "m" ⇒
        (μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · (` "*" · ` "m" · ` "n")
        · ` "n"
        ])))
     · `suc (`suc `zero)
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ `zero |suc "m" ⇒
       (μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       ·
       ((μ "*" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ `zero |suc "m" ⇒
           (μ "+" ⇒
            (ƛ "m" ⇒
             (ƛ "n" ⇒
              case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
              ])))
           · (` "*" · ` "m" · ` "n")
           · ` "n"
           ])))
        · ` "m"
        · ` "n")
       · ` "n"
       ]))
     · `suc (`suc `zero)
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
     (ƛ "n" ⇒
      case `suc (`suc `zero) [zero⇒ `zero |suc "m" ⇒
      (μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      ·
      ((μ "*" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ `zero |suc "m" ⇒
          (μ "+" ⇒
           (ƛ "m" ⇒
            (ƛ "n" ⇒
             case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
             ])))
          · (` "*" · ` "m" · ` "n")
          · ` "n"
          ])))
       · ` "m"
       · ` "n")
      · ` "n"
      ])
     · `suc (`suc `zero)
     —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
     case `suc (`suc `zero) [zero⇒ `zero |suc "m" ⇒
     (μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     ·
     ((μ "*" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ `zero |suc "m" ⇒
         (μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · (` "*" · ` "m" · ` "n")
         · ` "n"
         ])))
      · ` "m"
      · `suc (`suc `zero))
     · `suc (`suc `zero)
     ]
     —→⟨ β-suc (V-suc V-zero) ⟩
     (μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     ·
     ((μ "*" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ `zero |suc "m" ⇒
         (μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · (` "*" · ` "m" · ` "n")
         · ` "n"
         ])))
      · `suc `zero
      · `suc (`suc `zero))
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     ·
     ((μ "*" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ `zero |suc "m" ⇒
         (μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · (` "*" · ` "m" · ` "n")
         · ` "n"
         ])))
      · `suc `zero
      · `suc (`suc `zero))
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ))) ⟩
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     ·
     ((ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ `zero |suc "m" ⇒
        (μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        ·
        ((μ "*" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ `zero |suc "m" ⇒
            (μ "+" ⇒
             (ƛ "m" ⇒
              (ƛ "n" ⇒
               case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
               ])))
            · (` "*" · ` "m" · ` "n")
            · ` "n"
            ])))
         · ` "m"
         · ` "n")
        · ` "n"
        ]))
      · `suc `zero
      · `suc (`suc `zero))
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc V-zero)))) ⟩
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     ·
     ((ƛ "n" ⇒
       case `suc `zero [zero⇒ `zero |suc "m" ⇒
       (μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       ·
       ((μ "*" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ `zero |suc "m" ⇒
           (μ "+" ⇒
            (ƛ "m" ⇒
             (ƛ "n" ⇒
              case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
              ])))
           · (` "*" · ` "m" · ` "n")
           · ` "n"
           ])))
        · ` "m"
        · ` "n")
       · ` "n"
       ])
      · `suc (`suc `zero))
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     ·
     case `suc `zero [zero⇒ `zero |suc "m" ⇒
     (μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     ·
     ((μ "*" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ `zero |suc "m" ⇒
         (μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · (` "*" · ` "m" · ` "n")
         · ` "n"
         ])))
      · ` "m"
      · `suc (`suc `zero))
     · `suc (`suc `zero)
     ]
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (ξ-·₂ V-ƛ (β-suc V-zero)) ⟩
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     ·
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      ·
      ((μ "*" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ `zero |suc "m" ⇒
          (μ "+" ⇒
           (ƛ "m" ⇒
            (ƛ "n" ⇒
             case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
             ])))
          · (` "*" · ` "m" · ` "n")
          · ` "n"
          ])))
       · `zero
       · `suc (`suc `zero))
      · `suc (`suc `zero))
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ))) ⟩
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     ·
     ((ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒
        `suc
        ((μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · ` "m"
         · ` "n")
        ]))
      ·
      ((μ "*" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ `zero |suc "m" ⇒
          (μ "+" ⇒
           (ƛ "m" ⇒
            (ƛ "n" ⇒
             case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
             ])))
          · (` "*" · ` "m" · ` "n")
          · ` "n"
          ])))
       · `zero
       · `suc (`suc `zero))
      · `suc (`suc `zero))
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ))))) ⟩
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     ·
     ((ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒
        `suc
        ((μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · ` "m"
         · ` "n")
        ]))
      ·
      ((ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ `zero |suc "m" ⇒
         (μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         ·
         ((μ "*" ⇒
           (ƛ "m" ⇒
            (ƛ "n" ⇒
             case ` "m" [zero⇒ `zero |suc "m" ⇒
             (μ "+" ⇒
              (ƛ "m" ⇒
               (ƛ "n" ⇒
                case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
                ])))
             · (` "*" · ` "m" · ` "n")
             · ` "n"
             ])))
          · ` "m"
          · ` "n")
         · ` "n"
         ]))
       · `zero
       · `suc (`suc `zero))
      · `suc (`suc `zero))
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-zero))))) ⟩
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     ·
     ((ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒
        `suc
        ((μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · ` "m"
         · ` "n")
        ]))
      ·
      ((ƛ "n" ⇒
        case `zero [zero⇒ `zero |suc "m" ⇒
        (μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        ·
        ((μ "*" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ `zero |suc "m" ⇒
            (μ "+" ⇒
             (ƛ "m" ⇒
              (ƛ "n" ⇒
               case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
               ])))
            · (` "*" · ` "m" · ` "n")
            · ` "n"
            ])))
         · ` "m"
         · ` "n")
        · ` "n"
        ])
       · `suc (`suc `zero))
      · `suc (`suc `zero))
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))))))
     ⟩
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     ·
     ((ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒
        `suc
        ((μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · ` "m"
         · ` "n")
        ]))
      ·
      case `zero [zero⇒ `zero |suc "m" ⇒
      (μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      ·
      ((μ "*" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ `zero |suc "m" ⇒
          (μ "+" ⇒
           (ƛ "m" ⇒
            (ƛ "n" ⇒
             case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
             ])))
          · (` "*" · ` "m" · ` "n")
          · ` "n"
          ])))
       · ` "m"
       · `suc (`suc `zero))
      · `suc (`suc `zero)
      ]
      · `suc (`suc `zero))
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₂ V-ƛ β-zero))) ⟩
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     ·
     ((ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒
        `suc
        ((μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · ` "m"
         · ` "n")
        ]))
      · `zero
      · `suc (`suc `zero))
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-zero))) ⟩
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     ·
     ((ƛ "n" ⇒
       case `zero [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ])
      · `suc (`suc `zero))
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     ·
     case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "m"
      · `suc (`suc `zero))
     ]
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (ξ-·₂ V-ƛ β-zero) ⟩
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ]))
     · `suc (`suc `zero)
     · `suc (`suc `zero)
     —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
     (ƛ "n" ⇒
      case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       · ` "m"
       · ` "n")
      ])
     · `suc (`suc `zero)
     —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
     case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "m"
      · `suc (`suc `zero))
     ]
     —→⟨ β-suc (V-suc V-zero) ⟩
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · `suc `zero
      · `suc (`suc `zero))
     —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
     `suc
     ((ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒
        `suc
        ((μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · ` "m"
         · ` "n")
        ]))
      · `suc `zero
      · `suc (`suc `zero))
     —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
     `suc
     ((ƛ "n" ⇒
       case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ])
      · `suc (`suc `zero))
     —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
     `suc
     case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "m"
      · `suc (`suc `zero))
     ]
     —→⟨ ξ-suc (β-suc V-zero) ⟩
     `suc
     (`suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       · `zero
       · `suc (`suc `zero)))
     —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
     `suc
     (`suc
      ((ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒
         `suc
         ((μ "+" ⇒
           (ƛ "m" ⇒
            (ƛ "n" ⇒
             case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
             ])))
          · ` "m"
          · ` "n")
         ]))
       · `zero
       · `suc (`suc `zero)))
     —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
     `suc
     (`suc
      ((ƛ "n" ⇒
        case `zero [zero⇒ ` "n" |suc "m" ⇒
        `suc
        ((μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · ` "m"
         · ` "n")
        ])
       · `suc (`suc `zero)))
     —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
     `suc
     (`suc
      case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       · ` "m"
       · `suc (`suc `zero))
      ])
     —→⟨ ξ-suc (ξ-suc β-zero) ⟩ `suc (`suc (`suc (`suc `zero))) ∎)
    (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl

--- Exercise : recite progress-preservation
{-  
  Progress : 
    L --> M              Value M
    ----------          ----------
    Progress L          Progress M
  
  progress : 
    ∅ ⊢ M ⦂ A 
    ----------
    Progress M
  
  preservation :
    ∅ ⊢ M ⦂ A 
    M --> N
    ---------
    ∅ ⊢ N ⦂ A 
-}

--- Exercise : subject_expansion
{- 
subject_expansion : 
  M --> N
  ∅ ⊢ N ⦂ A
  ----------
  ∅ ⊢ M ⦂ A

ans 1 : 
  M = (λx. x x) (λx. x)
  M --> N : (λx. x) (λx. x)  is well typed, but M isn't well-typed
-}

--- Well-typed terms don’t get stuck
Normal : Term → Set
Normal M  =  ∀ {N} → ¬ (M —→ N)

Stuck : Term → Set
Stuck M  =  Normal M × ¬ Value M

unstuck : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    -----------
  → ¬ (Stuck M)
unstuck t ⟨ normal , ¬val ⟩ with progress t 
... | step x = normal x
... | done x = ¬val x

preserves : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    ---------
  → ∅ ⊢ N ⦂ A
preserves ⊢M (M ∎)               = ⊢M
preserves ⊢M (L —→⟨ L—→M ⟩ M—↠N) = preserves (preserve ⊢M L—→M)  M—↠N

wttdgs : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    -----------
  → ¬ (Stuck N)
wttdgs ⊢M M—↠N = unstuck (preserves ⊢M M—↠N)

--- Reduction is deterministic
cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl

det : ∀ {M M′ M″}
  → (M —→ M′)
  → (M —→ M″)
    --------
  → M′ ≡ M″
det (ξ-·₁ L—→L′)   (ξ-·₁ L—→L″)     =  cong₂ _·_ (det L—→L′ L—→L″) refl
det (ξ-·₁ L—→L′)   (ξ-·₂ VL M—→M″)  =  contradiction L—→L′ (V¬—→ VL)
det (ξ-·₁ L—→L′)   (β-ƛ _)          =  contradiction L—→L′ (V¬—→ V-ƛ)
det (ξ-·₂ VL _)    (ξ-·₁ L—→L″)     =  contradiction L—→L″ (V¬—→ VL)
det (ξ-·₂ _ M—→M′) (ξ-·₂ _ M—→M″)   =  cong₂ _·_ refl (det M—→M′ M—→M″)
det (ξ-·₂ _ M—→M′) (β-ƛ VM)         =  contradiction M—→M′ (V¬—→ VM)
det (β-ƛ _)        (ξ-·₁ L—→L″)     =  contradiction L—→L″ (V¬—→ V-ƛ)
det (β-ƛ VM)       (ξ-·₂ _ M—→M″)   =  contradiction M—→M″ (V¬—→ VM)
det (β-ƛ _)        (β-ƛ _)          =  refl
det (ξ-suc M—→M′)  (ξ-suc M—→M″)    =  cong `suc_ (det M—→M′ M—→M″)
det (ξ-case L—→L′) (ξ-case L—→L″)   =  cong₄ case_[zero⇒_|suc_⇒_]
                                         (det L—→L′ L—→L″) refl refl refl
det (ξ-case L—→L′) β-zero           =  contradiction L—→L′ (V¬—→ V-zero)
det (ξ-case L—→L′) (β-suc VL)       =  contradiction L—→L′ (V¬—→ (V-suc VL))
det β-zero         (ξ-case M—→M″)   =  contradiction M—→M″ (V¬—→ V-zero)
det β-zero         β-zero           =  refl
det (β-suc VL)     (ξ-case L—→L″)   =  contradiction L—→L″ (V¬—→ (V-suc VL))
det (β-suc _)      (β-suc _)        =  refl
det β-μ            β-μ              =  refl
