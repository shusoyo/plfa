module plfa.plf.Lambda where

open import Data.Bool.Base using (Bool; true; false; T; not)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit.Base using (tt)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Nullary.Decidable using (Dec; yes; no; False; toWitnessFalse; ¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term

--- example
two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]
           
twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

var? : (t : Term) → Bool
var? (` _)  =  true
var? _      =  false

ƛ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
ƛ′_⇒_ (` x) N = ƛ x ⇒ N

case′_[zero⇒_|suc_⇒_] : Term → Term → (t : Term) → {_ : T (var? t)} → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]

μ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"

--- Exercise
mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ `zero
          |suc "m" ⇒ plus · (` "*" · ` "m" · ` "n"  ) · ` "n" ]
      
mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
      ` "m" · (` "n" · ` "s") · ` "z"

pow : Term
pow = μ′ ^ ⇒ ƛ′ m ⇒ ƛ′ n ⇒
        case′ n
          [zero⇒ (case′ m [zero⇒ `suc `zero |suc m ⇒ `zero ])
          |suc n ⇒ mul · m · (^ · m · n )  ]
  where
  ^  =  ` "^"
  m  =  ` "m"
  n  =  ` "n"
  
data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _         = V
... | no  _         = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = ƛ x ⇒ N
... | no  _         = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]  = L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]  = `zero
(`suc M) [ y := V ] = `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = μ x ⇒ N
... | no  _         = μ x ⇒ N [ y := V ]

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]
      ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl


judge : ∀ {A : Set} → Dec A → Term → Term → Term
judge (yes _) _ t = t
judge (no  _) t _ = t

_[_:=_]′ : Term → Id → Term → Term
(`zero)                        [ y := V ]′  =  `zero
(`suc M)                       [ y := V ]′  =  `suc M [ y := V ]′
(L · M)                        [ y := V ]′  =  L [ y := V ]′ · M [ y := V ]′
(` x)                          [ y := V ]′  =  judge (x ≟ y) V         (` x)
(ƛ x ⇒ N)                      [ y := V ]′  =  judge (x ≟ y) (ƛ x ⇒ N) (ƛ x ⇒ N [ y := V ]′)
(μ x ⇒ N)                      [ y := V ]′  =  judge (x ≟ y) (μ x ⇒ N) (μ x ⇒ N [ y := V ]′)
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ]′  = 
  judge (x ≟ y) (case L [ y := V ]′ [zero⇒ M [ y := V ]′ |suc x ⇒ N ])
                (case L [ y := V ]′ [zero⇒ M [ y := V ]′ |suc x ⇒ N [ y := V ]′ ])

--- reduction
infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      ------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ---------
    → M —↠ M

  step—→ : ∀ L {M N}
    → M —↠ N
    → L —→ M
      ---------
    → L —↠ N

pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N

open import plfa.lf.Isomorphism using (_≲_)

—↠-trans : ∀ {L M N : Term} → L —↠ M → M —↠ N → L —↠ N
—↠-trans (M ∎) b = b
—↠-trans (L —→⟨ x ⟩ a) b = step—→ L (—↠-trans a b) x

—↠≲—↠′ : ∀ {a b : Term} → a —↠ b ≲ a —↠′ b
—↠≲—↠′ = 
  record 
    { to = to′
    ; from = from′
    ; from∘to = from∘to′
    }
  where
    to′ : ∀ {a b : Term} → a —↠ b → a —↠′ b
    to′ (M ∎)          =  refl′
    to′ (L —→⟨ f ⟩ g)  =  trans′ (step′ f)  (to′ g)
    from′ : ∀ {a b : Term} → a —↠′ b → a —↠ b 
    from′ refl′         =  _ ∎
    from′ (step′ x)     =  step—→ _ (_ ∎) x
    from′ (trans′ f g)  =  —↠-trans (from′ f) (from′ g)
    from∘to′ : ∀ {a b : Term} (x : a —↠ b) → from′ (to′ x) ≡ x 
    from∘to′ (M ∎)                             =  refl
    from∘to′ (L —→⟨ f ⟩ g) rewrite from∘to′ g  =  refl
    
postulate
  confluence : ∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

  diamond : ∀ {L M N}
    → ((L —→ M) × (L —→ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

postulate
  deterministic : ∀ {L M N}
    → L —→ M
    → L —→ N
      ------
    → M ≡ N

_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
  ∎

_ : plus · two · two —↠ `suc `suc `suc `suc `zero
_ =
  begin
    plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
      case two [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
         · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ]
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ "n" ⇒
      case `suc `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (case `suc `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc `suc (plus · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc `suc ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc `suc (case `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎

_ : plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero —↠ `suc `suc `suc `suc `zero
_ =
  begin
    (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (twoᶜ · ` "s" · ` "z")) · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (sucᶜ · `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (`suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc `suc `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · (`suc `suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎

--- plus-example
plus-example : plus · (`suc `zero) · (`suc `zero) —↠ `suc `suc `zero
plus-example = 
  begin
    plus · (`suc `zero) · (`suc `zero)
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (
      ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ ` "n"
          |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]
    ) · (`suc `zero) · (`suc `zero)
  —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
    (
      ƛ "n" ⇒
        case (`suc `zero) 
          [zero⇒ ` "n" 
          |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]
    ) · `suc `zero 
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    case (`suc `zero) 
      [zero⇒ `suc `zero 
      |suc "m" ⇒ `suc (plus · ` "m" · `suc `zero) ]
  —→⟨ β-suc V-zero ⟩
    `suc (plus · `zero · `suc `zero)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc (
      (
        ƛ "m" ⇒ (ƛ "n" ⇒
          case ` "m" 
            [zero⇒ ` "n" 
            |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
      ) · `zero · `suc `zero
    )
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩
    `suc (
      (
        ƛ "n" ⇒
          case `zero 
            [zero⇒ ` "n" 
            |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]
      ) · `suc `zero)
  —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩
    `suc
      case `zero 
        [zero⇒ `suc `zero 
        |suc "m" ⇒ `suc (plus · ` "m" · `suc `zero) ]
  —→⟨ ξ-suc (β-zero) ⟩
    `suc (`suc `zero)
 ∎

oneᶜ : Term
oneᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · ` "z"

plusᶜ-example : plusᶜ · oneᶜ · oneᶜ · sucᶜ · `zero —↠ `suc `suc `zero
plusᶜ-example = 
  begin
    (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z"))
    · oneᶜ · oneᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ oneᶜ · ` "s" · (` "n" · ` "s" · ` "z"))
    · oneᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒ (ƛ "z" ⇒ oneᶜ · ` "s" · (oneᶜ · ` "s" · ` "z"))) · sucᶜ · `zero
  —→⟨ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ oneᶜ · sucᶜ · (oneᶜ · sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · ` "z") · (ƛ "n" ⇒ `suc (` "n")) · (oneᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ` "z") · (oneᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ` "z") · ((ƛ "z" ⇒ sucᶜ · ` "z")  · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ` "z") · (sucᶜ · `zero) 
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ` "z") · (`suc `zero)
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    (ƛ "n" ⇒ `suc ` "n") · (`suc `zero)
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc `suc `zero
  ∎
  

--- A, B, C  ::=  A ⇒ B | `ℕ
infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type
  
infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

--- Exercise Context-≃
-- open plfa.lf.Isomorphism using (_≃_)
-- Context-≃ : Context ≃ List (Id × Type)
-- Context-≃ = {!   !}

infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A

_ : ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "y" ⦂ `ℕ , "z" ⦂ `ℕ ∋ "x" ⦂ `ℕ ⇒ `ℕ
_ = S (λ()) (S (λ()) Z)

S′ : ∀ {Γ x y A B}
   → {x≢y : False (x ≟ y)}
   → Γ ∋ x ⦂ A
     ------------------
   → Γ , y ⦂ B ∋ x ⦂ A
S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ M ⦂ A

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋s · (⊢` ∋s · ⊢` ∋z)))
  where
  ∋s = S′ Z
  ∋z = Z
  
⊢two : ∀ {Γ} → Γ ⊢ two ⦂ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢` ∋n)
         (⊢suc (⊢` ∋+ · ⊢` ∋m′ · ⊢` ∋n′)))))
  where
  ∋+  = S′ (S′ (S′ Z))
  ∋m  = S′ Z
  ∋n  = Z
  ∋m′ = Z
  ∋n′ = S′ Z

⊢2+2 : ∅ ⊢ plus · two · two ⦂ `ℕ
⊢2+2 = ⊢plus · ⊢two · ⊢two

⊢plusᶜ : ∀ {Γ A} → Γ  ⊢ plusᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢plusᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢` ∋m · ⊢` ∋s · (⊢` ∋n · ⊢` ∋s · ⊢` ∋z)))))
  where
  ∋m = S′ (S′ (S′ Z))
  ∋n = S′ (S′ Z)
  ∋s = S′ Z
  ∋z = Z

⊢sucᶜ : ∀ {Γ} → Γ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` ∋n))
  where
  ∋n = Z

⊢2+2ᶜ : ∅ ⊢ plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ⦂ `ℕ
⊢2+2ᶜ = ⊢plusᶜ · ⊢twoᶜ · ⊢twoᶜ · ⊢sucᶜ · ⊢zero

∋-functional : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-functional Z        Z          =  refl
∋-functional Z        (S x≢ _)   =  contradiction refl x≢
∋-functional (S x≢ _) Z          =  contradiction refl x≢
∋-functional (S _ ∋x) (S _ ∋x′)  =  ∋-functional ∋x ∋x′

nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ⦂ A)
nope₁ (() · _)

nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ⦂ A)
nope₂ (⊢ƛ (⊢` ∋x · ⊢` ∋x′))  = impossible (∋-functional ∋x ∋x′)
  where
  impossible : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  impossible ()

⊢mul : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) ⊢zero (⊢plus · ((⊢` ∋* · ⊢` ∋m′) · ⊢` ∋n) · ⊢` ∋n))))
  where
    ∋*  =  S′ (S′ (S′ Z))
    ∋m  =  S′ Z
    ∋n  =  S′ Z
    ∋m′ =  Z

⊢mulᶜ : ∀ {Γ A} → Γ  ⊢ mulᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢mulᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ ((⊢` ∋m · ((⊢` ∋n) · ⊢` ∋s)) · ⊢` ∋z))))
  where
    ∋m = S′ (S′ (S′ Z))
    ∋n = S′ (S′ Z)
    ∋s = S′ Z
    ∋z = Z