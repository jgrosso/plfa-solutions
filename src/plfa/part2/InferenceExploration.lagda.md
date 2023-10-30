```agda
{-
For fun, I tried to move as many constructors as possible from Term⁻ into Term⁺.
-}
module plfa.part2.InferenceExploration where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.String using (String; _≟_)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function.Base using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)

import plfa.part2.More as DB


infix  4 _×∋_⦂_
infix  4 _×⊢_↑_
infix  4 _×⊢_↓_

infixr 7 _⇒_
infixl 5 _,_⦂_

infix  5 ƛ_⇒_
infix  5 μ_⇒_
infix  6 _↑
infix  6 _↓_
infixl 7 _·_
infix  8 `suc_
infixr 9 _`×_
infixr 9 _`⊎_


Id : Set
Id = String


data ×Type : Set where
  `ℕ    : ×Type
  _⇒_   : ×Type → ×Type → ×Type
  _`×_  : ×Type → ×Type → ×Type
  Nat   : ×Type
  _`⊎_  : ×Type → ×Type → ×Type
  `⊤    : ×Type
  `⊥    : ×Type
  `List : ×Type → ×Type


data ×Context : Set where
  ∅     : ×Context
  _,_⦂_ : ×Context → Id → ×Type → ×Context


data _×∋_⦂_ : ×Context → Id → ×Type → Set where

  Z : ∀ {Γ x A}
    → Γ , x ⦂ A ×∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ×∋ x ⦂ A
    → Γ , y ⦂ B ×∋ x ⦂ A


data ×Term⁺ : Set

data ×Term⁻ : Set

data ×Term⁺ where
  `_                    : Id → ×Term⁺
  _·_                   : ×Term⁺ → ×Term⁻ → ×Term⁺
  _↓_                   : ×Term⁻ → ×Type → ×Term⁺
  `let_≔_,_             : Id → ×Term⁺ → ×Term⁺ → ×Term⁺
  `zero                 : ×Term⁺
  `suc_                 : ×Term⁻ → ×Term⁺
  con                   : ℕ → ×Term⁺
  `tt                   : ×Term⁺

data ×Term⁻ where
  ƛ_⇒_                  : Id → ×Term⁻ → ×Term⁻
  `case_[zero⇒_|suc_⇒_] : ×Term⁺ → ×Term⁻ → Id → ×Term⁻ → ×Term⁻
  μ_⇒_                  : Id → ×Term⁻ → ×Term⁻
  _↑                    : ×Term⁺ → ×Term⁻
  `⟨_,_⟩                : ×Term⁻ → ×Term⁻ → ×Term⁻
  case×_[_,_⇒_]         : ×Term⁺ → Id → Id → ×Term⁻ → ×Term⁻
  _`*_                  : ×Term⁻ → ×Term⁻ → ×Term⁻
  `inj₁                 : ×Term⁻ → ×Type → ×Term⁻
  `inj₂                 : ×Type → ×Term⁻ → ×Term⁻
  case⊎_[₁_⇒_|₂_⇒_]     : ×Term⁺ → Id → ×Term⁻ → Id → ×Term⁻ → ×Term⁻
  case⊤                 : ×Term⁺ → ×Term⁻ → ×Term⁻
  case⊥                 : ×Term⁺ → ×Term⁻
  `[]                   : ×Term⁻
  _`∷_                  : ×Term⁻ → ×Term⁻ → ×Term⁻
  caseL_[[]⇒_∣_∷_⇒_]    : ×Term⁺ → ×Term⁻ → Id → Id → ×Term⁻ → ×Term⁻


data _×⊢_↑_ : ×Context → ×Term⁺ → ×Type → Set

data _×⊢_↓_ : ×Context → ×Term⁻ → ×Type → Set

data _×⊢_↑_ where

  ⊢` : ∀ {γ a x}
    → γ ×∋ x ⦂ a
    → γ ×⊢ ` x ↑ a

  _·_ : ∀ {γ l m a b}
    → γ ×⊢ l ↑ a ⇒ b
    → γ ×⊢ m ↓ a
    → γ ×⊢ l · m ↑ b

  ⊢↓ : ∀ {γ m a}
    → γ ×⊢ m ↓ a
    → γ ×⊢ (m ↓ a) ↑ a

  ⊢let : ∀ {γ l m a b x}
    → γ ×⊢ l ↑ a
    → γ , x ⦂ a ×⊢ m ↑ b
    → γ ×⊢ `let x ≔ l , m ↑ b

  ⊢zero : ∀ {Γ}
    → Γ ×⊢ `zero ↑ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ×⊢ M ↓ `ℕ
    → Γ ×⊢ `suc M ↑ `ℕ

  ⊢con : ∀ {Γ n}
    → Γ ×⊢ con n ↑ Nat

  ⊢tt : ∀ {Γ}
    → Γ ×⊢ `tt ↑ `⊤

data _×⊢_↓_ where

  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ×⊢ N ↓ B
    → Γ ×⊢ ƛ x ⇒ N ↓ A ⇒ B

  ⊢case : ∀ {Γ L M x N A}
    → Γ ×⊢ L ↑ `ℕ
    → Γ ×⊢ M ↓ A
    → Γ , x ⦂ `ℕ ×⊢ N ↓ A
    → Γ ×⊢ `case L [zero⇒ M |suc x ⇒ N ] ↓ A

  ⊢μ : ∀ {Γ x N A}
    → Γ , x ⦂ A ×⊢ N ↓ A
    → Γ ×⊢ μ x ⇒ N ↓ A

  ⊢↑ : ∀ {Γ M A B}
    → Γ ×⊢ M ↑ A
    → A ≡ B
    → Γ ×⊢ (M ↑) ↓ B

  ⊢⟨_,_⟩ : ∀ {Γ L M A B}
    → Γ ×⊢ L ↓ A
    → Γ ×⊢ M ↓ B
    → Γ ×⊢ `⟨ L , M ⟩ ↓ A `× B


  ⊢case× : ∀ {Γ L M x y A B C}
    → Γ ×⊢ L ↑ A `× B
    → Γ , x ⦂ A , y ⦂ B ×⊢ M ↓ C
    → Γ ×⊢ case× L [ x , y ⇒ M ] ↓ C

  _⊢*_ : ∀ {Γ L M}
    → Γ ×⊢ L ↓ Nat
    → Γ ×⊢ M ↓ Nat
    → Γ ×⊢ L `* M ↓ Nat

  ⊢inj₁ : ∀ {Γ M A B}
    → Γ ×⊢ M ↓ A
    → Γ ×⊢ `inj₁ M B ↓ A `⊎ B

  ⊢inj₂ : ∀ {Γ M A B}
    → Γ ×⊢ M ↓ B
    → Γ ×⊢ `inj₂ A M ↓ A `⊎ B

  ⊢case⊎ : ∀ {Γ L M N x y A B C}
    → Γ ×⊢ L ↑ A `⊎ B
    → Γ , x ⦂ A ×⊢ M ↓ C
    → Γ , y ⦂ B ×⊢ N ↓ C
    → Γ ×⊢ case⊎ L [₁ x ⇒ M |₂ y ⇒ N ] ↓ C

  ⊢case⊤ : ∀ {Γ L M A}
    → Γ ×⊢ L ↑ `⊤
    → Γ ×⊢ M ↓ A
    → Γ ×⊢ case⊤ L M ↓ A

  ⊢case⊥ : ∀ {Γ M A}
    → Γ ×⊢ M ↑ `⊥
    → Γ ×⊢ case⊥ M ↓ A

  ⊢[] : ∀ {Γ A}
    → Γ ×⊢ `[] ↓ `List A

  _⊢∷_ : ∀ {Γ L M A}
    → Γ ×⊢ L ↓ A
    → Γ ×⊢ M ↓ `List A
    → Γ ×⊢ L `∷ M ↓ `List A

  ⊢caseL : ∀ {Γ L M N x y A B}
    → Γ ×⊢ L ↑ `List A
    → Γ ×⊢ M ↓ B
    → Γ , x ⦂ A , y ⦂ `List A ×⊢ N ↓ B
    → Γ ×⊢ caseL L [[]⇒ M ∣ x ∷ y ⇒ N ] ↓ B


_≟×Tp_ : (A B : ×Type) → Dec (A ≡ B)

`ℕ       ≟×Tp `ℕ            = yes refl
`ℕ       ≟×Tp (A ⇒ B)       = no λ()
`ℕ       ≟×Tp (A `× B)      = no λ()
`ℕ       ≟×Tp Nat           = no λ()
`ℕ       ≟×Tp (A `⊎ B)      = no λ()
`ℕ       ≟×Tp `⊤            = no λ()
`ℕ       ≟×Tp `⊥            = no λ()
`ℕ       ≟×Tp (`List A)     = no λ()

(A ⇒ B)  ≟×Tp `ℕ            = no λ()
(A ⇒ B)  ≟×Tp (A′ ⇒ B′)
  with A ≟×Tp A′ | B ≟×Tp B′
...  | no  A≢    | _        = no λ{ refl → A≢ refl }
...  | yes _     | no  B≢   = no λ{ refl → B≢ refl }
...  | yes refl  | yes refl = yes refl
(A ⇒ B)  ≟×Tp (A′ `× B′)    = no λ()
(A ⇒ B)  ≟×Tp Nat           = no λ()
(A ⇒ B)  ≟×Tp (A′ `⊎ B′)    = no λ()
(A ⇒ B)  ≟×Tp `⊤            = no λ()
(A ⇒ B)  ≟×Tp `⊥            = no λ()
(A ⇒ B)  ≟×Tp (`List A′)    = no λ()

(A `× B) ≟×Tp `ℕ            = no λ()
(A `× B) ≟×Tp (A′ ⇒ B′)     = no λ()
(A `× B) ≟×Tp (A′ `× B′)
  with A ≟×Tp A′ | B ≟×Tp B′
...  | no  A≢    | _        = no λ{ refl → A≢ refl }
...  | yes _     | no  B≢   = no λ{ refl → B≢ refl }
...  | yes refl  | yes refl = yes refl
(A `× B) ≟×Tp Nat           = no λ()
(A `× B) ≟×Tp (A′ `⊎ B′)    = no λ()
(A `× B) ≟×Tp `⊤            = no λ()
(A `× B) ≟×Tp `⊥            = no λ()
(A `× B) ≟×Tp (`List A′)    = no λ()

Nat      ≟×Tp `ℕ            = no λ()
Nat      ≟×Tp (A ⇒ B)       = no λ()
Nat      ≟×Tp (A `× B)      = no λ()
Nat      ≟×Tp Nat           = yes refl
Nat      ≟×Tp (A `⊎ B)      = no λ()
Nat      ≟×Tp `⊤            = no λ()
Nat      ≟×Tp `⊥            = no λ()
Nat      ≟×Tp (`List A)     = no λ()

(A `⊎ B) ≟×Tp `ℕ            = no λ()
(A `⊎ B) ≟×Tp (A′ ⇒ B′)     = no λ()
(A `⊎ B) ≟×Tp (A′ `× B′)    = no λ()
(A `⊎ B) ≟×Tp Nat           = no λ()
(A `⊎ B) ≟×Tp (A′ `⊎ B′)
  with A ≟×Tp A′ | B ≟×Tp B′
...  | no  A≢    | _        = no λ{ refl → A≢ refl }
...  | yes _     | no  B≢   = no λ{ refl → B≢ refl }
...  | yes refl  | yes refl = yes refl
(A `⊎ B) ≟×Tp `⊤            = no λ()
(A `⊎ B) ≟×Tp `⊥            = no λ()
(A `⊎ B) ≟×Tp (`List A′)    = no λ()

`⊤       ≟×Tp `ℕ            = no λ()
`⊤       ≟×Tp (A ⇒ B)       = no λ()
`⊤       ≟×Tp (A `× B)      = no λ()
`⊤       ≟×Tp Nat           = no λ()
`⊤       ≟×Tp (A `⊎ B)      = no λ()
`⊤       ≟×Tp `⊤            = yes refl
`⊤       ≟×Tp `⊥            = no λ()
`⊤       ≟×Tp (`List A)     = no λ()

`⊥       ≟×Tp `ℕ            = no λ()
`⊥       ≟×Tp (A ⇒ B)       = no λ()
`⊥       ≟×Tp (A `× B)      = no λ()
`⊥       ≟×Tp Nat           = no λ()
`⊥       ≟×Tp (A `⊎ B)      = no λ()
`⊥       ≟×Tp `⊤            = no λ()
`⊥       ≟×Tp `⊥            = yes refl
`⊥       ≟×Tp (`List A)     = no λ()

(`List A) ≟×Tp `ℕ           = no λ()
(`List A) ≟×Tp (A′ ⇒ B)     = no λ()
(`List A) ≟×Tp (A′ `× B)    = no λ()
(`List A) ≟×Tp Nat          = no λ()
(`List A) ≟×Tp (A′ `⊎ B)    = no λ()
(`List A) ≟×Tp `⊤           = no λ()
(`List A) ≟×Tp `⊥           = no λ()
(`List A) ≟×Tp (`List A′) with A ≟×Tp A′
... | no  A≢                = no λ{ refl → A≢ refl }
... | yes refl              = yes refl


uniq-×∋ : ∀ {Γ x A B} → Γ ×∋ x ⦂ A → Γ ×∋ x ⦂ B → A ≡ B
uniq-×∋ Z         Z         = refl
uniq-×∋ Z         (S x≢y _) = ⊥-elim (x≢y refl)
uniq-×∋ (S x≢y _) Z         = ⊥-elim (x≢y refl)
uniq-×∋ (S _ ∋x)  (S _ ∋x′) = uniq-×∋ ∋x ∋x′


uniq-×↑ : ∀ {Γ M A B} → Γ ×⊢ M ↑ A → Γ ×⊢ M ↑ B → A ≡ B
uniq-×↑ (⊢` ∋x) (⊢` ∋x′)   = uniq-×∋ ∋x ∋x′
uniq-×↑ (⊢L · ⊢M) (⊢L′ · ⊢M′) with uniq-×↑ ⊢L ⊢L′
... | refl                 = refl
uniq-×↑ (⊢↓ ⊢M) (⊢↓ ⊢M′)   = refl
uniq-×↑ (⊢let ⊢L ⊢M) (⊢let ⊢L′ ⊢M′) with uniq-×↑ ⊢L ⊢L′
... | refl with uniq-×↑ ⊢M ⊢M′
...           | refl       = refl
uniq-×↑ ⊢zero ⊢zero        = refl
uniq-×↑ (⊢suc M) (⊢suc M′) = refl
uniq-×↑ ⊢con ⊢con          = refl
uniq-×↑ ⊢tt ⊢tt            = refl

ext×∋ : ∀ {Γ B x y}
  → x ≢ y
  → ¬ (∃[ A ] Γ ×∋ x ⦂ A)
  → ¬ (∃[ A ] Γ , y ⦂ B ×∋ x ⦂ A)
ext×∋ x≢y _  ⟨ A , Z ⟩      = x≢y refl
ext×∋ _   ¬∃ ⟨ A , S _ ∋x ⟩ = ¬∃ ⟨ A , ∋x ⟩


×lookup :
    (Γ : ×Context) (x : Id)
  → Dec (∃[ A ] Γ ×∋ x ⦂ A)
×lookup ∅ x                      = no λ()
×lookup (Γ , y ⦂ B) x with x ≟ y
... | yes refl                   = yes ⟨ B , Z ⟩
... | no x≢y with ×lookup Γ x
...             | no  ¬∃         = no (ext×∋ x≢y ¬∃)
...             | yes ⟨ A , ∋x ⟩ = yes ⟨ A , S x≢y ∋x ⟩


¬×arg : ∀ {Γ A B L M}
  → Γ ×⊢ L ↑ A ⇒ B
  → ¬ Γ ×⊢ M ↓ A
  → ¬ (∃[ B′ ] Γ ×⊢ L · M ↑ B′)
¬×arg ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ with uniq-×↑ ⊢L ⊢L′
... | refl = ¬⊢M ⊢M′


¬×switch : ∀ {Γ M A B}
  → Γ ×⊢ M ↑ A
  → A ≢ B
  → ¬ Γ ×⊢ (M ↑) ↓ B
¬×switch ⊢M A≢B (⊢↑ ⊢M′ A′≡B) rewrite uniq-×↑ ⊢M ⊢M′ = A≢B A′≡B


×synthesize :
    (Γ : ×Context) (M : ×Term⁺)
  → Dec (∃[ A ] Γ ×⊢ M ↑ A)

×inherit :
    (Γ : ×Context) (M : ×Term⁻) (A : ×Type)
  → Dec (Γ ×⊢ M ↓ A)

×synthesize Γ (` x) with ×lookup Γ x
... | no ¬∃               = no λ{ ⟨ A , ⊢` ∋x ⟩ → ¬∃ ⟨ A , ∋x ⟩ }
... | yes ⟨ A , ∋x ⟩      = yes ⟨ A , ⊢` ∋x ⟩

×synthesize Γ (L · M) with ×synthesize Γ L
... | no  ¬∃              = no λ{ ⟨ _ , ⊢L  · _  ⟩ → ¬∃ ⟨ _ , ⊢L ⟩ }
... | yes ⟨ `ℕ      , ⊢L ⟩ = no λ{ ⟨ _ , ⊢L′ · _  ⟩ → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ Nat     , ⊢L ⟩ = no λ{ ⟨ _ , ⊢L′ · _  ⟩ → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A `× B  , ⊢L ⟩ = no λ{ ⟨ _ , ⊢L′ · _  ⟩ → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A `⊎ B  , ⊢L ⟩ = no λ{ ⟨ _ , ⊢L′ · _  ⟩ → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `⊤      , ⊢L ⟩ = no λ{ ⟨ _ , ⊢L′ · _  ⟩ → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `⊥      , ⊢L ⟩ = no λ{ ⟨ _ , ⊢L′ · _  ⟩ → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `List A , ⊢L ⟩ = no λ{ ⟨ _ , ⊢L′ · _  ⟩ → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A ⇒ B   , ⊢L ⟩ with ×inherit Γ M A
...    | no ¬⊢M            = no (¬×arg ⊢L ¬⊢M)
...    | yes ⊢M            = yes ⟨ B , ⊢L · ⊢M ⟩

×synthesize Γ (M ↓ A) with ×inherit Γ M A
... | no ¬⊢M               = no λ{ ⟨ _ , ⊢↓ ⊢M ⟩ → ¬⊢M ⊢M }
... | yes ⊢M               = yes ⟨ A , ⊢↓ ⊢M ⟩

×synthesize Γ (`let x ≔ L , M) with ×synthesize Γ L
... | no  ¬∃               = no λ{ ⟨ _ , ⊢let {a = A} ⊢L ⊢M ⟩ → ¬∃ ⟨ A , ⊢L ⟩ }
... | yes ⟨ A , ⊢L ⟩ with ×synthesize (Γ , x ⦂ A) M
...   | no  ¬∃             = no λ{ ⟨ B , ⊢let ⊢L′ ⊢M ⟩ → ¬∃ ⟨ B , case uniq-×↑ ⊢L ⊢L′ of (λ{ refl → ⊢M }) ⟩ }
...   | yes ⟨ B , ⊢M ⟩     = yes ⟨ B , ⊢let ⊢L ⊢M ⟩

×synthesize Γ `zero = yes ⟨ `ℕ , ⊢zero ⟩

×synthesize Γ (`suc M) with ×inherit Γ M `ℕ
... | no ¬⊢M = no λ{ ⟨ _ , ⊢suc ⊢M ⟩ → ¬⊢M ⊢M }
... | yes ⊢M = yes ⟨ `ℕ , ⊢suc ⊢M ⟩

×synthesize Γ (con _) = yes ⟨ Nat , ⊢con ⟩

×synthesize Γ `tt = yes ⟨ `⊤ , ⊢tt ⟩


×inherit Γ (ƛ x ⇒ N) `ℕ             = no λ()
×inherit Γ (ƛ x ⇒ N) (A ⇒ B) with ×inherit (Γ , x ⦂ A) N B
... | no ¬⊢N                        = no λ{ (⊢ƛ ⊢N) → ¬⊢N ⊢N }
... | yes ⊢N                        = yes (⊢ƛ ⊢N)
×inherit Γ (ƛ x ⇒ N) (A `× B)       = no λ()
×inherit Γ (ƛ x ⇒ N) Nat            = no λ()
×inherit Γ (ƛ x ⇒ N) (A `⊎ B)       = no λ()
×inherit Γ (ƛ x ⇒ N) `⊤             = no λ()
×inherit Γ (ƛ x ⇒ N) `⊥             = no λ()
×inherit Γ (ƛ x ⇒ N) (`List A)      = no λ()

×inherit Γ (`case L [zero⇒ M |suc x ⇒ N ]) A with ×synthesize Γ L
... | no  ¬∃                        = no λ{ (⊢case ⊢L  _ _) → ¬∃ ⟨ `ℕ , ⊢L ⟩}
... | yes ⟨ _ ⇒ _   , ⊢L ⟩          = no λ{ (⊢case ⊢L′ _ _) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ _ `× _  , ⊢L ⟩          = no λ{ (⊢case ⊢L′ _ _) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ Nat     , ⊢L ⟩          = no λ{ (⊢case ⊢L′ _ _) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ _ `⊎ _  , ⊢L ⟩          = no λ{ (⊢case ⊢L′ _ _) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `⊤      , ⊢L ⟩          = no λ{ (⊢case ⊢L′ _ _) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `⊥      , ⊢L ⟩          = no λ{ (⊢case ⊢L′ _ _) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `List _ , ⊢L ⟩          = no λ{ (⊢case ⊢L′ _ _) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `ℕ      , ⊢L ⟩ with ×inherit Γ M A
...    | no ¬⊢M                     = no λ{ (⊢case _ ⊢M _) → ¬⊢M ⊢M }
...    | yes ⊢M with ×inherit (Γ , x ⦂ `ℕ) N A
...       | no ¬⊢N                  = no λ{ (⊢case _ _ ⊢N) → ¬⊢N ⊢N }
...       | yes ⊢N                  = yes (⊢case ⊢L ⊢M ⊢N)

×inherit Γ (μ x ⇒ N) A with ×inherit (Γ , x ⦂ A) N A
... | no ¬⊢N                        = no λ{ (⊢μ ⊢N) → ¬⊢N ⊢N }
... | yes ⊢N                        = yes (⊢μ ⊢N)

×inherit Γ (M ↑) B with ×synthesize Γ M
... | no  ¬∃                        = no λ{ (⊢↑ ⊢M _) → ¬∃ ⟨ _ , ⊢M ⟩ }
... | yes ⟨ A , ⊢M ⟩ with A ≟×Tp B
...   | no  A≢B                     = no (¬×switch ⊢M A≢B)
...   | yes A≡B                     = yes (⊢↑ ⊢M A≡B)

×inherit Γ `⟨ L , M ⟩ `ℕ            = no λ()
×inherit Γ `⟨ L , M ⟩ (A ⇒ B)       = no λ()
×inherit Γ `⟨ L , M ⟩ (A `× B) with ×inherit Γ L A | ×inherit Γ M B
... | no  ¬∃ | _                    = no λ{ ⊢⟨ ⊢L , ⊢M ⟩ → ¬∃ ⊢L }
... | yes _  | no  ¬∃               = no λ{ ⊢⟨ ⊢L , ⊢M ⟩ → ¬∃ ⊢M }
... | yes ⊢L | yes ⊢M               = yes ⊢⟨ ⊢L , ⊢M ⟩
×inherit Γ `⟨ L , M ⟩ Nat           = no λ()
×inherit Γ `⟨ L , M ⟩ (A `⊎ B)      = no λ()
×inherit Γ `⟨ L , M ⟩ `⊤            = no λ()
×inherit Γ `⟨ L , M ⟩ `⊥            = no λ()
×inherit Γ `⟨ L , M ⟩ (`List A)     = no λ()

×inherit Γ (case× L [ x , y ⇒ M ]) C with ×synthesize Γ L
... | no  ¬∃                        = no λ{ (⊢case× ⊢L ⊢M) → ¬∃ ⟨ _ , ⊢L ⟩ }
... | yes ⟨ `ℕ      , ⊢L ⟩          = no λ{ (⊢case× ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A ⇒ B   , ⊢L ⟩          = no λ{ (⊢case× ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ Nat     , ⊢L ⟩          = no λ{ (⊢case× ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A `⊎ B  , ⊢L ⟩          = no λ{ (⊢case× ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `⊤      , ⊢L ⟩          = no λ{ (⊢case× ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `⊥      , ⊢L ⟩          = no λ{ (⊢case× ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `List A , ⊢L ⟩          = no λ{ (⊢case× ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A `× B  , ⊢L ⟩ with ×inherit (Γ , x ⦂ A , y ⦂ B) M C
...   | no  ¬∃                      = no λ{ (⊢case× ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ{ refl → ¬∃ ⊢M } }
...   | yes ⊢M                      = yes (⊢case× ⊢L ⊢M)

×inherit Γ (L `* M) `ℕ              = no λ()
×inherit Γ (L `* M) (A ⇒ B)         = no λ()
×inherit Γ (L `* M) (A `× B)        = no λ()
×inherit Γ (L `* M) (A `⊎ B)        = no λ()
×inherit Γ (L `* M) Nat with ×inherit Γ L Nat | ×inherit Γ M Nat
... | no  ¬∃ | _                    = no λ{ (⊢L ⊢* ⊢M) → ¬∃ ⊢L }
... | yes _  | no  ¬∃               = no λ{ (⊢L ⊢* ⊢M) → ¬∃ ⊢M }
... | yes ⊢L | yes ⊢M               = yes (⊢L ⊢* ⊢M)
×inherit Γ (L `* M) `⊤              = no λ()
×inherit Γ (L `* M) `⊥              = no λ()
×inherit Γ (L `* M) (`List A)       = no λ()

×inherit Γ (`inj₁ L B) `ℕ           = no λ()
×inherit Γ (`inj₁ L B) (A ⇒ B′)     = no λ()
×inherit Γ (`inj₁ L B) (A `× B′)    = no λ()
×inherit Γ (`inj₁ L B) Nat          = no λ()
×inherit Γ (`inj₁ L B) (A `⊎ B′) with ×inherit Γ L A
... | no  ¬∃                        = no λ{ (⊢inj₁ ⊢L) → ¬∃ ⊢L }
... | yes ⊢L with B ≟×Tp B′
...   | no  B≢                      = no λ{ (⊢inj₁ ⊢L) → B≢ refl }
...   | yes refl                    = yes (⊢inj₁ ⊢L)
×inherit Γ (`inj₁ L B) `⊤           = no λ()
×inherit Γ (`inj₁ L B) `⊥           = no λ()
×inherit Γ (`inj₁ L B) (`List A)    = no λ()

×inherit Γ (`inj₂ A M) `ℕ           = no λ()
×inherit Γ (`inj₂ A M) (A′ ⇒ B)     = no λ()
×inherit Γ (`inj₂ A M) (A′ `× B)    = no λ()
×inherit Γ (`inj₂ A M) Nat          = no λ()
×inherit Γ (`inj₂ A M) (A′ `⊎ B) with ×inherit Γ M B
... | no  ¬∃                        = no λ{ (⊢inj₂ ⊢M) → ¬∃ ⊢M }
... | yes ⊢M with A ≟×Tp A′
...   | no  A≢                      = no λ{ (⊢inj₂ ⊢M) → A≢ refl }
...   | yes refl                    = yes (⊢inj₂ ⊢M)
×inherit Γ (`inj₂ A M) `⊤           = no λ()
×inherit Γ (`inj₂ A M) `⊥           = no λ()
×inherit Γ (`inj₂ A M) (`List _)    = no λ()

×inherit Γ (case⊎ L [₁ x ⇒ M |₂ y ⇒ N ]) C with ×synthesize Γ L
... | no  ¬∃                        = no λ{ (⊢case⊎ ⊢L ⊢M ⊢N) → ¬∃ ⟨ _ `⊎ _ , ⊢L ⟩ }
... | yes ⟨ `ℕ      , ⊢L ⟩          = no λ{ (⊢case⊎ ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A ⇒ B   , ⊢L ⟩          = no λ{ (⊢case⊎ ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ Nat     , ⊢L ⟩          = no λ{ (⊢case⊎ ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A `× B  , ⊢L ⟩          = no λ{ (⊢case⊎ ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `⊤      , ⊢L ⟩          = no λ{ (⊢case⊎ ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `⊥      , ⊢L ⟩          = no λ{ (⊢case⊎ ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `List A , ⊢L ⟩          = no λ{ (⊢case⊎ ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A `⊎ B  , ⊢L ⟩ with ×inherit (Γ , x ⦂ A) M C | ×inherit (Γ , y ⦂ B) N C
...   | no  ¬∃ | _                  = no λ{ (⊢case⊎ ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ{ refl → ¬∃ ⊢M } }
...   | yes _  | no  ¬∃             = no λ{ (⊢case⊎ ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ{ refl → ¬∃ ⊢N } }
...   | yes ⊢M | yes ⊢N             = yes (⊢case⊎ ⊢L ⊢M ⊢N)

×inherit Γ (case⊤ L M) C with ×synthesize Γ L
... | no  ¬∃                        = no λ{ (⊢case⊤ ⊢L ⊢M) → ¬∃ ⟨ `⊤ , ⊢L ⟩ }
... | yes ⟨ `ℕ      , ⊢L ⟩          = no λ{ (⊢case⊤ ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A ⇒ B   , ⊢L ⟩          = no λ{ (⊢case⊤ ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ Nat     , ⊢L ⟩          = no λ{ (⊢case⊤ ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A `× B  , ⊢L ⟩          = no λ{ (⊢case⊤ ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A `⊎ B  , ⊢L ⟩          = no λ{ (⊢case⊤ ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `⊥      , ⊢L ⟩          = no λ{ (⊢case⊤ ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `List A , ⊢L ⟩          = no λ{ (⊢case⊤ ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `⊤ , ⊢L ⟩ with ×inherit Γ M C
...   | no  ¬∃                      = no λ{ (⊢case⊤ ⊢L′ ⊢M) → case uniq-×↑ ⊢L ⊢L′ of λ{ refl → ¬∃ ⊢M } }
...   | yes ⊢M                      = yes (⊢case⊤ ⊢L ⊢M)

×inherit Γ (case⊥ M) C with ×synthesize Γ M
... | no  ¬∃                        = no λ{ (⊢case⊥ ⊢M) → ¬∃ ⟨ `⊥ , ⊢M ⟩ }
... | yes ⟨ `ℕ      , ⊢M ⟩          = no λ{ (⊢case⊥ ⊢M′) → case uniq-×↑ ⊢M ⊢M′ of λ() }
... | yes ⟨ A ⇒ B   , ⊢M ⟩          = no λ{ (⊢case⊥ ⊢M′) → case uniq-×↑ ⊢M ⊢M′ of λ() }
... | yes ⟨ Nat     , ⊢M ⟩          = no λ{ (⊢case⊥ ⊢M′) → case uniq-×↑ ⊢M ⊢M′ of λ() }
... | yes ⟨ A `× B  , ⊢M ⟩          = no λ{ (⊢case⊥ ⊢M′) → case uniq-×↑ ⊢M ⊢M′ of λ() }
... | yes ⟨ A `⊎ B  , ⊢M ⟩          = no λ{ (⊢case⊥ ⊢M′) → case uniq-×↑ ⊢M ⊢M′ of λ() }
... | yes ⟨ `⊤      , ⊢M ⟩          = no λ{ (⊢case⊥ ⊢M′) → case uniq-×↑ ⊢M ⊢M′ of λ() }
... | yes ⟨ `⊥      , ⊢M ⟩          = yes (⊢case⊥ ⊢M)
... | yes ⟨ `List A , ⊢M ⟩          = no λ{ (⊢case⊥ ⊢M′) → case uniq-×↑ ⊢M ⊢M′ of λ() }

×inherit Γ `[] `ℕ                   = no λ()
×inherit Γ `[] (A ⇒ B)              = no λ()
×inherit Γ `[] Nat                  = no λ()
×inherit Γ `[] (A `× B)             = no λ()
×inherit Γ `[] (A `⊎ B)             = no λ()
×inherit Γ `[] `⊥                   = no λ()
×inherit Γ `[] `⊤                   = no λ()
×inherit Γ `[] (`List A)            = yes ⊢[]

×inherit Γ (L `∷ M) `ℕ              = no λ()
×inherit Γ (L `∷ M) (A ⇒ B)         = no λ()
×inherit Γ (L `∷ M) Nat             = no λ()
×inherit Γ (L `∷ M) (A `× B)        = no λ()
×inherit Γ (L `∷ M) (A `⊎ B)        = no λ()
×inherit Γ (L `∷ M) `⊤              = no λ()
×inherit Γ (L `∷ M) `⊥              = no λ()
×inherit Γ (L `∷ M) (`List A) with ×inherit Γ L A | ×inherit Γ M (`List A)
... | no  ¬∃ | _                    = no λ{ (⊢L ⊢∷ ⊢M) → ¬∃ ⊢L }
... | yes _  | no ¬∃                = no λ{ (⊢L ⊢∷ ⊢M) → ¬∃ ⊢M }
... | yes ⊢L | yes ⊢M               = yes (⊢L ⊢∷ ⊢M)

×inherit Γ (caseL L [[]⇒ M ∣ x ∷ y ⇒ N ]) C with ×synthesize Γ L | ×inherit Γ M C
... | no  ¬∃               | _      = no λ{ (⊢caseL ⊢L ⊢M ⊢N) → ¬∃ ⟨ `List _ , ⊢L ⟩ }
... | yes ⟨ `ℕ      , ⊢L ⟩ | _      = no λ{ (⊢caseL ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A ⇒ B   , ⊢L ⟩ | _      = no λ{ (⊢caseL ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A `× B  , ⊢L ⟩ | _      = no λ{ (⊢caseL ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ Nat     , ⊢L ⟩ | _      = no λ{ (⊢caseL ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ A `⊎ B  , ⊢L ⟩ | _      = no λ{ (⊢caseL ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `⊤      , ⊢L ⟩ | _      = no λ{ (⊢caseL ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `⊥      , ⊢L ⟩ | _      = no λ{ (⊢caseL ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ() }
... | yes ⟨ `List A , ⊢L ⟩ | no  ¬∃ = no λ{ (⊢caseL ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ{ refl → ¬∃ ⊢M } }
... | yes ⟨ `List A , ⊢L ⟩ | yes ⊢M with ×inherit (Γ , x ⦂ A , y ⦂ `List A) N C
...   | no  ¬∃                      = no λ{ (⊢caseL ⊢L′ ⊢M ⊢N) → case uniq-×↑ ⊢L ⊢L′ of λ{ refl → ¬∃ ⊢N } }
...   | yes ⊢N                      = yes (⊢caseL ⊢L ⊢M ⊢N)


∥_∥×Tp : ×Type → DB.Type
∥ `ℕ ∥×Tp      = DB.`ℕ
∥ A ⇒ B ∥×Tp   = ∥ A ∥×Tp DB.⇒ ∥ B ∥×Tp
∥ A `× B ∥×Tp  = ∥ A ∥×Tp DB.`× ∥ B ∥×Tp
∥ Nat ∥×Tp     = DB.Nat
∥ A `⊎ B ∥×Tp  = ∥ A ∥×Tp DB.`⊎ ∥ B ∥×Tp
∥ `⊤ ∥×Tp      = DB.`⊤
∥ `⊥ ∥×Tp      = DB.`⊥
∥ `List A ∥×Tp = DB.`List ∥ A ∥×Tp


∥_∥×Cx : ×Context → DB.Context
∥ ∅ ∥×Cx         = DB.∅
∥ Γ , x ⦂ A ∥×Cx = ∥ Γ ∥×Cx DB., ∥ A ∥×Tp


∥_∥×∋ : ∀ {Γ x A} → Γ ×∋ x ⦂ A → ∥ Γ ∥×Cx DB.∋ ∥ A ∥×Tp
∥ Z ∥×∋        = DB.Z
∥ S x≢ ×∋x ∥×∋ = DB.S ∥ ×∋x ∥×∋


∥_∥×⁺ : ∀ {Γ M A} → Γ ×⊢ M ↑ A → ∥ Γ ∥×Cx DB.⊢ ∥ A ∥×Tp

∥_∥×⁻ : ∀ {Γ M A} → Γ ×⊢ M ↓ A → ∥ Γ ∥×Cx DB.⊢ ∥ A ∥×Tp

∥ ⊢` ⊢x ∥×⁺      = DB.` ∥ ⊢x ∥×∋
∥ ⊢L · ⊢M ∥×⁺    = ∥ ⊢L ∥×⁺ DB.· ∥ ⊢M ∥×⁻
∥ ⊢↓ ⊢M ∥×⁺      = ∥ ⊢M ∥×⁻
∥ ⊢let ⊢L ⊢M ∥×⁺ = DB.`let ∥ ⊢L ∥×⁺ ∥ ⊢M ∥×⁺
∥ ⊢zero ∥×⁺           = DB.`zero
∥ ⊢suc ⊢M ∥×⁺         = DB.`suc ∥ ⊢M ∥×⁻
∥ ⊢con {_} {n} ∥×⁺    = DB.con n
∥ ⊢tt ∥×⁺             = DB.`tt

∥ ⊢ƛ ⊢N ∥×⁻           = DB.ƛ ∥ ⊢N ∥×⁻
∥ ⊢case ⊢L ⊢M ⊢N ∥×⁻  = DB.case ∥ ⊢L ∥×⁺ ∥ ⊢M ∥×⁻ ∥ ⊢N ∥×⁻
∥ ⊢μ ⊢M ∥×⁻           = DB.μ ∥ ⊢M ∥×⁻
∥ ⊢↑ ⊢M refl ∥×⁻      = ∥ ⊢M ∥×⁺
∥ ⊢⟨ ⊢L , ⊢M ⟩ ∥×⁻    = DB.`⟨ ∥ ⊢L ∥×⁻ , ∥ ⊢M ∥×⁻ ⟩
∥ ⊢case× ⊢L ⊢M ∥×⁻    = DB.case× ∥ ⊢L ∥×⁺ ∥ ⊢M ∥×⁻
∥ ⊢L ⊢* ⊢M ∥×⁻        = ∥ ⊢L ∥×⁻ DB.`* ∥ ⊢M ∥×⁻
∥ ⊢inj₁ ⊢M ∥×⁻        = DB.`inj₁ ∥ ⊢M ∥×⁻
∥ ⊢inj₂ ⊢M ∥×⁻        = DB.`inj₂ ∥ ⊢M ∥×⁻
∥ ⊢case⊎ ⊢L ⊢M ⊢N ∥×⁻ = DB.case⊎ ∥ ⊢L ∥×⁺ ∥ ⊢M ∥×⁻ ∥ ⊢N ∥×⁻
∥ ⊢case⊤ ⊢L ⊢M ∥×⁻    = DB.case⊤ ∥ ⊢L ∥×⁺ ∥ ⊢M ∥×⁻
∥ ⊢case⊥ ⊢L ∥×⁻       = DB.case⊥ ∥ ⊢L ∥×⁺
∥ ⊢caseL ⊢L ⊢M ⊢N ∥×⁻ = DB.caseL ∥ ⊢L ∥×⁺ ∥ ⊢M ∥×⁻ ∥ ⊢N ∥×⁻
∥ ⊢[] ∥×⁻             = DB.`[]
∥ ⊢L ⊢∷ ⊢M ∥×⁻        = ∥ ⊢L ∥×⁻ DB.`∷ ∥ ⊢M ∥×⁻
```
