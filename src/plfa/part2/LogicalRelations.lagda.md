```agda
module plfa.part2.LogicalRelations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Product using (_×_; ∃-syntax; Σ-syntax; -,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infixl 7 _·_
infix  9 `_
infix  9 #_

data Type : Set where
  _⇒_ : Type → Type → Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
    → Γ , A ∋ A
  S_ : ∀ {Γ A B}
    → Γ ∋ A
    → Γ , B ∋ A

data _⊢_ : Context → Type → Set where
  `_ : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢ A
  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
    → Γ ⊢ A ⇒ B
  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
    → Γ ⊢ B

length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
lookup {(Γ , _)} {(suc n)} (s≤s p)    =  lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero}    (s≤s z≤n)  =  Z
count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ}  =  ` count (toWitness n∈Γ)

ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)

exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)

private
  σ-subst : ∀ {Γ A B} → Γ ⊢ B → Γ , B ∋ A → Γ ⊢ A
  σ-subst M Z      =  M
  σ-subst M (S x)  =  ` x

_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} (σ-subst M) {A} N

data Value : ∀ {Γ A} → Γ ⊢ A → Set where
  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
    → Value (ƛ N)

infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
    → L · M —→ L′ · M
  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
    → V · M —→ V · M′
  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
    → (ƛ N) · W —→ N [ W ]

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where
  _∎ : (M : Γ ⊢ A)
    → M —↠ M
  _—→⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
  → M —↠ N
begin M—↠N = M—↠N

data Progress {A} (M : ∅ ⊢ A) : Set where
  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
    → Progress M
  done :
      Value M
    → Progress M

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ N)                          =  done V-ƛ
progress (L · M) with progress L
...    | step L—→L′                     =  step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M
...        | step M—→M′                 =  step (ξ-·₂ V-ƛ M—→M′)
...        | done VM                    =  step (β-ƛ VM)

data _—→∗_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where
  refl : ∀ {M}
    → M —→∗ M
  step : ∀ {M N O}
    → M —→∗ N
    → N —→ O
    → M —→∗ O

data Normalizes {Γ A} (M : Γ ⊢ A) : Set where
  NormalizesTo : (N : Γ ⊢ A)
    → Value N
    → M —→∗ N
    → Normalizes M

data _AppearsFreeIn_ : ∀ {Γ A B} → (Γ ∋ A) → (Γ ⊢ B) → Set where
  AFI-` : ∀ {Γ A} {x : Γ ∋ A}
    → x AppearsFreeIn (` x)
  AFI-ƛ : ∀ {Γ A B C} (x : Γ ∋ A) (M : Γ , B ⊢ C)
    → (S x) AppearsFreeIn M
    → x AppearsFreeIn (ƛ M)
  AFI-·₁ : ∀ {Γ A B C} (x : Γ ∋ A) (M : Γ ⊢ B ⇒ C) (N : Γ ⊢ B)
    → x AppearsFreeIn M
    → x AppearsFreeIn (M · N)
  AFI-·₂ : ∀ {Γ A B C} (x : Γ ∋ A) (M : Γ ⊢ B ⇒ C) (N : Γ ⊢ B)
    → x AppearsFreeIn N
    → x AppearsFreeIn (M · N)

{-
A≡B∧x≡y⇒xAppearsFreeIn`y : ∀ {Γ A B} {x : Γ ∋ A} {y : Γ ∋ B} (p : A ≡ B)
  → Eq.subst (Γ ∋_) p x ≡ y
  → x AppearsFreeIn (` y)
A≡B∧x≡y⇒xAppearsFreeIn`y refl refl = AFI-`

xAppearsFreeIn`y⇒A≡B : ∀ {Γ A B} {x : Γ ∋ A} {y : Γ ∋ B}
  → x AppearsFreeIn (` y)
  → A ≡ B
xAppearsFreeIn`y⇒A≡B AFI-` = refl

xAppearsFreeIn`y⇒x≡y : ∀ {Γ A B} {x : Γ ∋ A} {y : Γ ∋ B} (afi : x AppearsFreeIn (` y))
  → Eq.subst (Γ ∋_) (xAppearsFreeIn`y⇒A≡B afi) x ≡ y
xAppearsFreeIn`y⇒x≡y AFI-` = refl

module _ where
  open Data.Product using () renaming (_,_ to _⸴_)

  AppearsFreeIn-rename`⁻ : ∀ {Γ Δ A B} {x : Γ ∋ A} {y : Γ ∋ B} {ρ : ∀ {A} → Γ ∋ A → Δ ∋ A}
    → (∀ {A} {x y : Γ ∋ A} → ρ x ≡ ρ y → x ≡ y)
    → ρ x AppearsFreeIn (` ρ y)
    → x AppearsFreeIn (` y)
  AppearsFreeIn-rename`⁻ {x = x} {y = y} {ρ = ρ} ρ-inj ρxAFI`ρy with Eq.subst (λ ∙ → ρ x AppearsFreeIn (` ∙)) (Eq.sym (xAppearsFreeIn`y⇒x≡y ρxAFI`ρy)) ρxAFI`ρy
  ...  | foo = A≡B∧x≡y⇒xAppearsFreeIn`y (xAppearsFreeIn`y⇒A≡B ρxAFI`ρy) (ρ-inj {!!})

  AppearsFreeIn-rename⁻ : ∀ {Γ Δ A B} {x : Γ ∋ A} (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A) (M : Γ ⊢ B)
    → (∀ {A} {x y : Γ ∋ A} → ρ x ≡ ρ y → x ≡ y)
    → ρ x AppearsFreeIn rename ρ M
    → x AppearsFreeIn M
  AppearsFreeIn-rename⁻ {Γ = Γ} {x = x} ρ (` y) ρ-inj ρxAppearsFreeIn`ρy = {!!}
  AppearsFreeIn-rename⁻ ρ (ƛ M) ρ-inj ρxAppearsFreeIn[rename[ρ]ƛM] = {!!}
  AppearsFreeIn-rename⁻ ρ (M · N) ρ-inj ρxAppearsFreeIn[rename[ρ][M·N]] = {!!}

  AppearsFreeIn-subst⁻ : ∀ {Γ Δ A B} {x : Δ ∋ A} (σ : ∀ {A} → Γ ∋ A → Δ ⊢ A) (M : Γ ⊢ B)
    → x AppearsFreeIn subst σ M
    → ∃[ C ] Σ[ y ∈ Γ ∋ C ] ∃[ N ] σ y ≡ N × x AppearsFreeIn N
  AppearsFreeIn-subst⁻ {x = x} σ (` y) xAppearsFreeIn[subst[σ]`y] =
    -, y ⸴ σ y ⸴ refl ⸴ xAppearsFreeIn[subst[σ]`y]
  AppearsFreeIn-subst⁻ {x = x} σ (ƛ M) (AFI-ƛ _ _ xAppearsFreeIn[subst[exts[σ]]M])
    with AppearsFreeIn-subst⁻ (exts σ) (M) xAppearsFreeIn[subst[exts[σ]]M]
  ...  | C ⸴ Z   ⸴ _ ⸴ refl ⸴ ()
  ...  | C ⸴ S y ⸴ N ⸴ refl ⸴ xAppearsFreeInN = -, y ⸴ σ y ⸴ refl ⸴ {!xAppearsFreeInN!}
  AppearsFreeIn-subst⁻ {x = x} σ (M · N) xAppearsFreeIn[subst[σ][M·N]] = -, {!!} ⸴ {!!} ⸴ {!!} ⸴ {!!}
-}

AppearsFreeIn-subst⁺ : ∀ {Γ Δ A B} {x : Γ ∋ A} {y : Δ ∋ A} {σ : ∀ {A} → Γ ∋ A → Δ ⊢ A} {M : Γ ⊢ B}
  → x AppearsFreeIn M
  → σ x ≡ ` y
  → y AppearsFreeIn subst σ M
AppearsFreeIn-subst⁺ AFI-`                          σx≡`y rewrite σx≡`y = AFI-`
AppearsFreeIn-subst⁺ (AFI-ƛ _ M xAppearsFreeInM)    σx≡`y               = AFI-ƛ _ _ (AppearsFreeIn-subst⁺ xAppearsFreeInM (Eq.cong (rename S_) σx≡`y))
AppearsFreeIn-subst⁺ (AFI-·₁ _ M N xAppearsFreeInM) σx≡`y               = AFI-·₁ _ _ _ (AppearsFreeIn-subst⁺ xAppearsFreeInM σx≡`y)
AppearsFreeIn-subst⁺ (AFI-·₂ _ M N xAppearsFreeInM) σx≡`y               = AFI-·₂ _ _ _ (AppearsFreeIn-subst⁺ xAppearsFreeInM σx≡`y)

SxAppearsFreeInM⇒xAppearsFreeIn[M[N]] : ∀ {Γ A B C} {x : Γ ∋ A} {M : Γ , B ⊢ C} {N : Γ ⊢ B}
  → (S x) AppearsFreeIn M
  → x AppearsFreeIn (M [ N ])
SxAppearsFreeInM⇒xAppearsFreeIn[M[N]] SxAppearsFreeInM = AppearsFreeIn-subst⁺ SxAppearsFreeInM refl

xAppearsFreeIn[M[N]]⇒SxAppearsFreeInM⊎xAppearsFreeInN : ∀ {Γ A B C} {x : Γ ∋ A} {M : Γ , B ⊢ C} {N : Γ ⊢ B}
  → x AppearsFreeIn (M [ N ])
  → (S x) AppearsFreeIn M ⊎ x AppearsFreeIn N
xAppearsFreeIn[M[N]]⇒SxAppearsFreeInM⊎xAppearsFreeInN xAppearsFreeIn[M[N]] = {!!}

Closed : ∀ {Γ A} → (Γ ⊢ A) → Set
Closed {Γ} M =
  ∀ {B} (x : Γ ∋ B) → ¬ x AppearsFreeIn M

Closed[M·N]⇒ClosedM : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
  → Closed (M · N)
  → Closed M
Closed[M·N]⇒ClosedM Closed[M·N] x AFI-` = Closed[M·N] x (AFI-·₁ x (` x) _ AFI-`)
Closed[M·N]⇒ClosedM Closed[M·N] x (AFI-ƛ .x M xAppearsFreeInM) = Closed[M·N] x (AFI-·₁ x (ƛ M) _ (AFI-ƛ x M xAppearsFreeInM))
Closed[M·N]⇒ClosedM Closed[M·N] x (AFI-·₁ .x M N xAppearsFreeInM) = Closed[M·N] x (AFI-·₁ x (M · N) _ (AFI-·₁ x M N xAppearsFreeInM))
Closed[M·N]⇒ClosedM Closed[M·N] x (AFI-·₂ .x M N xAppearsFreeInN) = Closed[M·N] x (AFI-·₁ x (M · N) _ (AFI-·₂ x M N xAppearsFreeInN))

Closed[M·N]⇒ClosedN : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
  → Closed (M · N)
  → Closed N
Closed[M·N]⇒ClosedN Closed[M·N] x AFI-` = Closed[M·N] x (AFI-·₂ x _ (` x) AFI-`)
Closed[M·N]⇒ClosedN Closed[M·N] x (AFI-ƛ .x M xAppearsFreeInN) = Closed[M·N] x (AFI-·₂ x _ (ƛ M) (AFI-ƛ x M xAppearsFreeInN))
Closed[M·N]⇒ClosedN Closed[M·N] x (AFI-·₁ .x M N xAppearsFreeInN) = Closed[M·N] x (AFI-·₂ x _ (M · N) (AFI-·₁ x M N xAppearsFreeInN))
Closed[M·N]⇒ClosedN Closed[M·N] x (AFI-·₂ .x M N xAppearsFreeInN) = Closed[M·N] x (AFI-·₂ x _ (M · N) (AFI-·₂ x M N xAppearsFreeInN))

ClosedM∧ClosedN⇒Closed[M·N] : ∀ {Γ A B} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
  → Closed M
  → Closed N
  → Closed (M · N)
ClosedM∧ClosedN⇒Closed[M·N] ClosedM ClosedN x (AFI-·₁ .x _ _ xAppearsFreeIn[M]) = ClosedM x xAppearsFreeIn[M]
ClosedM∧ClosedN⇒Closed[M·N] ClosedM ClosedN x (AFI-·₂ .x _ _ xAppearsFreeIn[N]) = ClosedN x xAppearsFreeIn[N]

—→-Closed : ∀ {Γ A} {M N : Γ ⊢ A}
  → Closed M
  → M —→ N
  → Closed N
—→-Closed Closed[M·N] (ξ-·₁ M—→M′) x (AFI-·₁ .x _ _ xAppearsFreeInM′) = —→-Closed (Closed[M·N]⇒ClosedM Closed[M·N]) M—→M′ x xAppearsFreeInM′
—→-Closed Closed[M·N] (ξ-·₁ M—→M′) x (AFI-·₂ .x _ _ xAppearsFreeInN) = Closed[M·N]⇒ClosedN Closed[M·N] x xAppearsFreeInN
—→-Closed Closed[M·N] (ξ-·₂ ValueN N—→N′) x (AFI-·₁ .x _ _ xAppearsFreeInM) = Closed[M·N]⇒ClosedM Closed[M·N] x xAppearsFreeInM
—→-Closed Closed[M·N] (ξ-·₂ ValueN N—→N′) x (AFI-·₂ .x _ _ xAppearsFreeInN′) = —→-Closed (Closed[M·N]⇒ClosedN Closed[M·N]) N—→N′ x xAppearsFreeInN′
—→-Closed Closed[ƛM·N] (β-ƛ ValueN) x xAppearsFreeIn[M[N]] = {!!}

data R : ∀ {Γ A} → (Γ ⊢ A) → Set where
  R-` : ∀ {Γ A} {x : Γ ∋ A}
    → R (` x)
  R-ƛ : ∀ {Γ A B} (M : Γ , A ⊢ B)
    → (∀ N → Closed N → R (M [ N ]))
    → R (ƛ M)
  R-—→ : ∀ {Γ A} {M N : Γ ⊢ A}
    → M —→ N
    → R N
    → R M

r : ∀ {Γ A} (M : Γ ⊢ A)
  → Closed M
  → R M
r {A = A} (` x) ClosedM = ⊥-elim (ClosedM x AFI-`)
r {A = A ⇒ B} (ƛ M) ClosedM = R-ƛ M λ N ClosedN → r (M [ N ]) λ x xAppearsFreeInM[N] → ClosedM∧ClosedN⇒Closed[M·N] ClosedM ClosedN x {!!}
r {A = A} (M · N) ClosedM = {!!}

norm : ∀ {A} → (M : ∅ ⊢ A) → Normalizes M
norm M = {!!}
```
