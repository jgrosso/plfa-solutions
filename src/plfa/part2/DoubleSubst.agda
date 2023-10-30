module plfa.part2.DoubleSubst where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _*_; _<_; _≤?_; z≤n; s≤s; _⊔_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; _on_; case_of_)
open import Induction using (RecStruct)
open import Induction.WellFounded using (Acc; acc; WellFounded; WfRec)
import Induction.WellFounded as WF
open import Relation.Nullary using (¬_; no; yes)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.Construct.On using (wellFounded)
import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_

data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type

_≟-Type_ : DecidableEquality Type
`ℕ        ≟-Type `ℕ        = yes refl
`ℕ        ≟-Type (U₁ ⇒ U₂) = no λ()
(T₁ ⇒ T₂) ≟-Type `ℕ        = no λ()
(T₁ ⇒ T₂) ≟-Type (U₁ ⇒ U₂) with T₁ ≟-Type U₁ | T₂ ≟-Type U₂
...                           | yes refl     | yes refl = yes refl
...                           | no T₁≢U₁     | _        = no λ{ refl → T₁≢U₁ refl }
...                           | _            | no T₂≢U₂ = no λ{ refl → T₂≢U₂ refl }

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

_≟-Context_ : DecidableEquality Context
∅       ≟-Context ∅       = yes refl
∅       ≟-Context (Δ , y) = no λ()
(Γ , x) ≟-Context ∅       = no λ()
(Γ , x) ≟-Context (Δ , y) with Γ ≟-Context Δ | x ≟-Type y
...                          | yes refl      | yes refl = yes refl
...                          | no  Γ≢Δ       | _        = no λ{ refl → Γ≢Δ refl }
...                          | _             | no  x≢y  = no λ{ refl → x≢y refl }

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
    → Γ , A ∋ A
  S_ : ∀ {Γ A B}
    → Γ ∋ B
    → Γ , A ∋ B

data _⊢_ : Context → Type → Set where
  `_ : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢ A
  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
    → Γ ⊢ A ⇒ B
  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
    → Γ ⊢ B
  `zero : ∀ {Γ}
    → Γ ⊢ `ℕ
  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
    → Γ ⊢ `ℕ
  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
    → Γ ⊢ A

data extrinsic-term : Set where
  `ₑ_ : {Γ : Context} {A : Type}
    → Γ ∋ A
    → extrinsic-term
  ƛₑ_ :
      extrinsic-term
    → extrinsic-term
  _·ₑ_ :
      extrinsic-term
    → extrinsic-term
    → extrinsic-term
  `zeroₑ : (Γ : Context)
    → extrinsic-term
  `sucₑ_ :
      extrinsic-term
    → extrinsic-term
  caseₑ :
      extrinsic-term
    → extrinsic-term
    → extrinsic-term
    → extrinsic-term

record packed-term : Set where
  constructor ι
  field
    {Γ} : Context
    {A} : Type
    ⌊_⌋ : Γ ⊢ A

open packed-term

module _
  (P : packed-term → Set)
  (P-` : ∀ {Γ A} {x : Γ ∋ A} → P (ι (` x)))
  (P-ƛ : ∀ {Γ A B} {M : Γ , A ⊢ B} → P (ι M) → P (ι (ƛ M)))
  (P-· : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} → P (ι L) → P (ι M) → P (ι (L · M)))
  (P-`zero : ∀ {Γ} → P (ι {Γ} `zero))
  (P-`suc : ∀ {Γ} {M : Γ ⊢ `ℕ} → P (ι M) → P (ι (`suc M)))
  (P-case : ∀ {Γ A} {L : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A} → P (ι L) → P (ι M) → P (ι N) → P (ι (case L M N)))
  where

  private
    packed-term-ind′ : ∀ {Γ A} (M : Γ ⊢ A) → P (ι M)
    packed-term-ind′ (` x) = P-`
    packed-term-ind′ (ƛ M) = P-ƛ (packed-term-ind′ M)
    packed-term-ind′ (L · M) = P-· (packed-term-ind′ L) (packed-term-ind′ M)
    packed-term-ind′ `zero = P-`zero
    packed-term-ind′ (`suc M) = P-`suc (packed-term-ind′ M)
    packed-term-ind′ (case L M N) = P-case (packed-term-ind′ L) (packed-term-ind′ M) (packed-term-ind′ N)

  packed-term-ind : (M : packed-term) → P M
  packed-term-ind (ι M) = packed-term-ind′ M

to-extrinsic′ : ∀ {Γ A} → Γ ⊢ A → extrinsic-term
to-extrinsic′ (` x) =
  `ₑ x
to-extrinsic′ (ƛ_ {Γ} {A} {B} M) =
  ƛₑ (to-extrinsic′ M)
to-extrinsic′ (_·_ {Γ} {A} {B} L M) =
  (to-extrinsic′ L) ·ₑ (to-extrinsic′ M)
to-extrinsic′ {Γ} `zero =
  `zeroₑ Γ
to-extrinsic′ (`suc_ {Γ} M) =
  `sucₑ (to-extrinsic′ M)
to-extrinsic′ (case {Γ} {A} L M N) =
  caseₑ (to-extrinsic′ L) (to-extrinsic′ M) (to-extrinsic′ N)

to-extrinsic : packed-term → extrinsic-term
to-extrinsic = to-extrinsic′ ∘ ⌊_⌋

from-extrinsic : extrinsic-term → Maybe packed-term

from-extrinsic (`ₑ x) = just (ι (` x))

from-extrinsic (ƛₑ M)
  with from-extrinsic M
...  | just (ι {Γ , A} M′) = just (ι (ƛ M′))
...  | _                   = nothing

from-extrinsic (L ·ₑ M) with from-extrinsic L        | from-extrinsic M
...                        | just (ι {Γ} {A ⇒ B} L′) | just (ι {Δ} {C} M′) with Γ ≟-Context Δ | A ≟-Type C
...                                                                           | yes refl      | yes refl = just (ι (L′ · M′))
...                                                                           | yes refl      | no _     = nothing
...                                                                           | no  _         | _        = nothing
from-extrinsic _           | _                       | _ = nothing

from-extrinsic (`zeroₑ Γ) = just (ι {Γ} `zero)

from-extrinsic (`sucₑ M) with from-extrinsic M
...                         | just (ι {Γ} {`ℕ} M′) = just (ι (`suc M′))
...                         | _                    = nothing

from-extrinsic (caseₑ L M N) with from-extrinsic L     | from-extrinsic M    | from-extrinsic N
...                             | just (ι {Γ} {`ℕ} L′) | just (ι {Δ} {A} M′) | just (ι {Ε , `ℕ} {B} N′) with Γ ≟-Context Δ | Δ ≟-Context Ε | A ≟-Type B
...                                                                                                        | yes refl      | yes refl      | yes refl = just (ι (case L′ M′ N′))
...                                                                                                        | yes refl      | no  _         | _        = nothing
...                                                                                                        | no  _         | _             | _        = nothing
...                                                                                                        | _             | _             | no  _    = nothing
from-extrinsic _                | _                    | _                   | _ = nothing

from-to-extrinsic′ : ∀ {Γ A} (M : Γ ⊢ A)
  → from-extrinsic (to-extrinsic (ι {Γ} M)) ≡ just (ι M)
from-to-extrinsic′ (` x) = refl
from-to-extrinsic′ (ƛ M) rewrite from-to-extrinsic′ M = refl
from-to-extrinsic′ {Γ} (_·_ {A = A} L M)
  rewrite from-to-extrinsic′ L
        | from-to-extrinsic′ M
        | Eq.≡-≟-identity _≟-Context_ (refl {x = Γ})
        | Eq.≡-≟-identity _≟-Type_    (refl {x = A})
  = refl
from-to-extrinsic′ `zero = refl
from-to-extrinsic′ (`suc M) rewrite from-to-extrinsic′ M = refl
from-to-extrinsic′ (case {Γ} {A} L M N)
  rewrite from-to-extrinsic′ L
        | from-to-extrinsic′ M
        | from-to-extrinsic′ N
        | Eq.≡-≟-identity _≟-Context_ (refl {x = Γ})
        | Eq.≡-≟-identity _≟-Type_    (refl {x = A})
  = refl

from-to-extrinsic : ∀ M → from-extrinsic (to-extrinsic M) ≡ just M
from-to-extrinsic = from-to-extrinsic′ ∘ ⌊_⌋

K : {A : Set} {x : A} (P : x ≡ x → Set) →
    P refl → (x≡x : x ≡ x) → P x≡x
K P p refl = p

to-from-extrinsic : ∀ (M : extrinsic-term) →
  case from-extrinsic M of λ where
    (just M′) → to-extrinsic M′ ≡ M
    nothing   → ⊤

to-from-extrinsic (`ₑ x) = refl

to-from-extrinsic (ƛₑ M) with from-extrinsic M      | to-from-extrinsic M
...                         | (just (ι {Γ , A} M′)) | refl = refl
...                         | (just (ι {∅}     M′)) | _    = tt
...                         | nothing               | _    = tt

to-from-extrinsic (L ·ₑ M) with from-extrinsic L              | from-extrinsic M          | to-from-extrinsic L | to-from-extrinsic M
...                           | (just (ι {Γ} {A = A ⇒ B} L′)) | (just (ι {Δ} {A = C} M′)) | refl                | refl with Γ ≟-Context Δ | A ≟-Type C
...                                                                                                                       | yes refl      | yes refl = refl
...                                                                                                                       | yes refl      | no  _    = tt
...                                                                                                                       | no  _         | _        = tt
to-from-extrinsic _           | (just (ι {Γ} {A = A ⇒ B} L′)) | nothing                   | refl                | tt   = tt
to-from-extrinsic _           | (just (ι {A = `ℕ} L′))        | (just (ι M′))             | refl                | refl = tt
to-from-extrinsic _           | (just (ι {A = `ℕ} L′))        | nothing                   | refl                | tt   = tt
to-from-extrinsic _           | nothing                       | (just (ι M′))             | tt                  | refl = tt
to-from-extrinsic _           | nothing                       | nothing                   | tt                  | tt   = tt

to-from-extrinsic (`zeroₑ Γ) = refl

to-from-extrinsic (`sucₑ M) with from-extrinsic M          | to-from-extrinsic M
...                            | (just (ι {A = `ℕ} M′))    | refl = refl
...                            | (just (ι {A = _ ⇒ _} M′)) | refl = tt
...                            | nothing                   | tt   = tt

to-from-extrinsic (caseₑ L M N) with from-extrinsic L           | from-extrinsic M      | from-extrinsic N           | to-from-extrinsic L | to-from-extrinsic M | to-from-extrinsic N
to-from-extrinsic _                | (just (ι {Γ} {A = `ℕ} L′)) | (just (ι {Δ} {A} M′)) | (just (ι {Ε , `ℕ} {B} N′)) | refl                | refl                | refl with Γ ≟-Context Δ | Δ ≟-Context Ε | A ≟-Type B
...                                                                                                                                                                        | yes refl      | yes refl      | yes refl = refl
...                                                                                                                                                                        | yes refl      | yes refl      | no  _    = tt
...                                                                                                                                                                        | yes refl      | no  _         | yes refl = tt
...                                                                                                                                                                        | yes refl      | no  _         | no  _    = tt
...                                                                                                                                                                        | no  _         | _             | _        = tt
to-from-extrinsic _                | (just (ι {A = `ℕ} L′))     | (just (ι M′))         | (just (ι {_ , _ ⇒ _} N′))  | refl                | refl                | refl = tt
to-from-extrinsic _                | (just (ι {A = `ℕ} L′))     | (just (ι M′))         | (just (ι {∅} N′))          | refl                | refl                | refl = tt
to-from-extrinsic _                | (just (ι {A = `ℕ} L′))     | (just (ι M′))         | nothing                    | refl                | refl                | tt   = tt
to-from-extrinsic _                | (just (ι {A = `ℕ} L′))     | nothing               | (just (ι N′))              | refl                | tt                  | refl = tt
to-from-extrinsic _                | (just (ι {A = `ℕ} L′))     | nothing               | nothing                    | refl                | tt                  | tt   = tt
to-from-extrinsic _                | (just (ι {A = _ ⇒ _} L′))  | (just (ι M′))         | (just (ι {Ε , `ℕ} N′))     | refl                | refl                | refl = tt
to-from-extrinsic _                | (just (ι {A = _ ⇒ _} L′))  | (just (ι M′))         | (just (ι {Ε , _ ⇒ _} N′))  | refl                | refl                | refl = tt
to-from-extrinsic _                | (just (ι {A = _ ⇒ _} L′))  | (just (ι M′))         | (just (ι {∅} N′))          | refl                | refl                | refl = tt
to-from-extrinsic _                | (just (ι {A = _ ⇒ _} L′))  | (just (ι M′))         | nothing                    | refl                | refl                | tt   = tt
to-from-extrinsic _                | (just (ι {A = _ ⇒ _} L′))  | nothing               | (just (ι N′))              | refl                | tt                  | refl = tt
to-from-extrinsic _                | (just (ι {A = _ ⇒ _} L′))  | nothing               | nothing                    | refl                | tt                  | tt   = tt
to-from-extrinsic _                | nothing                    | _                     | _                          | tt                  | _                   | _    = tt

-- term-depth : extrinsic-term → ℕ
-- term-depth (`ₑ _) = 0
-- term-depth (ƛₑ M) = suc (term-depth M)
-- term-depth (L ·ₑ M) = suc (term-depth L ⊔ term-depth M)
-- term-depth (`zeroₑ Γ) = 0
-- term-depth (`sucₑ M) = suc (term-depth M)
-- term-depth (caseₑ L M N) = suc (term-depth L ⊔ term-depth M ⊔ term-depth N)

-- _<ₑ_ : extrinsic-term → extrinsic-term → Set
-- _<ₑ_ = _<_ on term-depth

-- <ₑ-well-founded : WellFounded _<ₑ_
-- <ₑ-well-founded = wellFounded term-depth <-wellFounded

-- open WF.All <ₑ-well-founded renaming (wfRec to <ₑ-rec)

term-depth : ∀ {Γ A} → Γ ⊢ A → ℕ
term-depth (` _) = 0
term-depth (ƛ M) = suc (term-depth M)
term-depth (L · M) = suc (term-depth L ⊔ term-depth M)
term-depth (`zero) = 0
term-depth (`suc M) = suc (term-depth M)
term-depth (case L M N) = suc (term-depth L ⊔ term-depth M ⊔ term-depth N)

term-depth′ : packed-term → ℕ
term-depth′ = term-depth ∘ ⌊_⌋

_≺_ : packed-term → packed-term → Set
_≺_ = _<_ on term-depth′

≺-well-founded : WellFounded _≺_
≺-well-founded = wellFounded term-depth′ <-wellFounded

open WF.All ≺-well-founded renaming (wfRec to ≺-rec)

-- module _
--   (P : ∀ {Γ A} → Γ ⊢ A → Set)
--   (P-ι : ((M : packed-term) → P ⌊ M ⌋) → ∀ {Γ A} (M : Γ ⊢ A) → P M)
--   (P-↑ : ∀ {Γ} → (∀ {A} (M : Γ ⊢ A) → P M) → ∀ {A B} (M : Γ , A ⊢ B) → P M)
--   (P-↑² : ∀ {Γ} → (∀ {A} (M : Γ ⊢ A) → P M) → ∀ {A B C} (M : Γ , A , B ⊢ C) → P M)
--   (P-` : ∀ {Γ A} {x : Γ ∋ A} → P (` x))
--   (P-`zero : ∀ {Γ} → P {Γ} `zero)
--   (P-ƛ : ∀ {Γ A} → ((M : Γ ⊢ A) → P M) → (M : Γ ⊢ A) → P (ƛ M))
--   where

--   term-ind : ∀ {Γ A} (M : Γ ⊢ A) → P M
--   term-ind = P-ι (≺-rec _ (P ∘ ⌊_⌋) λ where
--     (ι (` x)) ind → P-`
--     (ι (ƛ M)) ind → {!!}
--     (ι (L · M)) ind → {!!}
--     (ι `zero) ind → {!!}
--     (ι (`suc M)) ind → {!!}
--     (ι (case L M N)) ind → {!!})

-- module _
--   (P : ∀ {Γ A} → Γ ⊢ A → Set)
--   (P-↑ : ∀ {Γ} → (∀ {A} (M : Γ ⊢ A) → P M) → ∀ {A B} (M : Γ , A ⊢ B) → P M)
--   (P-↑² : ∀ {Γ} → (∀ {A} (M : Γ ⊢ A) → P M) → ∀ {A B C} (M : Γ , A , B ⊢ C) → P M)
--   (P-` : ∀ {Γ A} {x : Γ ∋ A} → P (` x))
--   (P-ƛ : ∀ {Γ A B} {M : Γ , A ⊢ B} → P M → P (ƛ M))
--   (P-· : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} → P L → P M → P (L · M))
--   (P-`zero : ∀ {Γ} → P {Γ} `zero)
--   (P-`suc : ∀ {Γ} {M : Γ ⊢ `ℕ} → P M → P (`suc M))
--   (P-case : ∀ {Γ A} {L : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A} → P L → P M → P N → P (case L M N))
--   where
--   term-ind : ∀ {Γ A} (M : Γ ⊢ A) → P M
--   term-ind (` x) = P-` x
--   term-ind (ƛ M) = P-ƛ (P-↑ term-ind M)
--   term-ind (L · M) = P-· (term-ind L) (term-ind M)
--   term-ind `zero = P-`zero
--   term-ind (`suc M) = P-`suc (term-ind M)
--   term-ind (case L M N) = P-case (term-ind L) (term-ind M) (P-↑ term-ind N)

ext : ∀ {Γ Δ}
  → (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , A ∋ B → Δ , A ∋ B)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
rename ρ (`suc M)       =  `suc (rename ρ M)
rename ρ (case L M N)   =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)

exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A B} → Γ , A ∋ B → Δ , A ⊢ B)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ} → (∀ {C} → Γ ∋ C → Δ ⊢ C) → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`zero)        =  `zero
subst σ (`suc M)       =  `suc (subst σ M)
subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)

substZero : ∀ {Γ}{A B} → Γ ⊢ A → Γ , A ∋ B → Γ ⊢ B
substZero V Z      =  V
substZero V (S x)  =  ` x

_[_] : ∀ {Γ A B}
  → Γ , A ⊢ B
  → Γ ⊢ A
    ---------
  → Γ ⊢ B
_[_] {Γ} {A} N V =  subst {Γ , A} {Γ} (substZero V) N

_[_][_] : ∀ {Γ A B C}
  → Γ , A , B ⊢ C
  → Γ ⊢ A
  → Γ ⊢ B
    -------------
  → Γ ⊢ C
_[_][_] {Γ} {A} {B} N V W =  subst {Γ , A , B} {Γ} σ N
  where
  σ : ∀ {C} → Γ , A , B ∋ C → Γ ⊢ C
  σ Z          =  W
  σ (S Z)      =  V
  σ (S (S x))  =  ` x

open import Axiom.Extensionality.Propositional using (ExtensionalityImplicit)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (extensionality)

postulate
  extensionality-implicit : ∀ {a b} → ExtensionalityImplicit a b

exts-ext : ∀ {Γ Δ Ε A B} (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A) (σ : ∀ {A} → Δ ∋ A → Ε ⊢ A)
  → exts σ {A} {B} ∘ ext ρ ≡ exts (σ ∘ ρ)
exts-ext ρ σ = extensionality
  λ{ Z     → refl
   ; (S _) → refl
   }

cong-app-implicit : ∀ {A : Set} {B : A → Set} {f g : {x : A} → B x} →
  (λ {x} → f {x}) ≡ (λ {x} → g {x}) → {x : A} → f {x} ≡ g {x}
cong-app-implicit refl = refl

exts²-ext² : ∀ {Γ Δ Ε : Context} {A B C : Type}
  → (ρ : ∀ {A : Type} → Γ ∋ A → Δ ∋ A)
  → (σ : ∀ {A : Type} → Δ ∋ A → Ε ⊢ A)
  → exts (exts σ {C}) {A} {B} ∘ (ext (ext ρ)) ≡ exts (exts (σ ∘ ρ))
exts²-ext² ρ σ = extensionality λ x →
  begin
    (exts (exts σ) ∘ ext (ext ρ)) x
  ≡⟨ Eq.cong-app (exts-ext (ext ρ) (exts σ)) x ⟩
    exts (exts σ ∘ ext ρ) x
  ≡⟨ Eq.cong-app (cong-app-implicit (cong-app-implicit
       (Eq.cong exts (extensionality-implicit (exts-ext ρ σ)))))
       x ⟩
    exts (exts (σ ∘ ρ)) x
  ∎

subst-rename : ∀ {Γ Δ Ε A} (M : Γ ⊢ A) (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A) (σ : ∀ {A} → Δ ∋ A → Ε ⊢ A)
  → subst σ (rename ρ M) ≡ subst (σ ∘ ρ) M
subst-rename (` x) ρ σ = refl
subst-rename {Γ} {Ε = Ε} {A} (ƛ M) ρ σ
  rewrite subst-rename M (ext ρ) (exts σ)
  = Eq.cong (λ (∙ : ∀ {A} → Γ , _ ∋ A → Ε , _ ⊢ A) →
               ƛ subst ∙ M)
      (extensionality-implicit (exts-ext ρ σ))
subst-rename (L · M) ρ σ
  rewrite subst-rename L ρ σ
        | subst-rename M ρ σ
  = refl
subst-rename `zero ρ σ = refl
subst-rename (`suc M) ρ σ rewrite subst-rename M ρ σ = refl
subst-rename {Γ} {Ε = Ε} {A} (case L M N) ρ σ
  rewrite subst-rename L ρ σ
        | subst-rename M ρ σ
        | subst-rename N (ext ρ) (exts σ)
  = Eq.cong (λ (∙ : ∀ {A} → Γ , _ ∋ A → Ε , _ ⊢ A) →
               case (subst (σ ∘ ρ) L) (subst (σ ∘ ρ) M) (subst ∙ N))
      (extensionality-implicit (exts-ext ρ σ))

exts-` : ∀ {Γ : Context} {A B : Type}
  → exts {Γ} `_ {A} {B} ≡ `_
exts-` = extensionality
  λ{ Z     → refl
   ; (S x) → refl
   }

exts²-` : ∀ {Γ : Context} {A B C : Type}
  → exts {Γ , A} (exts {Γ} `_) {B} {C} ≡ `_
exts²-` = extensionality
  λ{ Z         → refl
   ; (S Z)     → refl
   ; (S (S x)) → refl
   }

subst-` : ∀ {Γ : Context} {A : Type} (M : Γ ⊢ A)
  → subst `_ M ≡ M
subst-exts-` : ∀ {Γ : Context} {A B : Type} (M : Γ , A ⊢ B)
  → subst (exts `_) M ≡ M
subst-exts²-` : ∀ {Γ : Context} {A B C : Type} (M : Γ , A , B ⊢ C)
  → subst (exts (exts `_)) M ≡ M

subst-` (` x) = refl
subst-` (ƛ M) rewrite subst-exts-` M = refl
subst-` (L · M) rewrite subst-` L | subst-` M = refl
subst-` `zero = refl
subst-` (`suc M) rewrite subst-` M = refl
subst-` (case L M N) rewrite subst-` L | subst-` M | subst-exts-` N = refl

subst-exts-` M =
  begin
    subst (exts `_) M
  ≡⟨ Eq.cong-app (cong-app-implicit
       (Eq.cong subst (extensionality-implicit exts-`)))
       M ⟩
    subst `_ M
  ≡⟨ subst-` M ⟩
    M
  ∎

subst-exts²-` {Γ} {A = A} M =
  begin
    subst (exts (exts `_)) M
  ≡⟨ Eq.cong-app (cong-app-implicit
       (Eq.cong subst (extensionality-implicit exts²-`)))
       M ⟩
    subst `_ M
  ≡⟨ subst-` M ⟩
    M
  ∎

ext² : ∀ {Γ Δ Ε : Context} {A : Type} (ρ₁ : ∀ {A} → Γ ∋ A → Δ ∋ A) (ρ₂ : ∀ {A} → Δ ∋ A → Ε ∋ A)
  → (λ {B : Type} x → ext ρ₂ {A} {B} (ext ρ₁ x)) ≡ (λ {B : Type} → ext (ρ₂ ∘ ρ₁) {A} {B})
ext² ρ₁ ρ₂ = extensionality-implicit (extensionality
 λ{ Z     → refl
  ; (S x) → refl
  })

ext⁴ : ∀ {Γ Δ Ε : Context} {A C : Type} (ρ₁ : ∀ {A} → Γ ∋ A → Δ ∋ A) (ρ₂ : ∀ {A} → Δ ∋ A → Ε ∋ A)
  → (λ {B : Type} x → ext (ext ρ₂ {C}) {A} {B} (ext (ext ρ₁) x)) ≡ (λ {B : Type} → ext (ext (ρ₂ ∘ ρ₁)) {A} {B})
ext⁴ ρ₁ ρ₂ = extensionality-implicit (extensionality
 λ{ Z     → refl
  ; (S x) → Eq.cong S_ (Eq.cong-app (cong-app-implicit (ext² ρ₁ ρ₂)) x)
  })

rename² : ∀ {Γ Δ Ε : Context} {A : Type} (ρ₁ : ∀ {A} → Γ ∋ A → Δ ∋ A) (ρ₂ : ∀ {A} → Δ ∋ A → Ε ∋ A) (M : Γ ⊢ A)
  → rename ρ₂ {A} (rename ρ₁ M) ≡ rename (ρ₂ ∘ ρ₁) M
rename² ρ₁ ρ₂ (` x) = refl
rename² {Γ} {Ε = Ε} ρ₁ ρ₂ (ƛ M)
  rewrite rename² (ext ρ₁) (ext ρ₂) M
  = Eq.cong (λ (∙ : ∀ {A} → Γ , _ ∋ A → Ε , _ ∋ A) → ƛ rename ∙ M)
      (ext² ρ₁ ρ₂)
rename² ρ₁ ρ₂ (L · M) rewrite rename² ρ₁ ρ₂ L | rename² ρ₁ ρ₂ M = refl
rename² ρ₁ ρ₂ `zero = refl
rename² ρ₁ ρ₂ (`suc M) rewrite rename² ρ₁ ρ₂ M = refl
rename² {Γ} {Ε = Ε} ρ₁ ρ₂ (case L M N)
  rewrite rename² ρ₁ ρ₂ L
        | rename² ρ₁ ρ₂ M
        | rename² (ext ρ₁) (ext ρ₂) N
  = Eq.cong
      (λ (∙ : ∀ {A} → Γ , _ ∋ A → Ε , _ ∋ A) →
        case (rename (ρ₂ ∘ ρ₁) L) (rename (ρ₂ ∘ ρ₁) M) (rename ∙ N))
      (ext² ρ₁ ρ₂)

rename-as-subst : ∀ {Γ Δ : Context} {A : Type} (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → rename ρ {A} ≡ subst (`_ ∘ ρ)
rename-as-subst ρ = extensionality λ x →
  Eq.trans
    (Eq.sym (subst-` (rename ρ x)))
    (subst-rename x ρ `_)

_⟶_ : ∀ {Γ Δ Ε : Context}
  → (∀ {A : Type} → Γ ∋ A → Δ ⊢ A)
  → (∀ {A : Type} → Δ ∋ A → Ε ⊢ A)
  → (∀ {A : Type} → Γ ∋ A → Ε ⊢ A)
σ₁ ⟶ σ₂ = subst σ₂ ∘ σ₁

rename-exts : ∀ {Γ Δ Ε A B} (σ : ∀ {A} → Γ ∋ A → Δ ⊢ A) (ρ : ∀ {A} → Δ ∋ A → Ε ∋ A)
  → rename (ext ρ {B}) {A} ∘ exts σ ≡ exts (rename ρ ∘ σ)
rename-exts σ ρ = extensionality
  λ{ Z → refl
   ; (S x) →
     begin
       rename (ext ρ) (exts σ (S x))
     ≡⟨⟩
       rename (ext ρ) (rename S_ (σ x))
     ≡⟨ rename² S_ (ext ρ) (σ x) ⟩
       rename (ext ρ ∘ S_) (σ x)
     ≡⟨⟩
       rename (S_ ∘ ρ) (σ x)
     ≡⟨ Eq.sym (rename² ρ S_ (σ x)) ⟩
       rename S_ (rename ρ (σ x))
     ≡⟨⟩
       exts (rename ρ ∘ σ) (S x)
     ∎
   }

rename-exts² : ∀ {Γ Δ Ε A B C} (σ : ∀ {A} → Γ ∋ A → Δ ⊢ A) (ρ : ∀ {A} → Δ ∋ A → Ε ∋ A)
  → rename (ext (ext ρ {C}) {B}) {A} ∘ exts (exts σ) ≡ exts (exts (rename ρ ∘ σ))
rename-exts² σ ρ =
  begin
    rename (ext (ext ρ)) ∘ exts (exts σ)
  ≡⟨ rename-exts (exts σ) (ext ρ) ⟩
    exts (rename (ext ρ) ∘ exts σ)
  ≡⟨ cong-app-implicit (cong-app-implicit
       (Eq.cong exts (extensionality-implicit
         (rename-exts σ ρ)))) ⟩
    exts (exts (rename ρ ∘ σ))
  ∎

rename-subst : ∀ {Γ Δ Ε A} (σ : ∀ {A} → Γ ∋ A → Δ ⊢ A) (ρ : ∀ {A} → Δ ∋ A → Ε ∋ A) (M : Γ ⊢ A)
  → rename ρ (subst σ M) ≡ subst (rename ρ ∘ σ) M
rename-subst σ ρ (` x) = refl
rename-subst σ ρ (ƛ M)
  rewrite rename-subst (exts σ) (ext ρ) M
  = Eq.cong ƛ_
      (Eq.cong-app (cong-app-implicit
        (Eq.cong subst (extensionality-implicit
          (rename-exts σ ρ))))
         M)
rename-subst σ ρ (L · M)
  rewrite rename-subst σ ρ L
        | rename-subst σ ρ M
  = refl
rename-subst σ ρ `zero = refl
rename-subst σ ρ (`suc M) rewrite rename-subst σ ρ M = refl
rename-subst σ ρ (case L M N)
  rewrite rename-subst σ ρ L
        | rename-subst σ ρ M
        | rename-subst (exts σ) (ext ρ) N
  = Eq.cong (case (subst (rename ρ ∘ σ) L) (subst (rename ρ ∘ σ) M))
      (Eq.cong-app (cong-app-implicit
        (Eq.cong subst (extensionality-implicit
          (rename-exts σ ρ))))
        N)

subst-exts-∘-exts : ∀ {Γ Δ Ε : Context} {A B : Type} (σ₁ : ∀ {A : Type} → Γ ∋ A → Δ ⊢ A) (σ₂ : ∀ {A : Type} → Δ ∋ A → Ε ⊢ A) (x : Γ , B ∋ A)
  → subst (exts σ₂) (exts σ₁ x) ≡ exts (subst σ₂ ∘ σ₁) x

subst-exts-∘-exts σ₁ σ₂ Z = refl
subst-exts-∘-exts {Δ = Δ} σ₁ σ₂ (S x) =
  begin
    subst (exts σ₂) (exts σ₁ (S x))
  ≡⟨⟩
    subst (exts σ₂) (rename S_ (σ₁ x))
  ≡⟨ subst-rename (σ₁ x) S_ (exts σ₂) ⟩
    subst (exts σ₂ ∘ S_) (σ₁ x)
  ≡⟨⟩
    subst (rename S_ ∘ σ₂) (σ₁ x)
  ≡⟨ Eq.sym (rename-subst σ₂ S_ (σ₁ x)) ⟩
    rename S_ (subst σ₂ (σ₁ x))
  ≡⟨⟩
    exts (subst σ₂ ∘ σ₁) (S x)
  ∎

{-
subst² : ∀ {Γ Δ Ε : Context} {A : Type} (σ₁ : ∀ {A : Type} → Γ ∋ A → Δ ⊢ A) (σ₂ : ∀ {A : Type} → Δ ∋ A → Ε ⊢ A) (M : Γ ⊢ A)
  → subst σ₂ {A} (subst σ₁ M) ≡ subst (σ₁ ⟶ σ₂) M
subst² σ₁ σ₂ (` x) = refl
subst² σ₁ σ₂ (ƛ M) rewrite subst² (exts σ₁) (exts σ₂) M =
  Eq.cong ƛ_
    (Eq.cong-app (cong-app-implicit
      (Eq.cong subst (extensionality-implicit (extensionality
        (subst-exts-∘-exts σ₁ σ₂)))))
      M)
subst² σ₁ σ₂ (L · M)
  rewrite subst² σ₁ σ₂ L
        | subst² σ₁ σ₂ M
  = refl
subst² σ₁ σ₂ `zero = refl
subst² σ₁ σ₂ (`suc M) = {!!}
subst² σ₁ σ₂ (case L M N) = {!!}

double-subst :
  ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {N : Γ , A , B ⊢ C} →
    N [ V ][ W ] ≡ (N [ rename S_ W ]) [ V ]
double-subst {V = V} {W} {` Z}
  rewrite subst-rename W S_ (substZero V)
        | subst-` W = refl
double-subst {N = ` (S Z)} = refl
double-subst {N = ` (S (S x))} = refl
double-subst {V = V} {W} {ƛ M}
  = {!!}
double-subst {N = M · N} = {!!}
double-subst {N = `zero} = refl
double-subst {N = `suc M} = {!!}
double-subst {N = case L M N} = {!!}
-}
