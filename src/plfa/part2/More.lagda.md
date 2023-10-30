---
title     : "More: Additional constructs of simply-typed lambda calculus"
permalink : /More/
---

```agda
module plfa.part2.More where
```

So far, we have focussed on a relatively minimal language, based on
Plotkin's PCF, which supports functions, naturals, and fixpoints.  In
this chapter we extend our calculus to support the following:

  * primitive numbers
  * _let_ bindings
  * products
  * an alternative formulation of products
  * sums
  * unit type
  * an alternative formulation of unit type
  * empty type
  * lists

All of the data types should be familiar from Part I of this textbook.
For _let_ and the alternative formulations we show how they translate
to other constructs in the calculus.  Most of the description will be
informal. We show how to formalise the first four constructs and leave
the rest as an exercise for the reader.

Our informal descriptions will be in the style of
Chapter [Lambda](/Lambda/),
using extrinsically-typed terms,
while our formalisation will be in the style of
Chapter [DeBruijn](/DeBruijn/),
using intrinsically-typed terms.

By now, explaining with symbols should be more concise, more precise,
and easier to follow than explaining in prose.
For each construct, we give syntax, typing, reductions, and an example.
We also give translations where relevant; formally establishing the
correctness of translations will be the subject of the next chapter.

## Primitive numbers

We define a `Nat` type equivalent to the built-in natural number type
with multiplication as a primitive operation on numbers:

### Syntax

    A, B, C ::= ...                     Types
      Nat                                 primitive natural numbers

    L, M, N ::= ...                     Terms
      con c                               constant
      L `* M                              multiplication

    V, W ::= ...                        Values
      con c                               constant

### Typing

The hypothesis of the `con` rule is unusual, in that
it refers to a typing judgment of Agda rather than a
typing judgment of the defined calculus:

    c : ℕ
    --------------- con
    Γ ⊢ con c : Nat

    Γ ⊢ L : Nat
    Γ ⊢ M : Nat
    ---------------- _`*_
    Γ ⊢ L `* M : Nat

### Reduction

A rule that defines a primitive directly, such as the last rule below,
is called a δ rule.  Here the δ rule defines multiplication of
primitive numbers in terms of multiplication of naturals as given
by the Agda standard prelude:

    L —→ L′
    ----------------- ξ-*₁
    L `* M —→ L′ `* M

    M —→ M′
    ----------------- ξ-*₂
    V `* M —→ V `* M′

    ----------------------------- δ-*
    con c `* con d —→ con (c * d)

### Example

Here is a function to cube a primitive number:

    cube : ∅ ⊢ Nat ⇒ Nat
    cube = ƛ x ⇒ x `* x `* x


## Let bindings

Let bindings affect only the syntax of terms; they introduce no new
types or values:

### Syntax

    L, M, N ::= ...                     Terms
      `let x `= M `in N                   let

### Typing

    Γ ⊢ M ⦂ A
    Γ , x ⦂ A ⊢ N ⦂ B
    ------------------------- `let
    Γ ⊢ `let x `= M `in N ⦂ B

### Reduction

    M —→ M′
    --------------------------------------- ξ-let
    `let x `= M `in N —→ `let x `= M′ `in N

    --------------------------------- β-let
    `let x `= V `in N —→ N [ x := V ]

### Example

Here is a function to raise a primitive number to the tenth power:

    exp10 : ∅ ⊢ Nat ⇒ Nat
    exp10 = ƛ x ⇒ `let x2  `= x  `* x  `in
                  `let x4  `= x2 `* x2 `in
                  `let x5  `= x4 `* x  `in
                  x5 `* x5

### Translation

We can translate each _let_ term into an application of an abstraction:

    (`let x `= M `in N) †  =  (ƛ x ⇒ (N †)) · (M †)

Here `M †` is the translation of term `M` from a calculus with the
construct to a calculus without the construct.


## Products {#products}

### Syntax

    A, B, C ::= ...                     Types
      A `× B                              product type

    L, M, N ::= ...                     Terms
      `⟨ M , N ⟩                          pair
      `proj₁ L                            project first component
      `proj₂ L                            project second component

    V, W ::= ...                        Values
      `⟨ V , W ⟩                          pair

### Typing

    Γ ⊢ M ⦂ A
    Γ ⊢ N ⦂ B
    ----------------------- `⟨_,_⟩ or `×-I
    Γ ⊢ `⟨ M , N ⟩ ⦂ A `× B

    Γ ⊢ L ⦂ A `× B
    ---------------- `proj₁ or `×-E₁
    Γ ⊢ `proj₁ L ⦂ A

    Γ ⊢ L ⦂ A `× B
    ---------------- `proj₂ or `×-E₂
    Γ ⊢ `proj₂ L ⦂ B

### Reduction

    M —→ M′
    ------------------------- ξ-⟨,⟩₁
    `⟨ M , N ⟩ —→ `⟨ M′ , N ⟩

    N —→ N′
    ------------------------- ξ-⟨,⟩₂
    `⟨ V , N ⟩ —→ `⟨ V , N′ ⟩

    L —→ L′
    --------------------- ξ-proj₁
    `proj₁ L —→ `proj₁ L′

    L —→ L′
    --------------------- ξ-proj₂
    `proj₂ L —→ `proj₂ L′

    ---------------------- β-proj₁
    `proj₁ `⟨ V , W ⟩ —→ V

    ---------------------- β-proj₂
    `proj₂ `⟨ V , W ⟩ —→ W

### Example

Here is a function to swap the components of a pair:

    swap× : ∅ ⊢ A `× B ⇒ B `× A
    swap× = ƛ z ⇒ `⟨ `proj₂ z , `proj₁ z ⟩


## Alternative formulation of products

There is an alternative formulation of products, where in place of two
ways to eliminate the type we have a case term that binds two
variables.  We repeat the syntax in full, but only give the new type
and reduction rules:

### Syntax

    A, B, C ::= ...                     Types
      A `× B                              product type

    L, M, N ::= ...                     Terms
      `⟨ M , N ⟩                          pair
      case× L [⟨ x , y ⟩⇒ M ]             case

    V, W ::=                            Values
      `⟨ V , W ⟩                          pair

### Typing

    Γ ⊢ L ⦂ A `× B
    Γ , x ⦂ A , y ⦂ B ⊢ N ⦂ C
    ------------------------------- case× or ×-E
    Γ ⊢ case× L [⟨ x , y ⟩⇒ N ] ⦂ C

### Reduction

    L —→ L′
    --------------------------------------------------- ξ-case×
    case× L [⟨ x , y ⟩⇒ N ] —→ case× L′ [⟨ x , y ⟩⇒ N ]

    --------------------------------------------------------- β-case×
    case× `⟨ V , W ⟩ [⟨ x , y ⟩⇒ N ] —→ N [ x := V ][ y := W ]

### Example

Here is a function to swap the components of a pair rewritten in the new notation:

    swap×-case : ∅ ⊢ A `× B ⇒ B `× A
    swap×-case = ƛ z ⇒ case× z
                         [⟨ x , y ⟩⇒ `⟨ y , x ⟩ ]

### Translation

We can translate the alternative formulation into the one with projections:

      (case× L [⟨ x , y ⟩⇒ N ]) †
    =
      `let z `= (L †) `in
      `let x `= `proj₁ z `in
      `let y `= `proj₂ z `in
      (N †)

Here `z` is a variable that does not appear free in `N`.  We refer
to such a variable as _fresh_.

One might think that we could instead use a more compact translation:

    -- WRONG
      (case× L [⟨ x , y ⟩⇒ N ]) †
    =
      (N †) [ x := `proj₁ (L †) ] [ y := `proj₂ (L †) ]

But this behaves differently.  The first term always reduces `L`
before `N`, and it computes `` `proj₁ `` and `` `proj₂ `` exactly once.  The
second term does not reduce `L` to a value before reducing `N`, and
depending on how many times and where `x` and `y` appear in `N`, it
may reduce `L` many times or not at all, and it may compute `` `proj₁ ``
and `` `proj₂ `` many times or not at all.

We can also translate back the other way:

    (`proj₁ L) ‡  =  case× (L ‡) [⟨ x , y ⟩⇒ x ]
    (`proj₂ L) ‡  =  case× (L ‡) [⟨ x , y ⟩⇒ y ]

## Sums {#sums}

### Syntax

    A, B, C ::= ...                     Types
      A `⊎ B                              sum type

    L, M, N ::= ...                     Terms
      `inj₁ M                             inject first component
      `inj₂ N                             inject second component
      case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ]    case

    V, W ::= ...                        Values
      `inj₁ V                             inject first component
      `inj₂ W                             inject second component

### Typing

    Γ ⊢ M ⦂ A
    -------------------- `inj₁ or ⊎-I₁
    Γ ⊢ `inj₁ M ⦂ A `⊎ B

    Γ ⊢ N ⦂ B
    -------------------- `inj₂ or ⊎-I₂
    Γ ⊢ `inj₂ N ⦂ A `⊎ B

    Γ ⊢ L ⦂ A `⊎ B
    Γ , x ⦂ A ⊢ M ⦂ C
    Γ , y ⦂ B ⊢ N ⦂ C
    ----------------------------------------- case⊎ or ⊎-E
    Γ ⊢ case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ] ⦂ C

### Reduction

    M —→ M′
    ------------------- ξ-inj₁
    `inj₁ M —→ `inj₁ M′

    N —→ N′
    ------------------- ξ-inj₂
    `inj₂ N —→ `inj₂ N′

    L —→ L′
    ---------------------------------------------------------------------- ξ-case⊎
    case⊎ L [inj₁ x ⇒ M |inj₂ y ⇒ N ] —→ case⊎ L′ [inj₁ x ⇒ M |inj₂ y ⇒ N ]

    --------------------------------------------------------- β-inj₁
    case⊎ (`inj₁ V) [inj₁ x ⇒ M |inj₂ y ⇒ N ] —→ M [ x := V ]

    --------------------------------------------------------- β-inj₂
    case⊎ (`inj₂ W) [inj₁ x ⇒ M |inj₂ y ⇒ N ] —→ N [ y := W ]

### Example

Here is a function to swap the components of a sum:

    swap⊎ : ∅ ⊢ A `⊎ B ⇒ B `⊎ A
    swap⊎ = ƛ z ⇒ case⊎ z
                    [inj₁ x ⇒ `inj₂ x
                    |inj₂ y ⇒ `inj₁ y ]


## Unit type

For the unit type, there is a way to introduce
values of the type but no way to eliminate values of the type.
There are no reduction rules.

### Syntax

    A, B, C ::= ...                     Types
      `⊤                                  unit type

    L, M, N ::= ...                     Terms
      `tt                                 unit value

    V, W ::= ...                        Values
      `tt                                 unit value

### Typing

    ------------ `tt or ⊤-I
    Γ ⊢ `tt ⦂ `⊤

### Reduction

(none)

### Example

Here is the isomorphism between `A` and ``A `× `⊤``:

    to×⊤ : ∅ ⊢ A ⇒ A `× `⊤
    to×⊤ = ƛ x ⇒ `⟨ x , `tt ⟩

    from×⊤ : ∅ ⊢ A `× `⊤ ⇒ A
    from×⊤ = ƛ z ⇒ `proj₁ z


## Alternative formulation of unit type

There is an alternative formulation of the unit type, where in place of
no way to eliminate the type we have a case term that binds zero variables.
We repeat the syntax in full, but only give the new type and reduction rules:

### Syntax

    A, B, C ::= ...                     Types
      `⊤                                  unit type

    L, M, N ::= ...                     Terms
      `tt                                 unit value
      `case⊤ L [tt⇒ N ]                   case

    V, W ::= ...                        Values
      `tt                                 unit value

### Typing

    Γ ⊢ L ⦂ `⊤
    Γ ⊢ M ⦂ A
    ------------------------ case⊤ or ⊤-E
    Γ ⊢ case⊤ L [tt⇒ M ] ⦂ A

### Reduction

    L —→ L′
    ------------------------------------- ξ-case⊤
    case⊤ L [tt⇒ M ] —→ case⊤ L′ [tt⇒ M ]

    ----------------------- β-case⊤
    case⊤ `tt [tt⇒ M ] —→ M

### Example

Here is half the isomorphism between `A` and ``A `× `⊤`` rewritten in the new notation:

    from×⊤-case : ∅ ⊢ A `× `⊤ ⇒ A
    from×⊤-case = ƛ z ⇒ case× z
                          [⟨ x , y ⟩⇒ case⊤ y
                                        [tt⇒ x ] ]


### Translation

We can translate the alternative formulation into one without case:

    (case⊤ L [tt⇒ M ]) †  =  `let z `= (L †) `in (M †)

Here `z` is a variable that does not appear free in `M`.


## Empty type

For the empty type, there is a way to eliminate values of
the type but no way to introduce values of the type.  There are no
values of the type and no β rule, but there is a ξ rule.  The `case⊥`
construct plays a role similar to `⊥-elim` in Agda:

### Syntax

    A, B, C ::= ...                     Types
      `⊥                                  empty type

    L, M, N ::= ...                     Terms
      case⊥ L []                          case

### Typing

    Γ ⊢ L ⦂ `⊥
    ------------------ case⊥ or ⊥-E
    Γ ⊢ case⊥ L [] ⦂ A

### Reduction

    L —→ L′
    ------------------------- ξ-case⊥
    case⊥ L [] —→ case⊥ L′ []

### Example

Here is the isomorphism between `A` and ``A `⊎ `⊥``:

    to⊎⊥ : ∅ ⊢ A ⇒ A `⊎ `⊥
    to⊎⊥ = ƛ x ⇒ `inj₁ x

    from⊎⊥ : ∅ ⊢ A `⊎ `⊥ ⇒ A
    from⊎⊥ = ƛ z ⇒ case⊎ z
                     [inj₁ x ⇒ x
                     |inj₂ y ⇒ case⊥ y
                                 [] ]

## Lists

### Syntax

    A, B, C ::= ...                     Types
      `List A                             list type

    L, M, N ::= ...                     Terms
      `[]                                 nil
      M `∷ N                              cons
      caseL L [[]⇒ M | x ∷ y ⇒ N ]        case

    V, W ::= ...                        Values
      `[]                                 nil
      V `∷ W                              cons

### Typing

    ----------------- `[] or List-I₁
    Γ ⊢ `[] ⦂ `List A

    Γ ⊢ M ⦂ A
    Γ ⊢ N ⦂ `List A
    -------------------- _`∷_ or List-I₂
    Γ ⊢ M `∷ N ⦂ `List A

    Γ ⊢ L ⦂ `List A
    Γ ⊢ M ⦂ B
    Γ , x ⦂ A , xs ⦂ `List A ⊢ N ⦂ B
    -------------------------------------- caseL or List-E
    Γ ⊢ caseL L [[]⇒ M | x ∷ xs ⇒ N ] ⦂ B

### Reduction

    M —→ M′
    ----------------- ξ-∷₁
    M `∷ N —→ M′ `∷ N

    N —→ N′
    ----------------- ξ-∷₂
    V `∷ N —→ V `∷ N′

    L —→ L′
    --------------------------------------------------------------- ξ-caseL
    caseL L [[]⇒ M | x ∷ xs ⇒ N ] —→ caseL L′ [[]⇒ M | x ∷ xs ⇒ N ]

    ------------------------------------ β-[]
    caseL `[] [[]⇒ M | x ∷ xs ⇒ N ] —→ M

    --------------------------------------------------------------- β-∷
    caseL (V `∷ W) [[]⇒ M | x ∷ xs ⇒ N ] —→ N [ x := V ][ xs := W ]

### Example

Here is the map function for lists:

    mapL : ∅ ⊢ (A ⇒ B) ⇒ `List A ⇒ `List B
    mapL = μ mL ⇒ ƛ f ⇒ ƛ xs ⇒
             caseL xs
               [[]⇒ `[]
               | x ∷ xs ⇒ f · x `∷ mL · f · xs ]


## Formalisation

We now show how to formalise

  * primitive numbers
  * _let_ bindings
  * products
  * an alternative formulation of products

and leave formalisation of the remaining constructs as an exercise.


### Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
```


### Syntax

```agda
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_
infixr 9 _`×_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infixl 8 _`*_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_
```

### Types

```agda
data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type
  Nat   : Type
  _`×_  : Type → Type → Type
  _`⊎_  : Type → Type → Type
  `⊤    : Type
  `⊥    : Type
  `List : Type → Type
```

### Contexts

```agda
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
```

### Variables and the lookup judgment

```agda
data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ B
      ---------
    → Γ , A ∋ B
```

### Terms and the typing judgment

```agda
data _⊢_ : Context → Type → Set where

  -- variables

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  -- functions

  ƛ_  :  ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  -- naturals

  `zero : ∀ {Γ}
      ------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      -----
    → Γ ⊢ A

  -- fixpoint

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ----------
    → Γ ⊢ A

  -- primitive numbers

  con : ∀ {Γ}
    → ℕ
      -------
    → Γ ⊢ Nat

  _`*_ : ∀ {Γ}
    → Γ ⊢ Nat
    → Γ ⊢ Nat
      -------
    → Γ ⊢ Nat

  -- let

  `let : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ , A ⊢ B
      ----------
    → Γ ⊢ B

  -- products

  `⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ B
      -----------
    → Γ ⊢ A `× B

  `proj₁ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      -----------
    → Γ ⊢ A

  `proj₂ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      -----------
    → Γ ⊢ B

  -- alternative formulation of products

  case× : ∀ {Γ A B C}
    → Γ ⊢ A `× B
    → Γ , A , B ⊢ C
      --------------
    → Γ ⊢ C

  `inj₁ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ A `⊎ B

  `inj₂ : ∀ {Γ A B}
    → Γ ⊢ B
    → Γ ⊢ A `⊎ B

  case⊎ : ∀ {Γ A B C}
    → Γ ⊢ A `⊎ B
    → Γ , A ⊢ C
    → Γ , B ⊢ C
    → Γ ⊢ C

  `tt : ∀ {Γ}
    → Γ ⊢ `⊤

  case⊤ : ∀ {Γ A}
    → Γ ⊢ `⊤
    → Γ ⊢ A
    → Γ ⊢ A

  case⊥ : ∀ {Γ A}
    → Γ ⊢ `⊥
    → Γ ⊢ A

  `[] : ∀ {Γ A}
    → Γ ⊢ `List A

  _`∷_ : ∀ {Γ A}
    → Γ ⊢ A
    → Γ ⊢ `List A
    → Γ ⊢ `List A

  caseL : ∀ {Γ A B}
    → Γ ⊢ `List A
    → Γ ⊢ B
    → Γ , A , `List A ⊢ B
    → Γ ⊢ B

```

### Abbreviating de Bruijn indices

```agda
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
    --------------------------------
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ}  =  ` count (toWitness n∈Γ)
```

## Renaming

```agda
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
rename ρ (μ N)          =  μ (rename (ext ρ) N)
rename ρ (con n)        =  con n
rename ρ (M `* N)       =  rename ρ M `* rename ρ N
rename ρ (`let M N)     =  `let (rename ρ M) (rename (ext ρ) N)
rename ρ `⟨ M , N ⟩     =  `⟨ rename ρ M , rename ρ N ⟩
rename ρ (`proj₁ L)     =  `proj₁ (rename ρ L)
rename ρ (`proj₂ L)     =  `proj₂ (rename ρ L)
rename ρ (case× L M)    =  case× (rename ρ L) (rename (ext (ext ρ)) M)
rename ρ (`inj₁ M)      =  `inj₁ (rename ρ M)
rename ρ (`inj₂ N)      =  `inj₂ (rename ρ N)
rename ρ (case⊎ L M N)  =  case⊎ (rename ρ L) (rename (ext ρ) M) (rename (ext ρ) N)
rename ρ `tt            =  `tt
rename ρ (case⊤ L M)    =  case⊤ (rename ρ L) (rename ρ M)
rename ρ (case⊥ L)      =  case⊥ (rename ρ L)
rename ρ `[]            =  `[]
rename ρ (L `∷ M)       =  rename ρ L `∷ rename ρ M
rename ρ (caseL L M N)  =  caseL (rename ρ L) (rename ρ M) (rename (ext (ext ρ)) N)
```

## Simultaneous Substitution

```agda
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
subst σ (μ N)          =  μ (subst (exts σ) N)
subst σ (con n)        =  con n
subst σ (M `* N)       =  subst σ M `* subst σ N
subst σ (`let M N)     =  `let (subst σ M) (subst (exts σ) N)
subst σ `⟨ M , N ⟩     =  `⟨ subst σ M , subst σ N ⟩
subst σ (`proj₁ L)     =  `proj₁ (subst σ L)
subst σ (`proj₂ L)     =  `proj₂ (subst σ L)
subst σ (case× L M)    =  case× (subst σ L) (subst (exts (exts σ)) M)
subst σ (`inj₁ M)      =  `inj₁ (subst σ M)
subst σ (`inj₂ N)      =  `inj₂ (subst σ N)
subst σ (case⊎ L M N)  =  case⊎ (subst σ L) (subst (exts σ) M) (subst (exts σ) N)
subst σ `tt            =  `tt
subst σ (case⊤ L M)    =  case⊤ (subst σ L) (subst σ M)
subst σ (case⊥ L)      =  case⊥ (subst σ L)
subst σ `[]            =  `[]
subst σ (L `∷ M)       =  subst σ L `∷ subst σ M
subst σ (caseL L M N)  =  caseL (subst σ L) (subst σ M) (subst (exts (exts σ)) N)
```

## Single and double substitution

```agda
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
  module DoubleSubst where
  σ : ∀ {C} → Γ , A , B ∋ C → Γ ⊢ C
  σ Z          =  W
  σ (S Z)      =  V
  σ (S (S x))  =  ` x
```

## Values

```agda
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  -- functions

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  -- naturals

  V-zero : ∀ {Γ}
      -----------------
    → Value (`zero {Γ})

  V-suc_ : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)

  -- primitives

  V-con : ∀ {Γ n}
      -----------------
    → Value (con {Γ} n)

  -- products

  V-⟨_,_⟩ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------
    → Value `⟨ V , W ⟩

  V-inj₁ : ∀ {Γ A B} {V : Γ ⊢ A}
    → Value V
    → Value (`inj₁ {B = B} V)

  V-inj₂ : ∀ {Γ A B} {V : Γ ⊢ B}
    → Value V
    → Value (`inj₂ {A = A} V)

  V-tt : ∀ {Γ}
    → Value (`tt {Γ})

  V-[] : ∀ {Γ A}
    → Value (`[] {Γ} {A})

  V-∷ : ∀ {Γ A} {V : Γ ⊢ A} {W : Γ ⊢ `List A}
    → Value V
    → Value W
    → Value (V `∷ W)
```

Implicit arguments need to be supplied when they are
not fixed by the given arguments.

## Reduction

```agda
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  -- functions

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
    → Value V
      --------------------
    → (ƛ N) · V —→ N [ V ]

  -- naturals

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]

  -- fixpoint

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
      ----------------
    → μ N —→ N [ μ N ]

  -- primitive numbers

  ξ-*₁ : ∀ {Γ} {L L′ M : Γ ⊢ Nat}
    → L —→ L′
      -----------------
    → L `* M —→ L′ `* M

  ξ-*₂ : ∀ {Γ} {V M M′ : Γ ⊢ Nat}
    → Value V
    → M —→ M′
      -----------------
    → V `* M —→ V `* M′

  δ-* : ∀ {Γ c d}
      ---------------------------------
    → con {Γ} c `* con d —→ con (c * d)

  -- let

  ξ-let : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ , A ⊢ B}
    → M —→ M′
      ---------------------
    → `let M N —→ `let M′ N

  β-let : ∀ {Γ A B} {V : Γ ⊢ A} {N : Γ , A ⊢ B}
    → Value V
      -------------------
    → `let V N —→ N [ V ]

  -- products

  ξ-⟨,⟩₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ ⊢ B}
    → M —→ M′
      -------------------------
    → `⟨ M , N ⟩ —→ `⟨ M′ , N ⟩

  ξ-⟨,⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {N N′ : Γ ⊢ B}
    → Value V
    → N —→ N′
      -------------------------
    → `⟨ V , N ⟩ —→ `⟨ V , N′ ⟩

  ξ-proj₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
    → L —→ L′
      ---------------------
    → `proj₁ L —→ `proj₁ L′

  ξ-proj₂ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
    → L —→ L′
      ---------------------
    → `proj₂ L —→ `proj₂ L′

  β-proj₁ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------------
    → `proj₁ `⟨ V , W ⟩ —→ V

  β-proj₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------------
    → `proj₂ `⟨ V , W ⟩ —→ W

  -- alternative formulation of products

  ξ-case× : ∀ {Γ A B C} {L L′ : Γ ⊢ A `× B} {M : Γ , A , B ⊢ C}
    → L —→ L′
      -----------------------
    → case× L M —→ case× L′ M

  β-case× : ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {M : Γ , A , B ⊢ C}
    → Value V
    → Value W
      ----------------------------------
    → case× `⟨ V , W ⟩ M —→ M [ V ][ W ]

  ξ-inj₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A}
    → M —→ M′
    → `inj₁ {B = B} M —→ `inj₁ {B = B} M′

  ξ-inj₂ : ∀ {Γ A B} {N N′ : Γ ⊢ B}
    → N —→ N′
    → `inj₂ {A = A} N —→ `inj₂ {A = A} N′

  ξ-case⊎ : ∀ {Γ A B C} {L L′ : Γ ⊢ A `⊎ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → L —→ L′
    → case⊎ L M N —→ case⊎ L′ M N

  β-inj₁ : ∀ {Γ A B C} {V : Γ ⊢ A} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → Value V
    → case⊎ (`inj₁ V) M N —→ M [ V ]

  β-inj₂ : ∀ {Γ A B C} {V : Γ ⊢ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → Value V
    → case⊎ (`inj₂ V) M N —→ N [ V ]

  ξ-case⊤ : ∀ {Γ A} {L L′ : Γ ⊢ `⊤} {M : Γ ⊢ A}
    → L —→ L′
    → case⊤ L M —→ case⊤ L′ M

  β-case⊤ : ∀ {Γ A} {M : Γ ⊢ A}
    → case⊤ `tt M —→ M

  ξ-case⊥ : ∀ {Γ A} {L L′ : Γ ⊢ `⊥}
    → L —→ L′
    → case⊥ {A = A} L —→ case⊥ {A = A} L′

  ξ-∷₁ : ∀ {Γ A} {M M′ : Γ ⊢ A} {N : Γ ⊢ `List A}
    → M —→ M′
    → M `∷ N —→ M′ `∷ N

  ξ-∷₂ : ∀ {Γ A} {V : Γ ⊢ A} {N N′ : Γ ⊢ `List A}
    → Value V
    → N —→ N′
    → V `∷ N —→ V `∷ N′

  ξ-caseL : ∀ {Γ A B} {L L′ : Γ ⊢ `List A} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
    → L —→ L′
    → caseL L M N —→ caseL L′ M N

  β-[] : ∀ {Γ A B} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
    → caseL `[] M N —→ M

  β-∷ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ `List A} {M : Γ ⊢ B} {N : Γ , A , `List A ⊢ B}
    → Value V
    → Value W
    → caseL (V `∷ W) M N —→ N [ V ][ W ]

```

## Reflexive and transitive closure

```agda
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M —↠ M

  _—→⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```


## Values do not reduce

```agda
V¬—→ : ∀ {Γ A} {M N : Γ ⊢ A}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ V-ƛ          ()
V¬—→ V-zero       ()
V¬—→ (V-suc VM)   (ξ-suc M—→M′)     =  V¬—→ VM M—→M′
V¬—→ V-con        ()
V¬—→ V-⟨ VM , _ ⟩ (ξ-⟨,⟩₁ M—→M′)    =  V¬—→ VM M—→M′
V¬—→ V-⟨ _ , VN ⟩ (ξ-⟨,⟩₂ _ N—→N′)  =  V¬—→ VN N—→N′
V¬—→ (V-inj₁ VM)  (ξ-inj₁ M—→M′)    =  V¬—→ VM M—→M′
V¬—→ (V-inj₂ VN)  (ξ-inj₂ N—→N′)    =  V¬—→ VN N—→N′
V¬—→ V-[]         ()
V¬—→ (V-∷ VL VM)  (ξ-∷₁ L—→L′)      =  V¬—→ VL L—→L′
V¬—→ (V-∷ VL VM)  (ξ-∷₂ _ M—→M′)    =  V¬—→ VM M—→M′
```


## Progress

```agda
data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {A}
  → (M : ∅ ⊢ A)
    -----------
  → Progress M
progress (` ())
progress (ƛ N)                              =  done V-ƛ
progress (L · M) with progress L
...    | step L—→L′                         =  step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M
...        | step M—→M′                     =  step (ξ-·₂ V-ƛ M—→M′)
...        | done VM                        =  step (β-ƛ VM)
progress (`zero)                            =  done V-zero
progress (`suc M) with progress M
...    | step M—→M′                         =  step (ξ-suc M—→M′)
...    | done VM                            =  done (V-suc VM)
progress (case L M N) with progress L
...    | step L—→L′                         =  step (ξ-case L—→L′)
...    | done V-zero                        =  step β-zero
...    | done (V-suc VL)                    =  step (β-suc VL)
progress (μ N)                              =  step β-μ
progress (con n)                            =  done V-con
progress (L `* M) with progress L
...    | step L—→L′                         =  step (ξ-*₁ L—→L′)
...    | done V-con with progress M
...        | step M—→M′                     =  step (ξ-*₂ V-con M—→M′)
...        | done V-con                     =  step δ-*
progress (`let M N) with progress M
...    | step M—→M′                         =  step (ξ-let M—→M′)
...    | done VM                            =  step (β-let VM)
progress `⟨ M , N ⟩ with progress M
...    | step M—→M′                         =  step (ξ-⟨,⟩₁ M—→M′)
...    | done VM with progress N
...        | step N—→N′                     =  step (ξ-⟨,⟩₂ VM N—→N′)
...        | done VN                        =  done (V-⟨ VM , VN ⟩)
progress (`proj₁ L) with progress L
...    | step L—→L′                         =  step (ξ-proj₁ L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₁ VM VN)
progress (`proj₂ L) with progress L
...    | step L—→L′                         =  step (ξ-proj₂ L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₂ VM VN)
progress (case× L M) with progress L
...    | step L—→L′                         =  step (ξ-case× L—→L′)
...    | done (V-⟨ VM , VN ⟩)               =  step (β-case× VM VN)
progress (`inj₁ M) with progress M
...    | step M—→M′                         =  step (ξ-inj₁ M—→M′)
...    | done VM                            =  done (V-inj₁ VM)
progress (`inj₂ N) with progress N
...    | step N—→N′                         =  step (ξ-inj₂ N—→N′)
...    | done VN                            =  done (V-inj₂ VN)
progress (case⊎ L M N) with progress L
...    | step L—→L′                         =  step (ξ-case⊎ L—→L′)
...    | done (V-inj₁ VL)                   =  step (β-inj₁ VL)
...    | done (V-inj₂ VL)                   =  step (β-inj₂ VL)
progress `tt                                =  done V-tt
progress (case⊤ L M) with progress L
...    | step L—→L′                         =  step (ξ-case⊤ L—→L′)
...    | done V-tt                          =  step β-case⊤
progress (case⊥ L) with progress L
...    | step L—→L′                         =  step (ξ-case⊥ L—→L′)
...    | done ()
progress `[]                                =  done V-[]
progress (L `∷ M) with progress L
...    | step L—→L′                         =  step (ξ-∷₁ L—→L′)
...    | done VL with progress M
...        | step M—→M′                     =  step (ξ-∷₂ VL M—→M′)
...        | done VM                        =  done (V-∷ VL VM)
progress (caseL L M N) with progress L
...    | step L—→L′                         =  step (ξ-caseL L—→L′)
...    | done V-[]                          =  step β-[]
...    | done (V-∷ VL₁ VL₂)                 =  step (β-∷ VL₁ VL₂)
```


## Evaluation

```agda
record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N

data Steps {A} : ∅ ⊢ A → Set where

  steps : {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
```


## Examples

```agda
cube : ∅ ⊢ Nat ⇒ Nat
cube = ƛ (# 0 `* # 0 `* # 0)

_ : cube · con 2 —↠ con 8
_ =
  begin
    cube · con 2
  —→⟨ β-ƛ V-con ⟩
    con 2 `* con 2 `* con 2
  —→⟨ ξ-*₁ δ-* ⟩
    con 4 `* con 2
  —→⟨ δ-* ⟩
    con 8
  ∎

exp10 : ∅ ⊢ Nat ⇒ Nat
exp10 = ƛ (`let (# 0 `* # 0)
            (`let (# 0 `* # 0)
              (`let (# 0 `* # 2)
                (# 0 `* # 0))))

_ : exp10 · con 2 —↠ con 1024
_ =
  begin
    exp10 · con 2
  —→⟨ β-ƛ V-con ⟩
    `let (con 2 `* con 2) (`let (# 0 `* # 0) (`let (# 0 `* con 2) (# 0 `* # 0)))
  —→⟨ ξ-let δ-* ⟩
    `let (con 4) (`let (# 0 `* # 0) (`let (# 0 `* con 2) (# 0 `* # 0)))
  —→⟨ β-let V-con ⟩
    `let (con 4 `* con 4) (`let (# 0 `* con 2) (# 0 `* # 0))
  —→⟨ ξ-let δ-* ⟩
    `let (con 16) (`let (# 0 `* con 2) (# 0 `* # 0))
  —→⟨ β-let V-con ⟩
    `let (con 16 `* con 2) (# 0 `* # 0)
  —→⟨ ξ-let δ-* ⟩
    `let (con 32) (# 0 `* # 0)
  —→⟨ β-let V-con ⟩
    con 32 `* con 32
  —→⟨ δ-* ⟩
    con 1024
  ∎

swap× : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
swap× = ƛ `⟨ `proj₂ (# 0) , `proj₁ (# 0) ⟩

_ : swap× · `⟨ con 42 , `zero ⟩ —↠ `⟨ `zero , con 42 ⟩
_ =
  begin
    swap× · `⟨ con 42 , `zero ⟩
  —→⟨ β-ƛ V-⟨ V-con , V-zero ⟩ ⟩
    `⟨ `proj₂ `⟨ con 42 , `zero ⟩ , `proj₁ `⟨ con 42 , `zero ⟩ ⟩
  —→⟨ ξ-⟨,⟩₁ (β-proj₂ V-con V-zero) ⟩
    `⟨ `zero , `proj₁ `⟨ con 42 , `zero ⟩ ⟩
  —→⟨ ξ-⟨,⟩₂ V-zero (β-proj₁ V-con V-zero) ⟩
    `⟨ `zero , con 42 ⟩
  ∎

swap×-case : ∀ {A B} → ∅ ⊢ A `× B ⇒ B `× A
swap×-case = ƛ case× (# 0) `⟨ # 0 , # 1 ⟩

_ : swap×-case · `⟨ con 42 , `zero ⟩ —↠ `⟨ `zero , con 42 ⟩
_ =
  begin
     swap×-case · `⟨ con 42 , `zero ⟩
   —→⟨ β-ƛ V-⟨ V-con , V-zero ⟩ ⟩
     case× `⟨ con 42 , `zero ⟩ `⟨ # 0 , # 1 ⟩
   —→⟨ β-case× V-con V-zero ⟩
     `⟨ `zero , con 42 ⟩
   ∎

swap⊎ : ∀ {A B} → ∅ ⊢ A `⊎ B ⇒ B `⊎ A
swap⊎ = ƛ case⊎ (# 0) (`inj₂ (# 0)) (`inj₁ (# 0))

to×⊤ : ∀ {A} → ∅ ⊢ A ⇒ A `× `⊤
to×⊤ = ƛ `⟨ # 0 , `tt ⟩

from×⊤-case : ∀ {A} → ∅ ⊢ A `× `⊤ ⇒ A
from×⊤-case = ƛ case× (# 0) (case⊤ (# 0) (# 1))

to⊎⊥ : ∀ {A} → ∅ ⊢ A ⇒ A `⊎ `⊥
to⊎⊥ = ƛ `inj₁ (# 0)

from⊎⊥ : ∀ {A} → ∅ ⊢ A `⊎ `⊥ ⇒ A
from⊎⊥ = ƛ case⊎ (# 0) (# 0) (case⊥ (# 0))

mapL : ∀ {A B} → ∅ ⊢ (A ⇒ B) ⇒ `List A ⇒ `List B
mapL = μ ƛ ƛ caseL (# 0) `[] ((# 3 · # 1) `∷ (# 4 · # 3 · # 0))
```

#### Exercise `More` (recommended and practice)

Formalise the remaining constructs defined in this chapter.
Make your changes in this file.
Evaluate each example, applied to data as needed,
to confirm it returns the expected answer:

  * sums (recommended)
  * unit type (practice)
  * an alternative formulation of unit type (practice)
  * empty type (recommended)
  * lists (practice)

Please delimit any code you add as follows:

    -- begin
    -- end


#### Exercise `double-subst` (stretch)

Show that a double substitution is equivalent to two single
substitutions.
```agda
open import Axiom.Extensionality.Propositional using (ExtensionalityImplicit)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (extensionality)
open Eq.≡-Reasoning using (_≡⟨⟩_; step-≡) renaming (begin_ to ≡begin_; _∎ to _≡∎)

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

exts²-ext² : ∀ {Γ Δ Ε A B C}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → (σ : ∀ {A} → Δ ∋ A → Ε ⊢ A)
  → exts (exts σ {C}) {A} {B} ∘ (ext (ext ρ)) ≡ exts (exts (σ ∘ ρ))
exts²-ext² ρ σ = extensionality λ x →
  ≡begin
    (exts (exts σ) ∘ ext (ext ρ)) x
  ≡⟨ Eq.cong-app (exts-ext (ext ρ) (exts σ)) x ⟩
    exts (exts σ ∘ ext ρ) x
  ≡⟨ Eq.cong-app (cong-app-implicit (cong-app-implicit
       (Eq.cong exts (extensionality-implicit (exts-ext ρ σ)))))
       x ⟩
    exts (exts (σ ∘ ρ)) x
  ≡∎

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
subst-rename {Γ} {Ε = Ε} {A} (μ M) ρ σ
  rewrite subst-rename M (ext ρ) (exts σ)
  = Eq.cong (λ (∙ : ∀ {A} → Γ , _ ∋ A → Ε , _ ⊢ A) →
               μ subst ∙ M)
      (extensionality-implicit (exts-ext ρ σ))
subst-rename (con _) ρ σ = refl
subst-rename (L `* M) ρ σ
  rewrite subst-rename L ρ σ
        | subst-rename M ρ σ
  = refl
subst-rename {Γ} {Ε = Ε} {A} (`let L M) ρ σ
  rewrite subst-rename L ρ σ
        | subst-rename M (ext ρ) (exts σ)
  = Eq.cong (λ (∙ : ∀ {A} → Γ , _ ∋ A → Ε , _ ⊢ A) →
               `let (subst (σ ∘ ρ) L) (subst ∙ M))
      (extensionality-implicit (exts-ext ρ σ))
subst-rename `⟨ L , M ⟩ ρ σ
  rewrite subst-rename L ρ σ
        | subst-rename M ρ σ
  = refl
subst-rename (`proj₁ M) ρ σ rewrite subst-rename M ρ σ = refl
subst-rename (`proj₂ M) ρ σ rewrite subst-rename M ρ σ = refl
subst-rename {Γ} {A = D} (case× {A = A} {B = B} {C = C} L M) ρ σ
  rewrite subst-rename L ρ σ
        | subst-rename M (ext (ext ρ)) (exts (exts σ))
  = Eq.cong₂ case× refl
      (Eq.cong-app (cong-app-implicit
        (Eq.cong subst (extensionality-implicit
          (exts²-ext² ρ σ))))
         M)
subst-rename (`inj₁ M) ρ σ rewrite subst-rename M ρ σ = refl
subst-rename (`inj₂ M) ρ σ rewrite subst-rename M ρ σ = refl
subst-rename (case⊎ L M N) ρ σ
  rewrite subst-rename L ρ σ
        | subst-rename M (ext ρ) (exts σ)
        | subst-rename N (ext ρ) (exts σ)
  = Eq.cong₂ (case⊎ (subst (σ ∘ ρ) L))
      (Eq.cong-app (cong-app-implicit
        (Eq.cong subst (extensionality-implicit
          (exts-ext ρ σ))))
        M)
      (Eq.cong-app (cong-app-implicit
        (Eq.cong subst (extensionality-implicit
          (exts-ext ρ σ))))
        N)
subst-rename `tt ρ σ = refl
subst-rename (case⊤ L M) ρ σ
  rewrite subst-rename L ρ σ
        | subst-rename M ρ σ
  = refl
subst-rename (case⊥ M) ρ σ rewrite subst-rename M ρ σ = refl
subst-rename `[] ρ σ = refl
subst-rename (L `∷ M) ρ σ
  rewrite subst-rename L ρ σ
        | subst-rename M ρ σ
  = refl
subst-rename (caseL L M N) ρ σ
  rewrite subst-rename L ρ σ
        | subst-rename M ρ σ
        | subst-rename N (ext (ext ρ)) (exts (exts σ))
  = Eq.cong (caseL (subst (σ ∘ ρ) L) (subst (σ ∘ ρ) M))
      (Eq.cong-app (cong-app-implicit
        (Eq.cong subst (extensionality-implicit
          (exts²-ext² ρ σ))))
        N)

exts-` : ∀ {Γ A B}
  → exts {Γ} `_ {A} {B} ≡ `_
exts-` = extensionality
  λ{ Z     → refl
   ; (S x) → refl
   }

exts²-` : ∀ {Γ A B C}
  → exts {Γ , A} (exts {Γ} `_) {B} {C} ≡ `_
exts²-` = extensionality
  λ{ Z         → refl
   ; (S Z)     → refl
   ; (S (S x)) → refl
   }

subst-` : ∀ {Γ A} (M : Γ ⊢ A)
  → subst `_ M ≡ M
subst-exts-` : ∀ {Γ A B} (M : Γ , A ⊢ B)
  → subst (exts `_) M ≡ M
subst-exts²-` : ∀ {Γ A B C} (M : Γ , A , B ⊢ C)
  → subst (exts (exts `_)) M ≡ M

subst-` (` x) = refl
subst-` (ƛ M) rewrite subst-exts-` M = refl
subst-` (L · M) rewrite subst-` L | subst-` M = refl
subst-` `zero = refl
subst-` (`suc M) rewrite subst-` M = refl
subst-` (case L M N) rewrite subst-` L | subst-` M | subst-exts-` N = refl
subst-` (μ M) rewrite subst-exts-` M = refl
subst-` (con _) = refl
subst-` (L `* M) rewrite subst-` L | subst-` M = refl
subst-` (`let L M) rewrite subst-` L | subst-exts-` M = refl
subst-` `⟨ L , M ⟩ rewrite subst-` L | subst-` M = refl
subst-` (`proj₁ M) rewrite subst-` M = refl
subst-` (`proj₂ M) rewrite subst-` M = refl
subst-` (case× L M) rewrite subst-` L | subst-exts²-` M = refl
subst-` (`inj₁ M) rewrite subst-` M = refl
subst-` (`inj₂ M) rewrite subst-` M = refl
subst-` (case⊎ L M N)
  rewrite subst-` L
        | subst-exts-` M
        | subst-exts-` N
  = refl
subst-` `tt = refl
subst-` (case⊤ L M) rewrite subst-` L | subst-` M = refl
subst-` (case⊥ M) rewrite subst-` M = refl
subst-` `[] = refl
subst-` (L `∷ M) rewrite subst-` L | subst-` M = refl
subst-` (caseL L M N)
  rewrite subst-` L
        | subst-` M
        | subst-exts²-` N
  = refl

subst-exts-` M =
  ≡begin
    subst (exts `_) M
  ≡⟨ Eq.cong-app (cong-app-implicit
       (Eq.cong subst (extensionality-implicit exts-`)))
       M ⟩
    subst `_ M
  ≡⟨ subst-` M ⟩
    M
  ≡∎

subst-exts²-` {Γ} {A = A} M =
  ≡begin
    subst (exts (exts `_)) M
  ≡⟨ Eq.cong-app (cong-app-implicit
       (Eq.cong subst (extensionality-implicit exts²-`)))
       M ⟩
    subst `_ M
  ≡⟨ subst-` M ⟩
    M
  ≡∎

ext² : ∀ {Γ Δ Ε A} (ρ₁ : ∀ {A} → Γ ∋ A → Δ ∋ A) (ρ₂ : ∀ {A} → Δ ∋ A → Ε ∋ A)
  → (λ {B} x → ext ρ₂ {A} {B} (ext ρ₁ x)) ≡ (λ {B} → ext (ρ₂ ∘ ρ₁) {A} {B})
ext² ρ₁ ρ₂ = extensionality-implicit (extensionality
 λ{ Z     → refl
  ; (S x) → refl
  })

ext⁴ : ∀ {Γ Δ Ε A C} (ρ₁ : ∀ {A} → Γ ∋ A → Δ ∋ A) (ρ₂ : ∀ {A} → Δ ∋ A → Ε ∋ A)
  → (λ {B : Type} x → ext (ext ρ₂ {C}) {A} {B} (ext (ext ρ₁) x)) ≡ (λ {B : Type} → ext (ext (ρ₂ ∘ ρ₁)) {A} {B})
ext⁴ ρ₁ ρ₂ = extensionality-implicit (extensionality
 λ{ Z     → refl
  ; (S x) → Eq.cong S_ (Eq.cong-app (cong-app-implicit (ext² ρ₁ ρ₂)) x)
  })

rename² : ∀ {Γ Δ Ε A} (ρ₁ : ∀ {A} → Γ ∋ A → Δ ∋ A) (ρ₂ : ∀ {A} → Δ ∋ A → Ε ∋ A) (M : Γ ⊢ A)
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
rename² {Γ} {Ε = Ε} ρ₁ ρ₂ (μ M) rewrite rename² (ext ρ₁) (ext ρ₂) M
  = Eq.cong
      (λ (∙ : ∀ {A} → Γ , _ ∋ A → Ε , _ ∋ A) → μ rename ∙ M)
      (ext² ρ₁ ρ₂)
rename² ρ₁ ρ₂ (con _) = refl
rename² ρ₁ ρ₂ (L `* M) rewrite rename² ρ₁ ρ₂ L | rename² ρ₁ ρ₂ M = refl
rename² {Γ} {Ε = Ε} ρ₁ ρ₂ (`let L M)
  rewrite rename² ρ₁ ρ₂ L
        | rename² (ext ρ₁) (ext ρ₂) M
  = Eq.cong
      (λ (∙ : ∀ {A} → Γ , _ ∋ A → Ε , _ ∋ A) →
         `let (rename (ρ₂ ∘ ρ₁) L) (rename ∙ M))
      (ext² ρ₁ ρ₂)
rename² ρ₁ ρ₂ `⟨ L , M ⟩ rewrite rename² ρ₁ ρ₂ L | rename² ρ₁ ρ₂ M = refl
rename² ρ₁ ρ₂ (`proj₁ M) rewrite rename² ρ₁ ρ₂ M = refl
rename² ρ₁ ρ₂ (`proj₂ M) rewrite rename² ρ₁ ρ₂ M = refl
rename² {Γ} {Ε = Ε} ρ₁ ρ₂ (case× L M)
  rewrite rename² ρ₁ ρ₂ L
  rewrite rename² (ext (ext ρ₁)) (ext (ext ρ₂)) M
  = Eq.cong
      (λ (∙ : ∀ {A} → Γ , _ , _ ∋ A → Ε , _ , _ ∋ A) →
         case× (rename (ρ₂ ∘ ρ₁) L) (rename ∙ M))
      (ext⁴ ρ₁ ρ₂)
rename² ρ₁ ρ₂ (`inj₁ M) rewrite rename² ρ₁ ρ₂ M = refl
rename² ρ₁ ρ₂ (`inj₂ M) rewrite rename² ρ₁ ρ₂ M = refl
rename² {Γ} {Ε = Ε} ρ₁ ρ₂ (case⊎ L M N)
  rewrite rename² ρ₁ ρ₂ L
        | rename² (ext ρ₁) (ext ρ₂) M
        | rename² (ext ρ₁) (ext ρ₂) N
  = Eq.cong₂
      (λ (∙₁ : ∀ {A} → Γ , _ ∋ A → Ε , _ ∋ A)
         (∙₂ : ∀ {A} → Γ , _ ∋ A → Ε , _ ∋ A) →
         case⊎ (rename (ρ₂ ∘ ρ₁) L) (rename ∙₁ M) (rename ∙₂ N))
      (ext² ρ₁ ρ₂)
      (ext² ρ₁ ρ₂)
rename² ρ₁ ρ₂ `tt = refl
rename² ρ₁ ρ₂ (case⊤ L M) rewrite rename² ρ₁ ρ₂ L | rename² ρ₁ ρ₂ M = refl
rename² ρ₁ ρ₂ (case⊥ M) rewrite rename² ρ₁ ρ₂ M = refl
rename² ρ₁ ρ₂ `[] = refl
rename² ρ₁ ρ₂ (L `∷ M) rewrite rename² ρ₁ ρ₂ L | rename² ρ₁ ρ₂ M = refl
rename² {Γ} {Ε = Ε} ρ₁ ρ₂ (caseL L M N)
  rewrite rename² ρ₁ ρ₂ L
        | rename² ρ₁ ρ₂ M
        | rename² (ext (ext ρ₁)) (ext (ext ρ₂)) N
  = Eq.cong
      (λ (∙ : ∀ {A} → Γ , _ , _ ∋ A → Ε , _ , _ ∋ A) →
        caseL (rename (ρ₂ ∘ ρ₁) L) (rename (ρ₂ ∘ ρ₁) M) (rename ∙ N))
      (ext⁴ ρ₁ ρ₂)

`-ext : ∀ {Γ Δ : Context} {A B : Type} (ρ : ∀ {A : Type} → Γ ∋ A → Δ ∋ A)
  → `_ {A = B} ∘ ext ρ {A} ≡ exts (`_ ∘ ρ)
`-ext ρ = extensionality
  λ{ Z     → refl
   ; (S x) → refl
   }

rename-as-subst : ∀ {Γ Δ A} (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → rename ρ {A} ≡ subst (`_ ∘ ρ)
rename-as-subst ρ = extensionality λ x →
  Eq.trans
    (Eq.sym (subst-` (rename ρ x)))
    (subst-rename x ρ `_)

_⟶_ : ∀ {Γ Δ Ε}
  → (∀ {A : Type} → Γ ∋ A → Δ ⊢ A)
  → (∀ {A : Type} → Δ ∋ A → Ε ⊢ A)
  → (∀ {A : Type} → Γ ∋ A → Ε ⊢ A)
σ₁ ⟶ σ₂ = subst σ₂ ∘ σ₁

rename-exts : ∀ {Γ Δ Ε A B} (σ : ∀ {A} → Γ ∋ A → Δ ⊢ A) (ρ : ∀ {A} → Δ ∋ A → Ε ∋ A)
  → rename (ext ρ {B}) {A} ∘ exts σ ≡ exts (rename ρ ∘ σ)
rename-exts σ ρ = extensionality
  λ{ Z → refl
   ; (S x) →
     ≡begin
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
     ≡∎
   }

rename-exts² : ∀ {Γ Δ Ε A B C} (σ : ∀ {A} → Γ ∋ A → Δ ⊢ A) (ρ : ∀ {A} → Δ ∋ A → Ε ∋ A)
  → rename (ext (ext ρ {C}) {B}) {A} ∘ exts (exts σ) ≡ exts (exts (rename ρ ∘ σ))
rename-exts² σ ρ =
  ≡begin
    rename (ext (ext ρ)) ∘ exts (exts σ)
  ≡⟨ rename-exts (exts σ) (ext ρ) ⟩
    exts (rename (ext ρ) ∘ exts σ)
  ≡⟨ cong-app-implicit (cong-app-implicit
       (Eq.cong exts (extensionality-implicit
         (rename-exts σ ρ)))) ⟩
    exts (exts (rename ρ ∘ σ))
  ≡∎

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
rename-subst σ ρ (μ M)
  rewrite rename-subst (exts σ) (ext ρ) M
  = Eq.cong μ_
      (Eq.cong-app (cong-app-implicit
        (Eq.cong subst (extensionality-implicit
          (rename-exts σ ρ))))
         M)
rename-subst σ ρ (con _) = refl
rename-subst σ ρ (L `* M)
  rewrite rename-subst σ ρ L
        | rename-subst σ ρ M
  = refl
rename-subst σ ρ (`let L M)
  rewrite rename-subst σ ρ L
        | rename-subst (exts σ) (ext ρ) M
  = Eq.cong (`let (subst (rename ρ ∘ σ) L))
      (Eq.cong-app (cong-app-implicit
        (Eq.cong subst (extensionality-implicit
          (rename-exts σ ρ))))
        M)
rename-subst σ ρ `⟨ L , M ⟩
  rewrite rename-subst σ ρ L
        | rename-subst σ ρ M
  = refl
rename-subst σ ρ (`proj₁ M) rewrite rename-subst σ ρ M = refl
rename-subst σ ρ (`proj₂ M) rewrite rename-subst σ ρ M = refl
rename-subst σ ρ (case× L M)
  rewrite rename-subst σ ρ L
        | rename-subst (exts (exts σ)) (ext (ext ρ)) M
  = Eq.cong (case× (subst (rename ρ ∘ σ) L))
      (Eq.cong-app (cong-app-implicit
        (Eq.cong subst (extensionality-implicit
          (rename-exts² σ ρ))))
        M)
rename-subst σ ρ (`inj₁ M) rewrite rename-subst σ ρ M = refl
rename-subst σ ρ (`inj₂ M) rewrite rename-subst σ ρ M = refl
rename-subst σ ρ (case⊎ L M N)
  rewrite rename-subst σ ρ L
        | rename-subst (exts σ) (ext ρ) M
        | rename-subst (exts σ) (ext ρ) N
  = Eq.cong₂ (case⊎ (subst (rename ρ ∘ σ) L))
      (Eq.cong-app (cong-app-implicit
        (Eq.cong subst (extensionality-implicit
          (rename-exts σ ρ))))
        M)
      ((Eq.cong-app (cong-app-implicit
        (Eq.cong subst (extensionality-implicit
          (rename-exts σ ρ))))
        N))
rename-subst σ ρ `tt = refl
rename-subst σ ρ (case⊤ L M)
  rewrite rename-subst σ ρ L
        | rename-subst σ ρ M
  = refl
rename-subst σ ρ (case⊥ M) rewrite rename-subst σ ρ M = refl
rename-subst σ ρ `[] = refl
rename-subst σ ρ (M `∷ N)
  rewrite rename-subst σ ρ M
        | rename-subst σ ρ N
  = refl
rename-subst σ ρ (caseL L M N)
  rewrite rename-subst σ ρ L
        | rename-subst σ ρ M
        | rename-subst (exts (exts σ)) (ext (ext ρ)) N
  = Eq.cong (caseL (subst (rename ρ ∘ σ) L) (subst (rename ρ ∘ σ) M))
      (Eq.cong-app (cong-app-implicit
        (Eq.cong subst (extensionality-implicit
          (rename-exts² σ ρ))))
        N)

subst-exts-∘-exts : ∀ {Γ Δ Ε A B} (σ₁ : ∀ {A : Type} → Γ ∋ A → Δ ⊢ A) (σ₂ : ∀ {A} → Δ ∋ A → Ε ⊢ A)
  → subst (exts σ₂) ∘ exts σ₁ ≡ exts (subst σ₂ ∘ σ₁) {A} {B}
subst-exts-∘-exts {Δ = Δ} σ₁ σ₂ = extensionality λ where
  Z     → refl
  (S x) →
    ≡begin
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
    ≡∎

subst-exts²-∘-exts² : ∀ {Γ Δ Ε A B C} (σ₁ : ∀ {A} → Γ ∋ A → Δ ⊢ A) (σ₂ : ∀ {A} → Δ ∋ A → Ε ⊢ A)
  → subst (exts (exts σ₂ {A})) ∘ exts (exts σ₁) ≡ exts (exts (subst σ₂ ∘ σ₁)) {B} {C}
subst-exts²-∘-exts² {Δ = Δ} σ₁ σ₂ = extensionality λ where
  Z → refl
  (S x) →
    ≡begin
      subst (exts (exts σ₂)) (exts (exts σ₁) (S x))
    ≡⟨⟩
      subst (exts (exts σ₂)) (rename S_ (exts σ₁ x))
    ≡⟨ subst-rename (exts σ₁ x) S_ (exts (exts σ₂)) ⟩
      subst (exts (exts σ₂) ∘ S_) (exts σ₁ x)
    ≡⟨⟩
      subst (rename S_ ∘ exts σ₂) (exts σ₁ x)
    ≡⟨ Eq.sym (rename-subst (exts σ₂) S_ (exts σ₁ x)) ⟩
      rename S_ (subst (exts σ₂) (exts σ₁ x))
    ≡⟨ Eq.cong (rename S_) (Eq.cong-app (subst-exts-∘-exts σ₁ σ₂) x) ⟩
      rename S_ (exts (subst σ₂ ∘ σ₁) x)
    ≡⟨⟩
      exts (exts (subst σ₂ ∘ σ₁)) (S x)
    ≡∎

subst² : ∀ {Γ Δ Ε A} (σ₁ : ∀ {A} → Γ ∋ A → Δ ⊢ A) (σ₂ : ∀ {A} → Δ ∋ A → Ε ⊢ A) (M : Γ ⊢ A)
  → subst σ₂ {A} (subst σ₁ M) ≡ subst (σ₁ ⟶ σ₂) M
subst² σ₁ σ₂ (` x) = refl
subst² σ₁ σ₂ (ƛ M) rewrite subst² (exts σ₁) (exts σ₂) M =
  Eq.cong ƛ_
    (Eq.cong-app (cong-app-implicit (Eq.cong subst
      (extensionality-implicit
        (subst-exts-∘-exts σ₁ σ₂))))
      M)
subst² σ₁ σ₂ (L · M)
  rewrite subst² σ₁ σ₂ L
        | subst² σ₁ σ₂ M
  = refl
subst² σ₁ σ₂ `zero = refl
subst² σ₁ σ₂ (`suc M) rewrite subst² σ₁ σ₂ M = refl
subst² σ₁ σ₂ (case L M N)
  rewrite subst² σ₁ σ₂ L
        | subst² σ₁ σ₂ M
        | subst² (exts σ₁) (exts σ₂) N
  = Eq.cong (case _ _) (Eq.cong-app (cong-app-implicit (Eq.cong subst
      (extensionality-implicit
       (subst-exts-∘-exts σ₁ σ₂))))
      N)
subst² σ₁ σ₂ (μ M) rewrite subst² (exts σ₁) (exts σ₂) M =
  Eq.cong μ_
    (Eq.cong-app (cong-app-implicit (Eq.cong subst
      (extensionality-implicit
        (subst-exts-∘-exts σ₁ σ₂))))
      M)
subst² σ₁ σ₂ (con _) = refl
subst² σ₁ σ₂ (L `* M) rewrite subst² σ₁ σ₂ L | subst² σ₁ σ₂ M = refl
subst² σ₁ σ₂ (`let L M)
  rewrite subst² σ₁ σ₂ L
        | subst² (exts σ₁) (exts σ₂) M
  = Eq.cong (`let _)
      (Eq.cong-app (cong-app-implicit (Eq.cong subst
        (extensionality-implicit
          (subst-exts-∘-exts σ₁ σ₂))))
        M)
subst² σ₁ σ₂ `⟨ L , M ⟩ rewrite subst² σ₁ σ₂ L | subst² σ₁ σ₂ M = refl
subst² σ₁ σ₂ (`proj₁ M) rewrite subst² σ₁ σ₂ M = refl
subst² σ₁ σ₂ (`proj₂ M) rewrite subst² σ₁ σ₂ M = refl
subst² σ₁ σ₂ (case× L M)
  rewrite subst² σ₁ σ₂ L
        | subst² (exts (exts σ₁)) (exts (exts σ₂)) M
  = Eq.cong (case× _) (Eq.cong-app (cong-app-implicit (Eq.cong subst
      (extensionality-implicit
        (subst-exts²-∘-exts² σ₁ σ₂))))
      M)
subst² σ₁ σ₂ (`inj₁ M) rewrite subst² σ₁ σ₂ M = refl
subst² σ₁ σ₂ (`inj₂ M) rewrite subst² σ₁ σ₂ M = refl
subst² σ₁ σ₂ (case⊎ L M N)
  rewrite subst² σ₁ σ₂ L
        | subst² (exts σ₁) (exts σ₂) M
        | subst² (exts σ₁) (exts σ₂) N
  = Eq.cong₂ (case⊎ _)
      (Eq.cong-app (cong-app-implicit (Eq.cong subst
        (extensionality-implicit
          (subst-exts-∘-exts σ₁ σ₂))))
        M)
      (Eq.cong-app (cong-app-implicit (Eq.cong subst
        (extensionality-implicit
          (subst-exts-∘-exts σ₁ σ₂))))
        N)
subst² σ₁ σ₂ `tt = refl
subst² σ₁ σ₂ (case⊤ L M) rewrite subst² σ₁ σ₂ L | subst² σ₁ σ₂ M = refl
subst² σ₁ σ₂ (case⊥ M) rewrite subst² σ₁ σ₂ M = refl
subst² σ₁ σ₂ `[] = refl
subst² σ₁ σ₂ (L `∷ M) rewrite subst² σ₁ σ₂ L | subst² σ₁ σ₂ M = refl
subst² σ₁ σ₂ (caseL L M N)
  rewrite subst² σ₁ σ₂ L
        | subst² σ₁ σ₂ M
        | subst² (exts (exts σ₁)) (exts (exts σ₂)) N
  = Eq.cong (caseL _ _) (Eq.cong-app (cong-app-implicit (Eq.cong subst
      (extensionality-implicit
        (subst-exts²-∘-exts² σ₁ σ₂))))
      N)

substZero-renameS : ∀ {Γ A B} (M : Γ ⊢ A) (N : Γ ⊢ B)
  → subst (substZero N) (rename S_ M) ≡ M
substZero-renameS M N
  rewrite subst-rename M S_ (substZero N)
  = subst-` M

subst-exts-renameS² : ∀ {Γ A B C} (M : Γ ⊢ A) (N : Γ ⊢ B)
  → subst (exts (substZero N) {C}) (rename S_ (rename S_ M)) ≡ rename S_ M
subst-exts-renameS² {C = C} M N
  rewrite subst-rename (rename S_ M) (S_ {A = C}) (exts (substZero N))
        | subst-rename M S_ (rename (S_ {A = C}) ∘ substZero N)
        | Eq.sym (subst-rename M (S_ {A = C}) `_)
        | subst-` (rename (S_ {A = C}) M)
  = refl

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v w z}
  →   x     ≡   y
  →     u   ≡     v
  →       w ≡       z
  → f x u w ≡ f y v z
cong₃ f refl refl refl = refl

module _ {Γ A B} (V : Γ ⊢ A) (W : Γ ⊢ B) where
  double-subst′ : ∀ {C} → (N : Γ , A , B ⊢ C)
    → subst (subst (substZero V) ∘ substZero (rename S_ W)) N ≡ (N [ rename S_ W ]) [ V ]
  double-subst′ (` Z)
    rewrite subst-rename W S_ (substZero V)
          | subst-` W = refl
  double-subst′ (` (S Z)) = refl
  double-subst′ (` (S (S x))) = refl
  double-subst′ {C} (ƛ M)
    rewrite subst² (exts (substZero (rename S_ W))) (exts (substZero V)) M
    = Eq.cong
        (λ (∙ : ∀ {C} → _ ∋ C → _ ⊢ C) → ƛ subst ∙ M)
        (extensionality-implicit
          (Eq.sym (subst-exts-∘-exts (substZero (rename S_ W)) (substZero V))))
  double-subst′ (L · M) rewrite double-subst′ L | double-subst′ M = refl
  double-subst′ `zero = refl
  double-subst′ (`suc M) rewrite double-subst′ M = refl
  double-subst′ {C = C} (case L M N)
    rewrite double-subst′ L
          | double-subst′ M
          | subst² (exts (substZero (rename S_ W))) (exts (substZero V)) N
    = Eq.cong (case _ _) (Eq.cong-app (cong-app-implicit (Eq.cong subst
        (extensionality-implicit
          (Eq.sym
            (subst-exts-∘-exts (substZero (rename S_ W)) (substZero V))))))
        N)
  double-subst′ (μ M)
    rewrite subst² (exts (substZero (rename S_ W))) (exts (substZero V)) M
    = Eq.cong μ_ (Eq.cong-app (cong-app-implicit (Eq.cong subst
        (extensionality-implicit
          (Eq.sym
            (subst-exts-∘-exts (substZero (rename S_ W)) (substZero V))))))
        M)
  double-subst′ (con _) = refl
  double-subst′ (L `* M) =
    Eq.cong₂ _`*_ (double-subst′ L) (double-subst′ M)
  double-subst′ (`let L M)
    rewrite double-subst′ L
          | subst² (exts (substZero (rename S_ W))) (exts (substZero V)) M
    = Eq.cong (`let _) (Eq.cong-app (cong-app-implicit (Eq.cong subst
        (extensionality-implicit
          (Eq.sym
            (subst-exts-∘-exts (substZero (rename S_ W)) (substZero V))))))
        M)
  double-subst′ (`⟨ L , M ⟩) rewrite double-subst′ L | double-subst′ M = refl
  double-subst′ (`proj₁ M) rewrite double-subst′ M = refl
  double-subst′ (`proj₂ M) rewrite double-subst′ M = refl
  double-subst′ (case× L M)
    rewrite double-subst′ L
          | subst² (exts (exts (substZero (rename S_ W)))) (exts (exts (substZero V))) M
    = Eq.cong (case× _) (Eq.cong-app (cong-app-implicit (Eq.cong subst
        (extensionality-implicit
          (Eq.sym
            (subst-exts²-∘-exts² (substZero (rename S_ W)) (substZero V))))))
        M)
  double-subst′ (`inj₁ M) rewrite double-subst′ M = refl
  double-subst′ (`inj₂ M) rewrite double-subst′ M = refl
  double-subst′ (case⊎ L M N)
    rewrite double-subst′ L
          | subst² (exts (substZero (rename S_ W))) (exts (substZero V)) M
          | subst² (exts (substZero (rename S_ W))) (exts (substZero V)) N
    = Eq.cong₂ (case⊎ _)
        (Eq.cong-app (cong-app-implicit (Eq.cong subst
          (extensionality-implicit
            (Eq.sym
              (subst-exts-∘-exts (substZero (rename S_ W)) (substZero V))))))
          M)
        (Eq.cong-app (cong-app-implicit (Eq.cong subst
          (extensionality-implicit
            (Eq.sym
              (subst-exts-∘-exts (substZero (rename S_ W)) (substZero V))))))
          N)
  double-subst′ `tt = refl
  double-subst′ (case⊤ L M) rewrite double-subst′ L | double-subst′ M = refl
  double-subst′ (case⊥ M) rewrite double-subst′ M = refl
  double-subst′ `[] = refl
  double-subst′ (L `∷ M) rewrite double-subst′ L | double-subst′ M = refl
  double-subst′ (caseL L M N)
    rewrite double-subst′ L
          | double-subst′ M
          | subst² (exts (exts (substZero (rename S_ W)))) (exts (exts (substZero V))) N
    = Eq.cong (caseL _ _) (Eq.cong-app (cong-app-implicit (Eq.cong subst
        (extensionality-implicit
          (Eq.sym
            (subst-exts²-∘-exts² (substZero (rename S_ W)) (substZero V))))))
        N)

double-subst :
  ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {N : Γ , A , B ⊢ C} →
    N [ V ][ W ] ≡ (N [ rename S_ W ]) [ V ]
double-subst {V = V} {W} {N}
  rewrite double-subst′ V W N
        | subst² (substZero (rename S_ W)) (substZero V) N
  = Eq.cong-app (cong-app-implicit (Eq.cong subst
      (extensionality-implicit (extensionality λ where
        Z         → Eq.sym (substZero-renameS W V)
        (S Z)     → refl
        (S (S x)) → refl))))
      N
```
Note the arguments need to be swapped and `W` needs to have
its context adjusted via renaming in order for the right-hand
side to be well typed.

## Test examples

We repeat the [test examples](/DeBruijn/#examples) from Chapter [DeBruijn](/DeBruijn/),
in order to make sure we have not broken anything in the process of extending our base calculus.
```agda
two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

2+2 : ∀ {Γ} → Γ ⊢ `ℕ
2+2 = plus · two · two

Ch : Type → Type
Ch A  =  (A ⇒ A) ⇒ A ⇒ A

twoᶜ : ∀ {Γ A} → Γ ⊢ Ch A
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

plusᶜ : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

sucᶜ : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ `suc (# 0)

2+2ᶜ : ∀ {Γ} → Γ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
```

## Unicode

This chapter uses the following unicode:

    σ  U+03C3  GREEK SMALL LETTER SIGMA (\Gs or \sigma)
    †  U+2020  DAGGER (\dag)
    ‡  U+2021  DOUBLE DAGGER (\ddag)
