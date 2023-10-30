---
title     : "Bisimulation: Relating reduction systems"
permalink : /Bisimulation/
---

```agda
module plfa.part2.Bisimulation where
```

Some constructs can be defined in terms of other constructs.  In the
previous chapter, we saw how _let_ terms can be rewritten as an
application of an abstraction, and how two alternative formulations of
products — one with projections and one with case — can be formulated
in terms of each other.  In this chapter, we look at how to formalise
such claims.

Given two different systems, with different terms and reduction rules,
we define what it means to claim that one _simulates_ the other.
Let's call our two systems _source_ and _target_.  Let `M`, `N` range
over terms of the source, and `M†`, `N†` range over terms of the
target.  We define a relation

    M ~ M†

between corresponding terms of the two systems. We have a
_simulation_ of the source by the target if every reduction
in the source has a corresponding reduction sequence
in the target:

_Simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —↠ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —↠ --- N†

Sometimes we will have a stronger condition, where each reduction in the source
corresponds to a reduction (rather than a reduction sequence)
in the target:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

This stronger condition is known as _lock-step_ or _on the nose_ simulation.

We are particularly interested in the situation where there is also
a simulation from the target to the source: every reduction in the
target has a corresponding reduction sequence in the source.  This
situation is called a _bisimulation_.

Simulation is established by case analysis over all possible
reductions and all possible terms to which they are related.  For each
reduction step in the source we must show a corresponding reduction
sequence in the target.

For instance, the source might be lambda calculus with _let_
added, and the target the same system with `let` translated out.
The key rule defining our relation will be:

    M ~ M†
    N ~ N†
    --------------------------------
    let x = M in N ~ (ƛ x ⇒ N†) · M†

All the other rules are congruences: variables relate to
themselves, and abstractions and applications relate if their
components relate:

    -----
    x ~ x

    N ~ N†
    ------------------
    ƛ x ⇒ N ~ ƛ x ⇒ N†

    L ~ L†
    M ~ M†
    ---------------
    L · M ~ L† · M†

Covering the other constructs of our language — naturals,
fixpoints, products, and so on — would add little save length.

In this case, our relation can be specified by a function
from source to target:

    (x) †               =  x
    (ƛ x ⇒ N) †         =  ƛ x ⇒ (N †)
    (L · M) †           =  (L †) · (M †)
    (let x = M in N) †  =  (ƛ x ⇒ (N †)) · (M †)

And we have

    M † ≡ N
    -------
    M ~ N

and conversely. But in general we may have a relation without any
corresponding function.

This chapter formalises establishing that `~` as defined
above is a simulation from source to target.  We leave
establishing it in the reverse direction as an exercise.
Another exercise is to show the alternative formulations
of products in
Chapter [More](/More/)
are in bisimulation.


## Imports

We import our source language from
Chapter [More](/More/):
```agda
open import plfa.part2.More
```


## Simulation

The simulation is a straightforward formalisation of the rules
in the introduction:
```agda
infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

data _~_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ~` : ∀ {Γ A} {x : Γ ∋ A}
     ---------
   → ` x ~ ` x

  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
      ----------
    → ƛ N ~ ƛ N†

  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
      ---------------
    → L · M ~ L† · M†

  ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
    → M ~ M†
    → N ~ N†
      ----------------------
    → `let M N ~ (ƛ N†) · M†
```
The language in Chapter [More](/More/) has more constructs, which we could easily add.
However, leaving the simulation small lets us focus on the essence.
It's a handy technical trick that we can have a large source language,
but only bother to include in the simulation the terms of interest.

#### Exercise `_†` (practice)

Formalise the translation from source to target given in the introduction.
Show that `M † ≡ N` implies `M ~ N`, and conversely.

**Hint:** For simplicity, we focus on only a few constructs of the language,
so `_†` should be defined only on relevant terms. One way to do this is
to use a decidable predicate to pick out terms in the domain of `_†`, using
[proof by reflection](/Decidable/#proof-by-reflection).

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Nullary using (Dec; no; yes)
open import Relation.Nullary.Decidable.Core using (fromWitness; toWitness; True)

data in-dom-† : ∀ {Γ A} → Γ ⊢ A → Set where
  in-dom-†-` : ∀ {Γ A}
      (x : A ∋ Γ)
    → in-dom-† (` x)
  in-dom-†-ƛ : ∀ {Γ A B} {M : Γ , B ⊢ A}
    → in-dom-† M
    → in-dom-† (ƛ M)
  in-dom-†-· : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → in-dom-† L
    → in-dom-† M
    → in-dom-† (L · M)
  in-dom-†-`let : ∀ {Γ A B} {L : Γ ⊢ B} {M : Γ , B ⊢ A}
    → in-dom-† L
    → in-dom-† M
    → in-dom-† (`let L M)

in-dom-†? : ∀ {Γ A} (M : Γ ⊢ A) → Dec (in-dom-† M)
in-dom-†? (` x) = yes (in-dom-†-` x)
in-dom-†? (ƛ M)
  with in-dom-†? M
...  | yes M-∈-dom =
       yes (in-dom-†-ƛ M-∈-dom)
...  | no  M-∉-dom =
       no λ{ (in-dom-†-ƛ M-∈-dom) → M-∉-dom M-∈-dom }
in-dom-†? (L · M)
  with in-dom-†? L | in-dom-†? M
...  | yes L-∈-dom | yes M-∈-dom =
       yes (in-dom-†-· L-∈-dom M-∈-dom)
...  | no  L-∉-dom | _           =
       no λ{ (in-dom-†-· L-∈-dom M-∈-dom) → L-∉-dom L-∈-dom }
...  | _           | no  M-∉-dom =
       no λ{ (in-dom-†-· L-∈-dom M-∈-dom) → M-∉-dom M-∈-dom }
in-dom-†? `zero = no λ ()
in-dom-†? (`suc _) = no λ ()
in-dom-†? (case _ _ _) = no λ ()
in-dom-†? (μ _) = no λ ()
in-dom-†? (con _) = no λ ()
in-dom-†? (_ `* _) = no λ ()
in-dom-†? (`let L M)
  with in-dom-†? L | in-dom-†? M
...  | yes L-∈-dom | yes M-∈-dom =
       yes (in-dom-†-`let L-∈-dom M-∈-dom)
...  | no  L-∉-dom | _           =
       no λ{ (in-dom-†-`let L-∈-dom M-∈-dom) → L-∉-dom L-∈-dom }
...  | _           | no  M-∉-dom =
       no λ{ (in-dom-†-`let L-∈-dom M-∈-dom) → M-∉-dom M-∈-dom }
in-dom-†? `⟨ _ , _ ⟩ = no λ ()
in-dom-†? (`proj₁ _) = no λ ()
in-dom-†? (`proj₂ _) = no λ ()
in-dom-†? (case× _ _) = no λ ()
in-dom-†? (`inj₁ _) = no λ ()
in-dom-†? (`inj₂ _) = no λ ()
in-dom-†? (case⊎ _ _ _) = no λ ()
in-dom-†? `tt = no λ ()
in-dom-†? (case⊤ _ _) = no λ ()
in-dom-†? (case⊥ _) = no λ ()
in-dom-†? `[] = no λ ()
in-dom-†? (_ `∷ _) = no λ ()
in-dom-†? (caseL _ _ _) = no λ ()

_† : ∀ {Γ A}
    (M : Γ ⊢ A)
    {M-in-dom-† : True (in-dom-†? M)}
  → Γ ⊢ A
(` x) † = ` x
((ƛ M) †) {ƛ-∈-dom}
  with toWitness ƛ-∈-dom
...  | in-dom-†-ƛ M-∈-dom =
       ƛ ((M †) {fromWitness M-∈-dom})
((L · M) †) {·-∈-dom}
  with toWitness ·-∈-dom
...  | in-dom-†-· L-∈-dom M-∈-dom =
       ((L †) {fromWitness L-∈-dom}) · ((M †) {fromWitness M-∈-dom})
(`let L M †) {`let-∈-dom}
  with toWitness `let-∈-dom
...  | in-dom-†-`let L-∈-dom M-∈-dom =
       (ƛ ((M †) {fromWitness M-∈-dom})) · ((L †) {fromWitness L-∈-dom})

~† : ∀ {Γ A}
    (M : Γ ⊢ A)
    {M-∈-dom-† : True (in-dom-†? M)}
  → M ~ ((M †) {M-∈-dom-†})
~† (` x) = ~`
~† (ƛ M) {ƛ-∈-dom}
  with toWitness ƛ-∈-dom
...  | in-dom-†-ƛ M-∈-dom =
       ~ƛ (~† M)
~† (L · M) {·-∈-dom}
  with toWitness ·-∈-dom
...  | in-dom-†-· L-∈-dom M-∈-dom =
       (~† L) ~· (~† M)
~† (`let L M) {`let-∈-dom}
  with toWitness `let-∈-dom
...  | in-dom-†-`let L-∈-dom M-∈-dom =
       ~let (~† L) (~† M)

~⇒†≡ : ∀ {Γ A}
    {M : Γ ⊢ A}
    {M-∈-dom-† : True (in-dom-†? M)}
    {N : Γ ⊢ A}
  → M ~ N
  → ((M †) {M-∈-dom-†}) ≡ N
~⇒†≡ ~` = refl
~⇒†≡ {M-∈-dom-† = M-∈-dom} (~ƛ M~N)
  with toWitness M-∈-dom
...  | in-dom-†-ƛ N-∈-dom =
       Eq.cong ƛ_ (~⇒†≡ M~N)
~⇒†≡ {M-∈-dom-† = ·-∈-dom} (L~L† ~· M~M†)
  with toWitness ·-∈-dom
...  | in-dom-†-· L-∈-dom M-∈-dom =
       Eq.cong₂ _·_ (~⇒†≡ L~L†) (~⇒†≡ M~M†)
~⇒†≡ {M-∈-dom-† = `let-∈-dom} (~let L~L† M~M†)
  with toWitness `let-∈-dom
...  | in-dom-†-`let L-∈-dom M-∈-dom =
       Eq.cong₂ _·_
         (Eq.cong ƛ_ (~⇒†≡ M~M†))
         (~⇒†≡ L~L†)
```


## Simulation commutes with values

We need a number of technical results. The first is that simulation
commutes with values.  That is, if `M ~ M†` and `M` is a value then
`M†` is also a value:
```agda
~val : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M
    --------
  → Value M†
~val ~`           ()
~val (~ƛ ~N)      V-ƛ  =  V-ƛ
~val (~L ~· ~M)   ()
~val (~let ~M ~N) ()
```
It is a straightforward case analysis, where here the only value
of interest is a lambda abstraction.

#### Exercise `~val⁻¹` (practice)

Show that this also holds in the reverse direction: if `M ~ M†`
and `Value M†` then `Value M`.

```agda
~val⁻¹ : ∀ {Γ A}
    {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M†
  → Value M
~val⁻¹ (~ƛ ~M) V-ƛ = V-ƛ
```


## Simulation commutes with renaming

The next technical result is that simulation commutes with renaming.
That is, if `ρ` maps any judgment `Γ ∋ A` to a judgment `Δ ∋ A`,
and if `M ~ M†` then `rename ρ M ~ rename ρ M†`:

```agda
~rename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
    ----------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → rename ρ M ~ rename ρ M†)
~rename ρ (~`)          =  ~`
~rename ρ (~ƛ ~N)       =  ~ƛ (~rename (ext ρ) ~N)
~rename ρ (~L ~· ~M)    =  (~rename ρ ~L) ~· (~rename ρ ~M)
~rename ρ (~let ~M ~N)  =  ~let (~rename ρ ~M) (~rename (ext ρ) ~N)
```
The structure of the proof is similar to the structure of renaming itself:
reconstruct each term with recursive invocation, extending the environment
where appropriate (in this case, only for the body of an abstraction).


## Simulation commutes with substitution

The third technical result is that simulation commutes with substitution.
It is more complex than renaming, because where we had one renaming map
`ρ` here we need two substitution maps, `σ` and `σ†`.

The proof first requires we establish an analogue of extension.
If `σ` and `σ†` both map any judgment `Γ ∋ A` to a judgment `Δ ⊢ A`,
such that for every `x` in `Γ ∋ A` we have `σ x ~ σ† x`,
then for any `x` in `Γ , B ∋ A` we have `exts σ x ~ exts σ† x`:
```agda
~exts : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    --------------------------------------------------
  → (∀ {A B} → (x : Γ , B ∋ A) → exts σ x ~ exts σ† x)
~exts ~σ Z      =  ~`
~exts ~σ (S x)  =  ~rename S_ (~σ x)
```
The structure of the proof is similar to the structure of extension itself.
The newly introduced variable trivially relates to itself, and otherwise
we apply renaming to the hypothesis.

With extension under our belts, it is straightforward to show
substitution commutes.  If `σ` and `σ†` both map any judgment `Γ ∋ A`
to a judgment `Δ ⊢ A`, such that for every `x` in `Γ ∋ A` we have `σ
x ~ σ† x`, and if `M ~ M†`, then `subst σ M ~ subst σ† M†`:
```agda
~subst : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    ---------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → subst σ M ~ subst σ† M†)
~subst ~σ (~` {x = x})  =  ~σ x
~subst ~σ (~ƛ ~N)       =  ~ƛ (~subst (~exts ~σ) ~N)
~subst ~σ (~L ~· ~M)    =  (~subst ~σ ~L) ~· (~subst ~σ ~M)
~subst ~σ (~let ~M ~N)  =  ~let (~subst ~σ ~M) (~subst (~exts ~σ) ~N)
```
Again, the structure of the proof is similar to the structure of
substitution itself: reconstruct each term with recursive invocation,
extending the environment where appropriate (in this case, only for
the body of an abstraction).

From the general case of substitution, it is also easy to derive
the required special case.  If `N ~ N†` and `M ~ M†`, then
`N [ M ] ~ N† [ M† ]`:
```agda
~sub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {M M† : Γ ⊢ B}
  → N ~ N†
  → M ~ M†
    -----------------------
  → (N [ M ]) ~ (N† [ M† ])
~sub {Γ} {A} {B} ~N ~M = ~subst {Γ , B} {Γ} ~σ {A} ~N
  where
  ~σ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ _
  ~σ Z      =  ~M
  ~σ (S x)  =  ~`
```
Once more, the structure of the proof resembles the original.


## The relation is a simulation

Finally, we can show that the relation actually is a simulation.
In fact, we will show the stronger condition of a lock-step simulation.
What we wish to show is:

_Lock-step simulation_: For every `M`, `M†`, and `N`:
If `M ~ M†` and `M —→ N`
then `M† —→ N†` and `N ~ N†`
for some `N†`.

Or, in a diagram:

    M  --- —→ --- N
    |             |
    |             |
    ~             ~
    |             |
    |             |
    M† --- —→ --- N†

We first formulate a concept corresponding to the lower leg
of the diagram, that is, its right and bottom edges:
```agda
data Leg {Γ A} (M† N : Γ ⊢ A) : Set where

  leg : ∀ {N† : Γ ⊢ A}
    → N ~ N†
    → M† —→ N†
      --------
    → Leg M† N
```
For our formalisation, in this case, we can use a stronger
relation than `—↠`, replacing it by `—→`.

We can now state and prove that the relation is a simulation.
Again, in this case, we can use a stronger relation than
`—↠`, replacing it by `—→`:
```agda
sim : ∀ {Γ A} {M M† N : Γ ⊢ A}
  → M ~ M†
  → M —→ N
    ---------
  → Leg  M† N
sim ~`              ()
sim (~ƛ ~N)         ()
sim (~L ~· ~M)      (ξ-·₁ L—→)
  with sim ~L L—→
...  | leg ~L′ L†—→                 =  leg (~L′ ~· ~M)   (ξ-·₁ L†—→)
sim (~V ~· ~M)      (ξ-·₂ VV M—→)
  with sim ~M M—→
...  | leg ~M′ M†—→                 =  leg (~V ~· ~M′)   (ξ-·₂ (~val ~V VV) M†—→)
sim ((~ƛ ~N) ~· ~V) (β-ƛ VV)        =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))
sim (~let ~M ~N)    (ξ-let M—→)
  with sim ~M M—→
...  | leg ~M′ M†—→                 =  leg (~let ~M′ ~N) (ξ-·₂ V-ƛ M†—→)
sim (~let ~V ~N)    (β-let VV)      =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))
```
The proof is by case analysis, examining each possible instance of `M ~ M†`
and each possible instance of `M —→ M†`, using recursive invocation whenever
the reduction is by a `ξ` rule, and hence contains another reduction.
In its structure, it looks a little bit like a proof of progress:

* If the related terms are variables, no reduction applies.
* If the related terms are abstractions, no reduction applies.
* If the related terms are applications, there are three subcases:
  - The source term reduces via `ξ-·₁`, in which case the target term does as well.
    Recursive invocation gives us

        L  --- —→ ---  L′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        L† --- —→ --- L′†

    from which follows:

         L · M  --- —→ ---  L′ · M
           |                   |
           |                   |
           ~                   ~
           |                   |
           |                   |
        L† · M† --- —→ --- L′† · M†

  - The source term reduces via `ξ-·₂`, in which case the target term does as well.
    Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

         V · M  --- —→ ---  V · M′
           |                  |
           |                  |
           ~                  ~
           |                  |
           |                  |
        V† · M† --- —→ --- V† · M′†

    Since simulation commutes with values and `V` is a value, `V†` is also a value.

  - The source term reduces via `β-ƛ`, in which case the target term does as well:

         (ƛ x ⇒ N) · V  --- —→ ---  N [ x := V ]
              |                           |
              |                           |
              ~                           ~
              |                           |
              |                           |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x :=  V† ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V ] ~ N† [ x := V† ]`.

* If the related terms are a let and an application of an abstraction,
  there are two subcases:

  - The source term reduces via `ξ-let`, in which case the target term
    reduces via `ξ-·₂`.  Recursive invocation gives us

        M  --- —→ ---  M′
        |              |
        |              |
        ~              ~
        |              |
        |              |
        M† --- —→ --- M′†

    from which follows:

        let x = M in N --- —→ --- let x = M′ in N
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N) · M  --- —→ --- (ƛ x ⇒ N) · M′

  - The source term reduces via `β-let`, in which case the target
    term reduces via `β-ƛ`:

        let x = V in N  --- —→ ---  N [ x := V ]
              |                         |
              |                         |
              ~                         ~
              |                         |
              |                         |
        (ƛ x ⇒ N†) · V† --- —→ --- N† [ x := V† ]

    Since simulation commutes with values and `V` is a value, `V†` is also a value.
    Since simulation commutes with substitution and `N ~ N†` and `V ~ V†`,
    we have `N [ x := V ] ~ N† [ x := V† ]`.


#### Exercise `sim⁻¹` (practice)

Show that we also have a simulation in the other direction, and hence that we have
a bisimulation.

```agda
data Leg⁻¹ {Γ A} (M N† : Γ ⊢ A) : Set where
  leg⁻¹ : ∀ {N : Γ ⊢ A}
    → N ~ N†
    → M —→ N
    → Leg⁻¹ M N†

sim⁻¹ : ∀ {Γ A}
    {M M† N† : Γ ⊢ A}
  → M ~ M†
  → M† —→ N†
  → Leg⁻¹ M N†
sim⁻¹ (~L ~· ~M) (ξ-·₁ L†—→)
  with sim⁻¹ ~L L†—→
... | leg⁻¹ N~L′ L—→N =
      leg⁻¹ (N~L′ ~· ~M) (ξ-·₁ L—→N)
sim⁻¹ (~L ~· ~M) (ξ-·₂ V-L† M†—→)
  with sim⁻¹ ~M M†—→
...  | leg⁻¹ N~M′ M—→N =
       leg⁻¹ (~L ~· N~M′) (ξ-·₂ (~val⁻¹ ~L V-L†) M—→N)
sim⁻¹ ((~ƛ ~L) ~· ~M) (β-ƛ V-M†) =
  leg⁻¹ (~sub ~L ~M) (β-ƛ (~val⁻¹ ~M V-M†))
sim⁻¹ (~let ~L ~M) (ξ-·₂ V-ƛ L†—→)
  with sim⁻¹ ~L L†—→
... | leg⁻¹ ~N M—→ =
      leg⁻¹ (~let ~N ~M) (ξ-let M—→)
sim⁻¹ (~let ~L ~M) (β-ƛ V-L) =
  leg⁻¹ (~sub ~M ~L) (β-let (~val⁻¹ ~L V-L))
```

#### Exercise `products` (practice)

Show that the two formulations of products in
Chapter [More](/More/)
are in bisimulation.  The only constructs you need to include are
variables, and those connected to functions and products.
In this case, the simulation is _not_ lock-step.

```agda
infix 4 _~′_
infix 5 ~′ƛ_
infix 7 _~′·_

data _~′_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ~′` : ∀ {Γ A} {x : Γ ∋ A}
    → ` x ~′ ` x

  ~′ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~′ N†
    → ƛ N ~′ ƛ N†

  _~′·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~′ L†
    → M ~′ M†
    → L · M ~′ L† · M†

  ~′`⟨_,_⟩ : ∀ {Γ A B} {L L† : Γ ⊢ A} {M M† : Γ ⊢ B}
    → L ~′ L†
    → M ~′ M†
    → `⟨ L , M ⟩ ~′ `⟨ L† , M† ⟩

  ~′`proj₁ : ∀ {Γ A B} {M M† : Γ ⊢ A `× B}
    → M ~′ M†
    → `proj₁ M ~′ case× M† (# 1)

  ~′`proj₂ : ∀ {Γ A B} {M M† : Γ ⊢ A `× B}
    → M ~′ M†
    → `proj₂ M ~′ case× M† (# 0)


infix 5 in-dom-†′-ƛ_
infix 7 _in-dom-†′-·_

data in-dom-†′ : ∀ {Γ A} → Γ ⊢ A → Set where

  in-dom-†′-` : ∀ {Γ A}
      (x : A ∋ Γ)
    → in-dom-†′ (` x)

  in-dom-†′-ƛ_ : ∀ {Γ A B} {M : Γ , B ⊢ A}
    → in-dom-†′ M
    → in-dom-†′ (ƛ M)

  _in-dom-†′-·_ : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → in-dom-†′ L
    → in-dom-†′ M
    → in-dom-†′ (L · M)

  in-dom-†′-`⟨_,_⟩ : ∀ {Γ A B} {L : Γ ⊢ A} {M : Γ ⊢ B}
    → in-dom-†′ L
    → in-dom-†′ M
    → in-dom-†′ `⟨ L , M ⟩

  in-dom-†′-`proj₁ : ∀ {Γ A B} {M : Γ ⊢ A `× B}
    → in-dom-†′ M
    → in-dom-†′ (`proj₁ M)

  in-dom-†′-`proj₂ : ∀ {Γ A B} {M : Γ ⊢ A `× B}
    → in-dom-†′ M
    → in-dom-†′ (`proj₂ M)


in-dom-†′? : ∀ {Γ A} (M : Γ ⊢ A) → Dec (in-dom-†′ M)

in-dom-†′? (` x) = yes (in-dom-†′-` x)

in-dom-†′? (ƛ M)
  with in-dom-†′? M
...  | yes M-∈-dom =
       yes (in-dom-†′-ƛ M-∈-dom)
...  | no  M-∉-dom =
       no λ{ (in-dom-†′-ƛ M-∈-dom) → M-∉-dom M-∈-dom }

in-dom-†′? (L · M)
  with in-dom-†′? L | in-dom-†′? M
...  | yes L-∈-dom  | yes M-∈-dom =
       yes (L-∈-dom in-dom-†′-· M-∈-dom)
...  | no  L-∉-dom  | _ =
       no λ{ (L-∈-dom in-dom-†′-· M-∈-dom) → L-∉-dom L-∈-dom }
...  | _            | no  M-∉-dom =
       no λ{ (L-∈-dom in-dom-†′-· M-∈-dom) → M-∉-dom M-∈-dom }

in-dom-†′? `⟨ L , M ⟩
  with in-dom-†′? L | in-dom-†′? M
...  | yes L-∈-dom  | yes M-∈-dom =
       yes in-dom-†′-`⟨ L-∈-dom , M-∈-dom ⟩
...  | no  L-∉-dom  | _ =
       no λ{ in-dom-†′-`⟨ L-∈-dom , M-∈-dom ⟩ → L-∉-dom L-∈-dom }
...  | _            | no  M-∉-dom =
       no λ{ in-dom-†′-`⟨ L-∈-dom , M-∈-dom ⟩ → M-∉-dom M-∈-dom }

in-dom-†′? (`proj₁ M)
  with in-dom-†′? M
...  | yes M-∈-dom =
       yes (in-dom-†′-`proj₁ M-∈-dom)
...  | no  M-∉-dom =
       no λ{ (in-dom-†′-`proj₁ M-∈-dom) → M-∉-dom M-∈-dom }

in-dom-†′? (`proj₂ M)
  with in-dom-†′? M
...  | yes M-∈-dom =
       yes (in-dom-†′-`proj₂ M-∈-dom)
...  | no  M-∉-dom =
       no λ{ (in-dom-†′-`proj₂ M-∈-dom) → M-∉-dom M-∈-dom }

in-dom-†′? `zero = no λ ()
in-dom-†′? (`suc _) = no λ ()
in-dom-†′? (case _ _ _) = no λ ()
in-dom-†′? (μ _) = no λ ()
in-dom-†′? (con _) = no λ ()
in-dom-†′? (_ `* _) = no λ ()
in-dom-†′? (`let _ _) = no λ ()
in-dom-†′? (case× _ _) = no λ ()
in-dom-†′? (`inj₁ _) = no λ ()
in-dom-†′? (`inj₂ _) = no λ ()
in-dom-†′? (case⊎ _ _ _) = no λ ()
in-dom-†′? `tt = no λ ()
in-dom-†′? (case⊤ _ _) = no λ ()
in-dom-†′? (case⊥ _) = no λ ()
in-dom-†′? `[] = no λ ()
in-dom-†′? (_ `∷ _) = no λ ()
in-dom-†′? (caseL _ _ _) = no λ ()


_†′ : ∀ {Γ A}
  → (M : Γ ⊢ A)
  → {M-in-dom†′ : True (in-dom-†′? M)}
  → Γ ⊢ A

(` x) †′ = ` x

((ƛ M) †′) {ƛ-∈-dom}
  with toWitness ƛ-∈-dom
...  | in-dom-†′-ƛ M-∈-dom =
       ƛ ((M †′) {fromWitness M-∈-dom})

((L · M) †′) {·-∈-dom}
  with toWitness ·-∈-dom
...  | L-∈-dom in-dom-†′-· M-∈-dom =
       ((L †′) {fromWitness L-∈-dom}) · ((M †′) {fromWitness M-∈-dom})

(`⟨ L , M ⟩ †′) {`⟨,⟩-∈-dom}
  with toWitness `⟨,⟩-∈-dom
...  | in-dom-†′-`⟨ L-∈-dom , M-∈-dom ⟩ =
       `⟨ (L †′) {fromWitness L-∈-dom} , (M †′) {fromWitness M-∈-dom} ⟩

(`proj₁ M †′) {`proj₁-∈-dom}
  with toWitness `proj₁-∈-dom
...  | in-dom-†′-`proj₁ M-∈-dom =
       case× ((M †′) {fromWitness M-∈-dom}) (# 1)

(`proj₂ M †′) {`proj₂-∈-dom}
  with toWitness `proj₂-∈-dom
...  | in-dom-†′-`proj₂ M-∈-dom =
       case× ((M †′) {fromWitness M-∈-dom}) (# 0)


~†′ : ∀ {Γ A}
  → (M : Γ ⊢ A)
  → {M-∈-dom-†′ : True (in-dom-†′? M)}
  → M ~′ ((M †′) {M-∈-dom-†′})

~†′ (` x) = ~′`

~†′ (ƛ M) {ƛ-∈-dom}
  with toWitness ƛ-∈-dom
...  | in-dom-†′-ƛ M-∈-dom =
       ~′ƛ (~†′ M)

~†′ (L · M) {·-∈-dom}
  with toWitness ·-∈-dom
...  | L-∈-dom in-dom-†′-· M-∈-dom =
       (~†′ L) ~′· (~†′ M)

~†′ `⟨ L , M ⟩ {`⟨,⟩-∈-dom}
  with toWitness `⟨,⟩-∈-dom
...  | in-dom-†′-`⟨ L-∈-dom , M-∈-dom ⟩ =
       ~′`⟨ ~†′ L , ~†′ M ⟩

~†′ (`proj₁ M) {`proj₁-∈-dom}
  with toWitness `proj₁-∈-dom
...  | in-dom-†′-`proj₁ M-∈-dom =
       ~′`proj₁ (~†′ M)

~†′ (`proj₂ M) {`proj₂-∈-dom}
  with toWitness `proj₂-∈-dom
...  | in-dom-†′-`proj₂ M-∈-dom =
       ~′`proj₂ (~†′ M)


~′⇒†≡ : ∀ {Γ A} {M N : Γ ⊢ A} {M-∈-dom-†′ : True (in-dom-†′? M)}
  → M ~′ N
  → (M †′) {M-∈-dom-†′} ≡ N

~′⇒†≡ ~′` = refl

~′⇒†≡ {M-∈-dom-†′ = ƛ-∈-dom} (~′ƛ ~M)
  with toWitness ƛ-∈-dom
...  | in-dom-†′-ƛ M-∈-dom =
       Eq.cong ƛ_ (~′⇒†≡ ~M)

~′⇒†≡ {M-∈-dom-†′ = ·-∈-dom} (~L ~′· ~M)
  with toWitness ·-∈-dom
...  | L-∈-dom in-dom-†′-· M-∈-dom =
       Eq.cong₂ _·_ (~′⇒†≡ ~L) (~′⇒†≡ ~M)

~′⇒†≡ {M-∈-dom-†′ = `⟨,⟩-∈-dom} ~′`⟨ ~L , ~M ⟩
  with toWitness `⟨,⟩-∈-dom
...  | in-dom-†′-`⟨ L-∈-dom , M-∈-dom ⟩ =
       Eq.cong₂ `⟨_,_⟩ (~′⇒†≡ ~L) (~′⇒†≡ ~M)

~′⇒†≡ {M-∈-dom-†′ = `proj₁-∈-dom} (~′`proj₁ ~M)
  with toWitness `proj₁-∈-dom
...  | in-dom-†′-`proj₁ M-∈-dom =
       Eq.cong₂ case× (~′⇒†≡ ~M) refl

~′⇒†≡ {M-∈-dom-†′ = `proj₂-∈-dom} (~′`proj₂ ~M)
  with toWitness `proj₂-∈-dom
...  | in-dom-†′-`proj₂ M-∈-dom =
       Eq.cong₂ case× (~′⇒†≡ ~M) refl


~′val : ∀ {Γ A} {M M†′ : Γ ⊢ A}
  → M ~′ M†′
  → Value M
  → Value M†′

~′val (~′ƛ M~′) V-ƛ = V-ƛ
~′val ~′`⟨ L~′ , M~′ ⟩ V-⟨ V-L , V-M ⟩ =
  V-⟨ ~′val L~′ V-L , ~′val M~′ V-M ⟩


~′val⁻¹ : ∀ {Γ A} {M M†′ : Γ ⊢ A}
  → M ~′ M†′
  → Value M†′
  → Value M

~′val⁻¹ (~′ƛ M†′~′) V-ƛ = V-ƛ
~′val⁻¹ ~′`⟨ L†′~′ , M†′~′ ⟩ V-⟨ V-L†′ , V-M†′ ⟩ =
  V-⟨ ~′val⁻¹ L†′~′ V-L†′ , ~′val⁻¹ M†′~′ V-M†′ ⟩


~′rename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → (∀ {A} {M M†′ : Γ ⊢ A} → M ~′ M†′ → rename ρ M ~′ rename ρ M†′)

~′rename ρ ~′`              = ~′`
~′rename ρ (~′ƛ M~′)        = ~′ƛ ~′rename (ext ρ) M~′
~′rename ρ (L~′ ~′· M~′)    = ~′rename ρ L~′ ~′· ~′rename ρ M~′
~′rename ρ ~′`⟨ L~′ , M~′ ⟩ = ~′`⟨ ~′rename ρ L~′ , ~′rename ρ M~′ ⟩
~′rename ρ (~′`proj₁ M~′)   = ~′`proj₁ (~′rename ρ M~′)
~′rename ρ (~′`proj₂ M~′)   = ~′`proj₂ (~′rename ρ M~′)


~′exts : ∀ {Γ Δ}
  → {σ   : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ†′ : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~′ σ†′ x)
  → (∀ {A B} → (x : Γ , B ∋ A) → exts σ x ~′ exts σ†′ x)

~′exts σ~′ Z     = ~′`
~′exts σ~′ (S x) = ~′rename S_ (σ~′ x)


~′subst : ∀ {Γ Δ}
  → {σ   : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ†′ : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~′ σ†′ x)
  → (∀ {A} {M M†′ : Γ ⊢ A} → M ~′ M†′ → subst σ M ~′ subst σ†′ M†′)

~′subst σ~′ (~′` {x = x})    = σ~′ x
~′subst σ~′ (~′ƛ M~′)        = ~′ƛ (~′subst (~′exts σ~′) M~′)
~′subst σ~′ (L~′ ~′· M~′)    = (~′subst σ~′ L~′) ~′· (~′subst σ~′ M~′)
~′subst σ~′ ~′`⟨ L~′ , M~′ ⟩ = ~′`⟨ ~′subst σ~′ L~′ , ~′subst σ~′ M~′ ⟩
~′subst σ~′ (~′`proj₁ M~′)   = ~′`proj₁ (~′subst σ~′ M~′)
~′subst σ~′ (~′`proj₂ M~′)   = ~′`proj₂ (~′subst σ~′ M~′)


~′sub : ∀ {Γ A B} {N N†′ : Γ , B ⊢ A} {M M†′ : Γ ⊢ B}
  → N ~′ N†′
  → M ~′ M†′
  → (N [ M ]) ~′ (N†′ [ M†′ ])

~′sub {Γ} {A} {B} N~′ M~′ = ~′subst {Γ , B} {Γ} σ~′ {A} N~′
  where
  σ~′ : ∀ {A} → (x : Γ , B ∋ A) → _ ~′ _
  σ~′ Z     = M~′
  σ~′ (S _) = ~′`


~′sub² : ∀ {Γ A B C} {N N†′ : Γ , B , C ⊢ A} {L L†′ : Γ ⊢ B} {M M†′ : Γ ⊢ C}
  → N ~′ N†′
  → L ~′ L†′
  → M ~′ M†′
  → (N [ L ][ M ]) ~′ (N†′ [ L†′ ][ M†′ ])

~′sub² {Γ} {A} {B} {C} N~′ M~′ L~′ = ~′subst {Γ , B , C} {Γ} σ~′ {A} N~′
  where
  σ~′ : ∀ {A} → (x : Γ , B , C ∋ A) → _ ~′ _
  σ~′ Z         = L~′
  σ~′ (S Z)     = M~′
  σ~′ (S (S _)) = ~′`


data Leg′ {Γ A} (M†′ N : Γ ⊢ A) : Set where

  leg′ : ∀ {N†′ : Γ ⊢ A}
    → N ~′ N†′
    → M†′ —→ N†′
    → Leg′ M†′ N


sim′ : ∀ {Γ A} {M M†′ N : Γ ⊢ A}
  → M ~′ M†′
  → M —→ N
  → Leg′ M†′ N

sim′ (L~′ ~′· M~′) (ξ-·₁ L—→)
  with sim′ L~′ L—→
...  | leg′ L′~′ L†′—→ =
       leg′ (L′~′ ~′· M~′) (ξ-·₁ L†′—→)

sim′ (L~′ ~′· M~′) (ξ-·₂ V-L M—→)
  with sim′ M~′ M—→
...  | leg′ M′~′ M†′—→ =
       leg′ (L~′ ~′· M′~′) (ξ-·₂ (~′val L~′ V-L) M†′—→)

sim′ ((~′ƛ L~′) ~′· M~′) (β-ƛ V-M) =
  leg′ (~′sub L~′ M~′) (β-ƛ (~′val M~′ V-M))

sim′ ~′`⟨ L~′ , M~′ ⟩ (ξ-⟨,⟩₁ L—→)
  with sim′ L~′ L—→
...  | leg′ L′~′ L†′—→ =
       leg′ ~′`⟨ L′~′ , M~′ ⟩ (ξ-⟨,⟩₁ L†′—→)

sim′ ~′`⟨ L~′ , M~′ ⟩ (ξ-⟨,⟩₂ V-L M—→)
  with sim′ M~′ M—→
...  | leg′ M′~′ M†′—→ =
       leg′ ~′`⟨ L~′ , M′~′ ⟩ (ξ-⟨,⟩₂ (~′val L~′ V-L) M†′—→)

sim′ (~′`proj₁ M~′) (ξ-proj₁ M—→)
  with sim′ M~′ M—→
...  | leg′ M′~′ M†′—→ =
       leg′ (~′`proj₁ M′~′) (ξ-case× M†′—→)

sim′ (~′`proj₁ ~′`⟨ L~′ , M~′ ⟩) (β-proj₁ V-L V-M) =
  leg′ L~′ (β-case× (~′val L~′ V-L) (~′val M~′ V-M))

sim′ (~′`proj₂ M~′) (ξ-proj₂ M—→)
  with sim′ M~′ M—→
...  | leg′ M′~′ M†′—→ =
       leg′ (~′`proj₂ M′~′) (ξ-case× M†′—→)

sim′ (~′`proj₂ ~′`⟨ L~′ , M~′ ⟩) (β-proj₂ V-L V-M) =
  leg′ M~′ (β-case× (~′val L~′ V-L) (~′val M~′ V-M))


data Leg′⁻¹ {Γ A} (M N† : Γ ⊢ A) : Set where

  leg′⁻¹ : ∀ {N : Γ ⊢ A}
    → N ~′ N†
    → M —↠ N
    → Leg′⁻¹ M N†


—↠-distr : ∀ {Γ A B}
  → (f : Γ ⊢ A → Γ ⊢ B)
  → ({M M′ : Γ ⊢ A} → M —→ M′ → f M —→ f M′)
  → ({M M′ : Γ ⊢ A} → M —↠ M′ → f M —↠ f M′)
—↠-distr f embed (_ ∎) = _ ∎
—↠-distr f embed (_ —→⟨ M—→N ⟩ N—↠M′) =
  _ —→⟨ embed M—→N ⟩ —↠-distr f embed N—↠M′


sim′⁻¹ : ∀ {Γ A} {M M†′ N†′ : Γ ⊢ A}
  → M ~′ M†′
  → M†′ —→ N†′
  → Leg′⁻¹ M N†′

sim′⁻¹ (L†′~′ ~′· M†′~′) (ξ-·₁ L†′—→)
  with sim′⁻¹ L†′~′ L†′—→
...  | leg′⁻¹ L~′ L—↠ =
       leg′⁻¹
         (L~′ ~′· M†′~′)
         (—↠-distr (_· _) ξ-·₁ L—↠)

sim′⁻¹ (L~′ ~′· M~′) (ξ-·₂ V-L†′ M†′—→)
  with sim′⁻¹ M~′ M†′—→
...  | leg′⁻¹ M′~′ M—↠ =
       leg′⁻¹
         (L~′ ~′· M′~′)
         (—↠-distr (_ ·_) (ξ-·₂ (~′val⁻¹ L~′ V-L†′)) M—↠)

sim′⁻¹ ((~′ƛ L~′) ~′· M~′) (β-ƛ V-M†′) =
  leg′⁻¹
    (~′sub L~′ M~′)
    (_ —→⟨ β-ƛ (~′val⁻¹ M~′ V-M†′) ⟩ _ ∎)

sim′⁻¹ ~′`⟨ L~′ , M~′ ⟩ (ξ-⟨,⟩₁ L†′—→)
  with sim′⁻¹ L~′ L†′—→
...  | leg′⁻¹ L′~′ L—↠ =
       leg′⁻¹
         ~′`⟨ L′~′ , M~′ ⟩
         (—↠-distr `⟨_, _ ⟩ ξ-⟨,⟩₁ L—↠)

sim′⁻¹ ~′`⟨ L~′ , M~′ ⟩ (ξ-⟨,⟩₂ V-L†′ M†′—→)
  with sim′⁻¹ M~′ M†′—→
...  | leg′⁻¹ M′~′ M—↠ =
       leg′⁻¹
         ~′`⟨ L~′ , M′~′ ⟩
         (—↠-distr `⟨ _ ,_⟩ (ξ-⟨,⟩₂ (~′val⁻¹ L~′ V-L†′)) M—↠)

sim′⁻¹ (~′`proj₁ M~′) (ξ-case× M†′—→)
  with sim′⁻¹ M~′ M†′—→
...  | leg′⁻¹ M′~′ M—↠ =
       leg′⁻¹
         (~′`proj₁ M′~′)
         (—↠-distr `proj₁ ξ-proj₁ M—↠)

sim′⁻¹ (~′`proj₁ ~′`⟨ L~′ , M~′ ⟩) (β-case× V-L V-M) =
  leg′⁻¹
    (~′sub² ~′` L~′ M~′)
    (_ —→⟨ β-proj₁ (~′val⁻¹ L~′ V-L) (~′val⁻¹ M~′ V-M) ⟩ _ ∎)

sim′⁻¹ (~′`proj₂ M~′) (ξ-case× M†′—→)
  with sim′⁻¹ M~′ M†′—→
...  | leg′⁻¹ M′~′ M—↠ =
       leg′⁻¹
         (~′`proj₂ M′~′)
         (—↠-distr `proj₂ ξ-proj₂ M—↠)

sim′⁻¹ (~′`proj₂ ~′`⟨ L~′ , M~′ ⟩) (β-case× V-L V-M) =
  leg′⁻¹
    (~′sub² ~′` L~′ M~′)
    (_ —→⟨ β-proj₂ (~′val⁻¹ L~′ V-L) (~′val⁻¹ M~′ V-M) ⟩ _ ∎)
```

## Unicode

This chapter uses the following unicode:

    †  U+2020  DAGGER (\dag)
    ⁻  U+207B  SUPERSCRIPT MINUS (\^-)
    ¹  U+00B9  SUPERSCRIPT ONE (\^1)
