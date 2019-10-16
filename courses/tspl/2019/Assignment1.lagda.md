---
title     : "Assignment1: TSPL Assignment 1"
layout    : page
permalink : /TSPL/2019/Assignment1/
---

```
module Assignment1 where
```

## Qais Patankar s1620208@inf.ed.ac.uk

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using the "submit" command.
```bash
submit tspl cw1 Assignment1.lagda.md
```
Please ensure your files execute correctly under Agda!



## Good Scholarly Practice.

Please remember the University requirement as
regards all assessed work. Details about this can be found at:

> [http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct](http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct)

Furthermore, you are required to take reasonable measures to protect
your assessed work from unauthorised access. For example, if you put
any such work on a public repository then you must set access
permissions appropriately (generally permitting access only to
yourself, or your group in the case of group practicals).



## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm;
  ≤-refl; ≤-trans; ≤-antisym; ≤-total; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
open import plfa.part1.Relations using (_<_; z<s; s<s; zero; suc; even; odd)
```

## Naturals

#### Exercise `seven` (practice) {#seven}

Write out `7` in longhand.

```
_ =
      begin
        7
      ≡⟨⟩
        (suc (suc (suc (suc (suc (suc (suc zero)))))))
      ∎
```

#### Exercise `+-example` (practice) {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations.

```
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩ -- is shorthand for
    (suc (suc (suc zero)))  + (suc (suc (suc (suc zero))))
  ≡⟨⟩ -- inducive case
    suc ((suc (suc zero)) + (suc (suc (suc (suc zero)))))
  ≡⟨⟩ -- inductive case
    suc (suc ((suc zero) + (suc (suc (suc (suc zero))))))
  ≡⟨⟩ -- inductive case
    suc (suc (suc (suc (suc (suc (suc zero))))))
  ∎

-- Or more compactly, we can write
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc (4)))
  ≡⟨⟩
    7
  ∎

-- Or even, if we're lazy, we can use the "reflexive"
-- It knows 3 + 4, so it can immediately check if it is the same as 7
_ : 3 + 4 ≡ 7
_ = refl
```


#### Exercise `*-example` (practice) {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations.


```
_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    4 + (4 + 4)
  ≡⟨⟩
    4 + 8
  ≡⟨⟩
    12
  ∎
```

#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations.

    n ^ 0        =  1
    n ^ (1 + m)  =  n * (n ^ m)

```
_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ (suc m) = n * (n ^ m)
```

Check that `3 ^ 4` is `81`.

```
_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    3 * (3 * (3 * 3))
  ≡⟨⟩
    3 * (3 * 9)
  ≡⟨⟩
    3 * (27)
  ≡⟨⟩
    81
  ∎
```


#### Exercise `∸-examples` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.

```
∸-example : 5 ∸ 3 ≡ 2
∸-example =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

∸-example′ : 3 ∸ 5 ≡ 0
∸-example′ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎
```

#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring.
```
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin
```
For instance, the bitstring

    1011

standing for the number eleven is encoded, right to left, as

    x1 x1 x0 x1 nil

Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as

    x1 x1 x0 x1 x0 x0 nil

Define a function

    inc : Bin → Bin

```
inc : Bin → Bin
inc nil = x1 nil
inc (x0 a) = x1 a
inc (x1 a) = x0 (inc a)
```

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have

    inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

```
-- dec 0 is bin 0 which is x0 nil
_ : inc (x0 nil) ≡ x1 nil
_ =
  begin
    inc (x0 nil)
  ≡⟨⟩
    (x1 nil)
  ∎

-- dec 1 is bin 1 which is x1 nil
_ : inc (x1 nil) ≡ x0 x1 nil
_ =
  begin
    inc (x1 nil)
  ≡⟨⟩
    x0 inc nil
  ≡⟨⟩
    x0 x1 nil
  ∎

-- dec 2 is bin 10 which is x0 x1 nil
_ : inc (x0 x1 nil) ≡ x1 x1 nil
_ =
  begin
    inc (x0 x1 nil)
  ≡⟨⟩
    x1 x1 nil
  ∎

-- dec 3 is bin 11 which is x1 x1 nil
_ : inc (x1 x1 nil) ≡ x0 x0 x1 nil
_ =
  begin
    inc (x1 x1 nil)
  ≡⟨⟩
    x0 inc (x1 nil)
  ≡⟨⟩
    x0 x0 inc nil
  ≡⟨⟩
    x0 x0 x1 nil
  ∎

-- dec 4 is bin 100 which is x0 x0 x1 nil
_ : inc (x0 x0 x1 nil) ≡ x1 x0 x1 nil
_ =
  begin
    inc (x0 x0 x1 nil)
  ≡⟨⟩
    x1 x0 x1 nil
  ∎
```

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

```
to : ℕ → Bin
to zero = x0 nil
to (suc n) = inc (to n)

from : Bin → ℕ
from nil = zero
from (x0 x) = 2 * from x
-- "shift left and add one"
from (x1 n) = 2 * (from n) + 1
```

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `x0 nil`.
Confirm that these both give the correct answer for zero through four.

```
-------
-- from
-------

_ : from (x0 nil) ≡ 0
_ = refl

_ : from (x1 nil)  ≡ 1
_ = refl

_ : from (x0 x1 nil) ≡ 2
_ = refl

_ : from (x1 x1 nil) ≡ 3
_ = refl

_ : from (x0 x0 x1 nil) ≡ 4
_ =
  begin
    from (x0 x0 x1 nil)
  ≡⟨⟩
    2 * from (x0 x1 nil)
  ≡⟨⟩
    2 * (2 * from (x1 nil))
  ≡⟨⟩
    2 * (2 * (2 * (from nil) + 1))
  ≡⟨⟩
    2 * (2 * (2 * zero + 1))
  ≡⟨⟩
    2 * (2 * (1))
  ≡⟨⟩
    2 * 2
  ∎

-----
-- to
-----
_ : to 0 ≡ x0 nil
_ = refl

_ : to 1 ≡ x1 nil
_ = refl

_ : to 2 ≡ x0 x1 nil
_ = refl

_ : to 3 ≡ x1 x1 nil
_ = refl

_ : to 4 ≡ x0 x0 x1 nil
_ =
  begin
    to 4
  ≡⟨⟩
    to (suc 3)
  ≡⟨⟩
    inc (to 3)
  ≡⟨⟩
    inc (to (suc 2))
  ≡⟨⟩
    inc (inc (to 2))
  ≡⟨⟩
    inc (inc (to (suc 1)))
  ≡⟨⟩
    inc (inc (inc (to 1)))
  ≡⟨⟩
    inc (inc (inc (to (suc 0))))
  ≡⟨⟩
    inc (inc (inc (inc (to 0))))
  ≡⟨⟩
    inc (inc (inc (inc (nil))))
  ≡⟨⟩
    inc (inc (inc (x1 nil)))
  ≡⟨⟩
    inc (inc (x0 x1 nil))
  ≡⟨⟩
    inc (x1 x1 nil)
  ≡⟨⟩
    x0 x0 x1 nil
  ∎
```

## Induction

#### Exercise `operators` (practice) {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

Give an example of an operator that has an identity and is
associative but is not commutative.


#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the first four
days using a finite story of creation, as
[earlier][plfa.Naturals#finite-creation]


#### Exercise `+-swap` (recommended) {#plus-swap}

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.  You may need to use
the following function from the standard library:

    sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m


```
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ +-comm m (n + p) ⟩
    (n + p) + m
  ≡⟨ +-assoc n p m ⟩
    n + (p + m)
  ≡⟨ cong (n +_) (+-comm p m) ⟩
    n + (m + p)
  ∎
```

#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

```
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p =
  begin
    (zero + n) * p
  ≡⟨⟩
    n * p
  ≡⟨⟩
    zero * p + n * p
  ∎

*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    (suc (m + n)) * p
  ≡⟨⟩ -- (*)   (suc x) * y ≡ y + (x * y)
    p + ( (m + n) * p )
  ≡⟨ cong (p +_ ) (*-distrib-+ m n p)  ⟩ 
    p + ( (m * p) + (n * p) )
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩ -- symmetric on (x + y) + z ≡ x + (y + z)
    (p + (m * p)) + (n * p)
  ≡⟨⟩
    ( (suc m) * p ) + (n * p)
  ∎
```

#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

```
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    ((suc m) * n) * p
  ≡⟨⟩
    (n + (m * n)) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    (n * p) + ((m * n) * p)
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    refl
```

#### Exercise `*-comm` (practice) {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

#### Exercise `0∸n≡0` (practice) {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

#### Exercise `∸-+-assoc` (practice) {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings.

    from (inc x) ≡ suc (from x)
    to (from n) ≡ n
    from (to x) ≡ x

For each law: if it holds, prove; if not, give a counterexample.


## Relations


#### Exercise `orderings` (practice) {#orderings}

Give an example of a preorder that is not a partial order.

Give an example of a partial order that is not a preorder.


#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.


#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

```
<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p

<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)
```

#### Exercise `trichotomy` (practice) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation][plfa.Negation].)

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings.

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring.

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity.

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)
