---
title     : "Assignment3: TSPL Assignment 3"
layout    : page
permalink : /TSPL/2019/Assignment3/
---

```
module Assignment3 where
```

## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using the "submit" command.
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
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Algebra.Structures using (IsMonoid)
open import Level using (Level)
open import Relation.Unary using (Decidable)
open import plfa.part1.Relations using (_<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality)
open plfa.part1.Isomorphism.≃-Reasoning
open import plfa.part1.Lists using (List; []; _∷_; [_]; [_,_]; [_,_,_]; [_,_,_,_];
  _++_; reverse; map; foldr; sum; All; Any; here; there; _∈_)
open import plfa.part2.Lambda hiding (ƛ′_⇒_; case′_[zero⇒_|suc_⇒_]; μ′_⇒_; plus′)
  renaming (begin_ to lbegin_; _∎ to _l∎)
open import plfa.part2.Properties hiding (value?; unstuck; preserves; wttdgs)

```


## Lists

#### Exercise `reverse-++-distrib` (recommended)

Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first:

    reverse (xs ++ ys) ≡ reverse ys ++ reverse xs

```
open import plfa.part1.Lists using (++-identityˡ; ++-identityʳ; ++-assoc )

reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib {A} [] ys =
  begin
    reverse [] ++ reverse ys
  ≡⟨⟩
    [] ++ reverse ys
  ≡⟨ cong ([] ++_) (++-identityˡ (reverse ys)) ⟩
    reverse ys
  ≡⟨ (sym (++-identityʳ (reverse ys))) ⟩
    reverse ys ++ []
  ≡⟨⟩
    reverse ys ++ (reverse [])
  ∎
reverse-++-distrib (x ∷ xs) ys
  rewrite reverse-++-distrib xs ys
        | ++-assoc (reverse ys) (reverse xs) [ x ]
        = refl
```

Or in long form:

    begin
      (reverse ys ++ reverse xs) ++ [ x ]
    ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
      reverse ys ++ (reverse xs ++ [ x ])
    ≡⟨⟩
      reverse ys ++ reverse xs ++ [ x ]
    ∎

#### Exercise `reverse-involutive` (recommended)

A function is an _involution_ if when applied twice it acts
as the identity function.  Show that reverse is an involution:

    reverse (reverse xs) ≡ xs

```
reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs)
  rewrite reverse-++-distrib (reverse xs) [ x ]
        | reverse-involutive xs = refl
```

#### Exercise `map-compose` (practice)

Prove that the map of a composition is equal to the composition of two maps:

    map (g ∘ f) ≡ map g ∘ map f

The last step of the proof requires extensionality.

```
-- Dear marker, is this correct? Is there a better way I could do this?
-- When should we use this sort of formatting?
-- Thanks in advance.
map-compose : ∀ {A B C : Set}
            → (f : A → B)
            → (g : B → C)
              --------------
            → map (g ∘ f) ≡ map g ∘ map f

open import plfa.part1.Isomorphism using (extensionality)

map-compose f g = extensionality (helper f g)
  where
    helper : ∀ {A B C : Set}
      → (f : A → B)
      → (g : B → C)
      → (xs : List A)
        --------------
      → map (g ∘ f) xs ≡ (map g ∘ map f) xs

    helper f g [] = refl
    helper f g (y ∷ ys) = cong (_∷_ (g (f y))) (helper f g ys)
```

#### Exercise `map-++-distribute` (practice)

Prove the following relationship between map and append:

   map f (xs ++ ys) ≡ map f xs ++ map f ys

```
map-++-distribute : ∀ {A B : Set}
  → (f : A -> B)
  → (xs ys : List A)
    ----------------
  → map f (xs ++ ys) ≡ map f xs ++ map f ys

map-++-distribute f [] ys = refl
map-++-distribute f (x ∷ xs) ys  rewrite map-++-distribute f xs ys = refl
```

#### Exercise `map-Tree` (practice)

Define a type of trees with leaves of type `A` and internal
nodes of type `B`:
```
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B
```
Define a suitable map operator over trees:

    map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D

```
map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree A→C B→D (leaf a) = leaf (A→C a)
map-Tree A→C B→D (node left x right) = (node l y r)
  where
    l = map-Tree A→C B→D left
    r = map-Tree A→C B→D right
    y = B→D x
```

#### Exercise `product` (recommended)

Use fold to define a function to find the product of a list of numbers.
For example:

    product [ 1 , 2 , 3 , 4 ] ≡ 24

```
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ =
  begin
    product [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _*_ 1 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    1 * foldr _*_ 1 [ 2 , 3 , 4 ]
  ≡⟨⟩
    1 * 2 * foldr _*_ 1 [ 3 , 4 ]
  ≡⟨⟩
    1 * 2 * 3 * foldr _*_ 1 [ 4 ]
  ≡⟨⟩
    1 * 2 * 3 * 4 * foldr _*_ 1 []
  ≡⟨⟩
    1 * 2 * 3 * 4 * 1
  ∎
```

#### Exercise `foldr-++` (recommended)

Show that fold and append are related as follows:

    foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
      foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs

```
foldr-++′ : ∀ {A B : Set}
  → (_⊗_ : A -> B -> B)
  → (e : B)
  → (xs ys : List A)
    -------------
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs

foldr-++′ _⊗_ e [] ys = refl
foldr-++′ _⊗_ e (x ∷ xs) ys =
  begin
    x ⊗ foldr _⊗_ e (xs ++ ys)
  ≡⟨ cong (x ⊗_) (foldr-++′ _⊗_ e xs ys) ⟩
    x ⊗ foldr _⊗_ (foldr _⊗_ e ys) xs
  ∎

-- or the second part can be just:
--   foldr-++′ _⊗_ e (x ∷ xs) ys rewrite foldr-++′ _⊗_ e xs ys = refl
```

#### Exercise `map-is-foldr` (practice)

Show that map can be defined using fold:

    map-is-foldr : ∀ {A B : Set} {f : A → B} →
      map f ≡ foldr (λ x xs → f x ∷ xs) []

This requires extensionality.

```
map-is-foldr : ∀ {A B : Set}
  → (f : A → B)
  → (xs : List A)
    ------------
  → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f xs = extensionality (helper f)
  where
      helper : ∀ {A B : Set}
        → (f : A → B)
        → (ys : List A)
          ------------
        → map f ys ≡ foldr (λ y ys → f y ∷ ys) [] ys
      helper f [] = refl
      helper f (x ∷ ys) = cong ((f x) ∷_) (helper f ys)

```

#### Exercise `fold-Tree` (practice)

Define a suitable fold function for the type of trees given earlier:

    fold-Tree : ∀ {A B C : Set}
      → (A → C) → (C → B → C → C) → Tree A B → C


```
fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree {A} {B} {C} A→C f (leaf a) = A→C a
fold-Tree {A} {B} {C} A→C f (node left b right) = f l b r
  where
    -- note: f is a function that takes (node left b right) and produces a C
    l = fold-Tree A→C f left
    r = fold-Tree A→C f right

```

#### Exercise `map-is-fold-Tree` (practice)

Demonstrate an analogue of `map-is-foldr` for the type of trees.

```
map-is-fold-Tree : ∀ {A B C D : Set}
  → (ac : A → C)
  → (bd : B → D)
--  → (t : Tree A B)
    --------
  → map-Tree ac bd ≡ fold-Tree (λ { a → leaf (ac a) }) (λ { l b r → node l (bd b) r })


map-is-fold-Tree ac bd = extensionality (helper ac bd)
  where
      helper :  ∀ {A B C D : Set}
        → (ac : A → C)
        → (bd : B → D)
        → (t : Tree A B)
          --------
        → map-Tree ac bd t ≡ fold-Tree (λ { a → leaf (ac a) }) (λ { l b r → node l (bd b) r }) t
      helper ac bd (leaf a) = refl
      helper ac bd (node left b right)
        rewrite (helper ac bd left)
              | (helper ac bd right) = refl

```

#### Exercise `sum-downFrom` (stretch)

Define a function that counts down as follows:
```
downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n
```
For example:
```
_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl
```
Prove that the sum of the numbers `(n - 1) + ⋯ + 0` is
equal to `n * (n ∸ 1) / 2`:

    sum-downFrom : ∀ (n : ℕ)
      → sum (downFrom n) * 2 ≡ n * (n ∸ 1)


```

open import Data.Nat.Properties using (*-comm; *-distribˡ-+; +-comm;
                                       *-distribˡ-∸; *-zeroˡ)
open import Data.Nat.Properties using (m∸n+n≡m; +-∸-comm; +-∸-assoc)

sum-downFrom : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n)  =
      begin
        (n + foldr _+_ 0 (downFrom n)) * 2
      ≡⟨ *-comm (n + foldr _+_ 0 (downFrom n)) 2 ⟩
        2 * (n + foldr _+_ 0 (downFrom n))
      ≡⟨ *-distribˡ-+ 2 n (foldr _+_ 0 (downFrom n)) ⟩
        (2 * n) + (2 * (foldr _+_ 0 (downFrom n)))
      ≡⟨ +-comm (2 * n) (2 * (foldr _+_ 0 (downFrom n))) ⟩
        (2 * (foldr _+_ 0 (downFrom n))) + (2 * n)
      ≡⟨⟩
        (2 * sum (downFrom n)) + (2 * n)
      ≡⟨ cong (_+ (2 * n)) (*-comm 2 (sum (downFrom n))) ⟩
        (sum (downFrom n) * 2) + (2 * n)
      ≡⟨ cong (_+ (2 * n)) (sum-downFrom n) ⟩
        n * (n ∸ 1) + (2 * n)
      ≡⟨⟩
        (n * (n ∸ 1)) + (2 * n)
      ≡⟨ cong (_+ (2 * n)) (*-distribˡ-∸ n n 1) ⟩
        ((n * n) ∸ (n * 1)) + (2 * n)
      ≡⟨⟩
        ((n * n) ∸ (n * 1)) + (n + (1 * n))
      -- ≡⟨ Data.Nat.Properties.+-assoc ((n * n) ∸ (n * 1)) n (1 * n) ⟩
      ≡⟨ cong ( λ x → ((n * n) ∸ (n * 1)) + (n + x)) (*-identityˡ n)  ⟩
        (((n * n) ∸ (n * 1)) + (n + n))
      ≡⟨ cong ( λ x → ((n * n) ∸ (x)) + (n + n)) (*-identityʳ n)  ⟩
        ((n * n) ∸ n) + (n + n)
      ≡⟨ sym (+-assoc ((n * n) ∸ n) n n) ⟩
        ((n * n ∸ n) + n) + n
      ≡⟨⟩
        (((n * n) ∸ n) + n) + n
      ≡⟨ cong (_+ n) (sym (+-∸-comm n (n≤n*n n))) ⟩

      -- ≡⟨ cong ( λ x → x + n ) (m∸n+n≡m (n≤n*n n)) ⟩
        ( ((n * n) + n) ∸ n ) + n
      ≡⟨ cong (_+ n) ( +-∸-assoc (n * n) (Data.Nat.Properties.≤-reflexive (n≡n n) ) ) ⟩
        ( (n * n) + (n ∸ n) ) + n
      ≡⟨ cong ( λ x → ((n * n) + x) + n ) (Data.Nat.Properties.n∸n≡0 n) ⟩
         (n * n) + 0 + n
      ≡⟨ cong (_+ n) (+-identityʳ (n * n)) ⟩
         (n * n) + n
      ≡⟨ +-comm (n * n) n ⟩
        n + (n * n)
      ≡⟨⟩
        n + n * n
      ∎
      where
        n≡n : ∀ (n : ℕ) → n ≡ n
        n≡n a = refl

        n≤n*n : ∀ (n : ℕ) → n ≤ (n * n)
        n≤n*n zero = z≤n
        n≤n*n (suc m) = s≤s ( h m (m * suc m) )
          where
            h : ∀ (m l : ℕ) → m ≤ m + l
            h zero l =  z≤n
            h (suc m) l  = s≤s (h m l)
          -- where
          --   s = Data.Nat.Properties.*-monoʳ-≤ 1 (Data.Nat.Properties.≤-reflexive (n≡n n) ) -- rewrite Data.Nat.Properties.*-mono-≤ (s≤s (n * n)) = ?
          --   h : ∀ (n : ℕ) → n + 0 * n ≡ n
          --   h n =
          --     begin
          --       n + 0 * n
          --     ≡⟨⟩
          --       n + (0 * n)
          --     ≡⟨ cong (n +_) (*-zeroˡ n) ⟩
          --       n + 0
          --     ≡⟨ +-identityʳ n ⟩
          --       n
          --     ∎


```


#### Exercise `foldl` (practice)

Define a function `foldl` which is analogous to `foldr`, but where
operations associate to the left rather than the right.  For example:

    foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
    foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z

```
-- Your code goes here
foldl : {A B : Set} → (A → B → B) → B → List A → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = x ⊗ (foldl _⊗_ e xs)
```


#### Exercise `foldr-monoid-foldl` (practice)

Show that if `_⊗_` and `e` form a monoid, then `foldr _⊗_ e` and
`foldl _⊗_ e` always compute the same result.

```

open import plfa.part1.Lists using () renaming (IsMonoid to IsMonoidE)

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoidE _⊗_ e →
  ∀ (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs

--  ^^^^^^^^^^^^^  is this type signature correct?

foldr-monoid-foldl ox e mox [] = refl
foldr-monoid-foldl ox e mox (x ∷ xs) rewrite foldr-monoid-foldl ox e mox xs = refl

```


#### Exercise `Any-++-⇔` (recommended)

Prove a result similar to `All-++-⇔`, but with `Any` in place of `All`, and a suitable
replacement for `_×_`.  As a consequence, demonstrate an equivalence relating
`_∈_` and `_++_`.


```

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_⇔_)

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)

Any-++-⇔ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    }

  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)

    to [] ys Pys = inj₂ Pys
    to (x ∷ xs) ys (here Px) = inj₁ (here Px)
    to (x ∷ xs) ys (there Prests) with to xs ys Prests
    ... | inj₁ x₁ = inj₁ (there x₁)
    ... | inj₂ y = inj₂ y

    from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      Any P xs ⊎ Any P ys → Any P (xs ++ ys)
    from [] ys (inj₂ y) = y
    from (x ∷ xs) ys (inj₂ y) = there (from xs ys (inj₂ y))
    from (x ∷ xs) ys (inj₁ (here x₁)) = here x₁
    from (x ∷ xs) ys (inj₁ (there x′)) = there (from xs ys (inj₁ x′))

-- As a consequence, demonstrate an equivalence relating `_∈_` and `_++_`
-- (uhhh this is not an equivalence!!!)
∈-++ : ∀ {A : Set} {e : A} (xs ys : List A) → (e ∈ xs) → (e ∈ (xs ++ ys))
∈-++ (x ∷ xs) ys (here x₁) = here x₁
∈-++ (x ∷ xs) ys (there x∈xs) = there (∈-++ xs ys x∈xs)

```

#### Exercise `All-++-≃` (stretch)

Show that the equivalence `All-++-⇔` can be extended to an isomorphism.

```
-- Your code goes here
```


#### Exercise `¬Any⇔All¬` (recommended)

Show that `Any` and `All` satisfy a version of De Morgan's Law:

    (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs

(Can you see why it is important that here `_∘_` is generalised
to arbitrary levels, as described in the section on
[universe polymorphism]({{ site.baseurl }}/Equality/#unipoly)?)


```
¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} → (xs : List A) →
  (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs


¬Any→All¬ : ∀ {A : Set} {P : A → Set} → (xs : List A) →
  (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs

¬Any→All¬ [] p = []
¬Any→All¬ (x ∷ xs) p = (λ x → p (here x)) ∷ ¬Any→All¬ xs (λ z → p (there z))

All¬→¬Any : ∀ {A : Set} {P : A → Set} → (xs : List A) →
  All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs

All¬→¬Any [] p = λ ()
All¬→¬Any (x ∷ xs) (x₁ ∷ p) (here x₂) = x₁ x₂
All¬→¬Any (x ∷ xs) (x₁ ∷ p) (there x₂) = All¬→¬Any xs p x₂

¬Any⇔All¬ xs = record
  { to = ¬Any→All¬ xs
  ; from = All¬→¬Any xs
  }


```

Do we also have the following?

    (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs

If so, prove; if not, explain why.

Not provable! Because:

Any¬→¬All is provable, because Any is defined where there is at least
  one x in xs (and so is Any)


¬All→Any¬ is not, because whilst All is defined for 0 or more x in xs,
  Any is only defined where there is atleast one x in xs


  ¬All⇔Any¬ : ∀ {A : Set} {P : A → Set} → (xs : List A) →
    (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs

  ¬All→Any¬ : ∀ {A : Set} {P : A → Set} → (xs : List A) →
    (¬_ ∘ All P) xs → Any (¬_ ∘ P) xs

  ¬All→Any¬ [] ps = ? -- cannot prove!!!!!
  ¬All→Any¬ (x ∷ xs) x₁ = ? -- cannot prove!!!!!

  Any¬→¬All : ∀ {A : Set} {P : A → Set} → (xs : List A) →
    Any (¬_ ∘ P) xs → (¬_ ∘ All P) xs

  Any¬→¬All .(_ ∷ _) (here x) (p ∷ ps) = x p
  Any¬→¬All .(_ ∷ xs) (there {xs = xs} ps) (x ∷ y) = Any¬→¬All xs ps y

  ¬All⇔Any¬ xs = record
    { to =  ¬All→Any¬ xs
    ; from = Any¬→¬All xs
    }

#### Exercise `¬Any≃All¬` (stretch)

Show that the equivalence `¬Any⇔All¬` can be extended to an isomorphism.
You will need to use extensionality.

```
-- Your code goes here
```


#### Exercise `All-∀` (practice)

Show that `All P xs` is isomorphic to `∀ {x} → x ∈ xs → P x`.

```
-- You code goes here
```


#### Exercise `Any-∃` (practice)

Show that `Any P xs` is isomorphic to `∃[ x ] (x ∈ xs × P x)`.

```
-- You code goes here
```


#### Exercise `any?` (stretch)

Just as `All` has analogues `all` and `All?` which determine whether a
predicate holds for every element of a list, so does `Any` have
analogues `any` and `Any?` which determine whether a predicate holds
for some element of a list.  Give their definitions.

```
-- Your code goes here
```


#### Exercise `filter?` (stretch)

Define the following variant of the traditional `filter` function on lists,
which given a decidable predicate and a list returns all elements of the
list satisfying the predicate:
```
postulate
  filter? : ∀ {A : Set} {P : A → Set}
    → (P? : Decidable P) → List A → ∃[ ys ]( All P ys )
```



## Lambda

#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.  Your definition may use `plus` as
defined earlier.

```
mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
    [zero⇒ `zero
    |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n") ]
```


#### Exercise `mulᶜ` (practice)

Write out the definition of a lambda term that multiplies
two natural numbers represented as Church numerals. Your
definition may use `plusᶜ` as defined earlier (or may not
— there are nice definitions both ways).

```
-- Your code goes here
```


#### Exercise `primed` (stretch) {#primed}

Some people find it annoying to write `` ` "x" `` instead of `x`.
We can make examples with lambda terms slightly easier to write
by adding the following definitions:
```
ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N  =  ƛ x ⇒ N
ƛ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]      =  ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N
μ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥
```
We intend to apply the function only when the first term is a variable, which we
indicate by postulating a term `impossible` of the empty type `⊥`.  If we use
C-c C-n to normalise the term

  ƛ′ two ⇒ two

Agda will return an answer warning us that the impossible has occurred:

  ⊥-elim (plfa.part2.Lambda.impossible (`` `suc (`suc `zero)) (`suc (`suc `zero)) ``)

While postulating the impossible is a useful technique, it must be
used with care, since such postulation could allow us to provide
evidence of _any_ proposition whatsoever, regardless of its truth.

The definition of `plus` can now be written as follows:
```
plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"
```
Write out the definition of multiplication in the same style.


#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a `with` clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.

```
-- Your code goes here
```


#### Exercise `—↠≲—↠′` (practice)

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?

```
-- Your code goes here
```

#### Exercise `plus-example` (practice)

Write out the reduction sequence demonstrating that one plus one is two.

```
-- Your code goes here
```


#### Exercise `Context-≃` (practice)

Show that `Context` is isomorphic to `List (Id × Type)`.
For instance, the isomorphism relates the context

    ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ

to the list

    [ ⟨ "z" , `ℕ ⟩ , ⟨ "s" , `ℕ ⇒ `ℕ ⟩ ]

```
-- Your code goes here
```

#### Exercise `mul-type` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well typed.

```
mul-type : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
mul-type = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢zero)
              (⊢plus · ⊢` ∋n′ · ((⊢` ∋* · ⊢` ∋m′ · ⊢` ∋n′))))))
  where
  ∋m  = (S (λ()) Z)
  ∋m′ = Z
  ∋n′ = (S (λ()) Z)
  ∋*  = (S (λ()) (S (λ()) (S (λ()) Z)))

⊢mul = mul-type
```


#### Exercise `mulᶜ-type` (practice)

Using the term `mulᶜ` you defined earlier, write out the derivation
showing that it is well typed.

```
-- Your code goes here
```



## Properties

#### Exercise `Progress-≃` (practice)

Show that `Progress M` is isomorphic to `Value M ⊎ ∃[ N ](M —→ N)`.

```
-- Your code goes here
```

#### Exercise `progress′` (practice)

Write out the proof of `progress′` in full, and compare it to the
proof of `progress` above.

```
-- Your code goes here
```

#### Exercise `value?` (practice)

Combine `progress` and `—→¬V` to write a program that decides
whether a well-typed term is a value:
```
postulate
  value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
```

#### Exercise `subst′` (stretch)

Rewrite `subst` to work with the modified definition `_[_:=_]′`
from the exercise in the previous chapter.  As before, this
should factor dealing with bound variables into a single function,
defined by mutual recursion with the proof that substitution
preserves types.

```
-- Your code goes here
```


#### Exercise `mul-eval` (recommended)

Using the evaluator, confirm that two times two is four.

```
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
        · ` "n"
        · (` "*" · ` "m" · ` "n")
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
       · ` "n"
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
           · ` "n"
           · (` "*" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
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
      · ` "n"
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
          · ` "n"
          · (` "*" · ` "m" · ` "n")
          ])))
       · ` "m"
       · ` "n")
      ])
     · `suc (`suc `zero)
     —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
     case `suc (`suc `zero) [zero⇒ `zero |suc "m" ⇒
     (μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · `suc (`suc `zero)
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
         · ` "n"
         · (` "*" · ` "m" · ` "n")
         ])))
      · ` "m"
      · `suc (`suc `zero))
     ]
     —→⟨ β-suc (V-suc V-zero) ⟩
     (μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · `suc (`suc `zero)
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
         · ` "n"
         · (` "*" · ` "m" · ` "n")
         ])))
      · `suc `zero
      · `suc (`suc `zero))
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
         · ` "n"
         · (` "*" · ` "m" · ` "n")
         ])))
      · `suc `zero
      · `suc (`suc `zero))
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
         · ` "n"
         · (` "*" · ` "m" · ` "n")
         ])))
      · `suc `zero
      · `suc (`suc `zero))
     —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
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
     ·
     ((ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ `zero |suc "m" ⇒
        (μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "n"
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
            · ` "n"
            · (` "*" · ` "m" · ` "n")
            ])))
         · ` "m"
         · ` "n")
        ]))
      · `suc `zero
      · `suc (`suc `zero))
     —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
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
     ·
     ((ƛ "n" ⇒
       case `suc `zero [zero⇒ `zero |suc "m" ⇒
       (μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       · ` "n"
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
           · ` "n"
           · (` "*" · ` "m" · ` "n")
           ])))
        · ` "m"
        · ` "n")
       ])
      · `suc (`suc `zero))
     —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
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
     ·
     case `suc `zero [zero⇒ `zero |suc "m" ⇒
     (μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · `suc (`suc `zero)
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
         · ` "n"
         · (` "*" · ` "m" · ` "n")
         ])))
      · ` "m"
      · `suc (`suc `zero))
     ]
     —→⟨ ξ-·₂ V-ƛ (β-suc V-zero) ⟩
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
     ·
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · `suc (`suc `zero)
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
          · ` "n"
          · (` "*" · ` "m" · ` "n")
          ])))
       · `zero
       · `suc (`suc `zero)))
     —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
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
      · `suc (`suc `zero)
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
          · ` "n"
          · (` "*" · ` "m" · ` "n")
          ])))
       · `zero
       · `suc (`suc `zero)))
     —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
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
     ·
     ((ƛ "n" ⇒
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
          · ` "n"
          · (` "*" · ` "m" · ` "n")
          ])))
       · `zero
       · `suc (`suc `zero)))
     —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ))) ⟩
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
     ·
     ((ƛ "n" ⇒
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
      ·
      ((ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ `zero |suc "m" ⇒
         (μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · ` "n"
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
             · ` "n"
             · (` "*" · ` "m" · ` "n")
             ])))
          · ` "m"
          · ` "n")
         ]))
       · `zero
       · `suc (`suc `zero)))
     —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-zero))) ⟩
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
     ·
     ((ƛ "n" ⇒
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
      ·
      ((ƛ "n" ⇒
        case `zero [zero⇒ `zero |suc "m" ⇒
        (μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "n"
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
            · ` "n"
            · (` "*" · ` "m" · ` "n")
            ])))
         · ` "m"
         · ` "n")
        ])
       · `suc (`suc `zero)))
     —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
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
     ·
     ((ƛ "n" ⇒
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
      ·
      case `zero [zero⇒ `zero |suc "m" ⇒
      (μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · `suc (`suc `zero)
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
          · ` "n"
          · (` "*" · ` "m" · ` "n")
          ])))
       · ` "m"
       · `suc (`suc `zero))
      ])
     —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ β-zero) ⟩
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
     ·
     ((ƛ "n" ⇒
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
      · `zero)
     —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
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
     ·
     case `suc (`suc `zero) [zero⇒ `zero |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "m"
      · `zero)
     ]
     —→⟨ ξ-·₂ V-ƛ (β-suc (V-suc V-zero)) ⟩
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
     ·
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · `suc `zero
      · `zero)
     —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
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
     ·
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
      · `zero)
     —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero)))) ⟩
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
     ·
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
      · `zero)
     —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-ƛ V-zero)) ⟩
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
     ·
     `suc
     case `suc `zero [zero⇒ `zero |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "m"
      · `zero)
     ]
     —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-suc V-zero)) ⟩
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
     ·
     `suc
     (`suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       · `zero
       · `zero))
     —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ)))) ⟩
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
     ·
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
       · `zero))
     —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero)))) ⟩
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
     ·
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
       · `zero))
     —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (β-ƛ V-zero))) ⟩
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
     ·
     `suc
     (`suc
      case `zero [zero⇒ `zero |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       · ` "m"
       · `zero)
      ])
     —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc β-zero)) ⟩
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
     —→⟨ ξ-suc (ξ-suc β-zero) ⟩ `suc (`suc (`suc (`suc `zero))) l∎)
    (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl
```


#### Exercise: `progress-preservation` (practice)

Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.

```
-- Your code goes here
```


#### Exercise `subject_expansion` (practice)

We say that `M` _reduces_ to `N` if `M —→ N`,
but we can also describe the same situation by saying
that `N` _expands_ to `M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M —→ N` and `∅ ⊢ N ⦂ A` imply `∅ ⊢ M ⦂ A`.
Find two counter-examples to subject expansion, one
with case expressions and one not involving case expressions.

```
-- Your code goes here
```


#### Exercise `stuck` (practice)

Give an example of an ill-typed term that does get stuck.

```
-- Your code goes here
```

#### Exercise `unstuck` (recommended)

Provide proofs of the three postulates, `unstuck`, `preserves`, and `wttdgs` above.

```
unstuck : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ---------
  → ¬ (Stuck M)

unstuck f ⟨ fst , snd ⟩ with progress f
... | step a = fst a
... | done b = snd b


preserves : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    ---------
  → ∅ ⊢ N ⦂ A
preserves a (M l∎) = a
preserves a (L —→⟨ x ⟩ b) = preserves (preserve a x) b

wttdgs : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    --------
  → ¬ (Stuck N)
wttdgs a b = unstuck (preserves a b)

```
