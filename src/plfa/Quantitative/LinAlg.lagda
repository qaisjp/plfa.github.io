---
title     : "Quantitative: Relation to Linear Algebra"
layout    : page
permalink : /Quantitative/LinAlg/
---

\begin{code}
module plfa.Quantitative.LinAlg where
\end{code}


# Imports

\begin{code}
open import Algebra.Structures using (IsCommutativeSemiring)
open import Data.Nat using (ℕ; suc; zero; _+_; _*_)
open import Data.Nat.Properties using (*-+-isCommutativeSemiring)
open import Function using (_∘_; _|>_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Vec using (Vec; _∷_; []; zipWith)
open import Data.Vec.Properties using (zipWith-identityˡ)
-- Workaround for outdated agda-stdlib version
*-+-isSemiring = IsCommutativeSemiring.isSemiring *-+-isCommutativeSemiring
open import plfa.Quantitative _+_ _*_ 0 1 *-+-isSemiring

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning
\end{code}

\begin{code}
Mat : Set → ℕ → ℕ → Set
Mat A n m = Vec (Vec A m) n
\end{code}


# Erasure

\begin{code}
∥_∥ℕ : Precontext → ℕ
∥ ∅     ∥ℕ = zero
∥ γ , _ ∥ℕ = suc ∥ γ ∥ℕ
\end{code}

\begin{code}
∥_∥Fin : ∀ {γ} {A} → γ ∋ A → Fin ∥ γ ∥ℕ
∥ Z   ∥Fin = zero
∥ S x ∥Fin = suc ∥ x ∥Fin
\end{code}

\begin{code}
∥_∥Vec : ∀ {γ} → Context γ → Vec ℕ ∥ γ ∥ℕ
∥ ∅         ∥Vec = []
∥ Γ , π ∙ _ ∥Vec = π ∷ ∥ Γ ∥Vec
\end{code}

\begin{code}
∥_∥Mat : ∀ {γ δ} → Matrix γ δ → Mat ℕ ∥ γ ∥ℕ ∥ δ ∥ℕ
∥_∥Mat {∅}     {δ} Δ = []
∥_∥Mat {γ , _} {δ} Δ = ∥ Δ Z ∥Vec ∷ ∥ (Δ ∘ S_) ∥Mat
\end{code}


# Decoration

\begin{code}
fromℕ : ℕ → Precontext
fromℕ zero    = ∅
fromℕ (suc n) = fromℕ n , `0
\end{code}


# Examples

\begin{code}
_ : ∥ 0s {γ = fromℕ 5} ∥Vec
  ≡ (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
_ = refl
\end{code}

\begin{code}
_ : ∥ identity {γ = fromℕ 5} ∥Mat
  ≡ (1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []) ∷
    (0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ []) ∷
    (0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ []) ∷
    (0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ []) ∷
    (0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ []) ∷ []
_ = refl
\end{code}


# Identities

\begin{code}
lem-⋈-+ : ∀ {γ} (Γ Δ : Context γ)

    --------------------------------------------
  → ∥ Γ ⋈ Δ ∥Vec ≡ zipWith _+_ ∥ Γ ∥Vec ∥ Δ ∥Vec

lem-⋈-+ ∅ ∅ = refl
lem-⋈-+ (Γ , x ∙ A) (Δ , y ∙ .A) =
  begin
    x + y ∷ ∥ Γ ⋈ Δ ∥Vec
  ≡⟨ lem-⋈-+ Γ Δ |> cong (x + y ∷_) ⟩
    x + y ∷ zipWith _+_ ∥ Γ ∥Vec ∥ Δ ∥Vec
  ∎
\end{code}