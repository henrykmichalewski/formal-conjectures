/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1167

*Reference:* [erdosproblems.com/1167](https://www.erdosproblems.com/1167)

## Problem Statement

Let $r \geq 2$ be finite and $\lambda$ be an infinite cardinal. Let $\kappa_\alpha$ be cardinals
for all $\alpha < \gamma$. Is it true that
$$2^\lambda \to (\kappa_\alpha + 1)_{\alpha < \gamma}^{r+1}$$
implies
$$\lambda \to (\kappa_\alpha)_{\alpha < \gamma}^r?$$

Here the notation $\mu \to (\nu_\alpha)_{\alpha < \gamma}^s$ denotes the partition arrow: for
every coloring of $s$-element subsets of a set of cardinality $\mu$ using colors indexed by
$\alpha < \gamma$, there exists a monochromatic (homogeneous) subset of cardinality $\nu_\alpha$
for some $\alpha < \gamma$.

This is a problem of Erdős, Hajnal, and Rado.

## Overview

The central novelty in this file is `CardinalPartitionRel`: the general multicolor $r$-uniform
partition relation $\mu \to (\nu_\alpha)_{\alpha < \gamma}^r$ for infinite cardinals.

- `μ` (a `Cardinal`) is the size of the base set whose $r$-element subsets are colored.
- `r : ℕ` is the uniformity (edges are $r$-element finite sets).
- `γ` (an `Ordinal`) indexes the color classes.
- `ν : γ.ToType → Cardinal` assigns a target cardinality to each color.

The open question `erdos_1167` asks whether the $(r+1)$-uniform relation at $2^\lambda$
(with targets $\kappa_\alpha + 1$) implies the $r$-uniform relation at $\lambda$
(with targets $\kappa_\alpha$).

## Formalization Notes

- **r-element subsets**: We use `{s : Finset α // s.card = r}` as the type of $r$-element
  subsets of a type `α` with `#α = μ`.
- **Homogeneous set**: A set `H : Set α` is homogeneous for color `i` if every $r$-element
  subset of `H` receives color `i`.
- **Cardinal successor**: For an infinite cardinal $\kappa$, $\kappa + 1 = \kappa$ in cardinal
  arithmetic. The $+1$ in the antecedent is thus only nontrivial when $\kappa_\alpha$ is finite.
- We use `Ordinal.ToType` to turn the index ordinal `γ` into a type for the coloring function.
- We avoid the identifier `λ` (reserved in Lean 4) and write `lam` for the cardinal $\lambda$.
-/

open Cardinal Ordinal

namespace Erdos1167

universe u

/- ### The r-uniform cardinal partition relation -/

/--
`CardinalPartitionRel μ r γ ν` asserts the multicolor $r$-uniform partition relation
$$\mu \to (\nu_\alpha)_{\alpha < \gamma}^r.$$

It states: for any type `A` with `#A = μ` and any coloring `col` of the $r$-element finite
subsets of `A` by `γ.ToType` (the colors indexed by ordinals less than `γ`), there exists:
- a color `i : γ.ToType`, and
- a subset `H : Set A` with `#H = ν i`,
such that every $r$-element subset of `H` receives color `i`.

When `γ = 2` and `r = 2` this reduces to the classical binary partition relation
$\mu \to (\nu_0, \nu_1)^2$.
-/
def CardinalPartitionRel (μ : Cardinal.{u}) (r : ℕ) (γ : Ordinal.{u})
    (ν : γ.ToType → Cardinal.{u}) : Prop :=
  ∀ (A : Type u), #A = μ →
    ∀ col : {s : Finset A // s.card = r} → γ.ToType,
      ∃ (i : γ.ToType) (H : Set A),
        #H = ν i ∧
        ∀ (s : Finset A) (hs : s.card = r), (↑s : Set A) ⊆ H → col ⟨s, hs⟩ = i

/- ### The main open problem -/

/--
**OPEN**: Let $r \geq 2$ be finite and $\lambda$ be an infinite cardinal. Let
$\kappa_\alpha$ be cardinals for all $\alpha < \gamma$. Is it true that
$$2^\lambda \to (\kappa_\alpha + 1)_{\alpha < \gamma}^{r+1} \implies
  \lambda \to (\kappa_\alpha)_{\alpha < \gamma}^r?$$

Here $\kappa_\alpha + 1$ denotes the cardinal successor (for finite $\kappa_\alpha$) or
$\kappa_\alpha$ itself (for infinite $\kappa_\alpha$, since $\kappa + 1 = \kappa$).

The relation $\mu \to (\nu_\alpha)_{\alpha < \gamma}^s$ is the $s$-uniform partition relation:
every coloring of $s$-element subsets of a $\mu$-sized set by $\gamma$ colors yields a
monochromatic set of size $\nu_\alpha$ for some $\alpha$.

The "stepping-down" goes from $(r+1)$-uniform hypergraphs on a set of size $2^\lambda$ to
$r$-uniform hypergraphs on a set of size $\lambda$.

*A problem of Erdős, Hajnal, and Rado.*

**Status**: OPEN.
-/
@[category research open, AMS 5]
theorem erdos_1167 :
    ∀ (r : ℕ), 2 ≤ r →
    ∀ (lam : Cardinal.{u}), ℵ₀ ≤ lam →
    ∀ (γ : Ordinal.{u}) (κ : γ.ToType → Cardinal.{u}),
      -- Hypothesis: 2^lam → (κ_α + 1)_{α<γ}^{r+1}
      CardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ (fun α => κ α + 1) →
      -- Conclusion: lam → (κ_α)_{α<γ}^r
      CardinalPartitionRel lam r γ κ := by
  sorry

/- ### Variants and related results -/

namespace erdos_1167.variants

/--
**Finite target case**: When all $\kappa_\alpha$ are finite, $\kappa_\alpha + 1$ in the
partition relation is the ordinary successor natural number. This is the "classical" instance
of the stepping-down problem: from $(r+1)$-uniform colorings on $2^\lambda$ to $r$-uniform
colorings on $\lambda$, with finite target sizes.

**Status**: OPEN (as a special case of `erdos_1167`).
-/
@[category research open, AMS 5]
theorem finite_targets (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam)
    (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    CardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    CardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u})) := by
  sorry

/--
**Binary case**: The $\gamma = 2$ specialization, i.e. two color classes.

Is it true that $2^\lambda \to (\kappa_0 + 1, \kappa_1 + 1)^{r+1}$ implies
$\lambda \to (\kappa_0, \kappa_1)^r$ for all $r \geq 2$ and infinite $\lambda$?

**Status**: OPEN (as a special case of `erdos_1167`).
-/
@[category research open, AMS 5]
theorem binary_colors (r : ℕ) (hr : 2 ≤ r) (lam κ₀ κ₁ : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) :
    -- γ = 2, colors indexed by Fin 2
    (∀ (A : Type u), #A = (2 : Cardinal.{u}) ^ lam →
      ∀ col : {s : Finset A // s.card = r + 1} → Fin 2,
        (∃ H : Set A, #H = κ₀ + 1 ∧
          ∀ (s : Finset A) (hs : s.card = r + 1),
            (↑s : Set A) ⊆ H → col ⟨s, hs⟩ = 0) ∨
        (∃ H : Set A, #H = κ₁ + 1 ∧
          ∀ (s : Finset A) (hs : s.card = r + 1),
            (↑s : Set A) ⊆ H → col ⟨s, hs⟩ = 1)) →
    (∀ (A : Type u), #A = lam →
      ∀ col : {s : Finset A // s.card = r} → Fin 2,
        (∃ H : Set A, #H = κ₀ ∧
          ∀ (s : Finset A) (hs : s.card = r),
            (↑s : Set A) ⊆ H → col ⟨s, hs⟩ = 0) ∨
        (∃ H : Set A, #H = κ₁ ∧
          ∀ (s : Finset A) (hs : s.card = r),
            (↑s : Set A) ⊆ H → col ⟨s, hs⟩ = 1)) := by
  sorry

/--
**Infinite target case**: When all $\kappa_\alpha \geq \aleph_0$ are infinite, the cardinal
successor satisfies $\kappa_\alpha + 1 = \kappa_\alpha$ in cardinal arithmetic, so the
hypothesis simplifies to
$$2^\lambda \to (\kappa_\alpha)_{\alpha < \gamma}^{r+1}$$
implying
$$\lambda \to (\kappa_\alpha)_{\alpha < \gamma}^r.$$

The $+1$ disappears for infinite targets, making this a "pure" stepping-down lemma.

**Status**: OPEN (as a special case of `erdos_1167`).
-/
@[category research open, AMS 5]
theorem infinite_targets (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam)
    (γ : Ordinal.{u}) (κ : γ.ToType → Cardinal.{u}) (hκ : ∀ i, ℵ₀ ≤ κ i) :
    -- For infinite κ_α, κ_α + 1 = κ_α (so hypothesis and conclusion share the same targets)
    CardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ κ →
    CardinalPartitionRel lam r γ κ := by
  sorry

/--
**r = 2 case**: The stepping-down from 3-uniform to 2-uniform (pairs) partition relations.

Is it true that $2^\lambda \to (\kappa_\alpha + 1)_{\alpha < \gamma}^3$ implies
$\lambda \to (\kappa_\alpha)_{\alpha < \gamma}^2$?

This is the case $r = 2$ of `erdos_1167` and is a generalization of the classical
Erdős–Rado stepping-up/stepping-down theorems for pairs.

**Status**: OPEN (as a special case of `erdos_1167`).
-/
@[category research open, AMS 5]
theorem r_eq_two (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam)
    (γ : Ordinal.{u}) (κ : γ.ToType → Cardinal.{u}) :
    CardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) 3 γ (fun α => κ α + 1) →
    CardinalPartitionRel lam 2 γ κ := by
  sorry

end erdos_1167.variants

/- ### Sanity checks -/

/--
**Sanity check**: The hypothesis `ℵ₀ ≤ lam` is non-vacuous: $\aleph_0$ is an infinite cardinal.
-/
@[category test, AMS 5]
example : ℵ₀ ≤ ℵ₀ := le_refl _

/--
**Sanity check**: $2^{\aleph_0} > \aleph_0$, so the power $2^\lambda$ is strictly larger than
$\lambda$ for $\lambda = \aleph_0$. This confirms the two base sets in the stepping-down
implication are genuinely of different sizes.
-/
@[category test, AMS 5]
example : ℵ₀ < (2 : Cardinal) ^ ℵ₀ := Cardinal.cantor ℵ₀

/--
**Sanity check**: Every 0-element finset is empty. This confirms `Finset.card = 0` is
non-trivial and that the condition `s.card = r` in `CardinalPartitionRel` correctly captures
the notion of an $r$-element subset.
-/
@[category test, AMS 5]
example (A : Type u) (s : Finset A) (hs : s.card = 0) : s = ∅ :=
  Finset.card_eq_zero.mp hs

end Erdos1167
