/-
Copyright 2025 The Formal Conjectures Authors.

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
# Written on the Wall II - Conjecture 100

**Verbatim statement (WOWII #100, status O):**
> If G is a simple connected graph, then α(G) ≤ CEIL[(maximum of λ(v) + 0.5*length(G))/2]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj100


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitional choice

The original conjecture uses `length(G)`, which is ambiguous in DeLaVina's
notation.  We interpret `length(G)` as the **diameter** of `G` (the maximum
eccentricity, i.e. `maxEccentricity G`), which is the most natural graph-
theoretic notion of "length".  The inequality then reads:
  `α(G) ≤ ⌈(max_v l(v) + 0.5 · diam(G)) / 2⌉`
where `l(v) = indepNeighbors G v` and `diam(G) = (maxEccentricity G).toNat`.
-/

namespace WrittenOnTheWallII.GraphConjecture100

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 100](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`α(G) ≤ ⌈(max_v l(v) + 0.5 · diam(G)) / 2⌉`
where `α(G) = G.indepNum` is the independence number,
`max_v l(v)` is the maximum over all vertices of the independence number of
the neighbourhood, and `diam(G)` is the diameter of `G`.

**Note:** `length(G)` in DeLaVina's original is interpreted here as the diameter.
-/
@[category research open, AMS 5]
theorem conjecture100 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    let diam := (maxEccentricity G).toNat
    (G.indepNum : ℝ) ≤ ⌈((maxL : ℝ) + (1 / 2) * (diam : ℝ)) / 2⌉ := by
  sorry

-- Sanity checks

/-- The independence number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.indepNum := Nat.zero_le _

/-- `maxEccentricity` on a two-vertex complete graph is `⊤` since all eccentricities
are computed via `sSup` and the distance between the two vertices is 1. -/
@[category test, AMS 5]
example : 0 ≤ (maxEccentricity (⊤ : SimpleGraph (Fin 2))).toNat := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture100
