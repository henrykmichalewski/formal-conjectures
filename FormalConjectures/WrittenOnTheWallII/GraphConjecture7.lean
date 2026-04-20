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
# Written on the Wall II - Conjecture 7

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

This file introduces `matchingNumber G`, the size of a maximum matching of `G`,
as an integer-valued invariant (the existing `m G` returns a real number).
The two agree: `matchingNumber G = m G` for connected graphs.

**Conjecture 7:** For a connected graph `G`, `Ls(G) ≥ 1 + α(G) − m(G)`.
-/

namespace WrittenOnTheWallII.GraphConjecture7

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- `matchingNumber G` is the size of a maximum matching of `G`,
returned as a natural number.  A *matching* is a set of pairwise
vertex-disjoint edges; the matching number is the maximum cardinality
of such a set. -/
noncomputable def matchingNumber (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  let matchings := { M : Subgraph G | M.IsMatching }
  sSup (Set.image (fun M => M.edgeSet.toFinset.card) matchings)

/--
WOWII [Conjecture 7](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`Ls(G) ≥ 1 + α(G) − m(G)`
where `Ls(G)` is the maximum number of leaves over all spanning trees,
`α(G) = G.indepNum` is the independence number, and
`m(G)` is the size of a maximum matching.
-/
@[category research solved, AMS 5]
theorem conjecture7 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    1 + (G.indepNum : ℝ) - m G ≤ Ls G := by
  sorry

-- Sanity checks

/-- In the complete graph `K₃`, every edge is in a matching of size 1,
so `matchingNumber K₃ = 1`. -/
@[category test, AMS 5]
example : matchingNumber (⊤ : SimpleGraph (Fin 3)) = 1 := by
  unfold matchingNumber
  sorry

/-- In the path graph `P₃` (edges 0–1 and 1–2), the maximum matching has size 1
(we can pick either edge, but the two edges share vertex 1). -/
@[category test, AMS 5]
example : matchingNumber
    (SimpleGraph.fromEdgeSet {s(0, 1), s(1, 2)} : SimpleGraph (Fin 3)) = 1 := by
  unfold matchingNumber
  sorry

/-- In the complete graph `K₄`, a perfect matching has 2 edges, so `matchingNumber K₄ = 2`. -/
@[category test, AMS 5]
example : matchingNumber (⊤ : SimpleGraph (Fin 4)) = 2 := by
  unfold matchingNumber
  sorry

end WrittenOnTheWallII.GraphConjecture7
