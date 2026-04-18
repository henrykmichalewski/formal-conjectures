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
import FormalConjectures.WrittenOnTheWallII.GraphConjecture315

/-!
# Written on the Wall II - Conjecture 291

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

For a vertex `v` in a graph `G`, **T(v)** is the number of triangles (3-cliques) incident
to `v`, i.e., the number of 3-element cliques in `G` that contain `v`.

The **triangle-frequency of the minimum** is the number of vertices that achieve the
minimum value of T(v).

**k** (the first zero step in the Havel-Hakimi process) is defined here as
`n - residue(G)` using the existing `residue` function.

**Conjecture 291:** For a simple connected graph `G` with `n > 2`,
`γ_t(G) ≤ k + frequency(t_min(v))`
where `γ_t(G)` is the total domination number, `k` is the Havel-Hakimi zero step,
and `frequency(t_min(v))` is the number of vertices achieving the minimum triangle count.
-/

namespace WrittenOnTheWallII.GraphConjecture291

open Classical SimpleGraph WrittenOnTheWallII.GraphConjecture315

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The number of triangles (3-cliques) in `G` that are incident to vertex `v`.
This is the number of 3-element cliques containing `v`. -/
noncomputable def numTrianglesAtVertex (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : ℕ :=
  ((G.cliqueFinset 3).filter (fun s => v ∈ s)).card

/-- The minimum number of triangles incident to any vertex, over all vertices of `G`. -/
noncomputable def minTrianglesAtVertex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (numTrianglesAtVertex G)

/-- The number of vertices achieving the minimum triangle count. -/
noncomputable def freqMinTriangles (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun v => numTrianglesAtVertex G v = minTrianglesAtVertex G)).card

/-- The first step in the Havel-Hakimi process at which a zero appears.
Defined as `n - residue(G)` using the existing `residue` function. -/
noncomputable def havelHakimiZeroStep (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  Fintype.card α - residue G

/--
WOWII [Conjecture 291](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G` with `n > 2`,
`γ_t(G) ≤ k + frequency(t_min(v))`
where:
- `γ_t(G)` is the total domination number,
- `k` is the first step in which a zero appears in the Havel-Hakimi process,
- `frequency(t_min(v))` is the number of vertices achieving the minimum triangle count.
-/
@[category research open, AMS 5]
theorem conjecture291 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hn : 2 < Fintype.card α) :
    G.totalDominationNumber ≤
    havelHakimiZeroStep G + freqMinTriangles G := by
  sorry

-- Sanity checks

/-- In `K₃`, every vertex is in exactly 1 triangle. -/
@[category test, AMS 5]
example : numTrianglesAtVertex (⊤ : SimpleGraph (Fin 3)) (0 : Fin 3) = 1 := by
  unfold numTrianglesAtVertex
  decide +native

/-- In the path `P₃`, vertex 1 has no triangles incident to it
(0 and 2 are neighbors of 1 but not adjacent to each other). -/
@[category test, AMS 5]
example : numTrianglesAtVertex
    (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)) (1 : Fin 3) = 0 := by
  unfold numTrianglesAtVertex
  decide +native

/-- In `K₃`, the minimum triangle count is 1 (every vertex has 1 triangle). -/
@[category test, AMS 5]
example : minTrianglesAtVertex (⊤ : SimpleGraph (Fin 3)) = 1 := by
  unfold minTrianglesAtVertex numTrianglesAtVertex
  decide +native

/-- `havelHakimiZeroStep` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] : 0 ≤ havelHakimiZeroStep G :=
  Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture291
