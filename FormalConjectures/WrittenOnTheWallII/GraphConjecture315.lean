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
# Written on the Wall II - Conjecture 315

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

open Classical

namespace WrittenOnTheWallII.GraphConjecture315

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-
## Definitions for well totally dominated graphs

A *total dominating set* of `G` is a set `S` of vertices such that every vertex of `G`
(including vertices in `S`) has a neighbor in `S`. A total dominating set `S` is
*minimal* if no proper subset of `S` is also a total dominating set.

A graph `G` is *well totally dominated* if every minimal total dominating set
has the same cardinality; equivalently, the total domination number equals the
maximum cardinality of a minimal total dominating set.

The *pendant vertices* (also called *leaves*) of `G` are the vertices of degree 1.
-/

/-- A set `S` is a total dominating set of `G` if every vertex has a neighbor in `S`. -/
def IsTotalDominatingSet (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  ∀ v : α, ∃ w ∈ S, G.Adj v w

/-- A total dominating set `S` is minimal if no proper subset of `S` is also a
total dominating set. -/
def IsMinimalTotalDominatingSet (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  IsTotalDominatingSet G S ∧
  ∀ T : Finset α, T ⊂ S → ¬IsTotalDominatingSet G T

/-- A graph `G` is well totally dominated if every minimal total dominating set
has the same cardinality. -/
def isWellTotallyDominated (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  ∀ S T : Finset α,
    IsMinimalTotalDominatingSet G S →
    IsMinimalTotalDominatingSet G T →
    S.card = T.card

/-- The set of pendant vertices (leaves) of `G`: vertices of degree 1. -/
noncomputable def pendantVertices (G : SimpleGraph α) [DecidableRel G.Adj] : Finset α :=
  Finset.univ.filter (fun v => G.degree v = 1)

/--
WOWII [Conjecture 315](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

Let `G` be a simple connected graph and let `P` denote the set of pendant vertices
(vertices of degree 1). If `α(G) = |P|`, then `G` is well totally dominated.
-/
@[category research open, AMS 5]
theorem conjecture315 (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (h : G.indepNum = (pendantVertices G).card) :
    isWellTotallyDominated G := by
  sorry

-- Sanity checks

/-- In the path graph `P₃` (0-1-2), vertices 0 and 2 have degree 1,
so there are exactly 2 pendant vertices. -/
@[category test, AMS 5]
example : (pendantVertices (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3))).card = 2 := by
  unfold pendantVertices
  decide +native

/-- In `K₃`, all vertices have degree 2, so there are no pendant vertices. -/
@[category test, AMS 5]
example : (pendantVertices (⊤ : SimpleGraph (Fin 3))).card = 0 := by
  unfold pendantVertices
  decide +native

end WrittenOnTheWallII.GraphConjecture315
