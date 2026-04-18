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
# Written on the Wall II - Conjecture 217 (Residue-2 Core)

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

The **residue-2 core** of a graph `G` is obtained by iteratively removing vertices
of degree less than 2 until no such vertex remains.  Equivalently, it is the
maximal induced subgraph of `G` with minimum degree ≥ 2.  If no non-empty 2-core
exists (e.g., for forests), the core is empty.

The **residue-2 component count** `residue2ComponentCount G` is the number of
connected components of this residue-2 core.

## TODO

A fully constructive definition of `residue2Core` requires a well-founded
recursion on the cardinality of the remaining vertex set.  We provide classical
placeholders here and mark the constructive implementations as TODO.

## Conjecture 217

WOWII Conjecture 217 involves `c_{residue=2}(G)`, the component count of the
residue-2 core.  We state the natural conjectured bound:
  `residue2ComponentCount G ≤ G.indepNum`.
Each component of the 2-core contains a cycle, and the collection of these
cycle-components is bounded above by the independence number of `G`.
-/

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-!
### 2-core predicate
-/

/-- A set `S ⊆ V(G)` is a **2-core** of `G` if every vertex in `S` has at least 2
neighbours within `S`. -/
def Is2Core (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  ∀ v ∈ S, 2 ≤ (S.filter (fun w => G.Adj v w)).card

/-!
### Residue-2 core and component count (classical placeholders)

TODO: Replace `residue2Core` with the constructive fixpoint of iterative vertex
peeling, and `residue2ComponentCount` with the component count of the induced
subgraph on that core.
-/

/-- The residue-2 core of `G`.

TODO: Implement as the largest `S ⊆ V(G)` satisfying `Is2Core G S`.
This is a placeholder returning the empty set.
-/
noncomputable def residue2Core (G : SimpleGraph α) [DecidableRel G.Adj] : Finset α :=
  Classical.choice ⟨∅⟩

/-- The number of connected components of the residue-2 core of `G`.

TODO: Replace with `Fintype.card (G.induce (residue2Core G : Set α)).ConnectedComponent`
once `residue2Core` is correctly defined.
-/
noncomputable def residue2ComponentCount (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  Classical.choice ⟨0⟩

/--
WOWII [Conjecture 217](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
  `residue2ComponentCount G ≤ G.indepNum`.
The number of connected components of the residue-2 core does not exceed the
independence number of `G`.

Each component of the 2-core contains a cycle and contributes at least one
vertex to every maximum independent set.

**Note:** This conjecture is stated for the placeholder definition of
`residue2ComponentCount`; it should be revisited once the definitions are
made constructively correct.
-/
@[category research open, AMS 5]
theorem conjecture217 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    residue2ComponentCount G ≤ G.indepNum := by
  sorry

-- Sanity checks

/-- `residue2ComponentCount` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] :
    0 ≤ residue2ComponentCount G :=
  Nat.zero_le _

/-- The empty set is always a 2-core: the condition is vacuous. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] : Is2Core G ∅ :=
  fun _ hv => by simp at hv

/-- In `K₃`, the full vertex set `{0,1,2}` is a 2-core: every vertex `v` has
exactly 2 neighbours in `univ`. -/
@[category test, AMS 5]
example : Is2Core (⊤ : SimpleGraph (Fin 3)) Finset.univ := by
  intro _ _; sorry

/-- `residue2ComponentCount` on a path graph is nonneg. -/
@[category test, AMS 5]
example : 0 ≤ residue2ComponentCount
    (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)) :=
  Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture217
