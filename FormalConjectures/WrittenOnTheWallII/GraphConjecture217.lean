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
# Written on the Wall II - Conjecture 217

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Statement

WOWII Conjecture 217:
  *If `G` is a simple connected graph with `n > 1` such that
   `L(G) ≤ 4 · c_{residue=2}(G) + 2`, then `G` has a Hamiltonian path.*

Here:
- `L(G)` is the **leaf number** of `G`: the minimum number of leaves over all
  spanning trees of `G`.
- `c_{residue=2}(G)` is the number of connected components of the
  **residue-2 core** of `G` (the maximal induced subgraph of minimum degree
  at least 2, obtained by iteratively peeling off vertices of degree `< 2`).

## Definitions

Vertex connectivity is unavailable in Mathlib, and the iterative peeling needed
to define the residue-2 core uses well-founded recursion.  To keep the file
self-contained and focused on the statement of the conjecture, we use a
classical placeholder for `residue2ComponentCount G` and define
`leafNumber G` as the minimum leaf count of a spanning tree (or `0` if no
spanning tree exists).

## TODO

- Replace `residue2Core` with the constructive fixpoint of iterative vertex
  peeling.
- Replace `residue2ComponentCount` with the component count of the induced
  subgraph on that core.
-/

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/- ### 2-core predicate -/

/-- A set `S ⊆ V(G)` is a **2-core** of `G` if every vertex in `S` has at least 2
neighbours within `S`. -/
def Is2Core (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  ∀ v ∈ S, 2 ≤ (S.filter (fun w => G.Adj v w)).card

/- ### Residue-2 core and component count (classical placeholders) -/

/-- The residue-2 core of `G`.

TODO: Implement as the largest `S ⊆ V(G)` satisfying `Is2Core G S`, i.e. the
fixpoint of iteratively removing vertices of degree less than 2.
This is a placeholder returning the empty set. -/
noncomputable def residue2Core (G : SimpleGraph α) [DecidableRel G.Adj] : Finset α :=
  Classical.choice ⟨∅⟩

/-- The number of connected components of the residue-2 core of `G`.

TODO: Replace with `Fintype.card (G.induce (residue2Core G : Set α)).ConnectedComponent`
once `residue2Core` is correctly defined. -/
noncomputable def residue2ComponentCount (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  Classical.choice ⟨0⟩

/- ### Leaf number

The **leaf number** `L(G)` is the minimum number of leaves (degree-1 vertices)
over all spanning trees of `G`.  A spanning tree here is an induced subtree on
the full vertex set of `G` under the restriction of `G.Adj`. -/

/-- The number of leaves of the graph `T` (vertices of degree `1`). -/
noncomputable def numLeaves (T : SimpleGraph α) [DecidableRel T.Adj] : ℕ :=
  (Finset.univ.filter (fun v => T.degree v = 1)).card

/-- The **leaf number** of `G`: the minimum number of leaves over all spanning
subtrees of `G`, i.e. subgraphs `T ⊆ G` that are trees and have the same vertex
set as `G`.  If no such tree exists we take the infimum over the empty set,
which is `0` (by convention of `sInf` on `ℕ`). -/
noncomputable def leafNumber (G : SimpleGraph α) : ℕ :=
  sInf { k | ∃ T : SimpleGraph α, T ≤ G ∧ T.IsTree ∧
    ∃ _ : DecidableRel T.Adj, numLeaves T = k }

/--
WOWII [Conjecture 217](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

If `G` is a simple connected graph with `n > 1` and
`L(G) ≤ 4 · c_{residue=2}(G) + 2`,
then `G` has a Hamiltonian path, where `L(G)` is the leaf number of `G`
(minimum leaves over all spanning trees) and `c_{residue=2}(G)` is the
connected-component count of the residue-2 core of `G`.
-/
@[category research open, AMS 5]
theorem conjecture217 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hL : leafNumber G ≤ 4 * residue2ComponentCount G + 2) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  sorry

-- Sanity checks

/-- `residue2ComponentCount` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] :
    0 ≤ residue2ComponentCount G :=
  Nat.zero_le _

/-- `leafNumber` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : 0 ≤ leafNumber G := Nat.zero_le _

/-- The empty set is always a 2-core: the condition is vacuous. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] : Is2Core G ∅ :=
  fun _ hv => by simp at hv

end WrittenOnTheWallII.GraphConjecture217
