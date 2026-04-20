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
# Written on the Wall II - Conjecture 31

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture31

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The average eccentricity over a set of vertices `S`, i.e. the average of
`eccentricity G v` (as a natural number) for `v ∈ S`.  Returns 0 if `S` is
empty.  Here we interpret `ℕ∞`-eccentricity by taking the value 0 when the
eccentricity is `⊤` (disconnected component). -/
noncomputable def eccavg (G : SimpleGraph α) (S : Set α) : ℝ :=
  let Sf := S.toFinset
  if h : Sf.Nonempty then
    (∑ v ∈ Sf, ((eccentricity G v).toNat : ℝ)) / (Sf.card : ℝ)
  else 0

/--
WOWII [Conjecture 31](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`path(G) ≥ ⌈distavg(G, A) + 0.5 · eccavg(M)⌉`
where `path(G)` is the floor of the average distance, `A` is the set of
minimum-degree vertices, `M` is the set of maximum-degree vertices,
`distavg(G, A)` is the average distance from all vertices to `A`, and
`eccavg(M)` is the average eccentricity of the vertices in `M`.
-/
@[category research solved, AMS 5]
theorem conjecture31 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let A : Set α := {v | G.degree v = G.minDegree}
    let M : Set α := {v | G.degree v = G.maxDegree}
    Int.ceil (distavg G A + (1 / 2) * eccavg G M) ≤ (path G : ℤ) := by
  sorry

-- Sanity checks

/-- The `path G` invariant cast to ℤ is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (path G : ℤ) := Int.natCast_nonneg _

/-- `eccavg` over an empty set is 0. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : eccavg G ∅ = 0 := by
  unfold eccavg
  simp

end WrittenOnTheWallII.GraphConjecture31
