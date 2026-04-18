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
# Written on the Wall II - Conjecture 36

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture36

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 36](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`path(G) ≥ ⌈1 + √(n(G) mod Δ(Ḡ))⌉`
where `path(G)` is the floor of the average distance, `n(G)` is the number of
vertices, `Ḡ = Gᶜ` is the complement graph, and `Δ(Ḡ) = maxDegree(Ḡ)` is the
maximum degree of the complement.  When `Δ(Ḡ) = 0` we interpret `n mod 0 = 0`
(Lean's default natural number `%`).
-/
@[category research open, AMS 5]
theorem conjecture36 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let Gc := Gᶜ
    let deltaC := Gc.maxDegree
    let nG := Fintype.card α
    Int.ceil (1 + Real.sqrt ((nG % deltaC : ℕ) : ℝ)) ≤ (path G : ℤ) := by
  sorry

-- Sanity checks

/-- The complement of `K₃` has max degree 0. -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 3))ᶜ.maxDegree = 0 := by decide +native

/-- The `path G` invariant cast to ℤ is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (path G : ℤ) := Int.natCast_nonneg _

end WrittenOnTheWallII.GraphConjecture36
