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

import FormalConjectures.WrittenOnTheWallII.GraphConjecture19
import Mathlib.Combinatorics.SimpleGraph.Coloring

open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture19

-- Adapting the user's disproof attempt
-- The user's script seems to try to prove that K3 (ULift (Fin 3) with top) is a counterexample.
-- We expect this to fail if Conjecture 19 holds for K3.

theorem disproof_attempt :
    ∃ (G : SimpleGraph (ULift (Fin 3))), G.Connected ∧
    ¬ (FLOOR ((∑ v ∈ Finset.univ, ecc G v) / (Fintype.card (ULift (Fin 3)) : ℝ) + sSup (Set.range (indepNeighbors G))) ≤ b G) := by
  -- Construct K3
  let G : SimpleGraph (ULift (Fin 3)) := ⊤
  use G
  constructor
  · -- Connected
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    use (ULift.up 0)
    intro v
    by_cases h : v = ULift.up 0
    · rw [h]; use SimpleGraph.Walk.nil
    · use (SimpleGraph.Walk.cons (by simp; exact h) SimpleGraph.Walk.nil)
  · -- Inequality failure
    intro h_le
    -- We expect h_le to be true (2 <= 2), so this proof should fail to derive False
    -- unless the values are different.
    simp at h_le
    -- Let's calculate values
    have h_b : b G = 2 := by
      -- b(K3) = 2
      sorry
    have h_ecc : ∀ v, ecc G v = 1 := by
      intro v
      sorry
    have h_indep : ∀ v, indepNeighbors G v = 1 := by
      intro v
      sorry
    -- LHS = floor(3/3 + 1) = 2
    -- RHS = 2
    -- 2 <= 2 is True.
    -- So we cannot prove False from h_le.
    sorry

end WrittenOnTheWallII.GraphConjecture19
