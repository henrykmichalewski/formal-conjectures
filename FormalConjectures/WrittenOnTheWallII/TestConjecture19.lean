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

def K3 : SimpleGraph (Fin 3) := completeGraph (Fin 3)

lemma K3_b : b K3 = 2 := by sorry

lemma K3_ecc (v : Fin 3) : ecc K3 {v} = 1 := by sorry

lemma K3_indepNeighbors (v : Fin 3) : indepNeighbors K3 v = 1 := by sorry

theorem K3_not_counterexample :
    FLOOR ((∑ v ∈ Finset.univ, ecc K3 {v}) / (Fintype.card (Fin 3) : ℝ) + sSup (Set.range (fun (v : Fin 3) => indepNeighbors K3 v)))
      ≤ b K3 := by
  rw [K3_b]
  have h_ecc : ∀ v, ecc K3 {v} = 1 := K3_ecc
  simp [h_ecc]
  have h_indep : ∀ v, indepNeighbors K3 v = 1 := K3_indepNeighbors
  simp [h_indep]
  rw [FLOOR]
  norm_num
