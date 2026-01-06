import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-- The relation for the Grötzsch graph. -/
def GrotzschRel (i j : Fin 11) : Bool :=
  match i.val, j.val with
  -- Outer cycle
  | 0, 1 | 1, 0 => true
  | 1, 2 | 2, 1 => true
  | 2, 3 | 3, 2 => true
  | 3, 4 | 4, 3 => true
  | 4, 0 | 0, 4 => true
  -- Outer to inner
  | 5, 1 | 1, 5 => true
  | 5, 4 | 4, 5 => true
  | 6, 2 | 2, 6 => true
  | 6, 0 | 0, 6 => true
  | 7, 3 | 3, 7 => true
  | 7, 1 | 1, 7 => true
  | 8, 4 | 4, 8 => true
  | 8, 2 | 2, 8 => true
  | 9, 0 | 0, 9 => true
  | 9, 3 | 3, 9 => true
  -- Inner to center
  | 10, 5 | 5, 10 => true
  | 10, 6 | 6, 10 => true
  | 10, 7 | 7, 10 => true
  | 10, 8 | 8, 10 => true
  | 10, 9 | 9, 10 => true
  | _, _ => false

/-- The Grötzsch graph. -/
def GrotzschGraph : SimpleGraph (Fin 11) :=
  SimpleGraph.fromRel (fun i j => GrotzschRel i j)

instance : DecidableRel GrotzschGraph.Adj := fun i j =>
  decidable_of_iff ((GrotzschRel i j && i != j) = true) (by
    simp [GrotzschGraph, SimpleGraph.fromRel_adj, GrotzschRel]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
    rfl
  )

/-- The relation for the F4 graph. -/
def F4Rel (i j : Fin 19) : Bool :=
  let i_val := i.val
  let j_val := j.val
  -- Base: Grötzsch graph on 0-10
  if hi : i_val < 11 then
    if hj : j_val < 11 then
      GrotzschRel ⟨i_val, hi⟩ ⟨j_val, hj⟩
    else false
  -- Step 2: Vertex 11 connected to 0 and 2 (non-adjacent vertices of degree 4)
  else if (i_val = 11 && (j_val = 0 || j_val = 2)) || (j_val = 11 && (i_val = 0 || i_val = 2)) then
    true
  -- Step 3: Vertices 12, 13, 14 connected to vertices of degree 3 (5, 6, 7, 8, 9)
  else if (i_val ∈ [12, 13, 14] && j_val ∈ [5, 6, 7, 8, 9]) || (j_val ∈ [12, 13, 14] && i_val ∈ [5, 6, 7, 8, 9]) then
    true
  -- Step 4: Vertices 15, 16, 17 connected to 12, 13, 14
  else if (i_val ∈ [15, 16, 17] && j_val ∈ [12, 13, 14]) || (j_val ∈ [15, 16, 17] && i_val ∈ [12, 13, 14]) then
    true
  -- Step 5: Vertex 18 connected to 5 and 7
  else if (i_val = 18 && (j_val = 5 || j_val = 7)) || (j_val = 18 && (i_val = 5 || i_val = 7)) then
    true
  else
    false

set_option maxHeartbeats 400000

/-- The 19-vertex graph for F(4) ≤ 19. -/
def F4Graph : SimpleGraph (Fin 19) := SimpleGraph.fromRel (fun i j => F4Rel i j)
instance : DecidableRel F4Graph.Adj := fun i j =>
  decidable_of_iff (((F4Rel i j || F4Rel j i) && i != j) = true) (by
    dsimp [F4Graph, SimpleGraph.fromRel_adj]
    simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
    rw [and_comm]
    rfl
  )

-- Test 1: Check if F4Rel is computable
#eval F4Rel 0 1

-- Test 2: Check if DecidableRel is computable
#eval F4Graph.Adj 0 1

-- Test 3: Check Colorable decidability
-- Ensure Fintype and DecidableEq are available
instance : Fintype (Fin 19) := inferInstance
instance : DecidableEq (Fin 19) := inferInstance

-- Manually define Decidable instance
instance (n : ℕ) : Decidable (F4Graph.Colorable n) :=
  decidable_of_iff (∃ (c : Fin 19 → Fin n), ∀ i j, F4Graph.Adj i j → c i ≠ c j) (by
    rw [SimpleGraph.Colorable]
    constructor
    · intro h; rcases h with ⟨c, hc⟩; exact ⟨SimpleGraph.Coloring.mk c (fun {i j} h => hc i j h)⟩
    · intro h; rcases h with ⟨c⟩; exact ⟨c.toFun, fun i j h => c.valid h⟩
  )

-- #eval decide (F4Graph.Colorable 4) -- This might be slow or fail if noncomputable

-- #eval decide (F4Graph.Colorable 4) -- This might be slow or fail if noncomputable

-- #eval decide (F4Graph.Colorable 4) -- This might be slow or fail if noncomputable

-- Test 4: Check native_decide
lemma F4Graph_colorable_4 : F4Graph.Colorable 4 := by
  native_decide
