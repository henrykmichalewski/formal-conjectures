/-
Copyright 2026 The Formal Conjectures Authors.

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
# Erdős Problem 593

*Reference:* [erdosproblems.com/593](https://www.erdosproblems.com/593)

*References for known results:*
- [EGH75] Erdős, Paul and Galvin, Fred and Hajnal, András, On set-systems having large
  chromatic number and not containing prescribed subsystems.
  Infinite and finite sets (Colloq., Keszthely, 1973; dedicated to P. Erdős on his 60th
  birthday), Vol. I. Colloq. Math. Soc. János Bolyai 10, North-Holland (1975), 425–513.
- [Er95d] Erdős, Paul, Some of my favourite problems in various branches of combinatorics.
  Matematiche (Catania) 47 (1992), no. 2, 231–240 (1995).

**Problem (Erdős, $500)**: Characterize those finite 3-uniform hypergraphs which appear in
every 3-uniform hypergraph of chromatic number $> \aleph_0$.

**Background:** A hypergraph $H = (V, E)$ is **$r$-uniform** if every hyperedge $e \in E$
has exactly $r$ vertices. The **chromatic number** $\chi(H)$ of a hypergraph is the minimum
number of colors needed to color its vertices so that no hyperedge is monochromatic. A finite
$r$-uniform hypergraph $F$ is **obligatory** (for the class of $r$-uniform hypergraphs with
chromatic number $> \aleph_0$) if every $r$-uniform hypergraph with chromatic number
$> \aleph_0$ contains a copy of $F$ as a sub-hypergraph.

**Known (graph case, $r = 2$, Erdős–Galvin–Hajnal [EGH75]):** For graphs (2-uniform
hypergraphs), the problem is completely solved:
- A graph of chromatic number $\geq \aleph_1$ must contain all finite bipartite graphs.
- No fixed odd cycle is obligatory: for every odd $k$, there exists a graph with chromatic
  number $\aleph_1$ that contains no cycle of length $k$.

The 3-uniform case remains **open**.

**Formalization notes:** We represent a 3-uniform hypergraph on vertex type `V` as a pair
`(edges, uniform)` where `edges : Set (Finset V)` and every edge has cardinality 3. A proper
coloring sends vertices to colors such that no hyperedge is monochromatic. The chromatic
cardinal is the infimum of cardinalities of color types admitting a proper coloring. A finite
hypergraph `F` *appears* in `H` if there is an injective vertex map carrying edges of `F`
into edges of `H`.

We work at universe level `Type` (universe 0) throughout to avoid universe metavariable issues.
-/

open Cardinal Set SimpleGraph

namespace Erdos593

/- ## Definitions for 3-uniform hypergraphs -/

/-- A **3-uniform hypergraph** on vertex type `V` is a set of 3-element `Finset`s.
Each element of `edges` is a hyperedge, and `uniform` ensures each has exactly 3 vertices. -/
structure ThreeUniformHypergraph (V : Type) where
  /-- The set of hyperedges: each edge is a 3-element finset of vertices. -/
  edges : Set (Finset V)
  /-- Every hyperedge has exactly 3 vertices. -/
  uniform : ∀ e ∈ edges, e.card = 3

/-- A **proper coloring** of a 3-uniform hypergraph `H` by a color type `C` is a vertex
coloring such that no hyperedge is monochromatic (all three vertices receive the same color). -/
def ThreeUniformHypergraph.IsProperColoring {V : Type} (H : ThreeUniformHypergraph V)
    {C : Type} (f : V → C) : Prop :=
  ∀ e ∈ H.edges, ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v

/-- The **chromatic cardinal** of a 3-uniform hypergraph `H` is the infimum of cardinalities
of color types admitting a proper coloring. We use `Cardinal.{0}` matching `Type`. -/
noncomputable def ThreeUniformHypergraph.chromaticCardinal {V : Type}
    (H : ThreeUniformHypergraph V) : Cardinal.{0} :=
  sInf {κ : Cardinal.{0} | ∃ (C : Type), #C = κ ∧ ∃ f : V → C, H.IsProperColoring f}

/-- A finite 3-uniform hypergraph `F` **appears** in `H` (as a sub-hypergraph) if there
exists an injective vertex map `φ : W → V` that sends every hyperedge of `F` to a hyperedge
of `H`. -/
def ThreeUniformHypergraph.Appears {W V : Type} [DecidableEq V]
    (F : ThreeUniformHypergraph W) (H : ThreeUniformHypergraph V) : Prop :=
  ∃ φ : W → V, Function.Injective φ ∧
    ∀ e ∈ F.edges, e.image φ ∈ H.edges

/-- A finite 3-uniform hypergraph `F` on a `Fintype` vertex type is **obligatory** if it
appears in every 3-uniform hypergraph (on a `Type`-valued vertex set) whose chromatic
cardinal exceeds `ℵ₀`. -/
def IsObligatory {W : Type} [Fintype W] (F : ThreeUniformHypergraph W) : Prop :=
  ∀ (V : Type) [DecidableEq V] (H : ThreeUniformHypergraph V),
    ℵ₀ < H.chromaticCardinal → F.Appears H

/- ## Main open problem -/

/--
**Erdős Problem 593 ($500)**: Characterize those finite 3-uniform hypergraphs which appear in
every 3-uniform hypergraph of chromatic number $> \aleph_0$.

*Original statement (erdosproblems.com/593)*: "Characterize those finite 3-uniform hypergraphs
which appear in every 3-uniform hypergraph of chromatic number $> \aleph_0$."

**Background:** For graphs (2-uniform hypergraphs), the analogous problem is completely solved
by Erdős, Galvin, and Hajnal [EGH75]: the obligatory finite graphs are precisely the finite
bipartite graphs. No fixed odd cycle is obligatory. The 3-uniform case is open.

**Formalization:** We express the problem as asking for a characterization predicate `P` for
obligatory finite 3-uniform hypergraphs (formalized via `IsObligatory`). The `answer(sorry)`
records that no such characterization is known.

**Prize:** \$500 (see erdosproblems.com/593).

**Status:** OPEN.
-/
@[category research open, AMS 5]
theorem erdos_593 : answer(sorry) ↔
    ∃ (P : ∀ (W : Type) [Fintype W], ThreeUniformHypergraph W → Prop),
      ∀ (W : Type) [Fintype W] (F : ThreeUniformHypergraph W),
        IsObligatory F ↔ P W F := by
  sorry

/- ## Variants and partial results -/

/--
**Graph analogue — bipartite graphs are obligatory (solved, Erdős–Galvin–Hajnal [EGH75])**:
For the 2-uniform (graph) case, a graph of chromatic cardinal $> \aleph_0$ must contain all
finite bipartite graphs. Specifically, for every finite bipartite graph `F` and every graph
`G` with chromatic cardinal $> \aleph_0$, there is a graph homomorphism from `F` to `G`.

**Status:** SOLVED [EGH75].
-/
@[category research solved, AMS 5]
theorem erdos_593.variants.graph_case_bipartite_obligatory :
    answer(True) ↔
    ∀ (V : Type*) (G : SimpleGraph V),
      ℵ₀ < G.chromaticCardinal →
      ∀ (W : Type*) [Fintype W] (F : SimpleGraph W), F.IsBipartite →
        Nonempty (F →g G) := by
  simp only [true_iff]
  -- This is the Erdős–Galvin–Hajnal theorem [EGH75].
  sorry

/--
**Graph analogue — no odd cycle is obligatory (solved, Erdős–Galvin–Hajnal [EGH75])**:
For every odd $k \geq 3$, there exists a graph with chromatic cardinal $\aleph_1$ that
contains no cycle of length $k$. This shows the class of obligatory graphs is strictly
smaller than all finite graphs.

**Status:** SOLVED [EGH75].
-/
@[category research solved, AMS 5]
theorem erdos_593.variants.graph_case_no_odd_cycle :
    answer(True) ↔
    ∀ k : ℕ, Odd k → 3 ≤ k →
      ∃ (V : Type*) (G : SimpleGraph V),
        G.chromaticCardinal = ℵ_ 1 ∧
        IsEmpty (cycleGraph k →g G) := by
  simp only [true_iff]
  -- This is the Erdős–Galvin–Hajnal theorem [EGH75].
  sorry

/--
**Vertices must be uncountable**: Every 3-uniform hypergraph with chromatic cardinal
$> \aleph_0$ must have an uncountable vertex set.

**Proof:** If `V` is countable, there exists an injection `φ : V → ℕ`. Using distinct natural
numbers as colors gives a proper coloring, so $\chi(H) \leq \#\mathbb{N} = \aleph_0$,
contradicting $\chi(H) > \aleph_0$.
-/
@[category undergraduate, AMS 5]
theorem erdos_593.variants.uncountable_vertices_if_large_chromatic
    {V : Type} (H : ThreeUniformHypergraph V) (hχ : ℵ₀ < H.chromaticCardinal) :
    ¬ Countable V := by
  intro hcount
  -- Since V is countable, there is an injection φ : V → ℕ.
  obtain ⟨φ, hφ⟩ := Countable.exists_injective_nat V
  -- The injection φ is a proper coloring using ℕ as the color type:
  -- each edge has card 3, so we can extract two distinct vertices with distinct images.
  have hprop : H.IsProperColoring φ := by
    intro e he
    -- Extract 3 distinct elements from e using H.uniform.
    have hcard : e.card = 3 := H.uniform e he
    -- Since e.card = 3 ≥ 2, there exist two distinct elements u ≠ v in e.
    have hge : 1 < e.card := by omega
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hge
    exact ⟨u, hu, v, hv, fun heq => huv (hφ heq)⟩
  -- So χ(H) ≤ #ℕ = ℵ₀.
  have hle : H.chromaticCardinal ≤ ℵ₀ := by
    apply csInf_le
    · -- The set {κ | ∃ C, #C = κ ∧ ∃ f, proper} is bounded below by 0.
      exact ⟨0, fun _ ⟨_, _, _, _⟩ => Cardinal.zero_le _⟩
    · exact ⟨ℕ, Cardinal.mk_nat, φ, hprop⟩
  exact absurd (lt_of_lt_of_le hχ hle) (lt_irrefl _)

/--
**No hyperedges implies chromatic cardinal ≤ 1**: A 3-uniform hypergraph with no edges can
be properly colored with a single color, so its chromatic cardinal is at most 1. In
particular, $\chi(H) > \aleph_0$ implies `H` has at least one hyperedge.
-/
@[category undergraduate, AMS 5]
theorem erdos_593.variants.nonempty_edges_if_large_chromatic
    {V : Type} (H : ThreeUniformHypergraph V) (hχ : ℵ₀ < H.chromaticCardinal) :
    H.edges.Nonempty := by
  by_contra hempty
  push_neg at hempty
  -- H has no edges (hempty : H.edges = ∅), so any coloring is proper.
  have hprop : H.IsProperColoring (fun _ : V => (0 : Fin 1)) := by
    intro e he
    rw [hempty] at he
    exact (Set.mem_empty_iff_false e).mp he |>.elim
  -- Hence χ(H) ≤ 1 < ℵ₀.
  have hle : H.chromaticCardinal ≤ 1 := by
    apply csInf_le
    · exact ⟨0, fun _ ⟨_, _, _, _⟩ => Cardinal.zero_le _⟩
    · refine ⟨Fin 1, ?_, fun _ => 0, hprop⟩
      simp
  have h1le : (1 : Cardinal) ≤ ℵ₀ := le_of_lt Cardinal.one_lt_aleph0
  exact absurd (lt_of_lt_of_le hχ (hle.trans h1le)) (lt_irrefl _)

/--
**Monotonicity of the obligatory property**: If `F₁` appears in `F₂` and `F₂` is obligatory,
then `F₁` is also obligatory.

**Proof:** For any `H` with $\chi(H) > \aleph_0$, since `F₂` is obligatory, `F₂` appears
in `H` via some injection `φ₂`. Since `F₁` appears in `F₂` via `φ₁`, the composition
`φ₂ ∘ φ₁` witnesses that `F₁` appears in `H`.
-/
@[category undergraduate, AMS 5]
theorem erdos_593.variants.obligatory_monotone
    {W₁ W₂ : Type} [Fintype W₁] [Fintype W₂] [DecidableEq W₂]
    {F₁ : ThreeUniformHypergraph W₁} {F₂ : ThreeUniformHypergraph W₂}
    (h12 : F₁.Appears F₂) (hObl : IsObligatory F₂) :
    IsObligatory F₁ := by
  intro V _hV H hχ
  obtain ⟨φ₂, hφ₂_inj, hφ₂_edge⟩ := hObl V H hχ
  obtain ⟨φ₁, hφ₁_inj, hφ₁_edge⟩ := h12
  refine ⟨φ₂ ∘ φ₁, hφ₂_inj.comp hφ₁_inj, fun e he => ?_⟩
  -- e.image (φ₂ ∘ φ₁) = (e.image φ₁).image φ₂ by Finset.image_image
  -- (e.image φ₁).image φ₂ = e.image (φ₂ ∘ φ₁) by Finset.image_image
  have heq : e.image (φ₂ ∘ φ₁) = (e.image φ₁).image φ₂ := by
    rw [Finset.image_image]
  rw [heq]
  exact hφ₂_edge _ (hφ₁_edge e he)

/--
**The empty hypergraph is trivially obligatory**: The 3-uniform hypergraph on `PEmpty` (no
vertices, no edges) appears in every hypergraph via the empty injection.

This degenerate case confirms the definition is well-formed.
-/
@[category undergraduate, AMS 5]
theorem erdos_593.variants.empty_hypergraph_obligatory :
    IsObligatory (W := PEmpty) ⟨∅, fun _ h => (Set.mem_empty_iff_false _).mp h |>.elim⟩ := by
  intro V _hV H _hχ
  exact ⟨IsEmpty.elim inferInstance, Function.injective_of_subsingleton _,
    fun _ h => (Set.mem_empty_iff_false _).mp h |>.elim⟩

end Erdos593
