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
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
Title: Degree sequences in triangle-free graphs
Authors: P. Erdős, S. Fajtlowicz and W. Staton,
Published in Discrete Mathematics 92 (1991) 85–88.
-/

open BigOperators
open Classical
open scoped Finset

/-- A sequence of natural numbers is **compact** on a set `S` if consecutive terms at distance
`2` differ by `1` for all `k ∈ S`. -/
def IsCompactSequenceOn (d : ℕ → ℕ) (S : Set ℕ) : Prop :=
  ∀ k ∈ S, d (k + 2) = d k + 1

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of vertices of `G` having degree `d`. -/
noncomputable def degreeFreq (G : SimpleGraph α) (d : ℕ) : ℕ :=
  #{v | G.degree v = d}

/-- The maximum number of occurrences of any term of the degree sequence of `G`. -/
noncomputable def repetitionNumber (G : SimpleGraph α) : ℕ :=
  ((Finset.univ.image (fun v => G.degree v)).image (fun d => degreeFreq G d)).max.getD 0



end SimpleGraph

section lemmas

variable (d : ℕ → ℕ) (n k r : ℕ)

/-- **Lemma 1 (a)**
If a sequence `d` is nondecreasing and no three terms are equal, then terms at distance 2 differ by at least 1. -/
@[category API, AMS 5]
lemma lemma1_a
    (h_mono : Monotone d)
    (h_pos : ∀ k, 0 < d k)
    (h_no_three : ∀ k, d (k + 2) ≠ d k) :
    1 ≤ d (k + 2) - d k := by
  have : d k ≤ d (k + 2) := h_mono (by omega)
  have := h_no_three k
  omega

/-- **Lemma 1 (b)**
If a sequence `d` is nondecreasing and no three terms are equal, then terms at distance `2 * r` differ by at least `r`. -/
@[category API, AMS 5]
lemma lemma1_b
    (h_mono : Monotone d)
    (h_pos : ∀ k, 0 < d k)
    (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    r ≤ d (k + 2 * r) - d k := by
  sorry

/-- **Lemma 2 (a)**
Inequality involving sums of terms of a nondecreasing sequence with no three terms equal. -/
@[category API, AMS 5]
lemma lemma2_a
    (h_mono : Monotone d)
    (h_pos : ∀ k, 0 < d k)
    (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    2 * n * n ≤
      ∑ i ∈ .Icc (2 * n + 1) (4 * n), d i -
        ∑ i ∈ .Icc 1 (2 * n), d i := by
  have h_count : (Finset.Icc 1 (2 * n)).card = 2 * n := by
    rw [Nat.card_Icc]
    simp
  calc
    2 * n * n = (2 * n) * n := by omega
    _ = (Finset.Icc 1 (2 * n)).card * n := by rw [h_count]
    _ = ∑ i ∈ Finset.Icc 1 (2 * n), n := by rw [Finset.sum_const]; rfl
    _ ≤ ∑ i ∈ Finset.Icc 1 (2 * n), (d (i + 2 * n) - d i) := Finset.sum_le_sum (fun i hi => by
      have h := lemma1_b d i n h_mono h_pos h_no_three
      exact h)
    _ = (∑ i ∈ Finset.Icc 1 (2 * n), d (i + 2 * n)) - ∑ i ∈ Finset.Icc 1 (2 * n), d i := by
      symm
      rw [Nat.sub_eq_of_eq_add]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.sub_add_cancel]
      apply h_mono
      omega
    _ ≤ (∑ i ∈ Finset.Icc (2 * n + 1) (4 * n), d i) - ∑ i ∈ Finset.Icc 1 (2 * n), d i := by
      apply Nat.sub_le_sub_right
      let f : ℕ ↪ ℕ := ⟨fun i => i + 2 * n, by intro i j h; exact Nat.add_right_cancel h⟩
      change ∑ i ∈ Finset.Icc 1 (2 * n), d (f i) ≤ _
      have h_eq : ∑ i ∈ Finset.Icc 1 (2 * n), d (f i) = ∑ j ∈ (Finset.Icc 1 (2 * n)).image f, d j :=
        (Finset.sum_image (fun x _ y _ h => f.inj' h)).symm
      rw [h_eq]
      apply le_of_eq
      apply Finset.sum_congr
      · ext y
        simp only [Finset.mem_image, Finset.mem_Icc]
        change (∃ a, (1 ≤ a ∧ a ≤ 2 * n) ∧ a + 2 * n = y) ↔ _
        clear f h_eq
        constructor
        · rintro ⟨i, hi, rfl⟩
          constructor <;> omega
        · intro hy
          use y - 2 * n
          constructor
          · constructor <;> omega
          · rw [Nat.sub_add_cancel (by linarith)]
      · intro _ _; rfl

/-- **Lemma 2 (b)**
Inequality involving sums of terms of a nondecreasing sequence with no three terms equal. -/
@[category API, AMS 5]
lemma lemma2_b
    (h_mono : Monotone d)
    (h_pos : ∀ k, 0 < d k)
    (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    2 * n * n + 2 * n + 1 ≤
      ∑ i ∈ .Icc (2 * n + 1) (4 * n + 1), d i -
        ∑ i ∈ .Icc 1 (2 * n), d i := by
  let S1 := ∑ i ∈ Finset.Icc 1 (2 * n), d i
  let S2 := ∑ i ∈ Finset.Icc (2 * n + 1) (4 * n), d i
  have h_split : ∑ i ∈ Finset.Icc (2 * n + 1) (4 * n + 1), d i = S2 + d (4 * n + 1) := by
    rw [Finset.sum_Icc_succ_top]
    linarith
  rw [h_split]
  change 2 * n * n + 2 * n + 1 ≤ S2 + d (4 * n + 1) - S1
  have h_diff : 2 * n * n ≤ S2 - S1 := lemma2_a d n h_mono h_pos h_no_three
  have h_le_sums : S1 ≤ S2 := by
    by_cases hn : n = 0
    · subst hn
      simp [S1, S2]
    · have : 0 < n := Nat.pos_of_ne_zero hn
      have : 0 < 2 * n * n := by
        apply Nat.mul_pos
        · apply Nat.mul_pos
          · decide
          · assumption
        · assumption
      have : 0 < S2 - S1 := Nat.lt_of_lt_of_le this h_diff
      exact le_of_lt (tsub_pos_iff_lt.mp this)
  rw [add_comm S2]
  rw [Nat.add_sub_assoc h_le_sums]
  rw [add_assoc (2 * n * n)]
  rw [add_comm (d (4 * n + 1))]
  apply Nat.add_le_add h_diff
  have h_bound := lemma1_b d 1 (2 * n) h_mono h_pos h_no_three
  have h_idx : 1 + 2 * (2 * n) = 4 * n + 1 := by ring
  rw [h_idx] at h_bound
  have h_mono_le : d 1 ≤ d (4 * n + 1) := h_mono (by linarith)
  rw [Nat.le_sub_iff_add_le h_mono_le] at h_bound
  have h_pos_1 : 1 ≤ d 1 := Nat.succ_le_of_lt (h_pos 1)
  calc
    2 * n + 1 = 1 + 2 * n := by rw [add_comm]
    _ ≤ d 1 + 2 * n := Nat.add_le_add_right h_pos_1 _
    _ = 2 * n + d 1 := by rw [add_comm]
    _ ≤ d (4 * n + 1) := h_bound

/-- **Lemma 2 (c)**
Inequality involving sums of terms of a nondecreasing sequence with no three terms equal. -/
@[category API, AMS 5]
lemma lemma2_c
    (h_mono : Monotone d)
    (h_pos : ∀ k, 0 < d k)
    (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    2 * n * n + 2 * n ≤
      (∑ i ∈ .Icc (2 * n + 2) (4 * n + 2), d i) -
        ∑ i ∈ .Icc 1 (2 * n + 1), d i := by
  let d' := fun k => d (k + 1)
  have h_mono' : Monotone d' := fun i j h => h_mono (Nat.add_le_add_right h 1)
  have h_pos' : ∀ k, 0 < d' k := fun k => h_pos (k + 1)
  have h_no_three' : ∀ i, d' (i + 2) ≠ d' i := fun i => h_no_three (i + 1)
  have h_step := lemma2_a d' n h_mono' h_pos' h_no_three'
  let S1 := ∑ i ∈ Finset.Icc 1 (2 * n), d' i
  let S2 := ∑ i ∈ Finset.Icc (2 * n + 1) (4 * n), d' i
  have h_S1 : S1 = ∑ i ∈ Finset.Icc 2 (2 * n + 1), d i := by
    apply Finset.sum_bij (fun i _ => i + 1)
    · intro i hi
      replace hi := Finset.mem_Icc.mp hi
      apply Finset.mem_Icc.mpr
      constructor <;> linarith
    · intro i _ j _ h
      linarith
    · intro b hb
      replace hb := Finset.mem_Icc.mp hb
      refine ⟨b - 1, ?_⟩
      constructor
      · apply Nat.sub_add_cancel
        linarith
      · apply Finset.mem_Icc.mpr
        constructor
        · apply Nat.le_sub_of_add_le
          linarith
        · apply Nat.sub_le_of_le_add
          linarith
    · intro i _
      rfl
  have h_S2 : S2 = ∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 1), d i := by
    apply Finset.sum_bij (fun i _ => i + 1)
    · intro i hi
      replace hi := Finset.mem_Icc.mp hi
      apply Finset.mem_Icc.mpr
      constructor <;> linarith
    · intro i _ j _ h
      linarith
    · intro b hb
      replace hb := Finset.mem_Icc.mp hb
      refine ⟨b - 1, ?_⟩
      constructor
      · apply Nat.sub_add_cancel
        linarith
      · apply Finset.mem_Icc.mpr
        constructor
        · apply Nat.le_sub_of_add_le
          linarith
        · apply Nat.sub_le_of_le_add
          linarith
    · intro i _
      rfl
  change 2 * n * n ≤ S2 - S1 at h_step
  rw [h_S1, h_S2] at h_step
  let S1_orig := ∑ i ∈ Finset.Icc 1 (2 * n + 1), d i
  let S2_orig := ∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 2), d i
  have h_S1_split : S1_orig = d 1 + ∑ i ∈ Finset.Icc 2 (2 * n + 1), d i := by
    dsimp [S1_orig]
    have h_insert : Finset.Icc 1 (2 * n + 1) = insert 1 (Finset.Icc 2 (2 * n + 1)) := by
      rw [← Finset.insert_Icc_succ_left_eq_Icc (by linarith)]
      rfl
    rw [h_insert]
    rw [Finset.sum_insert]
    · rw [Finset.mem_Icc]
      intro h
      linarith
  have h_S2_split : S2_orig = (∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 1), d i) + d (4 * n + 2) := by
    dsimp [S2_orig]
    by_cases hn : n = 0
    · subst hn
      simp
    · rw [Finset.sum_Icc_succ_top (b := 4 * n + 1) (by linarith)]
  change 2 * n * n + 2 * n ≤ S2_orig - S1_orig
  rw [h_S1_split, h_S2_split]

  -- Goal: 2nn + 2n ≤ (S2' + d(4n+2)) - (d1 + S1')
  -- Rearrange to (S2' - S1') + (d(4n+2) - d1)
  -- But subtraction order matters.
  -- (A + B) - (C + D) = (A - D) + (B - C) if D <= A and C <= B?
  -- Here A = S2', B = d(4n+2), C = d1, D = S1'.
  -- We know S1' <= S2' (from h_step).
  -- We know d1 <= d(4n+2).
  -- So (S2' + d(4n+2)) - (d1 + S1') = (S2' - S1') + (d(4n+2) - d1).
  -- Let's prove this equality.
  have h_rearrange : (∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 1), d i) + d (4 * n + 2) - (d 1 + ∑ i ∈ Finset.Icc 2 (2 * n + 1), d i) =
      ((∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 1), d i) - ∑ i ∈ Finset.Icc 2 (2 * n + 1), d i) + (d (4 * n + 2) - d 1) := by
    have h1 : ∑ i ∈ Finset.Icc 2 (2 * n + 1), d i ≤ ∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 1), d i := by
      by_cases hn : n = 0
      · subst hn; simp
      · have : 0 < n := Nat.pos_of_ne_zero hn
        have : 0 < 2 * n * n := by apply Nat.mul_pos; apply Nat.mul_pos; decide; assumption; assumption
        have : 0 < (∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 1), d i) - ∑ i ∈ Finset.Icc 2 (2 * n + 1), d i := Nat.lt_of_lt_of_le this h_step
        exact le_of_lt (tsub_pos_iff_lt.mp this)
    have h2 : d 1 ≤ d (4 * n + 2) := h_mono (by linarith)
    rw [add_comm (d 1)]
    rw [tsub_add_tsub_comm h1 h2]
  rw [h_rearrange]
  apply Nat.add_le_add h_step
  have h_bound := lemma1_b d 1 (2 * n) h_mono h_pos h_no_three
  have h_idx : 1 + 2 * (2 * n) = 4 * n + 1 := by ring
  rw [h_idx] at h_bound
  have h_mono_le : d (4 * n + 1) ≤ d (4 * n + 2) := h_mono (by linarith)
  calc
    2 * n ≤ d (4 * n + 1) - d 1 := h_bound
    _ ≤ d (4 * n + 2) - d 1 := Nat.sub_le_sub_right h_mono_le _

/-- **Lemma 2 (d)**
Inequality involving sums of terms of a nondecreasing sequence with no three terms equal. -/
@[category API, AMS 5]
lemma lemma2_d
    (h_mono : Monotone d)
    (h_pos : ∀ k, 0 < d k)
    (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    2 * n * n + 4 * n + 2 ≤
      (∑ i ∈ .Icc (2 * n + 2) (4 * n + 3), d i) -
        ∑ i ∈ .Icc 1 (2 * n + 1), d i := by
  have h_step := lemma2_c d n h_mono h_pos h_no_three
  let S1 := ∑ i ∈ Finset.Icc 1 (2 * n + 1), d i
  let S2 := ∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 2), d i
  let S2' := ∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 3), d i
  change 2 * n * n + 2 * n ≤ S2 - S1 at h_step
  rw [Finset.sum_Icc_succ_top (b := 4 * n + 2) (by linarith)]
  have h_le : S1 ≤ S2 := by
    let f : ℕ ↪ ℕ := ⟨fun i => i + (2 * n + 1), by intro i j h; simp at h; exact h⟩
    apply le_trans (b := ∑ i ∈ Finset.Icc 1 (2 * n + 1), d (f i))
    · apply Finset.sum_le_sum
      intro i hi
      apply h_mono
      simp [f]
    · rw [← Finset.sum_map]
      apply Finset.sum_le_sum_of_subset
      intro j hj
      rw [Finset.mem_map] at hj
      rcases hj with ⟨i, hi, rfl⟩
      simp [f] at hi ⊢
      constructor <;> linarith
  rw [add_comm S2, Nat.add_sub_assoc h_le, add_comm (d (4 * n + 3))]
  refine le_trans ?_ (Nat.add_le_add h_step (Nat.le_refl _))
  have h_bound := lemma1_b d 1 (2 * n + 1) h_mono h_pos h_no_three
  have h_idx : 1 + 2 * (2 * n + 1) = 4 * n + 3 := by ring
  rw [h_idx] at h_bound
  have h_d1 : 1 ≤ d 1 := h_pos 1
  omega

end lemmas

namespace SimpleGraph

local notation "f_rep" => repetitionNumber

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The degree sequence of a graph, sorted in nondecreasing order. -/
noncomputable def degreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : α => G.degree v).sort (· ≤ ·)

/-- The degree sequence of `G` is **compact** if it satisfies
`IsCompactSequenceOn` for all valid indices `k` such that `k + 2 < Fintype.card α`. -/
def HasCompactdegreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  IsCompactSequenceOn (fun k => (degreeSequence G).getD k 0) {k | k + 2 < Fintype.card α}

/-- **Theorem 1.** If a triangle-free graph has `f = 2`,
then it is bipartite, has minimum degree `1`, and
its degree sequence is compact. -/
@[category research solved, AMS 5]
theorem theorem1 (G : SimpleGraph α) [DecidableRel G.Adj] (h₁ : G.CliqueFree 3) (h₂ : repetitionNumber G = 2) :
    G.IsBipartite ∧ G.minDegree = 1 ∧ HasCompactdegreeSequence G := by
  sorry

/-- The bipartite graph construction for Lemma 3. -/
def lemma3Graph (n : ℕ) : SimpleGraph (Fin (8 * n)) where
  Adj u v :=
    (u.val < 4 * n ∧ v.val ≥ 4 * n ∧
      (let i := u.val + 1; let j' := v.val - 4 * n + 1;
       (i + j' ≥ 4 * n + 1) ∨ (i ≤ n ∧ j' ≤ n) ∨ (i ≤ n ∧ 2 * n + 1 ≤ j' ∧ j' ≤ 3 * n))) ∨
    (v.val < 4 * n ∧ u.val ≥ 4 * n ∧
      (let i := v.val + 1; let j' := u.val - 4 * n + 1;
       (i + j' ≥ 4 * n + 1) ∨ (i ≤ n ∧ j' ≤ n) ∨ (i ≤ n ∧ 2 * n + 1 ≤ j' ∧ j' ≤ 3 * n)))
  symm u v h := by
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  loopless u h := by
    rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> linarith

instance (n : ℕ) : DecidableRel (lemma3Graph n).Adj := fun u v => by
  dsimp [lemma3Graph]
  infer_instance

lemma lemma3Graph_degree (n : ℕ) (v : Fin (8 * n)) :
    (lemma3Graph n).degree v =
      if v.val < 4 * n then
        if v.val + 1 ≤ n then v.val + 1 + 2 * n else v.val + 1
      else
        let j' := v.val - 4 * n + 1
        if j' ≤ n then j' + n
        else if j' ≤ 2 * n then j'
        else if j' ≤ 3 * n then j' + n
        else j' := by
  simp only [SimpleGraph.degree]
  rw [show (lemma3Graph n).neighborFinset v = Finset.univ.filter (fun x => (lemma3Graph n).Adj v x) by ext; simp]
  split_ifs with h_v_lt h_i_le h_j_le h_j_le_2n h_j_le_3n
  · -- Case 1: v < 4n, i ≤ n
    let i := v.val + 1
    let s := (Finset.Icc 1 n) ∪ (Finset.Icc (2 * n + 1) (3 * n)) ∪ (Finset.Icc (4 * n + 1 - i) (4 * n))
    have h_card : s.card = 2 * n + i := by
      have h_s1_s2 : Disjoint (Finset.Icc 1 n) (Finset.Icc (2 * n + 1) (3 * n)) := by
        rw [Finset.disjoint_left]; intro x h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
      have h_s1_s3 : Disjoint (Finset.Icc 1 n) (Finset.Icc (4 * n + 1 - i) (4 * n)) := by
        rw [Finset.disjoint_left]; intro x h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
      have h_s2_s3 : Disjoint (Finset.Icc (2 * n + 1) (3 * n)) (Finset.Icc (4 * n + 1 - i) (4 * n)) := by
        rw [Finset.disjoint_left]; intro x h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
      have h_disj : Disjoint (Finset.Icc 1 n ∪ Finset.Icc (2 * n + 1) (3 * n)) (Finset.Icc (4 * n + 1 - i) (4 * n)) := by
        rw [Finset.disjoint_union_left]; exact ⟨h_s1_s3, h_s2_s3⟩
      rw [Finset.card_union_of_disjoint h_disj, Finset.card_union_of_disjoint h_s1_s2, Nat.card_Icc, Nat.card_Icc, Nat.card_Icc]
      omega
    change _ = i + 2 * n
    rw [add_comm, ← h_card]
    have h_mem_bound : ∀ j' ∈ s, j' + 4 * n - 1 < 8 * n := by
      intro j' hj'
      have : j' ∈ (Finset.Icc 1 n) ∪ (Finset.Icc (2 * n + 1) (3 * n)) ∪ (Finset.Icc (4 * n + 1 - i) (4 * n)) := hj'
      simp only [Finset.mem_union, Finset.mem_Icc] at this
      omega
    apply Finset.card_bij (fun j' hj' => ⟨j' + 4 * n - 1, h_mem_bound j' hj'⟩)
    · intro j' hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : j' ∈ (Finset.Icc 1 n) ∪ (Finset.Icc (2 * n + 1) (3 * n)) ∪ (Finset.Icc (4 * n + 1 - i) (4 * n)) := hj'
      simp only [Finset.mem_union, Finset.mem_Icc] at this
      dsimp [lemma3Graph]
      simp only [h_v_lt, true_and, false_or, or_false]
      omega
    · intro j1 j2 _ _ h; simp [Fin.mk.inj_iff] at h; omega
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      dsimp [lemma3Graph] at hu
      simp only [h_v_lt, true_and, false_or, or_false] at hu
      use u.val - 4 * n + 1
      simp only [Finset.mem_union, Finset.mem_Icc]
      constructor
      · omega
      · simp [Fin.mk.inj_iff]; omega


  · -- Case 2: v < 4n, i > n
    let i := v.val + 1
    let s := Finset.Icc (4 * n + 1 - i) (4 * n)
    have h_card : s.card = i := by rw [Nat.card_Icc]; omega
    change _ = i
    rw [← h_card]
    have h_mem_bound : ∀ j' ∈ s, j' + 4 * n - 1 < 8 * n := by
      intro j' hj'
      simp only [Finset.mem_Icc] at hj'
      omega
    apply Finset.card_bij (fun j' hj' => ⟨j' + 4 * n - 1, h_mem_bound j' hj'⟩)
    · intro j' hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [Finset.mem_Icc] at hj'
      dsimp [lemma3Graph]
      simp only [h_v_lt, true_and, false_or, or_false]
      omega
    · intro j1 j2 _ _ h; simp [Fin.mk.inj_iff] at h; omega
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      dsimp [lemma3Graph] at hu
      simp only [h_v_lt, true_and, false_or, or_false] at hu
      use u.val - 4 * n + 1
      simp only [Finset.mem_Icc]
      constructor
      · omega
      · simp [Fin.mk.inj_iff]; omega

  · -- Case 3: v ≥ 4n, j' ≤ n
    let j' := v.val - 4 * n + 1
    let s := (Finset.Icc 1 n) ∪ (Finset.Icc (4 * n + 1 - j') (4 * n))
    have h_card : s.card = n + j' := by
      have h : Disjoint (Finset.Icc 1 n) (Finset.Icc (4 * n + 1 - j') (4 * n)) := by
        rw [Finset.disjoint_left]; intro x h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
      rw [Finset.card_union_of_disjoint h, Nat.card_Icc, Nat.card_Icc]; omega
    change _ = j' + n
    rw [add_comm, ← h_card]
    have h_mem_bound : ∀ i ∈ s, i - 1 < 8 * n := by
      intro i hi
      simp only [Finset.mem_union, Finset.mem_Icc] at hi
      omega
    apply Finset.card_bij (fun i hi => ⟨i - 1, h_mem_bound i hi⟩)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [Finset.mem_union, Finset.mem_Icc] at hi
      dsimp [lemma3Graph]
      simp only [h_v_lt, false_and, false_or, true_and]
      omega
    · intro i1 i2 _ _ h; simp [Fin.mk.inj_iff] at h; omega
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      dsimp [lemma3Graph] at hu
      simp only [h_v_lt, false_and, false_or, true_and] at hu
      use u.val + 1
      simp only [Finset.mem_union, Finset.mem_Icc]
      constructor
      · omega
      · simp [Fin.mk.inj_iff]; omega
  · -- Case 4: v ≥ 4n, n < j' ≤ 2n
    let j' := v.val - 4 * n + 1
    let s := Finset.Icc (4 * n + 1 - j') (4 * n)
    have h_card : s.card = j' := by rw [Nat.card_Icc]; omega
    change _ = j'
    rw [← h_card]
    have h_mem_bound : ∀ i ∈ s, i - 1 < 8 * n := by
      intro i hi
      simp only [Finset.mem_Icc] at hi
      omega
    apply Finset.card_bij (fun i hi => ⟨i - 1, h_mem_bound i hi⟩)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [Finset.mem_Icc] at hi
      dsimp [lemma3Graph]
      simp only [h_v_lt, false_and, false_or, true_and]
      omega
    · intro i1 i2 _ _ h; simp [Fin.mk.inj_iff] at h; omega
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      dsimp [lemma3Graph] at hu
      simp only [h_v_lt, false_and, false_or, true_and] at hu
      use u.val + 1
      simp only [Finset.mem_Icc]
      constructor
      · omega
      · simp [Fin.mk.inj_iff]; omega
  · -- Case 5: v ≥ 4n, 2n < j' ≤ 3n
    let j' := v.val - 4 * n + 1
    let s := (Finset.Icc 1 n) ∪ (Finset.Icc (4 * n + 1 - j') (4 * n))
    have h_card : s.card = n + j' := by
      have h : Disjoint (Finset.Icc 1 n) (Finset.Icc (4 * n + 1 - j') (4 * n)) := by
        rw [Finset.disjoint_left]; intro x h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
      rw [Finset.card_union_of_disjoint h, Nat.card_Icc, Nat.card_Icc]; omega
    change _ = j' + n
    rw [add_comm, ← h_card]
    have h_mem_bound : ∀ i ∈ s, i - 1 < 8 * n := by
      intro i hi
      simp only [Finset.mem_union, Finset.mem_Icc] at hi
      omega
    apply Finset.card_bij (fun i hi => ⟨i - 1, h_mem_bound i hi⟩)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [Finset.mem_union, Finset.mem_Icc] at hi
      dsimp [lemma3Graph]
      simp only [h_v_lt, false_and, false_or, true_and]
      omega
    · intro i1 i2 _ _ h; simp [Fin.mk.inj_iff] at h; omega
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      dsimp [lemma3Graph] at hu
      simp only [h_v_lt, false_and, false_or, true_and] at hu
      use u.val + 1
      simp only [Finset.mem_union, Finset.mem_Icc]
      constructor
      · omega
      · simp [Fin.mk.inj_iff]; omega
  · -- Case 6: v ≥ 4n, j' > 3n
    let j' := v.val - 4 * n + 1
    let s := Finset.Icc (4 * n + 1 - j') (4 * n)
    have h_card : s.card = j' := by rw [Nat.card_Icc]; omega
    change _ = j'
    rw [← h_card]
    have h_mem_bound : ∀ i ∈ s, i - 1 < 8 * n := by
      intro i hi
      simp only [Finset.mem_Icc] at hi
      omega
    apply Finset.card_bij (fun i hi => ⟨i - 1, h_mem_bound i hi⟩)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [Finset.mem_Icc] at hi
      dsimp [lemma3Graph]
      simp only [h_v_lt, false_and, false_or, true_and]
      omega
    · intro i1 i2 _ _ h; simp [Fin.mk.inj_iff] at h; omega
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      dsimp [lemma3Graph] at hu
      simp only [h_v_lt, false_and, false_or, true_and] at hu
      use u.val + 1
      simp only [Finset.mem_Icc]
      constructor
      · omega
      · simp [Fin.mk.inj_iff]; omega


set_option maxHeartbeats 0
/-- **Lemma 3.** For every `n` there exists a bipartite graph with
`8 n` vertices, minimum degree `n + 1`, and `f = 3`. -/
@[category API, AMS 5]
lemma lemma3Graph_bipartite (n : ℕ) : (lemma3Graph n).IsBipartite := by
  apply IsBipartiteWith.isBipartite (s := {v | v.val < 4 * n}) (t := {v | v.val ≥ 4 * n})
  constructor
  · apply Set.disjoint_left.mpr
    intro v hv h_v_ge
    simp at hv h_v_ge
    linarith
  · intro u v hadj
    dsimp [lemma3Graph] at hadj
    rcases hadj with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · left; simp [*]
    · right; simp [*]

lemma lemma3_minDegree (n : ℕ) (hn : 0 < n) : (lemma3Graph n).minDegree = n + 1 := by
  apply le_antisymm
  · let v : Fin (8 * n) := ⟨4 * n, by omega⟩
    apply (SimpleGraph.minDegree_le_degree (lemma3Graph n) v).trans
    rw [lemma3Graph_degree]
    simp only [v, Nat.lt_irrefl, false_and, if_false, add_le_iff_nonpos_left,
      nonpos_iff_eq_zero]
    split_ifs
    · exact le_refl _
    · omega
    · omega
    · omega
  · haveI : Nonempty (Fin (8 * n)) := ⟨⟨0, by omega⟩⟩
    apply SimpleGraph.le_minDegree_of_forall_le_degree (lemma3Graph n) (n + 1)
    intro v
    rw [lemma3Graph_degree]
    dsimp
    by_cases hv : v.val < 4 * n
    · simp [hv]
      split_ifs <;> omega
    · simp [hv]
      have h_ge_4n : v.val ≥ 4 * n := le_of_not_lt hv
      set j' := v.val - 4 * n + 1 with hj'
      have hj'_pos : j' ≥ 1 := by
        rw [hj']
        have : v.val - 4 * n ≥ 0 := Nat.zero_le _
        exact Nat.le_add_left 1 _
      split_ifs with h1 h2 h3
      · omega
      · omega
      · omega
      · -- Case j' > 3n
        have h_gt : v.val - 4 * n + 1 > 3 * n := lt_of_not_ge h3
        have h_ge : v.val - 4 * n + 1 ≥ 3 * n + 1 := Nat.succ_le_of_lt h_gt
        have h_n : 3 * n + 1 ≥ n + 1 := Nat.add_le_add_right (@Nat.le_mul_of_pos_left 3 n (by omega)) 1
        exact le_trans h_n h_ge

@[category API, AMS 5]
lemma lemma3_repetitionNumber (n : ℕ) (hn : 0 < n) : f_rep (lemma3Graph n) = (3 : ℕ) := by
  let d := n + 1
  have h_mem_degrees : d ∈ (Finset.univ.image (fun v => (lemma3Graph n).degree v)) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    use Fin.mk n (by omega)
    rw [lemma3Graph_degree]
    dsimp; split_ifs <;> omega
  apply le_antisymm
  · -- f_rep ≤ 3
    let degrees := (Finset.univ.image (fun v => (lemma3Graph n).degree v))
    let freqs := (degrees.image (fun d' => degreeFreq (lemma3Graph n) d'))
    have h_max : ∀ x ∈ freqs, x ≤ 3 := by
      intro x hx
      simp only [degrees, Finset.mem_image, exists_prop] at hx
      rcases hx with ⟨d', hd', rfl⟩
      unfold degreeFreq
      let f_v (x : ℕ) : Fin (8 * n) := Fin.mk x (by omega)
      let I1 := Finset.Ico 0 n
      let I2 := Finset.Ico n (4 * n)
      let I3 := Finset.Ico (4 * n) (5 * n)
      let I4 := Finset.Ico (5 * n) (6 * n)
      let I5 := Finset.Ico (6 * n) (7 * n)
      let I6 := Finset.Ico (7 * n) (8 * n)
      have h_univ : Finset.univ = (I1 ∪ I2 ∪ I3 ∪ I4 ∪ I5 ∪ I6).image f_v := by
        ext x
        simp only [Finset.mem_univ, true_iff, Finset.mem_image, Finset.mem_union, Finset.mem_Ico]
        use x.val
        constructor
        · have : x.val < 8 * n := x.isLt
          omega
        · simp [f_v]
      rw [h_univ, Finset.filter_image, Finset.card_image_of_injOn]
      · let S := (I1 ∪ I2 ∪ I3 ∪ I4 ∪ I5 ∪ I6)
        have h_le1 (s : Finset ℕ) (hs : s ⊆ S) : (s.filter (fun x => (lemma3Graph n).degree (f_v x) = d')).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro x hx y hy
          simp only [Finset.mem_filter] at hx hy
          have hx_lt : x < 8 * n := by
            have : x ∈ S := hs hx.1
            simp only [S, Finset.mem_union, Finset.mem_Ico] at this
            rcases this with h | h | h | h | h | h <;> omega
          have hy_lt : y < 8 * n := by
            have : y ∈ S := hs hy.1
            simp only [S, Finset.mem_union, Finset.mem_Ico] at this
            rcases this with h | h | h | h | h | h <;> omega
          let vx : Fin (8 * n) := Fin.mk x hx_lt
          let vy : Fin (8 * n) := Fin.mk y hy_lt
          have h_eq : (lemma3Graph n).degree vx = (lemma3Graph n).degree vy := by
            rw [hx.2, hy.2]
          rw [lemma3Graph_degree, lemma3Graph_degree] at h_eq
          dsimp at h_eq
          -- Use interval information to simplify split_ifs
          have hx_range : x ∈ s := hx.1
          have hy_range : y ∈ s := hy.1
          split_ifs at h_eq <;> omega
        -- Partition the sum
        rw [Finset.filter_union, Finset.card_union_of_disjoint]
        · rw [Finset.filter_union, Finset.card_union_of_disjoint]
          · rw [Finset.filter_union, Finset.card_union_of_disjoint]
            · rw [Finset.filter_union, Finset.card_union_of_disjoint]
              · rw [Finset.filter_union, Finset.card_union_of_disjoint]
                · have h1 := h_le1 I1 (by simp [S])
                  have h2 := h_le1 I2 (by simp [S])
                  have h3 := h_le1 I3 (by simp [S])
                  have h4 := h_le1 I4 (by simp [S])
                  have h5 := h_le1 I5 (by simp [S])
                  have h6 := h_le1 I6 (by simp [S])
                  -- Analyze ranges
                  by_cases hd1 : d' ∈ Finset.Icc (n + 1) (2 * n)
                  · simp only [Finset.mem_Icc] at hd1
                    have c1 : (I1.filter (fun x => (lemma3Graph n).degree (f_v x) = d')).card = 0 := by
                      apply Finset.card_eq_zero
                      apply Finset.eq_empty_of_forall_not_mem
                      intro x hx
                      simp only [Finset.mem_filter, Finset.mem_Ico] at hx
                      rw [lemma3Graph_degree] at hx
                      dsimp at hx
                      split_ifs at hx <;> omega
                    have c5 : (I5.filter (fun x => (lemma3Graph n).degree (f_v x) = d')).card = 0 := by
                      apply Finset.card_eq_zero
                      apply Finset.eq_empty_of_forall_not_mem
                      intro x hx
                      simp only [Finset.mem_filter, Finset.mem_Ico] at hx
                      rw [lemma3Graph_degree] at hx
                      dsimp at hx
                      split_ifs at hx <;> omega
                    have c6 : (I6.filter (fun x => (lemma3Graph n).degree (f_v x) = d')).card = 0 := by
                      apply Finset.card_eq_zero
                      apply Finset.eq_empty_of_forall_not_mem
                      intro x hx
                      simp only [Finset.mem_filter, Finset.mem_Ico] at hx
                      rw [lemma3Graph_degree] at hx
                      dsimp at hx
                      split_ifs at hx <;> omega
                    omega
                  · by_cases hd2 : d' ∈ Finset.Icc (2 * n + 1) (3 * n)
                    · simp only [Finset.mem_Icc] at hd2
                      have c2 : (I2.filter (fun x => (lemma3Graph n).degree (f_v x) = d')).card = 0 := by
                        apply Finset.card_eq_zero
                        apply Finset.eq_empty_of_forall_not_mem
                        intro x hx
                        simp only [Finset.mem_filter, Finset.mem_Ico] at hx
                        rw [lemma3Graph_degree] at hx
                        dsimp at hx
                        split_ifs at hx <;> omega
                      have c3 : (I3.filter (fun x => (lemma3Graph n).degree (f_v x) = d')).card = 0 := by
                        apply Finset.card_eq_zero
                        apply Finset.eq_empty_of_forall_not_mem
                        intro x hx
                        simp only [Finset.mem_filter, Finset.mem_Ico] at hx
                        rw [lemma3Graph_degree] at hx
                        dsimp at hx
                        split_ifs at hx <;> omega
                      have c4 : (I4.filter (fun x => (lemma3Graph n).degree (f_v x) = d')).card = 0 := by
                        apply Finset.card_eq_zero
                        apply Finset.eq_empty_of_forall_not_mem
                        intro x hx
                        simp only [Finset.mem_filter, Finset.mem_Ico] at hx
                        rw [lemma3Graph_degree] at hx
                        dsimp at hx
                        split_ifs at hx <;> omega
                      omega
                    · by_cases hd3 : d' ∈ Finset.Icc (3 * n + 1) (4 * n)
                      · simp only [Finset.mem_Icc] at hd3
                        have c1 : (I1.filter (fun x => (lemma3Graph n).degree (f_v x) = d')).card = 0 := by
                          apply Finset.card_eq_zero
                          apply Finset.eq_empty_of_forall_not_mem
                          intro x hx
                          simp only [Finset.mem_filter, Finset.mem_Ico] at hx
                          rw [lemma3Graph_degree] at hx
                          dsimp at hx
                          split_ifs at hx <;> omega
                        have c2 : (I2.filter (fun x => (lemma3Graph n).degree (f_v x) = d')).card = 0 := by
                          apply Finset.card_eq_zero
                          apply Finset.eq_empty_of_forall_not_mem
                          intro x hx
                          simp only [Finset.mem_filter, Finset.mem_Ico] at hx
                          rw [lemma3Graph_degree] at hx
                          dsimp at hx
                          split_ifs at hx <;> omega
                        have c3 : (I3.filter (fun x => (lemma3Graph n).degree (f_v x) = d')).card = 0 := by
                          apply Finset.card_eq_zero
                          apply Finset.eq_empty_of_forall_not_mem
                          intro x hx
                          simp only [Finset.mem_filter, Finset.mem_Ico] at hx
                          rw [lemma3Graph_degree] at hx
                          dsimp at hx
                          split_ifs at hx <;> omega
                        have c4 : (I4.filter (fun x => (lemma3Graph n).degree (f_v x) = d')).card = 0 := by
                          apply Finset.card_eq_zero
                          apply Finset.eq_empty_of_forall_not_mem
                          intro x hx
                          simp only [Finset.mem_filter, Finset.mem_Ico] at hx
                          rw [lemma3Graph_degree] at hx
                          dsimp at hx
                          split_ifs at hx <;> omega
                        omega
                      · -- d' is outside all these ranges
                        have c_all : (Finset.univ.filter (fun v => (lemma3Graph n).degree v = d')).card = 0 := by
                          apply Finset.card_eq_zero
                          apply Finset.eq_empty_of_forall_not_mem
                          intro v hv
                          simp only [Finset.mem_filter] at hv
                          rw [lemma3Graph_degree] at hv
                          dsimp at hv
                          split_ifs at hv <;> omega
                        exact c_all.le.trans (by omega)
                · rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_filter, Finset.mem_Ico] at h1 h2; omega
              · rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union] at h1 h2; omega
            · rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union] at h1 h2; omega
          · rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union] at h1 h2; omega
        · rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union] at h1 h2; omega
      · intro x hx y hy h_eq
        simp only [f_v] at h_eq
        exact Fin.mk.inj_iff.mp h_eq
    cases h : freqs.max with
    | bot =>
      have h_not_empty : freqs.Nonempty := ⟨_, by
        simp only [freqs, Finset.mem_image]
        use d, h_mem_degrees⟩
      have := Finset.max_eq_bot.mp h
      rw [this] at h_not_empty
      contradiction
    | coe m =>
      have h_mem : m ∈ freqs := Finset.mem_of_max h
      exact h_max m h_mem
  · -- f_rep ≥ 3
    let s : Finset (Fin (8 * n)) := {Fin.mk n (by omega), Fin.mk (4 * n) (by omega), Fin.mk (5 * n) (by omega)}
    have h_card : s.card = 3 := by
      have h1 : Fin.mk n (by omega) ≠ Fin.mk (4 * n) (by omega) := by simp [Fin.mk.inj_iff]; omega
      have h2 : Fin.mk (4 * n) (by omega) ≠ Fin.mk (5 * n) (by omega) := by simp [Fin.mk.inj_iff]; omega
      have h3 : Fin.mk n (by omega) ≠ Fin.mk (5 * n) (by omega) := by simp [Fin.mk.inj_iff]; omega
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [h2, h3]
      · simp [h1]
    have h_deg : ∀ v ∈ s, (lemma3Graph n).degree v = n + 1 := by
      intro v hv
      rw [lemma3Graph_degree]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> (dsimp; split_ifs <;> omega)
    have h_freq_ge_3 : 3 ≤ degreeFreq (lemma3Graph n) d := by
      unfold degreeFreq
      have h_subset : s ⊆ Finset.univ.filter (fun v => (lemma3Graph n).degree v = d) := by
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_deg v hv
      exact le_trans (by rw [h_card]; omega) (Finset.card_le_card h_subset)
    unfold repetitionNumber
    let degrees := (Finset.univ.image (fun v => (lemma3Graph n).degree v))
    let freqs := (degrees.image (fun d' => degreeFreq (lemma3Graph n) d'))
    cases h_max : freqs.max with
    | bot =>
      have h_not_empty : freqs.Nonempty := ⟨_, by
        simp only [freqs, Finset.mem_image]
        use d, h_mem_degrees⟩
      have := Finset.max_eq_bot.mp h_max
      rw [this] at h_not_empty
      contradiction
    | coe m =>
      have h_mem : degreeFreq (lemma3Graph n) d ∈ freqs := by
        simp only [freqs, Finset.mem_image]
        use d, h_mem_degrees
      exact le_trans h_freq_ge_3 (WithBot.coe_le_coe.mp (Finset.le_max (degreeFreq (lemma3Graph n) d) h_mem))

/-- **Lemma 3.** For every `n` there exists a bipartite graph with
`8 n` vertices, minimum degree `n + 1`, and `f = 3`. -/
@[category API, AMS 5]
lemma lemma3 (n : ℕ) (hn : 0 < n) :
    ∃ (G : SimpleGraph (Fin (8 * n))) (_ : DecidableRel G.Adj),
      G.IsBipartite ∧ G.minDegree = n + 1 ∧ f_rep G = 3 := by
  use lemma3Graph n, inferInstance
  constructor
  · -- IsBipartite
    exact lemma3Graph_bipartite n
  constructor
  · -- minDegree = n + 1
    exact lemma3_minDegree n hn
  · -- repetitionNumber = 3
    exact lemma3_repetitionNumber n hn

/-- **Lemma 4.** Let `G` be a triangle-free graph with `n` vertices and let `v` be a vertex of `G`.
There exists a triangle-free graph `H` containing `G` as an induced subgraph such that:
(i) the degree of `v` in `H` is one more than its degree in `G`;
(ii) for every vertex `w` of `G` other than `v` the degree of `w` in `H` is the same as its degree in `G`;
(iii) if `J` is the subgraph of `H` induced by the vertices not in `G`, then `f(J)=3` and `δ(J) ≥ 2n`. -/
@[category API, AMS 5]
lemma lemma4 (G : SimpleGraph α) [DecidableRel G.Adj] (h₁ : G.CliqueFree 3) (v : α) :
    ∃ (β : Type*) (_ : Fintype β) (H : SimpleGraph β) (_ : DecidableRel H.Adj) (i : G ↪g H),
      H.CliqueFree 3 ∧
      H.degree (i v) = G.degree v + 1 ∧
      (∀ w ≠ v, H.degree (i w) = G.degree w) ∧
      let J := H.induce (Set.compl (Set.range i))
      J.CliqueFree 3 ∧ repetitionNumber J = 3 ∧ J.minDegree ≥ 2 * Fintype.card α := by
  sorry

/-- **Theorem 2.** Every triangle-free graph is an induced subgraph of one
with `f = 3`. -/
@[category research solved, AMS 5]
theorem theorem2 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    ∃ (β : Type*) (_ : Fintype β) (H : SimpleGraph β) (_ : DecidableRel H.Adj) (i : G ↪g H),
      H.CliqueFree 3 ∧ repetitionNumber H = 3 := by
  sorry

/-- `F n` is the smallest number of vertices of a triangle-free graph
with chromatic number `n` and `f = 3`. -/
@[category research solved, AMS 5]
noncomputable def F (n : ℕ) : ℕ :=
  sInf { p | ∃ (G : SimpleGraph (Fin p)) (_ : DecidableRel G.Adj),
    G.CliqueFree 3 ∧ G.chromaticNumber = n ∧ repetitionNumber G = 3 }

@[category research solved, AMS 5]
theorem F_three : F 3 = 7 := by
  sorry

@[category research solved, AMS 5]
theorem F_four_le : F 4 ≤ 19 := by
  sorry

end SimpleGraph
