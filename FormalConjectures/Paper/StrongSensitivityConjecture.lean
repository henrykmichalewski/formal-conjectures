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
# Strong Sensitivity Conjecture (`bs(f) ≤ s(f)^2`)

This file formalizes the *strong* sensitivity conjecture, asserting:

For every Boolean function `f : {0,1}^n → {0,1}`,
`bs(f) ≤ s(f)^2`,
where bs(f) denotes block sensitivity and s(f) denotes sensitivity.

Huang's theorem proves a *quartic* upper bound, `bs(f) ≤ s(f)^4`, thereby
resolving the most widely known form of the sensitivity conjecture.

We now ask whether a stronger upper bound holds. Interestingly, the original
paper of Nisan and Szegedy, where the sensitivity conjecture first appeared,
already speculated that a *quadratic* upper bound might be the correct
relation. On the lower bound side, Rubinstein
(https://link.springer.com/article/10.1007/BF01200762) constructed Boolean functions
exhibiting the first quadratic separation. The best currently
known gap, due to Ambainis and Sun (https://arxiv.org/abs/1108.3494), is
`bs(f) ≥ (2/3)⋅s(f)^2`.

*References:*
* [Induced Subgraphs of Hypercubes and a Proof of the Sensitivity Conjecture](https://arxiv.org/abs/1907.00847)
  by Hao Huang (see Section 3, Concluding Remarks)
* [Variations on the Sensitivity Conjecture](https://arxiv.org/abs/1011.0354)
  by Pooya Hatami, Raghav Kulkarni, and Denis Pankratov (see Question 3.1)
* [On the Degree of Boolean Functions as Real Polynomials](https://link.springer.com/article/10.1007/BF01263419)
  by Noam Nisan, and Mario Szegedy (see Section 4, Open Problems)
-/

namespace StrongSensitivityConjecture

open Finset Function Classical

section Sensitivity

variable {n : ℕ}

/-- Flip operator,
`flip x B` returns input `x` with bits in block `B` inverted. -/
def flip (x : Fin n → Bool) (B : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ B then !(x i) else x i

/-- Local sensitivity s(f,x),
number of indices where flipping one bit changes the value of `f`. -/
def sensitivityAt (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  #{i | f (flip x {i}) ≠ f x}

/-- Global sensitivity s(f),
maximum sensitivity of `f` over all inputs. -/
def sensitivity (f : (Fin n → Bool) → Bool) : ℕ :=
  univ.sup (sensitivityAt f)

/-- Check validity of block collection (disjoint and sensitive),
A collection of blocks `cB` is valid for `f` at `x` if the blocks are
disjoint and flipping any block changes `f(x)`. -/
def IsValidBlockConfig (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (cB : Finset (Finset (Fin n))) : Prop :=
  (cB : Set (Finset (Fin n))).PairwiseDisjoint id ∧
  ∀ B ∈ cB, f (flip x B) ≠ f x

/-- Local block sensitivity bs(f,x),
maximum size of a collection of sensitive, disjoint blocks for `f` at `x`. -/
noncomputable def blockSensitivityAt (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  Finset.sup {cB | IsValidBlockConfig f x cB} card

/-- Global block sensitivity of `f`,
maximum block sensitivity of `f` over all inputs. -/
noncomputable def blockSensitivity (f : (Fin n → Bool) → Bool) : ℕ :=
  univ.sup (blockSensitivityAt f)

/-- Strong Sensitivity Conjecture,
for every Boolean function `f : {0,1}^n → {0,1}`,
`bs(f) ≤ s(f)^2`.

We call this the *strong* sensitivity conjecture because the original sensitivity
conjecture only asked for a polynomial bound in terms of `s(f)`. Huang's
celebrated result (often called the sensitivity theorem) gives a quartic bound,
`bs(f) ≤ s(f)^4`, thereby settling the original conjecture. -/
@[category research open, AMS 68]
theorem strong_sensitivity_conjecture {n : ℕ} (f : (Fin n → Bool) → Bool) :
    blockSensitivity f ≤ sensitivity f ^ 2 := by
  sorry


/-- Simple test example,
A Boolean function whose block sensitivity is strictly greater than
its sensitivity. Source: [Nisan1989](https://dl.acm.org/doi/10.1145/73007.73038).

`nisanExample(x) = 1` iff the Hamming weight of `x` is either
`n/2` or `n/2 + 1`. We assume `n` is a multiple of 4.
The function is symmetric, so its value only depends on the Hamming weight
of the input. -/
@[category test, AMS 68]
def nisanExample (n : ℕ) (x : Fin n → Bool) : Bool :=
  let w := #{i | x i}
  decide (w ∈ ({n / 2, n / 2 + 1} : Finset ℕ))

/-- Assuming `n` is a multiple of 4, the sensitivity of `nisanExample`
is `n/2 + 2`, achieved by any `x` with Hamming weight `n/2 + 2`. -/
@[category test, AMS 68]
lemma nisanExample_sensitivity (n : ℕ) (hn : 4 ∣ n) (hn0 : n ≠ 0) :
    sensitivity (nisanExample n) = n / 2 + 2 := by
  unfold sensitivity
  apply le_antisymm
  · apply Finset.sup_le
    intro x _
    unfold sensitivityAt nisanExample
    let w := #{i | x i}
    have hw : #{i | x i = true} = w := by
      congr; ext i; simp

    have h_flip_weight : ∀ i, #{j | (flip x {i}) j} = if x i then w - 1 else w + 1 := by
      intro i
      simp [flip]
      by_cases hi : x i
      · rw [if_pos hi]
        have : filter (fun j => (if j = i then !x j else x j)) univ = filter (fun j => x j) univ \ {i} := by
          ext j
          simp
          by_cases hji : j = i
          · rw [hji]; simp [hi]
          · simp [hji]
        have h_goal_eq : #{j | if j = i then x j = false else x j = true} = (filter (fun j => (if j = i then !x j else x j)) univ).card := by
          congr; ext j; simp; split_ifs <;> simp
        rw [h_goal_eq]
        rw [this]
        have h_subset : {i} ⊆ filter (fun j => x j) univ := by
          rw [Finset.singleton_subset_iff]
          rw [mem_filter]
          simp [hi]
        rw [Finset.card_sdiff h_subset]
        rw [hw, Finset.card_singleton]
      · rw [if_neg hi]
        have : filter (fun j => (if j = i then !x j else x j)) univ = filter (fun j => x j) univ ∪ {i} := by
          ext j
          simp
          by_cases hji : j = i
          · rw [hji]; simp [hi]
          · simp [hji]
        have h_goal_eq : #{j | if j = i then x j = false else x j = true} = (filter (fun j => (if j = i then !x j else x j)) univ).card := by
          congr; ext j; simp; split_ifs <;> simp
        rw [h_goal_eq]
        rw [this]
        have h_disj : Disjoint (filter (fun j => x j) univ) {i} := by
          rw [Finset.disjoint_singleton_right]
          rw [mem_filter]
          simp [hi]
        rw [Finset.card_union_of_disjoint h_disj]
        rw [hw, Finset.card_singleton]

    let target : Finset ℕ := {n / 2, n / 2 + 1}
    have h_val : ∀ y, nisanExample n y = (decide (#{i | y i} ∈ target)) := by
      intro y
      rfl

    simp only [h_val]
    simp only [h_flip_weight]

    rw [Finset.card_eq_sum_ones]
    rw [Finset.sum_filter]
    simp
    have h_union : univ = filter (fun i => x i) univ ∪ filter (fun i => x i = false) univ := by
      ext i
      simp
      apply Bool.eq_true_or_eq_false
    have h_disj : Disjoint (filter (fun i => x i) univ) (filter (fun i => x i = false) univ) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      simp at h1 h2
      rw [h1] at h2
      contradiction
    rw [h_union]
    rw [Finset.sum_union h_disj]

    let k := n / 2
    have hk : k = n / 2 := rfl
    have h2n : 2 ∣ n := dvd_trans (by norm_num) hn
    have hn_eq : n = 2 * k := by
      rw [hk]
      exact (Nat.mul_div_cancel' h2n).symm
    rw [hn_eq] at *

    have h_target_eq : target = {k, k+1} := by
      simp [target, hk]
    rw [h_target_eq] at *

    have hk2 : 2 ≤ k := by
      rw [hk]
      apply Nat.le_div_iff_mul_le (by norm_num) |>.mpr
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hn

    -- Analyze the sum based on w
    by_cases hw_k : w = k
    · subst w; simp; norm_num
      have : k - 1 ∉ ({k, k + 1} : Finset ℕ) := by
        simp; omega

      have h_term_pos : ∀ i, x i → (if (decide ((if x i then k - 1 else k + 1) = k) || decide ((if x i then k - 1 else k + 1) = k + 1)) = (decide (k = k) || decide (k = k + 1)) then 0 else 1) = 1 := by
        intro i hi
        simp [hi]
        have h1 : k - 1 ≠ k := by omega
        have h2 : k - 1 ≠ k + 1 := by omega
        have h3 : k = k := rfl
        simp [h1, h2, h3]

      have h_term_neg : ∀ i, !x i → (if (decide ((if x i then k - 1 else k + 1) = k) || decide ((if x i then k - 1 else k + 1) = k + 1)) = (decide (k = k) || decide (k = k + 1)) then 0 else 1) = 0 := by
        intro i hi
        simp at hi
        simp [hi]
        have h1 : k + 1 ≠ k := by omega
        have h2 : k + 1 = k + 1 := rfl
        have h3 : k = k := rfl
        simp [h1, h2, h3]

      have h_sum_pos : (∑ x_1 with x x_1 = true,
          if
              (decide ((if x x_1 = true then k - 1 else k + 1) = k) ||
                  decide ((if x x_1 = true then k - 1 else k + 1) = k + 1)) =
                (decide (k = k) || decide (k = k + 1)) then
            0
          else 1) = Finset.sum (filter (fun i => x i) univ) (fun _ => 1) := by
        refine Finset.sum_congr (by ext; simp) (fun i hi => ?_)
        have hxi : x i = true := by simp at hi; exact hi
        rw [h_term_pos i hxi]

      have h_sum_neg : (∑ x_1 with x x_1 = false,
          if
              (decide ((if x x_1 = true then k - 1 else k + 1) = k) ||
                  decide ((if x x_1 = true then k - 1 else k + 1) = k + 1)) =
                (decide (k = k) || decide (k = k + 1)) then
            0
          else 1) = Finset.sum (filter (fun i => x i = false) univ) (fun _ => 0) := by
        refine Finset.sum_congr (by ext; simp) (fun i hi => ?_)
        have hxi : x i = false := by simp at hi; exact hi
        have hxi' : !x i := by simp [hxi]
        rw [h_term_neg i hxi']

      have h_union_set : {i | x i = true} ∪ {i | x i = false} = Set.univ := by
        ext i
        simp
        apply Bool.eq_true_or_eq_false

      have h_card_simpl : #({i ∈ {i | x i = true} ∪ {i | x i = false} | x i = true}) = w := by
        rw [h_union_set]
        simp
        exact hw.symm
      rw [h_card_simpl]
      rw [hw_k]

      rw [← hk]
      rw [h_sum_pos, h_sum_neg]
      rw [Finset.sum_const, Finset.sum_const]
      simp
      omega
    by_cases hw_k1 : w = k + 1
    · subst w; simp; norm_num
      have : k + 2 ∉ ({k, k + 1} : Finset ℕ) := by
        simp; omega

      have h_term_pos : ∀ i, x i → (if (decide ((if x i then k else k + 2) = k) || decide ((if x i then k else k + 2) = k + 1)) = (decide (k + 1 = k) || decide (k + 1 = k + 1)) then 0 else 1) = 0 := by
        intro i hi
        simp [hi]
        have h1 : k = k := rfl
        have h2 : k + 1 ≠ k := by omega
        have h3 : k + 1 = k + 1 := rfl
        simp [h1, h2, h3]

      have h_term_neg : ∀ i, !x i → (if (decide ((if x i then k else k + 2) = k) || decide ((if x i then k else k + 2) = k + 1)) = (decide (k + 1 = k) || decide (k + 1 = k + 1)) then 0 else 1) = 1 := by
        intro i hi
        simp at hi
        simp [hi]
        have h1 : k + 2 ≠ k := by omega
        have h2 : k + 2 ≠ k + 1 := by omega
        have h3 : k + 1 ≠ k := by omega
        have h4 : k + 1 = k + 1 := rfl
        simp [h1, h2, h3, h4]

      have h_sum_pos : (∑ x_1 with x x_1 = true,
          if
              (decide ((if x x_1 = true then k else k + 2) = k) ||
                  decide ((if x x_1 = true then k else k + 2) = k + 1)) =
                (decide (k + 1 = k) || decide (k + 1 = k + 1)) then
            0
          else 1) = Finset.sum (filter (fun i => x i) univ) (fun _ => 0) := by
        refine Finset.sum_congr (by ext; simp) (fun i hi => ?_)
        have hxi : x i = true := by simp at hi; exact hi
        rw [h_term_pos i hxi]

      have h_sum_neg : (∑ x_1 with x x_1 = false,
          if
              (decide ((if x x_1 = true then k else k + 2) = k) ||
                  decide ((if x x_1 = true then k else k + 2) = k + 1)) =
                (decide (k + 1 = k) || decide (k + 1 = k + 1)) then
            0
          else 1) = Finset.sum (filter (fun i => x i = false) univ) (fun _ => 1) := by
        refine Finset.sum_congr (by ext; simp) (fun i hi => ?_)
        have hxi : x i = false := by simp at hi; exact hi
        have hxi' : !x i := by simp [hxi]
        rw [h_term_neg i hxi']

      have h_union_set : {i | x i = true} ∪ {i | x i = false} = Set.univ := by
        ext i
        simp
        apply Bool.eq_true_or_eq_false

      have h_card_simpl : #({i ∈ {i | x i = true} ∪ {i | x i = false} | x i = true}) = w := by
        rw [h_union_set]
        simp
        exact hw.symm
      rw [h_card_simpl]
      rw [hw_k1]

      rw [← hk]
      rw [h_sum_pos, h_sum_neg]
      rw [Finset.sum_const, Finset.sum_const]
      simp
      omega
    by_cases hw_km1 : w = k - 1
    · subst w; simp; norm_num
      have : k - 1 ∉ ({k, k + 1} : Finset ℕ) := by
        simp; omega
      have : k - 2 ∉ ({k, k + 1} : Finset ℕ) := by
        simp; omega

      have h_term_pos : ∀ i, x i → (if (decide ((if x i then k - 2 else k) = k) || decide ((if x i then k - 2 else k) = k + 1)) = (decide (k - 1 = k) || decide (k - 1 = k + 1)) then 0 else 1) = 0 := by
        intro i hi
        simp [hi]
        have h1 : k - 2 ≠ k := by omega
        have h2 : k - 2 ≠ k + 1 := by omega
        have h3 : k - 1 ≠ k := by omega
        have h4 : k - 1 ≠ k + 1 := by omega
        simp [h1, h2, h3, h4]

      have h_term_neg : ∀ i, !x i → (if (decide ((if x i then k - 2 else k) = k) || decide ((if x i then k - 2 else k) = k + 1)) = (decide (k - 1 = k) || decide (k - 1 = k + 1)) then 0 else 1) = 1 := by
        intro i hi
        simp at hi
        simp [hi]
        have h1 : k = k := rfl
        have h2 : k - 1 ≠ k := by omega
        have h3 : k - 1 ≠ k + 1 := by omega
        simp [h1, h2, h3]

      have h_sum_pos : (∑ x_1 with x x_1 = true,
          if
              (decide ((if x x_1 = true then k - 2 else k) = k) ||
                  decide ((if x x_1 = true then k - 2 else k) = k + 1)) =
                (decide (k - 1 = k) || decide (k - 1 = k + 1)) then
            0
          else 1) = Finset.sum (filter (fun i => x i) univ) (fun _ => 0) := by
        refine Finset.sum_congr (by ext; simp) (fun i hi => ?_)
        have hxi : x i = true := by simp at hi; exact hi
        rw [h_term_pos i hxi]

      have h_sum_neg : (∑ x_1 with x x_1 = false,
          if
              (decide ((if x x_1 = true then k - 2 else k) = k) ||
                  decide ((if x x_1 = true then k - 2 else k) = k + 1)) =
                (decide (k - 1 = k) || decide (k - 1 = k + 1)) then
            0
          else 1) = Finset.sum (filter (fun i => x i = false) univ) (fun _ => 1) := by
        refine Finset.sum_congr (by ext; simp) (fun i hi => ?_)
        have hxi : x i = false := by simp at hi; exact hi
        have hxi' : !x i := by simp [hxi]
        rw [h_term_neg i hxi']

      have h_union_set : {i | x i = true} ∪ {i | x i = false} = Set.univ := by
        ext i
        simp
        apply Bool.eq_true_or_eq_false

      have h_card_simpl : #({i ∈ {i | x i = true} ∪ {i | x i = false} | x i = true}) = w := by
        rw [h_union_set]
        simp
        exact hw.symm
      rw [h_card_simpl]
      rw [hw_km1]

      rw [← hk]
      rw [h_sum_pos, h_sum_neg]
      rw [Finset.sum_const, Finset.sum_const]
      simp
      omega
    by_cases hw_kp2 : w = k + 2
    · subst w; simp; norm_num
      have : k + 2 ∉ ({k, k + 1} : Finset ℕ) := by
        simp; omega
      have : k + 3 ∉ ({k, k + 1} : Finset ℕ) := by
        simp
        omega

      have h_term_pos : ∀ i, x i → (if (decide ((if x i then k + 1 else k + 3) = k) || decide ((if x i then k + 1 else k + 3) = k + 1)) = (decide (k + 2 = k) || decide (k + 2 = k + 1)) then 0 else 1) = 1 := by
        intro i hi
        simp [hi]
        have h1 : k + 1 ≠ k := by omega
        have h2 : k + 1 = k + 1 := rfl
        have h3 : k + 2 ≠ k := by omega
        have h4 : k + 2 ≠ k + 1 := by omega
        simp [h1, h2, h3, h4]

      have h_term_neg : ∀ i, !x i → (if (decide ((if x i then k + 1 else k + 3) = k) || decide ((if x i then k + 1 else k + 3) = k + 1)) = (decide (k + 2 = k) || decide (k + 2 = k + 1)) then 0 else 1) = 0 := by
        intro i hi
        simp at hi
        simp [hi]
        have h1 : k + 3 ≠ k := by omega
        have h2 : k + 3 ≠ k + 1 := by omega
        have h3 : k + 2 ≠ k := by omega
        have h4 : k + 2 ≠ k + 1 := by omega
        simp [h1, h2, h3, h4]

      have h_sum_pos : (∑ x_1 with x x_1 = true,
          if
              (decide ((if x x_1 = true then k + 1 else k + 3) = k) ||
                  decide ((if x x_1 = true then k + 1 else k + 3) = k + 1)) =
                (decide (k + 2 = k) || decide (k + 2 = k + 1)) then
            0
          else 1) = Finset.sum (filter (fun i => x i) univ) (fun _ => 1) := by
        refine Finset.sum_congr (by ext; simp) (fun i hi => ?_)
        have hxi : x i = true := by simp at hi; exact hi
        rw [h_term_pos i hxi]

      have h_sum_neg : (∑ x_1 with x x_1 = false,
          if
              (decide ((if x x_1 = true then k + 1 else k + 3) = k) ||
                  decide ((if x x_1 = true then k + 1 else k + 3) = k + 1)) =
                (decide (k + 2 = k) || decide (k + 2 = k + 1)) then
            0
          else 1) = Finset.sum (filter (fun i => x i = false) univ) (fun _ => 0) := by
        refine Finset.sum_congr (by ext; simp) (fun i hi => ?_)
        have hxi : x i = false := by simp at hi; exact hi
        have hxi' : !x i := by simp [hxi]
        rw [h_term_neg i hxi']

      have h_union_set : {i | x i = true} ∪ {i | x i = false} = Set.univ := by
        ext i
        simp
        apply Bool.eq_true_or_eq_false

      have h_card_simpl : #({i ∈ {i | x i = true} ∪ {i | x i = false} | x i = true}) = w := by
        rw [h_union_set]
        simp
        exact hw.symm
      rw [h_card_simpl]
      rw [hw_kp2]

      rw [← hk]
      rw [h_sum_pos, h_sum_neg]
      rw [Finset.sum_const, Finset.sum_const]
      simp
      omega

    -- Other cases
    have h_not_in : w ∉ {k, k + 1} := by
      simp
      omega
    simp [h_not_in]

    have h_wm1_not_in : w - 1 ∉ {k, k + 1} := by
      simp
      omega
    have h_wp1_not_in : w + 1 ∉ {k, k + 1} := by
      simp
      omega

    have h_sum_pos : (∑ x_1 with x x_1 = true,
          if
              (decide ((if x x_1 = true then w - 1 else w + 1) = k) ||
                  decide ((if x x_1 = true then w - 1 else w + 1) = k + 1)) =
                (decide (w = k) || decide (w = k + 1)) then
            0
          else 1) = Finset.sum (filter (fun i => x i) univ) (fun _ => 0) := by
      refine Finset.sum_congr (by ext; simp) (fun i hi => ?_)
      have hxi : x i = true := by simp at hi; exact hi
      rw [if_pos hxi]
      simp [hw]
      simp [target, hk2, hxi, h_wm1_not_in, h_not_in]
      show (if (decide (w - 1 = k) || decide (w - 1 = k + 1)) = (decide (w = k) || decide (w = k + 1)) then 0 else 1) = 0
      simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      simp [h_wm1_not_in, h_not_in]

    have h_sum_neg : (∑ x_1 with x x_1 = false,
          if
              (decide ((if x x_1 = true then w - 1 else w + 1) = k) ||
                  decide ((if x x_1 = true then w - 1 else w + 1) = k + 1)) =
                (decide (w = k) || decide (w = k + 1)) then
            0
          else 1) = Finset.sum (filter (fun i => x i = false) univ) (fun _ => 0) := by
      refine Finset.sum_congr (by ext; simp) (fun i hi => ?_)
      have hxi : x i = false := by simp at hi; exact hi
      rw [if_neg (by simp [hxi])]
      simp [hw]
      simp [target, hk2, hxi, h_wp1_not_in, h_not_in]
      show (if (decide (w + 1 = k) || decide (w + 1 = k + 1)) = (decide (w = k) || decide (w = k + 1)) then 0 else 1) = 0
      simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      simp [h_wp1_not_in, h_not_in]

    rw [h_sum_pos, h_sum_neg]
    simp
    omega

  · -- Lower bound
    let k := n / 2
    let x : Fin n → Bool := fun i => i.val < k + 2
    have hx : x ∈ univ := by simp
    refine le_trans ?_ (Finset.le_sup hx)
    unfold sensitivityAt nisanExample

    let w := #{i | x i}
    have hw : w = k + 2 := by
      simp [x]
      rw [Finset.card_eq_sum_ones]
      simp
      rw [← Finset.card_range (k+2)]
      congr
      ext i
      simp
      constructor
      · intro h; exact h
      · intro h
        have : k + 2 ≤ n := by
          rw [hk]
          apply Nat.add_le_of_le_sub
          rw [Nat.sub_eq_of_eq_add hn_eq.symm]
          rw [← Nat.div_two_mul_two_of_dvd hn] at hn_eq
          apply Nat.le_div_iff_mul_le (by norm_num) |>.mpr
          exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hn
        apply lt_of_lt_of_le h this

    have hk : n/2 = k := rfl
    rw [hk]
    rw [← hw]
    let target : Finset ℕ := {k, k + 1}

    have h_w_eq : #{j | x j = true} = w := by simp

    have h_val : ∀ y, nisanExample n y = (decide (#{i | y i} ∈ target)) := by
      intro y
      rfl
    simp only [h_val]

    have h_flip_weight : ∀ i, #{j | (flip x {i}) j} = if x i then k + 1 else k + 3 := by
      intro i
      simp [flip]
      by_cases hi : x i
      · rw [if_pos hi]
        have : filter (fun j => (if j = i then !x j else x j)) univ = filter (fun j => x j) univ \ {i} := by
          ext j
          simp
          by_cases hji : j = i
          · rw [hji]; simp [hi]
          · simp [hji]
        have h_goal_eq : #{j | if j = i then x j = false else x j = true} = (filter (fun j => (if j = i then !x j else x j)) univ).card := by
          congr; ext j; simp; split_ifs <;> simp
        rw [h_goal_eq]
        rw [this]
        have h_subset : {i} ⊆ filter (fun j => x j) univ := by
          rw [Finset.singleton_subset_iff]
          rw [mem_filter]
          simp [hi]
        rw [Finset.card_sdiff h_subset]
        rw [h_w_eq, hw, Finset.card_singleton]
        simp
      · rw [if_neg hi]
        have : filter (fun j => (if j = i then !x j else x j)) univ = filter (fun j => x j) univ ∪ {i} := by
          ext j
          simp
          by_cases hji : j = i
          · rw [hji]; simp [hi]
          · simp [hji]
        have h_goal_eq : #{j | if j = i then x j = false else x j = true} = (filter (fun j => (if j = i then !x j else x j)) univ).card := by
          congr; ext j; simp; split_ifs <;> simp
        rw [h_goal_eq]
        rw [this]
        have h_disj : Disjoint (filter (fun j => x j) univ) {i} := by
          rw [Finset.disjoint_singleton_right]
          rw [mem_filter]
          simp [hi]
        rw [Finset.card_union_of_disjoint h_disj]
        rw [h_w_eq, hw, Finset.card_singleton]
        simp

    simp only [h_flip_weight]

    have h_in_target : k + 1 ∈ target := by simp [target]
    have h_not_in_target : k + 2 ∉ target := by simp [target]; omega
    have h_not_in_target3 : k + 3 ∉ target := by simp [target]; omega

    -- Rewrite w as a sum
    have h_lhs_split : w = Finset.sum (filter (fun i => x i) univ) (fun _ => 1) + Finset.sum (filter (fun i => !x i) univ) (fun _ => 0) := by
      rw [Finset.sum_const_zero]
      rw [add_zero]
      rw [← h_w_eq]
      rw [Finset.card_eq_sum_ones]
      congr
      ext i
      simp
    rw [h_lhs_split]

    change (Finset.sum (filter (fun i => x i) univ) (fun _ => 1) + Finset.sum (filter (fun i => !x i) univ) (fun _ => 0)) ≤ _

    -- Now rewrite RHS
    conv_rhs =>
      rw [Finset.card_eq_sum_ones]
      rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => x i)]

    apply add_le_add
    · apply Finset.sum_le_sum
      intro i hi
      simp at hi
      simp [hi]
      simp [h_in_target, h_not_in_target, h_not_in_target3]
      -- x i is true. flip weight is k+1. k+1 in target (true).
      -- x weight is k+2. k+2 not in target (false).
      -- true != false is true.
      -- term is 1.
      simp [target]
    · apply Finset.sum_le_sum
      intro i hi
      simp at hi
      simp [hi]
      simp [h_in_target, h_not_in_target, h_not_in_target3]
      -- x i is false. flip weight is k+3. k+3 not in target (false).
      -- x weight is k+2. k+2 not in target (false).
      -- false != false is false.
      -- term is 0.
      simp [target]
      omega

    simp [hw]
    omega


/-- Assuming `n` is a multiple of 4, the block sensitivity of `nisanExample`
is `3n/4`, achieved by any `x` with Hamming weight `n/2`.
An optimal block configuration uses all `n/2` 1-bits as singleton blocks
and forms `n/4` disjoint size-2 blocks from the 0-bits. -/
@[category test, AMS 68]
lemma nisanExample_blockSensitivity (n : ℕ) (hn : 4 ∣ n) :
    blockSensitivity (nisanExample n) = 3 * n / 4 := by
  sorry

end Sensitivity
end StrongSensitivityConjecture
