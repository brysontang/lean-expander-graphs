/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.ConfigurationModelBinomial

/-!
# Asymptotic estimate for the closed-set first moment

The constant `1 / 1000` is deliberately small. The sum includes only nonempty vertex sets
of size at most half the vertices, and the pairing count is zero on odd inputs.

The key estimate is `closedCutTerm_le_geometric`: the vertex sets of size `s` contribute at
most `(100 / n) * (3 / 4) ^ s`. Its numerical content is in `ConfigurationModelBinomial`. With
`M = pairingCount`, `N = n * d` and `a = d * s - k`, the proof runs as follows.

* Summands with `a` odd vanish. For `a` even, the identity
  `M a * M (N - a) * C (N, a) = M N * C (N / 2, a / 2)` and the Vandermonde bound
  `C (N / 2, a / 2) ^ 2 ≤ C (N, a)` give `(M a * M (N - a)) ^ 2 * C (N, a) ≤ M N ^ 2`.
* Super-multiplicativity gives `C (n, s) ^ (d - 1) * C (n, s - k) ≤ C (N, a)`. Below the
  middle, `C (n, j) ≥ 2 ^ j` and, for `j ≥ 2`, `n ^ 2 * 2 ^ j ≤ 8 j ^ 2 * C (n, j)`; these
  supply the geometric decay and the factor `1 / n`. For `d = 3` and `s = 1` these bounds are
  too weak, but there the only summand has `a = 3` and vanishes by parity.
* Summands with `k > 0` occur only for `s > 1000`. There `C (d s, k) ≤ (d s) ^ k / k !` and
  `x ^ k / k ! ≤ exp x` with `x = s / 1000` bound the extra factors by `c ^ s` with `c` barely
  above `1`.
* So each summand, divided by `M N`, is at most `(100 / n) * (3 / 4) ^ s / 2 ^ (k + 1)`
  (`closedCutSummand_le`), and the weights `1 / 2 ^ (k + 1)` sum to at most one.

Summing the envelope over `s` gives `400 / n`, which tends to zero.
-/

open Finset Filter Topology

namespace ConfigurationModel

open Classical in
/-- Contribution of vertex sets of size `s` to the normalized closed-set union bound. -/
noncomputable def closedCutTerm (n d s : ℕ) (ε : ℝ) : ℝ :=
  ((n.choose s *
    ∑ k ∈ (range (d * s + 1)).filter (fun k : ℕ => (k : ℝ) < ε * s),
      (d * s).choose k * pairingCount (d * s - k) *
        pairingCount (n * d - (d * s - k)) : ℕ) : ℝ) / pairingCount (n * d)

/-- Rewrite the normalized integer count as a sum of real contributions. -/
theorem closedCutBound_div_eq_sum (n d : ℕ) (ε : ℝ) :
    (closedCutBound n d ε : ℝ) / pairingCount (n * d) =
      ∑ s ∈ Icc 1 (n / 2), closedCutTerm n d s ε := by
  simp only [closedCutBound, closedCutTerm, Nat.cast_sum, sum_div]

/-- A singleton cannot have zero crossing points in degree three: its three points cannot
pair internally. Since `1 / 1000 < 1`, the singleton contribution is zero. -/
theorem closedCutTerm_three_one (n : ℕ) : closedCutTerm n 3 1 (1 / 1000) = 0 := by
  norm_num [closedCutTerm, sum_filter, sum_range_succ, pairingCount]

/-- Small-case check: on four cubic vertices the closed two-vertex-cut term is `10 / 77`. -/
example : closedCutTerm 4 3 2 (1 / 1000) = 10 / 77 := by
  norm_num [closedCutTerm, sum_filter, sum_range_succ, pairingCount, Nat.doubleFactorial, Nat.choose]

/-- Small-case check: a singleton with two internal pairs contributes in even degree. -/
example : closedCutTerm 2 4 1 (1 / 1000) = 6 / 35 := by
  norm_num [closedCutTerm, sum_filter, sum_range_succ, pairingCount, Nat.doubleFactorial, Nat.choose]

/-- **Uniform numerical estimate.** A geometric envelope for each cut size, including the
factor `1 / n`.

Each summand of `closedCutTerm`, divided by `pairingCount (n * d)`, is at most
`(100 / n) * (3 / 4) ^ s / 2 ^ (k + 1)`. This is `closedCutSummand_le`, proved in
`ConfigurationModelBinomial` from the exact identity for pairing counts, Vandermonde-type
bounds for binomial coefficients, and, for the summands with `k > 0` (which occur only when
`s > 1000`), the bound `x ^ k / k ! ≤ exp x`. Summing the weights `1 / 2 ^ (k + 1)` over `k`
gives the claim. For `d = 3` and `s = 1` the binomial bounds are too weak, but the only summand
vanishes because `pairingCount 3 = 0`. -/
theorem closedCutTerm_le_geometric {n d s : ℕ} (hd : 3 ≤ d)
    (hn : Even (n * d)) (hs : 1 ≤ s) (hhalf : 2 * s ≤ n) :
    closedCutTerm n d s (1 / 1000) ≤ (100 / (n : ℝ)) * (3 / 4 : ℝ) ^ s := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hM : (0 : ℝ) < pairingCount (n * d) := by exact_mod_cast pairingCount_pos hn
  have hB0 : (0 : ℝ) ≤ (100 / (n : ℝ)) * (3 / 4 : ℝ) ^ s := by positivity
  -- each summand is bounded by the envelope times a geometric weight
  have hterm : ∀ k : ℕ, (k : ℝ) < 1 / 1000 * s →
      ((n.choose s * ((d * s).choose k * pairingCount (d * s - k) *
        pairingCount (n * d - (d * s - k))) : ℕ) : ℝ) / pairingCount (n * d) ≤
          (100 / (n : ℝ)) * (3 / 4 : ℝ) ^ s * (1 / 2) ^ (k + 1) := by
    intro k hk
    have hk' : 1000 * k < s := by
      have h2 : ((1000 * k : ℕ) : ℝ) < s := by
        push_cast
        linarith
      exact_mod_cast h2
    have hreal : ((n.choose s * ((d * s).choose k * pairingCount (d * s - k) *
        pairingCount (n * d - (d * s - k))) : ℕ) : ℝ) * ((n : ℝ) * 4 ^ s * 2 ^ (k + 1)) ≤
          100 * 3 ^ s * pairingCount (n * d) := by
      exact_mod_cast closedCutSummand_le hd hn hs hhalf hk'
    have hpos : (0 : ℝ) < (n : ℝ) * 4 ^ s * 2 ^ (k + 1) := by positivity
    have hrew : (100 / (n : ℝ)) * (3 / 4 : ℝ) ^ s * (1 / 2) ^ (k + 1) * pairingCount (n * d) =
        (100 * 3 ^ s * pairingCount (n * d)) / ((n : ℝ) * 4 ^ s * 2 ^ (k + 1)) := by
      rw [div_pow, div_pow, one_pow]
      field_simp
    rw [div_le_iff₀ hM, hrew, le_div_iff₀ hpos]
    exact hreal
  -- the geometric weights sum to at most one
  have hgeo : ∀ m : ℕ, ∑ k ∈ range m, (1 / 2 : ℝ) ^ (k + 1) = 1 - (1 / 2) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, ih]
      ring
  unfold closedCutTerm
  rw [mul_sum, Nat.cast_sum, sum_div]
  calc
    _ ≤ ∑ k ∈ (range (d * s + 1)).filter (fun k : ℕ => (k : ℝ) < 1 / 1000 * s),
        (100 / (n : ℝ)) * (3 / 4 : ℝ) ^ s * (1 / 2) ^ (k + 1) :=
      sum_le_sum fun k hk => hterm k (mem_filter.mp hk).2
    _ ≤ ∑ k ∈ range (d * s + 1), (100 / (n : ℝ)) * (3 / 4 : ℝ) ^ s * (1 / 2) ^ (k + 1) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
    _ = (100 / (n : ℝ)) * (3 / 4 : ℝ) ^ s * (1 - (1 / 2) ^ (d * s + 1)) := by
      rw [← mul_sum, hgeo]
    _ ≤ (100 / (n : ℝ)) * (3 / 4 : ℝ) ^ s := by
      have hp : (0 : ℝ) < (1 / 2) ^ (d * s + 1) := by positivity
      nlinarith [mul_nonneg hB0 hp.le]

/-- Summing the geometric envelope gives an explicit `O(1/n)` bound. -/
theorem closedCutBound_div_le {n d : ℕ} (hd : 3 ≤ d) (hn : Even (n * d)) :
    (closedCutBound n d (1 / 1000) : ℝ) / pairingCount (n * d) ≤ 400 / (n : ℝ) := by
  rw [closedCutBound_div_eq_sum]
  have hsum : ∑ s ∈ Icc 1 (n / 2), (3 / 4 : ℝ) ^ s ≤ 4 := by
    have h := (summable_geometric_of_lt_one (r := (3 / 4 : ℝ))
      (by norm_num) (by norm_num)).sum_le_tsum (Icc 1 (n / 2)) (fun _ _ => by positivity)
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h
    norm_num at h ⊢
    exact h
  calc
    _ ≤ ∑ s ∈ Icc 1 (n / 2), (100 / (n : ℝ)) * (3 / 4 : ℝ) ^ s := by
      apply sum_le_sum
      intro s hs
      exact closedCutTerm_le_geometric hd hn (mem_Icc.mp hs).1 (by
        have := (mem_Icc.mp hs).2
        omega)
    _ = (100 / (n : ℝ)) * ∑ s ∈ Icc 1 (n / 2), (3 / 4 : ℝ) ^ s := (mul_sum _ _ _).symm
    _ ≤ (100 / (n : ℝ)) * 4 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 400 / (n : ℝ) := by ring

/-- The numerical first-moment estimate, uniform over all cut sizes. -/
theorem tendsto_closedCutBound_div {d : ℕ} (hd : 3 ≤ d) :
    Tendsto (fun n => (closedCutBound n d (1 / 1000) : ℝ) / pairingCount (n * d))
      (atTop ⊓ 𝓟 {n | Even (n * d)}) (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((tendsto_const_div_atTop_nhds_zero_nat (400 : ℝ)).mono_left inf_le_left) ?_ ?_
  · exact Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rw [eventually_inf_principal]
    exact Filter.Eventually.of_forall fun n hn => closedCutBound_div_le hd hn

end ConfigurationModel
