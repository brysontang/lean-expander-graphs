/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.ConfigurationModelSwitching

/-!
# Lemma A: a positive proportion of pairings is simple

For every degree `d`, the proportion of simple pairings among the pairings of `n * d` points is
bounded below by a positive constant, uniformly in large `n`. This is one of the two inputs of
the reduction `ConfigurationModel.tendsto_card_regular_isEdgeExpander_div`; the other is in
`Expanders/ConfigurationModelExpansion.lean`.

## Main results
* `ConfigurationModel.exp_mul_card_pairings_le`: the explicit bound. For `n ≥ 8d + 8`,

  `exp (-(4d + 8d²)) * #{pairings} ≤ #{simple pairings}`.

* `ConfigurationModel.exists_simple_card_lower_bound`: the statement used by the reduction.

## Proof
The combinatorics is in `Expanders/ConfigurationModelSwitching.lean`: with `K = n d - 2d(d + 1)`,
switchings give

`((K - d) * (K² - n d³)) ^ (n d) * #{pairings} ≤ (K * K²) ^ (n d) * #{simple pairings}`.

For `n ≥ 8d + 8` one has `K ≥ n d / 2`, hence `(K - d) / K ≥ 1 - 2 / n` and
`(K² - n d³) / K² ≥ 1 - 4d / n`, and `(1 - t) ^ M ≥ exp (-2 t M)` for `0 ≤ t ≤ 1 / 2`.

The constant is far from the truth: the proportion of simple pairings converges to
`exp (-(d² - 1) / 4)` (Bender–Canfield 1978, Bollobás 1980).

## References
* E. A. Bender, E. R. Canfield, *The asymptotic number of labeled graphs with given degree
  sequences*, J. Combin. Theory Ser. A 24 (1978), 296–307.
* B. Bollobás, *A probabilistic proof of an asymptotic formula for the number of labelled regular
  graphs*, European J. Combin. 1 (1980), 311–316.
* B. D. McKay, *Asymptotics for symmetric 0-1 matrices with prescribed row sums*,
  Ars Combin. 19A (1985), 15–25. (The switching method.)
-/

open Finset

namespace ConfigurationModel

/-- `exp (-2t) ≤ 1 - t` for `0 ≤ t ≤ 1 / 2`. -/
private theorem exp_neg_two_mul_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    Real.exp (-(2 * t)) ≤ 1 - t := by
  have h := Real.add_one_le_exp (2 * t)
  have hpos : (0 : ℝ) < 2 * t + 1 := by linarith
  rw [Real.exp_neg]
  calc (Real.exp (2 * t))⁻¹ ≤ (2 * t + 1)⁻¹ := inv_anti₀ hpos h
    _ ≤ 1 - t := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith

/-- `exp (-2 t M) ≤ (1 - t) ^ M` for `0 ≤ t ≤ 1 / 2`. -/
private theorem exp_le_one_sub_pow {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) (M : ℕ) :
    Real.exp (-(2 * t * M)) ≤ (1 - t) ^ M := by
  calc Real.exp (-(2 * t * M)) = Real.exp (-(2 * t)) ^ M := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
    _ ≤ (1 - t) ^ M := pow_le_pow_left₀ (Real.exp_pos _).le (exp_neg_two_mul_le h0 h1) M

/-- **A positive proportion of pairings is simple, explicitly.** For `n ≥ 8d + 8`, at least a
proportion `exp (-(4d + 8d²))` of the pairings of `n * d` points is simple. (No parity
assumption is needed: for `n * d` odd both sides are `0`.) -/
theorem exp_mul_card_pairings_le {n d : ℕ} (hn : 8 * d + 8 ≤ n) :
    Real.exp (-(4 * d + 8 * d ^ 2)) * #(pairings n d) ≤ #(simplePairings n d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h := switching_card_bound n 0
    simp only [mul_zero, pow_zero, one_mul] at h
    simpa using (Nat.cast_le (α := ℝ)).mpr h
  -- Natural number facts about `K = n d - 2d(d + 1)`.
  have hX : d ≤ (d + 1) * d := Nat.le_mul_of_pos_left d (Nat.succ_pos d)
  have hM : 8 * ((d + 1) * d) ≤ n * d := by
    calc 8 * ((d + 1) * d) = (8 * d + 8) * d := by ring
      _ ≤ n * d := Nat.mul_le_mul_right d hn
  have h2K : n * d ≤ 2 * goodCount n d := by
    unfold goodCount
    omega
  have hdK : d ≤ goodCount n d := by
    unfold goodCount
    omega
  have hsq : n * d * d * d ≤ goodCount n d ^ 2 := by
    have h4 : (n * d) ^ 2 ≤ (2 * goodCount n d) ^ 2 := Nat.pow_le_pow_left h2K 2
    have h5 : n * d * (8 * ((d + 1) * d)) ≤ n * d * (n * d) := Nat.mul_le_mul_left _ hM
    nlinarith [h4, h5, Nat.zero_le (n * d * d)]
  -- The same facts over the reals.
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hn8 : (8 : ℝ) * d + 8 ≤ n := by exact_mod_cast hn
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (goodCount n d : ℝ) := ⟨_, rfl⟩
  have h2K' : (n : ℝ) * d ≤ 2 * k := by
    rw [hk]
    exact_mod_cast h2K
  have hdK' : (d : ℝ) ≤ k := by
    rw [hk]
    exact_mod_cast hdK
  have hkpos : 0 < k := hd0.trans_le hdK'
  -- The two ratios.
  have ht1 : (2 : ℝ) / n ≤ 1 / 2 := by
    rw [div_le_iff₀ hn0]
    linarith
  have ht2 : (4 : ℝ) * d / n ≤ 1 / 2 := by
    rw [div_le_iff₀ hn0]
    linarith
  have ht1' : (0 : ℝ) ≤ 2 / n := by positivity
  have ht2' : (0 : ℝ) ≤ 4 * d / n := by positivity
  have hr1 : (1 - 2 / n) * k ≤ k - d := by
    have h : (d : ℝ) ≤ 2 / n * k := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hn0]
      linarith
    linarith
  have hr2 : (1 - 4 * d / n) * k ^ 2 ≤ k ^ 2 - n * d * d * d := by
    have hsq' : ((n : ℝ) * d) ^ 2 ≤ (2 * k) ^ 2 := pow_le_pow_left₀ (by positivity) h2K' 2
    have h : (n : ℝ) * d * d * d ≤ 4 * d / n * k ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hn0]
      nlinarith [mul_le_mul_of_nonneg_left hsq' hd0.le]
    linarith
  -- The switching bound over the reals.
  have hsw : ((k - d) * (k ^ 2 - n * d * d * d)) ^ (n * d) * (#(pairings n d) : ℝ)
      ≤ (k * k ^ 2) ^ (n * d) * #(simplePairings n d) := by
    have h := (Nat.cast_le (α := ℝ)).mpr (switching_card_bound n d)
    push_cast [Nat.cast_sub hdK, Nat.cast_sub hsq] at h
    rw [← hk] at h
    exact h
  have hprod : ((1 - 2 / n) * (1 - 4 * d / n)) * (k * k ^ 2)
      ≤ (k - d) * (k ^ 2 - n * d * d * d) := by
    calc ((1 - 2 / n) * (1 - 4 * d / n)) * (k * k ^ 2)
        = ((1 - 2 / n) * k) * ((1 - 4 * d / n) * k ^ 2) := by ring
      _ ≤ (k - d) * (k ^ 2 - n * d * d * d) :=
          mul_le_mul hr1 hr2 (mul_nonneg (by linarith) (by positivity)) (by linarith)
  have hkk : (0 : ℝ) < (k * k ^ 2) ^ (n * d) := by positivity
  have hmain : ((1 - 2 / n) * (1 - 4 * d / n)) ^ (n * d) * (#(pairings n d) : ℝ)
      ≤ #(simplePairings n d) := by
    refine le_of_mul_le_mul_left ?_ hkk
    calc (k * k ^ 2) ^ (n * d) * (((1 - 2 / n) * (1 - 4 * d / n)) ^ (n * d)
          * (#(pairings n d) : ℝ))
        = (((1 - 2 / n) * (1 - 4 * d / n)) * (k * k ^ 2)) ^ (n * d) * #(pairings n d) := by
          rw [mul_pow (((1 : ℝ) - 2 / n) * (1 - 4 * d / n))]
          ring
      _ ≤ ((k - d) * (k ^ 2 - n * d * d * d)) ^ (n * d) * #(pairings n d) :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by linarith) (by linarith))
              (by positivity)) hprod _) (Nat.cast_nonneg _)
      _ ≤ (k * k ^ 2) ^ (n * d) * #(simplePairings n d) := hsw
  -- The exponential lower bound for the two ratios.
  have he1 := exp_le_one_sub_pow ht1' ht1 (n * d)
  have he2 := exp_le_one_sub_pow ht2' ht2 (n * d)
  have hexp : Real.exp (-(4 * d + 8 * d ^ 2))
      ≤ ((1 - 2 / n) * (1 - 4 * d / n)) ^ (n * d) := by
    have hsplit : Real.exp (-(4 * (d : ℝ) + 8 * d ^ 2))
        = Real.exp (-(2 * (2 / n) * ((n * d : ℕ) : ℝ)))
          * Real.exp (-(2 * (4 * d / n) * ((n * d : ℕ) : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    rw [hsplit, mul_pow]
    exact mul_le_mul he1 he2 (Real.exp_pos _).le (pow_nonneg (by linarith) _)
  exact (mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg _)).trans hmain

/-- **Lemma A (simplicity).** For every degree `d`, a positive proportion of the pairings of
`n * d` points is simple, uniformly in large `n` with `n * d` even.

The proof is by switchings (`ConfigurationModel.switching_card_bound`) and gives the explicit
constant `c = exp (-(4d + 8d²))` for `n ≥ 8d + 8`; see `exp_mul_card_pairings_le`. In fact the
proportion of simple pairings converges to `exp (-(d² - 1) / 4)` for `d ≥ 1`
(Bender–Canfield 1978, Bollobás 1980).

Remarks on the statement. For `d = 0` (no points, one empty pairing) and `d = 1` (every vertex
has a single point) every pairing is simple. The threshold `N` cannot be dropped: for
`0 < n ≤ d` with `n * d` even there are pairings but no simple ones, since a `d`-regular simple
graph needs more than `d` vertices. For `n * d` odd there are no pairings at all and the
inequality reads `0 ≤ 0`; the hypothesis `Even (n * d)` is not used by the proof. -/
theorem exists_simple_card_lower_bound (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
      c * #(pairings n d) ≤ #(simplePairings n d) :=
  ⟨Real.exp (-(4 * d + 8 * d ^ 2)), Real.exp_pos _, 8 * d + 8,
    fun _ hn _ => exp_mul_card_pairings_le hn⟩

end ConfigurationModel
