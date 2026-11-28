/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Mathlib

/-!
# Two-type trickling down, part 1: the algebra

This file holds everything about the two-type bound that involves no sums: the bound `β(p, q)`
itself, its properties, the sign certificates of the side polynomials, and the per-triangle
quadratic forms of the certificate. The theorem it serves is in
`Expanders/TwoTypeTricklingDown.lean`; the module docstring there states the result.

## The bound

With
* `b = p³ + 4p²q − 7p² − 13pq + 14p + 7q − 2`,
* `c = p³ + 2p²q − 4p² − 3pq + p + q`,
* `L = 2 (1 − q)(2 − p)(3 − p)`,
* `N(μ) = L μ² − b μ − c` (`twoTypeN`),
* `Δ = p⁴ − 8p³ + 6p²q + 20p² − 24pq − 16p + q² + 20q + 4` (`twoTypeDelta`), so that
  `4 L N(μ) = (2Lμ − b)² − (1 + p)² Δ`,

the bound is the larger root of `N`, `β(p, q) = (b + (1 + p) √Δ) / (4 (1 − q)(2 − p)(3 − p))`
(`twoTypeBound`).

## Theorems
* `twoTypeN_half`, `four_mul_twoTypeN`: `N(p/2) = −q (1 − p)(1 + p)² (2 − p)/2 ≤ 0` and the
  discriminant identity. **Proved.**
* `twoTypeDelta_nonneg`, `half_le_twoTypeBound`, `twoTypeN_pos_of_lt`,
  `twoTypeBound_lt_of_twoTypeN_pos`: for `0 ≤ q < 1`, `0 ≤ p ≤ 1/2`, `β` is a real root, at
  least `p/2`, and above `p/2` the sign of `N` decides the comparison with `β`. **Proved.**
* `twoTypeBound_zero`, `twoTypeBound_self`: `β(p, 0) = p/2` and `β(p, p) = p/(1 − p)`.
  **Proved.**
* `twoTypeBound_lt_edgeAverage`: `β(p, q) < (p + q)/(2 − p − q)` for `0 ≤ q < p ≤ 1/2`.
  **Proved.**
* `sideP2_neg`, `sideP3_neg`, `sideP5_pos`: signs of three polynomials on the region
  `0 < p ≤ 1/2`, `p/2 ≤ μ ≤ p/(1 − p)`, by exact Bernstein certificates. **Proved.**
* `TwoTypeMultipliers`, `triJ`, `triQ`: the integrand of the certificate and its symmetrisation
  over the six orderings of a triangle.
* `triQ_QQQ`, `triQ_PQQ`: decompositions of the per-triangle form with free multipliers.
  **Proved** (`ring`).
* `TwoTypeMultipliers.Good`, `triQ_QQQ_nonpos`, `triQ_PQQ_nonpos`: the sign conditions on the
  multipliers, and the resulting nonpositivity and rigidity of the per-triangle forms. **Proved.**
* `twoTypeMult`, `twoTypeMult_*`: the explicit multipliers in closed form and the exact identities
  behind their signs. **Proved.**
* `exists_good`: explicit multipliers satisfying the sign conditions whenever
  `0 < p ≤ 1/2`, `p/2 ≤ μ ≤ p/(1 − p)`, `μ < 1` and `N(μ) > 0`. **Proved.**
* `twoType_package`: `β` and `N` in terms of three atoms, for later comparisons. **Proved.**

The identities were first checked with sympy (`.lake/scratch-cert/lean/check_forms.py` and
`gen_bernstein.py`, which also generated the Bernstein certificates); the proofs below do not rely
on those checks.
-/

namespace TwoTypeTricklingDown

/-! ### The bound `β(p, q)` -/

/-- The quadratic `N(μ) = 2 (1 − q)(2 − p)(3 − p) μ² − b μ − c` whose larger root is the two-type
bound. It is linear in `q`. Its sign above `p/2` decides whether `μ` exceeds the bound
(`twoTypeN_pos_of_lt`, `twoTypeBound_lt_of_twoTypeN_pos`). -/
def twoTypeN (p q μ : ℝ) : ℝ :=
  2 * (1 - q) * (2 - p) * (3 - p) * μ ^ 2
    - (p ^ 3 + 4 * p ^ 2 * q - 7 * p ^ 2 - 13 * p * q + 14 * p + 7 * q - 2) * μ
    - (p ^ 3 + 2 * p ^ 2 * q - 4 * p ^ 2 - 3 * p * q + p + q)

/-- The discriminant `Δ` of `twoTypeN`, divided by `(1 + p)²`. It is nonnegative on
`0 ≤ p ≤ 1/2`, `0 ≤ q < 1` (`twoTypeDelta_nonneg`); outside that range it can be negative, and
then `Real.sqrt` reads it as `0`. -/
def twoTypeDelta (p q : ℝ) : ℝ :=
  p ^ 4 - 8 * p ^ 3 + 6 * p ^ 2 * q + 20 * p ^ 2 - 24 * p * q - 16 * p + q ^ 2 + 20 * q + 4

/-- **The two-type bound** `β(p, q) = (b + (1 + p) √Δ) / (4 (1 − q)(2 − p)(3 − p))`, the larger
root of `twoTypeN p q`. Special values: `β(p, 0) = p/2` (`twoTypeBound_zero`) and
`β(p, p) = p/(1 − p)` (`twoTypeBound_self`), for `0 ≤ p ≤ 1/2`.

The formula is meant for `0 ≤ q ≤ p ≤ 1/2`, where `Δ ≥ 0` and the denominator is positive.
Outside that range it is still a real number (Lean's `Real.sqrt` of a negative number is `0`,
and division by `0` gives `0`), but none of the theorems here say anything about it. -/
noncomputable def twoTypeBound (p q : ℝ) : ℝ :=
  ((p ^ 3 + 4 * p ^ 2 * q - 7 * p ^ 2 - 13 * p * q + 14 * p + 7 * q - 2)
    + (1 + p) * Real.sqrt (twoTypeDelta p q)) / (4 * (1 - q) * (2 - p) * (3 - p))

/-- The discriminant identity `4 L N(μ) = (2 L μ − b)² − (1 + p)² Δ`, `L = 2 (1 − q)(2 − p)(3 − p)`.
No hypotheses. -/
theorem four_mul_twoTypeN (p q μ : ℝ) :
    4 * (2 * (1 - q) * (2 - p) * (3 - p)) * twoTypeN p q μ =
      (2 * (2 * (1 - q) * (2 - p) * (3 - p)) * μ
        - (p ^ 3 + 4 * p ^ 2 * q - 7 * p ^ 2 - 13 * p * q + 14 * p + 7 * q - 2)) ^ 2
        - (1 + p) ^ 2 * twoTypeDelta p q := by
  unfold twoTypeN twoTypeDelta
  ring

/-- `N(p/2) = −q (1 − p)(1 + p)² (2 − p) / 2`, which is `≤ 0` for `q ≥ 0` and `−1 ≤ p ≤ 1`. No
hypotheses. -/
theorem twoTypeN_half (p q : ℝ) :
    twoTypeN p q (p / 2) = -q * (1 - p) * (1 + p) ^ 2 * (2 - p) / 2 := by
  unfold twoTypeN
  ring

/-- The hypotheses under which `β` behaves: `0 ≤ p ≤ 1/2` and `0 ≤ q < 1`. Then `L > 0`. -/
private theorem twoTypeL_pos {p q : ℝ} (hp2 : p ≤ 1 / 2) (hq1 : q < 1) :
    0 < 2 * (1 - q) * (2 - p) * (3 - p) := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 2 - p := by linarith
  have h3 : 0 < 3 - p := by linarith
  positivity

/-- `N(p/2) ≤ 0` on the range of `β`. -/
private theorem twoTypeN_half_nonpos {p q : ℝ} (hp2 : p ≤ 1 / 2) (hq : 0 ≤ q) :
    twoTypeN p q (p / 2) ≤ 0 := by
  rw [twoTypeN_half]
  have h1 : 0 ≤ 1 - p := by linarith
  have h2 : 0 ≤ 2 - p := by linarith
  have : 0 ≤ q * (1 - p) * (1 + p) ^ 2 * (2 - p) := by positivity
  linarith

/-- **`Δ ≥ 0`** for `0 ≤ p ≤ 1/2`, `0 ≤ q < 1`: since `N(p/2) ≤ 0` and `L > 0`, the discriminant
identity gives `(1 + p)² Δ ≥ (L p − b)² ≥ 0`. -/
theorem twoTypeDelta_nonneg {p q : ℝ} (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ twoTypeDelta p q := by
  have hL := twoTypeL_pos hp2 hq1
  have hN := twoTypeN_half_nonpos hp2 hq
  have h4 := four_mul_twoTypeN p q (p / 2)
  generalize 2 * (1 - q) * (2 - p) * (3 - p) = L at hL h4
  generalize twoTypeN p q (p / 2) = N0 at hN h4
  generalize twoTypeDelta p q = Δ at h4 ⊢
  generalize 2 * L * (p / 2) - (p ^ 3 + 4 * p ^ 2 * q - 7 * p ^ 2 - 13 * p * q + 14 * p + 7 * q
    - 2) = a at h4
  have h1 : 0 < (1 + p) ^ 2 := by positivity
  have hLN : 4 * L * N0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hN
  have : 0 ≤ (1 + p) ^ 2 * Δ := by nlinarith [sq_nonneg a]
  exact nonneg_of_mul_nonneg_right (by linarith [mul_comm ((1 + p) ^ 2) Δ]) h1

/-- The quantities behind `β`, as atoms: for `0 ≤ p ≤ 1/2` and `0 ≤ q < 1` there are `L > 0`
(namely `2 (1 − q)(2 − p)(3 − p)`), `b` and `s = (1 + p) √Δ ≥ 0` with `β = (b + s)/(2L)`,
`4 L N(μ) = (2Lμ − b)² − s²` for every `μ`, and `−s ≤ L p − b ≤ s` (from `N(p/2) ≤ 0`). Used to
compare `β` with other numbers through the sign of `N`. -/
theorem twoType_package {p q : ℝ} (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) (hq : 0 ≤ q)
    (hq1 : q < 1) :
    ∃ L b s : ℝ, 0 < L ∧ 0 ≤ s ∧ twoTypeBound p q = (b + s) / (2 * L) ∧
      (∀ μ, 4 * L * twoTypeN p q μ = (2 * L * μ - b) ^ 2 - s ^ 2) ∧
      -s ≤ L * p - b ∧ L * p - b ≤ s := by
  have hL := twoTypeL_pos hp2 hq1
  have hΔ := twoTypeDelta_nonneg hp0 hp2 hq hq1
  have hs0 : 0 ≤ (1 + p) * Real.sqrt (twoTypeDelta p q) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hss : ((1 + p) * Real.sqrt (twoTypeDelta p q)) ^ 2 = (1 + p) ^ 2 * twoTypeDelta p q := by
    rw [mul_pow, Real.sq_sqrt hΔ]
  have h4 : ∀ μ, 4 * (2 * (1 - q) * (2 - p) * (3 - p)) * twoTypeN p q μ =
      (2 * (2 * (1 - q) * (2 - p) * (3 - p)) * μ
        - (p ^ 3 + 4 * p ^ 2 * q - 7 * p ^ 2 - 13 * p * q + 14 * p + 7 * q - 2)) ^ 2
        - ((1 + p) * Real.sqrt (twoTypeDelta p q)) ^ 2 := fun μ => by
    rw [hss]; exact four_mul_twoTypeN p q μ
  have hN := twoTypeN_half_nonpos hp2 hq
  have hβ : twoTypeBound p q =
      ((p ^ 3 + 4 * p ^ 2 * q - 7 * p ^ 2 - 13 * p * q + 14 * p + 7 * q - 2)
        + (1 + p) * Real.sqrt (twoTypeDelta p q)) / (2 * (2 * (1 - q) * (2 - p) * (3 - p))) := by
    unfold twoTypeBound
    congr 1
    ring
  have h4h := h4 (p / 2)
  generalize 2 * (1 - q) * (2 - p) * (3 - p) = L at hL h4 h4h hβ
  generalize (p ^ 3 + 4 * p ^ 2 * q - 7 * p ^ 2 - 13 * p * q + 14 * p + 7 * q - 2) = b
    at h4 h4h hβ
  generalize (1 + p) * Real.sqrt (twoTypeDelta p q) = s at hs0 h4 h4h hβ
  have hLN : 4 * L * twoTypeN p q (p / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hN
  have hsq : (L * p - b) ^ 2 ≤ s ^ 2 := by
    have : 2 * L * (p / 2) = L * p := by ring
    rw [this] at h4h
    linarith
  exact ⟨L, b, s, hL, hs0, hβ, h4, (abs_le_of_sq_le_sq' hsq hs0).1, (abs_le_of_sq_le_sq' hsq hs0).2⟩

/-- **`β ≥ p/2`** for `0 ≤ p ≤ 1/2`, `0 ≤ q < 1`. In particular the root is real. Equality holds
at `q = 0` (`twoTypeBound_zero`). -/
theorem half_le_twoTypeBound {p q : ℝ} (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) (hq : 0 ≤ q)
    (hq1 : q < 1) : p / 2 ≤ twoTypeBound p q := by
  obtain ⟨L, b, s, hL, hs0, hβ, -, -, hup⟩ := twoType_package hp0 hp2 hq hq1
  rw [hβ, le_div_iff₀ (by positivity)]
  have : p / 2 * (2 * L) = L * p := by ring
  linarith

/-- **Above `β`, `N` is positive.** For `0 ≤ p ≤ 1/2`, `0 ≤ q < 1` and `μ > β(p, q)`:
`N(μ) > 0`. -/
theorem twoTypeN_pos_of_lt {p q μ : ℝ} (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) (hq : 0 ≤ q)
    (hq1 : q < 1) (hμ : twoTypeBound p q < μ) : 0 < twoTypeN p q μ := by
  obtain ⟨L, b, s, hL, hs0, hβ, h4, -, -⟩ := twoType_package hp0 hp2 hq hq1
  rw [hβ, div_lt_iff₀ (by positivity)] at hμ
  have h1 : s < 2 * L * μ - b := by linarith
  have h2 : s ^ 2 < (2 * L * μ - b) ^ 2 := by nlinarith
  have h3 : 0 < 4 * L * twoTypeN p q μ := by rw [h4]; linarith
  by_contra hle
  push Not at hle
  have : 4 * L * twoTypeN p q μ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
  linarith

/-- **Positivity of `N` above `p/2` puts `t` above `β`.** For `0 ≤ p ≤ 1/2`, `0 ≤ q < 1`,
`t ≥ p/2` and `N(t) > 0`: `β(p, q) < t`. (Below `p/2` this can fail: `N` is also positive below
its smaller root.) -/
theorem twoTypeBound_lt_of_twoTypeN_pos {p q t : ℝ} (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) (hq : 0 ≤ q)
    (hq1 : q < 1) (ht : p / 2 ≤ t) (hN : 0 < twoTypeN p q t) : twoTypeBound p q < t := by
  obtain ⟨L, b, s, hL, hs0, hβ, h4, hlow, -⟩ := twoType_package hp0 hp2 hq hq1
  by_contra hle
  push Not at hle
  rw [hβ, le_div_iff₀ (by positivity)] at hle
  have h1 : 2 * L * t - b ≤ s := by linarith
  have h2 : L * p ≤ 2 * L * t := by nlinarith
  have h3 : (2 * L * t - b) ^ 2 ≤ s ^ 2 := sq_le_sq' (by linarith) h1
  have h5 : 0 < 4 * L * twoTypeN p q t := by positivity
  rw [h4] at h5
  linarith

/-- **`β(p, 0) = p/2`** for every `p ≤ 1/2` (negative `p` included): here `Δ = (p² − 4p + 2)²`
with `p² − 4p + 2 > 0`. This is the cone value. -/
theorem twoTypeBound_zero {p : ℝ} (hp2 : p ≤ 1 / 2) : twoTypeBound p 0 = p / 2 := by
  have hΔ : twoTypeDelta p 0 = (p ^ 2 - 4 * p + 2) ^ 2 := by unfold twoTypeDelta; ring
  have hpos : 0 ≤ p ^ 2 - 4 * p + 2 := by nlinarith
  have h2 : (2 - p) ≠ 0 := by intro h; linarith
  have h3 : (3 - p) ≠ 0 := by intro h; linarith
  unfold twoTypeBound
  rw [hΔ, Real.sqrt_sq hpos]
  field_simp
  ring

/-- **`β(p, p) = p/(1 − p)`** for `0 ≤ p ≤ 1/2`: Oppenheim's bound. Here
`Δ = ((2 − p)(1 + p))²`. -/
theorem twoTypeBound_self {p : ℝ} (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) :
    twoTypeBound p p = p / (1 - p) := by
  have hΔ : twoTypeDelta p p = ((2 - p) * (1 + p)) ^ 2 := by unfold twoTypeDelta; ring
  have hpos : 0 ≤ (2 - p) * (1 + p) := mul_nonneg (by linarith) (by linarith)
  have h1 : (1 - p) ≠ 0 := by intro h; linarith
  have h2 : (2 - p) ≠ 0 := by intro h; linarith
  have h3 : (3 - p) ≠ 0 := by intro h; linarith
  unfold twoTypeBound
  rw [hΔ, Real.sqrt_sq hpos, div_eq_div_iff (by positivity) h1]
  ring

/-- **`β` is strictly below the edge-average bound.** For `0 ≤ q < p ≤ 1/2`,
`β(p, q) < s/(1 − s)` with `s = (p + q)/2`, i.e. `β(p, q) < (p + q)/(2 − p − q)`. Indeed
`N(s/(1 − s)) (2 − p − q)² = (p − q) G` with `G = p (1 − p)(2 − p) + p q (1 + p) + 6 q² > 0`.
At `q = p` the two agree (`twoTypeBound_self`). -/
theorem twoTypeBound_lt_edgeAverage {p q : ℝ} (hq : 0 ≤ q) (hqp : q < p) (hp2 : p ≤ 1 / 2) :
    twoTypeBound p q < (p + q) / (2 - p - q) := by
  have hp0 : 0 < p := lt_of_le_of_lt hq hqp
  have hden : 0 < 2 - p - q := by linarith
  refine twoTypeBound_lt_of_twoTypeN_pos hp0.le hp2 hq (by linarith) ?_ ?_
  · rw [le_div_iff₀ hden]; nlinarith
  · have hG : 0 < p * (1 - p) * (2 - p) + p * q * (1 + p) + 6 * q ^ 2 := by
      have h1 : 0 < 1 - p := by linarith
      have h2 : 0 < 2 - p := by linarith
      have : 0 < p * (1 - p) * (2 - p) := by positivity
      have : 0 ≤ p * q * (1 + p) := by positivity
      nlinarith [sq_nonneg q]
    have e : twoTypeN p q ((p + q) / (2 - p - q)) =
        (p - q) * (p * (1 - p) * (2 - p) + p * q * (1 + p) + 6 * q ^ 2) / (2 - p - q) ^ 2 := by
      unfold twoTypeN
      field_simp
      ring
    rw [e]
    exact div_pos (mul_pos (by linarith) hG) (by positivity)

/-! ### The side polynomials -/

/-- The side polynomial `P2` of the two-type certificate. -/
def sideP2 (p μ : ℝ) : ℝ :=
  2 * μ ^ 2 * p ^ 3 - 10 * μ ^ 2 * p ^ 2 + 26 * μ ^ 2 * p - 34 * μ ^ 2 + 3 * μ * p ^ 3 -
  17 * μ * p ^ 2 + 39 * μ * p - 13 * μ + p ^ 3 - 9 * p ^ 2 + 7 * p - 1

/-- `sideP2` on the unit square: `p = X/2`, `μ = p/2 + Y p (1 + p)/(2 (1 − p))`, times
`(2 (1 − p))^2`. -/
noncomputable def bernP2 (X Y : ℝ) : ℝ :=
  (1 / 64) * X ^ 7 * Y ^ 2 - (1 / 32) * X ^ 7 * Y + (1 / 64) * X ^ 7 -
  (3 / 32) * X ^ 6 * Y ^ 2 + (7 / 32) * X ^ 6 * Y - (1 / 8) * X ^ 6 + (1 / 4) * X ^ 5 * Y ^ 2 -
  (7 / 16) * X ^ 5 * Y + (3 / 16) * X ^ 5 + (1 / 2) * X ^ 4 * Y ^ 2 - (3 / 2) * X ^ 4 * Y +
  (3 / 4) * X ^ 4 - (21 / 4) * X ^ 3 * Y ^ 2 + (11 / 2) * X ^ 3 * Y - (9 / 4) * X ^ 3 -
  (17 / 2) * X ^ 2 * Y ^ 2 + (5 / 2) * X ^ 2 * Y - 13 * X * Y + 5 * X - 4

/-- **Bernstein certificate for `P2`** (bidegree `(7, 2)`, one box). On `[0, 1]²`,
`bernP2 = -27/64 - S` where `S` is a combination, with nonnegative
coefficients, of `X^i (1 - X)^(7 - i) Y^j (1 - Y)^(2 - j)`. -/
theorem bernP2_neg {X Y : ℝ} (hX0 : 0 ≤ X) (hX1 : X ≤ 1)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1) : bernP2 X Y < 0 := by
  obtain ⟨X', hX'⟩ : ∃ X', X' = 1 - X := ⟨_, rfl⟩
  obtain ⟨Y', hY'⟩ : ∃ Y', Y' = 1 - Y := ⟨_, rfl⟩
  have hX'0 : 0 ≤ X' := by rw [hX']; linarith
  have hY'0 : 0 ≤ Y' := by rw [hY']; linarith
  have e : bernP2 X Y = (-27 / 64 : ℝ) - ((229 / 64 : ℝ) * X' ^ 7 * Y' ^ 2 +
      (229 / 32 : ℝ) * X' ^ 7 * Y * Y' +
      (229 / 64 : ℝ) * X' ^ 7 * Y ^ 2 +
      (1283 / 64 : ℝ) * X * X' ^ 6 * Y' ^ 2 +
      (1699 / 32 : ℝ) * X * X' ^ 6 * Y * Y' +
      (2115 / 64 : ℝ) * X * X' ^ 6 * Y ^ 2 +
      (2889 / 64 : ℝ) * X ^ 2 * X' ^ 5 * Y' ^ 2 +
      (5305 / 32 : ℝ) * X ^ 2 * X' ^ 5 * Y * Y' +
      (8265 / 64 : ℝ) * X ^ 2 * X' ^ 5 * Y ^ 2 +
      (3359 / 64 : ℝ) * X ^ 3 * X' ^ 4 * Y' ^ 2 +
      (9023 / 32 : ℝ) * X ^ 3 * X' ^ 4 * Y * Y' +
      (17743 / 64 : ℝ) * X ^ 3 * X' ^ 4 * Y ^ 2 +
      (2143 / 64 : ℝ) * X ^ 4 * X' ^ 3 * Y' ^ 2 +
      (9007 / 32 : ℝ) * X ^ 4 * X' ^ 3 * Y * Y' +
      (22623 / 64 : ℝ) * X ^ 4 * X' ^ 3 * Y ^ 2 +
      (717 / 64 : ℝ) * X ^ 5 * X' ^ 2 * Y' ^ 2 +
      (5259 / 32 : ℝ) * X ^ 5 * X' ^ 2 * Y * Y' +
      (17145 / 64 : ℝ) * X ^ 5 * X' ^ 2 * Y ^ 2 +
      (99 / 64 : ℝ) * X ^ 6 * X' * Y' ^ 2 +
      (207 / 4 : ℝ) * X ^ 6 * X' * Y * Y' +
      (7155 / 64 : ℝ) * X ^ 6 * X' * Y ^ 2 +
      (27 / 4 : ℝ) * X ^ 7 * Y * Y' +
      (1269 / 64 : ℝ) * X ^ 7 * Y ^ 2) := by
    rw [hX', hY']
    unfold bernP2
    ring
  rw [e, sub_neg]
  exact lt_of_lt_of_le (b := 0) (by norm_num) (by positivity)

/-- The side polynomial `P3` of the two-type certificate. -/
def sideP3 (p μ : ℝ) : ℝ :=
  2 * μ ^ 2 * p ^ 3 - 6 * μ ^ 2 * p ^ 2 + 14 * μ ^ 2 * p - 26 * μ ^ 2 + 3 * μ * p ^ 3 -
  9 * μ * p ^ 2 + 25 * μ * p - 11 * μ + p ^ 3 - 5 * p ^ 2 + 5 * p - 1

/-- `sideP3` on the unit square: `p = X/2`, `μ = p/2 + Y p (1 + p)/(2 (1 − p))`, times
`(2 (1 − p))^2`. -/
noncomputable def bernP3 (X Y : ℝ) : ℝ :=
  (1 / 64) * X ^ 7 * Y ^ 2 - (1 / 32) * X ^ 7 * Y + (1 / 64) * X ^ 7 -
  (1 / 32) * X ^ 6 * Y ^ 2 + (3 / 32) * X ^ 6 * Y - (1 / 16) * X ^ 6 + (1 / 8) * X ^ 5 * Y ^ 2 -
  (3 / 16) * X ^ 5 * Y + (1 / 16) * X ^ 5 - (1 / 4) * X ^ 4 * Y ^ 2 - (1 / 4) * X ^ 4 * Y +
  (1 / 4) * X ^ 4 - (19 / 4) * X ^ 3 * Y ^ 2 + 4 * X ^ 3 * Y - (5 / 4) * X ^ 3 -
  (13 / 2) * X ^ 2 * Y ^ 2 - (1 / 2) * X ^ 2 * Y + X ^ 2 - 11 * X * Y + 3 * X - 4

/-- **Bernstein certificate for `P3`** (bidegree `(7, 2)`, one box). On `[0, 1]²`,
`bernP3 = -63/64 - S` where `S` is a combination, with nonnegative
coefficients, of `X^i (1 - X)^(7 - i) Y^j (1 - Y)^(2 - j)`. -/
theorem bernP3_neg {X Y : ℝ} (hX0 : 0 ≤ X) (hX1 : X ≤ 1)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1) : bernP3 X Y < 0 := by
  obtain ⟨X', hX'⟩ : ∃ X', X' = 1 - X := ⟨_, rfl⟩
  obtain ⟨Y', hY'⟩ : ∃ Y', Y' = 1 - Y := ⟨_, rfl⟩
  have hX'0 : 0 ≤ X' := by rw [hX']; linarith
  have hY'0 : 0 ≤ Y' := by rw [hY']; linarith
  have e : bernP3 X Y = (-63 / 64 : ℝ) - ((193 / 64 : ℝ) * X' ^ 7 * Y' ^ 2 +
      (193 / 32 : ℝ) * X' ^ 7 * Y * Y' +
      (193 / 64 : ℝ) * X' ^ 7 * Y ^ 2 +
      (1159 / 64 : ℝ) * X * X' ^ 6 * Y' ^ 2 +
      (1511 / 32 : ℝ) * X * X' ^ 6 * Y * Y' +
      (1863 / 64 : ℝ) * X * X' ^ 6 * Y ^ 2 +
      (2837 / 64 : ℝ) * X ^ 2 * X' ^ 5 * Y' ^ 2 +
      (4965 / 32 : ℝ) * X ^ 2 * X' ^ 5 * Y * Y' +
      (7509 / 64 : ℝ) * X ^ 2 * X' ^ 5 * Y ^ 2 +
      (3635 / 64 : ℝ) * X ^ 3 * X' ^ 4 * Y' ^ 2 +
      (8867 / 32 : ℝ) * X ^ 3 * X' ^ 4 * Y * Y' +
      (16483 / 64 : ℝ) * X ^ 3 * X' ^ 4 * Y ^ 2 +
      (2579 / 64 : ℝ) * X ^ 4 * X' ^ 3 * Y' ^ 2 +
      (9275 / 32 : ℝ) * X ^ 4 * X' ^ 3 * Y * Y' +
      (21363 / 64 : ℝ) * X ^ 4 * X' ^ 3 * Y ^ 2 +
      (961 / 64 : ℝ) * X ^ 5 * X' ^ 2 * Y' ^ 2 +
      (5663 / 32 : ℝ) * X ^ 5 * X' ^ 2 * Y * Y' +
      (16389 / 64 : ℝ) * X ^ 5 * X' ^ 2 * Y ^ 2 +
      (147 / 64 : ℝ) * X ^ 6 * X' * Y' ^ 2 +
      (465 / 8 : ℝ) * X ^ 6 * X' * Y * Y' +
      (6903 / 64 : ℝ) * X ^ 6 * X' * Y ^ 2 +
      (63 / 8 : ℝ) * X ^ 7 * Y * Y' +
      (1233 / 64 : ℝ) * X ^ 7 * Y ^ 2) := by
    rw [hX', hY']
    unfold bernP3
    ring
  rw [e, sub_neg]
  exact lt_of_lt_of_le (b := 0) (by norm_num) (by positivity)

/-- The side polynomial `P5` of the two-type certificate. -/
def sideP5 (p μ : ℝ) : ℝ :=
  2 * μ ^ 3 * p ^ 4 - 20 * μ ^ 3 * p ^ 3 + 64 * μ ^ 3 * p ^ 2 - 92 * μ ^ 3 * p + 62 * μ ^ 3 +
  6 * μ ^ 2 * p ^ 4 - 46 * μ ^ 2 * p ^ 3 + 116 * μ ^ 2 * p ^ 2 - 134 * μ ^ 2 * p + 58 * μ ^ 2 +
  6 * μ * p ^ 4 - 32 * μ * p ^ 3 + 65 * μ * p ^ 2 - 62 * μ * p + 15 * μ + 2 * p ^ 4 -
  6 * p ^ 3 + 13 * p ^ 2 - 8 * p + 1

/-- `sideP5` on the unit square: `p = X/2`, `μ = p/2 + Y p (1 + p)/(2 (1 − p))`, times
`(2 (1 − p))^3`. -/
noncomputable def bernP5 (X Y : ℝ) : ℝ :=
  (1 / 512) * X ^ 10 * Y ^ 3 - (3 / 512) * X ^ 10 * Y ^ 2 + (3 / 512) * X ^ 10 * Y -
  (1 / 512) * X ^ 10 - (7 / 256) * X ^ 9 * Y ^ 3 + (21 / 256) * X ^ 9 * Y ^ 2 -
  (21 / 256) * X ^ 9 * Y + (7 / 256) * X ^ 9 + (5 / 128) * X ^ 8 * Y ^ 3 -
  (23 / 128) * X ^ 8 * Y ^ 2 + (31 / 128) * X ^ 8 * Y - (13 / 128) * X ^ 8 +
  (21 / 64) * X ^ 7 * Y ^ 3 - (49 / 64) * X ^ 7 * Y ^ 2 + (35 / 64) * X ^ 7 * Y -
  (7 / 64) * X ^ 7 - (21 / 32) * X ^ 6 * Y ^ 3 + (89 / 32) * X ^ 6 * Y ^ 2 -
  (109 / 32) * X ^ 6 * Y + (41 / 32) * X ^ 6 - (13 / 16) * X ^ 5 * Y ^ 3 +
  (11 / 16) * X ^ 5 * Y ^ 2 + (23 / 16) * X ^ 5 * Y - (21 / 16) * X ^ 5 +
  (47 / 8) * X ^ 4 * Y ^ 3 - (121 / 8) * X ^ 4 * Y ^ 2 + (113 / 8) * X ^ 4 * Y -
  (35 / 8) * X ^ 4 + (31 / 4) * X ^ 3 * Y ^ 3 + (17 / 4) * X ^ 3 * Y ^ 2 -
  (67 / 4) * X ^ 3 * Y + (35 / 4) * X ^ 3 + 29 * X ^ 2 * Y ^ 2 - 19 * X ^ 2 * Y + 2 * X ^ 2 +
  30 * X * Y - 14 * X + 8

/-- **Bernstein certificate for `P5`** (bidegree `(10, 3)`, one box). On `[0, 1]²`,
`bernP5 = 81/512 + S` where `S` is a combination, with nonnegative
coefficients, of `X^i (1 - X)^(10 - i) Y^j (1 - Y)^(3 - j)`. -/
theorem bernP5_pos {X Y : ℝ} (hX0 : 0 ≤ X) (hX1 : X ≤ 1)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1) : 0 < bernP5 X Y := by
  obtain ⟨X', hX'⟩ : ∃ X', X' = 1 - X := ⟨_, rfl⟩
  obtain ⟨Y', hY'⟩ : ∃ Y', Y' = 1 - Y := ⟨_, rfl⟩
  have hX'0 : 0 ≤ X' := by rw [hX']; linarith
  have hY'0 : 0 ≤ Y' := by rw [hY']; linarith
  have e : bernP5 X Y = (81 / 512 : ℝ) + ((4015 / 512 : ℝ) * X' ^ 10 * Y' ^ 3 +
      (12045 / 512 : ℝ) * X' ^ 10 * Y * Y' ^ 2 +
      (12045 / 512 : ℝ) * X' ^ 10 * Y ^ 2 * Y' +
      (4015 / 512 : ℝ) * X' ^ 10 * Y ^ 3 +
      (16491 / 256 : ℝ) * X * X' ^ 9 * Y' ^ 3 +
      (57153 / 256 : ℝ) * X * X' ^ 9 * Y * Y' ^ 2 +
      (64833 / 256 : ℝ) * X * X' ^ 9 * Y ^ 2 * Y' +
      (24171 / 256 : ℝ) * X * X' ^ 9 * Y ^ 3 +
      (117187 / 512 : ℝ) * X ^ 2 * X' ^ 8 * Y' ^ 3 +
      (480073 / 512 : ℝ) * X ^ 2 * X' ^ 8 * Y * Y' ^ 2 +
      (623433 / 512 : ℝ) * X ^ 2 * X' ^ 8 * Y ^ 2 * Y' +
      (260547 / 512 : ℝ) * X ^ 2 * X' ^ 8 * Y ^ 3 +
      (29553 / 64 : ℝ) * X ^ 3 * X' ^ 7 * Y' ^ 3 +
      (146979 / 64 : ℝ) * X ^ 3 * X' ^ 7 * Y * Y' ^ 2 +
      (220419 / 64 : ℝ) * X ^ 3 * X' ^ 7 * Y ^ 2 * Y' +
      (103489 / 64 : ℝ) * X ^ 3 * X' ^ 7 * Y ^ 3 +
      (149415 / 256 : ℝ) * X ^ 4 * X' ^ 6 * Y' ^ 3 +
      (930773 / 256 : ℝ) * X ^ 4 * X' ^ 6 * Y * Y' ^ 2 +
      (1624917 / 256 : ℝ) * X ^ 4 * X' ^ 6 * Y ^ 2 * Y' +
      (858951 / 256 : ℝ) * X ^ 4 * X' ^ 6 * Y ^ 3 +
      (61481 / 128 : ℝ) * X ^ 5 * X' ^ 5 * Y' ^ 3 +
      (498099 / 128 : ℝ) * X ^ 5 * X' ^ 5 * Y * Y' ^ 2 +
      (1019523 / 128 : ℝ) * X ^ 5 * X' ^ 5 * Y ^ 2 * Y' +
      (608145 / 128 : ℝ) * X ^ 5 * X' ^ 5 * Y ^ 3 +
      (66079 / 256 : ℝ) * X ^ 6 * X' ^ 4 * Y' ^ 3 +
      (730565 / 256 : ℝ) * X ^ 6 * X' ^ 4 * Y * Y' ^ 2 +
      (1764165 / 256 : ℝ) * X ^ 6 * X' ^ 4 * Y ^ 2 * Y' +
      (1190471 / 256 : ℝ) * X ^ 6 * X' ^ 4 * Y ^ 3 +
      (2805 / 32 : ℝ) * X ^ 7 * X' ^ 3 * Y' ^ 3 +
      (90657 / 64 : ℝ) * X ^ 7 * X' ^ 3 * Y * Y' ^ 2 +
      (259683 / 64 : ℝ) * X ^ 7 * X' ^ 3 * Y ^ 2 * Y' +
      (198849 / 64 : ℝ) * X ^ 7 * X' ^ 3 * Y ^ 3 +
      (8775 / 512 : ℝ) * X ^ 8 * X' ^ 2 * Y' ^ 3 +
      (233145 / 512 : ℝ) * X ^ 8 * X' ^ 2 * Y * Y' ^ 2 +
      (796041 / 512 : ℝ) * X ^ 8 * X' ^ 2 * Y ^ 2 * Y' +
      (694467 / 512 : ℝ) * X ^ 8 * X' ^ 2 * Y ^ 3 +
      (189 / 128 : ℝ) * X ^ 9 * X' * Y' ^ 3 +
      (21897 / 256 : ℝ) * X ^ 9 * X' * Y * Y' ^ 2 +
      (89505 / 256 : ℝ) * X ^ 9 * X' * Y ^ 2 * Y' +
      (89451 / 256 : ℝ) * X ^ 9 * X' * Y ^ 3 +
      (3645 / 512 : ℝ) * X ^ 10 * Y * Y' ^ 2 +
      (17901 / 512 : ℝ) * X ^ 10 * Y ^ 2 * Y' +
      (20655 / 512 : ℝ) * X ^ 10 * Y ^ 3) := by
    rw [hX', hY']
    unfold bernP5
    ring
  rw [e]
  exact add_pos_of_pos_of_nonneg (by norm_num) (by positivity)

/-- **The region as a unit square.** For `0 < p ≤ 1/2`, the set `p/2 ≤ μ ≤ p/(1 − p)` (written
`μ (1 − p) ≤ p`) is covered by `μ = p/2 + Y p (1 + p) / (2 (1 − p))` with `0 ≤ Y ≤ 1`. -/
theorem exists_unit_param {p μ : ℝ} (hp : 0 < p) (hp2 : p ≤ 1 / 2) (h1 : p / 2 ≤ μ)
    (h2 : μ * (1 - p) ≤ p) :
    ∃ Y : ℝ, 0 ≤ Y ∧ Y ≤ 1 ∧ μ = p / 2 + Y * p * (1 + p) / (2 * (1 - p)) := by
  have h1p : 0 < 1 - p := by linarith
  have hpp : 0 < p * (1 + p) := by positivity
  refine ⟨(2 * μ - p) * (1 - p) / (p * (1 + p)), ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (by linarith) h1p.le) hpp.le
  · rw [div_le_one hpp]
    nlinarith
  · field_simp
    ring

/-- **`P2 < 0`** on `0 < p ≤ 1/2`, `p/2 ≤ μ ≤ p/(1 − p)`. Via `exists_unit_param` this is
`bernP2_neg`. -/
theorem sideP2_neg {p μ : ℝ} (hp : 0 < p) (hp2 : p ≤ 1 / 2) (h1 : p / 2 ≤ μ)
    (h2 : μ * (1 - p) ≤ p) : sideP2 p μ < 0 := by
  obtain ⟨Y, hY0, hY1, rfl⟩ := exists_unit_param hp hp2 h1 h2
  have h1p : 1 - p ≠ 0 := by intro h; linarith
  have e : sideP2 p (p / 2 + Y * p * (1 + p) / (2 * (1 - p))) * (2 * (1 - p)) ^ 2 =
      bernP2 (2 * p) Y := by
    unfold sideP2 bernP2
    field_simp
    ring
  have hb := bernP2_neg (X := 2 * p) (by linarith) (by linarith) hY0 hY1
  have hpos : 0 < (2 * (1 - p)) ^ 2 := pow_pos (by linarith) 2
  by_contra hc
  push Not at hc
  have := mul_nonneg hc hpos.le
  linarith

/-- **`P3 < 0`** on `0 < p ≤ 1/2`, `p/2 ≤ μ ≤ p/(1 − p)`. Via `exists_unit_param` this is
`bernP3_neg`. -/
theorem sideP3_neg {p μ : ℝ} (hp : 0 < p) (hp2 : p ≤ 1 / 2) (h1 : p / 2 ≤ μ)
    (h2 : μ * (1 - p) ≤ p) : sideP3 p μ < 0 := by
  obtain ⟨Y, hY0, hY1, rfl⟩ := exists_unit_param hp hp2 h1 h2
  have h1p : 1 - p ≠ 0 := by intro h; linarith
  have e : sideP3 p (p / 2 + Y * p * (1 + p) / (2 * (1 - p))) * (2 * (1 - p)) ^ 2 =
      bernP3 (2 * p) Y := by
    unfold sideP3 bernP3
    field_simp
    ring
  have hb := bernP3_neg (X := 2 * p) (by linarith) (by linarith) hY0 hY1
  have hpos : 0 < (2 * (1 - p)) ^ 2 := pow_pos (by linarith) 2
  by_contra hc
  push Not at hc
  have := mul_nonneg hc hpos.le
  linarith

/-- **`P5 > 0`** on `0 < p ≤ 1/2`, `p/2 ≤ μ ≤ p/(1 − p)`. Via `exists_unit_param` this is
`bernP5_pos`. -/
theorem sideP5_pos {p μ : ℝ} (hp : 0 < p) (hp2 : p ≤ 1 / 2) (h1 : p / 2 ≤ μ)
    (h2 : μ * (1 - p) ≤ p) : 0 < sideP5 p μ := by
  obtain ⟨Y, hY0, hY1, rfl⟩ := exists_unit_param hp hp2 h1 h2
  have h1p : 1 - p ≠ 0 := by intro h; linarith
  have e : sideP5 p (p / 2 + Y * p * (1 + p) / (2 * (1 - p))) * (2 * (1 - p)) ^ 3 =
      bernP5 (2 * p) Y := by
    unfold sideP5 bernP5
    field_simp
    ring
  have hb := bernP5_pos (X := 2 * p) (by linarith) (by linarith) hY0 hY1
  have hpos : 0 < (2 * (1 - p)) ^ 3 := pow_pos (by linarith) 3
  by_contra hc
  push Not at hc
  have := mul_nonpos_of_nonpos_of_nonneg hc hpos.le
  linarith

/-! ### The per-triangle forms -/

/-- The six multipliers of the two-type certificate:
* `aP`, the weight of the Garland inequality (polynomial `p − v`) at the vertices of `A`; the
  vertices off `A` use the polynomial `(q − v)(1 + v)` with weight `1`;
* `cP`, `cQ`, the weights of the vertex identity `E[c(x) f(x) (f(y) − μ f(x))] = 0` on and off
  `A`;
* `gPQ`, `gQP`, `gQQ`, the weights of the edge identity `E[g(x, y) f(x) (f(z) − h(x, y))] = 0`,
  indexed by the types of the ordered pair `(x, y)` (`P` in `A`, `Q` not in `A`; a pair inside
  `A` never carries weight). -/
structure TwoTypeMultipliers where
  /-- Weight of the Garland inequality at the vertices of `A`. -/
  aP : ℝ
  /-- Vertex-identity weight on `A`. -/
  cP : ℝ
  /-- Vertex-identity weight off `A`. -/
  cQ : ℝ
  /-- Edge-identity weight on pairs (in `A`, not in `A`). -/
  gPQ : ℝ
  /-- Edge-identity weight on pairs (not in `A`, in `A`). -/
  gQP : ℝ
  /-- Edge-identity weight on pairs with both ends off `A`. -/
  gQQ : ℝ

/-- **The integrand** at an ordered triangle `(x, y, z)`, as a function of the types `tx, ty`
(`true` = in `A`) and the values `fx = f(x)`, `fy`, `fz`, `hxy = h(x, y)`:
* the local term at `x`: `aP (p f_y² − f_y f_z − (p − 1) μ² f_x²)` if `x ∈ A` (Garland), and
  `q f_y² + (q − 1) f_y f_z − h_xy² − 2 (q − 1) μ² f_x²` otherwise (the quadratic
  `(q − v)(1 + v)`);
* the vertex identity term `c(x) f_x (f_y − μ f_x)`;
* the edge identity term `g(x, y) f_x (f_z − h_xy)`.

Its expectation over a random ordered triangle is `≥ 0` for an eigenfunction (the core file). -/
def triJ (M : TwoTypeMultipliers) (p q μ : ℝ) (tx ty : Bool) (fx fy fz hxy : ℝ) : ℝ :=
  (if tx then M.aP * (p * fy ^ 2 - fy * fz - (p - 1) * μ ^ 2 * fx ^ 2) + M.cP * fx * (fy - μ * fx)
    else q * fy ^ 2 + (q - 1) * fy * fz - hxy ^ 2 - 2 * (q - 1) * μ ^ 2 * fx ^ 2
      + M.cQ * fx * (fy - μ * fx))
  + (if tx then (if ty then 0 else M.gPQ) else (if ty then M.gQP else M.gQQ)) * fx * (fz - hxy)

/-- **The per-triangle form**: `triJ` summed over the six orderings of a triangle with vertex types
`t0, t1, t2`, values `f0, f1, f2` and edge values `h01, h02, h12` (`h` is symmetric). -/
def triQ (M : TwoTypeMultipliers) (p q μ : ℝ) (t0 t1 t2 : Bool) (f0 f1 f2 h01 h02 h12 : ℝ) : ℝ :=
  triJ M p q μ t0 t1 f0 f1 f2 h01 + triJ M p q μ t0 t2 f0 f2 f1 h02
    + triJ M p q μ t1 t0 f1 f0 f2 h01 + triJ M p q μ t1 t2 f1 f2 f0 h12
    + triJ M p q μ t2 t0 f2 f0 f1 h02 + triJ M p q μ t2 t1 f2 f1 f0 h12

/-- `triQ` is symmetric: exchanging the vertices `0` and `1`. -/
theorem triQ_swap01 (M : TwoTypeMultipliers) (p q μ : ℝ) (t0 t1 t2 : Bool)
    (f0 f1 f2 h01 h02 h12 : ℝ) :
    triQ M p q μ t0 t1 t2 f0 f1 f2 h01 h02 h12 = triQ M p q μ t1 t0 t2 f1 f0 f2 h01 h12 h02 := by
  unfold triQ
  ring

/-- `triQ` is symmetric: exchanging the vertices `0` and `2`. -/
theorem triQ_swap02 (M : TwoTypeMultipliers) (p q μ : ℝ) (t0 t1 t2 : Bool)
    (f0 f1 f2 h01 h02 h12 : ℝ) :
    triQ M p q μ t0 t1 t2 f0 f1 f2 h01 h02 h12 = triQ M p q μ t2 t1 t0 f2 f1 f0 h12 h02 h01 := by
  unfold triQ
  ring

namespace TwoTypeMultipliers

variable (M : TwoTypeMultipliers) (p q μ : ℝ)

/-- QQQ triangles: the coefficient of `(f0 + f1 + f2)²/3`. -/
noncomputable def qqqS : ℝ :=
  4 * q - 2 + 4 * (1 - q) * μ ^ 2 + 2 * M.cQ * (1 - μ) + 2 * M.gQQ + M.gQQ ^ 2 / 2

/-- QQQ triangles: the coefficient of `Σ_{i<j} (f_i − f_j)²/3`. -/
noncomputable def qqqD : ℝ :=
  q + 1 + 4 * (1 - q) * μ ^ 2 - M.cQ * (1 + 2 * μ) - M.gQQ + M.gQQ ^ 2 / 8

/-- PQQ triangles: twice the coefficient of `(f1 − f2)²`. -/
noncomputable def pqqU : ℝ :=
  M.aP * (1 + p) - M.cQ * (1 + 2 * μ) - M.gQP + 4 * (1 - q) * μ ^ 2 + q + M.gQP ^ 2 / 4

/-- PQQ triangles: twice the coefficient of `(f1 + f2)²`. -/
noncomputable def pqqS : ℝ :=
  M.aP * (p - 1) + M.cQ * (1 - 2 * μ) + M.gQP + 4 * (1 - q) * μ ^ 2 + q + M.gQQ ^ 2 / 4
    + M.gQP ^ 2 / 4

/-- PQQ triangles: the coefficient of `f0 (f1 + f2)`. -/
noncomputable def pqqX : ℝ := M.cP + M.cQ + M.gPQ + M.gQQ + 2 * q - 2 + M.gPQ * M.gQP / 2

/-- PQQ triangles: the coefficient of `f0²`. -/
noncomputable def pqqF : ℝ := 2 * M.aP * (1 - p) * μ ^ 2 - 2 * μ * M.cP + 2 * q + M.gPQ ^ 2 / 2

/-- **The sign conditions** on the multipliers at `(p, q, μ)`. They make every per-triangle form
of type QQQ or PQQ nonpositive (`triQ_QQQ_nonpos`, `triQ_PQQ_nonpos`) with the rigidity used in
the proof (`eq_of_triQ_QQQ_eq_zero`, `eq_zero_of_triQ_PQQ_eq_zero`), and they make the
Garland weight `aP` legitimate. -/
structure Good : Prop where
  /-- The Garland inequality enters with a nonnegative weight. -/
  aP_nonneg : 0 ≤ M.aP
  /-- QQQ: the coefficient of `(f0 + f1 + f2)²` is `≤ 0`. -/
  qqqS_nonpos : M.qqqS q μ ≤ 0
  /-- QQQ: the coefficient of `Σ_{i<j} (f_i − f_j)²` is `< 0`. -/
  qqqD_neg : M.qqqD q μ < 0
  /-- PQQ: the coefficient of `(f1 − f2)²` is `< 0`. -/
  pqqU_neg : M.pqqU p q μ < 0
  /-- PQQ: the coefficient of `(f1 + f2)²` is `< 0`. -/
  pqqS_neg : M.pqqS p q μ < 0
  /-- PQQ: the cross term completes the square in `f1 + f2 − 2μ f0`. -/
  pqqX_eq : M.pqqX q = -2 * μ * M.pqqS p q μ
  /-- PQQ: after completing the square, the coefficient of `f0²` is `< 0`. -/
  pqqF_neg : M.pqqF p q μ - 2 * μ ^ 2 * M.pqqS p q μ < 0

end TwoTypeMultipliers

open TwoTypeMultipliers

/-- **The QQQ form** (no vertex in `A`), with free multipliers:
`q_T = −2 Σ_k (h_k + gQQ (s − f_k)/4)² + (qqqS/3) s² + (qqqD/3) Σ_{i<j} (f_i − f_j)²`, where
`s = f0 + f1 + f2` and `h_k` is `h` on the edge opposite `k`. -/
theorem triQ_QQQ (M : TwoTypeMultipliers) (p q μ f0 f1 f2 h01 h02 h12 : ℝ) :
    triQ M p q μ false false false f0 f1 f2 h01 h02 h12 =
      -2 * ((h12 + M.gQQ * (f1 + f2) / 4) ^ 2 + (h02 + M.gQQ * (f0 + f2) / 4) ^ 2
          + (h01 + M.gQQ * (f0 + f1) / 4) ^ 2)
        + M.qqqS q μ / 3 * (f0 + f1 + f2) ^ 2
        + M.qqqD q μ / 3 * ((f0 - f1) ^ 2 + (f0 - f2) ^ 2 + (f1 - f2) ^ 2) := by
  simp only [triQ, triJ, qqqS, qqqD, Bool.false_eq_true, ↓reduceIte]
  ring

/-- **The PQQ form** (vertex `0` in `A`, vertices `1, 2` not), with free multipliers:
`q_T = −2 (h12 + gQQ σ/4)² − (w + gQP u/2)²/2 − (t + gPQ f0 + gQP σ/2)²/2 + (pqqU/2) u²
  + pqqF f0² + pqqX f0 σ + (pqqS/2) σ²`, where `u = f1 − f2`, `σ = f1 + f2`, `w = h01 − h02`,
`t = h01 + h02`. -/
theorem triQ_PQQ (M : TwoTypeMultipliers) (p q μ f0 f1 f2 h01 h02 h12 : ℝ) :
    triQ M p q μ true false false f0 f1 f2 h01 h02 h12 =
      -2 * (h12 + M.gQQ * (f1 + f2) / 4) ^ 2 - (h01 - h02 + M.gQP * (f1 - f2) / 2) ^ 2 / 2
        - (h01 + h02 + M.gPQ * f0 + M.gQP * (f1 + f2) / 2) ^ 2 / 2
        + M.pqqU p q μ / 2 * (f1 - f2) ^ 2 + M.pqqF p q μ * f0 ^ 2
        + M.pqqX q * f0 * (f1 + f2) + M.pqqS p q μ / 2 * (f1 + f2) ^ 2 := by
  simp only [triQ, triJ, pqqU, pqqF, pqqX, pqqS, Bool.false_eq_true, ↓reduceIte]
  ring

/-- Under the sign conditions, **every QQQ form is `≤ 0`**. -/
theorem triQ_QQQ_nonpos {M : TwoTypeMultipliers} {p q μ : ℝ} (hM : M.Good p q μ)
    (f0 f1 f2 h01 h02 h12 : ℝ) : triQ M p q μ false false false f0 f1 f2 h01 h02 h12 ≤ 0 := by
  rw [triQ_QQQ]
  have t1 : 0 ≤ (h12 + M.gQQ * (f1 + f2) / 4) ^ 2 + (h02 + M.gQQ * (f0 + f2) / 4) ^ 2
      + (h01 + M.gQQ * (f0 + f1) / 4) ^ 2 := by positivity
  have t2 : M.qqqS q μ / 3 * (f0 + f1 + f2) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [hM.qqqS_nonpos]) (sq_nonneg _)
  have t3 : M.qqqD q μ / 3 * ((f0 - f1) ^ 2 + (f0 - f2) ^ 2 + (f1 - f2) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [hM.qqqD_neg]) (by positivity)
  linarith

/-- **Rigidity of the QQQ form**: under the sign conditions, a QQQ form that vanishes has
`f0 = f1 = f2`. -/
theorem eq_of_triQ_QQQ_eq_zero {M : TwoTypeMultipliers} {p q μ : ℝ} (hM : M.Good p q μ)
    {f0 f1 f2 h01 h02 h12 : ℝ} (h : triQ M p q μ false false false f0 f1 f2 h01 h02 h12 = 0) :
    f0 = f1 ∧ f0 = f2 := by
  rw [triQ_QQQ] at h
  have t1 : 0 ≤ (h12 + M.gQQ * (f1 + f2) / 4) ^ 2 + (h02 + M.gQQ * (f0 + f2) / 4) ^ 2
      + (h01 + M.gQQ * (f0 + f1) / 4) ^ 2 := by positivity
  have t2 : M.qqqS q μ / 3 * (f0 + f1 + f2) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [hM.qqqS_nonpos]) (sq_nonneg _)
  have hD : M.qqqD q μ / 3 < 0 := by linarith [hM.qqqD_neg]
  have hC : 0 ≤ (f0 - f1) ^ 2 + (f0 - f2) ^ 2 + (f1 - f2) ^ 2 := by positivity
  have t3 : M.qqqD q μ / 3 * ((f0 - f1) ^ 2 + (f0 - f2) ^ 2 + (f1 - f2) ^ 2) = 0 := by
    have : M.qqqD q μ / 3 * ((f0 - f1) ^ 2 + (f0 - f2) ^ 2 + (f1 - f2) ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hD.le hC
    linarith
  have hC0 : (f0 - f1) ^ 2 + (f0 - f2) ^ 2 + (f1 - f2) ^ 2 = 0 :=
    (mul_eq_zero.mp t3).resolve_left hD.ne
  have e1 : (f0 - f1) ^ 2 = 0 :=
    le_antisymm (by linarith [sq_nonneg (f0 - f2), sq_nonneg (f1 - f2)]) (sq_nonneg _)
  have e2 : (f0 - f2) ^ 2 = 0 :=
    le_antisymm (by linarith [sq_nonneg (f0 - f1), sq_nonneg (f1 - f2)]) (sq_nonneg _)
  exact ⟨sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp e1),
    sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp e2)⟩

/-- The `f`-part of the PQQ form, completed: with `pqqX = −2 μ pqqS`,
`pqqF f0² + pqqX f0 σ + (pqqS/2) σ² = (pqqS/2)(σ − 2 μ f0)² + (pqqF − 2 μ² pqqS) f0²`. -/
private theorem pqq_complete {M : TwoTypeMultipliers} {p q μ : ℝ} (hM : M.Good p q μ)
    (f0 f1 f2 : ℝ) :
    M.pqqF p q μ * f0 ^ 2 + M.pqqX q * f0 * (f1 + f2) + M.pqqS p q μ / 2 * (f1 + f2) ^ 2 =
      M.pqqS p q μ / 2 * (f1 + f2 - 2 * μ * f0) ^ 2
        + (M.pqqF p q μ - 2 * μ ^ 2 * M.pqqS p q μ) * f0 ^ 2 := by
  rw [hM.pqqX_eq]
  ring

/-- Under the sign conditions, **every PQQ form is `≤ 0`**. -/
theorem triQ_PQQ_nonpos {M : TwoTypeMultipliers} {p q μ : ℝ} (hM : M.Good p q μ)
    (f0 f1 f2 h01 h02 h12 : ℝ) : triQ M p q μ true false false f0 f1 f2 h01 h02 h12 ≤ 0 := by
  rw [triQ_PQQ]
  have e := pqq_complete hM f0 f1 f2
  have t1 : 0 ≤ (h12 + M.gQQ * (f1 + f2) / 4) ^ 2 := sq_nonneg _
  have t2 : 0 ≤ (h01 - h02 + M.gQP * (f1 - f2) / 2) ^ 2 := sq_nonneg _
  have t3 : 0 ≤ (h01 + h02 + M.gPQ * f0 + M.gQP * (f1 + f2) / 2) ^ 2 := sq_nonneg _
  have t4 : M.pqqU p q μ / 2 * (f1 - f2) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [hM.pqqU_neg]) (sq_nonneg _)
  have t5 : M.pqqS p q μ / 2 * (f1 + f2 - 2 * μ * f0) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [hM.pqqS_neg]) (sq_nonneg _)
  have t6 : (M.pqqF p q μ - 2 * μ ^ 2 * M.pqqS p q μ) * f0 ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hM.pqqF_neg.le (sq_nonneg _)
  linarith

/-- **Rigidity of the PQQ form**: under the sign conditions, a PQQ form that vanishes has
`f0 = f1 = f2 = 0`. -/
theorem eq_zero_of_triQ_PQQ_eq_zero {M : TwoTypeMultipliers} {p q μ : ℝ} (hM : M.Good p q μ)
    {f0 f1 f2 h01 h02 h12 : ℝ} (h : triQ M p q μ true false false f0 f1 f2 h01 h02 h12 = 0) :
    f0 = 0 ∧ f1 = 0 ∧ f2 = 0 := by
  rw [triQ_PQQ] at h
  have e := pqq_complete hM f0 f1 f2
  have t1 : 0 ≤ (h12 + M.gQQ * (f1 + f2) / 4) ^ 2 := sq_nonneg _
  have t2 : 0 ≤ (h01 - h02 + M.gQP * (f1 - f2) / 2) ^ 2 := sq_nonneg _
  have t3 : 0 ≤ (h01 + h02 + M.gPQ * f0 + M.gQP * (f1 + f2) / 2) ^ 2 := sq_nonneg _
  have hU : M.pqqU p q μ / 2 < 0 := by linarith [hM.pqqU_neg]
  have hS : M.pqqS p q μ / 2 < 0 := by linarith [hM.pqqS_neg]
  have hF := hM.pqqF_neg
  have t4 : M.pqqU p q μ / 2 * (f1 - f2) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hU.le (sq_nonneg _)
  have t5 : M.pqqS p q μ / 2 * (f1 + f2 - 2 * μ * f0) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hS.le (sq_nonneg _)
  have t6 : (M.pqqF p q μ - 2 * μ ^ 2 * M.pqqS p q μ) * f0 ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hF.le (sq_nonneg _)
  have z4 : M.pqqU p q μ / 2 * (f1 - f2) ^ 2 = 0 := by linarith
  have z5 : M.pqqS p q μ / 2 * (f1 + f2 - 2 * μ * f0) ^ 2 = 0 := by linarith
  have z6 : (M.pqqF p q μ - 2 * μ ^ 2 * M.pqqS p q μ) * f0 ^ 2 = 0 := by linarith
  have hu : f1 - f2 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp z4).resolve_left hU.ne)
  have hs : f1 + f2 - 2 * μ * f0 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp z5).resolve_left hS.ne)
  have hf0 : f0 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp z6).resolve_left hF.ne)
  rw [hf0] at hs
  refine ⟨hf0, ?_, ?_⟩ <;> linarith

/-! ### The explicit multipliers -/

/-- The numerator `D² · cQ` of a multiplier of `twoTypeMult`. -/
def multUNum (p q μ : ℝ) : ℝ :=
  -2 * μ ^ 3 * p ^ 2 * q + 2 * μ ^ 3 * p ^ 2 + 12 * μ ^ 3 * p * q - 12 * μ ^ 3 * p -
  18 * μ ^ 3 * q + 18 * μ ^ 3 - 6 * μ ^ 2 * p ^ 2 * q + 6 * μ ^ 2 * p ^ 2 + 28 * μ ^ 2 * p * q -
  28 * μ ^ 2 * p - 30 * μ ^ 2 * q + 30 * μ ^ 2 - 6 * μ * p ^ 2 * q + 7 * μ * p ^ 2 +
  20 * μ * p * q - 18 * μ * p - 14 * μ * q + 15 * μ - 2 * p ^ 2 * q + p ^ 2 + 4 * p * q -
  6 * p - 2 * q + 1

/-- The numerator `(p² − 1) D² · aP` of a multiplier of `twoTypeMult`. -/
def multAPNum (p q μ : ℝ) : ℝ :=
  -4 * μ ^ 3 * p ^ 3 * q + 4 * μ ^ 3 * p ^ 3 + 26 * μ ^ 3 * p ^ 2 * q - 26 * μ ^ 3 * p ^ 2 -
  48 * μ ^ 3 * p * q + 48 * μ ^ 3 * p + 18 * μ ^ 3 * q - 18 * μ ^ 3 - μ ^ 2 * p ^ 5 +
  6 * μ ^ 2 * p ^ 4 - 9 * μ ^ 2 * p ^ 3 * q + 3 * μ ^ 2 * p ^ 3 + 44 * μ ^ 2 * p ^ 2 * q -
  46 * μ ^ 2 * p ^ 2 - 61 * μ ^ 2 * p * q + 64 * μ ^ 2 * p + 30 * μ ^ 2 * q - 38 * μ ^ 2 -
  2 * μ * p ^ 5 + 8 * μ * p ^ 4 - 6 * μ * p ^ 3 * q + 22 * μ * p ^ 2 * q - 27 * μ * p ^ 2 -
  30 * μ * p * q + 40 * μ * p + 14 * μ * q - 15 * μ - p ^ 5 + 2 * p ^ 4 - p ^ 3 * q - p ^ 3 +
  4 * p ^ 2 * q - 7 * p ^ 2 - 5 * p * q + 8 * p + 2 * q - 1

/-- The numerator `(1 + p) D² · cP` of a multiplier of `twoTypeMult`. -/
def multCPNum (p q μ : ℝ) : ℝ :=
  4 * μ ^ 4 * p ^ 3 * q - 4 * μ ^ 4 * p ^ 3 - 32 * μ ^ 4 * p ^ 2 * q + 32 * μ ^ 4 * p ^ 2 +
  84 * μ ^ 4 * p * q - 84 * μ ^ 4 * p - 72 * μ ^ 4 * q + 72 * μ ^ 4 + 2 * μ ^ 3 * p ^ 5 -
  12 * μ ^ 3 * p ^ 4 + 14 * μ ^ 3 * p ^ 3 * q + 2 * μ ^ 3 * p ^ 3 - 84 * μ ^ 3 * p ^ 2 * q +
  100 * μ ^ 3 * p ^ 2 + 142 * μ ^ 3 * p * q - 168 * μ ^ 3 * p - 48 * μ ^ 3 * q + 36 * μ ^ 3 +
  4 * μ ^ 2 * p ^ 5 - 16 * μ ^ 2 * p ^ 4 + 16 * μ ^ 2 * p ^ 3 * q - 10 * μ ^ 2 * p ^ 3 -
  64 * μ ^ 2 * p ^ 2 * q + 80 * μ ^ 2 * p ^ 2 + 56 * μ ^ 2 * p * q - 46 * μ ^ 2 * p -
  8 * μ ^ 2 * q + 28 * μ ^ 2 + 2 * μ * p ^ 5 - 4 * μ * p ^ 4 + 6 * μ * p ^ 3 * q -
  5 * μ * p ^ 3 - 12 * μ * p ^ 2 * q - 3 * μ * p ^ 2 + 6 * μ * p * q - 21 * μ * p + 7 * μ +
  5 * p ^ 3 + 3 * p ^ 2 - p + 1

/-- **The explicit multipliers** at `(p, q, μ)`. With `D = (1 − p) + (3 − p) μ` and
`τ = 2 (2μ − p)/D`, they are `gQQ = −2τ`, `gQP = −2p`, `gPQ = −2μ (1 − p)`,
`cQ = U = (1 − 2q − 2 (1 − q) μ² + 2τ − τ²)/(1 − μ)` (the factor `1 − μ` cancels, leaving
`multUNum / D²`), `aP = (lo + hi)/2` with
`lo = (U (1 − 2μ) + 4 (1 − q) μ² + q + τ² − 2p + p²)/(1 − p)` and
`hi = −(2p + p² − U (1 + 2μ) + 4 (1 − q) μ² + q)/(1 + p)`, and `cP` the value making
`pqqX = −2 μ pqqS`. They are stated here in closed form (numerators `multUNum`, `multAPNum`,
`multCPNum`); `gen_mult.py` in `.lake/scratch-cert/lean/` checks the closed forms against the
nested ones. At `D = 0`, `p = ±1` the formulas divide by zero and are meaningless; they are only
used where `exists_good` applies. -/
noncomputable def twoTypeMult (p q μ : ℝ) : TwoTypeMultipliers where
  aP := multAPNum p q μ / ((p ^ 2 - 1) * ((1 - p) + (3 - p) * μ) ^ 2)
  cP := multCPNum p q μ / ((1 + p) * ((1 - p) + (3 - p) * μ) ^ 2)
  cQ := multUNum p q μ / ((1 - p) + (3 - p) * μ) ^ 2
  gPQ := -2 * μ * (1 - p)
  gQP := -2 * p
  gQQ := -4 * (2 * μ - p) / ((1 - p) + (3 - p) * μ)

section Identities

variable {p q μ : ℝ} (hD : (1 - p) + (3 - p) * μ ≠ 0) (hp1 : 1 + p ≠ 0) (hp2 : p ^ 2 - 1 ≠ 0)
include hD

/-- `qqqS = 0` for the explicit multipliers. -/
theorem twoTypeMult_qqqS : (twoTypeMult p q μ).qqqS q μ = 0 := by
  simp only [qqqS, twoTypeMult]
  unfold multUNum
  generalize hDdef : (1 - p) + (3 - p) * μ = D at hD ⊢
  field_simp
  subst hDdef
  ring

/-- `qqqD · D² n₁ = 3 (1 + 2μ) D N − 3 x P2`, with `n₁ = 2p − 1 − 2μ (2 − p)` and
`x = p − μ (1 − p)`. -/
theorem twoTypeMult_qqqD :
    (twoTypeMult p q μ).qqqD q μ * (((1 - p) + (3 - p) * μ) ^ 2 * (2 * p - 1 - 2 * μ * (2 - p))) =
      3 * (1 + 2 * μ) * ((1 - p) + (3 - p) * μ) * twoTypeN p q μ
        - 3 * (p - μ * (1 - p)) * sideP2 p μ := by
  simp only [qqqD, twoTypeMult]
  unfold multUNum twoTypeN sideP2
  generalize hDdef : (1 - p) + (3 - p) * μ = D at hD ⊢
  field_simp
  subst hDdef
  ring

include hp1 hp2 in
/-- `pqqU · (1 − p) D = −N`. -/
theorem twoTypeMult_pqqU :
    (twoTypeMult p q μ).pqqU p q μ * ((1 - p) * ((1 - p) + (3 - p) * μ)) = -twoTypeN p q μ := by
  simp only [pqqU, twoTypeMult]
  unfold multUNum multAPNum twoTypeN
  generalize hDdef : (1 - p) + (3 - p) * μ = D at hD ⊢
  generalize hFdef : 1 + p = F at hp1 ⊢
  generalize hEdef : p ^ 2 - 1 = E at hp2 ⊢
  field_simp
  subst hEdef hFdef hDdef
  ring

include hp1 hp2 in
/-- `pqqS · (1 + p) D = −N`. -/
theorem twoTypeMult_pqqS :
    (twoTypeMult p q μ).pqqS p q μ * ((1 + p) * ((1 - p) + (3 - p) * μ)) = -twoTypeN p q μ := by
  simp only [pqqS, twoTypeMult]
  unfold multUNum multAPNum twoTypeN
  generalize hDdef : (1 - p) + (3 - p) * μ = D at hD ⊢
  generalize hFdef : 1 + p = F at hp1 ⊢
  generalize hEdef : p ^ 2 - 1 = E at hp2 ⊢
  field_simp
  subst hEdef hFdef hDdef
  ring

include hp1 hp2 in
/-- `pqqX = −2 μ pqqS`: this is how `cP` was chosen. -/
theorem twoTypeMult_pqqX :
    (twoTypeMult p q μ).pqqX q = -2 * μ * (twoTypeMult p q μ).pqqS p q μ := by
  simp only [pqqX, pqqS, twoTypeMult]
  unfold multUNum multAPNum multCPNum
  generalize hDdef : (1 - p) + (3 - p) * μ = D at hD ⊢
  generalize hFdef : 1 + p = F at hp1 ⊢
  generalize hEdef : p ^ 2 - 1 = E at hp2 ⊢
  field_simp
  subst hEdef hFdef hDdef
  ring

include hp1 hp2 in
/-- `(pqqF − 2μ² pqqS) · D² n₁ = 2 (1 − μ)² (1 + 2μ) D N − 2 (1 − μ)² x P3`. -/
theorem twoTypeMult_pqqF :
    ((twoTypeMult p q μ).pqqF p q μ - 2 * μ ^ 2 * (twoTypeMult p q μ).pqqS p q μ) *
        (((1 - p) + (3 - p) * μ) ^ 2 * (2 * p - 1 - 2 * μ * (2 - p))) =
      2 * (1 - μ) ^ 2 * (1 + 2 * μ) * ((1 - p) + (3 - p) * μ) * twoTypeN p q μ
        - 2 * (1 - μ) ^ 2 * (p - μ * (1 - p)) * sideP3 p μ := by
  simp only [pqqF, pqqS, twoTypeMult]
  unfold multUNum multAPNum multCPNum twoTypeN sideP3
  generalize hDdef : (1 - p) + (3 - p) * μ = D at hD ⊢
  generalize hFdef : 1 + p = F at hp1 ⊢
  generalize hEdef : p ^ 2 - 1 = E at hp2 ⊢
  field_simp
  subst hEdef hFdef hDdef
  ring

include hp2 in
/-- `aP · 2 (1 − p²) D² n₁ = 2 D (2μ (2p − 1) + p − 2) N − 2 (1 − p²) P5`. -/
theorem twoTypeMult_aP :
    (twoTypeMult p q μ).aP * (2 * (1 - p ^ 2) * ((1 - p) + (3 - p) * μ) ^ 2 *
        (2 * p - 1 - 2 * μ * (2 - p))) =
      2 * ((1 - p) + (3 - p) * μ) * (2 * μ * (2 * p - 1) + p - 2) * twoTypeN p q μ
        - 2 * (1 - p ^ 2) * sideP5 p μ := by
  simp only [twoTypeMult]
  unfold multAPNum twoTypeN sideP5
  generalize hDdef : (1 - p) + (3 - p) * μ = D at hD ⊢
  generalize hEdef : p ^ 2 - 1 = E at hp2 ⊢
  field_simp
  subst hEdef hDdef
  ring

end Identities

/-- From `X · F = R` with `F < 0 < R`: `X < 0`. -/
private theorem neg_of_mul_eq_of_neg {X F R : ℝ} (h : X * F = R) (hF : F < 0) (hR : 0 < R) :
    X < 0 := by
  by_contra hc
  push Not at hc
  have := mul_nonpos_of_nonneg_of_nonpos hc hF.le
  linarith

/-- From `X · F = R` with `0 < F` and `R < 0`: `X < 0`. -/
private theorem neg_of_mul_eq_of_pos {X F R : ℝ} (h : X * F = R) (hF : 0 < F) (hR : R < 0) :
    X < 0 := by
  by_contra hc
  push Not at hc
  have := mul_nonneg hc hF.le
  linarith

/-- **The explicit multipliers satisfy the sign conditions.** Let `0 < p ≤ 1/2`,
`p/2 ≤ μ ≤ p/(1 − p)` (written `μ (1 − p) ≤ p`), `μ < 1` and `N(μ) > 0`. Then
`twoTypeMult p q μ` is `Good`. With `n₁ = 2p − 1 − 2μ (2 − p) < 0` and `x = p − μ (1 − p) ≥ 0`,
the identities `twoTypeMult_*` reduce every condition to `N > 0` and the signs of the side
polynomials (`sideP2_neg`, `sideP3_neg`, `sideP5_pos`):
* `aP · 2 (1 − p²) D² n₁ = 2 D (2μ (2p − 1) + p − 2) N − 2 (1 − p²) P5 < 0`, so `aP > 0`;
* `qqqS = 0`;
* `qqqD · D² n₁ = 3 (1 + 2μ) D N − 3 x P2 > 0`, so `qqqD < 0`;
* `pqqU · (1 − p) D = −N` and `pqqS · (1 + p) D = −N`, so both are `< 0`;
* `(pqqF − 2μ² pqqS) · D² n₁ = 2 (1 − μ)² (1 + 2μ) D N − 2 (1 − μ)² x P3 > 0`, so it is `< 0`.

The parameter `q` enters only through `N`; no bound on `q` is needed here. -/
theorem exists_good {p q μ : ℝ} (hp : 0 < p) (hp2 : p ≤ 1 / 2) (h1 : p / 2 ≤ μ)
    (h2 : μ * (1 - p) ≤ p) (hμ1 : μ < 1) (hN : 0 < twoTypeN p q μ) :
    ∃ M : TwoTypeMultipliers, M.Good p q μ := by
  have hμ0 : 0 < μ := by linarith
  have hDpos : 0 < (1 - p) + (3 - p) * μ := by nlinarith
  have hD := hDpos.ne'
  have h1μ : 0 < 1 - μ := by linarith
  have h1p : 0 < 1 - p := by linarith
  have h1p' : 0 < 1 + p := by linarith
  have hpp : 0 < 1 - p ^ 2 := by nlinarith
  have hp21 : p ^ 2 - 1 ≠ 0 := by intro h; linarith
  have hn1 : 2 * p - 1 - 2 * μ * (2 - p) < 0 := by nlinarith
  have hx : 0 ≤ p - μ * (1 - p) := by linarith
  have ha : 2 * μ * (2 * p - 1) + p - 2 < 0 := by nlinarith
  have hP2 := sideP2_neg hp hp2 h1 h2
  have hP3 := sideP3_neg hp hp2 h1 h2
  have hP5 := sideP5_pos hp hp2 h1 h2
  have hD2n : ((1 - p) + (3 - p) * μ) ^ 2 * (2 * p - 1 - 2 * μ * (2 - p)) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hn1
  refine ⟨twoTypeMult p q μ, ?_, ?_, ?_, ?_, ?_, twoTypeMult_pqqX hD h1p'.ne' hp21, ?_⟩
  · -- `aP > 0`
    have key := twoTypeMult_aP (q := q) hD hp21
    have hF : 2 * (1 - p ^ 2) * ((1 - p) + (3 - p) * μ) ^ 2 * (2 * p - 1 - 2 * μ * (2 - p)) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hn1
    have hb : 2 * ((1 - p) + (3 - p) * μ) * (2 * μ * (2 * p - 1) + p - 2) * twoTypeN p q μ < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) ha) hN
    have hc : 0 < 2 * (1 - p ^ 2) * sideP5 p μ := by positivity
    by_contra hc'
    push Not at hc'
    have := mul_nonneg_of_nonpos_of_nonpos hc'.le hF.le
    linarith
  · exact (twoTypeMult_qqqS hD).le
  · refine neg_of_mul_eq_of_neg (twoTypeMult_qqqD hD) hD2n ?_
    have : 0 < 3 * (1 + 2 * μ) * ((1 - p) + (3 - p) * μ) * twoTypeN p q μ := by positivity
    have : 3 * (p - μ * (1 - p)) * sideP2 p μ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hP2.le
    linarith
  · exact neg_of_mul_eq_of_pos (twoTypeMult_pqqU hD h1p'.ne' hp21) (by positivity) (by linarith)
  · exact neg_of_mul_eq_of_pos (twoTypeMult_pqqS hD h1p'.ne' hp21) (by positivity) (by linarith)
  · refine neg_of_mul_eq_of_neg (twoTypeMult_pqqF hD h1p'.ne' hp21) hD2n ?_
    have : 0 < 2 * (1 - μ) ^ 2 * (1 + 2 * μ) * ((1 - p) + (3 - p) * μ) * twoTypeN p q μ := by
      positivity
    have : 2 * (1 - μ) ^ 2 * (p - μ * (1 - p)) * sideP3 p μ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hP3.le
    linarith

end TwoTypeTricklingDown
