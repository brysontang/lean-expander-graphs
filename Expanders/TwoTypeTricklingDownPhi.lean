/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.TwoTypeTricklingDownAlgebra

/-!
# Two-type trickling down, part 5: comparison with the edge-interpolated bound `Φ`

The open conjecture behind this work is `μ ≤ max_{uv} Φ(lam u, lam v)` with
`Φ(a, b) = s + a b/(1 − s)`, `s = (a + b)/2` (`edgePhi`), for `max lam ≤ 1/2`. This file compares
the proved two-type bound `β(p, q)` with `Φ(p, q)`. With `s = (p + q)/2`,
`N(Φ(p, q)) · 4 (2 − p − q)² = −q (p − q) H(p, q)` (`twoTypeN_edgePhi`), where `H` is the
polynomial `phiH`, and above `p/2` the sign of `N` decides the comparison with `β`.

## Theorems
* `edgePhi_zero`, `edgePhi_self`: `Φ(p, 0) = p/2`, `Φ(a, a) = a/(1 − a)`. **Proved.**
* `twoTypeBound_le_of_twoTypeN_nonneg`, `lt_twoTypeBound_of_twoTypeN_neg`: the sign of `N` decides
  the comparison with `β`. **Proved.**
* `phiH_neg`: `H < 0` on `0 ≤ q ≤ p ≤ 111/400`, by an exact Bernstein certificate. **Proved.**
* `twoTypeBound_le_edgePhi`: `β(p, q) ≤ Φ(p, q)` for `0 ≤ q ≤ p ≤ 111/400`. **Proved.**
* `exists_edgePhi_lt_twoTypeBound`: for `0 < p ≤ 1/2` with `p³ − p² − 7p + 2 < 0` (that is,
  `p > r₀ ≈ 0.27775`), `Φ(p, q) < β(p, q)` for all small `q > 0`. So the two-type theorem does not
  imply the `Φ` conjecture in that range. **Proved.**
* `twoTypeBound_two_fifths`: `β(2/5, 1/5) = (379 + 7 √1641)/1664 ≈ 0.398176`. **Proved.**

The Bernstein coefficients were generated and checked by `.lake/scratch-cert/lean/gen_bernH.py`.
-/

namespace TwoTypeTricklingDown

/-- The **edge-interpolated bound** `Φ(a, b) = s + a b/(1 − s)`, `s = (a + b)/2`, of the open
conjecture `μ ≤ max_{uv} Φ(lam u, lam v)`. At `s = 1` Lean's division by zero gives `Φ = s`; the
formula is only meant for `s < 1`. -/
noncomputable def edgePhi (a b : ℝ) : ℝ := (a + b) / 2 + a * b / (1 - (a + b) / 2)

/-- `Φ(p, 0) = p/2`. No hypotheses. -/
theorem edgePhi_zero (p : ℝ) : edgePhi p 0 = p / 2 := by
  unfold edgePhi
  ring

/-- `Φ(a, a) = a/(1 − a)`, Oppenheim's bound, for `a ≠ 1`. -/
theorem edgePhi_self {a : ℝ} (ha : a ≠ 1) : edgePhi a a = a / (1 - a) := by
  have h : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  unfold edgePhi
  have e : 1 - (a + a) / 2 = 1 - a := by ring
  rw [e]
  field_simp
  ring

/-- The polynomial `H` with `N(Φ(p, q)) · 4 (2 − p − q)² = −q (p − q) H(p, q)`. Its value at `q = 0`
is `2 (p + 1)(p − 2)(p³ − p² − 7p + 2)` (`phiH_zero`). -/
def phiH (p q : ℝ) : ℝ :=
  2 * p ^ 5 - 6 * p ^ 4 * q - 4 * p ^ 4 + 6 * p ^ 3 * q ^ 2 + 22 * p ^ 3 * q - 16 * p ^ 3
    - 2 * p ^ 2 * q ^ 3 - 28 * p ^ 2 * q ^ 2 + 16 * p ^ 2 * q + 22 * p ^ 2 + 10 * p * q ^ 3
    + 12 * p * q ^ 2 - 76 * p * q + 24 * p - 12 * q ^ 3 + 46 * q ^ 2 - 40 * q - 8

/-- `H(p, 0) = 2 (p + 1)(p − 2)(p³ − p² − 7p + 2)`. -/
theorem phiH_zero (p : ℝ) : phiH p 0 = 2 * (p + 1) * (p - 2) * (p ^ 3 - p ^ 2 - 7 * p + 2) := by
  unfold phiH
  ring

/-- **`N` at `Φ`.** `N(Φ(p, q)) · 4 (2 − p − q)² = −q (p − q) H(p, q)` whenever `p + q ≠ 2`. -/
theorem twoTypeN_edgePhi {p q : ℝ} (hpq : 2 - p - q ≠ 0) :
    twoTypeN p q (edgePhi p q) * (4 * (2 - p - q) ^ 2) = -q * (p - q) * phiH p q := by
  have hE : 1 - (p + q) / 2 ≠ 0 := by
    intro h; apply hpq; linarith
  unfold twoTypeN edgePhi phiH
  generalize hEdef : 1 - (p + q) / 2 = E at hE ⊢
  field_simp
  have : 2 - p - q = 2 * E := by rw [← hEdef]; ring
  rw [this]
  subst hEdef
  ring

/-- **`N(t) < 0` puts `t` below `β`.** For `0 ≤ p ≤ 1/2`, `0 ≤ q < 1`: if `N(t) < 0` then
`t < β(p, q)`. (No lower bound on `t` is needed: `t` lies strictly between the two roots.) -/
theorem lt_twoTypeBound_of_twoTypeN_neg {p q t : ℝ} (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) (hq : 0 ≤ q)
    (hq1 : q < 1) (hN : twoTypeN p q t < 0) : t < twoTypeBound p q := by
  obtain ⟨L, b, s, hL, hs0, hβ, h4, -, -⟩ := twoType_package hp0 hp2 hq hq1
  rw [hβ, lt_div_iff₀ (by positivity)]
  have h1 : 4 * L * twoTypeN p q t < 0 := mul_neg_of_pos_of_neg (by positivity) hN
  rw [h4] at h1
  have h2 := (abs_lt_of_sq_lt_sq' (a := 2 * L * t - b) (by linarith) hs0).2
  linarith

/-- **`N(t) ≥ 0` above `p/2` puts `t` above `β`.** For `0 ≤ p ≤ 1/2`, `0 ≤ q < 1`, `t ≥ p/2` and
`N(t) ≥ 0`: `β(p, q) ≤ t`. At `q = 0` this is `β(p, 0) = p/2 ≤ t`; for `q > 0`, `N(p/2) < 0`
keeps `t` away from the smaller root. -/
theorem twoTypeBound_le_of_twoTypeN_nonneg {p q t : ℝ} (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hq : 0 ≤ q) (hq1 : q < 1) (ht : p / 2 ≤ t) (hN : 0 ≤ twoTypeN p q t) :
    twoTypeBound p q ≤ t := by
  rcases hq.eq_or_lt with h0 | hq0
  · subst h0
    rw [twoTypeBound_zero hp2]
    exact ht
  obtain ⟨L, b, s, hL, hs0, hβ, h4, -, -⟩ := twoType_package hp0 hp2 hq hq1
  have hNh : twoTypeN p q (p / 2) < 0 := by
    rw [twoTypeN_half]
    have h1 : 0 < 1 - p := by linarith
    have h2 : 0 < 2 - p := by linarith
    have : 0 < q * (1 - p) * (1 + p) ^ 2 * (2 - p) := by positivity
    linarith
  have hlow : -s < L * p - b := by
    have h5 : 4 * L * twoTypeN p q (p / 2) < 0 := mul_neg_of_pos_of_neg (by positivity) hNh
    rw [h4] at h5
    have e : 2 * L * (p / 2) = L * p := by ring
    rw [e] at h5
    exact (abs_lt_of_sq_lt_sq' (by linarith) hs0).1
  by_contra hlt
  push Not at hlt
  rw [hβ, lt_div_iff₀ (by positivity)] at hlt
  have h1 : 2 * L * t - b < s := by linarith
  have h2 : L * p ≤ 2 * L * t := by nlinarith
  have h3 : (2 * L * t - b) ^ 2 < s ^ 2 := sq_lt_sq' (by linarith) h1
  have h5 : 0 ≤ 4 * L * twoTypeN p q t := mul_nonneg (by positivity) hN
  rw [h4] at h5
  linarith

/-- `phiH` on the unit square: `p = (111/400) X`, `q = p Y`. -/
noncomputable def bernH (X Y : ℝ) : ℝ :=
  -(16850581551 / 5120000000000) * X ^ 5 * Y ^ 3 +
  (50551744653 / 5120000000000) * X ^ 5 * Y ^ 2 - (50551744653 / 5120000000000) * X ^ 5 * Y +
  (16850581551 / 5120000000000) * X ^ 5 + (151807041 / 2560000000) * X ^ 4 * Y ^ 3 -
  (1062649287 / 6400000000) * X ^ 4 * Y ^ 2 + (1669877451 / 12800000000) * X ^ 4 * Y -
  (151807041 / 6400000000) * X ^ 4 - (4102893 / 16000000) * X ^ 3 * Y ^ 3 +
  (4102893 / 16000000) * X ^ 3 * Y ^ 2 + (1367631 / 4000000) * X ^ 3 * Y -
  (1367631 / 4000000) * X ^ 3 + (283383 / 80000) * X ^ 2 * Y ^ 2 -
  (234099 / 40000) * X ^ 2 * Y + (135531 / 80000) * X ^ 2 - (111 / 10) * X * Y +
  (333 / 50) * X - 8

/-- **Bernstein certificate for `H`** (bidegree `(5, 3)`, one box). On `[0, 1]²`,
`bernH = -41978731249/5120000000000 - S` with `S` a combination, with nonnegative coefficients, of
`X^i (1 - X)^(5 - i) Y^j (1 - Y)^(3 - j)`. -/
theorem bernH_neg {X Y : ℝ} (hX0 : 0 ≤ X) (hX1 : X ≤ 1) (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1) :
    bernH X Y < 0 := by
  obtain ⟨X', hX'⟩ : ∃ X', X' = 1 - X := ⟨_, rfl⟩
  obtain ⟨Y', hY'⟩ : ∃ Y', Y' = 1 - Y := ⟨_, rfl⟩
  have hX'0 : 0 ≤ X' := by rw [hX']; linarith
  have hY'0 : 0 ≤ Y' := by rw [hY']; linarith
  have e : bernH X Y =
      (-41978731249 / 5120000000000 : ℝ) - ((40918021268751 / 5120000000000 : ℝ) * X' ^ 5 * Y' ^ 3 +
      (122754063806253 / 5120000000000 : ℝ) * X' ^ 5 * Y * Y' ^ 2 +
      (122754063806253 / 5120000000000 : ℝ) * X' ^ 5 * Y ^ 2 * Y' +
      (40918021268751 / 5120000000000 : ℝ) * X' ^ 5 * Y ^ 3 +
      (34098181268751 / 1024000000000 : ℝ) * X * X' ^ 4 * Y' ^ 3 +
      (113660943806253 / 1024000000000 : ℝ) * X * X' ^ 4 * Y * Y' ^ 2 +
      (125027343806253 / 1024000000000 : ℝ) * X * X' ^ 4 * Y ^ 2 * Y' +
      (45464581268751 / 1024000000000 : ℝ) * X * X' ^ 4 * Y ^ 3 +
      (26410942868751 / 512000000000 : ℝ) * X ^ 2 * X' ^ 3 * Y' ^ 3 +
      (104962095806253 / 512000000000 : ℝ) * X ^ 2 * X' ^ 3 * Y * Y' ^ 2 +
      (128877711806253 / 512000000000 : ℝ) * X ^ 2 * X' ^ 3 * Y ^ 2 * Y' +
      (50326558868751 / 512000000000 : ℝ) * X ^ 2 * X' ^ 3 * Y ^ 3 +
      (18031362836751 / 512000000000 : ℝ) * X ^ 3 * X' ^ 2 * Y' ^ 3 +
      (97007633342253 / 512000000000 : ℝ) * X ^ 3 * X' ^ 2 * Y * Y' ^ 2 +
      (134348931998253 / 512000000000 : ℝ) * X ^ 3 * X' ^ 2 * Y ^ 2 * Y' +
      (55503954068751 / 512000000000 : ℝ) * X ^ 3 * X' ^ 2 * Y ^ 3 +
      (9158787067311 / 1024000000000 : ℝ) * X ^ 4 * X' * Y' ^ 3 +
      (90086947133853 / 1024000000000 : ℝ) * X ^ 4 * X' * Y * Y' ^ 2 +
      (141460479447693 / 1024000000000 : ℝ) * X ^ 4 * X' * Y ^ 2 * Y' +
      (60996766868751 / 1024000000000 : ℝ) * X ^ 4 * X' * Y ^ 3 +
      (84428705084253 / 5120000000000 : ℝ) * X ^ 5 * Y * Y' ^ 2 +
      (150207540093453 / 5120000000000 : ℝ) * X ^ 5 * Y ^ 2 * Y' +
      (66804997268751 / 5120000000000 : ℝ) * X ^ 5 * Y ^ 3) := by
    rw [hX', hY']
    unfold bernH
    ring
  rw [e, sub_neg]
  exact lt_of_lt_of_le (b := 0) (by norm_num) (by positivity)

/-- `H` on the unit square, as `bernH`. -/
theorem phiH_eq_bernH (X Y : ℝ) : phiH (111 / 400 * X) (111 / 400 * X * Y) = bernH X Y := by
  unfold phiH bernH
  ring

/-- **`H < 0`** on `0 ≤ q ≤ p ≤ 111/400` (exact Bernstein certificate `bernH_neg`, after
`p = (111/400) X`, `q = p Y`). The bound `111/400` is just below the root `r₀ ≈ 0.27775` of
`H(p, 0)`, beyond which `H(p, q) > 0` for small `q`. -/
theorem phiH_neg {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 111 / 400) : phiH p q < 0 := by
  rcases (hq.trans hqp).eq_or_lt with h0 | hp0
  · have hq0 : q = 0 := le_antisymm (h0 ▸ hqp) hq
    rw [← h0, hq0]
    norm_num [phiH]
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = p / (111 / 400) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = q / p := ⟨_, rfl⟩
  have hpX : p = 111 / 400 * X := by rw [hX]; field_simp
  have hqY : q = 111 / 400 * X * Y := by rw [← hpX, hY]; field_simp
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hX1 : X ≤ 1 := by rw [hX, div_le_one (by norm_num)]; exact hp
  have hY0 : 0 ≤ Y := by rw [hY]; exact div_nonneg hq hp0.le
  have hY1 : Y ≤ 1 := by rw [hY, div_le_one hp0]; exact hqp
  rw [hqY, hpX, phiH_eq_bernH]
  exact bernH_neg hX0 hX1 hY0 hY1

/-- **`β ≤ Φ` for `p ≤ 111/400`.** For `0 ≤ q ≤ p ≤ 111/400`, `β(p, q) ≤ Φ(p, q)`: here `Φ ≥ p/2`
and `N(Φ) = −q (p − q) H/(4 (2 − p − q)²) ≥ 0` since `H < 0` (`phiH_neg`). Equality holds at
`q = 0` (both `p/2`) and at `q = p` (both `p/(1 − p)`). -/
theorem twoTypeBound_le_edgePhi {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 111 / 400) :
    twoTypeBound p q ≤ edgePhi p q := by
  have hp0 : 0 ≤ p := hq.trans hqp
  have hden : 0 < 2 - p - q := by linarith
  have hE : 0 < 1 - (p + q) / 2 := by linarith
  refine twoTypeBound_le_of_twoTypeN_nonneg hp0 (by linarith) hq (by linarith) ?_ ?_
  · unfold edgePhi
    have : 0 ≤ p * q / (1 - (p + q) / 2) := div_nonneg (mul_nonneg hp0 hq) hE.le
    linarith
  · have key := twoTypeN_edgePhi (p := p) (q := q) hden.ne'
    have hH := phiH_neg hq hqp hp
    have hR : 0 ≤ -q * (p - q) * phiH p q := by
      have : 0 ≤ q * (p - q) := mul_nonneg hq (by linarith)
      nlinarith
    rw [← key] at hR
    by_contra hc
    push Not at hc
    have := mul_neg_of_neg_of_pos hc
      (mul_pos (by norm_num) (pow_pos hden 2) : (0 : ℝ) < 4 * (2 - p - q) ^ 2)
    linarith

/-- **`Φ < β` beyond `r₀`, for small `q`.** Let `0 < p ≤ 1/2` with `p³ − p² − 7p + 2 < 0`, i.e.
`p > r₀ ≈ 0.27775`. Then there is `q₀ > 0` with `Φ(p, q) < β(p, q)` for every `0 < q < q₀`.
Indeed `H(p, 0) = 2 (p + 1)(p − 2)(p³ − p² − 7p + 2) > 0`, so `H(p, q) > 0` for small `q` by
continuity, and then `N(Φ) < 0`. So in this range `β` does not prove the `Φ` conjecture. -/
theorem exists_edgePhi_lt_twoTypeBound {p : ℝ} (hp0 : 0 < p) (hp2 : p ≤ 1 / 2)
    (hr : p ^ 3 - p ^ 2 - 7 * p + 2 < 0) :
    ∃ q₀ > 0, ∀ q, 0 < q → q < q₀ → edgePhi p q < twoTypeBound p q := by
  have hH0 : 0 < phiH p 0 := by
    rw [phiH_zero]
    have h1 : 0 < 2 * (p + 1) := by linarith
    have h2 : 0 < (p - 2) * (p ^ 3 - p ^ 2 - 7 * p + 2) :=
      mul_pos_of_neg_of_neg (by linarith) hr
    have := mul_pos h1 h2
    linarith [mul_assoc (2 * (p + 1)) (p - 2) (p ^ 3 - p ^ 2 - 7 * p + 2)]
  have hcont : Continuous (fun q => phiH p q) := by
    unfold phiH
    fun_prop
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont.continuousAt (phiH p 0) hH0
  refine ⟨min δ p, lt_min hδ hp0, fun q hq hqq => ?_⟩
  have hqδ : q < δ := lt_of_lt_of_le hqq (min_le_left _ _)
  have hqp : q < p := lt_of_lt_of_le hqq (min_le_right _ _)
  have hHq : 0 < phiH p q := by
    have hd : dist q 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hq]; exact hqδ
    have := hball hd
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).1
    linarith
  have hden : 0 < 2 - p - q := by linarith
  refine lt_twoTypeBound_of_twoTypeN_neg hp0.le hp2 hq.le (by linarith) ?_
  have key := twoTypeN_edgePhi (p := p) (q := q) hden.ne'
  have hR : -q * (p - q) * phiH p q < 0 := by
    have : 0 < q * (p - q) * phiH p q := mul_pos (mul_pos hq (by linarith)) hHq
    linarith
  rw [← key] at hR
  by_contra hc
  push Not at hc
  have := mul_nonneg hc (by positivity : (0 : ℝ) ≤ 4 * (2 - p - q) ^ 2)
  linarith

/-- **The value at `(2/5, 1/5)`**: `β(2/5, 1/5) = (379 + 7 √1641)/1664 ≈ 0.398176`, against
`Φ(2/5, 1/5) = 29/70 ≈ 0.41429` and the edge-average bound `3/7`. Here `Δ = 1641/625`. -/
theorem twoTypeBound_two_fifths :
    twoTypeBound (2 / 5) (1 / 5) = (379 + 7 * Real.sqrt 1641) / 1664 := by
  have hΔ : twoTypeDelta (2 / 5) (1 / 5) = 1641 / 625 := by
    unfold twoTypeDelta
    norm_num
  have h625 : Real.sqrt 625 = 25 := by
    rw [show (625 : ℝ) = 25 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hs : Real.sqrt (1641 / 625) = Real.sqrt 1641 / 25 := by
    rw [Real.sqrt_div' _ (by norm_num), h625]
  unfold twoTypeBound
  rw [hΔ, hs]
  ring

/-- `Φ(2/5, 1/5) = 29/70`. -/
theorem edgePhi_two_fifths : edgePhi (2 / 5) (1 / 5) = 29 / 70 := by
  unfold edgePhi
  norm_num

end TwoTypeTricklingDown
