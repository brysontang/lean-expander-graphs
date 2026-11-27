/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.AlonBoppana

/-!
# Quantitative Alon–Boppana: the cosine rate and an explicit threshold

`SimpleGraph.alon_boppana` (in `Expanders.AlonBoppana`) says that every sufficiently large
`d`-regular graph has `λ₂ ≥ 2√(d − 1) − ε`, but it only asserts that a threshold `N(d, ε)`
exists, and the tent profile behind it has accuracy `O(1/K)` at radius `K`. This file proves the
bound at the sharp rate `O(1/k²)`:

  *two vertices at distance at least `2k` force `λ₂ ≥ 2√(d − 1) · cos(π / (k + 1))`*,

and from it an explicit threshold `N(d, ε) = (d + 1) ^ (2k − 1) + 1` with
`k ≈ π (d − 1)^{1/4} ε^{−1/2}`.

The distance hypothesis cannot be weakened to `2k − 1`: the complete graph `K₄` (`k = 1`,
diameter `1`, `λ₂ = −1 < 0`) and the cube `Q₃` (`k = 2`, diameter `3`, `λ₂ = 1 < √2`) violate
the conclusion. The bound is attained by `K₃,₃` at `k = 1` (diameter `2`, `λ₂ = 0`).

## Definitions
* `SimpleGraph.alonBoppanaRadius d ε`: the radius
  `k = max(1, ⌈π √(√(d − 1) / ε)⌉ − 1)`. For `ε > 0` it is the least `k ≥ 1` with
  `π² √(d − 1) ≤ ε (k + 1)²`, which is what the cosine bound needs for accuracy `ε`.
* `SimpleGraph.alonBoppanaCard d ε`: the threshold `(d + 1) ^ (2k − 1) + 1` with
  `k = alonBoppanaRadius d ε`.

## Theorems
* `SimpleGraph.AlonBoppana.exists_profile_cos`: for every `d` and every `k ≥ 1` there is a
  nonnegative, nonincreasing profile vanishing from `k` on that is a subsolution of the radial
  eigenvalue equation of the `d`-regular tree with eigenvalue `2√(d − 1) cos(π / (k + 1))`.
  **Proved.**
* `SimpleGraph.AlonBoppana.radial_mul_radial_eq_zero_of_le_edist` and
  `SimpleGraph.AlonBoppana.le_secondAdjEigenvalue_of_le_edist`: the separation lemma and the
  two-centre bound of `Expanders.AlonBoppana` under the weaker hypothesis `dist(v₀, v₁) ≥ 2K`
  (instead of `> 2K`). **Proved.**
* `SimpleGraph.cos_le_secondAdjEigenvalue_of_le_edist`: **quantitative Alon–Boppana**,
  `dist(v₀, v₁) ≥ 2k` with `k ≥ 1` gives `λ₂ ≥ 2√(d − 1) cos(π / (k + 1))`. **Proved.**
* `SimpleGraph.cos_le_secondAdjEigenvalue_of_lt_edist`: the same from `dist(v₀, v₁) > 2k`.
  **Proved.**
* `SimpleGraph.cos_le_secondAdjEigenvalue_of_le_ediam`: the same from `diam G ≥ 2k`. **Proved.**
* `SimpleGraph.cos_le_secondAdjEigenvalue_of_pow_lt_card`: the same from
  `(d + 1) ^ (2k − 1) < |V|`. **Proved.**
* `SimpleGraph.sub_le_secondAdjEigenvalue_of_le_edist` and
  `SimpleGraph.sub_le_secondAdjEigenvalue_of_pow_lt_card`: if `π² √(d − 1) ≤ ε (k + 1)²`, the
  same hypotheses give `λ₂ ≥ 2√(d − 1) − ε`. **Proved.**
* `SimpleGraph.one_le_alonBoppanaRadius`, `SimpleGraph.pi_sq_mul_sqrt_le_mul_alonBoppanaRadius`
  and `SimpleGraph.alonBoppanaRadius_le`: `alonBoppanaRadius d ε` is at least `1`, is large
  enough for accuracy `ε`, and is the least such radius. **Proved.**
* `SimpleGraph.alon_boppana_explicit`: **explicit Alon–Boppana**, `ε > 0` and
  `alonBoppanaCard d ε ≤ |V|` give `λ₂ ≥ 2√(d − 1) − ε`. **Proved.**

## Proof

The argument of `Expanders.AlonBoppana` reduces everything to a profile `g : ℕ → ℝ` that is
nonnegative, nonincreasing, vanishes from `K` on, and satisfies `μ g(0) ≤ d g(1)` and
`μ g(i + 1) ≤ g(i) + (d − 1) g(i + 2)`. Here `μ = 2√(d − 1) cos θ` with `θ = π / (k + 1)`, and
for `d ≥ 2` the profile is the damped sine of Nilli (2004),

  `g(i) = (d − 1)^(−i/2) · sin(φ + iθ)`, cut off to `0` once `φ + iθ ≥ π`.

Away from the centre the step inequality is the identity
`sin x + sin(x + 2θ) = 2 cos θ sin(x + θ)`, with the cut-off only helping. The phase
`φ = π/2 − arctan((d − 2) cos θ / (d sin θ))` is chosen so that the centre inequality is an
equality; it satisfies `θ ≤ φ ≤ π/2`, so `φ + kθ ≥ π` and the profile vanishes from `k` on.
Monotonicity follows from `sin(x + θ) / sin x ≤ sin(φ + θ) / sin φ ≤ √(d − 1)` for `x ≥ φ`.
For `d ≤ 1` the eigenvalue is `0` and the indicator of the centre works. Since the profile is
supported on the ball of radius `k − 1`, two centres at distance `2k` already have disjoint
supports with no edge between them, which is why `2k` (and not `2k + 1`) suffices.

## References
* A. Nilli, *Tight estimates for eigenvalues of regular graphs*, Electron. J. Combin. 11 (2004),
  #N9. Theorem 1 (for `d ≥ 3`): `s` vertices pairwise at distance `≥ 4k` give
  `λ_s ≥ 2√(d − 1) cos(π / (2k))`. For `s = 2` this is the case `k ↦ 2k − 1` of
  `cos_le_secondAdjEigenvalue_of_le_edist`, which needs only distance `≥ 4k − 2`.
* J. Friedman, *Some geometric aspects of graphs and their eigenfunctions*, Duke Math. J. 69
  (1993), 487–525: for `d ≥ 3`, diameter `2k` gives
  `λ₂ ≥ 2√(d − 1)(1 − π²/(2k²) + O(k⁻⁴))`; `cos_le_secondAdjEigenvalue_of_le_ediam` is this
  bound with an exact constant.
* A. Nilli, *On the second eigenvalue of a graph*, Discrete Math. 91 (1991), 207–210: the
  `O(1 / diameter)` rate.
-/

open Finset Matrix Real

namespace SimpleGraph

namespace AlonBoppana

/-! ## The cut-off sine -/

section SinCut

/-- `sin` cut off to `0` from its first positive zero `π` on. -/
private noncomputable def sinCut (x : ℝ) : ℝ := if x < π then Real.sin x else 0

private theorem sinCut_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ sinCut x := by
  unfold sinCut
  split_ifs with h
  · exact Real.sin_nonneg_of_nonneg_of_le_pi hx h.le
  · exact le_rfl

private theorem sinCut_eq_sin {x : ℝ} (hx : x ≤ π) : sinCut x = Real.sin x := by
  unfold sinCut
  split_ifs with h
  · rfl
  · rw [le_antisymm hx (not_lt.mp h), Real.sin_pi]

private theorem sinCut_of_le {x : ℝ} (hx : π ≤ x) : sinCut x = 0 := by
  unfold sinCut
  rw [if_neg (not_lt.mpr hx)]

/-- On `[π, 2π]` the sine is nonpositive, so cutting it off only increases it. -/
private theorem sin_le_sinCut {x : ℝ} (h2 : x ≤ 2 * π) : Real.sin x ≤ sinCut x := by
  unfold sinCut
  split_ifs with h
  · exact le_rfl
  · have e : Real.sin x = -Real.sin (x - π) := by rw [Real.sin_sub_pi, neg_neg]
    have := Real.sin_nonneg_of_nonneg_of_le_pi (x := x - π) (by linarith [not_lt.mp h])
      (by linarith)
    linarith

/-- The step inequality for the cut-off sine: `2 cos θ · S(x + θ) ≤ S(x) + S(x + 2θ)`. -/
private theorem two_cos_mul_sinCut_le {x θ : ℝ} (hx : 0 ≤ x) (hθ0 : 0 ≤ θ) :
    2 * Real.cos θ * sinCut (x + θ) ≤ sinCut x + sinCut (x + 2 * θ) := by
  by_cases h : x + θ < π
  · rw [sinCut_eq_sin (by linarith : x ≤ π), sinCut_eq_sin h.le]
    have hle := sin_le_sinCut (x := x + 2 * θ) (by linarith [Real.pi_pos])
    have h1 : Real.sin (x + 2 * θ)
        = Real.sin (x + θ) * Real.cos θ + Real.cos (x + θ) * Real.sin θ := by
      rw [← Real.sin_add]; congr 1; ring
    have h2 : Real.sin x
        = Real.sin (x + θ) * Real.cos θ - Real.cos (x + θ) * Real.sin θ := by
      rw [← Real.sin_sub]; congr 1; ring
    linarith
  · rw [sinCut_of_le (not_lt.mp h), mul_zero]
    exact add_nonneg (sinCut_nonneg hx) (sinCut_nonneg (by linarith))

/-- The growth bound for the cut-off sine beyond the phase `φ`: if
`sin(φ + θ) ≤ s sin φ` then `S(x + θ) ≤ s S(x)` for every `x ≥ φ`. -/
private theorem sinCut_add_le {x φ θ s : ℝ} (hφ0 : 0 < φ) (hφπ : φ < π) (hφx : φ ≤ x)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ π) (hs : 0 ≤ s) (hratio : Real.sin (φ + θ) ≤ s * Real.sin φ) :
    sinCut (x + θ) ≤ s * sinCut x := by
  by_cases h : x + θ < π
  · have hxπ : x < π := by linarith
    rw [sinCut_eq_sin h.le, sinCut_eq_sin hxπ.le]
    have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφπ
    have hsθ : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθ
    have hsx : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hxπ.le
    have h3 : 0 ≤ Real.sin θ * (Real.sin x * Real.cos φ - Real.cos x * Real.sin φ) := by
      rw [← Real.sin_sub]
      exact mul_nonneg hsθ (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
    have key : Real.sin φ * Real.sin (x + θ) ≤ Real.sin x * Real.sin (φ + θ) := by
      rw [Real.sin_add, Real.sin_add]
      nlinarith [h3]
    have : Real.sin φ * Real.sin (x + θ) ≤ Real.sin φ * (s * Real.sin x) := by
      calc _ ≤ Real.sin x * Real.sin (φ + θ) := key
        _ ≤ Real.sin x * (s * Real.sin φ) := mul_le_mul_of_nonneg_left hratio hsx
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hsφ
  · rw [sinCut_of_le (not_lt.mp h)]
    exact mul_nonneg hs (sinCut_nonneg (by linarith))

end SinCut

/-! ## The phase -/

section Phase

/-- The phase of the sine profile: `φ = π/2 − arctan((d − 2) cos θ / (d sin θ))`, so that
`cot φ = (d − 2) cos θ / (d sin θ)`. It is used only for `d ≥ 2` and `θ ∈ (0, π/2]`, where
`d sin θ > 0` (otherwise the quotient is a junk value). -/
private noncomputable def sinePhase (d : ℕ) (θ : ℝ) : ℝ :=
  π / 2 - Real.arctan (((d : ℝ) - 2) * Real.cos θ / (d * Real.sin θ))

/-- For `d ≥ 2` and `θ ∈ (0, π/2]` the phase lies in `[θ, π/2]` and satisfies
`d sin θ cos φ = (d − 2) cos θ sin φ`. -/
private theorem sinePhase_spec {d : ℕ} (hd : 2 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ π / 2) :
    0 < sinePhase d θ ∧ θ ≤ sinePhase d θ ∧ sinePhase d θ ≤ π / 2 ∧
      (d : ℝ) * Real.sin θ * Real.cos (sinePhase d θ)
        = ((d : ℝ) - 2) * Real.cos θ * Real.sin (sinePhase d θ) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcθ : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hθ
  obtain ⟨y, hy⟩ : ∃ y, y = ((d : ℝ) - 2) * Real.cos θ / (d * Real.sin θ) := ⟨_, rfl⟩
  have hφ : sinePhase d θ = π / 2 - Real.arctan y := by rw [sinePhase, hy]
  have hy0 : 0 ≤ y := by
    rw [hy]
    exact div_nonneg (mul_nonneg (by linarith) hcθ) (by positivity)
  have hsφ : Real.sin (sinePhase d θ) = 1 / √(1 + y ^ 2) := by
    rw [hφ, Real.sin_pi_div_two_sub, Real.cos_arctan]
  have hcφ : Real.cos (sinePhase d θ) = y / √(1 + y ^ 2) := by
    rw [hφ, Real.cos_pi_div_two_sub, Real.sin_arctan]
  have hid : (d : ℝ) * Real.sin θ * Real.cos (sinePhase d θ)
      = ((d : ℝ) - 2) * Real.cos θ * Real.sin (sinePhase d θ) := by
    rw [hsφ, hcφ, hy]
    have : (d : ℝ) * Real.sin θ ≠ 0 := by positivity
    field_simp
  have hpos : 0 < sinePhase d θ := by
    have := Real.arctan_lt_pi_div_two y
    rw [hφ]; linarith
  refine ⟨hpos, ?_, ?_, hid⟩
  · by_contra hlt
    have hlt := not_le.mp hlt
    have hp : 0 < Real.sin (θ - sinePhase d θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    rw [Real.sin_sub] at hp
    have hsφ0 : 0 ≤ Real.sin (sinePhase d θ) := by rw [hsφ]; positivity
    have hd0 : (0 : ℝ) < d := by linarith
    nlinarith [mul_pos hd0 hp, mul_nonneg hcθ hsφ0]
  · have := Real.arctan_nonneg.mpr hy0
    rw [hφ]; linarith

end Phase

/-! ## The profile -/

section Profile

/-- The sine profile for `d ≥ 2`: `g(i) = (d − 1)^(−i/2) · S(φ + iθ)` with `θ = π / (k + 1)`. -/
private theorem exists_profile_cos_of_two_le {d k : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) :
    ∃ g : ℕ → ℝ, Antitone g ∧ (∀ i, 0 ≤ g i) ∧ 0 < g 0 ∧ (∀ i, k ≤ i → g i = 0) ∧
      (2 * √((d : ℝ) - 1) * Real.cos (π / (k + 1))) * g 0 ≤ d * g 1 ∧
      ∀ i, (2 * √((d : ℝ) - 1) * Real.cos (π / (k + 1))) * g (i + 1)
        ≤ g i + ((d : ℝ) - 1) * g (i + 2) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set θ : ℝ := π / (k + 1) with hθ_def
  have hk1 : (0 : ℝ) < k + 1 := by linarith
  have hθ0 : 0 < θ := div_pos Real.pi_pos hk1
  have hθ2 : θ ≤ π / 2 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
  have hkθ : ((k : ℝ) + 1) * θ = π := by rw [hθ_def]; field_simp
  obtain ⟨hφ0, hθφ, hφ2, hid⟩ := sinePhase_spec hd hθ0 hθ2
  set φ := sinePhase d θ with hφ_def
  set s : ℝ := √((d : ℝ) - 1) with hs_def
  have hs2 : s ^ 2 = (d : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : 1 ≤ s := by nlinarith
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = s⁻¹ := ⟨_, rfl⟩
  have hst : s * t = 1 := by rw [ht_def]; exact mul_inv_cancel₀ (by linarith)
  have ht0 : 0 < t := by rw [ht_def]; exact inv_pos.mpr (by linarith)
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith [Real.pi_pos])
  -- the centre identity `d sin (φ + θ) = 2 (d - 1) cos θ sin φ`
  have hcentre : (d : ℝ) * Real.sin (φ + θ) = 2 * s ^ 2 * Real.cos θ * Real.sin φ := by
    rw [Real.sin_add, hs2]
    linear_combination hid
  have hratio : Real.sin (φ + θ) ≤ s * Real.sin φ := by
    have h2s : 2 * s * Real.cos θ ≤ d := by
      have := Real.cos_le_one θ
      nlinarith [sq_nonneg (s - 1)]
    have hd0 : (0 : ℝ) < d := by linarith
    refine le_of_mul_le_mul_left ?_ hd0
    rw [hcentre]
    nlinarith [mul_le_mul_of_nonneg_right h2s (mul_nonneg hs0 hsφ.le)]
  have hx : ∀ i : ℕ, φ + ((i + 1 : ℕ) : ℝ) * θ = (φ + (i : ℝ) * θ) + θ := by
    intro i; push_cast; ring
  have hx2 : ∀ i : ℕ, φ + ((i + 2 : ℕ) : ℝ) * θ = (φ + (i : ℝ) * θ) + 2 * θ := by
    intro i; push_cast; ring
  have hxi : ∀ i : ℕ, φ ≤ φ + (i : ℝ) * θ := fun i => by
    have : 0 ≤ (i : ℝ) * θ := by positivity
    linarith
  refine ⟨fun i => t ^ i * sinCut (φ + (i : ℝ) * θ), antitone_nat_of_succ_le fun n => ?_,
    fun i => mul_nonneg (pow_nonneg ht0.le i) (sinCut_nonneg (by linarith [hxi i])), ?_,
    fun i hi => ?_, ?_, fun i => ?_⟩
  · -- antitone
    change t ^ (n + 1) * sinCut (φ + ((n + 1 : ℕ) : ℝ) * θ) ≤ t ^ n * sinCut (φ + (n : ℝ) * θ)
    rw [hx n]
    have h := sinCut_add_le hφ0 (by linarith [Real.pi_pos]) (hxi n) hθ0.le
      (by linarith [Real.pi_pos]) hs0 hratio
    calc t ^ (n + 1) * sinCut (φ + (n : ℝ) * θ + θ)
        ≤ t ^ (n + 1) * (s * sinCut (φ + (n : ℝ) * θ)) :=
          mul_le_mul_of_nonneg_left h (pow_nonneg ht0.le _)
      _ = t ^ n * sinCut (φ + (n : ℝ) * θ) := by
          rw [pow_succ]
          linear_combination (t ^ n * sinCut (φ + (n : ℝ) * θ)) * hst
  · -- positive at the centre
    change 0 < t ^ 0 * sinCut (φ + ((0 : ℕ) : ℝ) * θ)
    rw [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero,
      sinCut_eq_sin (by linarith [Real.pi_pos])]
    exact hsφ
  · -- finitely supported
    change t ^ i * sinCut (φ + (i : ℝ) * θ) = 0
    have hi' : (k : ℝ) ≤ i := by exact_mod_cast hi
    rw [sinCut_of_le (by nlinarith), mul_zero]
  · -- the centre: an equality
    change (2 * s * Real.cos θ) * (t ^ 0 * sinCut (φ + ((0 : ℕ) : ℝ) * θ))
      ≤ d * (t ^ 1 * sinCut (φ + ((1 : ℕ) : ℝ) * θ))
    rw [Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul, pow_zero, one_mul, pow_one,
      sinCut_eq_sin (by linarith [Real.pi_pos]), sinCut_eq_sin (by linarith)]
    have e : (d : ℝ) * (t * Real.sin (φ + θ)) = 2 * s * Real.cos θ * Real.sin φ := by
      calc (d : ℝ) * (t * Real.sin (φ + θ)) = t * ((d : ℝ) * Real.sin (φ + θ)) := by ring
        _ = t * (2 * s ^ 2 * Real.cos θ * Real.sin φ) := by rw [hcentre]
        _ = 2 * s * Real.cos θ * Real.sin φ := by
          linear_combination (2 * s * Real.cos θ * Real.sin φ) * hst
    rw [e]
  · -- the step
    change (2 * s * Real.cos θ) * (t ^ (i + 1) * sinCut (φ + ((i + 1 : ℕ) : ℝ) * θ))
      ≤ t ^ i * sinCut (φ + (i : ℝ) * θ)
        + ((d : ℝ) - 1) * (t ^ (i + 2) * sinCut (φ + ((i + 2 : ℕ) : ℝ) * θ))
    rw [hx i, hx2 i]
    have h := two_cos_mul_sinCut_le (x := φ + (i : ℝ) * θ) (by linarith [hxi i]) hθ0.le
    have e1 : (2 * s * Real.cos θ) * (t ^ (i + 1) * sinCut (φ + (i : ℝ) * θ + θ))
        = t ^ i * (2 * Real.cos θ * sinCut (φ + (i : ℝ) * θ + θ)) := by
      rw [pow_succ]
      linear_combination (2 * Real.cos θ * t ^ i * sinCut (φ + (i : ℝ) * θ + θ)) * hst
    have e2 : ((d : ℝ) - 1) * (t ^ (i + 2) * sinCut (φ + (i : ℝ) * θ + 2 * θ))
        = t ^ i * sinCut (φ + (i : ℝ) * θ + 2 * θ) := by
      rw [← hs2, pow_add]
      linear_combination (t ^ i * sinCut (φ + (i : ℝ) * θ + 2 * θ)) * (s * t + 1) * hst
    rw [e1, e2, ← mul_add]
    exact mul_le_mul_of_nonneg_left h (pow_nonneg ht0.le i)

/-- **The sine profile.** For every degree `d` and every `k ≥ 1` there is a profile `g : ℕ → ℝ`
that is nonnegative, nonincreasing, positive at `0`, vanishes from `k` on, and is a subsolution
of the radial eigenvalue equation of the `d`-regular tree with eigenvalue
`μ = 2√(d − 1) cos(π / (k + 1))`: `μ g(0) ≤ d g(1)` and
`μ g(i + 1) ≤ g(i) + (d − 1) g(i + 2)` for all `i`.

For `d ≥ 2` the profile is `g(i) = (d − 1)^(−i/2) sin(φ + iθ)`, cut off to `0` once
`φ + iθ ≥ π`, with `θ = π / (k + 1)` and the phase `φ ∈ [θ, π/2]` given by
`cot φ = (d − 2) cos θ / (d sin θ)` (for `d = 2`, `φ = π/2`); the centre inequality then holds
with equality. For `d = 0` and `d = 1` the term `√(d − 1)` is `√(−1) = 0`, resp. `√0 = 0`, in
Lean, so `μ = 0`, and the indicator of `0` works. The hypothesis `k ≥ 1` is necessary: for
`k = 0` the support condition would force `g 0 = 0`. -/
theorem exists_profile_cos (d : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ∃ g : ℕ → ℝ, Antitone g ∧ (∀ i, 0 ≤ g i) ∧ 0 < g 0 ∧ (∀ i, k ≤ i → g i = 0) ∧
      (2 * √((d : ℝ) - 1) * Real.cos (π / (k + 1))) * g 0 ≤ d * g 1 ∧
      ∀ i, (2 * √((d : ℝ) - 1) * Real.cos (π / (k + 1))) * g (i + 1)
        ≤ g i + ((d : ℝ) - 1) * g (i + 2) := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · -- `d ≤ 1`: the eigenvalue is `0` and the indicator of the centre works
    have hs : √((d : ℝ) - 1) = 0 := Real.sqrt_eq_zero_of_nonpos (by
      have : (d : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hd
      linarith)
    refine ⟨fun i => if i = 0 then 1 else 0, antitone_nat_of_succ_le fun n => ?_,
      fun i => ?_, by simp, fun i hi => if_neg (by omega), ?_, fun i => ?_⟩
    · rw [if_neg (Nat.succ_ne_zero n)]
      split_ifs <;> norm_num
    · change 0 ≤ if i = 0 then (1 : ℝ) else 0
      split_ifs <;> norm_num
    · simp [hs]
    · change 2 * √((d : ℝ) - 1) * Real.cos (π / (k + 1)) * (if i + 1 = 0 then (1 : ℝ) else 0)
        ≤ (if i = 0 then (1 : ℝ) else 0) + ((d : ℝ) - 1) * (if i + 2 = 0 then (1 : ℝ) else 0)
      rw [if_neg (Nat.succ_ne_zero i), if_neg (Nat.succ_ne_zero (i + 1)), mul_zero, mul_zero,
        add_zero]
      split_ifs <;> norm_num
  · exact exists_profile_cos_of_two_le hd hk

end Profile

/-! ## Two centres at distance exactly `2K` -/

section TwoCentres

section Radial

variable {V : Type*} {G : SimpleGraph V}

/-- Radial functions whose profile vanishes from `K` on, around centres at distance at least
`2K`, have disjoint supports with no edge between them: for `K ≥ 1` the supports are balls of
radius `K − 1`, and `(K − 1) + 1 + (K − 1) < 2K`; for `K = 0` both functions vanish. This is
`SimpleGraph.AlonBoppana.radial_mul_radial_eq_zero` with `≤` in place of `<`. -/
theorem radial_mul_radial_eq_zero_of_le_edist {v₀ v₁ v u : V} {g : ℕ → ℝ} {K : ℕ}
    (hK : ∀ i, K ≤ i → g i = 0) (hfar : ((2 * K : ℕ) : ℕ∞) ≤ G.edist v₀ v₁)
    (hvu : G.edist v u ≤ 1) : radial G v₀ g v * radial G v₁ g u = 0 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨a, ha, hav⟩ := exists_edist_eq_of_radial_ne_zero hK h1
  obtain ⟨b, hb, hbu⟩ := exists_edist_eq_of_radial_ne_zero hK h2
  have h3 : G.edist v₀ v₁ ≤ G.edist v₀ v + G.edist v u + G.edist u v₁ :=
    G.edist_triangle.trans (add_le_add_left G.edist_triangle _)
  have h4 : G.edist v₀ v₁ ≤ (a : ℕ∞) + 1 + b := by
    rw [edist_comm (u := u), hbu, hav] at h3
    exact h3.trans (by gcongr)
  have h5 : ((2 * K : ℕ) : ℕ∞) ≤ ((a + 1 + b : ℕ) : ℕ∞) := by
    refine hfar.trans ?_
    push_cast
    exact h4
  have h6 : 2 * K ≤ a + 1 + b := by exact_mod_cast h5
  omega

end Radial

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {d : ℕ}

/-- **Two radial functions around vertices at distance at least `2K` give a lower bound on
`λ₂`.** If `g` is a nonnegative, nonincreasing profile, positive at `0`, vanishing from `K` on,
with `μ g(0) ≤ d g(1)` and `μ g(i + 1) ≤ g(i) + (d − 1) g(i + 2)`, and `G` is `d`-regular with
two vertices at distance at least `2K`, then `μ ≤ λ₂`.

This is `SimpleGraph.AlonBoppana.le_secondAdjEigenvalue_of_lt_edist` with the distance
hypothesis `dist(v₀, v₁) ≥ 2K` in place of `> 2K`. The hypotheses force `K ≥ 1` (from
`0 < g 0`), so `v₀ ≠ v₁`; unreachable pairs (`edist = ⊤`) are allowed. -/
theorem le_secondAdjEigenvalue_of_le_edist [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {v₀ v₁ : V} {g : ℕ → ℝ} {μ : ℝ} {K : ℕ}
    (hanti : Antitone g) (hnn : ∀ i, 0 ≤ g i) (hpos : 0 < g 0) (hK : ∀ i, K ≤ i → g i = 0)
    (h0 : μ * g 0 ≤ d * g 1)
    (hstep : ∀ i, μ * g (i + 1) ≤ g i + ((d : ℝ) - 1) * g (i + 2))
    (hfar : ((2 * K : ℕ) : ℕ∞) ≤ G.edist v₀ v₁) :
    μ ≤ G.secondAdjEigenvalue := by
  have hfar' : ((2 * K : ℕ) : ℕ∞) ≤ G.edist v₁ v₀ := by rwa [edist_comm]
  have hR₁ := mul_radial_dotProduct_le hd v₀ hanti hnn h0 hstep
  have hR₂ := mul_radial_dotProduct_le hd v₁ hanti hnn h0 hstep
  generalize hF₁ : radial G v₀ g = F₁ at hR₁
  generalize hF₂ : radial G v₁ g = F₂ at hR₂
  have hF₂nn : ∀ v, 0 ≤ F₂ v := fun v => hF₂ ▸ radial_nonneg hnn v₁ v
  have hF₁v₀ : F₁ v₀ = g 0 := hF₁ ▸ radial_self v₀ g
  have hF₂v₁ : F₂ v₁ = g 0 := hF₂ ▸ radial_self v₁ g
  -- the cross terms vanish
  have h12 : F₁ ⬝ᵥ F₂ = 0 := by
    subst hF₁ hF₂
    simp only [dotProduct]
    exact Finset.sum_eq_zero fun v _ => radial_mul_radial_eq_zero_of_le_edist hK hfar (by simp)
  have h1A2 : F₁ ⬝ᵥ G.adjMatrix ℝ *ᵥ F₂ = 0 := by
    subst hF₁ hF₂
    simp only [dotProduct, adjMatrix_mulVec_apply, Finset.mul_sum]
    exact Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun u hu =>
      radial_mul_radial_eq_zero_of_le_edist hK hfar
        (edist_eq_one_iff_adj.mpr ((G.mem_neighborFinset v u).mp hu)).le
  have h2A1 : F₂ ⬝ᵥ G.adjMatrix ℝ *ᵥ F₁ = 0 := by
    subst hF₁ hF₂
    simp only [dotProduct, adjMatrix_mulVec_apply, Finset.mul_sum]
    exact Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun u hu =>
      radial_mul_radial_eq_zero_of_le_edist hK hfar'
        (edist_eq_one_iff_adj.mpr ((G.mem_neighborFinset v u).mp hu)).le
  -- positivity
  have hpos₁ : 0 < F₁ ⬝ᵥ F₁ := by
    refine Matrix.IsHermitian.dotProduct_self_pos fun h => ?_
    rw [h] at hF₁v₀
    exact hpos.ne hF₁v₀
  have hnn₂ : 0 ≤ F₂ ⬝ᵥ F₂ := Finset.sum_nonneg fun v _ => mul_self_nonneg (F₂ v)
  have ha : 0 < ∑ v, F₂ v :=
    lt_of_lt_of_le (hF₂v₁ ▸ hpos) (Finset.single_le_sum (fun v _ => hF₂nn v) (mem_univ v₁))
  generalize hadef : ∑ v, F₂ v = a at ha
  generalize hbdef : ∑ v, F₁ v = b
  -- the test vector `a F₁ - b F₂`, orthogonal to the constants
  have hx : ∑ v, (a • F₁ - b • F₂) v = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hadef, hbdef]
    ring
  have hxx : (a • F₁ - b • F₂) ⬝ᵥ (a • F₁ - b • F₂)
      = a ^ 2 * (F₁ ⬝ᵥ F₁) + b ^ 2 * (F₂ ⬝ᵥ F₂) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm F₂ F₁, h12]
    ring
  have hxAx : (a • F₁ - b • F₂) ⬝ᵥ G.adjMatrix ℝ *ᵥ (a • F₁ - b • F₂)
      = a ^ 2 * (F₁ ⬝ᵥ G.adjMatrix ℝ *ᵥ F₁) + b ^ 2 * (F₂ ⬝ᵥ G.adjMatrix ℝ *ᵥ F₂) := by
    simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, h1A2, h2A1]
    ring
  have hvar := dotProduct_adjMatrix_mulVec_le hd hx
  rw [hxx, hxAx] at hvar
  have hxxpos : 0 < a ^ 2 * (F₁ ⬝ᵥ F₁) + b ^ 2 * (F₂ ⬝ᵥ F₂) := by positivity
  refine le_of_mul_le_mul_right ?_ hxxpos
  nlinarith [mul_le_mul_of_nonneg_left hR₁ (sq_nonneg a),
    mul_le_mul_of_nonneg_left hR₂ (sq_nonneg b)]

end TwoCentres

end AlonBoppana

/-! ## Quantitative Alon–Boppana -/

section Quantitative

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {d : ℕ}

/-- **Quantitative Alon–Boppana bound.** If `G` is `d`-regular and has two vertices at distance
at least `2k`, with `k ≥ 1`, then `λ₂ ≥ 2√(d − 1) cos(π / (k + 1))`. Since
`cos x ≥ 1 − x²/2`, this gives `λ₂ ≥ 2√(d − 1) − π² √(d − 1) / (k + 1)²`
(`sub_le_secondAdjEigenvalue_of_le_edist`), the sharp `O(1/k²)` rate.

Distances are `SimpleGraph.edist`, so the vertices may lie in different components
(`edist = ⊤`). The hypothesis `k ≥ 1` is necessary: for `k = 0` the distance hypothesis is
empty and the claim `λ₂ ≥ −2√(d − 1)` fails for `K₂` (`d = 1`, `λ₂ = −1`). Distance `2k − 1`
does not suffice (`K₄` at `k = 1`, the cube `Q₃` at `k = 2`), and `K₃,₃` at `k = 1` is an
equality case. For `d = 0` and `d = 1` the term `√(d − 1)` is `0` in Lean (`√(−1) = 0` and
`√0 = 0`), so the theorem says only `0 ≤ λ₂`. -/
theorem cos_le_secondAdjEigenvalue_of_le_edist [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {k : ℕ} (hk : 1 ≤ k) {v₀ v₁ : V} (hfar : ((2 * k : ℕ) : ℕ∞) ≤ G.edist v₀ v₁) :
    2 * √((d : ℝ) - 1) * Real.cos (π / (k + 1)) ≤ G.secondAdjEigenvalue := by
  obtain ⟨g, hanti, hnn, hpos, hK, h0, hstep⟩ := AlonBoppana.exists_profile_cos d hk
  exact AlonBoppana.le_secondAdjEigenvalue_of_le_edist hd hanti hnn hpos hK h0 hstep hfar

/-- **Quantitative Alon–Boppana bound, strict form.** If `G` is `d`-regular and has two vertices
at distance more than `2k`, with `k ≥ 1`, then `λ₂ ≥ 2√(d − 1) cos(π / (k + 1))`. This follows
from `cos_le_secondAdjEigenvalue_of_le_edist`, which needs only distance at least `2k`.

The hypothesis `k ≥ 1` is necessary: for `k = 0`, `K₂` (`d = 1`, distance `1 > 0`,
`λ₂ = −1 < 0`) is a counterexample. For `d = 0` and `d = 1` the term `√(d − 1)` is `0` in Lean,
so the theorem says only `0 ≤ λ₂`. -/
theorem cos_le_secondAdjEigenvalue_of_lt_edist [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {k : ℕ} (hk : 1 ≤ k) {v₀ v₁ : V} (hfar : ((2 * k : ℕ) : ℕ∞) < G.edist v₀ v₁) :
    2 * √((d : ℝ) - 1) * Real.cos (π / (k + 1)) ≤ G.secondAdjEigenvalue :=
  cos_le_secondAdjEigenvalue_of_le_edist hd hk hfar.le

/-- **Quantitative Alon–Boppana bound from the diameter.** A `d`-regular graph of (extended)
diameter at least `2k`, with `k ≥ 1`, has `λ₂ ≥ 2√(d − 1) cos(π / (k + 1))`. This is Friedman's
setting, with an exact constant in place of `1 − π²/(2k²) + O(k⁻⁴)`.

The diameter is `SimpleGraph.ediam`, which is `⊤` for a disconnected graph, so every
disconnected `d`-regular graph satisfies the hypothesis for every `k`. The hypothesis `k ≥ 1` is
necessary (`K₂`, `d = 1`, `λ₂ = −1`), and for `d = 0` and `d = 1` the theorem says only
`0 ≤ λ₂` (`√(d − 1) = 0` in Lean). -/
theorem cos_le_secondAdjEigenvalue_of_le_ediam [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {k : ℕ} (hk : 1 ≤ k) (hdiam : ((2 * k : ℕ) : ℕ∞) ≤ G.ediam) :
    2 * √((d : ℝ) - 1) * Real.cos (π / (k + 1)) ≤ G.secondAdjEigenvalue := by
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_ediam_of_finite
  exact cos_le_secondAdjEigenvalue_of_le_edist hd hk (v₀ := u) (v₁ := v) (huv ▸ hdiam)

/-- In a `d`-regular graph on more than `(d + 1) ^ (2k − 1)` vertices, with `k ≥ 1`, some two
vertices are at distance at least `2k`: a ball of radius `2k − 1` has at most
`(d + 1) ^ (2k − 1)` vertices. (`2k − 1` is natural-number subtraction, exact for `k ≥ 1`.) -/
private theorem exists_le_edist_of_pow_lt_card (hd : G.IsRegularOfDegree d) (v₀ : V) {k : ℕ}
    (hk : 1 ≤ k) (hn : (d + 1) ^ (2 * k - 1) < Fintype.card V) :
    ∃ v₁, ((2 * k : ℕ) : ℕ∞) ≤ G.edist v₀ v₁ := by
  obtain ⟨v₁, hfar⟩ := AlonBoppana.exists_lt_edist hd v₀ hn
  refine ⟨v₁, ?_⟩
  have e : ((2 * k : ℕ) : ℕ∞) = ((2 * k - 1 : ℕ) : ℕ∞) + 1 := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel (by omega)]
  rw [e]
  exact Order.add_one_le_of_lt hfar

/-- **Quantitative Alon–Boppana bound for large graphs.** A `d`-regular graph on more than
`(d + 1) ^ (2k − 1)` vertices, with `k ≥ 1`, has `λ₂ ≥ 2√(d − 1) cos(π / (k + 1))`.

Here `2k − 1` is natural-number subtraction, which is exact because `k ≥ 1`. The hypothesis
`k ≥ 1` is necessary: for `k = 0` the exponent is `2 · 0 − 1 = 0` in `ℕ`, so the size
hypothesis reads `1 < |V|`, and `K₂` (`d = 1`, `λ₂ = −1`) is a counterexample. For `d = 0` and
`d = 1` the term `√(d − 1)` is `0` in Lean, so the theorem says only `0 ≤ λ₂`. -/
theorem cos_le_secondAdjEigenvalue_of_pow_lt_card [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {k : ℕ} (hk : 1 ≤ k) (hn : (d + 1) ^ (2 * k - 1) < Fintype.card V) :
    2 * √((d : ℝ) - 1) * Real.cos (π / (k + 1)) ≤ G.secondAdjEigenvalue := by
  obtain ⟨v₀⟩ : Nonempty V := inferInstance
  obtain ⟨v₁, hfar⟩ := exists_le_edist_of_pow_lt_card hd v₀ hk hn
  exact cos_le_secondAdjEigenvalue_of_le_edist hd hk hfar

/-- From `cos x ≥ 1 − x²/2`: if `π² √(d − 1) ≤ ε (k + 1)²` then
`2√(d − 1) − ε ≤ 2√(d − 1) cos(π / (k + 1))`. -/
private theorem sub_le_two_mul_sqrt_mul_cos {k : ℕ} {ε : ℝ}
    (hε : π ^ 2 * √((d : ℝ) - 1) ≤ ε * (k + 1) ^ 2) :
    2 * √((d : ℝ) - 1) - ε ≤ 2 * √((d : ℝ) - 1) * Real.cos (π / (k + 1)) := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := π / (k + 1))
  have hs0 : 0 ≤ √((d : ℝ) - 1) := Real.sqrt_nonneg _
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [div_pow] at hc
  have h1 : √((d : ℝ) - 1) * (π ^ 2 / ((k : ℝ) + 1) ^ 2) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hc hs0]

/-- **Alon–Boppana with explicit accuracy, from two far-apart vertices.** If `G` is `d`-regular
and has two vertices at distance at least `2k`, with `k ≥ 1`, and `π² √(d − 1) ≤ ε (k + 1)²`,
then `λ₂ ≥ 2√(d − 1) − ε`. So accuracy `ε` needs only `k + 1 ≥ π (d − 1)^{1/4} / √ε`.

The hypothesis on `ε` forces `ε ≥ 0`, and `ε > 0` when `d ≥ 2`. The hypothesis `k ≥ 1` is
necessary (`K₂`, `d = 1`, `λ₂ = −1`, with any `0 ≤ ε < 1`). For `d = 0` and `d = 1` the term
`√(d − 1)` is `0` in Lean, so the theorem says only `−ε ≤ λ₂`. -/
theorem sub_le_secondAdjEigenvalue_of_le_edist [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : π ^ 2 * √((d : ℝ) - 1) ≤ ε * (k + 1) ^ 2) {v₀ v₁ : V}
    (hfar : ((2 * k : ℕ) : ℕ∞) ≤ G.edist v₀ v₁) :
    2 * √((d : ℝ) - 1) - ε ≤ G.secondAdjEigenvalue :=
  (sub_le_two_mul_sqrt_mul_cos hε).trans (cos_le_secondAdjEigenvalue_of_le_edist hd hk hfar)

/-- **Alon–Boppana with explicit accuracy, for large graphs.** A `d`-regular graph on more than
`(d + 1) ^ (2k − 1)` vertices, with `k ≥ 1` and `π² √(d − 1) ≤ ε (k + 1)²`, has
`λ₂ ≥ 2√(d − 1) − ε`.

Here `2k − 1` is natural-number subtraction, exact because `k ≥ 1`. The hypothesis `k ≥ 1` is
necessary (`K₂`, `d = 1`, `λ₂ = −1`, with any `0 ≤ ε < 1`). For `d = 0` and `d = 1` the term
`√(d − 1)` is `0` in Lean, so the theorem says only `−ε ≤ λ₂`. -/
theorem sub_le_secondAdjEigenvalue_of_pow_lt_card [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : π ^ 2 * √((d : ℝ) - 1) ≤ ε * (k + 1) ^ 2)
    (hn : (d + 1) ^ (2 * k - 1) < Fintype.card V) :
    2 * √((d : ℝ) - 1) - ε ≤ G.secondAdjEigenvalue :=
  (sub_le_two_mul_sqrt_mul_cos hε).trans (cos_le_secondAdjEigenvalue_of_pow_lt_card hd hk hn)

end Quantitative

/-! ## The explicit threshold `N(d, ε)` -/

section Explicit

/-- The radius for accuracy `ε` in the explicit Alon–Boppana bound:
`k = max(1, ⌈π √(√(d − 1) / ε)⌉₊ − 1)`, that is, `k = max(1, ⌈π (d − 1)^{1/4} ε^{−1/2}⌉ − 1)`
for `ε > 0` (reading `(d − 1)^{1/4}` as `0` for `d ≤ 1`). It satisfies `k ≥ 1`
(`one_le_alonBoppanaRadius`), and for `ε > 0` it is the least `k ≥ 1` with
`π² √(d − 1) ≤ ε (k + 1)²` (`pi_sq_mul_sqrt_le_mul_alonBoppanaRadius`, `alonBoppanaRadius_le`).

Junk values: the definition is meant for `ε > 0`. For `ε ≤ 0` the quotient `√(d − 1) / ε` is
`≤ 0` (it is `0` for `ε = 0`, as `x / 0 = 0` in Lean), its square root is `0`, and the radius is
`1`. For `d = 0` and `d = 1` the term `√(d − 1)` is `0` and the radius is again `1`. The
subtraction `⌈·⌉₊ − 1` is natural-number subtraction, which truncates `0 − 1` to `0`; the outer
`max 1` overrides that case. -/
noncomputable def alonBoppanaRadius (d : ℕ) (ε : ℝ) : ℕ :=
  max 1 (⌈π * √(√((d : ℝ) - 1) / ε)⌉₊ - 1)

/-- The explicit threshold `N(d, ε) = (d + 1) ^ (2k − 1) + 1` with `k = alonBoppanaRadius d ε`:
every `d`-regular graph on at least `N(d, ε)` vertices has `λ₂ ≥ 2√(d − 1) − ε`, for `ε > 0`
(`alon_boppana_explicit`). Since `k ≈ π (d − 1)^{1/4} ε^{−1/2}`, this is
`N(d, ε) = (d + 1) ^ O(d^{1/4} ε^{−1/2})`.

The subtraction `2k − 1` is natural-number subtraction, exact because `k ≥ 1`. For `d ≤ 1` the
radius is `1` and the threshold is `d + 2`; for `ε ≤ 0` the radius is the junk value `1` (see
`alonBoppanaRadius`) and the threshold is again `d + 2`. -/
noncomputable def alonBoppanaCard (d : ℕ) (ε : ℝ) : ℕ :=
  (d + 1) ^ (2 * alonBoppanaRadius d ε - 1) + 1

/-- The radius `alonBoppanaRadius d ε` is at least `1`, for every `d` and `ε`. -/
theorem one_le_alonBoppanaRadius (d : ℕ) (ε : ℝ) : 1 ≤ alonBoppanaRadius d ε :=
  le_max_left _ _

/-- For `ε > 0` the radius `k = alonBoppanaRadius d ε` is large enough for accuracy `ε`:
`π² √(d − 1) ≤ ε (k + 1)²`. (For `d ≤ 1` the left side is `π² · 0 = 0` in Lean.) -/
theorem pi_sq_mul_sqrt_le_mul_alonBoppanaRadius (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    π ^ 2 * √((d : ℝ) - 1) ≤ ε * ((alonBoppanaRadius d ε : ℝ) + 1) ^ 2 := by
  set x : ℝ := π * √(√((d : ℝ) - 1) / ε) with hx_def
  have hx0 : 0 ≤ x := mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg _)
  have hq : 0 ≤ √((d : ℝ) - 1) / ε := div_nonneg (Real.sqrt_nonneg _) hε.le
  have hceil : ⌈x⌉₊ ≤ alonBoppanaRadius d ε + 1 := by
    have : ⌈x⌉₊ - 1 ≤ alonBoppanaRadius d ε := le_max_right _ _
    omega
  have hxk : x ≤ (alonBoppanaRadius d ε : ℝ) + 1 :=
    (Nat.le_ceil x).trans (by exact_mod_cast hceil)
  have hx2 : x ^ 2 = π ^ 2 * (√((d : ℝ) - 1) / ε) := by
    rw [hx_def, mul_pow, Real.sq_sqrt hq]
  have hsq : x ^ 2 ≤ ((alonBoppanaRadius d ε : ℝ) + 1) ^ 2 := pow_le_pow_left₀ hx0 hxk 2
  have e : π ^ 2 * √((d : ℝ) - 1) = ε * x ^ 2 := by
    rw [hx2]
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hsq hε.le

/-- `alonBoppanaRadius d ε` is the least admissible radius: for `ε > 0`, every `k ≥ 1` with
`π² √(d − 1) ≤ ε (k + 1)²` is at least `alonBoppanaRadius d ε`. -/
theorem alonBoppanaRadius_le {d : ℕ} {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k)
    (h : π ^ 2 * √((d : ℝ) - 1) ≤ ε * ((k : ℝ) + 1) ^ 2) : alonBoppanaRadius d ε ≤ k := by
  set x : ℝ := π * √(√((d : ℝ) - 1) / ε) with hx_def
  have hq : 0 ≤ √((d : ℝ) - 1) / ε := div_nonneg (Real.sqrt_nonneg _) hε.le
  have hx2 : x ^ 2 = π ^ 2 * (√((d : ℝ) - 1) / ε) := by
    rw [hx_def, mul_pow, Real.sq_sqrt hq]
  have hsq : x ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := by
    rw [hx2, mul_div_assoc', div_le_iff₀ hε]
    linarith
  have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hxk : x ≤ ((k + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hceil : ⌈x⌉₊ ≤ k + 1 := Nat.ceil_le.mpr hxk
  exact max_le hk (Nat.sub_le_iff_le_add.mpr hceil)

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {d : ℕ}

/-- **Explicit Alon–Boppana bound.** For `ε > 0`, every `d`-regular graph on at least
`alonBoppanaCard d ε = (d + 1) ^ (2k − 1) + 1` vertices, where
`k = max(1, ⌈π (d − 1)^{1/4} ε^{−1/2}⌉ − 1)`, has `λ₂ ≥ 2√(d − 1) − ε`. This makes the
threshold `N` of `SimpleGraph.alon_boppana` explicit.

The hypothesis `ε > 0` cannot be dropped: for `ε ≤ 0` the radius is the junk value `1` and the
threshold is `d + 2` (see `alonBoppanaRadius`), and the Petersen graph (`d = 3`, `10` vertices,
`λ₂ = 1 < 2√2`) violates the conclusion. For `d = 0` and `d = 1` the term `√(d − 1)` is `0` in
Lean, so the theorem says only `−ε ≤ λ₂`; it has content for `d ≥ 2`. -/
theorem alon_boppana_explicit [Nontrivial V] (hd : G.IsRegularOfDegree d) {ε : ℝ} (hε : 0 < ε)
    (hn : alonBoppanaCard d ε ≤ Fintype.card V) :
    2 * √((d : ℝ) - 1) - ε ≤ G.secondAdjEigenvalue :=
  sub_le_secondAdjEigenvalue_of_pow_lt_card hd (one_le_alonBoppanaRadius d ε)
    (pi_sq_mul_sqrt_le_mul_alonBoppanaRadius d hε)
    (Nat.lt_of_succ_le (by unfold alonBoppanaCard at hn; exact hn))

end Explicit

end SimpleGraph
