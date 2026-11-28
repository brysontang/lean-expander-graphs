/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.WeightedGraph

/-!
# Edge-average trickling down, part 1: the Bochner inequality of one link

This file is about a single weighted graph `T : ι → ι → ℝ` (symmetric, nonnegative, no loops),
with `d b = Σ_c T b c`. In the application `T` is the link of a vertex `z` of a pure complex,
`T b c` the weight of the triangle `{z, b, c}`, and functions of an edge `b c` of `T` are functions
of the triangles through `z`.

For an edge function `h` (symmetric) let `a b = Σ_c T b c h b c / d b` be its average around `b`,
and put
* `S = Σ_{b,c} T b c · h b c²`,
* `A = Σ_b d b · a b²`,
* `B = Σ_{b,c} T b c · a b · a c`.

The **Bochner inequality of the link** (`local_bochner`) says: if the random walk on `T` has
second eigenvalue at most `lam`, then
`(2 + 2 lam) S − (4 + 2 lam) A + 2 B ≥ 0`.

In operator language (Chen–Liu, arXiv:2609.19514, Proposition 2.3): with `L_z` the sum of the
projections `I − Q_τ` over the edges `τ ∋ z`, acting on functions of the triangles through `z`, it
is `‖L_z h‖² ≥ (1 − lam) ⟨h, L_z h⟩`, i.e. `L_z² ⪰ (1 − lam) L_z`. Indeed
`‖L_z h‖² = 4S − 6A + 2B` and `⟨h, L_z h⟩ = 2S − 2A` (sums over ordered pairs).

## Proof (no spectral theorem)

After shifting `h` by a constant we may assume `Σ_b d b · a b = 0`. Let `p = P a` be the walk
applied to `a`. Three applications of the hypotheses suffice:
* the link bound on `a`: `B ≤ lam · A`;
* the link bound on `lam · a − p` (again of mean zero): a cubic moment inequality;
* `Σ T (K h − f b − f c)² ≥ 0` with `K = 2 + 2 lam` and `f = (2 + lam) a − p`, the least-squares
  comparison of `h` with a lifted vertex function.

The moments `C = Σ d p²` and `E = Σ T p p` enter, and the identity
`2 (1 + lam) Φ = X + 4 (1 − lam) H₁ + 2 H₂ + 2 (3 − lam) H₀`
(`X`, `H₁`, `H₂`, `H₀` the four nonnegative quantities) proves `Φ ≥ 0` for `−1 < lam ≤ 1`. The
case `lam > 1` is trivial, the case `lam = −1` follows by letting `lam ↓ −1`, and `lam < −1` only
occurs for a graph with no edges (`neg_one_le_of_walkSecondEigenvalueLE`).

## Theorems
* `sum_sum_mul_add_sq`, `sum_sum_mul_sub_sub_sq`: expansions of `Σ T (f b + f c)²` and
  `Σ T (K h − f b − f c)²`. **Proved.**
* `neg_one_le_of_walkSecondEigenvalueLE`: a weighted graph with an edge between distinct
  vertices has second eigenvalue at least `−1`. **Proved.**
* `local_bochner_of_sum_eq_zero`: the inequality for `−1 < lam ≤ 1` and `a` of mean zero.
  **Proved.**
* `local_bochner`: the inequality in general. **Proved.**
-/

open Finset

namespace EdgeAverageTricklingDown

variable {ι : Type*} [Fintype ι]

/-- `Σ_x Σ_y w x y (f x + f y)² = 2 Σ_x deg x · f x² + 2 Σ_x Σ_y w x y f x f y` for symmetric
`w`. -/
theorem sum_sum_mul_add_sq {w : ι → ι → ℝ} (hsymm : ∀ u v, w u v = w v u) (f : ι → ℝ) :
    ∑ x, ∑ y, w x y * (f x + f y) ^ 2 =
      2 * ∑ x, (∑ y, w x y) * f x ^ 2 + 2 * ∑ x, ∑ y, w x y * f x * f y := by
  have e : ∀ x y, w x y * (f x + f y) ^ 2 =
      w x y * f x ^ 2 + w x y * f y ^ 2 + 2 * (w x y * f x * f y) := fun x y => by ring
  have a1 : ∑ x, ∑ y, w x y * f x ^ 2 = ∑ x, (∑ y, w x y) * f x ^ 2 :=
    Finset.sum_congr rfl fun x _ => (Finset.sum_mul _ _ _).symm
  have a2 : ∑ x, ∑ y, w x y * f y ^ 2 = ∑ x, (∑ y, w x y) * f x ^ 2 := by
    rw [Finset.sum_comm, ← a1]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [hsymm y x]
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, a1, a2]
  ring

/-- **Expansion of the least-squares comparison.** For symmetric `T` and symmetric `h`,
`Σ T (K h − f b − f c)² = K² Σ T h² − 4 K Σ_b f b Σ_c T b c h b c + 2 Σ d f² + 2 Σ T f f`. -/
theorem sum_sum_mul_sub_sub_sq {T : ι → ι → ℝ} (hsymm : ∀ b c, T b c = T c b)
    (h : ι → ι → ℝ) (hh : ∀ b c, h b c = h c b) (K : ℝ) (f : ι → ℝ) :
    ∑ b, ∑ c, T b c * (K * h b c - f b - f c) ^ 2 =
      K ^ 2 * ∑ b, ∑ c, T b c * h b c ^ 2 - 4 * K * ∑ b, f b * ∑ c, T b c * h b c
        + 2 * ∑ b, (∑ c, T b c) * f b ^ 2 + 2 * ∑ b, ∑ c, T b c * f b * f c := by
  have e : ∀ b c, T b c * (K * h b c - f b - f c) ^ 2 =
      K ^ 2 * (T b c * h b c ^ 2) - 2 * K * (T b c * h b c * f b)
        - 2 * K * (T b c * h b c * f c) + T b c * f b ^ 2 + T b c * f c ^ 2
        + 2 * (T b c * f b * f c) := fun b c => by ring
  have s1 : ∑ b, ∑ c, T b c * h b c * f b = ∑ b, f b * ∑ c, T b c * h b c := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  have s2 : ∑ b, ∑ c, T b c * h b c * f c = ∑ b, f b * ∑ c, T b c * h b c := by
    rw [Finset.sum_comm, ← s1]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by
      rw [hsymm c b, hh c b]
  have s3 : ∑ b, ∑ c, T b c * f b ^ 2 = ∑ b, (∑ c, T b c) * f b ^ 2 :=
    Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm
  have s4 : ∑ b, ∑ c, T b c * f c ^ 2 = ∑ b, (∑ c, T b c) * f b ^ 2 := by
    rw [Finset.sum_comm, ← s3]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [hsymm c b]
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, s1, s2, s3, s4]
  ring

/-- **An edge forces `lam ≥ −1`.** If the weighted graph `w` has an edge of positive weight
between distinct vertices, every `lam` with `WalkSecondEigenvalueLE w lam` is at least `−1`. Test
on `deg v · 1_u − deg u · 1_v`, and use `Σ w (f x + f y)² ≥ 0`.

Without an edge between distinct vertices the conclusion can fail: the graph with no edges, or a
single vertex with a loop, satisfies the bound for every `lam`. -/
theorem neg_one_le_of_walkSecondEigenvalueLE {w : ι → ι → ℝ} (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) {lam : ℝ} (h : WalkSecondEigenvalueLE w lam) {u v : ι}
    (huv : u ≠ v) (hpos : 0 < w u v) : -1 ≤ lam := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, a = ∑ x, w u x := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ∑ x, w v x := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [ha]
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun x _ => hnn u x) (Finset.mem_univ v))
  have hb0 : 0 < b := by
    rw [hb]
    have hvu : 0 < w v u := by rw [hsymm]; exact hpos
    exact lt_of_lt_of_le hvu (Finset.single_le_sum (fun x _ => hnn v x) (Finset.mem_univ u))
  obtain ⟨f, hf⟩ : ∃ f : ι → ℝ, f = fun x => if x = u then b else if x = v then -a else 0 :=
    ⟨_, rfl⟩
  have hfu : f u = b := by rw [hf]; exact if_pos rfl
  have hfv : f v = -a := by rw [hf]; simp [huv.symm]
  have hf0 : ∀ x, x ≠ u ∧ x ≠ v → f x = 0 := fun x hx => by rw [hf]; simp [hx.1, hx.2]
  have hmean : ∑ x, (∑ y, w x y) * f x = 0 := by
    rw [Finset.sum_eq_add_of_mem u v (Finset.mem_univ _) (Finset.mem_univ _) huv
      fun x _ hx => by rw [hf0 x hx, mul_zero], hfu, hfv, ← ha, ← hb]
    ring
  have hnorm : ∑ x, (∑ y, w x y) * f x ^ 2 = a * b ^ 2 + b * a ^ 2 := by
    rw [Finset.sum_eq_add_of_mem u v (Finset.mem_univ _) (Finset.mem_univ _) huv
      fun x _ hx => by rw [hf0 x hx]; ring, hfu, hfv, ← ha, ← hb]
    ring
  have h1 := h f hmean
  have h2 := sum_sum_mul_add_sq hsymm f
  have h3 : 0 ≤ ∑ x, ∑ y, w x y * (f x + f y) ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (hnn x y) (sq_nonneg _)
  rw [hnorm] at h1 h2
  have hN : 0 < a * b ^ 2 + b * a ^ 2 := by positivity
  by_contra hlt
  push Not at hlt
  nlinarith [mul_pos (by linarith : (0 : ℝ) < -1 - lam) hN]

/-- **The Bochner inequality of a link, mean-zero case.** Let `T` be symmetric and nonnegative,
with random-walk second eigenvalue at most `lam`, `−1 < lam ≤ 1`. Let `h` be a symmetric function
of the edges, and `a` its average around each vertex (`Σ_c T b c h b c = a b · d b`), of
degree-weighted mean zero. Then `(2 + 2 lam) S − (4 + 2 lam) A + 2 B ≥ 0`.

The mean-zero condition is removed in `local_bochner` (the left side does not change when a
constant is subtracted from `h` and `a`). A vertex `b` of degree `0` is unconstrained by the
hypothesis on `a`, and contributes nothing. -/
theorem local_bochner_of_sum_eq_zero {T : ι → ι → ℝ} (hsymm : ∀ b c, T b c = T c b)
    (hnn : ∀ b c, 0 ≤ T b c) {lam : ℝ} (hlam : WalkSecondEigenvalueLE T lam) (hl1 : -1 < lam)
    (hl2 : lam ≤ 1) (h : ι → ι → ℝ) (hh : ∀ b c, h b c = h c b) (a : ι → ℝ)
    (ha : ∀ b, ∑ c, T b c * h b c = a b * ∑ c, T b c)
    (hmean : ∑ b, (∑ c, T b c) * a b = 0) :
    0 ≤ (2 + 2 * lam) * ∑ b, ∑ c, T b c * h b c ^ 2
      - (4 + 2 * lam) * ∑ b, (∑ c, T b c) * a b ^ 2 + 2 * ∑ b, ∑ c, T b c * a b * a c := by
  -- `p = P a`, the walk applied to `a`
  obtain ⟨p, hp⟩ : ∃ p : ι → ℝ, ∀ b, ∑ c, T b c * a c = p b * ∑ c, T b c := by
    refine ⟨fun b => (∑ c, T b c * a c) / ∑ c, T b c, fun b => ?_⟩
    rcases (Finset.sum_nonneg fun c _ => hnn b c : (0 : ℝ) ≤ ∑ c, T b c).eq_or_lt with h0 | h0
    · have hT0 : ∀ c, T b c = 0 := fun c =>
        (Finset.sum_eq_zero_iff_of_nonneg fun c _ => hnn b c).mp h0.symm c (Finset.mem_univ c)
      simp [hT0]
    · exact (div_mul_cancel₀ _ h0.ne').symm
  -- bilinear bookkeeping
  have I1 : ∀ x y : ι → ℝ, ∑ b, ∑ c, T b c * x b * y c = ∑ b, x b * ∑ c, T b c * y c := by
    intro x y
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  have I2 : ∀ x y : ι → ℝ, ∑ b, ∑ c, T b c * x b * y c = ∑ b, ∑ c, T b c * y b * x c := by
    intro x y
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [hsymm c b]; ring
  -- the five moments
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ b, ∑ c, T b c * h b c ^ 2 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ b, (∑ c, T b c) * a b ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ b, ∑ c, T b c * a b * a c := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = ∑ b, (∑ c, T b c) * p b ^ 2 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = ∑ b, ∑ c, T b c * p b * p c := ⟨_, rfl⟩
  rw [← hS, ← hA, ← hB]
  -- mixed moments
  have hap : ∑ b, (∑ c, T b c) * a b * p b = B := by
    rw [hB, I1]
    exact Finset.sum_congr rfl fun b _ => by rw [hp b]; ring
  have hTap : ∑ b, ∑ c, T b c * a b * p c = C := by
    rw [I2, I1, hC]
    exact Finset.sum_congr rfl fun b _ => by rw [hp b]; ring
  have hTpa : ∑ b, ∑ c, T b c * p b * a c = C := by
    rw [I2]; exact hTap
  have hpmean : ∑ b, (∑ c, T b c) * p b = 0 := by
    calc ∑ b, (∑ c, T b c) * p b = ∑ b, ∑ c, T b c * a c :=
          Finset.sum_congr rfl fun b _ => by rw [hp b]; ring
      _ = ∑ c, (∑ b, T c b) * a c := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ => by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun b _ => by rw [hsymm]
      _ = 0 := hmean
  -- `H₁`: the link bound on `a`
  have H1 : B ≤ lam * A := by
    rw [hB, hA]; exact hlam a hmean
  -- `H₂`: the link bound on `lam · a − p`, which again has mean zero
  have hu2mean : ∑ b, (∑ c, T b c) * (lam * a b - p b) = 0 := by
    have e : ∑ b, (∑ c, T b c) * (lam * a b - p b) =
        lam * ∑ b, (∑ c, T b c) * a b - ∑ b, (∑ c, T b c) * p b := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e, hmean, hpmean]; ring
  have H2 : ∑ b, ∑ c, T b c * (lam * a b - p b) * (lam * a c - p c) ≤
      lam * ∑ b, (∑ c, T b c) * (lam * a b - p b) ^ 2 :=
    hlam (fun b => lam * a b - p b) hu2mean
  have e1 : ∑ b, ∑ c, T b c * (lam * a b - p b) * (lam * a c - p c) =
      lam ^ 2 * B - 2 * lam * C + E := by
    have : ∀ b c, T b c * (lam * a b - p b) * (lam * a c - p c) =
        lam ^ 2 * (T b c * a b * a c) - lam * (T b c * a b * p c) - lam * (T b c * p b * a c)
          + T b c * p b * p c := fun b c => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← hB, hTap, hTpa, ← hE]
    ring
  have e2 : ∑ b, (∑ c, T b c) * (lam * a b - p b) ^ 2 = lam ^ 2 * A - 2 * lam * B + C := by
    have : ∀ b, (∑ c, T b c) * (lam * a b - p b) ^ 2 =
        lam ^ 2 * ((∑ c, T b c) * a b ^ 2) - 2 * lam * ((∑ c, T b c) * a b * p b)
          + (∑ c, T b c) * p b ^ 2 := fun b => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← hA, hap, ← hC]
  have H0 : 0 ≤ ∑ b, (∑ c, T b c) * (lam * a b - p b) ^ 2 :=
    Finset.sum_nonneg fun b _ =>
      mul_nonneg (Finset.sum_nonneg fun c _ => hnn b c) (sq_nonneg _)
  rw [e1, e2] at H2
  rw [e2] at H0
  -- `X`: the least-squares comparison of `h` with the lift of `f = (2 + lam) a − p`
  have hX : 0 ≤ ∑ b, ∑ c, T b c *
      ((2 + 2 * lam) * h b c - ((2 + lam) * a b - p b) - ((2 + lam) * a c - p c)) ^ 2 :=
    Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => mul_nonneg (hnn b c) (sq_nonneg _)
  rw [sum_sum_mul_sub_sub_sq hsymm h hh (2 + 2 * lam) (fun b => (2 + lam) * a b - p b)] at hX
  have F1 : ∑ b, ((2 + lam) * a b - p b) * ∑ c, T b c * h b c = (2 + lam) * A - B := by
    have : ∀ b, ((2 + lam) * a b - p b) * ∑ c, T b c * h b c =
        (2 + lam) * ((∑ c, T b c) * a b ^ 2) - (∑ c, T b c) * a b * p b := fun b => by
      rw [ha b]; ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← hA, hap]
  have F2 : ∑ b, (∑ c, T b c) * ((2 + lam) * a b - p b) ^ 2 =
      (2 + lam) ^ 2 * A - 2 * (2 + lam) * B + C := by
    have : ∀ b, (∑ c, T b c) * ((2 + lam) * a b - p b) ^ 2 =
        (2 + lam) ^ 2 * ((∑ c, T b c) * a b ^ 2) - 2 * (2 + lam) * ((∑ c, T b c) * a b * p b)
          + (∑ c, T b c) * p b ^ 2 := fun b => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← hA, hap, ← hC]
  have F3 : ∑ b, ∑ c, T b c * ((2 + lam) * a b - p b) * ((2 + lam) * a c - p c) =
      (2 + lam) ^ 2 * B - 2 * (2 + lam) * C + E := by
    have : ∀ b c, T b c * ((2 + lam) * a b - p b) * ((2 + lam) * a c - p c) =
        (2 + lam) ^ 2 * (T b c * a b * a c) - (2 + lam) * (T b c * a b * p c)
          - (2 + lam) * (T b c * p b * a c) + T b c * p b * p c := fun b c => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← hB, hTap, hTpa, ← hE]
    ring
  rw [← hS, F1, F2, F3] at hX
  -- the certificate
  have key : 2 * (1 + lam) * ((2 + 2 * lam) * S - (4 + 2 * lam) * A + 2 * B) =
      ((2 + 2 * lam) ^ 2 * S - 4 * (2 + 2 * lam) * ((2 + lam) * A - B)
          + 2 * ((2 + lam) ^ 2 * A - 2 * (2 + lam) * B + C)
          + 2 * ((2 + lam) ^ 2 * B - 2 * (2 + lam) * C + E))
        + 4 * ((1 - lam) * (lam * A - B))
        + 2 * (lam * (lam ^ 2 * A - 2 * lam * B + C) - (lam ^ 2 * B - 2 * lam * C + E))
        + 2 * ((3 - lam) * (lam ^ 2 * A - 2 * lam * B + C)) := by ring
  have k1 : 0 ≤ (1 - lam) * (lam * A - B) := mul_nonneg (by linarith) (by linarith)
  have k3 : 0 ≤ (3 - lam) * (lam ^ 2 * A - 2 * lam * B + C) := mul_nonneg (by linarith) H0
  have hpos : 0 < 2 * (1 + lam) := by linarith
  have hprod : 0 ≤ 2 * (1 + lam) * ((2 + 2 * lam) * S - (4 + 2 * lam) * A + 2 * B) := by
    rw [key]; linarith
  exact (mul_nonneg_iff_of_pos_left hpos).mp hprod

/-- **The Bochner inequality of a link** (Chen–Liu, arXiv:2609.19514, Proposition 2.3, in the
form `L_z² ⪰ (1 − lam) L_z`). Let `T` be a symmetric nonnegative weighted graph without loops
whose random walk has second eigenvalue at most `lam`. For every symmetric edge function `h`, with
`a` its average around each vertex (`Σ_c T b c h b c = a b · d b`),
`(2 + 2 lam) Σ T h² − (4 + 2 lam) Σ d a² + 2 Σ T a a ≥ 0`.

No hypothesis on `lam` and no connectivity is needed:
* `T` with no edges: every sum is `0`.
* `lam > 1`: the left side is `Σ T (2h − a b − a c)² + 2 (lam − 1) Σ T (h − a b)²`.
* `lam < −1` cannot occur once `T` has an edge (`neg_one_le_of_walkSecondEigenvalueLE`).
* `lam = −1`: limit of the case `−1 < lam ≤ 1`.
* A disconnected `T` forces `lam ≥ 1` (a function constant on components), so it is covered by
  the case `lam ≥ 1`.

The value of `a` at a vertex of degree `0` is irrelevant. -/
theorem local_bochner {T : ι → ι → ℝ} (hsymm : ∀ b c, T b c = T c b) (hnn : ∀ b c, 0 ≤ T b c)
    (hloop : ∀ b, T b b = 0) {lam : ℝ} (hlam : WalkSecondEigenvalueLE T lam)
    (h : ι → ι → ℝ) (hh : ∀ b c, h b c = h c b) (a : ι → ℝ)
    (ha : ∀ b, ∑ c, T b c * h b c = a b * ∑ c, T b c) :
    0 ≤ (2 + 2 * lam) * ∑ b, ∑ c, T b c * h b c ^ 2
      - (4 + 2 * lam) * ∑ b, (∑ c, T b c) * a b ^ 2 + 2 * ∑ b, ∑ c, T b c * a b * a c := by
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ b, ∑ c, T b c * h b c ^ 2 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ b, (∑ c, T b c) * a b ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ b, ∑ c, T b c * a b * a c := ⟨_, rfl⟩
  rw [← hS, ← hA, ← hB]
  have hha : ∑ b, a b * ∑ c, T b c * h b c = A := by
    rw [hA]; exact Finset.sum_congr rfl fun b _ => by rw [ha b]; ring
  -- `S − A = Σ T (h − a b)² ≥ 0`
  have J1 : 0 ≤ S - A := by
    have e : ∑ b, ∑ c, T b c * (h b c - a b) ^ 2 = S - A := by
      have : ∀ b c, T b c * (h b c - a b) ^ 2 =
          T b c * h b c ^ 2 - 2 * (a b * (T b c * h b c)) + T b c * a b ^ 2 := fun b c => by ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have s : ∑ b, ∑ c, T b c * a b ^ 2 = A := by
        rw [hA]; exact Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm
      rw [← hS, hha, s]
      ring
    rw [← e]
    exact Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ =>
      mul_nonneg (hnn b c) (sq_nonneg _)
  -- `4S − 6A + 2B = Σ T (2h − a b − a c)² ≥ 0`
  have J2 : 0 ≤ 4 * S - 6 * A + 2 * B := by
    have e := sum_sum_mul_sub_sub_sq hsymm h hh 2 a
    rw [← hS, hha, ← hA, ← hB] at e
    have : 0 ≤ ∑ b, ∑ c, T b c * (2 * h b c - a b - a c) ^ 2 :=
      Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ =>
        mul_nonneg (hnn b c) (sq_nonneg _)
    linarith
  -- no edges: everything vanishes
  by_cases hex : ∃ u v, u ≠ v ∧ 0 < T u v
  swap
  · have hT0 : ∀ u v, T u v = 0 := by
      intro u v
      by_cases huv : u = v
      · rw [huv, hloop]
      · exact le_antisymm (not_lt.mp fun hlt => hex ⟨u, v, huv, hlt⟩) (hnn u v)
    simp [hS, hA, hB, hT0]
  obtain ⟨u, v, huv, hpos⟩ := hex
  have hl1 := neg_one_le_of_walkSecondEigenvalueLE hsymm hnn hlam huv hpos
  -- the total weight is positive
  obtain ⟨D, hD⟩ : ∃ D, D = ∑ b, ∑ c, T b c := ⟨_, rfl⟩
  have hD0 : 0 < D := by
    rw [hD]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun b _ =>
      Finset.sum_nonneg fun c _ => hnn b c) (Finset.mem_univ u))
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun c _ => hnn u c) (Finset.mem_univ v))
  obtain ⟨M, hM⟩ : ∃ M, M = ∑ b, (∑ c, T b c) * a b := ⟨_, rfl⟩
  -- the case `−1 < lam' ≤ 1`, by shifting to mean zero
  have good : ∀ lam' : ℝ, -1 < lam' → lam' ≤ 1 → WalkSecondEigenvalueLE T lam' →
      0 ≤ (2 + 2 * lam') * S - (4 + 2 * lam') * A + 2 * B := by
    intro lam' h1 h2 hlam'
    obtain ⟨κ, hκ⟩ : ∃ κ, κ = M / D := ⟨_, rfl⟩
    have ha' : ∀ b, ∑ c, T b c * (h b c - κ) = (a b - κ) * ∑ c, T b c := by
      intro b
      have : ∑ c, T b c * (h b c - κ) = ∑ c, T b c * h b c - κ * ∑ c, T b c := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c _ => by ring
      rw [this, ha b]; ring
    have hmean' : ∑ b, (∑ c, T b c) * (a b - κ) = 0 := by
      have : ∑ b, (∑ c, T b c) * (a b - κ) = M - κ * D := by
        rw [hM, hD, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [this, hκ, div_mul_cancel₀ _ hD0.ne', sub_self]
    have hh' : ∀ b c, h b c - κ = h c b - κ := fun b c => by rw [hh b c]
    have key := local_bochner_of_sum_eq_zero hsymm hnn hlam' h1 h2 (fun b c => h b c - κ) hh'
      (fun b => a b - κ) ha' hmean'
    -- the left side is unchanged by the shift
    have hTh : ∑ b, ∑ c, T b c * h b c = M := by
      rw [hM]; exact Finset.sum_congr rfl fun b _ => by rw [ha b]; ring
    have hTa1 : ∑ b, ∑ c, T b c * a b = M := by
      rw [hM]; exact Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm
    have hTa2 : ∑ b, ∑ c, T b c * a c = M := by
      rw [Finset.sum_comm, ← hTa1]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [hsymm c b]
    have eS : ∑ b, ∑ c, T b c * (h b c - κ) ^ 2 = S - 2 * κ * M + κ ^ 2 * D := by
      have : ∀ b c, T b c * (h b c - κ) ^ 2 =
          T b c * h b c ^ 2 - 2 * κ * (T b c * h b c) + κ ^ 2 * T b c := fun b c => by ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [← hS, hTh, ← hD]
    have eA : ∑ b, (∑ c, T b c) * (a b - κ) ^ 2 = A - 2 * κ * M + κ ^ 2 * D := by
      have : ∀ b, (∑ c, T b c) * (a b - κ) ^ 2 =
          (∑ c, T b c) * a b ^ 2 - 2 * κ * ((∑ c, T b c) * a b) + κ ^ 2 * ∑ c, T b c :=
        fun b => by ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [← hA, ← hM, ← hD]
    have eB : ∑ b, ∑ c, T b c * (a b - κ) * (a c - κ) = B - 2 * κ * M + κ ^ 2 * D := by
      have : ∀ b c, T b c * (a b - κ) * (a c - κ) =
          T b c * a b * a c - κ * (T b c * a b) - κ * (T b c * a c) + κ ^ 2 * T b c :=
        fun b c => by ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [← hB, hTa1, hTa2, ← hD]
      ring
    rw [eS, eA, eB] at key
    linarith
  rcases lt_or_ge 1 lam with hgt | hle
  · -- `lam > 1`
    have : 0 ≤ (lam - 1) * (S - A) := mul_nonneg (by linarith) J1
    linarith
  rcases hl1.lt_or_eq with hlt | heq
  · exact good lam hlt hle hlam
  · -- `lam = −1`: let `lam' ↓ −1`
    subst heq
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨t, ht⟩ : ∃ t, t = min 1 (ε / (2 * (S - A + 1))) := ⟨_, rfl⟩
    have hSA : 0 < 2 * (S - A + 1) := by linarith
    have ht0 : 0 < t := by rw [ht]; exact lt_min one_pos (div_pos hε hSA)
    have ht1 : t ≤ 1 := by rw [ht]; exact min_le_left _ _
    have ht2 : t * (2 * (S - A + 1)) ≤ ε := by
      have : t ≤ ε / (2 * (S - A + 1)) := by rw [ht]; exact min_le_right _ _
      rwa [le_div_iff₀ hSA] at this
    have hg := good (-1 + t) (by linarith) (by linarith) (hlam.mono hnn (by linarith))
    nlinarith

end EdgeAverageTricklingDown
