/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.WeightedGraph

/-!
# Weighted-graph groundwork for trickling down

Three facts about a weighted graph `w : ι → ι → ℝ` (symmetric, nonnegative), with
`deg u = Σ_v w u v`, none of which mentions simplicial complexes:

* `exists_walk_eigenfunction_of_lt`: if the Rayleigh quotient of `f` exceeds `γ`, the random walk
  has an eigenfunction `g` with eigenvalue `γ' > γ` that is not orthogonal to `f`. (The spectral
  theorem, applied to the symmetrised walk matrix `w u v / √(deg u · deg v)`.)
* `garland_inequality`: **Garland's method**. If `w` is an average of weighted graphs `wz z`
  ("vertex links"), the degree in `wz z` is proportional to `w z ·`, and every `wz z` has second
  eigenvalue at most `μ`, then `⟨Mf, f⟩ ≤ μ ⟨f, f⟩ + (1 − μ) ⟨Mf, Mf⟩`.
* `walkSecondEigenvalueLE_of_garland`: if that inequality holds with `μ < 1` and `w` is
  connected, then `w` has second eigenvalue at most `μ / (1 − μ)`.
-/

open Finset Matrix

variable {ι : Type*} [Fintype ι]

/-- **A large Rayleigh quotient is witnessed by an eigenfunction.** If
`Σ w u v f u f v > γ · Σ deg u · f u²`, then there is `g` with
`Σ_v w u v g v = γ' · deg u · g u` for all `u`, for some `γ' > γ`, and `g` is not orthogonal to
`f` in the degree-weighted inner product. -/
theorem exists_walk_eigenfunction_of_lt {w : ι → ι → ℝ}
    (hsymm : ∀ u v, w u v = w v u) (hnn : ∀ u v, 0 ≤ w u v) {f : ι → ℝ} {γ : ℝ}
    (hf : γ * ∑ u, (∑ v, w u v) * f u ^ 2 < ∑ u, ∑ v, w u v * f u * f v) :
    ∃ (g : ι → ℝ) (γ' : ℝ), γ < γ' ∧
      (∀ u, ∑ v, w u v * g v = γ' * (∑ v, w u v) * g u) ∧
      ∑ u, (∑ v, w u v) * g u * f u ≠ 0 := by
  classical
  have hD0 : ∀ u, 0 ≤ ∑ v, w u v := fun u => Finset.sum_nonneg fun v _ => hnn u v
  obtain ⟨r, hr⟩ : ∃ r : ι → ℝ, r = fun u => Real.sqrt (∑ v, w u v) := ⟨_, rfl⟩
  have hrr : ∀ u, r u * r u = ∑ v, w u v := fun u => by
    rw [hr]; exact Real.mul_self_sqrt (hD0 u)
  -- a vertex of degree zero has no incident weight
  have hrow : ∀ u, r u = 0 → ∀ v, w u v = 0 := by
    intro u hu v
    have hDu : ∑ v, w u v = 0 := by rw [← hrr u, hu, mul_zero]
    exact (Finset.sum_eq_zero_iff_of_nonneg fun v _ => hnn u v).mp hDu v (Finset.mem_univ v)
  -- the symmetrised walk matrix
  obtain ⟨N, hNdef⟩ : ∃ N : Matrix ι ι ℝ, ∀ u v, N u v = w u v / (r u * r v) :=
    ⟨Matrix.of fun u v => w u v / (r u * r v), fun _ _ => rfl⟩
  have hN : N.IsHermitian := by
    ext u v
    simp [Matrix.conjTranspose_apply, hNdef, hsymm v u, mul_comm]
  have hNw : ∀ u v, N u v * (r u * r v) = w u v := by
    intro u v
    by_cases hu : r u = 0
    · simp [hu, hrow u hu v]
    by_cases hv : r v = 0
    · simp [hv, hsymm u v, hrow v hv u]
    · rw [hNdef]; field_simp
  obtain ⟨x, hx⟩ : ∃ x : ι → ℝ, ∀ u, x u = r u * f u := ⟨fun u => r u * f u, fun _ => rfl⟩
  have hquad : x ⬝ᵥ N *ᵥ x = ∑ u, ∑ v, w u v * f u * f v := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [← hNw u v, hx, hx]; ring
  have hnorm : x ⬝ᵥ x = ∑ u, (∑ v, w u v) * f u ^ 2 := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← hrr u, hx]; ring
  have h1 := hN.dotProduct_mulVec_eq_sum x
  have h2 := hN.sum_sq_coeff x
  rw [hquad] at h1
  rw [hnorm] at h2
  -- some eigen-direction carries a Rayleigh quotient above `γ`
  obtain ⟨j, hj⟩ : ∃ j, γ * hN.coeff x j ^ 2 < hN.eigenvalues j * hN.coeff x j ^ 2 := by
    by_contra hcon
    push Not at hcon
    have h3 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hcon j
    rw [← Finset.mul_sum, h2, ← h1] at h3
    exact absurd hf (not_lt.mpr h3)
  have hc : hN.coeff x j ≠ 0 := by
    intro h0
    rw [h0] at hj
    simp at hj
  have hγ : γ < hN.eigenvalues j :=
    lt_of_mul_lt_mul_right hj (sq_nonneg _)
  have he : ∀ u, ∑ v, N u v * hN.eigvec j v = hN.eigenvalues j * hN.eigvec j u := by
    intro u
    have h := congrFun (hN.mulVec_eigvec j) u
    simpa [mulVec, dotProduct] using h
  refine ⟨fun u => hN.eigvec j u / r u, hN.eigenvalues j, hγ, ?_, ?_⟩
  · intro u
    by_cases hu : r u = 0
    · simp [hrow u hu]
    · have hterm : ∀ v, w u v * (hN.eigvec j v / r v) = r u * (N u v * hN.eigvec j v) := by
        intro v
        by_cases hv : r v = 0
        · simp [hNdef, hv]
        · rw [← hNw u v]; field_simp
      simp only [hterm, ← Finset.mul_sum, he u, ← hrr u]
      field_simp
  · have hsum : ∑ u, (∑ v, w u v) * (hN.eigvec j u / r u) * f u = hN.coeff x j := by
      unfold Matrix.IsHermitian.coeff
      simp only [dotProduct]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : r u = 0
      · have hDu : ∑ v, w u v = 0 := by rw [← hrr u, hu, mul_zero]
        simp [hx, hu, hDu]
      · rw [← hrr u, hx]; field_simp
    rw [hsum]
    exact hc

/-- **Garland's method.** Suppose the weighted graph `w` is `1/c` times the sum of the weighted
graphs `wz z` (`hloc₁`), the degree of `u` in `wz z` is `c · w z u` (`hloc₂`), and every `wz z`
has random-walk second eigenvalue at most `μ`. Then for every `f`, with `m z` the `w`-weighted
mean of `f` around `z` (that is, `m = M f` for the walk operator `M`),
`⟨M f, f⟩ ≤ μ ⟨f, f⟩ + (1 − μ) ⟨M f, M f⟩` in the degree-weighted inner product. -/
theorem garland_inequality {w : ι → ι → ℝ} {wz : ι → ι → ι → ℝ} {c μ : ℝ} (hc : 0 < c)
    (hsymm : ∀ u v, w u v = w v u) (hzsymm : ∀ z u v, wz z u v = wz z v u)
    (hloc₁ : ∀ u v, ∑ z, wz z u v = c * w u v)
    (hloc₂ : ∀ z u, ∑ v, wz z u v = c * w z u)
    (hlocal : ∀ z, WalkSecondEigenvalueLE (wz z) μ)
    (f m : ι → ℝ) (hm : ∀ z, ∑ u, w z u * f u = m z * ∑ u, w z u) :
    ∑ u, ∑ v, w u v * f u * f v ≤
      μ * ∑ u, (∑ v, w u v) * f u ^ 2 + (1 - μ) * ∑ z, (∑ v, w z v) * m z ^ 2 := by
  -- the local inequality at `z`, applied to `f − m z`
  have hz : ∀ z, ∑ u, ∑ v, wz z u v * f u * f v - c * ((∑ v, w z v) * m z ^ 2) ≤
      μ * (c * ∑ u, w z u * f u ^ 2 - c * ((∑ v, w z v) * m z ^ 2)) := by
    intro z
    have horth : ∑ u, (∑ v, wz z u v) * (f u - m z) = 0 := by
      simp only [hloc₂, mul_sub, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul]
      rw [hm z]; ring
    have h := hlocal z (fun u => f u - m z) horth
    -- the three moments of `wz z`
    have s1 : ∑ u, ∑ v, wz z u v * f u = c * (m z * ∑ u, w z u) := by
      rw [← hm z, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_mul, hloc₂]; ring
    have s2 : ∑ u, ∑ v, wz z u v * f v = c * (m z * ∑ u, w z u) := by
      rw [Finset.sum_comm, ← s1]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [hzsymm z v u]
    have s0 : ∑ u, ∑ v, wz z u v = c * ∑ u, w z u := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => hloc₂ z u
    have s3 : ∑ u, (∑ v, wz z u v) * f u ^ 2 = c * ∑ u, w z u * f u ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hloc₂]; ring
    have s4 : ∑ u, (∑ v, wz z u v) * f u = c * (m z * ∑ u, w z u) := by
      rw [← s1]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_mul _ _ _
    have s5 : ∑ u, (∑ v, wz z u v) = c * ∑ u, w z u := s0
    have lhs : ∑ u, ∑ v, wz z u v * (f u - m z) * (f v - m z) =
        ∑ u, ∑ v, wz z u v * f u * f v - c * ((∑ v, w z v) * m z ^ 2) := by
      have e : ∀ u v, wz z u v * (f u - m z) * (f v - m z) =
          wz z u v * f u * f v - m z * (wz z u v * f u) - m z * (wz z u v * f v)
            + m z ^ 2 * wz z u v := fun u v => by ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, s1, s2, s0]
      ring
    have rhs : ∑ u, (∑ v, wz z u v) * (f u - m z) ^ 2 =
        c * ∑ u, w z u * f u ^ 2 - c * ((∑ v, w z v) * m z ^ 2) := by
      have e : ∀ u, (∑ v, wz z u v) * (f u - m z) ^ 2 =
          (∑ v, wz z u v) * f u ^ 2 - 2 * m z * ((∑ v, wz z u v) * f u)
            + m z ^ 2 * (∑ v, wz z u v) := fun u => by ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, s3, s4, s5]
      ring
    rw [lhs, rhs] at h
    exact h
  -- sum over `z`
  have hsum := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) => hz z
  have t1 : ∑ z, ∑ u, ∑ v, wz z u v * f u * f v = c * ∑ u, ∑ v, w u v * f u * f v := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul, hloc₁]; ring
  have t2 : ∑ z, ∑ u, w z u * f u ^ 2 = ∑ u, (∑ v, w u v) * f u ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by rw [hsymm z u]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, t1, t2] at hsum
  have h3 : c * (∑ u, ∑ v, w u v * f u * f v) ≤
      c * (μ * ∑ u, (∑ v, w u v) * f u ^ 2 + (1 - μ) * ∑ z, (∑ v, w z v) * m z ^ 2) := by
    linarith
  exact le_of_mul_le_mul_left h3 hc

/-- **From Garland's inequality to the second eigenvalue.** Let `w` be a symmetric nonnegative
weighted graph which is connected (in the form: a function constant along every edge of positive
weight is constant on the vertices of positive degree). If
`⟨M f, f⟩ ≤ μ ⟨f, f⟩ + (1 − μ) ⟨M f, M f⟩` for all `f`, with `μ < 1`, then the random walk has
second eigenvalue at most `μ / (1 − μ)`: an eigenvalue `γ < 1` must satisfy
`(1 − γ)(μ − (1 − μ) γ) ≥ 0`. -/
theorem walkSecondEigenvalueLE_of_garland {w : ι → ι → ℝ}
    (hsymm : ∀ u v, w u v = w v u) (hnn : ∀ u v, 0 ≤ w u v) {μ : ℝ} (hμ : μ < 1)
    (hconn : ∀ g : ι → ℝ, (∀ u v, 0 < w u v → g u = g v) →
      ∀ u v, 0 < ∑ x, w u x → 0 < ∑ x, w v x → g u = g v)
    (hG : ∀ f m : ι → ℝ, (∀ z, ∑ u, w z u * f u = m z * ∑ u, w z u) →
      ∑ u, ∑ v, w u v * f u * f v ≤
        μ * ∑ u, (∑ v, w u v) * f u ^ 2 + (1 - μ) * ∑ z, (∑ v, w z v) * m z ^ 2) :
    WalkSecondEigenvalueLE w (μ / (1 - μ)) := by
  intro f hf
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨g, γ, hγ, heig, hgf⟩ := exists_walk_eigenfunction_of_lt hsymm hnn hcon
  have hD0 : ∀ u, 0 ≤ ∑ v, w u v := fun u => Finset.sum_nonneg fun v _ => hnn u v
  -- `g` has positive norm
  have hgg : 0 < ∑ u, (∑ v, w u v) * g u ^ 2 := by
    obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hgf
    have hDu : ∑ v, w u v ≠ 0 := fun h => hu (by rw [h]; ring)
    have hgu : g u ≠ 0 := fun h => hu (by rw [h]; ring)
    have hpos : 0 < (∑ v, w u v) * g u ^ 2 :=
      mul_pos (lt_of_le_of_ne (hD0 u) (Ne.symm hDu)) (by positivity)
    exact Finset.sum_pos' (fun v _ => mul_nonneg (hD0 v) (sq_nonneg _)) ⟨u, Finset.mem_univ u, hpos⟩
  -- the quadratic form on an eigenfunction
  have hQ : ∑ u, ∑ v, w u v * g u * g v = γ * ∑ u, (∑ v, w u v) * g u ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have h1 : ∑ v, w u v * g u * g v = g u * ∑ v, w u v * g v := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [h1, heig u]; ring
  -- `Σ w u v (g u − g v)² = 2 (1 − γ) ⟨g, g⟩`
  have hdiff : ∑ u, ∑ v, w u v * (g u - g v) ^ 2 =
      2 * (1 - γ) * ∑ u, (∑ v, w u v) * g u ^ 2 := by
    have e : ∀ u v, w u v * (g u - g v) ^ 2 =
        w u v * g u ^ 2 + w u v * g v ^ 2 - 2 * (w u v * g u * g v) := fun u v => by ring
    have a1 : ∑ u, ∑ v, w u v * g u ^ 2 = ∑ u, (∑ v, w u v) * g u ^ 2 :=
      Finset.sum_congr rfl fun u _ => (Finset.sum_mul _ _ _).symm
    have a2 : ∑ u, ∑ v, w u v * g v ^ 2 = ∑ u, (∑ v, w u v) * g u ^ 2 := by
      rw [Finset.sum_comm, ← a1]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hsymm v u]
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, a1, a2, hQ]
    ring
  have hγ1 : γ ≤ 1 := by
    have h0 : 0 ≤ ∑ u, ∑ v, w u v * (g u - g v) ^ 2 :=
      Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => mul_nonneg (hnn u v) (sq_nonneg _)
    rw [hdiff] at h0
    by_contra hlt
    rw [not_le] at hlt
    nlinarith
  rcases hγ1.eq_or_lt with hγeq | hγlt
  · -- `γ = 1`: `g` is harmonic, hence constant on the support, hence orthogonal to `f`.
    have hzero : ∑ u, ∑ v, w u v * (g u - g v) ^ 2 = 0 := by
      rw [hdiff, hγeq]; ring
    have hedge : ∀ u v, 0 < w u v → g u = g v := by
      intro u v huv
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun u _ =>
        Finset.sum_nonneg fun v _ => mul_nonneg (hnn u v) (sq_nonneg (g u - g v))).mp hzero u
        (Finset.mem_univ u)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun v _ =>
        mul_nonneg (hnn u v) (sq_nonneg (g u - g v))).mp h1 v (Finset.mem_univ v)
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h huv.ne'
      · exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)
    obtain ⟨u₀, -, hu₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hgf
    have hDu₀ : 0 < ∑ v, w u₀ v :=
      lt_of_le_of_ne (hD0 u₀) (Ne.symm fun h => hu₀ (by rw [h]; ring))
    refine hgf ?_
    have hconst : ∀ u, (∑ v, w u v) * g u * f u = g u₀ * ((∑ v, w u v) * f u) := by
      intro u
      rcases (hD0 u).eq_or_lt with h | h
      · rw [← h]; ring
      · rw [hconn g hedge u u₀ h hDu₀]; ring
    simp only [hconst, ← Finset.mul_sum, hf, mul_zero]
  · -- `γ < 1`: Garland's inequality on the eigenfunction gives a quadratic inequality for `γ`.
    have h := hG g (fun z => γ * g z) (fun z => by rw [heig z]; ring)
    have hm : ∑ z, (∑ v, w z v) * (γ * g z) ^ 2 = γ ^ 2 * ∑ u, (∑ v, w u v) * g u ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [hQ, hm] at h
    have h1 : γ ≤ μ + (1 - μ) * γ ^ 2 := by
      have h2 : γ * ∑ u, (∑ v, w u v) * g u ^ 2 ≤
          (μ + (1 - μ) * γ ^ 2) * ∑ u, (∑ v, w u v) * g u ^ 2 := by linarith
      exact le_of_mul_le_mul_right h2 hgg
    have h3 : 0 ≤ (1 - γ) * (μ - (1 - μ) * γ) := by nlinarith
    have h4 : 0 ≤ μ - (1 - μ) * γ := nonneg_of_mul_nonneg_right h3 (by linarith)
    have h5 : γ ≤ μ / (1 - μ) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    exact absurd hγ (not_lt.mpr h5)
