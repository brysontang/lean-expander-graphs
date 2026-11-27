/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.TricklingDownSpectral

/-!
# The variational second eigenvalue of a random walk is a genuine eigenvalue

`WalkSecondEigenvalueLE w lam` (in `Expanders.WeightedGraph`) defines "the random walk on the
weighted graph `w` has second eigenvalue at most `lam`" variationally. For `d`-regular graphs
`SimpleGraph.walkSecondEigenvalueLE_adjMatrix_iff` ties it to an adjacency eigenvalue. Here we do
the general case. For symmetric nonnegative weights with every degree `deg u = Σ_v w u v`
positive, the random walk `w u v / deg u` is similar to the symmetric matrix

  `N u v = w u v / (√(deg u) · √(deg v))`  (`walkMatrix w`),

and:

* `walkMatrix_isHermitian`: `N` is symmetric.
* `walkMatrix_mulVec_sqrt`: `N √deg = √deg`.
* `dotProduct_walkMatrix_mulVec_le`: `xᵀNx ≤ xᵀx` for every `x`.
* `walkMatrix_largestEigenvalue`: the largest eigenvalue of `N` is `1`.
* `walkSecondEigenvalueLE_iff_secondEigenvalue_le`: `WalkSecondEigenvalueLE w lam` holds exactly
  when the second-largest eigenvalue of `N` is at most `lam`.

The proofs use the change of variables `x u = √(deg u) · f u`, which turns the degree-weighted
quantities of the definition into plain dot products:
`Σ_u deg u · f u = x ⬝ √deg`, `Σ_{u,v} w u v f u f v = xᵀNx` and `Σ_u deg u · f u² = x ⬝ x`.
-/

open Finset Matrix

variable {ι : Type*} [Fintype ι]

/-- The **symmetrised random-walk matrix** of a weighted graph:
`N u v = w u v / (√(deg u) · √(deg v))` with `deg u = Σ_v w u v`.

The definition makes sense for any `w`, but it has its intended meaning only under assumptions.
If the weights are symmetric, `N` is symmetric (`walkMatrix_isHermitian`). If moreover every
degree is positive, `N = D^{1/2} P D^{-1/2}` is similar to the random-walk matrix
`P u v = w u v / deg u` (with `D` the diagonal degree matrix), so the two have the same
eigenvalues. For the eigenvalue interpretation (`P` a genuine random walk, with largest eigenvalue
`1`, `walkMatrix_largestEigenvalue`) the weights must also be nonnegative.

For a vertex `u` of degree zero the denominators in its row and column vanish, and those entries
are `x / 0 = 0` in Lean (with symmetric nonnegative weights they are `0 / 0`). The resulting
zero-extended matrix no longer describes the random walk: `u` contributes an eigenvalue `0`
(eigenvector the indicator of `u`), which can sit above the second eigenvalue of the walk on the
other vertices. This is why `walkSecondEigenvalueLE_iff_secondEigenvalue_le` assumes every degree
positive (compare the example in the docstring of `WalkSecondEigenvalueLE`). -/
noncomputable def walkMatrix (w : ι → ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun u v => w u v / (Real.sqrt (∑ x, w u x) * Real.sqrt (∑ x, w v x))

theorem walkMatrix_apply (w : ι → ι → ℝ) (u v : ι) :
    walkMatrix w u v = w u v / (Real.sqrt (∑ x, w u x) * Real.sqrt (∑ x, w v x)) :=
  rfl

theorem walkMatrix_isHermitian {w : ι → ι → ℝ} (hsymm : ∀ u v, w u v = w v u) :
    (walkMatrix w).IsHermitian := by
  ext u v
  simp only [conjTranspose_apply, walkMatrix_apply, star_trivial, hsymm v u, mul_comm]

section Degrees

variable {w : ι → ι → ℝ}

/-- Clearing the denominators of `walkMatrix`. -/
theorem walkMatrix_mul_sqrt_mul_sqrt (hdeg : ∀ u, 0 < ∑ v, w u v) (u v : ι) :
    walkMatrix w u v * (Real.sqrt (∑ x, w u x) * Real.sqrt (∑ x, w v x)) = w u v := by
  rw [walkMatrix_apply]
  exact div_mul_cancel₀ _
    (mul_ne_zero (Real.sqrt_pos.mpr (hdeg u)).ne' (Real.sqrt_pos.mpr (hdeg v)).ne')

/-- The vector `√deg` is fixed by the symmetrised walk matrix (it is the image of the constant
function `1`, which the random walk fixes). -/
theorem walkMatrix_mulVec_sqrt (hdeg : ∀ u, 0 < ∑ v, w u v) :
    walkMatrix w *ᵥ (fun u => Real.sqrt (∑ v, w u v)) = fun u => Real.sqrt (∑ v, w u v) := by
  ext u
  have hu := Real.sqrt_pos.mpr (hdeg u)
  have hterm : ∀ v, walkMatrix w u v * Real.sqrt (∑ x, w v x) =
      w u v / Real.sqrt (∑ x, w u x) := by
    intro v
    have hv := Real.sqrt_pos.mpr (hdeg v)
    rw [walkMatrix_apply, div_mul_eq_mul_div, mul_comm (Real.sqrt _) (Real.sqrt _), ← div_div,
      mul_div_assoc, div_self hv.ne', mul_one]
  simp only [mulVec, dotProduct, hterm, ← Finset.sum_div]
  rw [div_eq_iff hu.ne', Real.mul_self_sqrt (hdeg u).le]

theorem sqrt_deg_ne_zero [Nonempty ι] (hdeg : ∀ u, 0 < ∑ v, w u v) :
    (fun u => Real.sqrt (∑ v, w u v)) ≠ 0 := by
  intro h
  obtain ⟨u⟩ := ‹Nonempty ι›
  exact (Real.sqrt_pos.mpr (hdeg u)).ne' (congrFun h u)

/-! ### The change of variables `x = √deg · f` -/

theorem dotProduct_sqrt_deg_eq (hdeg : ∀ u, 0 < ∑ v, w u v) {x f : ι → ℝ}
    (hx : ∀ u, x u = Real.sqrt (∑ v, w u v) * f u) :
    x ⬝ᵥ (fun u => Real.sqrt (∑ v, w u v)) = ∑ u, (∑ v, w u v) * f u := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hx]
  linear_combination f u * Real.mul_self_sqrt (hdeg u).le

theorem dotProduct_self_eq_sum_deg (hdeg : ∀ u, 0 < ∑ v, w u v) {x f : ι → ℝ}
    (hx : ∀ u, x u = Real.sqrt (∑ v, w u v) * f u) :
    x ⬝ᵥ x = ∑ u, (∑ v, w u v) * f u ^ 2 := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hx]
  linear_combination f u ^ 2 * Real.mul_self_sqrt (hdeg u).le

theorem dotProduct_walkMatrix_mulVec_eq (hdeg : ∀ u, 0 < ∑ v, w u v) {x f : ι → ℝ}
    (hx : ∀ u, x u = Real.sqrt (∑ v, w u v) * f u) :
    x ⬝ᵥ walkMatrix w *ᵥ x = ∑ u, ∑ v, w u v * f u * f v := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [← walkMatrix_mul_sqrt_mul_sqrt hdeg u v, hx u, hx v]
  ring

/-- The degree-weighted quadratic form is dominated by the degree-weighted norm:
`Σ_{u,v} w u v f u f v ≤ Σ_u deg u · f u²`, because the difference is
`½ Σ_{u,v} w u v (f u − f v)² ≥ 0`. -/
theorem sum_mul_mul_le_sum_deg_mul_sq (hsymm : ∀ u v, w u v = w v u)
    (hnonneg : ∀ u v, 0 ≤ w u v) (f : ι → ℝ) :
    ∑ u, ∑ v, w u v * f u * f v ≤ ∑ u, (∑ v, w u v) * f u ^ 2 := by
  have e : ∀ u v, w u v * (f u - f v) ^ 2 =
      w u v * f u ^ 2 + w u v * f v ^ 2 - 2 * (w u v * f u * f v) := fun u v => by ring
  have a1 : ∑ u, ∑ v, w u v * f u ^ 2 = ∑ u, (∑ v, w u v) * f u ^ 2 :=
    Finset.sum_congr rfl fun u _ => (Finset.sum_mul _ _ _).symm
  have a2 : ∑ u, ∑ v, w u v * f v ^ 2 = ∑ u, (∑ v, w u v) * f u ^ 2 := by
    rw [Finset.sum_comm, ← a1]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hsymm v u]
  have h0 : 0 ≤ ∑ u, ∑ v, w u v * (f u - f v) ^ 2 :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (hnonneg u v) (sq_nonneg _)
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, a1, a2] at h0
  linarith

/-- The symmetrised walk matrix is a contraction on quadratic forms: `xᵀNx ≤ xᵀx`. -/
theorem dotProduct_walkMatrix_mulVec_le (hsymm : ∀ u v, w u v = w v u)
    (hnonneg : ∀ u v, 0 ≤ w u v) (hdeg : ∀ u, 0 < ∑ v, w u v) (x : ι → ℝ) :
    x ⬝ᵥ walkMatrix w *ᵥ x ≤ x ⬝ᵥ x := by
  have hx : ∀ u, x u = Real.sqrt (∑ v, w u v) * (x u / Real.sqrt (∑ v, w u v)) := fun u =>
    (mul_div_cancel₀ (x u) (Real.sqrt_pos.mpr (hdeg u)).ne').symm
  rw [dotProduct_walkMatrix_mulVec_eq hdeg hx, dotProduct_self_eq_sum_deg hdeg hx]
  exact sum_mul_mul_le_sum_deg_mul_sq hsymm hnonneg _

end Degrees

/-! ### The spectrum of the symmetrised walk matrix -/

variable [DecidableEq ι]

/-- The largest eigenvalue of the symmetrised walk matrix is `1`. -/
theorem walkMatrix_largestEigenvalue [Nonempty ι] {w : ι → ι → ℝ}
    (hsymm : ∀ u v, w u v = w v u) (hnonneg : ∀ u v, 0 ≤ w u v) (hdeg : ∀ u, 0 < ∑ v, w u v) :
    (walkMatrix_isHermitian hsymm).largestEigenvalue = 1 := by
  apply le_antisymm
  · obtain ⟨y, hy, hNy⟩ := (walkMatrix_isHermitian hsymm).exists_eigenvector_largest
    have h1 := dotProduct_walkMatrix_mulVec_le hsymm hnonneg hdeg y
    rw [hNy, dotProduct_smul, smul_eq_mul] at h1
    exact le_of_mul_le_mul_right (by rwa [one_mul])
      (Matrix.IsHermitian.dotProduct_self_pos hy)
  · refine (walkMatrix_isHermitian hsymm).le_largest_of_mulVec_eq (sqrt_deg_ne_zero hdeg) ?_
    rw [one_smul]
    exact walkMatrix_mulVec_sqrt hdeg

/-- **The variational definition is a genuine second eigenvalue.** For symmetric nonnegative
weights with every degree positive, `WalkSecondEigenvalueLE w lam` holds exactly when the
second-largest eigenvalue of the symmetrised random-walk matrix is at most `lam`. -/
theorem walkSecondEigenvalueLE_iff_secondEigenvalue_le [Nontrivial ι] {w : ι → ι → ℝ}
    (hsymm : ∀ u v, w u v = w v u) (hnonneg : ∀ u v, 0 ≤ w u v) (hdeg : ∀ u, 0 < ∑ v, w u v)
    {lam : ℝ} :
    WalkSecondEigenvalueLE w lam ↔ (walkMatrix_isHermitian hsymm).secondEigenvalue ≤ lam := by
  -- `√deg` is an eigenvector for the top eigenvalue `1`
  have hNs : walkMatrix w *ᵥ (fun u => Real.sqrt (∑ v, w u v)) =
      (walkMatrix_isHermitian hsymm).largestEigenvalue • fun u => Real.sqrt (∑ v, w u v) := by
    rw [walkMatrix_largestEigenvalue hsymm hnonneg hdeg, one_smul]
    exact walkMatrix_mulVec_sqrt hdeg
  constructor
  · -- test the variational bound on a vector `x ⟂ √deg` attaining `λ₂`
    intro h
    obtain ⟨x, hx0, hxs, hle⟩ :=
      (walkMatrix_isHermitian hsymm).exists_orthogonal_second_le
        (fun u => Real.sqrt (∑ v, w u v))
    have hx : ∀ u, x u = Real.sqrt (∑ v, w u v) * (x u / Real.sqrt (∑ v, w u v)) := fun u =>
      (mul_div_cancel₀ (x u) (Real.sqrt_pos.mpr (hdeg u)).ne').symm
    have h1 := h (fun u => x u / Real.sqrt (∑ v, w u v))
      ((dotProduct_sqrt_deg_eq hdeg hx).symm.trans hxs)
    rw [← dotProduct_walkMatrix_mulVec_eq hdeg hx, ← dotProduct_self_eq_sum_deg hdeg hx] at h1
    exact le_of_mul_le_mul_right (hle.trans h1) (Matrix.IsHermitian.dotProduct_self_pos hx0)
  · -- Courant–Fischer for `x = √deg · f`, which is orthogonal to `√deg`
    intro h f hf
    obtain ⟨x, hx⟩ : ∃ x : ι → ℝ, ∀ u, x u = Real.sqrt (∑ v, w u v) * f u :=
      ⟨_, fun _ => rfl⟩
    rw [← dotProduct_sqrt_deg_eq hdeg hx] at hf
    rw [← dotProduct_walkMatrix_mulVec_eq hdeg hx, ← dotProduct_self_eq_sum_deg hdeg hx]
    have h1 := (walkMatrix_isHermitian hsymm).dotProduct_mulVec_le_second
      (sqrt_deg_ne_zero hdeg) hNs hf
    have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
    exact h1.trans (mul_le_mul_of_nonneg_right h hxx)
