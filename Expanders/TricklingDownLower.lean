/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.CompleteComplex
import Expanders.WalkSpectrum

/-!
# Two-sided trickling down: lower bounds on the spectra of links

Oppenheim's trickling-down theorem (`PreAbstractSimplicialComplex.trickling_down_weighted`)
carries an *upper* bound on the second eigenvalue of the random walks on the links of the
`(d − 2)`-dimensional faces of a weighted complex down to every lower-dimensional link. This file
proves the companion statement for the *bottom* of the spectrum. If the random walk on the link of
every set with `d − 1` elements has all its eigenvalues at least `κ`, then the random walk on the
link of every set `σ` with at most `d − 1` elements has all its eigenvalues at least

  `κ / (1 − j κ)`,  `j = d − 1 − |σ|`,

which is the same Möbius map `x ↦ x / (1 − j x)` as on the upper side. Together the two sides are
Oppenheim's two-sided trickling down.

The lower side needs much less than the upper side. An upper bound on the *second* eigenvalue has
to exclude the trivial eigenvalue `1` of the constant functions, and connectivity of the links is
what makes that eigenvalue simple. A lower bound constrains *every* eigenvalue, the trivial one
included, so nothing is excluded and connectivity never enters. The complex-free form
`trickling_down_lower` assumes only that the weight `m` is nonnegative and vanishes off the sets
with `d + 1` elements. It needs no complex, purity, positivity on top faces or connectivity, and
no sign condition on `κ`.

## Definitions
* `WalkSmallestEigenvalueGE w κ`: every eigenvalue of the random walk on the weighted graph `w`
  is at least `κ`, stated variationally over all functions.
* `PreAbstractSimplicialComplex.IsTwoSidedLocalSpectralExpanderOf K d m κ lam`: `K`, weighted by
  `m`, is a `lam`-local-spectral expander, and the random walk on each link it tests (`K` itself
  and the links of the faces of dimension at most `d − 2`) has every eigenvalue at least `κ`. This
  bounds every tested link directly, unlike Oppenheim's Definition 1.2, which bounds only the
  links of the `(d − 2)`-dimensional faces; see the docstring.

## Theorems (all proved here)
Weighted graphs:
* `walkSmallestEigenvalueGE_iff_le_eigenvalues`: the variational definition is the spectral one.
  For symmetric weights with every degree positive, it holds exactly when every eigenvalue of the
  symmetrised random-walk matrix `walkMatrix w` is at least `κ`.
* `WalkSmallestEigenvalueGE.mono`, `walkSmallestEigenvalueGE_of_forall_eq_zero`: monotonicity in
  `κ`, and the degenerate edgeless case.
* `walkSmallestEigenvalueGE_neg_one`: every symmetric nonnegative weighted graph satisfies the
  bound with `κ = −1`.
* `WalkSmallestEigenvalueGE.eq_zero_of_pos`: a nonnegative graph without loops that satisfies the
  bound with some `κ > 0` has no edges. `WalkSmallestEigenvalueGE.lt_zero`: if such a graph has an
  edge, it satisfies the bound only for `κ < 0`. Neither needs symmetry.
* `garland_inequality_lower`: **Garland's method, lower form**. If every local graph has every
  walk eigenvalue at least `κ`, then `κ ⟨f, f⟩ + (1 − κ) ⟨Mf, Mf⟩ ≤ ⟨Mf, f⟩`.
* `walkSmallestEigenvalueGE_of_garland`: that inequality with `κ ≤ 1/2` bounds every walk
  eigenvalue below by `κ / (1 − κ)`. It needs no connectivity and no symmetry, and `κ ≤ 1/2` is
  sharp for graphs with loops.

Weighted complexes (namespace `PreAbstractSimplicialComplex`):
* `walkSmallestEigenvalueGE_linkWeightOf_step`: one step of lower trickling down, from the vertex
  links of `σ` to the link of `σ`, for every `κ`.
* `linkWeightOf_eq_zero_of_walkSmallestEigenvalueGE_pos`: a positive lower bound on the links of
  the sets with `d − 1` elements makes every link edgeless.
* `trickling_down_lower`: **lower trickling down**, complex-free, with no connectivity and no sign
  condition.
* `trickling_down_lower_weighted`: the same, assuming the local bound only on the faces of a
  complex.
* `trickling_down_two_sided`: **two-sided trickling down**, the conjunction with
  `trickling_down_weighted`.
* `isTwoSidedLocalSpectralExpanderOf_of_trickling_down`: the packaged form, which derives the
  definition from Oppenheim-type hypotheses.
* `IsTwoSidedLocalSpectralExpanderOf.mono`: monotonicity in both parameters.
* `IsTwoSidedLocalSpectralExpanderOf.lt_zero`: the lower parameter is negative.
  `IsLocalSpectralExpanderOf.isTwoSidedLocalSpectralExpanderOf_neg_one`: every local spectral
  expander is two-sided with lower parameter `−1`.

All triangles on five points (`complete (Fin 5) 2`):
* `walkSmallestEigenvalueGE_complete_fin5_two_link_singleton`,
  `not_walkSmallestEigenvalueGE_complete_fin5_two_link_singleton`: the vertex links `K₄` have
  every walk eigenvalue at least `−1/3`, and this is sharp.
* `complete_fin5_two_walkSmallestEigenvalueGE`, `not_complete_fin5_two_walkSmallestEigenvalueGE`:
  lower trickling down bounds the walk on the underlying graph `K₅` below by `−1/4`, and this is
  sharp. Together with the upper bound `complete_fin5_two_walkSecondEigenvalueLE`, every eigenvalue
  of that walk other than `1` is exactly `−1/4`.
* `isTwoSidedLocalSpectralExpanderOf_complete_fin5_two`: the complex is a two-sided local spectral
  expander with parameters `(−1/3, −1/4)`, so the definition is satisfiable.
  `isTwoSidedLocalSpectralExpanderOf_complete_fin5_two_iff`: these parameters are optimal. The
  definition holds exactly when `κ ≤ −1/3` and `−1/4 ≤ lam`. In particular it fails for
  `(−1/3, −1/3)`, the walk constants with which the complex meets Oppenheim's Definition 1.2.

A closing `example` checks that lower trickling down from the universal bound `κ = −1`
recovers `link_walk_lower_bound` for every set with at most `d − 1` elements.

## References
* I. Oppenheim, *Local spectral expansion approach to high dimensional expanders Part I: Descent
  of spectral gaps*, Discrete Comput. Geom. 59 (2018), arXiv:1709.04431. See Definition 1.2
  (two-sided local spectral expansion: every link connected, and spectral bounds only on the
  1-dimensional links, those of the `(n − 2)`-dimensional faces), Theorem 1.4, Lemma 4.1 and
  Corollary 4.2. In the Laplacian normalisation used there, the top of the spectrum descends by
  `x ↦ 2 − 1/x`. With `x = 1 − κ` this is the walk-normalised `κ ↦ κ / (1 − κ)` used here.
  Oppenheim assumes every link connected, and the proof of Lemma 4.1 invokes it for both
  inequalities. His argument for this side does not need it, though: projecting onto the
  constants removes no more than projecting onto the kernel, so the `κ` inequality survives.
* Y. Dikstein, *ECC and HDX II: Oppenheim's Trickling Down Theorem*, lecture notes, Simons
  Institute, https://simons.berkeley.edu/sites/default/files/docs/14119/ecctalkii.pdf. Theorem 1.4
  ("trickling down for negative eigenvalues") is the one-step statement, and its footnote 1 says
  that connectivity is not needed for it.
-/

open Finset

variable {ι : Type*} [Fintype ι]

/-! ### The smallest eigenvalue of a random walk -/

/-- The random walk on the weighted graph `w` (symmetric, nonnegative weights) has **every
eigenvalue at least `κ`**: for every `f`,
`κ · Σ_u deg(u) f(u)² ≤ Σ_{u,v} w(u,v) f(u) f(v)`, where `deg(u) = Σ_v w(u,v)`.

Unlike `WalkSecondEigenvalueLE`, the condition quantifies over *all* `f`, not only those with
degree-weighted mean zero. A lower bound constrains every eigenvalue, including the top eigenvalue
`1` of the constant functions, which satisfies it whenever `κ ≤ 1`. So nothing has to be
excluded, and no theorem about this notion needs connectivity.

For symmetric weights with every degree positive, the condition says exactly that every
eigenvalue of the symmetrised random-walk matrix `walkMatrix w` (which is similar to the random
walk) is at least `κ` (`walkSmallestEigenvalueGE_iff_le_eigenvalues`).

Degenerate cases:
* Vertices of degree zero are ignored. With symmetric nonnegative weights every weight at such a
  vertex is `0`, so it contributes to neither side, and the condition sees only the random walk on
  the vertices of positive degree. A graph with no edges satisfies the condition for every `κ`
  (`walkSmallestEigenvalueGE_of_forall_eq_zero`). This covers an empty vertex type, and a
  one-element one without a loop.
* Every symmetric nonnegative `w` satisfies it for `κ = −1` (`walkSmallestEigenvalueGE_neg_one`).
  A single edge, with walk eigenvalues `1` and `−1`, shows that `−1` cannot be improved in
  general.
* As soon as some vertex has positive degree, `κ > 1` fails (take `f = 1`). If moreover `w` has
  no loops, every `κ ≥ 0` fails, and for this symmetry is not needed: `κ > 0` by
  `WalkSmallestEigenvalueGE.eq_zero_of_pos`, and `κ = 0` by `WalkSmallestEigenvalueGE.lt_zero`.
  With loops, `κ` can be as large as `1`: the identity matrix has every walk eigenvalue equal to
  `1`.

The definition reads `w` as given. If the weights are negative or not symmetric it is still a
statement about the quadratic form, but no longer about a random walk; every theorem below states
the hypotheses it needs. -/
def WalkSmallestEigenvalueGE (w : ι → ι → ℝ) (κ : ℝ) : Prop :=
  ∀ f : ι → ℝ, κ * ∑ u, (∑ v, w u v) * f u ^ 2 ≤ ∑ u, ∑ v, w u v * f u * f v

/-- **The variational definition is a genuine bound on the eigenvalues.** For symmetric weights
with every degree positive, `WalkSmallestEigenvalueGE w κ` holds exactly when every eigenvalue of
the symmetrised random-walk matrix `N u v = w u v / (√(deg u) · √(deg v))` (`walkMatrix w`, which
is similar to the random walk `w u v / deg u`) is at least `κ`. This is the lower-side companion
of `walkSecondEigenvalueLE_iff_secondEigenvalue_le`.

The proof is the change of variables `x = √deg · f` of `Expanders.WalkSpectrum`, which turns the
two sides of the definition into `κ · xᵀx` and `xᵀNx`, followed by the expansion of `x` in an
orthonormal eigenbasis of `N`. Nonnegativity of the weights is not needed. Positive degrees are:
at a vertex of degree zero `walkMatrix` has a zero row and column, hence an eigenvalue `0`, which
the definition does not see. For example `w = diag(1, 0)` satisfies the definition with `κ = 1`,
but its `walkMatrix` has the eigenvalue `0`. -/
theorem walkSmallestEigenvalueGE_iff_le_eigenvalues [DecidableEq ι] {w : ι → ι → ℝ}
    (hsymm : ∀ u v, w u v = w v u) (hdeg : ∀ u, 0 < ∑ v, w u v) {κ : ℝ} :
    WalkSmallestEigenvalueGE w κ ↔ ∀ j, κ ≤ (walkMatrix_isHermitian hsymm).eigenvalues j := by
  constructor
  · -- test the definition on the `j`-th eigenvector, divided by `√deg`
    intro h j
    have hx : ∀ u, (walkMatrix_isHermitian hsymm).eigvec j u = Real.sqrt (∑ v, w u v) *
        ((walkMatrix_isHermitian hsymm).eigvec j u / Real.sqrt (∑ v, w u v)) := fun u =>
      (mul_div_cancel₀ _ (Real.sqrt_pos.mpr (hdeg u)).ne').symm
    have h1 := h fun u => (walkMatrix_isHermitian hsymm).eigvec j u / Real.sqrt (∑ v, w u v)
    rw [← dotProduct_walkMatrix_mulVec_eq hdeg hx, ← dotProduct_self_eq_sum_deg hdeg hx,
      Matrix.IsHermitian.mulVec_eigvec, dotProduct_smul, smul_eq_mul] at h1
    exact le_of_mul_le_mul_right h1
      (Matrix.IsHermitian.dotProduct_self_pos (Matrix.IsHermitian.eigvec_ne_zero _ j))
  · -- expand `x = √deg · f` in the eigenbasis
    intro h f
    obtain ⟨x, hx⟩ : ∃ x : ι → ℝ, ∀ u, x u = Real.sqrt (∑ v, w u v) * f u :=
      ⟨_, fun _ => rfl⟩
    rw [← dotProduct_walkMatrix_mulVec_eq hdeg hx, ← dotProduct_self_eq_sum_deg hdeg hx,
      (walkMatrix_isHermitian hsymm).dotProduct_mulVec_eq_sum,
      ← (walkMatrix_isHermitian hsymm).sum_sq_coeff, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h j) (sq_nonneg _)

/-- A lower bound `κ` implies every smaller lower bound, for nonnegative weights (which make the
degree-weighted norm nonnegative). -/
theorem WalkSmallestEigenvalueGE.mono {w : ι → ι → ℝ} {κ κ' : ℝ}
    (h : WalkSmallestEigenvalueGE w κ) (hw : ∀ u v, 0 ≤ w u v) (hle : κ' ≤ κ) :
    WalkSmallestEigenvalueGE w κ' := fun f =>
  (mul_le_mul_of_nonneg_right hle (Finset.sum_nonneg fun u _ =>
    mul_nonneg (Finset.sum_nonneg fun v _ => hw u v) (sq_nonneg _))).trans (h f)

/-- **Degenerate case: no edges.** If every weight is zero, both sides of the defining inequality
vanish, so the bound holds for every `κ`, whatever its sign or size. -/
theorem walkSmallestEigenvalueGE_of_forall_eq_zero {w : ι → ι → ℝ} (hw : ∀ u v, w u v = 0)
    (κ : ℝ) : WalkSmallestEigenvalueGE w κ := by
  intro f
  simp [hw]

/-- **The universal lower bound.** For symmetric nonnegative weights every eigenvalue of the
random walk is at least `−1`: expanding `Σ_{u,v} w(u,v) (f(u) + f(v))² ≥ 0` gives
`2 Σ_u deg(u) f(u)² + 2 Σ_{u,v} w(u,v) f(u) f(v) ≥ 0`. A single edge attains `−1`. -/
theorem walkSmallestEigenvalueGE_neg_one {w : ι → ι → ℝ} (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) : WalkSmallestEigenvalueGE w (-1) := by
  intro f
  have h0 : 0 ≤ ∑ u, ∑ v, w u v * (f u + f v) ^ 2 :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => mul_nonneg (hnn u v) (sq_nonneg _)
  have e : ∀ u v, w u v * (f u + f v) ^ 2 =
      w u v * f u ^ 2 + w u v * f v ^ 2 + 2 * (w u v * f u * f v) := fun u v => by ring
  have a1 : ∑ u, ∑ v, w u v * f u ^ 2 = ∑ u, (∑ v, w u v) * f u ^ 2 :=
    Finset.sum_congr rfl fun u _ => (Finset.sum_mul _ _ _).symm
  have a2 : ∑ u, ∑ v, w u v * f v ^ 2 = ∑ u, (∑ v, w u v) * f u ^ 2 := by
    rw [Finset.sum_comm, ← a1]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hsymm v u]
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, a1, a2] at h0
  linarith

/-- **A positive lower bound leaves no edges.** If `w` is nonnegative and has no loops
(`w u u = 0`), and every walk eigenvalue is at least some `κ > 0`, then every weight is `0`. The
indicator of `u` gives `κ · deg(u) ≤ w(u, u) = 0`.

Symmetry is not needed. The absence of loops is: the identity matrix satisfies the bound with
`κ = 1`. The weighted graphs of links have no loops (`linkWeightOf_self`). -/
theorem WalkSmallestEigenvalueGE.eq_zero_of_pos {w : ι → ι → ℝ} {κ : ℝ}
    (h : WalkSmallestEigenvalueGE w κ) (hκ : 0 < κ) (hnn : ∀ u v, 0 ≤ w u v)
    (hloop : ∀ u, w u u = 0) (u v : ι) : w u v = 0 := by
  classical
  have h1 := h fun x => if x = u then 1 else 0
  simp only [ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hloop] at h1
  have hdeg : ∑ x, w u x = 0 := by
    refine le_antisymm ?_ (Finset.sum_nonneg fun x _ => hnn u x)
    by_contra hc
    rw [not_le] at hc
    linarith [mul_pos hκ hc]
  exact (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hnn u x).mp hdeg v (Finset.mem_univ v)

/-- **An edge forces a negative eigenvalue.** If `w` is nonnegative and has no loops, and
`w u v > 0` for some `u, v`, then a lower bound `κ` on every walk eigenvalue must be negative.
The function that is `1` at `u`, `−1` at `v` and `0` elsewhere has quadratic form
`−(w(u, v) + w(v, u)) < 0`, while the left side `κ · Σ deg f²` would be nonnegative for `κ ≥ 0`.
(The hypotheses force `u ≠ v`. On paper, for symmetric weights, the walk matrix has zero diagonal
and hence trace zero.)

Symmetry is not needed, as in `WalkSmallestEigenvalueGE.eq_zero_of_pos`. -/
theorem WalkSmallestEigenvalueGE.lt_zero {w : ι → ι → ℝ} {κ : ℝ}
    (h : WalkSmallestEigenvalueGE w κ) (hnn : ∀ u v, 0 ≤ w u v)
    (hloop : ∀ u, w u u = 0) {u v : ι} (huv : 0 < w u v) : κ < 0 := by
  classical
  have h1 := h fun x => (if x = u then 1 else 0) - (if x = v then 1 else 0)
  have hN : 0 ≤ ∑ x, (∑ y, w x y) * ((if x = u then 1 else 0) - (if x = v then 1 else 0)) ^ 2 :=
    Finset.sum_nonneg fun x _ =>
      mul_nonneg (Finset.sum_nonneg fun y _ => hnn x y) (sq_nonneg _)
  simp [mul_sub, Finset.sum_sub_distrib, hloop] at h1
  by_contra hκ
  rw [not_lt] at hκ
  linarith [mul_nonneg hκ hN, hnn v u]

/-! ### Garland's method for lower bounds -/

/-- **Garland's method, lower form.** Suppose that, for some `c > 0`, the weighted graph `w` is
`1/c` times the sum of the weighted graphs `wz z` (`hloc₁`), that the degree of `u` in `wz z` is
`c · w z u` (`hloc₂`), and that every `wz z` has every walk eigenvalue at least `κ`. Let `m z` be
the `w`-weighted mean of `f` around `z`, so that `m = M f` for the walk operator `M`. Then
`κ ⟨f, f⟩ + (1 − κ) ⟨M f, M f⟩ ≤ ⟨M f, f⟩` in the degree-weighted inner product.

The hypothesis `hm` leaves `m z` arbitrary at a vertex `z` of degree zero; its term in
`⟨M f, M f⟩` vanishes. This mirrors `garland_inequality`, with the inequality reversed and with no
orthogonality to the constants. It needs no sign condition on `κ` and no nonnegativity of the
weights. -/
theorem garland_inequality_lower {w : ι → ι → ℝ} {wz : ι → ι → ι → ℝ} {c κ : ℝ} (hc : 0 < c)
    (hsymm : ∀ u v, w u v = w v u) (hzsymm : ∀ z u v, wz z u v = wz z v u)
    (hloc₁ : ∀ u v, ∑ z, wz z u v = c * w u v)
    (hloc₂ : ∀ z u, ∑ v, wz z u v = c * w z u)
    (hlocal : ∀ z, WalkSmallestEigenvalueGE (wz z) κ)
    (f m : ι → ℝ) (hm : ∀ z, ∑ u, w z u * f u = m z * ∑ u, w z u) :
    κ * ∑ u, (∑ v, w u v) * f u ^ 2 + (1 - κ) * ∑ z, (∑ v, w z v) * m z ^ 2 ≤
      ∑ u, ∑ v, w u v * f u * f v := by
  -- the local inequality at `z`, applied to `f − m z`
  have hz : ∀ z, κ * (c * ∑ u, w z u * f u ^ 2 - c * ((∑ v, w z v) * m z ^ 2)) ≤
      ∑ u, ∑ v, wz z u v * f u * f v - c * ((∑ v, w z v) * m z ^ 2) := by
    intro z
    have h := hlocal z (fun u => f u - m z)
    -- the moments of `wz z`
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
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, s3, s4, s0]
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
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, t1, t2] at hsum
  have h3 : c * (κ * ∑ u, (∑ v, w u v) * f u ^ 2 + (1 - κ) * ∑ z, (∑ v, w z v) * m z ^ 2) ≤
      c * (∑ u, ∑ v, w u v * f u * f v) := by
    linarith
  exact le_of_mul_le_mul_left h3 hc

/-- The algebra behind `walkSmallestEigenvalueGE_of_garland`. With `N = ⟨f, f⟩`,
`M = ⟨Mf, Mf⟩` and `Q = ⟨Mf, f⟩`, the two hypotheses give `((1 − κ) Q − κ N)(Q − N) ≤ 0`. -/
private theorem garland_lower_algebra {κ N M Q : ℝ} (hκ : κ ≤ 1 / 2) (hN : 0 ≤ N)
    (hCS : Q ^ 2 ≤ M * N) (hG : κ * N + (1 - κ) * M ≤ Q) : κ / (1 - κ) * N ≤ Q := by
  have h1 : 0 < 1 - κ := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ h1]
  have hprod : ((1 - κ) * Q - κ * N) * (Q - N) ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hCS h1.le, mul_le_mul_of_nonneg_right hG hN]
  by_contra hcon
  rw [not_le] at hcon
  have hQN : N ≤ Q := by
    by_contra h'
    rw [not_le] at h'
    nlinarith [mul_pos (show 0 < κ * N - (1 - κ) * Q by linarith) (sub_pos.mpr h')]
  nlinarith [mul_le_mul_of_nonneg_left hQN h1.le, mul_nonneg (show 0 ≤ 1 - 2 * κ by linarith) hN]

/-- **From the lower Garland inequality to a lower bound on every eigenvalue.** Let `w` have
nonnegative weights. Suppose `κ ⟨f, f⟩ + (1 − κ) ⟨M f, M f⟩ ≤ ⟨M f, f⟩` holds for all `f`, in the
form proved by `garland_inequality_lower`, with `κ ≤ 1/2`. Then every walk eigenvalue is at least
`κ / (1 − κ)`. The denominator is at least `1/2`, so there is no division by zero.

Neither connectivity nor symmetry is used. The proof applies the hypothesis to `m = M f` and
combines it with the Cauchy–Schwarz inequality `⟨M f, f⟩² ≤ ⟨M f, M f⟩ ⟨f, f⟩`. No eigenfunction
is needed.

The condition `κ ≤ 1/2` is sharp for weighted graphs with loops. If `w` is the identity, then
`M f = f` and the hypothesis holds for every `κ`, but the conclusion `κ / (1 − κ) ≤ 1` fails for
`1/2 < κ < 1`. The weighted graphs of links have no loops, and for them
`walkSmallestEigenvalueGE_linkWeightOf_step` needs no condition on `κ` at all. -/
theorem walkSmallestEigenvalueGE_of_garland {w : ι → ι → ℝ} (hnn : ∀ u v, 0 ≤ w u v) {κ : ℝ}
    (hκ : κ ≤ 1 / 2)
    (hG : ∀ f m : ι → ℝ, (∀ z, ∑ u, w z u * f u = m z * ∑ u, w z u) →
      κ * ∑ u, (∑ v, w u v) * f u ^ 2 + (1 - κ) * ∑ z, (∑ v, w z v) * m z ^ 2 ≤
        ∑ u, ∑ v, w u v * f u * f v) :
    WalkSmallestEigenvalueGE w (κ / (1 - κ)) := by
  intro f
  have hD0 : ∀ u, 0 ≤ ∑ v, w u v := fun u => Finset.sum_nonneg fun v _ => hnn u v
  -- the walk average of `f`
  obtain ⟨m, hm_def⟩ : ∃ m : ι → ℝ, m = fun z => (∑ u, w z u * f u) / ∑ u, w z u := ⟨_, rfl⟩
  have hm : ∀ z, ∑ u, w z u * f u = m z * ∑ u, w z u := by
    intro z
    rcases (hD0 z).eq_or_lt with h | h
    · have hz : ∀ u, w z u = 0 := fun u =>
        (Finset.sum_eq_zero_iff_of_nonneg fun v _ => hnn z v).mp h.symm u (Finset.mem_univ u)
      simp [hz]
    · rw [hm_def]
      exact (div_mul_cancel₀ _ h.ne').symm
  have hQ : ∑ u, ∑ v, w u v * f u * f v = ∑ z, (∑ v, w z v) * m z * f z := by
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [show (∑ v, w z v) * m z * f z = f z * (m z * ∑ v, w z v) by ring, ← hm z, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hCS : (∑ z, (∑ v, w z v) * m z * f z) ^ 2 ≤
      (∑ z, (∑ v, w z v) * m z ^ 2) * ∑ z, (∑ v, w z v) * f z ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun z _ => mul_nonneg (hD0 z) (sq_nonneg _))
      (fun z _ => mul_nonneg (hD0 z) (sq_nonneg _)) fun z _ => le_of_eq (by ring)
  rw [← hQ] at hCS
  exact garland_lower_algebra hκ
    (Finset.sum_nonneg fun z _ => mul_nonneg (hD0 z) (sq_nonneg _)) hCS (hG f m hm)

namespace PreAbstractSimplicialComplex

variable [DecidableEq ι] {m : Finset ι → ℝ} {d : ℕ}

/-! ### Lower trickling down, with no complex -/

/-- If every vertex link of `σ` is edgeless, so is the link of `σ`. -/
private theorem linkWeightOf_eq_zero_of_forall_insert (hcard : ∀ F, m F ≠ 0 → #F = d + 1)
    {σ : Finset ι} (hσ : #σ + 2 ≤ d)
    (h : ∀ z, z ∉ σ → ∀ u v, linkWeightOf m (insert z σ) u v = 0) (u v : ι) :
    linkWeightOf m σ u v = 0 := by
  have hc : (d : ℝ) - 1 - #σ ≠ 0 := by
    have h' : ((#σ + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hσ
    push_cast at h'
    exact ne_of_gt (by linarith)
  have h1 := sum_linkWeightOf_insert hcard σ u v
  rw [Finset.sum_eq_zero fun z _ => by
    split_ifs with hz
    · rfl
    · exact h z hz u v] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_left hc

/-- **A positive lower bound leaves no edges in any link.** Let `m ≥ 0` vanish off the sets with
`d + 1` elements. Suppose that, for some `κ > 0`, the link of every set with `d − 1` elements has
every walk eigenvalue at least `κ`. Then the link of every set with at most `d − 1` elements has
no edges.

Links have no loops, so each link of a set with `d − 1` elements is edgeless
(`WalkSmallestEigenvalueGE.eq_zero_of_pos`). The localisation identity `sum_linkWeightOf_insert`
then carries this down to every smaller set. For `d = 0` the conclusion is empty. For `d = 1` it
concerns only `σ = ∅` and follows directly from the hypothesis there. For a top weight of a
complex of dimension `d ≥ 1` the underlying graph has an edge
(`IsTopWeight.exists_linkWeightOf_pos`), so there the hypothesis never holds with `κ > 0`. -/
theorem linkWeightOf_eq_zero_of_walkSmallestEigenvalueGE_pos (hnn : ∀ F, 0 ≤ m F)
    (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {κ : ℝ} (hκ : 0 < κ)
    (hlocal : ∀ σ : Finset ι, #σ + 1 = d → WalkSmallestEigenvalueGE (linkWeightOf m σ) κ) :
    ∀ σ : Finset ι, #σ + 1 ≤ d → ∀ u v, linkWeightOf m σ u v = 0 := by
  have key : ∀ j : ℕ, ∀ σ : Finset ι, #σ + 1 + j = d → ∀ u v, linkWeightOf m σ u v = 0 := by
    intro j
    induction j with
    | zero =>
      intro σ hσ
      exact (hlocal σ (by omega)).eq_zero_of_pos hκ (linkWeightOf_nonneg hnn σ)
        (linkWeightOf_self m σ)
    | succ j ih =>
      intro σ hσ
      exact linkWeightOf_eq_zero_of_forall_insert hcard (by omega) fun z hz =>
        ih (insert z σ) (by rw [Finset.card_insert_of_notMem hz]; omega)
  intro σ hσ
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hσ
  exact key j σ hj.symm

/-- **One step of lower trickling down.** Let `m ≥ 0` vanish off the sets with `d + 1` elements,
and let `σ` have at most `d − 2` elements (`σ = ∅` is allowed). If, for every `z ∉ σ`, the link of
`σ ∪ {z}` has every walk eigenvalue at least `κ`, then the link of `σ` has every walk eigenvalue
at least `κ / (1 − κ)`.

There is no complex, no purity, no connectivity and no sign condition on `κ`. The bound `κ` is
assumed only on the vertex links of this one `σ`, so different sets may use different constants.
The hypothesis `|σ| + 2 ≤ d` forces `d ≥ 2`. For `κ ≤ 1/2` the proof is Garland's method
(`garland_inequality_lower`, then `walkSmallestEigenvalueGE_of_garland`) with
`c = d − 1 − |σ| > 0`. For `κ > 1/2` the hypothesis makes every vertex link of `σ` edgeless
(`WalkSmallestEigenvalueGE.eq_zero_of_pos`), and then the link of `σ` is edgeless too. So the
conclusion holds whatever value `κ / (1 − κ)` takes, including the junk value `κ / 0 = 0` at
`κ = 1`. -/
theorem walkSmallestEigenvalueGE_linkWeightOf_step (hnn : ∀ F, 0 ≤ m F)
    (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {σ : Finset ι} (hσ : #σ + 2 ≤ d) {κ : ℝ}
    (hloc : ∀ z, z ∉ σ → WalkSmallestEigenvalueGE (linkWeightOf m (insert z σ)) κ) :
    WalkSmallestEigenvalueGE (linkWeightOf m σ) (κ / (1 - κ)) := by
  rcases le_or_gt κ (1 / 2) with hκ | hκ
  · have hc : (0 : ℝ) < (d : ℝ) - 1 - #σ := by
      have h : ((#σ + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hσ
      push_cast at h
      linarith
    refine walkSmallestEigenvalueGE_of_garland (linkWeightOf_nonneg hnn σ) hκ fun f mm hmm => ?_
    refine garland_inequality_lower
      (wz := fun z u v => if z ∈ σ then 0 else linkWeightOf m (insert z σ) u v) hc
      (linkWeightOf_symm m σ) ?_ (sum_linkWeightOf_insert hcard σ)
      (sum_linkWeightOf_insert_right hcard σ) ?_ f mm hmm
    · intro z u v
      split_ifs
      · rfl
      · exact linkWeightOf_symm m (insert z σ) u v
    · intro z
      by_cases hz : z ∈ σ
      · exact walkSmallestEigenvalueGE_of_forall_eq_zero (fun u v => by simp [hz]) _
      · simpa only [if_neg hz] using hloc z hz
  · refine walkSmallestEigenvalueGE_of_forall_eq_zero
      (linkWeightOf_eq_zero_of_forall_insert hcard hσ fun z hz => ?_) _
    exact (hloc z hz).eq_zero_of_pos (by linarith) (linkWeightOf_nonneg hnn _)
      (linkWeightOf_self m _)

/-- **Lower trickling down, with no complex, purity or connectivity.** Let `m ≥ 0` be a weight
vanishing off the sets with `d + 1` elements, for instance a top weight of a pure `d`-dimensional
complex. Suppose the link of every set with `d − 1` elements has every random-walk eigenvalue at
least `κ`. Then the link of every set `σ` with at most `d − 1` elements has every walk eigenvalue
at least `κ / (1 − j κ)`, where `j = d − 1 − |σ|`. For `σ = ∅`, every walk eigenvalue of the
weighted underlying graph is at least `κ / (1 − (d − 1) κ)`.

This is the lower half of Oppenheim's two-sided trickling down, with the same Möbius map as the
upper half `trickling_down_weighted`. Unlike that theorem, it has no connectivity hypothesis, no
condition `d ≥ 2` and no sign condition on `κ`.
* `κ ≤ 0` is the substantive case. Every denominator `1 − j κ` is at least `1`, and the bound
  improves (moves up towards `0`) as `j` grows, that is, as the link gets larger.
* `κ > 0` is degenerate. The hypothesis makes every link in the conclusion edgeless
  (`linkWeightOf_eq_zero_of_walkSmallestEigenvalueGE_pos`). So the conclusion holds whatever
  value the expression takes, including the junk value `κ / 0 = 0` when `1 − j κ = 0` and the
  negative values when `1 − j κ < 0`.
* For `d = 0` the hypothesis and the conclusion are both empty. For `d = 1` both concern only
  `σ = ∅`, with `j = 0`, and the conclusion is the hypothesis.
* There is no natural-number subtraction: `j` is computed in `ℝ` as `(d : ℝ) − 1 − |σ|`, which is
  a natural number whenever `|σ| + 1 ≤ d`.
* The hypothesis covers every set with `d − 1` elements, faces or not.
  `trickling_down_lower_weighted` assumes the bound on the faces of a complex only.

Every graph satisfies the hypothesis with `κ = −1` (`walkSmallestEigenvalueGE_neg_one`), and then
the conclusion is `link_walk_lower_bound` for the sets with at most `d − 1` elements.

The bound is sharp for complete complexes. On paper: take all `(d + 1)`-sets of `N ≥ d + 1`
points, with the uniform weight. For `|σ| ≤ d − 1` the link of `σ` is the complete graph, with
equal weights, on the `N − |σ|` points outside `σ`. Its smallest walk eigenvalue is
`−1/(N − 1 − |σ|)`. Starting from `κ = −1/(N − d)`, the value on the links of the sets with
`d − 1` elements, the trickled value is the same `−1/(N − 1 − |σ|)`. Only the case
`complete (Fin 5) 2` at `σ = ∅` is proved in Lean, in `complete_fin5_two_walkSmallestEigenvalueGE`
and `not_complete_fin5_two_walkSmallestEigenvalueGE`. -/
theorem trickling_down_lower (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = d + 1)
    {κ : ℝ}
    (hlocal : ∀ σ : Finset ι, #σ + 1 = d → WalkSmallestEigenvalueGE (linkWeightOf m σ) κ) :
    ∀ σ : Finset ι, #σ + 1 ≤ d →
      WalkSmallestEigenvalueGE (linkWeightOf m σ) (κ / (1 - ((d : ℝ) - 1 - #σ) * κ)) := by
  rcases lt_or_ge 0 κ with hκ | hκ
  · -- `κ > 0`: every link is edgeless
    intro σ hσ
    exact walkSmallestEigenvalueGE_of_forall_eq_zero
      (linkWeightOf_eq_zero_of_walkSmallestEigenvalueGE_pos hnn hcard hκ hlocal σ hσ) _
  -- `κ ≤ 0`: induction on `j = d − 1 − |σ|`
  have key : ∀ j : ℕ, ∀ σ : Finset ι, #σ + 1 + j = d →
      WalkSmallestEigenvalueGE (linkWeightOf m σ) (κ / (1 - (j : ℝ) * κ)) := by
    intro j
    induction j with
    | zero =>
      intro σ hσ
      simpa using hlocal σ (by omega)
    | succ j ih =>
      intro σ hσ
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have h1 : 0 < 1 - (j : ℝ) * κ := by nlinarith
      have hstep := walkSmallestEigenvalueGE_linkWeightOf_step hnn hcard (σ := σ) (by omega)
        fun z hz => ih (insert z σ) (by rw [Finset.card_insert_of_notMem hz]; omega)
      have e : κ / (1 - (j : ℝ) * κ) / (1 - κ / (1 - (j : ℝ) * κ)) =
          κ / (1 - ((j : ℝ) + 1) * κ) := by
        have e1 : 1 - κ / (1 - (j : ℝ) * κ) =
            (1 - ((j : ℝ) + 1) * κ) / (1 - (j : ℝ) * κ) := by
          rw [eq_div_iff h1.ne', sub_mul, div_mul_cancel₀ _ h1.ne']
          ring
        rw [e1, div_div_div_cancel_right₀ h1.ne']
      rw [e] at hstep
      simpa using hstep
  intro σ hσ
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hσ
  have hj' : (d : ℝ) - 1 - #σ = j := by
    have h : (d : ℝ) = #σ + 1 + j := by exact_mod_cast hj
    linarith
  rw [hj']
  exact key j σ hj.symm

/-! ### Lower trickling down on a complex -/

/-- A weight supported on the faces of `K` gives the "link" of a nonempty non-face no edges. -/
private theorem linkWeightOf_eq_zero_of_notMem_of_support {K : PreAbstractSimplicialComplex ι}
    (hK : ∀ F, m F ≠ 0 → F ∈ K) {τ : Finset ι} (hne : τ.Nonempty) (hτ : τ ∉ K) (u v : ι) :
    linkWeightOf m τ u v = 0 := by
  unfold linkWeightOf
  split_ifs
  · refine Finset.sum_eq_zero fun F hF => ?_
    by_contra h
    rw [Finset.mem_filter] at hF
    exact hτ (K.mem_of_subset (hK F h)
      ((Finset.subset_insert _ _).trans ((Finset.subset_insert _ _).trans hF.2)) hne)
  · rfl

/-- The hypothesis of `trickling_down_lower` from the hypothesis on faces alone. -/
private theorem walkSmallestEigenvalueGE_of_forall_mem {K : PreAbstractSimplicialComplex ι}
    (hd : 2 ≤ d) (hK : ∀ F, m F ≠ 0 → F ∈ K) {κ : ℝ}
    (hlocal : ∀ σ ∈ K, #σ + 1 = d → WalkSmallestEigenvalueGE (linkWeightOf m σ) κ)
    (τ : Finset ι) (hτ : #τ + 1 = d) : WalkSmallestEigenvalueGE (linkWeightOf m τ) κ := by
  by_cases hτK : τ ∈ K
  · exact hlocal τ hτK hτ
  · have hne : τ.Nonempty := by
      rw [← Finset.card_pos]
      omega
    exact walkSmallestEigenvalueGE_of_forall_eq_zero
      (linkWeightOf_eq_zero_of_notMem_of_support hK hne hτK) _

variable (K : PreAbstractSimplicialComplex ι)

/-- **Lower trickling down on a complex.** This is `trickling_down_lower` with the local bound
assumed only on the `(d − 2)`-dimensional faces of `K`. The weight `m` must be nonnegative and
supported on faces of `K` with `d + 1` elements. Every top weight (`IsTopWeight`) is one, but
purity, positivity on the top faces and connectivity are not needed. The conclusion covers every
set `σ` with at most `d − 1` elements: the faces of dimension at most `d − 2`, the empty set, and
the nonempty non-faces, whose links have no edges.

The condition `d ≥ 2` is needed. For `d = 1` the hypothesis concerns sets with no element, and `∅`
is never a face, so the hypothesis is empty. The conclusion at `σ = ∅` would then bound every walk
eigenvalue of the underlying graph below by an arbitrary `κ`, and a single edge, with walk
eigenvalue `−1`, refutes that. For `d = 0` the conclusion is empty. As in `trickling_down_lower`,
there is no sign condition on `κ`. -/
theorem trickling_down_lower_weighted (hd : 2 ≤ d) (hnn : ∀ F, 0 ≤ m F)
    (hcard : ∀ F, m F ≠ 0 → #F = d + 1) (hK : ∀ F, m F ≠ 0 → F ∈ K) {κ : ℝ}
    (hlocal : ∀ σ ∈ K, #σ + 1 = d → WalkSmallestEigenvalueGE (linkWeightOf m σ) κ) :
    ∀ σ : Finset ι, #σ + 1 ≤ d →
      WalkSmallestEigenvalueGE (linkWeightOf m σ) (κ / (1 - ((d : ℝ) - 1 - #σ) * κ)) :=
  trickling_down_lower hnn hcard (walkSmallestEigenvalueGE_of_forall_mem hd hK hlocal)

/-- **Two-sided trickling down (Oppenheim, Theorem 1.4).** Take the hypotheses of
`trickling_down_weighted`:
* `d ≥ 2` and a top weight `m`;
* connected links for `K` and for its faces of dimension at most `d − 3`;
* `(d − 1) · lam < 1`;
* second walk eigenvalue at most `lam` on the links of the `(d − 2)`-dimensional faces.

Add a lower bound `κ` on every walk eigenvalue of those same links. Then, with
`j = d − 1 − |σ|`, the link of every face `σ` of dimension at most `d − 2`, and `K` itself, has
every walk eigenvalue at least `κ / (1 − j κ)` and second walk eigenvalue at most
`lam / (1 − j · lam)`.

Connectivity is used only for the upper bound. There is no sign condition on `κ`; the case
`κ > 0` is degenerate, as explained in `trickling_down_lower`. -/
theorem trickling_down_two_sided (hd : 2 ≤ d) (hm : K.IsTopWeight d m)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ d → (K.link σ).IsConnected)
    {lam : ℝ} (hlam : ((d : ℝ) - 1) * lam < 1)
    (hupper : ∀ σ ∈ K, #σ + 1 = d → WalkSecondEigenvalueLE (linkWeightOf m σ) lam)
    {κ : ℝ} (hlower : ∀ σ ∈ K, #σ + 1 = d → WalkSmallestEigenvalueGE (linkWeightOf m σ) κ) :
    ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d →
      WalkSmallestEigenvalueGE (linkWeightOf m σ) (κ / (1 - ((d : ℝ) - 1 - #σ) * κ)) ∧
      WalkSecondEigenvalueLE (linkWeightOf m σ) (lam / (1 - ((d : ℝ) - 1 - #σ) * lam)) :=
  fun σ hσ hcard =>
    ⟨K.trickling_down_lower_weighted hd hm.nonneg hm.card_eq_of_ne_zero
        (fun _ h => hm.mem_of_ne_zero h) hlower σ hcard,
      K.trickling_down_weighted hd hm hconn hlam hupper σ hσ hcard⟩

/-! ### Two-sided local spectral expanders -/

/-- `K`, with the weight `m` on its top faces, is a **two-sided `(κ, lam)`-local-spectral
expander** of dimension `d` when two things hold:
* it is a `lam`-local-spectral expander (`IsLocalSpectralExpanderOf`). That is, `d ≥ 1`, `m` is a
  top weight, and the random walk on `K` itself and on the link of every face of dimension at
  most `d − 2` has second eigenvalue at most `lam`;
* on the same links, every eigenvalue of the random walk is at least `κ`.

So the spectrum of each such link, apart from its top eigenvalue `1`, lies in `[κ, lam]`.

Oppenheim's Definition 1.2 is different. It assumes every link is connected and bounds the
spectrum only on the links of the `(d − 2)`-dimensional faces; his Theorem 1.4 then bounds the
lower links. This definition, like `IsLocalSpectralExpanderOf`, bounds every tested link directly
with one pair of constants, so it is stronger in the upper parameter. (In the lower parameter the
two agree for `d ≥ 2` and a top weight: by `trickling_down_lower_weighted`, which needs no
connectivity, a bound `κ` on the links of the `(d − 2)`-dimensional faces gives `κ` on every
tested link, as in the proof of `isTwoSidedLocalSpectralExpanderOf_of_trickling_down`.) For example,
`complete (Fin 5) 2` meets Oppenheim's condition with walk constants `(−1/3, −1/3)`: its vertex
links `K₄` are connected (`isConnected_complete_fin5_two_link`) with walk spectrum `{1, −1/3}`
(`walkSecondEigenvalueLE_complete_fin5_two_link_singleton`,
`walkSmallestEigenvalueGE_complete_fin5_two_link_singleton`). This definition, however, holds for
it exactly when `κ ≤ −1/3` and `−1/4 ≤ lam`
(`isTwoSidedLocalSpectralExpanderOf_complete_fin5_two_iff`), because `K` itself, with underlying
graph `K₅`, is tested too and has second walk eigenvalue `−1/4`.
`isTwoSidedLocalSpectralExpanderOf_of_trickling_down` derives this definition from Oppenheim-type
hypotheses.

Every tested link has an edge, so the lower parameter is always negative
(`IsTwoSidedLocalSpectralExpanderOf.lt_zero`). The value `κ = −1` is always allowed
(`IsLocalSpectralExpanderOf.isTwoSidedLocalSpectralExpanderOf_neg_one`), so the lower condition
restricts anything only for `κ > −1`. Dimension `0` is excluded, as in
`IsLocalSpectralExpanderOf`, and for `d = 1` only `K` itself is tested. -/
def IsTwoSidedLocalSpectralExpanderOf (d : ℕ) (m : Finset ι → ℝ) (κ lam : ℝ) : Prop :=
  K.IsLocalSpectralExpanderOf d m lam ∧ ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d →
    WalkSmallestEigenvalueGE (linkWeightOf m σ) κ

variable {K} {κ lam : ℝ}

/-- The upper half of a two-sided local spectral expander. -/
theorem IsTwoSidedLocalSpectralExpanderOf.isLocalSpectralExpanderOf
    (h : K.IsTwoSidedLocalSpectralExpanderOf d m κ lam) : K.IsLocalSpectralExpanderOf d m lam :=
  h.1

/-- The lower half of a two-sided local spectral expander, at one link. -/
theorem IsTwoSidedLocalSpectralExpanderOf.walkSmallestEigenvalueGE
    (h : K.IsTwoSidedLocalSpectralExpanderOf d m κ lam) {σ : Finset ι} (hσ : σ = ∅ ∨ σ ∈ K)
    (hcard : #σ + 1 ≤ d) : WalkSmallestEigenvalueGE (linkWeightOf m σ) κ :=
  h.2 σ hσ hcard

/-- **Monotonicity.** A two-sided `(κ, lam)`-local-spectral expander is a two-sided
`(κ', lam')`-local-spectral expander whenever `κ' ≤ κ` and `lam ≤ lam'`. -/
theorem IsTwoSidedLocalSpectralExpanderOf.mono
    (h : K.IsTwoSidedLocalSpectralExpanderOf d m κ lam) {κ' lam' : ℝ} (hκ : κ' ≤ κ)
    (hlam : lam ≤ lam') : K.IsTwoSidedLocalSpectralExpanderOf d m κ' lam' :=
  ⟨⟨h.1.one_le, h.1.isTopWeight, fun σ hσ hcard =>
      (h.1.walkSecondEigenvalueLE hσ hcard).mono (linkWeightOf_nonneg h.1.isTopWeight.nonneg σ)
        hlam⟩,
    fun σ hσ hcard =>
      (h.2 σ hσ hcard).mono (linkWeightOf_nonneg h.1.isTopWeight.nonneg σ) hκ⟩

/-- **The lower parameter is negative.** The weighted underlying graph of a two-sided local
spectral expander has an edge (`IsLocalSpectralExpanderOf.exists_linkWeightOf_pos`), so its random
walk has a negative eigenvalue (`WalkSmallestEigenvalueGE.lt_zero`). -/
theorem IsTwoSidedLocalSpectralExpanderOf.lt_zero
    (h : K.IsTwoSidedLocalSpectralExpanderOf d m κ lam) : κ < 0 := by
  have hd := h.isLocalSpectralExpanderOf.one_le
  have hd' : #(∅ : Finset ι) + 1 ≤ d := by rw [Finset.card_empty]; omega
  obtain ⟨u, v, huv⟩ := h.isLocalSpectralExpanderOf.exists_linkWeightOf_pos (Or.inl rfl) hd'
  exact (h.walkSmallestEigenvalueGE (Or.inl rfl) hd').lt_zero
    (linkWeightOf_nonneg h.isLocalSpectralExpanderOf.isTopWeight.nonneg ∅)
    (linkWeightOf_self m ∅) huv

/-- **Every local spectral expander is two-sided with lower parameter `−1`.** By
`link_walk_lower_bound`, the link of a set `σ` with `|σ| + 1 ≤ d` has every walk eigenvalue at
least `−1 / (d − |σ|) ≥ −1`; the denominator `d − |σ|` is at least `1`. No better universal
constant exists: `−1` is attained whenever the link of some `(d − 2)`-dimensional face is a single
edge. -/
theorem IsLocalSpectralExpanderOf.isTwoSidedLocalSpectralExpanderOf_neg_one
    (h : K.IsLocalSpectralExpanderOf d m lam) :
    K.IsTwoSidedLocalSpectralExpanderOf d m (-1) lam := by
  refine ⟨h, fun σ _ hcard f => ?_⟩
  have hm := h.isTopWeight
  have h1 := hm.link_walk_lower_bound σ f
  have hj : (1 : ℝ) ≤ (d : ℝ) - #σ := by
    have h' : ((#σ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hcard
    push_cast at h'
    linarith
  have hN : 0 ≤ ∑ u, (∑ v, linkWeightOf m σ u v) * f u ^ 2 := Finset.sum_nonneg fun u _ =>
    mul_nonneg (Finset.sum_nonneg fun v _ => linkWeightOf_nonneg hm.nonneg σ u v) (sq_nonneg _)
  have h2 : -1 ≤ -(1 / ((d : ℝ) - #σ)) := by
    rw [neg_le_neg_iff, div_le_one (by linarith)]
    exact hj
  exact (mul_le_mul_of_nonneg_right h2 hN).trans h1

variable (K) in
/-- **Two-sided trickling down, packaged.** Under the hypotheses of `trickling_down_two_sided`,
`K` is a two-sided `(κ, lam / (1 − (d − 1) lam))`-local-spectral expander.

The upper parameter is the one from `isLocalSpectralExpanderOf_of_trickling_down_weighted`. The
lower parameter is `κ` itself, the bound at `j = 0`. For `κ ≤ 0` the bounds `κ / (1 − j κ)`
increase with `j`, so the links of the `(d − 2)`-faces are the worst, and a single constant loses
the improvement at the lower levels; `trickling_down_two_sided` keeps it. There is no sign
condition on `κ`. For `κ > 0` the hypotheses contradict each other: the lower bound makes every
link edgeless, while a top weight gives the underlying graph an edge. -/
theorem isTwoSidedLocalSpectralExpanderOf_of_trickling_down (hd : 2 ≤ d) (hm : K.IsTopWeight d m)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ d → (K.link σ).IsConnected)
    (hlam : ((d : ℝ) - 1) * lam < 1)
    (hupper : ∀ σ ∈ K, #σ + 1 = d → WalkSecondEigenvalueLE (linkWeightOf m σ) lam)
    (hlower : ∀ σ ∈ K, #σ + 1 = d → WalkSmallestEigenvalueGE (linkWeightOf m σ) κ) :
    K.IsTwoSidedLocalSpectralExpanderOf d m κ (lam / (1 - ((d : ℝ) - 1) * lam)) := by
  refine ⟨K.isLocalSpectralExpanderOf_of_trickling_down_weighted hd hm hconn hlam hupper,
    fun σ _ hcard => ?_⟩
  have hloc := walkSmallestEigenvalueGE_of_forall_mem hd (fun _ h => hm.mem_of_ne_zero h) hlower
  rcases le_or_gt κ 0 with hκ | hκ
  · -- `κ ≤ κ / (1 − j κ)` for `κ ≤ 0`
    refine (trickling_down_lower hm.nonneg hm.card_eq_of_ne_zero hloc σ hcard).mono
      (linkWeightOf_nonneg hm.nonneg σ) ?_
    have hj : (0 : ℝ) ≤ (d : ℝ) - 1 - #σ := by
      have h' : ((#σ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hcard
      push_cast at h'
      linarith
    have h1 : 1 ≤ 1 - ((d : ℝ) - 1 - #σ) * κ := by nlinarith
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  · -- `κ > 0`: every link is edgeless
    exact walkSmallestEigenvalueGE_of_forall_eq_zero
      (linkWeightOf_eq_zero_of_walkSmallestEigenvalueGE_pos hm.nonneg hm.card_eq_of_ne_zero hκ
        hloc σ hcard) _

/-! ### All triangles on five points -/

/-- **The vertex links are `K₄`, from below.** In all triangles on five points, the random walk on
the link of any vertex `z` (the complete graph on the other four points, every edge of weight `1`)
has every eigenvalue at least `−1/3`. Its eigenvalues are `1` and `−1/3`.

On paper: every `u ≠ z` has degree `3`, and
`Σ_{u ≠ v} f(u) f(v) = (Σ f)² − Σ f² ≥ −Σ f² = (−1/3) · Σ 3 f(u)²`, all sums running over the
points other than `z`. The vertex `z` has degree `0` in its own link and drops out. -/
theorem walkSmallestEigenvalueGE_complete_fin5_two_link_singleton (z : Fin 5) :
    WalkSmallestEigenvalueGE ((complete (Fin 5) 2).linkWeight 2 {z}) (-1 / 3) := by
  intro f
  simp only [linkWeight_complete_fin5_two_singleton]
  fin_cases z <;> simp only [Fin.sum_univ_five] <;> simp +decide
  · nlinarith [sq_nonneg (f 1 + f 2 + f 3 + f 4)]
  · nlinarith [sq_nonneg (f 0 + f 2 + f 3 + f 4)]
  · nlinarith [sq_nonneg (f 0 + f 1 + f 3 + f 4)]
  · nlinarith [sq_nonneg (f 0 + f 1 + f 2 + f 4)]
  · nlinarith [sq_nonneg (f 0 + f 1 + f 2 + f 3)]

/-- **The bound `−1/3` on the vertex links is sharp.** For the link of `z` (the complete graph
`K₄` on the other four points, every edge of weight `1`), the function that is `1` at `z + 1`,
`−1` at `z + 2` and `0` elsewhere has `Σ_{u,v} w(u,v) f(u) f(v) = −2` and
`Σ_u deg(u) f(u)² = 6`, so no lower bound above `−1/3` holds. -/
theorem not_walkSmallestEigenvalueGE_complete_fin5_two_link_singleton (z : Fin 5) {μ : ℝ}
    (hμ : -1 / 3 < μ) :
    ¬ WalkSmallestEigenvalueGE ((complete (Fin 5) 2).linkWeight 2 {z}) μ := by
  intro h
  have h1 := h fun x => if x = z + 1 then 1 else if x = z + 2 then -1 else 0
  simp only [linkWeight_complete_fin5_two_singleton, Fin.sum_univ_five] at h1
  fin_cases z <;> simp +decide at h1 <;> linarith

/-- **Lower trickling down on all triangles on five points.** The vertex links `K₄` have every
walk eigenvalue at least `−1/3`. From this, `trickling_down_lower` (with `d = 2`, `σ = ∅`, `j = 1`)
bounds every eigenvalue of the random walk on the underlying graph `K₅` below by
`(−1/3) / (1 + 1/3) = −1/4`. -/
theorem complete_fin5_two_walkSmallestEigenvalueGE :
    WalkSmallestEigenvalueGE ((complete (Fin 5) 2).linkWeight 2 ∅) (-1 / 4) := by
  have h := trickling_down_lower ((complete (Fin 5) 2).uniformWeight_nonneg 2)
    ((complete (Fin 5) 2).card_eq_of_uniformWeight_ne_zero 2) (κ := -1 / 3)
    (fun σ hσ => by
      obtain ⟨z, rfl⟩ := card_eq_one.mp (by omega : #σ = 1)
      rw [← linkWeight_eq_linkWeightOf]
      exact walkSmallestEigenvalueGE_complete_fin5_two_link_singleton z)
    ∅ (by simp)
  rwa [← linkWeight_eq_linkWeightOf, trickling_down_bound_complete_fin5_two] at h

/-- **The bound `−1/4` is sharp.** The underlying graph is `K₅`, every edge of weight `3`. The test
function `f = (1, −1, 0, 0, 0)` has `Σ_{u,v} w(u,v) f(u) f(v) = −6` and `Σ_u deg(u) f(u)² = 24`, so
no lower bound above `−1/4` holds.

Together with `complete_fin5_two_walkSecondEigenvalueLE` (second eigenvalue at most `−1/4`), this
pins down the walk on `K₅` exactly: every eigenvalue other than the top eigenvalue `1` equals
`−1/4`, and two-sided trickling down is exact here. -/
theorem not_complete_fin5_two_walkSmallestEigenvalueGE {μ : ℝ} (hμ : -1 / 4 < μ) :
    ¬ WalkSmallestEigenvalueGE ((complete (Fin 5) 2).linkWeight 2 ∅) μ := by
  intro h
  have h1 := h ![1, -1, 0, 0, 0]
  simp only [linkWeight_complete_fin5_two_empty, Fin.sum_univ_five] at h1
  simp +decide at h1
  linarith

/-- **All triangles on five points form a two-sided local spectral expander**, with parameters
`(−1/3, −1/4)`. This is the packaged theorem `isTwoSidedLocalSpectralExpanderOf_of_trickling_down`
with `κ = lam = −1/3` on the vertex links `K₄`, so `IsTwoSidedLocalSpectralExpanderOf` is
satisfiable. The lower parameter is `−1/3` rather than `−1/4` because the definition uses one
constant for every link, and the vertex links `K₄` do have the eigenvalue `−1/3`. The upper
parameter is `−1/4` rather than `−1/3` because `K` itself is tested, and its underlying graph `K₅`
has second walk eigenvalue `−1/4`. Both parameters are optimal
(`isTwoSidedLocalSpectralExpanderOf_complete_fin5_two_iff`). -/
theorem isTwoSidedLocalSpectralExpanderOf_complete_fin5_two :
    (complete (Fin 5) 2).IsTwoSidedLocalSpectralExpanderOf 2
      ((complete (Fin 5) 2).uniformWeight 2) (-1 / 3) (-1 / 4) := by
  have hm : (complete (Fin 5) 2).IsTopWeight 2 ((complete (Fin 5) 2).uniformWeight 2) :=
    (complete (Fin 5) 2).isTopWeight_uniformWeight isPure_complete_fin5_two
      ⟨{0}, mem_complete.mpr ⟨singleton_nonempty 0, by simp⟩⟩
  have h := (complete (Fin 5) 2).isTwoSidedLocalSpectralExpanderOf_of_trickling_down le_rfl hm
    (fun σ _ hσ => isConnected_complete_fin5_two_link σ (by omega)) (lam := -1 / 3)
    (by norm_num)
    (fun σ _ hσ => by
      obtain ⟨z, rfl⟩ := card_eq_one.mp (by omega : #σ = 1)
      rw [← linkWeight_eq_linkWeightOf]
      exact walkSecondEigenvalueLE_complete_fin5_two_link_singleton z)
    (κ := -1 / 3)
    (fun σ _ hσ => by
      obtain ⟨z, rfl⟩ := card_eq_one.mp (by omega : #σ = 1)
      rw [← linkWeight_eq_linkWeightOf]
      exact walkSmallestEigenvalueGE_complete_fin5_two_link_singleton z)
  convert h using 1
  norm_num

/-- **The parameters `(−1/3, −1/4)` are optimal.** All triangles on five points, with the uniform
weight, form a two-sided `(κ, lam)`-local-spectral expander exactly when `κ ≤ −1/3` and
`−1/4 ≤ lam`. A larger `κ` fails on a vertex link `K₄`
(`not_walkSmallestEigenvalueGE_complete_fin5_two_link_singleton`), and a smaller `lam` fails on
`K` itself, whose underlying graph is `K₅` (`not_complete_fin5_two_walkSecondEigenvalueLE`).

In particular the definition fails for `(−1/3, −1/3)`, although the complex meets Oppenheim's
Definition 1.2 with these walk constants: that definition tests only the vertex links, which are
connected with walk spectrum `{1, −1/3}`. See the docstring of
`IsTwoSidedLocalSpectralExpanderOf`. -/
theorem isTwoSidedLocalSpectralExpanderOf_complete_fin5_two_iff {κ lam : ℝ} :
    (complete (Fin 5) 2).IsTwoSidedLocalSpectralExpanderOf 2
      ((complete (Fin 5) 2).uniformWeight 2) κ lam ↔ κ ≤ -1 / 3 ∧ -1 / 4 ≤ lam := by
  constructor
  · intro h
    refine ⟨le_of_not_gt fun hκ => ?_, le_of_not_gt fun hlam => ?_⟩
    · have h1 := h.walkSmallestEigenvalueGE (σ := {0})
        (Or.inr (mem_complete.mpr ⟨singleton_nonempty 0, by simp⟩)) (by simp)
      rw [← linkWeight_eq_linkWeightOf] at h1
      exact not_walkSmallestEigenvalueGE_complete_fin5_two_link_singleton 0 hκ h1
    · have h1 := h.isLocalSpectralExpanderOf.walkSecondEigenvalueLE (σ := ∅) (Or.inl rfl)
        (by simp)
      rw [← linkWeight_eq_linkWeightOf] at h1
      exact not_complete_fin5_two_walkSecondEigenvalueLE hlam h1
  · rintro ⟨hκ, hlam⟩
    exact isTwoSidedLocalSpectralExpanderOf_complete_fin5_two.mono hκ hlam

/-! ### Sanity check: `κ = −1` recovers `link_walk_lower_bound` -/

/- Every walk eigenvalue of a graph is at least `−1` (`walkSmallestEigenvalueGE_neg_one`), and
lower trickling down from `κ = −1` gives `−1 / (1 + j) = −1 / (d − |σ|)`, which is exactly
`link_walk_lower_bound` for the links of sets with at most `d − 1` elements. -/
example (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = d + 1) (σ : Finset ι)
    (hσ : #σ + 1 ≤ d) :
    WalkSmallestEigenvalueGE (linkWeightOf m σ) (-(1 / ((d : ℝ) - #σ))) := by
  have h := trickling_down_lower hnn hcard (κ := -1)
    (fun τ _ => walkSmallestEigenvalueGE_neg_one (linkWeightOf_symm m τ)
      (linkWeightOf_nonneg hnn τ)) σ hσ
  have e : (-1 : ℝ) / (1 - ((d : ℝ) - 1 - #σ) * -1) = -(1 / ((d : ℝ) - #σ)) := by
    rw [show (1 : ℝ) - ((d : ℝ) - 1 - #σ) * -1 = (d : ℝ) - #σ by ring, neg_div]
  rwa [e] at h

end PreAbstractSimplicialComplex
