/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.SimplexRigidity
import Expanders.NegativeRigidity
import Expanders.TricklingDownLower
import Expanders.TwoSided

/-!
# Stability in the trace bound: near-optimal walks are nearly uniform

The trace bound (`WalkSecondEigenvalueLE.neg_one_div_card_le`, Chung's Lemma 1.7) says that the
second eigenvalue `μ₂` of the random walk on a weighted graph with `n` vertices of positive degree
is at least `−1/(n − 1)`, with equality only for the uniformly weighted complete graph
(`walkSecondEigenvalueLE_neg_one_div_card_iff`). This file makes the rigidity quantitative. Let
`w` be symmetric, nonnegative, without loops and with every degree `deg u = Σ_v w(u,v)` positive
(the graph need not be connected), let `vol = Σ_u deg u`, `π(u) = deg u / vol`, let
`1 = μ₁ ≥ μ₂ ≥ … ≥ μ_n` be the walk eigenvalues and `ε = μ₂ + 1/(n − 1) ≥ 0`. Then:

* **(a)** `μ_n ≤ −π(u)/(1 − π(u)) ≤ μ₂` for every vertex `u`;
* **(b)** `μ_n ≤ −w(u,v)/√(deg u · deg v) ≤ −2w(u,v)/(deg u + deg v) ≤ μ₂` for `u ≠ v`;
* **(c)** `μ_n ≥ −1/(n − 1) − (n − 2) ε`, and
  `Σ_{j ≥ 2} (μ_j + 1/(n − 1))² = Σ_{u,v} w(u,v)²/(deg u · deg v) − n/(n − 1)`
  `  ≤ (n − 1)(n − 2) ε²`;
* **(d)** stability: `π(u) ≤ (1 + (n − 1)(n − 2) ε)/(n + (n − 1)(n − 2) ε)`,
  `2w(u,v)/(deg u + deg v) ≤ w(u,v)/√(deg u · deg v) ≤ 1/(n − 1) + (n − 2) ε`,
  `π(u) ≥ (1 − (n − 1) ε)/(n − (n − 1) ε)`, `2w(u,v)/(deg u + deg v) ≥ 1/(n − 1) − ε`, and if
  `ε < 1/(n − 1)` every pair carries positive weight.

All of (d) is sharp: for `n ≥ 3` and every `ε ∈ [0, 1/(n − 1))` one of four explicit families
attains each bound, and two of them, together with the complete bipartite graphs at
`ε = 1/(n − 1)`, attain equality in (c).

## How this was found
The statement was proposed after a numerical search, and an independent attempt to refute it
found no counterexample. That attempt ran 352,051 random weightings with `n = 3..15` in eight
regimes and 51,602 link graphs of random pure complexes. It factored the walk characteristic
polynomials of the four families exactly over `ℚ(a)` with sympy for `n = 3..7`, and ran
Nelder–Mead searches for violations at fixed `ε`. All margins were `≥ −2·10⁻¹⁵`. The scripts are
in `.lake/scratch-frontier/trace-bound-sharp-stability-skeptic/` and
`.lake/scratch-frontier/trace-bound-sharp-stability-lit/`. The proof here is the one suggested
with the statement: test functions for (a) and (b), the trace and Frobenius norm of the
symmetrised walk for (c), and algebra for (d). The sympy certificates for the two edge families
are in `.lake/scratch-frontier/trace-bound-sharp-stability/`.

## What is known
The statement is true, but it is folklore-level rather than new mathematics:
* (a) and (b) are Rayleigh quotients of the two standard test vectors (`1_u − π(u)` and
  `deg v · 1_u − deg u · 1_v`). The `μ₂` half of (b) is already in the project
  (`WalkSecondEigenvalueLE.neg_two_mul_weight_le`). For unweighted graphs the `μ₂` half of (b) at
  `w(u,v) = 0` is in Chung's *Spectral Graph Theory*, Lemma 1.7, and the `μ_n` half of (a) at a
  vertex of maximum degree is in Li, Guo and Shiu (2014); the second paper was seen only through
  its abstract.
* The sum bound in (c) is Yu and Peng's (2010) inequality
  `2R₋₁ ≤ (n − 1)(n − 2)(n/(n − 1) − ρ_{n−1})² + n/(n − 1)`, where `R₋₁` is the general Randić
  index and `ρ_{n−1} = 1 − μ₂` the smallest nonzero normalised Laplacian eigenvalue. It is quoted
  as Remark 2.3 of E. I. Milovanović and I. Ž. Milovanović, *Remarks on bounds of normalized
  Laplacian eigenvalues of graphs*, arXiv:1506.05762; we read that text. The lower bound on `μ_n`
  is the Lupaş / Wolkowicz–Styan trace inequality applied to the `n − 1` nontrivial eigenvalues.
  These sources treat simple unweighted (connected) graphs, but the proofs carry over to weighted
  graphs unchanged.
* (d) is a few lines of algebra on top of (a)–(c).

The literature search (WebSearch / WebFetch, by the two refutation passes and again while writing
this file) did not find two things written down: the `ε`-form of (d) for weighted graphs, and the
four weighted extremal families. It also turned up a correction. Milovanović–Milovanović
(Theorem 2.1, case (7)) state equality in the sum bound only for `K_n` (Yu–Peng's own equality
statement was not checked), but the heavy vertex family, the heavy edge
family and the complete bipartite graphs `K_{p,q}` (`n ≥ 3`) also attain it
(`starWeight_trace_bound_eq`, `edgeWeight_trace_bound_eq`, `bipartiteWeight_trace_bound_eq`). The
search covered high-dimensional expander sources (Kaufman–Oppenheim, Oppenheim Part I, Alev–Lau,
Dikstein's lecture notes) and found no `ε`-form stability statement for links. None would be
needed, since it is immediate. This should not be presented as a new result. It is a
quantitative companion to `walkSecondEigenvalueLE_neg_one_div_card_iff` and to the rigidity
theorems in `Expanders.NegativeRigidity` and `Expanders.SimplexRigidity`.

## Conventions
`n = Fintype.card ι` is the number of vertices; `deg u = Σ_v w u v`; `vol = Σ_x Σ_y w x y`;
`π(u) = deg u / vol`; `μ₂`, `μ_n` are `(walkMatrix_isHermitian hsymm).secondEigenvalue` and
`.smallestEigenvalue`; "the eigenvalues `μ_j`, `j ≥ 2`" are `eigenvalues j` for
`j ∈ univ.erase (topIndex ι)`. The variational forms use `WalkSecondEigenvalueLE w lam`
(`μ₂ ≤ lam`) and `WalkSmallestEigenvalueGE w κ` (`μ_n ≥ κ`), and `ε` appears through the
hypothesis `WalkSecondEigenvalueLE w (ε − 1/(n − 1))`, that is `μ₂ + 1/(n − 1) ≤ ε`. The
spectral forms set `ε = μ₂ + 1/(n − 1)` exactly.

## Definitions
* `starWeight o α β`: weight `β` on the pairs containing `o`, `α` on the other pairs, `0` on the
  diagonal. With `α = 1` it is the vertex family `w(o, x) = a`.
* `edgeWeight o o' α β γ`: weight `γ` on `{o, o'}`, `β` on the other pairs meeting `{o, o'}`,
  `α` on the rest. With `α = β = 1, γ = τ` it is the light edge family. With `α = 1`, `β = a`
  and `γ = a(2a − 1)` it is the heavy edge family.
* `bipartiteWeight A`: the complete bipartite graph between `A` and its complement. For `A = {o}`
  it is the star.

## Main theorems
Spectral form (all **proved**):
* `walkMatrix_vertex_bound` (a), `walkMatrix_edge_bound` (b), `walkMatrix_trace_bound` (c),
  `walkMatrix_stability` (d).
* `walkMatrix_eigenvalues_of_sum_sq_eq`: if `ε > 0` and equality holds in the sum bound of (c),
  the nontrivial spectrum is `μ₂` (exactly `n − 2` times) and `−1/(n − 1) − (n − 2) ε` (once).

Variational form (the workhorses, all **proved**):
* (a) `WalkSecondEigenvalueLE.neg_stationary_div_le`,
  `WalkSmallestEigenvalueGE.le_neg_stationary_div`.
* (b) `WalkSecondEigenvalueLE.neg_two_mul_weight_div_le`,
  `WalkSmallestEigenvalueGE.le_neg_weight_div_sqrt`, `two_mul_weight_div_le_weight_div_sqrt`.
* (c) `WalkSecondEigenvalueLE.walkSmallestEigenvalueGE_trace`,
  `WalkSecondEigenvalueLE.sum_sq_div_sub_le`, `sum_erase_topIndex_walkMatrix_eigenvalues_add_sq`.
* (d) `WalkSecondEigenvalueLE.stationary_le`, `WalkSecondEigenvalueLE.weight_div_sqrt_le`,
  `WalkSecondEigenvalueLE.le_stationary`, `WalkSecondEigenvalueLE.sub_le_two_mul_weight_div`,
  `WalkSecondEigenvalueLE.weight_pos_of_lt`.

Sharpness (all **proved**):
* Exact second eigenvalues: `walkSecondEigenvalueLE_starWeight_iff_of_le_one` (light vertex,
  `μ₂ = −a/(a + n − 2)`), `walkSecondEigenvalueLE_starWeight_iff_of_one_le` (heavy vertex,
  `μ₂ = −1/(a + n − 2)`), `walkSecondEigenvalueLE_edgeWeight_light_iff` (light edge,
  `μ₂ = −τ/(τ + n − 2)`), `walkSecondEigenvalueLE_edgeWeight_heavy_iff` (heavy edge,
  `μ₂ = −1/(2a + n − 3)`), `walkSecondEigenvalueLE_bipartiteWeight_iff` (`μ₂ = 0`).
* Equality in (d), for each family: `starWeight_le_stationary_sharp`,
  `starWeight_stationary_le_sharp`, `edgeWeight_sub_le_two_mul_weight_div_sharp`,
  `edgeWeight_weight_div_sqrt_le_sharp`; for every `ε ∈ [0, 1/(n − 1))`:
  `exists_starWeight_le_stationary_eq`, `exists_starWeight_stationary_le_eq`,
  `exists_edgeWeight_sub_le_two_mul_weight_div_eq`, `exists_edgeWeight_weight_div_sqrt_le_eq`.
* Equality in (c): `starWeight_trace_bound_eq`, `edgeWeight_trace_bound_eq`,
  `bipartiteWeight_trace_bound_eq`. The spectra, with `μ₂` of multiplicity `n − 2`:
  `starWeight_walkMatrix_spectrum`, `edgeWeight_walkMatrix_spectrum`,
  `bipartiteWeight_walkMatrix_spectrum`.
* At parameter `1` the vertex and edge families are `K_n` (`starWeight_one_one`,
  `edgeWeight_one_one_one`), with `ε = 0`.

## Deviations from the proposed statement
* The two lower bounds of (d) hold with no condition on `ε` in spectral form. The proposal
  assumed `ε < 1/(n − 1)`, which is exactly the condition for them to be positive. In the
  variational form the lower degree bound needs `ε ≤ n/(n − 1)` (`μ₂ ≤ 1`), which is automatic
  spectrally.
* The upper bounds of (d) need no assumption on `ε`. The upper edge bound also holds for `u = v`.
* `n ≥ 2` is automatic for a nonempty vertex type: a vertex of positive degree without a loop
  has a neighbour. `n ≥ 3` is used only for sharpness. For `n = 2` the only graph is a single
  edge, with `ε = 0`.
* In the variational forms of (a) and (b) the loop-free hypothesis is used only at the
  vertices involved. It is used globally, through `tr = 0`, in (c) and (d) and in all spectral
  forms.
-/

open Finset Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Graph

variable {w : ι → ι → ℝ} {lam κ ε : ℝ}

/-- The three moments of `s · 1_u − c`. -/
private theorem moments_indicator_sub (hsymm : ∀ u v, w u v = w v u) (u : ι) (s c : ℝ) :
    (∑ x, (∑ y, w x y) * (s * (if x = u then 1 else 0) - c) =
        s * (∑ y, w u y) - c * ∑ x, ∑ y, w x y) ∧
    (∑ x, ∑ y, w x y * (s * (if x = u then 1 else 0) - c) * (s * (if y = u then 1 else 0) - c) =
        s ^ 2 * w u u - 2 * s * c * (∑ y, w u y) + c ^ 2 * ∑ x, ∑ y, w x y) ∧
    (∑ x, (∑ y, w x y) * (s * (if x = u then 1 else 0) - c) ^ 2 =
        s ^ 2 * (∑ y, w u y) - 2 * s * c * (∑ y, w u y) + c ^ 2 * ∑ x, ∑ y, w x y) := by
  obtain ⟨e, he⟩ : ∃ e : ι → ℝ, e = fun x => if x = u then 1 else 0 := ⟨_, rfl⟩
  have he' : ∀ x, (if x = u then (1 : ℝ) else 0) = e x := fun x => by rw [he]
  simp only [he']
  have s0 : ∑ x, (∑ v, w x v) * e x = ∑ y, w u y := by rw [he]; simp
  have s1 : ∑ x, ∑ y, w x y * e x * e y = w u u := by rw [he]; simp
  have s2 : ∑ x, ∑ y, w x y * e x = ∑ y, w u y := by
    rw [← s0]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_mul]
  have s3 : ∑ x, ∑ y, w x y * e y = ∑ y, w u y := by
    rw [he]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl fun x _ => hsymm x u
  have hee : ∀ x, e x ^ 2 = e x := fun x => by simp only [he]; split_ifs <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · have e1 : ∀ x, (∑ v, w x v) * (s * e x - c) = s * ((∑ v, w x v) * e x) - c * ∑ v, w x v :=
      fun x => by ring
    simp only [e1, Finset.sum_sub_distrib, ← Finset.mul_sum, s0]
  · have e1 : ∀ x y, w x y * (s * e x - c) * (s * e y - c) =
        s ^ 2 * (w x y * e x * e y) - s * c * (w x y * e x) - s * c * (w x y * e y)
          + c ^ 2 * w x y := fun x y => by ring
    simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, s1, s2, s3]
    ring
  · have e1 : ∀ x, (∑ v, w x v) * (s * e x - c) ^ 2 =
        (s ^ 2 - 2 * s * c) * ((∑ v, w x v) * e x) + c ^ 2 * ∑ v, w x v := fun x => by
      have := hee x
      linear_combination (∑ v, w x v) * s ^ 2 * this
    simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, s0]
    ring

/-- The three moments of the two-point function `s · 1_u + t · 1_v`, `u ≠ v`. -/
private theorem moments_two_point (hsymm : ∀ u v, w u v = w v u) {u v : ι} (huv : u ≠ v)
    (s t : ℝ) :
    (∑ x, (∑ y, w x y) * ((if x = u then s else 0) + (if x = v then t else 0)) =
        s * (∑ y, w u y) + t * ∑ y, w v y) ∧
    (∑ x, ∑ y, w x y * ((if x = u then s else 0) + (if x = v then t else 0)) *
        ((if y = u then s else 0) + (if y = v then t else 0)) =
        s ^ 2 * w u u + 2 * s * t * w u v + t ^ 2 * w v v) ∧
    (∑ x, (∑ y, w x y) * ((if x = u then s else 0) + (if x = v then t else 0)) ^ 2 =
        s ^ 2 * (∑ y, w u y) + t ^ 2 * ∑ y, w v y) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  · simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hsymm v u]
    ring
  · have e1 : ∀ x, ((if x = u then s else 0) + (if x = v then t else 0)) ^ 2 =
        (if x = u then s ^ 2 else 0) + (if x = v then t ^ 2 else 0) := by
      intro x
      by_cases hxu : x = u
      · subst hxu; simp [huv]
      · by_cases hxv : x = v
        · subst hxv; simp [hxu]
        · simp [hxu, hxv]
    simp only [e1, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring

omit [DecidableEq ι] in
/-- A vertex `u` of positive degree without a loop has a neighbour `v ≠ u`. -/
theorem exists_ne_weight_pos_of_loop_eq_zero (hnn : ∀ u v, 0 ≤ w u v) {u : ι}
    (hloop : w u u = 0) (hu : 0 < ∑ v, w u v) : ∃ v, v ≠ u ∧ 0 < w u v := by
  obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu.ne'
  exact ⟨v, fun h => hv (h ▸ hloop), lt_of_le_of_ne (hnn u v) (Ne.symm hv)⟩

/-- With symmetric nonnegative weights, a vertex `u` of positive degree without a loop has a
neighbour of positive degree, so `deg u < vol`: `π(u) < 1`. -/
theorem deg_lt_vol_of_loop_eq_zero (hsymm : ∀ u v, w u v = w v u) (hnn : ∀ u v, 0 ≤ w u v)
    {u : ι} (hloop : w u u = 0) (hu : 0 < ∑ v, w u v) :
    ∑ y, w u y < ∑ x, ∑ y, w x y := by
  obtain ⟨v, hvu, hpos⟩ := exists_ne_weight_pos_of_loop_eq_zero hnn hloop hu
  have hdeg0 : ∀ x, 0 ≤ ∑ y, w x y := fun x => Finset.sum_nonneg fun y _ => hnn x y
  have hv : w u v ≤ ∑ y, w v y := by
    rw [hsymm u v]
    exact Finset.single_le_sum (f := fun y => w v y) (fun y _ => hnn v y) (Finset.mem_univ u)
  have hp : ∑ x ∈ {u, v}, (∑ y, w x y) = (∑ y, w u y) + ∑ y, w v y := Finset.sum_pair hvu.symm
  have h1 : ∑ x ∈ {u, v}, (∑ y, w x y) ≤ ∑ x, ∑ y, w x y :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => hdeg0 x
  linarith

/-- The ratio `π/(1 − π)` with `π = a/D`, cleared: `−(a/D)/(1 − a/D) = −a/(D − a)`. -/
private theorem neg_div_one_sub_div {a D : ℝ} (h : a < D) (hD : 0 < D) :
    -(a / D) / (1 - a / D) = -a / (D - a) := by
  have h1 : D - a ≠ 0 := by linarith
  field_simp

/-! ### (a) The vertex bound -/

/-- **(a), lower half, cleared of denominators.** If every walk eigenvalue of `w` is at least
`κ`, then `κ · (vol − deg u) ≤ −deg u` at every vertex `u` of positive degree without a loop. -/
theorem WalkSmallestEigenvalueGE.mul_vol_sub_deg_le (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (h : WalkSmallestEigenvalueGE w κ) {u : ι} (hloop : w u u = 0)
    (hu : 0 < ∑ v, w u v) :
    κ * ((∑ x, ∑ y, w x y) - ∑ y, w u y) ≤ -(∑ y, w u y) := by
  have hvol := deg_lt_vol_of_loop_eq_zero hsymm hnn hloop hu
  obtain ⟨-, hq, hn⟩ := moments_indicator_sub hsymm u (∑ x, ∑ y, w x y) (∑ y, w u y)
  have h1 := h fun x => (∑ x, ∑ y, w x y) * (if x = u then 1 else 0) - ∑ y, w u y
  rw [hq, hn, hloop] at h1
  obtain ⟨a, ha⟩ : ∃ a, a = ∑ y, w u y := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = ∑ x, ∑ y, w x y := ⟨_, rfl⟩
  rw [← ha, ← hD] at h1 ⊢
  rw [← ha, ← hD] at hvol
  rw [← ha] at hu
  have hD0 : 0 < D := by linarith
  have h2 : (D * a) * (κ * (D - a)) ≤ (D * a) * (-a) := by nlinarith
  exact le_of_mul_le_mul_left h2 (mul_pos hD0 hu)

/-- **(a), lower half**: `μ_n ≤ −π(u)/(1 − π(u))`, where `π(u) = deg u / vol`. -/
theorem WalkSmallestEigenvalueGE.le_neg_stationary_div (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (h : WalkSmallestEigenvalueGE w κ) {u : ι} (hloop : w u u = 0)
    (hu : 0 < ∑ v, w u v) :
    κ ≤ -((∑ y, w u y) / ∑ x, ∑ y, w x y) / (1 - (∑ y, w u y) / ∑ x, ∑ y, w x y) := by
  have hvol := deg_lt_vol_of_loop_eq_zero hsymm hnn hloop hu
  have h1 := h.mul_vol_sub_deg_le hsymm hnn hloop hu
  rw [neg_div_one_sub_div hvol (hu.trans hvol), le_div_iff₀ (by linarith)]
  exact h1

/-- **(a), upper half**: `−π(u)/(1 − π(u)) ≤ μ₂`, where `π(u) = deg u / vol`. -/
theorem WalkSecondEigenvalueLE.neg_stationary_div_le (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (h : WalkSecondEigenvalueLE w lam) {u : ι} (hloop : w u u = 0)
    (hu : 0 < ∑ v, w u v) :
    -((∑ y, w u y) / ∑ x, ∑ y, w x y) / (1 - (∑ y, w u y) / ∑ x, ∑ y, w x y) ≤ lam := by
  have hvol := deg_lt_vol_of_loop_eq_zero hsymm hnn hloop hu
  have h1 := h.neg_deg_le hsymm hnn hu
  rw [neg_div_one_sub_div hvol (hu.trans hvol), div_le_iff₀ (by linarith)]
  exact h1

/-! ### (b) The edge bound -/

/-- **(b), upper half, cleared of denominators**: `−2 w(u, v) ≤ lam · (deg u + deg v)`. This is
`WalkSecondEigenvalueLE.neg_two_mul_weight_le` with loops excluded only at `u` and `v`. -/
theorem WalkSecondEigenvalueLE.neg_two_mul_weight_le_of_loops (h : WalkSecondEigenvalueLE w lam)
    (hsymm : ∀ u v, w u v = w v u) {u v : ι} (huu : w u u = 0) (hvv : w v v = 0) (huv : u ≠ v)
    (hu : 0 < ∑ x, w u x) (hv : 0 < ∑ x, w v x) :
    -(2 * w u v) ≤ lam * ((∑ x, w u x) + ∑ x, w v x) := by
  obtain ⟨hm, hq, hn⟩ := moments_two_point hsymm huv (∑ x, w v x) (-(∑ x, w u x))
  have h1 := h _ (by rw [hm]; ring)
  rw [hq, hn, huu, hvv] at h1
  have h2 : ((∑ x, w u x) * ∑ x, w v x) * (-(2 * w u v)) ≤
      ((∑ x, w u x) * ∑ x, w v x) * (lam * ((∑ x, w u x) + ∑ x, w v x)) := by
    linarith
  exact le_of_mul_le_mul_left h2 (mul_pos hu hv)

/-- **(b), upper half**: `−2 w(u, v)/(deg u + deg v) ≤ μ₂`. -/
theorem WalkSecondEigenvalueLE.neg_two_mul_weight_div_le (h : WalkSecondEigenvalueLE w lam)
    (hsymm : ∀ u v, w u v = w v u) {u v : ι} (huu : w u u = 0) (hvv : w v v = 0) (huv : u ≠ v)
    (hu : 0 < ∑ x, w u x) (hv : 0 < ∑ x, w v x) :
    -(2 * w u v / ((∑ x, w u x) + ∑ x, w v x)) ≤ lam := by
  have h1 := h.neg_two_mul_weight_le_of_loops hsymm huu hvv huv hu hv
  rw [← neg_div, div_le_iff₀ (by linarith)]
  exact h1

/-- **(b), lower half, cleared of denominators** (the `2 × 2` compression):
`κ · √(deg u · deg v) ≤ −w(u, v)`. No sign condition on the weights is needed. -/
theorem WalkSmallestEigenvalueGE.mul_sqrt_le_neg_weight (h : WalkSmallestEigenvalueGE w κ)
    (hsymm : ∀ u v, w u v = w v u) {u v : ι} (huu : w u u = 0) (hvv : w v v = 0) (huv : u ≠ v)
    (hu : 0 < ∑ x, w u x) (hv : 0 < ∑ x, w v x) :
    κ * Real.sqrt ((∑ x, w u x) * ∑ x, w v x) ≤ -w u v := by
  obtain ⟨-, hq, hn⟩ := moments_two_point hsymm huv (Real.sqrt (∑ x, w v x))
    (-Real.sqrt (∑ x, w u x))
  have h1 := h fun x => (if x = u then Real.sqrt (∑ x, w v x) else 0) +
    (if x = v then -Real.sqrt (∑ x, w u x) else 0)
  rw [hq, hn, huu, hvv] at h1
  rw [neg_sq, Real.sq_sqrt hu.le, Real.sq_sqrt hv.le] at h1
  have hr : Real.sqrt ((∑ x, w u x) * ∑ x, w v x) =
      Real.sqrt (∑ x, w u x) * Real.sqrt (∑ x, w v x) := Real.sqrt_mul hu.le _
  have hr0 : 0 < Real.sqrt ((∑ x, w u x) * ∑ x, w v x) := Real.sqrt_pos.mpr (mul_pos hu hv)
  have hr2 : Real.sqrt ((∑ x, w u x) * ∑ x, w v x) ^ 2 = (∑ x, w u x) * ∑ x, w v x :=
    Real.sq_sqrt (mul_pos hu hv).le
  have e1 : (2 * Real.sqrt ((∑ x, w u x) * ∑ x, w v x)) *
      (κ * Real.sqrt ((∑ x, w u x) * ∑ x, w v x)) =
      κ * ((∑ x, w v x) * (∑ x, w u x) + (∑ x, w u x) * ∑ x, w v x) := by
    rw [mul_mul_mul_comm, ← sq, hr2]; ring
  have e2 : (2 * Real.sqrt ((∑ x, w u x) * ∑ x, w v x)) * (-w u v) =
      2 * Real.sqrt (∑ x, w v x) * -Real.sqrt (∑ x, w u x) * w u v := by
    rw [hr]; ring
  have h2 : (2 * Real.sqrt ((∑ x, w u x) * ∑ x, w v x)) *
      (κ * Real.sqrt ((∑ x, w u x) * ∑ x, w v x)) ≤
      (2 * Real.sqrt ((∑ x, w u x) * ∑ x, w v x)) * (-w u v) := by
    rw [e1, e2]
    linarith
  exact le_of_mul_le_mul_left h2 (by positivity)

/-- **(b), lower half** (the `2 × 2` compression): `μ_n ≤ −w(u, v)/√(deg u · deg v)`. -/
theorem WalkSmallestEigenvalueGE.le_neg_weight_div_sqrt (h : WalkSmallestEigenvalueGE w κ)
    (hsymm : ∀ u v, w u v = w v u) {u v : ι} (huu : w u u = 0) (hvv : w v v = 0) (huv : u ≠ v)
    (hu : 0 < ∑ x, w u x) (hv : 0 < ∑ x, w v x) :
    κ ≤ -(w u v / Real.sqrt ((∑ x, w u x) * ∑ x, w v x)) := by
  have h1 := h.mul_sqrt_le_neg_weight hsymm huu hvv huv hu hv
  rw [← neg_div, le_div_iff₀ (Real.sqrt_pos.mpr (mul_pos hu hv))]
  exact h1

/-- **The arithmetic–geometric mean step of (b)**: for `t ≥ 0` and `a, b > 0`,
`2t/(a + b) ≤ t/√(ab)`. -/
theorem two_mul_div_add_le_div_sqrt_mul {t a b : ℝ} (ht : 0 ≤ t) (ha : 0 < a) (hb : 0 < b) :
    2 * t / (a + b) ≤ t / Real.sqrt (a * b) := by
  have hr : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha.le _
  have hsa := Real.sq_sqrt ha.le
  have hsb := Real.sq_sqrt hb.le
  have hr0 : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr (mul_pos ha hb)
  rw [div_le_div_iff₀ (by linarith) hr0, hr]
  have : 2 * (Real.sqrt a * Real.sqrt b) ≤ a + b := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b)]
  nlinarith

/-! ### (c) The trace bound -/

/-- **The sum of the squared eigenvalues** of a real symmetric matrix is the sum of its squared
entries (the squared Frobenius norm). -/
theorem Matrix.IsHermitian.sum_eigenvalues_sq_eq_sum_sq {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    ∑ j, hA.eigenvalues j ^ 2 = ∑ u, ∑ v, A u v ^ 2 := by
  have h1 : ∀ j, hA.eigenvalues j ^ 2 = ∑ v, (A *ᵥ hA.eigvec j) v ^ 2 := by
    intro j
    have h := hA.eigvec_dotProduct_eigvec j j
    simp only [if_true, dotProduct] at h
    rw [hA.mulVec_eigvec j]
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    rw [show ∑ i, hA.eigvec j i ^ 2 = 1 by simpa [sq] using h, mul_one]
  have h2 : ∀ j v, (A *ᵥ hA.eigvec j) v = hA.coeff (A v) j := by
    intro j v
    change (fun k => A v k) ⬝ᵥ hA.eigvec j = hA.eigvec j ⬝ᵥ A v
    rw [dotProduct_comm]
  simp only [h1, h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [hA.sum_sq_coeff]
  simp [dotProduct, sq]

/-- **The convex step of (c).** If `x_j ≤ ε` for `j ∈ s` and `Σ_{j ∈ s} x_j = 0`, then every
`x_j ≥ −(|s| − 1) ε` and `Σ_{j ∈ s} x_j² ≤ |s| (|s| − 1) ε²`. -/
theorem Finset.sum_sq_le_of_le_of_sum_eq_zero {α : Type*} [DecidableEq α] (s : Finset α)
    (x : α → ℝ) {ε : ℝ} (hx : ∀ j ∈ s, x j ≤ ε) (hsum : ∑ j ∈ s, x j = 0) :
    (∀ j ∈ s, -(((#s : ℝ) - 1) * ε) ≤ x j) ∧
      ∑ j ∈ s, x j ^ 2 ≤ (#s : ℝ) * ((#s : ℝ) - 1) * ε ^ 2 := by
  have hlow : ∀ j ∈ s, -(((#s : ℝ) - 1) * ε) ≤ x j := by
    intro j hj
    have h1 := Finset.add_sum_erase s x hj
    have h2 : ∑ k ∈ s.erase j, x k ≤ #(s.erase j) • ε :=
      Finset.sum_le_card_nsmul _ _ _ fun k hk => hx k (Finset.mem_of_mem_erase hk)
    rw [nsmul_eq_mul, Finset.card_erase_of_mem hj, Nat.cast_sub (Finset.card_pos.mpr ⟨j, hj⟩),
      Nat.cast_one] at h2
    linarith
  refine ⟨hlow, ?_⟩
  have h3 : ∀ j ∈ s, x j ^ 2 ≤ ((#s : ℝ) - 1) * ε ^ 2 + (2 - (#s : ℝ)) * ε * x j := by
    intro j hj
    nlinarith [mul_nonneg (sub_nonneg.mpr (hx j hj)) (neg_le_iff_add_nonneg.mp (hlow j hj))]
  have h4 := Finset.sum_le_sum h3
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum, Finset.sum_const,
    nsmul_eq_mul] at h4
  linarith

omit [DecidableEq ι] in
/-- On the diagonal the symmetrised walk matrix vanishes when `w` has no loops. -/
theorem walkMatrix_apply_self_of_loop {w : ι → ι → ℝ} {u : ι} (hloop : w u u = 0) :
    walkMatrix w u u = 0 := by
  rw [walkMatrix_apply, hloop, zero_div]

omit [DecidableEq ι] in
/-- The squared entries of the symmetrised walk matrix: `N(u, v)² = w(u, v)²/(deg u · deg v)`. -/
theorem walkMatrix_apply_sq {w : ι → ι → ℝ} (hnn : ∀ u v, 0 ≤ w u v) (u v : ι) :
    walkMatrix w u v ^ 2 = w u v ^ 2 / ((∑ x, w u x) * ∑ x, w v x) := by
  rw [walkMatrix_apply, div_pow, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun x _ => hnn u x),
    Real.sq_sqrt (Finset.sum_nonneg fun x _ => hnn v x)]

omit [DecidableEq ι] in
/-- A weighted graph with no loops and every degree positive on a nonempty vertex type has at
least two vertices. -/
theorem nontrivial_of_deg_pos [Nonempty ι] {w : ι → ι → ℝ} (hnn : ∀ u v, 0 ≤ w u v)
    (hdiag : ∀ u, w u u = 0) (hdeg : ∀ u, 0 < ∑ v, w u v) : Nontrivial ι := by
  obtain ⟨u⟩ := ‹Nonempty ι›
  obtain ⟨v, hvu, -⟩ := exists_ne_weight_pos_of_loop_eq_zero hnn (hdiag u) (hdeg u)
  exact ⟨⟨v, u, hvu⟩⟩

/-- **The three spectral facts behind (c).** For symmetric nonnegative weights with no loops and
every degree positive, the symmetrised walk matrix has top eigenvalue `1` (at `topIndex`), trace
`0`, and squared Frobenius norm `Σ_{u,v} w(u,v)²/(deg u · deg v)`. -/
theorem walkMatrix_eigenvalues_facts [Nonempty ι] {w : ι → ι → ℝ} (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (hdiag : ∀ u, w u u = 0) (hdeg : ∀ u, 0 < ∑ v, w u v) :
    (walkMatrix_isHermitian hsymm).eigenvalues (Matrix.IsHermitian.topIndex ι) = 1 ∧
      ∑ j, (walkMatrix_isHermitian hsymm).eigenvalues j = 0 ∧
      ∑ j, (walkMatrix_isHermitian hsymm).eigenvalues j ^ 2 =
        ∑ u, ∑ v, w u v ^ 2 / ((∑ x, w u x) * ∑ x, w v x) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.IsHermitian.eigenvalues_topIndex, walkMatrix_largestEigenvalue hsymm hnn hdeg]
  · have h := (walkMatrix_isHermitian hsymm).trace_eq_sum_eigenvalues
    simp only [Matrix.trace, Matrix.diag, walkMatrix_apply_self_of_loop (hdiag _),
      Finset.sum_const_zero, RCLike.ofReal_real_eq_id, id] at h
    exact h.symm
  · rw [Matrix.IsHermitian.sum_eigenvalues_sq_eq_sum_sq]
    simp only [walkMatrix_apply_sq hnn]

/-- **The core of (c).** Let `w` be symmetric, nonnegative, without loops, with every degree
positive, on `n ≥ 2` vertices, and suppose `μ₂ ≤ ε − 1/(n − 1)`. Then `ε ≥ 0`, every eigenvalue
of the walk is at least `−1/(n − 1) − (n − 2) ε`, and the eigenvalues `μ_j` other than the top
one satisfy `Σ_j (μ_j + 1/(n − 1))² ≤ (n − 1)(n − 2) ε²`. -/
theorem WalkSecondEigenvalueLE.walkMatrix_core [Nontrivial ι] (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (hdiag : ∀ u, w u u = 0) (hdeg : ∀ u, 0 < ∑ v, w u v)
    (h : WalkSecondEigenvalueLE w (ε - 1 / ((Fintype.card ι : ℝ) - 1))) :
    0 ≤ ε ∧
      (∀ j, -(1 / ((Fintype.card ι : ℝ) - 1)) - ((Fintype.card ι : ℝ) - 2) * ε ≤
        (walkMatrix_isHermitian hsymm).eigenvalues j) ∧
      ∑ j ∈ univ.erase (Matrix.IsHermitian.topIndex ι),
          ((walkMatrix_isHermitian hsymm).eigenvalues j + 1 / ((Fintype.card ι : ℝ) - 1)) ^ 2 ≤
        ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε ^ 2 := by
  obtain ⟨htop, htr, -⟩ := walkMatrix_eigenvalues_facts hsymm hnn hdiag hdeg
  have h2 := (walkSecondEigenvalueLE_iff_secondEigenvalue_le hsymm hnn hdeg).mp h
  have hN : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.one_lt_card
  have hcard : ((#(univ.erase (Matrix.IsHermitian.topIndex ι)) : ℕ) : ℝ) =
      (Fintype.card ι : ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Fintype.card ι := ⟨_, rfl⟩
  rw [← hNdef] at hN hcard h2 ⊢
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (N - 1) := ⟨_, rfl⟩
  rw [← hc] at h2 ⊢
  have hN1 : N - 1 ≠ 0 := by linarith
  have hc1 : (N - 1) * c = 1 := by rw [hc]; field_simp
  have hc0 : 0 < c := by rw [hc]; exact div_pos one_pos (by linarith)
  have hx : ∀ j ∈ univ.erase (Matrix.IsHermitian.topIndex ι),
      (walkMatrix_isHermitian hsymm).eigenvalues j + c ≤ ε := fun j hj => by
    have := (walkMatrix_isHermitian hsymm).eigenvalues_le_secondEigenvalue
      (Finset.ne_of_mem_erase hj)
    linarith
  have hsum : ∑ j ∈ univ.erase (Matrix.IsHermitian.topIndex ι),
      ((walkMatrix_isHermitian hsymm).eigenvalues j + c) = 0 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard, hc1]
    have := Finset.add_sum_erase univ (walkMatrix_isHermitian hsymm).eigenvalues
      (mem_univ (Matrix.IsHermitian.topIndex ι))
    rw [htop, htr] at this
    linarith
  obtain ⟨hlow, hsq⟩ := Finset.sum_sq_le_of_le_of_sum_eq_zero _ _ hx hsum
  rw [hcard] at hlow hsq
  have hε : 0 ≤ ε := by
    have h1 := Finset.sum_le_card_nsmul _ _ _ hx
    rw [hsum, nsmul_eq_mul, hcard] at h1
    nlinarith
  refine ⟨hε, fun j => ?_, ?_⟩
  · by_cases hj : j = Matrix.IsHermitian.topIndex ι
    · rw [hj, htop]
      nlinarith
    · have := hlow j (mem_erase.mpr ⟨hj, mem_univ _⟩)
      linarith
  · calc _ ≤ (N - 1) * (N - 1 - 1) * ε ^ 2 := hsq
      _ = _ := by ring

/-- **(c), the lower end of the spectrum**: `μ_n ≥ −1/(n − 1) − (n − 2) ε` whenever
`μ₂ ≤ ε − 1/(n − 1)`. Stated variationally: the bound on `μ₂` gives a lower bound on every walk
eigenvalue. Here `n = |ι|`. No connectivity is needed, and `n ≥ 2` is automatic: a vertex of
positive degree without a loop has a neighbour. The empty vertex type is allowed; there both
predicates hold trivially. -/
theorem WalkSecondEigenvalueLE.walkSmallestEigenvalueGE_trace (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (hdiag : ∀ u, w u u = 0) (hdeg : ∀ u, 0 < ∑ v, w u v)
    (h : WalkSecondEigenvalueLE w (ε - 1 / ((Fintype.card ι : ℝ) - 1))) :
    WalkSmallestEigenvalueGE w
      (-(1 / ((Fintype.card ι : ℝ) - 1)) - ((Fintype.card ι : ℝ) - 2) * ε) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · intro f
    simp
  · have := nontrivial_of_deg_pos hnn hdiag hdeg
    exact (walkSmallestEigenvalueGE_iff_le_eigenvalues hsymm hdeg).mpr
      (h.walkMatrix_core hsymm hnn hdiag hdeg).2.1

/-- **(c), the trace identity**: the eigenvalues `μ_j` of the walk other than the top one
(`j ≠ topIndex`, where the eigenvalue is `1`) satisfy
`Σ_j (μ_j + 1/(n − 1))² = Σ_{u,v} w(u,v)²/(deg u · deg v) − n/(n − 1)`.
It combines `tr S = 0` (no loops) and `tr S² = Σ w²/(deg · deg)`. If the graph is disconnected,
`1` is a repeated eigenvalue and its other copies are among the `μ_j`. -/
theorem sum_erase_topIndex_walkMatrix_eigenvalues_add_sq [Nonempty ι]
    (hsymm : ∀ u v, w u v = w v u) (hnn : ∀ u v, 0 ≤ w u v) (hdiag : ∀ u, w u u = 0)
    (hdeg : ∀ u, 0 < ∑ v, w u v) :
    ∑ j ∈ univ.erase (Matrix.IsHermitian.topIndex ι),
        ((walkMatrix_isHermitian hsymm).eigenvalues j + 1 / ((Fintype.card ι : ℝ) - 1)) ^ 2 =
      ∑ u, ∑ v, w u v ^ 2 / ((∑ x, w u x) * ∑ x, w v x) -
        (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) := by
  have := nontrivial_of_deg_pos hnn hdiag hdeg
  obtain ⟨htop, htr, hsq⟩ := walkMatrix_eigenvalues_facts hsymm hnn hdiag hdeg
  have hN : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.one_lt_card
  have hsplit := Finset.add_sum_erase univ
    (fun j => ((walkMatrix_isHermitian hsymm).eigenvalues j + 1 / ((Fintype.card ι : ℝ) - 1)) ^ 2)
    (mem_univ (Matrix.IsHermitian.topIndex ι))
  simp only [htop] at hsplit
  have hall : ∑ j, ((walkMatrix_isHermitian hsymm).eigenvalues j +
      1 / ((Fintype.card ι : ℝ) - 1)) ^ 2 =
      ∑ j, (walkMatrix_isHermitian hsymm).eigenvalues j ^ 2 +
        2 * (1 / ((Fintype.card ι : ℝ) - 1)) * ∑ j, (walkMatrix_isHermitian hsymm).eigenvalues j +
        (Fintype.card ι : ℝ) * (1 / ((Fintype.card ι : ℝ) - 1)) ^ 2 := by
    have e : ∀ j, ((walkMatrix_isHermitian hsymm).eigenvalues j +
        1 / ((Fintype.card ι : ℝ) - 1)) ^ 2 =
        (walkMatrix_isHermitian hsymm).eigenvalues j ^ 2 +
          2 * (1 / ((Fintype.card ι : ℝ) - 1)) * (walkMatrix_isHermitian hsymm).eigenvalues j +
          (1 / ((Fintype.card ι : ℝ) - 1)) ^ 2 := fun j => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_univ,
      nsmul_eq_mul]
  rw [hall, htr, hsq] at hsplit
  have hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have e2 : ∑ j ∈ univ.erase (Matrix.IsHermitian.topIndex ι),
      ((walkMatrix_isHermitian hsymm).eigenvalues j + 1 / ((Fintype.card ι : ℝ) - 1)) ^ 2 =
      ∑ u, ∑ v, w u v ^ 2 / ((∑ x, w u x) * ∑ x, w v x) +
        (Fintype.card ι : ℝ) * (1 / ((Fintype.card ι : ℝ) - 1)) ^ 2 -
        (1 + 1 / ((Fintype.card ι : ℝ) - 1)) ^ 2 := by linarith
  rw [e2]
  field_simp
  ring

/-- **(c), the sum of squares**: if `μ₂ ≤ ε − 1/(n − 1)`, then
`Σ_{u,v} w(u,v)²/(deg u · deg v) − n/(n − 1) ≤ (n − 1)(n − 2) ε²`. By
`sum_erase_topIndex_walkMatrix_eigenvalues_add_sq` the left side is
`Σ_{j ≥ 2} (μ_j + 1/(n − 1))²`. The empty vertex type is allowed (both sides are then `0` and
`2 ε²`). -/
theorem WalkSecondEigenvalueLE.sum_sq_div_sub_le (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (hdiag : ∀ u, w u u = 0) (hdeg : ∀ u, 0 < ∑ v, w u v)
    (h : WalkSecondEigenvalueLE w (ε - 1 / ((Fintype.card ι : ℝ) - 1))) :
    ∑ u, ∑ v, w u v ^ 2 / ((∑ x, w u x) * ∑ x, w v x) -
        (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) ≤
      ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, Fintype.card_eq_zero, Nat.cast_zero]
    nlinarith [sq_nonneg ε]
  · have := nontrivial_of_deg_pos hnn hdiag hdeg
    rw [← sum_erase_topIndex_walkMatrix_eigenvalues_add_sq hsymm hnn hdiag hdeg]
    exact (h.walkMatrix_core hsymm hnn hdiag hdeg).2.2

/-! ### (d) Stability: degrees and edge weights -/

/-- **(d), upper degree bound**: if `μ₂ ≤ ε − 1/(n − 1)`, every vertex has
`π(u) ≤ (1 + (n − 1)(n − 2) ε)/(n + (n − 1)(n − 2) ε)`. -/
theorem WalkSecondEigenvalueLE.stationary_le (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (hdiag : ∀ u, w u u = 0) (hdeg : ∀ u, 0 < ∑ v, w u v)
    (h : WalkSecondEigenvalueLE w (ε - 1 / ((Fintype.card ι : ℝ) - 1))) (u : ι) :
    (∑ y, w u y) / ∑ x, ∑ y, w x y ≤
      (1 + ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε) /
        ((Fintype.card ι : ℝ) + ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε) := by
  have : Nonempty ι := ⟨u⟩
  have := nontrivial_of_deg_pos hnn hdiag hdeg
  obtain ⟨hε, -, -⟩ := h.walkMatrix_core hsymm hnn hdiag hdeg
  have hκ := (h.walkSmallestEigenvalueGE_trace hsymm hnn hdiag hdeg).mul_vol_sub_deg_le hsymm hnn
    (hdiag u) (hdeg u)
  have hvol := deg_lt_vol_of_loop_eq_zero hsymm hnn (hdiag u) (hdeg u)
  have hN : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.one_lt_card
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Fintype.card ι := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = ∑ y, w u y := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = ∑ x, ∑ y, w x y := ⟨_, rfl⟩
  rw [← hNdef] at hN hκ ⊢
  rw [← ha, ← hD] at hκ hvol ⊢
  have hu : 0 < a := ha ▸ hdeg u
  have hN1 : N - 1 ≠ 0 := by linarith
  have hc1 : (N - 1) * (1 / (N - 1)) = 1 := by field_simp
  have hM : 0 ≤ (N - 1) * (N - 2) * ε := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ N - 1) (by linarith : (0 : ℝ) ≤ N - 2)
    exact mul_nonneg this hε
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have h1 := mul_le_mul_of_nonneg_left hκ (by linarith : (0 : ℝ) ≤ N - 1)
  have e : (N - 1) * ((-(1 / (N - 1)) - (N - 2) * ε) * (D - a)) =
      -(1 + (N - 1) * (N - 2) * ε) * (D - a) := by
    linear_combination (-(D - a)) * hc1
  rw [e] at h1
  nlinarith

/-- **(d), upper edge bound**: if `μ₂ ≤ ε − 1/(n − 1)`, then for all `u, v`,
`w(u, v)/√(deg u · deg v) ≤ 1/(n − 1) + (n − 2) ε`. For `u = v` the left side is `0`. -/
theorem WalkSecondEigenvalueLE.weight_div_sqrt_le (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (hdiag : ∀ u, w u u = 0) (hdeg : ∀ u, 0 < ∑ v, w u v)
    (h : WalkSecondEigenvalueLE w (ε - 1 / ((Fintype.card ι : ℝ) - 1))) (u v : ι) :
    w u v / Real.sqrt ((∑ x, w u x) * ∑ x, w v x) ≤
      1 / ((Fintype.card ι : ℝ) - 1) + ((Fintype.card ι : ℝ) - 2) * ε := by
  have : Nonempty ι := ⟨u⟩
  have := nontrivial_of_deg_pos hnn hdiag hdeg
  obtain ⟨hε, -, -⟩ := h.walkMatrix_core hsymm hnn hdiag hdeg
  have hN : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.one_lt_card
  by_cases huv : u = v
  · subst huv
    rw [hdiag, zero_div]
    have : 0 < 1 / ((Fintype.card ι : ℝ) - 1) := div_pos one_pos (by linarith)
    nlinarith
  · have := (h.walkSmallestEigenvalueGE_trace hsymm hnn hdiag hdeg).le_neg_weight_div_sqrt hsymm
      (hdiag u) (hdiag v) huv (hdeg u) (hdeg v)
    linarith

omit [DecidableEq ι] in
/-- **(d), the comparison of the two edge quantities**: `2w(u,v)/(deg u + deg v) ≤
w(u,v)/√(deg u · deg v)` (arithmetic–geometric mean), for nonnegative weights and positive
degrees. -/
theorem two_mul_weight_div_le_weight_div_sqrt (hnn : ∀ u v, 0 ≤ w u v) {u v : ι}
    (hu : 0 < ∑ x, w u x) (hv : 0 < ∑ x, w v x) :
    2 * w u v / ((∑ x, w u x) + ∑ x, w v x) ≤ w u v / Real.sqrt ((∑ x, w u x) * ∑ x, w v x) :=
  two_mul_div_add_le_div_sqrt_mul (hnn u v) hu hv

/-- **(d), lower edge bound**: if `μ₂ ≤ ε − 1/(n − 1)`, then for distinct `u, v` of positive
degree without loops, `2w(u, v)/(deg u + deg v) ≥ 1/(n − 1) − ε`. It holds for every `ε`
(it is `WalkSecondEigenvalueLE.neg_two_mul_weight_div_le` rewritten) and is informative when
`ε < 1/(n − 1)`. -/
theorem WalkSecondEigenvalueLE.sub_le_two_mul_weight_div
    (h : WalkSecondEigenvalueLE w (ε - 1 / ((Fintype.card ι : ℝ) - 1)))
    (hsymm : ∀ u v, w u v = w v u) {u v : ι} (huu : w u u = 0) (hvv : w v v = 0) (huv : u ≠ v)
    (hu : 0 < ∑ x, w u x) (hv : 0 < ∑ x, w v x) :
    1 / ((Fintype.card ι : ℝ) - 1) - ε ≤ 2 * w u v / ((∑ x, w u x) + ∑ x, w v x) := by
  have := h.neg_two_mul_weight_div_le hsymm huu hvv huv hu hv
  linarith

/-- **(d), every pair is an edge**: if `μ₂ ≤ ε − 1/(n − 1)` with `ε < 1/(n − 1)` (that is,
`μ₂ < 0`), any two distinct vertices of positive degree without loops are joined by an edge of
positive weight. -/
theorem WalkSecondEigenvalueLE.weight_pos_of_lt
    (h : WalkSecondEigenvalueLE w (ε - 1 / ((Fintype.card ι : ℝ) - 1)))
    (hsymm : ∀ u v, w u v = w v u) {u v : ι} (huu : w u u = 0) (hvv : w v v = 0) (huv : u ≠ v)
    (hu : 0 < ∑ x, w u x) (hv : 0 < ∑ x, w v x) (hε : ε < 1 / ((Fintype.card ι : ℝ) - 1)) :
    0 < w u v := by
  have h1 := h.sub_le_two_mul_weight_div hsymm huu hvv huv hu hv
  by_contra hw
  rw [not_lt] at hw
  have : 2 * w u v / ((∑ x, w u x) + ∑ x, w v x) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  linarith

/-- **(d), lower degree bound**: if `μ₂ ≤ ε − 1/(n − 1)` and `ε ≤ n/(n − 1)` (that is,
`ε − 1/(n − 1) ≤ 1`), every vertex `u` of positive degree without a loop has
`π(u) ≥ (1 − (n − 1) ε)/(n − (n − 1) ε)`. The bound is positive exactly when `ε < 1/(n − 1)`.
The hypothesis on `ε` is needed: for `ε > n/(n − 1)` the right side exceeds `1`. It is
automatic when `ε − 1/(n − 1)` is the actual `μ₂`, since `μ₂ ≤ 1`. -/
theorem WalkSecondEigenvalueLE.le_stationary (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (h : WalkSecondEigenvalueLE w (ε - 1 / ((Fintype.card ι : ℝ) - 1)))
    {u : ι} (hloop : w u u = 0) (hu : 0 < ∑ v, w u v)
    (hε : ε ≤ (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) :
    (1 - ((Fintype.card ι : ℝ) - 1) * ε) / ((Fintype.card ι : ℝ) - ((Fintype.card ι : ℝ) - 1) * ε)
      ≤ (∑ y, w u y) / ∑ x, ∑ y, w x y := by
  obtain ⟨v, hvu, -⟩ := exists_ne_weight_pos_of_loop_eq_zero hnn hloop hu
  have : Nontrivial ι := ⟨⟨v, u, hvu⟩⟩
  have hN : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.one_lt_card
  have hvol := deg_lt_vol_of_loop_eq_zero hsymm hnn hloop hu
  have h1 := h.neg_deg_le hsymm hnn hu
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Fintype.card ι := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = ∑ y, w u y := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = ∑ x, ∑ y, w x y := ⟨_, rfl⟩
  rw [← hNdef] at hN h1 hε ⊢
  rw [← ha, ← hD] at h1 hvol ⊢
  rw [← ha] at hu
  have hN1 : N - 1 ≠ 0 := by linarith
  have hc1 : (N - 1) * (1 / (N - 1)) = 1 := by field_simp
  have hε' : (N - 1) * ε ≤ N := by
    rw [le_div_iff₀ (by linarith)] at hε
    linarith
  rcases (sub_nonneg.mpr hε').eq_or_lt with h0 | h0
  · rw [← h0, div_zero]
    exact div_nonneg hu.le (by linarith)
  · rw [div_le_div_iff₀ h0 (by linarith)]
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ N - 1)
    have e : (N - 1) * ((ε - 1 / (N - 1)) * (D - a)) = ((N - 1) * ε - 1) * (D - a) := by
      linear_combination (-(D - a)) * hc1
    rw [e] at h2
    nlinarith

end Graph

/-! ### The statement in spectral form

Here `μ₂` and `μ_n` are the second-largest and the smallest eigenvalue of the symmetrised walk
matrix `walkMatrix w`, which is similar to the random walk when every degree is positive. -/

section SpectralForm

variable {w : ι → ι → ℝ}

/-- The second eigenvalue `μ₂` of the walk satisfies its own variational bound. -/
theorem walkSecondEigenvalueLE_walkMatrix_secondEigenvalue [Nontrivial ι]
    (hsymm : ∀ u v, w u v = w v u) (hnn : ∀ u v, 0 ≤ w u v) (hdeg : ∀ u, 0 < ∑ v, w u v) :
    WalkSecondEigenvalueLE w (walkMatrix_isHermitian hsymm).secondEigenvalue :=
  (walkSecondEigenvalueLE_iff_secondEigenvalue_le hsymm hnn hdeg).mpr le_rfl

/-- The smallest eigenvalue `μ_n` of the walk is a lower bound for every walk eigenvalue. -/
theorem walkSmallestEigenvalueGE_walkMatrix_smallestEigenvalue [Nonempty ι]
    (hsymm : ∀ u v, w u v = w v u) (hdeg : ∀ u, 0 < ∑ v, w u v) :
    WalkSmallestEigenvalueGE w (walkMatrix_isHermitian hsymm).smallestEigenvalue :=
  (walkSmallestEigenvalueGE_iff_le_eigenvalues hsymm hdeg).mpr
    (walkMatrix_isHermitian hsymm).smallestEigenvalue_le_eigenvalues

/-- If `μ₂` is characterised variationally as `μ`, it is `μ`. -/
theorem walkMatrix_secondEigenvalue_eq_of_forall_iff [Nontrivial ι]
    (hsymm : ∀ u v, w u v = w v u) (hnn : ∀ u v, 0 ≤ w u v) (hdeg : ∀ u, 0 < ∑ v, w u v)
    {μ : ℝ} (h : ∀ lam, WalkSecondEigenvalueLE w lam ↔ μ ≤ lam) :
    (walkMatrix_isHermitian hsymm).secondEigenvalue = μ := by
  apply le_antisymm
  · exact (walkSecondEigenvalueLE_iff_secondEigenvalue_le hsymm hnn hdeg).mp ((h μ).mpr le_rfl)
  · exact (h _).mp (walkSecondEigenvalueLE_walkMatrix_secondEigenvalue hsymm hnn hdeg)

/-- If `μ_n` is characterised variationally as `μ`, it is `μ`. -/
theorem walkMatrix_smallestEigenvalue_eq_of_forall_iff [Nonempty ι]
    (hsymm : ∀ u v, w u v = w v u) (hdeg : ∀ u, 0 < ∑ v, w u v)
    {μ : ℝ} (h : ∀ κ, WalkSmallestEigenvalueGE w κ ↔ κ ≤ μ) :
    (walkMatrix_isHermitian hsymm).smallestEigenvalue = μ := by
  apply le_antisymm
  · exact (h _).mp (walkSmallestEigenvalueGE_walkMatrix_smallestEigenvalue hsymm hdeg)
  · have h1 := (walkSmallestEigenvalueGE_iff_le_eigenvalues hsymm hdeg).mp ((h μ).mpr le_rfl)
    rw [← (walkMatrix_isHermitian hsymm).eigenvalues_bottomIndex]
    exact h1 _

/-- **(a), spectral form.** Let `w` be symmetric, nonnegative, without loops and with every
degree positive, on at least two vertices. For every vertex `u`, with `π(u) = deg u / vol`,

  `μ_n ≤ −π(u)/(1 − π(u)) ≤ μ₂`.

Degenerate cases. `π(u) < 1` always holds here (`deg_lt_vol_of_loop_eq_zero`), so no
denominator vanishes. Connectivity is not assumed: for a disconnected `w`, `μ₂ = 1` and the upper
inequality is weak. `[Nontrivial ι]` is needed to name `μ₂`; with one vertex no `w` meets the
other hypotheses. Loops must be excluded: for `w` the identity matrix (a loop at every vertex and
nothing else) every walk eigenvalue is `1`, while `−π(u)/(1 − π(u)) = −1/(n − 1)`. Positive
degrees are needed for `walkMatrix` to be similar to the walk (see the docstring of
`walkMatrix`). -/
theorem walkMatrix_vertex_bound [Nontrivial ι] (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (hdiag : ∀ u, w u u = 0) (hdeg : ∀ u, 0 < ∑ v, w u v) (u : ι) :
    (walkMatrix_isHermitian hsymm).smallestEigenvalue ≤
        -((∑ y, w u y) / ∑ x, ∑ y, w x y) / (1 - (∑ y, w u y) / ∑ x, ∑ y, w x y) ∧
      -((∑ y, w u y) / ∑ x, ∑ y, w x y) / (1 - (∑ y, w u y) / ∑ x, ∑ y, w x y) ≤
        (walkMatrix_isHermitian hsymm).secondEigenvalue :=
  ⟨(walkSmallestEigenvalueGE_walkMatrix_smallestEigenvalue hsymm hdeg).le_neg_stationary_div
      hsymm hnn (hdiag u) (hdeg u),
    (walkSecondEigenvalueLE_walkMatrix_secondEigenvalue hsymm hnn hdeg).neg_stationary_div_le
      hsymm hnn (hdiag u) (hdeg u)⟩

/-- **(b), spectral form.** Under the hypotheses of `walkMatrix_vertex_bound`, for distinct
vertices `u, v`,

  `μ_n ≤ −w(u,v)/√(deg u · deg v) ≤ −2w(u,v)/(deg u + deg v) ≤ μ₂`.

The first inequality is the `2 × 2` compression of the walk to `{u, v}`; it is stronger than
the bound `μ_n ≤ −2w(u,v)/(deg u + deg v)`. The weight `w(u, v)` may be `0`, and then the chain
reads `μ_n ≤ 0 ≤ 0 ≤ μ₂`. For `u = v` the last inequality would read `0 ≤ μ₂`, which fails for
the complete graph, so `u ≠ v` is needed. The other degenerate cases are as in
`walkMatrix_vertex_bound`. -/
theorem walkMatrix_edge_bound [Nontrivial ι] (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (hdiag : ∀ u, w u u = 0) (hdeg : ∀ u, 0 < ∑ v, w u v) {u v : ι}
    (huv : u ≠ v) :
    (walkMatrix_isHermitian hsymm).smallestEigenvalue ≤
        -(w u v / Real.sqrt ((∑ x, w u x) * ∑ x, w v x)) ∧
      -(w u v / Real.sqrt ((∑ x, w u x) * ∑ x, w v x)) ≤
        -(2 * w u v / ((∑ x, w u x) + ∑ x, w v x)) ∧
      -(2 * w u v / ((∑ x, w u x) + ∑ x, w v x)) ≤
        (walkMatrix_isHermitian hsymm).secondEigenvalue :=
  ⟨(walkSmallestEigenvalueGE_walkMatrix_smallestEigenvalue hsymm hdeg).le_neg_weight_div_sqrt
      hsymm (hdiag u) (hdiag v) huv (hdeg u) (hdeg v),
    neg_le_neg (two_mul_weight_div_le_weight_div_sqrt hnn (hdeg u) (hdeg v)),
    (walkSecondEigenvalueLE_walkMatrix_secondEigenvalue hsymm hnn hdeg).neg_two_mul_weight_div_le
      hsymm (hdiag u) (hdiag v) huv (hdeg u) (hdeg v)⟩

/-- **(c), spectral form.** Under the hypotheses of `walkMatrix_vertex_bound`, let `n = |ι|`
and `ε = μ₂ + 1/(n − 1)`. Then `ε ≥ 0` (the trace bound), `μ_n ≥ −1/(n − 1) − (n − 2) ε`, and
the eigenvalues `μ_j` other than the top one (`j ≠ topIndex`) satisfy

  `Σ_j (μ_j + 1/(n − 1))² = Σ_{u,v} w(u,v)²/(deg u · deg v) − n/(n − 1)`
  `  ≤ (n − 1)(n − 2) ε²`.

Degenerate cases. For a disconnected `w` the eigenvalue `1` is repeated and its other copies are
among the `μ_j`; then `ε = n/(n − 1)` and everything still holds. For `n = 2` the hypotheses
force a single edge, `ε = 0`, and both bounds are equalities. Loops must be excluded: for the
all-ones matrix (`K_n` with a loop at every vertex) the left side of the identity is
`1/(n − 1)` and the right side is `−1/(n − 1)`. -/
theorem walkMatrix_trace_bound [Nontrivial ι] (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (hdiag : ∀ u, w u u = 0) (hdeg : ∀ u, 0 < ∑ v, w u v) {ε : ℝ}
    (hε : ε = (walkMatrix_isHermitian hsymm).secondEigenvalue + 1 / ((Fintype.card ι : ℝ) - 1)) :
    0 ≤ ε ∧
      -(1 / ((Fintype.card ι : ℝ) - 1)) - ((Fintype.card ι : ℝ) - 2) * ε ≤
        (walkMatrix_isHermitian hsymm).smallestEigenvalue ∧
      ∑ j ∈ univ.erase (Matrix.IsHermitian.topIndex ι),
          ((walkMatrix_isHermitian hsymm).eigenvalues j + 1 / ((Fintype.card ι : ℝ) - 1)) ^ 2 =
        ∑ u, ∑ v, w u v ^ 2 / ((∑ x, w u x) * ∑ x, w v x) -
          (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) ∧
      ∑ u, ∑ v, w u v ^ 2 / ((∑ x, w u x) * ∑ x, w v x) -
          (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) ≤
        ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε ^ 2 := by
  have h : WalkSecondEigenvalueLE w (ε - 1 / ((Fintype.card ι : ℝ) - 1)) := by
    rw [hε, add_sub_cancel_right]
    exact walkSecondEigenvalueLE_walkMatrix_secondEigenvalue hsymm hnn hdeg
  obtain ⟨h0, hlow, -⟩ := h.walkMatrix_core hsymm hnn hdiag hdeg
  refine ⟨h0, ?_, sum_erase_topIndex_walkMatrix_eigenvalues_add_sq hsymm hnn hdiag hdeg,
    h.sum_sq_div_sub_le hsymm hnn hdiag hdeg⟩
  rw [← (walkMatrix_isHermitian hsymm).eigenvalues_bottomIndex]
  exact hlow _

/-- **(d), spectral form: stability.** Under the hypotheses of `walkMatrix_vertex_bound`, let
`n = |ι|`, `ε = μ₂ + 1/(n − 1)` and `π(u) = deg u / vol`. Then for all vertices `u, v`:
* `π(u) ≤ (1 + (n − 1)(n − 2) ε)/(n + (n − 1)(n − 2) ε)`;
* `2w(u,v)/(deg u + deg v) ≤ w(u,v)/√(deg u · deg v) ≤ 1/(n − 1) + (n − 2) ε`;
* `π(u) ≥ (1 − (n − 1) ε)/(n − (n − 1) ε)`;
* `2w(u,v)/(deg u + deg v) ≥ 1/(n − 1) − ε` if `u ≠ v`;
* if `ε < 1/(n − 1)` (that is, `μ₂ < 0`), every pair `u ≠ v` carries positive weight.
Degenerate cases. The two lower bounds hold for every such `w`, with no condition on `ε`, and
are positive exactly when `ε < 1/(n − 1)`; the original statement assumed `ε < 1/(n − 1)` for
them. The denominator of the lower degree bound is `n − (n − 1) ε = (n − 1)(1 − μ₂)`, which
vanishes exactly when `μ₂ = 1` (a disconnected `w`); then the left side is `0` in Lean and the
bound is trivially true. The upper edge bound also holds for `u = v`, where `w(u, u) = 0`. For
`n = 2` everything is an equality with `ε = 0`. The hypotheses are those of
`walkMatrix_vertex_bound`. -/
theorem walkMatrix_stability [Nontrivial ι] (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (hdiag : ∀ u, w u u = 0) (hdeg : ∀ u, 0 < ∑ v, w u v) {ε : ℝ}
    (hε : ε = (walkMatrix_isHermitian hsymm).secondEigenvalue + 1 / ((Fintype.card ι : ℝ) - 1)) :
    (∀ u, (∑ y, w u y) / ∑ x, ∑ y, w x y ≤
      (1 + ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε) /
        ((Fintype.card ι : ℝ) + ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε)) ∧
    (∀ u v, 2 * w u v / ((∑ x, w u x) + ∑ x, w v x) ≤
        w u v / Real.sqrt ((∑ x, w u x) * ∑ x, w v x) ∧
      w u v / Real.sqrt ((∑ x, w u x) * ∑ x, w v x) ≤
        1 / ((Fintype.card ι : ℝ) - 1) + ((Fintype.card ι : ℝ) - 2) * ε) ∧
    (∀ u, (1 - ((Fintype.card ι : ℝ) - 1) * ε) /
        ((Fintype.card ι : ℝ) - ((Fintype.card ι : ℝ) - 1) * ε) ≤
      (∑ y, w u y) / ∑ x, ∑ y, w x y) ∧
    (∀ u v, u ≠ v →
      1 / ((Fintype.card ι : ℝ) - 1) - ε ≤ 2 * w u v / ((∑ x, w u x) + ∑ x, w v x)) ∧
    (ε < 1 / ((Fintype.card ι : ℝ) - 1) → ∀ u v, u ≠ v → 0 < w u v) := by
  have h : WalkSecondEigenvalueLE w (ε - 1 / ((Fintype.card ι : ℝ) - 1)) := by
    rw [hε, add_sub_cancel_right]
    exact walkSecondEigenvalueLE_walkMatrix_secondEigenvalue hsymm hnn hdeg
  have hN : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.one_lt_card
  have hε1 : ε ≤ (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) := by
    have h2 := (walkMatrix_isHermitian hsymm).secondEigenvalue_le_largestEigenvalue
    rw [walkMatrix_largestEigenvalue hsymm hnn hdeg] at h2
    have hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
    have e : (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) =
        1 + 1 / ((Fintype.card ι : ℝ) - 1) := by field_simp; ring
    rw [e, hε]
    linarith
  refine ⟨fun u => h.stationary_le hsymm hnn hdiag hdeg u, fun u v =>
    ⟨two_mul_weight_div_le_weight_div_sqrt hnn (hdeg u) (hdeg v),
      h.weight_div_sqrt_le hsymm hnn hdiag hdeg u v⟩,
    fun u => h.le_stationary hsymm hnn (hdiag u) (hdeg u) hε1,
    fun u v huv => h.sub_le_two_mul_weight_div hsymm (hdiag u) (hdiag v) huv (hdeg u) (hdeg v),
    fun hlt u v huv =>
      h.weight_pos_of_lt hsymm (hdiag u) (hdiag v) huv (hdeg u) (hdeg v) hlt⟩

end SpectralForm

/-! ### Sharpness: the extremal families -/

section Families

/-- The weight `β` on the pairs of distinct vertices containing `o`, `α` on the other pairs of
distinct vertices, and `0` on the diagonal. -/
def starWeight (o : ι) (α β : ℝ) (x y : ι) : ℝ :=
  if x = y then 0 else if x = o ∨ y = o then β else α

omit [Fintype ι] in
/-- `starWeight` is symmetric. -/
theorem starWeight_symm (o : ι) (α β : ℝ) (x y : ι) :
    starWeight o α β x y = starWeight o α β y x := by
  unfold starWeight
  by_cases hxy : x = y
  · simp [hxy]
  · rw [if_neg hxy, if_neg (Ne.symm hxy)]
    simp only [or_comm]

omit [Fintype ι] in
/-- `starWeight` has no loops. -/
theorem starWeight_self (o : ι) (α β : ℝ) (x : ι) : starWeight o α β x x = 0 := by
  simp [starWeight]

omit [Fintype ι] in
/-- `starWeight` is nonnegative when `α, β ≥ 0`. -/
theorem starWeight_nonneg (o : ι) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (x y : ι) :
    0 ≤ starWeight o α β x y := by
  unfold starWeight
  split_ifs
  exacts [le_rfl, hβ, hα]

omit [Fintype ι] in
/-- At `α = β = 1` the vertex family is the complete graph `K_n` with unit weights. -/
theorem starWeight_one_one (o : ι) (x y : ι) :
    starWeight o 1 1 x y = if x = y then 0 else 1 := by
  unfold starWeight
  split_ifs <;> rfl

/-- The row action of `starWeight`. -/
theorem sum_starWeight_mul (o : ι) (α β : ℝ) (x : ι) (g : ι → ℝ) :
    ∑ y, starWeight o α β x y * g y =
      α * ((∑ y, g y) - g x) + (β - α) * ((if x = o then 1 else 0) * (∑ y, g y) + g o) -
        2 * (β - α) * (if x = o then g x else 0) := by
  have e : ∀ y, starWeight o α β x y * g y =
      α * g y - α * (if x = y then g y else 0) + (β - α) * (if x = o then 1 else 0) * g y +
        (β - α) * (if y = o then g y else 0) -
        2 * (β - α) * (if x = o then (if x = y then g y else 0) else 0) := by
    intro y
    unfold starWeight
    by_cases hxy : x = y
    · subst hxy
      by_cases hx : x = o
      · simp [hx]
        ring
      · simp [hx]
    · by_cases hx : x = o
      · subst hx
        simp [hxy, Ne.symm hxy]
        ring
      · by_cases hy : y = o
        · simp [hx, hy]
          ring
        · simp [hxy, hx, hy]
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> simp <;> ring

/-- The degrees of `starWeight`. -/
theorem sum_starWeight (o : ι) (α β : ℝ) (x : ι) :
    ∑ y, starWeight o α β x y =
      ((Fintype.card ι : ℝ) - 2) * α + β +
        ((Fintype.card ι : ℝ) - 2) * (β - α) * (if x = o then 1 else 0) := by
  have h := sum_starWeight_mul o α β x (fun _ => 1)
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [h]
  split_ifs <;> ring

/-- The quadratic form of `starWeight`. -/
theorem sum_sum_starWeight_mul_mul (o : ι) (α β : ℝ) (f : ι → ℝ) :
    ∑ x, ∑ y, starWeight o α β x y * f x * f y =
      α * ((∑ x, f x) ^ 2 - ∑ x, f x ^ 2) + 2 * (β - α) * f o * (∑ x, f x) -
        2 * (β - α) * f o ^ 2 := by
  have e : ∀ x, ∑ y, starWeight o α β x y * f x * f y =
      α * (∑ y, f y) * f x - α * f x ^ 2 + (β - α) * (∑ y, f y) * (if x = o then f x else 0) +
        (β - α) * f o * f x - 2 * (β - α) * (if x = o then f x ^ 2 else 0) := by
    intro x
    have h1 : ∑ y, starWeight o α β x y * f x * f y = f x * ∑ y, starWeight o α β x y * f y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [h1, sum_starWeight_mul]
    split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The degree-weighted mean and norm of `starWeight`. -/
theorem sum_starWeight_mul_moments (o : ι) (α β : ℝ) (f : ι → ℝ) :
    ∑ x, (∑ y, starWeight o α β x y) * f x =
        (((Fintype.card ι : ℝ) - 2) * α + β) * (∑ x, f x) +
          ((Fintype.card ι : ℝ) - 2) * (β - α) * f o ∧
      ∑ x, (∑ y, starWeight o α β x y) * f x ^ 2 =
        (((Fintype.card ι : ℝ) - 2) * α + β) * (∑ x, f x ^ 2) +
          ((Fintype.card ι : ℝ) - 2) * (β - α) * f o ^ 2 := by
  constructor
  · have e : ∀ x, (∑ y, starWeight o α β x y) * f x =
        (((Fintype.card ι : ℝ) - 2) * α + β) * f x +
          ((Fintype.card ι : ℝ) - 2) * (β - α) * (if x = o then f x else 0) := by
      intro x; rw [sum_starWeight]; split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  · have e : ∀ x, (∑ y, starWeight o α β x y) * f x ^ 2 =
        (((Fintype.card ι : ℝ) - 2) * α + β) * f x ^ 2 +
          ((Fintype.card ι : ℝ) - 2) * (β - α) * (if x = o then f x ^ 2 else 0) := by
      intro x; rw [sum_starWeight]; split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]

/-- The real-arithmetic core of the vertex family: with `m = a + n − 2`, `R` the sum and `U` the
sum of squares of `f` off `o`, and `p = f(o)`. -/
private theorem star_quadratic_le {N a lam p R U : ℝ} (hN : 2 ≤ N) (ha : 0 < a)
    (h1 : 0 ≤ 1 + lam * (a + N - 2)) (h2 : 0 ≤ a + lam * (a + N - 2))
    (hCS : R ^ 2 ≤ (N - 1) * U) (hmean : (a + N - 2) * R + (N - 1) * a * p = 0) :
    2 * a * p * R + R ^ 2 - U ≤ lam * ((a + N - 2) * U + (N - 1) * a * p ^ 2) := by
  have key : (N - 1) * a * ((2 * a * p * R + R ^ 2 - U) -
      lam * ((a + N - 2) * U + (N - 1) * a * p ^ 2)) =
      -(a * (1 + lam * (a + N - 2))) * ((N - 1) * U - R ^ 2) -
        (2 * a + N - 2) * (a + lam * (a + N - 2)) * R ^ 2 +
        ((a + N - 2) * R + (N - 1) * a * p) *
          (2 * a * R - lam * ((N - 1) * a * p - (a + N - 2) * R)) := by ring
  rw [hmean, zero_mul, add_zero] at key
  have hle : (N - 1) * a * ((2 * a * p * R + R ^ 2 - U) -
      lam * ((a + N - 2) * U + (N - 1) * a * p ^ 2)) ≤ 0 := by
    rw [key]
    have t1 := mul_nonneg (mul_nonneg ha.le h1) (sub_nonneg.mpr hCS)
    have t2 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * a + N - 2) h2) (sq_nonneg R)
    linarith
  have hpos : 0 < (N - 1) * a := mul_pos (by linarith) ha
  by_contra hc
  rw [not_le] at hc
  have := mul_pos hpos (sub_pos.mpr hc)
  linarith

/-- Cauchy–Schwarz off one vertex: `(Σ_{x ≠ o} f x)² ≤ (n − 1) Σ_{x ≠ o} f(x)²`. -/
private theorem sq_sum_sub_le (o : ι) (f : ι → ℝ) :
    ((∑ x, f x) - f o) ^ 2 ≤ ((Fintype.card ι : ℝ) - 1) * ((∑ x, f x ^ 2) - f o ^ 2) := by
  have : Nonempty ι := ⟨o⟩
  have h := sq_sum_le_card_mul_sum_sq (s := univ.erase o) (f := f)
  rw [Finset.sum_erase_eq_sub (mem_univ o), Finset.sum_erase_eq_sub (f := fun x => f x ^ 2)
    (mem_univ o), card_erase_of_mem (mem_univ o), card_univ, Nat.cast_sub Fintype.card_pos,
    Nat.cast_one] at h
  exact h

/-- **The second eigenvalue of the vertex family is at most `lam`** when
`lam ≥ max(−a/m, −1/m)`, `m = a + n − 2`, for `starWeight o 1 a` (`w(o, x) = a`, all other
weights `1`) on `n ≥ 2` vertices with `a > 0`. -/
theorem walkSecondEigenvalueLE_starWeight (hN : 2 ≤ Fintype.card ι) (o : ι) {a lam : ℝ}
    (ha : 0 < a) (h1 : 0 ≤ 1 + lam * (a + Fintype.card ι - 2))
    (h2 : 0 ≤ a + lam * (a + Fintype.card ι - 2)) :
    WalkSecondEigenvalueLE (starWeight o 1 a) lam := by
  intro f hf
  obtain ⟨hm, hn⟩ := sum_starWeight_mul_moments o 1 a f
  rw [hm] at hf
  rw [sum_sum_starWeight_mul_mul, hn]
  have hNr : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have := star_quadratic_le hNr ha h1 h2 (sq_sum_sub_le o f) (p := f o)
    (by linear_combination hf)
  linarith

/-- The degree of `o`, the degree of any other vertex, and the volume of the vertex family. -/
theorem starWeight_degrees (o : ι) (α β : ℝ) :
    (∑ y, starWeight o α β o y = ((Fintype.card ι : ℝ) - 1) * β) ∧
      (∀ x, x ≠ o → ∑ y, starWeight o α β x y = ((Fintype.card ι : ℝ) - 2) * α + β) ∧
      ∑ x, ∑ y, starWeight o α β x y =
        ((Fintype.card ι : ℝ) - 1) * (((Fintype.card ι : ℝ) - 2) * α + 2 * β) := by
  refine ⟨?_, fun x hx => ?_, ?_⟩
  · rw [sum_starWeight, if_pos rfl]; ring
  · rw [sum_starWeight, if_neg hx]; ring
  · have h := (sum_starWeight_mul_moments o α β (fun _ => 1)).1
    simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    rw [h]; ring

/-- **The light vertex family has `μ₂ = −a/(a + n − 2)` exactly**: for `0 < a ≤ 1` and `n ≥ 2`,
`WalkSecondEigenvalueLE (starWeight o 1 a) lam ↔ −a/(a + n − 2) ≤ lam`. The test function is
`−(a + n − 2)` at `o` and `a` elsewhere. -/
theorem walkSecondEigenvalueLE_starWeight_iff_of_le_one (hN : 2 ≤ Fintype.card ι) (o : ι)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (lam : ℝ) :
    WalkSecondEigenvalueLE (starWeight o 1 a) lam ↔
      -(a / (a + Fintype.card ι - 2)) ≤ lam := by
  have hNr : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have hm : 0 < a + Fintype.card ι - 2 := by linarith
  rw [← neg_div, div_le_iff₀ hm]
  constructor
  · intro h
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * a + Fintype.card ι - 2 := ⟨_, rfl⟩
    have hS : ∑ x, (a - (if x = o then c else 0)) = Fintype.card ι * a - c := by
      simp [Finset.sum_sub_distrib]
    have hT : ∑ x, (a - (if x = o then c else 0)) ^ 2 =
        Fintype.card ι * a ^ 2 - 2 * a * c + c ^ 2 := by
      have e : ∀ x, (a - (if x = o then c else 0)) ^ 2 =
          a ^ 2 - (if x = o then 2 * a * c - c ^ 2 else 0) := fun x => by split_ifs <;> ring
      simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    have hp : (a - (if o = o then c else 0)) = a - c := by simp
    obtain ⟨hm1, hn1⟩ := sum_starWeight_mul_moments o 1 a fun x => a - (if x = o then c else 0)
    have h1 := h (fun x => a - (if x = o then c else 0)) (by rw [hm1, hS, hp, hc]; ring)
    rw [sum_sum_starWeight_mul_mul, hn1, hS, hT, hp, hc] at h1
    have hpos : 0 < ((Fintype.card ι : ℝ) - 1) * a * (2 * a + Fintype.card ι - 2) :=
      mul_pos (mul_pos (by linarith) ha0) (by linarith)
    have e1 : ((Fintype.card ι : ℝ) - 1) * a * (2 * a + Fintype.card ι - 2) * (-a) =
        1 * (((Fintype.card ι : ℝ) * a - (2 * a + Fintype.card ι - 2)) ^ 2 -
          ((Fintype.card ι : ℝ) * a ^ 2 - 2 * a * (2 * a + Fintype.card ι - 2) +
            (2 * a + Fintype.card ι - 2) ^ 2)) +
        2 * (a - 1) * (a - (2 * a + Fintype.card ι - 2)) *
          ((Fintype.card ι : ℝ) * a - (2 * a + Fintype.card ι - 2)) -
        2 * (a - 1) * (a - (2 * a + Fintype.card ι - 2)) ^ 2 := by ring
    have e2 : ((Fintype.card ι : ℝ) - 1) * a * (2 * a + Fintype.card ι - 2) *
        (lam * (a + Fintype.card ι - 2)) =
        lam * ((((Fintype.card ι : ℝ) - 2) * 1 + a) *
            ((Fintype.card ι : ℝ) * a ^ 2 - 2 * a * (2 * a + Fintype.card ι - 2) +
              (2 * a + Fintype.card ι - 2) ^ 2) +
          ((Fintype.card ι : ℝ) - 2) * (a - 1) * (a - (2 * a + Fintype.card ι - 2)) ^ 2) := by
      ring
    have h2 : ((Fintype.card ι : ℝ) - 1) * a * (2 * a + Fintype.card ι - 2) * (-a) ≤
        ((Fintype.card ι : ℝ) - 1) * a * (2 * a + Fintype.card ι - 2) *
          (lam * (a + Fintype.card ι - 2)) := by
      rw [e1, e2]; exact h1
    exact le_of_mul_le_mul_left h2 hpos
  · intro h
    refine walkSecondEigenvalueLE_starWeight hN o ha0 ?_ (by linarith)
    nlinarith

/-- **The heavy vertex family has `μ₂ = −1/(a + n − 2)` exactly**: for `a ≥ 1` and `n ≥ 3`,
`WalkSecondEigenvalueLE (starWeight o 1 a) lam ↔ −1/(a + n − 2) ≤ lam`. The test function is
`1_x − 1_y` for two vertices `x, y ≠ o`, which needs `n ≥ 3`. -/
theorem walkSecondEigenvalueLE_starWeight_iff_of_one_le (hN : 3 ≤ Fintype.card ι) (o : ι)
    {a : ℝ} (ha1 : 1 ≤ a) (lam : ℝ) :
    WalkSecondEigenvalueLE (starWeight o 1 a) lam ↔
      -(1 / (a + Fintype.card ι - 2)) ≤ lam := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have hm : 0 < a + Fintype.card ι - 2 := by linarith
  rw [← neg_div, div_le_iff₀ hm]
  constructor
  · intro h
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp
      (by rw [card_erase_of_mem (mem_univ o), card_univ]; omega : 1 < #(univ.erase o))
    have hxo := Finset.ne_of_mem_erase hx
    have hyo := Finset.ne_of_mem_erase hy
    obtain ⟨hm1, hq1, hn1⟩ := moments_two_point (starWeight_symm o 1 a) hxy 1 (-1)
    obtain ⟨-, hdeg, -⟩ := starWeight_degrees (ι := ι) o 1 a
    have h1 := h _ (by rw [hm1, hdeg x hxo, hdeg y hyo]; ring)
    rw [hq1, hn1, hdeg x hxo, hdeg y hyo, starWeight_self, starWeight_self] at h1
    have hw : starWeight o 1 a x y = 1 := by
      simp [starWeight, hxy, hxo, hyo]
    rw [hw] at h1
    nlinarith
  · intro h
    exact walkSecondEigenvalueLE_starWeight (by omega) o (by linarith) (by linarith)
      (by nlinarith)

/-- The vertex family has every degree positive, for `a > 0` and `n ≥ 2`. -/
theorem starWeight_deg_pos (hN : 2 ≤ Fintype.card ι) (o : ι) {a : ℝ} (ha : 0 < a) (x : ι) :
    0 < ∑ y, starWeight o 1 a x y := by
  have hNr : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  obtain ⟨h0, h1, -⟩ := starWeight_degrees (ι := ι) o 1 a
  by_cases hx : x = o
  · rw [hx, h0]; exact mul_pos (by linarith) ha
  · rw [h1 x hx]; linarith

/-- The stationary probability of `o` in the vertex family is `a/(2a + n − 2)`. -/
theorem starWeight_stationary (hN : 2 ≤ Fintype.card ι) (o : ι) {a : ℝ} (ha : 0 < a) :
    (∑ y, starWeight o 1 a o y) / ∑ x, ∑ y, starWeight o 1 a x y =
      a / (2 * a + Fintype.card ι - 2) := by
  have hNr : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  obtain ⟨h0, -, hv⟩ := starWeight_degrees (ι := ι) o 1 a
  rw [h0, hv]
  have h1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have h2 : 2 * a + (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith
  have h3 : ((Fintype.card ι : ℝ) - 2) * 1 + 2 * a ≠ 0 := by linarith
  field_simp
  ring

/-- **Sharpness of the lower degree bound** (the light vertex family). For `0 < a ≤ 1` on
`n ≥ 2` vertices, `starWeight o 1 a` (`w(o, x) = a`, all other weights `1`) has
`μ₂ = ε − 1/(n − 1)` exactly, with `ε = 1/(n − 1) − a/(a + n − 2) ∈ [0, 1/(n − 1))`, and the
vertex `o` attains `π(o) = (1 − (n − 1) ε)/(n − (n − 1) ε)`. At `a = 1` it is `K_n` and `ε = 0`. -/
theorem starWeight_le_stationary_sharp (hN : 2 ≤ Fintype.card ι) (o : ι) {a ε : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hε : ε = 1 / ((Fintype.card ι : ℝ) - 1) - a / (a + Fintype.card ι - 2)) :
    (∀ lam, WalkSecondEigenvalueLE (starWeight o 1 a) lam ↔
      ε - 1 / ((Fintype.card ι : ℝ) - 1) ≤ lam) ∧
    (∑ y, starWeight o 1 a o y) / ∑ x, ∑ y, starWeight o 1 a x y =
      (1 - ((Fintype.card ι : ℝ) - 1) * ε) /
        ((Fintype.card ι : ℝ) - ((Fintype.card ι : ℝ) - 1) * ε) := by
  have hNr : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have e : ε - 1 / ((Fintype.card ι : ℝ) - 1) = -(a / (a + Fintype.card ι - 2)) := by
    rw [hε]; ring
  refine ⟨fun lam => ?_, ?_⟩
  · rw [e]
    exact walkSecondEigenvalueLE_starWeight_iff_of_le_one hN o ha0 ha1 lam
  rw [starWeight_stationary hN o ha0]
  have h1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have h2 : a + (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith
  have h3 : 2 * a + (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith
  have hX : 1 - ((Fintype.card ι : ℝ) - 1) * ε =
      ((Fintype.card ι : ℝ) - 1) * a / (a + Fintype.card ι - 2) := by
    rw [hε]; field_simp; ring
  have hY : (Fintype.card ι : ℝ) - ((Fintype.card ι : ℝ) - 1) * ε =
      ((Fintype.card ι : ℝ) - 1) * (2 * a + Fintype.card ι - 2) / (a + Fintype.card ι - 2) := by
    rw [hε]; field_simp; ring
  rw [hX, hY]
  field_simp

/-- **Sharpness of the upper degree bound** (the heavy vertex family). For `a ≥ 1` on `n ≥ 3`
vertices, `starWeight o 1 a` has `μ₂ = ε − 1/(n − 1)` exactly, with
`ε = (a − 1)/((n − 1)(a + n − 2)) ∈ [0, 1/(n − 1))`, and the vertex `o` attains
`π(o) = (1 + (n − 1)(n − 2) ε)/(n + (n − 1)(n − 2) ε)`. At `a = 1` it is `K_n` and `ε = 0`. -/
theorem starWeight_stationary_le_sharp (hN : 3 ≤ Fintype.card ι) (o : ι) {a ε : ℝ}
    (ha1 : 1 ≤ a)
    (hε : ε = (a - 1) / (((Fintype.card ι : ℝ) - 1) * (a + Fintype.card ι - 2))) :
    (∀ lam, WalkSecondEigenvalueLE (starWeight o 1 a) lam ↔
      ε - 1 / ((Fintype.card ι : ℝ) - 1) ≤ lam) ∧
    (∑ y, starWeight o 1 a o y) / ∑ x, ∑ y, starWeight o 1 a x y =
      (1 + ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε) /
        ((Fintype.card ι : ℝ) + ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε) := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have h1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have h2 : a + (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith
  have h3 : 2 * a + (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith
  have e : ε - 1 / ((Fintype.card ι : ℝ) - 1) = -(1 / (a + Fintype.card ι - 2)) := by
    rw [hε]; field_simp; ring
  refine ⟨fun lam => ?_, ?_⟩
  · rw [e]
    exact walkSecondEigenvalueLE_starWeight_iff_of_one_le hN o ha1 lam
  rw [starWeight_stationary (by omega) o (by linarith)]
  have hX : 1 + ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε =
      a * ((Fintype.card ι : ℝ) - 1) / (a + Fintype.card ι - 2) := by
    rw [hε]; field_simp; ring
  have hY : (Fintype.card ι : ℝ) + ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε =
      ((Fintype.card ι : ℝ) - 1) * (2 * a + Fintype.card ι - 2) / (a + Fintype.card ι - 2) := by
    rw [hε]; field_simp; ring
  rw [hX, hY]
  field_simp

/-- `w(u,v)²/(deg u · deg v)` for the vertex family is again a vertex-family weight. -/
private theorem starWeight_sq_div (hN : 2 ≤ Fintype.card ι) (o : ι) {a : ℝ} (ha : 0 < a)
    (x y : ι) :
    starWeight o 1 a x y ^ 2 / ((∑ z, starWeight o 1 a x z) * ∑ z, starWeight o 1 a y z) =
      starWeight o (1 / (a + Fintype.card ι - 2) ^ 2)
        (a / (((Fintype.card ι : ℝ) - 1) * (a + Fintype.card ι - 2))) x y := by
  have hNr : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have h1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have h2 : a + (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith
  obtain ⟨d0, d1, -⟩ := starWeight_degrees (ι := ι) o 1 a
  have d1' : ∀ x, x ≠ o → ∑ y, starWeight o 1 a x y = a + Fintype.card ι - 2 := fun x hx => by
    rw [d1 x hx]; ring
  by_cases hxy : x = y
  · subst hxy; simp [starWeight]
  · by_cases hx : x = o
    · subst hx
      rw [d0, d1' y (Ne.symm hxy)]
      simp only [starWeight, if_neg hxy, true_or, if_true]
      field_simp
    · by_cases hy : y = o
      · subst hy
        rw [d0, d1' x hx]
        simp only [starWeight, if_neg hxy, or_true, if_true]
        field_simp
      · rw [d1' x hx, d1' y hy]
        simp only [starWeight, if_neg hxy, hx, hy, or_false, if_false]
        field_simp

/-- **Equality in (c) for the heavy vertex family.** For `a ≥ 1` on `n ≥ 3` vertices, with
`ε = (a − 1)/((n − 1)(a + n − 2))` (so `μ₂ = ε − 1/(n − 1)` by
`starWeight_stationary_le_sharp`), the smallest walk eigenvalue is exactly
`−1/(n − 1) − (n − 2) ε = −a/(a + n − 2)`, and
`Σ_{u,v} w(u,v)²/(deg u · deg v) − n/(n − 1) = (n − 1)(n − 2) ε²`: both halves of (c) are
equalities. -/
theorem starWeight_trace_bound_eq (hN : 3 ≤ Fintype.card ι) (o : ι) {a ε : ℝ} (ha1 : 1 ≤ a)
    (hε : ε = (a - 1) / (((Fintype.card ι : ℝ) - 1) * (a + Fintype.card ι - 2))) :
    (∀ κ, WalkSmallestEigenvalueGE (starWeight o 1 a) κ ↔
      κ ≤ -(1 / ((Fintype.card ι : ℝ) - 1)) - ((Fintype.card ι : ℝ) - 2) * ε) ∧
    ∑ u, ∑ v, starWeight o 1 a u v ^ 2 /
        ((∑ x, starWeight o 1 a u x) * ∑ x, starWeight o 1 a v x) -
        (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) =
      ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε ^ 2 := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have h1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have h2 : a + (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith
  have h3 : 2 * a + (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith
  have ha : 0 < a := by linarith
  have hsymm := starWeight_symm (ι := ι) o 1 a
  have hnn := starWeight_nonneg (ι := ι) o zero_le_one ha.le
  have hdiag := starWeight_self (ι := ι) o 1 a
  have hdeg := starWeight_deg_pos (by omega) o ha
  have e : -(1 / ((Fintype.card ι : ℝ) - 1)) - ((Fintype.card ι : ℝ) - 2) * ε =
      -(a / (a + Fintype.card ι - 2)) := by
    rw [hε]; field_simp; ring
  refine ⟨fun κ => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · have h4 := h.mul_vol_sub_deg_le hsymm hnn (hdiag o) (hdeg o)
    obtain ⟨d0, -, hv⟩ := starWeight_degrees (ι := ι) o 1 a
    rw [d0, hv] at h4
    rw [e, le_neg, div_le_iff₀ (by linarith)]
    have h5 : ((Fintype.card ι : ℝ) - 1) * (κ * (a + Fintype.card ι - 2)) ≤
        ((Fintype.card ι : ℝ) - 1) * (-a) := by linarith
    have h6 := le_of_mul_le_mul_left h5 (by linarith)
    linarith
  · have h4 := ((starWeight_stationary_le_sharp hN o ha1 hε).1 _).mpr le_rfl
    exact (h4.walkSmallestEigenvalueGE_trace hsymm hnn hdiag hdeg).mono hnn h
  · simp only [starWeight_sq_div (by omega) o ha]
    rw [(starWeight_degrees (ι := ι) o _ _).2.2, hε]
    field_simp
    ring

/-- The weight `γ` on the pair `{o, o'}`, `β` on the other pairs of distinct vertices meeting
`{o, o'}`, `α` on the pairs of distinct vertices avoiding it, and `0` on the diagonal. -/
def edgeWeight (o o' : ι) (α β γ : ℝ) (x y : ι) : ℝ :=
  if x = y then 0 else
    if (x = o ∧ y = o') ∨ (x = o' ∧ y = o) then γ else
      if x = o ∨ x = o' ∨ y = o ∨ y = o' then β else α

omit [Fintype ι] in
/-- `edgeWeight` is symmetric (for any `o, o'`). -/
theorem edgeWeight_symm (o o' : ι) (α β γ : ℝ) (x y : ι) :
    edgeWeight o o' α β γ x y = edgeWeight o o' α β γ y x := by
  unfold edgeWeight
  by_cases hxy : x = y
  · simp [hxy]
  · rw [if_neg hxy, if_neg (Ne.symm hxy)]
    have e1 : ((x = o ∧ y = o') ∨ (x = o' ∧ y = o)) ↔ ((y = o ∧ x = o') ∨ (y = o' ∧ x = o)) := by
      tauto
    have e2 : (x = o ∨ x = o' ∨ y = o ∨ y = o') ↔ (y = o ∨ y = o' ∨ x = o ∨ x = o') := by tauto
    simp only [e1, e2]

omit [Fintype ι] in
/-- `edgeWeight` has no loops. -/
theorem edgeWeight_self (o o' : ι) (α β γ : ℝ) (x : ι) : edgeWeight o o' α β γ x x = 0 := by
  simp [edgeWeight]

omit [Fintype ι] in
/-- `edgeWeight` is nonnegative when `α, β, γ ≥ 0`. -/
theorem edgeWeight_nonneg (o o' : ι) {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (x y : ι) : 0 ≤ edgeWeight o o' α β γ x y := by
  unfold edgeWeight
  split_ifs
  exacts [le_rfl, hγ, hβ, hα]

omit [Fintype ι] in
/-- At `α = β = γ = 1` the edge family is the complete graph `K_n` with unit weights. -/
theorem edgeWeight_one_one_one (o o' : ι) (x y : ι) :
    edgeWeight o o' 1 1 1 x y = if x = y then 0 else 1 := by
  unfold edgeWeight
  split_ifs <;> rfl

/-- The row action of `edgeWeight`. -/
theorem sum_edgeWeight_mul {o o' : ι} (hoo : o ≠ o') (α β γ : ℝ) (x : ι) (g : ι → ℝ) :
    ∑ y, edgeWeight o o' α β γ x y * g y =
      α * ((∑ y, g y) - g x) +
        (β - α) * (((if x = o then 1 else 0) + (if x = o' then 1 else 0)) * (∑ y, g y) +
          g o + g o') +
        (γ - 2 * β + α) * ((if x = o then 1 else 0) * g o' + (if x = o' then 1 else 0) * g o) -
        2 * (β - α) * ((if x = o then g x else 0) + (if x = o' then g x else 0)) := by
  have e : ∀ y, edgeWeight o o' α β γ x y * g y =
      α * g y - α * (if x = y then g y else 0) +
        (β - α) * ((if x = o then 1 else 0) + (if x = o' then 1 else 0)) * g y +
        (β - α) * ((if y = o then g y else 0) + (if y = o' then g y else 0)) +
        (γ - 2 * β + α) * ((if x = o then 1 else 0) * (if y = o' then g y else 0) +
          (if x = o' then 1 else 0) * (if y = o then g y else 0)) -
        2 * (β - α) * ((if x = o then 1 else 0) + (if x = o' then 1 else 0)) *
          (if x = y then g y else 0) := by
    intro y
    unfold edgeWeight
    by_cases hxy : x = y
    · subst hxy
      by_cases hx : x = o
      · subst hx; simp [hoo]; ring
      · by_cases hx' : x = o'
        · subst hx'; simp [hx]; ring
        · simp [hx, hx']
    · rw [if_neg hxy]
      have hyx : ¬y = x := Ne.symm hxy
      by_cases hx : x = o
      · subst hx
        by_cases hy : y = o'
        · subst hy; simp [hoo, hyx]; ring
        · simp [hy, hxy, hyx, hoo]; ring
      · by_cases hx' : x = o'
        · subst hx'
          by_cases hy' : y = o
          · subst hy'; simp [hx, hyx]; ring
          · simp [hx, hy', hxy, hyx]; ring
        · by_cases hy : y = o
          · subst hy; simp [hx, hx', hoo]; ring
          · by_cases hy' : y = o'
            · subst hy'; simp [hx, hx', hy]; ring
            · simp [hx, hx', hy, hy', hxy]
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_add,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> ring

/-- The degrees of `edgeWeight`: `d₀ = (n − 2)β + γ` at `o, o'` and `d₁ = (n − 3)α + 2β`
elsewhere. -/
theorem sum_edgeWeight {o o' : ι} (hoo : o ≠ o') (α β γ : ℝ) (x : ι) :
    ∑ y, edgeWeight o o' α β γ x y =
      (((Fintype.card ι : ℝ) - 3) * α + 2 * β) +
        ((((Fintype.card ι : ℝ) - 2) * β + γ) - (((Fintype.card ι : ℝ) - 3) * α + 2 * β)) *
          ((if x = o then 1 else 0) + (if x = o' then 1 else 0)) := by
  have h := sum_edgeWeight_mul hoo α β γ x (fun _ => 1)
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [h]
  by_cases hx : x = o
  · subst hx; simp [hoo]; ring
  · by_cases hx' : x = o'
    · subst hx'; simp [hx]; ring
    · simp [hx, hx']; ring

/-- The quadratic form of `edgeWeight`. -/
theorem sum_sum_edgeWeight_mul_mul {o o' : ι} (hoo : o ≠ o') (α β γ : ℝ) (f : ι → ℝ) :
    ∑ x, ∑ y, edgeWeight o o' α β γ x y * f x * f y =
      α * ((∑ x, f x) ^ 2 - ∑ x, f x ^ 2) + 2 * (β - α) * (f o + f o') * (∑ x, f x) +
        2 * (γ - 2 * β + α) * f o * f o' - 2 * (β - α) * (f o ^ 2 + f o' ^ 2) := by
  have e : ∀ x, ∑ y, edgeWeight o o' α β γ x y * f x * f y =
      α * (∑ y, f y) * f x - α * f x ^ 2 +
        (β - α) * (∑ y, f y) * ((if x = o then f x else 0) + (if x = o' then f x else 0)) +
        (β - α) * (f o + f o') * f x +
        (γ - 2 * β + α) * ((if x = o then f x else 0) * f o' + (if x = o' then f x else 0) * f o) -
        2 * (β - α) * ((if x = o then f x ^ 2 else 0) + (if x = o' then f x ^ 2 else 0)) := by
    intro x
    have h1 : ∑ y, edgeWeight o o' α β γ x y * f x * f y =
        f x * ∑ y, edgeWeight o o' α β γ x y * f y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [h1, sum_edgeWeight_mul hoo]
    split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The degree-weighted mean and norm of `edgeWeight`, with `d₀, d₁` as in `sum_edgeWeight`. -/
theorem sum_edgeWeight_mul_moments {o o' : ι} (hoo : o ≠ o') (α β γ : ℝ) (f : ι → ℝ) :
    ∑ x, (∑ y, edgeWeight o o' α β γ x y) * f x =
        (((Fintype.card ι : ℝ) - 3) * α + 2 * β) * (∑ x, f x) +
          ((((Fintype.card ι : ℝ) - 2) * β + γ) - (((Fintype.card ι : ℝ) - 3) * α + 2 * β)) *
            (f o + f o') ∧
      ∑ x, (∑ y, edgeWeight o o' α β γ x y) * f x ^ 2 =
        (((Fintype.card ι : ℝ) - 3) * α + 2 * β) * (∑ x, f x ^ 2) +
          ((((Fintype.card ι : ℝ) - 2) * β + γ) - (((Fintype.card ι : ℝ) - 3) * α + 2 * β)) *
            (f o ^ 2 + f o' ^ 2) := by
  constructor
  · have e : ∀ x, (∑ y, edgeWeight o o' α β γ x y) * f x =
        (((Fintype.card ι : ℝ) - 3) * α + 2 * β) * f x +
          ((((Fintype.card ι : ℝ) - 2) * β + γ) - (((Fintype.card ι : ℝ) - 3) * α + 2 * β)) *
            ((if x = o then f x else 0) + (if x = o' then f x else 0)) := by
      intro x; rw [sum_edgeWeight hoo]; split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  · have e : ∀ x, (∑ y, edgeWeight o o' α β γ x y) * f x ^ 2 =
        (((Fintype.card ι : ℝ) - 3) * α + 2 * β) * f x ^ 2 +
          ((((Fintype.card ι : ℝ) - 2) * β + γ) - (((Fintype.card ι : ℝ) - 3) * α + 2 * β)) *
            ((if x = o then f x ^ 2 else 0) + (if x = o' then f x ^ 2 else 0)) := by
      intro x; rw [sum_edgeWeight hoo]; split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]

/-- The degrees and the volume of `edgeWeight`. -/
theorem edgeWeight_degrees {o o' : ι} (hoo : o ≠ o') (α β γ : ℝ) :
    (∑ y, edgeWeight o o' α β γ o y = ((Fintype.card ι : ℝ) - 2) * β + γ) ∧
      (∑ y, edgeWeight o o' α β γ o' y = ((Fintype.card ι : ℝ) - 2) * β + γ) ∧
      (∀ x, x ≠ o → x ≠ o' →
        ∑ y, edgeWeight o o' α β γ x y = ((Fintype.card ι : ℝ) - 3) * α + 2 * β) ∧
      ∑ x, ∑ y, edgeWeight o o' α β γ x y =
        2 * (((Fintype.card ι : ℝ) - 2) * β + γ) +
          ((Fintype.card ι : ℝ) - 2) * (((Fintype.card ι : ℝ) - 3) * α + 2 * β) := by
  refine ⟨?_, ?_, fun x hx hx' => ?_, ?_⟩
  · rw [sum_edgeWeight hoo]; simp [hoo]
  · rw [sum_edgeWeight hoo]; simp [Ne.symm hoo]
  · rw [sum_edgeWeight hoo]; simp [hx, hx']
  · have h := (sum_edgeWeight_mul_moments hoo α β γ (fun _ => 1)).1
    simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    rw [h]; ring

/-- The sum and the sum of squares of `f` off `{o, o'}`, and Cauchy–Schwarz there. -/
private theorem sum_sub_sub_facts {o o' : ι} (hoo : o ≠ o') (f : ι → ℝ) :
    0 ≤ (∑ x, f x ^ 2) - f o ^ 2 - f o' ^ 2 ∧
      ((∑ x, f x) - f o - f o') ^ 2 ≤
        ((Fintype.card ι : ℝ) - 2) * ((∑ x, f x ^ 2) - f o ^ 2 - f o' ^ 2) := by
  have hmem : o' ∈ univ.erase o := mem_erase.mpr ⟨Ne.symm hoo, mem_univ _⟩
  have e1 : ∑ x ∈ (univ.erase o).erase o', f x = (∑ x, f x) - f o - f o' := by
    rw [Finset.sum_erase_eq_sub hmem, Finset.sum_erase_eq_sub (mem_univ o)]
  have e2 : ∑ x ∈ (univ.erase o).erase o', f x ^ 2 = (∑ x, f x ^ 2) - f o ^ 2 - f o' ^ 2 := by
    rw [Finset.sum_erase_eq_sub (f := fun x => f x ^ 2) hmem,
      Finset.sum_erase_eq_sub (f := fun x => f x ^ 2) (mem_univ o)]
  have hcard : ((#((univ.erase o).erase o') : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 2 := by
    have h1 : #((univ.erase o).erase o') = Fintype.card ι - 2 := by
      rw [card_erase_of_mem hmem, card_erase_of_mem (mem_univ o), card_univ]; omega
    have h2 : 2 ≤ Fintype.card ι := by
      have := Finset.card_le_univ ({o, o'} : Finset ι)
      rw [card_pair hoo] at this; exact this
    rw [h1, Nat.cast_sub h2]; norm_num
  refine ⟨?_, ?_⟩
  · rw [← e2]; exact Finset.sum_nonneg fun x _ => sq_nonneg _
  · have h := sq_sum_le_card_mul_sum_sq (s := (univ.erase o).erase o') (f := f)
    rwa [e1, e2, hcard] at h

/-- **The second eigenvalue of the heavy edge family is at most `lam`** when
`lam ≥ −1/(2a + n − 3)`: `edgeWeight o o' 1 a (a(2a − 1))` has `w(o, o') = a(2a − 1)`,
`w(o, x) = w(o', x) = a` and all other weights `1`. Needs `a ≥ 1` and `n ≥ 2`. -/
theorem walkSecondEigenvalueLE_edgeWeight_heavy (hN : 2 ≤ Fintype.card ι) {o o' : ι}
    (hoo : o ≠ o') {a lam : ℝ} (ha : 1 ≤ a) (h1 : 0 ≤ 1 + lam * (2 * a + Fintype.card ι - 3)) :
    WalkSecondEigenvalueLE (edgeWeight o o' 1 a (a * (2 * a - 1))) lam := by
  intro f hf
  have hNr : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  obtain ⟨hm, hn⟩ := sum_edgeWeight_mul_moments hoo 1 a (a * (2 * a - 1)) f
  rw [hm] at hf
  rw [sum_sum_edgeWeight_mul_mul hoo, hn]
  obtain ⟨hU, -⟩ := sum_sub_sub_facts hoo f
  have hd1 : 0 < 2 * a + (Fintype.card ι : ℝ) - 3 := by linarith
  -- the mean condition says `R + a (p + q) = 0`
  have hE : (∑ x, f x) - f o - f o' + a * (f o + f o') = 0 := by
    have : (2 * a + (Fintype.card ι : ℝ) - 3) *
        ((∑ x, f x) - f o - f o' + a * (f o + f o')) = 0 := by linear_combination hf
    exact (mul_eq_zero.mp this).resolve_left hd1.ne'
  have h2 : 0 ≤ a * (2 * a - 1) + lam * a * (2 * a + Fintype.card ι - 3) := by nlinarith
  have key : 2 * ((1 * ((∑ x, f x) ^ 2 - ∑ x, f x ^ 2) + 2 * (a - 1) * (f o + f o') * (∑ x, f x) +
      2 * (a * (2 * a - 1) - 2 * a + 1) * f o * f o' - 2 * (a - 1) * (f o ^ 2 + f o' ^ 2)) -
      lam * ((((Fintype.card ι : ℝ) - 3) * 1 + 2 * a) * (∑ x, f x ^ 2) +
        ((((Fintype.card ι : ℝ) - 2) * a + a * (2 * a - 1)) -
          (((Fintype.card ι : ℝ) - 3) * 1 + 2 * a)) * (f o ^ 2 + f o' ^ 2))) =
      -(1 + lam * (2 * a + Fintype.card ι - 3)) *
          (2 * ((∑ x, f x ^ 2) - f o ^ 2 - f o' ^ 2) + a * (f o + f o') ^ 2) -
        (a * (2 * a - 1) + lam * a * (2 * a + Fintype.card ι - 3)) * (f o - f o') ^ 2 +
        2 * ((∑ x, f x) - f o - f o' + a * (f o + f o')) ^ 2 := by ring
  rw [hE] at key
  have t1 := mul_nonneg h1 (by positivity : (0 : ℝ) ≤
    2 * ((∑ x, f x ^ 2) - f o ^ 2 - f o' ^ 2) + a * (f o + f o') ^ 2)
  have t2 := mul_nonneg h2 (sq_nonneg (f o - f o'))
  nlinarith

/-- **The second eigenvalue of the light edge family is at most `lam`** when
`lam ≥ −τ/(τ + n − 2)`: `edgeWeight o o' 1 1 τ` has `w(o, o') = τ` and all other weights `1`.
Needs `0 < τ ≤ 1` and `n ≥ 3`. -/
theorem walkSecondEigenvalueLE_edgeWeight_light (hN : 3 ≤ Fintype.card ι) {o o' : ι}
    (hoo : o ≠ o') {τ lam : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (h : -τ ≤ lam * (τ + Fintype.card ι - 2)) :
    WalkSecondEigenvalueLE (edgeWeight o o' 1 1 τ) lam := by
  intro f hf
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  obtain ⟨hm, hn⟩ := sum_edgeWeight_mul_moments hoo 1 1 τ f
  rw [hm] at hf
  rw [sum_sum_edgeWeight_mul_mul hoo, hn]
  obtain ⟨-, hCS⟩ := sum_sub_sub_facts hoo f
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Fintype.card ι := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ x, f x := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = ∑ x, f x ^ 2 := ⟨_, rfl⟩
  rw [← hNdef] at hf hCS h hNr ⊢
  rw [← hS] at hf hCS ⊢
  rw [← hT] at hCS ⊢
  obtain ⟨p, hp⟩ : ∃ p, p = f o := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = f o' := ⟨_, rfl⟩
  rw [← hp, ← hq] at hf hCS ⊢
  obtain ⟨R, hR⟩ : ∃ R, R = S - p - q := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = T - p ^ 2 - q ^ 2 := ⟨_, rfl⟩
  rw [← hR, ← hU] at hCS
  have hS' : S = R + p + q := by rw [hR]; ring
  have hT' : T = U + p ^ 2 + q ^ 2 := by rw [hU]; ring
  rw [hS'] at hf
  rw [hS', hT']
  have hD0 : 0 < τ + N - 2 := by linarith
  have hE : (N - 1) * R + (τ + N - 2) * (p + q) = 0 := by linear_combination hf
  have hA1 : 0 ≤ 1 + lam * (N - 1) := by
    by_contra hc
    rw [not_le] at hc
    have : (τ + N - 2) * (1 + lam * (N - 1)) < 0 := mul_neg_of_pos_of_neg hD0 hc
    nlinarith
  have hA2 : 0 ≤ τ + lam * (τ + N - 2) := by linarith
  have hF : 0 < N ^ 2 - N + 2 * τ - 2 := by nlinarith
  have hA3 : 0 ≤ (N ^ 2 - N + 2 * τ - 2) *
      (2 * (N - 2) * (1 - τ) + (N - 1) * (τ + lam * (τ + N - 2))) :=
    mul_nonneg hF.le (by nlinarith)
  have key : 2 * (N - 2) * (τ + N - 2) ^ 2 *
      ((1 * ((R + p + q) ^ 2 - (U + p ^ 2 + q ^ 2)) + 2 * (1 - 1) * (p + q) * (R + p + q) +
        2 * (τ - 2 * 1 + 1) * p * q - 2 * (1 - 1) * (p ^ 2 + q ^ 2)) -
      lam * (((N - 3) * 1 + 2 * 1) * (U + p ^ 2 + q ^ 2) +
        (((N - 2) * 1 + τ) - ((N - 3) * 1 + 2 * 1)) * (p ^ 2 + q ^ 2))) =
      -(2 * (τ + N - 2) ^ 2 * (1 + lam * (N - 1))) * ((N - 2) * U - R ^ 2) -
        ((N - 2) * (τ + N - 2) ^ 2 * (τ + lam * (τ + N - 2))) * (p - q) ^ 2 -
        ((N ^ 2 - N + 2 * τ - 2) *
          (2 * (N - 2) * (1 - τ) + (N - 1) * (τ + lam * (τ + N - 2)))) * R ^ 2 +
        ((N - 1) * R + (τ + N - 2) * (p + q)) *
          (N^3*R*lam - N^3*lam*p - N^3*lam*q + N^2*R*lam*τ - 5*N^2*R*lam - N^2*R*τ + 4*N^2*R
            - 2*N^2*lam*p*τ + 6*N^2*lam*p - 2*N^2*lam*q*τ + 6*N^2*lam*q + N^2*p*τ + N^2*q*τ
            - 3*N*R*lam*τ + 8*N*R*lam + 7*N*R*τ - 16*N*R - N*lam*p*τ^2 + 8*N*lam*p*τ
            - 12*N*lam*p - N*lam*q*τ^2 + 8*N*lam*q*τ - 12*N*lam*q + N*p*τ^2 - 4*N*p*τ
            + N*q*τ^2 - 4*N*q*τ + 2*R*lam*τ - 4*R*lam - 10*R*τ + 16*R + 2*lam*p*τ^2
            - 8*lam*p*τ + 8*lam*p + 2*lam*q*τ^2 - 8*lam*q*τ + 8*lam*q - 2*p*τ^2 + 4*p*τ
            - 2*q*τ^2 + 4*q*τ) := by ring
  rw [hE, zero_mul, add_zero] at key
  have t1 := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (τ + N - 2) ^ 2) hA1)
    (sub_nonneg.mpr hCS)
  have t2 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ N - 2)
    (by positivity : (0 : ℝ) ≤ (τ + N - 2) ^ 2)) (mul_nonneg hA2 (sq_nonneg (p - q)))
  have t3 := mul_nonneg hA3 (sq_nonneg R)
  have hK : 0 < 2 * (N - 2) * (τ + N - 2) ^ 2 := by
    have : 0 < N - 2 := by linarith
    positivity
  have hX : 2 * (N - 2) * (τ + N - 2) ^ 2 *
      ((1 * ((R + p + q) ^ 2 - (U + p ^ 2 + q ^ 2)) + 2 * (1 - 1) * (p + q) * (R + p + q) +
        2 * (τ - 2 * 1 + 1) * p * q - 2 * (1 - 1) * (p ^ 2 + q ^ 2)) -
      lam * (((N - 3) * 1 + 2 * 1) * (U + p ^ 2 + q ^ 2) +
        (((N - 2) * 1 + τ) - ((N - 3) * 1 + 2 * 1)) * (p ^ 2 + q ^ 2))) ≤ 0 := by
    rw [key]
    linarith
  by_contra hc
  rw [not_le] at hc
  have := mul_pos hK (sub_pos.mpr hc)
  linarith


/-- **The heavy edge family has `μ₂ = −1/(2a + n − 3)` exactly**, for `a ≥ 1` and `n ≥ 3`. The
test function is the quotient eigenvector: `−(n − 2)` at `o, o'` and `2a` elsewhere. -/
theorem walkSecondEigenvalueLE_edgeWeight_heavy_iff (hN : 3 ≤ Fintype.card ι) {o o' : ι}
    (hoo : o ≠ o') {a : ℝ} (ha : 1 ≤ a) (lam : ℝ) :
    WalkSecondEigenvalueLE (edgeWeight o o' 1 a (a * (2 * a - 1))) lam ↔
      -(1 / (2 * a + Fintype.card ι - 3)) ≤ lam := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have hd1 : 0 < 2 * a + (Fintype.card ι : ℝ) - 3 := by linarith
  rw [← neg_div, div_le_iff₀ hd1]
  constructor
  · intro h
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * a + Fintype.card ι - 2 := ⟨_, rfl⟩
    obtain ⟨f, hf⟩ : ∃ f : ι → ℝ,
        f = fun x => 2 * a - (if x = o then c else 0) - (if x = o' then c else 0) := ⟨_, rfl⟩
    have hS : ∑ x, f x = Fintype.card ι * (2 * a) - c - c := by
      rw [hf]; simp [Finset.sum_sub_distrib]
    have hT : ∑ x, f x ^ 2 = Fintype.card ι * (2 * a) ^ 2 - 2 * (4 * a * c - c ^ 2) := by
      have e : ∀ x, f x ^ 2 = (2 * a) ^ 2 - (if x = o then 4 * a * c - c ^ 2 else 0) -
          (if x = o' then 4 * a * c - c ^ 2 else 0) := by
        intro x
        rw [hf]
        by_cases hx : x = o
        · subst hx; simp [hoo]; ring
        · by_cases hx' : x = o'
          · subst hx'; simp [hx]; ring
          · simp [hx, hx']
      simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    have hp : f o = 2 * a - c := by rw [hf]; simp [hoo]
    have hq : f o' = 2 * a - c := by rw [hf]; simp [Ne.symm hoo]
    obtain ⟨hm1, hn1⟩ := sum_edgeWeight_mul_moments hoo 1 a (a * (2 * a - 1)) f
    have h1 := h f (by rw [hm1, hS, hp, hq, hc]; ring)
    rw [sum_sum_edgeWeight_mul_mul hoo, hn1, hS, hT, hp, hq, hc] at h1
    have hP : 0 < 2 * a * ((Fintype.card ι : ℝ) - 2) * (2 * a + Fintype.card ι - 2) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    refine le_of_mul_le_mul_left ?_ hP
    have e1 : 2 * a * ((Fintype.card ι : ℝ) - 2) * (2 * a + Fintype.card ι - 2) * (-1) =
        1 * (((Fintype.card ι : ℝ) * (2 * a) - (2 * a + Fintype.card ι - 2) -
            (2 * a + Fintype.card ι - 2)) ^ 2 -
          ((Fintype.card ι : ℝ) * (2 * a) ^ 2 -
            2 * (4 * a * (2 * a + Fintype.card ι - 2) - (2 * a + Fintype.card ι - 2) ^ 2))) +
        2 * (a - 1) *
          (2 * a - (2 * a + Fintype.card ι - 2) + (2 * a - (2 * a + Fintype.card ι - 2))) *
          ((Fintype.card ι : ℝ) * (2 * a) - (2 * a + Fintype.card ι - 2) -
            (2 * a + Fintype.card ι - 2)) +
        2 * (a * (2 * a - 1) - 2 * a + 1) * (2 * a - (2 * a + Fintype.card ι - 2)) *
          (2 * a - (2 * a + Fintype.card ι - 2)) -
        2 * (a - 1) * ((2 * a - (2 * a + Fintype.card ι - 2)) ^ 2 +
          (2 * a - (2 * a + Fintype.card ι - 2)) ^ 2) := by ring
    have e2 : 2 * a * ((Fintype.card ι : ℝ) - 2) * (2 * a + Fintype.card ι - 2) *
        (lam * (2 * a + Fintype.card ι - 3)) =
        lam * ((((Fintype.card ι : ℝ) - 3) * 1 + 2 * a) *
            ((Fintype.card ι : ℝ) * (2 * a) ^ 2 -
              2 * (4 * a * (2 * a + Fintype.card ι - 2) - (2 * a + Fintype.card ι - 2) ^ 2)) +
          ((((Fintype.card ι : ℝ) - 2) * a + a * (2 * a - 1)) -
              (((Fintype.card ι : ℝ) - 3) * 1 + 2 * a)) *
            ((2 * a - (2 * a + Fintype.card ι - 2)) ^ 2 +
              (2 * a - (2 * a + Fintype.card ι - 2)) ^ 2)) := by ring
    rw [e1, e2]
    exact h1
  · intro h
    exact walkSecondEigenvalueLE_edgeWeight_heavy (by omega) hoo ha (by linarith)

/-- **The light edge family has `μ₂ = −τ/(τ + n − 2)` exactly**, for `0 < τ ≤ 1` and `n ≥ 3`.
The test function is `1_o − 1_{o'}`. -/
theorem walkSecondEigenvalueLE_edgeWeight_light_iff (hN : 3 ≤ Fintype.card ι) {o o' : ι}
    (hoo : o ≠ o') {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (lam : ℝ) :
    WalkSecondEigenvalueLE (edgeWeight o o' 1 1 τ) lam ↔
      -(τ / (τ + Fintype.card ι - 2)) ≤ lam := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have hd0 : 0 < τ + (Fintype.card ι : ℝ) - 2 := by linarith
  rw [← neg_div, div_le_iff₀ hd0]
  constructor
  · intro h
    obtain ⟨d0, d0', -, -⟩ := edgeWeight_degrees hoo 1 1 τ
    obtain ⟨hm1, hq1, hn1⟩ := moments_two_point (edgeWeight_symm o o' 1 1 τ) hoo 1 (-1)
    have h1 := h _ (by rw [hm1, d0, d0']; ring)
    rw [hq1, hn1, d0, d0', edgeWeight_self, edgeWeight_self] at h1
    have hw : edgeWeight o o' 1 1 τ o o' = τ := by simp [edgeWeight, hoo]
    rw [hw] at h1
    nlinarith
  · exact walkSecondEigenvalueLE_edgeWeight_light hN hoo hτ0 hτ1

/-- **Sharpness of the lower edge bound** (the light edge family). For `0 < τ ≤ 1` on `n ≥ 3`
vertices, `edgeWeight o o' 1 1 τ` (`w(o, o') = τ`, all other weights `1`) has
`μ₂ = ε − 1/(n − 1)` exactly, with `ε = 1/(n − 1) − τ/(τ + n − 2) ∈ [0, 1/(n − 1))`, and the pair
`{o, o'}` attains `2w(o, o')/(deg o + deg o') = 1/(n − 1) − ε`. At `τ = 1` it is `K_n`. -/
theorem edgeWeight_sub_le_two_mul_weight_div_sharp (hN : 3 ≤ Fintype.card ι) {o o' : ι}
    (hoo : o ≠ o') {τ ε : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hε : ε = 1 / ((Fintype.card ι : ℝ) - 1) - τ / (τ + Fintype.card ι - 2)) :
    (∀ lam, WalkSecondEigenvalueLE (edgeWeight o o' 1 1 τ) lam ↔
      ε - 1 / ((Fintype.card ι : ℝ) - 1) ≤ lam) ∧
    2 * edgeWeight o o' 1 1 τ o o' /
        ((∑ x, edgeWeight o o' 1 1 τ o x) + ∑ x, edgeWeight o o' 1 1 τ o' x) =
      1 / ((Fintype.card ι : ℝ) - 1) - ε := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have e : ε - 1 / ((Fintype.card ι : ℝ) - 1) = -(τ / (τ + Fintype.card ι - 2)) := by
    rw [hε]; ring
  refine ⟨fun lam => ?_, ?_⟩
  · rw [e]
    exact walkSecondEigenvalueLE_edgeWeight_light_iff hN hoo hτ0 hτ1 lam
  obtain ⟨d0, d0', -, -⟩ := edgeWeight_degrees hoo 1 1 τ
  have hw : edgeWeight o o' 1 1 τ o o' = τ := by simp [edgeWeight, hoo]
  rw [d0, d0', hw, hε, sub_sub_cancel]
  have h1 : τ + (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith
  have hD : ((Fintype.card ι : ℝ) - 2) * 1 + τ = τ + Fintype.card ι - 2 := by ring
  rw [hD]
  field_simp
  ring

/-- The degrees of the heavy edge family: `a(2a + n − 3)` at `o, o'` and `2a + n − 3`
elsewhere. -/
private theorem edgeWeight_heavy_degrees {o o' : ι} (hoo : o ≠ o') (a : ℝ) :
    (∑ y, edgeWeight o o' 1 a (a * (2 * a - 1)) o y = a * (2 * a + Fintype.card ι - 3)) ∧
      (∑ y, edgeWeight o o' 1 a (a * (2 * a - 1)) o' y = a * (2 * a + Fintype.card ι - 3)) ∧
      (∀ x, x ≠ o → x ≠ o' →
        ∑ y, edgeWeight o o' 1 a (a * (2 * a - 1)) x y = 2 * a + Fintype.card ι - 3) := by
  obtain ⟨d0, d0', d1, -⟩ := edgeWeight_degrees hoo 1 a (a * (2 * a - 1))
  exact ⟨by rw [d0]; ring, by rw [d0']; ring, fun x hx hx' => by rw [d1 x hx hx']; ring⟩

/-- **Sharpness of the upper edge bound**, in both forms (the heavy edge family). For `a ≥ 1` on
`n ≥ 3` vertices, `edgeWeight o o' 1 a (a(2a − 1))` (`w(o, o') = a(2a − 1)`,
`w(o, x) = w(o', x) = a`, all other weights `1`) has `μ₂ = ε − 1/(n − 1)` exactly, with
`ε = 2(a − 1)/((n − 1)(2a + n − 3)) ∈ [0, 1/(n − 1))`, and the pair `{o, o'}` attains
`w(o, o')/√(deg o · deg o') = 2w(o, o')/(deg o + deg o') = 1/(n − 1) + (n − 2) ε`. At `a = 1`
it is `K_n`. -/
theorem edgeWeight_weight_div_sqrt_le_sharp (hN : 3 ≤ Fintype.card ι) {o o' : ι}
    (hoo : o ≠ o') {a ε : ℝ} (ha : 1 ≤ a)
    (hε : ε = 2 * (a - 1) / (((Fintype.card ι : ℝ) - 1) * (2 * a + Fintype.card ι - 3))) :
    (∀ lam, WalkSecondEigenvalueLE (edgeWeight o o' 1 a (a * (2 * a - 1))) lam ↔
      ε - 1 / ((Fintype.card ι : ℝ) - 1) ≤ lam) ∧
    edgeWeight o o' 1 a (a * (2 * a - 1)) o o' /
        Real.sqrt ((∑ x, edgeWeight o o' 1 a (a * (2 * a - 1)) o x) *
          ∑ x, edgeWeight o o' 1 a (a * (2 * a - 1)) o' x) =
      1 / ((Fintype.card ι : ℝ) - 1) + ((Fintype.card ι : ℝ) - 2) * ε ∧
    2 * edgeWeight o o' 1 a (a * (2 * a - 1)) o o' /
        ((∑ x, edgeWeight o o' 1 a (a * (2 * a - 1)) o x) +
          ∑ x, edgeWeight o o' 1 a (a * (2 * a - 1)) o' x) =
      1 / ((Fintype.card ι : ℝ) - 1) + ((Fintype.card ι : ℝ) - 2) * ε := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have h1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have h2 : 2 * a + (Fintype.card ι : ℝ) - 3 ≠ 0 := by linarith
  have h3 : a ≠ 0 := by linarith
  have e : ε - 1 / ((Fintype.card ι : ℝ) - 1) = -(1 / (2 * a + Fintype.card ι - 3)) := by
    rw [hε]; field_simp; ring
  have e2 : 1 / ((Fintype.card ι : ℝ) - 1) + ((Fintype.card ι : ℝ) - 2) * ε =
      (2 * a - 1) / (2 * a + Fintype.card ι - 3) := by
    rw [hε]; field_simp; ring
  obtain ⟨d0, d0', -⟩ := edgeWeight_heavy_degrees (ι := ι) hoo a
  have hw : edgeWeight o o' 1 a (a * (2 * a - 1)) o o' = a * (2 * a - 1) := by
    simp [edgeWeight, hoo]
  refine ⟨fun lam => ?_, ?_, ?_⟩
  · rw [e]
    exact walkSecondEigenvalueLE_edgeWeight_heavy_iff hN hoo ha lam
  · rw [d0, d0', hw, e2, Real.sqrt_mul_self (by nlinarith)]
    field_simp
  · rw [d0, d0', hw, e2]
    field_simp
    ring

/-- `w(u,v)²/(deg u · deg v)` for the heavy edge family is again an edge-family weight. -/
private theorem edgeWeight_heavy_sq_div (hN : 3 ≤ Fintype.card ι) {o o' : ι} (hoo : o ≠ o')
    {a : ℝ} (ha : 1 ≤ a) (x y : ι) :
    edgeWeight o o' 1 a (a * (2 * a - 1)) x y ^ 2 /
        ((∑ z, edgeWeight o o' 1 a (a * (2 * a - 1)) x z) *
          ∑ z, edgeWeight o o' 1 a (a * (2 * a - 1)) y z) =
      edgeWeight o o' (1 / (2 * a + Fintype.card ι - 3) ^ 2)
        (a / (2 * a + Fintype.card ι - 3) ^ 2)
        ((2 * a - 1) ^ 2 / (2 * a + Fintype.card ι - 3) ^ 2) x y := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have h2 : 2 * a + (Fintype.card ι : ℝ) - 3 ≠ 0 := by linarith
  have h3 : a ≠ 0 := by linarith
  obtain ⟨d0, d0', d1⟩ := edgeWeight_heavy_degrees (ι := ι) hoo a
  by_cases hxy : x = y
  · subst hxy; simp [edgeWeight]
  have hyx : ¬y = x := Ne.symm hxy
  by_cases hx : x = o
  · subst hx
    by_cases hy : y = o'
    · subst hy
      rw [d0, d0']
      simp [edgeWeight, hoo]
      field_simp
    · rw [d0, d1 y hyx hy]
      simp [edgeWeight, hxy, hy, hoo, hyx]
      field_simp
  · by_cases hx' : x = o'
    · subst hx'
      by_cases hy : y = o
      · subst hy
        rw [d0, d0']
        simp [edgeWeight, hx]
        field_simp
      · rw [d0', d1 y hy hyx]
        simp [edgeWeight, hx, hy, hxy]
        field_simp
    · by_cases hy : y = o
      · subst hy
        rw [d1 x hx hx', d0]
        simp [edgeWeight, hx, hx']
        field_simp
      · by_cases hy' : y = o'
        · subst hy'
          rw [d1 x hx hx', d0']
          simp [edgeWeight, hx, hx']
          field_simp
        · rw [d1 x hx hx', d1 y hy hy']
          simp [edgeWeight, hx, hx', hy, hy', hxy]
          field_simp

/-- **Equality in (c) for the heavy edge family.** For `a ≥ 1` on `n ≥ 3` vertices, with
`ε = 2(a − 1)/((n − 1)(2a + n − 3))` (so `μ₂ = ε − 1/(n − 1)` by
`edgeWeight_weight_div_sqrt_le_sharp`), the smallest walk eigenvalue is exactly
`−1/(n − 1) − (n − 2) ε = −(2a − 1)/(2a + n − 3)`, and
`Σ_{u,v} w(u,v)²/(deg u · deg v) − n/(n − 1) = (n − 1)(n − 2) ε²`. -/
theorem edgeWeight_trace_bound_eq (hN : 3 ≤ Fintype.card ι) {o o' : ι} (hoo : o ≠ o')
    {a ε : ℝ} (ha : 1 ≤ a)
    (hε : ε = 2 * (a - 1) / (((Fintype.card ι : ℝ) - 1) * (2 * a + Fintype.card ι - 3))) :
    (∀ κ, WalkSmallestEigenvalueGE (edgeWeight o o' 1 a (a * (2 * a - 1))) κ ↔
      κ ≤ -(1 / ((Fintype.card ι : ℝ) - 1)) - ((Fintype.card ι : ℝ) - 2) * ε) ∧
    ∑ u, ∑ v, edgeWeight o o' 1 a (a * (2 * a - 1)) u v ^ 2 /
        ((∑ x, edgeWeight o o' 1 a (a * (2 * a - 1)) u x) *
          ∑ x, edgeWeight o o' 1 a (a * (2 * a - 1)) v x) -
        (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) =
      ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε ^ 2 := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have h1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have h2 : 2 * a + (Fintype.card ι : ℝ) - 3 ≠ 0 := by linarith
  have hd1 : 0 < 2 * a + (Fintype.card ι : ℝ) - 3 := by linarith
  have ha0 : 0 < a := by linarith
  have hsymm := edgeWeight_symm (ι := ι) o o' 1 a (a * (2 * a - 1))
  have hnn := edgeWeight_nonneg (ι := ι) o o' zero_le_one ha0.le (by nlinarith : (0 : ℝ) ≤
    a * (2 * a - 1))
  have hdiag := edgeWeight_self (ι := ι) o o' 1 a (a * (2 * a - 1))
  obtain ⟨d0, d0', d1⟩ := edgeWeight_heavy_degrees (ι := ι) hoo a
  have hdeg : ∀ x, 0 < ∑ y, edgeWeight o o' 1 a (a * (2 * a - 1)) x y := by
    intro x
    by_cases hx : x = o
    · rw [hx, d0]; positivity
    · by_cases hx' : x = o'
      · rw [hx', d0']; positivity
      · rw [d1 x hx hx']; exact hd1
  have e : -(1 / ((Fintype.card ι : ℝ) - 1)) - ((Fintype.card ι : ℝ) - 2) * ε =
      -((2 * a - 1) / (2 * a + Fintype.card ι - 3)) := by
    rw [hε]; field_simp; ring
  refine ⟨fun κ => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · have h4 := h.mul_sqrt_le_neg_weight hsymm (hdiag o) (hdiag o') hoo (hdeg o) (hdeg o')
    have hw : edgeWeight o o' 1 a (a * (2 * a - 1)) o o' = a * (2 * a - 1) := by
      simp [edgeWeight, hoo]
    rw [d0, d0', hw, Real.sqrt_mul_self (by positivity)] at h4
    rw [e, le_neg, div_le_iff₀ hd1]
    have h5 : a * (κ * (2 * a + Fintype.card ι - 3)) ≤ a * (-(2 * a - 1)) := by linarith
    have h6 := le_of_mul_le_mul_left h5 ha0
    linarith
  · have h4 := ((edgeWeight_weight_div_sqrt_le_sharp hN hoo ha hε).1 _).mpr le_rfl
    exact (h4.walkSmallestEigenvalueGE_trace hsymm hnn hdiag hdeg).mono hnn h
  · simp only [edgeWeight_heavy_sq_div hN hoo ha]
    rw [(edgeWeight_degrees (ι := ι) hoo _ _ _).2.2.2, hε]
    field_simp
    ring


/-! #### Every `ε ∈ [0, 1/(n − 1))` is attained -/

/-- **The lower degree bound is sharp for every `ε ∈ [0, 1/(n − 1))`** (`n ≥ 3`): with
`L = 1/(n − 1) − ε` and `a = L(n − 2)/(1 − L) ∈ (0, 1]`, the light vertex family
`starWeight o 1 a` has `μ₂ = ε − 1/(n − 1)` exactly and `π(o) = (1 − (n − 1) ε)/(n − (n − 1) ε)`.
The second eigenvalue is pinned down variationally; `walkMatrix_secondEigenvalue_eq_of_forall_iff`
turns it into an equality for the eigenvalue of `walkMatrix`. -/
theorem exists_starWeight_le_stationary_eq (hN : 3 ≤ Fintype.card ι) (o : ι) {ε : ℝ}
    (h0 : 0 ≤ ε) (h1 : ε < 1 / ((Fintype.card ι : ℝ) - 1)) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
      (∀ lam, WalkSecondEigenvalueLE (starWeight o 1 a) lam ↔
        ε - 1 / ((Fintype.card ι : ℝ) - 1) ≤ lam) ∧
      (∑ y, starWeight o 1 a o y) / ∑ x, ∑ y, starWeight o 1 a x y =
        (1 - ((Fintype.card ι : ℝ) - 1) * ε) /
          ((Fintype.card ι : ℝ) - ((Fintype.card ι : ℝ) - 1) * ε) := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 / ((Fintype.card ι : ℝ) - 1) - ε := ⟨_, rfl⟩
  have hc : 1 / ((Fintype.card ι : ℝ) - 1) ≤ 1 / 2 :=
    div_le_div_of_nonneg_left zero_le_one two_pos (by linarith)
  have hL0 : 0 < L := by linarith
  have hL1 : L < 1 := by linarith
  have hLc : L * ((Fintype.card ι : ℝ) - 1) ≤ 1 := by
    have : L ≤ 1 / ((Fintype.card ι : ℝ) - 1) := by linarith
    rwa [le_div_iff₀ (by linarith)] at this
  refine ⟨L * ((Fintype.card ι : ℝ) - 2) / (1 - L), ?_, ?_, ?_⟩
  · exact div_pos (mul_pos hL0 (by linarith)) (by linarith)
  · rw [div_le_one (by linarith)]; nlinarith
  · apply starWeight_le_stationary_sharp (by omega) o
      (div_pos (mul_pos hL0 (by linarith)) (by linarith))
    · rw [div_le_one (by linarith)]; nlinarith
    · have h2 : 1 - L ≠ 0 := by linarith
      have h3 : (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith
      have e : L * ((Fintype.card ι : ℝ) - 2) / (1 - L) /
          (L * ((Fintype.card ι : ℝ) - 2) / (1 - L) + Fintype.card ι - 2) = L := by
        have : L * ((Fintype.card ι : ℝ) - 2) / (1 - L) + Fintype.card ι - 2 =
            ((Fintype.card ι : ℝ) - 2) / (1 - L) := by field_simp; ring
        rw [this]
        field_simp
      rw [e, hL]; ring

/-- **The upper degree bound is sharp for every `ε ∈ [0, 1/(n − 1))`** (`n ≥ 3`): with
`L = 1/(n − 1) − ε` and `a = 1/L − n + 2 ≥ 1`, the heavy vertex family `starWeight o 1 a` has
`μ₂ = ε − 1/(n − 1)` exactly and `π(o) = (1 + (n − 1)(n − 2) ε)/(n + (n − 1)(n − 2) ε)`. -/
theorem exists_starWeight_stationary_le_eq (hN : 3 ≤ Fintype.card ι) (o : ι) {ε : ℝ}
    (h0 : 0 ≤ ε) (h1 : ε < 1 / ((Fintype.card ι : ℝ) - 1)) :
    ∃ a : ℝ, 1 ≤ a ∧
      (∀ lam, WalkSecondEigenvalueLE (starWeight o 1 a) lam ↔
        ε - 1 / ((Fintype.card ι : ℝ) - 1) ≤ lam) ∧
      (∑ y, starWeight o 1 a o y) / ∑ x, ∑ y, starWeight o 1 a x y =
        (1 + ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε) /
          ((Fintype.card ι : ℝ) + ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε) := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 / ((Fintype.card ι : ℝ) - 1) - ε := ⟨_, rfl⟩
  have hL0 : 0 < L := by linarith
  have hLc : L * ((Fintype.card ι : ℝ) - 1) ≤ 1 := by
    have : L ≤ 1 / ((Fintype.card ι : ℝ) - 1) := by linarith
    rwa [le_div_iff₀ (by linarith)] at this
  have ha : 1 ≤ 1 / L - Fintype.card ι + 2 := by
    have : (Fintype.card ι : ℝ) - 1 ≤ 1 / L := by rw [le_div_iff₀ hL0]; linarith
    linarith
  refine ⟨1 / L - Fintype.card ι + 2, ha, ?_⟩
  apply starWeight_stationary_le_sharp hN o ha
  have e : 1 / L - (Fintype.card ι : ℝ) + 2 + Fintype.card ι - 2 = 1 / L := by ring
  rw [e, show ε = 1 / ((Fintype.card ι : ℝ) - 1) - L by rw [hL]; ring]
  have h2 : L ≠ 0 := hL0.ne'
  field_simp
  ring

/-- **The lower edge bound is sharp for every `ε ∈ [0, 1/(n − 1))`** (`n ≥ 3`, `o ≠ o'`): with
`L = 1/(n − 1) − ε` and `τ = L(n − 2)/(1 − L) ∈ (0, 1]`, the light edge family
`edgeWeight o o' 1 1 τ` has `μ₂ = ε − 1/(n − 1)` exactly and
`2w(o, o')/(deg o + deg o') = 1/(n − 1) − ε`. -/
theorem exists_edgeWeight_sub_le_two_mul_weight_div_eq (hN : 3 ≤ Fintype.card ι) {o o' : ι}
    (hoo : o ≠ o') {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1 / ((Fintype.card ι : ℝ) - 1)) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧
      (∀ lam, WalkSecondEigenvalueLE (edgeWeight o o' 1 1 τ) lam ↔
        ε - 1 / ((Fintype.card ι : ℝ) - 1) ≤ lam) ∧
      2 * edgeWeight o o' 1 1 τ o o' /
          ((∑ x, edgeWeight o o' 1 1 τ o x) + ∑ x, edgeWeight o o' 1 1 τ o' x) =
        1 / ((Fintype.card ι : ℝ) - 1) - ε := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 / ((Fintype.card ι : ℝ) - 1) - ε := ⟨_, rfl⟩
  have hc : 1 / ((Fintype.card ι : ℝ) - 1) ≤ 1 / 2 :=
    div_le_div_of_nonneg_left zero_le_one two_pos (by linarith)
  have hL0 : 0 < L := by linarith
  have hL1 : L < 1 := by linarith
  have hLc : L * ((Fintype.card ι : ℝ) - 1) ≤ 1 := by
    have : L ≤ 1 / ((Fintype.card ι : ℝ) - 1) := by linarith
    rwa [le_div_iff₀ (by linarith)] at this
  have hτ0 : 0 < L * ((Fintype.card ι : ℝ) - 2) / (1 - L) :=
    div_pos (mul_pos hL0 (by linarith)) (by linarith)
  have hτ1 : L * ((Fintype.card ι : ℝ) - 2) / (1 - L) ≤ 1 := by
    rw [div_le_one (by linarith)]; nlinarith
  refine ⟨_, hτ0, hτ1, ?_⟩
  apply edgeWeight_sub_le_two_mul_weight_div_sharp hN hoo hτ0 hτ1
  have h2 : 1 - L ≠ 0 := by linarith
  have h3 : (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith
  have e : L * ((Fintype.card ι : ℝ) - 2) / (1 - L) /
      (L * ((Fintype.card ι : ℝ) - 2) / (1 - L) + Fintype.card ι - 2) = L := by
    have : L * ((Fintype.card ι : ℝ) - 2) / (1 - L) + Fintype.card ι - 2 =
        ((Fintype.card ι : ℝ) - 2) / (1 - L) := by field_simp; ring
    rw [this]
    field_simp
  rw [e, hL]; ring

/-- **The upper edge bound is sharp for every `ε ∈ [0, 1/(n − 1))`**, in both forms (`n ≥ 3`,
`o ≠ o'`): with `L = 1/(n − 1) − ε` and `a = (1/L − n + 3)/2 ≥ 1`, the heavy edge family
`edgeWeight o o' 1 a (a(2a − 1))` has `μ₂ = ε − 1/(n − 1)` exactly and
`w(o, o')/√(deg o · deg o') = 2w(o, o')/(deg o + deg o') = 1/(n − 1) + (n − 2) ε`. -/
theorem exists_edgeWeight_weight_div_sqrt_le_eq (hN : 3 ≤ Fintype.card ι) {o o' : ι}
    (hoo : o ≠ o') {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1 / ((Fintype.card ι : ℝ) - 1)) :
    ∃ a : ℝ, 1 ≤ a ∧
      (∀ lam, WalkSecondEigenvalueLE (edgeWeight o o' 1 a (a * (2 * a - 1))) lam ↔
        ε - 1 / ((Fintype.card ι : ℝ) - 1) ≤ lam) ∧
      edgeWeight o o' 1 a (a * (2 * a - 1)) o o' /
          Real.sqrt ((∑ x, edgeWeight o o' 1 a (a * (2 * a - 1)) o x) *
            ∑ x, edgeWeight o o' 1 a (a * (2 * a - 1)) o' x) =
        1 / ((Fintype.card ι : ℝ) - 1) + ((Fintype.card ι : ℝ) - 2) * ε ∧
      2 * edgeWeight o o' 1 a (a * (2 * a - 1)) o o' /
          ((∑ x, edgeWeight o o' 1 a (a * (2 * a - 1)) o x) +
            ∑ x, edgeWeight o o' 1 a (a * (2 * a - 1)) o' x) =
        1 / ((Fintype.card ι : ℝ) - 1) + ((Fintype.card ι : ℝ) - 2) * ε := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 / ((Fintype.card ι : ℝ) - 1) - ε := ⟨_, rfl⟩
  have hL0 : 0 < L := by linarith
  have hLc : L * ((Fintype.card ι : ℝ) - 1) ≤ 1 := by
    have : L ≤ 1 / ((Fintype.card ι : ℝ) - 1) := by linarith
    rwa [le_div_iff₀ (by linarith)] at this
  have ha : 1 ≤ (1 / L - Fintype.card ι + 3) / 2 := by
    have : (Fintype.card ι : ℝ) - 1 ≤ 1 / L := by rw [le_div_iff₀ hL0]; linarith
    linarith
  refine ⟨(1 / L - Fintype.card ι + 3) / 2, ha, ?_⟩
  apply edgeWeight_weight_div_sqrt_le_sharp hN hoo ha
  have e : 2 * ((1 / L - Fintype.card ι + 3) / 2) + (Fintype.card ι : ℝ) - 3 = 1 / L := by ring
  rw [e, show ε = 1 / ((Fintype.card ι : ℝ) - 1) - L by rw [hL]; ring]
  have h2 : L ≠ 0 := hL0.ne'
  field_simp
  ring

/-- The complete bipartite graph between `A` and its complement, with unit weights. For
`A = {o}` it is the star centred at `o`. -/
def bipartiteWeight (A : Finset ι) (x y : ι) : ℝ := if (x ∈ A ↔ y ∈ A) then 0 else 1

omit [Fintype ι] in
/-- `bipartiteWeight` is symmetric. -/
theorem bipartiteWeight_symm (A : Finset ι) (x y : ι) :
    bipartiteWeight A x y = bipartiteWeight A y x := by
  unfold bipartiteWeight
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp [hx, hy]

omit [Fintype ι] in
/-- `bipartiteWeight` has no loops. -/
theorem bipartiteWeight_self (A : Finset ι) (x : ι) : bipartiteWeight A x x = 0 := by
  simp [bipartiteWeight]

omit [Fintype ι] in
/-- `bipartiteWeight` is nonnegative. -/
theorem bipartiteWeight_nonneg (A : Finset ι) (x y : ι) : 0 ≤ bipartiteWeight A x y := by
  unfold bipartiteWeight
  split_ifs <;> norm_num

/-- The row action of `bipartiteWeight`. -/
theorem sum_bipartiteWeight_mul (A : Finset ι) (x : ι) (g : ι → ℝ) :
    ∑ y, bipartiteWeight A x y * g y =
      if x ∈ A then (∑ y, g y) - ∑ y ∈ A, g y else ∑ y ∈ A, g y := by
  by_cases hx : x ∈ A
  · rw [if_pos hx]
    have e : ∀ y, bipartiteWeight A x y * g y = g y - (if y ∈ A then g y else 0) := by
      intro y; unfold bipartiteWeight; by_cases hy : y ∈ A <;> simp [hx, hy]
    simp only [e, Finset.sum_sub_distrib, Fintype.sum_ite_mem]
  · rw [if_neg hx]
    have e : ∀ y, bipartiteWeight A x y * g y = (if y ∈ A then g y else 0) := by
      intro y; unfold bipartiteWeight; by_cases hy : y ∈ A <;> simp [hx, hy]
    simp only [e, Fintype.sum_ite_mem]

/-- The degrees of `bipartiteWeight`: `n − |A|` on `A` and `|A|` off it. -/
theorem sum_bipartiteWeight (A : Finset ι) (x : ι) :
    ∑ y, bipartiteWeight A x y =
      (#A : ℝ) + ((Fintype.card ι : ℝ) - 2 * #A) * (if x ∈ A then 1 else 0) := by
  have h := sum_bipartiteWeight_mul A x (fun _ => 1)
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [h]
  split_ifs <;> ring

/-- The quadratic form, the degree-weighted mean and the degree-weighted norm of
`bipartiteWeight`, with `S_A = Σ_{x ∈ A} f x` and `T_A = Σ_{x ∈ A} f(x)²`. -/
theorem bipartiteWeight_moments (A : Finset ι) (f : ι → ℝ) :
    (∑ x, ∑ y, bipartiteWeight A x y * f x * f y =
        2 * (∑ x ∈ A, f x) * ((∑ x, f x) - ∑ x ∈ A, f x)) ∧
      (∑ x, (∑ y, bipartiteWeight A x y) * f x =
        ((Fintype.card ι : ℝ) - #A) * (∑ x ∈ A, f x) + (#A : ℝ) * ((∑ x, f x) - ∑ x ∈ A, f x)) ∧
      ∑ x, (∑ y, bipartiteWeight A x y) * f x ^ 2 =
        ((Fintype.card ι : ℝ) - #A) * (∑ x ∈ A, f x ^ 2) +
          (#A : ℝ) * ((∑ x, f x ^ 2) - ∑ x ∈ A, f x ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · have e : ∀ x, ∑ y, bipartiteWeight A x y * f x * f y =
        (∑ y ∈ A, f y) * f x +
          ((∑ y, f y) - 2 * ∑ y ∈ A, f y) * (if x ∈ A then f x else 0) := by
      intro x
      have h1 : ∑ y, bipartiteWeight A x y * f x * f y =
          f x * ∑ y, bipartiteWeight A x y * f y := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [h1, sum_bipartiteWeight_mul]
      split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Fintype.sum_ite_mem]
    ring
  · have e : ∀ x, (∑ y, bipartiteWeight A x y) * f x =
        (#A : ℝ) * f x + ((Fintype.card ι : ℝ) - 2 * #A) * (if x ∈ A then f x else 0) := by
      intro x; rw [sum_bipartiteWeight]; split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Fintype.sum_ite_mem]
    ring
  · have e : ∀ x, (∑ y, bipartiteWeight A x y) * f x ^ 2 =
        (#A : ℝ) * f x ^ 2 + ((Fintype.card ι : ℝ) - 2 * #A) * (if x ∈ A then f x ^ 2 else 0) := by
      intro x; rw [sum_bipartiteWeight]; split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Fintype.sum_ite_mem]
    ring

omit [DecidableEq ι] in
/-- `0 < |A| < n` when `A` is nonempty and not everything. -/
private theorem card_bounds {A : Finset ι} (hA : A.Nonempty) (hA' : A ≠ univ) :
    (0 : ℝ) < #A ∧ (#A : ℝ) < Fintype.card ι := by
  refine ⟨by exact_mod_cast hA.card_pos, ?_⟩
  have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hA')
  rw [card_univ] at this
  exact_mod_cast this

/-- **The complete bipartite graph has `μ₂ ≤ 0`.** -/
theorem walkSecondEigenvalueLE_bipartiteWeight_zero {A : Finset ι} (hA : A.Nonempty)
    (hA' : A ≠ univ) : WalkSecondEigenvalueLE (bipartiteWeight A) 0 := by
  intro f hf
  obtain ⟨hq, hm, -⟩ := bipartiteWeight_moments A f
  rw [hm] at hf
  rw [hq, zero_mul]
  obtain ⟨hk0, hkN⟩ := card_bounds hA hA'
  have h1 : ((Fintype.card ι : ℝ) - #A) * (2 * (∑ x ∈ A, f x) * ((∑ x, f x) - ∑ x ∈ A, f x)) =
      -(2 * #A * ((∑ x, f x) - ∑ x ∈ A, f x) ^ 2) := by
    linear_combination (2 * ((∑ x, f x) - ∑ x ∈ A, f x)) * hf
  have h2 : 0 ≤ 2 * #A * ((∑ x, f x) - ∑ x ∈ A, f x) ^ 2 := by positivity
  by_contra hc
  rw [not_le] at hc
  have := mul_pos (sub_pos.mpr hkN) hc
  linarith

/-- **The complete bipartite graph has `μ₂ = 0` exactly** on `n ≥ 3` vertices (one side then has
two vertices `x, y`, and `1_x − 1_y` has quadratic form `0`). -/
theorem walkSecondEigenvalueLE_bipartiteWeight_iff (hN : 3 ≤ Fintype.card ι) {A : Finset ι}
    (hA : A.Nonempty) (hA' : A ≠ univ) (lam : ℝ) :
    WalkSecondEigenvalueLE (bipartiteWeight A) lam ↔ 0 ≤ lam := by
  constructor
  · intro h
    have key : ∃ x y, x ≠ y ∧ (x ∈ A ↔ y ∈ A) := by
      by_cases h2 : 2 ≤ #A
      · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h2
        exact ⟨x, y, hxy, by simp [hx, hy]⟩
      · have h1 : #A = 1 := by have := hA.card_pos; omega
        have : 1 < #Aᶜ := by rw [card_compl]; omega
        obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp this
        rw [mem_compl] at hx hy
        exact ⟨x, y, hxy, by simp [hx, hy]⟩
    obtain ⟨x, y, hxy, hxyA⟩ := key
    obtain ⟨hk0, hkN⟩ := card_bounds hA hA'
    obtain ⟨hm1, hq1, hn1⟩ := moments_two_point (bipartiteWeight_symm A) hxy 1 (-1)
    have hdeq : ∑ z, bipartiteWeight A x z = ∑ z, bipartiteWeight A y z := by
      rw [sum_bipartiteWeight, sum_bipartiteWeight]
      by_cases hx : x ∈ A
      · simp [hx, hxyA.mp hx]
      · simp [hx, mt hxyA.mpr hx]
    have hpos : 0 < ∑ z, bipartiteWeight A y z := by
      rw [sum_bipartiteWeight]
      by_cases hy : y ∈ A
      · simp only [hy, if_true]; linarith
      · simp only [hy, if_false]; linarith
    have hw : bipartiteWeight A x y = 0 := by simp [bipartiteWeight, hxyA]
    have h1 := h _ (by rw [hm1, hdeq]; ring)
    rw [hq1, hn1, hw, bipartiteWeight_self, bipartiteWeight_self, hdeq] at h1
    nlinarith
  · intro h
    exact (walkSecondEigenvalueLE_bipartiteWeight_zero hA hA').mono (bipartiteWeight_nonneg A) h

/-- **The complete bipartite graph has `μ_n = −1` exactly** (test function `1` on `A`, `−1` off
it). -/
theorem walkSmallestEigenvalueGE_bipartiteWeight_iff {A : Finset ι} (hA : A.Nonempty)
    (hA' : A ≠ univ) (κ : ℝ) :
    WalkSmallestEigenvalueGE (bipartiteWeight A) κ ↔ κ ≤ -1 := by
  constructor
  · intro h
    obtain ⟨hk0, hkN⟩ := card_bounds hA hA'
    have h1 := h (fun x => if x ∈ A then 1 else -1)
    obtain ⟨hq, -, hn⟩ := bipartiteWeight_moments A (fun x => if x ∈ A then (1 : ℝ) else -1)
    rw [hq, hn] at h1
    have sA : ∑ x ∈ A, (if x ∈ A then (1 : ℝ) else -1) = #A := by
      rw [Finset.sum_congr rfl fun x hx => if_pos hx]; simp
    have sA2 : ∑ x ∈ A, (if x ∈ A then (1 : ℝ) else -1) ^ 2 = #A := by
      rw [Finset.sum_congr rfl fun x hx => by rw [if_pos hx]]; simp
    have s1 : ∑ x, (if x ∈ A then (1 : ℝ) else -1) = 2 * #A - Fintype.card ι := by
      have e : ∀ x, (if x ∈ A then (1 : ℝ) else -1) = 2 * (if x ∈ A then 1 else 0) - 1 :=
        fun x => by split_ifs <;> ring
      simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, Fintype.sum_ite_mem]
      simp
    have s2 : ∑ x, (if x ∈ A then (1 : ℝ) else -1) ^ 2 = Fintype.card ι := by
      have e : ∀ x, (if x ∈ A then (1 : ℝ) else -1) ^ 2 = 1 := fun x => by split_ifs <;> ring
      simp [e]
    rw [sA, sA2, s1, s2] at h1
    have hP : 0 < 2 * (#A : ℝ) * ((Fintype.card ι : ℝ) - #A) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  · intro h
    exact (walkSmallestEigenvalueGE_neg_one (bipartiteWeight_symm A)
      (bipartiteWeight_nonneg A)).mono (bipartiteWeight_nonneg A) h

/-- **Equality in (c) at `ε = 1/(n − 1)`: the complete bipartite graphs.** On `n ≥ 3` vertices,
for `∅ ≠ A ≠ ι` (in particular the star, `A = {o}`), `bipartiteWeight A` has
`μ₂ = ε − 1/(n − 1) = 0` exactly, `μ_n = −1/(n − 1) − (n − 2) ε = −1` exactly, and
`Σ_{u,v} w(u,v)²/(deg u · deg v) − n/(n − 1) = (n − 1)(n − 2) ε²`, with `ε = 1/(n − 1)`. -/
theorem bipartiteWeight_trace_bound_eq (hN : 3 ≤ Fintype.card ι) {A : Finset ι}
    (hA : A.Nonempty) (hA' : A ≠ univ) {ε : ℝ} (hε : ε = 1 / ((Fintype.card ι : ℝ) - 1)) :
    (∀ lam, WalkSecondEigenvalueLE (bipartiteWeight A) lam ↔
      ε - 1 / ((Fintype.card ι : ℝ) - 1) ≤ lam) ∧
    (∀ κ, WalkSmallestEigenvalueGE (bipartiteWeight A) κ ↔
      κ ≤ -(1 / ((Fintype.card ι : ℝ) - 1)) - ((Fintype.card ι : ℝ) - 2) * ε) ∧
    ∑ u, ∑ v, bipartiteWeight A u v ^ 2 /
        ((∑ x, bipartiteWeight A u x) * ∑ x, bipartiteWeight A v x) -
        (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) =
      ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε ^ 2 := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨hk0, hkN⟩ := card_bounds hA hA'
  refine ⟨fun lam => ?_, fun κ => ?_, ?_⟩
  · rw [hε, sub_self]; exact walkSecondEigenvalueLE_bipartiteWeight_iff hN hA hA' lam
  · have e : -(1 / ((Fintype.card ι : ℝ) - 1)) - ((Fintype.card ι : ℝ) - 2) * ε = -1 := by
      rw [hε]; field_simp; ring
    rw [e]; exact walkSmallestEigenvalueGE_bipartiteWeight_iff hA hA' κ
  · have hk : (#A : ℝ) * ((Fintype.card ι : ℝ) - #A) ≠ 0 :=
      (mul_pos hk0 (by linarith)).ne'
    have hNk : (Fintype.card ι : ℝ) - #A ≠ 0 := by linarith
    have hk0' : (#A : ℝ) ≠ 0 := hk0.ne'
    have e : ∀ u v, bipartiteWeight A u v ^ 2 /
        ((∑ x, bipartiteWeight A u x) * ∑ x, bipartiteWeight A v x) =
        bipartiteWeight A u v / ((#A : ℝ) * ((Fintype.card ι : ℝ) - #A)) := by
      intro u v
      by_cases h : (u ∈ A ↔ v ∈ A)
      · have h0 : bipartiteWeight A u v = 0 := if_pos h
        rw [h0]; simp
      · have hw : bipartiteWeight A u v = 1 := if_neg h
        rw [hw, sum_bipartiteWeight, sum_bipartiteWeight]
        by_cases hu : u ∈ A
        · have hv : v ∉ A := fun hv => h ⟨fun _ => hv, fun _ => hu⟩
          simp only [hu, hv, if_true, if_false]
          ring
        · have hv : v ∈ A := by
            by_contra hv
            exact h ⟨fun hu' => absurd hu' hu, fun hv' => absurd hv' hv⟩
          simp only [hu, hv, if_true, if_false]
          ring
    simp only [e, ← Finset.sum_div]
    have hvol := (bipartiteWeight_moments A (fun _ => 1)).2.1
    simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hvol
    rw [hvol, hε]
    field_simp
    ring

/-! #### Equality in (c) forces the spectrum `1, μ₂ (n − 2 times), μ_n` -/

/-- **The equality case of the convex step.** If `x_j ≤ ε` on a nonempty `s`, `Σ x_j = 0`,
`ε > 0` and `Σ x_j² = |s| (|s| − 1) ε²`, then every `x_j` is `ε` or `−(|s| − 1) ε`, and exactly
`|s| − 1` of them are `ε`. -/
theorem Finset.eq_or_eq_of_sum_sq_eq {α : Type*} [DecidableEq α] (s : Finset α) (hs : s.Nonempty)
    (x : α → ℝ) {ε : ℝ} (hε : 0 < ε) (hx : ∀ j ∈ s, x j ≤ ε) (hsum : ∑ j ∈ s, x j = 0)
    (heq : ∑ j ∈ s, x j ^ 2 = (#s : ℝ) * ((#s : ℝ) - 1) * ε ^ 2) :
    (∀ j ∈ s, x j = ε ∨ x j = -(((#s : ℝ) - 1) * ε)) ∧
      (#(s.filter fun j => x j = ε) : ℝ) = (#s : ℝ) - 1 := by
  obtain ⟨hlow, -⟩ := Finset.sum_sq_le_of_le_of_sum_eq_zero s x hx hsum
  have ht : ∀ j ∈ s, 0 ≤ (ε - x j) * (((#s : ℝ) - 1) * ε + x j) := fun j hj =>
    mul_nonneg (sub_nonneg.mpr (hx j hj)) (by linarith [hlow j hj])
  have htsum : ∑ j ∈ s, (ε - x j) * (((#s : ℝ) - 1) * ε + x j) = 0 := by
    have e : ∀ j, (ε - x j) * (((#s : ℝ) - 1) * ε + x j) =
        ((#s : ℝ) - 1) * ε ^ 2 + (2 - (#s : ℝ)) * ε * x j - x j ^ 2 := fun j => by ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, heq,
      Finset.sum_const, nsmul_eq_mul]
    ring
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg ht).mp htsum
  have hdich : ∀ j ∈ s, x j = ε ∨ x j = -(((#s : ℝ) - 1) * ε) := by
    intro j hj
    rcases mul_eq_zero.mp (hzero j hj) with h | h
    · left; linarith
    · right; linarith
  refine ⟨hdich, ?_⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun j => x j = ε) x
  have h1 : ∑ j ∈ s.filter (fun j => x j = ε), x j = #(s.filter fun j => x j = ε) * ε := by
    rw [Finset.sum_congr rfl fun j hj => (Finset.mem_filter.mp hj).2, Finset.sum_const,
      nsmul_eq_mul]
  have h2 : ∑ j ∈ s.filter (fun j => ¬x j = ε), x j =
      #(s.filter fun j => ¬x j = ε) * (-(((#s : ℝ) - 1) * ε)) := by
    rw [Finset.sum_congr rfl fun j hj => ((hdich j (Finset.mem_filter.mp hj).1).resolve_left
      (Finset.mem_filter.mp hj).2), Finset.sum_const, nsmul_eq_mul]
  have hcard := Finset.card_filter_add_card_filter_not (s := s) (fun j => x j = ε)
  have hcard' : (#(s.filter fun j => x j = ε) : ℝ) + #(s.filter fun j => ¬x j = ε) = #s := by
    exact_mod_cast hcard
  rw [h1, h2, hsum] at hsplit
  have hs0 : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  have h3 : ((#(s.filter fun j => x j = ε) : ℝ) * #s - #s * ((#s : ℝ) - 1)) * ε = 0 := by
    have : (#(s.filter fun j => ¬x j = ε) : ℝ) = #s - #(s.filter fun j => x j = ε) := by
      linarith
    rw [this] at hsplit
    linear_combination hsplit
  have h4 := (mul_eq_zero.mp h3).resolve_right hε.ne'
  have h5 : (#s : ℝ) * ((#(s.filter fun j => x j = ε) : ℝ) - ((#s : ℝ) - 1)) = 0 := by
    linear_combination h4
  have h6 := (mul_eq_zero.mp h5).resolve_left hs0.ne'
  linarith

/-- The nontrivial eigenvalues of the walk: there are `n − 1` of them, each is at most `μ₂`, and
they sum to `−1`. -/
theorem walkMatrix_erase_topIndex_facts [Nontrivial ι] {w : ι → ι → ℝ}
    (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (hdiag : ∀ u, w u u = 0) (hdeg : ∀ u, 0 < ∑ v, w u v) :
    ((#(univ.erase (Matrix.IsHermitian.topIndex ι)) : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 ∧
      (∀ j ∈ univ.erase (Matrix.IsHermitian.topIndex ι),
        (walkMatrix_isHermitian hsymm).eigenvalues j ≤
          (walkMatrix_isHermitian hsymm).secondEigenvalue) ∧
      ∑ j ∈ univ.erase (Matrix.IsHermitian.topIndex ι),
        (walkMatrix_isHermitian hsymm).eigenvalues j = -1 := by
  obtain ⟨htop, htr, -⟩ := walkMatrix_eigenvalues_facts hsymm hnn hdiag hdeg
  refine ⟨?_, fun j hj => (walkMatrix_isHermitian hsymm).eigenvalues_le_secondEigenvalue
    (Finset.ne_of_mem_erase hj), ?_⟩
  · rw [card_erase_of_mem (mem_univ _), card_univ, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  · have := Finset.add_sum_erase univ (walkMatrix_isHermitian hsymm).eigenvalues
      (mem_univ (Matrix.IsHermitian.topIndex ι))
    rw [htop, htr] at this
    linarith

/-- **Equality in (c) pins down the spectrum.** Under the hypotheses of `walkMatrix_trace_bound`,
with `ε = μ₂ + 1/(n − 1) > 0`, suppose
`Σ_{u,v} w(u,v)²/(deg u · deg v) − n/(n − 1) = (n − 1)(n − 2) ε²`. Then every eigenvalue `μ_j`
other than the top one is `μ₂` or `−1/(n − 1) − (n − 2) ε`, and exactly `n − 2` of them equal
`μ₂`: the walk has spectrum `1, μ₂` (`n − 2` times) and `μ_n = −1/(n − 1) − (n − 2) ε` (once).
For `ε = 0` (the complete graph) all `n − 1` nontrivial eigenvalues equal `μ₂`, so `ε > 0` is
needed for the count. -/
theorem walkMatrix_eigenvalues_of_sum_sq_eq [Nontrivial ι] {w : ι → ι → ℝ}
    (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (hdiag : ∀ u, w u u = 0) (hdeg : ∀ u, 0 < ∑ v, w u v) {ε : ℝ}
    (hε : ε = (walkMatrix_isHermitian hsymm).secondEigenvalue + 1 / ((Fintype.card ι : ℝ) - 1))
    (hpos : 0 < ε)
    (heq : ∑ u, ∑ v, w u v ^ 2 / ((∑ x, w u x) * ∑ x, w v x) -
        (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1) =
      ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ε ^ 2) :
    (∀ j ∈ univ.erase (Matrix.IsHermitian.topIndex ι),
      (walkMatrix_isHermitian hsymm).eigenvalues j =
          (walkMatrix_isHermitian hsymm).secondEigenvalue ∨
        (walkMatrix_isHermitian hsymm).eigenvalues j =
          -(1 / ((Fintype.card ι : ℝ) - 1)) - ((Fintype.card ι : ℝ) - 2) * ε) ∧
      (#((univ.erase (Matrix.IsHermitian.topIndex ι)).filter fun j =>
        (walkMatrix_isHermitian hsymm).eigenvalues j =
          (walkMatrix_isHermitian hsymm).secondEigenvalue) : ℝ) =
        (Fintype.card ι : ℝ) - 2 := by
  obtain ⟨hcard, hle, hsum⟩ := walkMatrix_erase_topIndex_facts hsymm hnn hdiag hdeg
  have hN : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.one_lt_card
  have hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have hc1 : ((Fintype.card ι : ℝ) - 1) * (1 / ((Fintype.card ι : ℝ) - 1)) = 1 := by field_simp
  have hs : (univ.erase (Matrix.IsHermitian.topIndex ι)).Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < ((#(univ.erase (Matrix.IsHermitian.topIndex ι)) : ℕ) : ℝ) := by
      rw [hcard]; linarith
    exact_mod_cast this
  have hx : ∀ j ∈ univ.erase (Matrix.IsHermitian.topIndex ι),
      (walkMatrix_isHermitian hsymm).eigenvalues j + 1 / ((Fintype.card ι : ℝ) - 1) ≤ ε :=
    fun j hj => by rw [hε]; linarith [hle j hj]
  have hxsum : ∑ j ∈ univ.erase (Matrix.IsHermitian.topIndex ι),
      ((walkMatrix_isHermitian hsymm).eigenvalues j + 1 / ((Fintype.card ι : ℝ) - 1)) = 0 := by
    rw [Finset.sum_add_distrib, hsum, Finset.sum_const, nsmul_eq_mul, hcard, hc1]; ring
  have hxsq : ∑ j ∈ univ.erase (Matrix.IsHermitian.topIndex ι),
      ((walkMatrix_isHermitian hsymm).eigenvalues j + 1 / ((Fintype.card ι : ℝ) - 1)) ^ 2 =
      ((#(univ.erase (Matrix.IsHermitian.topIndex ι)) : ℕ) : ℝ) *
        (((#(univ.erase (Matrix.IsHermitian.topIndex ι)) : ℕ) : ℝ) - 1) * ε ^ 2 := by
    have : Nonempty ι := inferInstance
    rw [sum_erase_topIndex_walkMatrix_eigenvalues_add_sq hsymm hnn hdiag hdeg, heq, hcard]
    ring
  obtain ⟨hdich, hcnt⟩ := Finset.eq_or_eq_of_sum_sq_eq _ hs _ hpos hx hxsum hxsq
  rw [hcard] at hdich hcnt
  refine ⟨fun j hj => ?_, ?_⟩
  · rcases hdich j hj with h | h
    · left; rw [hε] at h; linarith
    · right; linarith
  · rw [show (Fintype.card ι : ℝ) - 2 = (Fintype.card ι : ℝ) - 1 - 1 by ring, ← hcnt]
    congr 2
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj, h⟩; exact ⟨hj, by rw [h, hε]⟩
    · rintro ⟨hj, h⟩; exact ⟨hj, by rw [hε] at h; linarith⟩


/-- **The spectrum of the heavy vertex family.** For `a > 1` on `n ≥ 3` vertices, the walk on
`starWeight o 1 a` has `μ₂ = −1/(a + n − 2)`, attained by exactly `n − 2` of the nontrivial
eigenvalues, and `μ_n = −a/(a + n − 2)`. (`[Nontrivial ι]` follows from `n ≥ 3`; it is needed to
state `μ₂`.) -/
theorem starWeight_walkMatrix_spectrum [Nontrivial ι] (hN : 3 ≤ Fintype.card ι) (o : ι) {a : ℝ}
    (ha : 1 < a) :
    (walkMatrix_isHermitian (starWeight_symm o 1 a)).secondEigenvalue =
        -(1 / (a + Fintype.card ι - 2)) ∧
      (walkMatrix_isHermitian (starWeight_symm o 1 a)).smallestEigenvalue =
        -(a / (a + Fintype.card ι - 2)) ∧
      (#((univ.erase (Matrix.IsHermitian.topIndex ι)).filter fun j =>
        (walkMatrix_isHermitian (starWeight_symm o 1 a)).eigenvalues j =
          (walkMatrix_isHermitian (starWeight_symm o 1 a)).secondEigenvalue) : ℝ) =
        (Fintype.card ι : ℝ) - 2 := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have h1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have h2 : a + (Fintype.card ι : ℝ) - 2 ≠ 0 := by linarith
  have ha0 : 0 < a := by linarith
  have hsymm := starWeight_symm (ι := ι) o 1 a
  have hnn := starWeight_nonneg (ι := ι) o zero_le_one ha0.le
  have hdiag := starWeight_self (ι := ι) o 1 a
  have hdeg := starWeight_deg_pos (by omega) o ha0
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (a - 1) / (((Fintype.card ι : ℝ) - 1) * (a + Fintype.card ι - 2)) :=
    ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hε]; exact div_pos (by linarith) (mul_pos (by linarith) (by linarith))
  obtain ⟨hiff, -⟩ := starWeight_stationary_le_sharp hN o ha.le hε
  obtain ⟨hκ, hsq⟩ := starWeight_trace_bound_eq hN o ha.le hε
  have h2nd := walkMatrix_secondEigenvalue_eq_of_forall_iff hsymm hnn hdeg hiff
  have hbot := walkMatrix_smallestEigenvalue_eq_of_forall_iff hsymm hdeg hκ
  have hε' : ε = (walkMatrix_isHermitian hsymm).secondEigenvalue +
      1 / ((Fintype.card ι : ℝ) - 1) := by rw [h2nd]; ring
  refine ⟨?_, ?_, (walkMatrix_eigenvalues_of_sum_sq_eq hsymm hnn hdiag hdeg hε' hεpos hsq).2⟩
  · rw [h2nd, hε]; field_simp; ring
  · rw [hbot, hε]; field_simp; ring

/-- **The spectrum of the heavy edge family.** For `a > 1` on `n ≥ 3` vertices and `o ≠ o'`,
the walk on `edgeWeight o o' 1 a (a(2a − 1))` has `μ₂ = −1/(2a + n − 3)`, attained by exactly
`n − 2` of the nontrivial eigenvalues, and `μ_n = −(2a − 1)/(2a + n − 3)`. -/
theorem edgeWeight_walkMatrix_spectrum [Nontrivial ι] (hN : 3 ≤ Fintype.card ι) {o o' : ι}
    (hoo : o ≠ o') {a : ℝ} (ha : 1 < a) :
    (walkMatrix_isHermitian (edgeWeight_symm o o' 1 a (a * (2 * a - 1)))).secondEigenvalue =
        -(1 / (2 * a + Fintype.card ι - 3)) ∧
      (walkMatrix_isHermitian (edgeWeight_symm o o' 1 a (a * (2 * a - 1)))).smallestEigenvalue =
        -((2 * a - 1) / (2 * a + Fintype.card ι - 3)) ∧
      (#((univ.erase (Matrix.IsHermitian.topIndex ι)).filter fun j =>
        (walkMatrix_isHermitian (edgeWeight_symm o o' 1 a (a * (2 * a - 1)))).eigenvalues j =
          (walkMatrix_isHermitian
            (edgeWeight_symm o o' 1 a (a * (2 * a - 1)))).secondEigenvalue) : ℝ) =
        (Fintype.card ι : ℝ) - 2 := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have h1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have h2 : 2 * a + (Fintype.card ι : ℝ) - 3 ≠ 0 := by linarith
  have hd1 : 0 < 2 * a + (Fintype.card ι : ℝ) - 3 := by linarith
  have ha0 : 0 < a := by linarith
  have hsymm := edgeWeight_symm (ι := ι) o o' 1 a (a * (2 * a - 1))
  have hnn := edgeWeight_nonneg (ι := ι) o o' zero_le_one ha0.le (by nlinarith : (0 : ℝ) ≤
    a * (2 * a - 1))
  have hdiag := edgeWeight_self (ι := ι) o o' 1 a (a * (2 * a - 1))
  obtain ⟨d0, d0', d1⟩ := edgeWeight_heavy_degrees (ι := ι) hoo a
  have hdeg : ∀ x, 0 < ∑ y, edgeWeight o o' 1 a (a * (2 * a - 1)) x y := by
    intro x
    by_cases hx : x = o
    · rw [hx, d0]; positivity
    · by_cases hx' : x = o'
      · rw [hx', d0']; positivity
      · rw [d1 x hx hx']; exact hd1
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ,
      ε = 2 * (a - 1) / (((Fintype.card ι : ℝ) - 1) * (2 * a + Fintype.card ι - 3)) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hε]; exact div_pos (by linarith) (mul_pos (by linarith) hd1)
  obtain ⟨hiff, -, -⟩ := edgeWeight_weight_div_sqrt_le_sharp hN hoo ha.le hε
  obtain ⟨hκ, hsq⟩ := edgeWeight_trace_bound_eq hN hoo ha.le hε
  have h2nd := walkMatrix_secondEigenvalue_eq_of_forall_iff hsymm hnn hdeg hiff
  have hbot := walkMatrix_smallestEigenvalue_eq_of_forall_iff hsymm hdeg hκ
  have hε' : ε = (walkMatrix_isHermitian hsymm).secondEigenvalue +
      1 / ((Fintype.card ι : ℝ) - 1) := by rw [h2nd]; ring
  refine ⟨?_, ?_, (walkMatrix_eigenvalues_of_sum_sq_eq hsymm hnn hdiag hdeg hε' hεpos hsq).2⟩
  · rw [h2nd, hε]; field_simp; ring
  · rw [hbot, hε]; field_simp; ring

/-- **The spectrum of the complete bipartite graphs**, in particular the star. For `∅ ≠ A ≠ ι`
on `n ≥ 3` vertices, the walk on `bipartiteWeight A` has `μ₂ = 0`, attained by exactly `n − 2`
of the nontrivial eigenvalues, and `μ_n = −1`. -/
theorem bipartiteWeight_walkMatrix_spectrum [Nontrivial ι] (hN : 3 ≤ Fintype.card ι)
    {A : Finset ι} (hA : A.Nonempty) (hA' : A ≠ univ) :
    (walkMatrix_isHermitian (bipartiteWeight_symm A)).secondEigenvalue = 0 ∧
      (walkMatrix_isHermitian (bipartiteWeight_symm A)).smallestEigenvalue = -1 ∧
      (#((univ.erase (Matrix.IsHermitian.topIndex ι)).filter fun j =>
        (walkMatrix_isHermitian (bipartiteWeight_symm A)).eigenvalues j =
          (walkMatrix_isHermitian (bipartiteWeight_symm A)).secondEigenvalue) : ℝ) =
        (Fintype.card ι : ℝ) - 2 := by
  have hNr : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  obtain ⟨hk0, hkN⟩ := card_bounds hA hA'
  have hsymm := bipartiteWeight_symm A
  have hnn := bipartiteWeight_nonneg A
  have hdiag := bipartiteWeight_self A
  have hdeg : ∀ x, 0 < ∑ y, bipartiteWeight A x y := by
    intro x
    rw [sum_bipartiteWeight]
    by_cases hx : x ∈ A
    · simp only [hx, if_true]; linarith
    · simp only [hx, if_false]; linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / ((Fintype.card ι : ℝ) - 1) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; exact div_pos one_pos (by linarith)
  obtain ⟨hiff, hκ, hsq⟩ := bipartiteWeight_trace_bound_eq hN hA hA' hε
  have h2nd := walkMatrix_secondEigenvalue_eq_of_forall_iff hsymm hnn hdeg hiff
  have hbot := walkMatrix_smallestEigenvalue_eq_of_forall_iff hsymm hdeg hκ
  have hε' : ε = (walkMatrix_isHermitian hsymm).secondEigenvalue +
      1 / ((Fintype.card ι : ℝ) - 1) := by rw [h2nd]; ring
  refine ⟨?_, ?_, (walkMatrix_eigenvalues_of_sum_sq_eq hsymm hnn hdiag hdeg hε' hεpos hsq).2⟩
  · rw [h2nd, hε]; ring
  · rw [hbot, hε]
    have h1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring

end Families
