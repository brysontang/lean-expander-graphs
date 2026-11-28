/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.NegativeRigidity
import Expanders.CompleteComplexGeneral
import Expanders.SimplexRigidity

/-!
# Equality in trickling down for `2`-complexes, and an exactly sharp family

Let `m ≥ 0` be a weight on the triangles of a pure `2`-dimensional complex (a top weight
`IsTopWeight K 2 m`), `w = linkWeightOf m ∅` its weighted underlying graph, `M = D⁻¹ W` the random
walk on it, and suppose every vertex link `linkWeightOf m {z}` has random-walk second eigenvalue at
most `lam`. With `γ = lam / (1 − lam)`, trickling down (Oppenheim; `trickling_down_weighted`) says
that on a connected complex the walk `M` has second eigenvalue `μ ≤ γ` when `lam < 1/2`. This file
decides when `μ = γ`, and shows that equality happens for every `lam ∈ (0, 1/2)`.

The **edge operator** is `(E_lam f)(u, v) = Σ_x m{u, v, x} f(x) − lam · w(u, v) · (f u + f v)`
(`edgeOperator`).

## Main results

(i) The equality criterion.
* `tricklingEquality_iff`, `walkEigenspace_eq_edgeKernel`,
  `finrank_walkEigenspace_eq_finrank_edgeKernel`: for `m ≥ 0` supported on three-element sets,
  vertex links of second eigenvalue at most `lam`, and `lam ≠ 1`, the following sets of `f`
  coincide (no connectivity is needed): the `γ`-eigenspace of `M`; `ker E_lam`; the `f` all
  of whose localisations `f − γ f(z)` are `lam`-eigenfunctions of the vertex links; and
  (`IsTopWeight.tricklingEquality_iff_upWalk`) the `f` whose lift `f u + f v` is an eigenfunction,
  on the edges, of the lazy up-down walk on edges with eigenvalue `2 (1 + lam) / 3`, or of the
  non-lazy one with eigenvalue `lam + 1/2`. The lift is injective on the vertices
  (`IsPure.eq_of_liftSum_eq`). So `mult_M(γ) = dim ker E_lam`. **Proved.**
* `eigen_of_edgeOperator_eq_zero`: `ker E_lam` lies in the `γ`-eigenspace for every `lam ≠ 1`,
  with no bound on the links. **Proved.**
* `IsTopWeight.eigen_eq_one_or_le`, `IsTopWeight.eq_of_eigen_one`: on a connected complex every
  eigenvalue of `M` other than the simple eigenvalue `1` is at most `γ`. **Proved.**
* `IsTopWeight.isLeast_iff_exists_edgeOperator_eq_zero`: for `lam < 1/2`, on a connected complex,
  `μ = γ` exactly when `ker E_lam` contains a function that is nonzero at a vertex. **Proved.**
* `edgeOperator_const_half`, `IsTopWeight.not_isLeast_half`: at `lam = 1/2` the constants lie in
  `ker E_{1/2}` but `μ < 1 = γ`, so the last statement fails there. **Proved.**

(ii) The structure of the equality case.
* `IsTopWeight.exists_extremal_edge_of_isLeast`: if `μ = γ`, some edge `z₁ z₂` has both vertex links
  of second eigenvalue exactly `lam`. So `lam = max_z λ_z`, and the set `Z` of vertices attaining
  it spans an edge. **Proved.**
* `eq_mul_of_link_lt`, `eq_zero_of_link_lt_of_link_lt`: every `γ`-eigenfunction satisfies
  `f u = γ f(z)` for `z ∉ Z` and every neighbour `u` of `z`, and vanishes at both ends of every
  edge disjoint from `Z` and at all their neighbours (for `lam ≠ 1/2`). **Proved.**

(iii) Special values.
* `IsTopWeight.mem_of_link_neg`: for any weight, if every vertex link has a negative bound, the
  connected complex is complete on its vertices; `complete_two_isLeast`: conversely, with uniform
  weights the complete complex on `N` points has `λ_z = −1/(N − 2)` and `μ = −1/(N − 1) = γ`;
  `twoHeavyWeight_spec`: for a non-uniform weight on the complete complex on five points a vertex
  link has positive second eigenvalue, so the converse needs the uniform weight. **Proved.** (The
  first two are short consequences of `Expanders/NegativeRigidity.lean` and
  `Expanders/CompleteComplexGeneral.lean`.)
* `IsTopWeight.isLeast_zero_iff_det_eq_zero`: when the links have bound `lam = 0`, `μ = 0` exactly
  when the weight matrix `(w(u, v))` on the vertices is singular. **Proved.**

(iv) An exactly sharp family.
* `tetraPendant_sharp`: the boundary of a tetrahedron with pendant triangles of weight `t > 0` on
  two opposite edges has `λ_0 = … = λ_3 = x(t)`, the positive root of
  `2 (t + 2) x² + (t + 2) x − t`, `λ_4 = λ_5 = −1`, and `μ = x / (1 − x)` exactly, i.e.
  `(2t + 6) μ² + (2 − t) μ − t = 0`. **Proved.**
* `tetraPendant_root_existsUnique`, `tetraPendant_root_strictMono`, `tetraPendant_root_of_mem_Ioo`:
  `x(t)` is well defined and increases from `0` to `1/2`. **Proved.**
* `exists_isLeast_trickling_down_two`: so for **every** `lam ∈ (0, 1/2)` there is a connected
  weighted `2`-complex on six points whose vertex links have second eigenvalue at most `lam` and
  whose underlying graph has second eigenvalue exactly `lam / (1 − lam)`. **Proved.**
* The uniform pendant family for `k = 1, 2`: `tetraPendantWeight_one_eq_uniformWeight` (`k = 1`
  is `X_1`), and `pendantTwo_sharp`, `pendantTwo_root`: two uniform pendant triangles on each of
  two opposite edges give `λ_z = (√5 − 1)/4` on the tetrahedron, `−1` at the pendants, and
  `μ = 1/√5` exactly, as for `X_2`; `pendantTwo_isLocalSpectralExpander_iff`: in the unweighted
  language, this complex is a `μ`-local spectral expander exactly for `μ ≥ 1/√5`. **Proved.**

(v) One polytope.
* `octahedron_sharp`: the boundary of the octahedron (cross-polytope in `ℝ³`) has every vertex
  link and the underlying graph of second eigenvalue exactly `0`. **Proved.**

## What is not formalised here
* The family with `k` uniform pendant triangles on each of two opposite edges (`t = k`), stated
  alongside `X_t` in the conjecture, for `k ≥ 3`; only `k = 1` and `k = 2` are formalised.
* (v) The other regular polytopes (higher cross-polytopes and simplices along the whole chain, the
  icosahedron, the 600-cell), and (vi) the computer census of equality cases on at most eight
  points; both are computational remarks, checked numerically and exactly by the proposer and two
  skeptics. (Simplices are the complete complexes, `trickling_down_complete`.)
* An explicit non-uniform weight on a complete complex with `max_z λ_z < 0` for which equality
  `μ = γ` fails (seen numerically by the skeptic). That `max_z λ_z < 0` itself can fail for a
  non-uniform weight on the complete complex is `twoHeavyWeight_spec`.
* The variant of `IsTopWeight.isLeast_zero_iff_det_eq_zero` with the `0/1` adjacency matrix, which
  the conjecture itself lists as unproved.

## How this was found
By computation, then proved. The proposer computed second eigenvalues of all vertex links and of
the underlying graph over every isomorphism class of pure `2`-complexes on at most seven points,
part of the eight-point range, random weighted complexes and polytope boundaries, compared `μ` with
`γ` and `dim ker E_lam` with the multiplicity of `γ`, and found `X_t` with exact symbolic
algebra. Two independent skeptics re-derived the proof, rebuilt the census with their own
generator (checked against a Pólya count), and found no counterexample. The proof here is the
equality case of Garland's method: summed over the vertices, the nonnegative slacks
`lam ‖h_z‖² − ⟨h_z, W_z h_z⟩` of the localisations `h_z = f − γ f(z)` add up to
`(1 − γ)(lam − (1 − lam) γ) ‖f‖²`, which vanishes at `γ = lam / (1 − lam)`
(`garland_local_eq_of_eigen`); a localisation that attains the link bound is a link
eigenfunction (`WalkSecondEigenvalueLE.eigen_of_le`), and that eigen-equation is the edge
equation (`local_eigen_iff_edge`). Attainment of the second eigenvalue
(`exists_eigen_of_isLeast`) uses that the walk has finitely many eigenvalues.

## Literature
A search of the high-dimensional-expander literature (web searches on trickle-down tightness and
on the equality case of Garland's method; Oppenheim's papers arXiv:1407.8517 and
arXiv:1709.04431, Kaufman–Oppenheim arXiv:1707.02799, Alev–Lau arXiv:2001.02827, Chen–Liu
arXiv:2609.19514, the surveys arXiv:2304.10106, and about thirty further papers and lecture
notes read by the literature skeptic) found:
* trickling down itself: H. Garland, *p-adic curvature and the cohomology of discrete subgroups of
  p-adic groups*, Ann. of Math. 97 (1973); I. Oppenheim, *Local spectral expansion approach to
  high dimensional expanders part I*, Discrete Comput. Geom. 59 (2018), arXiv:1709.04431;
* **near** sharpness only: S. Liu, S. Mohanty, T. Schramm, E. Yang, *Local and global expansion in
  random geometric graphs*, STOC 2023, arXiv:2210.00158, Proposition 1.8: for each
  `lam ∈ (0, 1/2]` and `η > 0` a random geometric `2`-complex with vertex links at most `lam` and
  second eigenvalue at least `lam / (1 − lam) − η`;
* exact equality for **uniform** weights on the triangle complexes of tight distance-regular
  graphs (Johnson graphs `J(2d, d)`, halved cubes, Taylor graphs such as the icosahedron):
  A. Jurišić, J. Koolen, P. Terwilliger, *Tight distance-regular graphs*, J. Algebraic Combin. 12
  (2000), arXiv:math/0108196 (Theorem 12.4 and the notion of an edge tight with respect to
  `θ₁`, which for those graphs is the edge-kernel condition); they phrase it as a local
  eigenvalue, not as trickling down;
* exact equality for complete complexes (folklore; `trickling_down_complete` in this project).

Not found in this search: the equality criterion for general weights stated as the equality case of
trickling down, the structure statements (ii), and an explicit finite complex attaining
`lam / (1 − lam)` exactly for every `lam ∈ (0, 1/2)` (the family `tetraPendant`). These are small
observations; the criterion should be regarded as folklore-level, the family as a modest
strengthening of Liu–Mohanty–Schramm–Yang's Proposition 1.8 from approximate to exact.
-/

open Finset

variable {ι : Type*} [Fintype ι]

section Graph

variable {w : ι → ι → ℝ}

/-- If `2 s β + s² κ ≤ 0` for every real `s`, then `β = 0`. -/
private theorem eq_zero_of_forall_two_mul_add_sq_le {β κ : ℝ}
    (h : ∀ s : ℝ, 2 * s * β + s ^ 2 * κ ≤ 0) : β = 0 := by
  by_contra hβ
  have hc : 0 < |κ| + 1 := by positivity
  have h1 := h (β / (|κ| + 1))
  have h2 : -|κ| ≤ κ := neg_abs_le κ
  have hb : 0 < β ^ 2 := by positivity
  have e : 2 * (β / (|κ| + 1)) * β + (β / (|κ| + 1)) ^ 2 * κ =
      β ^ 2 * (2 * (|κ| + 1) + κ) / (|κ| + 1) ^ 2 := by
    field_simp
  rw [e] at h1
  have h3 : 0 < β ^ 2 * (2 * (|κ| + 1) + κ) := by
    apply mul_pos hb
    linarith [abs_nonneg κ]
  have h4 : 0 < β ^ 2 * (2 * (|κ| + 1) + κ) / (|κ| + 1) ^ 2 := by positivity
  linarith

omit [Fintype ι] in
private theorem row_eq_zero_of_deg_eq_zero (hnn : ∀ u v, 0 ≤ w u v) {u : ι} [Fintype ι]
    (h : ∑ v, w u v = 0) (v : ι) : w u v = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun v _ => hnn u v).mp h v (Finset.mem_univ v)

/-- **Maximisers of the Rayleigh quotient are eigenfunctions.** Let `w` be symmetric and
nonnegative, with `deg u = Σ_v w u v`, and let the walk on `w` have second eigenvalue at most
`lam`. If `f` has degree-weighted mean zero and attains the bound,
`lam · Σ deg u · f u² ≤ Σ w u v f u f v`, then `f` is a `lam`-eigenfunction:
`Σ_v w u v f v = lam · deg u · f u` for every `u`.

Degenerate cases: `f = 0` is allowed (it is an eigenfunction); at a vertex of degree `0` both sides
are `0`. The proof is the first variation of the Rayleigh quotient in the direction
`g = (W f − lam D f) / D` (with `x / 0 = 0`), which has mean zero. -/
theorem WalkSecondEigenvalueLE.eigen_of_le (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) {lam : ℝ} (h : WalkSecondEigenvalueLE w lam) {f : ι → ℝ}
    (hf : ∑ u, (∑ v, w u v) * f u = 0)
    (hle : lam * ∑ u, (∑ v, w u v) * f u ^ 2 ≤ ∑ u, ∑ v, w u v * f u * f v) (u : ι) :
    ∑ v, w u v * f v = lam * (∑ v, w u v) * f u := by
  set r : ι → ℝ := fun u => ∑ v, w u v * f v - lam * (∑ v, w u v) * f u with hr
  set g : ι → ℝ := fun u => r u / ∑ v, w u v with hg
  have hD0 : ∀ u, 0 ≤ ∑ v, w u v := fun u => Finset.sum_nonneg fun v _ => hnn u v
  -- at a vertex of degree zero, `r` vanishes
  have hr0 : ∀ u, ∑ v, w u v = 0 → r u = 0 := by
    intro u hu
    simp only [hr, row_eq_zero_of_deg_eq_zero hnn hu, zero_mul, Finset.sum_const_zero,
      mul_zero, sub_zero]
  have hdg : ∀ u, (∑ v, w u v) * g u = r u := by
    intro u
    rcases (hD0 u).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, hr0 u h0.symm]
    · simp only [hg]
      field_simp
  -- `Σ r = 0`
  have hsumr : ∑ u, r u = 0 := by
    simp only [hr, Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    have e1 : ∑ y, ∑ x, w x y * f y = ∑ y, (∑ v, w y v) * f y := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by rw [hsymm x y]
    rw [e1, hf]
    have e2 : ∑ x, lam * (∑ v, w x v) * f x = lam * ∑ x, (∑ v, w x v) * f x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e2, hf]
    ring
  have hgmean : ∑ u, (∑ v, w u v) * g u = 0 := by
    simp only [hdg]
    exact hsumr
  -- the perturbation `f + s g`
  have key : ∀ s : ℝ, 2 * s * (∑ u, g u * r u) +
      s ^ 2 * (∑ u, ∑ v, w u v * g u * g v - lam * ∑ u, (∑ v, w u v) * g u ^ 2) ≤ 0 := by
    intro s
    have hm : ∑ u, (∑ v, w u v) * (f u + s * g u) = 0 := by
      have e : ∀ u, (∑ v, w u v) * (f u + s * g u) =
          (∑ v, w u v) * f u + s * ((∑ v, w u v) * g u) := fun u => by ring
      simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hf, hgmean, mul_zero, add_zero]
    have h1 := h (fun u => f u + s * g u) hm
    -- expand both sides
    have eQ : ∑ u, ∑ v, w u v * (f u + s * g u) * (f v + s * g v) =
        ∑ u, ∑ v, w u v * f u * f v + 2 * s * ∑ u, g u * ∑ v, w u v * f v +
          s ^ 2 * ∑ u, ∑ v, w u v * g u * g v := by
      have e : ∀ u v, w u v * (f u + s * g u) * (f v + s * g v) =
          w u v * f u * f v + s * (w u v * f u * g v) + s * (w u v * g u * f v) +
            s ^ 2 * (w u v * g u * g v) := fun u v => by ring
      simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
      have e2 : ∑ u, ∑ v, w u v * f u * g v = ∑ u, g u * ∑ v, w u v * f v := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by rw [hsymm u v]; ring
      have e3 : ∑ u, ∑ v, w u v * g u * f v = ∑ u, g u * ∑ v, w u v * f v := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [e2, e3]
      ring
    have eN : ∑ u, (∑ v, w u v) * (f u + s * g u) ^ 2 =
        ∑ u, (∑ v, w u v) * f u ^ 2 + 2 * s * ∑ u, g u * ((∑ v, w u v) * f u) +
          s ^ 2 * ∑ u, (∑ v, w u v) * g u ^ 2 := by
      have e : ∀ u, (∑ v, w u v) * (f u + s * g u) ^ 2 =
          (∑ v, w u v) * f u ^ 2 + 2 * s * (g u * ((∑ v, w u v) * f u)) +
            s ^ 2 * ((∑ v, w u v) * g u ^ 2) := fun u => by ring
      simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [eQ, eN] at h1
    have er : ∑ u, g u * r u =
        ∑ u, g u * ∑ v, w u v * f v - lam * ∑ u, g u * ((∑ v, w u v) * f u) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp only [hr]
      ring
    rw [er]
    nlinarith
  have hβ := eq_zero_of_forall_two_mul_add_sq_le key
  -- `Σ g r = Σ r² / deg = 0` forces `r = 0`
  have hterm : ∀ u, 0 ≤ g u * r u := by
    intro u
    rcases (hD0 u).eq_or_lt with h0 | h0
    · rw [hr0 u h0.symm, mul_zero]
    · have : g u * r u = r u ^ 2 / ∑ v, w u v := by
        simp only [hg]
        ring
      rw [this]
      positivity
  have hgr := (Finset.sum_eq_zero_iff_of_nonneg fun u _ => hterm u).mp hβ u (Finset.mem_univ u)
  have hru : r u = 0 := by
    rcases (hD0 u).eq_or_lt with h0 | h0
    · exact hr0 u h0.symm
    · have : g u * r u = r u ^ 2 / ∑ v, w u v := by
        simp only [hg]
        ring
      rw [this] at hgr
      have := (div_eq_zero_iff.mp hgr).resolve_right h0.ne'
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have : ∑ v, w u v * f v - lam * (∑ v, w u v) * f u = 0 := hru
  linarith


omit [Fintype ι] in
/-- On an eigenfunction (`Σ_v w u v f v = γ · deg u · f u` for all `u`), the quadratic form is
`γ` times the degree-weighted norm. No hypothesis on `w`; `f = 0` gives `0 = 0`. -/
theorem sum_mul_mul_eq_of_eigen [Fintype ι] {f : ι → ℝ} {γ : ℝ}
    (heig : ∀ u, ∑ v, w u v * f v = γ * (∑ v, w u v) * f u) :
    ∑ u, ∑ v, w u v * f u * f v = γ * ∑ u, (∑ v, w u v) * f u ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h1 : ∑ v, w u v * f u * f v = f u * ∑ v, w u v * f v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [h1, heig u]
  ring

omit [Fintype ι] in
/-- An eigenfunction for an eigenvalue `γ ≠ 1` of the walk on a symmetric `w` has
degree-weighted mean zero. For `γ = 1` this fails: the constants are `1`-eigenfunctions. -/
theorem sum_deg_mul_eq_zero_of_eigen [Fintype ι] (hsymm : ∀ u v, w u v = w v u) {f : ι → ℝ}
    {γ : ℝ} (heig : ∀ u, ∑ v, w u v * f v = γ * (∑ v, w u v) * f u) (hγ : γ ≠ 1) :
    ∑ u, (∑ v, w u v) * f u = 0 := by
  have h1 : ∑ u, ∑ v, w u v * f v = ∑ u, (∑ v, w u v) * f u := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ => by rw [hsymm u v]
  have h2 : ∑ u, ∑ v, w u v * f v = γ * ∑ u, (∑ v, w u v) * f u := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [heig u]; ring
  have h3 : (1 - γ) * ∑ u, (∑ v, w u v) * f u = 0 := by linarith
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hγ))

omit [Fintype ι] in
/-- An eigenfunction with positive degree-weighted norm and eigenvalue `γ ≠ 1` rules out every
bound `μ < γ` on the second eigenvalue. For `γ = 1` the eigenfunction may be constant, which says
nothing about the second eigenvalue; with zero norm it says nothing either. -/
theorem not_walkSecondEigenvalueLE_of_eigen [Fintype ι] (hsymm : ∀ u v, w u v = w v u)
    {f : ι → ℝ} {γ : ℝ} (heig : ∀ u, ∑ v, w u v * f v = γ * (∑ v, w u v) * f u) (hγ : γ ≠ 1)
    (hf : 0 < ∑ u, (∑ v, w u v) * f u ^ 2) {μ : ℝ} (hμ : μ < γ) :
    ¬ WalkSecondEigenvalueLE w μ := by
  intro h
  have h1 := h f (sum_deg_mul_eq_zero_of_eigen hsymm heig hγ)
  rw [sum_mul_mul_eq_of_eigen heig] at h1
  have := le_of_mul_le_mul_right h1 hf
  linarith

omit [Fintype ι] in
/-- `Σ w(u,v) (g u − g v)² = 2 (1 − γ) ‖g‖²` for an eigenfunction `g`. -/
private theorem sum_mul_sub_sq_of_eigen [Fintype ι] (hsymm : ∀ u v, w u v = w v u) {g : ι → ℝ}
    {γ : ℝ} (heig : ∀ u, ∑ v, w u v * g v = γ * (∑ v, w u v) * g u) :
    ∑ u, ∑ v, w u v * (g u - g v) ^ 2 = 2 * (1 - γ) * ∑ u, (∑ v, w u v) * g u ^ 2 := by
  have hQ := sum_mul_mul_eq_of_eigen heig
  have e : ∀ u v, w u v * (g u - g v) ^ 2 =
      w u v * g u ^ 2 + w u v * g v ^ 2 - 2 * (w u v * g u * g v) := fun u v => by ring
  have a1 : ∑ u, ∑ v, w u v * g u ^ 2 = ∑ u, (∑ v, w u v) * g u ^ 2 :=
    Finset.sum_congr rfl fun u _ => (Finset.sum_mul _ _ _).symm
  have a2 : ∑ u, ∑ v, w u v * g v ^ 2 = ∑ u, (∑ v, w u v) * g u ^ 2 := by
    rw [Finset.sum_comm, ← a1]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hsymm v u]
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, a1, a2, hQ]
  ring

omit [Fintype ι] in
/-- Every eigenvalue of the random walk on a symmetric nonnegative `w` that has an eigenfunction
of positive degree-weighted norm is at most `1`. (Eigenfunctions of norm `0` are supported on
vertices of degree `0` and satisfy the eigen-equation for every `γ`.) -/
theorem eigen_le_one [Fintype ι] (hsymm : ∀ u v, w u v = w v u) (hnn : ∀ u v, 0 ≤ w u v)
    {g : ι → ℝ} {γ : ℝ} (heig : ∀ u, ∑ v, w u v * g v = γ * (∑ v, w u v) * g u)
    (hg : 0 < ∑ u, (∑ v, w u v) * g u ^ 2) : γ ≤ 1 := by
  have h0 : 0 ≤ ∑ u, ∑ v, w u v * (g u - g v) ^ 2 :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => mul_nonneg (hnn u v) (sq_nonneg _)
  rw [sum_mul_sub_sq_of_eigen hsymm heig] at h0
  by_contra hlt
  rw [not_le] at hlt
  nlinarith

omit [Fintype ι] in
/-- **The eigenvalue `1` is simple on a connected graph**: an eigenfunction for `1` is constant on
the vertices of positive degree. Connectivity is in the functional form of
`walkSecondEigenvalueLE_of_garland`; values at vertices of degree `0` are unconstrained. -/
theorem eq_of_eigen_one [Fintype ι] (hsymm : ∀ u v, w u v = w v u) (hnn : ∀ u v, 0 ≤ w u v)
    (hconn : ∀ g : ι → ℝ, (∀ u v, 0 < w u v → g u = g v) →
      ∀ u v, 0 < ∑ x, w u x → 0 < ∑ x, w v x → g u = g v)
    {g : ι → ℝ} (heig : ∀ u, ∑ v, w u v * g v = 1 * (∑ v, w u v) * g u) (u v : ι)
    (hu : 0 < ∑ x, w u x) (hv : 0 < ∑ x, w v x) : g u = g v := by
  have hzero : ∑ u, ∑ v, w u v * (g u - g v) ^ 2 = 0 := by
    rw [sum_mul_sub_sq_of_eigen hsymm heig]
    ring
  refine hconn g (fun a b hab => ?_) u v hu hv
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => mul_nonneg (hnn a b) (sq_nonneg (g a - g b))).mp hzero a
    (Finset.mem_univ a)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ =>
    mul_nonneg (hnn a b) (sq_nonneg (g a - g b))).mp h1 b (Finset.mem_univ b)
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h hab.ne'
  · exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)

omit [Fintype ι] in
/-- A function that is not degree-orthogonal to some `f` has positive norm. -/
private theorem norm_pos_of_inner_ne_zero [Fintype ι] (hnn : ∀ u v, 0 ≤ w u v) {g f : ι → ℝ}
    (h : ∑ u, (∑ v, w u v) * g u * f u ≠ 0) : 0 < ∑ u, (∑ v, w u v) * g u ^ 2 := by
  have hD0 : ∀ u, 0 ≤ ∑ v, w u v := fun u => Finset.sum_nonneg fun v _ => hnn u v
  obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hDu : ∑ v, w u v ≠ 0 := fun h => hu (by rw [h]; ring)
  have hgu : g u ≠ 0 := fun h => hu (by rw [h]; ring)
  have hpos : 0 < (∑ v, w u v) * g u ^ 2 :=
    mul_pos (lt_of_le_of_ne (hD0 u) (Ne.symm hDu)) (by positivity)
  exact Finset.sum_pos' (fun v _ => mul_nonneg (hD0 v) (sq_nonneg _)) ⟨u, Finset.mem_univ u, hpos⟩

omit [Fintype ι] in
/-- **The walk has finitely many eigenvalues.** The eigenvalues `γ` carried by an eigenfunction of
positive degree-weighted norm form a finite set. (Without the norm condition every `γ` would
qualify as soon as some vertex has degree `0`.) The proof embeds them in the eigenvalues of the
endomorphism `g ↦ (W g) / deg` (with `x / 0 = 0`). -/
theorem finite_setOf_eigen [Fintype ι] [DecidableEq ι] (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) :
    {γ : ℝ | ∃ g : ι → ℝ, (∀ u, ∑ v, w u v * g v = γ * (∑ v, w u v) * g u) ∧
      0 < ∑ u, (∑ v, w u v) * g u ^ 2}.Finite := by
  let S : Module.End ℝ (ι → ℝ) :=
    { toFun := fun g u => (∑ v, w u v * g v) / ∑ v, w u v
      map_add' := fun g g' => by
        funext u
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, add_div]
      map_smul' := fun a g => by
        funext u
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← mul_div_assoc, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun v _ => by ring }
  refine (Module.End.finite_hasEigenvalue S).subset ?_
  rintro γ ⟨g, heig, hg⟩
  have hD0 : ∀ u, 0 ≤ ∑ v, w u v := fun u => Finset.sum_nonneg fun v _ => hnn u v
  let g' : ι → ℝ := fun u => if 0 < ∑ v, w u v then g u else 0
  have hrow : ∀ u v, ¬ 0 < ∑ x, w v x → w u v = 0 := by
    intro u v hv
    have hv0 : ∑ x, w v x = 0 := le_antisymm (not_lt.mp hv) (hD0 v)
    rw [hsymm]
    exact row_eq_zero_of_deg_eq_zero hnn hv0 u
  have hS : S g' = γ • g' := by
    funext u
    show (∑ v, w u v * g' v) / ∑ v, w u v = γ * g' u
    have e : ∑ v, w u v * g' v = ∑ v, w u v * g v := by
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : 0 < ∑ x, w v x
      · simp only [g', if_pos hv]
      · simp only [g', if_neg hv, hrow u v hv, zero_mul]
    rw [e, heig u]
    by_cases hu : 0 < ∑ v, w u v
    · simp only [g', if_pos hu]
      field_simp
    · have hu0 : ∑ v, w u v = 0 := le_antisymm (not_lt.mp hu) (hD0 u)
      simp only [g', if_neg hu, hu0, div_zero, mul_zero]
  have hne : g' ≠ 0 := by
    obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg.ne'
    have hDu : ∑ v, w u v ≠ 0 := fun h => hu (by rw [h]; ring)
    have hgu : g u ≠ 0 := fun h => hu (by rw [h]; ring)
    intro h0
    have := congrFun h0 u
    simp only [g', if_pos (lt_of_le_of_ne (hD0 u) (Ne.symm hDu)), Pi.zero_apply] at this
    exact hgu this
  exact Module.End.hasEigenvalue_of_hasEigenvector
    (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hS, hne⟩)

omit [Fintype ι] in
/-- **The second eigenvalue is attained.** On a connected weighted graph (symmetric, nonnegative,
connected in the functional form of `walkSecondEigenvalueLE_of_garland`), if `γ` is the least
valid bound on the second eigenvalue of the random walk, then `γ` is an eigenvalue: some
eigenfunction of mean zero and positive degree-weighted norm has eigenvalue exactly `γ`.

Degenerate cases: on a graph with no edges every `γ` is valid, so no `γ` is least and the statement
is vacuous; on a connected graph the least bound is below `1` (`ne_one_of_isLeast`). The proof
uses that the walk has finitely many eigenvalues (`finite_setOf_eigen`). -/
theorem exists_eigen_of_isLeast [Fintype ι] [DecidableEq ι] (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v)
    (hconn : ∀ g : ι → ℝ, (∀ u v, 0 < w u v → g u = g v) →
      ∀ u v, 0 < ∑ x, w u x → 0 < ∑ x, w v x → g u = g v)
    {γ : ℝ} (h : IsLeast {μ | WalkSecondEigenvalueLE w μ} γ) :
    ∃ g : ι → ℝ, (∀ u, ∑ v, w u v * g v = γ * (∑ v, w u v) * g u) ∧
      0 < ∑ u, (∑ v, w u v) * g u ^ 2 ∧ ∑ u, (∑ v, w u v) * g u = 0 := by
  by_contra hcon
  have hfin := (finite_setOf_eigen hsymm hnn).inter_of_left (Set.Iio γ)
  set s := hfin.toFinset with hs
  obtain ⟨μ₀, hμ₀, hmax⟩ : ∃ μ₀ < γ, ∀ e ∈ s, e ≤ μ₀ := by
    by_cases hne : s.Nonempty
    · refine ⟨s.max' hne, ?_, fun e he => s.le_max' e he⟩
      exact ((Set.Finite.mem_toFinset hfin).mp (s.max'_mem hne)).2
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact ⟨γ - 1, by linarith, fun e he => by simp [hne] at he⟩
  have hμ : (μ₀ + γ) / 2 < γ := by linarith
  have hnot : ¬ WalkSecondEigenvalueLE w ((μ₀ + γ) / 2) := fun hw => by
    have := h.2 hw
    linarith
  unfold WalkSecondEigenvalueLE at hnot
  push Not at hnot
  obtain ⟨f, hf, hlt⟩ := hnot
  obtain ⟨g, γ', hγ', heig, horth⟩ := exists_walk_eigenfunction_of_lt hsymm hnn hlt
  have hg := norm_pos_of_inner_ne_zero hnn horth
  have hle1 := eigen_le_one hsymm hnn heig hg
  have hne1 : γ' ≠ 1 := by
    rintro rfl
    obtain ⟨u₀, -, hu₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero horth
    have hD0 : ∀ u, 0 ≤ ∑ v, w u v := fun u => Finset.sum_nonneg fun v _ => hnn u v
    have hDu₀ : 0 < ∑ v, w u₀ v :=
      lt_of_le_of_ne (hD0 u₀) (Ne.symm fun h => hu₀ (by rw [h]; ring))
    refine horth ?_
    have hconst : ∀ u, (∑ v, w u v) * g u * f u = g u₀ * ((∑ v, w u v) * f u) := by
      intro u
      rcases (hD0 u).eq_or_lt with h0 | h0
      · rw [← h0]; ring
      · rw [eq_of_eigen_one hsymm hnn hconn heig u u₀ h0 hDu₀]; ring
    simp only [hconst, ← Finset.mul_sum, hf, mul_zero]
  have hγ'γ : γ' ≤ γ := by
    have h1 := h.1 g (sum_deg_mul_eq_zero_of_eigen hsymm heig hne1)
    rw [sum_mul_mul_eq_of_eigen heig] at h1
    exact le_of_mul_le_mul_right h1 hg
  rcases hγ'γ.eq_or_lt with heq | hlt'
  · exact hcon ⟨g, heq ▸ heig, hg, sum_deg_mul_eq_zero_of_eigen hsymm heig hne1⟩
  · have hmem : γ' ∈ s := by
      exact (Set.Finite.mem_toFinset hfin).mpr ⟨⟨g, heig, hg⟩, hlt'⟩
    have := hmax γ' hmem
    linarith

omit [Fintype ι] in
/-- **On a connected graph the second eigenvalue is below `1`**: `1` is never the least valid
bound. (On a disconnected graph it can be: two disjoint edges have second eigenvalue `1`.) -/
theorem ne_one_of_isLeast [Fintype ι] [DecidableEq ι] (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v)
    (hconn : ∀ g : ι → ℝ, (∀ u v, 0 < w u v → g u = g v) →
      ∀ u v, 0 < ∑ x, w u x → 0 < ∑ x, w v x → g u = g v)
    {γ : ℝ} (h : IsLeast {μ | WalkSecondEigenvalueLE w μ} γ) : γ ≠ 1 := by
  rintro rfl
  obtain ⟨g, heig, hg, hmean⟩ := exists_eigen_of_isLeast hsymm hnn hconn h
  have hD0 : ∀ u, 0 ≤ ∑ v, w u v := fun u => Finset.sum_nonneg fun v _ => hnn u v
  obtain ⟨u₀, -, hu₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg.ne'
  have hDu₀ : 0 < ∑ v, w u₀ v :=
    lt_of_le_of_ne (hD0 u₀) (Ne.symm fun h => hu₀ (by rw [h]; ring))
  have hconst : ∀ u, (∑ v, w u v) * g u = g u₀ * ∑ v, w u v := by
    intro u
    rcases (hD0 u).eq_or_lt with h0 | h0
    · rw [← h0]; ring
    · rw [eq_of_eigen_one hsymm hnn hconn heig u u₀ h0 hDu₀]; ring
  have hsq : ∀ u, (∑ v, w u v) * g u ^ 2 = g u₀ * ((∑ v, w u v) * g u) := by
    intro u
    rcases (hD0 u).eq_or_lt with h0 | h0
    · rw [← h0]; ring
    · rw [eq_of_eigen_one hsymm hnn hconn heig u u₀ h0 hDu₀]; ring
  rw [Finset.sum_congr rfl fun u _ => hsq u, ← Finset.mul_sum, hmean, mul_zero] at hg
  exact lt_irrefl _ hg

end Graph

/-! ### Garland's method with equality -/

section Garland

variable {w : ι → ι → ℝ} {wz : ι → ι → ι → ℝ} {c : ℝ}

omit [Fintype ι] in
/-- The local moments of Garland's method, at one vertex `z`: the localisation `f − m z` has mean
zero in the link of `z`, and its quadratic form and norm there are given by the global data. -/
private theorem garland_local_moments [Fintype ι] (hzsymm : ∀ z u v, wz z u v = wz z v u)
    (hloc₂ : ∀ z u, ∑ v, wz z u v = c * w z u) (f m : ι → ℝ)
    (hm : ∀ z, ∑ u, w z u * f u = m z * ∑ u, w z u) (z : ι) :
    ∑ u, (∑ v, wz z u v) * (f u - m z) = 0 ∧
    ∑ u, ∑ v, wz z u v * (f u - m z) * (f v - m z) =
        ∑ u, ∑ v, wz z u v * f u * f v - c * ((∑ v, w z v) * m z ^ 2) ∧
    ∑ u, (∑ v, wz z u v) * (f u - m z) ^ 2 =
        c * ∑ u, w z u * f u ^ 2 - c * ((∑ v, w z v) * m z ^ 2) := by
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
  refine ⟨?_, ?_, ?_⟩
  · simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, s4, s0]
    ring
  · have e : ∀ u v, wz z u v * (f u - m z) * (f v - m z) =
        wz z u v * f u * f v - m z * (wz z u v * f u) - m z * (wz z u v * f v)
          + m z ^ 2 * wz z u v := fun u v => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, s1, s2, s0]
    ring
  · have e : ∀ u, (∑ v, wz z u v) * (f u - m z) ^ 2 =
        (∑ v, wz z u v) * f u ^ 2 - 2 * m z * ((∑ v, wz z u v) * f u)
          + m z ^ 2 * (∑ v, wz z u v) := fun u => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, s3, s4, s0]
    ring

omit [Fintype ι] in
/-- **Garland's identity at an eigenfunction.** Under the hypotheses of `garland_inequality`, let
`f` be an eigenfunction of the walk on `w` with eigenvalue `γ = lam / (1 − lam)`, `lam ≠ 1`, and
let every `wz z` have second eigenvalue at most `lam`. Then at every `z` the localisation
`h_z = f − γ f(z)` has mean zero in `wz z` and attains the bound there: its quadratic form is
exactly `lam` times its norm.

The reason: summed over `z`, the slacks `lam ‖h_z‖² − ⟨h_z, W_z h_z⟩` (each `≥ 0`) add up to
`c (1 − γ)(lam − (1 − lam) γ) ‖f‖²`, and the second factor vanishes at `γ = lam / (1 − lam)`. -/
theorem garland_local_eq_of_eigen [Fintype ι] (hsymm : ∀ u v, w u v = w v u)
    (hzsymm : ∀ z u v, wz z u v = wz z v u)
    (hloc₁ : ∀ u v, ∑ z, wz z u v = c * w u v)
    (hloc₂ : ∀ z u, ∑ v, wz z u v = c * w z u) {lam : ℝ}
    (hlocal : ∀ z, WalkSecondEigenvalueLE (wz z) lam) (hlam : lam ≠ 1) {f : ι → ℝ}
    (heig : ∀ u, ∑ v, w u v * f v = lam / (1 - lam) * (∑ v, w u v) * f u) (z : ι) :
    ∑ u, (∑ v, wz z u v) * (f u - lam / (1 - lam) * f z) = 0 ∧
    ∑ u, ∑ v, wz z u v * (f u - lam / (1 - lam) * f z) * (f v - lam / (1 - lam) * f z) =
      lam * ∑ u, (∑ v, wz z u v) * (f u - lam / (1 - lam) * f z) ^ 2 := by
  set γ := lam / (1 - lam) with hγdef
  have hγ : γ * (1 - lam) = lam := by
    rw [hγdef]
    field_simp [sub_ne_zero.mpr (Ne.symm hlam)]
  have hm : ∀ z, ∑ u, w z u * f u = (γ * f z) * ∑ u, w z u := fun z => by
    rw [heig z]; ring
  have hmom := garland_local_moments hzsymm hloc₂ f (fun z => γ * f z) hm
  -- the slack at each vertex is nonnegative
  have hslack : ∀ z, 0 ≤ lam * ∑ u, (∑ v, wz z u v) * (f u - γ * f z) ^ 2 -
      ∑ u, ∑ v, wz z u v * (f u - γ * f z) * (f v - γ * f z) := fun z => by
    have := hlocal z (fun u => f u - γ * f z) (hmom z).1
    linarith
  -- and the slacks add up to zero
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
  have t3 : ∑ z, (∑ v, w z v) * (γ * f z) ^ 2 = γ ^ 2 * ∑ u, (∑ v, w u v) * f u ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  have hQ := sum_mul_mul_eq_of_eigen heig
  have hsum : ∑ z, (lam * ∑ u, (∑ v, wz z u v) * (f u - γ * f z) ^ 2 -
      ∑ u, ∑ v, wz z u v * (f u - γ * f z) * (f v - γ * f z)) = 0 := by
    simp only [fun z => (hmom z).2.1, fun z => (hmom z).2.2]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, t1, t2, t3, hQ]
    linear_combination (c * (∑ u, (∑ v, w u v) * f u ^ 2) * (γ - 1)) * hγ
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hslack z).mp hsum z (Finset.mem_univ z)
  exact ⟨(hmom z).1, by linarith⟩

omit [Fintype ι] in
/-- **Equality in Garland's method: localisations are link eigenfunctions.** Under the hypotheses
of `garland_local_eq_of_eigen`, with nonnegative local weights, every localisation
`f − γ f(z)` of a `γ`-eigenfunction `f`, `γ = lam / (1 − lam)`, is a `lam`-eigenfunction of the
walk on `wz z` (or zero there). -/
theorem garland_local_eigen_of_eigen [Fintype ι] (hsymm : ∀ u v, w u v = w v u)
    (hzsymm : ∀ z u v, wz z u v = wz z v u) (hznn : ∀ z u v, 0 ≤ wz z u v)
    (hloc₁ : ∀ u v, ∑ z, wz z u v = c * w u v)
    (hloc₂ : ∀ z u, ∑ v, wz z u v = c * w z u) {lam : ℝ}
    (hlocal : ∀ z, WalkSecondEigenvalueLE (wz z) lam) (hlam : lam ≠ 1) {f : ι → ℝ}
    (heig : ∀ u, ∑ v, w u v * f v = lam / (1 - lam) * (∑ v, w u v) * f u) (z u : ι) :
    ∑ v, wz z u v * (f v - lam / (1 - lam) * f z) =
      lam * (∑ v, wz z u v) * (f u - lam / (1 - lam) * f z) := by
  obtain ⟨h1, h2⟩ := garland_local_eq_of_eigen hsymm hzsymm hloc₁ hloc₂ hlocal hlam heig z
  exact (hlocal z).eigen_of_le (hzsymm z) (hznn z) (f := fun u => f u - lam / (1 - lam) * f z)
    h1 h2.ge u

omit [Fintype ι] in
/-- The local eigen-equation at `(z, u)` is the edge equation at `(z, u)`, for `lam ≠ 1`, using
`γ (1 − lam) = lam`. At `lam = 1` the junk value `γ = 0` breaks this. -/
theorem local_eigen_iff_edge [Fintype ι] (hloc₂ : ∀ z u, ∑ v, wz z u v = c * w z u) {lam : ℝ}
    (hlam : lam ≠ 1) (f : ι → ℝ) (z u : ι) :
    ∑ v, wz z u v * (f v - lam / (1 - lam) * f z) =
        lam * (∑ v, wz z u v) * (f u - lam / (1 - lam) * f z) ↔
      ∑ v, wz z u v * f v = c * lam * w z u * (f z + f u) := by
  have hγ : lam / (1 - lam) * (1 - lam) = lam := by
    field_simp [sub_ne_zero.mpr (Ne.symm hlam)]
  have e : ∑ v, wz z u v * (f v - lam / (1 - lam) * f z) =
      ∑ v, wz z u v * f v - lam / (1 - lam) * f z * (c * w z u) := by
    rw [← hloc₂ z u, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [e, hloc₂ z u]
  constructor
  · intro h
    linear_combination h + (c * w z u * f z) * hγ
  · intro h
    linear_combination h - (c * w z u * f z) * hγ

omit [Fintype ι] in
/-- **The edge equations imply the eigen-equation**, for every `lam ≠ 1` and with no hypothesis on
the local graphs beyond `hloc₂`: summing the edge equation at `(z, u)` over `u` gives
`(1 − lam) (W f)(z) = lam · deg z · f z`. -/
theorem eigen_of_edge [Fintype ι] (hzsymm : ∀ z u v, wz z u v = wz z v u)
    (hloc₂ : ∀ z u, ∑ v, wz z u v = c * w z u) (hc : c ≠ 0) {lam : ℝ} (hlam : lam ≠ 1)
    {f : ι → ℝ} (hE : ∀ z u, ∑ v, wz z u v * f v = c * lam * w z u * (f z + f u)) (z : ι) :
    ∑ v, w z v * f v = lam / (1 - lam) * (∑ v, w z v) * f z := by
  have h1 : ∑ u, ∑ v, wz z u v * f v = c * ∑ v, w z v * f v := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ u, wz z u v = c * w z v := by
      rw [← hloc₂ z v]
      exact Finset.sum_congr rfl fun u _ => hzsymm z u v
    rw [this]; ring
  have h2 : ∑ u, ∑ v, wz z u v * f v =
      c * lam * ((∑ v, w z v) * f z + ∑ v, w z v * f v) := by
    simp only [hE]
    rw [mul_add, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  have h3 : c * ((1 - lam) * ∑ v, w z v * f v - lam * ((∑ v, w z v) * f z)) = 0 := by
    linear_combination h1.symm.trans h2
  have h4 := (mul_eq_zero.mp h3).resolve_left hc
  have h1l : (1 - lam) ≠ 0 := sub_ne_zero.mpr (Ne.symm hlam)
  field_simp
  linear_combination h4

omit [Fintype ι] in
/-- **The equality criterion for Garland's method.** Under the hypotheses of `garland_inequality`
(with `c > 0`), with nonnegative local weights each of second eigenvalue at most `lam ≠ 1`, and
`γ = lam / (1 − lam)`, the following are equivalent for `f : ι → ℝ`:
* `f` is a `γ`-eigenfunction of the walk on `w` (or zero on the vertices of positive degree);
* the edge equations `Σ_v wz z u v f v = c lam w z u (f z + f u)` hold for all `z, u`;
* every localisation `f − γ f(z)` is a `lam`-eigenfunction of the walk on `wz z`. -/
theorem garland_eigen_iff [Fintype ι] (hsymm : ∀ u v, w u v = w v u)
    (hzsymm : ∀ z u v, wz z u v = wz z v u) (hznn : ∀ z u v, 0 ≤ wz z u v) (hc : 0 < c)
    (hloc₁ : ∀ u v, ∑ z, wz z u v = c * w u v)
    (hloc₂ : ∀ z u, ∑ v, wz z u v = c * w z u) {lam : ℝ}
    (hlocal : ∀ z, WalkSecondEigenvalueLE (wz z) lam) (hlam : lam ≠ 1) (f : ι → ℝ) :
    ((∀ u, ∑ v, w u v * f v = lam / (1 - lam) * (∑ v, w u v) * f u) ↔
      ∀ z u, ∑ v, wz z u v * f v = c * lam * w z u * (f z + f u)) ∧
    ((∀ u, ∑ v, w u v * f v = lam / (1 - lam) * (∑ v, w u v) * f u) ↔
      ∀ z u, ∑ v, wz z u v * (f v - lam / (1 - lam) * f z) =
        lam * (∑ v, wz z u v) * (f u - lam / (1 - lam) * f z)) := by
  have hloc : ∀ z u, (∑ v, wz z u v * (f v - lam / (1 - lam) * f z) =
        lam * (∑ v, wz z u v) * (f u - lam / (1 - lam) * f z)) ↔
      ∑ v, wz z u v * f v = c * lam * w z u * (f z + f u) :=
    local_eigen_iff_edge hloc₂ hlam f
  have hA : (∀ u, ∑ v, w u v * f v = lam / (1 - lam) * (∑ v, w u v) * f u) →
      ∀ z u, ∑ v, wz z u v * (f v - lam / (1 - lam) * f z) =
        lam * (∑ v, wz z u v) * (f u - lam / (1 - lam) * f z) :=
    fun heig => garland_local_eigen_of_eigen hsymm hzsymm hznn hloc₁ hloc₂ hlocal hlam heig
  have hB : (∀ z u, ∑ v, wz z u v * f v = c * lam * w z u * (f z + f u)) →
      ∀ u, ∑ v, w u v * f v = lam / (1 - lam) * (∑ v, w u v) * f u :=
    fun hE => eigen_of_edge hzsymm hloc₂ hc.ne' hlam hE
  refine ⟨⟨fun h z u => (hloc z u).mp (hA h z u), hB⟩,
    ⟨hA, fun h => hB fun z u => (hloc z u).mp (h z u)⟩⟩

omit [Fintype ι] in
/-- **A vertex whose link is strictly better forces the eigenfunction locally.** Under the
hypotheses of `garland_local_eq_of_eigen`, with nonnegative local weights, if the walk on `wz z`
has second eigenvalue at most some `μ < lam`, then every `γ`-eigenfunction `f`,
`γ = lam / (1 − lam)`, satisfies `f u = γ f(z)` at every vertex `u` of positive degree in
`wz z`. -/
theorem eq_mul_of_walkSecondEigenvalueLE_lt [Fintype ι] (hsymm : ∀ u v, w u v = w v u)
    (hzsymm : ∀ z u v, wz z u v = wz z v u) (hznn : ∀ z u v, 0 ≤ wz z u v)
    (hloc₁ : ∀ u v, ∑ z, wz z u v = c * w u v)
    (hloc₂ : ∀ z u, ∑ v, wz z u v = c * w z u) {lam : ℝ}
    (hlocal : ∀ z, WalkSecondEigenvalueLE (wz z) lam) (hlam : lam ≠ 1) {f : ι → ℝ}
    (heig : ∀ u, ∑ v, w u v * f v = lam / (1 - lam) * (∑ v, w u v) * f u) {z : ι} {μ : ℝ}
    (hμ : μ < lam) (hz : WalkSecondEigenvalueLE (wz z) μ) {u : ι} (hu : 0 < ∑ v, wz z u v) :
    f u = lam / (1 - lam) * f z := by
  obtain ⟨h1, h2⟩ := garland_local_eq_of_eigen hsymm hzsymm hloc₁ hloc₂ hlocal hlam heig z
  have h3 := hz _ h1
  rw [h2] at h3
  have hD0 : ∀ u, 0 ≤ ∑ v, wz z u v := fun u => Finset.sum_nonneg fun v _ => hznn z u v
  have hV0 : 0 ≤ ∑ u, (∑ v, wz z u v) * (f u - lam / (1 - lam) * f z) ^ 2 :=
    Finset.sum_nonneg fun u _ => mul_nonneg (hD0 u) (sq_nonneg _)
  have hV : ∑ u, (∑ v, wz z u v) * (f u - lam / (1 - lam) * f z) ^ 2 = 0 := by
    by_contra hne
    have hpos : 0 < ∑ u, (∑ v, wz z u v) * (f u - lam / (1 - lam) * f z) ^ 2 :=
      lt_of_le_of_ne hV0 (Ne.symm hne)
    have := le_of_mul_le_mul_right h3 hpos
    linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun u _ =>
    mul_nonneg (hD0 u) (sq_nonneg (f u - lam / (1 - lam) * f z))).mp hV u (Finset.mem_univ u)
  have := (mul_eq_zero.mp hterm).resolve_left hu.ne'
  have := pow_eq_zero_iff two_ne_zero |>.mp this
  linarith

end Garland

namespace PreAbstractSimplicialComplex

variable [DecidableEq ι]

/-! ### Two-dimensional weights: the edge operator -/

section Two

variable {m : Finset ι → ℝ}

/-- The **edge operator** `E_lam` of a weight `m` on triangles: for a function `f` on the points,
`(E_lam f)(u, v) = Σ_x m{u, v, x} f(x) − lam · w(u, v) · (f u + f v)`, where `w = linkWeightOf m ∅`
is the weighted underlying graph (`w(u, v)` is the total weight of the triangles through `u v`).
The first sum is written with the link of `u`: `linkWeightOf m {u} v x` is the weight of the
triangle `{u, v, x}` when `u, v, x` are distinct and `0` otherwise
(`linkWeightOf_singleton_eq`).

Degenerate arguments: for `u = v`, and for a pair `u v` lying in no triangle of positive weight,
both terms are `0`, so `E_lam f` is supported on the edges. -/
noncomputable def edgeOperator (m : Finset ι → ℝ) (lam : ℝ) (f : ι → ℝ) (u v : ι) : ℝ :=
  ∑ x, linkWeightOf m {u} v x * f x - lam * linkWeightOf m ∅ u v * (f u + f v)

/-- For `m` supported on sets with `d + 1` elements, the weight of a set with `d + 1` elements is
its own weight. -/
theorem faceWeight_eq_self {d : ℕ} (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {s : Finset ι}
    (hs : #s = d + 1) :
    faceWeight m s = m s := by
  unfold faceWeight
  rw [Finset.sum_eq_single_of_mem s (by simp)]
  intro F hF hne
  rw [Finset.mem_filter] at hF
  by_contra h
  exact hne (Finset.eq_of_subset_of_card_le hF.2 (by rw [hs, hcard F h])).symm

/-- In the link of a point `u`, the edge `v x` has the weight of the triangle `{u, v, x}`. -/
theorem linkWeightOf_singleton_eq (hcard : ∀ F, m F ≠ 0 → #F = 2 + 1) (u v x : ι) :
    linkWeightOf m {u} v x = if u ≠ v ∧ u ≠ x ∧ v ≠ x then m {u, v, x} else 0 := by
  unfold linkWeightOf
  by_cases h : u ≠ v ∧ u ≠ x ∧ v ≠ x
  · rw [if_pos ⟨h.2.2, by simpa [eq_comm] using h.1, by simpa [eq_comm] using h.2.1⟩, if_pos h,
      faceWeight_eq_self hcard (card_eq_three.mpr ⟨v, x, u, h.2.2, Ne.symm h.1, Ne.symm h.2.1,
        rfl⟩)]
    congr 1
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · rw [if_neg h, if_neg]
    rintro ⟨h1, h2, h3⟩
    simp only [Finset.mem_singleton] at h2 h3
    exact h ⟨Ne.symm h2, Ne.symm h3, h1⟩

/-- **Localisation, for triangles.** The weight of an edge of the underlying graph is the sum of its
weights in the links of the points. -/
theorem sum_linkWeightOf_singleton (hcard : ∀ F, m F ≠ 0 → #F = 2 + 1) (u v : ι) :
    ∑ z, linkWeightOf m {z} u v = 1 * linkWeightOf m ∅ u v := by
  have h := sum_linkWeightOf_insert (d := 2) hcard ∅ u v
  simp only [Finset.notMem_empty, if_false, Finset.card_empty, Nat.cast_zero, sub_zero,
    Finset.insert_empty] at h
  rw [h]
  norm_num

/-- **Localisation of degrees, for triangles.** The degree of `u` in the link of `z` is the weight
of the edge `z u`. -/
theorem sum_linkWeightOf_singleton_right (hcard : ∀ F, m F ≠ 0 → #F = 2 + 1) (z u : ι) :
    ∑ v, linkWeightOf m {z} u v = 1 * linkWeightOf m ∅ z u := by
  have h := sum_linkWeightOf_insert_right (d := 2) hcard ∅ z u
  simp only [Finset.notMem_empty, if_false, Finset.card_empty, Nat.cast_zero, sub_zero,
    Finset.insert_empty] at h
  rw [h]
  norm_num

/-- The edge equation `E_lam f (u, v) = 0`, in the form used by `garland_eigen_iff` (with
`c = 1`). -/
theorem edgeOperator_eq_zero_iff (f : ι → ℝ) (lam : ℝ) (u v : ι) :
    edgeOperator m lam f u v = 0 ↔
      ∑ x, linkWeightOf m {u} v x * f x = 1 * lam * linkWeightOf m ∅ u v * (f u + f v) := by
  unfold edgeOperator
  constructor <;> intro h <;> linarith

/-- **The edge kernel lies in the `γ`-eigenspace, for every `lam ≠ 1`.** If `m` is supported on
sets with three elements (no sign condition) and `E_lam f = 0`, then `f` is an eigenfunction of
the walk on the weighted underlying graph with eigenvalue `γ = lam / (1 − lam)`: summing
`(E_lam f)(z, u) = 0` over `u` gives `(1 − lam) (W f)(z) = lam · deg z · f z`.

No bound on the links is needed. At `lam = 1/2` (`γ = 1`) the constants lie in the edge kernel
(`edgeOperator_const_half`), and they are `1`-eigenfunctions. At `lam = 1` the value
`lam / (1 − lam)` is the junk value `1 / 0 = 0`, and the statement is excluded. -/
theorem eigen_of_edgeOperator_eq_zero (hcard : ∀ F, m F ≠ 0 → #F = 2 + 1) {lam : ℝ}
    (hlam : lam ≠ 1) {f : ι → ℝ} (hE : ∀ u v, edgeOperator m lam f u v = 0) (u : ι) :
    ∑ v, linkWeightOf m ∅ u v * f v = lam / (1 - lam) * (∑ v, linkWeightOf m ∅ u v) * f u :=
  eigen_of_edge (wz := fun z => linkWeightOf m {z}) (fun z => linkWeightOf_symm m {z})
    (sum_linkWeightOf_singleton_right hcard) one_ne_zero hlam
    (fun z u => (edgeOperator_eq_zero_iff f lam z u).mp (hE z u)) u

/-- **Constants lie in the edge kernel at `lam = 1/2`.** For `m` supported on sets with three
elements, `E_{1/2}` vanishes on constant functions, since the triangles through an edge have total
weight `w(u, v)`. So at `lam = 1/2` the edge kernel is never zero (on a complex with an edge),
although the second eigenvalue `μ < 1 = γ` on a connected complex: the criterion
`isLeast_iff_exists_edgeOperator_eq_zero` needs `lam < 1/2`. -/
theorem edgeOperator_const_half (hcard : ∀ F, m F ≠ 0 → #F = 2 + 1) (a : ℝ) (u v : ι) :
    edgeOperator m (1 / 2) (fun _ => a) u v = 0 := by
  unfold edgeOperator
  rw [← Finset.sum_mul, sum_linkWeightOf_singleton_right hcard u v]
  ring

/-- **The trickling-down equality criterion for triangle weights.** Let `m ≥ 0` be supported on
sets with three elements (for instance a top weight of a pure `2`-dimensional complex), let every
link `linkWeightOf m {z}` have random-walk second eigenvalue at most `lam`, `lam ≠ 1`, and let
`γ = lam / (1 − lam)`. For `f : ι → ℝ` the following are equivalent:
* `f` is a `γ`-eigenfunction of the walk on the weighted underlying graph `w = linkWeightOf m ∅`:
  `Σ_v w(u, v) f v = γ · deg u · f u` for all `u`;
* `f` lies in the edge kernel: `E_lam f = 0`, i.e.
  `Σ_x m{u, v, x} f x = lam · w(u, v) · (f u + f v)` for every edge `u v`;
* for every `z`, the localisation `f − γ f(z)` is a `lam`-eigenfunction of the walk on the link of
  `z` (possibly zero there).

This is the equality case of Garland's method (`garland_eigen_iff`, with `c = 1`). No connectivity
and no upper bound on `lam` are needed; for `lam ≥ 1/2` the statement is still true, but then
`γ ≥ 1` (or `γ < −1` when `lam > 1`) and `γ` is not the second eigenvalue. The implication from the edge kernel to the
eigenspace needs no link bound at all (`eigen_of_edgeOperator_eq_zero`).

Degenerate cases: a point that lies in no triangle of positive weight has degree `0`, and both the
eigen-equation and the edge equations say nothing about the value of `f` there. A point `z` lying
in no triangle has an empty link, whose bound is vacuous. -/
theorem tricklingEquality_iff (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = 2 + 1)
    {lam : ℝ} (hlocal : ∀ z, WalkSecondEigenvalueLE (linkWeightOf m {z}) lam) (hlam : lam ≠ 1)
    (f : ι → ℝ) :
    ((∀ u, ∑ v, linkWeightOf m ∅ u v * f v =
        lam / (1 - lam) * (∑ v, linkWeightOf m ∅ u v) * f u) ↔
      ∀ u v, edgeOperator m lam f u v = 0) ∧
    ((∀ u, ∑ v, linkWeightOf m ∅ u v * f v =
        lam / (1 - lam) * (∑ v, linkWeightOf m ∅ u v) * f u) ↔
      ∀ z u, ∑ v, linkWeightOf m {z} u v * (f v - lam / (1 - lam) * f z) =
        lam * (∑ v, linkWeightOf m {z} u v) * (f u - lam / (1 - lam) * f z)) := by
  have h := garland_eigen_iff (wz := fun z => linkWeightOf m {z}) (linkWeightOf_symm m ∅)
    (fun z => linkWeightOf_symm m {z}) (fun z => linkWeightOf_nonneg hnn {z}) one_pos
    (sum_linkWeightOf_singleton hcard) (sum_linkWeightOf_singleton_right hcard) hlocal hlam f
  refine ⟨h.1.trans ?_, h.2⟩
  exact forall_congr' fun u => forall_congr' fun v => (edgeOperator_eq_zero_iff f lam u v).symm

/-- **Vertices outside the extremal set.** Under the hypotheses of `tricklingEquality_iff`, if the
link of `z` has second eigenvalue at most some `μ < lam`, then every `γ`-eigenfunction `f`,
`γ = lam / (1 − lam)`, satisfies `f u = γ f(z)` at every neighbour `u` of `z`. -/
theorem eq_mul_of_link_lt (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = 2 + 1) {lam : ℝ}
    (hlocal : ∀ z, WalkSecondEigenvalueLE (linkWeightOf m {z}) lam) (hlam : lam ≠ 1)
    {f : ι → ℝ}
    (heig : ∀ u, ∑ v, linkWeightOf m ∅ u v * f v =
      lam / (1 - lam) * (∑ v, linkWeightOf m ∅ u v) * f u)
    {z : ι} {μ : ℝ} (hμ : μ < lam) (hz : WalkSecondEigenvalueLE (linkWeightOf m {z}) μ) {u : ι}
    (hu : 0 < linkWeightOf m ∅ z u) : f u = lam / (1 - lam) * f z :=
  eq_mul_of_walkSecondEigenvalueLE_lt (wz := fun z => linkWeightOf m {z})
    (linkWeightOf_symm m ∅) (fun z => linkWeightOf_symm m {z})
    (fun z => linkWeightOf_nonneg hnn {z}) (sum_linkWeightOf_singleton hcard)
    (sum_linkWeightOf_singleton_right hcard) hlocal hlam heig hμ hz
    (by rw [sum_linkWeightOf_singleton_right hcard, one_mul]; exact hu)

/-- `γ = lam / (1 − lam)` satisfies `γ² ≠ 1` unless `lam = 1/2` (where `γ = 1`); `γ = −1` never
happens, and at `lam = 1` the junk value is `γ = 0`. -/
private theorem gamma_sq_ne_one {lam : ℝ} (hlam1 : lam ≠ 1) (hlam2 : lam ≠ 1 / 2) :
    (lam / (1 - lam)) ^ 2 ≠ 1 := by
  have h1 : 1 - lam ≠ 0 := sub_ne_zero.mpr (Ne.symm hlam1)
  intro h
  have h' : lam ^ 2 = (1 - lam) ^ 2 := by
    rw [div_pow] at h
    field_simp at h
    linarith
  have : (2 * lam - 1) = 0 := by nlinarith
  exact hlam2 (by linarith)

/-- **Edges disjoint from the extremal set.** Under the hypotheses of `tricklingEquality_iff`,
with `lam ≠ 1/2`, let `u v` be an edge whose two links both have second eigenvalue strictly
below `lam`. Then every `γ`-eigenfunction vanishes at `u`, at `v` and at every neighbour of `u`
or `v`: `f(u) = γ f(v) = γ² f(u)` and `γ² ≠ 1`.

At `lam = 1/2` the constants are `1`-eigenfunctions and the conclusion fails. -/
theorem eq_zero_of_link_lt_of_link_lt (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = 2 + 1)
    {lam : ℝ} (hlocal : ∀ z, WalkSecondEigenvalueLE (linkWeightOf m {z}) lam) (hlam1 : lam ≠ 1)
    (hlam2 : lam ≠ 1 / 2) {f : ι → ℝ}
    (heig : ∀ u, ∑ v, linkWeightOf m ∅ u v * f v =
      lam / (1 - lam) * (∑ v, linkWeightOf m ∅ u v) * f u)
    {u v : ι} (huv : 0 < linkWeightOf m ∅ u v)
    (hu : ∃ μ < lam, WalkSecondEigenvalueLE (linkWeightOf m {u}) μ)
    (hv : ∃ μ < lam, WalkSecondEigenvalueLE (linkWeightOf m {v}) μ) :
    f u = 0 ∧ f v = 0 ∧
      ∀ x, (0 < linkWeightOf m ∅ u x ∨ 0 < linkWeightOf m ∅ v x) → f x = 0 := by
  obtain ⟨μ, hμ, hμu⟩ := hu
  obtain ⟨ν, hν, hνv⟩ := hv
  have h1 : f v = lam / (1 - lam) * f u :=
    eq_mul_of_link_lt hnn hcard hlocal hlam1 heig hμ hμu huv
  have h2 : f u = lam / (1 - lam) * f v :=
    eq_mul_of_link_lt hnn hcard hlocal hlam1 heig hν hνv (by rwa [linkWeightOf_symm])
  have hu0 : f u = 0 := by
    have h3 : (1 - (lam / (1 - lam)) ^ 2) * f u = 0 := by
      rw [h1] at h2
      linear_combination h2
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (gamma_sq_ne_one hlam1 hlam2).symm)
  have hv0 : f v = 0 := by rw [h1, hu0, mul_zero]
  refine ⟨hu0, hv0, fun x hx => ?_⟩
  rcases hx with hx | hx
  · rw [eq_mul_of_link_lt hnn hcard hlocal hlam1 heig hμ hμu hx, hu0, mul_zero]
  · rw [eq_mul_of_link_lt hnn hcard hlocal hlam1 heig hν hνv hx, hv0, mul_zero]

/-- The `γ`-eigenspace of the random walk on `w`, as a subspace of `ι → ℝ`: the kernel of
`W − γ D`. It contains every function that vanishes on the vertices of positive degree. -/
def walkEigenspace (w : ι → ι → ℝ) (γ : ℝ) : Submodule ℝ (ι → ℝ) where
  carrier := {f | ∀ u, ∑ v, w u v * f v = γ * (∑ v, w u v) * f u}
  add_mem' := fun {f g} hf hg u => by
    have hf' : ∑ v, w u v * f v = γ * (∑ v, w u v) * f u := hf u
    have hg' : ∑ v, w u v * g v = γ * (∑ v, w u v) * g u := hg u
    show ∑ v, w u v * (f v + g v) = γ * (∑ v, w u v) * (f u + g u)
    simp only [mul_add, Finset.sum_add_distrib, hf', hg']
  zero_mem' := fun u => by
    show ∑ v, w u v * 0 = γ * (∑ v, w u v) * 0
    simp
  smul_mem' := fun c f hf u => by
    have hf' : ∑ v, w u v * f v = γ * (∑ v, w u v) * f u := hf u
    show ∑ v, w u v * (c * f v) = γ * (∑ v, w u v) * (c * f u)
    have e : ∑ v, w u v * (c * f v) = c * ∑ v, w u v * f v := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [e, hf']
    ring

/-- The **edge kernel** `ker E_lam`, as a subspace of `ι → ℝ`. It contains every function that
vanishes on the points lying in a triangle of positive weight. -/
noncomputable def edgeKernel (m : Finset ι → ℝ) (lam : ℝ) : Submodule ℝ (ι → ℝ) where
  carrier := {f | ∀ u v, edgeOperator m lam f u v = 0}
  add_mem' := fun {f g} hf hg u v => by
    have hf' : edgeOperator m lam f u v = 0 := hf u v
    have hg' : edgeOperator m lam g u v = 0 := hg u v
    show edgeOperator m lam (f + g) u v = 0
    unfold edgeOperator at hf' hg' ⊢
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    linear_combination hf' + hg'
  zero_mem' := fun u v => by
    show edgeOperator m lam 0 u v = 0
    simp [edgeOperator]
  smul_mem' := fun c f hf u v => by
    have hf' : edgeOperator m lam f u v = 0 := hf u v
    show edgeOperator m lam (c • f) u v = 0
    unfold edgeOperator at hf' ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    have e : ∑ x, linkWeightOf m {u} v x * (c * f x) = c * ∑ x, linkWeightOf m {u} v x * f x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e]
    linear_combination c * hf'

/-- **The `γ`-eigenspace is the edge kernel**, as subspaces, under the hypotheses of
`tricklingEquality_iff`. In particular they have the same dimension: the multiplicity of
`γ = lam / (1 − lam)` as an eigenvalue of the walk is `dim ker E_lam`. (Both subspaces contain
all functions supported off the points of positive degree, so their dimensions on the vertices
differ from those on `ι` by the same number.) -/
theorem walkEigenspace_eq_edgeKernel (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = 2 + 1)
    {lam : ℝ} (hlocal : ∀ z, WalkSecondEigenvalueLE (linkWeightOf m {z}) lam) (hlam : lam ≠ 1) :
    walkEigenspace (linkWeightOf m ∅) (lam / (1 - lam)) = edgeKernel m lam :=
  Submodule.ext fun f => (tricklingEquality_iff hnn hcard hlocal hlam f).1

/-- **`mult(γ) = dim ker E_lam`**, under the hypotheses of `tricklingEquality_iff`: the
`γ`-eigenspace of the walk, `γ = lam / (1 − lam)`, and the edge kernel have the same dimension
(both counted in `ι → ℝ`, see `walkEigenspace_eq_edgeKernel`). -/
theorem finrank_walkEigenspace_eq_finrank_edgeKernel (hnn : ∀ F, 0 ≤ m F)
    (hcard : ∀ F, m F ≠ 0 → #F = 2 + 1) {lam : ℝ}
    (hlocal : ∀ z, WalkSecondEigenvalueLE (linkWeightOf m {z}) lam) (hlam : lam ≠ 1) :
    Module.finrank ℝ (walkEigenspace (linkWeightOf m ∅) (lam / (1 - lam))) =
      Module.finrank ℝ (edgeKernel m lam) := by
  rw [walkEigenspace_eq_edgeKernel hnn hcard hlocal hlam]

/-! ### The edge walk and the lift -/

/-- The **lift** of a function on points to finite sets: `liftSum f σ = Σ_{v ∈ σ} f v`; on an edge
`{u, v}` it is `f u + f v`. -/
def liftSum (f : ι → ℝ) (σ : Finset ι) : ℝ := ∑ v ∈ σ, f v

/-- The **lazy up-down walk** on level `k` of a weighted complex, as an operator on functions on
`(k + 1)`-sets: from `σ`, add a point `x ∉ σ` with probability
`faceWeight m (σ ∪ {x}) / ((d − k) · faceWeight m σ)`, then delete a uniformly random one of the
`k + 2` points. This is the operator whose quadratic form appears (unnormalised) in
`sum_faceWeight_mul_sq_sum_powersetCard` of `Expanders/UpDownWalk.lean`.

Junk values: the normalisation is `x⁻¹` with `0⁻¹ = 0`, so `upWalk m d k g σ = 0` when
`faceWeight m σ = 0` (for instance off the faces) or `d = k`. For `m` supported on sets with
`d + 1` elements and `#σ = k + 1`, the probabilities add up to `1` (`sum_faceWeight_insert`). -/
noncomputable def upWalk (m : Finset ι → ℝ) (d k : ℕ) (g : Finset ι → ℝ) (σ : Finset ι) : ℝ :=
  (((d : ℝ) - k) * faceWeight m σ)⁻¹ *
    ∑ x, if x ∈ σ then 0 else
      faceWeight m (insert x σ) * (((k : ℝ) + 2)⁻¹ * ∑ y ∈ insert x σ, g ((insert x σ).erase y))

/-- The **non-lazy up-down walk** on level `k`: as `upWalk`, but the deleted point is a uniformly
random one of the `k + 1` points of `σ`, never the added one. Same junk values as `upWalk`. -/
noncomputable def nonLazyUpWalk (m : Finset ι → ℝ) (d k : ℕ) (g : Finset ι → ℝ)
    (σ : Finset ι) : ℝ :=
  (((d : ℝ) - k) * faceWeight m σ)⁻¹ *
    ∑ x, if x ∈ σ then 0 else
      faceWeight m (insert x σ) * (((k : ℝ) + 1)⁻¹ * ∑ y ∈ σ, g ((insert x σ).erase y))

omit [Fintype ι] in
/-- Summing the lift over the facets of a set:
`Σ_{y ∈ τ} liftSum f (τ \ {y}) = (#τ − 1) · liftSum f τ`. -/
theorem sum_liftSum_erase (f : ι → ℝ) (τ : Finset ι) :
    ∑ y ∈ τ, liftSum f (τ.erase y) = ((#τ : ℝ) - 1) * liftSum f τ := by
  unfold liftSum
  rw [Finset.sum_congr rfl fun y hy => Finset.sum_erase_eq_sub hy, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  ring

private theorem faceWeight_pair_eq (m : Finset ι → ℝ) {u v : ι} (huv : u ≠ v) :
    faceWeight m {u, v} = linkWeightOf m ∅ u v := by
  unfold linkWeightOf
  rw [if_pos ⟨huv, Finset.notMem_empty u, Finset.notMem_empty v⟩, Finset.insert_empty]

/-- The weights of the triangles on an edge `u v`, as the link of `u`. -/
private theorem linkWeightOf_singleton_eq_ite (m : Finset ι → ℝ) {u v : ι} (huv : u ≠ v)
    (x : ι) :
    linkWeightOf m {u} v x =
      if x ∈ ({u, v} : Finset ι) then 0 else faceWeight m (insert x {u, v}) := by
  unfold linkWeightOf
  by_cases hx : x ∈ ({u, v} : Finset ι)
  · rw [if_pos hx, if_neg]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rintro ⟨h1, -, h3⟩
    rcases hx with rfl | rfl
    · exact h3 (Finset.mem_singleton_self _)
    · exact h1 rfl
  · rw [if_neg hx]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    rw [if_pos ⟨Ne.symm hx.2, fun h => huv (Finset.mem_singleton.mp h).symm,
      fun h => hx.1 (Finset.mem_singleton.mp h)⟩]
    congr 1
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- **The edge walk on a lift.** For `m` supported on sets with three elements and an edge `u v` of
positive weight `w = w(u, v)`, the lazy up-down walk on level `1` maps the lift of `f` to
`(2/3)(f u + f v) + (2/3) · Σ_x m{u, v, x} f(x) / w`, and the non-lazy one to
`(1/2)(f u + f v) + Σ_x m{u, v, x} f(x) / w`. -/
theorem upWalk_liftSum_pair (hcard : ∀ F, m F ≠ 0 → #F = 2 + 1) (f : ι → ℝ) {u v : ι}
    (huv : u ≠ v) (hw : 0 < linkWeightOf m ∅ u v) :
    upWalk m 2 1 (liftSum f) {u, v} = 2 / 3 * (f u + f v) +
        2 / 3 * (∑ x, linkWeightOf m {u} v x * f x) / linkWeightOf m ∅ u v ∧
    nonLazyUpWalk m 2 1 (liftSum f) {u, v} = 1 / 2 * (f u + f v) +
        (∑ x, linkWeightOf m {u} v x * f x) / linkWeightOf m ∅ u v := by
  have hW := faceWeight_pair_eq m huv
  have hsum := sum_faceWeight_insert (d := 2) hcard {u, v}
  rw [Finset.card_pair huv] at hsum
  have hsum' : ∑ x, (if x ∈ ({u, v} : Finset ι) then 0 else faceWeight m (insert x {u, v})) =
      linkWeightOf m ∅ u v := by
    rw [hsum, hW]; norm_num
  have hT : ∑ x, (if x ∈ ({u, v} : Finset ι) then 0 else faceWeight m (insert x {u, v})) * f x =
      ∑ x, linkWeightOf m {u} v x * f x :=
    Finset.sum_congr rfl fun x _ => by rw [linkWeightOf_singleton_eq_ite m huv x]
  have h3 : ∀ x, x ∉ ({u, v} : Finset ι) → #(insert x ({u, v} : Finset ι)) = 3 := fun x hx => by
    rw [Finset.card_insert_of_notMem hx, Finset.card_pair huv]
  have hlift : ∀ x, x ∉ ({u, v} : Finset ι) →
      liftSum f (insert x {u, v}) = f x + (f u + f v) := fun x hx => by
    unfold liftSum
    rw [Finset.sum_insert hx, Finset.sum_pair huv]
  have hpw : 0 < faceWeight m {u, v} := by rw [hW]; exact hw
  constructor
  · unfold upWalk
    have e : ∀ x, (if x ∈ ({u, v} : Finset ι) then 0 else faceWeight m (insert x {u, v}) *
        ((((1 : ℕ) : ℝ) + 2)⁻¹ *
          ∑ y ∈ insert x {u, v}, liftSum f ((insert x ({u, v} : Finset ι)).erase y))) =
        2 / 3 * ((if x ∈ ({u, v} : Finset ι) then 0 else faceWeight m (insert x {u, v})) *
          (f u + f v) +
        (if x ∈ ({u, v} : Finset ι) then 0 else faceWeight m (insert x {u, v})) * f x) := by
      intro x
      by_cases hx : x ∈ ({u, v} : Finset ι)
      · simp [hx]
      · rw [if_neg hx, if_neg hx, sum_liftSum_erase, h3 x hx, hlift x hx]
        norm_num
        ring
    rw [Finset.sum_congr rfl fun x _ => e x, ← Finset.mul_sum, Finset.sum_add_distrib,
      ← Finset.sum_mul, hsum', hT, hW]
    field_simp
    ring
  · unfold nonLazyUpWalk
    have e : ∀ x, (if x ∈ ({u, v} : Finset ι) then 0 else faceWeight m (insert x {u, v}) *
        ((((1 : ℕ) : ℝ) + 1)⁻¹ *
          ∑ y ∈ ({u, v} : Finset ι), liftSum f ((insert x ({u, v} : Finset ι)).erase y))) =
        1 / 2 * (if x ∈ ({u, v} : Finset ι) then 0 else faceWeight m (insert x {u, v})) *
          (f u + f v) +
        (if x ∈ ({u, v} : Finset ι) then 0 else faceWeight m (insert x {u, v})) * f x := by
      intro x
      by_cases hx : x ∈ ({u, v} : Finset ι)
      · simp [hx]
      · rw [if_neg hx, if_neg hx]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        have hxu : x ≠ u := hx.1
        have hxv : x ≠ v := hx.2
        rw [Finset.sum_pair huv]
        unfold liftSum
        have e1 : (insert x ({u, v} : Finset ι)).erase u = {x, v} := by
          ext y
          simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hy, rfl | rfl | rfl⟩
            · exact Or.inl rfl
            · exact absurd rfl hy
            · exact Or.inr rfl
          · rintro (rfl | rfl)
            · exact ⟨hxu, Or.inl rfl⟩
            · exact ⟨Ne.symm huv, Or.inr (Or.inr rfl)⟩
        have e2 : (insert x ({u, v} : Finset ι)).erase v = {x, u} := by
          ext y
          simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hy, rfl | rfl | rfl⟩
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact absurd rfl hy
          · rintro (rfl | rfl)
            · exact ⟨hxv, Or.inl rfl⟩
            · exact ⟨huv, Or.inr (Or.inl rfl)⟩
        rw [e1, e2, Finset.sum_pair hxv, Finset.sum_pair hxu]
        norm_num
        ring
    rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, hsum', hT, hW]
    field_simp
    ring

/-- **The edge equation is an eigen-equation of the lifted edge walk.** For an edge `u v` of
positive weight: `(E_lam f)(u, v) = 0` exactly when the lazy up-down walk on edges maps the lift
of `f` to `2 (1 + lam) / 3` times itself at `{u, v}`, and exactly when the non-lazy one maps it to
`(lam + 1/2)` times itself there. -/
theorem upWalk_liftSum_eq_iff (hcard : ∀ F, m F ≠ 0 → #F = 2 + 1) (lam : ℝ) (f : ι → ℝ)
    {u v : ι} (huv : u ≠ v) (hw : 0 < linkWeightOf m ∅ u v) :
    (upWalk m 2 1 (liftSum f) {u, v} = 2 * (1 + lam) / 3 * liftSum f {u, v} ↔
      edgeOperator m lam f u v = 0) ∧
    (nonLazyUpWalk m 2 1 (liftSum f) {u, v} = (lam + 1 / 2) * liftSum f {u, v} ↔
      edgeOperator m lam f u v = 0) := by
  obtain ⟨h1, h2⟩ := upWalk_liftSum_pair hcard f huv hw
  have hl : liftSum f {u, v} = f u + f v := Finset.sum_pair huv
  rw [h1, h2, hl]
  unfold edgeOperator
  set T := ∑ x, linkWeightOf m {u} v x * f x
  set W := linkWeightOf m ∅ u v
  have hW : W ≠ 0 := hw.ne'
  have k1 : 2 / 3 * (f u + f v) + 2 / 3 * T / W - 2 * (1 + lam) / 3 * (f u + f v) =
      2 / 3 * (T - lam * W * (f u + f v)) / W := by
    field_simp
    ring
  have k2 : 1 / 2 * (f u + f v) + T / W - (lam + 1 / 2) * (f u + f v) =
      (T - lam * W * (f u + f v)) / W := by
    field_simp
    ring
  rw [← sub_eq_zero, k1, ← sub_eq_zero (a := 1 / 2 * (f u + f v) + T / W), k2,
    div_eq_zero_iff, div_eq_zero_iff, mul_eq_zero]
  simp only [hW, or_false]
  norm_num

/-- `E_lam f` vanishes off the edges of positive weight. -/
theorem edgeOperator_eq_zero_of_linkWeightOf_eq_zero (hnn : ∀ F, 0 ≤ m F)
    (hcard : ∀ F, m F ≠ 0 → #F = 2 + 1) {u v : ι} (h : linkWeightOf m ∅ u v = 0) (lam : ℝ)
    (f : ι → ℝ) : edgeOperator m lam f u v = 0 := by
  have hs := sum_linkWeightOf_singleton_right hcard u v
  rw [h, mul_zero] at hs
  have h0 : ∀ x, linkWeightOf m {u} v x = 0 := fun x =>
    (Finset.sum_eq_zero_iff_of_nonneg fun x _ => linkWeightOf_nonneg hnn {u} v x).mp hs x
      (Finset.mem_univ x)
  simp [edgeOperator, h0, h]

end Two

/-! ### Two-dimensional complexes -/

section Complex

variable {K : PreAbstractSimplicialComplex ι} {m : Finset ι → ℝ}

/-- The vertex-link bounds of `trickling_down_weighted` for `d = 2` hold at every point: a point
that is not a vertex has an empty link. -/
theorem IsTopWeight.walkSecondEigenvalueLE_singleton (hm : K.IsTopWeight 2 m) {lam : ℝ}
    (hlocal : ∀ σ ∈ K, #σ + 1 = 2 → WalkSecondEigenvalueLE (linkWeightOf m σ) lam) (z : ι) :
    WalkSecondEigenvalueLE (linkWeightOf m {z}) lam := by
  by_cases hz : {z} ∈ K
  · exact hlocal {z} hz (by rw [card_singleton])
  · exact walkSecondEigenvalueLE_of_forall_eq_zero
      (hm.linkWeightOf_eq_zero_of_notMem (singleton_nonempty z) hz) lam

private theorem IsTopWeight.hconn_empty (hm : K.IsTopWeight 2 m) (hconn : K.IsConnected) :
    ∀ g : ι → ℝ, (∀ u v, 0 < linkWeightOf m ∅ u v → g u = g v) →
      ∀ u v, 0 < ∑ x, linkWeightOf m ∅ u x → 0 < ∑ x, linkWeightOf m ∅ v x → g u = g v :=
  fun g hg u v hu hv =>
    hm.eq_of_forall_linkWeightOf_pos (σ := ∅) (by rwa [link_empty]) g hg u v hu hv

private theorem IsTopWeight.norm_pos_of_vertex (hm : K.IsTopWeight 2 m) {f : ι → ℝ}
    (hf : ∃ u ∈ K.vertices, f u ≠ 0) :
    0 < ∑ u, (∑ v, linkWeightOf m ∅ u v) * f u ^ 2 := by
  obtain ⟨u, hu, hfu⟩ := hf
  have hnn := linkWeightOf_nonneg hm.nonneg ∅
  refine Finset.sum_pos' (fun x _ => mul_nonneg (Finset.sum_nonneg fun v _ => hnn x v)
    (sq_nonneg _)) ⟨u, Finset.mem_univ u, mul_pos ?_ (by positivity)⟩
  exact (hm.sum_linkWeightOf_empty_pos_iff (by norm_num)).mpr hu

private theorem IsTopWeight.exists_vertex_of_norm_pos (hm : K.IsTopWeight 2 m) {f : ι → ℝ}
    (hf : 0 < ∑ u, (∑ v, linkWeightOf m ∅ u v) * f u ^ 2) : ∃ u ∈ K.vertices, f u ≠ 0 := by
  obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hf.ne'
  have hnn := linkWeightOf_nonneg hm.nonneg ∅
  refine ⟨u, (hm.sum_linkWeightOf_empty_pos_iff (by norm_num)).mp ?_,
    fun h0 => hu (by rw [h0]; ring)⟩
  exact lt_of_le_of_ne (Finset.sum_nonneg fun v _ => hnn u v)
    (Ne.symm fun h0 => hu (by rw [h0]; ring))

/-- **The spectrum below `1`.** Let `m` be a top weight of a connected pure `2`-dimensional
complex `K`, whose vertex links have second eigenvalue at most `lam < 1`. Then every eigenvalue
`γ` of the random walk on the weighted underlying graph (with an eigenfunction that is nonzero
at some vertex) is either `1` or at most `lam / (1 − lam)`: this is trickling down
(`IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_step`). The eigenvalue `1` is simple
(`IsTopWeight.eq_of_eigen_one`). For `lam ≥ 1/2` the bound is at least `1` and says nothing. -/
theorem IsTopWeight.eigen_eq_one_or_le (hm : K.IsTopWeight 2 m) (hconn : K.IsConnected)
    {lam : ℝ} (hlam : lam < 1)
    (hlocal : ∀ σ ∈ K, #σ + 1 = 2 → WalkSecondEigenvalueLE (linkWeightOf m σ) lam)
    {g : ι → ℝ} {γ : ℝ}
    (heig : ∀ u, ∑ v, linkWeightOf m ∅ u v * g v = γ * (∑ v, linkWeightOf m ∅ u v) * g u)
    (hg : ∃ u ∈ K.vertices, g u ≠ 0) : γ = 1 ∨ γ ≤ lam / (1 - lam) := by
  by_cases h1 : γ = 1
  · exact Or.inl h1
  refine Or.inr ?_
  have hstep := hm.walkSecondEigenvalueLE_linkWeightOf_step (σ := ∅) (by simp)
    (by rwa [link_empty]) hlam fun z _ _ => by
      rw [insert_empty]; exact hm.walkSecondEigenvalueLE_singleton hlocal z
  have hN := hm.norm_pos_of_vertex hg
  have h := hstep g (sum_deg_mul_eq_zero_of_eigen (linkWeightOf_symm m ∅) heig h1)
  rw [sum_mul_mul_eq_of_eigen heig] at h
  exact le_of_mul_le_mul_right h hN

/-- **The eigenvalue `1` is simple** on a connected complex: an eigenfunction for `1` is constant
on the vertices. -/
theorem IsTopWeight.eq_of_eigen_one (hm : K.IsTopWeight 2 m) (hconn : K.IsConnected)
    {g : ι → ℝ}
    (heig : ∀ u, ∑ v, linkWeightOf m ∅ u v * g v = 1 * (∑ v, linkWeightOf m ∅ u v) * g u)
    {u v : ι} (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) : g u = g v :=
  _root_.eq_of_eigen_one (linkWeightOf_symm m ∅) (linkWeightOf_nonneg hm.nonneg ∅)
    (hm.hconn_empty hconn) heig u v ((hm.sum_linkWeightOf_empty_pos_iff (by norm_num)).mpr hu)
    ((hm.sum_linkWeightOf_empty_pos_iff (by norm_num)).mpr hv)

/-- **Equality in trickling down for `2`-complexes: `μ = γ` exactly when the edge kernel is
nonzero.** Let `m` be a top weight of a connected pure `2`-dimensional complex `K`, let every
vertex link have random-walk second eigenvalue at most `lam`, with `lam < 1/2`, and let
`γ = lam / (1 − lam)`. Trickling down says the weighted underlying graph has second eigenvalue
`μ ≤ γ`. Equality, in the form "`γ` is the least valid bound", holds exactly when some `f` with
`E_lam f = 0` is nonzero at a vertex of `K`.

Degenerate cases and hypotheses:
* `lam < 1/2` is needed: at `lam = 1/2` the constants lie in the edge kernel
  (`edgeOperator_const_half`) while `μ < 1 = γ`.
* Connectivity is needed for `μ ≤ γ` (a disconnected complex has `μ = 1`) and for the eigenvalue
  `1` to be simple.
* Values of `f` at points that are not vertices are irrelevant to `E_lam f`, so the witness must be
  nonzero at a vertex.
* `lam` is any valid vertex-link bound, not necessarily the largest vertex-link eigenvalue; but
  equality forces it to be one (`IsTopWeight.exists_extremal_edge_of_isLeast`). -/
theorem IsTopWeight.isLeast_iff_exists_edgeOperator_eq_zero (hm : K.IsTopWeight 2 m)
    (hconn : K.IsConnected) {lam : ℝ} (hlam : lam < 1 / 2)
    (hlocal : ∀ σ ∈ K, #σ + 1 = 2 → WalkSecondEigenvalueLE (linkWeightOf m σ) lam) :
    IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf m ∅) μ} (lam / (1 - lam)) ↔
      ∃ f : ι → ℝ, (∀ u v, edgeOperator m lam f u v = 0) ∧ ∃ u ∈ K.vertices, f u ≠ 0 := by
  have hl1 : lam ≠ 1 := by intro h; rw [h] at hlam; norm_num at hlam
  have hγ1 : lam / (1 - lam) ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq (sub_ne_zero.mpr (Ne.symm hl1))] at h
    linarith
  have hloc' := hm.walkSecondEigenvalueLE_singleton hlocal
  have hcrit := fun f => (tricklingEquality_iff hm.nonneg hm.card_eq_of_ne_zero hloc' hl1 f).1
  constructor
  · intro h
    obtain ⟨g, heig, hg, -⟩ := exists_eigen_of_isLeast (linkWeightOf_symm m ∅)
      (linkWeightOf_nonneg hm.nonneg ∅) (hm.hconn_empty hconn) h
    exact ⟨g, (hcrit g).mp heig, hm.exists_vertex_of_norm_pos hg⟩
  · rintro ⟨f, hE, hf⟩
    have heig := (hcrit f).mpr hE
    have hN := hm.norm_pos_of_vertex hf
    refine ⟨?_, fun μ hμ => ?_⟩
    · exact hm.walkSecondEigenvalueLE_linkWeightOf_step (σ := ∅) (by simp)
        (by rwa [link_empty]) (by linarith) fun z _ _ => by
          rw [insert_empty]; exact hloc' z
    · by_contra hlt
      rw [not_le] at hlt
      exact not_walkSecondEigenvalueLE_of_eigen (linkWeightOf_symm m ∅) heig hγ1 hN hlt hμ

/-- `lam` is the exact second eigenvalue of the link of `z` exactly when no smaller bound holds. -/
private theorem isLeast_link_iff {z : ι} {lam : ℝ}
    (hz : WalkSecondEigenvalueLE (linkWeightOf m {z}) lam) :
    IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf m {z}) μ} lam ↔
      ¬ ∃ μ < lam, WalkSecondEigenvalueLE (linkWeightOf m {z}) μ := by
  constructor
  · rintro ⟨-, hlow⟩ ⟨μ, hμ, hμz⟩
    exact absurd (hlow hμz) (not_le.mpr hμ)
  · intro h
    refine ⟨hz, fun μ hμ => ?_⟩
    by_contra hlt
    exact h ⟨μ, not_le.mp hlt, hμ⟩

private theorem IsTopWeight.linkWeightOf_empty_pos_of_mem (hm : K.IsTopWeight 2 m)
    {F : Finset ι} (hF : F ∈ K) (hFc : #F = 2 + 1) {x y : ι} (hx : x ∈ F) (hy : y ∈ F)
    (hxy : x ≠ y) : 0 < linkWeightOf m ∅ x y :=
  hm.linkWeightOf_pos_iff.mpr ⟨hxy, Finset.notMem_empty x, Finset.notMem_empty y, F, hF, hFc,
    Finset.insert_subset hx (Finset.insert_subset hy (Finset.empty_subset F))⟩

/-- **The extremal set spans an edge.** Let `m` be a top weight of a pure `2`-dimensional complex
whose vertex links have second eigenvalue at most `lam`, `lam ≠ 1, 1/2`, and let `f` be a
`γ`-eigenfunction, `γ = lam / (1 − lam)`, that is nonzero at some vertex. Then some edge `z₁ z₂`
has both vertex links of second eigenvalue exactly `lam`.

So the set `Z` of vertices whose links attain `lam` is nonempty (`lam = max_z λ_z`), and it is not
independent; it need not contain a triangle. Proof: if every edge had an endpoint outside `Z`,
every triangle would have an edge disjoint from `Z`, and `f` would vanish on all three of its
vertices (`eq_zero_of_link_lt_of_link_lt`). No connectivity is needed. -/
theorem IsTopWeight.exists_extremal_edge (hm : K.IsTopWeight 2 m) {lam : ℝ}
    (hlocal : ∀ σ ∈ K, #σ + 1 = 2 → WalkSecondEigenvalueLE (linkWeightOf m σ) lam)
    (hlam1 : lam ≠ 1) (hlam2 : lam ≠ 1 / 2) {f : ι → ℝ}
    (heig : ∀ u, ∑ v, linkWeightOf m ∅ u v * f v =
      lam / (1 - lam) * (∑ v, linkWeightOf m ∅ u v) * f u)
    (hf : ∃ u ∈ K.vertices, f u ≠ 0) :
    ∃ z₁ z₂, 0 < linkWeightOf m ∅ z₁ z₂ ∧
      IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf m {z₁}) μ} lam ∧
      IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf m {z₂}) μ} lam := by
  have hloc' := hm.walkSecondEigenvalueLE_singleton hlocal
  by_contra hcon
  have hP : ∀ z₁ z₂, 0 < linkWeightOf m ∅ z₁ z₂ →
      (∃ μ < lam, WalkSecondEigenvalueLE (linkWeightOf m {z₁}) μ) ∨
        (∃ μ < lam, WalkSecondEigenvalueLE (linkWeightOf m {z₂}) μ) := by
    intro z₁ z₂ h
    by_contra hn
    rw [not_or] at hn
    exact hcon ⟨z₁, z₂, h, (isLeast_link_iff (hloc' z₁)).mpr hn.1,
      (isLeast_link_iff (hloc' z₂)).mpr hn.2⟩
  obtain ⟨u, hu, hfu⟩ := hf
  obtain ⟨-, F, hF, huF, hFc⟩ := hm.isPure {u} hu
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hFc
  have hw : ∀ x ∈ ({a, b, c} : Finset ι), ∀ y ∈ ({a, b, c} : Finset ι), x ≠ y →
      0 < linkWeightOf m ∅ x y := fun x hx y hy hxy =>
    hm.linkWeightOf_empty_pos_of_mem hF hFc hx hy hxy
  have ha : a ∈ ({a, b, c} : Finset ι) := by simp
  have hb : b ∈ ({a, b, c} : Finset ι) := by simp
  have hc : c ∈ ({a, b, c} : Finset ι) := by simp
  have hZ : ∀ {x y : ι}, 0 < linkWeightOf m ∅ x y →
      (∃ μ < lam, WalkSecondEigenvalueLE (linkWeightOf m {x}) μ) →
      (∃ μ < lam, WalkSecondEigenvalueLE (linkWeightOf m {y}) μ) →
      f x = 0 ∧ f y = 0 ∧
        ∀ z, (0 < linkWeightOf m ∅ x z ∨ 0 < linkWeightOf m ∅ y z) → f z = 0 :=
    fun hxy hx hy => eq_zero_of_link_lt_of_link_lt hm.nonneg hm.card_eq_of_ne_zero hloc' hlam1
      hlam2 heig hxy hx hy
  -- two of the three vertices are outside `Z`, and they form an edge disjoint from `Z`
  have hall : f a = 0 ∧ f b = 0 ∧ f c = 0 := by
    rcases hP a b (hw a ha b hb hab) with hPa | hPb
    · rcases hP a c (hw a ha c hc hac) with hPa' | hPc
      · rcases hP b c (hw b hb c hc hbc) with hPb | hPc
        · obtain ⟨h1, h2, h3⟩ := hZ (hw a ha b hb hab) hPa hPb
          exact ⟨h1, h2, h3 c (Or.inl (hw a ha c hc hac))⟩
        · obtain ⟨h1, h2, h3⟩ := hZ (hw a ha c hc hac) hPa hPc
          exact ⟨h1, h3 b (Or.inl (hw a ha b hb hab)), h2⟩
      · obtain ⟨h1, h2, h3⟩ := hZ (hw a ha c hc hac) hPa hPc
        exact ⟨h1, h3 b (Or.inl (hw a ha b hb hab)), h2⟩
    · rcases hP a c (hw a ha c hc hac) with hPa | hPc
      · obtain ⟨h1, h2, h3⟩ := hZ (hw a ha b hb hab) hPa hPb
        exact ⟨h1, h2, h3 c (Or.inl (hw a ha c hc hac))⟩
      · obtain ⟨h1, h2, h3⟩ := hZ (hw b hb c hc hbc) hPb hPc
        exact ⟨h3 a (Or.inl (hw b hb a ha (Ne.symm hab))), h1, h2⟩
  have huF' : u ∈ ({a, b, c} : Finset ι) := Finset.singleton_subset_iff.mp huF
  simp only [Finset.mem_insert, Finset.mem_singleton] at huF'
  rcases huF' with rfl | rfl | rfl
  · exact hfu hall.1
  · exact hfu hall.2.1
  · exact hfu hall.2.2

/-- **Structure of the equality case.** Under the hypotheses of
`IsTopWeight.isLeast_iff_exists_edgeOperator_eq_zero`, if trickling down is exact
(`γ = lam / (1 − lam)` is the least valid bound for the underlying graph), then some edge `z₁ z₂`
has both vertex links of second eigenvalue exactly `lam`. In particular `lam` is the largest
vertex-link eigenvalue, and the set of vertices attaining it spans an edge. The behaviour of the
eigenfunctions away from that set is `eq_mul_of_link_lt` and `eq_zero_of_link_lt_of_link_lt`. -/
theorem IsTopWeight.exists_extremal_edge_of_isLeast (hm : K.IsTopWeight 2 m)
    (hconn : K.IsConnected) {lam : ℝ} (hlam : lam < 1 / 2)
    (hlocal : ∀ σ ∈ K, #σ + 1 = 2 → WalkSecondEigenvalueLE (linkWeightOf m σ) lam)
    (h : IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf m ∅) μ} (lam / (1 - lam))) :
    ∃ z₁ z₂, 0 < linkWeightOf m ∅ z₁ z₂ ∧
      IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf m {z₁}) μ} lam ∧
      IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf m {z₂}) μ} lam := by
  have hl1 : lam ≠ 1 := by intro h; rw [h] at hlam; norm_num at hlam
  obtain ⟨f, hE, hf⟩ := (hm.isLeast_iff_exists_edgeOperator_eq_zero hconn hlam hlocal).mp h
  exact hm.exists_extremal_edge hlocal hl1 hlam.ne
    (eigen_of_edgeOperator_eq_zero hm.card_eq_of_ne_zero hl1 hE) hf

private theorem IsTopWeight.forall_edgeOperator_iff (hm : K.IsTopWeight 2 m) {lam : ℝ}
    {f : ι → ℝ} (P : Finset ι → Prop)
    (hP : ∀ u v, u ≠ v → 0 < linkWeightOf m ∅ u v → (P {u, v} ↔ edgeOperator m lam f u v = 0)) :
    (∀ u v, edgeOperator m lam f u v = 0) ↔ ∀ e ∈ K, #e = 2 → P e := by
  constructor
  · intro hE e he hec
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hec
    obtain ⟨-, F, hF, heF, hFc⟩ := hm.isPure _ he
    have hw : 0 < linkWeightOf m ∅ u v :=
      hm.linkWeightOf_pos_iff.mpr ⟨huv, Finset.notMem_empty u, Finset.notMem_empty v, F, hF, hFc,
        by rwa [Finset.insert_empty]⟩
    exact (hP u v huv hw).mpr (hE u v)
  · intro hE u v
    rcases (linkWeightOf_nonneg hm.nonneg ∅ u v).eq_or_lt with h0 | hw
    · exact edgeOperator_eq_zero_of_linkWeightOf_eq_zero hm.nonneg hm.card_eq_of_ne_zero h0.symm
        lam f
    · obtain ⟨huv, -, -, F, hF, -, hsub⟩ := hm.linkWeightOf_pos_iff.mp hw
      have he : ({u, v} : Finset ι) ∈ K :=
        K.mem_of_subset hF (by rwa [Finset.insert_empty] at hsub) (Finset.insert_nonempty _ _)
      exact (hP u v huv hw).mp (hE _ he (Finset.card_pair huv))

/-- **The equality criterion through the edge walk.** Let `m` be a top weight of a pure
`2`-dimensional complex `K` whose vertex links have second eigenvalue at most `lam ≠ 1`, and let
`γ = lam / (1 − lam)`. Then `f` is a `γ`-eigenfunction of the walk on the underlying graph exactly
when its lift `liftSum f` (`f u + f v` on the edge `u v`) is an eigenfunction, on the edges of `K`,
of the lazy up-down walk on level `1` with eigenvalue `2 (1 + lam) / 3`, and exactly when it is one
of the non-lazy up-down walk with eigenvalue `lam + 1/2`. The lift is injective on the vertices
(`IsPure.eq_of_liftSum_eq`), so this identifies the `γ`-eigenspace of the walk with a subspace of
that eigenspace of the edge walk.

The eigen-equations are imposed on the edges only: off the faces `upWalk` takes the junk value
`0`. -/
theorem IsTopWeight.tricklingEquality_iff_upWalk (hm : K.IsTopWeight 2 m) {lam : ℝ}
    (hlocal : ∀ σ ∈ K, #σ + 1 = 2 → WalkSecondEigenvalueLE (linkWeightOf m σ) lam)
    (hlam : lam ≠ 1) (f : ι → ℝ) :
    ((∀ u, ∑ v, linkWeightOf m ∅ u v * f v =
        lam / (1 - lam) * (∑ v, linkWeightOf m ∅ u v) * f u) ↔
      ∀ e ∈ K, #e = 2 → upWalk m 2 1 (liftSum f) e = 2 * (1 + lam) / 3 * liftSum f e) ∧
    ((∀ u, ∑ v, linkWeightOf m ∅ u v * f v =
        lam / (1 - lam) * (∑ v, linkWeightOf m ∅ u v) * f u) ↔
      ∀ e ∈ K, #e = 2 → nonLazyUpWalk m 2 1 (liftSum f) e = (lam + 1 / 2) * liftSum f e) := by
  have hcrit := (tricklingEquality_iff hm.nonneg hm.card_eq_of_ne_zero
    (hm.walkSecondEigenvalueLE_singleton hlocal) hlam f).1
  exact ⟨hcrit.trans (hm.forall_edgeOperator_iff _ fun u v huv hw =>
      (upWalk_liftSum_eq_iff hm.card_eq_of_ne_zero lam f huv hw).1),
    hcrit.trans (hm.forall_edgeOperator_iff _ fun u v huv hw =>
      (upWalk_liftSum_eq_iff hm.card_eq_of_ne_zero lam f huv hw).2)⟩

omit [Fintype ι] in
/-- **The lift is injective on the vertices.** In a pure `2`-dimensional complex, a function on the
points is determined on the vertices by the sums `f u + f v` over the edges: a vertex `v` lies in a
triangle `{v, a, b}`, and `2 f v = (f v + f a) + (f v + f b) − (f a + f b)`. No connectivity is
needed. -/
theorem IsPure.eq_of_liftSum_eq (hpure : K.IsPure 2) {f g : ι → ℝ}
    (h : ∀ e ∈ K, #e = 2 → liftSum f e = liftSum g e) {v : ι} (hv : v ∈ K.vertices) :
    f v = g v := by
  obtain ⟨-, F, hF, hvF, hFc⟩ := hpure {v} hv
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hFc
  have hpair : ∀ x y, x ≠ y → ({x, y} : Finset ι) ⊆ {a, b, c} → f x + f y = g x + g y := by
    intro x y hxy hsub
    have := h {x, y} (K.mem_of_subset hF hsub (Finset.insert_nonempty _ _)) (Finset.card_pair hxy)
    unfold liftSum at this
    rwa [Finset.sum_pair hxy, Finset.sum_pair hxy] at this
  have h1 := hpair a b hab (by intro y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  have h2 := hpair a c hac (by intro y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  have h3 := hpair b c hbc (by intro y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  have hv' : v ∈ ({a, b, c} : Finset ι) := Finset.singleton_subset_iff.mp hvF
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
  rcases hv' with rfl | rfl | rfl <;> linarith

/-- **The criterion fails at `lam = 1/2`.** On a connected complex the second eigenvalue of the
underlying graph is below `1 = (1/2) / (1 − 1/2)`, although the constants lie in the edge kernel
of `E_{1/2}` (`edgeOperator_const_half`). -/
theorem IsTopWeight.not_isLeast_half (hm : K.IsTopWeight 2 m) (hconn : K.IsConnected) :
    ¬ IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf m ∅) μ} ((1 / 2) / (1 - 1 / 2)) := by
  intro h
  exact ne_one_of_isLeast (linkWeightOf_symm m ∅) (linkWeightOf_nonneg hm.nonneg ∅)
    (hm.hconn_empty hconn) h (by norm_num)

/-- In the weighted underlying graph of a `2`-dimensional complex, a point that is not a vertex
is isolated. -/
private theorem IsTopWeight.linkWeightOf_empty_eq_zero_of_notMem (hm : K.IsTopWeight 2 m)
    (x : ι) {v : ι} (hv : v ∉ K.vertices) : linkWeightOf m ∅ x v = 0 := by
  by_contra hne
  have hpos := lt_of_le_of_ne (linkWeightOf_nonneg hm.nonneg ∅ x v) (Ne.symm hne)
  obtain ⟨-, -, -, F, hF, -, hsub⟩ := hm.linkWeightOf_pos_iff.mp hpos
  exact hv (K.mem_of_subset hF (Finset.singleton_subset_iff.mpr
    (hsub (Finset.mem_insert_of_mem (Finset.mem_insert_self v ∅)))) (Finset.singleton_nonempty v))

open Classical in
/-- **The case `lam = 0`: equality is a determinant condition.** Let `m` be a top weight of a
connected pure `2`-dimensional complex whose vertex links have second eigenvalue at most `0`.
Then the weighted underlying graph has second eigenvalue exactly `0` (the trickling-down value
`0 / (1 − 0)`) exactly when the weight matrix `(w(u, v))_{u, v ∈ V}` on the vertices of `K` is
singular. Here `w(u, v)` is the total weight of the triangles through `u v`.

At `γ = 0` the `γ`-eigenspace is the kernel of `W` (the degree matrix drops out), so this is
`IsTopWeight.isLeast_iff_exists_edgeOperator_eq_zero` read through `tricklingEquality_iff`. The
matrix is indexed by the vertices only; on all of `ι` it would be singular as soon as some point is
not a vertex. The same statement with the `0/1` adjacency matrix in place of `w` is not proved
here (it agreed with this one on every complex tested by the proposer and the skeptic). -/
theorem IsTopWeight.isLeast_zero_iff_det_eq_zero (hm : K.IsTopWeight 2 m)
    (hconn : K.IsConnected)
    (hlocal : ∀ σ ∈ K, #σ + 1 = 2 → WalkSecondEigenvalueLE (linkWeightOf m σ) 0) :
    IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf m ∅) μ} 0 ↔
      (Matrix.of fun u v : K.vertices => linkWeightOf m ∅ u v).det = 0 := by
  have h := hm.isLeast_iff_exists_edgeOperator_eq_zero hconn (by norm_num) hlocal
  have h0 : (0 : ℝ) / (1 - 0) = 0 := by norm_num
  rw [h0] at h
  rw [h, ← Matrix.exists_mulVec_eq_zero_iff]
  have hloc' := hm.walkSecondEigenvalueLE_singleton hlocal
  have hcrit := fun f =>
    (tricklingEquality_iff hm.nonneg hm.card_eq_of_ne_zero hloc' (by norm_num) f).1
  have hsum : ∀ x (g : ι → ℝ), ∑ v, linkWeightOf m ∅ x v * g v =
      ∑ v : K.vertices, linkWeightOf m ∅ x v * g v := by
    intro x g
    have hsplit := Fintype.sum_subtype_add_sum_subtype (· ∈ K.vertices)
      (fun v => linkWeightOf m ∅ x v * g v)
    have hzero : ∑ v : {v // v ∉ K.vertices}, linkWeightOf m ∅ x v * g v = 0 :=
      Finset.sum_eq_zero fun v _ => by
        rw [hm.linkWeightOf_empty_eq_zero_of_notMem x v.2, zero_mul]
    rw [hzero, add_zero] at hsplit
    exact hsplit.symm
  constructor
  · rintro ⟨f, hE, u, hu, hfu⟩
    have heig := (hcrit f).mpr hE
    refine ⟨fun v => f v, fun h0 => hfu (congrFun h0 ⟨u, hu⟩), ?_⟩
    funext x
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← hsum, heig]
    ring
  · rintro ⟨x, hx0, hx⟩
    refine ⟨fun v => if h : v ∈ K.vertices then x ⟨v, h⟩ else 0, (hcrit _).mp ?_, ?_⟩
    · intro u
      rw [zero_div, zero_mul, zero_mul, hsum]
      by_cases hu : u ∈ K.vertices
      · have := congrFun hx ⟨u, hu⟩
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
        rw [← this]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [dif_pos v.2]
      · refine Finset.sum_eq_zero fun v _ => ?_
        rw [linkWeightOf_symm, hm.linkWeightOf_empty_eq_zero_of_notMem v hu, zero_mul]
    · obtain ⟨⟨v, hv⟩, hxv⟩ := Function.ne_iff.mp hx0
      exact ⟨v, hv, by simpa [hv] using hxv⟩

/-- **Negative vertex links force the complete complex** (the weighted form of
`eq_complete_of_trickling_down_neg`, for `d = 2`). Let `m` be a top weight of a connected pure
`2`-dimensional complex `K` all of whose vertex links have some negative second-eigenvalue bound.
Then every set of at most three vertices of `K` is a face: `K` is the complete `2`-complex on its
vertex set.

This is one half of "`max_z λ_z < 0` exactly for the complete complex"; the other half holds for
the uniform weight (`complete_two_isLeast`), with `λ_z = −1/(N − 2)`. It does not hold for every
positive weight on the complete complex: on five or more points a weight concentrated on two
triangles through a common vertex `z`, meeting only at `z`, makes the link of `z` nearly two
disjoint edges, with positive second eigenvalue (`twoHeavyWeight_spec`).
Connectivity is needed: two disjoint triangles have vertex links with second eigenvalue `−1`. -/
theorem IsTopWeight.mem_of_link_neg (hm : K.IsTopWeight 2 m) (hconn : K.IsConnected)
    (hneg : ∀ σ ∈ K, #σ + 1 = 2 → ∃ lam < 0, WalkSecondEigenvalueLE (linkWeightOf m σ) lam)
    {s : Finset ι} (hs : s.Nonempty) (hsv : ∀ v ∈ s, v ∈ K.vertices) (hcard : #s ≤ 3) :
    s ∈ K :=
  hm.mem_of_trickling_down_neg le_rfl (fun σ hσ hc => by
    rw [card_eq_zero.mp (by omega : #σ = 0), link_empty]; exact hconn) hneg hs hsv hcard

end Complex

/-- **Equality for the complete complex.** In the complete `2`-dimensional complex on
`N = Fintype.card ι ≥ 3` points, with every triangle of weight `1`, every vertex link has second
eigenvalue exactly `lam = −1/(N − 2)`, and the underlying graph has second eigenvalue exactly
`lam / (1 − lam) = −1/(N − 1)`: trickling down is exact, with `lam` the largest vertex-link
eigenvalue. By `IsTopWeight.isLeast_iff_exists_edgeOperator_eq_zero` the edge kernel of
`E_{−1/(N−2)}` is therefore nonzero at some vertex.

This is `trickling_down_complete` and `walkSecondEigenvalueLE_linkWeight_complete_iff` for
`d = 2`. For a larger `lam` (still `< 0`) used as the link bound, `lam / (1 − lam) > −1/(N − 1)`
and equality fails; for non-uniform weights on the complete complex it can fail too (seen
numerically by the skeptic; not formalised here). -/
theorem complete_two_isLeast (hn : 2 + 1 ≤ Fintype.card ι) :
    (∀ z : ι, IsLeast {μ | WalkSecondEigenvalueLE ((complete ι 2).linkWeight 2 {z}) μ}
      (-(1 / ((Fintype.card ι : ℝ) - 2)))) ∧
    IsLeast {μ | WalkSecondEigenvalueLE ((complete ι 2).linkWeight 2 ∅) μ}
      (-(1 / ((Fintype.card ι : ℝ) - 2)) / (1 - -(1 / ((Fintype.card ι : ℝ) - 2)))) ∧
    -(1 / ((Fintype.card ι : ℝ) - 2)) / (1 - -(1 / ((Fintype.card ι : ℝ) - 2))) =
      -(1 / ((Fintype.card ι : ℝ) - 1)) := by
  have e : -(1 / ((Fintype.card ι : ℝ) - 2)) / (1 - -(1 / ((Fintype.card ι : ℝ) - 2))) =
      -(1 / ((Fintype.card ι : ℝ) - 1)) := by
    have h := trickling_down_bound_complete (n := Fintype.card ι) (d := 2) (k := 0) (by omega)
    norm_num at h ⊢
    convert h using 2
  have hlink : ∀ (z : ι) (μ : ℝ), WalkSecondEigenvalueLE ((complete ι 2).linkWeight 2 {z}) μ ↔
      -(1 / ((Fintype.card ι : ℝ) - 2)) ≤ μ := by
    intro z μ
    rw [walkSecondEigenvalueLE_linkWeight_complete_iff hn (by simp), card_singleton,
      Nat.cast_one, show (Fintype.card ι : ℝ) - 1 - 1 = (Fintype.card ι : ℝ) - 2 by ring]
  have hwhole : ∀ μ : ℝ, WalkSecondEigenvalueLE ((complete ι 2).linkWeight 2 ∅) μ ↔
      -(1 / ((Fintype.card ι : ℝ) - 1)) ≤ μ := by
    intro μ
    rw [walkSecondEigenvalueLE_linkWeight_complete_iff hn (by simp), card_empty, Nat.cast_zero,
      sub_zero]
  refine ⟨fun z => ⟨(hlink z _).mpr le_rfl, fun μ hμ => (hlink z μ).mp hμ⟩,
    ⟨?_, fun μ hμ => ?_⟩, e⟩
  · rw [e]
    exact (hwhole _).mpr le_rfl
  · rw [e]
    exact (hwhole μ).mp hμ

/-- A non-uniform weight on the complete complex on five points: `1` on the triangles `{0, 1, 2}`
and `{0, 3, 4}`, which meet only at `0`, and `1/4` on the other eight triangles. -/
noncomputable def twoHeavyWeight (F : Finset (Fin 5)) : ℝ :=
  if F = {0, 1, 2} ∨ F = {0, 3, 4} then 1 else if #F = 3 then 1 / 4 else 0

/-- **Negative vertex links are not forced by completeness.** `twoHeavyWeight` is a top weight
of the complete `2`-complex on five points, but the link of `0` (nearly two disjoint edges
`1 2` and `3 4`) has no bound `≤ 0` on its second eigenvalue: the function `1, 1, −1, −1` on
`1, 2, 3, 4` has mean zero and positive quadratic form. So in `IsTopWeight.mem_of_link_neg` the
converse ("complete implies negative vertex links") holds for the uniform weight
(`complete_two_isLeast`) but not for every positive weight; on four points (where the links are
weighted triangles) it does hold for every positive weight, which is not formalised here. -/
theorem twoHeavyWeight_spec :
    (complete (Fin 5) 2).IsTopWeight 2 twoHeavyWeight ∧
      ∀ μ ≤ 0, ¬ WalkSecondEigenvalueLE (linkWeightOf twoHeavyWeight {0}) μ := by
  have hm : (complete (Fin 5) 2).IsTopWeight 2 twoHeavyWeight := by
    refine ⟨isPure_complete (by decide), ⟨{0}, mem_complete.mpr ⟨by decide, by decide⟩⟩,
      fun F _ hFc => ?_, fun F hF => ?_⟩
    · unfold twoHeavyWeight
      split_ifs <;> norm_num
    · unfold twoHeavyWeight
      have hF' : ¬ #F = 2 + 1 := fun hc => hF ⟨mem_complete.mpr ⟨Finset.card_pos.mp (by omega),
        by omega⟩, hc⟩
      rw [if_neg, if_neg hF']
      rintro (rfl | rfl) <;> exact hF' (by decide)
  refine ⟨hm, fun μ hμ h => ?_⟩
  have h1 := h (fun v => if v = 1 ∨ v = 2 then 1 else if v = 3 ∨ v = 4 then -1 else 0) (by
    simp only [Fin.sum_univ_five, linkWeightOf_singleton_eq hm.card_eq_of_ne_zero, twoHeavyWeight]
    simp (config := {decide := true}) only [if_true, if_false]
    norm_num)
  simp only [Fin.sum_univ_five, linkWeightOf_singleton_eq hm.card_eq_of_ne_zero,
    twoHeavyWeight] at h1
  simp (config := {decide := true}) only [if_true, if_false] at h1
  norm_num at h1
  nlinarith

/-! ### A sharp family: the tetrahedron with two pendant triangles -/

section Sharp

/-- **The link of a tetrahedron vertex in `tetraPendant`.** The link is a triangle `a b c` with a
pendant edge `c e` of weight `t > 0`; degrees `2, 2, 2 + t, t`. If `x > 0` is a root of
`2 (t + 2) x² + (t + 2) x − t`, then on the mean-zero space the quadratic form is at most `x` times
the norm. Certificate: with `A = 4tx − 2t + 16x > 0` and `B = 4tx + 2t + 8x`,
`t A (x‖f‖² − Q f) = A t (4x + 2) ((a − b)/2)² + (A (a + b)/2 + B c)² + 4t(t + 3) R(x) c²` on the
mean-zero hyperplane, where `R(x) = 0`. -/
theorem pendant_ineq {t x : ℝ} (ht : 0 < t) (hx : 0 < x)
    (hR : 2 * (t + 2) * x ^ 2 + (t + 2) * x - t = 0) {a b c e : ℝ}
    (hf : 2 * a + 2 * b + (2 + t) * c + t * e = 0) :
    2 * (a * b + a * c + b * c + t * c * e) ≤
      x * (2 * a ^ 2 + 2 * b ^ 2 + (2 + t) * c ^ 2 + t * e ^ 2) := by
  set A := 4 * t * x - 2 * t + 16 * x with hA
  set B := 4 * t * x + 2 * t + 8 * x with hB
  have hApos : 0 < A := by
    by_contra h
    push Not at h
    nlinarith [mul_pos ht hx, sq_nonneg x]
  have key : t * A * (x * (2 * a ^ 2 + 2 * b ^ 2 + (2 + t) * c ^ 2 + t * e ^ 2) -
      2 * (a * b + a * c + b * c + t * c * e)) =
      A * t * (4 * x + 2) * ((a - b) / 2) ^ 2 + (A * ((a + b) / 2) + B * c) ^ 2 +
        4 * t * (t + 3) * (2 * (t + 2) * x ^ 2 + (t + 2) * x - t) * c ^ 2 := by
    linear_combination (-2 * (2 * t * x - t + 8 * x) *
      (2 * a * x + 2 * b * x + c * t * x + 2 * c * t + 2 * c * x - e * t * x)) * hf
  have hR0 : 0 ≤ A * t * (4 * x + 2) * ((a - b) / 2) ^ 2 + (A * ((a + b) / 2) + B * c) ^ 2 +
      4 * t * (t + 3) * (2 * (t + 2) * x ^ 2 + (t + 2) * x - t) * c ^ 2 := by
    rw [hR]
    have : 0 ≤ A * t * (4 * x + 2) * ((a - b) / 2) ^ 2 := by positivity
    nlinarith [sq_nonneg (A * ((a + b) / 2) + B * c)]
  rw [← key] at hR0
  have htA : 0 < t * A := mul_pos ht hApos
  nlinarith


/-- The complex `X`: the boundary of the tetrahedron on `{0, 1, 2, 3}` with a pendant triangle
glued on each of two opposite edges, `{0, 3, 4}` and `{1, 2, 5}`. -/
def tetraPendant : PreAbstractSimplicialComplex (Fin 6) where
  faces := {s | s.Nonempty ∧ (s ⊆ {0, 1, 2} ∨ s ⊆ {0, 1, 3} ∨ s ⊆ {0, 2, 3} ∨ s ⊆ {1, 2, 3} ∨
    s ⊆ {0, 3, 4} ∨ s ⊆ {1, 2, 5})}
  isRelLowerSet_faces := by
    rintro s ⟨hne, hs⟩
    refine ⟨hne, fun t hts ht => ⟨ht, ?_⟩⟩
    rcases hs with h | h | h | h | h | h
    · exact Or.inl (hts.trans h)
    · exact Or.inr (Or.inl (hts.trans h))
    · exact Or.inr (Or.inr (Or.inl (hts.trans h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hts.trans h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hts.trans h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hts.trans h)))))

/-- The faces of `tetraPendant`, by definition. -/
theorem mem_tetraPendant {s : Finset (Fin 6)} :
    s ∈ tetraPendant ↔ s.Nonempty ∧ (s ⊆ {0, 1, 2} ∨ s ⊆ {0, 1, 3} ∨ s ⊆ {0, 2, 3} ∨
      s ⊆ {1, 2, 3} ∨ s ⊆ {0, 3, 4} ∨ s ⊆ {1, 2, 5}) := Iff.rfl

/-- The weight `m_t` on the triangles of `tetraPendant`: `1` on the four triangles of the
tetrahedron, `t` on the two pendant triangles, `0` on every other set. -/
noncomputable def tetraPendantWeight (t : ℝ) (s : Finset (Fin 6)) : ℝ :=
  if s = {0, 1, 2} ∨ s = {0, 1, 3} ∨ s = {0, 2, 3} ∨ s = {1, 2, 3} then 1
  else if s = {0, 3, 4} ∨ s = {1, 2, 5} then t else 0

private theorem eq_of_subset_three {s T : Finset (Fin 6)} (hT : #T = 3) (hs : #s = 2 + 1)
    (h : s ⊆ T) : s = T :=
  Finset.eq_of_subset_of_card_le h (by rw [hT, hs])

/-- For `t > 0`, `tetraPendantWeight t` is a top weight of the pure `2`-dimensional complex
`tetraPendant`. For `t ≤ 0` it is not: the pendant triangles would get weight `≤ 0`. -/
theorem isTopWeight_tetraPendant {t : ℝ} (ht : 0 < t) :
    tetraPendant.IsTopWeight 2 (tetraPendantWeight t) where
  isPure := by
    intro σ hσ
    rcases (mem_tetraPendant.mp hσ).2 with h | h | h | h | h | h
    all_goals
      refine ⟨(card_le_card h).trans (by decide), _, mem_tetraPendant.mpr ⟨by decide, ?_⟩, h,
        by decide⟩
      simp
  exists_mem := ⟨{0, 1, 2}, mem_tetraPendant.mpr ⟨by decide, by simp⟩⟩
  pos := by
    intro F hF hFc
    rcases (mem_tetraPendant.mp hF).2 with h | h | h | h | h | h <;>
      · rw [eq_of_subset_three (by decide) hFc h]
        unfold tetraPendantWeight
        simp (config := {decide := true}) [ht]
  eq_zero := by
    intro F hF
    unfold tetraPendantWeight
    rw [if_neg, if_neg]
    · rintro (rfl | rfl)
      · exact hF ⟨mem_tetraPendant.mpr ⟨by decide, by simp⟩, by decide⟩
      · exact hF ⟨mem_tetraPendant.mpr ⟨by decide, by simp⟩, by decide⟩
    · rintro (rfl | rfl | rfl | rfl)
      all_goals exact hF ⟨mem_tetraPendant.mpr ⟨by decide, by simp⟩, by decide⟩

/-- `tetraPendant` is connected. -/
theorem isConnected_tetraPendant : tetraPendant.IsConnected := by
  rw [IsConnected, SimpleGraph.connected_iff]
  have hv : ∀ v : Fin 6, v ∈ tetraPendant.vertices := by
    intro v
    show {v} ∈ tetraPendant
    rw [mem_tetraPendant]
    fin_cases v <;> decide
  have hadj : ∀ a b : Fin 6, a ≠ b → ({a, b} : Finset (Fin 6)) ∈ tetraPendant →
      (tetraPendant.oneSkeleton.induce tetraPendant.vertices).Adj ⟨a, hv a⟩ ⟨b, hv b⟩ := by
    intro a b hab h
    rw [SimpleGraph.induce_adj, oneSkeleton, SimpleGraph.fromRel_adj]
    exact ⟨hab, Or.inl h⟩
  have hr : ∀ a : tetraPendant.vertices,
      (tetraPendant.oneSkeleton.induce tetraPendant.vertices).Reachable a ⟨0, hv 0⟩ := by
    rintro ⟨a, ha⟩
    fin_cases a
    · rfl
    · exact (hadj 1 0 (by decide) (by rw [mem_tetraPendant]; decide)).reachable
    · exact (hadj 2 0 (by decide) (by rw [mem_tetraPendant]; decide)).reachable
    · exact (hadj 3 0 (by decide) (by rw [mem_tetraPendant]; decide)).reachable
    · exact (hadj 4 0 (by decide) (by rw [mem_tetraPendant]; decide)).reachable
    · exact (hadj 5 1 (by decide) (by rw [mem_tetraPendant]; decide)).reachable.trans
        (hadj 1 0 (by decide) (by rw [mem_tetraPendant]; decide)).reachable
  exact ⟨fun a b => (hr a).trans (hr b).symm, ⟨⟨0, hv 0⟩⟩⟩


/-- `tetraPendantWeight t` as a sum of point masses on the six triangles. -/
theorem tetraPendantWeight_eq (t : ℝ) (F : Finset (Fin 6)) :
    tetraPendantWeight t F =
      (if F = {0, 1, 2} then 1 else 0) + (if F = {0, 1, 3} then 1 else 0) +
        (if F = {0, 2, 3} then 1 else 0) + (if F = {1, 2, 3} then 1 else 0) +
          (if F = {0, 3, 4} then t else 0) + (if F = {1, 2, 5} then t else 0) := by
  unfold tetraPendantWeight
  by_cases h1 : F = {0, 1, 2}
  · subst h1; simp (config := {decide := true})
  by_cases h2 : F = {0, 1, 3}
  · subst h2; simp (config := {decide := true})
  by_cases h3 : F = {0, 2, 3}
  · subst h3; simp (config := {decide := true})
  by_cases h4 : F = {1, 2, 3}
  · subst h4; simp (config := {decide := true})
  by_cases h5 : F = {0, 3, 4}
  · subst h5; simp (config := {decide := true})
  by_cases h6 : F = {1, 2, 5}
  · subst h6; simp (config := {decide := true})
  simp [h1, h2, h3, h4, h5, h6]

/-- The weight of a set `s` in `tetraPendant`: the total weight of the triangles containing it. -/
theorem faceWeight_tetraPendantWeight (t : ℝ) (s : Finset (Fin 6)) :
    faceWeight (tetraPendantWeight t) s =
      (if s ⊆ {0, 1, 2} then 1 else 0) + (if s ⊆ {0, 1, 3} then 1 else 0) +
        (if s ⊆ {0, 2, 3} then 1 else 0) + (if s ⊆ {1, 2, 3} then 1 else 0) +
          (if s ⊆ {0, 3, 4} then t else 0) + (if s ⊆ {1, 2, 5} then t else 0) := by
  unfold faceWeight
  simp only [tetraPendantWeight_eq, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_filter, Finset.mem_univ, true_and]


/-- Evaluation of the link weights of `tetraPendant`. -/
private theorem linkWeightOf_tetraPendant (t : ℝ) (σ : Finset (Fin 6)) (u v : Fin 6) :
    linkWeightOf (tetraPendantWeight t) σ u v =
      if u ≠ v ∧ u ∉ σ ∧ v ∉ σ then
        (if insert u (insert v σ) ⊆ {0, 1, 2} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {0, 1, 3} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {0, 2, 3} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {1, 2, 3} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {0, 3, 4} then t else 0) +
          (if insert u (insert v σ) ⊆ {1, 2, 5} then t else 0)
      else 0 := by
  rw [linkWeightOf, faceWeight_tetraPendantWeight]

/-- The links of the points of the tetrahedron are triangles with a pendant edge of weight `t`,
with second eigenvalue at most `x`. -/
private theorem walkSecondEigenvalueLE_tetraPendant_core {t x : ℝ} (ht : 0 < t) (hx : 0 < x)
    (hR : 2 * (t + 2) * x ^ 2 + (t + 2) * x - t = 0) {z : Fin 6} (hz : z ≤ 3) :
    WalkSecondEigenvalueLE (linkWeightOf (tetraPendantWeight t) {z}) x := by
  intro f hf
  simp only [Fin.sum_univ_six, linkWeightOf_tetraPendant] at hf ⊢
  fin_cases z
  all_goals simp (config := {decide := true}) only [if_true, if_false] at hf ⊢
  all_goals norm_num at hf ⊢
  · linarith [pendant_ineq ht hx hR (a := f 1) (b := f 2) (c := f 3) (e := f 4) (by linarith)]
  · linarith [pendant_ineq ht hx hR (a := f 0) (b := f 3) (c := f 2) (e := f 5) (by linarith)]
  · linarith [pendant_ineq ht hx hR (a := f 0) (b := f 3) (c := f 1) (e := f 5) (by linarith)]
  · linarith [pendant_ineq ht hx hR (a := f 1) (b := f 2) (c := f 0) (e := f 4) (by linarith)]
  · exact absurd hz (by decide)
  · exact absurd hz (by decide)

/-- The links of the two pendant points are single edges, with second eigenvalue `−1`. -/
private theorem walkSecondEigenvalueLE_tetraPendant_pendant {t : ℝ} (ht : 0 < t) {z : Fin 6}
    (hz : 4 ≤ z) : WalkSecondEigenvalueLE (linkWeightOf (tetraPendantWeight t) {z}) (-1) := by
  intro f hf
  simp only [Fin.sum_univ_six, linkWeightOf_tetraPendant] at hf ⊢
  fin_cases z
  all_goals simp (config := {decide := true}) only [if_true, if_false] at hf ⊢
  all_goals norm_num at hf ⊢
  all_goals try exact absurd hz (by decide)
  · have h3 : f 0 + f 3 = 0 :=
      (mul_eq_zero.mp (by linarith : t * (f 0 + f 3) = 0)).resolve_left ht.ne'
    have e : t * (f 0 + f 3) ^ 2 = 0 := by rw [h3]; ring
    nlinarith [e]
  · have h3 : f 1 + f 2 = 0 :=
      (mul_eq_zero.mp (by linarith : t * (f 1 + f 2) = 0)).resolve_left ht.ne'
    have e : t * (f 1 + f 2) ^ 2 = 0 := by rw [h3]; ring
    nlinarith [e]

/-- The `γ`-eigenfunction of `tetraPendant`: `γ, −γ, −γ, γ` at `0, 1, 2, 3` and `1, −1` at the
pendant points `4, 5`. -/
def tetraPendantEigen (γ : ℝ) (v : Fin 6) : ℝ :=
  if v = 0 ∨ v = 3 then γ else if v = 1 ∨ v = 2 then -γ else if v = 4 then 1 else -1

private theorem tetraPendant_eigen {t γ : ℝ} (hRγ : (2 * t + 6) * γ ^ 2 + (2 - t) * γ - t = 0)
    (u : Fin 6) :
    ∑ v, linkWeightOf (tetraPendantWeight t) ∅ u v * tetraPendantEigen γ v =
      γ * (∑ v, linkWeightOf (tetraPendantWeight t) ∅ u v) * tetraPendantEigen γ u := by
  simp only [Fin.sum_univ_six, linkWeightOf_tetraPendant, tetraPendantEigen]
  fin_cases u
  all_goals simp (config := {decide := true}) only [if_true, if_false]
  all_goals norm_num
  all_goals first
    | linear_combination hRγ
    | linear_combination (-1 : ℝ) * hRγ
    | ring

private theorem linkWeightOf_tetraPendant_empty_eval (t : ℝ) :
    linkWeightOf (tetraPendantWeight t) ∅ 0 1 = 2 ∧ linkWeightOf (tetraPendantWeight t) ∅ 1 0 = 2 ∧
    linkWeightOf (tetraPendantWeight t) ∅ 2 0 = 2 ∧ linkWeightOf (tetraPendantWeight t) ∅ 3 1 = 2 ∧
    linkWeightOf (tetraPendantWeight t) ∅ 4 0 = t := by
  simp only [linkWeightOf_tetraPendant]
  simp (config := {decide := true}) only [if_true, if_false]
  norm_num

omit [Fintype ι] [DecidableEq ι] in
private theorem norm_pos_of_term [Fintype ι] {w : ι → ι → ℝ} (hnn : ∀ u v, 0 ≤ w u v)
    {h : ι → ℝ} (u : ι) (hu : 0 < ∑ v, w u v) (hh : h u ≠ 0) :
    0 < ∑ u, (∑ v, w u v) * h u ^ 2 :=
  Finset.sum_pos' (fun x _ => mul_nonneg (Finset.sum_nonneg fun v _ => hnn x v) (sq_nonneg _))
    ⟨u, Finset.mem_univ u, mul_pos hu (by positivity)⟩

/-- **A sharp family for trickling down in dimension `2`.** Let `t > 0` and let `x > 0` be the
positive root of `2 (t + 2) x² + (t + 2) x − t = 0` (so `0 < x < 1/2`). In the complex
`tetraPendant` (the boundary of the tetrahedron `{0, 1, 2, 3}` with pendant triangles `{0, 3, 4}`
and `{1, 2, 5}` on two opposite edges), with weight `1` on the tetrahedron and `t` on the pendant
triangles:
* the links of `0, 1, 2, 3` (a triangle with a pendant edge of weight `t`) have second eigenvalue
  exactly `x`;
* the links of the pendant points `4, 5` (a single edge) have second eigenvalue exactly `−1`;
* the weighted underlying graph has second eigenvalue exactly `μ = x / (1 − x)`, the value that
  trickling down (`trickling_down_weighted`) gives from the vertex-link bound `x`; equivalently
  `(2t + 6) μ² + (2 − t) μ − t = 0`.

"Exactly `a`" is `IsLeast {μ | WalkSecondEigenvalueLE … μ} a`. The eigenfunction is
`γ, −γ, −γ, γ, 1, −1` with `γ = x / (1 − x)`; the link lower bounds come from the equality
criterion (`tricklingEquality_iff`), which makes each localisation of that eigenfunction a link
eigenfunction. Every positive `t` is allowed; the root `x` ranges over all of `(0, 1/2)`
(`tetraPendant_root_*`). -/
theorem tetraPendant_sharp {t x : ℝ} (ht : 0 < t) (hx : 0 < x)
    (hR : 2 * (t + 2) * x ^ 2 + (t + 2) * x - t = 0) :
    x < 1 / 2 ∧
    (∀ z : Fin 6, z ≤ 3 →
      IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf (tetraPendantWeight t) {z}) μ} x) ∧
    (∀ z : Fin 6, 4 ≤ z →
      IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf (tetraPendantWeight t) {z}) μ} (-1)) ∧
    IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf (tetraPendantWeight t) ∅) μ} (x / (1 - x)) ∧
    (2 * t + 6) * (x / (1 - x)) ^ 2 + (2 - t) * (x / (1 - x)) - t = 0 := by
  have hx2 : x < 1 / 2 := by
    by_contra h
    push Not at h
    have := mul_nonneg (sub_nonneg.mpr h)
      (show (0 : ℝ) ≤ 2 * (t + 2) * (x + 1 / 2) + (t + 2) by nlinarith)
    nlinarith
  have hx1 : x ≠ 1 := by intro h; rw [h] at hx2; norm_num at hx2
  have h1x : 0 < 1 - x := by linarith
  set γ := x / (1 - x) with hγ
  have hγ0 : 0 < γ := div_pos hx h1x
  have hγ1 : γ ≠ 1 := by
    intro h
    rw [hγ, div_eq_one_iff_eq h1x.ne'] at h
    linarith
  have hRγ : (2 * t + 6) * γ ^ 2 + (2 - t) * γ - t = 0 := by
    rw [hγ]
    field_simp
    linear_combination hR
  have hm := isTopWeight_tetraPendant ht
  have hloc : ∀ z, WalkSecondEigenvalueLE (linkWeightOf (tetraPendantWeight t) {z}) x := by
    intro z
    by_cases hz : z ≤ 3
    · exact walkSecondEigenvalueLE_tetraPendant_core ht hx hR hz
    · exact (walkSecondEigenvalueLE_tetraPendant_pendant ht (by omega)).mono
        (linkWeightOf_nonneg hm.nonneg {z}) (by linarith)
  have heig : ∀ u, ∑ v, linkWeightOf (tetraPendantWeight t) ∅ u v * tetraPendantEigen γ v =
      x / (1 - x) * (∑ v, linkWeightOf (tetraPendantWeight t) ∅ u v) *
        tetraPendantEigen γ u :=
    tetraPendant_eigen hRγ
  have hlinks := (tricklingEquality_iff hm.nonneg hm.card_eq_of_ne_zero hloc hx1
    (tetraPendantEigen γ)).2.mp heig
  have hev := linkWeightOf_tetraPendant_empty_eval t
  have hdeg : ∀ z u, ∑ v, linkWeightOf (tetraPendantWeight t) {z} u v =
      linkWeightOf (tetraPendantWeight t) ∅ z u := fun z u => by
    rw [sum_linkWeightOf_singleton_right hm.card_eq_of_ne_zero, one_mul]
  refine ⟨hx2, fun z hz => ⟨hloc z, fun μ hμ => ?_⟩, fun z hz => ⟨?_, fun μ hμ => ?_⟩,
    ⟨?_, fun μ hμ => ?_⟩, hRγ⟩
  · -- the core links: the localisation of the eigenfunction is an `x`-eigenfunction
    by_contra hlt
    rw [not_le] at hlt
    refine not_walkSecondEigenvalueLE_of_eigen (linkWeightOf_symm _ {z}) (hlinks z) hx1 ?_ hlt hμ
    fin_cases z
    · refine norm_pos_of_term (linkWeightOf_nonneg hm.nonneg {0}) 1 ?_ ?_
      · rw [hdeg, hev.1]; norm_num
      · simp (config := {decide := true}) only [tetraPendantEigen, if_true, if_false]; nlinarith
    · refine norm_pos_of_term (linkWeightOf_nonneg hm.nonneg {1}) 0 ?_ ?_
      · rw [hdeg, hev.2.1]; norm_num
      · simp (config := {decide := true}) only [tetraPendantEigen, if_true, if_false]; nlinarith
    · refine norm_pos_of_term (linkWeightOf_nonneg hm.nonneg {2}) 0 ?_ ?_
      · rw [hdeg, hev.2.2.1]; norm_num
      · simp (config := {decide := true}) only [tetraPendantEigen, if_true, if_false]; nlinarith
    · refine norm_pos_of_term (linkWeightOf_nonneg hm.nonneg {3}) 1 ?_ ?_
      · rw [hdeg, hev.2.2.2.1]; norm_num
      · simp (config := {decide := true}) only [tetraPendantEigen, if_true, if_false]; nlinarith
    · exact absurd hz (by decide)
    · exact absurd hz (by decide)
  · exact walkSecondEigenvalueLE_tetraPendant_pendant ht hz
  · -- no link is below `−1`
    have hzK : {z} ∈ tetraPendant := by
      rw [mem_tetraPendant]
      fin_cases z <;> decide
    have := hm.neg_one_div_le_of_walkSecondEigenvalueLE_link (Or.inr hzK) (by simp) hμ
    norm_num at this
    exact this
  · exact hm.walkSecondEigenvalueLE_linkWeightOf_step (σ := ∅) (by simp)
      (by rw [link_empty]; exact isConnected_tetraPendant) (by linarith) fun z _ _ => by
        rw [insert_empty]; exact hloc z
  · by_contra hlt
    rw [not_le] at hlt
    refine not_walkSecondEigenvalueLE_of_eigen (linkWeightOf_symm _ ∅) heig hγ1 ?_ hlt hμ
    refine norm_pos_of_term (linkWeightOf_nonneg hm.nonneg ∅) 4 ?_
      (by simp (config := {decide := true}) [tetraPendantEigen])
    exact lt_of_lt_of_le (by rw [hev.2.2.2.2]; exact ht)
      (Finset.single_le_sum (fun v _ => linkWeightOf_nonneg hm.nonneg ∅ 4 v) (Finset.mem_univ 0))

/-- **The root `x(t)` exists and is unique.** For `t > 0` the equation
`2 (t + 2) x² + (t + 2) x − t = 0` has exactly one positive root,
`x(t) = (√((t + 2)(9t + 2)) − (t + 2)) / (4 (t + 2))`. -/
theorem tetraPendant_root_existsUnique {t : ℝ} (ht : 0 < t) :
    ∃! x : ℝ, 0 < x ∧ 2 * (t + 2) * x ^ 2 + (t + 2) * x - t = 0 := by
  have hD : 0 ≤ (t + 2) * (9 * t + 2) := by positivity
  set s := Real.sqrt ((t + 2) * (9 * t + 2)) with hsdef
  have hs : s ^ 2 = (t + 2) * (9 * t + 2) := Real.sq_sqrt hD
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hx0 : 0 < (s - (t + 2)) / (4 * (t + 2)) := by
    apply div_pos _ (by positivity)
    have h2 : (t + 2) ^ 2 < s ^ 2 := by rw [hs]; nlinarith
    nlinarith
  have hRx : 2 * (t + 2) * ((s - (t + 2)) / (4 * (t + 2))) ^ 2 +
      (t + 2) * ((s - (t + 2)) / (4 * (t + 2))) - t = 0 := by
    field_simp
    linear_combination 2 * hs
  refine ⟨(s - (t + 2)) / (4 * (t + 2)), ⟨hx0, hRx⟩, ?_⟩
  rintro y ⟨hy, hRy⟩
  have hfac : (y - (s - (t + 2)) / (4 * (t + 2))) *
      (2 * (t + 2) * (y + (s - (t + 2)) / (4 * (t + 2))) + (t + 2)) = 0 := by
    linear_combination hRy - hRx
  have hpos : 0 < 2 * (t + 2) * (y + (s - (t + 2)) / (4 * (t + 2))) + (t + 2) := by
    positivity
  linarith [(mul_eq_zero.mp hfac).resolve_right hpos.ne']

/-- **`x(t)` is strictly increasing.** If `0 < t < t'` and `x, x' > 0` are the positive roots for
`t` and `t'`, then `x < x'`. -/
theorem tetraPendant_root_strictMono {t t' x x' : ℝ} (ht : 0 < t) (htt : t < t') (hx : 0 < x)
    (hR : 2 * (t + 2) * x ^ 2 + (t + 2) * x - t = 0) (hx' : 0 < x')
    (hR' : 2 * (t' + 2) * x' ^ 2 + (t' + 2) * x' - t' = 0) : x < x' := by
  have hx2 : x < 1 / 2 := by
    by_contra h
    push Not at h
    have := mul_nonneg (sub_nonneg.mpr h)
      (show (0 : ℝ) ≤ 2 * (t + 2) * (x + 1 / 2) + (t + 2) by nlinarith)
    nlinarith
  -- at `t'` the old root is below the new one: `R(t', x) = (t' − t)(2x − 1)(x + 1) < 0`
  have hneg : 2 * (t' + 2) * x ^ 2 + (t' + 2) * x - t' < 0 := by
    have e : 2 * (t' + 2) * x ^ 2 + (t' + 2) * x - t' = (t' - t) * ((2 * x - 1) * (x + 1)) := by
      linear_combination hR
    rw [e]
    exact mul_neg_of_pos_of_neg (by linarith) (mul_neg_of_neg_of_pos (by linarith) (by linarith))
  by_contra h
  push Not at h
  have : 2 * (t' + 2) * x' ^ 2 + (t' + 2) * x' ≤ 2 * (t' + 2) * x ^ 2 + (t' + 2) * x := by
    have h1 : x' ^ 2 ≤ x ^ 2 := by nlinarith
    nlinarith
  linarith

/-- **`x(t)` takes every value in `(0, 1/2)`.** For `0 < x < 1/2`, the parameter
`t = 2x (1 + 2x) / ((1 − 2x)(1 + x))` is positive and has `x` as its root. Together with
`tetraPendant_root_strictMono` and the bound `x < 1/2` of `tetraPendant_sharp`, `x(t)` increases
from `0` to `1/2` as `t` runs over `(0, ∞)`. -/
theorem tetraPendant_root_of_mem_Ioo {x : ℝ} (h0 : 0 < x) (h1 : x < 1 / 2) :
    0 < 2 * x * (1 + 2 * x) / ((1 - 2 * x) * (1 + x)) ∧
      2 * (2 * x * (1 + 2 * x) / ((1 - 2 * x) * (1 + x)) + 2) * x ^ 2 +
        (2 * x * (1 + 2 * x) / ((1 - 2 * x) * (1 + x)) + 2) * x -
          2 * x * (1 + 2 * x) / ((1 - 2 * x) * (1 + x)) = 0 := by
  have ha : 0 < 1 - 2 * x := by linarith
  have hb : 0 < 1 + x := by linarith
  refine ⟨by positivity, ?_⟩
  field_simp
  ring

/-- **Trickling down is sharp in dimension `2` for every `lam ∈ (0, 1/2)`.** For each such `lam`
there is a top weight `m` on the connected pure `2`-dimensional complex `tetraPendant` (on six
points) whose vertex links all have second eigenvalue at most `lam` (exactly `lam` at four of
them), and whose weighted underlying graph has second eigenvalue exactly `lam / (1 − lam)`, the
bound of `trickling_down_weighted`. The complex is then a `lam / (1 − lam)`-local spectral
expander and no better one. The weight is `1` on the tetrahedron and
`t = 2 lam (1 + 2 lam) / ((1 − 2 lam)(1 + lam))` on the two pendant triangles.

Degenerate and excluded values: for `lam ≤ 0` sharpness comes from other examples, the complete
complexes (`complete_two_isLeast`, `trickling_down_complete`) for the values `−1/(N − 2)` and the
octahedron (`octahedron_sharp`) for `0`, and `IsTopWeight.isLeast_zero_iff_det_eq_zero`
characterises it at `lam = 0`. At `lam = 1/2` the bound `lam / (1 − lam) = 1` is never attained on
a connected complex (`IsTopWeight.not_isLeast_half`), and for `lam > 1/2` it exceeds `1` and is
trivial. -/
theorem exists_isLeast_trickling_down_two {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2) :
    ∃ m : Finset (Fin 6) → ℝ, tetraPendant.IsTopWeight 2 m ∧ tetraPendant.IsConnected ∧
      (∀ σ ∈ tetraPendant, #σ + 1 = 2 → WalkSecondEigenvalueLE (linkWeightOf m σ) lam) ∧
      IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf m ∅) μ} (lam / (1 - lam)) ∧
      IsLeast {μ | tetraPendant.IsLocalSpectralExpanderOf 2 m μ} (lam / (1 - lam)) := by
  obtain ⟨ht, hR⟩ := tetraPendant_root_of_mem_Ioo h0 h1
  set t := 2 * lam * (1 + 2 * lam) / ((1 - 2 * lam) * (1 + lam)) with htdef
  obtain ⟨-, hcore, hpend, hwhole, -⟩ := tetraPendant_sharp ht h0 hR
  have hm := isTopWeight_tetraPendant ht
  have hloc : ∀ z, WalkSecondEigenvalueLE (linkWeightOf (tetraPendantWeight t) {z}) lam := by
    intro z
    by_cases hz : z ≤ 3
    · exact (hcore z hz).1
    · exact (hpend z (by omega)).1.mono (linkWeightOf_nonneg hm.nonneg {z}) (by linarith)
  have hle : lam ≤ lam / (1 - lam) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  refine ⟨tetraPendantWeight t, hm, isConnected_tetraPendant, fun σ _ hσ => ?_, hwhole,
    ⟨⟨le_of_lt (by norm_num), hm, fun σ hσ hc => ?_⟩, fun μ hμ => hwhole.2 (hμ.2.2 ∅ (Or.inl rfl)
      (by simp))⟩⟩
  · obtain ⟨z, rfl⟩ := card_eq_one.mp (by omega : #σ = 1)
    exact hloc z
  · rcases Nat.lt_or_ge #σ 1 with h | h
    · rw [card_eq_zero.mp (by omega : #σ = 0)]
      exact hwhole.1
    · obtain ⟨z, rfl⟩ := card_eq_one.mp (by omega : #σ = 1)
      exact (hloc z).mono (linkWeightOf_nonneg hm.nonneg {z}) hle


/-! ### Two uniform pendants on each of two opposite edges -/

/-- The complex `P₂` on `Fin 8`: the boundary of the tetrahedron `{0, 1, 2, 3}` with two pendant
triangles `{0, 3, 4}`, `{0, 3, 5}` on the edge `0 3` and two, `{1, 2, 6}`, `{1, 2, 7}`, on the
opposite edge `1 2`. (One pendant on each edge, with uniform weights, is `tetraPendant` with
`t = 1`.) -/
def pendantTwo : PreAbstractSimplicialComplex (Fin 8) where
  faces := {s | s.Nonempty ∧ (s ⊆ {0, 1, 2} ∨ s ⊆ {0, 1, 3} ∨ s ⊆ {0, 2, 3} ∨ s ⊆ {1, 2, 3} ∨
    s ⊆ {0, 3, 4} ∨ s ⊆ {0, 3, 5} ∨ s ⊆ {1, 2, 6} ∨ s ⊆ {1, 2, 7})}
  isRelLowerSet_faces := by
    rintro s ⟨hne, hs⟩
    refine ⟨hne, fun t hts ht => ⟨ht, ?_⟩⟩
    rcases hs with h | h | h | h | h | h | h | h
    · exact Or.inl (hts.trans h)
    · exact Or.inr (Or.inl (hts.trans h))
    · exact Or.inr (Or.inr (Or.inl (hts.trans h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hts.trans h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hts.trans h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hts.trans h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hts.trans h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hts.trans h)))))))

/-- The faces of `pendantTwo`, by definition. -/
theorem mem_pendantTwo {s : Finset (Fin 8)} :
    s ∈ pendantTwo ↔ s.Nonempty ∧ (s ⊆ {0, 1, 2} ∨ s ⊆ {0, 1, 3} ∨ s ⊆ {0, 2, 3} ∨
      s ⊆ {1, 2, 3} ∨ s ⊆ {0, 3, 4} ∨ s ⊆ {0, 3, 5} ∨ s ⊆ {1, 2, 6} ∨ s ⊆ {1, 2, 7}) := Iff.rfl

/-- Weight `1` on each of the eight triangles of `pendantTwo`, as a sum of point masses. -/
noncomputable def pendantTwoWeight (F : Finset (Fin 8)) : ℝ :=
  (if F = {0, 1, 2} then 1 else 0) + (if F = {0, 1, 3} then 1 else 0) +
    (if F = {0, 2, 3} then 1 else 0) + (if F = {1, 2, 3} then 1 else 0) +
    (if F = {0, 3, 4} then 1 else 0) + (if F = {0, 3, 5} then 1 else 0) +
    (if F = {1, 2, 6} then 1 else 0) + (if F = {1, 2, 7} then 1 else 0)

private theorem eq_of_subset_three' {s T : Finset (Fin 8)} (hT : #T = 3) (hs : #s = 2 + 1)
    (h : s ⊆ T) : s = T :=
  Finset.eq_of_subset_of_card_le h (by rw [hT, hs])

/-- `pendantTwoWeight` is a top weight of the pure `2`-dimensional complex `pendantTwo`. -/
theorem isTopWeight_pendantTwo : pendantTwo.IsTopWeight 2 pendantTwoWeight where
  isPure := by
    intro σ hσ
    rcases (mem_pendantTwo.mp hσ).2 with h | h | h | h | h | h | h | h
    all_goals
      refine ⟨(card_le_card h).trans (by decide), _, mem_pendantTwo.mpr ⟨by decide, ?_⟩, h,
        by decide⟩
      simp
  exists_mem := ⟨{0, 1, 2}, mem_pendantTwo.mpr ⟨by decide, by simp⟩⟩
  pos := by
    intro F hF hFc
    rcases (mem_pendantTwo.mp hF).2 with h | h | h | h | h | h | h | h <;>
      · rw [eq_of_subset_three' (by decide) hFc h]
        unfold pendantTwoWeight
        simp (config := {decide := true})
  eq_zero := by
    intro F hF
    unfold pendantTwoWeight
    have hne : ∀ T : Finset (Fin 8), T ∈ pendantTwo → #T = 2 + 1 → F ≠ T := by
      rintro T hT hTc rfl
      exact hF ⟨hT, hTc⟩
    rw [if_neg (hne _ (mem_pendantTwo.mpr ⟨by decide, by simp⟩) (by decide)),
      if_neg (hne _ (mem_pendantTwo.mpr ⟨by decide, by simp⟩) (by decide)),
      if_neg (hne _ (mem_pendantTwo.mpr ⟨by decide, by simp⟩) (by decide)),
      if_neg (hne _ (mem_pendantTwo.mpr ⟨by decide, by simp⟩) (by decide)),
      if_neg (hne _ (mem_pendantTwo.mpr ⟨by decide, by simp⟩) (by decide)),
      if_neg (hne _ (mem_pendantTwo.mpr ⟨by decide, by simp⟩) (by decide)),
      if_neg (hne _ (mem_pendantTwo.mpr ⟨by decide, by simp⟩) (by decide)),
      if_neg (hne _ (mem_pendantTwo.mpr ⟨by decide, by simp⟩) (by decide))]
    norm_num

/-- `pendantTwo` is connected. -/
theorem isConnected_pendantTwo : pendantTwo.IsConnected := by
  rw [IsConnected, SimpleGraph.connected_iff]
  have hv : ∀ v : Fin 8, v ∈ pendantTwo.vertices := by
    intro v
    show {v} ∈ pendantTwo
    rw [mem_pendantTwo]
    fin_cases v <;> decide
  have hadj : ∀ a b : Fin 8, a ≠ b → ({a, b} : Finset (Fin 8)) ∈ pendantTwo →
      (pendantTwo.oneSkeleton.induce pendantTwo.vertices).Adj ⟨a, hv a⟩ ⟨b, hv b⟩ := by
    intro a b hab h
    rw [SimpleGraph.induce_adj, oneSkeleton, SimpleGraph.fromRel_adj]
    exact ⟨hab, Or.inl h⟩
  have hr : ∀ a : pendantTwo.vertices,
      (pendantTwo.oneSkeleton.induce pendantTwo.vertices).Reachable a ⟨1, hv 1⟩ := by
    rintro ⟨a, ha⟩
    fin_cases a
    · exact (hadj 0 1 (by decide) (by rw [mem_pendantTwo]; decide)).reachable
    · rfl
    · exact (hadj 2 1 (by decide) (by rw [mem_pendantTwo]; decide)).reachable
    · exact (hadj 3 1 (by decide) (by rw [mem_pendantTwo]; decide)).reachable
    · exact (hadj 4 0 (by decide) (by rw [mem_pendantTwo]; decide)).reachable.trans
        (hadj 0 1 (by decide) (by rw [mem_pendantTwo]; decide)).reachable
    · exact (hadj 5 0 (by decide) (by rw [mem_pendantTwo]; decide)).reachable.trans
        (hadj 0 1 (by decide) (by rw [mem_pendantTwo]; decide)).reachable
    · exact (hadj 6 1 (by decide) (by rw [mem_pendantTwo]; decide)).reachable
    · exact (hadj 7 1 (by decide) (by rw [mem_pendantTwo]; decide)).reachable
  exact ⟨fun a b => (hr a).trans (hr b).symm, ⟨⟨1, hv 1⟩⟩⟩

/-- The link weights of `pendantTwo`, evaluated through its eight triangles. -/
private theorem linkWeightOf_pendantTwo (σ : Finset (Fin 8)) (u v : Fin 8) :
    linkWeightOf pendantTwoWeight σ u v =
      if u ≠ v ∧ u ∉ σ ∧ v ∉ σ then
        (if insert u (insert v σ) ⊆ {0, 1, 2} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {0, 1, 3} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {0, 2, 3} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {1, 2, 3} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {0, 3, 4} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {0, 3, 5} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {1, 2, 6} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {1, 2, 7} then 1 else 0)
      else 0 := by
  unfold linkWeightOf faceWeight pendantTwoWeight
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- The vertex-link bounds of `pendantTwo` at the tetrahedron: a triangle with two pendant edges
at one corner, of second eigenvalue at most `x` (`pendant_ineq` with `t = 2` applied to the mean
of the two pendant values, plus Cauchy–Schwarz). -/
private theorem walkSecondEigenvalueLE_pendantTwo_core {x : ℝ} (hx : 0 < x)
    (hR : 2 * (2 + 2) * x ^ 2 + (2 + 2) * x - 2 = 0) {z : Fin 8} (hz : z ≤ 3) :
    WalkSecondEigenvalueLE (linkWeightOf pendantTwoWeight {z}) x := by
  intro f hf
  fin_cases z
  all_goals try exact absurd hz (by decide)
  all_goals simp only [Fin.sum_univ_eight, linkWeightOf_pendantTwo] at hf ⊢
  all_goals simp (config := {decide := true}) only [if_true, if_false] at hf ⊢
  all_goals norm_num at hf ⊢
  · linarith [pendant_ineq two_pos hx hR (a := f 1) (b := f 2) (c := f 3) (e := (f 4 + f 5) / 2)
      (by linarith), mul_nonneg hx.le (sq_nonneg (f 4 - f 5))]
  · linarith [pendant_ineq two_pos hx hR (a := f 0) (b := f 3) (c := f 2) (e := (f 6 + f 7) / 2)
      (by linarith), mul_nonneg hx.le (sq_nonneg (f 6 - f 7))]
  · linarith [pendant_ineq two_pos hx hR (a := f 0) (b := f 3) (c := f 1) (e := (f 6 + f 7) / 2)
      (by linarith), mul_nonneg hx.le (sq_nonneg (f 6 - f 7))]
  · linarith [pendant_ineq two_pos hx hR (a := f 1) (b := f 2) (c := f 0) (e := (f 4 + f 5) / 2)
      (by linarith), mul_nonneg hx.le (sq_nonneg (f 4 - f 5))]

/-- The vertex links of the pendant points of `pendantTwo` are single edges, of second eigenvalue
`−1`. -/
private theorem walkSecondEigenvalueLE_pendantTwo_pendant {z : Fin 8} (hz : 4 ≤ z) :
    WalkSecondEigenvalueLE (linkWeightOf pendantTwoWeight {z}) (-1) := by
  intro f hf
  fin_cases z
  all_goals try exact absurd hz (by decide)
  all_goals simp only [Fin.sum_univ_eight, linkWeightOf_pendantTwo] at hf ⊢
  all_goals simp (config := {decide := true}) only [if_true, if_false] at hf ⊢
  all_goals norm_num at hf ⊢
  · have h3 : f 3 = -f 0 := by linarith
    rw [h3]; nlinarith
  · have h3 : f 3 = -f 0 := by linarith
    rw [h3]; nlinarith
  · have h2 : f 2 = -f 1 := by linarith
    rw [h2]; nlinarith
  · have h2 : f 2 = -f 1 := by linarith
    rw [h2]; nlinarith

/-- The `γ`-eigenfunction of `pendantTwo`: `γ, −γ, −γ, γ` on the tetrahedron, `1` at the pendants
`4, 5` and `−1` at `6, 7`. -/
def pendantTwoEigen (γ : ℝ) (v : Fin 8) : ℝ :=
  if v = 0 ∨ v = 3 then γ else if v = 1 ∨ v = 2 then -γ else if v = 4 ∨ v = 5 then 1 else -1

/-- **Two uniform pendants per edge: equality with `lam = (√5 − 1)/4`.** In `pendantTwo`, with
every triangle of weight `1`, let `x > 0` be the root of `8x² + 4x − 2` (that is,
`x = (√5 − 1)/4`, the `t = 2` case of `tetraPendant_sharp`). The links of `0, 1, 2, 3` (a triangle
with two pendant edges at one corner) have second eigenvalue exactly `x`, those of the four pendant
points (a single edge) exactly `−1`, and the underlying graph exactly `x / (1 − x)` (`= 1/√5`), the
trickling-down value. This is the case `k = 2` of the uniform pendant family of the conjecture;
`k = 1` is `tetraPendant_sharp` at `t = 1`. The general `k` is not formalised here. -/
theorem pendantTwo_sharp {x : ℝ} (hx : 0 < x) (hR : 2 * (2 + 2) * x ^ 2 + (2 + 2) * x - 2 = 0) :
    (∀ z : Fin 8, z ≤ 3 →
      IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf pendantTwoWeight {z}) μ} x) ∧
    (∀ z : Fin 8, 4 ≤ z →
      IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf pendantTwoWeight {z}) μ} (-1)) ∧
    IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf pendantTwoWeight ∅) μ} (x / (1 - x)) := by
  have hx2 : x < 1 / 2 := by nlinarith
  have hx1 : x ≠ 1 := by intro h; rw [h] at hx2; norm_num at hx2
  have h1x : 0 < 1 - x := by linarith
  set γ := x / (1 - x) with hγ
  have hγ0 : 0 < γ := div_pos hx h1x
  have hγ1 : γ ≠ 1 := by
    intro h
    rw [hγ, div_eq_one_iff_eq h1x.ne'] at h
    linarith
  have hRγ : (2 * 2 + 6) * γ ^ 2 + (2 - 2) * γ - 2 = 0 := by
    rw [hγ]
    field_simp
    linear_combination hR
  have hm := isTopWeight_pendantTwo
  have hloc : ∀ z, WalkSecondEigenvalueLE (linkWeightOf pendantTwoWeight {z}) x := by
    intro z
    by_cases hz : z ≤ 3
    · exact walkSecondEigenvalueLE_pendantTwo_core hx hR hz
    · exact (walkSecondEigenvalueLE_pendantTwo_pendant (by omega)).mono
        (linkWeightOf_nonneg hm.nonneg {z}) (by linarith)
  have heig : ∀ u, ∑ v, linkWeightOf pendantTwoWeight ∅ u v * pendantTwoEigen γ v =
      x / (1 - x) * (∑ v, linkWeightOf pendantTwoWeight ∅ u v) * pendantTwoEigen γ u := by
    intro u
    simp only [Fin.sum_univ_eight, linkWeightOf_pendantTwo, pendantTwoEigen]
    fin_cases u
    all_goals simp (config := {decide := true}) only [if_true, if_false]
    all_goals norm_num
    all_goals first
      | linear_combination hRγ
      | linear_combination (-1 : ℝ) * hRγ
      | ring
  have hlinks := (tricklingEquality_iff hm.nonneg hm.card_eq_of_ne_zero hloc hx1
    (pendantTwoEigen γ)).2.mp heig
  have hdeg : ∀ z u, ∑ v, linkWeightOf pendantTwoWeight {z} u v =
      linkWeightOf pendantTwoWeight ∅ z u := fun z u => by
    rw [sum_linkWeightOf_singleton_right hm.card_eq_of_ne_zero, one_mul]
  have hw : ∀ a b : Fin 8, ({a, b} : Finset (Fin 8)) = {0, 1} ∨ ({a, b} : Finset (Fin 8)) = {0, 2} ∨
      ({a, b} : Finset (Fin 8)) = {1, 3} ∨ ({a, b} : Finset (Fin 8)) = {2, 3} → a ≠ b →
      0 < linkWeightOf pendantTwoWeight ∅ a b := by
    intro a b hab hne
    refine hm.linkWeightOf_pos_iff.mpr ⟨hne, Finset.notMem_empty a, Finset.notMem_empty b, ?_⟩
    rw [Finset.insert_empty]
    rcases hab with h | h | h | h <;> rw [h]
    · exact ⟨{0, 1, 2}, mem_pendantTwo.mpr ⟨by decide, by simp⟩, by decide, by decide⟩
    · exact ⟨{0, 1, 2}, mem_pendantTwo.mpr ⟨by decide, by simp⟩, by decide, by decide⟩
    · exact ⟨{1, 2, 3}, mem_pendantTwo.mpr ⟨by decide, by simp⟩, by decide, by decide⟩
    · exact ⟨{1, 2, 3}, mem_pendantTwo.mpr ⟨by decide, by simp⟩, by decide, by decide⟩
  refine ⟨fun z hz => ⟨hloc z, fun μ hμ => ?_⟩, fun z hz => ⟨?_, fun μ hμ => ?_⟩,
    ⟨?_, fun μ hμ => ?_⟩⟩
  · by_contra hlt
    rw [not_le] at hlt
    refine not_walkSecondEigenvalueLE_of_eigen (linkWeightOf_symm _ {z}) (hlinks z) hx1 ?_ hlt hμ
    fin_cases z
    · refine norm_pos_of_term (linkWeightOf_nonneg hm.nonneg {0}) 1 ?_ ?_
      · rw [hdeg]; exact hw 0 1 (Or.inl rfl) (by decide)
      · simp (config := {decide := true}) only [pendantTwoEigen, if_true, if_false]; nlinarith
    · refine norm_pos_of_term (linkWeightOf_nonneg hm.nonneg {1}) 0 ?_ ?_
      · rw [hdeg, linkWeightOf_symm]; exact hw 0 1 (Or.inl rfl) (by decide)
      · simp (config := {decide := true}) only [pendantTwoEigen, if_true, if_false]; nlinarith
    · refine norm_pos_of_term (linkWeightOf_nonneg hm.nonneg {2}) 0 ?_ ?_
      · rw [hdeg, linkWeightOf_symm]; exact hw 0 2 (Or.inr (Or.inl rfl)) (by decide)
      · simp (config := {decide := true}) only [pendantTwoEigen, if_true, if_false]; nlinarith
    · refine norm_pos_of_term (linkWeightOf_nonneg hm.nonneg {3}) 1 ?_ ?_
      · rw [hdeg, linkWeightOf_symm]; exact hw 1 3 (Or.inr (Or.inr (Or.inl rfl))) (by decide)
      · simp (config := {decide := true}) only [pendantTwoEigen, if_true, if_false]; nlinarith
    all_goals exact absurd hz (by decide)
  · exact walkSecondEigenvalueLE_pendantTwo_pendant hz
  · have hzK : {z} ∈ pendantTwo := by
      rw [mem_pendantTwo]
      fin_cases z <;> decide
    have := hm.neg_one_div_le_of_walkSecondEigenvalueLE_link (Or.inr hzK) (by simp) hμ
    norm_num at this
    exact this
  · exact hm.walkSecondEigenvalueLE_linkWeightOf_step (σ := ∅) (by simp)
      (by rw [link_empty]; exact isConnected_pendantTwo) (by linarith) fun z _ _ => by
        rw [insert_empty]; exact hloc z
  · by_contra hlt
    rw [not_le] at hlt
    refine not_walkSecondEigenvalueLE_of_eigen (linkWeightOf_symm _ ∅) heig hγ1 ?_ hlt hμ
    refine norm_pos_of_term (linkWeightOf_nonneg hm.nonneg ∅) 0 ?_ ?_
    · exact lt_of_lt_of_le (hw 0 1 (Or.inl rfl) (by decide))
        (Finset.single_le_sum (fun v _ => linkWeightOf_nonneg hm.nonneg ∅ 0 v)
          (Finset.mem_univ 1))
    · simp (config := {decide := true}) only [pendantTwoEigen, if_true, if_false]
      exact hγ0.ne'

/-- The root in `pendantTwo_sharp` is `x = (√5 − 1)/4`, and then `x / (1 − x) = 1/√5`. -/
theorem pendantTwo_root :
    0 < (Real.sqrt 5 - 1) / 4 ∧
      2 * (2 + 2) * ((Real.sqrt 5 - 1) / 4) ^ 2 + (2 + 2) * ((Real.sqrt 5 - 1) / 4) - 2 = 0 ∧
      (Real.sqrt 5 - 1) / 4 / (1 - (Real.sqrt 5 - 1) / 4) = 1 / Real.sqrt 5 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h1 : 1 < Real.sqrt 5 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h3 : Real.sqrt 5 < 3 := by nlinarith
  refine ⟨by linarith, by nlinarith, ?_⟩
  have hne : (1 - (Real.sqrt 5 - 1) / 4) ≠ 0 := by linarith
  have hs : Real.sqrt 5 ≠ 0 := by linarith
  rw [div_eq_div_iff hne hs]
  linear_combination (1 / 4 : ℝ) * h5

/-- With `t = 1`, `tetraPendantWeight` is the uniform weight: `tetraPendant_sharp` at `t = 1` is the
case `k = 1` of the uniform pendant family. -/
theorem tetraPendantWeight_one_eq_uniformWeight :
    tetraPendantWeight 1 = tetraPendant.uniformWeight 2 := by
  funext F
  unfold uniformWeight
  split_ifs with h
  · obtain ⟨hF, hFc⟩ := h
    rcases (mem_tetraPendant.mp hF).2 with h | h | h | h | h | h <;>
      · rw [eq_of_subset_three (by decide) hFc h]
        unfold tetraPendantWeight
        simp (config := {decide := true})
  · exact (isTopWeight_tetraPendant one_pos).eq_zero F h

/-- `pendantTwoWeight` is the uniform weight of `pendantTwo`. -/
theorem pendantTwoWeight_eq_uniformWeight : pendantTwoWeight = pendantTwo.uniformWeight 2 := by
  funext F
  unfold uniformWeight
  split_ifs with h
  · obtain ⟨hF, hFc⟩ := h
    rcases (mem_pendantTwo.mp hF).2 with h | h | h | h | h | h | h | h <;>
      · rw [eq_of_subset_three' (by decide) hFc h]
        unfold pendantTwoWeight
        simp (config := {decide := true})
  · exact isTopWeight_pendantTwo.eq_zero F h

/-- **An unweighted complex on which trickling down is exact with `lam > 0`.** `pendantTwo`
(counting top faces, as in `IsLocalSpectralExpander`) is a `μ`-local spectral expander exactly
when `μ ≥ 1/√5`. Its vertex links have second eigenvalue at most `lam = (√5 − 1)/4`, and
`1/√5 = lam / (1 − lam)` is the bound of `trickling_down`. The binding link is the complex
itself; the vertex links are below `1/√5`. -/
theorem pendantTwo_isLocalSpectralExpander_iff (μ : ℝ) :
    pendantTwo.IsLocalSpectralExpander 2 μ ↔ 1 / Real.sqrt 5 ≤ μ := by
  obtain ⟨hx, hR, he⟩ := pendantTwo_root
  obtain ⟨hcore, hpend, hwhole⟩ := pendantTwo_sharp hx hR
  rw [he] at hwhole
  have hm := isTopWeight_pendantTwo
  rw [isLocalSpectralExpander_iff_isLocalSpectralExpanderOf, ← pendantTwoWeight_eq_uniformWeight]
  have hx2 : (Real.sqrt 5 - 1) / 4 ≤ 1 / Real.sqrt 5 := by
    rw [← he, le_div_iff₀ (by nlinarith)]
    nlinarith
  constructor
  · intro h
    exact hwhole.2 (h.2.2 ∅ (Or.inl rfl) (by simp))
  · intro hle
    refine ⟨by norm_num, hm, fun σ hσ hc => ?_⟩
    rcases Nat.lt_or_ge #σ 1 with h | h
    · rw [card_eq_zero.mp (by omega : #σ = 0)]
      exact hwhole.1.mono (linkWeightOf_nonneg hm.nonneg ∅) hle
    · obtain ⟨z, rfl⟩ := card_eq_one.mp (by omega : #σ = 1)
      by_cases hz : z ≤ 3
      · exact (hcore z hz).1.mono (linkWeightOf_nonneg hm.nonneg {z}) (hx2.trans hle)
      · exact (hpend z (by omega)).1.mono (linkWeightOf_nonneg hm.nonneg {z})
          (by linarith [hx2, hle])

end Sharp

/-! ### The octahedron: equality at `lam = 0` -/

section Octahedron

/-- The boundary of the octahedron (the `3`-dimensional cross-polytope) on `Fin 6`, with antipodal
pairs `{0, 1}`, `{2, 3}`, `{4, 5}`: its faces are the nonempty subsets of the eight triangles that
contain one point of each pair. -/
def octahedron : PreAbstractSimplicialComplex (Fin 6) where
  faces := {s | s.Nonempty ∧ (s ⊆ {0, 2, 4} ∨ s ⊆ {0, 2, 5} ∨ s ⊆ {0, 3, 4} ∨ s ⊆ {0, 3, 5} ∨
    s ⊆ {1, 2, 4} ∨ s ⊆ {1, 2, 5} ∨ s ⊆ {1, 3, 4} ∨ s ⊆ {1, 3, 5})}
  isRelLowerSet_faces := by
    rintro s ⟨hne, hs⟩
    refine ⟨hne, fun t hts ht => ⟨ht, ?_⟩⟩
    rcases hs with h | h | h | h | h | h | h | h
    · exact Or.inl (hts.trans h)
    · exact Or.inr (Or.inl (hts.trans h))
    · exact Or.inr (Or.inr (Or.inl (hts.trans h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hts.trans h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hts.trans h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hts.trans h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hts.trans h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hts.trans h)))))))

/-- The faces of `octahedron`, by definition. -/
theorem mem_octahedron {s : Finset (Fin 6)} :
    s ∈ octahedron ↔ s.Nonempty ∧ (s ⊆ {0, 2, 4} ∨ s ⊆ {0, 2, 5} ∨ s ⊆ {0, 3, 4} ∨
      s ⊆ {0, 3, 5} ∨ s ⊆ {1, 2, 4} ∨ s ⊆ {1, 2, 5} ∨ s ⊆ {1, 3, 4} ∨ s ⊆ {1, 3, 5}) := Iff.rfl

/-- Weight `1` on each of the eight triangles of the octahedron (the uniform weight), as a sum of
point masses. -/
noncomputable def octahedronWeight (F : Finset (Fin 6)) : ℝ :=
  (if F = {0, 2, 4} then 1 else 0) + (if F = {0, 2, 5} then 1 else 0) +
    (if F = {0, 3, 4} then 1 else 0) + (if F = {0, 3, 5} then 1 else 0) +
    (if F = {1, 2, 4} then 1 else 0) + (if F = {1, 2, 5} then 1 else 0) +
    (if F = {1, 3, 4} then 1 else 0) + (if F = {1, 3, 5} then 1 else 0)

/-- `octahedronWeight` is a top weight of the pure `2`-dimensional complex `octahedron`. -/
theorem isTopWeight_octahedron : octahedron.IsTopWeight 2 octahedronWeight where
  isPure := by
    intro σ hσ
    rcases (mem_octahedron.mp hσ).2 with h | h | h | h | h | h | h | h
    all_goals
      refine ⟨(card_le_card h).trans (by decide), _, mem_octahedron.mpr ⟨by decide, ?_⟩, h,
        by decide⟩
      simp
  exists_mem := ⟨{0, 2, 4}, mem_octahedron.mpr ⟨by decide, by simp⟩⟩
  pos := by
    intro F hF hFc
    rcases (mem_octahedron.mp hF).2 with h | h | h | h | h | h | h | h <;>
      · rw [eq_of_subset_three (by decide) hFc h]
        unfold octahedronWeight
        simp (config := {decide := true})
  eq_zero := by
    intro F hF
    unfold octahedronWeight
    have hne : ∀ T : Finset (Fin 6), T ∈ octahedron → #T = 2 + 1 → F ≠ T := by
      rintro T hT hTc rfl
      exact hF ⟨hT, hTc⟩
    rw [if_neg (hne _ (mem_octahedron.mpr ⟨by decide, by simp⟩) (by decide)),
      if_neg (hne _ (mem_octahedron.mpr ⟨by decide, by simp⟩) (by decide)),
      if_neg (hne _ (mem_octahedron.mpr ⟨by decide, by simp⟩) (by decide)),
      if_neg (hne _ (mem_octahedron.mpr ⟨by decide, by simp⟩) (by decide)),
      if_neg (hne _ (mem_octahedron.mpr ⟨by decide, by simp⟩) (by decide)),
      if_neg (hne _ (mem_octahedron.mpr ⟨by decide, by simp⟩) (by decide)),
      if_neg (hne _ (mem_octahedron.mpr ⟨by decide, by simp⟩) (by decide)),
      if_neg (hne _ (mem_octahedron.mpr ⟨by decide, by simp⟩) (by decide))]
    norm_num

/-- The octahedron is connected. -/
theorem isConnected_octahedron : octahedron.IsConnected := by
  rw [IsConnected, SimpleGraph.connected_iff]
  have hv : ∀ v : Fin 6, v ∈ octahedron.vertices := by
    intro v
    show {v} ∈ octahedron
    rw [mem_octahedron]
    fin_cases v <;> decide
  have hadj : ∀ a b : Fin 6, a ≠ b → ({a, b} : Finset (Fin 6)) ∈ octahedron →
      (octahedron.oneSkeleton.induce octahedron.vertices).Adj ⟨a, hv a⟩ ⟨b, hv b⟩ := by
    intro a b hab h
    rw [SimpleGraph.induce_adj, oneSkeleton, SimpleGraph.fromRel_adj]
    exact ⟨hab, Or.inl h⟩
  have hr : ∀ a : octahedron.vertices,
      (octahedron.oneSkeleton.induce octahedron.vertices).Reachable a ⟨2, hv 2⟩ := by
    rintro ⟨a, ha⟩
    fin_cases a
    · exact (hadj 0 2 (by decide) (by rw [mem_octahedron]; decide)).reachable
    · exact (hadj 1 2 (by decide) (by rw [mem_octahedron]; decide)).reachable
    · rfl
    · exact (hadj 3 0 (by decide) (by rw [mem_octahedron]; decide)).reachable.trans
        (hadj 0 2 (by decide) (by rw [mem_octahedron]; decide)).reachable
    · exact (hadj 4 2 (by decide) (by rw [mem_octahedron]; decide)).reachable
    · exact (hadj 5 2 (by decide) (by rw [mem_octahedron]; decide)).reachable
  exact ⟨fun a b => (hr a).trans (hr b).symm, ⟨⟨2, hv 2⟩⟩⟩

/-- The link weights of the octahedron, evaluated through its eight triangles. -/
private theorem linkWeightOf_octahedron (σ : Finset (Fin 6)) (u v : Fin 6) :
    linkWeightOf octahedronWeight σ u v =
      if u ≠ v ∧ u ∉ σ ∧ v ∉ σ then
        (if insert u (insert v σ) ⊆ {0, 2, 4} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {0, 2, 5} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {0, 3, 4} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {0, 3, 5} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {1, 2, 4} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {1, 2, 5} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {1, 3, 4} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {1, 3, 5} then 1 else 0)
      else 0 := by
  unfold linkWeightOf faceWeight octahedronWeight
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- No vertex link of the octahedron has a negative bound: the test function `1, −1` on an
antipodal pair of the link has mean zero and quadratic form `0`. -/
private theorem octahedron_link_nonneg (z : Fin 6) {μ : ℝ}
    (h : WalkSecondEigenvalueLE (linkWeightOf octahedronWeight {z}) μ) : 0 ≤ μ := by
  by_cases hz : z ≤ 1
  · have h1 := h (fun v => if v = 2 then 1 else if v = 3 then -1 else 0) (by
      simp only [Fin.sum_univ_six, linkWeightOf_octahedron]
      fin_cases z <;> simp (config := {decide := true}) at hz ⊢)
    simp only [Fin.sum_univ_six, linkWeightOf_octahedron] at h1
    fin_cases z
    all_goals simp (config := {decide := true}) at hz h1 ⊢
    all_goals linarith
  · have h1 := h (fun v => if v = 0 then 1 else if v = 1 then -1 else 0) (by
      simp only [Fin.sum_univ_six, linkWeightOf_octahedron]
      fin_cases z <;> simp (config := {decide := true}) at hz ⊢)
    simp only [Fin.sum_univ_six, linkWeightOf_octahedron] at h1
    fin_cases z
    all_goals simp (config := {decide := true}) at hz h1 ⊢
    all_goals linarith

/-- **The octahedron attains equality at `lam = 0`.** With weight `1` on every triangle, every
vertex link (a `4`-cycle) has second eigenvalue exactly `0`, and so does the underlying graph
`K_{2,2,2}`: `0 = 0 / (1 − 0)`, the trickling-down value. The eigenfunction is `1` and `−1` at the
antipodal pair `0, 1` and `0` elsewhere (a coordinate function); it lies in the kernel of the
weight matrix, which is therefore singular, as `IsTopWeight.isLeast_zero_iff_det_eq_zero`
requires. This is the `3`-dimensional cross-polytope case of part (v) of the conjecture; the
higher cross-polytopes, the icosahedron and the 600-cell are not formalised here. -/
theorem octahedron_sharp :
    (∀ z : Fin 6, IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf octahedronWeight {z}) μ} 0) ∧
    IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf octahedronWeight ∅) μ} (0 / (1 - 0)) := by
  have hm := isTopWeight_octahedron
  have hloc : ∀ z : Fin 6, WalkSecondEigenvalueLE (linkWeightOf octahedronWeight {z}) 0 := by
    intro z f hf
    simp only [Fin.sum_univ_six, linkWeightOf_octahedron] at hf ⊢
    fin_cases z
    all_goals simp (config := {decide := true}) only [if_true, if_false] at hf ⊢
    all_goals norm_num at hf ⊢
    · have h5 : f 5 = -(f 2 + f 3) - f 4 := by linarith
      rw [h5]; nlinarith [sq_nonneg (f 2 + f 3)]
    · have h5 : f 5 = -(f 2 + f 3) - f 4 := by linarith
      rw [h5]; nlinarith [sq_nonneg (f 2 + f 3)]
    · have h5 : f 5 = -(f 0 + f 1) - f 4 := by linarith
      rw [h5]; nlinarith [sq_nonneg (f 0 + f 1)]
    · have h5 : f 5 = -(f 0 + f 1) - f 4 := by linarith
      rw [h5]; nlinarith [sq_nonneg (f 0 + f 1)]
    · have h3 : f 3 = -(f 0 + f 1) - f 2 := by linarith
      rw [h3]; nlinarith [sq_nonneg (f 0 + f 1)]
    · have h3 : f 3 = -(f 0 + f 1) - f 2 := by linarith
      rw [h3]; nlinarith [sq_nonneg (f 0 + f 1)]
  -- the coordinate function `1_0 − 1_1`
  set F : Fin 6 → ℝ := fun v => if v = 0 then 1 else if v = 1 then -1 else 0 with hF
  have heig : ∀ u, ∑ v, linkWeightOf octahedronWeight ∅ u v * F v =
      0 / (1 - 0) * (∑ v, linkWeightOf octahedronWeight ∅ u v) * F u := by
    intro u
    simp only [Fin.sum_univ_six, linkWeightOf_octahedron, hF]
    fin_cases u
    all_goals simp (config := {decide := true}) only [if_true, if_false]
    all_goals norm_num
  refine ⟨fun z => ⟨hloc z, fun μ hμ => ?_⟩, ⟨?_, fun μ hμ => ?_⟩⟩
  · exact octahedron_link_nonneg z hμ
  · exact hm.walkSecondEigenvalueLE_linkWeightOf_step (σ := ∅) (by simp)
      (by rw [link_empty]; exact isConnected_octahedron) (by norm_num) fun z _ _ => by
        rw [insert_empty]; exact hloc z
  · by_contra hlt
    rw [not_le] at hlt
    refine not_walkSecondEigenvalueLE_of_eigen (linkWeightOf_symm _ ∅) heig (by norm_num) ?_ hlt
      hμ
    refine norm_pos_of_term (linkWeightOf_nonneg hm.nonneg ∅) 0 ?_ (by simp [hF])
    simp only [Fin.sum_univ_six, linkWeightOf_octahedron]
    simp (config := {decide := true}) only [if_true, if_false]
    norm_num

end Octahedron

end PreAbstractSimplicialComplex
