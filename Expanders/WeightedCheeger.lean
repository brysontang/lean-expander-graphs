/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.WalkSpectrum
import Expanders.WeightedComplex

/-!
# Cheeger's inequality for weighted graphs

`Expanders/Cheeger.lean` proves Cheeger's inequality for `d`-regular simple graphs. This file
proves it for an arbitrary finite weighted graph `w : ι → ι → ℝ` with symmetric nonnegative
weights: the degrees `deg u = Σ_v w u v` may differ, loops `w u u > 0` are allowed (a loop counts
once in `deg u` and never in a cut), and so are vertices of degree `0`. Expansion is measured by
the **conductance** (cut weight over volume), and the spectrum by the second eigenvalue of the
random walk `w u v / deg u`, in the variational form `WalkSecondEigenvalueLE` of
`Expanders/WeightedGraph.lean`. In this normalisation Cheeger's inequality reads
`(1 − λ₂)/2 ≤ φ(w) ≤ √(2 (1 − λ₂))`.

## Definitions
* `weightVol w S`: the volume `vol S = Σ_{u ∈ S} deg u` of a vertex set.
* `weightCut w S`: the cut `Σ_{u ∈ S, v ∉ S} w u v`, the weight of the edges leaving `S`.
* `conductance w`: `φ(w) = min { cut S / vol S : 0 < vol S, 2 vol S ≤ vol ι }`. When no set is
  admissible (at most one vertex of positive degree) it is the junk value `0`.

## Theorems (all proved)
The easy direction, and connectivity:
* `WalkSecondEigenvalueLE.mul_vol_le_cut`: if the random walk has second eigenvalue at most `lam`,
  then `(1 − lam) · vol S · vol Sᶜ / vol ι ≤ cut S` for **every** `S`.
* `WalkSecondEigenvalueLE.weightCut_ge`: hence `(1 − lam)/2 · vol S ≤ cut S` whenever
  `2 vol S ≤ vol ι` (Cheeger's inequality, easy direction, set form).
* `WalkSecondEigenvalueLE.weightCut_pos`, `WalkSecondEigenvalueLE.eq_of_forall_pos`: for `lam < 1`
  every cut between two sets of positive volume has positive weight, so the graph of positive
  weights is connected on the vertices of positive degree.

The hard direction:
* `two_mul_sum_deg_mul_le_sum_mul_abs_sub`: the weighted co-area inequality.
* `sq_le_two_mul_one_sub_of_eigenfunction`: the sweep-cut lemma for a single eigenfunction of the
  random walk (no mean-zero condition).
* `walkSecondEigenvalueLE_of_weightCut_ge`: if `φ ≥ 0` and `φ · vol S ≤ cut S` whenever
  `2 vol S ≤ vol ι`, the random walk has second eigenvalue at most `1 − φ²/2`.

Conductance:
* `WalkSecondEigenvalueLE.one_sub_div_two_le_conductance` and
  `walkSecondEigenvalueLE_conductance`: the two directions, stated for `conductance`.
* `walk_cheeger`: **Cheeger's inequality for weighted graphs.** If every degree is positive and
  `λ₂` is the second eigenvalue of the symmetrised walk matrix `walkMatrix w`, then
  `(1 − λ₂)/2 ≤ conductance w ≤ √(2 (1 − λ₂))`.
* Basic API: `conductance_nonneg`, `conductance_le`, `conductance_mul_weightVol_le`,
  `le_conductance`, `exists_weightVol_pos_of_ne`, and for volumes and cuts `weightVol_nonneg`,
  `weightVol_mono`, `weightVol_add_weightVol_compl`, `weightCut_nonneg`, `weightCut_compl`.

Specialisations:
* `SimpleGraph.conductance_adjMatrix`, `SimpleGraph.secondEigenvalue_walkMatrix_adjMatrix`: for a
  `d`-regular graph the conductance is `h(G)/d` and the walk eigenvalue is `λ₂/d`. Thus
  `walk_cheeger` for the adjacency weights is `SimpleGraph.cheeger` divided by `d`, using
  `d · √(2 (1 − λ₂/d)) = √(2 d (d − λ₂))`.
* `PreAbstractSimplicialComplex.IsTopWeight.isConnected_link_of_walkSecondEigenvalueLE`,
  `PreAbstractSimplicialComplex.IsLocalSpectralExpanderOf.isConnected_link`,
  `PreAbstractSimplicialComplex.IsLocalSpectralExpander.isConnected_link`: a link of a weighted
  complex whose random walk has second eigenvalue below `1` is connected.

## Degenerate cases
* Every symmetric nonnegative `w` satisfies `WalkSecondEigenvalueLE w 1`
  (`sum_mul_mul_le_sum_deg_mul_sq`), so all bounds above are informative only for `lam < 1`, and
  `lam < 1` is exactly what the connectivity results need.
* If at most one vertex has positive degree, `WalkSecondEigenvalueLE w lam` holds for every
  `lam`, every `S` with `2 vol S ≤ vol ι` has `vol S = 0`, and `conductance w = 0`.
* `walkMatrix` is zero-extended at vertices of degree `0`, so it has extra eigenvalues `0` there;
  that is why `walk_cheeger` assumes every degree positive.

## References
* F. Chung, *Spectral Graph Theory*, CBMS Regional Conference Series 92, AMS 1997, Chapter 2,
  Theorem 2.2 (`2h ≥ λ ≥ h²/2` for the normalised Laplacian of a weighted graph, loops allowed;
  here `λ = 1 − λ₂` and `h` is the conductance), and Lemma 1.7 (the multiplicity of the walk
  eigenvalue `1` is the number of components).
* F. Chung, *Four proofs for the Cheeger inequality and graph partition algorithms*,
  https://fanchung.ucsd.edu/wp/cheeger.pdf
* F. Chung and K. Oden, *Weighted graph Laplacians and isoperimetric inequalities*, Pacific J.
  Math. 192 (2000).
* The Markov-chain form `Φ²/2 ≤ 1 − λ₂ ≤ 2Φ` for reversible chains, where holding probabilities
  play the role of loops: A. Sinclair and M. Jerrum, Inform. and Comput. 82 (1989); G. Lawler and
  A. Sokal, Trans. AMS 309 (1988); D. Levin, Y. Peres and E. Wilmer, *Markov Chains and Mixing
  Times*, 2nd ed., Theorem 13.10.
* Origins: J. Dodziuk (1984), N. Alon and V. Milman (1985), N. Alon (1986).
* D. Spielman, *Spectral Graph Theory* lecture notes, Lecture 7, "Cheeger's inequality" (2009),
  §7.4 (the every-`S` bound `WalkSecondEigenvalueLE.mul_vol_le_cut`); L. C. Lau, CS860 notes,
  Chapter 4, "Cheeger's inequality" (Waterloo 2022),
  https://cs.uwaterloo.ca/~lapchi/cs860-2022/notes/04-Cheeger.pdf
-/

open Finset Matrix

variable {ι : Type*} [Fintype ι]

/-- The **volume** of a vertex set `S` in the weighted graph `w`: the total degree
`vol S = Σ_{u ∈ S} deg u`, where `deg u = Σ_v w u v`. A loop `w u u` counts once in `deg u`.
`vol ∅ = 0`, and `weightVol w univ` is the total volume. No hypothesis on `w` is built in; for
nonnegative weights the volume is nonnegative and monotone (`weightVol_nonneg`,
`weightVol_mono`). -/
noncomputable def weightVol (w : ι → ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ u ∈ S, ∑ v, w u v

/-- The **cut** of a vertex set `S` in the weighted graph `w`: the total weight
`Σ_{u ∈ S} Σ_{v ∉ S} w u v` of the ordered pairs leaving `S`, so each edge leaving `S` is counted
once and loops never count. `cut ∅ = cut univ = 0`, and for symmetric weights
`cut Sᶜ = cut S` (`weightCut_compl`). -/
noncomputable def weightCut [DecidableEq ι] (w : ι → ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, w u v

/-- The **conductance** (volume-normalised Cheeger constant) of a weighted graph:
`φ(w) = inf { cut S / vol S : 0 < vol S, 2 vol S ≤ vol ι }`.

Junk values:
* If no set is admissible, the infimum is over an empty type and is `0` in Lean
  (`Real.iInf_of_isEmpty`). For nonnegative weights this happens exactly when at most one vertex
  has positive degree: for instance on an empty or one-element `ι`, on a graph with no edges, or
  on a single vertex with a loop and nothing else.
* Sets of volume `0` are excluded, which avoids `cut S / 0 = 0`.
* The index type is finite, so whenever some set is admissible the infimum is attained, whatever
  the signs of the weights (`conductance_le` needs no hypothesis on `w`). With negative weights it
  can be negative: `![![3, -1], ![-1, 3]]` has conductance `−1/2`. All the Cheeger bounds below
  assume nonnegative weights; `conductance_le` and `le_conductance` do not need them.

For a `d`-regular simple graph the conductance is `h(G)/d` (`SimpleGraph.conductance_adjMatrix`).
-/
noncomputable def conductance [DecidableEq ι] (w : ι → ι → ℝ) : ℝ :=
  ⨅ S : {S : Finset ι // 0 < weightVol w S ∧ 2 * weightVol w S ≤ weightVol w univ},
    weightCut w S.1 / weightVol w S.1

section Basic

variable {w : ι → ι → ℝ}

theorem weightVol_nonneg (hnn : ∀ u v, 0 ≤ w u v) (S : Finset ι) : 0 ≤ weightVol w S :=
  sum_nonneg fun u _ => sum_nonneg fun v _ => hnn u v

/-- For nonnegative weights the volume is monotone. -/
theorem weightVol_mono (hnn : ∀ u v, 0 ≤ w u v) {S T : Finset ι} (h : S ⊆ T) :
    weightVol w S ≤ weightVol w T :=
  sum_le_sum_of_subset_of_nonneg h fun u _ _ => sum_nonneg fun v _ => hnn u v

theorem weightVol_singleton (w : ι → ι → ℝ) (u : ι) : weightVol w {u} = ∑ v, w u v :=
  sum_singleton _ _

/-- For nonnegative weights, the degree of a vertex of `S` is at most the volume of `S`. -/
theorem sum_le_weightVol (hnn : ∀ u v, 0 ≤ w u v) {S : Finset ι} {u : ι} (hu : u ∈ S) :
    ∑ v, w u v ≤ weightVol w S := by
  rw [← weightVol_singleton]
  exact weightVol_mono hnn (singleton_subset_iff.mpr hu)

/-- For nonnegative weights, total volume `0` means that every weight is `0`. -/
theorem eq_zero_of_weightVol_univ_eq_zero (hnn : ∀ u v, 0 ≤ w u v)
    (h : weightVol w univ = 0) (u v : ι) : w u v = 0 := by
  have hu := (sum_eq_zero_iff_of_nonneg fun u _ => sum_nonneg fun v _ => hnn u v).mp h u
    (mem_univ u)
  exact (sum_eq_zero_iff_of_nonneg fun v _ => hnn u v).mp hu v (mem_univ v)

variable [DecidableEq ι]

/-- `vol S + vol Sᶜ = vol ι`. -/
theorem weightVol_add_weightVol_compl (w : ι → ι → ℝ) (S : Finset ι) :
    weightVol w S + weightVol w Sᶜ = weightVol w univ := by
  rw [weightVol, weightVol, weightVol, sum_add_sum_compl]

theorem weightCut_nonneg (hnn : ∀ u v, 0 ≤ w u v) (S : Finset ι) : 0 ≤ weightCut w S :=
  sum_nonneg fun u _ => sum_nonneg fun v _ => hnn u v

/-- For symmetric weights a set and its complement have the same cut. -/
theorem weightCut_compl (hsymm : ∀ u v, w u v = w v u) (S : Finset ι) :
    weightCut w Sᶜ = weightCut w S := by
  rw [weightCut, weightCut, compl_compl, sum_comm]
  exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => hsymm v u

end Basic

/-! ### Moments of an indicator function -/

section Moments

variable [DecidableEq ι] {w : ι → ι → ℝ}

private theorem sum_deg_mul_indicator (w : ι → ι → ℝ) (S : Finset ι) :
    ∑ u, (∑ v, w u v) * (if u ∈ S then (1 : ℝ) else 0) = weightVol w S := by
  simp [weightVol, mul_ite]

private theorem sum_mul_indicator_left (w : ι → ι → ℝ) (S : Finset ι) :
    ∑ u, ∑ v, w u v * (if u ∈ S then (1 : ℝ) else 0) = weightVol w S := by
  rw [← sum_deg_mul_indicator]
  exact sum_congr rfl fun u _ => (sum_mul _ _ _).symm

private theorem sum_mul_indicator_right (hsymm : ∀ u v, w u v = w v u) (S : Finset ι) :
    ∑ u, ∑ v, w u v * (if v ∈ S then (1 : ℝ) else 0) = weightVol w S := by
  rw [sum_comm, ← sum_mul_indicator_left]
  exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by rw [hsymm v u]

private theorem sum_mul_indicator_mul_indicator (w : ι → ι → ℝ) (S : Finset ι) :
    ∑ u, ∑ v, w u v * (if u ∈ S then (1 : ℝ) else 0) * (if v ∈ S then (1 : ℝ) else 0) =
      weightVol w S - weightCut w S := by
  have h : ∀ u, ∑ v, w u v * (if u ∈ S then (1 : ℝ) else 0) * (if v ∈ S then (1 : ℝ) else 0) =
      if u ∈ S then ∑ v ∈ S, w u v else 0 := by
    intro u
    by_cases hu : u ∈ S
    · simp [hu, mul_ite]
    · simp [hu]
  rw [Fintype.sum_congr _ _ h, Fintype.sum_ite_mem, weightVol, weightCut, ← sum_sub_distrib]
  refine sum_congr rfl fun u _ => ?_
  rw [← sum_add_sum_compl S (w u)]
  ring

end Moments

/-! ### The cut bound -/

section CutBound

variable [DecidableEq ι] {w : ι → ι → ℝ}

/-- **The cut bound.** If the random walk on `w` has second eigenvalue at most `lam`, then every
vertex set `S`, of any size, satisfies

  `(1 − lam) · vol S · vol Sᶜ / vol ι ≤ cut S`.

When `vol ι ≠ 0` this reads `cut S ≥ (1 − lam) · vol S · (1 − vol S / vol ι)`, the sharp form of
the easy direction of Cheeger's inequality (`WalkSecondEigenvalueLE.weightCut_ge`).

No hypothesis on `lam` is needed: for `lam ≥ 1` the left side is `≤ 0`. If `vol ι = 0` the left
side is the junk value `x / 0 = 0`; this degenerate case is the only use of nonnegativity of the
weights. The proof tests the definition on `𝟙_S − vol S / vol ι`, whose degree-weighted norm is
`vol S · vol Sᶜ / vol ι` and whose Laplacian form is `cut S`. -/
theorem WalkSecondEigenvalueLE.mul_vol_le_cut (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) {lam : ℝ} (h : WalkSecondEigenvalueLE w lam) (S : Finset ι) :
    (1 - lam) * weightVol w S * weightVol w Sᶜ / weightVol w univ ≤ weightCut w S := by
  rcases (weightVol_nonneg hnn univ).eq_or_lt with h0 | h0
  · rw [← h0, div_zero]
    exact weightCut_nonneg hnn S
  set a := weightVol w S / weightVol w univ with ha
  have hcompl := weightVol_add_weightVol_compl w S
  have hdeg := sum_deg_mul_indicator w S
  have hdeg1 : ∑ u, (∑ v, w u v) = weightVol w univ := by simp [weightVol]
  -- the test function `𝟙_S − a`, of degree-weighted mean zero
  have hmean : ∑ u, (∑ v, w u v) * ((if u ∈ S then (1 : ℝ) else 0) - a) = 0 := by
    simp only [mul_sub, sum_sub_distrib, hdeg, ← sum_mul, hdeg1, ha]
    field_simp
    ring
  have h1 := h _ hmean
  have hQ : ∑ u, ∑ v, w u v * ((if u ∈ S then (1 : ℝ) else 0) - a) *
      ((if v ∈ S then (1 : ℝ) else 0) - a) =
      (weightVol w S - weightCut w S) - 2 * a * weightVol w S + a ^ 2 * weightVol w univ := by
    have e : ∀ u v, w u v * ((if u ∈ S then (1 : ℝ) else 0) - a) *
        ((if v ∈ S then (1 : ℝ) else 0) - a) =
        w u v * (if u ∈ S then (1 : ℝ) else 0) * (if v ∈ S then (1 : ℝ) else 0)
          - a * (w u v * (if u ∈ S then (1 : ℝ) else 0))
          - a * (w u v * (if v ∈ S then (1 : ℝ) else 0)) + a ^ 2 * w u v := fun u v => by ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum,
      sum_mul_indicator_mul_indicator, sum_mul_indicator_left, sum_mul_indicator_right hsymm]
    rw [show ∑ u, ∑ v, w u v = weightVol w univ by simp [weightVol]]
    ring
  have hN : ∑ u, (∑ v, w u v) * ((if u ∈ S then (1 : ℝ) else 0) - a) ^ 2 =
      weightVol w S - 2 * a * weightVol w S + a ^ 2 * weightVol w univ := by
    have e : ∀ u, (∑ v, w u v) * ((if u ∈ S then (1 : ℝ) else 0) - a) ^ 2 =
        (∑ v, w u v) * (if u ∈ S then (1 : ℝ) else 0) * (1 - 2 * a) + a ^ 2 * (∑ v, w u v) := by
      intro u
      by_cases hu : u ∈ S <;> simp [hu] <;> ring
    simp only [e, sum_add_distrib, ← sum_mul, ← mul_sum, hdeg, hdeg1]
    ring
  rw [hQ, hN] at h1
  have hnorm : weightVol w S - 2 * a * weightVol w S + a ^ 2 * weightVol w univ =
      weightVol w S * weightVol w Sᶜ / weightVol w univ := by
    rw [show weightVol w Sᶜ = weightVol w univ - weightVol w S by linarith, ha]
    field_simp
    ring
  rw [mul_assoc, mul_div_assoc, ← hnorm]
  linarith

/-- **A spectral gap makes every cut heavy.** If the random walk on `w` has second eigenvalue
`lam < 1`, then every set `S` such that both `S` and `Sᶜ` have positive volume has a cut of
positive weight. The hypothesis `lam < 1` is necessary: `WalkSecondEigenvalueLE w 1` holds for
every symmetric nonnegative `w` (`sum_mul_mul_le_sum_deg_mul_sq`), disconnected ones included. -/
theorem WalkSecondEigenvalueLE.weightCut_pos (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) {lam : ℝ} (hlam : lam < 1) (h : WalkSecondEigenvalueLE w lam)
    {S : Finset ι} (hS : 0 < weightVol w S) (hSc : 0 < weightVol w Sᶜ) :
    0 < weightCut w S := by
  have hV : 0 < weightVol w univ := by
    rw [← weightVol_add_weightVol_compl w S]
    linarith
  have h2 : 0 < (1 - lam) * weightVol w S * weightVol w Sᶜ / weightVol w univ := by
    have : 0 < 1 - lam := by linarith
    positivity
  exact h2.trans_le (h.mul_vol_le_cut hsymm hnn S)

/-- **A spectral gap forces connectivity.** If the random walk on `w` has second eigenvalue
`lam < 1`, then a function `g` that is constant along every edge of positive weight takes a single
value on all vertices of positive degree. In other words, the graph of positive weights is
connected once its vertices of degree `0` are removed; those vertices are unconstrained.

This is the hypothesis `hconn` of `walkSecondEigenvalueLE_of_garland`. The hypothesis `lam < 1` is
necessary (see `WalkSecondEigenvalueLE.weightCut_pos`). -/
theorem WalkSecondEigenvalueLE.eq_of_forall_pos (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) {lam : ℝ} (hlam : lam < 1) (h : WalkSecondEigenvalueLE w lam)
    (g : ι → ℝ) (hg : ∀ u v, 0 < w u v → g u = g v) (u v : ι) (hu : 0 < ∑ x, w u x)
    (hv : 0 < ∑ x, w v x) : g u = g v := by
  by_contra hne
  -- the level set of `g` through `u` has no edge leaving it
  set S : Finset ι := {x | g x = g u} with hS_def
  have hcut : weightCut w S = 0 := by
    refine sum_eq_zero fun x hx => sum_eq_zero fun y hy => ?_
    simp only [hS_def, mem_compl, mem_filter, mem_univ, true_and] at hx hy
    by_contra hxy
    exact hy ((hg x y (lt_of_le_of_ne (hnn x y) (Ne.symm hxy))).symm.trans hx)
  have hS : 0 < weightVol w S :=
    lt_of_lt_of_le hu (sum_le_weightVol hnn (by simp [hS_def]))
  have hSc : 0 < weightVol w Sᶜ :=
    lt_of_lt_of_le hv (sum_le_weightVol hnn (by simp [hS_def, Ne.symm hne]))
  exact (h.weightCut_pos hsymm hnn hlam hS hSc).ne' hcut

/-- **Cheeger's inequality, easy direction (set form).** If the random walk on `w` has second
eigenvalue at most `lam`, then every set `S` with at most half the total volume has
`(1 − lam)/2 · vol S ≤ cut S`.

No hypothesis on `lam`: for `lam > 1` the left side is `≤ 0`. If `vol ι = 0` every admissible `S`
has `vol S = 0` and the bound is `0 ≤ cut S`. -/
theorem WalkSecondEigenvalueLE.weightCut_ge (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) {lam : ℝ} (h : WalkSecondEigenvalueLE w lam) {S : Finset ι}
    (hS : 2 * weightVol w S ≤ weightVol w univ) :
    (1 - lam) / 2 * weightVol w S ≤ weightCut w S := by
  have hcut0 := weightCut_nonneg hnn S
  have hS0 := weightVol_nonneg hnn S
  rcases le_or_gt lam 1 with hl | hl
  · rcases (weightVol_nonneg hnn univ).eq_or_lt with h0 | h0
    · have : weightVol w S = 0 := by linarith
      rw [this, mul_zero]
      exact hcut0
    · have h1 := h.mul_vol_le_cut hsymm hnn S
      have hcompl := weightVol_add_weightVol_compl w S
      have hX : 0 ≤ (1 - lam) * weightVol w S := mul_nonneg (by linarith) hS0
      have h2 : (1 - lam) / 2 * weightVol w S ≤
          (1 - lam) * weightVol w S * weightVol w Sᶜ / weightVol w univ := by
        rw [le_div_iff₀ h0]
        nlinarith [mul_le_mul_of_nonneg_left
          (show weightVol w univ ≤ 2 * weightVol w Sᶜ by linarith) hX]
      linarith
  · have : (1 - lam) / 2 * weightVol w S ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hS0
    linarith

end CutBound

/-! ### The hard direction -/

section Hard

variable [DecidableEq ι] {w : ι → ι → ℝ}

omit [DecidableEq ι] in
private theorem sum_mul_sub_sq (hsymm : ∀ u v, w u v = w v u) (f : ι → ℝ) :
    ∑ u, ∑ v, w u v * (f u - f v) ^ 2 =
      2 * ∑ u, (∑ v, w u v) * f u ^ 2 - 2 * ∑ u, ∑ v, w u v * f u * f v := by
  have e : ∀ u v, w u v * (f u - f v) ^ 2 =
      w u v * f u ^ 2 + w u v * f v ^ 2 - 2 * (w u v * f u * f v) := fun u v => by ring
  have a1 : ∑ u, ∑ v, w u v * f u ^ 2 = ∑ u, (∑ v, w u v) * f u ^ 2 :=
    sum_congr rfl fun u _ => (sum_mul _ _ _).symm
  have a2 : ∑ u, ∑ v, w u v * f v ^ 2 = ∑ u, (∑ v, w u v) * f u ^ 2 := by
    rw [sum_comm, ← a1]
    exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by rw [hsymm v u]
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, a1, a2]
  ring

omit [DecidableEq ι] in
private theorem sum_mul_add_sq (hsymm : ∀ u v, w u v = w v u) (f : ι → ℝ) :
    ∑ u, ∑ v, w u v * (f u + f v) ^ 2 =
      2 * ∑ u, (∑ v, w u v) * f u ^ 2 + 2 * ∑ u, ∑ v, w u v * f u * f v := by
  have e : ∀ u v, w u v * (f u + f v) ^ 2 =
      w u v * f u ^ 2 + w u v * f v ^ 2 + 2 * (w u v * f u * f v) := fun u v => by ring
  have a1 : ∑ u, ∑ v, w u v * f u ^ 2 = ∑ u, (∑ v, w u v) * f u ^ 2 :=
    sum_congr rfl fun u _ => (sum_mul _ _ _).symm
  have a2 : ∑ u, ∑ v, w u v * f v ^ 2 = ∑ u, (∑ v, w u v) * f u ^ 2 := by
    rw [sum_comm, ← a1]
    exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by rw [hsymm v u]
  simp only [e, sum_add_distrib, ← mul_sum, a1, a2]
  ring

private theorem sum_mul_abs_indicator_sub (hsymm : ∀ u v, w u v = w v u) (S : Finset ι) :
    ∑ u, ∑ v, w u v * |(if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then (1 : ℝ) else 0)| =
      2 * weightCut w S := by
  have e : ∀ u v, w u v * |(if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then (1 : ℝ) else 0)| =
      w u v * (if u ∈ S then (1 : ℝ) else 0) + w u v * (if v ∈ S then (1 : ℝ) else 0)
        - 2 * (w u v * (if u ∈ S then (1 : ℝ) else 0) * (if v ∈ S then (1 : ℝ) else 0)) := by
    intro u v
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · simp only [hu, hv, if_true, sub_self, abs_zero]
      ring
    all_goals simp [hu, hv]
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_mul_indicator_left,
    sum_mul_indicator_right hsymm, sum_mul_indicator_mul_indicator]
  ring

/-- **Weighted co-area inequality.** Suppose every set `S` with `2 vol S ≤ vol ι` has
`φ · vol S ≤ cut S`. Then every nonnegative function `g` vanishing off one such set satisfies

  `2 φ · Σ_v deg v · g v ≤ Σ_{u,v} w u v · |g u − g v|`.

The right side sums over ordered pairs, so each edge is counted twice (loops contribute `0`).
`φ` may have any sign. The proof is by strong induction on the support, peeling off the minimum
level of `g`. -/
theorem two_mul_sum_deg_mul_le_sum_mul_abs_sub (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) {φ : ℝ}
    (hφ : ∀ S : Finset ι, 2 * weightVol w S ≤ weightVol w univ →
      φ * weightVol w S ≤ weightCut w S)
    (S : Finset ι) (hS : 2 * weightVol w S ≤ weightVol w univ) (g : ι → ℝ)
    (hg : ∀ v, 0 ≤ g v) (hgS : ∀ v ∉ S, g v = 0) :
    2 * φ * ∑ v, (∑ x, w v x) * g v ≤ ∑ u, ∑ v, w u v * |g u - g v| := by
  induction S using Finset.strongInduction generalizing g with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have h0 : ∀ v, g v = 0 := fun v => hgS v (notMem_empty v)
    simp [h0]
  -- peel off the minimum level `m` of `g` on `S`
  obtain ⟨v₀, hv₀, hmin⟩ := S.exists_min_image g hne
  set m := g v₀ with hm_def
  have hm : 0 ≤ m := hg v₀
  set g' : ι → ℝ := fun v => if v ∈ S then g v - m else 0 with hg'_def
  have hg' : ∀ v, 0 ≤ g' v := by
    intro v
    by_cases hv : v ∈ S
    · simp only [g', hv, if_true]
      linarith [hmin v hv]
    · simp [g', hv]
  have hg'S : ∀ v ∉ S.erase v₀, g' v = 0 := by
    intro v hv
    by_cases hvS : v ∈ S
    · have : v = v₀ := by
        by_contra hne'
        exact hv (mem_erase.mpr ⟨hne', hvS⟩)
      subst this
      simp [g', hvS, hm_def]
    · simp [g', hvS]
  have hS' : 2 * weightVol w (S.erase v₀) ≤ weightVol w univ :=
    le_trans (by linarith [weightVol_mono hnn (erase_subset v₀ S)]) hS
  have ih' := ih (S.erase v₀) (erase_ssubset hv₀) hS' g' hg' hg'S
  -- `g = m 𝟙_S + g'`
  have hdecomp : ∀ v, g v = m * (if v ∈ S then (1 : ℝ) else 0) + g' v := by
    intro v
    by_cases hv : v ∈ S
    · simp [g', hv]
    · simp [g', hv, hgS v hv]
  have hsum : ∑ v, (∑ x, w v x) * g v = m * weightVol w S + ∑ v, (∑ x, w v x) * g' v := by
    rw [← sum_deg_mul_indicator w S, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun v _ => by rw [hdecomp v]; ring
  have habs : ∀ u v, w u v * |g u - g v| =
      m * (w u v * |(if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then (1 : ℝ) else 0)|)
        + w u v * |g' u - g' v| := by
    intro u v
    have hu' := hg' u
    have hv' := hg' v
    have key : |g u - g v| =
        m * |(if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then (1 : ℝ) else 0)|
          + |g' u - g' v| := by
      by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
      · have e1 : g u - g v = g' u - g' v := by simp [g', hu, hv]
        rw [e1]
        simp [hu, hv]
      · have e1 : g u - g v = m + g' u := by simp [g', hu, hgS v hv]
        have e2 : g' v = 0 := by simp [g', hv]
        rw [e1, e2, abs_of_nonneg (by linarith), sub_zero, abs_of_nonneg hu']
        simp [hu, hv]
      · have e1 : g u - g v = -(m + g' v) := by simp [g', hv, hgS u hu]
        have e2 : g' u = 0 := by simp [g', hu]
        rw [e1, e2, abs_neg, abs_of_nonneg (by linarith), zero_sub, abs_neg, abs_of_nonneg hv']
        simp [hu, hv]
      · simp [g', hu, hv, hgS u hu, hgS v hv]
    rw [key]
    ring
  simp only [habs, sum_add_distrib, ← mul_sum]
  rw [sum_mul_abs_indicator_sub hsymm, hsum]
  nlinarith [mul_le_mul_of_nonneg_left (hφ S hS) hm]

/-- **The sweep-cut lemma.** Suppose `φ ≥ 0` and every set `S` with `2 vol S ≤ vol ι` has
`φ · vol S ≤ cut S`. Let `g` be an eigenfunction of the random walk with eigenvalue `γ`, written
without division as `Σ_v w u v · g v = γ · deg u · g u` for every `u`, such that `g` is positive at
some vertex of positive degree and `{g > 0}` has at most half the total volume. Then
`φ² ≤ 2 (1 − γ)`.

`g` need not have degree-weighted mean zero. The positivity condition makes the positive part of
`g` have positive degree-weighted norm (a function that vanishes on every vertex of positive
degree, for instance `g = 0` or the indicator of an isolated vertex, satisfies the eigen-equation
for every `γ`, so without this condition the conclusion fails). `φ ≥ 0` is used to
square the co-area bound. The proof applies the co-area inequality to the square of the positive
part `h = max g 0` and Cauchy–Schwarz over ordered pairs, with `Σ w (h u − h v)² ≤ 2 (1 − γ) ‖h‖²`
and `Σ w (h u + h v)² ≤ 4 ‖h‖²` in the degree-weighted norm. -/
theorem sq_le_two_mul_one_sub_of_eigenfunction (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) {φ : ℝ} (hφ0 : 0 ≤ φ)
    (hφ : ∀ S : Finset ι, 2 * weightVol w S ≤ weightVol w univ →
      φ * weightVol w S ≤ weightCut w S)
    {g : ι → ℝ} {γ : ℝ} (heig : ∀ u, ∑ v, w u v * g v = γ * (∑ v, w u v) * g u)
    (hpos : ∃ u, 0 < ∑ v, w u v ∧ 0 < g u)
    (hhalf : 2 * weightVol w {v | 0 < g v} ≤ weightVol w univ) :
    φ ^ 2 ≤ 2 * (1 - γ) := by
  -- the positive part `h` of `g`
  set h : ι → ℝ := fun v => max (g v) 0 with hh_def
  have hh0 : ∀ v, 0 ≤ h v := fun v => le_max_right _ _
  have hhg : ∀ v, h v * g v = h v ^ 2 := by
    intro v
    rcases le_total (g v) 0 with hv | hv
    · simp [h, max_eq_right hv]
    · simp [h, max_eq_left hv, sq]
  have hD0 : ∀ u, 0 ≤ ∑ v, w u v := fun u => sum_nonneg fun v _ => hnn u v
  set Q := ∑ u, (∑ v, w u v) * h u ^ 2 with hQ_def
  have hQ : 0 < Q := by
    obtain ⟨u, hu, hgu⟩ := hpos
    have h1 : 0 < (∑ v, w u v) * h u ^ 2 := by
      have : h u = g u := max_eq_left hgu.le
      rw [this]
      positivity
    exact lt_of_lt_of_le h1 (single_le_sum (f := fun u => (∑ v, w u v) * h u ^ 2)
      (fun u _ => mul_nonneg (hD0 u) (sq_nonneg _)) (mem_univ u))
  -- the quadratic form of `h` is at least `γ Q`, and at most `Q`
  set R := ∑ u, ∑ v, w u v * h u * h v with hR_def
  have hR : γ * Q ≤ R := by
    rw [hQ_def, hR_def, mul_sum]
    refine sum_le_sum fun u _ => ?_
    have e1 : ∑ v, w u v * h u * h v = h u * ∑ v, w u v * h v := by
      rw [mul_sum]
      exact sum_congr rfl fun v _ => by ring
    have e2 : h u * ∑ v, w u v * g v = γ * ((∑ v, w u v) * h u ^ 2) := by
      rw [heig u, ← hhg u]
      ring
    rw [e1, ← e2]
    exact mul_le_mul_of_nonneg_left
      (sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hnn u v)) (hh0 u)
  have hRQ : R ≤ Q := sum_mul_mul_le_sum_deg_mul_sq hsymm hnn h
  set E := ∑ u, ∑ v, w u v * (h u - h v) ^ 2 with hE_def
  set P := ∑ u, ∑ v, w u v * (h u + h v) ^ 2 with hP_def
  have hE : E = 2 * Q - 2 * R := sum_mul_sub_sq hsymm h
  have hP : P = 2 * Q + 2 * R := sum_mul_add_sq hsymm h
  have hE0 : 0 ≤ E :=
    sum_nonneg fun u _ => sum_nonneg fun v _ => mul_nonneg (hnn u v) (sq_nonneg _)
  have hP0 : 0 ≤ P :=
    sum_nonneg fun u _ => sum_nonneg fun v _ => mul_nonneg (hnn u v) (sq_nonneg _)
  -- co-area applied to `h²`, supported on `{g > 0}`
  set T := ∑ u, ∑ v, w u v * |h u ^ 2 - h v ^ 2| with hT_def
  have hcoarea : 2 * φ * Q ≤ T :=
    two_mul_sum_deg_mul_le_sum_mul_abs_sub hsymm hnn hφ {v | 0 < g v} hhalf
      (fun v => h v ^ 2) (fun v => sq_nonneg _) (by
        intro v hv
        simp only [mem_filter, mem_univ, true_and, not_lt] at hv
        simp [h, max_eq_right hv])
  -- Cauchy–Schwarz over ordered pairs: `T² ≤ E P`
  have hCS : T ^ 2 ≤ E * P := by
    have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset (ι × ι))
      (r := fun p => w p.1 p.2 * |h p.1 ^ 2 - h p.2 ^ 2|)
      (f := fun p => w p.1 p.2 * (h p.1 - h p.2) ^ 2)
      (g := fun p => w p.1 p.2 * (h p.1 + h p.2) ^ 2)
      (fun p _ => mul_nonneg (hnn _ _) (sq_nonneg _))
      (fun p _ => mul_nonneg (hnn _ _) (sq_nonneg _))
      (fun p _ => le_of_eq (by rw [mul_pow, sq_abs]; ring))
    simp only [Fintype.sum_prod_type] at hcs
    exact hcs
  -- combine
  have h1 : (2 * φ * Q) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by positivity) hcoarea 2
  have h2 : E * P ≤ (2 * (1 - γ) * Q) * (4 * Q) :=
    mul_le_mul (by linarith) (by linarith) hP0 (by linarith)
  have h3 : φ ^ 2 * (4 * Q ^ 2) ≤ (2 * (1 - γ)) * (4 * Q ^ 2) := by nlinarith
  exact le_of_mul_le_mul_right h3 (by positivity)

/-- **Cheeger's inequality, hard direction.** If `φ ≥ 0` and every set `S` with at most half the
total volume has `φ · vol S ≤ cut S`, then the random walk on `w` has second eigenvalue at most
`1 − φ²/2`.

The hypothesis `φ ≥ 0` is necessary: the single edge `K₂` satisfies the cut hypothesis with
`φ = −10`, but its random walk has second eigenvalue `−1 > 1 − 100/2`. Degenerate case: if
`vol ι = 0` (no edges) the conclusion holds for every value
(`walkSecondEigenvalueLE_of_forall_eq_zero`).

The proof takes an eigenfunction `g` with eigenvalue `γ > 1 − φ²/2`
(`exists_walk_eigenfunction_of_lt`), subtracts its degree-weighted mean (which keeps it an
eigenfunction, since `(1 − γ) ⟨g, 1⟩ = 0`), and applies the sweep-cut lemma
`sq_le_two_mul_one_sub_of_eigenfunction` to it or to its negative, whichever has positive set of
at most half the volume. -/
theorem walkSecondEigenvalueLE_of_weightCut_ge (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) {φ : ℝ} (hφ0 : 0 ≤ φ)
    (hφ : ∀ S : Finset ι, 2 * weightVol w S ≤ weightVol w univ →
      φ * weightVol w S ≤ weightCut w S) :
    WalkSecondEigenvalueLE w (1 - φ ^ 2 / 2) := by
  intro f hf
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨g, γ, hγ, heig, hgf⟩ := exists_walk_eigenfunction_of_lt hsymm hnn hcon
  have hD0 : ∀ u, 0 ≤ ∑ v, w u v := fun u => sum_nonneg fun v _ => hnn u v
  have hdeg1 : ∑ u, (∑ v, w u v) = weightVol w univ := by simp [weightVol]
  -- the total volume is positive
  have hV : 0 < weightVol w univ := by
    rcases (weightVol_nonneg hnn univ).eq_or_lt with h0 | h0
    · refine absurd ?_ hgf
      refine sum_eq_zero fun u _ => ?_
      have : ∑ v, w u v = 0 :=
        sum_eq_zero fun v _ => eq_zero_of_weightVol_univ_eq_zero hnn h0.symm u v
      rw [this]
      ring
    · exact h0
  -- `(1 − γ) ⟨g, 1⟩ = 0`
  have hsum : (1 - γ) * ∑ u, (∑ v, w u v) * g u = 0 := by
    have h1 : ∑ u, ∑ v, w u v * g v = ∑ u, (∑ v, w u v) * g u := by
      rw [sum_comm]
      refine sum_congr rfl fun v _ => ?_
      rw [sum_mul]
      exact sum_congr rfl fun u _ => by rw [hsymm u v]
    have h2 : ∑ u, ∑ v, w u v * g v = γ * ∑ u, (∑ v, w u v) * g u := by
      rw [mul_sum]
      exact sum_congr rfl fun u _ => by rw [heig u]; ring
    linarith
  -- subtract the degree-weighted mean `c`; the result is still an eigenfunction
  set c := (∑ u, (∑ v, w u v) * g u) / weightVol w univ with hc_def
  have hc : c * (1 - γ) = 0 := by
    rw [hc_def, div_mul_eq_mul_div, mul_comm, hsum, zero_div]
  set g' : ι → ℝ := fun u => g u - c with hg'_def
  have heig' : ∀ u, ∑ v, w u v * g' v = γ * (∑ v, w u v) * g' u := by
    intro u
    have e : ∑ v, w u v * g' v = ∑ v, w u v * g v - c * ∑ v, w u v := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun v _ => by simp only [g']; ring
    rw [e, heig u]
    simp only [g']
    linear_combination (-(∑ v, w u v)) * hc
  have hmean' : ∑ u, (∑ v, w u v) * g' u = 0 := by
    simp only [g', mul_sub, sum_sub_distrib, ← sum_mul, hdeg1, hc_def]
    field_simp
    ring
  -- `g'` does not vanish on the vertices of positive degree
  obtain ⟨u₀, hu₀⟩ : ∃ u, (∑ v, w u v) * g' u ≠ 0 := by
    by_contra hcon'
    push Not at hcon'
    apply hgf
    have e : ∀ u, (∑ v, w u v) * g u * f u =
        (∑ v, w u v) * g' u * f u + c * ((∑ v, w u v) * f u) := by
      intro u
      simp only [g']
      ring
    simp only [e, sum_add_distrib, ← mul_sum, hf, hcon', zero_mul, sum_const_zero, mul_zero,
      add_zero]
  have hposex : ∃ u, 0 < ∑ v, w u v ∧ 0 < g' u := by
    by_contra hcon'
    push Not at hcon'
    have hle : ∀ u ∈ univ, (∑ v, w u v) * g' u ≤ 0 := by
      intro u _
      rcases (hD0 u).eq_or_lt with h | h
      · rw [← h, zero_mul]
      · exact mul_nonpos_of_nonneg_of_nonpos h.le (hcon' u h)
    exact hu₀ ((sum_eq_zero_iff_of_nonpos hle).mp hmean' u₀ (mem_univ _))
  have hnegex : ∃ u, 0 < ∑ v, w u v ∧ g' u < 0 := by
    by_contra hcon'
    push Not at hcon'
    have hle : ∀ u ∈ univ, 0 ≤ (∑ v, w u v) * g' u := by
      intro u _
      rcases (hD0 u).eq_or_lt with h | h
      · rw [← h, zero_mul]
      · exact mul_nonneg h.le (hcon' u h)
    exact hu₀ ((sum_eq_zero_iff_of_nonneg hle).mp hmean' u₀ (mem_univ _))
  -- one of `{g' > 0}`, `{g' < 0}` has at most half the volume
  have hdisj : weightVol w {v | 0 < g' v} + weightVol w {v | g' v < 0} ≤ weightVol w univ := by
    have hsplit := sum_filter_add_sum_filter_not univ (fun v => 0 < g' v) (fun u => ∑ v, w u v)
    have hsub : ({v | g' v < 0} : Finset ι) ⊆ ({v | ¬ 0 < g' v} : Finset ι) := by
      intro v
      simp only [mem_filter, mem_univ, true_and, not_lt]
      exact le_of_lt
    have := weightVol_mono hnn hsub
    unfold weightVol at *
    linarith
  have key : φ ^ 2 ≤ 2 * (1 - γ) := by
    by_cases h2 : 2 * weightVol w {v | 0 < g' v} ≤ weightVol w univ
    · exact sq_le_two_mul_one_sub_of_eigenfunction hsymm hnn hφ0 hφ heig' hposex h2
    · refine sq_le_two_mul_one_sub_of_eigenfunction hsymm hnn hφ0 hφ (g := fun u => -g' u)
        ?_ ?_ ?_
      · intro u
        simp only [mul_neg, sum_neg_distrib, heig' u]
      · obtain ⟨u, hu, hgu⟩ := hnegex
        exact ⟨u, hu, neg_pos.mpr hgu⟩
      · have e : ({v | 0 < -g' v} : Finset ι) = ({v | g' v < 0} : Finset ι) := by
          ext v
          simp
        rw [e]
        linarith
  linarith

end Hard

/-! ### Conductance and Cheeger's inequality -/

section Conductance

variable [DecidableEq ι] {w : ι → ι → ℝ}

/-- For nonnegative weights the conductance is nonnegative (including the junk value `0`). -/
theorem conductance_nonneg (hnn : ∀ u v, 0 ≤ w u v) : 0 ≤ conductance w :=
  Real.iInf_nonneg fun S => div_nonneg (weightCut_nonneg hnn _) S.2.1.le

/-- The conductance is at most the cut ratio of every admissible set. No hypothesis on the
weights is needed: the index type is finite, so the quotients are bounded below. -/
theorem conductance_le {S : Finset ι} (h0 : 0 < weightVol w S)
    (hS : 2 * weightVol w S ≤ weightVol w univ) :
    conductance w ≤ weightCut w S / weightVol w S :=
  ciInf_le (f := fun S : {S : Finset ι // 0 < weightVol w S ∧
      2 * weightVol w S ≤ weightVol w univ} => weightCut w S.1 / weightVol w S.1)
    (Set.finite_range _).bddBelow ⟨S, h0, hS⟩

/-- Every set with at most half the total volume, including sets of volume `0`, has
`conductance w · vol S ≤ cut S`. This holds also when no set is admissible, since the conductance
is then `0`. -/
theorem conductance_mul_weightVol_le (hnn : ∀ u v, 0 ≤ w u v) {S : Finset ι}
    (hS : 2 * weightVol w S ≤ weightVol w univ) :
    conductance w * weightVol w S ≤ weightCut w S := by
  rcases (weightVol_nonneg hnn S).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]
    exact weightCut_nonneg hnn S
  · exact (le_div_iff₀ h0).mp (conductance_le h0 hS)

/-- A lower bound `c · vol S ≤ cut S` on every admissible set bounds the conductance below. The
existence of an admissible set is needed: otherwise the conductance is the junk value `0`. -/
theorem le_conductance {c : ℝ}
    (hne : ∃ S : Finset ι, 0 < weightVol w S ∧ 2 * weightVol w S ≤ weightVol w univ)
    (h : ∀ S : Finset ι, 0 < weightVol w S → 2 * weightVol w S ≤ weightVol w univ →
      c * weightVol w S ≤ weightCut w S) :
    c ≤ conductance w := by
  obtain ⟨S, hS⟩ := hne
  have : Nonempty {S : Finset ι // 0 < weightVol w S ∧ 2 * weightVol w S ≤ weightVol w univ} :=
    ⟨⟨S, hS⟩⟩
  exact le_ciInf fun S => (le_div_iff₀ S.2.1).mpr (h S.1 S.2.1 S.2.2)

/-- Two distinct vertices of positive degree give an admissible set: the one of smaller degree,
as a singleton. (Conversely, for nonnegative weights an admissible set exists only if two
distinct vertices have positive degree: one in `S`, and one in `Sᶜ`, because
`vol Sᶜ ≥ vol S > 0`. This direction is not needed here.) -/
theorem exists_weightVol_pos_of_ne (hnn : ∀ u v, 0 ≤ w u v) {u v : ι} (huv : u ≠ v)
    (hu : 0 < ∑ x, w u x) (hv : 0 < ∑ x, w v x) :
    ∃ S : Finset ι, 0 < weightVol w S ∧ 2 * weightVol w S ≤ weightVol w univ := by
  have hpair : (∑ x, w u x) + (∑ x, w v x) ≤ weightVol w univ := by
    have := weightVol_mono hnn (subset_univ {u, v})
    rwa [weightVol, sum_pair huv] at this
  rcases le_total (∑ x, w u x) (∑ x, w v x) with h | h
  · exact ⟨{u}, by rwa [weightVol_singleton], by rw [weightVol_singleton]; linarith⟩
  · exact ⟨{v}, by rwa [weightVol_singleton], by rw [weightVol_singleton]; linarith⟩

/-- **Cheeger's inequality, easy direction, for the conductance.** If the random walk on `w` has
second eigenvalue at most `lam` and two distinct vertices have positive degree, then
`(1 − lam)/2 ≤ conductance w`.

The two vertices are needed. Without them no set is admissible and the conductance is the junk
value `0`, while `WalkSecondEigenvalueLE w lam` holds for every `lam` (for example on a single
vertex with a loop), so `(1 − lam)/2` can be positive. -/
theorem WalkSecondEigenvalueLE.one_sub_div_two_le_conductance (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) {lam : ℝ} (h : WalkSecondEigenvalueLE w lam) {u v : ι}
    (huv : u ≠ v) (hu : 0 < ∑ x, w u x) (hv : 0 < ∑ x, w v x) :
    (1 - lam) / 2 ≤ conductance w :=
  le_conductance (exists_weightVol_pos_of_ne hnn huv hu hv) fun _ _ hS =>
    h.weightCut_ge hsymm hnn hS

/-- **Cheeger's inequality, hard direction, for the conductance.** The random walk on every
symmetric nonnegative weighted graph has second eigenvalue at most `1 − (conductance w)² / 2`.
There is no further hypothesis: when no set is admissible the conductance is `0` and the bound
is `1`, which always holds. -/
theorem walkSecondEigenvalueLE_conductance (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) : WalkSecondEigenvalueLE w (1 - conductance w ^ 2 / 2) :=
  walkSecondEigenvalueLE_of_weightCut_ge hsymm hnn (conductance_nonneg hnn) fun _ hS =>
    conductance_mul_weightVol_le hnn hS

/-- **Cheeger's inequality for weighted graphs.** Let `w` be symmetric and nonnegative with every
degree positive, on at least two vertices, and let `λ₂` be the second-largest eigenvalue (with
multiplicity) of the symmetrised random-walk matrix `walkMatrix w`. Then

  `(1 − λ₂)/2 ≤ conductance w ≤ √(2 (1 − λ₂))`.

`Nontrivial ι` is needed for `λ₂` to exist. The positive degrees are needed for the lower bound:
`walkMatrix` is zero-extended at a vertex of degree `0`, which adds an eigenvalue `0`. For
`w = [[1, 0], [0, 0]]` the matrix `walkMatrix w` has eigenvalues `1, 0`, so `λ₂ = 0`, while no set
is admissible and the conductance is the junk value `0 < 1/2`. The upper bound holds without
them, as `walkSecondEigenvalueLE_conductance` shows, but its translation to `walkMatrix` goes
through `walkSecondEigenvalueLE_iff_secondEigenvalue_le`, which needs them. The argument of the
square root is nonnegative, since `λ₂ ≤ 1`.

For the adjacency weights of a `d`-regular graph this is `SimpleGraph.cheeger` divided by `d`
(`SimpleGraph.conductance_adjMatrix`, `SimpleGraph.secondEigenvalue_walkMatrix_adjMatrix`). -/
theorem walk_cheeger [Nontrivial ι] (hsymm : ∀ u v, w u v = w v u) (hnn : ∀ u v, 0 ≤ w u v)
    (hdeg : ∀ u, 0 < ∑ v, w u v) :
    (1 - (walkMatrix_isHermitian hsymm).secondEigenvalue) / 2 ≤ conductance w ∧
      conductance w ≤ Real.sqrt (2 * (1 - (walkMatrix_isHermitian hsymm).secondEigenvalue)) := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne ι
  refine ⟨((walkSecondEigenvalueLE_iff_secondEigenvalue_le hsymm hnn hdeg).mpr le_rfl
    |>.one_sub_div_two_le_conductance hsymm hnn huv (hdeg u) (hdeg v)), ?_⟩
  have h1 := (walkSecondEigenvalueLE_iff_secondEigenvalue_le hsymm hnn hdeg).mp
    (walkSecondEigenvalueLE_conductance hsymm hnn)
  have hsq : conductance w ^ 2 ≤ 2 * (1 - (walkMatrix_isHermitian hsymm).secondEigenvalue) := by
    linarith
  exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)

end Conductance

/-! ### Regular graphs -/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

omit [DecidableEq V] in
/-- In a `d`-regular graph the volume of `S` is `d · |S|`. -/
theorem weightVol_adjMatrix (hd : G.IsRegularOfDegree d) (S : Finset V) :
    weightVol (fun u v => G.adjMatrix ℝ u v) S = d * #S := by
  have hdeg : ∀ u, ∑ v, G.adjMatrix ℝ u v = d := by
    intro u
    have := congrFun (adjMatrix_mulVec_one_of_regular hd) u
    simpa [mulVec, dotProduct] using this
  simp only [weightVol, hdeg, sum_const, nsmul_eq_mul, mul_comm]

/-- For the adjacency weights of a simple graph the cut of `S` counts the edges leaving `S`. -/
theorem weightCut_adjMatrix (S : Finset V) :
    weightCut (fun u v => G.adjMatrix ℝ u v) S = #(G.edgeBoundary S) := by
  rw [edgeBoundary, interedges_def, card_filter, sum_product]
  push_cast
  simp [weightCut, adjMatrix_apply]

/-- **The conductance of a regular graph.** For a `d`-regular graph the conductance of the
adjacency weights is the Cheeger constant divided by the degree: `φ = h(G) / d`.

This holds for every `d` and every vertex type. For `d = 0` both sides are junk `0`: no set has
positive volume, and `h(G) / 0 = 0`. On fewer than two vertices both infima are over empty types
and both sides are `0`. -/
theorem conductance_adjMatrix (hd : G.IsRegularOfDegree d) :
    conductance (fun u v => G.adjMatrix ℝ u v) = G.edgeExpansion / d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · rw [Nat.cast_zero, div_zero]
    have : IsEmpty {S : Finset V // 0 < weightVol (fun u v => G.adjMatrix ℝ u v) S ∧
        2 * weightVol (fun u v => G.adjMatrix ℝ u v) S ≤
          weightVol (fun u v => G.adjMatrix ℝ u v) univ} :=
      ⟨fun S => by
        have h := S.2.1
        rw [weightVol_adjMatrix hd, Nat.cast_zero, zero_mul] at h
        exact lt_irrefl _ h⟩
    exact Real.iInf_of_isEmpty _
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hiff : ∀ S : Finset V, (0 < weightVol (fun u v => G.adjMatrix ℝ u v) S ∧
      2 * weightVol (fun u v => G.adjMatrix ℝ u v) S ≤
        weightVol (fun u v => G.adjMatrix ℝ u v) univ) ↔
      (S.Nonempty ∧ 2 * #S ≤ Fintype.card V) := by
    intro S
    rw [weightVol_adjMatrix hd, weightVol_adjMatrix hd, card_univ, ← card_pos]
    refine and_congr ?_ ?_
    · rw [mul_pos_iff_of_pos_left hd0', Nat.cast_pos]
    · rw [show (2 : ℝ) * (d * #S) = d * ((2 * #S : ℕ) : ℝ) by push_cast; ring,
        mul_le_mul_iff_right₀ hd0', Nat.cast_le]
  unfold conductance edgeExpansion
  rw [div_eq_mul_inv, Real.iInf_mul_of_nonneg (inv_nonneg.mpr hd0'.le)]
  refine Equiv.iInf_congr (Equiv.subtypeEquivRight hiff) fun S => ?_
  change (#(G.edgeBoundary S.1) : ℝ) / #S.1 * (d : ℝ)⁻¹ =
    weightCut (fun u v => G.adjMatrix ℝ u v) S.1 / weightVol (fun u v => G.adjMatrix ℝ u v) S.1
  rw [weightCut_adjMatrix, weightVol_adjMatrix hd S.1]
  field_simp

/-- **The walk eigenvalue of a regular graph.** For a `d`-regular graph on at least two vertices
the second eigenvalue of the symmetrised walk matrix of the adjacency weights is `λ₂ / d`, with
`λ₂` the second adjacency eigenvalue.

For `d = 0` the graph has no edges, both matrices are `0`, and both sides are `0` (with the junk
value `λ₂ / 0 = 0`). `Nontrivial V` is needed for second eigenvalues to exist. -/
theorem secondEigenvalue_walkMatrix_adjMatrix [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    (walkMatrix_isHermitian (w := fun u v => G.adjMatrix ℝ u v)
      fun u v => G.isSymm_adjMatrix.apply v u).secondEigenvalue = G.secondAdjEigenvalue / d := by
  have hsymm : ∀ u v, G.adjMatrix ℝ u v = G.adjMatrix ℝ v u := fun u v =>
    G.isSymm_adjMatrix.apply v u
  have hnn : ∀ u v, 0 ≤ G.adjMatrix ℝ u v := fun u v => by
    rw [adjMatrix_apply]
    split_ifs <;> norm_num
  have hdeg' : ∀ u, ∑ v, G.adjMatrix ℝ u v = d := by
    intro u
    have := congrFun (adjMatrix_mulVec_one_of_regular hd) u
    simpa [mulVec, dotProduct] using this
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · -- `d = 0`: no edges, and both matrices vanish
    have hA : ∀ u v, G.adjMatrix ℝ u v = 0 := by
      intro u v
      rw [adjMatrix_apply, if_neg]
      intro hadj
      have := (G.degree_pos_iff_exists_adj u).mpr ⟨v, hadj⟩
      rw [hd u] at this
      exact lt_irrefl _ this
    have hW : walkMatrix (fun u v => G.adjMatrix ℝ u v) = 0 := by
      ext u v
      simp only [walkMatrix_apply, hA, zero_div, Matrix.zero_apply]
    rw [Nat.cast_zero, div_zero, ← Matrix.IsHermitian.eigenvalues_secondIndex,
      (walkMatrix_isHermitian hsymm).eigenvalues_eq_zero_iff.mpr hW]
    rfl
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hdeg : ∀ u, 0 < ∑ v, G.adjMatrix ℝ u v := fun u => by rw [hdeg' u]; exact hd0'
  apply le_antisymm
  · rw [← walkSecondEigenvalueLE_iff_secondEigenvalue_le hsymm hnn hdeg,
      walkSecondEigenvalueLE_adjMatrix_iff hd hd0, div_mul_cancel₀ _ hd0'.ne']
  · rw [div_le_iff₀ hd0', ← walkSecondEigenvalueLE_adjMatrix_iff hd hd0,
      walkSecondEigenvalueLE_iff_secondEigenvalue_le hsymm hnn hdeg]

end SimpleGraph

/-! ### Connectivity of the links of a weighted complex -/

namespace PreAbstractSimplicialComplex

variable [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {d : ℕ} {m : Finset ι → ℝ}

/-- In a weighted complex, every vertex of the link of a set `σ` with `#σ + 1 ≤ d` has positive
degree in the weighted graph `linkWeightOf m σ`: a top face through `σ ∪ {x}` has a further
vertex `y`, and `x y` is an edge of positive weight. -/
theorem IsTopWeight.sum_linkWeightOf_pos_of_mem_vertices (hm : K.IsTopWeight d m)
    {σ : Finset ι} (hcard : #σ + 1 ≤ d) {x : ι} (hx : x ∈ (K.link σ).vertices) :
    0 < ∑ y, linkWeightOf m σ x y := by
  obtain ⟨-, hdisj, hmem⟩ := mem_link.mp (show {x} ∈ K.link σ from hx)
  have hxσ : x ∉ σ := disjoint_singleton_left.mp hdisj
  obtain ⟨-, F, hF, hsub, hFcard⟩ := hm.isPure _ hmem
  have hlt : #({x} ∪ σ) < #F := by
    rw [singleton_union, card_insert_of_notMem hxσ]
    omega
  obtain ⟨y, hyF, hy⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hxy : x ≠ y := fun h => hy (h ▸ mem_union_left _ (mem_singleton_self x))
  have hyσ : y ∉ σ := fun h => hy (mem_union_right _ h)
  have hpos : 0 < linkWeightOf m σ x y := by
    refine hm.linkWeightOf_pos_iff.mpr ⟨hxy, hxσ, hyσ, F, hF, hFcard, ?_⟩
    intro z hz
    simp only [mem_insert] at hz
    rcases hz with rfl | rfl | hz
    · exact hsub (mem_union_left _ (mem_singleton_self _))
    · exact hyF
    · exact hsub (mem_union_right _ hz)
  exact lt_of_lt_of_le hpos
    (single_le_sum (fun z _ => linkWeightOf_nonneg hm.nonneg σ x z) (mem_univ y))

/-- An edge of positive weight in `linkWeightOf m σ` is an edge of the 1-skeleton of the link
of `σ`. -/
theorem IsTopWeight.oneSkeleton_link_adj_of_linkWeightOf_pos (hm : K.IsTopWeight d m)
    {σ : Finset ι} {x y : ι} (h : 0 < linkWeightOf m σ x y) :
    (K.link σ).oneSkeleton.Adj x y := by
  obtain ⟨hxy, hx, hy, F, hF, -, hsub⟩ := hm.linkWeightOf_pos_iff.mp h
  rw [oneSkeleton, SimpleGraph.fromRel_adj]
  refine ⟨hxy, Or.inl (mem_link.mpr ⟨insert_nonempty _ _, ?_, K.mem_of_subset hF ?_ ?_⟩)⟩
  · rw [disjoint_left]
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  · intro z hz
    refine hsub ?_
    simp only [mem_union, mem_insert, mem_singleton] at hz ⊢
    tauto
  · exact ⟨x, by simp⟩

/-- **A spectral gap of a link makes it connected.** Let `m` be a top weight of the
`d`-dimensional complex `K` and let `σ` be `∅` or a face with `#σ + 1 ≤ d`. If the random walk on
the weighted graph of the link of `σ` has second eigenvalue `lam < 1`, then the link of `σ` is
connected.

`lam < 1` is necessary, since every weighted graph satisfies the bound with `lam = 1`. The
conditions on `σ` are the ones under which `IsLocalSpectralExpanderOf` tests the link; they give
the link a vertex (`IsTopWeight.exists_linkWeightOf_pos`), and every vertex of the link positive
degree. The vertices of positive degree in `linkWeightOf m σ` are exactly the vertices of the
link, and its edges of positive weight are exactly the edges of the link, so this is
`WalkSecondEigenvalueLE.eq_of_forall_pos` for the reachability indicator of a vertex. -/
theorem IsTopWeight.isConnected_link_of_walkSecondEigenvalueLE (hm : K.IsTopWeight d m)
    {σ : Finset ι} (hσ : σ = ∅ ∨ σ ∈ K) (hcard : #σ + 1 ≤ d) {lam : ℝ}
    (h : WalkSecondEigenvalueLE (linkWeightOf m σ) lam) (hlam : lam < 1) :
    (K.link σ).IsConnected := by
  classical
  have hsymm := linkWeightOf_symm m σ
  have hnn := linkWeightOf_nonneg hm.nonneg σ
  have hvert : ∀ x, 0 < ∑ y, linkWeightOf m σ x y → x ∈ (K.link σ).vertices := fun x hx =>
    K.mem_vertices_link_of_pos (hm.sum_linkWeightOf_pos_iff.mp hx)
  have hdeg : ∀ x y, 0 < linkWeightOf m σ x y → 0 < ∑ z, linkWeightOf m σ x z := fun x y h =>
    lt_of_lt_of_le h (single_le_sum (fun z _ => hnn x z) (mem_univ y))
  obtain ⟨x₀, y₀, h₀⟩ := hm.exists_linkWeightOf_pos hσ hcard
  have hx₀ := hdeg x₀ y₀ h₀
  set G := (K.link σ).oneSkeleton.induce (K.link σ).vertices with hG
  set a : (K.link σ).vertices := ⟨x₀, hvert x₀ hx₀⟩ with ha
  -- the indicator of the component of `a`
  set g : ι → ℝ := fun z => if hz : z ∈ (K.link σ).vertices then
    (if G.Reachable a ⟨z, hz⟩ then 1 else 0) else 0 with hg_def
  have hg : ∀ u v, 0 < linkWeightOf m σ u v → g u = g v := by
    intro u v huv
    have hu := hvert u (hdeg u v huv)
    have hv := hvert v (hdeg v u (by rwa [hsymm]))
    have hadj : G.Adj ⟨u, hu⟩ ⟨v, hv⟩ :=
      SimpleGraph.comap_adj.mpr (hm.oneSkeleton_link_adj_of_linkWeightOf_pos huv)
    have hreach : G.Reachable a ⟨u, hu⟩ ↔ G.Reachable a ⟨v, hv⟩ :=
      ⟨fun hr => hr.trans hadj.reachable, fun hr => hr.trans hadj.symm.reachable⟩
    simp only [hg_def, dif_pos hu, dif_pos hv, hreach]
  show G.Connected
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨a, fun b => ?_⟩
  have hb := hm.sum_linkWeightOf_pos_of_mem_vertices hcard b.2
  have heq := h.eq_of_forall_pos hsymm hnn hlam g hg x₀ b hx₀ hb
  simp only [hg_def, dif_pos (hvert x₀ hx₀), dif_pos b.2] at heq
  by_contra hnot
  rw [if_pos (show G.Reachable a ⟨x₀, hvert x₀ hx₀⟩ from SimpleGraph.Reachable.refl a),
    if_neg (show ¬ G.Reachable a ⟨b.1, b.2⟩ from hnot)] at heq
  exact one_ne_zero heq

/-- **The links of a local spectral expander are connected.** In a `lam`-local-spectral expander
with `lam < 1` (weighted version), the complex itself and the link of every face of dimension at
most `d − 2` are connected.

This does not remove the connectivity hypothesis of `trickling_down_weighted`: a complex that is
already known to be a local spectral expander has every link bound that trickling down would
produce. -/
theorem IsLocalSpectralExpanderOf.isConnected_link {lam : ℝ}
    (h : K.IsLocalSpectralExpanderOf d m lam) (hlam : lam < 1) {σ : Finset ι}
    (hσ : σ = ∅ ∨ σ ∈ K) (hcard : #σ + 1 ≤ d) : (K.link σ).IsConnected :=
  h.isTopWeight.isConnected_link_of_walkSecondEigenvalueLE hσ hcard
    (h.walkSecondEigenvalueLE hσ hcard) hlam

/-- **The links of a local spectral expander are connected** (counting weights). In a
`lam`-local-spectral expander with `lam < 1`, the complex itself and the link of every face of
dimension at most `d − 2` are connected. -/
theorem IsLocalSpectralExpander.isConnected_link {lam : ℝ}
    (h : K.IsLocalSpectralExpander d lam) (hlam : lam < 1) {σ : Finset ι}
    (hσ : σ = ∅ ∨ σ ∈ K) (hcard : #σ + 1 ≤ d) : (K.link σ).IsConnected :=
  ((K.isLocalSpectralExpander_iff_isLocalSpectralExpanderOf).mp h).isConnected_link hlam hσ hcard

end PreAbstractSimplicialComplex
