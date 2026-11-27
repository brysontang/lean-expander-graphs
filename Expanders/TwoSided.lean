/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.Basic

/-!
# Two-sided spectral expansion: the mixing lemma and Hoffman's bounds

For a `d`-regular graph `G` on `n` vertices with adjacency eigenvalues
`d = λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ`, `Expanders/Basic.lean` controls only `λ₂`, which measures one-sided
expansion. This file adds the smallest eigenvalue `λₙ` and the **two-sided spectral parameter**
`λ(G) = max(|λ₂|, |λₙ|)`, the largest absolute value of an eigenvalue other than the trivial
`λ₁ = d`, and proves the classical consequences: the expander mixing lemma and Hoffman's bounds
on the independence and chromatic numbers.

Throughout, `e(S, T) = #(G.interedges S T)` counts the *ordered* pairs `(u, v)` with `u ∈ S`,
`v ∈ T` and `u ~ v`. An edge with both ends in `S ∩ T` is counted twice, so `e(S, S)` is twice
the number of edges inside `S`.

## Definitions
* `Matrix.IsHermitian.smallestEigenvalue`: the smallest eigenvalue `λₙ` of a real symmetric
  matrix. `Matrix.IsHermitian.bottomIndex`: the index of the eigenbasis carrying it.
* `SimpleGraph.smallestAdjEigenvalue`: the smallest adjacency eigenvalue `λₙ`.
* `SimpleGraph.twoSidedAdjEigenvalue`: the two-sided parameter `λ(G) = max(|λ₂|, |λₙ|)`.
* `SimpleGraph.IsTwoSidedSpectralExpander d lam`: `G` is `d`-regular and `λ(G) ≤ lam` (an
  `(n, d, lam)`-graph).
* `SimpleGraph.centeredIndicator S`: the indicator of `S` minus its mean, `1_S − (|S|/n) 𝟙`.

## Theorems (all proved here)
Linear algebra, for a real symmetric matrix `A` (namespace `Matrix.IsHermitian`):
* `smallestEigenvalue_le_eigenvalues`, `smallestEigenvalue_le_secondEigenvalue`,
  `eigenvalues_bottomIndex`: `λₙ` is the least eigenvalue and sits at `bottomIndex`.
* `smallest_mul_le_dotProduct_mulVec`: the lower Rayleigh bound `λₙ · xᵀx ≤ xᵀAx`;
  `smallest_le_of_mulVec_eq`: every eigenvalue is at least `λₙ`;
  `exists_eigenvector_smallest`: `λₙ` has a nonzero eigenvector.
* `dotProduct_mulVec_eq_sum_coeff`: the bilinear form in the eigenbasis,
  `xᵀAy = Σⱼ λⱼ cⱼ(x) cⱼ(y)`.
* `coeff_topIndex_eq_zero`: if `λ₂ < λ₁`, a vector orthogonal to a top eigenvector has no
  component along the top vector of the eigenbasis.

Graphs (namespace `SimpleGraph`):
* `smallestAdjEigenvalue_nonpos`: `λₙ ≤ 0` for every graph. `smallestAdjEigenvalue_le_neg_one`:
  `λₙ ≤ −1` as soon as there is an edge, with no regularity assumption; hence
  `one_le_twoSidedAdjEigenvalue`: `λ(G) ≥ 1` as soon as there is an edge.
  `smallestAdjEigenvalue_le_secondAdjEigenvalue`: `λₙ ≤ λ₂`.
* `twoSidedAdjEigenvalue_eq_max`: `λ(G) = max(λ₂, −λₙ)`. `twoSidedAdjEigenvalue_le_degree`:
  `λ(G) ≤ d` for a `d`-regular graph.
* `eigenvalues_mem_Icc_of_coeff_ne_zero`, the key lemma: in a regular graph a vector orthogonal
  to `𝟙` has components only along eigenvectors with eigenvalue in `[λₙ, λ₂]`, even when
  `λ₁ = d` is repeated; `abs_eigenvalues_le_twoSidedAdjEigenvalue` is the same with `|λⱼ| ≤ λ(G)`.
* `sq_dotProduct_adjMatrix_mulVec_le`: the bilinear bound `(xᵀAy)² ≤ λ(G)² · xᵀx · yᵀy` for
  `x ⟂ 𝟙` and arbitrary `y`.
* `indicator_dotProduct_adjMatrix_mulVec`: `1_Sᵀ A 1_T = e(S, T)`.
  `card_interedges_eq_add_dotProduct_centeredIndicator`: for a `d`-regular graph,
  `e(S, T) = d|S||T|/n + c_Sᵀ A c_T` with `c_S = centeredIndicator S`. Supporting facts:
  `sum_centeredIndicator`, `centeredIndicator_dotProduct_self`,
  `one_vecMul_adjMatrix_of_regular`.
* `expander_mixing_lemma`, the **expander mixing lemma** in its sharp form,
  `|e(S, T) − d|S||T|/n| ≤ λ(G) √(|S|(1 − |S|/n) · |T|(1 − |T|/n))`;
  `expander_mixing_lemma_sqrt_card_mul`, the weak form with `√(|S||T|)`;
  `IsTwoSidedSpectralExpander.expander_mixing_lemma`, the sharp form with `λ(G) ≤ lam`.
  `IsTwoSidedSpectralExpander.isSpectralExpander`: a two-sided expander with parameter `lam` has
  spectral gap at least `d − lam`.
* `card_interedges_self_le`, `le_card_interedges_self`: the one-sided bounds
  `d|S|²/n + λₙ|S|(1 − |S|/n) ≤ e(S, S) ≤ d|S|²/n + λ₂|S|(1 − |S|/n)`.
* **Hoffman's ratio bound**: `IsIndepSet.card_mul_degree_sub_smallestAdjEigenvalue_le`
  (`|S|(d − λₙ) ≤ n(−λₙ)` for an independent set `S`),
  `indepNum_mul_degree_sub_smallestAdjEigenvalue_le` (the same for `α(G)`), and
  `hoffman_ratio_bound` (`α(G) ≤ n(−λₙ)/(d − λₙ)`, for `d ≥ 1`). Supporting fact:
  `IsIndepSet.interedges_self_eq_empty`.
* **Hoffman's chromatic bound**: `Colorable.degree_sub_smallestAdjEigenvalue_le`
  (`d − λₙ ≤ k(−λₙ)` for a `k`-colourable graph),
  `Colorable.one_sub_degree_div_smallestAdjEigenvalue_le` (`1 − d/λₙ ≤ k`), and
  `hoffman_chromatic_bound` (`1 − d/λₙ ≤ χ(G)`).

## References
* N. Alon and F. R. K. Chung, *Explicit construction of linear sized tolerant networks*,
  Discrete Math. 72 (1988): the expander mixing lemma.
* R. Beigel, G. Margulis and D. Spielman, *Fault diagnosis in a small constant number of parallel
  testing rounds*, SPAA 1993: the sharp form with the factors `1 − |S|/n` and `1 − |T|/n`.
* S. Hoory, N. Linial and A. Wigderson, *Expander graphs and their applications*,
  Bull. AMS 43 (2006), Lemma 2.5; S. Vadhan, *Pseudorandomness*, Lemma 4.15.
* A. J. Hoffman, *On eigenvalues and colorings of graphs*, in *Graph Theory and its
  Applications* (1970): the chromatic bound `χ ≥ 1 − λ₁/λₙ`.
* W. H. Haemers, *Hoffman's ratio bound*, Linear Algebra Appl. (2021), arXiv:2102.05529: the
  ratio bound, which Hoffman never published.
-/

open Finset Matrix

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian)

/-! ### The smallest eigenvalue of a real symmetric matrix -/

/-- The smallest eigenvalue `λₙ` of a real symmetric matrix, counted with multiplicity: the last
entry of Mathlib's decreasingly sorted `eigenvalues₀`. The index `Fintype.card n - 1` is a
natural-number subtraction; it never truncates because `Nonempty n` makes the cardinality
positive. For a `1 × 1` matrix the smallest and the largest eigenvalue coincide. -/
noncomputable def smallestEigenvalue [Nonempty n] : ℝ :=
  hA.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos Nat.one_pos⟩

/-- The index (in Mathlib's unsorted indexing by `n`) carrying the smallest eigenvalue. When
`n` has one element it is the same index as `topIndex n`. -/
noncomputable def bottomIndex (n : Type*) [Fintype n] [Nonempty n] : n :=
  Fintype.equivOfCardEq (Fintype.card_fin _)
    (⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos Nat.one_pos⟩ : Fin (Fintype.card n))

/-- The eigenvalue at `bottomIndex n` is `λₙ`. -/
theorem eigenvalues_bottomIndex [Nonempty n] :
    hA.eigenvalues (bottomIndex n) = hA.smallestEigenvalue := by
  simp [eigenvalues, bottomIndex, smallestEigenvalue]

/-- Every eigenvalue in the eigenbasis is at least `λₙ`. -/
theorem smallestEigenvalue_le_eigenvalues [Nonempty n] (j : n) :
    hA.smallestEigenvalue ≤ hA.eigenvalues j :=
  hA.eigenvalues₀_antitone (Fin.le_iff_val_le_val.mpr (Nat.le_sub_one_of_lt (Fin.isLt _)))

/-- `λₙ ≤ λ₂`. When `n` has exactly two elements, `λₙ` and `λ₂` are the same entry of
`eigenvalues₀`, so equality holds. -/
theorem smallestEigenvalue_le_secondEigenvalue [Nontrivial n] :
    hA.smallestEigenvalue ≤ hA.secondEigenvalue := by
  have := Fintype.one_lt_card (α := n)
  exact hA.eigenvalues₀_antitone (Fin.mk_le_mk.mpr (by omega))

/-- **Lower Rayleigh bound**: `λₙ · xᵀx ≤ xᵀAx` for every vector `x`. -/
theorem smallest_mul_le_dotProduct_mulVec [Nonempty n] (x : n → ℝ) :
    hA.smallestEigenvalue * (x ⬝ᵥ x) ≤ x ⬝ᵥ A *ᵥ x := by
  rw [hA.dotProduct_mulVec_eq_sum, ← hA.sum_sq_coeff, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (hA.smallestEigenvalue_le_eigenvalues j) (sq_nonneg _)

/-- Every eigenvalue is at least `λₙ`: if `A w = μ w` with `w ≠ 0` then `λₙ ≤ μ`. -/
theorem smallest_le_of_mulVec_eq [Nonempty n] {μ : ℝ} {w : n → ℝ} (hw : w ≠ 0)
    (h : A *ᵥ w = μ • w) : hA.smallestEigenvalue ≤ μ := by
  have h1 := hA.smallest_mul_le_dotProduct_mulVec w
  rw [h, dotProduct_smul, smul_eq_mul] at h1
  exact le_of_mul_le_mul_right h1 (dotProduct_self_pos hw)

/-- `λₙ` really is an eigenvalue: it has a nonzero eigenvector. -/
theorem exists_eigenvector_smallest [Nonempty n] :
    ∃ w : n → ℝ, w ≠ 0 ∧ A *ᵥ w = hA.smallestEigenvalue • w :=
  ⟨hA.eigvec (bottomIndex n), hA.eigvec_ne_zero _, by
    rw [mulVec_eigvec, eigenvalues_bottomIndex]⟩

/-! ### The bilinear form in the eigenbasis -/

/-- The bilinear form of `A` is diagonal in the eigenbasis: `xᵀAy = Σⱼ λⱼ cⱼ(x) cⱼ(y)`. -/
theorem dotProduct_mulVec_eq_sum_coeff (x y : n → ℝ) :
    x ⬝ᵥ A *ᵥ y = ∑ j, hA.eigenvalues j * (hA.coeff x j * hA.coeff y j) := by
  rw [← hA.sum_coeff_mul_coeff x (A *ᵥ y)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_mulVec]
  ring

/-- If `λ₂ < λ₁` (the top eigenspace is a line) and `x` is orthogonal to a nonzero eigenvector
`w` for `λ₁`, then `x` has no component along the top vector of the eigenbasis. Without
`λ₂ < λ₁` this fails: the eigenbasis need not contain `w / ‖w‖`. -/
theorem coeff_topIndex_eq_zero [Nontrivial n] (hlt : hA.secondEigenvalue < hA.largestEigenvalue)
    {w : n → ℝ} (hw : w ≠ 0) (hAw : A *ᵥ w = hA.largestEigenvalue • w) {x : n → ℝ}
    (hx : x ⬝ᵥ w = 0) : hA.coeff x (topIndex n) = 0 := by
  have hcw : ∀ j, j ≠ topIndex n → hA.coeff w j = 0 := fun j hj =>
    hA.coeff_eq_zero_of_lt hAw ((hA.eigenvalues_le_secondEigenvalue hj).trans_lt hlt)
  have hcw0 : hA.coeff w (topIndex n) ≠ 0 := by
    intro h0
    refine hw (dotProduct_self_eq_zero.mp ?_)
    rw [← hA.sum_sq_coeff]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = topIndex n
    · rw [hj, h0]; ring
    · rw [hcw j hj]; ring
  have h := hA.sum_coeff_mul_coeff x w
  rw [hx, Finset.sum_eq_single (topIndex n)
    (fun j _ hj => by rw [hcw j hj, mul_zero]) (by simp)] at h
  exact (mul_eq_zero.mp h).resolve_right hcw0

end Matrix.IsHermitian

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### The smallest adjacency eigenvalue and the two-sided parameter -/

/-- The **smallest adjacency eigenvalue** `λₙ`, counted with multiplicity. It is defined for
every graph on a nonempty vertex type, regular or not. On one vertex, and more generally for an
edgeless graph, it is `0`; it is always at most `0` (`smallestAdjEigenvalue_nonpos`) and at most
`−1` once there is an edge (`smallestAdjEigenvalue_le_neg_one`). -/
noncomputable def smallestAdjEigenvalue [Nonempty V] : ℝ :=
  (G.isHermitian_adjMatrix ℝ).smallestEigenvalue

/-- `λₙ` is the last entry of the sorted spectrum `adjEigenvalues` (index `n − 1`, a
natural-number subtraction that does not truncate since `n ≥ 1`). -/
theorem smallestAdjEigenvalue_eq_adjEigenvalues [Nonempty V] :
    G.smallestAdjEigenvalue
      = G.adjEigenvalues ⟨Fintype.card V - 1, Nat.sub_lt Fintype.card_pos Nat.one_pos⟩ := rfl

/-- `λₙ ≤ λ₂`, for every graph on at least two vertices. On exactly two vertices `λₙ` and `λ₂`
are the same entry of the sorted spectrum. -/
theorem smallestAdjEigenvalue_le_secondAdjEigenvalue [Nontrivial V] :
    G.smallestAdjEigenvalue ≤ G.secondAdjEigenvalue :=
  (G.isHermitian_adjMatrix ℝ).smallestEigenvalue_le_secondEigenvalue

/-- The **two-sided spectral parameter** `λ(G) = max(|λ₂|, |λₙ|)`.

For a `d`-regular graph this is the largest absolute value of an eigenvalue other than the
trivial `λ₁ = d` (counted once), and it lies in `[0, d]` (`twoSidedAdjEigenvalue_nonneg`,
`twoSidedAdjEigenvalue_le_degree`). It equals `d` exactly when `λ₂ = d` or `λₙ = −d`, which by
standard facts (not proved in this file) means that `G` is disconnected or has a bipartite
component. Edge cases: `λ(K₂) = 1` (there `λ₂ = λₙ = −1`), and `λ(G) = 0` for an edgeless graph
(`d = 0`), where all eigenvalues vanish. The quantity is defined for every graph on at least two
vertices (`λ₂` needs `Nontrivial V`; there is no junk value for `n ≤ 1`, the definition simply
does not apply), but for an irregular graph `λ₁` is not the degree and `λ(G)` does not have
this meaning. -/
noncomputable def twoSidedAdjEigenvalue [Nontrivial V] : ℝ :=
  max |G.secondAdjEigenvalue| |G.smallestAdjEigenvalue|

/-- `G` is a **two-sided `d`-regular spectral expander with parameter `lam`** (an
`(n, d, lam)`-graph): `G` is `d`-regular and every eigenvalue other than the trivial `λ₁ = d`
has absolute value at most `lam`, i.e. `λ(G) ≤ lam`.

Unlike `IsSpectralExpander d δ`, which bounds the *gap* `d − λ₂` from below, the parameter here
is an *upper bound* on `λ(G)`; `IsTwoSidedSpectralExpander.isSpectralExpander` converts. The
definition never holds for `lam < 0`, since `λ(G) ≥ 0`, and every `d`-regular graph satisfies it
for every `lam ≥ d` (`twoSidedAdjEigenvalue_le_degree`). It needs `n ≥ 2` (`Nontrivial V`). -/
def IsTwoSidedSpectralExpander [Nontrivial V] (d : ℕ) (lam : ℝ) : Prop :=
  G.IsRegularOfDegree d ∧ G.twoSidedAdjEigenvalue ≤ lam

/-- `λ(G) ≥ 0`, being a maximum of absolute values. -/
theorem twoSidedAdjEigenvalue_nonneg [Nontrivial V] : 0 ≤ G.twoSidedAdjEigenvalue :=
  le_max_of_le_left (abs_nonneg _)

/-- `λₙ ≤ 0` for every graph on a nonempty vertex type (test vector: a coordinate vector, on
which the quadratic form vanishes because the graph has no loops). -/
theorem smallestAdjEigenvalue_nonpos [Nonempty V] : G.smallestAdjEigenvalue ≤ 0 := by
  have h := (G.isHermitian_adjMatrix ℝ).smallest_mul_le_dotProduct_mulVec
    (Pi.single (Classical.arbitrary V) (1 : ℝ))
  simp only [single_dotProduct, Pi.single_eq_same, mul_one, mulVec_single_one,
    adjMatrix_apply, col_apply] at h
  simpa [smallestAdjEigenvalue] using h

/-- The two-sided parameter is `max(λ₂, −λₙ)`: no absolute values are needed, because
`λₙ ≤ 0` and `λₙ ≤ λ₂`. -/
theorem twoSidedAdjEigenvalue_eq_max [Nontrivial V] :
    G.twoSidedAdjEigenvalue = max G.secondAdjEigenvalue (-G.smallestAdjEigenvalue) := by
  have h1 := G.smallestAdjEigenvalue_nonpos
  have h2 := G.smallestAdjEigenvalue_le_secondAdjEigenvalue
  rw [twoSidedAdjEigenvalue, abs_of_nonpos h1]
  rcases le_or_gt 0 G.secondAdjEigenvalue with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, max_eq_right (by linarith), max_eq_right (by linarith)]

/-- `1_Sᵀ A 1_T = e(S, T)`: the adjacency bilinear form on two indicator vectors counts the
ordered adjacent pairs in `S × T` (so an edge inside `S ∩ T` is counted twice). -/
theorem indicator_dotProduct_adjMatrix_mulVec (S T : Finset V) :
    (fun v => if v ∈ S then (1 : ℝ) else 0) ⬝ᵥ
        G.adjMatrix ℝ *ᵥ (fun v => if v ∈ T then (1 : ℝ) else 0)
      = #(G.interedges S T) := by
  rw [interedges_def, Finset.card_filter, Finset.sum_product]
  push_cast
  simp only [dotProduct, mulVec, adjMatrix_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter]

variable {G} {d : ℕ}

/-- `λₙ ≤ −1` for every graph with at least one edge `u ~ v`; no regularity is needed (test
vector `e_u − e_v`). -/
theorem smallestAdjEigenvalue_le_neg_one [Nonempty V] {u v : V} (h : G.Adj u v) :
    G.smallestAdjEigenvalue ≤ -1 := by
  have huv : u ≠ v := h.ne
  let x : V → ℝ := Pi.single u 1 - Pi.single v 1
  have hx := (G.isHermitian_adjMatrix ℝ).smallest_mul_le_dotProduct_mulVec x
  have h1 : x ⬝ᵥ x = 2 := by
    simp [x, dotProduct_sub, huv, huv.symm]; norm_num
  have h2 : x ⬝ᵥ G.adjMatrix ℝ *ᵥ x = -2 := by
    simp [x, mulVec_sub, sub_dotProduct, dotProduct_sub, single_dotProduct, adjMatrix_apply, h,
      h.symm]; norm_num
  rw [h1, h2] at hx
  change G.smallestAdjEigenvalue * 2 ≤ -2 at hx
  linarith

/-- `λ(G) ≥ 1` for every graph with at least one edge (since `λₙ ≤ −1`); no regularity is
needed. For an edgeless graph `λ(G) = 0`. -/
theorem one_le_twoSidedAdjEigenvalue [Nontrivial V] {u v : V} (h : G.Adj u v) :
    1 ≤ G.twoSidedAdjEigenvalue := by
  have h1 := smallestAdjEigenvalue_le_neg_one h
  refine le_max_of_le_right ?_
  rw [abs_of_neg (by linarith)]
  linarith

/-- `λ(G) ≤ d` for a `d`-regular graph: every adjacency eigenvalue lies in `[−d, d]`. -/
theorem twoSidedAdjEigenvalue_le_degree [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    G.twoSidedAdjEigenvalue ≤ d := by
  obtain ⟨f, hf, -, hAf⟩ := exists_eigenvector_secondAdjEigenvalue hd
  obtain ⟨w, hw, hAw⟩ := (G.isHermitian_adjMatrix ℝ).exists_eigenvector_smallest
  exact max_le (abs_le_of_adjMatrix_mulVec_eq hd hf hAf) (abs_le_of_adjMatrix_mulVec_eq hd hw hAw)

/-! ### Vectors orthogonal to the constants -/

/-- **Key lemma.** In a `d`-regular graph, a vector `x` with `Σ x_v = 0` has a nonzero
component `cⱼ(x)` only along eigenvectors whose eigenvalue lies in `[λₙ, λ₂]`.

The point is that Mathlib's eigenbasis need not contain `𝟙/√n` when `λ₁ = d` is repeated (a
disconnected graph); in that case `λ₂ = λ₁` and the top index is harmless. `d = 0` is allowed. -/
theorem eigenvalues_mem_Icc_of_coeff_ne_zero [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {x : V → ℝ} (hx : ∑ v, x v = 0) {j : V} (hj : (G.isHermitian_adjMatrix ℝ).coeff x j ≠ 0) :
    (G.isHermitian_adjMatrix ℝ).eigenvalues j ∈
      Set.Icc G.smallestAdjEigenvalue G.secondAdjEigenvalue := by
  refine ⟨(G.isHermitian_adjMatrix ℝ).smallestEigenvalue_le_eigenvalues j, ?_⟩
  by_cases hjt : j = Matrix.IsHermitian.topIndex V
  · rcases (G.isHermitian_adjMatrix ℝ).secondEigenvalue_le_largestEigenvalue.eq_or_lt
      with heq | hlt
    · rw [hjt, Matrix.IsHermitian.eigenvalues_topIndex]
      exact heq.symm.le
    · exfalso
      have h1 : (1 : V → ℝ) ≠ 0 := fun h => one_ne_zero (congrFun h (Classical.arbitrary V))
      have hA1 : G.adjMatrix ℝ *ᵥ (1 : V → ℝ)
          = (G.isHermitian_adjMatrix ℝ).largestEigenvalue • (1 : V → ℝ) := by
        rw [adjMatrix_mulVec_one_of_regular hd]
        exact congrArg (· • (1 : V → ℝ)) (largestAdjEigenvalue_eq hd).symm
      refine hj ?_
      rw [hjt]
      exact (G.isHermitian_adjMatrix ℝ).coeff_topIndex_eq_zero hlt h1 hA1
        (by rw [dotProduct_one, hx])
  · exact (G.isHermitian_adjMatrix ℝ).eigenvalues_le_secondEigenvalue hjt

/-- In a `d`-regular graph, every eigenvalue along which a vector `x ⟂ 𝟙` has a nonzero
component has absolute value at most `λ(G)`. -/
theorem abs_eigenvalues_le_twoSidedAdjEigenvalue [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {x : V → ℝ} (hx : ∑ v, x v = 0) {j : V} (hj : (G.isHermitian_adjMatrix ℝ).coeff x j ≠ 0) :
    |(G.isHermitian_adjMatrix ℝ).eigenvalues j| ≤ G.twoSidedAdjEigenvalue := by
  have hmem := eigenvalues_mem_Icc_of_coeff_ne_zero hd hx hj
  exact (abs_le_max_abs_abs hmem.1 hmem.2).trans (max_comm _ _).le

/-- **Bilinear bound.** In a `d`-regular graph, if `Σ x_v = 0` then for *every* `y`,
`(xᵀAy)² ≤ λ(G)² · xᵀx · yᵀy`. Only `x` has to be orthogonal to `𝟙`. -/
theorem sq_dotProduct_adjMatrix_mulVec_le [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {x : V → ℝ} (hx : ∑ v, x v = 0) (y : V → ℝ) :
    (x ⬝ᵥ G.adjMatrix ℝ *ᵥ y) ^ 2 ≤ G.twoSidedAdjEigenvalue ^ 2 * (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  set hA := G.isHermitian_adjMatrix ℝ
  have hterm : ∀ j, (hA.eigenvalues j * hA.coeff x j) ^ 2
      ≤ G.twoSidedAdjEigenvalue ^ 2 * hA.coeff x j ^ 2 := by
    intro j
    by_cases hj : hA.coeff x j = 0
    · simp [hj]
    · have habs := abs_eigenvalues_le_twoSidedAdjEigenvalue hd hx hj
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (sq_le_sq' (abs_le.mp habs).1 (abs_le.mp habs).2) (sq_nonneg _)
  rw [hA.dotProduct_mulVec_eq_sum_coeff]
  calc (∑ j, hA.eigenvalues j * (hA.coeff x j * hA.coeff y j)) ^ 2
      = (∑ j, (hA.eigenvalues j * hA.coeff x j) * hA.coeff y j) ^ 2 := by simp_rw [mul_assoc]
    _ ≤ (∑ j, (hA.eigenvalues j * hA.coeff x j) ^ 2) * ∑ j, hA.coeff y j ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ j, G.twoSidedAdjEigenvalue ^ 2 * hA.coeff x j ^ 2) * ∑ j, hA.coeff y j ^ 2 :=
        mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ => hterm j)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = G.twoSidedAdjEigenvalue ^ 2 * (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
        rw [← Finset.mul_sum, hA.sum_sq_coeff, hA.sum_sq_coeff, mul_assoc]

/-! ### Centered indicator vectors -/

/-- The **centered indicator** of `S`: `1_S − (|S|/n) 𝟙`, the indicator of `S` shifted to be
orthogonal to the constants (`sum_centeredIndicator`). On an empty vertex type the division
`|S|/0` is the junk value `0`, which is why the lemmas about it assume `Nonempty V`. -/
noncomputable def centeredIndicator (S : Finset V) : V → ℝ :=
  fun v => (if v ∈ S then (1 : ℝ) else 0) - #S / Fintype.card V

/-- The centered indicator is orthogonal to the constants: `Σ_v (1_S − (|S|/n) 𝟙)_v = 0`. -/
theorem sum_centeredIndicator [Nonempty V] (S : Finset V) : ∑ v, centeredIndicator S v = 0 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [centeredIndicator, Finset.sum_sub_distrib, Finset.sum_const, card_univ, nsmul_eq_mul]
  simp
  field_simp
  ring

/-- `‖1_S − (|S|/n) 𝟙‖² = |S| (1 − |S|/n)`. -/
theorem centeredIndicator_dotProduct_self [Nonempty V] (S : Finset V) :
    centeredIndicator S ⬝ᵥ centeredIndicator S = #S * (1 - (#S : ℝ) / Fintype.card V) := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hterm : ∀ v, centeredIndicator S v * centeredIndicator S v
      = (if v ∈ S then (1 : ℝ) else 0) * (1 - 2 * (#S / Fintype.card V))
        + (#S / Fintype.card V : ℝ) ^ 2 := by
    intro v
    by_cases hv : v ∈ S <;> simp [centeredIndicator, hv] <;> ring
  simp only [dotProduct, hterm, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    card_univ, nsmul_eq_mul]
  simp
  field_simp
  ring

private theorem card_mul_one_sub_card_div_nonneg [Nonempty V] (S : Finset V) :
    0 ≤ (#S : ℝ) * (1 - (#S : ℝ) / Fintype.card V) := by
  rw [← centeredIndicator_dotProduct_self]
  exact Finset.sum_nonneg fun v _ => mul_self_nonneg _

omit [DecidableEq V] in
/-- `𝟙ᵀ A = d 𝟙ᵀ` for a `d`-regular graph. -/
theorem one_vecMul_adjMatrix_of_regular (hd : G.IsRegularOfDegree d) :
    (1 : V → ℝ) ᵥ* G.adjMatrix ℝ = (d : ℝ) • (1 : V → ℝ) := by
  ext v
  simp [hd v]

/-- The decomposition behind the mixing lemma: in a `d`-regular graph on a nonempty vertex type,
`e(S, T) = d|S||T|/n + (1_S − (|S|/n)𝟙)ᵀ A (1_T − (|T|/n)𝟙)`. -/
theorem card_interedges_eq_add_dotProduct_centeredIndicator [Nonempty V]
    (hd : G.IsRegularOfDegree d) (S T : Finset V) :
    (#(G.interedges S T) : ℝ)
      = d * #S * #T / Fintype.card V
        + centeredIndicator S ⬝ᵥ G.adjMatrix ℝ *ᵥ centeredIndicator T := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hS : (fun v => if v ∈ S then (1 : ℝ) else 0)
      = centeredIndicator S + ((#S : ℝ) / Fintype.card V) • (1 : V → ℝ) := by
    ext v; simp [centeredIndicator]
  have hT : (fun v => if v ∈ T then (1 : ℝ) else 0)
      = centeredIndicator T + ((#T : ℝ) / Fintype.card V) • (1 : V → ℝ) := by
    ext v; simp [centeredIndicator]
  have h1 : centeredIndicator S ⬝ᵥ G.adjMatrix ℝ *ᵥ (1 : V → ℝ) = 0 := by
    rw [adjMatrix_mulVec_one_of_regular hd, dotProduct_smul, dotProduct_one,
      sum_centeredIndicator, smul_zero]
  have h2 : (1 : V → ℝ) ⬝ᵥ G.adjMatrix ℝ *ᵥ centeredIndicator T = 0 := by
    rw [dotProduct_mulVec, one_vecMul_adjMatrix_of_regular hd, smul_dotProduct, one_dotProduct,
      sum_centeredIndicator, smul_zero]
  have h3 : (1 : V → ℝ) ⬝ᵥ G.adjMatrix ℝ *ᵥ (1 : V → ℝ) = d * Fintype.card V := by
    rw [adjMatrix_mulVec_one_of_regular hd, dotProduct_smul, dotProduct_one]
    simp
  rw [← indicator_dotProduct_adjMatrix_mulVec, hS, hT]
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, h1, h2, h3]
  field_simp
  ring

/-! ### The expander mixing lemma -/

/-- **Expander mixing lemma**, sharp form (Alon–Chung; Beigel–Margulis–Spielman). For a
`d`-regular graph on `n ≥ 2` vertices and any vertex sets `S`, `T`,
`|e(S, T) − d|S||T|/n| ≤ λ(G) · √(|S|(1 − |S|/n) · |T|(1 − |T|/n))`,
where `e(S, T) = #(G.interedges S T)` counts ordered adjacent pairs in `S × T` (edges inside
`S ∩ T` count twice) and `λ(G) = max(|λ₂|, |λₙ|)`.

`S` and `T` are arbitrary: they may overlap, be empty, or be all of `V`. If `S` or `T` is empty
or everything, both sides are `0`; for `d = 0` also `λ(G) = 0` and both sides are `0`. The
argument of the square root is a product of two nonnegative numbers, so `Real.sqrt` is never
applied to a negative number. `n ≥ 2` (`Nontrivial V`) is needed only because `λ₂` is; the
division by `n` is then genuine. -/
theorem expander_mixing_lemma [Nontrivial V] (hd : G.IsRegularOfDegree d) (S T : Finset V) :
    |(#(G.interedges S T) : ℝ) - d * #S * #T / Fintype.card V|
      ≤ G.twoSidedAdjEigenvalue * Real.sqrt ((#S * (1 - (#S : ℝ) / Fintype.card V))
          * (#T * (1 - (#T : ℝ) / Fintype.card V))) := by
  rw [card_interedges_eq_add_dotProduct_centeredIndicator hd S T, add_sub_cancel_left]
  have h := sq_dotProduct_adjMatrix_mulVec_le hd (sum_centeredIndicator S) (centeredIndicator T)
  rw [centeredIndicator_dotProduct_self S, centeredIndicator_dotProduct_self T, mul_assoc] at h
  calc _ ≤ Real.sqrt (G.twoSidedAdjEigenvalue ^ 2 * ((#S * (1 - (#S : ℝ) / Fintype.card V))
          * (#T * (1 - (#T : ℝ) / Fintype.card V)))) := Real.abs_le_sqrt h
    _ = _ := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq G.twoSidedAdjEigenvalue_nonneg]

/-- **Expander mixing lemma**, the usual weak form: for a `d`-regular graph on `n ≥ 2` vertices
and any vertex sets `S`, `T`, `|e(S, T) − d|S||T|/n| ≤ λ(G) · √(|S||T|)`, with `e(S, T)`
counting ordered adjacent pairs. It follows from the sharp form `expander_mixing_lemma` by
dropping the factors `1 − |S|/n, 1 − |T|/n ∈ [0, 1]`. -/
theorem expander_mixing_lemma_sqrt_card_mul [Nontrivial V] (hd : G.IsRegularOfDegree d)
    (S T : Finset V) :
    |(#(G.interedges S T) : ℝ) - d * #S * #T / Fintype.card V|
      ≤ G.twoSidedAdjEigenvalue * Real.sqrt (#S * #T) := by
  refine (expander_mixing_lemma hd S T).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) G.twoSidedAdjEigenvalue_nonneg)
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hs : (#S : ℝ) * (1 - (#S : ℝ) / Fintype.card V) ≤ #S := by
    have : 0 ≤ (#S : ℝ) * (#S / Fintype.card V) := by positivity
    nlinarith
  have ht : (#T : ℝ) * (1 - (#T : ℝ) / Fintype.card V) ≤ #T := by
    have : 0 ≤ (#T : ℝ) * (#T / Fintype.card V) := by positivity
    nlinarith
  exact mul_le_mul hs ht (card_mul_one_sub_card_div_nonneg T) (Nat.cast_nonneg _)

/-- The mixing lemma for an `(n, d, lam)`-graph: the bound of `expander_mixing_lemma` with
`λ(G)` replaced by any upper bound `lam`. -/
theorem IsTwoSidedSpectralExpander.expander_mixing_lemma [Nontrivial V] {lam : ℝ}
    (h : G.IsTwoSidedSpectralExpander d lam) (S T : Finset V) :
    |(#(G.interedges S T) : ℝ) - d * #S * #T / Fintype.card V|
      ≤ lam * Real.sqrt ((#S * (1 - (#S : ℝ) / Fintype.card V))
          * (#T * (1 - (#T : ℝ) / Fintype.card V))) :=
  (SimpleGraph.expander_mixing_lemma h.1 S T).trans
    (mul_le_mul_of_nonneg_right h.2 (Real.sqrt_nonneg _))

/-- A two-sided expander with parameter `lam` is a one-sided spectral expander with gap
`d − lam`, since `λ₂ ≤ |λ₂| ≤ λ(G) ≤ lam`. -/
theorem IsTwoSidedSpectralExpander.isSpectralExpander [Nontrivial V] {lam : ℝ}
    (h : G.IsTwoSidedSpectralExpander d lam) : G.IsSpectralExpander d (d - lam) := by
  refine ⟨h.1, ?_⟩
  rw [spectralGap_eq h.1]
  have : G.secondAdjEigenvalue ≤ lam := (le_abs_self _).trans ((le_max_left _ _).trans h.2)
  linarith

/-- One-sided upper bound on the edges inside a set: for a `d`-regular graph on `n ≥ 2`
vertices, `e(S, S) ≤ d|S|²/n + λ₂ · |S|(1 − |S|/n)`, where `e(S, S)` is twice the number of
edges inside `S`. Holds for every `S`, including `∅` and `V` (where both sides are `0` and `dn`). -/
theorem card_interedges_self_le [Nontrivial V] (hd : G.IsRegularOfDegree d) (S : Finset V) :
    (#(G.interedges S S) : ℝ) ≤ d * #S ^ 2 / Fintype.card V
      + G.secondAdjEigenvalue * (#S * (1 - (#S : ℝ) / Fintype.card V)) := by
  rw [card_interedges_eq_add_dotProduct_centeredIndicator hd S S,
    ← centeredIndicator_dotProduct_self]
  have := dotProduct_adjMatrix_mulVec_le hd (sum_centeredIndicator S)
  have e : (d : ℝ) * #S * #S / Fintype.card V = d * #S ^ 2 / Fintype.card V := by ring
  linarith

/-- One-sided lower bound on the edges inside a set: for a `d`-regular graph on a nonempty
vertex type, `d|S|²/n + λₙ · |S|(1 − |S|/n) ≤ e(S, S)`, where `e(S, S)` is twice the number of
edges inside `S`. Holds for every `S`, and also on one vertex (`n = 1`, where `d = 0`). -/
theorem le_card_interedges_self [Nonempty V] (hd : G.IsRegularOfDegree d) (S : Finset V) :
    d * #S ^ 2 / Fintype.card V + G.smallestAdjEigenvalue * (#S * (1 - (#S : ℝ) / Fintype.card V))
      ≤ #(G.interedges S S) := by
  rw [card_interedges_eq_add_dotProduct_centeredIndicator hd S S,
    ← centeredIndicator_dotProduct_self]
  have := (G.isHermitian_adjMatrix ℝ).smallest_mul_le_dotProduct_mulVec (centeredIndicator S)
  change G.smallestAdjEigenvalue * _ ≤ _ at this
  have e : (d : ℝ) * #S * #S / Fintype.card V = d * #S ^ 2 / Fintype.card V := by ring
  linarith

/-! ### Hoffman's bounds -/

omit [Fintype V] [DecidableEq V] in
/-- An independent set spans no ordered adjacent pairs: `e(S, S) = 0`. -/
theorem IsIndepSet.interedges_self_eq_empty {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    G.interedges S S = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  rintro ⟨u, v⟩ he
  rw [mem_interedges_iff] at he
  exact hS (Finset.mem_coe.mpr he.1) (Finset.mem_coe.mpr he.2.1) he.2.2.ne he.2.2

/-- **Hoffman's ratio bound**, for one independent set, in multiplicative form: in a `d`-regular
graph on `n ≥ 1` vertices every independent set `S` satisfies `|S| (d − λₙ) ≤ n (−λₙ)`.

The multiplicative form needs no case split: for `S = ∅` it reads `0 ≤ n(−λₙ)`, true because
`λₙ ≤ 0`, and for `d = 0` (where `λₙ = 0`) it reads `0 ≤ 0`. See `hoffman_ratio_bound` for the
quotient form `α(G) ≤ n(−λₙ)/(d − λₙ)`, which needs `d ≥ 1`. -/
theorem IsIndepSet.card_mul_degree_sub_smallestAdjEigenvalue_le [Nonempty V]
    (hd : G.IsRegularOfDegree d) {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    (#S : ℝ) * (d - G.smallestAdjEigenvalue) ≤ Fintype.card V * (-G.smallestAdjEigenvalue) := by
  have h := le_card_interedges_self hd S
  rw [hS.interedges_self_eq_empty, Finset.card_empty, Nat.cast_zero] at h
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hl := G.smallestAdjEigenvalue_nonpos
  set s : ℝ := (#S : ℝ)
  set N : ℝ := (Fintype.card V : ℝ)
  set l := G.smallestAdjEigenvalue
  -- `h : d s² / N + l s (1 − s / N) ≤ 0`; multiply by `N`.
  have h' : s * (s * (d - l) - N * (-l)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_left h hn.le
    field_simp at this
    nlinarith
  rcases (show (0 : ℝ) ≤ s from Nat.cast_nonneg _).eq_or_lt with h0 | hpos
  · rw [← h0]; nlinarith
  · nlinarith

/-- **Hoffman's ratio bound** in multiplicative form: for a `d`-regular graph on `n ≥ 1`
vertices, `α(G) (d − λₙ) ≤ n (−λₙ)`. Valid for every `d`, including `d = 0`, where it reads
`0 ≤ 0`. -/
theorem indepNum_mul_degree_sub_smallestAdjEigenvalue_le [Nonempty V]
    (hd : G.IsRegularOfDegree d) :
    (G.indepNum : ℝ) * (d - G.smallestAdjEigenvalue)
      ≤ Fintype.card V * (-G.smallestAdjEigenvalue) := by
  obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
  rw [← hS.card_eq]
  exact hS.isIndepSet.card_mul_degree_sub_smallestAdjEigenvalue_le hd

/-- **Hoffman's ratio bound**: for a `d`-regular graph on `n` vertices with `d ≥ 1`, the
independence number satisfies `α(G) ≤ n (−λₙ) / (d − λₙ)`.

The hypothesis `d ≥ 1` makes the denominator positive (`d − λₙ ≥ d`). It cannot be dropped:
for `d = 0` the graph is edgeless, `λₙ = 0`, the quotient is the junk value `0 / 0 = 0`, and
`α(G) = n` violates the bound. `indepNum_mul_degree_sub_smallestAdjEigenvalue_le` is the
multiplicative form, valid for every `d`. `Nonempty V` is needed to define `λₙ`; it does not
follow from the other hypotheses, since on an empty vertex type every graph is vacuously
`d`-regular for every `d`. -/
theorem hoffman_ratio_bound [Nonempty V] (hd : G.IsRegularOfDegree d) (hd0 : 0 < d) :
    (G.indepNum : ℝ)
      ≤ Fintype.card V * (-G.smallestAdjEigenvalue) / (d - G.smallestAdjEigenvalue) := by
  have hpos : (0 : ℝ) < d - G.smallestAdjEigenvalue := by
    have h1 := G.smallestAdjEigenvalue_nonpos
    have h2 : (0 : ℝ) < d := by exact_mod_cast hd0
    linarith
  rw [le_div_iff₀ hpos]
  exact indepNum_mul_degree_sub_smallestAdjEigenvalue_le hd

/-- **Hoffman's chromatic bound** in multiplicative form: a `k`-colourable `d`-regular graph on
`n ≥ 1` vertices satisfies `d − λₙ ≤ k (−λₙ)`. (Each colour class is independent; sum the ratio
bound over the classes.) For `d = 0` it reads `0 ≤ 0`; `k = 0` is impossible on a nonempty
vertex type. -/
theorem Colorable.degree_sub_smallestAdjEigenvalue_le [Nonempty V] (hd : G.IsRegularOfDegree d)
    {k : ℕ} (hc : G.Colorable k) :
    (d : ℝ) - G.smallestAdjEigenvalue ≤ k * (-G.smallestAdjEigenvalue) := by
  obtain ⟨C⟩ := hc
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hind : ∀ c : Fin k, G.IsIndepSet ((univ.filter fun v => C v = c : Finset V) : Set V) := by
    intro c u hu v hv _ hadj
    simp only [coe_filter, mem_univ, true_and] at hu hv
    exact C.valid hadj (hu.trans hv.symm)
  have hsum : (Fintype.card V : ℝ) = ∑ c : Fin k, (#(univ.filter fun v => C v = c) : ℝ) := by
    rw [← card_univ, Finset.card_eq_sum_card_fiberwise (f := C) (t := univ)
      (fun _ _ => mem_univ _)]
    push_cast
    rfl
  have key : (∑ c : Fin k, (#(univ.filter fun v => C v = c) : ℝ)) * (d - G.smallestAdjEigenvalue)
      ≤ k * (Fintype.card V * (-G.smallestAdjEigenvalue)) := by
    rw [Finset.sum_mul]
    calc ∑ c : Fin k, (#(univ.filter fun v => C v = c) : ℝ) * (d - G.smallestAdjEigenvalue)
        ≤ ∑ _c : Fin k, (Fintype.card V : ℝ) * (-G.smallestAdjEigenvalue) :=
          Finset.sum_le_sum fun c _ =>
            (hind c).card_mul_degree_sub_smallestAdjEigenvalue_le hd
      _ = k * (Fintype.card V * (-G.smallestAdjEigenvalue)) := by simp
  rw [← hsum] at key
  nlinarith

/-- **Hoffman's chromatic bound** in quotient form: a `k`-colourable `d`-regular graph on a
nonempty vertex type satisfies `1 − d/λₙ ≤ k`.

No hypothesis on `d` is needed. If `λₙ < 0` this is the multiplicative form divided by `−λₙ`.
If `λₙ = 0` (for a regular graph this happens exactly when `d = 0`, by
`smallestAdjEigenvalue_le_neg_one`), `d / λₙ` is the junk value `d / 0 = 0` and the statement
reads `1 ≤ k`, true because a nonempty vertex type needs at least one colour. -/
theorem Colorable.one_sub_degree_div_smallestAdjEigenvalue_le [Nonempty V]
    (hd : G.IsRegularOfDegree d) {k : ℕ} (hc : G.Colorable k) :
    1 - (d : ℝ) / G.smallestAdjEigenvalue ≤ k := by
  have h := hc.degree_sub_smallestAdjEigenvalue_le hd
  rcases G.smallestAdjEigenvalue_nonpos.eq_or_lt with h0 | hneg
  · obtain ⟨C⟩ := hc
    have hk : 1 ≤ k := (C (Classical.arbitrary V)).pos
    rw [h0, div_zero, sub_zero]
    exact_mod_cast hk
  · have hl0 : G.smallestAdjEigenvalue ≠ 0 := hneg.ne
    have e : 1 - (d : ℝ) / G.smallestAdjEigenvalue
        = (d - G.smallestAdjEigenvalue) / (-G.smallestAdjEigenvalue) := by
      field_simp
      ring
    rw [e, div_le_iff₀ (neg_pos.mpr hneg)]
    exact h

/-- **Hoffman's chromatic bound**: for a `d`-regular graph on a nonempty finite vertex type,
`χ(G) ≥ 1 − d/λₙ`, i.e. `1 − λ₁/λₙ ≤ χ(G)` since `λ₁ = d`.

The chromatic number `G.chromaticNumber` is an extended natural number; on a finite vertex type
it is finite, so `ENat.toNat` loses nothing here (it would send `⊤` to `0`). For `d = 0` the
quotient `d / λₙ` is the junk value `0 / 0 = 0` and the bound reads `1 ≤ χ(G)`, which holds. -/
theorem hoffman_chromatic_bound [Nonempty V] (hd : G.IsRegularOfDegree d) :
    1 - (d : ℝ) / G.smallestAdjEigenvalue ≤ G.chromaticNumber.toNat :=
  G.colorable_chromaticNumber_of_fintype.one_sub_degree_div_smallestAdjEigenvalue_le hd

end SimpleGraph
