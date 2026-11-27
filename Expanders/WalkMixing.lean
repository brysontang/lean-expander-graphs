/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.TwoSided

/-!
# Walk counts, Chung's diameter bound and mixing of the random walk

Let `G` be a `d`-regular graph on `n ≥ 2` vertices with adjacency matrix `A`, second eigenvalue
`λ₂` and two-sided parameter `λ = λ(G) = max(|λ₂|, |λₙ|)` (`SimpleGraph.twoSidedAdjEigenvalue`
from `Expanders/TwoSided.lean`). The entry `(Aʳ) u v` counts the walks of length `r` from `u` to
`v` (`SimpleGraph.adjMatrix_pow_apply_eq_card_walk`), and there are `dʳ` walks of length `r`
from each vertex. This file shows that the walk counts are close to uniform, `(Aʳ) u v ≈ dʳ/n`,
with an error controlled by `λʳ`, and draws the classical consequences: Chung's diameter bound
and the `L²` and total-variation mixing of the random walk.

For the lazy matrix `A + d·1` (`2d` times the lazy random walk `(1 + A/d)/2`) all eigenvalues
are shifted into `[0, 2d]`, so the error is controlled by the one-sided quantity `d + λ₂`; this
gives a diameter bound that also applies to bipartite graphs.

Throughout, `n = Fintype.card V` is cast to `ℝ`, so `n − 1` is real subtraction and never
truncates; every division by `n` is genuine because `n ≥ 2`.

## Definitions
This file introduces no new definitions. It uses `SimpleGraph.secondAdjEigenvalue`
(`Expanders/Basic.lean`), `SimpleGraph.smallestAdjEigenvalue`,
`SimpleGraph.twoSidedAdjEigenvalue` and `SimpleGraph.centeredIndicator`
(`Expanders/TwoSided.lean`), and Mathlib's `SimpleGraph.dist` and `SimpleGraph.diam`.

## Theorems (all proved here)
Walk counts (namespace `SimpleGraph`):
* `abs_adjMatrix_pow_apply_sub_le`: `|(Aʳ) u v − dʳ/n| ≤ λʳ (1 − 1/n)` for all `r`, `u`, `v`.
* `abs_adjMatrix_add_degree_pow_apply_sub_le`: the lazy version
  `|((A + d·1)ʳ) u v − (2d)ʳ/n| ≤ (d + λ₂)ʳ (1 − 1/n)`;
  `degree_add_secondAdjEigenvalue_nonneg`: `0 ≤ d + λ₂`.

Diameter:
* `exists_walk_length_eq_of_mul_twoSidedAdjEigenvalue_pow_lt`: if `(n − 1) λʳ < dʳ`, every
  ordered pair of vertices is joined by a walk of length exactly `r`;
  `connected_and_diam_le_of_mul_twoSidedAdjEigenvalue_pow_lt`: then `G` is connected,
  `dist u v ≤ r` and `diam G ≤ r`.
* `connected_and_diam_le_of_mul_degree_add_secondAdjEigenvalue_pow_lt`: if
  `(n − 1)(d + λ₂)ʳ < (2d)ʳ`, then `G` is connected, `dist u v ≤ r` and `diam G ≤ r`.
* `exists_walk_length_eq_floor_log_add_one` and
  `connected_and_diam_le_floor_log_twoSidedAdjEigenvalue`, **Chung's diameter bound**: if
  `λ < d`, every ordered pair is joined by a walk of length exactly `⌊log(n − 1)/log(d/λ)⌋ + 1`,
  so `G` is connected and `diam G ≤ ⌊log(n − 1)/log(d/λ)⌋ + 1`.
* `connected_and_diam_le_floor_log_secondAdjEigenvalue`, the lazy (one-sided) form: if `λ₂ < d`,
  `G` is connected and `diam G ≤ ⌊log(n − 1)/log(2d/(d + λ₂))⌋ + 1`.

Mixing:
* `dotProduct_self_adjMatrix_pow_mulVec_sub_le`, **`L²` mixing**: with `m = (Σ x)/n`,
  `‖Aᵗx − dᵗ m 𝟙‖² ≤ λ^{2t} ‖x − m 𝟙‖²`.
* `sum_abs_adjMatrix_pow_mulVec_sub_le`, **`L¹` (total-variation) mixing**: for a probability
  vector `p`, `Σ_v |(Aᵗp) v − dᵗ/n| ≤ √(n − 1) λᵗ`.
* `sum_abs_randomWalk_pow_mulVec_sub_le`: the same for the random walk `P = A/d` (for `d ≥ 1`),
  `Σ_v |(Pᵗp) v − 1/n| ≤ √(n − 1) (λ/d)ᵗ`; the total-variation distance to the uniform
  distribution is half the left-hand side.

The proofs work in the eigenbasis of `A`: `(A + c·1)ʳ` multiplies the coefficient along the
`j`-th eigenvector by `(λⱼ + c)ʳ`, and a vector orthogonal to `𝟙` only has coefficients along
eigenvalues in `[λₙ, λ₂]` (`SimpleGraph.eigenvalues_mem_Icc_of_coeff_ne_zero`), even when
`λ₁ = d` is repeated. These linear-algebra steps are private lemmas of this file.

## Sharpness
* The strict inequalities in the hypotheses cannot be weakened. For the exact-length walk
  statement `exists_walk_length_eq_of_mul_twoSidedAdjEigenvalue_pow_lt`, equality holds and the
  conclusion fails for `Kₙ` at `r = 1` (no closed walk of length `1`) and for `K₂` at every `r`
  (no closed walk of odd length, and no walk of even length between its two vertices). The
  diameter statements hold for `Kₙ` at `r = 1` and for `K₂` at `r ≥ 1` even at equality. Their
  strictness is witnessed by the edgeless graph on `n ≥ 2` vertices at every `r ≥ 1`
  (`d = λ = λ₂ = 0`, both sides `0`, disconnected) and by `K₂` at `r = 0` (both sides `1`,
  diameter `1`).
* Chung states the diameter bound with `⌈log(n − 1)/log(d/λ)⌉`. That bound on the diameter is
  true but is not proved here; the exact-length walk statement fails at the ceiling for every
  `Kₙ` with `n ≥ 3`, where `log(n − 1)/log(d/λ) = 1`, so `⌊·⌋ + 1` is the right form for it.
* The walk-count bounds and the `L²` and `L¹` bounds are attained (for instance on the diagonal
  of `Kₙ`, and for `K₂` started from a point mass).

## References
* F. R. K. Chung, *Diameters and eigenvalues*, J. Amer. Math. Soc. 2 (1989) 187–196: the
  diameter bound `D ≤ ⌈log(n − 1)/log(d/λ)⌉` and the walk-count argument.
* S. Hoory, N. Linial and A. Wigderson, *Expander graphs and their applications*, Bull. AMS 43
  (2006), §3.1.1: Theorem 3.2 (`‖Âᵗp − u‖₁ ≤ √n αᵗ`) and Lemma 3.4 (the per-step `L²`
  contraction).
* L. Lovász, *Random walks on graphs: a survey* (1993), Theorem 5.1: the pointwise bound
  `|Pᵗ(i, j) − π(j)| ≤ √(d_j/d_i) λᵗ`.
* F. Chung, V. Faber and T. Manteuffel, *An upper bound on the diameter of a graph from
  eigenvalues associated with its Laplacian*, SIAM J. Discrete Math. 7 (1994): the optimal
  shifted form of the one-sided diameter bound, of which the lazy bound here is a weaker special
  case.
* D. Aldous and J. A. Fill, *Reversible Markov Chains and Random Walks on Graphs*, §10.2.
* D. A. Levin, Y. Peres and E. L. Wilmer, *Markov Chains and Mixing Times* (lazy walks).
-/

open Finset Matrix

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian)

/-- `A + c·1` acts diagonally on coefficients: `cⱼ((A + c·1)x) = (λⱼ + c) cⱼ(x)`. -/
private theorem coeff_add_smul_one_mulVec (c : ℝ) (x : n → ℝ) (j : n) :
    hA.coeff ((A + c • 1) *ᵥ x) j = (hA.eigenvalues j + c) * hA.coeff x j := by
  rw [add_mulVec, smul_mulVec, one_mulVec]
  unfold coeff
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul, ← coeff, ← coeff, coeff_mulVec]
  ring

/-- `cⱼ((A + c·1)ʳ x) = (λⱼ + c)ʳ cⱼ(x)`. -/
private theorem coeff_add_smul_one_pow_mulVec (c : ℝ) (r : ℕ) (x : n → ℝ) (j : n) :
    hA.coeff ((A + c • 1) ^ r *ᵥ x) j = (hA.eigenvalues j + c) ^ r * hA.coeff x j := by
  induction r generalizing x with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ← mulVec_mulVec, ih, coeff_add_smul_one_mulVec, pow_succ]
    ring

/-- The termwise bound: if `|λⱼ + c| ≤ K` whenever `cⱼ(x) ≠ 0`, then
`((λⱼ + c)ʳ cⱼ(x))² ≤ K^{2r} cⱼ(x)²`. -/
private theorem sq_pow_mul_coeff_le {c K : ℝ} {x : n → ℝ}
    (hK : ∀ j, hA.coeff x j ≠ 0 → |hA.eigenvalues j + c| ≤ K) (r : ℕ) (j : n) :
    ((hA.eigenvalues j + c) ^ r * hA.coeff x j) ^ 2 ≤ K ^ (2 * r) * hA.coeff x j ^ 2 := by
  by_cases hj : hA.coeff x j = 0
  · simp [hj]
  · have h := abs_le.mp (hK j hj)
    have h2 : (hA.eigenvalues j + c) ^ 2 ≤ K ^ 2 := sq_le_sq' h.1 h.2
    have h3 : ((hA.eigenvalues j + c) ^ 2) ^ r ≤ (K ^ 2) ^ r :=
      pow_le_pow_left₀ (sq_nonneg _) h2 r
    rw [mul_pow, ← pow_mul, mul_comm r 2, pow_mul, pow_mul]
    exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)

/-- If every eigenvalue along which `x` has a component satisfies `|λⱼ + c| ≤ K`, then
`‖(A + c·1)ʳ x‖² ≤ K^{2r} ‖x‖²`. -/
private theorem dotProduct_self_add_smul_one_pow_mulVec_le {c K : ℝ} {x : n → ℝ}
    (hK : ∀ j, hA.coeff x j ≠ 0 → |hA.eigenvalues j + c| ≤ K) (r : ℕ) :
    ((A + c • 1) ^ r *ᵥ x) ⬝ᵥ ((A + c • 1) ^ r *ᵥ x) ≤ K ^ (2 * r) * (x ⬝ᵥ x) := by
  rw [← hA.sum_sq_coeff, ← hA.sum_sq_coeff, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [coeff_add_smul_one_pow_mulVec]
  exact hA.sq_pow_mul_coeff_le hK r j

/-- If every eigenvalue along which `x` has a component satisfies `|λⱼ + c| ≤ K`, then for every
`y`, `(xᵀ(A + c·1)ʳy)² ≤ K^{2r} ‖x‖² ‖y‖²`. -/
private theorem sq_dotProduct_add_smul_one_pow_mulVec_le {c K : ℝ} {x : n → ℝ}
    (hK : ∀ j, hA.coeff x j ≠ 0 → |hA.eigenvalues j + c| ≤ K) (r : ℕ) (y : n → ℝ) :
    (x ⬝ᵥ (A + c • 1) ^ r *ᵥ y) ^ 2 ≤ K ^ (2 * r) * (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  rw [← hA.sum_coeff_mul_coeff x]
  simp_rw [coeff_add_smul_one_pow_mulVec]
  calc (∑ j, hA.coeff x j * ((hA.eigenvalues j + c) ^ r * hA.coeff y j)) ^ 2
      = (∑ j, ((hA.eigenvalues j + c) ^ r * hA.coeff x j) * hA.coeff y j) ^ 2 := by
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ (∑ j, ((hA.eigenvalues j + c) ^ r * hA.coeff x j) ^ 2) * ∑ j, hA.coeff y j ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ j, K ^ (2 * r) * hA.coeff x j ^ 2) * ∑ j, hA.coeff y j ^ 2 :=
        mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ => hA.sq_pow_mul_coeff_le hK r j)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = K ^ (2 * r) * (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
        rw [← Finset.mul_sum, hA.sum_sq_coeff, hA.sum_sq_coeff]

end Matrix.IsHermitian

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {d : ℕ}

/-! ### Powers of the shifted adjacency matrix -/

/-- `(A + c·1)ʳ 𝟙 = (d + c)ʳ 𝟙` in a `d`-regular graph. -/
private theorem adjMatrix_add_smul_one_pow_mulVec_one (hd : G.IsRegularOfDegree d) (c : ℝ)
    (r : ℕ) :
    (G.adjMatrix ℝ + c • 1) ^ r *ᵥ (1 : V → ℝ) = ((d : ℝ) + c) ^ r • (1 : V → ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, add_mulVec, smul_mulVec, one_mulVec,
      adjMatrix_mulVec_one_of_regular hd, ← add_smul, smul_smul, pow_succ]

/-- `(A + c·1)ʳ` is symmetric, so `xᵀ (A + c·1)ʳ y = ((A + c·1)ʳ x)ᵀ y`. -/
private theorem dotProduct_adjMatrix_add_smul_one_pow_mulVec_comm (c : ℝ) (r : ℕ)
    (x y : V → ℝ) :
    x ⬝ᵥ (G.adjMatrix ℝ + c • 1) ^ r *ᵥ y = ((G.adjMatrix ℝ + c • 1) ^ r *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, transpose_pow, transpose_add, transpose_smul,
    transpose_one, transpose_adjMatrix]

/-- The entry decomposition: in a `d`-regular graph on a nonempty vertex type,
`(A + c·1)ʳ u v = (d + c)ʳ / n + c_uᵀ (A + c·1)ʳ c_v`, where `c_u = 1_{u} − (1/n) 𝟙` is the
centered indicator of `{u}`. -/
private theorem adjMatrix_add_smul_one_pow_apply_eq [Nonempty V] (hd : G.IsRegularOfDegree d)
    (c : ℝ) (r : ℕ) (u v : V) :
    ((G.adjMatrix ℝ + c • 1) ^ r) u v
      = ((d : ℝ) + c) ^ r / Fintype.card V
        + centeredIndicator {u} ⬝ᵥ (G.adjMatrix ℝ + c • 1) ^ r *ᵥ centeredIndicator {v} := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : ∀ w : V, (Pi.single w (1 : ℝ) : V → ℝ)
      = centeredIndicator {w} + ((1 : ℝ) / Fintype.card V) • (1 : V → ℝ) := by
    intro w
    ext z
    by_cases hz : z = w <;> simp [centeredIndicator, hz]
  have h1 : centeredIndicator {u} ⬝ᵥ (G.adjMatrix ℝ + c • 1) ^ r *ᵥ (1 : V → ℝ) = 0 := by
    rw [adjMatrix_add_smul_one_pow_mulVec_one hd, dotProduct_smul, dotProduct_one,
      sum_centeredIndicator, smul_zero]
  have h2 : (1 : V → ℝ) ⬝ᵥ (G.adjMatrix ℝ + c • 1) ^ r *ᵥ centeredIndicator {v} = 0 := by
    rw [dotProduct_adjMatrix_add_smul_one_pow_mulVec_comm,
      adjMatrix_add_smul_one_pow_mulVec_one hd, smul_dotProduct, one_dotProduct,
      sum_centeredIndicator, smul_zero]
  have h3 : (1 : V → ℝ) ⬝ᵥ (G.adjMatrix ℝ + c • 1) ^ r *ᵥ (1 : V → ℝ)
      = ((d : ℝ) + c) ^ r * Fintype.card V := by
    rw [adjMatrix_add_smul_one_pow_mulVec_one hd, dotProduct_smul, dotProduct_one]
    simp
  have he : ((G.adjMatrix ℝ + c • 1) ^ r) u v
      = Pi.single u (1 : ℝ) ⬝ᵥ (G.adjMatrix ℝ + c • 1) ^ r *ᵥ Pi.single v (1 : ℝ) := by
    rw [single_dotProduct, mulVec_single_one, one_mul, col_apply]
  rw [he, hs u, hs v]
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, h1, h2, h3]
  field_simp
  ring

/-- The generic entrywise bound: if every eigenvalue `λⱼ` along which some vector `x ⟂ 𝟙` has a
component satisfies `|λⱼ + c| ≤ K`, then `|(A + c·1)ʳ u v − (d + c)ʳ / n| ≤ Kʳ (1 − 1/n)`. -/
private theorem abs_adjMatrix_add_smul_one_pow_apply_sub_le [Nonempty V]
    (hd : G.IsRegularOfDegree d) {c K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x : V → ℝ, ∑ v, x v = 0 → ∀ j, (G.isHermitian_adjMatrix ℝ).coeff x j ≠ 0 →
      |(G.isHermitian_adjMatrix ℝ).eigenvalues j + c| ≤ K) (r : ℕ) (u v : V) :
    |((G.adjMatrix ℝ + c • 1) ^ r) u v - ((d : ℝ) + c) ^ r / Fintype.card V|
      ≤ K ^ r * (1 - 1 / Fintype.card V) := by
  rw [adjMatrix_add_smul_one_pow_apply_eq hd, add_sub_cancel_left]
  have h := (G.isHermitian_adjMatrix ℝ).sq_dotProduct_add_smul_one_pow_mulVec_le
    (hK _ (sum_centeredIndicator {u})) r (centeredIndicator {v})
  simp only [centeredIndicator_dotProduct_self, card_singleton, Nat.cast_one, one_mul] at h
  have hn : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos
  have h0 : 0 ≤ 1 - 1 / (Fintype.card V : ℝ) := by
    rw [sub_nonneg]
    exact div_le_one_of_le₀ hn (by positivity)
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg (pow_nonneg hK0 r) h0)
  calc _ ≤ _ := h
    _ = (K ^ r * (1 - 1 / Fintype.card V)) ^ 2 := by ring

/-! ### Walk counts converge to uniform -/

/-- **Walk counts converge to uniform.** In a `d`-regular graph on `n ≥ 2` vertices, for every
length `r` and all vertices `u`, `v` (equal or not), the number `(Aʳ) u v` of walks of length
`r` from `u` to `v` satisfies `|(Aʳ) u v − dʳ/n| ≤ λʳ (1 − 1/n)`, where
`λ = λ(G) = max(|λ₂|, |λₙ|)` is the two-sided parameter.

Degenerate cases: for `r = 0` both `A⁰ = 1` and `λ⁰ = 1` (Lean's `0 ^ 0 = 1` included, which
is the value needed when `λ = 0`), and the bound reads `|δᵤᵥ − 1/n| ≤ 1 − 1/n`. For `d = 0`
the graph is edgeless, `λ = 0`, and for `r ≥ 1` both sides are `0`. `n ≥ 2` (`Nontrivial V`)
is needed only because `λ₂` is; the division by `n` is then genuine. The bound is attained, for
example on the diagonal of `Kₙ`. -/
theorem abs_adjMatrix_pow_apply_sub_le [Nontrivial V] (hd : G.IsRegularOfDegree d) (r : ℕ)
    (u v : V) :
    |(G.adjMatrix ℝ ^ r) u v - (d : ℝ) ^ r / Fintype.card V|
      ≤ G.twoSidedAdjEigenvalue ^ r * (1 - 1 / Fintype.card V) := by
  have h := abs_adjMatrix_add_smul_one_pow_apply_sub_le (c := 0) hd G.twoSidedAdjEigenvalue_nonneg
    (fun x hx j hj => by
      rw [add_zero]
      exact abs_eigenvalues_le_twoSidedAdjEigenvalue hd hx hj) r u v
  simpa using h

/-- Every adjacency eigenvalue of a `d`-regular graph is at least `−d`, in particular `λₙ`. -/
private theorem neg_degree_le_smallestAdjEigenvalue_of_regular [Nonempty V]
    (hd : G.IsRegularOfDegree d) : -(d : ℝ) ≤ G.smallestAdjEigenvalue := by
  obtain ⟨w, hw, hAw⟩ := (G.isHermitian_adjMatrix ℝ).exists_eigenvector_smallest
  exact (abs_le.mp (abs_le_of_adjMatrix_mulVec_eq hd hw hAw)).1

/-- `0 ≤ d + λ₂` for a `d`-regular graph on `n ≥ 2` vertices, because every adjacency eigenvalue
is at least `−d`. Equality holds for `K₂` (`d = 1`, `λ₂ = −1`) and for the edgeless graph
(`d = 0 = λ₂`). -/
theorem degree_add_secondAdjEigenvalue_nonneg [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    0 ≤ (d : ℝ) + G.secondAdjEigenvalue := by
  linarith [neg_degree_le_smallestAdjEigenvalue_of_regular hd,
    G.smallestAdjEigenvalue_le_secondAdjEigenvalue]

/-- **Lazy walk counts converge to uniform.** In a `d`-regular graph on `n ≥ 2` vertices, for
every `r` and all vertices `u`, `v`,
`|((A + d·1)ʳ) u v − (2d)ʳ/n| ≤ (d + λ₂)ʳ (1 − 1/n)`.
The matrix `A + d·1` is `2d` times the lazy random walk `(1 + A/d)/2`; its eigenvalues are
`λⱼ + d ∈ [0, 2d]`, so only the one-sided quantity `d + λ₂ ≥ 0`
(`degree_add_secondAdjEigenvalue_nonneg`) appears, and the bound is useful for bipartite graphs
as well.

Degenerate cases: for `r = 0` it reads `|δᵤᵥ − 1/n| ≤ 1 − 1/n` (with `0 ^ 0 = 1` when
`d + λ₂ = 0`). For `K₂`, `d + λ₂ = 0` and the bound says `(A + 1)ʳ u v = 2ʳ/2` for `r ≥ 1`.
For `d = 0` the matrix is `0` and both sides vanish for `r ≥ 1`. -/
theorem abs_adjMatrix_add_degree_pow_apply_sub_le [Nontrivial V] (hd : G.IsRegularOfDegree d)
    (r : ℕ) (u v : V) :
    |((G.adjMatrix ℝ + (d : ℝ) • 1) ^ r) u v - (2 * (d : ℝ)) ^ r / Fintype.card V|
      ≤ ((d : ℝ) + G.secondAdjEigenvalue) ^ r * (1 - 1 / Fintype.card V) := by
  have h := abs_adjMatrix_add_smul_one_pow_apply_sub_le (c := (d : ℝ)) hd
    (degree_add_secondAdjEigenvalue_nonneg hd) (fun x hx j hj => by
      have hmem := eigenvalues_mem_Icc_of_coeff_ne_zero hd hx hj
      have h1 := neg_degree_le_smallestAdjEigenvalue_of_regular (G := G) hd
      rw [abs_le]
      constructor <;> linarith [hmem.1, hmem.2]) r u v
  rwa [← two_mul] at h

/-! ### Diameter bounds -/

/-- A nonzero entry of `(A + c·1)ʳ` at `(u, v)` gives a walk from `u` to `v` of length at most
`r`. -/
private theorem exists_walk_length_le_of_adjMatrix_add_smul_one_pow_ne_zero (c : ℝ) (r : ℕ)
    {u v : V} (h : ((G.adjMatrix ℝ + c • 1) ^ r) u v ≠ 0) : ∃ p : G.Walk u v, p.length ≤ r := by
  induction r generalizing u with
  | zero =>
    have huv : u = v := by
      by_contra huv
      exact h (by rw [pow_zero, one_apply_ne huv])
    subst huv
    exact ⟨Walk.nil, le_rfl⟩
  | succ r ih =>
    rw [pow_succ', mul_apply] at h
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    obtain ⟨p, hp⟩ := ih (right_ne_zero_of_mul hw)
    by_cases huw : u = w
    · subst huw
      exact ⟨p, by omega⟩
    · have hadj : G.Adj u w := by
        by_contra hna
        apply left_ne_zero_of_mul hw
        simp [adjMatrix_apply, hna, one_apply_ne huw]
      exact ⟨Walk.cons hadj p, by rw [Walk.length_cons]; omega⟩

/-- From `|X − B/N| ≤ K (1 − 1/N)` and `(N − 1) K < B` with `N > 0`, conclude `X > 0`. -/
private theorem pos_of_abs_sub_div_le {X B K N : ℝ} (hN : 0 < N)
    (h : |X - B / N| ≤ K * (1 - 1 / N)) (hlt : (N - 1) * K < B) : 0 < X := by
  have h1 := (abs_le.mp h).1
  have e : B / N - K * (1 - 1 / N) = (B - (N - 1) * K) / N := by
    field_simp
  have h2 : 0 < (B - (N - 1) * K) / N := div_pos (by linarith) hN
  linarith

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Walks of length at most `r` between all pairs give connectivity and the diameter bound. -/
private theorem connected_and_diam_le_of_forall_exists_walk [Nonempty V] {r : ℕ}
    (h : ∀ u v : V, ∃ p : G.Walk u v, p.length ≤ r) :
    G.Connected ∧ (∀ u v, G.dist u v ≤ r) ∧ G.diam ≤ r := by
  have hdist : ∀ u v, G.dist u v ≤ r := fun u v => by
    obtain ⟨p, hp⟩ := h u v
    exact (dist_le p).trans hp
  refine ⟨⟨fun u v => (h u v).elim fun p _ => p.reachable⟩, hdist, ?_⟩
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  exact huv ▸ hdist u v

/-- **Walks of every exact length `r` with `(n − 1) λʳ < dʳ`.** In a `d`-regular graph on
`n ≥ 2` vertices, if `(n − 1) λʳ < dʳ` then every ordered pair of vertices `u`, `v` (including
`u = v`) is joined by a walk of length exactly `r`: by `abs_adjMatrix_pow_apply_sub_le`,
`(Aʳ) u v ≥ (dʳ − (n − 1) λʳ)/n > 0`.

The inequality must be strict: `Kₙ` at `r = 1` has `(n − 1) λ = d` and no walk of length `1`
from a vertex to itself, and `K₂` has `(n − 1) λʳ = dʳ = 1` for every `r` and no walk of odd
length from a vertex to itself, nor of even length between its two vertices. `n − 1` is real
subtraction. For `d = 0` the hypothesis never
holds (it reads `n − 1 < 1` for `r = 0` and `0 < 0` for `r ≥ 1`). -/
theorem exists_walk_length_eq_of_mul_twoSidedAdjEigenvalue_pow_lt [Nontrivial V]
    (hd : G.IsRegularOfDegree d) {r : ℕ}
    (h : ((Fintype.card V : ℝ) - 1) * G.twoSidedAdjEigenvalue ^ r < (d : ℝ) ^ r) (u v : V) :
    ∃ p : G.Walk u v, p.length = r := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hpos := pos_of_abs_sub_div_le hn (abs_adjMatrix_pow_apply_sub_le hd r u v) h
  rw [adjMatrix_pow_apply_eq_card_walk] at hpos
  have : 0 < Fintype.card {p : G.Walk u v | p.length = r} := by exact_mod_cast hpos
  obtain ⟨⟨p, hp⟩⟩ := Fintype.card_pos_iff.mp this
  exact ⟨p, hp⟩

/-- **Diameter from the two-sided parameter, for a fixed `r`.** In a `d`-regular graph on
`n ≥ 2` vertices with `(n − 1) λʳ < dʳ`, the graph is connected, `dist u v ≤ r` for all `u`,
`v`, and `diam G ≤ r`. (Mathlib's `diam` is `0` for a disconnected graph, so the connectivity
statement is not implied by the diameter bound.) The strict inequality is needed: at equality,
the edgeless graph on `n ≥ 2` vertices (every `r ≥ 1`) is disconnected, and `K₂` at `r = 0` has
diameter `1 > 0`. (The examples `Kₙ` at `r = 1` and `K₂` at `r ≥ 1`, which show strictness is
needed for exact-length walks, satisfy this conclusion at equality.) -/
theorem connected_and_diam_le_of_mul_twoSidedAdjEigenvalue_pow_lt [Nontrivial V]
    (hd : G.IsRegularOfDegree d) {r : ℕ}
    (h : ((Fintype.card V : ℝ) - 1) * G.twoSidedAdjEigenvalue ^ r < (d : ℝ) ^ r) :
    G.Connected ∧ (∀ u v, G.dist u v ≤ r) ∧ G.diam ≤ r :=
  connected_and_diam_le_of_forall_exists_walk fun u v =>
    (exists_walk_length_eq_of_mul_twoSidedAdjEigenvalue_pow_lt hd h u v).elim
      fun p hp => ⟨p, hp.le⟩

/-- **Diameter from the one-sided gap (lazy walks), for a fixed `r`.** In a `d`-regular graph on
`n ≥ 2` vertices with `(n − 1)(d + λ₂)ʳ < (2d)ʳ`, the graph is connected, `dist u v ≤ r` for all
`u`, `v`, and `diam G ≤ r`. The lazy walk only gives walks of length *at most* `r`, but it needs
no control of `λₙ`, so it applies to bipartite graphs.

The inequality must be strict (for `r = 0` it would read `n − 1 ≤ 1`, true for `K₂`, whose
diameter is `1`; for `r ≥ 1` both sides are `0` on the edgeless graph on `n ≥ 2` vertices,
which is disconnected). For `K₂`, `d + λ₂ = 0` and the hypothesis holds for every `r ≥ 1`.
For `d = 0` the hypothesis never holds. -/
theorem connected_and_diam_le_of_mul_degree_add_secondAdjEigenvalue_pow_lt [Nontrivial V]
    (hd : G.IsRegularOfDegree d) {r : ℕ}
    (h : ((Fintype.card V : ℝ) - 1) * ((d : ℝ) + G.secondAdjEigenvalue) ^ r
      < (2 * (d : ℝ)) ^ r) :
    G.Connected ∧ (∀ u v, G.dist u v ≤ r) ∧ G.diam ≤ r := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  refine connected_and_diam_le_of_forall_exists_walk fun u v => ?_
  have hpos := pos_of_abs_sub_div_le hn (abs_adjMatrix_add_degree_pow_apply_sub_le hd r u v) h
  exact exists_walk_length_le_of_adjMatrix_add_smul_one_pow_ne_zero (d : ℝ) r hpos.ne'

/-- The real-number core of the logarithmic forms: for `0 ≤ a < b` and `N ≥ 1`, with
`r = ⌊log N / log(b/a)⌋₊ + 1`, `N aʳ < bʳ`. If `a = 0`, Lean's `b/0 = 0` and `log 0 = 0` give
`r = 1`, and `N · 0 < b` holds. -/
private theorem mul_pow_floor_log_add_one_lt {a b N : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hN : 1 ≤ N) :
    N * a ^ (⌊Real.log N / Real.log (b / a)⌋₊ + 1)
      < b ^ (⌊Real.log N / Real.log (b / a)⌋₊ + 1) := by
  have hb : 0 < b := ha.trans_lt hab
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_pow (Nat.succ_ne_zero _), mul_zero]
    exact pow_pos hb _
  · have hlog : 0 < Real.log (b / a) := Real.log_pos ((one_lt_div ha').mpr hab)
    have hr : Real.log N / Real.log (b / a)
        < ((⌊Real.log N / Real.log (b / a)⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      exact Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hlog, ← Real.log_pow] at hr
    have h2 : N < (b / a) ^ (⌊Real.log N / Real.log (b / a)⌋₊ + 1) :=
      (Real.log_lt_log_iff (by linarith) (pow_pos (div_pos hb ha') _)).mp hr
    rwa [div_pow, lt_div_iff₀ (pow_pos ha' _)] at h2

omit [DecidableEq V] in
private theorem one_le_card_sub_one [Nontrivial V] : (1 : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by
  have h := Fintype.one_lt_card (α := V)
  have : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast h
  linarith

/-- **Exact-length walks, logarithmic form.** In a `d`-regular graph on `n ≥ 2` vertices with
`λ < d`, every ordered pair of vertices `u`, `v` (including `u = v`) is joined by a walk of
length exactly `⌊log(n − 1) / log(d/λ)⌋₊ + 1`.

Junk values: `⌊·⌋₊` is `Nat.floor`, which would send a negative number to `0`, but here the
quotient is nonnegative. If `λ = 0`, `d/λ` is `d/0 = 0` and `log 0 = 0`, so the length is `1`;
this cannot actually occur under `λ < d`, since then `d ≥ 1` and `λ ≥ 1`
(`one_le_twoSidedAdjEigenvalue`), but the statement does not rely on it. For `n = 2`,
`log 1 = 0` and the length is `1` (no regular graph on two vertices has `λ < d`).

The `⌊·⌋₊ + 1` cannot be replaced by Chung's `⌈·⌉` here: for `Kₙ` with `n ≥ 3`,
`log(n − 1)/log(d/λ) = 1`, and there is no walk of length `1` from a vertex to itself. -/
theorem exists_walk_length_eq_floor_log_add_one [Nontrivial V] (hd : G.IsRegularOfDegree d)
    (hlt : G.twoSidedAdjEigenvalue < d) (u v : V) :
    ∃ p : G.Walk u v, p.length
      = ⌊Real.log ((Fintype.card V : ℝ) - 1)
          / Real.log ((d : ℝ) / G.twoSidedAdjEigenvalue)⌋₊ + 1 :=
  exists_walk_length_eq_of_mul_twoSidedAdjEigenvalue_pow_lt hd
    (mul_pow_floor_log_add_one_lt G.twoSidedAdjEigenvalue_nonneg hlt one_le_card_sub_one) u v

/-- **Chung's diameter bound.** A `d`-regular graph on `n ≥ 2` vertices with `λ < d` is
connected and has `diam G ≤ ⌊log(n − 1) / log(d/λ)⌋₊ + 1`.

Connectivity is part of the conclusion because Mathlib's `diam` is `0` for a disconnected graph.
Junk values are as in `exists_walk_length_eq_floor_log_add_one`: if `λ = 0` the quotient is
`log(n − 1)/log 0 = 0` and the bound is `1` (impossible under `λ < d`, but not excluded by
hand), and for `n = 2` it is `1`. Chung (1989) states the bound with `⌈log(n − 1)/log(d/λ)⌉`,
which is at most this one; the ceiling form is true but is not proved here. -/
theorem connected_and_diam_le_floor_log_twoSidedAdjEigenvalue [Nontrivial V]
    (hd : G.IsRegularOfDegree d) (hlt : G.twoSidedAdjEigenvalue < d) :
    G.Connected ∧ G.diam ≤ ⌊Real.log ((Fintype.card V : ℝ) - 1)
          / Real.log ((d : ℝ) / G.twoSidedAdjEigenvalue)⌋₊ + 1 := by
  have h := connected_and_diam_le_of_mul_twoSidedAdjEigenvalue_pow_lt hd
    (mul_pow_floor_log_add_one_lt G.twoSidedAdjEigenvalue_nonneg hlt one_le_card_sub_one)
  exact ⟨h.1, h.2.2⟩

/-- **One-sided (lazy) diameter bound.** A `d`-regular graph on `n ≥ 2` vertices with `λ₂ < d`
is connected and has `diam G ≤ ⌊log(n − 1) / log(2d/(d + λ₂))⌋₊ + 1`. Only `λ₂` enters, so the
bound applies to bipartite graphs, where `λ = d`.

Junk values: if `d + λ₂ = 0` (this happens for `K₂`), `2d/(d + λ₂)` is `2d/0 = 0` and
`log 0 = 0`, so the bound reads `diam G ≤ 1`, which is correct. `⌊·⌋₊` is `Nat.floor`; the
quotient is nonnegative here. For `n = 2`, `log 1 = 0` and the bound is `1`. -/
theorem connected_and_diam_le_floor_log_secondAdjEigenvalue [Nontrivial V]
    (hd : G.IsRegularOfDegree d) (hlt : G.secondAdjEigenvalue < d) :
    G.Connected ∧ G.diam ≤ ⌊Real.log ((Fintype.card V : ℝ) - 1)
          / Real.log (2 * (d : ℝ) / ((d : ℝ) + G.secondAdjEigenvalue))⌋₊ + 1 := by
  have h := connected_and_diam_le_of_mul_degree_add_secondAdjEigenvalue_pow_lt hd
    (mul_pow_floor_log_add_one_lt (degree_add_secondAdjEigenvalue_nonneg hd) (by linarith)
      one_le_card_sub_one)
  exact ⟨h.1, h.2.2⟩

/-! ### Mixing of the random walk -/

/-- **`L²` mixing.** In a `d`-regular graph on `n ≥ 2` vertices, for every vector `x`, every
`t`, and `m = (Σ_v x_v)/n` the mean of `x`,
`‖Aᵗx − dᵗ m 𝟙‖² ≤ λ^{2t} ‖x − m 𝟙‖²` (squared Euclidean norms written as dot products).
Equivalently, `Aᵗ/dᵗ` contracts the component of `x` orthogonal to `𝟙` by `(λ/d)ᵗ`.

The mean is passed as an argument `m` with `hm : m = (Σ_v x_v)/n`; the division by `n` is
genuine since `n ≥ 2`. For `t = 0` the two sides are equal. For `d = 0` and `t ≥ 1` both sides
are `0` (`A = 0`, `λ = 0`). -/
theorem dotProduct_self_adjMatrix_pow_mulVec_sub_le [Nontrivial V] (hd : G.IsRegularOfDegree d)
    (x : V → ℝ) {m : ℝ} (hm : m = (∑ v, x v) / Fintype.card V) (t : ℕ) :
    (G.adjMatrix ℝ ^ t *ᵥ x - ((d : ℝ) ^ t * m) • 1)
        ⬝ᵥ (G.adjMatrix ℝ ^ t *ᵥ x - ((d : ℝ) ^ t * m) • 1)
      ≤ G.twoSidedAdjEigenvalue ^ (2 * t) * ((x - m • 1) ⬝ᵥ (x - m • 1)) := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : G.adjMatrix ℝ ^ t *ᵥ (1 : V → ℝ) = (d : ℝ) ^ t • (1 : V → ℝ) := by
    simpa using adjMatrix_add_smul_one_pow_mulVec_one hd 0 t
  have he : G.adjMatrix ℝ ^ t *ᵥ x - ((d : ℝ) ^ t * m) • 1
      = G.adjMatrix ℝ ^ t *ᵥ (x - m • 1) := by
    rw [mulVec_sub, mulVec_smul, h1, smul_smul, mul_comm]
  have hsum : ∑ v, (x - m • 1) v = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
      Finset.sum_sub_distrib, Finset.sum_const, card_univ, nsmul_eq_mul, hm]
    field_simp
    ring
  have h := (G.isHermitian_adjMatrix ℝ).dotProduct_self_add_smul_one_pow_mulVec_le (c := 0)
    (fun j hj => by
      rw [add_zero]
      exact abs_eigenvalues_le_twoSidedAdjEigenvalue hd hsum hj) t
  simp only [zero_smul, add_zero] at h
  rw [he]
  exact h

/-- **`L¹` (total-variation) mixing, unnormalised.** In a `d`-regular graph on `n ≥ 2` vertices,
for every probability vector `p` (`p ≥ 0`, `Σ_v p_v = 1`) and every `t`,
`Σ_v |(Aᵗp)_v − dᵗ/n| ≤ √(n − 1) · λᵗ`. Dividing by `dᵗ` gives the random-walk form
`sum_abs_randomWalk_pow_mulVec_sub_le`.

The argument of the square root is `n − 1 ≥ 1` (real subtraction), never negative. For `t = 0`
it reads `Σ_v |p_v − 1/n| ≤ √(n − 1)`. For `d = 0` and `t ≥ 1` both sides are `0`. The bound is
attained for `K₂` started from a point mass. -/
theorem sum_abs_adjMatrix_pow_mulVec_sub_le [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {p : V → ℝ} (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∑ v, p v = 1) (t : ℕ) :
    ∑ v, |(G.adjMatrix ℝ ^ t *ᵥ p) v - (d : ℝ) ^ t / Fintype.card V|
      ≤ Real.sqrt ((Fintype.card V : ℝ) - 1) * G.twoSidedAdjEigenvalue ^ t := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hN1 : (0 : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by linarith [one_le_card_sub_one (V := V)]
  have h := dotProduct_self_adjMatrix_pow_mulVec_sub_le hd p
    (m := 1 / Fintype.card V) (by rw [hp1]) t
  have hz : ∀ v, (G.adjMatrix ℝ ^ t *ᵥ p - ((d : ℝ) ^ t * (1 / Fintype.card V)) • 1) v
      = (G.adjMatrix ℝ ^ t *ᵥ p) v - (d : ℝ) ^ t / Fintype.card V := by
    intro v
    simp [div_eq_mul_inv]
  have hpp : (p - (1 / (Fintype.card V : ℝ)) • (1 : V → ℝ))
      ⬝ᵥ (p - (1 / (Fintype.card V : ℝ)) • (1 : V → ℝ)) ≤ 1 - 1 / Fintype.card V := by
    have hsq : ∑ v, p v ^ 2 ≤ 1 := by
      have := Finset.sum_sq_le_sq_sum_of_nonneg (s := univ) (fun v _ => hp0 v)
      rwa [hp1, one_pow] at this
    have e : (p - (1 / (Fintype.card V : ℝ)) • (1 : V → ℝ))
        ⬝ᵥ (p - (1 / (Fintype.card V : ℝ)) • (1 : V → ℝ))
        = ∑ v, p v ^ 2 - 1 / Fintype.card V := by
      have : ∀ v, (p v - 1 / (Fintype.card V : ℝ)) * (p v - 1 / (Fintype.card V : ℝ))
          = p v ^ 2 - 2 / Fintype.card V * p v + 1 / (Fintype.card V : ℝ) ^ 2 := fun v => by
        ring
      simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
        this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp1,
        Finset.sum_const, card_univ, nsmul_eq_mul]
      field_simp
      ring
    linarith
  have hcs : (∑ v, |(G.adjMatrix ℝ ^ t *ᵥ p) v - (d : ℝ) ^ t / Fintype.card V|) ^ 2
      ≤ Fintype.card V
        * ∑ v, ((G.adjMatrix ℝ ^ t *ᵥ p) v - (d : ℝ) ^ t / Fintype.card V) ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ => (1 : ℝ))
      (fun v => |(G.adjMatrix ℝ ^ t *ᵥ p) v - (d : ℝ) ^ t / Fintype.card V|)
    simpa [sq_abs] using this
  have hzz : ∑ v, ((G.adjMatrix ℝ ^ t *ᵥ p) v - (d : ℝ) ^ t / Fintype.card V) ^ 2
      = (G.adjMatrix ℝ ^ t *ᵥ p - ((d : ℝ) ^ t * (1 / Fintype.card V)) • 1)
        ⬝ᵥ (G.adjMatrix ℝ ^ t *ᵥ p - ((d : ℝ) ^ t * (1 / Fintype.card V)) • 1) := by
    simp only [dotProduct, hz, sq]
  rw [hzz] at hcs
  have hfin : (∑ v, |(G.adjMatrix ℝ ^ t *ᵥ p) v - (d : ℝ) ^ t / Fintype.card V|) ^ 2
      ≤ (Real.sqrt ((Fintype.card V : ℝ) - 1) * G.twoSidedAdjEigenvalue ^ t) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hN1, ← pow_mul, mul_comm t 2]
    calc _ ≤ _ := hcs
      _ ≤ Fintype.card V * (G.twoSidedAdjEigenvalue ^ (2 * t) * (1 - 1 / Fintype.card V)) :=
          mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hpp
            (pow_nonneg G.twoSidedAdjEigenvalue_nonneg _))) hn.le
      _ = ((Fintype.card V : ℝ) - 1) * G.twoSidedAdjEigenvalue ^ (2 * t) := by
          field_simp
  exact (le_abs_self _).trans (abs_le_of_sq_le_sq hfin
    (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg G.twoSidedAdjEigenvalue_nonneg _)))

/-- **Total-variation mixing of the random walk.** Let `G` be `d`-regular on `n ≥ 2` vertices
with `d ≥ 1`, and let `P = A/d` (written `(d : ℝ)⁻¹ • A`) be its random-walk matrix. For every
probability vector `p` and every `t`,
`Σ_v |(Pᵗp)_v − 1/n| ≤ √(n − 1) · (λ/d)ᵗ`;
the total-variation distance between the distribution after `t` steps and the uniform
distribution is half the left-hand side. (`P` is symmetric, so `Pᵗp` is also the distribution
after `t` steps of the walk started from `p`.)

The hypothesis `d ≥ 1` cannot be dropped: for `d = 0`, Lean's `0⁻¹ = 0` makes `P = 0`, which is
not a random walk, and for `t ≥ 1` the left-hand side is `1` while the right-hand side is
`√(n − 1) · (0/0)ᵗ = 0`. -/
theorem sum_abs_randomWalk_pow_mulVec_sub_le [Nontrivial V] (hd : G.IsRegularOfDegree d)
    (hd0 : 0 < d) {p : V → ℝ} (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∑ v, p v = 1) (t : ℕ) :
    ∑ v, |(((d : ℝ)⁻¹ • G.adjMatrix ℝ) ^ t *ᵥ p) v - 1 / Fintype.card V|
      ≤ Real.sqrt ((Fintype.card V : ℝ) - 1) * (G.twoSidedAdjEigenvalue / d) ^ t := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
  have h := sum_abs_adjMatrix_pow_mulVec_sub_le hd hp0 hp1 t
  have hterm : ∀ v, |(((d : ℝ)⁻¹ • G.adjMatrix ℝ) ^ t *ᵥ p) v - 1 / Fintype.card V|
      = ((d : ℝ)⁻¹) ^ t * |(G.adjMatrix ℝ ^ t *ᵥ p) v - (d : ℝ) ^ t / Fintype.card V| := by
    intro v
    rw [smul_pow, smul_mulVec, Pi.smul_apply, smul_eq_mul,
      ← abs_of_pos (pow_pos (inv_pos.mpr hdpos) t), ← abs_mul,
      abs_of_pos (pow_pos (inv_pos.mpr hdpos) t)]
    congr 1
    rw [mul_sub, ← mul_div_assoc, ← mul_pow, inv_mul_cancel₀ hdpos.ne', one_pow]
  calc _ = ((d : ℝ)⁻¹) ^ t
        * ∑ v, |(G.adjMatrix ℝ ^ t *ᵥ p) v - (d : ℝ) ^ t / Fintype.card V| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => hterm v
    _ ≤ ((d : ℝ)⁻¹) ^ t * (Real.sqrt ((Fintype.card V : ℝ) - 1)
        * G.twoSidedAdjEigenvalue ^ t) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg (inv_nonneg.mpr hdpos.le) t)
    _ = _ := by
        rw [div_pow, inv_pow]
        ring

end SimpleGraph
