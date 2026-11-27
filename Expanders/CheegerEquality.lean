/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.Cheeger
import Expanders.Hypercube

/-!
# When the easy side of Cheeger's inequality is sharp

For a `d`-regular graph `G` on `n ≥ 2` vertices with second adjacency eigenvalue `λ₂`, spectral
gap `d − λ₂` and Cheeger constant `h(G)`, the easy side of Cheeger's inequality
(`spectralGap_div_two_le_edgeExpansion`, in `Expanders/Cheeger.lean`) reads
`(d − λ₂)/2 ≤ h(G)`. This file characterises the graphs where it is an equality, and finds the
best constant in front of `d − λ₂` for a fixed number of vertices and for a fixed degree.

The equality case: when the gap is positive, `h(G) = (d − λ₂)/2` exactly when some balanced cut
`(S, Sᶜ)` (`2|S| = n`) has its `±1` vector `χ_S` as an eigenvector for `λ₂`, or equivalently
when every vertex has exactly `(d − λ₂)/2` neighbours across that cut. The proof sharpens the
easy side into the cut bound `|∂S| ≥ (d − λ₂)|S||Sᶜ|/n`, and uses the equality case of
Courant–Fischer for `λ₂`.

## Definitions
* `SimpleGraph.cutVector S`: the `±1` vector `χ_S` of a cut, `1` on `S` and `−1` off `S`.
* `SimpleGraph.crossDegree G S v`: the number `c_S(v)` of neighbours of `v` on the other side
  of the cut `(S, Sᶜ)`.

## Theorems (all proved here)
Linear algebra, for a real symmetric matrix (namespace `Matrix.IsHermitian`):
* `mulVec_eq_secondEigenvalue_smul_of_eq`: **equality in Courant–Fischer for `λ₂`**. If `x` is
  orthogonal to a nonzero top eigenvector and `xᵀAx = λ₂ · xᵀx`, then `A x = λ₂ x`. No gap
  `λ₂ < λ₁` is assumed.

Cut vectors (namespace `SimpleGraph`):
* `cutVector_dotProduct_self`, `sum_cutVector`: `χ_S ⬝ χ_S = n` and `Σ χ_S = 2|S| − n`.
* `cutVector_dotProduct_adjMatrix_mulVec`: `χ_Sᵀ A χ_S = d n − 4|∂S|`.
* `adjMatrix_mulVec_cutVector_apply`: `(A χ_S)(v) = χ_S(v) (d − 2 c_S(v))`.
* `adjMatrix_mulVec_cutVector_eq_iff`: `A χ_S = μ χ_S` iff `c_S(v) = (d − μ)/2` at every `v`.

The cut bound and the sharp constant:
* `spectralGap_mul_card_mul_card_compl_le`: `(d − λ₂) |S| |Sᶜ| / n ≤ |∂S|` for every `S`.
* `isEdgeExpander_spectralGap_mul_ceil`, `spectralGap_mul_ceil_div_le_edgeExpansion`,
  `IsSpectralExpander.isEdgeExpander_ceil`: easy Cheeger with the constant `⌈n/2⌉/n` in place of
  `1/2`, in set, value and predicate form.

The equality case of the easy side:
* `exists_edgeExpansion_eq`: the Cheeger constant is attained by some admissible `S`.
* `two_mul_card_eq_of_cutVector`: for a positive gap, a cut vector that is a `λ₂`-eigenvector
  belongs to a balanced cut.
* `card_edgeBoundary_eq_of_cutVector`, part (a): if `A χ_S = λ₂ χ_S` then
  `|∂S| = (d − λ₂)/2 · |S|`. `edgeExpansion_eq_of_cutVector`: then `h(G) = (d − λ₂)/2`.
* `balanced_of_card_edgeBoundary_le`, part (b): for a positive gap, a nonempty `S` with
  `2|S| ≤ n` and `|∂S| ≤ (d − λ₂)/2 · |S|` is balanced and `χ_S` is a `λ₂`-eigenvector.
  `balanced_of_edgeExpansion_eq`: the same for minimisers when `h(G) = (d − λ₂)/2`.
* `edgeExpansion_eq_spectralGap_div_two_iff`: for a positive gap, `h(G) = (d − λ₂)/2` iff some
  balanced cut has `c_S(v) = (d − λ₂)/2` at every vertex.
  `edgeExpansion_eq_spectralGap_div_two_iff_exists`: without the gap hypothesis, the same with
  an arbitrary cut.
* Corollaries, for a positive gap: `spectralGap_div_two_lt_edgeExpansion_of_odd` (odd `n` forces
  `(d − λ₂)/2 < h(G)`); `exists_nat_of_edgeExpansion_eq_spectralGap_div_two` (equality forces
  `h(G) = k` and `λ₂ = d − 2k` for a natural number `k ≥ 1`);
  `spectralGap_div_two_lt_edgeExpansion_of_lt_two` (a gap below `2` forces strict inequality).
* `hypercube_exists_crossDegree_eq_one`: the hypercube has a balanced cut crossed once at every
  vertex.

The complete graph `K_n`:
* `secondAdjEigenvalue_top`: `λ₂(K_n) = −1`. `spectralGap_top`: the gap is `n`.
* `card_edgeBoundary_top`: `|∂S| = |S| |Sᶜ|`, so the cut bound is an equality for every `S`.
* `edgeExpansion_top`: `h(K_n) = ⌈n/2⌉`.

The best constant in the easy side:
* `forall_mul_spectralGap_le_edgeExpansion_iff`: on `n ≥ 2` vertices, `c (d − λ₂) ≤ h(G)` for
  every regular `G` iff `c ≤ ⌈n/2⌉/n`. `forall_isSpectralExpander_isEdgeExpander_mul_iff`: the
  same for the predicate implication "spectral expander with gap `δ ≥ 0` ⇒ `c δ`-edge-expander".
* `forall_regular_mul_spectralGap_le_edgeExpansion_iff`,
  `forall_regular_isSpectralExpander_isEdgeExpander_mul_iff`: for a fixed degree `d ≥ 1` and
  all vertex types, the best constant is `1/2`, attained by the hypercube.

## References
* R. Simoens, A. Abiad, N. van de Berg, E. Juliano, H. Reijnders, T. van Veluw, J. Wittebol,
  *The edge-isoperimetric number of graphs and their powers: approaches from spectral graph
  theory, optimization and finite geometry*, arXiv:2601.17519 (2026), Corollary 5.5: the
  equality characterisation (presumably under a standing connectivity assumption: some such
  hypothesis is needed, and here it is the positive gap).
* W. H. Haemers, *Interlacing eigenvalues and graphs*, Linear Algebra Appl. 226 (1995)
  593–616, Theorem 3.5: the cut bound and its equality case.
* S. Bezrukov, R. Elsässer, B. Monien, R. Preis, J.-P. Tillich, *New spectral lower bounds on
  the bisection width of graphs*, Theoret. Comput. Sci. 320 (2004) 155–174: the bisection-width
  version of the equality case.
* B. Mohar, *Isoperimetric numbers of graphs*, J. Combin. Theory Ser. B 47 (1989) 274–291:
  the easy side, and `h(K_n) = ⌈n/2⌉`.
* M. Fiedler, *Algebraic connectivity of graphs*, Czechoslovak Math. J. 23 (1973) 298–305, and
  N. Alon, V. D. Milman, *λ₁, isoperimetric inequalities for graphs, and superconcentrators*,
  J. Combin. Theory Ser. B 38 (1985) 73–88: the cut bound.
* D. Spielman, *Spectral Graph Theory*, lecture notes (2009), Lecture 7, Theorem 7.1.1: the cut
  bound for every `S`.
-/

open Finset Matrix

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian)

/-- If `λ₂ < λ₁` and `w` is a nonzero top eigenvector, a vector `x ⟂ w` has no component along
the top vector of the eigenbasis. -/
private theorem coeff_topIndex_eq_zero_of_secondEigenvalue_lt [Nontrivial n] {w : n → ℝ}
    (hw : w ≠ 0) (hAw : A *ᵥ w = hA.largestEigenvalue • w)
    (hlt : hA.secondEigenvalue < hA.largestEigenvalue) {x : n → ℝ} (hx : x ⬝ᵥ w = 0) :
    hA.coeff x (topIndex n) = 0 := by
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

/-- **Equality in Courant–Fischer for `λ₂`.** Let `w` be a nonzero eigenvector for the largest
eigenvalue `λ₁`. If `x ⟂ w` attains the variational bound `xᵀAx ≤ λ₂ · xᵀx`
(`dotProduct_mulVec_le_second`) with equality, then `x` is an eigenvector for `λ₂`:
`A x = λ₂ x`.

No gap `λ₂ < λ₁` is assumed: when `λ₂ = λ₁` the conclusion says `x` lies in the top eigenspace.
`x = 0` is allowed (both sides are `0`). The hypothesis `w ≠ 0` cannot be dropped: for `w = 0`
the orthogonality condition is empty, and `x = (1, 0, 1)` with `A = diag(1, 0, −1)` has
`xᵀAx = 0 = λ₂ · xᵀx` but `A x ≠ 0`. -/
theorem mulVec_eq_secondEigenvalue_smul_of_eq [Nontrivial n] {w : n → ℝ} (hw : w ≠ 0)
    (hAw : A *ᵥ w = hA.largestEigenvalue • w) {x : n → ℝ} (hx : x ⬝ᵥ w = 0)
    (heq : x ⬝ᵥ A *ᵥ x = hA.secondEigenvalue * (x ⬝ᵥ x)) :
    A *ᵥ x = hA.secondEigenvalue • x := by
  have hnn : ∀ j ∈ (univ : Finset n),
      0 ≤ (hA.secondEigenvalue - hA.eigenvalues j) * hA.coeff x j ^ 2 := by
    intro j _
    by_cases hj : j = topIndex n
    · rcases hA.secondEigenvalue_le_largestEigenvalue.eq_or_lt with h | hlt
      · rw [hj, eigenvalues_topIndex, h, sub_self, zero_mul]
      · rw [hj, coeff_topIndex_eq_zero_of_secondEigenvalue_lt hA hw hAw hlt hx]
        simp
    · exact mul_nonneg (sub_nonneg.mpr (hA.eigenvalues_le_secondEigenvalue hj)) (sq_nonneg _)
  have hsum : ∑ j, (hA.secondEigenvalue - hA.eigenvalues j) * hA.coeff x j ^ 2 = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hA.sum_sq_coeff,
      ← hA.dotProduct_mulVec_eq_sum, heq, sub_self]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  have hy : ∀ j, hA.coeff (A *ᵥ x - hA.secondEigenvalue • x) j
      = (hA.eigenvalues j - hA.secondEigenvalue) * hA.coeff x j := by
    intro j
    have h1 : hA.coeff (A *ᵥ x - hA.secondEigenvalue • x) j
        = hA.coeff (A *ᵥ x) j - hA.coeff (hA.secondEigenvalue • x) j := by
      simp [coeff, dotProduct_sub]
    rw [h1, coeff_mulVec, coeff_smul]
    ring
  have hzero : (A *ᵥ x - hA.secondEigenvalue • x) ⬝ᵥ (A *ᵥ x - hA.secondEigenvalue • x) = 0 := by
    rw [← hA.sum_sq_coeff]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hy]
    have := hterm j (mem_univ j)
    linear_combination (hA.secondEigenvalue - hA.eigenvalues j) * this
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hzero)

end Matrix.IsHermitian

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Cut vectors and cross degrees -/

omit [Fintype V] in
/-- The **cut vector** `χ_S` of a vertex set `S`: `1` on `S` and `-1` off `S`. -/
def cutVector (S : Finset V) : V → ℝ := fun v => if v ∈ S then 1 else -1

variable (G) in
/-- The **cross degree** `c_S(v)` of a vertex `v` for the cut `(S, Sᶜ)`: the number of neighbours
of `v` on the other side of the cut. For `S = ∅` or `S = univ` it is `0` at every vertex. -/
def crossDegree (S : Finset V) (v : V) : ℕ :=
  #{u ∈ G.neighborFinset v | (u ∈ S ↔ v ∉ S)}

omit [Fintype V] in
/-- `χ_S(v)² = 1`. -/
theorem cutVector_apply_mul_self (S : Finset V) (v : V) : cutVector S v * cutVector S v = 1 := by
  unfold cutVector; split_ifs <;> norm_num

omit [Fintype V] in
/-- A cut vector has no zero entry. -/
theorem cutVector_apply_ne_zero (S : Finset V) (v : V) : cutVector S v ≠ 0 := by
  unfold cutVector; split_ifs <;> norm_num

/-- `χ_S ⬝ χ_S = n`, the number of vertices. -/
theorem cutVector_dotProduct_self (S : Finset V) :
    cutVector S ⬝ᵥ cutVector S = Fintype.card V := by
  simp [dotProduct, cutVector_apply_mul_self]

/-- `Σ_v χ_S(v) = 2|S| − n`. The subtraction is in `ℝ`, so it is negative when `2|S| < n`. -/
theorem sum_cutVector (S : Finset V) :
    ∑ v, cutVector S v = 2 * #S - Fintype.card V := by
  have h : ∀ v, cutVector S v = 2 * (if v ∈ S then (1 : ℝ) else 0) - 1 := by
    intro v; unfold cutVector; split_ifs <;> norm_num
  have h1 : ∑ v : V, (if v ∈ S then (1 : ℝ) else 0) = #S := by simp
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, Finset.sum_const, card_univ,
    nsmul_eq_mul, mul_one]

/-- The quadratic form of a cut vector counts boundary edges: in a `d`-regular graph on `n`
vertices, `χ_Sᵀ A χ_S = d n − 4 |∂S|` (a real subtraction). Every `S`, every `d` (including
`d = 0`, where both sides are `0`) and every vertex type (including the empty one) is allowed. -/
theorem cutVector_dotProduct_adjMatrix_mulVec (hd : G.IsRegularOfDegree d) (S : Finset V) :
    cutVector S ⬝ᵥ G.adjMatrix ℝ *ᵥ cutVector S
      = d * Fintype.card V - 4 * #(G.edgeBoundary S) := by
  have hlap := sum_adj_sub_sq_div_two hd (cutVector S)
  have hind := sum_adj_indicator_sub_sq (G := G) S (1 / 2)
  have hterm : ∀ u v, (if G.Adj u v then (cutVector S u - cutVector S v) ^ 2 else 0)
      = 4 * (if G.Adj u v then
        (((if u ∈ S then (1 : ℝ) else 0) - 1 / 2) - ((if v ∈ S then (1 : ℝ) else 0) - 1 / 2)) ^ 2
        else 0) := by
    intro u v
    by_cases ha : G.Adj u v <;> by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
      simp [cutVector, ha, hu, hv] <;> norm_num
  simp only [hterm, ← Finset.mul_sum] at hlap
  rw [cutVector_dotProduct_self] at hlap
  linarith

omit [DecidableEq V] in
/-- In a `d`-regular graph the column sums of the adjacency matrix are `d`:
`Σ_v (A x)_v = d Σ_v x_v`. -/
private theorem sum_adjMatrix_mulVec_of_regular (hd : G.IsRegularOfDegree d) (x : V → ℝ) :
    ∑ v, (G.adjMatrix ℝ *ᵥ x) v = d * ∑ v, x v := by
  have h := dotProduct_mulVec (1 : V → ℝ) (G.adjMatrix ℝ) x
  rw [← mulVec_transpose, transpose_adjMatrix, adjMatrix_mulVec_one_of_regular hd,
    one_dotProduct, smul_dotProduct, one_dotProduct, smul_eq_mul] at h
  exact h

/-- **The eigen-equation of a cut vector, vertex by vertex.** In a `d`-regular graph,
`(A χ_S)(v) = χ_S(v) · (d − 2 c_S(v))`, where `c_S(v)` is the cross degree. The subtraction is
in `ℝ`. -/
theorem adjMatrix_mulVec_cutVector_apply (hd : G.IsRegularOfDegree d) (S : Finset V) (v : V) :
    (G.adjMatrix ℝ *ᵥ cutVector S) v = cutVector S v * (d - 2 * G.crossDegree S v) := by
  rw [adjMatrix_mulVec_apply]
  have hsplit : ∑ u ∈ G.neighborFinset v, cutVector S u
      = (#{u ∈ G.neighborFinset v | u ∈ S} : ℝ) - #{u ∈ G.neighborFinset v | u ∉ S} := by
    simp only [cutVector]
    rw [Finset.sum_ite]
    simp [sub_eq_add_neg]
  have htot : #{u ∈ G.neighborFinset v | u ∈ S} + #{u ∈ G.neighborFinset v | u ∉ S} = d := by
    rw [card_filter_add_card_filter_not, card_neighborFinset_eq_degree, hd v]
  have htot' : (#{u ∈ G.neighborFinset v | u ∈ S} : ℝ) + #{u ∈ G.neighborFinset v | u ∉ S}
      = d := by exact_mod_cast htot
  rw [hsplit]
  by_cases hv : v ∈ S
  · have hc : G.crossDegree S v = #{u ∈ G.neighborFinset v | u ∉ S} := by
      unfold crossDegree
      congr 1
      exact Finset.filter_congr fun u _ => by simp [hv]
    rw [hc]
    simp only [cutVector, hv, if_true]
    linarith
  · have hc : G.crossDegree S v = #{u ∈ G.neighborFinset v | u ∈ S} := by
      unfold crossDegree
      congr 1
      exact Finset.filter_congr fun u _ => by simp [hv]
    rw [hc]
    simp only [cutVector, hv, if_false]
    linarith

/-- **Counting form of the eigen-equation.** In a `d`-regular graph, `χ_S` is an eigenvector
with eigenvalue `μ` exactly when every vertex has cross degree `(d − μ)/2`. Any real `μ` is
allowed; for `μ` with `(d − μ)/2` not a natural number both sides are false. -/
theorem adjMatrix_mulVec_cutVector_eq_iff (hd : G.IsRegularOfDegree d) (S : Finset V) (μ : ℝ) :
    G.adjMatrix ℝ *ᵥ cutVector S = μ • cutVector S ↔
      ∀ v, (G.crossDegree S v : ℝ) = (d - μ) / 2 := by
  constructor
  · intro h v
    have h1 := congrFun h v
    rw [adjMatrix_mulVec_cutVector_apply hd, Pi.smul_apply, smul_eq_mul, mul_comm μ] at h1
    have h2 := mul_left_cancel₀ (cutVector_apply_ne_zero S v) h1
    linarith
  · intro h
    ext v
    rw [adjMatrix_mulVec_cutVector_apply hd, Pi.smul_apply, smul_eq_mul, h v]
    ring

/-! ### The cut bound -/

/-- **The spectral cut bound.** In a `d`-regular graph on `n` vertices, every vertex set `S`
(of any size) satisfies `(d − λ₂) · |S| · |Sᶜ| / n ≤ |∂S|`, that is
`|∂S| ≥ gap · |S| (n − |S|) / n`.

`S = ∅` and `S = univ` give `0 ≤ 0`. `n ≥ 2` by `Nontrivial V`, so the division is genuine.
The complete graph attains equality for every `S` (`card_edgeBoundary_top`, `spectralGap_top`).
For `d = 0` the gap is `0` and the bound is trivial. -/
theorem spectralGap_mul_card_mul_card_compl_le [Nontrivial V] (hd : G.IsRegularOfDegree d)
    (S : Finset V) :
    G.spectralGap * (#S * #Sᶜ) / Fintype.card V ≤ #(G.edgeBoundary S) := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hc : (#Sᶜ : ℝ) = Fintype.card V - #S := by
    rw [card_compl, Nat.cast_sub (card_le_univ S)]
  -- Test vector: the indicator of `S`, shifted to be orthogonal to the all-ones vector.
  let x : V → ℝ := fun v => (if v ∈ S then (1 : ℝ) else 0) - #S / Fintype.card V
  have h1 : ∑ v : V, (if v ∈ S then (1 : ℝ) else 0) = #S := by simp
  have hsum : ∑ v, x v = 0 := by
    simp only [x, Finset.sum_sub_distrib, h1, Finset.sum_const, card_univ, nsmul_eq_mul]
    field_simp
    ring
  have hxx : x ⬝ᵥ x = #S * #Sᶜ / Fintype.card V := by
    have hterm : ∀ v, x v * x v = (if v ∈ S then (1 : ℝ) else 0)
        * (1 - 2 * (#S / Fintype.card V)) + (#S / Fintype.card V : ℝ) ^ 2 := by
      intro v
      by_cases hv : v ∈ S <;> simp [x, hv] <;> ring
    simp only [dotProduct, hterm, Finset.sum_add_distrib, ← Finset.sum_mul, h1, Finset.sum_const,
      card_univ, nsmul_eq_mul, hc]
    field_simp
    ring
  have key := spectralGap_mul_le hd hsum
  rw [hxx, sum_adj_indicator_sub_sq] at key
  rw [mul_div_assoc]
  exact key

/-- **Easy Cheeger with the sharp constant, set form.** A `d`-regular graph on `n` vertices is a
`(d − λ₂) · ⌈n/2⌉ / n`-edge-expander. Here `⌈n/2⌉` is written `(n + 1) / 2` in `ℕ` (rounding
down), and `n ≥ 2` by `Nontrivial V`, so the division by `n` is genuine. Since
`⌈n/2⌉ / n ≥ 1/2`, this sharpens `isEdgeExpander_spectralGap_div_two`, strictly for odd `n`. -/
theorem isEdgeExpander_spectralGap_mul_ceil [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    G.IsEdgeExpander (G.spectralGap * ((Fintype.card V + 1) / 2 : ℕ) / Fintype.card V) := by
  intro S hS
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hcut := spectralGap_mul_card_mul_card_compl_le hd S
  have hc : (Fintype.card V + 1) / 2 ≤ #Sᶜ := by rw [card_compl]; omega
  have hc' : (((Fintype.card V + 1) / 2 : ℕ) : ℝ) ≤ #Sᶜ := by exact_mod_cast hc
  have hgap := G.spectralGap_nonneg
  calc G.spectralGap * ((Fintype.card V + 1) / 2 : ℕ) / Fintype.card V * #S
      = G.spectralGap * (#S * ((Fintype.card V + 1) / 2 : ℕ)) / Fintype.card V := by ring
    _ ≤ G.spectralGap * (#S * #Sᶜ) / Fintype.card V := by gcongr
    _ ≤ #(G.edgeBoundary S) := hcut

/-- **Easy Cheeger with the sharp constant**: `(d − λ₂) · ⌈n/2⌉ / n ≤ h(G)` for a `d`-regular
graph on `n ≥ 2` vertices (`⌈n/2⌉` is `(n + 1) / 2` in `ℕ`). The constant is best possible for
each `n` (`forall_mul_spectralGap_le_edgeExpansion_iff`). -/
theorem spectralGap_mul_ceil_div_le_edgeExpansion [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    G.spectralGap * ((Fintype.card V + 1) / 2 : ℕ) / Fintype.card V ≤ G.edgeExpansion :=
  (isEdgeExpander_spectralGap_mul_ceil hd).le_edgeExpansion

/-- **Easy Cheeger with the sharp constant, predicate form.** A `d`-regular spectral expander
with gap `δ` on `n ≥ 2` vertices is a `δ · ⌈n/2⌉ / n`-edge-expander (`⌈n/2⌉` is `(n + 1) / 2`
in `ℕ`). No sign condition on `δ` is needed. -/
theorem IsSpectralExpander.isEdgeExpander_ceil [Nontrivial V] {δ : ℝ}
    (h : G.IsSpectralExpander d δ) :
    G.IsEdgeExpander (δ * ((Fintype.card V + 1) / 2 : ℕ) / Fintype.card V) :=
  (isEdgeExpander_spectralGap_mul_ceil h.1).mono (by gcongr; exact h.2)

/-! ### When the easy side is an equality -/

variable (G) in
/-- The Cheeger constant is attained: on `n ≥ 2` vertices some nonempty `S` with `2|S| ≤ n` has
`h(G) = |∂S| / |S|` (a genuine division, as `S ≠ ∅`). On fewer than two vertices no such `S`
exists and `h(G)` is the junk value `0`, which is why `Nontrivial V` is assumed. No regularity
is needed. -/
theorem exists_edgeExpansion_eq [Nontrivial V] : ∃ S : Finset V, S.Nonempty ∧
    2 * #S ≤ Fintype.card V ∧ G.edgeExpansion = #(G.edgeBoundary S) / #S := by
  have : Nonempty {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V} :=
    ⟨⟨{Classical.arbitrary V}, singleton_nonempty _, by
      have := Fintype.one_lt_card (α := V)
      rw [card_singleton]; omega⟩⟩
  obtain ⟨⟨S, hne, hS⟩, h⟩ := exists_eq_ciInf_of_finite
    (f := fun S : {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V} =>
      (#(G.edgeBoundary S.1) : ℝ) / #S.1)
  exact ⟨S, hne, hS, h.symm⟩

/-- **A cut vector that is a `λ₂`-eigenvector is balanced when the gap is positive.** In a
`d`-regular graph with `λ₂ < d`, if `A χ_S = λ₂ χ_S` then `2|S| = n`. The gap hypothesis is
needed: when `λ₂ = d` (for instance for a disconnected graph, which includes every graph with
`d = 0`), `S = ∅` and every union of components also satisfy `A χ_S = λ₂ χ_S`. -/
theorem two_mul_card_eq_of_cutVector [Nontrivial V] (hd : G.IsRegularOfDegree d)
    (hgap : 0 < G.spectralGap) {S : Finset V}
    (hA : G.adjMatrix ℝ *ᵥ cutVector S = G.secondAdjEigenvalue • cutVector S) :
    2 * #S = Fintype.card V := by
  have h := sum_adjMatrix_mulVec_of_regular hd (cutVector S)
  rw [hA] at h
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h
  rw [spectralGap_eq hd] at hgap
  have hz : ((d : ℝ) - G.secondAdjEigenvalue) * ∑ v, cutVector S v = 0 := by
    linear_combination -h
  have hsum := (mul_eq_zero.mp hz).resolve_left hgap.ne'
  rw [sum_cutVector] at hsum
  have h2 : (2 * #S : ℝ) = Fintype.card V := by linarith
  exact_mod_cast h2

/-- **Equality case (a): edges of an eigencut.** In a `d`-regular graph, if the cut vector of `S`
is an eigenvector for `λ₂`, then `|∂S| = (d − λ₂)/2 · |S|`.

No balance or gap hypothesis is needed. When the gap is positive, `S` is automatically balanced
(`two_mul_card_eq_of_cutVector`). When the gap is `0` both sides are `0`. `S = ∅` is allowed (the
hypothesis then forces `λ₂ = d`). -/
theorem card_edgeBoundary_eq_of_cutVector [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {S : Finset V}
    (hA : G.adjMatrix ℝ *ᵥ cutVector S = G.secondAdjEigenvalue • cutVector S) :
    (#(G.edgeBoundary S) : ℝ) = G.spectralGap / 2 * #S := by
  have hq := cutVector_dotProduct_adjMatrix_mulVec hd S
  rw [hA, dotProduct_smul, smul_eq_mul, cutVector_dotProduct_self] at hq
  have h4 : 4 * (#(G.edgeBoundary S) : ℝ) = G.spectralGap * Fintype.card V := by
    rw [spectralGap_eq hd]; linarith
  rcases G.spectralGap_nonneg.eq_or_lt with h0 | hpos
  · rw [← h0] at h4 ⊢
    linarith
  · have hN : (Fintype.card V : ℝ) = 2 * #S := by
      exact_mod_cast (two_mul_card_eq_of_cutVector hd hpos hA).symm
    rw [hN] at h4
    linarith

/-- **Equality case (a): an eigencut forces `h(G) = (d − λ₂)/2`.** If some cut vector `χ_S` of a
`d`-regular graph is an eigenvector for `λ₂`, the easy side of Cheeger's inequality is an
equality. Any `S` is allowed. When the gap `d − λ₂` is `0` (for instance `d = 0`, or a
disconnected graph) the equality `h(G) = 0` holds regardless of `S`, by the hard side of
Cheeger's inequality (`edgeExpansion_le_sqrt`). -/
theorem edgeExpansion_eq_of_cutVector [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {S : Finset V}
    (hA : G.adjMatrix ℝ *ᵥ cutVector S = G.secondAdjEigenvalue • cutVector S) :
    G.edgeExpansion = G.spectralGap / 2 := by
  rcases G.spectralGap_nonneg.eq_or_lt with h0 | hpos
  · have h1 := edgeExpansion_le_sqrt hd
    rw [← h0, mul_zero, Real.sqrt_zero] at h1
    rw [← h0, zero_div]
    exact le_antisymm h1 G.edgeExpansion_nonneg
  · have hbal := two_mul_card_eq_of_cutVector hd hpos hA
    have hne : S.Nonempty := by
      rw [← Finset.card_pos]
      have := Fintype.one_lt_card (α := V)
      omega
    have hs : (0 : ℝ) < #S := by exact_mod_cast hne.card_pos
    refine le_antisymm ?_ (spectralGap_div_two_le_edgeExpansion hd)
    calc G.edgeExpansion ≤ #(G.edgeBoundary S) / #S := G.edgeExpansion_le hne hbal.le
      _ = G.spectralGap / 2 := by
        rw [card_edgeBoundary_eq_of_cutVector hd hA]
        field_simp

/-- **Equality case (b): a set meeting the easy bound is a balanced eigencut.** Let `G` be
`d`-regular on `n` vertices with positive gap `d − λ₂`. If a nonempty `S` with `2|S| ≤ n` has
`|∂S| ≤ (d − λ₂)/2 · |S|`, then `S` is balanced (`2|S| = n`) and its cut vector is an
eigenvector for `λ₂`.

Both `S ≠ ∅` and the gap hypothesis are needed. `S = ∅` satisfies the inequality, and for gap `0`
the union `C₃ + C₅` has a minimiser (the triangle) that is not balanced. -/
theorem balanced_of_card_edgeBoundary_le [Nontrivial V] (hd : G.IsRegularOfDegree d)
    (hgap : 0 < G.spectralGap) {S : Finset V} (hne : S.Nonempty)
    (hS : 2 * #S ≤ Fintype.card V)
    (hle : (#(G.edgeBoundary S) : ℝ) ≤ G.spectralGap / 2 * #S) :
    2 * #S = Fintype.card V ∧
      G.adjMatrix ℝ *ᵥ cutVector S = G.secondAdjEigenvalue • cutVector S := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hs : (0 : ℝ) < #S := by exact_mod_cast hne.card_pos
  have hc : (#Sᶜ : ℝ) = Fintype.card V - #S := by
    rw [card_compl, Nat.cast_sub (card_le_univ S)]
  have hcut := spectralGap_mul_card_mul_card_compl_le hd S
  -- `gap · |S| (n − |S|) / n ≤ |∂S| ≤ gap |S| / 2` forces `2|S| ≥ n`.
  have hbal : 2 * #S = Fintype.card V := by
    rw [div_le_iff₀ hn, hc] at hcut
    have h2 : (Fintype.card V : ℝ) ≤ 2 * #S := by nlinarith [mul_pos hgap hs]
    have : Fintype.card V ≤ 2 * #S := by exact_mod_cast h2
    omega
  refine ⟨hbal, ?_⟩
  have hN : (Fintype.card V : ℝ) = 2 * #S := by exact_mod_cast hbal.symm
  have hsum : ∑ v, cutVector S v = 0 := by rw [sum_cutVector, hN]; ring
  have hxA : cutVector S ⬝ᵥ G.adjMatrix ℝ *ᵥ cutVector S
      = G.secondAdjEigenvalue * (cutVector S ⬝ᵥ cutVector S) := by
    refine le_antisymm (dotProduct_adjMatrix_mulVec_le hd hsum) ?_
    rw [cutVector_dotProduct_self, cutVector_dotProduct_adjMatrix_mulVec hd, hN]
    rw [spectralGap_eq hd] at hle
    linarith
  have h1v : (1 : V → ℝ) ≠ 0 := fun h => one_ne_zero (congrFun h (Classical.arbitrary V))
  have hAw : G.adjMatrix ℝ *ᵥ (1 : V → ℝ)
      = (G.isHermitian_adjMatrix ℝ).largestEigenvalue • (1 : V → ℝ) := by
    rw [adjMatrix_mulVec_one_of_regular hd]
    exact congrArg (· • (1 : V → ℝ)) (largestAdjEigenvalue_eq hd).symm
  have hx1 : cutVector S ⬝ᵥ (1 : V → ℝ) = 0 := by rw [dotProduct_one, hsum]
  exact (G.isHermitian_adjMatrix ℝ).mulVec_eq_secondEigenvalue_smul_of_eq h1v hAw hx1 hxA

/-- **Equality case (b), minimiser form.** If `h(G) = (d − λ₂)/2 > 0` for a `d`-regular graph,
then every minimiser of the Cheeger ratio (a nonempty `S` with `2|S| ≤ n` and
`|∂S| ≤ h(G) |S|`) is balanced and its cut vector is an eigenvector for `λ₂`. -/
theorem balanced_of_edgeExpansion_eq [Nontrivial V] (hd : G.IsRegularOfDegree d)
    (hgap : 0 < G.spectralGap) (heq : G.edgeExpansion = G.spectralGap / 2)
    {S : Finset V} (hne : S.Nonempty) (hS : 2 * #S ≤ Fintype.card V)
    (hmin : (#(G.edgeBoundary S) : ℝ) ≤ G.edgeExpansion * #S) :
    2 * #S = Fintype.card V ∧
      G.adjMatrix ℝ *ᵥ cutVector S = G.secondAdjEigenvalue • cutVector S :=
  balanced_of_card_edgeBoundary_le hd hgap hne hS (heq ▸ hmin)

/-- **When the easy side of Cheeger is an equality.** For a `d`-regular graph on `n ≥ 2`
vertices with positive gap `d − λ₂`: `h(G) = (d − λ₂)/2` if and only if there is a balanced cut
(`2|S| = n`) at which every vertex has exactly `(d − λ₂)/2` neighbours across the cut.

The gap hypothesis is needed for the forward direction: `C₃ + C₅` has gap `0` and `h = 0`, but no
balanced cut without crossing edges. (`edgeExpansion_eq_spectralGap_div_two_iff_exists` drops
both the gap hypothesis and the balance condition.) -/
theorem edgeExpansion_eq_spectralGap_div_two_iff [Nontrivial V] (hd : G.IsRegularOfDegree d)
    (hgap : 0 < G.spectralGap) :
    G.edgeExpansion = G.spectralGap / 2 ↔ ∃ S : Finset V, 2 * #S = Fintype.card V ∧
      ∀ v, (G.crossDegree S v : ℝ) = G.spectralGap / 2 := by
  have hc : ∀ S : Finset V, (G.adjMatrix ℝ *ᵥ cutVector S = G.secondAdjEigenvalue • cutVector S
      ↔ ∀ v, (G.crossDegree S v : ℝ) = G.spectralGap / 2) := by
    intro S
    rw [adjMatrix_mulVec_cutVector_eq_iff hd, spectralGap_eq hd]
  constructor
  · intro heq
    obtain ⟨S, hne, hS, hS'⟩ := exists_edgeExpansion_eq G
    have hpos : (0 : ℝ) < #S := by exact_mod_cast hne.card_pos
    have hmin : (#(G.edgeBoundary S) : ℝ) ≤ G.edgeExpansion * #S := by
      rw [hS', div_mul_cancel₀ _ hpos.ne']
    obtain ⟨hbal, hA⟩ := balanced_of_edgeExpansion_eq hd hgap heq hne hS hmin
    exact ⟨S, hbal, (hc S).mp hA⟩
  · rintro ⟨S, -, hcnt⟩
    exact edgeExpansion_eq_of_cutVector hd ((hc S).mpr hcnt)

/-- **When the easy side of Cheeger is an equality, without a gap hypothesis.** For a `d`-regular
graph on `n ≥ 2` vertices, `h(G) = (d − λ₂)/2` if and only if some cut `(S, Sᶜ)` has every
vertex with exactly `(d − λ₂)/2` neighbours across it.

When the gap is `0` both sides hold (the witness is `S = ∅`, whose cross degrees are all `0`, and
`h(G) = 0` by the hard side of Cheeger's inequality). When the gap is positive the witness is
automatically balanced (`two_mul_card_eq_of_cutVector`). -/
theorem edgeExpansion_eq_spectralGap_div_two_iff_exists [Nontrivial V]
    (hd : G.IsRegularOfDegree d) :
    G.edgeExpansion = G.spectralGap / 2 ↔
      ∃ S : Finset V, ∀ v, (G.crossDegree S v : ℝ) = G.spectralGap / 2 := by
  constructor
  · intro heq
    rcases G.spectralGap_nonneg.eq_or_lt with h0 | hpos
    · exact ⟨∅, fun v => by simp [crossDegree, ← h0]⟩
    · obtain ⟨S, -, hS⟩ := (edgeExpansion_eq_spectralGap_div_two_iff hd hpos).mp heq
      exact ⟨S, hS⟩
  · rintro ⟨S, hcnt⟩
    refine edgeExpansion_eq_of_cutVector hd ((adjMatrix_mulVec_cutVector_eq_iff hd S _).mpr ?_)
    intro v
    rw [hcnt v, spectralGap_eq hd]

/-- **Corollary (i): odd order forces strict inequality.** A `d`-regular graph on an odd number
of vertices with positive gap has `(d − λ₂)/2 < h(G)`. The gap hypothesis is needed: for gap `0`
both sides are `0`. -/
theorem spectralGap_div_two_lt_edgeExpansion_of_odd [Nontrivial V] (hd : G.IsRegularOfDegree d)
    (hgap : 0 < G.spectralGap) (hodd : Odd (Fintype.card V)) :
    G.spectralGap / 2 < G.edgeExpansion := by
  refine lt_of_le_of_ne (spectralGap_div_two_le_edgeExpansion hd) fun heq => ?_
  obtain ⟨S, hbal, -⟩ := (edgeExpansion_eq_spectralGap_div_two_iff hd hgap).mp heq.symm
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **Corollary (ii): equality forces integrality.** If a `d`-regular graph with positive gap has
`h(G) = (d − λ₂)/2`, then `h(G)` is a positive integer `k` and `λ₂ = d − 2k` (a real
subtraction). The integer `k` is the common cross degree of the balanced cut of
`edgeExpansion_eq_spectralGap_div_two_iff`. -/
theorem exists_nat_of_edgeExpansion_eq_spectralGap_div_two [Nontrivial V]
    (hd : G.IsRegularOfDegree d) (hgap : 0 < G.spectralGap)
    (heq : G.edgeExpansion = G.spectralGap / 2) :
    ∃ k : ℕ, 1 ≤ k ∧ G.edgeExpansion = k ∧ G.secondAdjEigenvalue = d - 2 * k := by
  obtain ⟨S, -, hcnt⟩ := (edgeExpansion_eq_spectralGap_div_two_iff hd hgap).mp heq
  set v := Classical.arbitrary V
  refine ⟨G.crossDegree S v, ?_, by rw [heq, hcnt v], ?_⟩
  · have h : (0 : ℝ) < G.crossDegree S v := by rw [hcnt v]; linarith
    exact_mod_cast h
  · rw [hcnt v]; have := spectralGap_eq hd (G := G); linarith

/-- **Corollary (iii): a small gap forces strict inequality.** A `d`-regular graph with gap
`0 < d − λ₂ < 2` has `(d − λ₂)/2 < h(G)`, since equality would make `(d − λ₂)/2` a positive
integer. For gap `0` both sides are `0`. -/
theorem spectralGap_div_two_lt_edgeExpansion_of_lt_two [Nontrivial V]
    (hd : G.IsRegularOfDegree d) (hgap : 0 < G.spectralGap) (h2 : G.spectralGap < 2) :
    G.spectralGap / 2 < G.edgeExpansion := by
  refine lt_of_le_of_ne (spectralGap_div_two_le_edgeExpansion hd) fun heq => ?_
  obtain ⟨k, hk, hh, -⟩ := exists_nat_of_edgeExpansion_eq_spectralGap_div_two hd hgap heq.symm
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- The hypercube `Q_{n+1}` has a balanced cut at which every vertex has exactly one neighbour
across, as the equality `h(Q_{n+1}) = 1 = gap/2` (`hypercube_edgeExpansion`,
`hypercube_spectralGap`) forces through `edgeExpansion_eq_spectralGap_div_two_iff`. The
dimension is written `n + 1` because `Q₀` has a single vertex, where `λ₂` and the gap are not
defined. -/
theorem hypercube_exists_crossDegree_eq_one (n : ℕ) :
    ∃ S : Finset (Fin (n + 1) → Bool), 2 * #S = Fintype.card (Fin (n + 1) → Bool) ∧
      ∀ v, (hypercube (n + 1)).crossDegree S v = 1 := by
  have hd := hypercube_isRegularOfDegree (n + 1)
  have hgap := hypercube_spectralGap n
  obtain ⟨S, hS, hc⟩ := (edgeExpansion_eq_spectralGap_div_two_iff hd (by rw [hgap]; norm_num)).mp
    (by rw [hypercube_edgeExpansion, hgap]; norm_num)
  refine ⟨S, hS, fun v => ?_⟩
  have h := hc v
  rw [hgap] at h
  exact_mod_cast (h.trans (by norm_num) : ((hypercube (n + 1)).crossDegree S v : ℝ) = 1)

/-! ### The complete graph -/

/-- In the complete graph, `A x = −x` for every `x` with `Σ x = 0`. -/
private theorem adjMatrix_top_mulVec_of_sum_eq_zero {x : V → ℝ} (hx : ∑ v, x v = 0) :
    (⊤ : SimpleGraph V).adjMatrix ℝ *ᵥ x = -x := by
  ext i
  rw [adjMatrix_mulVec_apply, neighborFinset_top, Pi.neg_apply]
  have h := Finset.sum_compl_add_sum {i} x
  rw [sum_singleton, hx] at h
  linarith

/-- **The second eigenvalue of the complete graph** `K_n` is `−1`. Here `n ≥ 2` by
`Nontrivial V`; on one vertex `λ₂` is not defined. -/
theorem secondAdjEigenvalue_top [Nontrivial V] :
    (⊤ : SimpleGraph V).secondAdjEigenvalue = -1 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨x, hx, hx0, hle⟩ := exists_sum_eq_zero_secondAdjEigenvalue_mul_le (⊤ : SimpleGraph V)
    rw [adjMatrix_top_mulVec_of_sum_eq_zero hx0, dotProduct_neg] at hle
    have hpos := Matrix.IsHermitian.dotProduct_self_pos hx
    nlinarith
  · obtain ⟨u, v, huv⟩ := exists_pair_ne V
    set x : V → ℝ := Pi.single u 1 - Pi.single v 1 with hx_def
    have hx0 : ∑ w, x w = 0 := by simp [x, Finset.sum_sub_distrib]
    have hx : x ≠ 0 := by
      intro h
      have := congrFun h u
      simp [x, huv] at this
    have hle := dotProduct_adjMatrix_mulVec_le IsRegularOfDegree.top hx0
    rw [adjMatrix_top_mulVec_of_sum_eq_zero hx0, dotProduct_neg] at hle
    have hpos := Matrix.IsHermitian.dotProduct_self_pos hx
    nlinarith

/-- **The spectral gap of the complete graph** `K_n` (`n ≥ 2`) is `n`: it is `(n − 1)`-regular
with `λ₂ = −1`. The degree `n − 1` is a natural-number subtraction, which does not truncate
since `n ≥ 1`. -/
theorem spectralGap_top [Nontrivial V] :
    (⊤ : SimpleGraph V).spectralGap = Fintype.card V := by
  rw [spectralGap_eq IsRegularOfDegree.top, secondAdjEigenvalue_top,
    Nat.cast_sub Fintype.card_pos]
  push_cast
  ring

/-- In the complete graph every pair `(u, v)` with `u ∈ S`, `v ∉ S` is a boundary edge:
`|∂S| = |S| · |Sᶜ|`. Every `S` and every vertex type is allowed. With `spectralGap_top`, this
says that `K_n` attains the cut bound `spectralGap_mul_card_mul_card_compl_le` for every `S`. -/
theorem card_edgeBoundary_top (S : Finset V) :
    #((⊤ : SimpleGraph V).edgeBoundary S) = #S * #Sᶜ := by
  rw [edgeBoundary, interedges_def, Finset.filter_true_of_mem, card_product]
  rintro ⟨u, v⟩ h
  simp only [mem_product, mem_compl] at h
  exact (top_adj u v).mpr fun huv => h.2 (huv ▸ h.1)

/-- **The Cheeger constant of the complete graph** `K_n` (`n ≥ 2`) is `⌈n/2⌉`, written
`(n + 1) / 2` in `ℕ` (rounding down). It is attained by any `S` with `|S| = ⌊n/2⌋`, which is
nonempty because `n ≥ 2`. On one vertex `h` would be the junk value `0`, which is why
`Nontrivial V` is assumed. -/
theorem edgeExpansion_top [Nontrivial V] :
    (⊤ : SimpleGraph V).edgeExpansion = ((Fintype.card V + 1) / 2 : ℕ) := by
  have h1 := Fintype.one_lt_card (α := V)
  refine le_antisymm ?_ ?_
  · obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq
      (show Fintype.card V / 2 ≤ #(univ : Finset V) by rw [card_univ]; omega)
    have hne : S.Nonempty := by rw [← card_pos, hS]; omega
    have h2 : 2 * #S ≤ Fintype.card V := by rw [hS]; omega
    have hle := (⊤ : SimpleGraph V).edgeExpansion_le hne h2
    have hpos : (0 : ℝ) < (Fintype.card V / 2 : ℕ) := by
      have : 0 < Fintype.card V / 2 := by omega
      exact_mod_cast this
    have hsub : Fintype.card V - Fintype.card V / 2 = (Fintype.card V + 1) / 2 := by omega
    rw [card_edgeBoundary_top, card_compl, hS, hsub, Nat.cast_mul,
      mul_div_cancel_left₀ _ hpos.ne'] at hle
    exact hle
  · refine IsEdgeExpander.le_edgeExpansion fun S hS => ?_
    rw [card_edgeBoundary_top, card_compl]
    have h : (Fintype.card V + 1) / 2 * #S ≤ #S * (Fintype.card V - #S) := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ (by omega)
    exact_mod_cast h

/-! ### The best constant in the easy side of Cheeger -/

/-- **The best constant for a fixed number of vertices.** On a vertex type with `n ≥ 2`
elements, `c · (d − λ₂) ≤ h(G)` holds for every regular graph `G` if and only if
`c ≤ ⌈n/2⌉ / n` (with `⌈n/2⌉` written `(n + 1) / 2` in `ℕ`). The complete graph shows that the
constant cannot be improved. Negative `c` are allowed; they always satisfy both sides. -/
theorem forall_mul_spectralGap_le_edgeExpansion_iff [Nontrivial V] {c : ℝ} :
    (∀ (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ), H.IsRegularOfDegree k →
      c * H.spectralGap ≤ H.edgeExpansion) ↔
    c ≤ ((Fintype.card V + 1) / 2 : ℕ) / Fintype.card V := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  constructor
  · intro h
    have h' := h ⊤ _ IsRegularOfDegree.top
    rw [spectralGap_top, edgeExpansion_top] at h'
    rw [le_div_iff₀ hn]
    exact h'
  · intro hc H _ k hk
    calc c * H.spectralGap
        ≤ (((Fintype.card V + 1) / 2 : ℕ) / Fintype.card V : ℝ) * H.spectralGap :=
          mul_le_mul_of_nonneg_right hc H.spectralGap_nonneg
      _ = H.spectralGap * ((Fintype.card V + 1) / 2 : ℕ) / Fintype.card V := by ring
      _ ≤ H.edgeExpansion := spectralGap_mul_ceil_div_le_edgeExpansion hk

/-- **The best constant in the predicate form, for a fixed number of vertices.** On a vertex
type with `n ≥ 2` elements, "every regular spectral expander with gap `δ ≥ 0` is a
`c δ`-edge-expander" holds if and only if `c ≤ ⌈n/2⌉ / n` (with `⌈n/2⌉` written `(n + 1) / 2`
in `ℕ`).

The restriction `0 ≤ δ` matters only for negative `c`: every regular graph is a spectral
expander with any gap `δ < 0`, and `c δ` is then positive, so without it negative `c` would
fail. -/
theorem forall_isSpectralExpander_isEdgeExpander_mul_iff [Nontrivial V] {c : ℝ} :
    (∀ (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ) (δ : ℝ), 0 ≤ δ →
      H.IsSpectralExpander k δ → H.IsEdgeExpander (c * δ)) ↔
    c ≤ ((Fintype.card V + 1) / 2 : ℕ) / Fintype.card V := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  constructor
  · intro h
    have h' := (h ⊤ _ (Fintype.card V) hn.le
      ⟨IsRegularOfDegree.top, spectralGap_top.ge⟩).le_edgeExpansion
    rw [edgeExpansion_top] at h'
    rw [le_div_iff₀ hn]
    exact h'
  · intro hc H _ k δ hδ hH
    refine (hH.isEdgeExpander_ceil).mono ?_
    calc c * δ ≤ (((Fintype.card V + 1) / 2 : ℕ) / Fintype.card V : ℝ) * δ :=
          mul_le_mul_of_nonneg_right hc hδ
      _ = δ * ((Fintype.card V + 1) / 2 : ℕ) / Fintype.card V := by ring

/-- **The best constant for a fixed degree `d ≥ 1`.** "`c · (d − λ₂) ≤ h(G)` for every
`d`-regular graph `G` on at least two vertices" holds if and only if `c ≤ 1/2`. The hypercube
`Q_d` shows that `1/2` cannot be improved. For `d = 0` every `c` works (both sides of the
inequality are `0`), which is why `1 ≤ d` is assumed. -/
theorem forall_regular_mul_spectralGap_le_edgeExpansion_iff (hd : 1 ≤ d) {c : ℝ} :
    (∀ (W : Type) [Fintype W] [DecidableEq W] [Nontrivial W] (H : SimpleGraph W)
      [DecidableRel H.Adj], H.IsRegularOfDegree d → c * H.spectralGap ≤ H.edgeExpansion) ↔
    c ≤ 1 / 2 := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    have h' := h _ (hypercube (k + 1)) (hypercube_isRegularOfDegree (k + 1))
    rw [hypercube_spectralGap, hypercube_edgeExpansion] at h'
    linarith
  · intro hc W _ _ _ H _ hH
    calc c * H.spectralGap ≤ 1 / 2 * H.spectralGap :=
          mul_le_mul_of_nonneg_right hc H.spectralGap_nonneg
      _ = H.spectralGap / 2 := by ring
      _ ≤ H.edgeExpansion := spectralGap_div_two_le_edgeExpansion hH

/-- **The best constant in the predicate form, for a fixed degree `d ≥ 1`.** "Every `d`-regular
spectral expander with gap `δ ≥ 0`, on at least two vertices, is a `c δ`-edge-expander" holds if
and only if `c ≤ 1/2`. So the constant `1/2` of `IsSpectralExpander.isEdgeExpander` is best
possible. The hypercube `Q_d` is the extremal example. For `d = 0` every `c` works, and the
restriction `0 ≤ δ` matters only for negative `c` (see
`forall_isSpectralExpander_isEdgeExpander_mul_iff`). -/
theorem forall_regular_isSpectralExpander_isEdgeExpander_mul_iff (hd : 1 ≤ d) {c : ℝ} :
    (∀ (W : Type) [Fintype W] [DecidableEq W] [Nontrivial W] (H : SimpleGraph W)
      [DecidableRel H.Adj] (δ : ℝ), 0 ≤ δ → H.IsSpectralExpander d δ →
        H.IsEdgeExpander (c * δ)) ↔
    c ≤ 1 / 2 := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    have h' := (h _ (hypercube (k + 1)) 2 (by norm_num)
      ⟨hypercube_isRegularOfDegree (k + 1), (hypercube_spectralGap k).ge⟩).le_edgeExpansion
    rw [hypercube_edgeExpansion] at h'
    linarith
  · intro hc W _ _ _ H _ δ hδ hH
    refine hH.isEdgeExpander.mono ?_
    calc c * δ ≤ 1 / 2 * δ := mul_le_mul_of_nonneg_right hc hδ
      _ = δ / 2 := by ring

end SimpleGraph
