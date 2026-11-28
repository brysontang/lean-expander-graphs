/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.SimplexRigidity
import Expanders.CompleteComplexGeneral

/-!
# Optimal weights on the complete complex

Let `N = Fintype.card ι`, `1 ≤ d`, `K = complete ι d` (all nonempty sets of at most `d + 1`
points), and `lam* = −1/(N − 1)`. No `d`-dimensional local spectral expander on `N` vertices has a
parameter below `lam*`, and the complete complex with every top face of weight `1` attains it
(`isLeast_setOf_isLocalSpectralExpanderOf`). Call a top weight `m` of `K` **optimal** if `K` with
the weight `m` is a `lam*`-local spectral expander, and **pair-balanced** if `faceWeight m {u, v}`
is the same for all pairs of distinct points, that is, if `m` is a real-weighted
`2`-`(N, d + 1)` design. This file determines which weights are optimal, as far as is proved
below.

## Main results

All declarations are in the namespace `PreAbstractSimplicialComplex.OptimalWeights`.

**(i) Characterisation.** `isLocalSpectralExpanderOf_complete_neg_one_div_iff`: `m` is optimal
exactly when (a) `m` is pair-balanced and (b) the link of every `σ` with `1 ≤ |σ| ≤ d − 1` has walk
second eigenvalue at most `lam*`. (a) alone does not imply (b): `fin_six_counterexample`
(`N = 6`, `d = 2`, `m = 1 + (101/1000) z` fails at the vertex link of the point `0`).

**(ii) Rigidity versus flexibility.**
`forall_isLocalSpectralExpanderOf_complete_eq_mul_uniformWeight_iff`: every optimal weight is a
positive multiple of the uniform weight exactly when `d = 1` or `N ≤ d + 3`. The two halves are
`exists_eq_mul_uniformWeight_of_isLocalSpectralExpanderOf_complete` and
`exists_isLocalSpectralExpanderOf_complete_ne_mul_uniformWeight`.

**(iii) The optimal set, for `d ≥ 2` and `N ≥ d + 4`.** Proved:
* it is closed under positive scaling (`isLocalSpectralExpanderOf_const_mul`, any complex and
  parameter);
* it is relatively closed in the cone of top weights, hence in the pair-balanced cone
  (`exists_isClosed_isLocalSpectralExpanderOf_iff`, any complex and parameter);
* every pair-balanced `m` with `min m ≥ (1 − 1/(N − 1)²) · max m` is optimal
  (`isLocalSpectralExpanderOf_complete_of_ratio`), so the optimal set contains a neighbourhood of
  the uniform weight in the pair-balanced cone
  (`exists_nhds_uniformWeight_isLocalSpectralExpanderOf`);
* for the minimal `2`-trade `z` (`tradeWeight`) and `1 + δ z` (`uniformAddTrade`): if `1 + δ z` is
  optimal then `|δ| ≤ (d − 1)/(2(N − 1))`
  (`two_mul_abs_le_of_isLocalSpectralExpanderOf_uniformAddTrade`), with the bound coming from the
  regular link of `{a₁} ∪ S` (`abs_le_of_walkSecondEigenvalueLE_uniformAddTrade`). Conversely
  `1 + δ z` is optimal when `(2(N − 1)² − 1)|δ| ≤ 1`
  (`isLocalSpectralExpanderOf_uniformAddTrade`), in particular when `|δ| ≤ 1/(2N²)`
  (`isLocalSpectralExpanderOf_uniformAddTrade_of_abs_le`);
* the vertex-link constraints are convex for every `d` (`convex_setOf_vertexLinks`), and for
  `d ≤ 2` the optimal set is a convex cone (`convex_setOf_isLocalSpectralExpanderOf_complete`).

## What is not proved here

These parts of the statement are omitted. The file compiles without them.
* **The dimension.** The claim that the projectivised optimal set has dimension exactly
  `C(N, d + 1) − C(N, 2)`. It needs the full row rank of the pairs-versus-`(d + 1)`-sets inclusion
  matrix (Gottlieb, Kantor, Wilson), which is not in Mathlib. Proved here: the optimal set
  contains the segment of weights `1 + δ z` with `|δ| ≤ 1/(2N²)`, so its projectivisation has
  dimension at least `1`.
* **Semialgebraicity.** Mathlib has no notion of semialgebraic set. The closed set of
  `exists_isClosed_isLocalSpectralExpanderOf_iff` is given by inequalities that are polynomial in
  `m` and a test function `f`, but the quantifier over `f` is not eliminated.
* **Sufficiency in the trade threshold.** The claim that `1 + δ z` is optimal for every
  `|δ| ≤ (d − 1)/(2(N − 1))`. It was verified exactly for `N ≤ 14` and by closed forms per link
  type for `N ≤ 40`, but it has no general proof, on paper or here. Formalized: the comparison
  range above, and necessity.
* **Non-convexity for `N = 7`, `d = 3`.** Two exactly certified optimal weights have a midpoint
  that is not optimal. The certificate has a margin of about `7 · 10⁻⁷`, and formalizing it would
  need exact positive-semidefiniteness certificates for 28 links of each weight.
* **The spectrahedral form for `d = 2`.** The file proves convexity and the regularity of the
  vertex links (`sum_linkWeightOf_singleton_of_pairBalanced`), which is what the linear matrix
  inequality `M_x + (c/(N − 1)) I − (cN/(N − 1)²) J ⪯ 0` expresses. It does not state the matrix
  inequality itself.

## Proof notes

For (i), the case `σ = ∅` is the equality case of the trace bound,
`walkSecondEigenvalueLE_neg_one_div_card_iff` in `Expanders/SimplexRigidity.lean`. The underlying
graph has no loops and all `N` degrees positive, so it attains `−1/(N − 1)` exactly when all
pairs carry one weight.

For the rigid half of (ii), with `k = N − d − 1 ≤ 2` the weight of a top face `F` is an
alternating sum, over subsets of its complement, of the weights of sets with at most two points
(`eq_sum_powerset_compl_faceWeight`). Pair balance makes these depend only on the size of the set.
This one argument covers `N = d + 1`, `N = d + 2` and `N = d + 3`, and replaces the Kneser-graph
computation of the original sketch.

For the flexible half, the minimal trade on three disjoint pairs and a stem `S` of `d − 2` points
is pair-balanced with value `0`. Two points miss one of the three pairs, and switching the choice
in that pair is a sign-reversing involution. Small multiples of the trade are optimal by a
comparison lemma for random walks (`walkSecondEigenvalueLE_of_le_of_le`): if
`a · w ≤ w' ≤ b · w`, the spectral gap shrinks by at most the factor `a / b`. Every nonempty link
of the uniform weight has the strictly smaller value `−1/(N − 1 − |σ|)`, which leaves the room.

## How this was found

The statement was found by computation. A search over weights on complete complexes was followed
by two independent skeptic passes, which re-implemented `faceWeight`, `linkWeightOf` and
`WalkSecondEigenvalueLE` as exact positive-semidefiniteness tests. They checked:
* the null-space dimension for 112 pairs `(N, d)`;
* the exact trade threshold for 45 pairs with `N ≤ 14`, and closed forms by link type up to
  `N = 40`;
* the `N = 6` example, and the `N = 7`, `d = 3` non-convexity certificate.

Neither pass refuted any part. The parts listed above were then proved here.

## Literature

The search consisted of web searches in this session and in the skeptic passes, about 25 queries
in all. They covered: weighted high-dimensional expanders, optimal and non-uniform weights on the
complete complex, designs and trades in high-dimensional expanders, the weighted equality case of
the trace bound, and Lean formalizations. The skeptic passes fetched and searched these papers:
Oppenheim, arXiv:1709.04431 and arXiv:1407.8517; Kaufman–Oppenheim, arXiv:1707.02799; Alev–Lau,
arXiv:2001.02827; Liu–Mohanty–Yang, arXiv:1907.10771; Golowich, arXiv:2105.09358; Bauer–Jost,
arXiv:0910.3118; Graham–Li–Li 1980.

**What was found.** Every ingredient is classical.
* Part (i) is the equality case of the trace bound: F. Chung, *Spectral Graph Theory*, Lemma 1.7;
  Bauer–Jost, Section 2.
* Part (ii) is the existence theory of null designs. Nonzero null `2`-designs on `(d + 1)`-sets
  exist exactly when `d ≥ 2` and `N ≥ d + 4`: J. E. Graver, W. B. Jurkat, *The module structure of
  integral designs*, J. Combin. Theory Ser. A 15 (1973); R. L. Graham, S.-Y. R. Li, W.-C. W. Li,
  *On the structure of t-designs*, SIAM J. Algebraic Discrete Methods 1 (1980). In the latter, the
  family of generators is empty exactly when `v ≤ k + t` or `k ≤ t`. The trade `z` used here is
  their standard minimal trade.
* The dimension in (iii) is the rank of the inclusion matrix (Gottlieb, Kantor, Wilson).

**What was not found.** The search found no paper on high-dimensional expanders that states
(i)–(iii). Since each follows in a few lines from the classical facts above, they should be regarded
as a corollary, not as new mathematics. The explicit constants were not found in the search either
(the radius is simply what the standard comparison argument gives, and is not best possible):
* the radius `1 − 1/(N − 1)²`;
* the trade threshold `(d − 1)/(2(N − 1))`, whose sufficiency is unproved in general;
* the `δ = 101/1000` example.
-/

open Finset

variable {ι : Type*} [Fintype ι]

namespace PreAbstractSimplicialComplex.OptimalWeights

/-- **The Dirichlet form.** For symmetric `w`, with `deg u = Σ_v w u v`,
`Σ_{u,v} w u v (f u − f v)² = 2 (Σ_u deg u · f u² − Σ_{u,v} w u v f u f v)`. No sign condition on
`w`. -/
theorem sum_sum_mul_sub_sq_eq {w : ι → ι → ℝ} (hsymm : ∀ u v, w u v = w v u) (f : ι → ℝ) :
    ∑ u, ∑ v, w u v * (f u - f v) ^ 2 =
      2 * (∑ u, (∑ v, w u v) * f u ^ 2 - ∑ u, ∑ v, w u v * f u * f v) := by
  have h1 : ∑ u, ∑ v, w u v * f v ^ 2 = ∑ u, (∑ v, w u v) * f u ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ => by rw [hsymm]
  have h3 : ∑ u, ∑ v, w u v * f u ^ 2 = ∑ u, (∑ v, w u v) * f u ^ 2 := by
    simp only [Finset.sum_mul]
  have h2 : ∑ u, ∑ v, w u v * (f u - f v) ^ 2 =
      ∑ u, ∑ v, w u v * f u ^ 2 + ∑ u, ∑ v, w u v * f v ^ 2 -
        2 * ∑ u, ∑ v, w u v * f u * f v := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [h2, h1, h3]
  ring

/-- **Comparison of random walks.** Let `w` and `w'` be symmetric, `w ≥ 0`, and
`a · w ≤ w' ≤ b · w` entrywise with `a, b > 0`. If the walk on `w` has second eigenvalue at most
`lam ≤ 1`, then the walk on `w'` has second eigenvalue at most `1 − (a / b) (1 − lam)`: the
spectral gap `1 − lam` shrinks by at most the factor `a / b`.

The Dirichlet form of `w'` is at least `a` times that of `w`, and for `f` of `deg'`-mean zero,
`Σ deg' f² ≤ Σ deg' (f − μ)² ≤ b Σ deg (f − μ)²`, where `μ` is the `deg`-mean of `f`. The weights
`w'` are nonnegative by the hypotheses. If `w = 0` then `w' = 0` and every bound holds. The
hypothesis `lam ≤ 1` makes `1 − lam ≥ 0`; for `lam > 1` the conclusion would exceed `1`, a bound
that every symmetric nonnegative weight satisfies anyway. -/
theorem walkSecondEigenvalueLE_of_le_of_le {w w' : ι → ι → ℝ} {lam a b : ℝ}
    (hsymm : ∀ u v, w u v = w v u) (hsymm' : ∀ u v, w' u v = w' v u)
    (hnn : ∀ u v, 0 ≤ w u v) (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ u v, a * w u v ≤ w' u v) (hhi : ∀ u v, w' u v ≤ b * w u v)
    (hlam : lam ≤ 1) (h : WalkSecondEigenvalueLE w lam) :
    WalkSecondEigenvalueLE w' (1 - a / b * (1 - lam)) := by
  intro f hf
  have hdeg : ∀ u, 0 ≤ ∑ v, w u v := fun u => sum_nonneg fun v _ => hnn u v
  have hnn' : ∀ u v, 0 ≤ w' u v := fun u v => le_trans (mul_nonneg ha.le (hnn u v)) (hlo u v)
  have hdeg' : ∀ u, 0 ≤ ∑ v, w' u v := fun u => sum_nonneg fun v _ => hnn' u v
  have hdegb : ∀ u, ∑ v, w' u v ≤ b * ∑ v, w u v := fun u => by
    rw [mul_sum]; exact sum_le_sum fun v _ => hhi u v
  obtain ⟨D, hD⟩ : ∃ D, D = ∑ u, ∑ v, w u v := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hD ▸ sum_nonneg fun u _ => hdeg u
  rcases hD0.eq_or_lt with hD0 | hD0
  · -- no edges
    have hw0 : ∀ u v, w u v = 0 := by
      intro u v
      have h1 : ∑ v, w u v = 0 := by
        have := (sum_eq_zero_iff_of_nonneg fun x _ => hdeg x).mp (by rw [← hD, hD0]) u (mem_univ u)
        exact this
      exact (sum_eq_zero_iff_of_nonneg fun x _ => hnn u x).mp h1 v (mem_univ v)
    have hw0' : ∀ u v, w' u v = 0 := fun u v =>
      le_antisymm (by simpa [hw0] using hhi u v) (hnn' u v)
    simp [hw0']
  · obtain ⟨μ, hμ⟩ : ∃ μ, μ = (∑ u, (∑ v, w u v) * f u) / D := ⟨_, rfl⟩
    have hg : ∑ u, (∑ v, w u v) * (f u - μ) = 0 := by
      have e : ∑ u, (∑ v, w u v) * (f u - μ) = ∑ u, (∑ v, w u v) * f u - μ * D := by
        rw [hD, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun u _ => by ring
      rw [e, hμ, div_mul_cancel₀ _ hD0.ne']
      ring
    have h1 := h (fun u => f u - μ) hg
    -- Dirichlet forms
    have hE := sum_sum_mul_sub_sq_eq hsymm (fun u => f u - μ)
    have hE' := sum_sum_mul_sub_sq_eq hsymm' f
    have hshift : ∑ u, ∑ v, w u v * ((f u - μ) - (f v - μ)) ^ 2 =
        ∑ u, ∑ v, w u v * (f u - f v) ^ 2 :=
      Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    have hcmp : a * ∑ u, ∑ v, w u v * (f u - f v) ^ 2 ≤ ∑ u, ∑ v, w' u v * (f u - f v) ^ 2 := by
      rw [Finset.mul_sum]
      refine sum_le_sum fun u _ => ?_
      rw [Finset.mul_sum]
      refine sum_le_sum fun v _ => ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hlo u v) (sq_nonneg _)
    -- norms
    have hn1 : ∑ u, (∑ v, w' u v) * f u ^ 2 ≤ ∑ u, (∑ v, w' u v) * (f u - μ) ^ 2 := by
      have e : ∑ u, (∑ v, w' u v) * (f u - μ) ^ 2 =
          ∑ u, (∑ v, w' u v) * f u ^ 2 - 2 * μ * ∑ u, (∑ v, w' u v) * f u +
            μ ^ 2 * ∑ u, ∑ v, w' u v := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun u _ => by ring
      rw [e, hf, mul_zero, sub_zero]
      have : 0 ≤ μ ^ 2 * ∑ u, ∑ v, w' u v :=
        mul_nonneg (sq_nonneg _) (sum_nonneg fun u _ => hdeg' u)
      linarith
    have hn2 : ∑ u, (∑ v, w' u v) * (f u - μ) ^ 2 ≤ b * ∑ u, (∑ v, w u v) * (f u - μ) ^ 2 := by
      rw [Finset.mul_sum]
      refine sum_le_sum fun u _ => ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hdegb u) (sq_nonneg _)
    -- combine
    set Ng := ∑ u, (∑ v, w u v) * (f u - μ) ^ 2 with hNg
    set Nf' := ∑ u, (∑ v, w' u v) * f u ^ 2 with hNf'
    have hNg0 : 0 ≤ Ng := sum_nonneg fun u _ => mul_nonneg (hdeg u) (sq_nonneg _)
    have hr : 0 ≤ a / b * (1 - lam) := mul_nonneg (div_nonneg ha.le hb.le) (by linarith)
    have hk : a / b * (1 - lam) * Nf' ≤ a * (1 - lam) * Ng := by
      have := mul_le_mul_of_nonneg_left (hn1.trans hn2) hr
      calc a / b * (1 - lam) * Nf' ≤ a / b * (1 - lam) * (b * Ng) := this
        _ = a * (1 - lam) * Ng := by field_simp
    have hEg : 2 * (1 - lam) * Ng ≤ ∑ u, ∑ v, w u v * (f u - f v) ^ 2 := by
      rw [← hshift, hE]
      linarith
    have hfin : 2 * (a * (1 - lam) * Ng) ≤ ∑ u, ∑ v, w' u v * (f u - f v) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hEg ha.le
      linarith
    rw [hE'] at hfin
    nlinarith

section

variable [DecidableEq ι]

/-- `faceWeight` is additive in the weight. No hypothesis. -/
theorem faceWeight_add (m m' : Finset ι → ℝ) (s : Finset ι) :
    faceWeight (fun F => m F + m' F) s = faceWeight m s + faceWeight m' s :=
  Finset.sum_add_distrib

/-- `faceWeight` is homogeneous in the weight. No hypothesis. -/
theorem faceWeight_const_mul (c : ℝ) (m : Finset ι → ℝ) (s : Finset ι) :
    faceWeight (fun F => c * m F) s = c * faceWeight m s :=
  (Finset.mul_sum _ _ _).symm

/-- `faceWeight` is monotone in the weight. No hypothesis. -/
theorem faceWeight_mono {m m' : Finset ι → ℝ} (h : ∀ F, m F ≤ m' F) (s : Finset ι) :
    faceWeight m s ≤ faceWeight m' s :=
  Finset.sum_le_sum fun F _ => h F

/-- Link weights are additive in the weight. No hypothesis. -/
theorem linkWeightOf_add (m m' : Finset ι → ℝ) (σ : Finset ι) (u v : ι) :
    linkWeightOf (fun F => m F + m' F) σ u v = linkWeightOf m σ u v + linkWeightOf m' σ u v := by
  unfold linkWeightOf
  split_ifs
  · exact faceWeight_add m m' _
  · ring

/-- Link weights are homogeneous in the weight. No hypothesis. -/
theorem linkWeightOf_const_mul (c : ℝ) (m : Finset ι → ℝ) (σ : Finset ι) (u v : ι) :
    linkWeightOf (fun F => c * m F) σ u v = c * linkWeightOf m σ u v := by
  unfold linkWeightOf
  split_ifs
  · exact faceWeight_const_mul c m _
  · ring

/-- Link weights are monotone in the weight. No hypothesis. -/
theorem linkWeightOf_mono {m m' : Finset ι → ℝ} (h : ∀ F, m F ≤ m' F) (σ : Finset ι) (u v : ι) :
    linkWeightOf m σ u v ≤ linkWeightOf m' σ u v := by
  unfold linkWeightOf
  split_ifs
  · exact faceWeight_mono h _
  · exact le_rfl

variable {d : ℕ} {m : Finset ι → ℝ}

omit [DecidableEq ι] in
/-- A top weight of `complete ι d` forces `d + 1 ≤ N`, where `N = Fintype.card ι`: on fewer
points the complete complex is empty (`N = 0`) or not pure of dimension `d`. -/
theorem card_le_of_isTopWeight_complete (hm : (complete ι d).IsTopWeight d m) :
    d + 1 ≤ Fintype.card ι := by
  obtain ⟨F, -, hF, -⟩ := hm.exists_pos
  rw [← hF]
  exact card_le_univ F

/-- **The whole complex is optimal exactly for pair-balanced weights.** Let `m` be a top weight of
the complete `d`-dimensional complex on `N = Fintype.card ι` points. Its weighted underlying graph
has walk second eigenvalue at most `−1/(N − 1)` exactly when all pairs `{u, v}` of distinct points
have the same weight `faceWeight m {u, v}`, that is, when `m` is a real-weighted `2`-`(N, d + 1)`
design.

This is the equality case of the trace bound, `walkSecondEigenvalueLE_neg_one_div_card_iff`: for
`d ≥ 1` every point is a vertex of positive degree, so the walk lives on all `N` points, and the
graph has no loops. Degenerate case: `d = 0` is allowed; then the graph has no edges and every
pair has weight `0`, so both sides hold. The subtraction `N − 1` is in `ℝ`. -/
theorem walkSecondEigenvalueLE_linkWeightOf_empty_complete_iff
    (hm : (complete ι d).IsTopWeight d m) :
    WalkSecondEigenvalueLE (linkWeightOf m ∅) (-(1 / ((Fintype.card ι : ℝ) - 1))) ↔
      ∃ c, ∀ u v : ι, u ≠ v → faceWeight m {u, v} = c := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- dimension `0`: no edges, and every pair has weight `0`
    exact ⟨fun _ => ⟨0, fun u v huv => faceWeight_eq_zero_of_lt_card hm.card_eq_of_ne_zero
      (by rw [card_pair huv]; omega)⟩, fun _ => walkSecondEigenvalueLE_of_forall_eq_zero
        (linkWeightOf_eq_zero_of_le_card hm.card_eq_of_ne_zero (Nat.zero_le _)) _⟩
  have hN := card_le_of_isTopWeight_complete hm
  have hP : ({u | 0 < ∑ v, linkWeightOf m ∅ u v} : Finset ι) = univ := by
    ext u
    simp only [mem_filter, mem_univ, true_and, iff_true]
    exact (hm.sum_linkWeightOf_empty_pos_iff hd).mpr
      (mem_complete.mpr ⟨singleton_nonempty u, by rw [card_singleton]; omega⟩)
  have h2 : 2 ≤ #({u | 0 < ∑ v, linkWeightOf m ∅ u v} : Finset ι) := by
    rw [hP, card_univ]; omega
  have key := walkSecondEigenvalueLE_neg_one_div_card_iff (linkWeightOf_symm m ∅)
    (linkWeightOf_nonneg hm.nonneg ∅) h2
  rw [hP, card_univ] at key
  rw [key]
  have hlw : ∀ u v, u ≠ v → linkWeightOf m ∅ u v = faceWeight m {u, v} := by
    intro u v huv
    unfold linkWeightOf
    rw [if_pos ⟨huv, notMem_empty u, notMem_empty v⟩, insert_empty]
  have hpos : ∀ u, 0 < ∑ x, linkWeightOf m ∅ u x := fun u => by
    have : u ∈ ({u | 0 < ∑ v, linkWeightOf m ∅ u v} : Finset ι) := by rw [hP]; exact mem_univ u
    exact (mem_filter.mp this).2
  constructor
  · rintro ⟨-, c, -, hc⟩
    exact ⟨c, fun u v huv => (hlw u v huv).symm.trans (hc u v huv (hpos u) (hpos v))⟩
  · rintro ⟨c, hc⟩
    refine ⟨linkWeightOf_self m ∅, c, ?_, fun u v huv _ _ => (hlw u v huv).trans (hc u v huv)⟩
    obtain ⟨u, v, huv⟩ : ∃ u v : ι, u ≠ v := Fintype.exists_pair_of_one_lt_card (by omega)
    obtain ⟨F, hsF, -, hF⟩ := exists_subsuperset_card_eq (n := d + 1)
      (subset_univ ({u, v} : Finset ι)) (by rw [card_pair huv]; omega) (by rw [card_univ]; exact hN)
    rw [← hc u v huv]
    exact hm.faceWeight_pos_iff.mpr
      ⟨F, mem_complete.mpr ⟨card_pos.mp (by omega), by omega⟩, hF, hsF⟩

/-- **Optimal weights on the complete complex, part (i).** Let `1 ≤ d`, let `m` be a top weight of
the complete `d`-dimensional complex on `N = Fintype.card ι` points, and `lam* = −1/(N − 1)`, the
least parameter of any `d`-dimensional expander on `N` vertices
(`isLeast_setOf_isLocalSpectralExpanderOf`). With the weight `m`, the complete complex is a
`lam*`-local spectral expander exactly when
* (a) all pairs of distinct points have the same weight `faceWeight m {u, v}`, and
* (b) for every `σ` with `1 ≤ |σ| ≤ d − 1` the link of `σ` has walk second eigenvalue at most
  `lam*`.

(a) is the instance `σ = ∅` (`walkSecondEigenvalueLE_linkWeightOf_empty_complete_iff`), and (b) is
the rest of the definition, since every nonempty set of at most `d + 1` points is a face. (a) does
not imply (b): `fin_six_counterexample`.

Degenerate cases: `d + 1 ≤ N` follows from `hm`. For `d = 1`, (b) is vacuous. The hypothesis
`1 ≤ d` is needed: no complex is a `0`-dimensional expander
(`not_isLocalSpectralExpanderOf_zero`), while (a) and (b) hold for every `0`-dimensional top
weight. -/
theorem isLocalSpectralExpanderOf_complete_neg_one_div_iff (hd : 1 ≤ d)
    (hm : (complete ι d).IsTopWeight d m) :
    (complete ι d).IsLocalSpectralExpanderOf d m (-(1 / ((Fintype.card ι : ℝ) - 1))) ↔
      (∃ c, ∀ u v : ι, u ≠ v → faceWeight m {u, v} = c) ∧
        ∀ σ : Finset ι, 1 ≤ #σ → #σ + 1 ≤ d →
          WalkSecondEigenvalueLE (linkWeightOf m σ) (-(1 / ((Fintype.card ι : ℝ) - 1))) := by
  rw [← walkSecondEigenvalueLE_linkWeightOf_empty_complete_iff hm]
  constructor
  · intro h
    exact ⟨h.walkSecondEigenvalueLE (Or.inl rfl) (by rw [card_empty]; omega),
      fun σ h1 hσ => h.walkSecondEigenvalueLE
        (Or.inr (mem_complete.mpr ⟨card_pos.mp (by omega), by omega⟩)) hσ⟩
  · rintro ⟨h0, h1⟩
    refine ⟨hd, hm, fun σ _ hcard => ?_⟩
    rcases σ.eq_empty_or_nonempty with rfl | hne
    · exact h0
    · exact h1 σ (card_pos.mpr hne) hcard

/-! ### Rigidity: few points force the uniform weight -/

/-- A set `F` with `d + 1` elements is the only set with `d + 1` elements containing it. So if `m`
vanishes off the sets with `d + 1` elements, the weight `faceWeight m F` is `m F`. -/
theorem faceWeight_eq_of_card_eq (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {F : Finset ι}
    (hF : #F = d + 1) : faceWeight m F = m F := by
  unfold faceWeight
  refine Finset.sum_eq_single_of_mem F (by simp) fun G hG hGF => ?_
  by_contra h
  have hsub := (mem_filter.mp hG).2
  exact hGF (eq_of_subset_of_card_le hsub (by rw [hcard G h, hF])).symm

/-- **Inclusion–exclusion over the complement.** If `m` vanishes off the sets with `d + 1`
elements and `#F = d + 1`, then `m F = Σ_{A ⊆ Fᶜ} (−1)^{|A|} faceWeight m A`: the right side is the
total weight of the sets disjoint from `Fᶜ`, that is, contained in `F`, and `F` is the only one
with nonzero weight. No sign condition on `m`. -/
theorem eq_sum_powerset_compl_faceWeight (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {F : Finset ι}
    (hF : #F = d + 1) :
    m F = ∑ A ∈ Fᶜ.powerset, (-1 : ℝ) ^ #A * faceWeight m A := by
  have h1 : ∀ A ∈ Fᶜ.powerset, (-1 : ℝ) ^ #A * faceWeight m A =
      ∑ G, if A ⊆ G then (-1 : ℝ) ^ #A * m G else 0 := by
    intro A _
    rw [faceWeight, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ G, ∑ A ∈ Fᶜ.powerset, (if A ⊆ G then (-1 : ℝ) ^ #A * m G else 0) =
      if G ⊆ F then m G else 0 := by
    intro G
    rw [← Finset.sum_filter]
    have e : Fᶜ.powerset.filter (fun A => A ⊆ G) = (Fᶜ ∩ G).powerset := by
      ext A
      simp only [mem_filter, mem_powerset, subset_inter_iff]
    have hz := congrArg (Int.cast : ℤ → ℝ) (sum_powerset_neg_one_pow_card (x := Fᶜ ∩ G))
    push_cast at hz
    rw [e, ← Finset.sum_mul, hz]
    have e2 : Fᶜ ∩ G = ∅ ↔ G ⊆ F := by
      constructor
      · intro h x hx
        by_contra hxF
        have : x ∈ Fᶜ ∩ G := mem_inter.mpr ⟨mem_compl.mpr hxF, hx⟩
        rw [h] at this
        exact notMem_empty x this
      · intro h
        ext x
        simp only [mem_inter, mem_compl, notMem_empty, iff_false, not_and]
        intro hx hxG
        exact hx (h hxG)
    by_cases hG : G ⊆ F
    · rw [if_pos (e2.mpr hG), if_pos hG, one_mul]
    · rw [if_neg (mt e2.mp hG), if_neg hG, zero_mul]
  rw [Finset.sum_congr rfl fun G _ => h2 G]
  rw [Finset.sum_eq_single_of_mem F (mem_univ F) fun G _ hGF => ?_, if_pos subset_rfl]
  split_ifs with hG
  · by_contra h
    exact hGF (eq_of_subset_of_card_le hG (by rw [hcard G h, hF]))
  · rfl

/-- **Pair-balanced implies point-balanced.** If `m` vanishes off the sets with `d + 1` elements and
every pair of distinct points has weight `c`, then `d · faceWeight m {u} = (N − 1) c` for every
point `u`, where `N = Fintype.card ι` (double counting, `sum_faceWeight_insert`). For `d ≥ 1` the
weight of a point is therefore `(N − 1) c / d`, the same for all points. No sign condition on `m`;
for `d = 0` both sides are `0`. -/
theorem mul_faceWeight_singleton_of_pairBalanced (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {c : ℝ}
    (hc : ∀ u v : ι, u ≠ v → faceWeight m {u, v} = c) (u : ι) :
    (d : ℝ) * faceWeight m {u} = ((Fintype.card ι : ℝ) - 1) * c := by
  have h := sum_faceWeight_insert hcard {u}
  rw [card_singleton] at h
  have e : ∀ v, (if v ∈ ({u} : Finset ι) then 0 else faceWeight m (insert v {u})) =
      c - if v = u then c else 0 := by
    intro v
    by_cases hv : v = u
    · rw [if_pos (mem_singleton.mpr hv), if_pos hv]; ring
    · rw [if_neg (by rwa [mem_singleton]), if_neg hv, sub_zero]; exact hc v u hv
  rw [Finset.sum_congr rfl fun v _ => e v, Finset.sum_sub_distrib, Finset.sum_ite_eq' univ u,
    if_pos (mem_univ u), sum_const, card_univ, nsmul_eq_mul] at h
  push_cast at h
  linarith

/-- **Rigidity: on few points, pair balance forces a constant weight.** Let `1 ≤ d`, and `d = 1` or
`N ≤ d + 3`, where `N = Fintype.card ι`. If `m` vanishes off the sets with `d + 1` elements and all
pairs of distinct points have the same weight, then `m` has the same value on all sets with `d + 1`
elements. There is no sign condition on `m` and no complex.

For `d = 1` the sets in question are the pairs themselves. Otherwise the complement of a
`(d + 1)`-set `F` has `k = N − d − 1 ≤ 2` points, and `eq_sum_powerset_compl_faceWeight` writes
`m F` as an alternating sum of weights of sets with at most `2` points. Those depend only on the
size of the set (`mul_faceWeight_singleton_of_pairBalanced`), and `k` does not depend on `F`. For
`k = 2` this replaces the Kneser-graph argument of the original proof sketch. If `N < d + 1` there
is no set with `d + 1` elements and the statement is vacuous.

Both hypotheses are needed. For `d = 0` the pairs carry no weight, so pair balance says nothing.
For `d ≥ 2` and `N ≥ d + 4` the minimal trade (`tradeWeight`) is a nonzero pair-balanced weight
supported on `(d + 1)`-sets (`faceWeight_tradeWeight_pair`). -/
theorem eq_of_pairBalanced_of_le (hd : 1 ≤ d) (hsmall : d = 1 ∨ Fintype.card ι ≤ d + 3)
    (hcard : ∀ F, m F ≠ 0 → #F = d + 1)
    (hbal : ∃ c, ∀ u v : ι, u ≠ v → faceWeight m {u, v} = c)
    {F G : Finset ι} (hF : #F = d + 1) (hG : #G = d + 1) : m F = m G := by
  obtain ⟨c, hc⟩ := hbal
  rcases hsmall with rfl | hsmall
  · obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hF
    obtain ⟨u', v', huv', rfl⟩ := card_eq_two.mp hG
    rw [← faceWeight_eq_of_card_eq hcard hF, ← faceWeight_eq_of_card_eq hcard hG, hc u v huv,
      hc u' v' huv']
  · let φ : ℕ → ℝ := fun j =>
      if j = 0 then faceWeight m ∅ else if j = 1 then ((Fintype.card ι : ℝ) - 1) * c / d else c
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have hφ : ∀ A : Finset ι, #A ≤ 2 → faceWeight m A = φ #A := by
      intro A hA
      obtain h | h | h : #A = 0 ∨ #A = 1 ∨ #A = 2 := by omega
      · rw [card_eq_zero.mp h]
        simp [φ]
      · obtain ⟨u, rfl⟩ := card_eq_one.mp h
        have := mul_faceWeight_singleton_of_pairBalanced hcard hc u
        simp only [φ, card_singleton, one_ne_zero, if_false, if_true]
        rw [eq_div_iff hd0]
        linarith
      · obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp h
        simp only [φ, h, OfNat.ofNat_ne_zero, if_false, OfNat.ofNat_ne_one]
        exact hc u v huv
    have key : ∀ H : Finset ι, #H = d + 1 → m H =
        ∑ j ∈ range (Fintype.card ι - (d + 1) + 1),
          (Fintype.card ι - (d + 1)).choose j • ((-1 : ℝ) ^ j * φ j) := by
      intro H hH
      have hHc : #Hᶜ = Fintype.card ι - (d + 1) := by rw [card_compl, hH]
      rw [eq_sum_powerset_compl_faceWeight hcard hH]
      rw [Finset.sum_congr rfl fun A hA => congrArg (fun x => (-1 : ℝ) ^ #A * x)
        (hφ A (by have := card_le_card (mem_powerset.mp hA); omega))]
      rw [Finset.sum_powerset_apply_card (fun j => (-1 : ℝ) ^ j * φ j), hHc]
    rw [key F hF, key G hG]

omit [Fintype ι] [DecidableEq ι] in
/-- A top weight that takes one value on all `d`-dimensional faces of `K` is a positive multiple of
the uniform weight. Any complex `K`; the multiple is the common value, positive because `K` has a
top face. -/
theorem exists_eq_mul_uniformWeight_of_isTopWeight {K : PreAbstractSimplicialComplex ι}
    (hm : K.IsTopWeight d m)
    (heq : ∀ F G, F ∈ K → G ∈ K → #F = d + 1 → #G = d + 1 → m F = m G) :
    ∃ κ > 0, m = fun F => κ * K.uniformWeight d F := by
  obtain ⟨F0, hF0, hc0, hpos⟩ := hm.exists_pos
  refine ⟨m F0, hpos, funext fun F => ?_⟩
  unfold uniformWeight
  split_ifs with h
  · rw [mul_one]
    exact heq F F0 h.1 hF0 h.2 hc0
  · rw [mul_zero]
    exact hm.eq_zero F h

/-! ### The optimal weights form a cone -/

omit [DecidableEq ι] in
/-- Multiplying all weights by `κ > 0` does not change the random walk, so it keeps every bound on
its second eigenvalue. For `κ = 0` the conclusion holds trivially (no edges); for `κ < 0` it fails
in general, since both sides of the defining inequality change sign. -/
theorem walkSecondEigenvalueLE_const_mul {w : ι → ι → ℝ} {lam κ : ℝ}
    (h : WalkSecondEigenvalueLE w lam) (hκ : 0 < κ) :
    WalkSecondEigenvalueLE (fun u v => κ * w u v) lam := by
  intro f hf
  have e0 : ∑ u, (∑ v, κ * w u v) * f u = κ * ∑ u, (∑ v, w u v) * f u := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [← Finset.mul_sum]
    ring
  rw [e0] at hf
  have h1 := h f ((mul_eq_zero.mp hf).resolve_left hκ.ne')
  have e1 : ∑ u, ∑ v, κ * w u v * f u * f v = κ * ∑ u, ∑ v, w u v * f u * f v := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    exact sum_congr rfl fun v _ => by ring
  have e2 : ∑ u, (∑ v, κ * w u v) * f u ^ 2 = κ * ∑ u, (∑ v, w u v) * f u ^ 2 := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [← Finset.mul_sum]
    ring
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left h1 hκ.le
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- A positive multiple of a top weight is a top weight. Any complex. -/
theorem isTopWeight_const_mul {K : PreAbstractSimplicialComplex ι} (hm : K.IsTopWeight d m)
    {κ : ℝ} (hκ : 0 < κ) : K.IsTopWeight d (fun F => κ * m F) :=
  ⟨hm.isPure, hm.exists_mem, fun F hF hc => mul_pos hκ (hm.pos F hF hc),
    fun F hF => by rw [hm.eq_zero F hF, mul_zero]⟩

/-- **The weights of a `lam`-local spectral expander form a cone.** If `K` with the weight `m` is a
`lam`-local spectral expander, so is `K` with the weight `κ · m` for every `κ > 0`. Any complex,
any dimension, any `lam`; in particular the optimal weights of the complete complex are closed
under positive scaling. -/
theorem isLocalSpectralExpanderOf_const_mul {K : PreAbstractSimplicialComplex ι} {lam : ℝ}
    (h : K.IsLocalSpectralExpanderOf d m lam) {κ : ℝ} (hκ : 0 < κ) :
    K.IsLocalSpectralExpanderOf d (fun F => κ * m F) lam := by
  refine ⟨h.one_le, isTopWeight_const_mul h.isTopWeight hκ, fun σ hσ hcard => ?_⟩
  have e : linkWeightOf (fun F => κ * m F) σ = fun u v => κ * linkWeightOf m σ u v :=
    funext fun u => funext fun v => linkWeightOf_const_mul κ m σ u v
  rw [e]
  exact walkSecondEigenvalueLE_const_mul (h.walkSecondEigenvalueLE hσ hcard) hκ

/-! ### An explicit neighbourhood of the uniform weight -/

/-- **An explicit neighbourhood of the uniform weight.** Let `1 ≤ d`, let `m` be a top weight of the
complete `d`-dimensional complex on `N = Fintype.card ι` points with all pairs of the same weight,
and suppose `m F ≥ (1 − 1/(N − 1)²) · m G` for all sets `F, G` with `d + 1` elements, that is,
`min m ≥ (1 − 1/(N − 1)²) · max m` on top faces. Then `m` is optimal: the complex is a
`(−1/(N − 1))`-local spectral expander.

The link of `σ ≠ ∅` is sandwiched between `min m` and `max m` times the uniform link, the complete
graph on `N − |σ|` points with walk eigenvalue `−1/(N − 1 − |σ|)`
(`walkSecondEigenvalueLE_linkWeight_complete_iff`). The comparison lemma
`walkSecondEigenvalueLE_of_le_of_le` loses the factor `min m / max m` in the spectral gap, and the
worst case is `|σ| = 1`, where the factor `1 − 1/(N − 1)²` is exactly what is needed.

Degenerate cases: for `d = 1` no nonempty `σ` is tested and the ratio hypothesis is not used; this
includes `N = 2`, where the factor is `0`. Since only the comparison argument is used, the constant
is not the best possible for an individual `m`. -/
theorem isLocalSpectralExpanderOf_complete_of_ratio (hd : 1 ≤ d)
    (hm : (complete ι d).IsTopWeight d m)
    (hbal : ∃ c, ∀ u v : ι, u ≠ v → faceWeight m {u, v} = c)
    (hratio : ∀ F G : Finset ι, #F = d + 1 → #G = d + 1 →
      (1 - 1 / ((Fintype.card ι : ℝ) - 1) ^ 2) * m G ≤ m F) :
    (complete ι d).IsLocalSpectralExpanderOf d m (-(1 / ((Fintype.card ι : ℝ) - 1))) := by
  have hN := card_le_of_isTopWeight_complete hm
  refine (isLocalSpectralExpanderOf_complete_neg_one_div_iff hd hm).mpr ⟨hbal, fun σ hσ1 hσd => ?_⟩
  have hne : (powersetCard (d + 1) (univ : Finset ι)).Nonempty :=
    powersetCard_nonempty.mpr (by rw [card_univ]; exact hN)
  obtain ⟨F0, hF0, hmin⟩ := (powersetCard (d + 1) univ).exists_min_image m hne
  obtain ⟨G0, hG0, hmax⟩ := (powersetCard (d + 1) univ).exists_max_image m hne
  have hF0c : #F0 = d + 1 := (mem_powersetCard.mp hF0).2
  have hG0c : #G0 = d + 1 := (mem_powersetCard.mp hG0).2
  have htop : ∀ F : Finset ι, #F = d + 1 → F ∈ complete ι d := fun F hF =>
    mem_complete.mpr ⟨card_pos.mp (by omega), by omega⟩
  have ha : 0 < m F0 := hm.pos F0 (htop F0 hF0c) hF0c
  have hb : 0 < m G0 := hm.pos G0 (htop G0 hG0c) hG0c
  have hU : ∀ F, (complete ι d).uniformWeight d F = if #F = d + 1 then 1 else 0 := by
    intro F
    unfold uniformWeight
    by_cases hF : #F = d + 1
    · rw [if_pos ⟨htop F hF, hF⟩, if_pos hF]
    · rw [if_neg fun h => hF h.2, if_neg hF]
  have hzero : ∀ F : Finset ι, #F ≠ d + 1 → m F = 0 := fun F hF =>
    hm.eq_zero F fun h => hF h.2
  have hlo : ∀ F, m F0 * (complete ι d).uniformWeight d F ≤ m F := by
    intro F
    rw [hU]
    split_ifs with hF
    · rw [mul_one]
      exact hmin F (mem_powersetCard.mpr ⟨subset_univ F, hF⟩)
    · rw [mul_zero, hzero F hF]
  have hhi : ∀ F, m F ≤ m G0 * (complete ι d).uniformWeight d F := by
    intro F
    rw [hU]
    split_ifs with hF
    · rw [mul_one]
      exact hmax F (mem_powersetCard.mpr ⟨subset_univ F, hF⟩)
    · rw [mul_zero, hzero F hF]
  have hlo' : ∀ u v, m F0 * linkWeightOf ((complete ι d).uniformWeight d) σ u v ≤
      linkWeightOf m σ u v := fun u v => by
    rw [← linkWeightOf_const_mul]
    exact linkWeightOf_mono hlo σ u v
  have hhi' : ∀ u v, linkWeightOf m σ u v ≤
      m G0 * linkWeightOf ((complete ι d).uniformWeight d) σ u v := fun u v => by
    rw [← linkWeightOf_const_mul]
    exact linkWeightOf_mono hhi σ u v
  have hUσ : WalkSecondEigenvalueLE (linkWeightOf ((complete ι d).uniformWeight d) σ)
      (-(1 / ((Fintype.card ι : ℝ) - 1 - #σ))) := by
    rw [← linkWeight_eq_linkWeightOf]
    exact (walkSecondEigenvalueLE_linkWeight_complete_iff hN hσd).mpr le_rfl
  -- the real numbers involved
  have hk : (1 : ℝ) ≤ #σ := by exact_mod_cast hσ1
  have hkd : ((#σ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hσd
  have hdN : ((d + 1 : ℕ) : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  push_cast at hkd hdN
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (Fintype.card ι : ℝ) - 1 := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (Fintype.card ι : ℝ) - 1 - #σ := ⟨_, rfl⟩
  have hx1 : 1 ≤ x := by rw [hx]; linarith
  have hxy : x ≤ y - 1 := by rw [hx, hy]; linarith
  have hy2 : 2 ≤ y := by linarith
  have hlam : -(1 / ((Fintype.card ι : ℝ) - 1 - #σ)) ≤ 1 := by
    rw [← hx]
    have : 0 ≤ 1 / x := by positivity
    linarith
  have hcmp := walkSecondEigenvalueLE_of_le_of_le (linkWeightOf_symm _ σ) (linkWeightOf_symm m σ)
    (linkWeightOf_nonneg (uniformWeight_nonneg _ d) σ) ha hb hlo' hhi' hlam hUσ
  refine hcmp.mono (linkWeightOf_nonneg hm.nonneg σ) ?_
  rw [← hx, ← hy]
  have hr : 1 - 1 / y ^ 2 ≤ m F0 / m G0 := by
    have := hratio F0 G0 hF0c hG0c
    rw [← hy] at this
    rw [le_div_iff₀ hb]
    exact this
  have hr0 : 0 ≤ 1 - 1 / y ^ 2 := by
    have : 1 / y ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  have h1 : 1 + 1 / (y - 1) ≤ 1 + 1 / x := by
    have : 1 / (y - 1) ≤ 1 / x := one_div_le_one_div_of_le (by linarith) hxy
    linarith
  have h2 : (1 - 1 / y ^ 2) * (1 + 1 / (y - 1)) = 1 + 1 / y := by
    have : y - 1 ≠ 0 := by linarith
    have : y ≠ 0 := by linarith
    field_simp
    ring
  have h3 : (1 - 1 / y ^ 2) * (1 + 1 / (y - 1)) ≤ m F0 / m G0 * (1 + 1 / x) :=
    mul_le_mul hr h1 (by linarith [one_div_nonneg.mpr (by linarith : (0 : ℝ) ≤ y - 1)])
      (le_trans hr0 hr)
  have h4 : 1 - -(1 / x) = 1 + 1 / x := by ring
  rw [h4]
  have h5 : -(1 / y) = 1 - (1 + 1 / y) := by ring
  rw [h5]
  linarith

/-- **The optimal weights contain a neighbourhood of the uniform weight in the pair-balanced cone.**
For `1 ≤ d` there is a neighbourhood `V` of `uniformWeight` in `Finset ι → ℝ` (product topology)
such that every pair-balanced top weight of `complete ι d` in `V` is optimal. The proof takes the
sup-norm ball of radius `1/(2(N − 1)²)` and applies `isLocalSpectralExpanderOf_complete_of_ratio`.

Degenerate case: if `N < d + 1` there is no top weight and `V` is the whole space. Whether `V`
contains weights other than multiples of the uniform weight is part (ii): it does exactly when
`d ≥ 2` and `N ≥ d + 4`. -/
theorem exists_nhds_uniformWeight_isLocalSpectralExpanderOf (hd : 1 ≤ d) :
    ∃ V ∈ nhds ((complete ι d).uniformWeight d), ∀ m ∈ V, (complete ι d).IsTopWeight d m →
      (∃ c, ∀ u v : ι, u ≠ v → faceWeight m {u, v} = c) →
      (complete ι d).IsLocalSpectralExpanderOf d m (-(1 / ((Fintype.card ι : ℝ) - 1))) := by
  by_cases hN : d + 1 ≤ Fintype.card ι
  · obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / ((Fintype.card ι : ℝ) - 1) ^ 2 := ⟨_, rfl⟩
    have hN' : ((d + 1 : ℕ) : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast at hN'
    have hη0 : 0 < η := by
      have : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by linarith
      rw [hη]
      positivity
    have hη1 : η ≤ 1 := by
      rw [hη, div_le_one (by nlinarith)]
      nlinarith
    refine ⟨Metric.ball ((complete ι d).uniformWeight d) (η / 2),
      Metric.ball_mem_nhds _ (by positivity), fun m hmV hm hbal => ?_⟩
    rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)] at hmV
    have hclose : ∀ F : Finset ι, #F = d + 1 → |m F - 1| < η / 2 := by
      intro F hF
      have := hmV F
      rw [Real.dist_eq] at this
      unfold uniformWeight at this
      rwa [if_pos ⟨mem_complete.mpr ⟨card_pos.mp (by omega), by omega⟩, hF⟩] at this
    refine isLocalSpectralExpanderOf_complete_of_ratio hd hm hbal fun F G hF hG => ?_
    rw [← hη]
    have h1 := abs_lt.mp (hclose F hF)
    have h2 := abs_lt.mp (hclose G hG)
    have h3 : (1 - η) * m G ≤ (1 - η) * (1 + η / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  · exact ⟨Set.univ, Filter.univ_mem, fun m _ hm _ =>
      absurd (card_le_of_isTopWeight_complete hm) hN⟩

end

section

variable [DecidableEq ι]

/-! ### The minimal trade -/

/-- The face of the minimal trade selected by `c`: the set `S` together with one point `p (i, c i)`
of each of the three pairs `{p (i, false), p (i, true)}`. When `p` is injective and its range is
disjoint from `S`, these are `8` distinct sets with `#S + 3` elements (`card_tradeFace`,
`tradeFace_injective`). The definition itself has no hypotheses. -/
def tradeFace (p : Fin 3 × Bool → ι) (S : Finset ι) (c : Fin 3 → Bool) : Finset ι :=
  S ∪ univ.image fun i => p (i, c i)

/-- The sign `(−1)^{#{i | c i}}` attached to the face `tradeFace p S c`. -/
noncomputable def tradeSign (c : Fin 3 → Bool) : ℝ := ∏ i, if c i then -1 else 1

/-- **The minimal `2`-trade** with stem `S` on the three pairs `{p (i, false), p (i, true)}`: weight
`tradeSign c` on each face `tradeFace p S c`, and `0` on every other set. For `d = 2` and `S = ∅` it
is the alternating sum of the eight triangles that meet each of three disjoint pairs once. Every
pair of points has total weight `0` (`faceWeight_tradeWeight_pair`): this is the standard minimal
trade, a generator of the null `2`-designs (Graver–Jurkat 1973; Graham–Li–Li 1980). The definition
reads `p` and `S` without hypotheses; the facts below assume `p` injective and `S` disjoint from
its range. -/
noncomputable def tradeWeight (p : Fin 3 × Bool → ι) (S : Finset ι) (F : Finset ι) : ℝ :=
  ∑ c, if tradeFace p S c = F then tradeSign c else 0

variable {p : Fin 3 × Bool → ι} {S : Finset ι}

omit [Fintype ι] in
/-- Membership in a face of the trade. -/
theorem mem_tradeFace {c : Fin 3 → Bool} {x : ι} :
    x ∈ tradeFace p S c ↔ x ∈ S ∨ ∃ i, p (i, c i) = x := by
  simp [tradeFace]

omit [Fintype ι] in
/-- A face of the trade has `#S + 3` elements, when `p` is injective and its range misses `S`. -/
theorem card_tradeFace (hp : Function.Injective p) (hS : ∀ y, p y ∉ S) (c : Fin 3 → Bool) :
    #(tradeFace p S c) = #S + 3 := by
  unfold tradeFace
  rw [card_union_of_disjoint, card_image_of_injective _ fun i j h => congrArg Prod.fst (hp h),
    card_univ, Fintype.card_fin]
  rw [disjoint_left]
  intro x hxS hx
  obtain ⟨i, -, rfl⟩ := mem_image.mp hx
  exact hS _ hxS

omit [Fintype ι] in
/-- Different choices give different faces, when `p` is injective and its range misses `S`. -/
theorem tradeFace_injective (hp : Function.Injective p) (hS : ∀ y, p y ∉ S) :
    Function.Injective (tradeFace p S) := by
  intro c c' h
  funext i
  have hx : p (i, c i) ∈ tradeFace p S c' := h ▸ mem_tradeFace.mpr (Or.inr ⟨i, rfl⟩)
  rcases mem_tradeFace.mp hx with hx | ⟨j, hj⟩
  · exact absurd hx (hS _)
  · have := hp hj
    rw [Prod.mk.injEq] at this
    obtain ⟨rfl, h2⟩ := this
    exact h2.symm

/-- The trade needs `#S + 6` points: `N ≥ #S + 6`. With `#S + 3 = d + 1` this is `N ≥ d + 4`. -/
theorem card_add_six_le (hp : Function.Injective p) (hS : ∀ y, p y ∉ S) :
    #S + 6 ≤ Fintype.card ι := by
  have h : #(S ∪ univ.image p) = #S + 6 := by
    rw [card_union_of_disjoint, card_image_of_injective _ hp, card_univ]
    · simp
    · rw [disjoint_left]
      intro x hxS hx
      obtain ⟨y, -, rfl⟩ := mem_image.mp hx
      exact hS _ hxS
  rw [← h]
  exact card_le_univ _

/-- Summing against the trade is the signed sum over its eight faces. No hypothesis. -/
theorem sum_tradeWeight_mul (g : Finset ι → ℝ) :
    ∑ F, tradeWeight p S F * g F = ∑ c, tradeSign c * g (tradeFace p S c) := by
  unfold tradeWeight
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_ite_eq univ (tradeFace p S c), if_pos (mem_univ _)]

/-- Summing against the trade over the sets containing `s`. No hypothesis. -/
theorem sum_filter_tradeWeight_mul (s : Finset ι) (G : Finset ι → ℝ) :
    ∑ F with s ⊆ F, tradeWeight p S F * G F =
      ∑ c, if s ⊆ tradeFace p S c then tradeSign c * G (tradeFace p S c) else 0 := by
  rw [Finset.sum_filter]
  have := sum_tradeWeight_mul (p := p) (S := S) (fun F => if s ⊆ F then G F else 0)
  simp only [mul_ite, mul_zero] at this
  rw [this]

/-- The weight of `s` under the trade: the signed number of faces of the trade containing `s`. No
hypothesis. -/
theorem faceWeight_tradeWeight (s : Finset ι) :
    faceWeight (tradeWeight p S) s = ∑ c, if s ⊆ tradeFace p S c then tradeSign c else 0 := by
  have := sum_filter_tradeWeight_mul (p := p) (S := S) s fun _ => 1
  simp only [mul_one] at this
  rw [faceWeight, this]

omit [Fintype ι] in
/-- The trade vanishes off the sets with `#S + 3` elements. -/
theorem tradeWeight_eq_zero_of_card_ne (hp : Function.Injective p) (hS : ∀ y, p y ∉ S)
    {F : Finset ι} (hF : #F ≠ #S + 3) : tradeWeight p S F = 0 :=
  Finset.sum_eq_zero fun c _ => if_neg fun h => hF (by rw [← h]; exact card_tradeFace hp hS c)

omit [Fintype ι] in
/-- The value of the trade on its face `tradeFace p S c` is `tradeSign c`. -/
theorem tradeWeight_tradeFace (hp : Function.Injective p) (hS : ∀ y, p y ∉ S)
    (c : Fin 3 → Bool) : tradeWeight p S (tradeFace p S c) = tradeSign c := by
  unfold tradeWeight
  rw [Finset.sum_eq_single c (fun c' _ hc' => if_neg fun h => hc' (tradeFace_injective hp hS h))
    (by simp), if_pos rfl]

/-- A sign has absolute value `1`. -/
theorem abs_tradeSign (c : Fin 3 → Bool) : |tradeSign c| = 1 := by
  unfold tradeSign
  rw [Finset.abs_prod]
  exact Finset.prod_eq_one fun i _ => by split_ifs <;> simp

omit [Fintype ι] in
/-- The trade takes values in `[−1, 1]` (in fact in `{−1, 0, 1}`). -/
theorem abs_tradeWeight_le (hp : Function.Injective p) (hS : ∀ y, p y ∉ S) (F : Finset ι) :
    |tradeWeight p S F| ≤ 1 := by
  by_cases h : ∃ c, tradeFace p S c = F
  · obtain ⟨c, rfl⟩ := h
    rw [tradeWeight_tradeFace hp hS, abs_tradeSign]
  · push Not at h
    rw [show tradeWeight p S F = 0 from Finset.sum_eq_zero fun c _ => if_neg (h c)]
    simp

omit [Fintype ι] in
/-- **Two points miss one of three pairs.** If `p` is injective, then for any two points `u, v` one
of the three pairs `{p (i, false), p (i, true)}` contains neither. -/
theorem exists_free_class (hp : Function.Injective p) (u v : ι) :
    ∃ i, ∀ b, p (i, b) ≠ u ∧ p (i, b) ≠ v := by
  by_contra h
  have h' : ∀ i, ∃ b, p (i, b) = u ∨ p (i, b) = v := by
    intro i
    by_contra hi
    push Not at hi
    exact h ⟨i, hi⟩
  choose g hg using h'
  obtain ⟨i, j, hij, hf⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i => decide (p (i, g i) = u)) (by simp)
  have key : p (i, g i) = p (j, g j) := by
    by_cases hi : p (i, g i) = u
    · have hj : p (j, g j) = u := by simpa [hi] using hf.symm
      rw [hi, hj]
    · have hj : ¬ p (j, g j) = u := by simpa [hi] using hf.symm
      rw [(hg i).resolve_left hi, (hg j).resolve_left hj]
  exact hij (congrArg Prod.fst (hp key))

/-- Switching the choice in one pair changes the sign. -/
theorem tradeSign_update (c : Fin 3 → Bool) (i : Fin 3) :
    tradeSign (Function.update c i (!c i)) = -tradeSign c := by
  unfold tradeSign
  have e : ∀ c' : Fin 3 → Bool, (∏ j, if c' j then (-1 : ℝ) else 1) =
      (if c' i then -1 else 1) * ∏ j ∈ univ.erase i, if c' j then (-1 : ℝ) else 1 :=
    fun c' => (Finset.mul_prod_erase _ _ (mem_univ i)).symm
  rw [e, e c]
  have : ∏ j ∈ univ.erase i, (if Function.update c i (!c i) j then (-1 : ℝ) else 1) =
      ∏ j ∈ univ.erase i, if c j then (-1 : ℝ) else 1 :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (mem_erase.mp hj).1]
  rw [this, Function.update_self]
  cases c i <;> simp

omit [Fintype ι] in
/-- Switching the choice in pair `i` does not change membership of a point outside pair `i`. -/
theorem mem_tradeFace_update_iff {c : Fin 3 → Bool} {i : Fin 3} {b : Bool} {x : ι}
    (hx : ∀ b', p (i, b') ≠ x) :
    x ∈ tradeFace p S (Function.update c i b) ↔ x ∈ tradeFace p S c := by
  rw [mem_tradeFace, mem_tradeFace]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨j, hj⟩
    by_cases hji : j = i
    · subst hji
      exact absurd hj (hx _)
    · exact ⟨j, by rwa [Function.update_of_ne hji] at hj⟩
  · rintro ⟨j, hj⟩
    by_cases hji : j = i
    · subst hji
      exact absurd hj (hx _)
    · exact ⟨j, by rwa [Function.update_of_ne hji]⟩

/-- **Cancellation.** If some pair `i` is disjoint from `s`, the trade gives `s` total weight `0`:
switching the choice in pair `i` is a sign-reversing involution on the faces containing `s`. No
hypothesis on `p` or `S`. -/
theorem faceWeight_tradeWeight_eq_zero {s : Finset ι} {i : Fin 3} (hi : ∀ b, p (i, b) ∉ s) :
    faceWeight (tradeWeight p S) s = 0 := by
  rw [faceWeight_tradeWeight]
  let τ : (Fin 3 → Bool) → (Fin 3 → Bool) := fun c => Function.update c i (!c i)
  have hτ : Function.Involutive τ := fun c => by
    simp only [τ, Function.update_self, Bool.not_not, Function.update_idem, Function.update_eq_self]
  have hsub : ∀ c, s ⊆ tradeFace p S (τ c) ↔ s ⊆ tradeFace p S c := by
    intro c
    have hx : ∀ x ∈ s, ∀ b', p (i, b') ≠ x := fun x hx b' hb => hi b' (by rw [hb]; exact hx)
    constructor
    · intro h x hx'
      exact (mem_tradeFace_update_iff (hx x hx')).mp (h hx')
    · intro h x hx'
      exact (mem_tradeFace_update_iff (hx x hx')).mpr (h hx')
  obtain ⟨G, hG⟩ : ∃ G : (Fin 3 → Bool) → ℝ,
      G = fun c => if s ⊆ tradeFace p S c then tradeSign c else 0 := ⟨_, rfl⟩
  have hgoal : (∑ c, if s ⊆ tradeFace p S c then tradeSign c else 0) = ∑ c, G c := by rw [hG]
  rw [hgoal]
  have key : ∀ c, G (τ c) = -G c := by
    intro c
    rw [hG]
    dsimp only
    rw [if_congr (hsub c) rfl rfl]
    simp only [τ, tradeSign_update]
    split_ifs <;> simp
  have hsum : ∑ c, G (τ c) = ∑ c, G c := Equiv.sum_comp (hτ.toPerm τ) G
  rw [Finset.sum_congr rfl fun c _ => key c, Finset.sum_neg_distrib] at hsum
  linarith

/-- **The trade is pair-balanced with value `0`**: every pair of points lies in as many faces of
positive as of negative sign. Only injectivity of `p` is used (`exists_free_class`). The same holds
for `u = v`. -/
theorem faceWeight_tradeWeight_pair (hp : Function.Injective p) (u v : ι) :
    faceWeight (tradeWeight p S) {u, v} = 0 := by
  obtain ⟨i, hi⟩ := exists_free_class hp u v
  exact faceWeight_tradeWeight_eq_zero fun b hb => by
    rcases mem_insert.mp hb with h | h
    · exact (hi b).1 h
    · exact (hi b).2 (mem_singleton.mp h)

omit [Fintype ι] in
/-- Sums over a face of the trade, when `p` is injective and its range misses `S`. -/
theorem sum_tradeFace (hp : Function.Injective p) (hS : ∀ y, p y ∉ S) (c : Fin 3 → Bool)
    (g : ι → ℝ) : ∑ x ∈ tradeFace p S c, g x = ∑ x ∈ S, g x + ∑ i, g (p (i, c i)) := by
  unfold tradeFace
  rw [sum_union, sum_image fun i _ j _ h => congrArg Prod.fst (hp h)]
  rw [disjoint_left]
  intro x hxS hx
  obtain ⟨i, -, rfl⟩ := mem_image.mp hx
  exact hS _ hxS

omit [Fintype ι] in
/-- The faces of the trade containing `{a₁} ∪ S`, where `a₁ = p (0, false)`, are those with
`c 0 = false`. -/
theorem insert_subset_tradeFace_iff (hp : Function.Injective p) (hS : ∀ y, p y ∉ S)
    {c : Fin 3 → Bool} : insert (p (0, false)) S ⊆ tradeFace p S c ↔ c 0 = false := by
  constructor
  · intro h
    rcases mem_tradeFace.mp (h (mem_insert_self _ _)) with h1 | ⟨j, hj⟩
    · exact absurd h1 (hS _)
    · have := hp hj
      rw [Prod.mk.injEq] at this
      obtain ⟨rfl, h2⟩ := this
      exact h2
  · intro hc
    refine insert_subset (mem_tradeFace.mpr (Or.inr ⟨0, by rw [hc]⟩)) ?_
    intro x hx
    exact mem_tradeFace.mpr (Or.inl hx)

omit [Fintype ι] in
/-- For a face containing `{a₁} ∪ S`, a function vanishing on `{a₁} ∪ S` sums over the rest of the
face to its values at the two remaining points `p (1, c 1)` and `p (2, c 2)`. -/
theorem sum_sdiff_tradeFace (hp : Function.Injective p) (hS : ∀ y, p y ∉ S)
    {c : Fin 3 → Bool} (hc : c 0 = false) (g : ι → ℝ)
    (hg : ∀ x ∈ insert (p (0, false)) S, g x = 0) :
    ∑ x ∈ tradeFace p S c \ insert (p (0, false)) S, g x = g (p (1, c 1)) + g (p (2, c 2)) := by
  have hsub := (insert_subset_tradeFace_iff hp hS).mpr hc
  rw [Finset.sum_sdiff_eq_sub hsub, Finset.sum_eq_zero hg, sub_zero, sum_tradeFace hp hS,
    Fin.sum_univ_three, Finset.sum_eq_zero fun x hx => hg x (mem_insert_of_mem hx), hc,
    hg _ (mem_insert_self _ _)]
  ring

/-- A sum over `Fin 3 → Bool` as a triple sum over `Bool`. -/
theorem sum_fin_three_bool (G : (Fin 3 → Bool) → ℝ) :
    ∑ c, G c = ∑ a : Bool, ∑ b : Bool, ∑ e : Bool, G ![a, b, e] := by
  let eqv : Bool × Bool × Bool ≃ (Fin 3 → Bool) :=
    { toFun := fun x => ![x.1, x.2.1, x.2.2]
      invFun := fun c => (c 0, c 1, c 2)
      left_inv := fun x => by simp
      right_inv := fun c => by
        funext i
        fin_cases i <;> rfl }
  rw [← eqv.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

/-! ### The uniform weight plus a multiple of the trade -/

variable {d : ℕ}

/-- **The perturbed weight `1 + δ z`**: the uniform weight of the complete `d`-dimensional complex
plus `δ` times the minimal trade `z = tradeWeight p S`. It is a top weight for `|δ| < 1`
(`isTopWeight_uniformAddTrade`), and all its pairs have the same weight for every `δ`
(`faceWeight_uniformAddTrade_pair`). The definition has no hypotheses. -/
noncomputable def uniformAddTrade (d : ℕ) (p : Fin 3 × Bool → ι) (S : Finset ι) (δ : ℝ)
    (F : Finset ι) : ℝ :=
  (complete ι d).uniformWeight d F + δ * tradeWeight p S F

omit [Fintype ι] in
/-- Unfolding `uniformAddTrade` as a function. -/
theorem uniformAddTrade_eq (d : ℕ) (p : Fin 3 × Bool → ι) (S : Finset ι) (δ : ℝ) :
    uniformAddTrade d p S δ =
      fun F => (complete ι d).uniformWeight d F + δ * tradeWeight p S F := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- In the complete complex every set with `d + 1` elements is a top face, of uniform weight `1`. -/
theorem uniformWeight_complete_of_card_eq {F : Finset ι} (hF : #F = d + 1) :
    (complete ι d).uniformWeight d F = 1 := by
  unfold uniformWeight
  rw [if_pos ⟨mem_complete.mpr ⟨card_pos.mp (by omega), by omega⟩, hF⟩]

omit [Fintype ι] [DecidableEq ι] in
/-- A set with a number of elements other than `d + 1` has uniform weight `0`. -/
theorem uniformWeight_complete_of_card_ne {F : Finset ι} (hF : #F ≠ d + 1) :
    (complete ι d).uniformWeight d F = 0 := by
  unfold uniformWeight
  rw [if_neg fun h => hF h.2]

omit [Fintype ι] in
/-- On a set with `d + 1` elements, `1 + δ z` differs from `1` by at most `|δ|`. -/
theorem abs_uniformAddTrade_sub_one_le (hp : Function.Injective p) (hS : ∀ y, p y ∉ S) (δ : ℝ)
    {F : Finset ι} (hF : #F = d + 1) : |uniformAddTrade d p S δ F - 1| ≤ |δ| := by
  rw [uniformAddTrade, uniformWeight_complete_of_card_eq hF, add_sub_cancel_left, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_tradeWeight_le hp hS F)

/-- `1 + δ z` is a top weight of the complete complex when `|δ| < 1`, `p` is injective, its range
misses `S`, and `#S + 3 = d + 1` (so `d ≥ 2` and `N ≥ d + 4`). For `|δ| ≥ 1` it has a top face of
weight `≤ 0`. -/
theorem isTopWeight_uniformAddTrade (hp : Function.Injective p) (hS : ∀ y, p y ∉ S)
    (hSd : #S + 3 = d + 1) {δ : ℝ} (hδ : |δ| < 1) :
    (complete ι d).IsTopWeight d (uniformAddTrade d p S δ) := by
  have hN : d + 1 ≤ Fintype.card ι := by have := card_add_six_le hp hS; omega
  refine ⟨isPure_complete hN, ⟨{p (0, false)}, mem_complete.mpr ⟨singleton_nonempty _, by
    rw [card_singleton]; omega⟩⟩, fun F _ hc => ?_, fun F hF => ?_⟩
  · have h1 := abs_le.mp (abs_uniformAddTrade_sub_one_le hp hS δ hc)
    linarith [h1.1]
  · have hc : #F ≠ d + 1 := fun h => hF ⟨mem_complete.mpr ⟨card_pos.mp (by omega), by omega⟩, h⟩
    rw [uniformAddTrade, uniformWeight_complete_of_card_ne hc,
      tradeWeight_eq_zero_of_card_ne hp hS (by omega), mul_zero, add_zero]

/-- **`1 + δ z` is pair-balanced** for every `δ`: each pair has the weight `C(N − 2, d − 1)` that it
has under the uniform weight. Needs `1 ≤ d` (for `d = 0` the uniform weight gives pairs weight
`0`, not `C(N − 2, d − 1) = 1`) and `p` injective. -/
theorem faceWeight_uniformAddTrade_pair (hp : Function.Injective p) (hd : 1 ≤ d) {u v : ι}
    (huv : u ≠ v) (δ : ℝ) :
    faceWeight (uniformAddTrade d p S δ) {u, v} = ((Fintype.card ι - 2).choose (d - 1) : ℝ) := by
  rw [uniformAddTrade_eq, faceWeight_add, faceWeight_const_mul, faceWeight_tradeWeight_pair hp,
    mul_zero, add_zero, ← topDegree_eq_faceWeight,
    topDegree_complete_eq_choose (by rw [card_pair huv]; omega), card_pair huv,
    show d + 1 - 2 = d - 1 by omega]

omit [Fintype ι] in
/-- **`1 + δ z` is not a multiple of the uniform weight** when `δ ≠ 0`: it is `1 + δ` on the face
with `c ≡ false` and `1 − δ` on the face that differs in the first pair. -/
theorem uniformAddTrade_ne_mul_uniformWeight (hp : Function.Injective p) (hS : ∀ y, p y ∉ S)
    (hSd : #S + 3 = d + 1) {δ : ℝ} (hδ : δ ≠ 0) (κ : ℝ) :
    uniformAddTrade d p S δ ≠ fun F => κ * (complete ι d).uniformWeight d F := by
  intro h
  have h0 := congrFun h (tradeFace p S fun _ => false)
  have h1 := congrFun h (tradeFace p S (Function.update (fun _ => false) 0 true))
  have hc0 : #(tradeFace p S fun _ => false) = d + 1 := by rw [card_tradeFace hp hS]; omega
  have hc1 : #(tradeFace p S (Function.update (fun _ => false) 0 true)) = d + 1 := by
    rw [card_tradeFace hp hS]; omega
  simp only [uniformAddTrade, tradeWeight_tradeFace hp hS, uniformWeight_complete_of_card_eq hc0,
    uniformWeight_complete_of_card_eq hc1] at h0 h1
  have hs0 : tradeSign (fun _ : Fin 3 => false) = 1 := by simp [tradeSign]
  have hs1 : tradeSign (Function.update (fun _ : Fin 3 => false) 0 true) = -1 := by
    have := tradeSign_update (fun _ : Fin 3 => false) 0
    simp only [Bool.not_false] at this
    rw [this, hs0]
  rw [hs0] at h0
  rw [hs1] at h1
  exact hδ (by linarith)

/-- **Sufficiency in the comparison range.** If `(2(N − 1)² − 1) |δ| ≤ 1`, the weight `1 + δ z` is
optimal: the complete complex with this weight is a `(−1/(N − 1))`-local spectral expander. On top
faces `1 − |δ| ≤ 1 + δ z ≤ 1 + |δ|`, and `(1 − |δ|)/(1 + |δ|) ≥ 1 − 1/(N − 1)²`, so this is
`isLocalSpectralExpanderOf_complete_of_ratio`. The hypotheses force `d ≥ 2`, `N ≥ d + 4` and
`|δ| ≤ 1/49`.

By computation the exact threshold is `|δ| ≤ (d − 1)/(2(N − 1))`, much larger. Its necessity is
`two_mul_abs_le_of_isLocalSpectralExpanderOf_uniformAddTrade`; its sufficiency beyond the range
proved here is only verified numerically (exactly for `N ≤ 14`) and is not formalized. -/
theorem isLocalSpectralExpanderOf_uniformAddTrade (hp : Function.Injective p)
    (hS : ∀ y, p y ∉ S) (hSd : #S + 3 = d + 1) {δ : ℝ}
    (hδ : (2 * ((Fintype.card ι : ℝ) - 1) ^ 2 - 1) * |δ| ≤ 1) :
    (complete ι d).IsLocalSpectralExpanderOf d (uniformAddTrade d p S δ)
      (-(1 / ((Fintype.card ι : ℝ) - 1))) := by
  have hd : 1 ≤ d := by omega
  have h6 := card_add_six_le hp hS
  have hN6 : (6 : ℝ) ≤ Fintype.card ι := by exact_mod_cast (by omega : 6 ≤ Fintype.card ι)
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (Fintype.card ι : ℝ) - 1 := ⟨_, rfl⟩
  rw [← hy] at hδ
  have hy5 : 5 ≤ y := by linarith
  have hδ0 := abs_nonneg δ
  have h49 : 49 ≤ 2 * y ^ 2 - 1 := by nlinarith
  have hδ1 : |δ| < 1 := by nlinarith [mul_le_mul_of_nonneg_right h49 hδ0]
  have hm := isTopWeight_uniformAddTrade hp hS hSd hδ1
  refine isLocalSpectralExpanderOf_complete_of_ratio hd hm
    ⟨_, fun u v huv => faceWeight_uniformAddTrade_pair hp hd huv δ⟩ fun F G hF hG => ?_
  rw [← hy]
  have hbF := (abs_le.mp (abs_uniformAddTrade_sub_one_le hp hS δ hF)).1
  have hbG := (abs_le.mp (abs_uniformAddTrade_sub_one_le hp hS δ hG)).2
  have hy2 : 0 < y ^ 2 := by positivity
  have hq : 2 * |δ| ≤ (1 + |δ|) / y ^ 2 := by
    rw [le_div_iff₀ hy2]
    nlinarith
  have hη : 1 / y ^ 2 ≤ 1 := by rw [div_le_one hy2]; nlinarith
  have h1 : (1 - 1 / y ^ 2) * uniformAddTrade d p S δ G ≤ (1 - 1 / y ^ 2) * (1 + |δ|) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (1 - 1 / y ^ 2) * (1 + |δ|) = (1 + |δ|) - (1 + |δ|) / y ^ 2 := by ring
  linarith

/-! ### The test function at the regular link -/

/-- The values of the test function on the six points of the trade: `0` on the first pair, `±1` on
the second, `±s` on the third (`+` at `p (i, false)`). -/
noncomputable def tradeTestValue (s : ℝ) (y : Fin 3 × Bool) : ℝ :=
  ![0, 1, s] y.1 * (if y.2 then -1 else 1)

/-- The test function: `tradeTestValue s y` at `p y`, and `0` off the range of `p`. -/
noncomputable def tradeTest (p : Fin 3 × Bool → ι) (s : ℝ) (x : ι) : ℝ :=
  ∑ y, if p y = x then tradeTestValue s y else 0

omit [Fintype ι] in
/-- The test function at a point of the trade, when `p` is injective. -/
theorem tradeTest_apply (hp : Function.Injective p) (s : ℝ) (y : Fin 3 × Bool) :
    tradeTest p s (p y) = tradeTestValue s y := by
  unfold tradeTest
  rw [Finset.sum_eq_single y (fun y' _ hy' => if_neg fun h => hy' (hp h)) (by simp), if_pos rfl]

omit [Fintype ι] in
/-- The test function vanishes off the range of `p`. -/
theorem tradeTest_eq_zero (s : ℝ) {x : ι} (hx : ∀ y, p y ≠ x) : tradeTest p s x = 0 :=
  Finset.sum_eq_zero fun y _ => if_neg (hx y)

/-- Weighted sums of a function `φ` of the test function, with `φ 0 = 0`, reduce to the six
points. -/
theorem sum_mul_tradeTest (hp : Function.Injective p) (s : ℝ) (g : ι → ℝ) (φ : ℝ → ℝ)
    (hφ : φ 0 = 0) :
    ∑ x, g x * φ (tradeTest p s x) = ∑ y, g (p y) * φ (tradeTestValue s y) := by
  have h : ∀ x, g x * φ (tradeTest p s x) =
      ∑ y, if p y = x then g (p y) * φ (tradeTestValue s y) else 0 := by
    intro x
    by_cases hx : ∃ y, p y = x
    · obtain ⟨y0, rfl⟩ := hx
      rw [tradeTest_apply hp, Finset.sum_eq_single y0
        (fun y _ hy => if_neg fun h => hy (hp h)) (by simp), if_pos rfl]
    · push Not at hx
      rw [tradeTest_eq_zero s hx, hφ, mul_zero]
      exact (Finset.sum_eq_zero fun y _ => if_neg (hx y)).symm
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_ite_eq univ (p y), if_pos (mem_univ _)]

/-- The test function has sum `0`. -/
theorem sum_tradeTestValue (s : ℝ) : ∑ y, tradeTestValue s y = 0 := by
  simp [tradeTestValue, Fintype.sum_prod_type]

/-- For `s = ±1` the test function has squared norm `4`. -/
theorem sum_tradeTestValue_sq {s : ℝ} (hs : s ^ 2 = 1) : ∑ y, tradeTestValue s y ^ 2 = 4 := by
  simp [tradeTestValue, Fintype.sum_prod_type, Fin.sum_univ_three, hs]
  norm_num

end

section

variable [DecidableEq ι] {d : ℕ} {p : Fin 3 × Bool → ι} {S : Finset ι}

/-! ### Necessity: the trade threshold at the link of `{a₁} ∪ S` -/

omit [DecidableEq ι] in
/-- Degree-weighted sums are linear in the weighted graph. No hypothesis. -/
theorem sum_deg_add_mul (A B : ι → ι → ℝ) (δ : ℝ) (g : ι → ℝ) :
    ∑ u, (∑ v, (A u v + δ * B u v)) * g u =
      ∑ u, (∑ v, A u v) * g u + δ * ∑ u, (∑ v, B u v) * g u := by
  have e : ∀ u, (∑ v, (A u v + δ * B u v)) * g u =
      (∑ v, A u v) * g u + δ * ((∑ v, B u v) * g u) := fun u => by
    rw [sum_add_distrib, ← mul_sum]; ring
  rw [sum_congr rfl fun u _ => e u, sum_add_distrib, ← mul_sum]

omit [DecidableEq ι] in
/-- Quadratic forms are linear in the weighted graph. No hypothesis. -/
theorem sum_quad_add_mul (A B : ι → ι → ℝ) (δ : ℝ) (f : ι → ℝ) :
    ∑ u, ∑ v, (A u v + δ * B u v) * f u * f v =
      ∑ u, ∑ v, A u v * f u * f v + δ * ∑ u, ∑ v, B u v * f u * f v := by
  have e : ∀ u, ∑ v, (A u v + δ * B u v) * f u * f v =
      ∑ v, A u v * f u * f v + δ * ∑ v, B u v * f u * f v := fun u => by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun v _ => by ring
  rw [sum_congr rfl fun u _ => e u, sum_add_distrib, ← mul_sum]

/-- **Necessity in the trade threshold, at one link.** Let `p` be injective, its range miss `S`, and
`#S + 3 = d + 1`, and let `σ = {a₁} ∪ S` with `a₁ = p (0, false)`, a set with `d − 1` elements. If
the link of `σ` for the weight `1 + δ z` has walk second eigenvalue at most `−1/(N − 1)`, then
`2 (N − 1) |δ| ≤ d − 1`.

The link is the complete graph on the `N − d + 1` points outside `σ`, plus `δ` times a signed
`K_{2,2}` between the second and third pairs; it is regular of degree `N − d`. The test function
`(1, −1, s, −s)` on those four points, with `s` the sign of `δ` (`tradeTest`), has Rayleigh quotient
`(−4 + 8|δ|) / (4 (N − d))`. By computation this quotient is the second eigenvalue of the link, so
the bound is attained there. No hypothesis on `δ`: the statement does not need `1 + δ z` to be a
top weight. -/
theorem abs_le_of_walkSecondEigenvalueLE_uniformAddTrade (hp : Function.Injective p)
    (hS : ∀ y, p y ∉ S) (hSd : #S + 3 = d + 1) {δ : ℝ}
    (h : WalkSecondEigenvalueLE (linkWeightOf (uniformAddTrade d p S δ) (insert (p (0, false)) S))
      (-(1 / ((Fintype.card ι : ℝ) - 1)))) :
    2 * ((Fintype.card ι : ℝ) - 1) * |δ| ≤ d - 1 := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Finset ι, σ = insert (p (0, false)) S := ⟨_, rfl⟩
  rw [← hσ] at h
  have h0S : p (0, false) ∉ S := hS _
  have hσc : #σ = #S + 1 := by rw [hσ, card_insert_of_notMem h0S]
  have hσd : #σ + 1 = d := by omega
  have h6 := card_add_six_le hp hS
  -- the sign of `δ`
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = if 0 ≤ δ then 1 else -1 := ⟨_, rfl⟩
  have hs2 : s ^ 2 = 1 := by rw [hs]; split_ifs <;> norm_num
  have hsδ : s * δ = |δ| := by
    rw [hs]
    split_ifs with hδ
    · rw [one_mul, abs_of_nonneg hδ]
    · rw [abs_of_neg (not_le.mp hδ)]; ring
  -- the test function vanishes on `σ`
  have hpσ : ∀ y, p y ∈ σ → y = (0, false) := by
    intro y hy
    rw [hσ, mem_insert] at hy
    rcases hy with hy | hy
    · exact hp hy
    · exact absurd hy (hS y)
  have hv0 : tradeTestValue s (0, false) = 0 := by simp [tradeTestValue]
  have hfσ : ∀ x ∈ σ, tradeTest p s x = 0 := by
    intro x hx
    by_cases hxp : ∃ y, p y = x
    · obtain ⟨y, rfl⟩ := hxp
      rw [tradeTest_apply hp, hpσ y hx, hv0]
    · push Not at hxp
      exact tradeTest_eq_zero s hxp
  -- the uniform part is a clique
  have hU : linkWeightOf ((complete ι d).uniformWeight d) σ = cliqueWeight σᶜ 1 := by
    rw [← linkWeight_eq_linkWeightOf, linkWeight_complete_eq_cliqueWeight (by omega),
      show d - 1 - #σ = 0 by omega, Nat.choose_zero_right, Nat.cast_one]
  have hσle : #σ ≤ Fintype.card ι := card_le_univ σ
  obtain ⟨n1, hn1⟩ : ∃ n1 : ℝ, n1 = (#σᶜ : ℝ) - 1 := ⟨_, rfl⟩
  have hσd' : (#σ : ℝ) + 1 = d := by exact_mod_cast hσd
  have hn1' : n1 = (Fintype.card ι : ℝ) - d := by
    rw [hn1, card_compl, Nat.cast_sub hσle]
    linarith
  have hdegU : ∀ φ : ℝ → ℝ, φ 0 = 0 → ∀ y,
      (∑ v, cliqueWeight σᶜ 1 (p y) v) * φ (tradeTestValue s y) =
        n1 * φ (tradeTestValue s y) := by
    intro φ hφ y
    rw [sum_cliqueWeight]
    by_cases hy : p y ∈ σ
    · rw [hpσ y hy, hv0, hφ, mul_zero, mul_zero]
    · rw [if_pos (mem_compl.mpr hy), one_mul, hn1]
  have hdegU1 : ∀ y, (∑ v, cliqueWeight σᶜ 1 (p y) v) * tradeTestValue s y =
      n1 * tradeTestValue s y := fun y => hdegU id rfl y
  have hmeanU : ∑ u, (∑ v, cliqueWeight σᶜ 1 u v) * tradeTest p s u = 0 := by
    have : ∑ u, (∑ v, cliqueWeight σᶜ 1 u v) * tradeTest p s u =
        ∑ y, (∑ v, cliqueWeight σᶜ 1 (p y) v) * tradeTestValue s y :=
      sum_mul_tradeTest hp s (fun u => ∑ v, cliqueWeight σᶜ 1 u v) id rfl
    rw [this, sum_congr rfl fun y _ => hdegU1 y, ← mul_sum, sum_tradeTestValue, mul_zero]
  have hnormU : ∑ u, (∑ v, cliqueWeight σᶜ 1 u v) * tradeTest p s u ^ 2 = 4 * n1 := by
    have := sum_mul_tradeTest hp s (fun u => ∑ v, cliqueWeight σᶜ 1 u v) (fun x => x ^ 2)
      (by norm_num)
    rw [this, sum_congr rfl fun y _ => hdegU (fun x => x ^ 2) (by norm_num) y, ← mul_sum,
      sum_tradeTestValue_sq hs2]
    ring
  have hN1 : ((d + 1 : ℕ) : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast (by omega : d + 1 ≤ Fintype.card ι)
  push_cast at hN1
  have hn1pos : 0 < n1 := by rw [hn1']; linarith
  have hquadU : ∑ u, ∑ v, cliqueWeight σᶜ 1 u v * tradeTest p s u * tradeTest p s v = -4 := by
    rw [sum_cliqueWeight_mul_mul_eq σᶜ 1 _ hmeanU, hnormU, ← hn1]
    field_simp
  -- the trade part
  have hcardt : ∀ F, tradeWeight p S F ≠ 0 → #F = d + 1 := fun F hF => by
    by_contra h'
    exact hF (tradeWeight_eq_zero_of_card_ne hp hS (by omega))
  have hdσ : (d : ℝ) - #σ = 1 := by linarith
  have hdegT : ∀ g : ι → ℝ, ∑ u, (∑ v, linkWeightOf (tradeWeight p S) σ u v) * g u =
      ∑ c, if c 0 = false then tradeSign c * ∑ x ∈ tradeFace p S c \ σ, g x else 0 := by
    intro g
    have e1 : ∀ u, (∑ v, linkWeightOf (tradeWeight p S) σ u v) * g u =
        (if u ∈ σ then 0 else faceWeight (tradeWeight p S) (insert u σ)) * g u := by
      intro u
      rw [sum_linkWeightOf hcardt σ u, hdσ]
      split_ifs <;> ring
    rw [sum_congr rfl fun u _ => e1 u, sum_faceWeight_insert_mul, sum_filter_tradeWeight_mul]
    refine sum_congr rfl fun c _ => ?_
    rw [hσ]
    exact if_congr (insert_subset_tradeFace_iff hp hS) rfl rfl
  have hquadT : ∑ u, ∑ v, linkWeightOf (tradeWeight p S) σ u v * tradeTest p s u *
      tradeTest p s v = ∑ c, if c 0 = false then tradeSign c *
        ((∑ x ∈ tradeFace p S c \ σ, tradeTest p s x) ^ 2 -
          ∑ x ∈ tradeFace p S c \ σ, tradeTest p s x ^ 2) else 0 := by
    rw [sum_linkWeightOf_mul_mul, sum_filter_tradeWeight_mul]
    refine sum_congr rfl fun c _ => ?_
    rw [hσ]
    exact if_congr (insert_subset_tradeFace_iff hp hS) rfl rfl
  have hsd : ∀ c : Fin 3 → Bool, c 0 = false → ∀ φ : ℝ → ℝ, φ 0 = 0 →
      ∑ x ∈ tradeFace p S c \ σ, φ (tradeTest p s x) =
        φ (tradeTestValue s (1, c 1)) + φ (tradeTestValue s (2, c 2)) := by
    intro c hc φ hφ
    rw [hσ, sum_sdiff_tradeFace hp hS hc (fun x => φ (tradeTest p s x)) fun x hx => by
      rw [← hσ] at hx
      show φ (tradeTest p s x) = 0
      rw [hfσ x hx, hφ], tradeTest_apply hp, tradeTest_apply hp]
  have hsd1 : ∀ c : Fin 3 → Bool, c 0 = false →
      ∑ x ∈ tradeFace p S c \ σ, tradeTest p s x =
        tradeTestValue s (1, c 1) + tradeTestValue s (2, c 2) := fun c hc => hsd c hc id rfl
  have hmeanT : ∑ u, (∑ v, linkWeightOf (tradeWeight p S) σ u v) * tradeTest p s u = 0 := by
    rw [hdegT]
    have e : ∀ c : Fin 3 → Bool,
        (if c 0 = false then tradeSign c * ∑ x ∈ tradeFace p S c \ σ, tradeTest p s x else 0) =
          if c 0 = false then
            tradeSign c * (tradeTestValue s (1, c 1) + tradeTestValue s (2, c 2)) else 0 := by
      intro c
      split_ifs with hc
      · rw [hsd1 c hc]
      · rfl
    rw [sum_congr rfl fun c _ => e c, sum_fin_three_bool]
    simp [tradeSign, tradeTestValue, Fin.prod_univ_three]
    ring
  have hnormT : ∑ u, (∑ v, linkWeightOf (tradeWeight p S) σ u v) * tradeTest p s u ^ 2 = 0 := by
    rw [hdegT]
    have e : ∀ c : Fin 3 → Bool,
        (if c 0 = false then tradeSign c * ∑ x ∈ tradeFace p S c \ σ, tradeTest p s x ^ 2
          else 0) = if c 0 = false then
            tradeSign c * (tradeTestValue s (1, c 1) ^ 2 + tradeTestValue s (2, c 2) ^ 2)
          else 0 := by
      intro c
      split_ifs with hc
      · rw [hsd c hc (fun x => x ^ 2) (by norm_num)]
      · rfl
    rw [sum_congr rfl fun c _ => e c, sum_fin_three_bool]
    simp [tradeSign, tradeTestValue, Fin.prod_univ_three]
  have hquadT' : ∑ u, ∑ v, linkWeightOf (tradeWeight p S) σ u v * tradeTest p s u *
      tradeTest p s v = 8 * s := by
    rw [hquadT]
    have e : ∀ c : Fin 3 → Bool,
        (if c 0 = false then tradeSign c * ((∑ x ∈ tradeFace p S c \ σ, tradeTest p s x) ^ 2 -
          ∑ x ∈ tradeFace p S c \ σ, tradeTest p s x ^ 2) else 0) = if c 0 = false then
            tradeSign c * ((tradeTestValue s (1, c 1) + tradeTestValue s (2, c 2)) ^ 2 -
              (tradeTestValue s (1, c 1) ^ 2 + tradeTestValue s (2, c 2) ^ 2)) else 0 := by
      intro c
      split_ifs with hc
      · rw [hsd1 c hc, hsd c hc (fun x => x ^ 2) (by norm_num)]
      · rfl
    rw [sum_congr rfl fun c _ => e c, sum_fin_three_bool]
    simp [tradeSign, tradeTestValue, Fin.prod_univ_three]
    ring
  -- the perturbed link
  have hsplit : linkWeightOf (uniformAddTrade d p S δ) σ =
      fun u v => cliqueWeight σᶜ 1 u v + δ * linkWeightOf (tradeWeight p S) σ u v := by
    funext u v
    rw [uniformAddTrade_eq, linkWeightOf_add, linkWeightOf_const_mul, hU]
  rw [hsplit] at h
  have hmean : ∑ u, (∑ v, (cliqueWeight σᶜ 1 u v + δ * linkWeightOf (tradeWeight p S) σ u v)) *
      tradeTest p s u = 0 := by
    rw [sum_deg_add_mul, hmeanU, hmeanT, mul_zero, add_zero]
  have h1 := h (tradeTest p s) hmean
  rw [sum_quad_add_mul, sum_deg_add_mul, hquadU, hquadT', hnormU, hnormT, hn1'] at h1
  have hy : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by linarith
  rw [mul_zero, add_zero, show -(1 / ((Fintype.card ι : ℝ) - 1)) * (4 * ((Fintype.card ι : ℝ) - d))
    = -(4 * ((Fintype.card ι : ℝ) - d)) / ((Fintype.card ι : ℝ) - 1) by ring,
    le_div_iff₀ hy] at h1
  have : δ * (8 * s) = 8 * |δ| := by rw [← hsδ]; ring
  rw [this] at h1
  nlinarith

end

section

variable [DecidableEq ι] {d : ℕ} {p : Fin 3 × Bool → ι} {S : Finset ι}

/-- **An optimal trade perturbation has `|δ| ≤ (d − 1)/(2(N − 1))`.** If `1 + δ z` is optimal, then
`2 (N − 1) |δ| ≤ d − 1`, by `abs_le_of_walkSecondEigenvalueLE_uniformAddTrade` at the face
`{a₁} ∪ S`. -/
theorem two_mul_abs_le_of_isLocalSpectralExpanderOf_uniformAddTrade (hp : Function.Injective p)
    (hS : ∀ y, p y ∉ S) (hSd : #S + 3 = d + 1) {δ : ℝ}
    (h : (complete ι d).IsLocalSpectralExpanderOf d (uniformAddTrade d p S δ)
      (-(1 / ((Fintype.card ι : ℝ) - 1)))) :
    2 * ((Fintype.card ι : ℝ) - 1) * |δ| ≤ d - 1 := by
  have h0S : p (0, false) ∉ S := hS _
  have hc : #(insert (p (0, false)) S) = #S + 1 := card_insert_of_notMem h0S
  refine abs_le_of_walkSecondEigenvalueLE_uniformAddTrade hp hS hSd
    (h.walkSecondEigenvalueLE (Or.inr (mem_complete.mpr ⟨insert_nonempty _ _, by omega⟩))
      (by omega))

/-- **The range `|δ| ≤ 1/(2N²)`.** In particular `1 + δ z` is optimal whenever
`|δ| ≤ 1/(2N²)`, since then `(2(N − 1)² − 1)|δ| ≤ 1`. -/
theorem isLocalSpectralExpanderOf_uniformAddTrade_of_abs_le (hp : Function.Injective p)
    (hS : ∀ y, p y ∉ S) (hSd : #S + 3 = d + 1) {δ : ℝ}
    (hδ : |δ| ≤ 1 / (2 * (Fintype.card ι : ℝ) ^ 2)) :
    (complete ι d).IsLocalSpectralExpanderOf d (uniformAddTrade d p S δ)
      (-(1 / ((Fintype.card ι : ℝ) - 1))) := by
  refine isLocalSpectralExpanderOf_uniformAddTrade hp hS hSd ?_
  have h6 := card_add_six_le hp hS
  have hN : (6 : ℝ) ≤ Fintype.card ι := by exact_mod_cast (by omega : 6 ≤ Fintype.card ι)
  have hpos : 0 < 2 * (Fintype.card ι : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hpos] at hδ
  have h1 : 2 * ((Fintype.card ι : ℝ) - 1) ^ 2 - 1 ≤ 2 * (Fintype.card ι : ℝ) ^ 2 := by nlinarith
  have h0 := abs_nonneg δ
  nlinarith

/-- For `d ≥ 2` and `N ≥ d + 4` the trade exists: six distinct points `p` and a set `S` of `d − 2`
further points. -/
theorem exists_trade_data (hd : 2 ≤ d) (hN : d + 4 ≤ Fintype.card ι) :
    ∃ (p : Fin 3 × Bool → ι) (S : Finset ι),
      Function.Injective p ∧ (∀ y, p y ∉ S) ∧ #S + 3 = d + 1 := by
  obtain ⟨e⟩ : Nonempty (Fin 3 × Bool ↪ ι) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  have hc : d - 2 ≤ #(univ \ univ.map e) := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_map, card_univ]
    simp
    omega
  obtain ⟨S, hS, hSc⟩ := exists_subset_card_eq hc
  refine ⟨e, S, e.injective, fun y hy => ?_, by omega⟩
  have := hS hy
  simp at this

/-- **Part (ii), rigidity.** If `d = 1` or `N ≤ d + 3`, every optimal weight of the complete
`d`-dimensional complex on `N = Fintype.card ι` points is a positive multiple of the uniform
weight. Optimal weights are pair-balanced (part (i)), and pair balance forces a constant weight
(`eq_of_pairBalanced_of_le`). Degenerate cases: `d = 0` is excluded by the definition of an
expander; for `N < d + 1` there is no top weight. -/
theorem exists_eq_mul_uniformWeight_of_isLocalSpectralExpanderOf_complete
    (hsmall : d = 1 ∨ Fintype.card ι ≤ d + 3) {m : Finset ι → ℝ}
    (h : (complete ι d).IsLocalSpectralExpanderOf d m (-(1 / ((Fintype.card ι : ℝ) - 1)))) :
    ∃ κ > 0, m = fun F => κ * (complete ι d).uniformWeight d F := by
  have hbal := ((isLocalSpectralExpanderOf_complete_neg_one_div_iff h.one_le h.isTopWeight).mp h).1
  exact exists_eq_mul_uniformWeight_of_isTopWeight h.isTopWeight fun F G _ _ hF hG =>
    eq_of_pairBalanced_of_le h.one_le hsmall h.isTopWeight.card_eq_of_ne_zero hbal hF hG

/-- **Part (ii), flexibility.** If `d ≥ 2` and `N ≥ d + 4`, the complete `d`-dimensional complex has
an optimal weight that is not a multiple of the uniform weight: `1 + z/(2N²)` for the minimal
trade `z`. -/
theorem exists_isLocalSpectralExpanderOf_complete_ne_mul_uniformWeight (hd : 2 ≤ d)
    (hN : d + 4 ≤ Fintype.card ι) :
    ∃ m : Finset ι → ℝ,
      (complete ι d).IsLocalSpectralExpanderOf d m (-(1 / ((Fintype.card ι : ℝ) - 1))) ∧
        ∀ κ : ℝ, m ≠ fun F => κ * (complete ι d).uniformWeight d F := by
  obtain ⟨p, S, hp, hS, hSd⟩ := exists_trade_data (ι := ι) hd hN
  have hN0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (by omega : 0 < Fintype.card ι)
  have hδ : (1 / (2 * (Fintype.card ι : ℝ) ^ 2)) ≠ 0 := by positivity
  exact ⟨_, isLocalSpectralExpanderOf_uniformAddTrade_of_abs_le hp hS hSd
    (le_of_eq (abs_of_pos (by positivity))), uniformAddTrade_ne_mul_uniformWeight hp hS hSd hδ⟩

/-- **Optimal weights on the complete complex, part (ii).** Let `1 ≤ d` and `N = Fintype.card ι`.
Every top weight `m` that makes the complete `d`-dimensional complex a `(−1/(N − 1))`-local spectral
expander is a positive multiple of the uniform weight exactly when `d = 1` or `N ≤ d + 3`.

In design-theoretic terms: by part (i) the optimal weights are pair-balanced, and nonzero null
`2`-designs on `(d + 1)`-sets exist exactly when `d ≥ 2` and `N ≥ d + 4`. The rigid half is
`exists_eq_mul_uniformWeight_of_isLocalSpectralExpanderOf_complete`, the flexible half is
`exists_isLocalSpectralExpanderOf_complete_ne_mul_uniformWeight`.

Degenerate cases: `d + 1 ≤ N` is not assumed; for `N < d + 1` there are no top weights, the left
side holds vacuously, and so does `N ≤ d + 3`. The hypothesis `1 ≤ d` is needed: for `d = 0` the
left side holds vacuously (there are no `0`-dimensional expanders), but the right side fails once
`N ≥ 4`. -/
theorem forall_isLocalSpectralExpanderOf_complete_eq_mul_uniformWeight_iff (hd : 1 ≤ d) :
    (∀ m : Finset ι → ℝ, (complete ι d).IsLocalSpectralExpanderOf d m
        (-(1 / ((Fintype.card ι : ℝ) - 1))) →
      ∃ κ > 0, m = fun F => κ * (complete ι d).uniformWeight d F) ↔
      (d = 1 ∨ Fintype.card ι ≤ d + 3) := by
  refine ⟨fun h => ?_, fun hsmall m hm =>
    exists_eq_mul_uniformWeight_of_isLocalSpectralExpanderOf_complete hsmall hm⟩
  by_contra hc
  push Not at hc
  obtain ⟨m, hm, hne⟩ :=
    exists_isLocalSpectralExpanderOf_complete_ne_mul_uniformWeight (ι := ι) (d := d)
      (by omega) (by omega)
  obtain ⟨κ, -, heq⟩ := h m hm
  exact hne κ heq

/-! ### The example on six points -/

/-- The six points of `Fin 6`, paired as `{0, 1}, {2, 3}, {4, 5}`: `p (i, b) = 2 i + b`. -/
def finSixTradePoint (y : Fin 3 × Bool) : Fin 6 :=
  ⟨2 * y.1.val + (if y.2 then 1 else 0), by have := y.1.isLt; split_ifs <;> omega⟩

/-- The six points are distinct. -/
theorem finSixTradePoint_injective : Function.Injective finSixTradePoint := by
  unfold Function.Injective
  decide

/-- **Pair balance does not imply optimality.** On `N = 6` points with `d = 2`, take the pairs
`{0, 1}, {2, 3}, {4, 5}`, `S = ∅`, and `m = 1 + (101/1000) z`. Then `m` is a top weight of all
triangles on six points and every pair has the same weight, so the whole complex attains
`−1/(N − 1) = −1/5`; but the vertex link of `0` has walk second eigenvalue above `−1/5` (by
computation it is `−1/4 + (101/1000)/2 = −0.1995`), so `m` is not optimal. Hence condition (b) of
`isLocalSpectralExpanderOf_complete_neg_one_div_iff` does not follow from (a). The threshold is
`(d − 1)/(2(N − 1)) = 1/10`. -/
theorem fin_six_counterexample :
    (complete (Fin 6) 2).IsTopWeight 2 (uniformAddTrade 2 finSixTradePoint ∅ (101 / 1000)) ∧
      (∃ c, ∀ u v : Fin 6, u ≠ v →
        faceWeight (uniformAddTrade 2 finSixTradePoint ∅ (101 / 1000)) {u, v} = c) ∧
      ¬ WalkSecondEigenvalueLE
        (linkWeightOf (uniformAddTrade 2 finSixTradePoint ∅ (101 / 1000)) {0}) (-(1 / 5)) ∧
      ¬ (complete (Fin 6) 2).IsLocalSpectralExpanderOf 2
        (uniformAddTrade 2 finSixTradePoint ∅ (101 / 1000)) (-(1 / 5)) := by
  have hp := finSixTradePoint_injective
  have hS : ∀ y, finSixTradePoint y ∉ (∅ : Finset (Fin 6)) := fun y => notMem_empty _
  have hSd : #(∅ : Finset (Fin 6)) + 3 = 2 + 1 := rfl
  have h5 : -(1 / (5 : ℝ)) = -(1 / ((Fintype.card (Fin 6) : ℝ) - 1)) := by
    rw [Fintype.card_fin]; norm_num
  have h0 : ({0} : Finset (Fin 6)) = insert (finSixTradePoint (0, false)) ∅ := by
    decide
  have hfail : ¬ WalkSecondEigenvalueLE
      (linkWeightOf (uniformAddTrade 2 finSixTradePoint ∅ (101 / 1000)) {0}) (-(1 / 5)) := by
    intro h
    rw [h0, h5] at h
    have := abs_le_of_walkSecondEigenvalueLE_uniformAddTrade hp hS hSd h
    rw [Fintype.card_fin] at this
    norm_num at this
  refine ⟨isTopWeight_uniformAddTrade hp hS hSd (by norm_num),
    ⟨_, fun u v huv => faceWeight_uniformAddTrade_pair hp (by norm_num) huv _⟩, hfail,
    fun h => hfail (h.walkSecondEigenvalueLE
      (Or.inr (mem_complete.mpr ⟨singleton_nonempty _, by rw [card_singleton]; omega⟩))
      (by rw [card_singleton]))⟩

end

section

variable [DecidableEq ι] {d : ℕ}

omit [DecidableEq ι] in
/-- **Convex combinations with proportional degrees.** If two weighted graphs satisfy the same walk
bound `lam` and have proportional degree vectors, `deg₁ = c₁ g` and `deg₂ = c₂ g`, then so does
`a w₁ + b w₂` for `a, b ≥ 0` with `a c₁ + b c₂ > 0`: the mean-zero condition is then the same
linear condition on `f` for all three graphs, and both sides of the bound are linear in the
weights. Without proportional degrees the mean-zero conditions differ and the conclusion can
fail. -/
theorem walkSecondEigenvalueLE_add_of_sum_eq {w₁ w₂ : ι → ι → ℝ} {lam a b c₁ c₂ : ℝ}
    {g : ι → ℝ} (h₁ : WalkSecondEigenvalueLE w₁ lam) (h₂ : WalkSecondEigenvalueLE w₂ lam)
    (hg₁ : ∀ u, ∑ v, w₁ u v = c₁ * g u) (hg₂ : ∀ u, ∑ v, w₂ u v = c₂ * g u)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < a * c₁ + b * c₂) :
    WalkSecondEigenvalueLE (fun u v => a * w₁ u v + b * w₂ u v) lam := by
  intro f hf
  have hdeg : ∀ u, ∑ v, (a * w₁ u v + b * w₂ u v) = (a * c₁ + b * c₂) * g u := fun u => by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hg₁, hg₂]; ring
  simp only [hdeg] at hf ⊢
  have hgf : ∑ u, g u * f u = 0 := by
    have : ∑ u, (a * c₁ + b * c₂) * g u * f u = (a * c₁ + b * c₂) * ∑ u, g u * f u := by
      rw [mul_sum]; exact sum_congr rfl fun u _ => by ring
    rw [this] at hf
    exact (mul_eq_zero.mp hf).resolve_left hc.ne'
  have hf₁ : ∑ u, (∑ v, w₁ u v) * f u = 0 := by
    simp only [hg₁, mul_assoc, ← mul_sum, hgf, mul_zero]
  have hf₂ : ∑ u, (∑ v, w₂ u v) * f u = 0 := by
    simp only [hg₂, mul_assoc, ← mul_sum, hgf, mul_zero]
  have e1 := h₁ f hf₁
  have e2 := h₂ f hf₂
  have hq : ∑ u, ∑ v, (a * w₁ u v + b * w₂ u v) * f u * f v =
      a * ∑ u, ∑ v, w₁ u v * f u * f v + b * ∑ u, ∑ v, w₂ u v * f u * f v := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun v _ => by ring
  have hn : ∑ u, (a * c₁ + b * c₂) * g u * f u ^ 2 =
      a * ∑ u, (∑ v, w₁ u v) * f u ^ 2 + b * ∑ u, (∑ v, w₂ u v) * f u ^ 2 := by
    simp only [hg₁, hg₂, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun u _ => by ring
  rw [hq, hn]
  nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hb]

/-- For a top weight of the complete complex of dimension `d ≥ 1`, every pair of distinct points has
positive weight. -/
theorem faceWeight_pair_pos_of_isTopWeight_complete {m : Finset ι → ℝ}
    (hm : (complete ι d).IsTopWeight d m) (hd : 1 ≤ d) {u v : ι} (huv : u ≠ v) :
    0 < faceWeight m {u, v} := by
  have hN := card_le_of_isTopWeight_complete hm
  obtain ⟨F, hsF, -, hF⟩ := exists_subsuperset_card_eq (n := d + 1)
    (subset_univ ({u, v} : Finset ι)) (by rw [card_pair huv]; omega) (by rw [card_univ]; exact hN)
  exact hm.faceWeight_pos_iff.mpr ⟨F, mem_complete.mpr ⟨card_pos.mp (by omega), by omega⟩, hF, hsF⟩

/-- **Vertex links of a pair-balanced weight are regular.** If `m` vanishes off the sets with
`d + 1` elements and every pair has weight `c`, the link of `{x}` gives every point `u ≠ x`
degree `(d − 1) c`, and `x` degree `0`. No sign condition on `m`. -/
theorem sum_linkWeightOf_singleton_of_pairBalanced {m : Finset ι → ℝ}
    (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {c : ℝ}
    (hc : ∀ u v : ι, u ≠ v → faceWeight m {u, v} = c) (x u : ι) :
    ∑ v, linkWeightOf m {x} u v = ((d : ℝ) - 1) * c * (if u = x then 0 else 1) := by
  rw [sum_linkWeightOf hcard, card_singleton]
  by_cases hu : u = x
  · rw [if_pos (mem_singleton.mpr hu), if_pos hu, mul_zero]
  · rw [if_neg (by rwa [mem_singleton]), if_neg hu, hc u x hu]
    push_cast
    ring

/-- **The vertex-link constraints are convex.** For every `d`, the top weights of the complete
`d`-dimensional complex on `N` points that satisfy the bound `−1/(N − 1)` for the whole complex and
for every vertex link form a convex set. By part (i) the first constraint is pair balance, and
then every vertex link is regular of degree `(d − 1) c`
(`sum_linkWeightOf_singleton_of_pairBalanced`), so for each test function the constraint is linear
in the weight: a linear matrix inequality.
Degenerate cases: for `d ≤ 1` the vertex links have no edges and their constraints are vacuous. -/
theorem convex_setOf_vertexLinks :
    Convex ℝ {m : Finset ι → ℝ | (complete ι d).IsTopWeight d m ∧
      WalkSecondEigenvalueLE (linkWeightOf m ∅) (-(1 / ((Fintype.card ι : ℝ) - 1))) ∧
      ∀ x : ι,
        WalkSecondEigenvalueLE (linkWeightOf m {x}) (-(1 / ((Fintype.card ι : ℝ) - 1)))} := by
  rintro m₁ ⟨hm₁, h₁, hx₁⟩ m₂ ⟨hm₂, h₂, hx₂⟩ a b ha hb hab
  have e : a • m₁ + b • m₂ = fun F => a * m₁ F + b * m₂ F := by
    funext F
    simp
  rw [e]
  have hab' : 0 < a ∨ 0 < b := by
    by_contra h
    push Not at h
    linarith
  have hm : (complete ι d).IsTopWeight d (fun F => a * m₁ F + b * m₂ F) :=
    ⟨hm₁.isPure, hm₁.exists_mem, fun F hF hc => by
      have := hm₁.pos F hF hc
      have := hm₂.pos F hF hc
      rcases hab' with h | h <;> nlinarith,
      fun F hF => by rw [hm₁.eq_zero F hF, hm₂.eq_zero F hF]; ring⟩
  obtain ⟨c₁, hc₁⟩ := (walkSecondEigenvalueLE_linkWeightOf_empty_complete_iff hm₁).mp h₁
  obtain ⟨c₂, hc₂⟩ := (walkSecondEigenvalueLE_linkWeightOf_empty_complete_iff hm₂).mp h₂
  refine ⟨hm, (walkSecondEigenvalueLE_linkWeightOf_empty_complete_iff hm).mpr
    ⟨a * c₁ + b * c₂, fun u v huv => by
      rw [faceWeight_add, faceWeight_const_mul, faceWeight_const_mul, hc₁ u v huv,
        hc₂ u v huv]⟩, fun x => ?_⟩
  have hlink : linkWeightOf (fun F => a * m₁ F + b * m₂ F) {x} =
      fun u v => a * linkWeightOf m₁ {x} u v + b * linkWeightOf m₂ {x} u v := by
    funext u v
    rw [linkWeightOf_add, linkWeightOf_const_mul, linkWeightOf_const_mul]
  rw [hlink]
  rcases (by omega : d ≤ 1 ∨ 2 ≤ d) with hd1 | hd2
  · -- `d ≤ 1`: the vertex links have no edges
    refine walkSecondEigenvalueLE_of_forall_eq_zero (fun u v => ?_) _
    rw [linkWeightOf_eq_zero_of_le_card hm₁.card_eq_of_ne_zero (by rw [card_singleton]; exact hd1),
      linkWeightOf_eq_zero_of_le_card hm₂.card_eq_of_ne_zero (by rw [card_singleton]; exact hd1)]
    ring
  · have hd : 1 ≤ d := by omega
    have hN := card_le_of_isTopWeight_complete hm₁
    obtain ⟨u, v, huv⟩ : ∃ u v : ι, u ≠ v := Fintype.exists_pair_of_one_lt_card (by omega)
    have hc₁0 : 0 < c₁ := hc₁ u v huv ▸ faceWeight_pair_pos_of_isTopWeight_complete hm₁ hd huv
    have hc₂0 : 0 < c₂ := hc₂ u v huv ▸ faceWeight_pair_pos_of_isTopWeight_complete hm₂ hd huv
    have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
      linarith
    exact walkSecondEigenvalueLE_add_of_sum_eq (hx₁ x) (hx₂ x)
      (sum_linkWeightOf_singleton_of_pairBalanced hm₁.card_eq_of_ne_zero hc₁ x)
      (sum_linkWeightOf_singleton_of_pairBalanced hm₂.card_eq_of_ne_zero hc₂ x) ha hb
      (by rcases hab' with h | h <;> nlinarith [mul_pos hd1 hc₁0, mul_pos hd1 hc₂0])

/-- **For `d ≤ 2` the optimal weights form a convex cone.** For `d ≤ 2`, the set of weights `m` that
make the complete `d`-dimensional complex a `(−1/(N − 1))`-local spectral expander is convex (and a
cone, by `isLocalSpectralExpanderOf_const_mul`). For `d = 2` the only links besides the complex are
the vertex links (`convex_setOf_vertexLinks`). For `d = 1` the set consists of the positive
multiples of the uniform weight, and for `d = 0` it is empty.

For `d ≥ 3` the links of faces with at least two points need not be regular, and convexity fails in
general: computation found optimal `P₁, P₂` for `N = 7`, `d = 3` whose midpoint is not optimal. That
example is not formalized here. -/
theorem convex_setOf_isLocalSpectralExpanderOf_complete (hd2 : d ≤ 2) :
    Convex ℝ {m : Finset ι → ℝ |
      (complete ι d).IsLocalSpectralExpanderOf d m (-(1 / ((Fintype.card ι : ℝ) - 1)))} := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · convert convex_empty (𝕜 := ℝ) (E := Finset ι → ℝ)
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact not_isLocalSpectralExpanderOf_zero
  · convert convex_setOf_vertexLinks (ι := ι) (d := d) using 1
    ext m
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨h.isTopWeight, h.walkSecondEigenvalueLE (Or.inl rfl) (by rw [card_empty]; omega),
        fun x => ?_⟩
      rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl
      · exact walkSecondEigenvalueLE_of_forall_eq_zero (fun u v =>
          linkWeightOf_eq_zero_of_le_card h.isTopWeight.card_eq_of_ne_zero
            (by rw [card_singleton]) u v) _
      · exact h.walkSecondEigenvalueLE
          (Or.inr (mem_complete.mpr ⟨singleton_nonempty x, by rw [card_singleton]; omega⟩))
          (by rw [card_singleton])
    · rintro ⟨hm, h0, hx⟩
      refine (isLocalSpectralExpanderOf_complete_neg_one_div_iff hd hm).mpr
        ⟨(walkSecondEigenvalueLE_linkWeightOf_empty_complete_iff hm).mp h0,
          fun σ hσ1 hσd => ?_⟩
      obtain ⟨x, rfl⟩ := card_eq_one.mp (by omega : #σ = 1)
      exact hx x

end

section

variable [DecidableEq ι] {d : ℕ}

omit [DecidableEq ι] in
/-- **The walk bound without the mean-zero constraint.** For symmetric `w` with positive total
degree `D = Σ_{u,v} w u v`, the bound `lam` holds exactly when, for every `f`,
`D (Q(f) − lam N(f)) ≤ (1 − lam) M(f)²`, where `Q(f) = Σ_{u,v} w u v f u f v`,
`N(f) = Σ_u deg u f u²` and `M(f) = Σ_u deg u f u`. (Shift `f` by its degree-weighted mean.) Each of
these inequalities is a polynomial inequality in the weights and the values of `f`. The hypothesis
`D > 0` is needed: for `w = 0` the right side holds and so does the bound, but the proof divides by
`D`. -/
theorem walkSecondEigenvalueLE_iff_forall_le {w : ι → ι → ℝ} {lam : ℝ}
    (hsymm : ∀ u v, w u v = w v u) (hD : 0 < ∑ u, ∑ v, w u v) :
    WalkSecondEigenvalueLE w lam ↔ ∀ f : ι → ℝ,
      (∑ u, ∑ v, w u v) * (∑ u, ∑ v, w u v * f u * f v - lam * ∑ u, (∑ v, w u v) * f u ^ 2) ≤
        (1 - lam) * (∑ u, (∑ v, w u v) * f u) ^ 2 := by
  constructor
  · intro h f
    obtain ⟨Dw, hDw⟩ : ∃ x, x = ∑ u, ∑ v, w u v := ⟨_, rfl⟩
    obtain ⟨M, hM⟩ : ∃ x, x = ∑ u, (∑ v, w u v) * f u := ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ x, x = ∑ u, ∑ v, w u v * f u * f v := ⟨_, rfl⟩
    obtain ⟨Nf, hNf⟩ : ∃ x, x = ∑ u, (∑ v, w u v) * f u ^ 2 := ⟨_, rfl⟩
    rw [← hDw, ← hM, ← hQ, ← hNf]
    rw [← hDw] at hD
    obtain ⟨μ, hμ⟩ : ∃ μ, μ = M / Dw := ⟨_, rfl⟩
    have hμD : μ * Dw = M := by rw [hμ, div_mul_cancel₀ _ hD.ne']
    have hA : ∑ u, ∑ v, w u v * f u = M := by
      rw [hM]
      simp only [Finset.sum_mul]
    have hB : ∑ u, ∑ v, w u v * f v = M := by
      rw [hM, Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => by rw [hsymm]
    have hg : ∑ u, (∑ v, w u v) * (f u - μ) = 0 := by
      have e : ∀ u, (∑ v, w u v) * (f u - μ) = (∑ v, w u v) * f u - μ * ∑ v, w u v :=
        fun u => by ring
      rw [Finset.sum_congr rfl fun u _ => e u, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hM,
        ← hDw, hμD, sub_self]
    have h1 := h (fun u => f u - μ) hg
    have hQg : ∑ u, ∑ v, w u v * (f u - μ) * (f v - μ) = Q - 2 * μ * M + μ ^ 2 * Dw := by
      have e : ∀ u, ∑ v, w u v * (f u - μ) * (f v - μ) =
          ∑ v, w u v * f u * f v - μ * ∑ v, w u v * f u - μ * ∑ v, w u v * f v +
            μ ^ 2 * ∑ v, w u v := by
        intro u
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [Finset.sum_congr rfl fun u _ => e u, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hA, hB,
        ← hQ, ← hDw]
      ring
    have hNg : ∑ u, (∑ v, w u v) * (f u - μ) ^ 2 = Nf - 2 * μ * M + μ ^ 2 * Dw := by
      have e : ∀ u, (∑ v, w u v) * (f u - μ) ^ 2 =
          (∑ v, w u v) * f u ^ 2 - 2 * μ * ((∑ v, w u v) * f u) + μ ^ 2 * ∑ v, w u v :=
        fun u => by ring
      rw [Finset.sum_congr rfl fun u _ => e u, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← hNf, ← hM, ← hDw]
    rw [hQg, hNg] at h1
    have h2 : Q - lam * Nf ≤ (1 - lam) * (2 * μ * M - μ ^ 2 * Dw) := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hD.le
    calc Dw * (Q - lam * Nf) ≤ Dw * ((1 - lam) * (2 * μ * M - μ ^ 2 * Dw)) := h3
      _ = (1 - lam) * (2 * (μ * Dw) * M - (μ * Dw) ^ 2) := by ring
      _ = (1 - lam) * M ^ 2 := by rw [hμD]; ring
  · intro h f hf
    have h1 := h f
    rw [hf] at h1
    have h2 : (∑ u, ∑ v, w u v) * (∑ u, ∑ v, w u v * f u * f v -
        lam * ∑ u, (∑ v, w u v) * f u ^ 2) ≤ 0 := by simpa using h1
    have h3 : ∑ u, ∑ v, w u v * f u * f v - lam * ∑ u, (∑ v, w u v) * f u ^ 2 ≤ 0 := by
      by_contra h4
      push Not at h4
      have := mul_pos hD h4
      linarith
    linarith

omit [Fintype ι] in
/-- Each link weight is a continuous (indeed linear) function of the weight `m`. -/
theorem continuous_linkWeightOf [Fintype ι] (σ : Finset ι) (u v : ι) :
    Continuous fun m : Finset ι → ℝ => linkWeightOf m σ u v := by
  unfold linkWeightOf faceWeight
  split_ifs
  · exact continuous_finsetSum _ fun F _ => continuous_apply F
  · exact continuous_const

/-- **The expander weights are relatively closed.** For any complex `K`, any `d` and any `lam`,
there is a closed set `C ⊆ (Finset ι → ℝ)` such that a top weight `m` makes `K` a `lam`-local
spectral expander exactly when `m ∈ C`. So the set of such weights is closed in the cone of top
weights (an open subset of the space of weights supported on the top faces). In particular the
optimal weights of the complete complex form a closed subset of the pair-balanced cone.

`C` is cut out by the inequalities of `walkSecondEigenvalueLE_iff_forall_le`, polynomial in `m` and
the test function `f`, one family for each link. Eliminating the quantifier over `f` would make
`C` semialgebraic; that is not done here, and Mathlib has no notion of semialgebraic set. For
`d = 0` there is no expander and `C = ∅`. -/
theorem exists_isClosed_isLocalSpectralExpanderOf_iff (K : PreAbstractSimplicialComplex ι)
    (d : ℕ) (lam : ℝ) :
    ∃ C : Set (Finset ι → ℝ), IsClosed C ∧
      ∀ m, K.IsTopWeight d m → (K.IsLocalSpectralExpanderOf d m lam ↔ m ∈ C) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨∅, isClosed_empty, fun m _ =>
      ⟨fun h => absurd h not_isLocalSpectralExpanderOf_zero,
        fun h => absurd h (Set.notMem_empty m)⟩⟩
  refine ⟨⋂ σ : Finset ι, ⋂ (_ : (σ = ∅ ∨ σ ∈ K) ∧ #σ + 1 ≤ d), ⋂ f : ι → ℝ,
    {m | (∑ u, ∑ v, linkWeightOf m σ u v) * (∑ u, ∑ v, linkWeightOf m σ u v * f u * f v -
        lam * ∑ u, (∑ v, linkWeightOf m σ u v) * f u ^ 2) ≤
      (1 - lam) * (∑ u, (∑ v, linkWeightOf m σ u v) * f u) ^ 2}, ?_, fun m hm => ?_⟩
  · refine isClosed_iInter fun σ => isClosed_iInter fun _ => isClosed_iInter fun f => ?_
    have hc := continuous_linkWeightOf (ι := ι) σ
    refine isClosed_le ?_ ?_
    · refine (continuous_finsetSum _ fun u _ => continuous_finsetSum _ fun v _ => hc u v).mul
        ((continuous_finsetSum _ fun u _ => continuous_finsetSum _ fun v _ =>
          ((hc u v).mul continuous_const).mul continuous_const).sub
          (continuous_const.mul (continuous_finsetSum _ fun u _ =>
            (continuous_finsetSum _ fun v _ => hc u v).mul continuous_const)))
    · exact continuous_const.mul ((continuous_finsetSum _ fun u _ =>
        (continuous_finsetSum _ fun v _ => hc u v).mul continuous_const).pow 2)
  · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    have hpos : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d →
        0 < ∑ u, ∑ v, linkWeightOf m σ u v := by
      intro σ hσ hcard
      obtain ⟨u, v, huv⟩ := hm.exists_linkWeightOf_pos hσ hcard
      have hnn := linkWeightOf_nonneg hm.nonneg σ
      refine lt_of_lt_of_le huv (le_trans
        (Finset.single_le_sum (fun x _ => hnn u x) (mem_univ v)) ?_)
      exact Finset.single_le_sum (f := fun y => ∑ x, linkWeightOf m σ y x)
        (fun y _ => Finset.sum_nonneg fun x _ => hnn y x) (mem_univ u)
    constructor
    · intro h σ hσ f
      exact (walkSecondEigenvalueLE_iff_forall_le (linkWeightOf_symm m σ)
        (hpos σ hσ.1 hσ.2)).mp (h.walkSecondEigenvalueLE hσ.1 hσ.2) f
    · intro h
      refine ⟨hd, hm, fun σ hσ hcard => ?_⟩
      exact (walkSecondEigenvalueLE_iff_forall_le (linkWeightOf_symm m σ)
        (hpos σ hσ hcard)).mpr fun f => h σ ⟨hσ, hcard⟩ f

end

end PreAbstractSimplicialComplex.OptimalWeights
