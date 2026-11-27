/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.CompleteComplex

/-!
# The complete complex in every dimension and size

The complete `d`-dimensional complex `complete ι d` on `N = Fintype.card ι` points has every
nonempty set of at most `d + 1` points as a face. `Expanders/CompleteComplex.lean` treats the case
`N = 5`, `d = 2` by hand. Here every `N` and `d` is handled at once. For `N ≥ d + 1`, the link of
every set `σ` with `#σ + 1 ≤ d` is a complete graph with constant weights, so its random walk has
a single nontrivial eigenvalue, `−1/(N − 1 − #σ)`. Consequences:

* trickling down is tight along the whole chain of links: for `d ≥ 2` the complete complex meets
  the hypotheses of `trickling_down`, and fed the exact value at the smallest links, the theorem
  returns the exact value at every link;
* the complete complex is a `lam`-local-spectral expander exactly for `lam ≥ −1/(N − 1)`;
* no complex on `N` vertices does better. The weighted underlying graph of any `d`-dimensional
  expander with `n` vertices has parameter at least `−1/(n − 1)`, by the trace bound for random
  walks, so `−1/(N − 1)` is the least possible parameter on `N` vertices;
* the **simplex gap**: a parameter below `−1/(d + 1)` forces a single top face.

All subtractions inside real-valued bounds are in `ℝ`; the docstrings name the junk values.

## Definitions
* `PreAbstractSimplicialComplex.cliqueWeight T c`: the complete graph on `T` with every edge of
  weight `c`, as a weighted graph on `ι`.

## Theorems
Weighted cliques:
* `sum_cliqueWeight`: the degrees, `c · (#T − 1)` on `T` and `0` off it. **Proved.**
* `sum_cliqueWeight_mul_mul_eq`, `walkSecondEigenvalueLE_cliqueWeight`: on the mean-zero space the
  quadratic form of the clique on `T` is exactly `−1/(#T − 1)` times the degree-weighted norm, with
  no hypothesis on `T` or the weight. **Proved.**
* `walkSecondEigenvalueLE_cliqueWeight_iff`: for `#T ≥ 2` and `c > 0`, the bound `lam` is valid
  exactly when `−1/(#T − 1) ≤ lam`. **Proved.**

The complete complex:
* `topDegree_complete_eq_choose`: a set `s` with `#s ≤ d + 1` lies in `C(N − #s, d + 1 − #s)` top
  faces. **Proved.**
* `linkWeight_complete_eq_choose`, `linkWeight_complete_eq_cliqueWeight`: the link graph of `σ`
  is the complete graph on the points outside `σ` with weight `C(N − #σ − 2, d − 1 − #σ)`.
  **Proved.**
* `sum_linkWeight_complete_mul_mul_eq`: its quadratic form is `−1/(N − 1 − #σ)` times the norm on
  the whole mean-zero space. **Proved.**
* `walkSecondEigenvalueLE_linkWeight_complete_iff`: **exact link spectra**; for `N ≥ d + 1` the
  bound `μ` is valid for the link of `σ` exactly when `−1/(N − 1 − #σ) ≤ μ`. **Proved.**
* `trickling_down_bound_complete`: the algebra of the trickling-down recursion at
  `lam = −1/(N − d)`. **Proved.**
* `walkSecondEigenvalueLE_linkWeight_complete_iff_tricklingBound`: the trickling-down formula,
  evaluated at that value, is the least valid bound for each link. **Proved.**
* `trickling_down_complete`: **trickling down is tight**; for `d ≥ 2` the theorem
  `trickling_down` itself applies to the complete complex (its links are connected), and the bound
  it returns for each link is the least valid one. **Proved.**
* `isLocalSpectralExpander_complete_iff_le`: for `1 ≤ d` and `N ≥ d + 1`, the complete complex is
  a `lam`-local-spectral expander exactly when `−1/(N − 1) ≤ lam`. **Proved.**
* `isLocalSpectralExpander_complete_fin5_two_iff`: the case `N = 5`, `d = 2`; the value `−1/4` of
  `isLocalSpectralExpander_complete_fin5_two` is optimal. **Proved.**

The best possible parameter on `N` vertices:
* `neg_one_div_card_le_of_walkSecondEigenvalueLE`: the **trace bound**; a symmetric nonnegative
  weighted graph with `n ≥ 2` vertices of positive degree has walk second eigenvalue at least
  `−1/(n − 1)`. **Proved.**
* `IsTopWeight.succ_le_natCard_vertices`: a weighted `d`-dimensional complex has at least `d + 1`
  vertices. **Proved.**
* `IsLocalSpectralExpanderOf.neg_one_div_natCard_vertices_le`,
  `IsLocalSpectralExpander.neg_one_div_natCard_vertices_le`: a `lam`-local-spectral expander with
  `n` vertices has `−1/(n − 1) ≤ lam`. **Proved.**
* `isLeast_setOf_isLocalSpectralExpanderOf`, `isLeast_setOf_isLocalSpectralExpander`: among the
  `d`-dimensional local spectral expanders on `ι` in which every point is a vertex, the least
  parameter is `−1/(N − 1)`, weighted or not. **Proved.**

The simplex gap:
* `IsLocalSpectralExpanderOf.neg_one_div_succ_le_of_ne`: two distinct top faces force
  `lam ≥ −1/(d + 1)`. **Proved.**
* `walkSecondEigenvalueLE_linkWeightOf_iff_of_unique_top`,
  `isLocalSpectralExpanderOf_iff_of_unique_top`: a weighted simplex has exact link values
  `−1/(d − #σ)` and is a `lam`-expander exactly when `−1/d ≤ lam`. **Proved.**
* `exists_lt_neg_one_div_succ_isLocalSpectralExpanderOf_iff`: some `lam < −1/(d + 1)` is attained
  exactly by a single simplex. **Proved.**

## References
None of this is new mathematics. The link spectra are a textbook exercise, tightness is a line of
algebra on top of them, and the trace bound is classical.
* I. Dinur, *Lecture 2: Trickle down theorem, and random walks on HDX*, Weizmann HDX course
  (2022), Example 2.1: the links of the complete complex are complete graphs ("check!").
* I. Oppenheim, *Local spectral expansion approach to high dimensional expanders part I: Descent
  of spectral gaps*, Discrete Comput. Geom. 59 (2018); arXiv:1709.04431. The trickle-down theorem.
* F. Chung, *Spectral Graph Theory*, CBMS Regional Conference Series 92, AMS (1997),
  Lemma 1.7(ii): the second-smallest eigenvalue `λ₁` of the normalised Laplacian (eigenvalues
  `0 = λ₀ ≤ λ₁ ≤ …`, counted with multiplicity, so `λ₁ = 0` for a disconnected graph) of a graph
  on `n ≥ 2` vertices is at most `n/(n − 1)`, with equality exactly for the complete graph. The
  walk eigenvalues are `1 − λᵢ`, so `1 − λ₁` is the walk's second-largest eigenvalue, and for a
  graph without isolated vertices this is the trace bound. The version here counts only the
  vertices of positive degree, and allows weights and loops.
* J. Jost, R. Mulas, F. Münch, *Spectral gap of the largest eigenvalue of the normalized graph
  Laplacian*, arXiv:1910.14402: the companion bound `λ_max ≥ n/(n − 1)` for a graph without
  isolated vertices, with equality exactly for complete graphs, attributed to Chung.
* Y. Dikstein, I. Dinur, Y. Filmus, P. Harsha, *Boolean function analysis on high-dimensional
  expanders*, APPROX/RANDOM 2018: the complete complex as an `O(1/n)` two-sided local spectral
  expander.
-/

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-! ### The complete graph with constant weights -/

/-- The sum of `f u * f v` over ordered pairs of distinct elements of `T` is the square of the sum
minus the sum of the squares. (The same statement is a private lemma of
`Expanders/WeightedComplex.lean`.) -/
private theorem sum_sum_ite_ne_mul_eq_sq_sub (T : Finset ι) (f : ι → ℝ) :
    ∑ u, ∑ v, (if u ≠ v ∧ u ∈ T ∧ v ∈ T then f u * f v else 0) =
      (∑ v ∈ T, f v) ^ 2 - ∑ v ∈ T, f v ^ 2 := by
  have h : ∀ u, ∑ v, (if u ≠ v ∧ u ∈ T ∧ v ∈ T then f u * f v else 0) =
      if u ∈ T then f u * (∑ v ∈ T, f v) - f u ^ 2 else 0 := by
    intro u
    by_cases hu : u ∈ T
    · have e : ∀ v, (if u ≠ v ∧ u ∈ T ∧ v ∈ T then f u * f v else 0) =
          if v ∈ T.erase u then f u * f v else 0 := by
        intro v
        refine if_congr ?_ rfl rfl
        rw [Finset.mem_erase]
        exact ⟨fun h => ⟨h.1.symm, h.2.2⟩, fun h => ⟨h.1.symm, hu, h.2⟩⟩
      rw [if_pos hu, Finset.sum_congr rfl fun v _ => e v, Fintype.sum_ite_mem,
        Finset.sum_erase_eq_sub hu, Finset.mul_sum]
      ring
    · rw [if_neg hu]
      exact Finset.sum_eq_zero fun v _ => if_neg fun h => hu h.2.1
  rw [Finset.sum_congr rfl fun u _ => h u, Fintype.sum_ite_mem, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  ring

/-- The **complete graph on `T` with every edge of weight `c`**, as a weighted graph on all of `ι`:
distinct `u, v ∈ T` are joined with weight `c`. There are no loops, and every point outside `T` is
isolated. For `#T ≤ 1` or `c = 0` the graph has no edges. -/
def cliqueWeight (T : Finset ι) (c : ℝ) (u v : ι) : ℝ :=
  if u ≠ v ∧ u ∈ T ∧ v ∈ T then c else 0

/-- **Degrees of a clique.** In the complete graph on `T` with edge weight `c`, a point of `T` has
degree `c · (#T − 1)` and a point outside `T` has degree `0`. -/
theorem sum_cliqueWeight (T : Finset ι) (c : ℝ) (u : ι) :
    ∑ v, cliqueWeight T c u v = if u ∈ T then c * ((#T : ℝ) - 1) else 0 := by
  unfold cliqueWeight
  by_cases hu : u ∈ T
  · have e : ∀ v, (if u ≠ v ∧ u ∈ T ∧ v ∈ T then c else 0) =
        if v ∈ T.erase u then c else 0 := by
      intro v
      refine if_congr ?_ rfl rfl
      rw [Finset.mem_erase]
      exact ⟨fun h => ⟨h.1.symm, h.2.2⟩, fun h => ⟨h.1.symm, hu, h.2⟩⟩
    rw [if_pos hu, Finset.sum_congr rfl fun v _ => e v, Fintype.sum_ite_mem, sum_const,
      card_erase_of_mem hu, nsmul_eq_mul, Nat.cast_sub (card_pos.mpr ⟨u, hu⟩), Nat.cast_one]
    ring
  · rw [if_neg hu]
    exact Finset.sum_eq_zero fun v _ => if_neg fun h => hu h.2.1

/-- **The whole spectrum of a clique.** In the complete graph on `T` with edge weight `c`, every
`f` with degree-weighted mean zero has `Σ_{u,v} w(u,v) f(u) f(v) = −1/(#T − 1) · Σ_u deg(u) f(u)²`.
So for `#T ≥ 2` and `c > 0` the random walk acts as multiplication by `−1/(#T − 1)` on the whole
mean-zero space: its eigenvalues on `T` are `1` (on constants) and `−1/(#T − 1)`.

There is no hypothesis on `T` or `c`. When the graph has no edges (`#T ≤ 1` or `c = 0`) both sides
are `0`, whatever the coefficient is; for `#T = 1` the coefficient is the junk value
`−(1 / 0) = 0`, and for `T = ∅` it is `−(1 / (−1)) = 1`. For `c < 0` the identity still holds. -/
theorem sum_cliqueWeight_mul_mul_eq (T : Finset ι) (c : ℝ) (f : ι → ℝ)
    (hf : ∑ u, (∑ v, cliqueWeight T c u v) * f u = 0) :
    ∑ u, ∑ v, cliqueWeight T c u v * f u * f v =
      -(1 / ((#T : ℝ) - 1)) * ∑ u, (∑ v, cliqueWeight T c u v) * f u ^ 2 := by
  by_cases hT : 2 ≤ #T
  · have hm : (0 : ℝ) < (#T : ℝ) - 1 := by
      have : (2 : ℝ) ≤ #T := by exact_mod_cast hT
      linarith
    have hmean : ∑ u, (∑ v, cliqueWeight T c u v) * f u = c * ((#T : ℝ) - 1) * ∑ u ∈ T, f u := by
      simp only [sum_cliqueWeight, ite_mul, zero_mul, Fintype.sum_ite_mem, Finset.mul_sum]
    have hnorm : ∑ u, (∑ v, cliqueWeight T c u v) * f u ^ 2 =
        c * ((#T : ℝ) - 1) * ∑ u ∈ T, f u ^ 2 := by
      simp only [sum_cliqueWeight, ite_mul, zero_mul, Fintype.sum_ite_mem, Finset.mul_sum]
    have hquad : ∑ u, ∑ v, cliqueWeight T c u v * f u * f v =
        c * ((∑ v ∈ T, f v) ^ 2 - ∑ v ∈ T, f v ^ 2) := by
      rw [← sum_sum_ite_ne_mul_eq_sq_sub, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      unfold cliqueWeight
      split_ifs <;> ring
    rw [hquad, hnorm]
    by_cases hc : c = 0
    · rw [hc]
      ring
    · rw [hmean] at hf
      have hs1 : ∑ u ∈ T, f u = 0 := (mul_eq_zero.mp hf).resolve_left (mul_ne_zero hc hm.ne')
      rw [hs1]
      field_simp
      ring
  · have hzero : ∀ u v, cliqueWeight T c u v = 0 := by
      intro u v
      refine if_neg fun h => h.1 ?_
      exact Finset.card_le_one.mp (by omega) u h.2.1 v h.2.2
    simp [hzero]

/-- The complete graph on `T` with edge weight `c` satisfies the second-eigenvalue bound
`−1/(#T − 1)`, with equality for every test function (`sum_cliqueWeight_mul_mul_eq`). There is no
hypothesis on `T` or `c`; the degenerate cases are those of `sum_cliqueWeight_mul_mul_eq`. -/
theorem walkSecondEigenvalueLE_cliqueWeight (T : Finset ι) (c : ℝ) :
    WalkSecondEigenvalueLE (cliqueWeight T c) (-(1 / ((#T : ℝ) - 1))) := fun f hf =>
  (sum_cliqueWeight_mul_mul_eq T c f hf).le

/-- **The second eigenvalue of a weighted clique.** For `#T ≥ 2` and `c > 0`, the random walk on
the complete graph on `T` with edge weight `c` has second eigenvalue at most `lam` exactly when
`−1/(#T − 1) ≤ lam`.

Both hypotheses are needed. For `#T ≤ 1` or `c = 0` the graph has no edges and every `lam` is
valid. For `c < 0` the degree-weighted norm is `≤ 0`, and the valid `lam` are exactly those with
`lam ≤ −1/(#T − 1)`. -/
theorem walkSecondEigenvalueLE_cliqueWeight_iff {T : Finset ι} (hT : 2 ≤ #T) {c : ℝ} (hc : 0 < c)
    {lam : ℝ} :
    WalkSecondEigenvalueLE (cliqueWeight T c) lam ↔ -(1 / ((#T : ℝ) - 1)) ≤ lam := by
  have hm : (0 : ℝ) < (#T : ℝ) - 1 := by
    have : (2 : ℝ) ≤ #T := by exact_mod_cast hT
    linarith
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < #T)
    let f : ι → ℝ := fun x => if x = u then 1 else if x = v then -1 else 0
    have hfu : f u = 1 := if_pos rfl
    have hfv : f v = -1 := by simp [f, huv.symm]
    have hf0 : ∀ x, x ≠ u ∧ x ≠ v → f x = 0 := fun x hx => by simp [f, hx.1, hx.2]
    have hs1 : ∑ x ∈ T, f x = 0 := by
      rw [Finset.sum_eq_add_of_mem u v hu hv huv fun x _ hx => hf0 x hx, hfu, hfv]
      ring
    have hs2 : ∑ x ∈ T, f x ^ 2 = 2 := by
      rw [Finset.sum_eq_add_of_mem u v hu hv huv fun x _ hx => by rw [hf0 x hx]; ring, hfu,
        hfv]
      ring
    have hmean : ∑ x, (∑ y, cliqueWeight T c x y) * f x = 0 := by
      simp only [sum_cliqueWeight, ite_mul, zero_mul, Fintype.sum_ite_mem, ← Finset.mul_sum, hs1,
        mul_zero]
    have hnorm : ∑ x, (∑ y, cliqueWeight T c x y) * f x ^ 2 = c * ((#T : ℝ) - 1) * 2 := by
      simp only [sum_cliqueWeight, ite_mul, zero_mul, Fintype.sum_ite_mem, ← Finset.mul_sum, hs2]
    have h1 := h f hmean
    rw [sum_cliqueWeight_mul_mul_eq T c f hmean, hnorm] at h1
    -- `h1 : -(1 / (#T − 1)) · (c (#T − 1) 2) ≤ lam · (c (#T − 1) 2)`
    exact le_of_mul_le_mul_right h1 (by positivity)
  · intro h
    exact (walkSecondEigenvalueLE_cliqueWeight T c).mono
      (fun u v => by unfold cliqueWeight; split_ifs <;> linarith) h

/-! ### The complete complex: face counts and link graphs -/

/-- **Top faces through a set.** In the complete `d`-dimensional complex on `N = Fintype.card ι`
points, a set `s` with at most `d + 1` elements lies in exactly `C(N − #s, d + 1 − #s)` faces with
`d + 1` elements.

Both subtractions are natural-number subtractions; neither truncates, since `#s ≤ N` always and
`#s ≤ d + 1` by hypothesis. There is no hypothesis on `N` or `d`: for `N < d + 1` the binomial
coefficient is `0`, as it should be. The hypothesis on `s` is needed: a set with more than `d + 1`
elements lies in no such face, while the formula would give `C(N − #s, 0) = 1`. -/
theorem topDegree_complete_eq_choose {d : ℕ} {s : Finset ι} (hs : #s ≤ d + 1) :
    (complete ι d).topDegree d s = (Fintype.card ι - #s).choose (d + 1 - #s) := by
  rw [← card_univ, ← card_filter_powersetCard_subset s univ (d + 1) (subset_univ s) hs]
  unfold topDegree
  congr 1
  ext F
  simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ, mem_complete]
  constructor
  · rintro ⟨-, h, hsF⟩
    exact ⟨h, hsF⟩
  · rintro ⟨h, hsF⟩
    exact ⟨⟨card_pos.mp (by omega), h.le⟩, h, hsF⟩

/-- **The link graphs of the complete complex.** In the complete `d`-dimensional complex on
`N = Fintype.card ι` points, for a set `σ` with `#σ + 1 ≤ d`, distinct points `u, v` outside `σ`
are joined in the weighted graph of the link of `σ` with weight `C(N − #σ − 2, d − 1 − #σ)`, the
number of ways to complete `σ ∪ {u, v}` to a top face; all other weights are `0`.

The subtraction `d − 1 − #σ` does not truncate, by the hypothesis. `N − #σ − 2` truncates to `0`
exactly when at most one point lies outside `σ`, and then no pair `u, v` qualifies. There is no
hypothesis on `N`; for `N < d + 1` the link graph has no edges (the binomial coefficient is `0`,
or no pair qualifies). The hypothesis on `σ` is needed: for
`#σ ≥ d` the link has no edges (`linkWeight_eq_zero_of_le_card`), while the formula would give
`C(N − #σ − 2, 0) = 1`. -/
theorem linkWeight_complete_eq_choose {d : ℕ} {σ : Finset ι} (hσ : #σ + 1 ≤ d) (u v : ι) :
    (complete ι d).linkWeight d σ u v =
      if u ≠ v ∧ u ∉ σ ∧ v ∉ σ then ((Fintype.card ι - #σ - 2).choose (d - 1 - #σ) : ℝ)
      else 0 := by
  unfold linkWeight
  split_ifs with h
  · obtain ⟨huv, hu, hv⟩ := h
    have hcard : #(insert u (insert v σ)) = #σ + 2 := by
      rw [card_insert_of_notMem (by simp [huv, hu]), card_insert_of_notMem hv]
    rw [topDegree_complete_eq_choose (by omega), hcard]
    congr 2
    omega
  · rfl

/-- The link graph of `σ` in the complete complex is the complete graph on the points outside `σ`,
every edge with weight `C(N − #σ − 2, d − 1 − #σ)`, where `N = Fintype.card ι`. The degenerate
cases are those of `linkWeight_complete_eq_choose`. -/
theorem linkWeight_complete_eq_cliqueWeight {d : ℕ} {σ : Finset ι} (hσ : #σ + 1 ≤ d) :
    (complete ι d).linkWeight d σ =
      cliqueWeight σᶜ ((Fintype.card ι - #σ - 2).choose (d - 1 - #σ) : ℝ) := by
  funext u v
  rw [linkWeight_complete_eq_choose hσ, cliqueWeight]
  simp only [mem_compl]

/-- **The whole spectrum of a link of the complete complex.** In the complete `d`-dimensional
complex on `N = Fintype.card ι` points, let `#σ + 1 ≤ d`. For every `f` with degree-weighted mean
zero in the weighted graph `L` of the link of `σ`,
`Σ_{u,v} L(u,v) f(u) f(v) = −1/(N − 1 − #σ) · Σ_u deg(u) f(u)²`. So, for `N ≥ d + 1`, the random
walk on the link has eigenvalue `−1/(N − 1 − #σ)` on the whole mean-zero space.

The subtraction `N − 1 − #σ` is in `ℝ`. There is no hypothesis on `N`: for `N < d + 1` the link
graph has no edges and both sides are `0` (for `N = #σ + 1` the coefficient is the junk value
`−(1 / 0) = 0`). -/
theorem sum_linkWeight_complete_mul_mul_eq {d : ℕ} {σ : Finset ι} (hσ : #σ + 1 ≤ d)
    (f : ι → ℝ) (hf : ∑ u, (∑ v, (complete ι d).linkWeight d σ u v) * f u = 0) :
    ∑ u, ∑ v, (complete ι d).linkWeight d σ u v * f u * f v =
      -(1 / ((Fintype.card ι : ℝ) - 1 - #σ)) *
        ∑ u, (∑ v, (complete ι d).linkWeight d σ u v) * f u ^ 2 := by
  rw [linkWeight_complete_eq_cliqueWeight hσ] at hf ⊢
  rw [sum_cliqueWeight_mul_mul_eq _ _ f hf, card_compl, Nat.cast_sub (card_le_univ σ)]
  ring_nf

/-- **Exact link spectra of the complete complex.** In the complete `d`-dimensional complex on
`N = Fintype.card ι ≥ d + 1` points, for every set `σ` with `#σ + 1 ≤ d` (a face of dimension at
most `d − 2`, or `σ = ∅`), the random walk on the weighted graph of the link of `σ` has second
eigenvalue at most `μ` exactly when `−1/(N − 1 − #σ) ≤ μ`. The subtraction is in `ℝ`, and
`N − 1 − #σ ≥ 1`.

The hypothesis `d + 1 ≤ N` is needed: for `N ≤ d` every link graph has no edges, so every `μ` is
valid. -/
theorem walkSecondEigenvalueLE_linkWeight_complete_iff {d : ℕ} (hn : d + 1 ≤ Fintype.card ι)
    {σ : Finset ι} (hσ : #σ + 1 ≤ d) {μ : ℝ} :
    WalkSecondEigenvalueLE ((complete ι d).linkWeight d σ) μ ↔
      -(1 / ((Fintype.card ι : ℝ) - 1 - #σ)) ≤ μ := by
  have hT : 2 ≤ #σᶜ := by rw [card_compl]; omega
  have hc : (0 : ℝ) < ((Fintype.card ι - #σ - 2).choose (d - 1 - #σ) : ℕ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  rw [linkWeight_complete_eq_cliqueWeight hσ, walkSecondEigenvalueLE_cliqueWeight_iff hT hc,
    card_compl, Nat.cast_sub (card_le_univ σ)]
  ring_nf

/-! ### Trickling down is tight on the complete complex -/

/-- **The trickling-down recursion on the complete complex, as algebra.** Feeding the value
`lam = −1/(n − d)` into the trickling-down bound `lam / (1 − (d − 1 − k) · lam)` gives
`−1/(n − 1 − k)`.

All subtractions are in `ℝ`. The only hypothesis is `n ≠ d`, which makes `n − d` nonzero; for
`n = d` the left side is the junk value `0 / 1 = 0`. There is no hypothesis on `k`: when
`n − 1 − k = 0` both sides are `0` (each is a division by zero). -/
theorem trickling_down_bound_complete {n d k : ℕ} (hn : n ≠ d) :
    -(1 / ((n : ℝ) - d)) / (1 - ((d : ℝ) - 1 - k) * -(1 / ((n : ℝ) - d))) =
      -(1 / ((n : ℝ) - 1 - k)) := by
  have h1 : (n : ℝ) - d ≠ 0 := sub_ne_zero.mpr (Nat.cast_injective.ne hn)
  have e : 1 - ((d : ℝ) - 1 - k) * -(1 / ((n : ℝ) - d)) = ((n : ℝ) - 1 - k) / ((n : ℝ) - d) := by
    field_simp
    ring
  rw [e]
  rcases eq_or_ne ((n : ℝ) - 1 - k) 0 with h2 | h2
  · rw [h2]
    simp
  · field_simp

/-- **The trickling-down formula is exact on the complete complex.** In the complete
`d`-dimensional complex on `N = Fintype.card ι ≥ d + 1` points, let `lam = −1/(N − d)`, which is
the exact second eigenvalue of the links of the `(d − 2)`-dimensional faces (`#σ + 1 = d` in
`walkSecondEigenvalueLE_linkWeight_complete_iff`). For every `σ` with `#σ + 1 ≤ d`, the
trickling-down formula `lam / (1 − (d − 1 − #σ) · lam)` is the least valid bound for the link of
`σ`: a bound `μ` is valid exactly when it is at least the formula. All subtractions are in `ℝ`.

This is a statement about the formula; it does not apply `trickling_down`. For `d ≥ 2` the
complete complex satisfies the hypotheses of `trickling_down`, which then returns exactly this
bound (`trickling_down_complete`). For `d = 1` that theorem does not apply, and the statement holds
because the formula at `σ = ∅` is `lam / 1 = lam`. -/
theorem walkSecondEigenvalueLE_linkWeight_complete_iff_tricklingBound {d : ℕ}
    (hn : d + 1 ≤ Fintype.card ι) {σ : Finset ι} (hσ : #σ + 1 ≤ d) {μ : ℝ} :
    WalkSecondEigenvalueLE ((complete ι d).linkWeight d σ) μ ↔
      -(1 / ((Fintype.card ι : ℝ) - d)) /
          (1 - ((d : ℝ) - 1 - #σ) * -(1 / ((Fintype.card ι : ℝ) - d))) ≤ μ := by
  rw [trickling_down_bound_complete (by omega),
    walkSecondEigenvalueLE_linkWeight_complete_iff hn hσ]

/-- **Trickling down is tight along the whole chain of links.** Let `2 ≤ d`,
`N = Fintype.card ι ≥ d + 1` and `lam = −1/(N − d)`. The complete `d`-dimensional complex meets
every hypothesis of `trickling_down` with this `lam`: it is pure (`isPure_complete`); for
`#σ + 2 ≤ d` the link of `σ` is connected (`isConnected_link_complete`: its 1-skeleton is the
complete graph on the at least three points outside `σ`); `(d − 1) · lam < 1`, since `lam < 0`;
and the links of the `(d − 2)`-dimensional faces have second eigenvalue at most `lam`
(`walkSecondEigenvalueLE_linkWeight_complete_iff`). For every `σ` with `#σ + 1 ≤ d`, the bound
`lam / (1 − (d − 1 − #σ) · lam)` that `trickling_down` then returns for the link of `σ` is valid,
and no smaller bound is (`walkSecondEigenvalueLE_linkWeight_complete_iff_tricklingBound`). So
trickling down loses nothing on the complete complex, at any level. All subtractions are in `ℝ`.

The hypothesis `2 ≤ d` is that of `trickling_down`. The statement also holds for `d = 1`, where
the only link is the complex itself and the formula is `lam / 1 = lam`, by
`walkSecondEigenvalueLE_linkWeight_complete_iff_tricklingBound`; but `trickling_down` does not
apply there. The hypothesis `d + 1 ≤ N` is needed: for `N ≤ d` every link graph has no edges, so
every bound is valid and there is no least one. -/
theorem trickling_down_complete {d : ℕ} (hd : 2 ≤ d) (hn : d + 1 ≤ Fintype.card ι)
    {σ : Finset ι} (hσ : #σ + 1 ≤ d) :
    IsLeast {μ | WalkSecondEigenvalueLE ((complete ι d).linkWeight d σ) μ}
      (-(1 / ((Fintype.card ι : ℝ) - d)) /
        (1 - ((d : ℝ) - 1 - #σ) * -(1 / ((Fintype.card ι : ℝ) - d)))) := by
  refine ⟨?_, fun μ hμ =>
    (walkSecondEigenvalueLE_linkWeight_complete_iff_tricklingBound hn hσ).mp hμ⟩
  have hN : ((d + 1 : ℕ) : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  have hd' : ((2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
  push_cast at hN hd'
  have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) - d := by linarith
  have hlam : ((d : ℝ) - 1) * -(1 / ((Fintype.card ι : ℝ) - d)) < 1 := by
    have : ((d : ℝ) - 1) * -(1 / ((Fintype.card ι : ℝ) - d)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (neg_nonpos.mpr (by positivity))
    linarith
  have hconn : ∀ τ : Finset ι, (τ = ∅ ∨ τ ∈ complete ι d) → #τ + 2 ≤ d →
      ((complete ι d).link τ).IsConnected := by
    intro τ _ hτ
    obtain ⟨x, hx⟩ : ∃ x, x ∉ τ := by
      by_contra h
      simp only [not_exists, not_not] at h
      rw [eq_univ_of_forall h, card_univ] at hτ
      omega
    exact isConnected_link_complete (by omega) hx
  have hlocal : ∀ τ ∈ complete ι d, #τ + 1 = d →
      WalkSecondEigenvalueLE ((complete ι d).linkWeight d τ)
        (-(1 / ((Fintype.card ι : ℝ) - d))) := by
    intro τ _ hτ
    refine (walkSecondEigenvalueLE_linkWeight_complete_iff hn hτ.le).mpr (le_of_eq ?_)
    have : (#τ : ℝ) = d - 1 := by
      rw [← hτ]
      push_cast
      ring
    rw [this]
    ring_nf
  have hσ' : σ = ∅ ∨ σ ∈ complete ι d := by
    rcases σ.eq_empty_or_nonempty with h | h
    · exact Or.inl h
    · exact Or.inr (mem_complete.mpr ⟨h, by omega⟩)
  exact (complete ι d).trickling_down hd (isPure_complete hn) hconn hlam hlocal σ hσ' hσ

/-! ### The complete complex as a local spectral expander -/

/-- **The complete complex is a local spectral expander with the optimal parameter.** For
`1 ≤ d` and `N = Fintype.card ι ≥ d + 1`, the complete `d`-dimensional complex on `ι` is a
`lam`-local-spectral expander exactly when `−1/(N − 1) ≤ lam`. The subtraction is in `ℝ`.

The binding link is the complex itself (`σ = ∅`); the link of a face `σ` has the smaller value
`−1/(N − 1 − #σ)`. Both hypotheses are needed: no complex is a `0`-dimensional expander
(`not_isLocalSpectralExpander_zero`), and for `N ≤ d` the complete complex is either empty
(`N = 0`) or not pure of dimension `d`. For `N = d + 1` this is the simplex and the value is
`−1/d`, so `IsLocalSpectralExpander.neg_one_div_le` is sharp. -/
theorem isLocalSpectralExpander_complete_iff_le {d : ℕ} (hd : 1 ≤ d)
    (hn : d + 1 ≤ Fintype.card ι) {lam : ℝ} :
    (complete ι d).IsLocalSpectralExpander d lam ↔ -(1 / ((Fintype.card ι : ℝ) - 1)) ≤ lam := by
  constructor
  · intro h
    have h0 := h.walkSecondEigenvalueLE (σ := ∅) (Or.inl rfl) (by rw [card_empty]; omega)
    rw [walkSecondEigenvalueLE_linkWeight_complete_iff hn (by rw [card_empty]; omega),
      card_empty, Nat.cast_zero, sub_zero] at h0
    exact h0
  · intro h
    obtain ⟨x⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    refine ⟨hd, isPure_complete hn, ⟨{x}, mem_complete.mpr ⟨singleton_nonempty x, by
      rw [card_singleton]; omega⟩⟩, fun σ _ hσ => ?_⟩
    rw [walkSecondEigenvalueLE_linkWeight_complete_iff hn hσ]
    refine le_trans ?_ h
    have hk : ((#σ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hσ
    have hN : ((d + 1 : ℕ) : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
    push_cast at hk hN
    have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 - #σ := by linarith
    have hle : (Fintype.card ι : ℝ) - 1 - #σ ≤ (Fintype.card ι : ℝ) - 1 := by
      have : (0 : ℝ) ≤ #σ := Nat.cast_nonneg _
      linarith
    exact neg_le_neg (one_div_le_one_div_of_le hpos hle)

/-- All triangles on five points form a `lam`-local-spectral expander exactly when
`−1/4 ≤ lam`. This is the case `N = 5`, `d = 2` of `isLocalSpectralExpander_complete_iff_le`; it
contains `isLocalSpectralExpander_complete_fin5_two` and shows that its value `−1/4` is optimal. -/
theorem isLocalSpectralExpander_complete_fin5_two_iff {lam : ℝ} :
    (complete (Fin 5) 2).IsLocalSpectralExpander 2 lam ↔ -1 / 4 ≤ lam := by
  rw [isLocalSpectralExpander_complete_iff_le (by norm_num) (by simp), Fintype.card_fin]
  norm_num

/-! ### No complex on `N` vertices does better: the trace bound -/

omit [DecidableEq ι] in
/-- **The trace bound for a weighted graph.** Let `w` be symmetric and nonnegative, and let
`n = #{u | 0 < deg u}` be the number of vertices of positive degree, `deg u = Σ_v w(u, v)`. If
`n ≥ 2` and the random walk on `w` has second eigenvalue at most `lam`, then `−1/(n − 1) ≤ lam`.
The subtraction is in `ℝ`. Equality holds for the complete graph with constant weights
(`walkSecondEigenvalueLE_cliqueWeight`).

This is the variational form of the classical fact that the walk matrix of a loopless graph has
trace `0`. The proof takes `u₀` of least positive degree `a` and the test function
`S · 1_{u₀} − a`, where `S = Σ_u deg u ≥ n a`. Loops are allowed: they only help.

The hypothesis `n ≥ 2` is needed. For a single loop `n = 1`, every `lam` is valid, while the
junk value of the bound is `−(1 / 0) = 0`. -/
theorem neg_one_div_card_le_of_walkSecondEigenvalueLE {w : ι → ι → ℝ}
    (hsymm : ∀ u v, w u v = w v u) (hnn : ∀ u v, 0 ≤ w u v) {lam : ℝ}
    (h : WalkSecondEigenvalueLE w lam) (hP : 2 ≤ #{u | 0 < ∑ v, w u v}) :
    -(1 / ((#{u | 0 < ∑ v, w u v} : ℝ) - 1)) ≤ lam := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ι, P = ({u | 0 < ∑ v, w u v} : Finset ι) := ⟨_, rfl⟩
  rw [← hPdef] at hP ⊢
  have hdeg_nn : ∀ x, 0 ≤ ∑ v, w x v := fun x => Finset.sum_nonneg fun v _ => hnn x v
  obtain ⟨u₀, hu₀, hmin⟩ := P.exists_min_image (fun x => ∑ v, w x v) (card_pos.mp (by omega))
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ∑ v, w u₀ v := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ x, ∑ v, w x v := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [ha]
    rw [hPdef] at hu₀
    exact (mem_filter.mp hu₀).2
  -- `S` is the sum of the degrees over `P`, so `S ≥ n a`
  have hSP : S = ∑ x ∈ P, ∑ v, w x v := by
    rw [hS, hPdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rfl
    · exact le_antisymm (not_lt.mp hx) (hdeg_nn x)
  have hna : (#P : ℝ) * a ≤ S := by
    rw [hSP]
    have := Finset.card_nsmul_le_sum P (fun x => ∑ v, w x v) a fun x hx => ha ▸ hmin x hx
    rwa [nsmul_eq_mul] at this
  have hn2 : (2 : ℝ) ≤ #P := by exact_mod_cast hP
  have hSa : 0 < S - a := by nlinarith
  have hS0 : 0 < S := by linarith
  -- the test function `S · 1_{u₀} − a`
  let e : ι → ℝ := fun x => if x = u₀ then 1 else 0
  let f : ι → ℝ := fun x => S * e x - a
  have hsum_e : ∀ g : ι → ℝ, ∑ x, g x * e x = g u₀ := by
    intro g
    simp [e]
  have hcol : ∑ x, w x u₀ = a := by
    rw [ha]
    exact Finset.sum_congr rfl fun x _ => hsymm x u₀
  have hmean : ∑ x, (∑ v, w x v) * f x = 0 := by
    have hx : ∀ x, (∑ v, w x v) * f x = S * ((∑ v, w x v) * e x) - a * ∑ v, w x v := by
      intro x
      simp only [f]
      ring
    rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hsum_e (fun x => ∑ v, w x v), ← ha, ← hS]
    ring
  have hinner : ∀ x, ∑ y, w x y * f x * f y = f x * (S * w x u₀ - a * ∑ y, w x y) := by
    intro x
    have hy : ∀ y, w x y * f x * f y = f x * (S * (w x y * e y) - a * w x y) := by
      intro y
      simp only [f]
      ring
    rw [Finset.sum_congr rfl fun y _ => hy y, ← Finset.mul_sum, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hsum_e (fun y => w x y)]
  have hquad : ∑ x, ∑ y, w x y * f x * f y = S ^ 2 * w u₀ u₀ - S * a ^ 2 := by
    rw [Finset.sum_congr rfl fun x _ => hinner x]
    have hx : ∀ x, f x * (S * w x u₀ - a * ∑ y, w x y) =
        S * ((S * w x u₀ - a * ∑ y, w x y) * e x) - a * S * w x u₀ + a ^ 2 * ∑ y, w x y := by
      intro x
      simp only [f]
      ring
    rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      hsum_e (fun x => S * w x u₀ - a * ∑ y, w x y), hcol, ← ha, ← hS]
    ring
  have hnorm : ∑ x, (∑ v, w x v) * f x ^ 2 = S * a * (S - a) := by
    have hx : ∀ x, (∑ v, w x v) * f x ^ 2 =
        S * (S - 2 * a) * ((∑ v, w x v) * e x) + a ^ 2 * ∑ v, w x v := by
      intro x
      simp only [f, e]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hsum_e (fun x => ∑ v, w x v), ← ha, ← hS]
    ring
  have h1 := h f hmean
  rw [hquad, hnorm] at h1
  have hw0 : 0 ≤ w u₀ u₀ := hnn u₀ u₀
  -- dividing by `S a > 0`: `−a ≤ lam (S − a)`
  have h2 : -a ≤ lam * (S - a) := by
    have h3 : S * a * (-a) ≤ S * a * (lam * (S - a)) := by
      nlinarith [mul_nonneg (sq_nonneg S) hw0]
    exact le_of_mul_le_mul_left h3 (mul_pos hS0 ha0)
  -- and `(n − 1) a ≤ S − a` turns this into `−1 ≤ lam (n − 1)`
  have hn1 : (0 : ℝ) < (#P : ℝ) - 1 := by linarith
  have key : -1 ≤ lam * ((#P : ℝ) - 1) := by
    rcases le_or_gt 0 lam with hl | hl
    · nlinarith
    · have h4 : lam * (S - a) ≤ lam * (((#P : ℝ) - 1) * a) :=
        mul_le_mul_of_nonpos_left (by linarith) hl.le
      have h5 : a * (-1) ≤ a * (lam * ((#P : ℝ) - 1)) := by linarith
      exact le_of_mul_le_mul_left h5 ha0
  rw [show -(1 / ((#P : ℝ) - 1)) = -1 / ((#P : ℝ) - 1) by ring, div_le_iff₀ hn1]
  exact key

section Vertices

variable {K : PreAbstractSimplicialComplex ι} {d : ℕ} {m : Finset ι → ℝ} {lam : ℝ}

/-- For a top weight of a complex of dimension `d ≥ 1`, the vertices of positive degree in the
weighted underlying graph are exactly the vertices of the complex. -/
private theorem sum_linkWeightOf_empty_pos_iff_singleton_mem (hd : 1 ≤ d)
    (hm : K.IsTopWeight d m) {v : ι} : 0 < ∑ x, linkWeightOf m ∅ v x ↔ {v} ∈ K := by
  constructor
  · intro h
    have h' := K.mem_vertices_link_of_pos (hm.sum_linkWeightOf_pos_iff.mp h)
    rw [link_empty] at h'
    exact h'
  · intro hv
    obtain ⟨-, F, hF, hvF, hcard⟩ := hm.isPure {v} hv
    obtain ⟨x, hx, hxv⟩ := Finset.exists_mem_ne (by omega : 1 < #F) v
    have hpos : 0 < linkWeightOf m ∅ v x := by
      refine hm.linkWeightOf_pos_iff.mpr
        ⟨hxv.symm, notMem_empty v, notMem_empty x, F, hF, hcard, ?_⟩
      rw [insert_empty]
      exact insert_subset (singleton_subset_iff.mp hvF) (singleton_subset_iff.mpr hx)
    exact lt_of_lt_of_le hpos
      (single_le_sum (fun y _ => linkWeightOf_nonneg hm.nonneg ∅ v y) (mem_univ x))

omit [DecidableEq ι] in
/-- **A `d`-dimensional complex has at least `d + 1` vertices.** If `m` is a top weight of `K`, the
number `Nat.card K.vertices` of vertices of `K` is at least `d + 1`: the points of a top face are
vertices. This holds for `d = 0` as well. -/
theorem IsTopWeight.succ_le_natCard_vertices (hm : K.IsTopWeight d m) :
    d + 1 ≤ Nat.card K.vertices := by
  obtain ⟨F, hF, hcard, -⟩ := hm.exists_pos
  have hsub : (↑F : Set ι) ⊆ K.vertices := fun v hv =>
    K.mem_of_subset hF (singleton_subset_iff.mpr hv) (singleton_nonempty v)
  rw [← hcard, ← Set.ncard_coe_finset, Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-- **No weighted complex on `n` vertices beats the complete complex.** If `K`, with top weight
`m`, is a `lam`-local-spectral expander and has `n = Nat.card K.vertices` vertices, then
`−1/(n − 1) ≤ lam`; here `n ≥ d + 1 ≥ 2` (`IsTopWeight.succ_le_natCard_vertices`), so the
subtraction, which is in `ℝ`, is at least `1`. The complete complex on `n` points attains the bound
(`isLeast_setOf_isLocalSpectralExpanderOf`).

Only the complex itself (`σ = ∅`) is used: its weighted underlying graph has exactly the vertices
of `K` as vertices of positive degree, and the trace bound
`neg_one_div_card_le_of_walkSecondEigenvalueLE` applies. Since `n ≥ d + 1`, this improves
`IsLocalSpectralExpanderOf.neg_one_div_le` (`lam ≥ −1/d`) whenever `K` has more than `d + 1`
vertices. -/
theorem IsLocalSpectralExpanderOf.neg_one_div_natCard_vertices_le
    (h : K.IsLocalSpectralExpanderOf d m lam) :
    -(1 / ((Nat.card K.vertices : ℝ) - 1)) ≤ lam := by
  have hd := h.one_le
  have hm := h.isTopWeight
  have hV : K.vertices = ↑({v | 0 < ∑ x, linkWeightOf m ∅ v x} : Finset ι) := by
    ext v
    simp only [coe_filter, mem_univ, true_and]
    exact (sum_linkWeightOf_empty_pos_iff_singleton_mem hd hm).symm
  have hcard : Nat.card K.vertices = #({v | 0 < ∑ x, linkWeightOf m ∅ v x} : Finset ι) := by
    rw [hV, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have h2 : 2 ≤ Nat.card K.vertices := by
    have := hm.succ_le_natCard_vertices
    omega
  rw [hcard] at h2 ⊢
  exact neg_one_div_card_le_of_walkSecondEigenvalueLE (linkWeightOf_symm m ∅)
    (linkWeightOf_nonneg hm.nonneg ∅)
    (h.walkSecondEigenvalueLE (Or.inl rfl) (by rw [card_empty]; omega)) h2

/-- **No complex on `n` vertices beats the complete complex.** A `lam`-local-spectral expander
with `n = Nat.card K.vertices` vertices has `−1/(n − 1) ≤ lam`, where `n ≥ d + 1 ≥ 2` and the
subtraction is in `ℝ`. This is the uniform case of
`IsLocalSpectralExpanderOf.neg_one_div_natCard_vertices_le`. -/
theorem IsLocalSpectralExpander.neg_one_div_natCard_vertices_le
    (h : K.IsLocalSpectralExpander d lam) :
    -(1 / ((Nat.card K.vertices : ℝ) - 1)) ≤ lam :=
  ((K.isLocalSpectralExpander_iff_isLocalSpectralExpanderOf).mp h).neg_one_div_natCard_vertices_le

end Vertices

/-- **The best possible parameter on `N` vertices, weighted.** Let `N = Fintype.card ι`, `1 ≤ d` and
`d + 1 ≤ N`. Among all weighted `d`-dimensional local spectral expanders on `ι` in which every
point is a vertex, the least possible parameter is `−1/(N − 1)`, attained by the complete complex
with every top face of weight `1`. The subtraction is in `ℝ`.

Both hypotheses are needed for the value to be attained: there is no `0`-dimensional expander, and
a pure `d`-dimensional complex with a face has at least `d + 1` vertices. The lower bound itself
holds for every `d` and `N` (`IsLocalSpectralExpanderOf.neg_one_div_natCard_vertices_le`). -/
theorem isLeast_setOf_isLocalSpectralExpanderOf {d : ℕ} (hd : 1 ≤ d)
    (hn : d + 1 ≤ Fintype.card ι) :
    IsLeast {lam | ∃ (K : PreAbstractSimplicialComplex ι) (m : Finset ι → ℝ),
        (∀ v, {v} ∈ K) ∧ K.IsLocalSpectralExpanderOf d m lam}
      (-(1 / ((Fintype.card ι : ℝ) - 1))) := by
  refine ⟨⟨complete ι d, (complete ι d).uniformWeight d,
    fun v => mem_complete.mpr ⟨singleton_nonempty v, by rw [card_singleton]; omega⟩, ?_⟩, ?_⟩
  · rw [← isLocalSpectralExpander_iff_isLocalSpectralExpanderOf,
      isLocalSpectralExpander_complete_iff_le hd hn]
  · rintro lam ⟨K, m, hV, h⟩
    have hall : K.vertices = Set.univ := Set.eq_univ_of_forall hV
    have hb := h.neg_one_div_natCard_vertices_le
    rwa [hall, Nat.card_univ, Nat.card_eq_fintype_card] at hb

/-- **The best possible parameter on `N` vertices.** Let `N = Fintype.card ι`, `1 ≤ d` and
`d + 1 ≤ N`. Among all `d`-dimensional local spectral expanders on `ι` in which every point is a
vertex, the least possible parameter is `−1/(N − 1)`, attained by the complete complex
(`isLocalSpectralExpander_complete_iff_le`). The subtraction is in `ℝ`; the hypotheses are those
of `isLeast_setOf_isLocalSpectralExpanderOf`. -/
theorem isLeast_setOf_isLocalSpectralExpander {d : ℕ} (hd : 1 ≤ d)
    (hn : d + 1 ≤ Fintype.card ι) :
    IsLeast {lam | ∃ K : PreAbstractSimplicialComplex ι,
        (∀ v, {v} ∈ K) ∧ K.IsLocalSpectralExpander d lam}
      (-(1 / ((Fintype.card ι : ℝ) - 1))) := by
  refine ⟨⟨complete ι d,
    fun v => mem_complete.mpr ⟨singleton_nonempty v, by rw [card_singleton]; omega⟩,
    (isLocalSpectralExpander_complete_iff_le hd hn).mpr le_rfl⟩, ?_⟩
  rintro lam ⟨K, hV, h⟩
  have hall : K.vertices = Set.univ := Set.eq_univ_of_forall hV
  have hb := h.neg_one_div_natCard_vertices_le
  rwa [hall, Nat.card_univ, Nat.card_eq_fintype_card] at hb

/-! ### The simplex gap -/

section Simplex

variable {K : PreAbstractSimplicialComplex ι} {d : ℕ} {m : Finset ι → ℝ} {lam : ℝ}

/-- **Two top faces force `lam ≥ −1/(d + 1)`.** A weighted `lam`-local-spectral expander of
dimension `d` with two distinct `d`-dimensional faces has at least `d + 2` vertices, so
`−1/(d + 1) ≤ lam` by `IsLocalSpectralExpanderOf.neg_one_div_natCard_vertices_le`. The bound is
attained by the complete `d`-dimensional complex on `d + 2` points, the boundary of the
`(d + 1)`-simplex (`isLocalSpectralExpander_complete_iff_le`). -/
theorem IsLocalSpectralExpanderOf.neg_one_div_succ_le_of_ne
    (h : K.IsLocalSpectralExpanderOf d m lam) {F G : Finset ι} (hF : F ∈ K) (hG : G ∈ K)
    (hFc : #F = d + 1) (hGc : #G = d + 1) (hFG : F ≠ G) : -(1 / ((d : ℝ) + 1)) ≤ lam := by
  have hGF : ¬ G ⊆ F := fun hsub => hFG (eq_of_subset_of_card_le hsub (by omega)).symm
  obtain ⟨x, hxG, hxF⟩ := not_subset.mp hGF
  have hsub : (↑(insert x F) : Set ι) ⊆ K.vertices := by
    intro v hv
    rw [coe_insert, Set.mem_insert_iff] at hv
    rcases hv with rfl | hv
    · exact K.mem_of_subset hG (singleton_subset_iff.mpr hxG) (singleton_nonempty _)
    · exact K.mem_of_subset hF (singleton_subset_iff.mpr hv) (singleton_nonempty _)
  have hN : d + 2 ≤ Nat.card K.vertices := by
    rw [Nat.card_coe_set_eq]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, card_insert_of_notMem hxF, hFc] at this
    omega
  have hN' : ((d + 2 : ℕ) : ℝ) ≤ Nat.card K.vertices := by exact_mod_cast hN
  push_cast at hN'
  have hpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  exact le_trans (neg_le_neg (one_div_le_one_div_of_le hpos (by linarith)))
    h.neg_one_div_natCard_vertices_le

/-- With at most one top face, the weight of a set is the weight of that face if the set lies in
it, and `0` otherwise. -/
private theorem faceWeight_eq_of_unique_top (hm : K.IsTopWeight d m) {F : Finset ι} (hF : F ∈ K)
    (hFc : #F = d + 1) (hone : ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F = G)
    (s : Finset ι) : faceWeight m s = if s ⊆ F then m F else 0 := by
  have hz : ∀ G, G ≠ F → m G = 0 := fun G hGF => by
    by_contra h0
    obtain ⟨hG, hGc⟩ := hm.ne_zero_iff.mp h0
    exact hGF (hone G hG F hF hGc hFc)
  unfold faceWeight
  split_ifs with hs
  · exact Finset.sum_eq_single_of_mem F (by simp [hs]) fun G _ hGF => hz G hGF
  · refine Finset.sum_eq_zero fun G hG => hz G ?_
    rintro rfl
    exact hs (mem_filter.mp hG).2

/-- With at most one top face `F`, the link graph of `σ ⊆ F` is the complete graph on `F \ σ` with
every edge of weight `m F`. -/
private theorem linkWeightOf_eq_cliqueWeight_of_unique_top (hm : K.IsTopWeight d m)
    {F : Finset ι} (hF : F ∈ K) (hFc : #F = d + 1)
    (hone : ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F = G) {σ : Finset ι} (hσF : σ ⊆ F) :
    linkWeightOf m σ = cliqueWeight (F \ σ) (m F) := by
  funext u v
  unfold linkWeightOf cliqueWeight
  rw [faceWeight_eq_of_unique_top hm hF hFc hone]
  by_cases h : u ≠ v ∧ u ∉ σ ∧ v ∉ σ
  · rw [if_pos h]
    simp only [insert_subset_iff, mem_sdiff]
    refine if_congr ?_ rfl rfl
    tauto
  · rw [if_neg h, if_neg]
    rintro ⟨h1, h2, h3⟩
    exact h ⟨h1, (mem_sdiff.mp h2).2, (mem_sdiff.mp h3).2⟩

/-- **The link spectra of a weighted simplex.** If `m` is a top weight of `K` and `K` has at most
one `d`-dimensional face (so exactly one, `F`), then for `σ = ∅` or a face `σ` with `#σ + 1 ≤ d`,
the link graph of `σ` is the complete graph on `F \ σ` with constant weight, and its random walk
has second eigenvalue at most `μ` exactly when `−1/(d − #σ) ≤ μ`. The subtraction is in `ℝ`, and
`d − #σ ≥ 1`. -/
theorem walkSecondEigenvalueLE_linkWeightOf_iff_of_unique_top (hm : K.IsTopWeight d m)
    (hone : ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F = G) {σ : Finset ι}
    (hσ : σ = ∅ ∨ σ ∈ K) (hcard : #σ + 1 ≤ d) {μ : ℝ} :
    WalkSecondEigenvalueLE (linkWeightOf m σ) μ ↔ -(1 / ((d : ℝ) - #σ)) ≤ μ := by
  obtain ⟨F, hF, hFc, hmF⟩ := hm.exists_pos
  have hσF : σ ⊆ F := by
    rcases hσ with rfl | hσ
    · exact empty_subset F
    · obtain ⟨-, G, hG, hσG, hGc⟩ := hm.isPure σ hσ
      rwa [hone G hG F hF hGc hFc] at hσG
  have hT : #(F \ σ) = d + 1 - #σ := by rw [card_sdiff_of_subset hσF, hFc]
  rw [linkWeightOf_eq_cliqueWeight_of_unique_top hm hF hFc hone hσF,
    walkSecondEigenvalueLE_cliqueWeight_iff (by omega) hmF, hT, Nat.cast_sub (by omega)]
  push_cast
  ring_nf

/-- **A weighted simplex is a `lam`-local-spectral expander exactly when `−1/d ≤ lam`.** If
`1 ≤ d`, `m` is a top weight of `K`, and `K` has at most one `d`-dimensional face (so exactly
one), then `K` with the weight `m` is a `lam`-local-spectral expander exactly when `−1/d ≤ lam`,
whatever the value of `m` on that face. The hypothesis `1 ≤ d` is needed: there is no
`0`-dimensional expander (`not_isLocalSpectralExpanderOf_zero`). -/
theorem isLocalSpectralExpanderOf_iff_of_unique_top (hd : 1 ≤ d) (hm : K.IsTopWeight d m)
    (hone : ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F = G) :
    K.IsLocalSpectralExpanderOf d m lam ↔ -(1 / (d : ℝ)) ≤ lam := by
  refine ⟨fun h => h.neg_one_div_le, fun h => ⟨hd, hm, fun σ hσ hcard => ?_⟩⟩
  rw [walkSecondEigenvalueLE_linkWeightOf_iff_of_unique_top hm hone hσ hcard]
  refine le_trans ?_ h
  have hk : ((#σ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hcard
  push_cast at hk
  have hpos : (0 : ℝ) < d - #σ := by linarith
  have hσ0 : (0 : ℝ) ≤ #σ := Nat.cast_nonneg _
  exact neg_le_neg (one_div_le_one_div_of_le hpos (by linarith))

/-- **The simplex gap.** A weighted complex is a `lam`-local-spectral expander of dimension `d`
for some `lam < −1/(d + 1)` exactly when `1 ≤ d`, `m` is a top weight of `K`, and `K` has at most
one `d`-dimensional face (so exactly one: `K` is a single simplex with its faces). So the least
parameter of a weighted `d`-dimensional local spectral expander is either `−1/d`, for a single
simplex (`isLocalSpectralExpanderOf_iff_of_unique_top`), or at least `−1/(d + 1)`, for every other
complex (`IsLocalSpectralExpanderOf.neg_one_div_succ_le_of_ne`); nothing lies strictly between.

The condition `1 ≤ d` on the right is needed: for `d = 0` both sides are false, since there is no
`0`-dimensional expander (`not_isLocalSpectralExpanderOf_zero`). -/
theorem exists_lt_neg_one_div_succ_isLocalSpectralExpanderOf_iff :
    (∃ lam < -(1 / ((d : ℝ) + 1)), K.IsLocalSpectralExpanderOf d m lam) ↔
      1 ≤ d ∧ K.IsTopWeight d m ∧ ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F = G := by
  constructor
  · rintro ⟨lam, hlam, h⟩
    refine ⟨h.one_le, h.isTopWeight, fun F hF G hG hFc hGc => ?_⟩
    by_contra hFG
    exact absurd (h.neg_one_div_succ_le_of_ne hF hG hFc hGc hFG) (not_le.mpr hlam)
  · rintro ⟨hd, hm, hone⟩
    refine ⟨-(1 / (d : ℝ)), ?_, (isLocalSpectralExpanderOf_iff_of_unique_top hd hm hone).mpr le_rfl⟩
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have : 1 / ((d : ℝ) + 1) < 1 / d := one_div_lt_one_div_of_lt (by linarith) (by linarith)
    linarith

end Simplex

end PreAbstractSimplicialComplex
