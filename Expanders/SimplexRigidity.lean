/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.CompleteComplex

/-!
# The least possible second eigenvalue: the trace bound and rigidity of the simplex

The second eigenvalue of a random walk cannot be very negative. The eigenvalues of the walk on a
weighted graph whose vertices of positive degree form a set `P` of size `N` sum to the trace of
the walk, which is at least `0`, and the top eigenvalue is `1`; so the second eigenvalue is at
least `−1/(N − 1)`, with equality exactly for the uniformly weighted complete graph on `P`
(Chung, *Spectral Graph Theory*, Lemma 1.7). We prove this for `WalkSecondEigenvalueLE` directly,
with test functions in place of eigenvalues, and then apply it to simplicial complexes.

For a top weight `m` of a pure `d`-dimensional complex `K` and a face `σ` with `|σ| ≤ d − 1`
(or `σ = ∅`), the link of `σ` has at least `d + 1 − |σ|` vertices of positive degree, so its
second eigenvalue is at least `−1/(d − |σ|)`. The project already shows that `−1/(d − |σ|)` is
also a lower bound for *every* eigenvalue of the walk on the link (`link_walk_lower_bound`), so a
link whose second eigenvalue is `−1/(d − |σ|)` has every nontrivial eigenvalue equal to it. We
show this happens exactly when a single top face contains `σ`, and conclude that the complexes
that are `(−1/d)`-local spectral expanders are exactly the single `d`-simplices.

## Definitions
None: this file only proves theorems about `WalkSecondEigenvalueLE` (`Expanders/WeightedGraph`),
`linkWeightOf`, `IsTopWeight`, `IsLocalSpectralExpanderOf` (`Expanders/WeightedComplex`) and
`IsLocalSpectralExpander`, `topDegree`, `vertices` (`Expanders/HighDim`).

## Theorems
Weighted graphs (`w` symmetric and nonnegative; `deg u = Σ_v w u v`, `D = Σ_u deg u`, and `P` the
set of vertices of positive degree):
* `WalkSecondEigenvalueLE.mul_loop_sub_sq_le`, `WalkSecondEigenvalueLE.neg_deg_le`: testing the
  definition on `D · 1_u − deg u` gives `D · w u u − (deg u)² ≤ lam · deg u · (D − deg u)`, and so
  `−deg u ≤ lam · (D − deg u)` when `deg u > 0`. **Proved.**
* `WalkSecondEigenvalueLE.neg_one_div_card_le`: the **trace bound**: if `#P ≥ 2`, every `lam`
  with `WalkSecondEigenvalueLE w lam` is at least `−1/(#P − 1)`. **Proved.**
* `walkSecondEigenvalueLE_neg_one_div_card_iff`: **equality in the trace bound**:
  `WalkSecondEigenvalueLE w (−1/(#P − 1))` holds exactly when `w` has no loops and gives one
  positive weight `c` to every pair of distinct vertices of `P`. **Proved.**

Weighted complexes (`m ≥ 0` vanishing off the sets with `d + 1` elements, or a top weight):
* `le_card_pos_degree_linkWeightOf`, `IsTopWeight.le_card_pos_degree_link`: if a set of nonzero
  weight contains `σ` and `|σ| + 1 ≤ d`, the link of `σ` has at least `d + 1 − |σ|` vertices of
  positive degree. **Proved.**
* `neg_one_div_le_of_walkSecondEigenvalueLE_linkWeightOf`,
  `IsTopWeight.neg_one_div_le_of_walkSecondEigenvalueLE_link`: so the second eigenvalue of that
  link is at least `−1/(d − |σ|)`. **Proved.**
* `walkSecondEigenvalueLE_linkWeightOf_neg_one_div_iff`: **equality in the link bound**: for
  `|σ| + 1 ≤ d`, the link of `σ` has second eigenvalue at most `−1/(d − |σ|)` exactly when at most
  one set of nonzero weight contains `σ`. **Proved.**
* `sum_linkWeightOf_mul_mul_eq_neg_one_div_mul`,
  `IsTopWeight.sum_linkWeightOf_mul_mul_eq_neg_one_div_mul`: if at most one set of nonzero weight
  contains `σ`, the quadratic form of the link equals `−1/(d − |σ|)` times the degree-weighted
  norm on every `f` of mean zero. This is an identity, with no sign condition on `m` and any `σ`.
  When moreover `m ≥ 0`, `|σ| + 1 ≤ d` and some set of nonzero weight contains `σ`, it says that
  every nontrivial eigenvalue of the walk on the link is `−1/(d − |σ|)`. **Proved.**
* `IsTopWeight.forall_eq_of_subset_iff_topDegree_le_one`: for a top weight, "at most one set of
  nonzero weight contains `σ`" is `topDegree d σ ≤ 1`. **Proved.**
* `IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_neg_one_div_iff`: for `σ = ∅` or a face, with
  `|σ| + 1 ≤ d`, the link bound is attained exactly when `topDegree d σ = 1`. **Proved.**
* `IsPure.succ_le_ncard_vertices`: a pure `d`-dimensional complex with a face has at least
  `d + 1` vertices. **Proved.**
* `IsTopWeight.sum_linkWeightOf_empty_pos_iff`: for a top weight and `d ≥ 1`, the vertices of
  positive degree in the weighted underlying graph are exactly the vertices of `K`. **Proved.**
* `IsLocalSpectralExpanderOf.neg_one_div_ncard_vertices_le`,
  `IsLocalSpectralExpander.neg_one_div_ncard_vertices_le`: a `lam`-local spectral expander with
  `n = K.vertices.ncard` vertices has `lam ≥ −1/(n − 1)`. Since `n ≥ d + 1` this strengthens
  `IsLocalSpectralExpanderOf.neg_one_div_le`. (`Set.ncard` and `Nat.card` agree here:
  `Nat.card_coe_set_eq`.) **Proved.**
* `isLocalSpectralExpanderOf_neg_one_div_iff`, `isLocalSpectralExpander_neg_one_div_iff`:
  **rigidity of the simplex**: `K` (with the weight `m`) is a `(−1/d)`-local spectral expander
  exactly when `d ≥ 1`, (`m` is a top weight of `K`) and `K` consists of the nonempty subsets of a
  single set with `d + 1` elements. **Proved.**
* `isLocalSpectralExpander_complete_fin_succ_neg_one_div`: the `d`-simplex
  `complete (Fin (d + 1)) d` is a `(−1/d)`-local spectral expander, so the bound
  `IsLocalSpectralExpander.neg_one_div_le` is attained in every dimension `d ≥ 1`. **Proved.**

## References
* F. Chung, *Spectral Graph Theory*, CBMS Regional Conference Series in Mathematics 92, AMS,
  1997, Lemma 1.7: the trace bound and its equality case, for the normalised Laplacian.
* F. Bauer, J. Jost, *Bipartite and neighborhood graphs and the spectrum of the normalized graph
  Laplace operator*, Comm. Anal. Geom. 21 (2013), 787–845, arXiv:0910.3118, Section 2,
  (21)–(22): for a connected weighted graph on `N` vertices, loops allowed, the eigenvalues of the
  normalised Laplacian sum to `N − Σ_i w_ii/d_i`, so the smallest nonzero one is at most
  `(N − Σ_i w_ii/d_i)/(N − 1)`. In walk terms this is the trace bound with loops: the second
  eigenvalue of the walk is at least `−1/(N − 1)`, and loops only raise it.
* *Abelian Cayley high-dimensional expanders with polylogarithmic degree*, arXiv:2609.08937,
  Lemma 5.1: the lower bound `−1/(d − |σ|)` for every eigenvalue of a link
  (`link_walk_lower_bound`), through the sum-of-squares identity used here.
* T. Kaufman, I. Oppenheim, *High order random walks: beyond spectral gap*, arXiv:1707.02799, and
  V. L. Alev, L. C. Lau, *Improved analysis of higher order random walks*, arXiv:2001.02827: the
  same lower bound from the up-down walk being positive semidefinite.
* I. Oppenheim, *Local spectral expansion approach to high dimensional expanders part I*,
  Discrete Comput. Geom. 59 (2018), arXiv:1709.04431.

The equality cases for complexes (a link attains `−1/(d − |σ|)` exactly when one top face
contains `σ`; the `(−1/d)`-expanders are the simplices) are short consequences of these, and we
found them stated nowhere; they should be regarded as folklore.
-/

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Weighted graphs: the trace lower bound -/

section Graph

variable {w : ι → ι → ℝ} {lam : ℝ}

omit [DecidableEq ι] in
/-- **The bound at one vertex.** Let `w` be symmetric and nonnegative, `deg x = Σ_v w x v`, and
`D = Σ_x deg x`. If the random walk on `w` has second eigenvalue at most `lam`, then for every
vertex `u`,

  `D · w u u − (deg u)² ≤ lam · (deg u · (D − deg u))`.

This is the definition tested on `D · 1_u − deg u` (the indicator of `u`, scaled and shifted by
a constant), which has degree-weighted mean zero. No hypothesis on `u`: if `deg u = 0` then
`w u u = 0` and both sides vanish, and if `D = 0` every weight is `0`. -/
theorem WalkSecondEigenvalueLE.mul_loop_sub_sq_le (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (h : WalkSecondEigenvalueLE w lam) (u : ι) :
    (∑ x, ∑ v, w x v) * w u u - (∑ v, w u v) ^ 2 ≤
      lam * ((∑ v, w u v) * ((∑ x, ∑ v, w x v) - ∑ v, w u v)) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, a = ∑ v, w u v := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = ∑ x, ∑ v, w x v := ⟨_, rfl⟩
  rw [← ha, ← hD]
  have hdeg0 : ∀ x, 0 ≤ ∑ v, w x v := fun x => Finset.sum_nonneg fun v _ => hnn x v
  have hDa : a ≤ D := by
    rw [ha, hD]
    exact Finset.single_le_sum (f := fun x => ∑ v, w x v) (fun x _ => hdeg0 x) (Finset.mem_univ u)
  have ha0 : 0 ≤ a := ha ▸ hdeg0 u
  rcases (ha0.trans hDa).eq_or_lt with hD0 | hD0
  · -- `D = 0`: then `deg u = 0` and both sides vanish
    have ha' : a = 0 := le_antisymm (hD0 ▸ hDa) ha0
    rw [← hD0, ha']
    simp
  obtain ⟨e, he⟩ : ∃ e : ι → ℝ, e = fun x => if x = u then 1 else 0 := ⟨_, rfl⟩
  -- moments of the indicator `e` of `u`
  have s0 : ∑ x, (∑ v, w x v) * e x = a := by
    rw [ha, he]; simp
  have s1 : ∑ x, ∑ y, w x y * e x * e y = w u u := by
    rw [he]; simp
  have s2 : ∑ x, ∑ y, w x y * e x = a := by
    rw [← s0]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_mul]
  have s3 : ∑ x, ∑ y, w x y * e y = a := by
    rw [ha, he]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl fun x _ => hsymm x u
  have hee : ∀ x, e x ^ 2 = e x := fun x => by simp only [he]; split_ifs <;> norm_num
  -- the test function `D · e − a`
  have hmean : ∑ x, (∑ v, w x v) * (D * e x - a) = 0 := by
    have e1 : ∀ x, (∑ v, w x v) * (D * e x - a) = D * ((∑ v, w x v) * e x) - a * ∑ v, w x v :=
      fun x => by ring
    simp only [e1, Finset.sum_sub_distrib, ← Finset.mul_sum, s0, ← hD]
    ring
  have hquad : ∑ x, ∑ y, w x y * (D * e x - a) * (D * e y - a) = D ^ 2 * w u u - a ^ 2 * D := by
    have e1 : ∀ x y, w x y * (D * e x - a) * (D * e y - a) =
        D ^ 2 * (w x y * e x * e y) - a * D * (w x y * e x) - a * D * (w x y * e y)
          + a ^ 2 * w x y := fun x y => by ring
    simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, s1, s2, s3,
      ← hD]
    ring
  have hnorm : ∑ x, (∑ v, w x v) * (D * e x - a) ^ 2 = D ^ 2 * a - a ^ 2 * D := by
    have e1 : ∀ x, (∑ v, w x v) * (D * e x - a) ^ 2 =
        (D ^ 2 - 2 * a * D) * ((∑ v, w x v) * e x) + a ^ 2 * ∑ v, w x v := fun x => by
      have := hee x
      linear_combination (∑ v, w x v) * D ^ 2 * this
    simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, s0, ← hD]
    ring
  have h1 := h (fun x => D * e x - a) hmean
  rw [hquad, hnorm] at h1
  have h2 : D * (D * w u u - a ^ 2) ≤ D * (lam * (a * (D - a))) := by linarith
  exact le_of_mul_le_mul_left h2 hD0

omit [DecidableEq ι] in
/-- **The bound at a vertex of positive degree.** Let `w` be symmetric and nonnegative,
`deg x = Σ_v w x v` and `D = Σ_x deg x`. If the random walk on `w` has second eigenvalue at most
`lam` and `deg u > 0`, then `−deg u ≤ lam · (D − deg u)`. This drops the loop term from
`WalkSecondEigenvalueLE.mul_loop_sub_sq_le` and divides by `deg u`. -/
theorem WalkSecondEigenvalueLE.neg_deg_le (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (h : WalkSecondEigenvalueLE w lam) {u : ι}
    (hu : 0 < ∑ v, w u v) :
    -(∑ v, w u v) ≤ lam * ((∑ x, ∑ v, w x v) - ∑ v, w u v) := by
  classical
  have h1 := h.mul_loop_sub_sq_le hsymm hnn u
  have hD : 0 ≤ ∑ x, ∑ v, w x v :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun v _ => hnn x v
  have hloop := mul_nonneg hD (hnn u u)
  have h2 : (∑ v, w u v) * -(∑ v, w u v) ≤
      (∑ v, w u v) * (lam * ((∑ x, ∑ v, w x v) - ∑ v, w u v)) := by linarith
  exact le_of_mul_le_mul_left h2 hu

omit [DecidableEq ι] in
/-- **The trace bound.** Let `w` be symmetric and nonnegative, and let `N` be the number of
vertices of positive degree `deg u = Σ_v w u v`. If `N ≥ 2` and the random walk on `w` has second
eigenvalue at most `lam`, then `lam ≥ −1/(N − 1)`. (Spectrally: the eigenvalues of the walk on the
`N` vertices of positive degree sum to its trace, which is `≥ 0`, and the top one is `1`. The proof
here sums `WalkSecondEigenvalueLE.neg_deg_le` over those vertices instead.) The bound is attained
exactly by the uniformly weighted complete graph on those `N` vertices
(`walkSecondEigenvalueLE_neg_one_div_card_iff`).

Vertices of degree `0` do not count towards `N` (the definition of `WalkSecondEigenvalueLE`
ignores them). The hypothesis `N ≥ 2` cannot be dropped: if `N = 0` (no edges) or `N = 1` (a single
vertex carrying a loop) the bound `WalkSecondEigenvalueLE w lam` holds for every `lam`, while in
Lean the right-hand side `−(1/(N − 1))` would be `1` for `N = 0` and `−(1/0) = 0` for `N = 1`. -/
theorem WalkSecondEigenvalueLE.neg_one_div_card_le (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (h : WalkSecondEigenvalueLE w lam)
    (hN : 2 ≤ #{u | 0 < ∑ v, w u v}) :
    -(1 / ((#{u | 0 < ∑ v, w u v} : ℝ) - 1)) ≤ lam := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Finset ι, P = ({u | 0 < ∑ v, w u v} : Finset ι) := ⟨_, rfl⟩
  rw [← hP] at hN ⊢
  obtain ⟨D, hD⟩ : ∃ D, D = ∑ x, ∑ v, w x v := ⟨_, rfl⟩
  have hdeg0 : ∀ x, 0 ≤ ∑ v, w x v := fun x => Finset.sum_nonneg fun v _ => hnn x v
  have hDP : ∑ x ∈ P, ∑ v, w x v = D := by
    rw [hP, hD]
    exact Finset.sum_filter_of_ne fun x _ hx => lt_of_le_of_ne (hdeg0 x) (Ne.symm hx)
  obtain ⟨u0, hu0⟩ : P.Nonempty := Finset.card_pos.mp (by omega)
  have hu0' : 0 < ∑ v, w u0 v := by rw [hP] at hu0; exact (Finset.mem_filter.mp hu0).2
  have hD0 : 0 < D := by
    rw [hD]
    exact lt_of_lt_of_le hu0'
      (Finset.single_le_sum (f := fun x => ∑ v, w x v) (fun x _ => hdeg0 x) (Finset.mem_univ u0))
  have key : ∀ x ∈ P, -(∑ v, w x v) ≤ lam * (D - ∑ v, w x v) := by
    intro x hx
    rw [hP] at hx
    rw [hD]
    exact h.neg_deg_le hsymm hnn (Finset.mem_filter.mp hx).2
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_neg_distrib, hDP, ← Finset.mul_sum, Finset.sum_sub_distrib, hDP,
    Finset.sum_const, nsmul_eq_mul] at hsum
  have hN' : (1 : ℝ) ≤ (#P : ℝ) - 1 := by
    have : (2 : ℝ) ≤ #P := by exact_mod_cast hN
    linarith
  have h1 : -1 ≤ lam * ((#P : ℝ) - 1) := by
    have h2 : D * (-1) ≤ D * (lam * ((#P : ℝ) - 1)) := by linarith
    exact le_of_mul_le_mul_left h2 hD0
  rw [← neg_div, div_le_iff₀ (by linarith)]
  exact h1

/-- The sum of `c · f u · f v` over the ordered pairs of distinct elements of `T`. -/
private theorem sum_sum_ite_ne_mul_const (T : Finset ι) (f : ι → ℝ) (c : ℝ) :
    ∑ u, ∑ v, (if u ≠ v ∧ u ∈ T ∧ v ∈ T then c else 0) * f u * f v =
      c * ((∑ v ∈ T, f v) ^ 2 - ∑ v ∈ T, f v ^ 2) := by
  have h : ∀ u, ∑ v, (if u ≠ v ∧ u ∈ T ∧ v ∈ T then c else 0) * f u * f v =
      if u ∈ T then c * (f u * (∑ v ∈ T, f v) - f u ^ 2) else 0 := by
    intro u
    by_cases hu : u ∈ T
    · have e : ∀ v, (if u ≠ v ∧ u ∈ T ∧ v ∈ T then c else 0) * f u * f v =
          if v ∈ T.erase u then c * (f u * f v) else 0 := by
        intro v
        by_cases hv : v ∈ T.erase u
        · rw [if_pos hv, if_pos ⟨(Finset.mem_erase.mp hv).1.symm, hu, (Finset.mem_erase.mp hv).2⟩]
          ring
        · rw [if_neg hv, if_neg]
          · ring
          · rintro ⟨h1, -, h3⟩
            exact hv (Finset.mem_erase.mpr ⟨Ne.symm h1, h3⟩)
      rw [if_pos hu, Finset.sum_congr rfl fun v _ => e v, Fintype.sum_ite_mem,
        ← Finset.mul_sum, Finset.sum_erase_eq_sub hu, Finset.mul_sum]
      ring
    · rw [if_neg hu]
      exact Finset.sum_eq_zero fun v _ => by rw [if_neg fun h => hu h.2.1]; ring
  rw [Finset.sum_congr rfl fun u _ => h u, Fintype.sum_ite_mem, ← Finset.mul_sum,
    Finset.sum_sub_distrib, ← Finset.sum_mul, sq]

omit [DecidableEq ι] in
/-- **Equality in the trace bound.** Let `w` be symmetric and nonnegative, and let `N ≥ 2` be the
number of vertices of positive degree `deg u = Σ_v w u v`. The random walk on `w` has second
eigenvalue at most `−1/(N − 1)` (the least value allowed by
`WalkSecondEigenvalueLE.neg_one_div_card_le`) exactly when `w` has no loops and there is a
`c > 0` such that every two distinct vertices of positive degree are joined with weight `c`: the
weighted graph is the complete graph on its vertices of positive degree, uniformly weighted.

A loop anywhere makes the bound strict, so `w u u = 0` is part of the conclusion rather than a
hypothesis. (Loops at vertices of degree `0` are excluded automatically, since `w u u ≤ deg u`.)
Vertices of degree `0` are otherwise unconstrained: all their weights are `0`. The hypothesis
`N ≥ 2` is needed as in the trace bound: for `N = 1` the weighted graph is a single loop, which
satisfies `WalkSecondEigenvalueLE w 0` (in Lean `−(1/(1 − 1)) = 0`) but has a loop. -/
theorem walkSecondEigenvalueLE_neg_one_div_card_iff (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) (hN : 2 ≤ #{u | 0 < ∑ v, w u v}) :
    WalkSecondEigenvalueLE w (-(1 / ((#{u | 0 < ∑ v, w u v} : ℝ) - 1))) ↔
      (∀ u, w u u = 0) ∧
        ∃ c > 0, ∀ u v, u ≠ v → 0 < ∑ x, w u x → 0 < ∑ x, w v x → w u v = c := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Finset ι, P = ({u | 0 < ∑ v, w u v} : Finset ι) := ⟨_, rfl⟩
  rw [← hP] at hN ⊢
  have hmemP : ∀ x, x ∈ P ↔ 0 < ∑ v, w x v := fun x => by rw [hP]; simp
  have hdeg0 : ∀ x, 0 ≤ ∑ v, w x v := fun x => Finset.sum_nonneg fun v _ => hnn x v
  have hzero : ∀ x, x ∉ P → ∀ y, w x y = 0 := by
    intro x hx y
    have h0 : ∑ v, w x v = 0 :=
      le_antisymm (not_lt.mp fun h => hx ((hmemP x).mpr h)) (hdeg0 x)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun v _ => hnn x v).mp h0 y (Finset.mem_univ y)
  -- without loops, the degree of `u` is a sum over the other vertices of positive degree
  have hdegE : (∀ u, w u u = 0) → ∀ u, ∑ v, w u v = ∑ v ∈ P.erase u, w u v := by
    intro hdiag u
    refine (Finset.sum_subset (Finset.subset_univ (P.erase u)) fun v _ hv => ?_).symm
    rw [Finset.mem_erase, not_and_or] at hv
    rcases hv with h | h
    · rw [not_not] at h
      rw [h, hdiag]
    · rw [hsymm]
      exact hzero v h u
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = #P := ⟨_, rfl⟩
  rw [← hNdef]
  have hN2 : (2 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have hcardE : ∀ u ∈ P, ((#(P.erase u) : ℕ) : ℝ) = N - 1 := by
    intro u hu
    rw [Finset.card_erase_of_mem hu, Nat.cast_sub (by omega), hNdef, Nat.cast_one]
  constructor
  · intro h
    obtain ⟨D, hD⟩ : ∃ D, D = ∑ x, ∑ v, w x v := ⟨_, rfl⟩
    have hD0' : 0 ≤ D := hD ▸ Finset.sum_nonneg fun x _ => hdeg0 x
    have hDP : ∑ x ∈ P, ∑ v, w x v = D := by
      rw [hP, hD]
      exact Finset.sum_filter_of_ne fun x _ hx => lt_of_le_of_ne (hdeg0 x) (Ne.symm hx)
    -- step 0: the bound at each vertex, `(N − 1) · D · w u u + deg u · D ≤ N · (deg u)²`
    have hvert : ∀ u, (N - 1) * (D * w u u) + (∑ v, w u v) * D ≤ N * (∑ v, w u v) ^ 2 := by
      intro u
      have h1 := h.mul_loop_sub_sq_le hsymm hnn u
      rw [← hD] at h1
      have e : -(1 / (N - 1)) * ((∑ v, w u v) * (D - ∑ v, w u v)) =
          -((∑ v, w u v) * (D - ∑ v, w u v)) / (N - 1) := by ring
      rw [e, le_div_iff₀ hN1] at h1
      linarith
    -- step 1: `D ≤ N · deg u` on `P`
    have hstep1 : ∀ u ∈ P, D ≤ N * ∑ v, w u v := by
      intro u hu
      have h1 := hvert u
      have hloop : 0 ≤ (N - 1) * (D * w u u) := mul_nonneg hN1.le (mul_nonneg hD0' (hnn u u))
      have ha := (hmemP u).mp hu
      have h2 : (∑ v, w u v) * D ≤ (∑ v, w u v) * (N * ∑ v, w u v) := by linarith
      exact le_of_mul_le_mul_left h2 ha
    -- step 2: the degrees are all `D / N`
    have hsum0 : ∑ u ∈ P, (N * ∑ v, w u v - D) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hDP, Finset.sum_const, nsmul_eq_mul, ← hNdef]
      ring
    have hdegeq : ∀ u ∈ P, N * ∑ v, w u v = D := by
      intro u hu
      have := (Finset.sum_eq_zero_iff_of_nonneg fun x hx => sub_nonneg.mpr (hstep1 x hx)).mp
        hsum0 u hu
      linarith
    have hD0 : 0 < D := by
      obtain ⟨u0, hu0⟩ : P.Nonempty := Finset.card_pos.mp (by omega)
      have := hdegeq u0 hu0
      have := (hmemP u0).mp hu0
      nlinarith
    -- step 3: there are no loops
    have hdiag : ∀ u, w u u = 0 := by
      intro u
      by_cases hu : u ∈ P
      · have h1 := hvert u
        have h2 := hdegeq u hu
        have h3 : (N - 1) * (D * w u u) ≤ 0 := by
          have e : N * (∑ v, w u v) ^ 2 = (∑ v, w u v) * D := by rw [← h2]; ring
          linarith
        have h4 : 0 < (N - 1) * D := mul_pos hN1 hD0
        have h5 : (N - 1) * D * w u u ≤ (N - 1) * D * 0 := by rw [mul_zero, mul_assoc]; exact h3
        exact le_antisymm (le_of_mul_le_mul_left h5 h4) (hnn u u)
      · exact hzero u hu u
    have hdegE' := hdegE hdiag
    -- step 4: two-point test functions bound every weight below
    have hlow : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → D / (N * (N - 1)) ≤ w u v := by
      intro u hu v hv huv
      obtain ⟨a, ha⟩ : ∃ a, a = ∑ x, w u x := ⟨_, rfl⟩
      obtain ⟨b, hb⟩ : ∃ b, b = ∑ x, w v x := ⟨_, rfl⟩
      have hNa : N * a = D := ha ▸ hdegeq u hu
      have hNb : N * b = D := hb ▸ hdegeq v hv
      have ha0 : 0 < a := ha ▸ (hmemP u).mp hu
      have hab : a = b := by
        have : N * a = N * b := hNa.trans hNb.symm
        exact mul_left_cancel₀ (by linarith) this
      obtain ⟨eu, heu⟩ : ∃ e : ι → ℝ, e = fun x => if x = u then 1 else 0 := ⟨_, rfl⟩
      obtain ⟨ev, hev⟩ : ∃ e : ι → ℝ, e = fun x => if x = v then 1 else 0 := ⟨_, rfl⟩
      have m_u : ∑ x, (∑ y, w x y) * eu x = a := by rw [ha, heu]; simp
      have m_v : ∑ x, (∑ y, w x y) * ev x = b := by rw [hb, hev]; simp
      have hmean : ∑ x, (∑ y, w x y) * (b * eu x - a * ev x) = 0 := by
        have e1 : ∀ x, (∑ y, w x y) * (b * eu x - a * ev x) =
            b * ((∑ y, w x y) * eu x) - a * ((∑ y, w x y) * ev x) := fun x => by ring
        simp only [e1, Finset.sum_sub_distrib, ← Finset.mul_sum, m_u, m_v]
        ring
      have q : ∀ p r : ι, ∑ x, ∑ y, w x y * (if x = p then 1 else 0) * (if y = r then 1 else 0) =
          w p r := fun p r => by simp
      have hquad : ∑ x, ∑ y, w x y * (b * eu x - a * ev x) * (b * eu y - a * ev y) =
          -(2 * a * b * w u v) := by
        have e1 : ∀ x y, w x y * (b * eu x - a * ev x) * (b * eu y - a * ev y) =
            b ^ 2 * (w x y * eu x * eu y) - a * b * (w x y * eu x * ev y)
              - a * b * (w x y * ev x * eu y) + a ^ 2 * (w x y * ev x * ev y) :=
          fun x y => by ring
        simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        rw [heu, hev, q, q, q, q, hdiag, hdiag, hsymm v u]
        ring
      have hnorm : ∑ x, (∑ y, w x y) * (b * eu x - a * ev x) ^ 2 = a * b ^ 2 + b * a ^ 2 := by
        have e1 : ∀ x, (∑ y, w x y) * (b * eu x - a * ev x) ^ 2 =
            b ^ 2 * ((∑ y, w x y) * eu x) + a ^ 2 * ((∑ y, w x y) * ev x) := by
          intro x
          rw [heu, hev]
          by_cases hxu : x = u
          · subst hxu; simp [huv, mul_comm]
          · by_cases hxv : x = v
            · subst hxv; simp [hxu, mul_comm]
            · simp [hxu, hxv]
        simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, m_u, m_v]
        ring
      have h1 := h (fun x => b * eu x - a * ev x) hmean
      rw [hquad, hnorm, ← hab] at h1
      have h2 : -(1 / (N - 1)) * (a * a ^ 2 + a * a ^ 2) = -(2 * a ^ 3) / (N - 1) := by ring
      rw [h2, le_div_iff₀ hN1] at h1
      have h3 : a ^ 2 * a ≤ a ^ 2 * (w u v * (N - 1)) := by nlinarith
      have h4 := le_of_mul_le_mul_left h3 (by positivity)
      rw [div_le_iff₀ (by positivity), ← hNa]
      nlinarith
    -- step 5: the weights at `u` sum to `deg u`, so every lower bound is attained
    refine ⟨hdiag, D / (N * (N - 1)), by positivity, fun u v huv hu hv => ?_⟩
    have hu' := (hmemP u).mpr hu
    have hv' := (hmemP v).mpr hv
    have hs : ∑ y ∈ P.erase u, (w u y - D / (N * (N - 1))) = 0 := by
      rw [Finset.sum_sub_distrib, ← hdegE', Finset.sum_const, nsmul_eq_mul, hcardE u hu']
      have := hdegeq u hu'
      field_simp
      linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg fun y hy =>
      sub_nonneg.mpr (hlow u hu' y (Finset.mem_erase.mp hy).2 (Finset.mem_erase.mp hy).1.symm)).mp
      hs v (Finset.mem_erase.mpr ⟨huv.symm, hv'⟩)
    linarith
  · rintro ⟨hdiag, c, hc, hcw⟩ f hf
    have hdegE' := hdegE hdiag
    have hw : ∀ x y, w x y = if x ≠ y ∧ x ∈ P ∧ y ∈ P then c else 0 := by
      intro x y
      by_cases hxy : x = y
      · rw [if_neg fun h => h.1 hxy, hxy, hdiag]
      by_cases hx : x ∈ P
      · by_cases hy : y ∈ P
        · rw [if_pos ⟨hxy, hx, hy⟩]
          exact hcw x y hxy ((hmemP x).mp hx) ((hmemP y).mp hy)
        · rw [if_neg fun h => hy h.2.2, hsymm]
          exact hzero y hy x
      · rw [if_neg fun h => hx h.2.1]
        exact hzero x hx y
    have hdegc : ∀ x, ∑ y, w x y = if x ∈ P then c * (N - 1) else 0 := by
      intro x
      split_ifs with hx
      · rw [hdegE' x, Finset.sum_congr rfl fun y hy => (hw x y).trans
          (if_pos ⟨(Finset.mem_erase.mp hy).1.symm, hx, (Finset.mem_erase.mp hy).2⟩),
          Finset.sum_const, nsmul_eq_mul, hcardE x hx]
        ring
      · exact Finset.sum_eq_zero fun y _ => hzero x hx y
    have hmeanP : ∑ x, (∑ y, w x y) * f x = c * (N - 1) * ∑ x ∈ P, f x := by
      simp only [hdegc, ite_mul, zero_mul]
      rw [Fintype.sum_ite_mem, Finset.mul_sum]
    have hnormP : ∑ x, (∑ y, w x y) * f x ^ 2 = c * (N - 1) * ∑ x ∈ P, f x ^ 2 := by
      simp only [hdegc, ite_mul, zero_mul]
      rw [Fintype.sum_ite_mem, Finset.mul_sum]
    have hfP : ∑ x ∈ P, f x = 0 := by
      rw [hmeanP] at hf
      exact (mul_eq_zero.mp hf).resolve_left (by positivity)
    have hQ : ∑ x, ∑ y, w x y * f x * f y = c * ((∑ x ∈ P, f x) ^ 2 - ∑ x ∈ P, f x ^ 2) := by
      simp only [hw]
      exact sum_sum_ite_ne_mul_const P f c
    rw [hQ, hnormP, hfP]
    apply le_of_eq
    field_simp
    ring

end Graph

namespace PreAbstractSimplicialComplex

/-! ### The links of a weighted complex: the lower bound `−1/(d − |σ|)` is attained only by a
simplex -/

section Link

variable {m : Finset ι → ℝ} {d : ℕ} {lam : ℝ}

omit [Fintype ι] [DecidableEq ι] in
/-- `0 < d − |σ|` as a real number. -/
private theorem sub_card_pos {σ : Finset ι} (hσd : #σ + 1 ≤ d) : (0 : ℝ) < (d : ℝ) - #σ := by
  have h : ((#σ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hσd
  push_cast at h
  linarith

/-- A vertex `u ∈ F \ σ` of a set `F ⊇ σ` of nonzero weight has positive degree in the link of
`σ`. -/
private theorem sum_linkWeightOf_pos_of_mem_sdiff (hnn : ∀ F, 0 ≤ m F)
    (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {σ F : Finset ι} (hσF : σ ⊆ F) (hF : m F ≠ 0)
    (hσd : #σ + 1 ≤ d) {u : ι} (hu : u ∈ F \ σ) : 0 < ∑ v, linkWeightOf m σ u v := by
  rw [sum_linkWeightOf hcard, if_neg (Finset.mem_sdiff.mp hu).2]
  refine mul_pos (sub_card_pos hσd) ?_
  rw [faceWeight_pos_iff hnn]
  exact ⟨F, Finset.insert_subset (Finset.mem_sdiff.mp hu).1 hσF,
    lt_of_le_of_ne (hnn F) (Ne.symm hF)⟩

/-- **A link has at least `d + 1 − |σ|` vertices of positive degree.** Let `m ≥ 0` vanish off the
sets with `d + 1` elements, and let `σ` lie in a set `F` with `m F ≠ 0`. If `|σ| + 1 ≤ d`, every
vertex of `F \ σ` has positive degree in the weighted graph of the link of `σ`, so at least
`d + 1 − |σ|` vertices do.

The natural-number subtraction `d + 1 − |σ|` is a genuine difference, since `|σ| ≤ d`. The
hypothesis `|σ| + 1 ≤ d` is needed: for `|σ| = d` the link has no edges at all
(`linkWeightOf_eq_zero_of_le_card`), so no vertex has positive degree, while `d + 1 − |σ| = 1`. -/
theorem le_card_pos_degree_linkWeightOf (hnn : ∀ F, 0 ≤ m F)
    (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {σ F : Finset ι} (hσF : σ ⊆ F) (hF : m F ≠ 0)
    (hσd : #σ + 1 ≤ d) : d + 1 - #σ ≤ #{u | 0 < ∑ v, linkWeightOf m σ u v} := by
  have hsub : F \ σ ⊆ ({u | 0 < ∑ v, linkWeightOf m σ u v} : Finset ι) := fun u hu =>
    Finset.mem_filter.mpr
      ⟨Finset.mem_univ u, sum_linkWeightOf_pos_of_mem_sdiff hnn hcard hσF hF hσd hu⟩
  have := Finset.card_le_card hsub
  rwa [Finset.card_sdiff_of_subset hσF, hcard F hF] at this

/-- **The second eigenvalue of a link is at least `−1/(d − |σ|)`.** Let `m ≥ 0` vanish off the
sets with `d + 1` elements, let `σ` lie in a set of nonzero weight, and let `|σ| + 1 ≤ d`. If the
random walk on the link of `σ` has second eigenvalue at most `lam`, then `lam ≥ −1/(d − |σ|)`.
This is the trace bound `WalkSecondEigenvalueLE.neg_one_div_card_le` applied with the
`d + 1 − |σ| ≥ 2` vertices of positive degree from `le_card_pos_degree_linkWeightOf`.

Together with `link_walk_lower_bound` (no eigenvalue of the link is below `−1/(d − |σ|)`), this
says that the bound `−1/(d − |σ|)` can only be attained with every nontrivial eigenvalue equal to
it; `walkSecondEigenvalueLE_linkWeightOf_neg_one_div_iff` says when. The hypotheses are needed:
if no set of nonzero weight contains `σ`, the link has no edges and every `lam` is allowed
(`walkSecondEigenvalueLE_of_forall_eq_zero`), and so it is for `|σ| = d`, where in Lean the bound
`−(1/(d − |σ|)) = −(1/0)` would be `0`. -/
theorem neg_one_div_le_of_walkSecondEigenvalueLE_linkWeightOf (hnn : ∀ F, 0 ≤ m F)
    (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {σ F : Finset ι} (hσF : σ ⊆ F) (hF : m F ≠ 0)
    (hσd : #σ + 1 ≤ d) (h : WalkSecondEigenvalueLE (linkWeightOf m σ) lam) :
    -(1 / ((d : ℝ) - #σ)) ≤ lam := by
  have hN := le_card_pos_degree_linkWeightOf hnn hcard hσF hF hσd
  have h2 : 2 ≤ #({u | 0 < ∑ v, linkWeightOf m σ u v} : Finset ι) := by omega
  have ha := h.neg_one_div_card_le (linkWeightOf_symm m σ) (linkWeightOf_nonneg hnn σ) h2
  refine le_trans ?_ ha
  have hle : (d : ℝ) - #σ ≤ (#({u | 0 < ∑ v, linkWeightOf m σ u v} : Finset ι) : ℝ) - 1 := by
    have h3 : ((d + 1 - #σ : ℕ) : ℝ) ≤
        (#({u | 0 < ∑ v, linkWeightOf m σ u v} : Finset ι) : ℝ) := by
      exact_mod_cast hN
    rw [Nat.cast_sub (by omega)] at h3
    push_cast at h3
    linarith
  exact neg_le_neg (one_div_le_one_div_of_le (sub_card_pos hσd) hle)

/-- The degree-weighted mean of `f` on the link of `σ`, face by face. -/
private theorem sum_linkWeightOf_mul_eq_faces (hcard : ∀ F, m F ≠ 0 → #F = d + 1)
    (σ : Finset ι) (f : ι → ℝ) :
    ∑ u, (∑ v, linkWeightOf m σ u v) * f u =
      ((d : ℝ) - #σ) * ∑ F with σ ⊆ F, m F * ∑ v ∈ F \ σ, f v := by
  rw [← sum_faceWeight_insert_mul m σ f, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [sum_linkWeightOf hcard]
  split_ifs <;> ring

/-- The quadratic form of the link of `σ` plus `1/(d − |σ|)` times its degree-weighted norm is a
sum of squares, face by face. -/
private theorem sum_linkWeightOf_mul_mul_add_one_div (hcard : ∀ F, m F ≠ 0 → #F = d + 1)
    {σ : Finset ι} (h0 : (d : ℝ) - #σ ≠ 0) (f : ι → ℝ) :
    ∑ u, ∑ v, linkWeightOf m σ u v * f u * f v +
        1 / ((d : ℝ) - #σ) * ∑ u, (∑ v, linkWeightOf m σ u v) * f u ^ 2 =
      ∑ F with σ ⊆ F, m F * (∑ v ∈ F \ σ, f v) ^ 2 := by
  rw [← sum_linkWeightOf_mul_mul_add m σ f]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [sum_linkWeightOf hcard]
  split_ifs
  · ring
  · field_simp

/-- If at most one set of nonzero weight contains `σ`, the sum of squares above vanishes for
every `f` of degree-weighted mean zero. -/
private theorem sum_sq_eq_zero_of_unique_support (hcard : ∀ F, m F ≠ 0 → #F = d + 1)
    {σ : Finset ι} (h0 : (d : ℝ) - #σ ≠ 0)
    (huniq : ∀ F G, σ ⊆ F → σ ⊆ G → m F ≠ 0 → m G ≠ 0 → F = G) (f : ι → ℝ)
    (hf : ∑ u, (∑ v, linkWeightOf m σ u v) * f u = 0) :
    ∑ F with σ ⊆ F, m F * (∑ v ∈ F \ σ, f v) ^ 2 = 0 := by
  rw [sum_linkWeightOf_mul_eq_faces hcard] at hf
  have hf' := (mul_eq_zero.mp hf).resolve_left h0
  by_cases hex : ∃ F₀, σ ⊆ F₀ ∧ m F₀ ≠ 0
  · obtain ⟨F₀, hσF₀, hF₀⟩ := hex
    have hmem : F₀ ∈ ({F | σ ⊆ F} : Finset (Finset ι)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσF₀⟩
    have hzero : ∀ G ∈ ({F | σ ⊆ F} : Finset (Finset ι)), G ≠ F₀ → m G = 0 := by
      intro G hG hne
      by_contra h
      exact hne (huniq G F₀ (Finset.mem_filter.mp hG).2 hσF₀ h hF₀)
    rw [Finset.sum_eq_single_of_mem F₀ hmem fun G hG hne => by rw [hzero G hG hne, zero_mul]]
      at hf' ⊢
    rw [(mul_eq_zero.mp hf').resolve_left hF₀]
    ring
  · push Not at hex
    exact Finset.sum_eq_zero fun G hG => by rw [hex G (Finset.mem_filter.mp hG).2, zero_mul]

/-- **The quadratic form in the equality case.** Let `m` vanish off the sets with `d + 1`
elements, and suppose at most one set of nonzero weight contains `σ`. Then for every `f` of
degree-weighted mean zero, the quadratic form of the link of `σ` is exactly `−1/(d − |σ|)` times
the degree-weighted norm of `f`. When moreover `m ≥ 0`, `|σ| + 1 ≤ d` and some set of nonzero
weight contains `σ`, this says that every nontrivial eigenvalue of the walk on the link is
`−1/(d − |σ|)`. (Without these the reading fails: with signed `m` the "walk" is not a random walk,
and otherwise the link has no edges and there is no walk.)

As an identity it needs no sign condition on `m` and no condition on `σ`. If no set of nonzero
weight contains `σ`, or if `|σ| ≥ d`, the link has no edges and both sides are `0`; for `|σ| = d`
the coefficient is the junk value `−(1/0) = 0` in Lean. -/
theorem sum_linkWeightOf_mul_mul_eq_neg_one_div_mul (hcard : ∀ F, m F ≠ 0 → #F = d + 1)
    {σ : Finset ι} (huniq : ∀ F G, σ ⊆ F → σ ⊆ G → m F ≠ 0 → m G ≠ 0 → F = G) (f : ι → ℝ)
    (hf : ∑ u, (∑ v, linkWeightOf m σ u v) * f u = 0) :
    ∑ u, ∑ v, linkWeightOf m σ u v * f u * f v =
      -(1 / ((d : ℝ) - #σ)) * ∑ u, (∑ v, linkWeightOf m σ u v) * f u ^ 2 := by
  rcases lt_or_ge #σ d with hlt | hge
  · have hl := sub_card_pos (d := d) (σ := σ) (by omega)
    have h2 := sum_linkWeightOf_mul_mul_add_one_div hcard hl.ne' f
    rw [sum_sq_eq_zero_of_unique_support hcard hl.ne' huniq f hf] at h2
    linarith
  · simp [linkWeightOf_eq_zero_of_le_card hcard hge]

/-- **Equality in the link bound.** Let `m ≥ 0` vanish off the sets with `d + 1` elements, and
let `|σ| + 1 ≤ d`. The random walk on the weighted graph of the link of `σ` has second eigenvalue
at most `−1/(d − |σ|)`, the least possible value (`link_walk_lower_bound`,
`neg_one_div_le_of_walkSecondEigenvalueLE_linkWeightOf`), exactly when at most one set of nonzero
weight contains `σ`. In that case, if `F` is that set, the link is the complete graph on `F \ σ`
with every edge of weight `m F` (`linkWeightOf_eq_sum`), and every nontrivial eigenvalue of its
walk is `−1/(d − |σ|)` (`sum_linkWeightOf_mul_mul_eq_neg_one_div_mul`).

No complex is involved, and there is no hypothesis that `σ` lies in a set of nonzero weight: if
none does, both sides hold (the link has no edges). The hypothesis `|σ| + 1 ≤ d` is needed only
at `|σ| = d`, where the link has no edges, the left-hand side reads `WalkSecondEigenvalueLE _ 0`
in Lean (`−(1/0) = 0`) and holds, while two sets of nonzero weight may contain `σ`. For
`|σ| > d` both sides hold. -/
theorem walkSecondEigenvalueLE_linkWeightOf_neg_one_div_iff (hnn : ∀ F, 0 ≤ m F)
    (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {σ : Finset ι} (hσd : #σ + 1 ≤ d) :
    WalkSecondEigenvalueLE (linkWeightOf m σ) (-(1 / ((d : ℝ) - #σ))) ↔
      ∀ F G, σ ⊆ F → σ ⊆ G → m F ≠ 0 → m G ≠ 0 → F = G := by
  have hl := sub_card_pos hσd
  constructor
  · intro h F₁ F₂ hσ₁ hσ₂ h₁ h₂
    by_contra hne
    have hc₁ := hcard F₁ h₁
    have hc₂ := hcard F₂ h₂
    have hns : ¬ F₂ ⊆ F₁ := fun hsub => hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    obtain ⟨u, huF₂, huF₁⟩ := Finset.not_subset.mp hns
    have huσ : u ∉ σ := fun hu => huF₁ (hσ₁ hu)
    have hcardsd : 0 < #(F₁ \ σ) := by
      have := Finset.card_sdiff_add_card_eq_card hσ₁
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hcardsd
    have hvF₁ := (Finset.mem_sdiff.mp hv).1
    have huv : u ≠ v := fun e => huF₁ (e ▸ hvF₁)
    obtain ⟨a, ha⟩ : ∃ a, a = ∑ x, linkWeightOf m σ u x := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = ∑ x, linkWeightOf m σ v x := ⟨_, rfl⟩
    have hpos₁ : 0 < m F₁ := lt_of_le_of_ne (hnn F₁) (Ne.symm h₁)
    have ha0 : 0 < a :=
      ha ▸ sum_linkWeightOf_pos_of_mem_sdiff hnn hcard hσ₂ h₂ hσd
        (Finset.mem_sdiff.mpr ⟨huF₂, huσ⟩)
    -- the test function: `b` at `u`, `−a` at `v`
    obtain ⟨f, hf⟩ : ∃ f : ι → ℝ, f = fun x => if x = u then b else if x = v then -a else 0 :=
      ⟨_, rfl⟩
    have hfu : f u = b := by rw [hf]; exact if_pos rfl
    have hfv : f v = -a := by rw [hf]; simp [huv.symm]
    have hf0 : ∀ x, x ≠ u → x ≠ v → f x = 0 := fun x hxu hxv => by rw [hf]; simp [hxu, hxv]
    have hmean : ∑ x, (∑ y, linkWeightOf m σ x y) * f x = 0 := by
      rw [Finset.sum_eq_add_of_mem u v (Finset.mem_univ _) (Finset.mem_univ _) huv
        fun x _ hx => by rw [hf0 x hx.1 hx.2, mul_zero], hfu, hfv, ← ha, ← hb]
      ring
    have h1 := h f hmean
    have h2 := sum_linkWeightOf_mul_mul_add_one_div hcard hl.ne' f
    -- `F₁` contains `v` but not `u`, so its square is `a²`
    have hS : ∑ x ∈ F₁ \ σ, f x = -a := by
      rw [Finset.sum_eq_single_of_mem v hv fun x hx hxv => ?_]
      · exact hfv
      · exact hf0 x (fun e => huF₁ (e ▸ (Finset.mem_sdiff.mp hx).1)) hxv
    have h3 : m F₁ * a ^ 2 ≤ ∑ F with σ ⊆ F, m F * (∑ v ∈ F \ σ, f v) ^ 2 := by
      have := Finset.single_le_sum (f := fun F => m F * (∑ v ∈ F \ σ, f v) ^ 2)
        (fun G _ => mul_nonneg (hnn G) (sq_nonneg _))
        (Finset.mem_filter.mpr ⟨Finset.mem_univ F₁, hσ₁⟩)
      simpa only [hS, neg_sq] using this
    have h4 : 0 < m F₁ * a ^ 2 := mul_pos hpos₁ (pow_pos ha0 2)
    have h5 : -(1 / ((d : ℝ) - #σ)) * ∑ u, (∑ v, linkWeightOf m σ u v) * f u ^ 2 =
        -(1 / ((d : ℝ) - #σ) * ∑ u, (∑ v, linkWeightOf m σ u v) * f u ^ 2) := neg_mul _ _
    linarith
  · exact fun huniq f hf => (sum_linkWeightOf_mul_mul_eq_neg_one_div_mul hcard huniq f hf).le

variable {K : PreAbstractSimplicialComplex ι}

omit [Fintype ι] [DecidableEq ι] in
/-- A top weight of `K` has a top face through `σ`, when `σ` is `∅` or a face. -/
private theorem IsTopWeight.exists_top_face_superset (hm : K.IsTopWeight d m) {σ : Finset ι}
    (hσ : σ = ∅ ∨ σ ∈ K) : ∃ F ∈ K, #F = d + 1 ∧ σ ⊆ F := by
  rcases hσ with rfl | hσ
  · obtain ⟨F, hF, hc, -⟩ := hm.exists_pos
    exact ⟨F, hF, hc, Finset.empty_subset F⟩
  · obtain ⟨-, F, hF, hσF, hc⟩ := hm.isPure σ hσ
    exact ⟨F, hF, hc, hσF⟩

/-- **A link of a complex has at least `d + 1 − |σ|` vertices of positive degree.** For a top
weight `m` of the `d`-dimensional complex `K` and `σ = ∅` or a face of `K` with `|σ| + 1 ≤ d`,
the weighted graph of the link of `σ` has at least `d + 1 − |σ|` vertices of positive degree (the
vertices outside `σ` of any top face through `σ`). This is `le_card_pos_degree_linkWeightOf`; the
same remarks on its hypotheses apply. For a nonempty `σ` that is not a face the link has no
edges. -/
theorem IsTopWeight.le_card_pos_degree_link (hm : K.IsTopWeight d m) {σ : Finset ι}
    (hσ : σ = ∅ ∨ σ ∈ K) (hσd : #σ + 1 ≤ d) :
    d + 1 - #σ ≤ #{u | 0 < ∑ v, linkWeightOf m σ u v} := by
  obtain ⟨F, hF, hFc, hσF⟩ := hm.exists_top_face_superset hσ
  exact le_card_pos_degree_linkWeightOf hm.nonneg hm.card_eq_of_ne_zero hσF
    (hm.pos F hF hFc).ne' hσd

/-- **The second eigenvalue of a link of a complex is at least `−1/(d − |σ|)`.** For a top weight
`m` of the `d`-dimensional complex `K` and `σ = ∅` or a face of `K` with `|σ| + 1 ≤ d`, every
`lam` bounding the second eigenvalue of the walk on the link of `σ` is at least `−1/(d − |σ|)`.
This is `neg_one_div_le_of_walkSecondEigenvalueLE_linkWeightOf`; the same remarks on its
hypotheses apply. -/
theorem IsTopWeight.neg_one_div_le_of_walkSecondEigenvalueLE_link (hm : K.IsTopWeight d m)
    {σ : Finset ι} (hσ : σ = ∅ ∨ σ ∈ K) (hσd : #σ + 1 ≤ d)
    (h : WalkSecondEigenvalueLE (linkWeightOf m σ) lam) : -(1 / ((d : ℝ) - #σ)) ≤ lam := by
  obtain ⟨F, hF, hFc, hσF⟩ := hm.exists_top_face_superset hσ
  exact neg_one_div_le_of_walkSecondEigenvalueLE_linkWeightOf hm.nonneg hm.card_eq_of_ne_zero
    hσF (hm.pos F hF hFc).ne' hσd h

/-- For a top weight `m` of `K`, "at most one set of nonzero weight contains `σ`" says that at
most one top face of `K` contains `σ`, that is, `topDegree d σ ≤ 1`. Any finite set `σ` is
allowed. -/
theorem IsTopWeight.forall_eq_of_subset_iff_topDegree_le_one (hm : K.IsTopWeight d m)
    (σ : Finset ι) :
    (∀ F G, σ ⊆ F → σ ⊆ G → m F ≠ 0 → m G ≠ 0 → F = G) ↔ K.topDegree d σ ≤ 1 := by
  classical
  unfold topDegree
  rw [Finset.card_le_one]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro h F ⟨hF, hFc, hσF⟩ G ⟨hG, hGc, hσG⟩
    exact h F G hσF hσG (hm.ne_zero_iff.mpr ⟨hF, hFc⟩) (hm.ne_zero_iff.mpr ⟨hG, hGc⟩)
  · intro h F G hσF hσG hF hG
    obtain ⟨hF1, hF2⟩ := hm.ne_zero_iff.mp hF
    obtain ⟨hG1, hG2⟩ := hm.ne_zero_iff.mp hG
    exact h F ⟨hF1, hF2, hσF⟩ G ⟨hG1, hG2, hσG⟩

/-- **Equality in the link bound, for a complex.** For a top weight `m` of the `d`-dimensional
complex `K` and `σ = ∅` or a face of `K` with `|σ| + 1 ≤ d`, the random walk on the link of `σ`
has second eigenvalue at most `−1/(d − |σ|)` (the least possible value) exactly when `σ` lies in
exactly one top face of `K`. The answer does not depend on the weight `m`.

The hypotheses on `σ` matter:
* For a nonempty `σ` that is not a face, the link has no edges and the left-hand side holds, but
  `topDegree d σ = 0`. Without the face hypothesis the statement is
  `walkSecondEigenvalueLE_linkWeightOf_neg_one_div_iff` combined with
  `IsTopWeight.forall_eq_of_subset_iff_topDegree_le_one`: the bound holds iff
  `topDegree d σ ≤ 1`.
* For `|σ| = d`, the left-hand side reads `WalkSecondEigenvalueLE _ 0` in Lean (`−(1/0) = 0`) and
  holds since the link has no edges, while `σ` may lie in many top faces. -/
theorem IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_neg_one_div_iff (hm : K.IsTopWeight d m)
    {σ : Finset ι} (hσ : σ = ∅ ∨ σ ∈ K) (hσd : #σ + 1 ≤ d) :
    WalkSecondEigenvalueLE (linkWeightOf m σ) (-(1 / ((d : ℝ) - #σ))) ↔
      K.topDegree d σ = 1 := by
  rw [PreAbstractSimplicialComplex.walkSecondEigenvalueLE_linkWeightOf_neg_one_div_iff hm.nonneg
    hm.card_eq_of_ne_zero hσd, hm.forall_eq_of_subset_iff_topDegree_le_one]
  have : 0 < K.topDegree d σ := by
    rw [topDegree_pos_iff]
    exact hm.exists_top_face_superset hσ
  omega

/-- **The quadratic form in the equality case, for a complex.** For a top weight `m` of `K`, if
at most one top face of `K` contains `σ`, then for every `f` of degree-weighted mean zero the
quadratic form of the link of `σ` is `−1/(d − |σ|)` times the degree-weighted norm of `f`. When
moreover `|σ| + 1 ≤ d` and `σ` is `∅` or a face of `K` (so that exactly one top face contains
`σ`), this says that every nontrivial eigenvalue of the walk on the link is `−1/(d − |σ|)`. This
is `sum_linkWeightOf_mul_mul_eq_neg_one_div_mul`, with the same degenerate cases: if no top face
contains `σ`, or `|σ| ≥ d`, both sides are `0` (for `|σ| = d` the coefficient is `−(1/0) = 0`). -/
theorem IsTopWeight.sum_linkWeightOf_mul_mul_eq_neg_one_div_mul (hm : K.IsTopWeight d m)
    {σ : Finset ι} (h1 : K.topDegree d σ ≤ 1) (f : ι → ℝ)
    (hf : ∑ u, (∑ v, linkWeightOf m σ u v) * f u = 0) :
    ∑ u, ∑ v, linkWeightOf m σ u v * f u * f v =
      -(1 / ((d : ℝ) - #σ)) * ∑ u, (∑ v, linkWeightOf m σ u v) * f u ^ 2 :=
  PreAbstractSimplicialComplex.sum_linkWeightOf_mul_mul_eq_neg_one_div_mul hm.card_eq_of_ne_zero
    ((hm.forall_eq_of_subset_iff_topDegree_le_one σ).mpr h1) f hf

end Link

/-! ### Local spectral expanders: the number of vertices, and rigidity of the simplex -/

section Expander

variable {K : PreAbstractSimplicialComplex ι} {d : ℕ} {m : Finset ι → ℝ} {lam : ℝ}

omit [Fintype ι] [DecidableEq ι] in
/-- **A `d`-dimensional complex has at least `d + 1` vertices.** A pure `d`-dimensional complex
on a finite type with at least one face has a face with `d + 1` elements, all of whose points are
vertices. (`K.vertices` is the set of points `v` with `{v} ∈ K`, and `Set.ncard` counts it; for an
infinite set `ncard` would be `0`, which `[Finite ι]` rules out.) The complex with no faces is
pure of every dimension and has no vertices, hence the hypothesis `hne`. -/
theorem IsPure.succ_le_ncard_vertices [Finite ι] (hpure : K.IsPure d) (hne : ∃ F, F ∈ K) :
    d + 1 ≤ K.vertices.ncard := by
  obtain ⟨F, hF, hc⟩ := hpure.exists_card_eq hne
  have hsub : (↑F : Set ι) ⊆ K.vertices := fun v hv =>
    K.mem_of_subset hF (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  calc d + 1 = (↑F : Set ι).ncard := by rw [Set.ncard_coe_finset, hc]
    _ ≤ K.vertices.ncard := Set.ncard_le_ncard hsub

/-- **The vertices of positive degree of the underlying graph are the vertices of `K`.** For a top
weight `m` of the `d`-dimensional complex `K` with `d ≥ 1`, a point `u` has positive degree in the
weighted underlying graph of `K` (the link of `∅`) exactly when `{u}` is a face of `K`, that is,
`u ∈ K.vertices`. The degree of `u` is `d · faceWeight m {u}`, which is positive exactly when `u`
lies in a top face.

The hypothesis `d ≥ 1` is needed: for `d = 0` the underlying graph has no edges, so no point has
positive degree, while the points of the top faces are vertices. -/
theorem IsTopWeight.sum_linkWeightOf_empty_pos_iff (hm : K.IsTopWeight d m) (hd : 1 ≤ d) {u : ι} :
    0 < ∑ v, linkWeightOf m ∅ u v ↔ {u} ∈ K := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [sum_linkWeightOf hm.card_eq_of_ne_zero, if_neg (Finset.notMem_empty u), Finset.card_empty,
    Nat.cast_zero, sub_zero, Finset.insert_empty]
  constructor
  · intro hu
    have hf : 0 < faceWeight m {u} := pos_of_mul_pos_right hu hd0.le
    obtain ⟨F, hF, -, huF⟩ := hm.faceWeight_pos_iff.mp hf
    exact K.mem_of_subset hF huF (Finset.singleton_nonempty u)
  · intro hu
    obtain ⟨-, F, hF, huF, hc⟩ := hm.isPure {u} hu
    exact mul_pos hd0 (hm.faceWeight_pos_iff.mpr ⟨F, hF, hc, huF⟩)

/-- **A local spectral expander on `n` vertices has `lam ≥ −1/(n − 1)`.** If `K`, with the weight
`m`, is a `lam`-local spectral expander and `K` has `n` vertices, then `lam ≥ −1/(n − 1)`: the
vertices of positive degree in the weighted underlying graph of `K` are exactly the vertices of
`K` (`IsTopWeight.sum_linkWeightOf_empty_pos_iff`), and the trace bound
`WalkSecondEigenvalueLE.neg_one_div_card_le` applies to that graph. The vertex count is
`n = K.vertices.ncard`, which equals `Nat.card K.vertices` (`Nat.card_coe_set_eq`).

There are no degenerate cases: the definition forces `d ≥ 1`, and then `n ≥ d + 1 ≥ 2`
(`IsPure.succ_le_ncard_vertices`), so `n − 1 ≥ 1` (the subtraction is in `ℝ`). Since `n ≥ d + 1`,
this is at least as strong as `IsLocalSpectralExpanderOf.neg_one_div_le` (`lam ≥ −1/d`), and
strictly stronger when `K` has more than `d + 1` vertices. -/
theorem IsLocalSpectralExpanderOf.neg_one_div_ncard_vertices_le
    (h : K.IsLocalSpectralExpanderOf d m lam) :
    -(1 / ((K.vertices.ncard : ℝ) - 1)) ≤ lam := by
  have hm := h.isTopWeight
  have hd := h.one_le
  have hd' : #(∅ : Finset ι) + 1 ≤ d := by rw [Finset.card_empty]; omega
  -- the vertices of positive degree are the vertices of `K`
  have heq : K.vertices = ↑({u | 0 < ∑ v, linkWeightOf m ∅ u v} : Finset ι) := by
    ext u
    rw [Finset.coe_filter]
    simp only [Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact (hm.sum_linkWeightOf_empty_pos_iff hd).symm
  have hN := hm.le_card_pos_degree_link (Or.inl rfl) hd'
  rw [Finset.card_empty] at hN
  have h2 : 2 ≤ #({u | 0 < ∑ v, linkWeightOf m ∅ u v} : Finset ι) := by omega
  have ha := (h.walkSecondEigenvalueLE (Or.inl rfl) hd').neg_one_div_card_le
    (linkWeightOf_symm m ∅) (linkWeightOf_nonneg hm.nonneg ∅) h2
  rwa [heq, Set.ncard_coe_finset]

/-- **A local spectral expander on `n` vertices has `lam ≥ −1/(n − 1)`**, for the counting
weights: the case `m = K.uniformWeight d` of
`IsLocalSpectralExpanderOf.neg_one_div_ncard_vertices_le`. It strengthens
`IsLocalSpectralExpander.neg_one_div_le`. There are no degenerate cases, since the definition
forces `d ≥ 1` and so `n ≥ 2`. -/
theorem IsLocalSpectralExpander.neg_one_div_ncard_vertices_le
    (h : K.IsLocalSpectralExpander d lam) : -(1 / ((K.vertices.ncard : ℝ) - 1)) ≤ lam :=
  ((K.isLocalSpectralExpander_iff_isLocalSpectralExpanderOf).mp
    h).neg_one_div_ncard_vertices_le

/-- **Rigidity of the simplex, weighted.** `K`, with the weight `m`, is a `(−1/d)`-local spectral
expander exactly when `d ≥ 1`, `m` is a top weight of `K`, and `K` is a single `d`-simplex: there
is a set `F` with `d + 1` elements whose nonempty subsets are exactly the faces of `K`. (The top
weights of a single simplex `F` are the functions `c · 1_F` with `c > 0`.) So the bound
`IsLocalSpectralExpanderOf.neg_one_div_le` is attained, in every dimension `d ≥ 1`, exactly by the
simplices, with any weight.

For `d = 0` both sides are false (`not_isLocalSpectralExpanderOf_zero`); the junk value
`−(1/0) = 0` of the bound plays no role. -/
theorem isLocalSpectralExpanderOf_neg_one_div_iff :
    K.IsLocalSpectralExpanderOf d m (-(1 / (d : ℝ))) ↔
      1 ≤ d ∧ K.IsTopWeight d m ∧
        ∃ F : Finset ι, #F = d + 1 ∧ ∀ τ, τ ∈ K ↔ τ.Nonempty ∧ τ ⊆ F := by
  constructor
  · rintro ⟨hd, hm, h⟩
    refine ⟨hd, hm, ?_⟩
    have h0 : #(∅ : Finset ι) + 1 ≤ d := by rw [Finset.card_empty]; omega
    have hE := h ∅ (Or.inl rfl) h0
    have e : -(1 / (d : ℝ)) = -(1 / ((d : ℝ) - #(∅ : Finset ι))) := by simp
    rw [e, hm.walkSecondEigenvalueLE_linkWeightOf_neg_one_div_iff (Or.inl rfl) h0] at hE
    have huniq := (hm.forall_eq_of_subset_iff_topDegree_le_one ∅).mpr hE.le
    obtain ⟨F, hF, hFc, hmF⟩ := hm.exists_pos
    refine ⟨F, hFc, fun τ => ⟨fun hτ => ⟨K.nonempty_of_mem hτ, ?_⟩,
      fun ⟨hne, hτF⟩ => K.mem_of_subset hF hτF hne⟩⟩
    obtain ⟨-, G, hG, hτG, hGc⟩ := hm.isPure τ hτ
    have := huniq G F (Finset.empty_subset _) (Finset.empty_subset _) (hm.pos G hG hGc).ne'
      hmF.ne'
    exact this ▸ hτG
  · rintro ⟨hd, hm, F, hFc, hK⟩
    refine ⟨hd, hm, fun σ _ hσd => ?_⟩
    have huniq : ∀ G H, σ ⊆ G → σ ⊆ H → m G ≠ 0 → m H ≠ 0 → G = H := by
      have key : ∀ G, m G ≠ 0 → G = F := by
        intro G hG
        obtain ⟨hGK, hGc⟩ := hm.ne_zero_iff.mp hG
        exact Finset.eq_of_subset_of_card_le ((hK G).mp hGK).2 (by omega)
      intro G H _ _ hG hH
      rw [key G hG, key H hH]
    refine ((walkSecondEigenvalueLE_linkWeightOf_neg_one_div_iff hm.nonneg hm.card_eq_of_ne_zero
      hσd).mpr huniq).mono (linkWeightOf_nonneg hm.nonneg σ) ?_
    have hle : (d : ℝ) - #σ ≤ d := by
      have : (0 : ℝ) ≤ #σ := Nat.cast_nonneg _
      linarith
    exact neg_le_neg (one_div_le_one_div_of_le (sub_card_pos hσd) hle)

/-- **Rigidity of the simplex.** `K` is a `(−1/d)`-local spectral expander (for the counting
weights) exactly when `d ≥ 1` and `K` is a single `d`-simplex: there is a set `F` with `d + 1`
elements whose nonempty subsets are exactly the faces of `K`. So the bound
`IsLocalSpectralExpander.neg_one_div_le` is attained, in every dimension `d ≥ 1`, exactly by the
simplices.

For `d = 0` both sides are false (`not_isLocalSpectralExpander_zero`); the junk value
`−(1/0) = 0` of the bound plays no role. -/
theorem isLocalSpectralExpander_neg_one_div_iff :
    K.IsLocalSpectralExpander d (-(1 / (d : ℝ))) ↔
      1 ≤ d ∧ ∃ F : Finset ι, #F = d + 1 ∧ ∀ τ, τ ∈ K ↔ τ.Nonempty ∧ τ ⊆ F := by
  rw [K.isLocalSpectralExpander_iff_isLocalSpectralExpanderOf,
    isLocalSpectralExpanderOf_neg_one_div_iff]
  constructor
  · rintro ⟨hd, -, h⟩
    exact ⟨hd, h⟩
  · rintro ⟨hd, F, hFc, hK⟩
    have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
    have hFK : F ∈ K := (hK F).mpr ⟨hFne, subset_rfl⟩
    refine ⟨hd, K.isTopWeight_uniformWeight (fun τ hτ => ?_) ⟨F, hFK⟩, F, hFc, hK⟩
    have hτF := ((hK τ).mp hτ).2
    exact ⟨hFc ▸ Finset.card_le_card hτF, F, hFK, hτF, hFc⟩

/-- **The `d`-simplex is a `(−1/d)`-local spectral expander.** For `d ≥ 1`, the complete
`d`-dimensional complex on `d + 1` points (all nonempty subsets of `Fin (d + 1)`) is a
`(−1/d)`-local spectral expander, so the bound `IsLocalSpectralExpander.neg_one_div_le` is
attained in every dimension `d ≥ 1`. For `d = 0` it is not a local spectral expander at all
(`not_isLocalSpectralExpander_zero`). -/
theorem isLocalSpectralExpander_complete_fin_succ_neg_one_div {d : ℕ} (hd : 1 ≤ d) :
    (complete (Fin (d + 1)) d).IsLocalSpectralExpander d (-(1 / (d : ℝ))) := by
  refine isLocalSpectralExpander_neg_one_div_iff.mpr ⟨hd, Finset.univ, by simp, fun τ => ?_⟩
  rw [mem_complete]
  exact ⟨fun h => ⟨h.1, Finset.subset_univ τ⟩,
    fun h => ⟨h.1, (Finset.card_le_univ τ).trans (by simp)⟩⟩

end Expander

end PreAbstractSimplicialComplex
