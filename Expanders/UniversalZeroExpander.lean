/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.NegativeRigidity

/-!
# Complexes that are `0`-local spectral expanders for every weighting

A weighted complex `(K, m)` is a `0`-local spectral expander when the random walk on every link of
a face of dimension at most `d − 2` (and on `K` itself) has second eigenvalue at most `0`. Which
pure complexes have this property for **every** positive weight `m` on their top faces? The answer
is purely combinatorial: exactly those in which any two distinct top faces share `d` vertices, that
is, whose top faces form a clique of the Johnson graph `J(n, d + 1)`.

## The result

Let `d ≥ 1` and let `K` be a pure `d`-dimensional complex with at least one face
(`tfae_forall_isLocalSpectralExpanderOf_zero`). The following are equivalent.
* **(a)** `K.IsLocalSpectralExpanderOf d m 0` for every top weight `m` of `K`.
* **(b)** Any two distinct top faces share exactly `d` vertices.
* **(c)** All top faces contain a common `d`-set `D` (a *sunflower*, top faces `D ∪ {x}`), or all
  top faces lie in a common `(d + 2)`-set `T` (top faces `T \ {y}`).
* **(d)** `K` is a matroid complex (`IsMatroidComplex`), and the link of every `σ` with
  `|σ| = d − 1` (`σ = ∅` when `d = 1`) has no two disjoint edges (`NoTwoDisjointLinkEdges`).
* **(d′)** The link of every `σ` with `|σ| ≤ d − 2`, including `σ = ∅`, is connected, and the
  links of the `(d − 2)`-faces have no two disjoint edges.

The connectivity hypothesis in (d′) cannot be dropped: two disjoint triangles meet the matching
condition but are not universally `0` (`disjointTriangles_counterexample`).

Consequences, for a complex `K` on a vertex type `ι` with `N = Fintype.card ι` points:
* `forall_isLocalSpectralExpanderOf_zero_of_card_le`: if `N ≤ d + 2` (in particular for the simplex,
  `N = d + 1`, and for every pure `d`-complex on `d + 2` points) `K` is universally `0`.
* `forall_isLocalSpectralExpanderOf_zero_iff_cone`: if every point is a vertex and `N ≥ d + 3`,
  `K` is universally `0` exactly when it is the cone `Δ^{d−1} * (N − d points)`: for some `d`-set
  `D`, the faces are the nonempty subsets of the sets `D ∪ {x}`, `x ∉ D` (the matroid
  `U_{d,d} ⊕ U_{1,N−d}`).
* `isLocalSpectralExpanderOf_twoTriangles_zero`: the two triangles sharing an edge of
  `Expanders/NegativeRigidity.lean` (the example showing that `lam < 0` cannot be relaxed to
  `lam ≤ 0` there) are a `0`-local spectral expander for every weighting.

## Proof

* (a) ⇒ (b) (`exists_isTopWeight_not_walkSecondEigenvalueLE_zero`). If distinct top faces `F, G`
  meet in `σ` with `|σ| ≤ d − 1`, weigh every top face `1`, and `F` and `G` additionally by a large
  `t`. With `A = F \ σ`, `B = G \ σ` and `D(·)` the degree sum in the link of `σ`, the test
  function `D(B) · 1_A − D(A) · 1_B` has degree-weighted mean zero, and the definition of
  `WalkSecondEigenvalueLE` at `0` gives
  `D(B)² W(A, A) + D(A)² W(B, B) ≤ D(A) D(B) (W(A, B) + W(B, A))`
  (`WalkSecondEigenvalueLE.sq_mul_add_sq_mul_le_of_zero`). Now `W(A, A), W(B, B) ≥ t`, while
  `W(A, B) + W(B, A)` does not see `t` (no edge between `A` and `B` lies in `F` or `G`), which is
  impossible once `t` exceeds it. One explicit weight, no limit, no Lorentzian polynomials.
* (b) ⇒ (a) (`IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_zero`). The sets `F \ σ` of the top
  faces through `σ` pairwise share `d − |σ|` points, so they form a sunflower or lie in a common
  set (`Finset.sunflower_or_subset_of_card_inter`, the classification of Johnson-graph cliques).
  The quadratic form of the link is `Σ_F m F ((Σ_{F∖σ} f)² − Σ_{F∖σ} f²)`
  (`sum_linkWeightOf_mul_mul`), and in each case it is `≤ 0` on mean-zero `f` by a direct
  computation (`sum_mul_sq_sub_le_zero_of_sunflower`, `sum_mul_sq_sub_le_zero_of_codim_one`; the
  second rests on the inequality `two_mul_sum_mul_sum_mul_sq_le`). This handles every link at
  once: trickling down is not used.
* (b) ⇔ (c): the Johnson clique classification again (`forall_card_inter_iff_sunflower_or_subset`).
* (b) ⇒ (d): basis exchange is immediate (`isMatroidComplex_of_forall_card_inter`); two disjoint
  edges in the link of a `(d − 2)`-face give top faces meeting in `d − 1` points
  (`noTwoDisjointLinkEdges_of_forall_card_inter`). (d) ⇒ (b): by basis exchange, two bases at
  distance `≥ 2` lead to two bases at distance exactly `2`, i.e. two top faces meeting in `d − 1`
  points (`forall_card_inter_of_isMatroidComplex`).
* (b) ⇒ (d′): two vertices of a link are joined directly or through a common vertex of their top
  faces (`isConnected_link_of_forall_card_inter`). (d′) ⇒ (b): take top faces `F, G` meeting in a
  set `σ` that is as large as possible among the pairs meeting in at most `d − 1` points. If
  `|σ| = d − 1` the matching condition fails; otherwise walk from `F \ σ` to `G \ σ` in the
  connected link of `σ`, keeping a top face that meets `F` in `d` points
  (`forall_card_inter_of_isConnected_link`).

## How it was found, and the literature

The statement was found by computation: exhaustive enumeration of the pure `d`-complexes on up to
seven points with every point a vertex (several million complexes over eleven pairs `(N, d)`),
exact inertia tests of the link matrices over `ℚ` with random and extreme weights, and exact
checks of the test-function certificate used in (a) ⇒ (b). It survived an independent attempt to
refute it, and is proved here.

Literature search (web searches on "every weighting / all weights" `0`-local spectral expanders,
Lorentzian bases, Johnson-graph cliques of top faces, and matroids on whose bases every function is
a valuated matroid; and reading of the sources below). Found: the related *existence* statement,
that **some** weighting of `K` is a `0`-local spectral expander exactly when `K` is a matroid
complex, follows from Anari, Liu, Oveis Gharan and Vinzant (*Log-concave polynomials II*,
arXiv:1811.01816, Prop. 4.1 and Thm. 2.16, the latter through Oppenheim's trickling down, their
Thm. 5.1: a weighted complex is a `0`-expander iff its generating polynomial is strongly
log-concave, and the uniform weighting of a matroid is one) together with Brändén and Huh
(*Lorentzian polynomials*, Ann. of Math. 192 (2020), §2–3: the support of a Lorentzian polynomial
is M-convex, so the top faces are the bases of a matroid). The classification of the cliques of
the Johnson graph into the two families of (c) is classical folklore. Not found: any statement of
the "every weighting" characterization (a) ⇔ (b) ⇔ (c), of the matching condition in (d), or of
the cone classification for `N ≥ d + 3`. Husic, Loho,
Smith and Végh (*On complete classes of valuated matroids*, arXiv:2107.06961) study when *all*
functions on a set system are valuated matroids, for sparse paving families, which is a different
question. The closest framework is Baker, Huh, Kummer and Lorscheid (*Lorentzian polynomials and
matroids over triangular hyperfields 1*, arXiv:2508.02907, and its second part), who study the space
of Lorentzian polynomials supported on the bases of a fixed matroid; item (a) says that this space
is the whole open simplex of positive coefficient vectors, and neither part was found to state
when that happens. Every ingredient here is standard and the proofs are short, so the result should be
regarded as unrecorded folklore rather than as new.

## Definitions
* `PreAbstractSimplicialComplex.IsMatroidComplex`: the augmentation axiom for `{∅} ∪ K`.
* `PreAbstractSimplicialComplex.NoTwoDisjointLinkEdges`: the links of the `(d − 2)`-faces (and of
  `∅` when `d = 1`) have no two disjoint edges.
* `PreAbstractSimplicialComplex.disjointTriangles`: two disjoint triangles on `Fin 6`.
-/

open Finset

variable {ι : Type*}

/-! ### Weighted graphs: a two-set test function at `0` -/

section Graph

variable [Fintype ι] {w : ι → ι → ℝ}

/-- **The two-set test at `0`.** If the random walk on `w` has second eigenvalue at most `0`, then
for any functions `a, b` (typically the indicators of two sets `A, B`), writing `deg u = Σ_v w u v`,
`D(a) = Σ_u deg u · a u` and `Q(a, b) = Σ_{u,v} w u v · a u · b v`,

  `D(b)² Q(a, a) + D(a)² Q(b, b) ≤ D(a) D(b) (Q(a, b) + Q(b, a))`.

This is the definition tested on `D(b) · a − D(a) · b`, which has degree-weighted mean zero. No
hypothesis on `w` (symmetry, sign, loops) or on `a, b` is needed. If `D(a) = 0` or `D(b) = 0`
the test function is a multiple of `b` or of `a` and the inequality may carry no information. -/
theorem WalkSecondEigenvalueLE.sq_mul_add_sq_mul_le_of_zero (h : WalkSecondEigenvalueLE w 0)
    (a b : ι → ℝ) :
    (∑ u, (∑ v, w u v) * b u) ^ 2 * (∑ u, ∑ v, w u v * a u * a v) +
        (∑ u, (∑ v, w u v) * a u) ^ 2 * (∑ u, ∑ v, w u v * b u * b v) ≤
      (∑ u, (∑ v, w u v) * a u) * (∑ u, (∑ v, w u v) * b u) *
        ((∑ u, ∑ v, w u v * a u * b v) + ∑ u, ∑ v, w u v * b u * a v) := by
  obtain ⟨dA, hdA⟩ : ∃ x, x = ∑ u, (∑ v, w u v) * a u := ⟨_, rfl⟩
  obtain ⟨dB, hdB⟩ : ∃ x, x = ∑ u, (∑ v, w u v) * b u := ⟨_, rfl⟩
  rw [← hdA, ← hdB]
  have hmean : ∑ u, (∑ v, w u v) * (dB * a u - dA * b u) = 0 := by
    have e : ∀ u, (∑ v, w u v) * (dB * a u - dA * b u) =
        dB * ((∑ v, w u v) * a u) - dA * ((∑ v, w u v) * b u) := fun u => by ring
    rw [Finset.sum_congr rfl fun u _ => e u, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← hdA, ← hdB]
    ring
  have h1 := h (fun u => dB * a u - dA * b u) hmean
  have e : ∀ u v, w u v * (dB * a u - dA * b u) * (dB * a v - dA * b v) =
      dB ^ 2 * (w u v * a u * a v) - dA * dB * (w u v * a u * b v) -
        dA * dB * (w u v * b u * a v) + dA ^ 2 * (w u v * b u * b v) := fun u v => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
  nlinarith [h1]

end Graph

/-! ### Two quadratic inequalities, and Johnson-graph cliques -/

section Algebra

variable {α : Type*}

/-- **An inequality for nonnegative weights.** For `m ≥ 0` on a finite set `s` and any `g`, with
`M = Σ m`,

  `2 M Σ m g² ≤ (Σ m g)² + M² Σ g²`.

Equivalently `Σ_i (M − m_i)² g_i² + Σ_{i ≠ j} m_i m_j g_i g_j ≥ 0`, and the proof writes the
difference as `½ Σ_{i ≠ j} (m_j g_i + m_i g_j)² + Σ_i g_i² ((Σ_{j ≠ i} m_j)² − Σ_{j ≠ i} m_j²)`.
For `s = ∅`, or one element, both sides are equal (for two elements the difference is the single
square `(m₂ g₁ + m₁ g₂)²`). The sign condition on `m` is needed: for `m = (1, 1, −1)` and
`g = (1, −1, 0)` the left side is `4` and the right side is `2`. -/
theorem two_mul_sum_mul_sum_mul_sq_le (s : Finset α) (m g : α → ℝ) (hm : ∀ i ∈ s, 0 ≤ m i) :
    2 * (∑ i ∈ s, m i) * ∑ i ∈ s, m i * g i ^ 2 ≤
      (∑ i ∈ s, m i * g i) ^ 2 + (∑ i ∈ s, m i) ^ 2 * ∑ i ∈ s, g i ^ 2 := by
  classical
  -- the off-diagonal sum of squares `Σ_{i ≠ j} (m j g i + m i g j)²` is nonnegative
  have hoff : 0 ≤ ∑ i ∈ s, ∑ j ∈ s.erase i, (m j * g i + m i * g j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hfull : ∑ i ∈ s, ∑ j ∈ s, (m j * g i + m i * g j) ^ 2 =
      2 * (∑ i ∈ s, g i ^ 2) * (∑ j ∈ s, m j ^ 2) + 2 * (∑ i ∈ s, m i * g i) ^ 2 := by
    have e : ∀ i j, (m j * g i + m i * g j) ^ 2 =
        g i ^ 2 * m j ^ 2 + 2 * (m i * g i) * (m j * g j) + m i ^ 2 * g j ^ 2 :=
      fun i j => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hdiag : ∑ i ∈ s, ∑ j ∈ s.erase i, (m j * g i + m i * g j) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, (m j * g i + m i * g j) ^ 2 - 4 * ∑ i ∈ s, m i ^ 2 * g i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_erase_eq_sub hi]
    ring
  -- for each `i`, `Σ_{j ≠ i} m j² ≤ (Σ_{j ≠ i} m j)²`
  have hrow : ∀ i ∈ s, g i ^ 2 * ((∑ j ∈ s, m j ^ 2) - m i ^ 2) ≤
      g i ^ 2 * ((∑ j ∈ s, m j) - m i) ^ 2 := by
    intro i hi
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [← Finset.sum_erase_eq_sub hi, ← Finset.sum_erase_eq_sub hi, sq, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun k hk => hm k (Finset.mem_of_mem_erase hk)) hj)
      (hm j (Finset.mem_of_mem_erase hj))
  have hsum := Finset.sum_le_sum hrow
  have e1 : ∑ i ∈ s, g i ^ 2 * ((∑ j ∈ s, m j ^ 2) - m i ^ 2) =
      (∑ i ∈ s, g i ^ 2) * (∑ j ∈ s, m j ^ 2) - ∑ i ∈ s, m i ^ 2 * g i ^ 2 := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i ∈ s, g i ^ 2 * ((∑ j ∈ s, m j) - m i) ^ 2 =
      (∑ j ∈ s, m j) ^ 2 * (∑ i ∈ s, g i ^ 2) -
        2 * (∑ j ∈ s, m j) * (∑ i ∈ s, m i * g i ^ 2) + ∑ i ∈ s, m i ^ 2 * g i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2] at hsum
  rw [hdiag, hfull] at hoff
  nlinarith [hoff, hsum]

variable [DecidableEq ι]

/-- **The quadratic form of a sunflower is nonpositive on mean-zero functions.** Let the finite
sets `A i` (`i ∈ s`) each consist of a common set `C` and exactly one further point, with weights
`m i ≥ 0`. If `Σ_i m i · Σ_{A i} f = 0`, then `Σ_i m i ((Σ_{A i} f)² − Σ_{A i} f²) ≤ 0`; in fact
the sum is `−M ((Σ_C f)² + Σ_C f²)`, `M = Σ m`.

The further points need not be distinct, and `C = ∅` is allowed. With `A i = F i \ σ` for the top
faces `F i ⊇ σ`, the sum is the quadratic form of the link of `σ` (`sum_linkWeightOf_mul_mul`) and
the hypothesis is its mean-zero condition. -/
theorem sum_mul_sq_sub_le_zero_of_sunflower (s : Finset α) (m : α → ℝ) (A : α → Finset ι)
    (C : Finset ι) (f : ι → ℝ) (hm : ∀ i ∈ s, 0 ≤ m i)
    (hA : ∀ i ∈ s, C ⊆ A i ∧ #(A i \ C) = 1)
    (hmean : ∑ i ∈ s, m i * ∑ v ∈ A i, f v = 0) :
    ∑ i ∈ s, m i * ((∑ v ∈ A i, f v) ^ 2 - ∑ v ∈ A i, f v ^ 2) ≤ 0 := by
  obtain ⟨c, hc⟩ : ∃ c, c = ∑ v ∈ C, f v := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = ∑ v ∈ C, f v ^ 2 := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := hq ▸ Finset.sum_nonneg fun v _ => sq_nonneg (f v)
  have key : ∀ i ∈ s, (∑ v ∈ A i, f v) ^ 2 - ∑ v ∈ A i, f v ^ 2 =
      2 * c * ∑ v ∈ A i, f v - (c ^ 2 + q) := by
    intro i hi
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (hA i hi).2
    have e1 := Finset.sum_sdiff (hA i hi).1 (f := f)
    have e2 := Finset.sum_sdiff (hA i hi).1 (f := fun v => f v ^ 2)
    rw [hx, Finset.sum_singleton] at e1 e2
    rw [← e1, ← e2, ← hc, ← hq]
    ring
  calc ∑ i ∈ s, m i * ((∑ v ∈ A i, f v) ^ 2 - ∑ v ∈ A i, f v ^ 2)
      = ∑ i ∈ s, (2 * c * (m i * ∑ v ∈ A i, f v) - (c ^ 2 + q) * m i) :=
        Finset.sum_congr rfl fun i hi => by rw [key i hi]; ring
    _ = 2 * c * (∑ i ∈ s, m i * ∑ v ∈ A i, f v) - (c ^ 2 + q) * ∑ i ∈ s, m i := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 0 := by
        rw [hmean, mul_zero, zero_sub, neg_nonpos]
        exact mul_nonneg (by positivity) (Finset.sum_nonneg hm)

/-- **The quadratic form of a family of codimension-one subsets is nonpositive on mean-zero
functions.** Let the finite sets `A i` (`i ∈ s`) each be a set `T` with exactly one point removed,
distinct `i` giving distinct sets, with weights `m i ≥ 0`. If `Σ_i m i · Σ_{A i} f = 0`, then
`Σ_i m i ((Σ_{A i} f)² − Σ_{A i} f²) ≤ 0`.

With `t = Σ_T f`, `y_i` the point of `T` missing from `A i` and `g i = f(y_i)`, the sum is
`2 Σ m g² − M t² − M Σ_T f²` (`M = Σ m`, and `M t = Σ m g` by the mean-zero condition), and
`two_mul_sum_mul_sum_mul_sq_le` together with `Σ_i g i² ≤ Σ_T f²` shows it is `≤ 0`.

The distinctness hypothesis `hinj` is what gives `Σ_i g i² ≤ Σ_T f²` (the `y_i` are distinct). It
is not needed for the conclusion itself, which only depends on the total weight carried by each
distinct set, but it holds in the application (distinct top faces through `σ` have distinct
`F \ σ`). `T` may have any size; only the shape "`T` minus one point" matters. -/
theorem sum_mul_sq_sub_le_zero_of_codim_one (s : Finset α) (m : α → ℝ) (A : α → Finset ι)
    (T : Finset ι) (f : ι → ℝ) (hm : ∀ i ∈ s, 0 ≤ m i)
    (hA : ∀ i ∈ s, A i ⊆ T ∧ #(T \ A i) = 1) (hinj : ∀ i ∈ s, ∀ j ∈ s, A i = A j → i = j)
    (hmean : ∑ i ∈ s, m i * ∑ v ∈ A i, f v = 0) :
    ∑ i ∈ s, m i * ((∑ v ∈ A i, f v) ^ 2 - ∑ v ∈ A i, f v ^ 2) ≤ 0 := by
  obtain ⟨t, ht⟩ : ∃ t, t = ∑ v ∈ T, f v := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = ∑ v ∈ T, f v ^ 2 := ⟨_, rfl⟩
  -- `g i` is the value of `f` at the point of `T` missing from `A i`
  set g : α → ℝ := fun i => ∑ v ∈ T \ A i, f v with hg
  have hS : ∀ i ∈ s, ∑ v ∈ A i, f v = t - g i := by
    intro i hi
    have e := Finset.sum_sdiff (hA i hi).1 (f := f)
    rw [ht, ← e]
    ring
  have hS2 : ∀ i ∈ s, ∑ v ∈ A i, f v ^ 2 = P - g i ^ 2 := by
    intro i hi
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (hA i hi).2
    have e := Finset.sum_sdiff (hA i hi).1 (f := fun v => f v ^ 2)
    rw [hy, Finset.sum_singleton] at e
    simp only [hg, hy, Finset.sum_singleton]
    rw [hP, ← e]
    ring
  -- the missing points are distinct, so `Σ g i² ≤ Σ_T f²`
  have hG : ∑ i ∈ s, g i ^ 2 ≤ P := by
    have hdisj : (s : Set α).PairwiseDisjoint fun i => T \ A i := by
      intro i hi j hj hij
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro v hvi hvj
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (hA i hi).2
      obtain ⟨y', hy'⟩ := Finset.card_eq_one.mp (hA j hj).2
      rw [hy, Finset.mem_singleton] at hvi
      rw [hy', Finset.mem_singleton] at hvj
      refine hij (hinj i hi j hj ?_)
      rw [← Finset.sdiff_sdiff_eq_self (hA i hi).1, ← Finset.sdiff_sdiff_eq_self (hA j hj).1,
        hy, hy', ← hvi, ← hvj]
    have e : ∑ i ∈ s, g i ^ 2 = ∑ v ∈ s.biUnion fun i => T \ A i, f v ^ 2 := by
      rw [Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl fun i hi => ?_
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (hA i hi).2
      simp only [hg, hy, Finset.sum_singleton]
    rw [e, hP]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.biUnion_subset.mpr fun i _ => Finset.sdiff_subset) fun v _ _ => sq_nonneg _
  obtain ⟨M, hM⟩ : ∃ M, M = ∑ i ∈ s, m i := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM ▸ Finset.sum_nonneg hm
  have hmean' : M * t = ∑ i ∈ s, m i * g i := by
    have e : ∑ i ∈ s, m i * ∑ v ∈ A i, f v = M * t - ∑ i ∈ s, m i * g i := by
      rw [hM, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i hi => by rw [hS i hi]; ring
    linarith
  have hgoal : ∑ i ∈ s, m i * ((∑ v ∈ A i, f v) ^ 2 - ∑ v ∈ A i, f v ^ 2) =
      2 * ∑ i ∈ s, m i * g i ^ 2 - M * t ^ 2 - M * P := by
    have e : ∑ i ∈ s, m i * ((∑ v ∈ A i, f v) ^ 2 - ∑ v ∈ A i, f v ^ 2) =
        ∑ i ∈ s, (t ^ 2 * m i - 2 * t * (m i * g i) + 2 * (m i * g i ^ 2) - P * m i) :=
      Finset.sum_congr rfl fun i hi => by rw [hS i hi, hS2 i hi]; ring
    rw [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hM, ← hmean']
    ring
  rw [hgoal]
  have hkey := two_mul_sum_mul_sum_mul_sq_le s m g hm
  rw [← hM, ← hmean'] at hkey
  -- `Σ m g² ≤ M · Σ g²`, which settles `M = 0`
  have hH : ∑ i ∈ s, m i * g i ^ 2 ≤ M * ∑ i ∈ s, g i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
      (hM ▸ Finset.single_le_sum hm hi) (sq_nonneg _)
  have hG0 : 0 ≤ ∑ i ∈ s, g i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hM0.eq_or_lt with h0 | hpos
  · rw [← h0] at hH ⊢
    nlinarith
  · have h1 : M * (2 * ∑ i ∈ s, m i * g i ^ 2 - M * t ^ 2 - M * P) ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_left hG (sq_nonneg M)]
    by_contra hcon
    push Not at hcon
    nlinarith [mul_pos hpos hcon]

/-- **Cliques of the Johnson graph.** A family of `(k + 1)`-element sets, any two distinct members
of which share exactly `k` elements, is a sunflower (all members contain a common set `C`, with
exactly one further element each) or lies in a common set `T`, each member missing exactly one
element of `T`.

Then `#C = k` and `#T = k + 2` as soon as the family is nonempty. Degenerate cases: the empty
family is a sunflower with `C = ∅`; a single set `A` is a sunflower with `C` any `k`-subset; two
distinct sets are of both kinds; for `k = 0` (singletons) the family is always a sunflower with
`C = ∅`. The family may be infinite (it is given by a predicate `P`). -/
theorem Finset.sunflower_or_subset_of_card_inter {P : Finset ι → Prop} {k : ℕ}
    (hcard : ∀ A, P A → #A = k + 1) (hint : ∀ A B, P A → P B → A ≠ B → #(A ∩ B) = k) :
    (∃ C, ∀ A, P A → C ⊆ A ∧ #(A \ C) = 1) ∨ (∃ T, ∀ A, P A → A ⊆ T ∧ #(T \ A) = 1) := by
  by_cases h2 : ∃ A B, P A ∧ P B ∧ A ≠ B
  · obtain ⟨A, B, hA, hB, hAB⟩ := h2
    have hAc := hcard A hA
    have hBc := hcard B hB
    have hABc := hint A B hA hB hAB
    have hTc : #(A ∪ B) = k + 2 := by
      have := Finset.card_union_add_card_inter A B
      omega
    -- a member that misses a point `c` of `A ∩ B` is `(A ∪ B) \ {c}`
    have hD : ∀ D, P D → ∀ c ∈ A ∩ B, c ∉ D → D = (A ∪ B).erase c := by
      intro D hD c hc hcD
      have hcA := (Finset.mem_inter.mp hc).1
      have hcB := (Finset.mem_inter.mp hc).2
      have hDA : D ≠ A := fun h => hcD (h ▸ hcA)
      have hDB : D ≠ B := fun h => hcD (h ▸ hcB)
      have h1 : D ∩ A = A.erase c := by
        refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
        · obtain ⟨hxD, hxA⟩ := Finset.mem_inter.mp hx
          exact Finset.mem_erase.mpr ⟨fun h => hcD (h ▸ hxD), hxA⟩
        · rw [Finset.card_erase_of_mem hcA, hint D A hD hA hDA]
          omega
      have h2 : D ∩ B = B.erase c := by
        refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
        · obtain ⟨hxD, hxB⟩ := Finset.mem_inter.mp hx
          exact Finset.mem_erase.mpr ⟨fun h => hcD (h ▸ hxD), hxB⟩
        · rw [Finset.card_erase_of_mem hcB, hint D B hD hB hDB]
          omega
      have hsub : (A ∪ B).erase c ⊆ D := by
        intro x hx
        rw [Finset.mem_erase, Finset.mem_union] at hx
        rcases hx.2 with h | h
        · have h' : x ∈ A.erase c := Finset.mem_erase.mpr ⟨hx.1, h⟩
          rw [← h1] at h'
          exact (Finset.mem_inter.mp h').1
        · have h' : x ∈ B.erase c := Finset.mem_erase.mpr ⟨hx.1, h⟩
          rw [← h2] at h'
          exact (Finset.mem_inter.mp h').1
      refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
      rw [hcard D hD, Finset.card_erase_of_mem (Finset.mem_union_left _ hcA), hTc]
      omega
    by_cases hall : ∀ D, P D → A ∩ B ⊆ D
    · left
      refine ⟨A ∩ B, fun D hD => ⟨hall D hD, ?_⟩⟩
      rw [Finset.card_sdiff_of_subset (hall D hD), hcard D hD, hABc]
      omega
    · right
      push Not at hall
      obtain ⟨D0, hD0, hnot⟩ := hall
      obtain ⟨c, hc, hcD0⟩ := Finset.not_subset.mp hnot
      have hD0eq := hD D0 hD0 c hc hcD0
      have hk : 1 ≤ k := by
        rw [← hABc]
        exact Finset.card_pos.mpr ⟨c, hc⟩
      refine ⟨A ∪ B, fun E hE => ?_⟩
      have hET : E ⊆ A ∪ B := by
        by_contra hET
        obtain ⟨e, he, heT⟩ := Finset.not_subset.mp hET
        have hCE : A ∩ B ⊆ E := by
          by_contra hCE
          obtain ⟨c', hc', hc'E⟩ := Finset.not_subset.mp hCE
          exact hET (hD E hE c' hc' hc'E ▸ Finset.erase_subset _ _)
        have hED0 : E ≠ D0 := by
          rintro rfl
          rw [hD0eq] at he
          exact heT (Finset.mem_of_mem_erase he)
        -- `E ∩ D0` misses both `e` and `c`, so it is too small
        have hsub : E ∩ D0 ⊆ (E.erase e).erase c := by
          intro x hx
          obtain ⟨hxE, hxD⟩ := Finset.mem_inter.mp hx
          rw [hD0eq] at hxD
          refine Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hxD).1,
            Finset.mem_erase.mpr ⟨?_, hxE⟩⟩
          rintro rfl
          exact heT (Finset.mem_erase.mp hxD).2
        have hcE : c ∈ E := hCE hc
        have hce : c ≠ e := fun h =>
          heT (h ▸ Finset.mem_union_left _ (Finset.mem_inter.mp hc).1)
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hce, hcE⟩),
          Finset.card_erase_of_mem he, hcard E hE, hint E D0 hE hD0 hED0] at this
        omega
      refine ⟨hET, ?_⟩
      rw [Finset.card_sdiff_of_subset hET, hTc, hcard E hE]
      omega
  · push Not at h2
    by_cases h1 : ∃ A, P A
    · obtain ⟨A, hA⟩ := h1
      obtain ⟨x, hx⟩ : A.Nonempty := Finset.card_pos.mp (by rw [hcard A hA]; omega)
      left
      refine ⟨A.erase x, fun D hD => ?_⟩
      rw [h2 D A hD hA]
      refine ⟨Finset.erase_subset _ _, ?_⟩
      rw [Finset.card_sdiff_of_subset (Finset.erase_subset _ _), Finset.card_erase_of_mem hx]
      have := hcard A hA
      omega
    · left
      exact ⟨∅, fun D hD => absurd ⟨D, hD⟩ h1⟩

end Algebra

namespace PreAbstractSimplicialComplex

variable [DecidableEq ι] (K : PreAbstractSimplicialComplex ι)

/-! ### Matroid complexes and the matching condition -/

/-- `K` is a **matroid complex**: the faces of `K`, together with `∅`, satisfy the augmentation
axiom of the independent sets of a matroid. Whenever `σ` is `∅` or a face, `τ` is a face and
`|σ| < |τ|`, some `x ∈ τ \ σ` has `σ ∪ {x}` a face. (The hereditary axiom holds for every complex:
faces are closed under nonempty subsets.)

The complex with no faces is a matroid complex (of the matroid of loops). -/
def IsMatroidComplex : Prop :=
  ∀ σ τ : Finset ι, (σ = ∅ ∨ σ ∈ K) → τ ∈ K → #σ < #τ → ∃ x ∈ τ, x ∉ σ ∧ insert x σ ∈ K

/-- The links of the `(d − 2)`-dimensional faces have **no two disjoint edges** (matching number
at most `1`): for every `σ` with `|σ| = d − 1` that is a face, or is `∅` (which happens only for
`d = 1`, when the link is `K` itself), no two disjoint `2`-element faces of the link of `σ` exist.

In a pure `d`-complex every such link of a face has an edge, so the condition says that every link
of a `(d − 2)`-face has matching number exactly `1`: it is a star `K_{1,t}` or a triangle `K_3`.
For `d = 0` no `σ` has `|σ| + 1 = 0` and the condition is vacuous. -/
def NoTwoDisjointLinkEdges (d : ℕ) : Prop :=
  ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 = d →
    ∀ e ∈ K.link σ, ∀ e' ∈ K.link σ, #e = 2 → #e' = 2 → ¬ Disjoint e e'

variable {K} {d : ℕ} {m : Finset ι → ℝ}

/-- Two distinct sets with `d + 1` elements share at most `d` elements. -/
theorem card_inter_le_of_ne {F G : Finset ι} (hF : #F = d + 1) (hG : #G = d + 1) (hFG : F ≠ G) :
    #(F ∩ G) ≤ d := by
  by_contra h
  have h1 : F ∩ G = F := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have h2 : F ⊆ G := h1 ▸ Finset.inter_subset_right
  exact hFG (Finset.eq_of_subset_of_card_le h2 (by omega))

/-! ### (a) ⇒ (b): one explicit weight -/

section Fin

variable [Fintype ι]

/-- **A bad weight for two far-apart top faces.** Let `K` be pure of dimension `d`, and let `F, G`
be top faces meeting in a set `σ = F ∩ G` with `|σ| ≤ d − 1`. Then some top weight `m` of `K`
makes the link of `σ` fail the second-eigenvalue bound `0`.

The weight is `1` on every top face, plus `t` on `F` and on `G`, where `t − 1` is the total weight
`W(A, B) + W(B, A)` of the edges of the link of `σ` between `A = F \ σ` and `B = G \ σ` for the
uniform weight. The test function is `D(B) · 1_A − D(A) · 1_B`
(`WalkSecondEigenvalueLE.sq_mul_add_sq_mul_le_of_zero`): the edges inside `A` and inside `B` have
weight at least `t`, and the edges between them do not see `t`.

`σ = ∅` is allowed (then `F, G` are disjoint and the link is `K` itself), and `σ` is then `∅` or a
face, so it is one of the links that `IsLocalSpectralExpanderOf` tests. The hypothesis forces
`d ≥ 1` and `F ≠ G`. No connectivity, matroid or vertex hypothesis is used. -/
theorem exists_isTopWeight_not_walkSecondEigenvalueLE_zero (hpure : K.IsPure d)
    {F G : Finset ι} (hF : F ∈ K) (hG : G ∈ K) (hFc : #F = d + 1) (hGc : #G = d + 1)
    (hlt : #(F ∩ G) + 1 ≤ d) :
    ∃ m, K.IsTopWeight d m ∧ ¬ WalkSecondEigenvalueLE (linkWeightOf m (F ∩ G)) 0 := by
  set σ := F ∩ G with hσ
  -- indicators of `F \ G` and `G \ F`
  set a : ι → ℝ := fun x => if x ∈ F ∧ x ∉ G then 1 else 0 with ha
  set b : ι → ℝ := fun x => if x ∈ G ∧ x ∉ F then 1 else 0 with hb
  have ha0 : ∀ x, 0 ≤ a x := fun x => by simp only [ha]; split_ifs <;> norm_num
  have hb0 : ∀ x, 0 ≤ b x := fun x => by simp only [hb]; split_ifs <;> norm_num
  set wu := linkWeightOf (K.uniformWeight d) σ with hwu
  have hwu0 : ∀ x y, 0 ≤ wu x y := linkWeightOf_nonneg (K.uniformWeight_nonneg d) σ
  set X := (∑ x, ∑ y, wu x y * a x * b y) + ∑ x, ∑ y, wu x y * b x * a y with hX
  have hX0 : 0 ≤ X := add_nonneg
    (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (hwu0 x y) (ha0 x)) (hb0 y))
    (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (hwu0 x y) (hb0 x)) (ha0 y))
  set t := X + 1 with ht
  have ht0 : 0 < t := by linarith
  -- the weight: uniform, plus `t` on `F` and on `G`
  set m : Finset ι → ℝ := fun H => K.uniformWeight d H + if H = F ∨ H = G then t else 0 with hm
  have hmtop : K.IsTopWeight d m := by
    refine ⟨hpure, ⟨F, hF⟩, fun H hH hc => ?_, fun H hH => ?_⟩
    · have h1 : K.uniformWeight d H = 1 := by rw [uniformWeight, if_pos ⟨hH, hc⟩]
      simp only [hm, h1]
      split_ifs <;> linarith
    · have h1 : K.uniformWeight d H = 0 := by rw [uniformWeight, if_neg hH]
      have h2 : ¬ (H = F ∨ H = G) := by
        rintro (rfl | rfl)
        · exact hH ⟨hF, hFc⟩
        · exact hH ⟨hG, hGc⟩
      simp only [hm, h1, if_neg h2, add_zero]
  refine ⟨m, hmtop, fun hw => ?_⟩
  set w := linkWeightOf m σ with hw'
  have hw0 : ∀ x y, 0 ≤ w x y := linkWeightOf_nonneg hmtop.nonneg σ
  -- across `F \ G` and `G \ F` the two weights agree
  have hcross : ∀ x y, (x ∉ G ∧ y ∉ F) ∨ (x ∉ F ∧ y ∉ G) → w x y = wu x y := by
    intro x y hxy
    simp only [hw', hwu, linkWeightOf]
    split_ifs with hc
    · unfold faceWeight
      refine Finset.sum_congr rfl fun H hH => ?_
      rw [Finset.mem_filter] at hH
      have hxH : x ∈ H := hH.2 (Finset.mem_insert_self _ _)
      have hyH : y ∈ H := hH.2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have hne' : ¬ (H = F ∨ H = G) := by
        rintro (rfl | rfl) <;> rcases hxy with h | h
        · exact h.2 hyH
        · exact h.1 hxH
        · exact h.1 hxH
        · exact h.2 hyH
      simp only [hm, if_neg hne', add_zero]
    · rfl
  have hQab : ∑ x, ∑ y, w x y * a x * b y = ∑ x, ∑ y, wu x y * a x * b y := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    by_cases hx : x ∈ F ∧ x ∉ G
    · by_cases hy : y ∈ G ∧ y ∉ F
      · rw [hcross x y (Or.inl ⟨hx.2, hy.2⟩)]
      · simp [hb, hy]
    · simp [ha, hx]
  have hQba : ∑ x, ∑ y, w x y * b x * a y = ∑ x, ∑ y, wu x y * b x * a y := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    by_cases hx : x ∈ G ∧ x ∉ F
    · by_cases hy : y ∈ F ∧ y ∉ G
      · rw [hcross x y (Or.inr ⟨hx.2, hy.2⟩)]
      · simp [ha, hy]
    · simp [hb, hx]
  -- inside `F \ G` (and inside `G \ F`) every edge has weight at least `t`
  have hinside : ∀ H, H = F ∨ H = G → ∀ x y, x ≠ y → x ∈ H \ σ → y ∈ H \ σ → t ≤ w x y := by
    intro H hH x y hxy hx hy
    rw [Finset.mem_sdiff] at hx hy
    have hc : x ≠ y ∧ x ∉ σ ∧ y ∉ σ := ⟨hxy, hx.2, hy.2⟩
    simp only [hw', linkWeightOf]
    rw [if_pos hc]
    have hσH : σ ⊆ H := by
      rcases hH with rfl | rfl
      · exact Finset.inter_subset_left
      · exact Finset.inter_subset_right
    have hle : m H ≤ faceWeight m (insert x (insert y σ)) := by
      unfold faceWeight
      refine Finset.single_le_sum (f := m) (fun H' _ => hmtop.nonneg H') ?_
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Finset.insert_subset hx.1 (Finset.insert_subset hy.1 hσH)⟩
    have hmH : t ≤ m H := by
      simp only [hm, if_pos hH]
      linarith [K.uniformWeight_nonneg d H]
    linarith
  -- two points in each of `F \ G` and `G \ F`
  have htwo : ∀ H, H = F ∨ H = G → ∃ x y, x ≠ y ∧ x ∈ H \ σ ∧ y ∈ H \ σ := by
    intro H hH
    have hσH : σ ⊆ H := by
      rcases hH with rfl | rfl
      · exact Finset.inter_subset_left
      · exact Finset.inter_subset_right
    have hHc : #H = d + 1 := by rcases hH with rfl | rfl <;> assumption
    have h2 : 1 < #(H \ σ) := by
      rw [Finset.card_sdiff_of_subset hσH, hHc]
      omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h2
    exact ⟨x, y, hxy, hx, hy⟩
  have hFσ : ∀ x, x ∈ F \ σ ↔ x ∈ F ∧ x ∉ G := fun x => by simp [hσ]
  have hGσ : ∀ x, x ∈ G \ σ ↔ x ∈ G ∧ x ∉ F := fun x => by simp [hσ]
  obtain ⟨a1, a2, ha12, ha1, ha2⟩ := htwo F (Or.inl rfl)
  obtain ⟨b1, b2, hb12, hb1, hb2⟩ := htwo G (Or.inr rfl)
  have haa : a a1 = 1 := by simp only [ha]; rw [if_pos ((hFσ a1).mp ha1)]
  have haa' : a a2 = 1 := by simp only [ha]; rw [if_pos ((hFσ a2).mp ha2)]
  have hbb : b b1 = 1 := by simp only [hb]; rw [if_pos ((hGσ b1).mp hb1)]
  have hbb' : b b2 = 1 := by simp only [hb]; rw [if_pos ((hGσ b2).mp hb2)]
  have hwa := hinside F (Or.inl rfl) a1 a2 ha12 ha1 ha2
  have hwb := hinside G (Or.inr rfl) b1 b2 hb12 hb1 hb2
  -- lower bounds: `Q(a, a) ≥ t`, `D(a) ≥ t`, and the same for `b`
  have hQaa : t ≤ ∑ x, ∑ y, w x y * a x * a y := by
    have h1 : w a1 a2 * a a1 * a a2 ≤ ∑ y, w a1 y * a a1 * a y :=
      Finset.single_le_sum (f := fun y => w a1 y * a a1 * a y)
        (fun y _ => mul_nonneg (mul_nonneg (hw0 _ _) (ha0 _)) (ha0 _)) (Finset.mem_univ _)
    have h2 : ∑ y, w a1 y * a a1 * a y ≤ ∑ x, ∑ y, w x y * a x * a y :=
      Finset.single_le_sum (f := fun x => ∑ y, w x y * a x * a y)
        (fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (mul_nonneg (hw0 _ _) (ha0 _))
          (ha0 _)) (Finset.mem_univ _)
    rw [haa, haa'] at h1
    rw [haa] at h2
    linarith
  have hQbb : t ≤ ∑ x, ∑ y, w x y * b x * b y := by
    have h1 : w b1 b2 * b b1 * b b2 ≤ ∑ y, w b1 y * b b1 * b y :=
      Finset.single_le_sum (f := fun y => w b1 y * b b1 * b y)
        (fun y _ => mul_nonneg (mul_nonneg (hw0 _ _) (hb0 _)) (hb0 _)) (Finset.mem_univ _)
    have h2 : ∑ y, w b1 y * b b1 * b y ≤ ∑ x, ∑ y, w x y * b x * b y :=
      Finset.single_le_sum (f := fun x => ∑ y, w x y * b x * b y)
        (fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (mul_nonneg (hw0 _ _) (hb0 _))
          (hb0 _)) (Finset.mem_univ _)
    rw [hbb, hbb'] at h1
    rw [hbb] at h2
    linarith
  have hdA : t ≤ ∑ x, (∑ y, w x y) * a x := by
    have h1 : w a1 a2 ≤ ∑ y, w a1 y := Finset.single_le_sum (fun y _ => hw0 a1 y) (mem_univ _)
    have h2 : (∑ y, w a1 y) * a a1 ≤ ∑ x, (∑ y, w x y) * a x :=
      Finset.single_le_sum (f := fun x => (∑ y, w x y) * a x)
        (fun x _ => mul_nonneg (Finset.sum_nonneg fun y _ => hw0 x y) (ha0 x)) (mem_univ _)
    rw [haa, mul_one] at h2
    linarith
  have hdB : t ≤ ∑ x, (∑ y, w x y) * b x := by
    have h1 : w b1 b2 ≤ ∑ y, w b1 y := Finset.single_le_sum (fun y _ => hw0 b1 y) (mem_univ _)
    have h2 : (∑ y, w b1 y) * b b1 ≤ ∑ x, (∑ y, w x y) * b x :=
      Finset.single_le_sum (f := fun x => (∑ y, w x y) * b x)
        (fun x _ => mul_nonneg (Finset.sum_nonneg fun y _ => hw0 x y) (hb0 x)) (mem_univ _)
    rw [hbb, mul_one] at h2
    linarith
  have hmain := hw.sq_mul_add_sq_mul_le_of_zero a b
  rw [hQab, hQba, ← hX] at hmain
  obtain ⟨dA, hdA'⟩ : ∃ x, x = ∑ x, (∑ y, w x y) * a x := ⟨_, rfl⟩
  obtain ⟨dB, hdB'⟩ : ∃ x, x = ∑ x, (∑ y, w x y) * b x := ⟨_, rfl⟩
  rw [← hdA', ← hdB'] at hmain
  rw [← hdA'] at hdA
  rw [← hdB'] at hdB
  have hpA : 0 < dA := by linarith
  have hpB : 0 < dB := by linarith
  have h3 : t * (dA ^ 2 + dB ^ 2) ≤ dA * dB * X := by
    nlinarith [mul_le_mul_of_nonneg_left hQaa (sq_nonneg dB),
      mul_le_mul_of_nonneg_left hQbb (sq_nonneg dA)]
  have h4 : 2 * t * (dA * dB) ≤ X * (dA * dB) := by nlinarith [sq_nonneg (dA - dB)]
  have h5 := le_of_mul_le_mul_right h4 (mul_pos hpA hpB)
  linarith

/-- **(a) ⇒ (b).** If `K`, pure of dimension `d`, is a `0`-local spectral expander for every top
weight, then any two distinct top faces share exactly `d` vertices.

Only purity is assumed: a non-pure complex has no top weight, so the hypothesis would hold
vacuously while the conclusion can fail. If `K` has no faces the conclusion is vacuous. `d ≥ 1` is
not needed: for `d = 0` distinct top faces are distinct singletons and the conclusion
`#(F ∩ G) = 0` holds for every complex. In fact a single weight per pair of faces is used, see
`exists_isTopWeight_not_walkSecondEigenvalueLE_zero`. -/
theorem forall_card_inter_of_forall_isLocalSpectralExpanderOf_zero (hpure : K.IsPure d)
    (h : ∀ m, K.IsTopWeight d m → K.IsLocalSpectralExpanderOf d m 0) :
    ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F ≠ G → #(F ∩ G) = d := by
  intro F hF G hG hFc hGc hFG
  have hle := card_inter_le_of_ne hFc hGc hFG
  by_contra hne
  obtain ⟨m, hm, hnot⟩ :=
    exists_isTopWeight_not_walkSecondEigenvalueLE_zero hpure hF hG hFc hGc (by omega)
  have hσ : F ∩ G = ∅ ∨ F ∩ G ∈ K := by
    rcases (F ∩ G).eq_empty_or_nonempty with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (K.mem_of_subset hF Finset.inter_subset_left h0)
  exact hnot ((h m hm).walkSecondEigenvalueLE hσ (by omega))

/-! ### (b) ⇒ (a): every link, every weight -/

/-- **(b) ⇒ (a), for one link.** If any two distinct top faces of `K` share exactly `d` vertices,
then for every top weight `m` and **every** set `σ`, the weighted graph of the link of `σ` has
random-walk second eigenvalue at most `0`.

No restriction on `σ` is needed. For `|σ| ≥ d` the link has no edges and the bound is vacuous;
for a nonempty `σ` that is not a face the link is empty as well. For the other `σ` the sets
`F \ σ` of the top faces `F ⊇ σ` form a clique of a Johnson graph, so they are a sunflower or lie
in a common set (`Finset.sunflower_or_subset_of_card_inter`); the two cases are
`sum_mul_sq_sub_le_zero_of_sunflower` and `sum_mul_sq_sub_le_zero_of_codim_one`. No connectivity
hypothesis and no trickling down is used. -/
theorem IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_zero (hm : K.IsTopWeight d m)
    (hb : ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F ≠ G → #(F ∩ G) = d) (σ : Finset ι) :
    WalkSecondEigenvalueLE (linkWeightOf m σ) 0 := by
  by_cases hσ : #σ + 1 ≤ d
  swap
  · exact walkSecondEigenvalueLE_of_forall_eq_zero
      (fun u v => linkWeightOf_eq_zero_of_le_card hm.card_eq_of_ne_zero (by omega) u v) 0
  intro f hf
  have hℓ : (0 : ℝ) < (d : ℝ) - #σ := by
    have h : ((#σ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hσ
    push_cast at h
    linarith
  -- the mean-zero condition, face by face
  have hmean : ∑ F with σ ⊆ F, m F * ∑ v ∈ F \ σ, f v = 0 := by
    have e : ∑ u, (∑ v, linkWeightOf m σ u v) * f u =
        ((d : ℝ) - #σ) * ∑ u, (if u ∈ σ then 0 else faceWeight m (insert u σ)) * f u := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [sum_linkWeightOf hm.card_eq_of_ne_zero]
      split_ifs <;> ring
    rw [e, sum_faceWeight_insert_mul] at hf
    exact (mul_eq_zero.mp hf).resolve_left hℓ.ne'
  rw [sum_linkWeightOf_mul_mul, zero_mul]
  -- restrict to the top faces through `σ`
  have hsupp : ∀ (g : Finset ι → ℝ), ∑ F with σ ⊆ F, m F * g F =
      ∑ F ∈ {F | σ ⊆ F} with m F ≠ 0, m F * g F := fun g =>
    (Finset.sum_filter_of_ne fun F _ h => left_ne_zero_of_mul h).symm
  rw [hsupp] at hmean ⊢
  set s := ({F | σ ⊆ F} : Finset (Finset ι)).filter (fun F => m F ≠ 0) with hs
  have hmem : ∀ F ∈ s, σ ⊆ F ∧ m F ≠ 0 := fun F hF => by
    rw [hs, Finset.mem_filter, Finset.mem_filter] at hF
    exact ⟨hF.1.2, hF.2⟩
  have hm0 : ∀ F ∈ s, 0 ≤ m F := fun F _ => hm.nonneg F
  -- the sets `F \ σ` of the top faces through `σ` pairwise share `d − |σ|` points
  have hcl := Finset.sunflower_or_subset_of_card_inter
    (P := fun A => ∃ F, σ ⊆ F ∧ m F ≠ 0 ∧ A = F \ σ) (k := d - #σ)
    (by
      rintro A ⟨F, hσF, hmF, rfl⟩
      rw [Finset.card_sdiff_of_subset hσF, hm.card_eq_of_ne_zero F hmF]
      omega)
    (by
      rintro A B ⟨F, hσF, hmF, rfl⟩ ⟨G, hσG, hmG, rfl⟩ hAB
      have hFG : F ≠ G := by rintro rfl; exact hAB rfl
      have e : (F \ σ) ∩ (G \ σ) = (F ∩ G) \ σ := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_sdiff]
        tauto
      rw [e, Finset.card_sdiff_of_subset (Finset.subset_inter hσF hσG),
        hb F (hm.mem_of_ne_zero hmF) G (hm.mem_of_ne_zero hmG) (hm.card_eq_of_ne_zero F hmF)
          (hm.card_eq_of_ne_zero G hmG) hFG])
  rcases hcl with ⟨C, hC⟩ | ⟨T, hT⟩
  · exact sum_mul_sq_sub_le_zero_of_sunflower s m (fun F => F \ σ) C f hm0
      (fun F hF => hC _ ⟨F, (hmem F hF).1, (hmem F hF).2, rfl⟩) hmean
  · refine sum_mul_sq_sub_le_zero_of_codim_one s m (fun F => F \ σ) T f hm0
      (fun F hF => hT _ ⟨F, (hmem F hF).1, (hmem F hF).2, rfl⟩) (fun F hF G hG hFG => ?_) hmean
    rw [← Finset.sdiff_union_of_subset (hmem F hF).1,
      ← Finset.sdiff_union_of_subset (hmem G hG).1]
    exact congrArg (· ∪ σ) hFG

/-- **(b) ⇒ (a).** If any two distinct top faces of `K` share exactly `d` vertices and `d ≥ 1`,
then `K` is a `0`-local spectral expander for every top weight.

Purity and the existence of a face are part of `IsTopWeight`, so they are not assumed. `d ≥ 1` is
needed: no complex is a `0`-dimensional expander (`not_isLocalSpectralExpanderOf_zero`), while a
set of vertices satisfies the hypothesis vacuously. -/
theorem forall_isLocalSpectralExpanderOf_zero_of_forall_card_inter (hd : 1 ≤ d)
    (hb : ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F ≠ G → #(F ∩ G) = d) :
    ∀ m, K.IsTopWeight d m → K.IsLocalSpectralExpanderOf d m 0 :=
  fun _ hm => ⟨hd, hm, fun σ _ _ => hm.walkSecondEigenvalueLE_linkWeightOf_zero hb σ⟩

/-- **(a) ⇔ (b).** For `d ≥ 1` and `K` pure of dimension `d`, `K` is a `0`-local spectral
expander for every top weight exactly when any two distinct top faces share exactly `d` vertices.

Degenerate cases: for `d = 0` the left side fails for every complex with a face (and holds
vacuously for the complex with no faces), while the right side holds for every set of vertices; a
complex with no faces satisfies both sides vacuously; a non-pure complex has no top weights, so
the left side holds vacuously, which is why purity is assumed. -/
theorem forall_isLocalSpectralExpanderOf_zero_iff (hd : 1 ≤ d) (hpure : K.IsPure d) :
    (∀ m, K.IsTopWeight d m → K.IsLocalSpectralExpanderOf d m 0) ↔
      ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F ≠ G → #(F ∩ G) = d :=
  ⟨forall_card_inter_of_forall_isLocalSpectralExpanderOf_zero hpure,
    forall_isLocalSpectralExpanderOf_zero_of_forall_card_inter hd⟩

end Fin

/-! ### (b) ⇔ (c): sunflowers and codimension-one families -/

/-- **(b) ⇒ (c).** If any two distinct top faces share `d` vertices and some top face exists,
then all top faces contain a common `d`-set, or all lie in a common `(d + 2)`-set.

The existence of a top face is needed for the cardinalities: with no top faces, (b) holds and (c)
can fail when `ι` has fewer than `d` points. A complex with a single top face satisfies the first
alternative (and the second as well when `ι` has at least `d + 2` points). -/
theorem sunflower_or_subset_of_forall_card_inter (htop : ∃ F ∈ K, #F = d + 1)
    (hb : ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F ≠ G → #(F ∩ G) = d) :
    (∃ D : Finset ι, #D = d ∧ ∀ F ∈ K, #F = d + 1 → D ⊆ F) ∨
      (∃ T : Finset ι, #T = d + 2 ∧ ∀ F ∈ K, #F = d + 1 → F ⊆ T) := by
  obtain ⟨F0, hF0, hF0c⟩ := htop
  rcases Finset.sunflower_or_subset_of_card_inter (P := fun F => F ∈ K ∧ #F = d + 1) (k := d)
    (fun F hF => hF.2) (fun F G hF hG hFG => hb F hF.1 G hG.1 hF.2 hG.2 hFG) with
    ⟨C, hC⟩ | ⟨T, hT⟩
  · left
    refine ⟨C, ?_, fun F hF hFc => (hC F ⟨hF, hFc⟩).1⟩
    have h := (hC F0 ⟨hF0, hF0c⟩).2
    rw [Finset.card_sdiff_of_subset (hC F0 ⟨hF0, hF0c⟩).1, hF0c] at h
    have := Finset.card_le_card (hC F0 ⟨hF0, hF0c⟩).1
    omega
  · right
    refine ⟨T, ?_, fun F hF hFc => (hT F ⟨hF, hFc⟩).1⟩
    have h := (hT F0 ⟨hF0, hF0c⟩).2
    rw [Finset.card_sdiff_of_subset (hT F0 ⟨hF0, hF0c⟩).1, hF0c] at h
    omega

/-- **(c) ⇒ (b).** If all top faces contain a common `d`-set, or all lie in a common
`(d + 2)`-set, then any two distinct top faces share exactly `d` vertices. No hypothesis on `K`
or `d`. -/
theorem forall_card_inter_of_sunflower_or_subset
    (hc : (∃ D : Finset ι, #D = d ∧ ∀ F ∈ K, #F = d + 1 → D ⊆ F) ∨
      (∃ T : Finset ι, #T = d + 2 ∧ ∀ F ∈ K, #F = d + 1 → F ⊆ T)) :
    ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F ≠ G → #(F ∩ G) = d := by
  rcases hc with ⟨D, hD, hDF⟩ | ⟨T, hT, hTF⟩ <;> intro F hF G hG hFc hGc hFG
  · have h1 := Finset.card_le_card (Finset.subset_inter (hDF F hF hFc) (hDF G hG hGc))
    have h2 := card_inter_le_of_ne hFc hGc hFG
    omega
  · have h1 := Finset.card_le_card (Finset.union_subset (hTF F hF hFc) (hTF G hG hGc))
    have h2 := Finset.card_union_add_card_inter F G
    have h3 := card_inter_le_of_ne hFc hGc hFG
    omega

/-- **(b) ⇔ (c)** for a pure complex with a face: the Johnson clique classification. -/
theorem forall_card_inter_iff_sunflower_or_subset (hpure : K.IsPure d) (hne : ∃ F, F ∈ K) :
    (∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F ≠ G → #(F ∩ G) = d) ↔
      ((∃ D : Finset ι, #D = d ∧ ∀ F ∈ K, #F = d + 1 → D ⊆ F) ∨
        (∃ T : Finset ι, #T = d + 2 ∧ ∀ F ∈ K, #F = d + 1 → F ⊆ T)) :=
  ⟨sunflower_or_subset_of_forall_card_inter (hpure.exists_card_eq hne),
    forall_card_inter_of_sunflower_or_subset⟩

/-! ### (b) ⇔ (d): matroid complexes -/

/-- Two top faces meeting in `d − 1` points give two disjoint edges in the link of their
intersection, so they cannot exist under `NoTwoDisjointLinkEdges`. For `d = 1` the faces are
disjoint edges of `K`. -/
theorem NoTwoDisjointLinkEdges.not_card_inter_add_one_eq (h : K.NoTwoDisjointLinkEdges d)
    {F G : Finset ι} (hF : F ∈ K) (hG : G ∈ K) (hFc : #F = d + 1) (hGc : #G = d + 1)
    (hFG : #(F ∩ G) + 1 = d) : False := by
  have hσ : F ∩ G = ∅ ∨ F ∩ G ∈ K := by
    rcases (F ∩ G).eq_empty_or_nonempty with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (K.mem_of_subset hF Finset.inter_subset_left h0)
  have hcF : #(F \ G) = 2 := by
    rw [Finset.card_sdiff, Finset.inter_comm, hFc]
    omega
  have hcG : #(G \ F) = 2 := by
    rw [Finset.card_sdiff, hGc]
    omega
  have heF : F \ G ∈ K.link (F ∩ G) := mem_link.mpr ⟨Finset.card_pos.mp (by omega),
    Finset.disjoint_sdiff_inter F G, by rw [Finset.sdiff_union_inter]; exact hF⟩
  have heG : G \ F ∈ K.link (F ∩ G) := by
    refine mem_link.mpr ⟨Finset.card_pos.mp (by omega), ?_, ?_⟩
    · rw [Finset.inter_comm]
      exact Finset.disjoint_sdiff_inter G F
    · rw [Finset.inter_comm, Finset.sdiff_union_inter]
      exact hG
  exact h (F ∩ G) hσ hFG _ heF _ heG hcF hcG disjoint_sdiff_sdiff

/-- **(b) ⇒ the matching condition.** If any two distinct top faces share `d` vertices, the link
of a `(d − 2)`-face (or of `∅`, for `d = 1`) has no two disjoint edges: two such edges, with the
face, would be top faces meeting in `d − 1` points. No hypothesis on `K` or `d`. -/
theorem noTwoDisjointLinkEdges_of_forall_card_inter
    (hb : ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F ≠ G → #(F ∩ G) = d) :
    K.NoTwoDisjointLinkEdges d := by
  intro σ _ hσc e he e' he' hec he'c hdisj
  obtain ⟨-, heσ, heK⟩ := mem_link.mp he
  obtain ⟨-, he'σ, he'K⟩ := mem_link.mp he'
  have hc1 : #(e ∪ σ) = d + 1 := by rw [Finset.card_union_of_disjoint heσ]; omega
  have hc2 : #(e' ∪ σ) = d + 1 := by rw [Finset.card_union_of_disjoint he'σ]; omega
  have hne : e ∪ σ ≠ e' ∪ σ := by
    intro h
    have h' : e = e' := by
      rw [← Finset.union_sdiff_cancel_right heσ, h, Finset.union_sdiff_cancel_right he'σ]
    subst h'
    rw [disjoint_self, Finset.bot_eq_empty] at hdisj
    rw [hdisj, Finset.card_empty] at hec
    omega
  have hsub : (e ∪ σ) ∩ (e' ∪ σ) ⊆ σ := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_union] at hx
    rcases hx with ⟨h1 | h1, h2 | h2⟩
    · exact absurd h2 (Finset.disjoint_left.mp hdisj h1)
    · exact h2
    · exact h1
    · exact h1
  have := Finset.card_le_card hsub
  have := hb _ heK _ he'K hc1 hc2 hne
  omega

/-- **(b) ⇒ matroid.** If `K` is pure of dimension `d` and any two distinct top faces share `d`
vertices, then `K` is a matroid complex. Given `σ` (a face or `∅`) and a larger face `τ`, a point
of `τ \ σ` inside a top face through `σ` augments `σ`; if there is none, `τ \ σ` lies in the single
point by which a top face through `τ` differs from one through `σ`, and then `τ = σ ∪ {that
point}`. `d` is arbitrary. -/
theorem isMatroidComplex_of_forall_card_inter (hpure : K.IsPure d)
    (hb : ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F ≠ G → #(F ∩ G) = d) :
    K.IsMatroidComplex := by
  intro σ τ hσ hτ hlt
  obtain ⟨z0, hz0⟩ : (τ \ σ).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset]
    intro h
    exact absurd (Finset.card_le_card h) (by omega)
  rcases hσ with rfl | hσK
  · refine ⟨z0, (Finset.mem_sdiff.mp hz0).1, Finset.notMem_empty _, ?_⟩
    rw [insert_empty]
    exact K.mem_of_subset hτ (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hz0).1)
      (Finset.singleton_nonempty _)
  obtain ⟨-, F, hF, hσF, hFc⟩ := hpure σ hσK
  obtain ⟨-, G, hG, hτG, hGc⟩ := hpure τ hτ
  by_cases hz : ∃ z ∈ τ \ σ, z ∈ F
  · obtain ⟨z, hz, hzF⟩ := hz
    exact ⟨z, (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2,
      K.mem_of_subset hF (Finset.insert_subset hzF hσF) (Finset.insert_nonempty _ _)⟩
  push Not at hz
  have hsub : τ \ σ ⊆ G \ F := fun z hz' =>
    Finset.mem_sdiff.mpr ⟨hτG (Finset.mem_sdiff.mp hz').1, hz z hz'⟩
  have hFG : F ≠ G := by
    rintro rfl
    exact (Finset.mem_sdiff.mp (hsub hz0)).2 (Finset.mem_sdiff.mp (hsub hz0)).1
  have hGF : #(G \ F) = 1 := by
    rw [Finset.card_sdiff, hGc, hb F hF G hG hFc hGc hFG]
    omega
  have hone : ∀ x ∈ τ \ σ, x = z0 := fun x hx =>
    Finset.card_le_one.mp (hGF ▸ Finset.card_le_card hsub) x hx z0 hz0
  have hτsub : τ ⊆ insert z0 σ := by
    intro x hx
    by_cases hxσ : x ∈ σ
    · exact Finset.mem_insert_of_mem hxσ
    · rw [hone x (Finset.mem_sdiff.mpr ⟨hx, hxσ⟩)]
      exact Finset.mem_insert_self _ _
  have heq : τ = insert z0 σ := Finset.eq_of_subset_of_card_le hτsub
    (by rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hz0).2]; omega)
  exact ⟨z0, (Finset.mem_sdiff.mp hz0).1, (Finset.mem_sdiff.mp hz0).2, heq ▸ hτ⟩

/-- **(d) ⇒ (b).** In a matroid complex of dimension `d ≥ 1` whose `(d − 2)`-face links have no
two disjoint edges, any two distinct top faces share exactly `d` vertices. If two top faces met in
fewer than `d − 1` points, basis exchange (`F − x + y`, `x ∈ F \ G`, `y ∈ G`) would move one of
them a step closer to the other, down to two top faces meeting in exactly `d − 1` points, which
the matching condition excludes (`NoTwoDisjointLinkEdges.not_card_inter_add_one_eq`).

Purity is not assumed: the statement only concerns the faces with `d + 1` elements. `d ≥ 1` is used
so that `F \ {x}` is a face; for `d = 0` the matching condition is vacuous and two distinct
singletons share no point. -/
theorem forall_card_inter_of_isMatroidComplex (hd : 1 ≤ d) (hmat : K.IsMatroidComplex)
    (hmatch : K.NoTwoDisjointLinkEdges d) :
    ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F ≠ G → #(F ∩ G) = d := by
  intro F hF G hG hFc hGc hFG
  have hle := card_inter_le_of_ne hFc hGc hFG
  suffices h : d ≤ #(F ∩ G) by omega
  by_contra hlt
  push Not at hlt
  have key : ∀ j : ℕ, ∀ F', F' ∈ K → #F' = d + 1 → #(F' ∩ G) + 1 + j = d → False := by
    intro j
    induction j with
    | zero =>
      intro F' hF' hF'c hc
      exact hmatch.not_card_inter_add_one_eq hF' hG hF'c hGc (by omega)
    | succ j ih =>
      intro F' hF' hF'c hc
      obtain ⟨x, hx⟩ : (F' \ G).Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_sdiff, Finset.inter_comm, hF'c]
        omega)
      obtain ⟨hxF, hxG⟩ := Finset.mem_sdiff.mp hx
      have hσc : #(F'.erase x) = d := by rw [Finset.card_erase_of_mem hxF, hF'c]; omega
      have hσK : F'.erase x ∈ K :=
        K.mem_of_subset hF' (Finset.erase_subset _ _) (Finset.card_pos.mp (by omega))
      obtain ⟨y, hyG, hyσ, hyK⟩ := hmat _ G (Or.inr hσK) hG (by omega)
      have hyx : y ≠ x := fun h => hxG (h ▸ hyG)
      have hyF : y ∉ F' := fun h => hyσ (Finset.mem_erase.mpr ⟨hyx, h⟩)
      have hc' : #(insert y (F'.erase x)) = d + 1 := by
        rw [Finset.card_insert_of_notMem hyσ, hσc]
      have he : insert y (F'.erase x) ∩ G = insert y (F' ∩ G) := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨h1 | ⟨-, h1⟩, h2⟩
          · exact Or.inl h1
          · exact Or.inr ⟨h1, h2⟩
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨Or.inl rfl, hyG⟩
          · exact ⟨Or.inr ⟨fun h => hxG (h ▸ h2), h1⟩, h2⟩
      have hyFG : y ∉ F' ∩ G := fun h => hyF (Finset.mem_inter.mp h).1
      refine ih _ hyK hc' ?_
      rw [he, Finset.card_insert_of_notMem hyFG]
      omega
  exact key (d - 1 - #(F ∩ G)) F hF hFc (by omega)

/-! ### (b) ⇔ (d′): connected links -/

/-- A pair `u ≠ w` outside `σ` that lies, with `σ`, in a face is an edge of the link of `σ`. -/
private theorem link_adj_of_subset {σ H : Finset ι} (hH : H ∈ K) {u w : ι} (huw : u ≠ w)
    (hu : u ∉ σ) (hw : w ∉ σ) (hsub : insert u (insert w σ) ⊆ H)
    (hu' : u ∈ (K.link σ).vertices) (hw' : w ∈ (K.link σ).vertices) :
    ((K.link σ).oneSkeleton.induce (K.link σ).vertices).Adj ⟨u, hu'⟩ ⟨w, hw'⟩ := by
  rw [SimpleGraph.induce_adj, oneSkeleton, SimpleGraph.fromRel_adj]
  refine ⟨huw, Or.inl (mem_link.mpr ⟨Finset.insert_nonempty _ _, ?_, ?_⟩)⟩
  · rw [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    exact ⟨hu, hw⟩
  · refine K.mem_of_subset hH (fun x hx => hsub ?_) (by simp)
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto

/-- The vertices of the link of `σ` are the points `u ∉ σ` with `σ ∪ {u}` a face. -/
private theorem mem_vertices_link_iff {σ : Finset ι} {u : ι} :
    u ∈ (K.link σ).vertices ↔ u ∉ σ ∧ insert u σ ∈ K := by
  show {u} ∈ K.link σ ↔ _
  rw [mem_link, Finset.disjoint_singleton_left, Finset.singleton_union]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨Finset.singleton_nonempty u, h.1, h.2⟩⟩

/-- **(b) ⇒ connected links.** If `K` is pure of dimension `d` with a face and any two distinct
top faces share `d` vertices, the link of every `σ` with `|σ| ≤ d − 2` (`σ = ∅` or a face) is
connected: two of its vertices are joined directly, or through a point of `(F ∩ G) \ σ` for top
faces `F, G` through them, which exists because `|F ∩ G| = d ≥ |σ| + 2`.

The face of `K` is needed only for `σ = ∅` (the complex with no faces is not connected). -/
theorem isConnected_link_of_forall_card_inter (hpure : K.IsPure d) (hne : ∃ F, F ∈ K)
    (hb : ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F ≠ G → #(F ∩ G) = d)
    {σ : Finset ι} (hσ : σ = ∅ ∨ σ ∈ K) (hcard : #σ + 2 ≤ d) : (K.link σ).IsConnected := by
  rw [IsConnected, SimpleGraph.connected_iff]
  have htop : ∀ u ∈ (K.link σ).vertices, ∃ F ∈ K, #F = d + 1 ∧ insert u σ ⊆ F := by
    intro u hu
    obtain ⟨-, F, hF, hsub, hFc⟩ := hpure _ (mem_vertices_link_iff.mp hu).2
    exact ⟨F, hF, hFc, hsub⟩
  refine ⟨fun ⟨u, hu⟩ ⟨v, hv⟩ => ?_, ?_⟩
  · obtain ⟨F, hF, hFc, huF⟩ := htop u hu
    obtain ⟨G, hG, hGc, hvG⟩ := htop v hv
    have huσ := (mem_vertices_link_iff.mp hu).1
    have hvσ := (mem_vertices_link_iff.mp hv).1
    have hσF : σ ⊆ F := (Finset.subset_insert _ _).trans huF
    have hσG : σ ⊆ G := (Finset.subset_insert _ _).trans hvG
    have huF' : u ∈ F := huF (Finset.mem_insert_self _ _)
    have hvG' : v ∈ G := hvG (Finset.mem_insert_self _ _)
    by_cases huv : u = v
    · subst huv
      rfl
    by_cases hvF : v ∈ F
    · exact (link_adj_of_subset hF huv huσ hvσ
        (Finset.insert_subset huF' (Finset.insert_subset hvF hσF)) hu hv).reachable
    by_cases huG : u ∈ G
    · exact (link_adj_of_subset hG huv huσ hvσ
        (Finset.insert_subset huG (Finset.insert_subset hvG' hσG)) hu hv).reachable
    have hFG : F ≠ G := by rintro rfl; exact hvF hvG'
    obtain ⟨x, hx⟩ : ((F ∩ G) \ σ).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_sdiff_of_subset (Finset.subset_inter hσF hσG), hb F hF G hG hFc hGc hFG]
      omega)
    obtain ⟨hxFG, hxσ⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hxF, hxG⟩ := Finset.mem_inter.mp hxFG
    have hxV : x ∈ (K.link σ).vertices := mem_vertices_link_iff.mpr ⟨hxσ,
      K.mem_of_subset hF (Finset.insert_subset hxF hσF) (Finset.insert_nonempty _ _)⟩
    have hux : u ≠ x := fun h => huG (h ▸ hxG)
    have hxv : x ≠ v := fun h => hvF (h ▸ hxF)
    exact (link_adj_of_subset hF hux huσ hxσ
        (Finset.insert_subset huF' (Finset.insert_subset hxF hσF)) hu hxV).reachable.trans
      (link_adj_of_subset hG hxv hxσ hvσ
        (Finset.insert_subset hxG (Finset.insert_subset hvG' hσG)) hxV hv).reachable
  · obtain ⟨F, hF, hσF, hFc⟩ : ∃ F ∈ K, σ ⊆ F ∧ #F = d + 1 := by
      rcases hσ with rfl | hσK
      · obtain ⟨F, hF, hFc⟩ := hpure.exists_card_eq hne
        exact ⟨F, hF, Finset.empty_subset _, hFc⟩
      · obtain ⟨-, F, hF, hsub, hFc⟩ := hpure σ hσK
        exact ⟨F, hF, hsub, hFc⟩
    obtain ⟨x, hx⟩ : (F \ σ).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_sdiff_of_subset hσF, hFc]
      omega)
    exact ⟨⟨x, mem_vertices_link_iff.mpr ⟨(Finset.mem_sdiff.mp hx).2,
      K.mem_of_subset hF (Finset.insert_subset (Finset.mem_sdiff.mp hx).1 hσF)
        (Finset.insert_nonempty _ _)⟩⟩⟩

/-- `#X + #Y ≤ #(X ∩ Y) + #H` for subsets `X, Y` of `H`. -/
private theorem card_add_card_le_of_subset {H X Y : Finset ι} (hX : X ⊆ H) (hY : Y ⊆ H) :
    #X + #Y ≤ #(X ∩ Y) + #H := by
  have h1 := Finset.card_union_add_card_inter X Y
  have h2 := Finset.card_le_card (Finset.union_subset hX hY)
  omega

/-- **(d′) ⇒ (b).** Let `K` be pure of dimension `d`, with the link of every `σ` with
`|σ| ≤ d − 2` (`σ = ∅` or a face) connected, and no two disjoint edges in the links of the
`(d − 2)`-faces. Then any two distinct top faces share exactly `d` vertices.

Proof: choose top faces `F, G` meeting in a set `σ` as large as possible among the pairs that meet
in at most `d − 1` points (formally, strong induction on `d − 1 − |F ∩ G|`). If `|σ| = d − 1`,
`F \ σ` and `G \ σ` are disjoint edges of the link of `σ`. Otherwise walk in the connected link of
`σ` from `F \ σ` to `G \ σ`; along the walk, the current vertex lies in a top face meeting `F` in
`d` points, because consecutive top faces share more than `|σ|` points; at the end this top face
also meets `G` in `d` points, so `F` and `G` share at least `d − 1 > |σ|` points.

For `d = 1` the connectivity hypothesis is vacuous and the matching condition alone gives the
conclusion (two edges of a graph without disjoint edges meet). The connectivity hypothesis cannot
be dropped: `disjointTriangles_counterexample` shows this for `d = 2` (two disjoint `d`-simplices
give the same failure for every `d ≥ 2`, but only `d = 2` is formalized). `d = 0` is allowed, and there the
conclusion `#(F ∩ G) = 0` holds for distinct singletons whatever the hypotheses. -/
theorem forall_card_inter_of_isConnected_link (hpure : K.IsPure d)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ d → (K.link σ).IsConnected)
    (hmatch : K.NoTwoDisjointLinkEdges d) :
    ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F ≠ G → #(F ∩ G) = d := by
  -- every two top faces share at least `d` points, by strong induction on `d − 1 − |F ∩ G|`
  have key : ∀ j : ℕ, ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 →
      #(F ∩ G) + 1 + j = d → False := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro F hF G hG hFc hGc hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact hmatch.not_card_inter_add_one_eq hF hG hFc hGc (by omega)
      -- pairs of top faces meeting in more than `|F ∩ G|` points meet in at least `d`
      have hbig : ∀ F' ∈ K, ∀ G' ∈ K, #F' = d + 1 → #G' = d + 1 →
          #(F ∩ G) < #(F' ∩ G') → d ≤ #(F' ∩ G') := by
        intro F' hF' G' hG' hF'c hG'c hlt
        by_contra hd
        push Not at hd
        exact ih (d - 1 - #(F' ∩ G')) (by omega) F' hF' G' hG' hF'c hG'c (by omega)
      set σ := F ∩ G with hσdef
      have hσ : σ = ∅ ∨ σ ∈ K := by
        rcases σ.eq_empty_or_nonempty with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (K.mem_of_subset hF Finset.inter_subset_left h0)
      have hc := hconn σ hσ (by omega)
      have hσF : σ ⊆ F := Finset.inter_subset_left
      have hσG : σ ⊆ G := Finset.inter_subset_right
      obtain ⟨u, hu⟩ : (F \ σ).Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_sdiff_of_subset hσF, hFc]; omega)
      obtain ⟨v, hv⟩ : (G \ σ).Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_sdiff_of_subset hσG, hGc]; omega)
      have huV : u ∈ (K.link σ).vertices :=
        mem_vertices_link_iff.mpr ⟨(Finset.mem_sdiff.mp hu).2,
          K.mem_of_subset hF (Finset.insert_subset (Finset.mem_sdiff.mp hu).1 hσF)
            (Finset.insert_nonempty _ _)⟩
      have hvV : v ∈ (K.link σ).vertices :=
        mem_vertices_link_iff.mpr ⟨(Finset.mem_sdiff.mp hv).2,
          K.mem_of_subset hG (Finset.insert_subset (Finset.mem_sdiff.mp hv).1 hσG)
            (Finset.insert_nonempty _ _)⟩
      have hreach := hc.preconnected ⟨u, huV⟩ ⟨v, hvV⟩
      rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
      -- along a walk in the link of `σ`, the current vertex lies in a top face close to `F`
      have walk : ∀ b : (K.link σ).vertices,
          Relation.ReflTransGen ((K.link σ).oneSkeleton.induce (K.link σ).vertices).Adj
            ⟨u, huV⟩ b → ∃ H ∈ K, #H = d + 1 ∧ insert (b : ι) σ ⊆ H ∧ d ≤ #(H ∩ F) := by
        intro b hb
        induction hb with
        | refl =>
          refine ⟨F, hF, hFc, Finset.insert_subset (Finset.mem_sdiff.mp hu).1 hσF, ?_⟩
          rw [Finset.inter_self, hFc]
          omega
        | @tail b c _ hbc ihb =>
          obtain ⟨H, hH, hHc, hbH, hHF⟩ := ihb
          have hadj := SimpleGraph.comap_adj.mp hbc
          rw [oneSkeleton, SimpleGraph.fromRel_adj] at hadj
          obtain ⟨-, hbc'⟩ := hadj
          have hpair : ({(b : ι), (c : ι)} : Finset ι) ∈ K.link σ :=
            hbc'.elim id fun h => by rwa [Finset.pair_comm]
          obtain ⟨-, -, hmem⟩ := mem_link.mp hpair
          obtain ⟨-, H', hH', hsub, hH'c⟩ := hpure _ hmem
          have hbσ : (b : ι) ∉ σ := (mem_vertices_link_iff.mp b.2).1
          have hbH' : insert (b : ι) σ ⊆ H' := fun x hx => hsub (by
            simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hx ⊢
            tauto)
          have hcH' : insert (c : ι) σ ⊆ H' := fun x hx => hsub (by
            simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hx ⊢
            tauto)
          have hHH' : d ≤ #(H ∩ H') := by
            refine hbig H hH H' hH' hHc hH'c ?_
            have h1 := Finset.card_le_card (Finset.subset_inter hbH hbH')
            rw [Finset.card_insert_of_notMem hbσ] at h1
            omega
          have h2 := card_add_card_le_of_subset (H := H) (X := H ∩ F) (Y := H ∩ H')
            Finset.inter_subset_left Finset.inter_subset_left
          have h3 : #((H ∩ F) ∩ (H ∩ H')) ≤ #(H' ∩ F) := Finset.card_le_card (fun x hx => by
            simp only [Finset.mem_inter] at hx ⊢
            exact ⟨hx.2.2, hx.1.2⟩)
          refine ⟨H', hH', hH'c, hcH', hbig H' hH' F hF hH'c hFc ?_⟩
          omega
      obtain ⟨H, hH, hHc, hvH, hHF⟩ := walk _ hreach
      have hHG : d ≤ #(H ∩ G) := by
        refine hbig H hH G hG hHc hGc ?_
        have h1 := Finset.card_le_card (Finset.subset_inter hvH
          (Finset.insert_subset (Finset.mem_sdiff.mp hv).1 hσG))
        rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hv).2] at h1
        omega
      have h2 := card_add_card_le_of_subset (H := H) (X := H ∩ F) (Y := H ∩ G)
        Finset.inter_subset_left Finset.inter_subset_left
      have h3 : #((H ∩ F) ∩ (H ∩ G)) ≤ #σ := Finset.card_le_card (fun x hx => by
        rw [hσdef]
        simp only [Finset.mem_inter] at hx ⊢
        exact ⟨hx.1.2, hx.2.2⟩)
      omega
  intro F hF G hG hFc hGc hFG
  have hle := card_inter_le_of_ne hFc hGc hFG
  by_contra hne
  exact key (d - 1 - #(F ∩ G)) F hF G hG hFc hGc (by omega)

/-! ### The equivalence -/

section Fin

variable [Fintype ι]

/-- **Complexes that are `0`-local spectral expanders for every weighting.** For `d ≥ 1` and `K`
pure of dimension `d` with at least one face, the following are equivalent:
1. `K` is a `0`-local spectral expander for every top weight `m`;
2. any two distinct top faces share exactly `d` vertices;
3. all top faces contain a common `d`-set, or all lie in a common `(d + 2)`-set;
4. `K` is a matroid complex and the links of its `(d − 2)`-faces (of `∅`, for `d = 1`) have no
   two disjoint edges;
5. the links of all faces of dimension at most `d − 3`, and `K` itself, are connected, and the
   links of the `(d − 2)`-faces have no two disjoint edges.

Degenerate cases.
* `d = 1`: item 1 says that the weighted graph `K` has second eigenvalue at most `0` for all edge
  weights, and item 5 says only that `K` has no two disjoint edges (its connectivity condition is
  vacuous, since no `σ` has `|σ| + 2 ≤ 1`). So `K` is a star or a triangle.
* A single top face (a simplex) satisfies every item.
* `d = 0` is excluded: item 1 then fails (`not_isLocalSpectralExpanderOf_zero`), while items 2–5
  hold for every pure `0`-dimensional complex with a face (a nonempty set of vertices).
* The face is needed: the complex with no faces satisfies items 1, 2 and 4 vacuously, but not
  item 5 for `d ≥ 2` (it is not connected), nor item 3 when `ι` has fewer than `d` points.
* Purity is needed: a non-pure complex has no top weight, so item 1 holds vacuously. -/
theorem tfae_forall_isLocalSpectralExpanderOf_zero (hd : 1 ≤ d) (hpure : K.IsPure d)
    (hne : ∃ F, F ∈ K) :
    List.TFAE
      [∀ m, K.IsTopWeight d m → K.IsLocalSpectralExpanderOf d m 0,
        ∀ F ∈ K, ∀ G ∈ K, #F = d + 1 → #G = d + 1 → F ≠ G → #(F ∩ G) = d,
        (∃ D : Finset ι, #D = d ∧ ∀ F ∈ K, #F = d + 1 → D ⊆ F) ∨
          (∃ T : Finset ι, #T = d + 2 ∧ ∀ F ∈ K, #F = d + 1 → F ⊆ T),
        K.IsMatroidComplex ∧ K.NoTwoDisjointLinkEdges d,
        (∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ d → (K.link σ).IsConnected) ∧
          K.NoTwoDisjointLinkEdges d] := by
  tfae_have 1 ↔ 2 := forall_isLocalSpectralExpanderOf_zero_iff hd hpure
  tfae_have 2 ↔ 3 := forall_card_inter_iff_sunflower_or_subset hpure hne
  tfae_have 2 → 4 := fun hb =>
    ⟨isMatroidComplex_of_forall_card_inter hpure hb, noTwoDisjointLinkEdges_of_forall_card_inter hb⟩
  tfae_have 4 → 2 := fun h => forall_card_inter_of_isMatroidComplex hd h.1 h.2
  tfae_have 2 → 5 := fun hb =>
    ⟨fun _ hσ hc => isConnected_link_of_forall_card_inter hpure hne hb hσ hc,
      noTwoDisjointLinkEdges_of_forall_card_inter hb⟩
  tfae_have 5 → 2 := fun h => forall_card_inter_of_isConnected_link hpure h.1 h.2
  tfae_finish

/-! ### Consequences -/

/-- **Few points: everything is universally `0`.** If `ι` has at most `d + 2` points and `d ≥ 1`,
every complex `K` on `ι` is a `0`-local spectral expander for every top weight. This covers the
simplex (`d + 1` points) and every pure `d`-complex on `d + 2` points. With at most `d` points
there is no top face, hence no top weight, and the statement is vacuous. -/
theorem forall_isLocalSpectralExpanderOf_zero_of_card_le (hd : 1 ≤ d)
    (hN : Fintype.card ι ≤ d + 2) : ∀ m, K.IsTopWeight d m → K.IsLocalSpectralExpanderOf d m 0 := by
  refine forall_isLocalSpectralExpanderOf_zero_of_forall_card_inter hd ?_
  intro F _ G _ hFc hGc hFG
  have h1 := Finset.card_le_univ (F ∪ G)
  have h2 := Finset.card_union_add_card_inter F G
  have h3 := card_inter_le_of_ne hFc hGc hFG
  omega

/-- **Many points: only the cone.** Let `K` be pure of dimension `d ≥ 1`, with every point of `ι`
a vertex, and `N = Fintype.card ι ≥ d + 3`. Then `K` is a `0`-local spectral expander for every top
weight exactly when, for some `d`-set `D`, the faces of `K` are the nonempty subsets of the sets
`D ∪ {x}`, `x ∉ D`: `K` is the cone `Δ^{d−1} * (N − d points)`, the independence complex of
`U_{d,d} ⊕ U_{1,N−d}`.

The hypotheses: with `N ≤ d + 2` every complex qualifies
(`forall_isLocalSpectralExpanderOf_zero_of_card_le`), and the boundary of a `(d + 1)`-simplex
(`N = d + 2`) is not a cone; without `hV`, a complex inside a `(d + 2)`-subset of a larger `ι` would
also qualify. The direction "cone ⇒ universally `0`" uses only `d ≥ 1`. -/
theorem forall_isLocalSpectralExpanderOf_zero_iff_cone (hd : 1 ≤ d) (hpure : K.IsPure d)
    (hV : ∀ v, {v} ∈ K) (hN : d + 3 ≤ Fintype.card ι) :
    (∀ m, K.IsTopWeight d m → K.IsLocalSpectralExpanderOf d m 0) ↔
      ∃ D : Finset ι, #D = d ∧ ∀ s, s ∈ K ↔ s.Nonempty ∧ ∃ x ∉ D, s ⊆ insert x D := by
  obtain ⟨v0⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hne : ∃ F, F ∈ K := ⟨_, hV v0⟩
  constructor
  · intro h
    rcases (forall_card_inter_iff_sunflower_or_subset hpure hne).mp
      (forall_card_inter_of_forall_isLocalSpectralExpanderOf_zero hpure h) with
      ⟨D, hD, hDF⟩ | ⟨T, hT, hTF⟩
    · refine ⟨D, hD, fun s => ⟨fun hs => ?_, fun ⟨hsne, x, hx, hsx⟩ => ?_⟩⟩
      · obtain ⟨-, F, hF, hsF, hFc⟩ := hpure s hs
        have hDF' := hDF F hF hFc
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (by
          rw [Finset.card_sdiff_of_subset hDF', hFc, hD]; omega : #(F \ D) = 1)
        have hxF : x ∈ F \ D := by rw [hx]; exact Finset.mem_singleton_self x
        refine ⟨K.nonempty_of_mem hs, x, (Finset.mem_sdiff.mp hxF).2, fun y hy => ?_⟩
        by_cases hyD : y ∈ D
        · exact Finset.mem_insert_of_mem hyD
        · have : y ∈ F \ D := Finset.mem_sdiff.mpr ⟨hsF hy, hyD⟩
          rw [hx, Finset.mem_singleton] at this
          rw [this]
          exact Finset.mem_insert_self _ _
      · obtain ⟨-, F, hF, hxF, hFc⟩ := hpure _ (hV x)
        have hsub : insert x D ⊆ F :=
          Finset.insert_subset (Finset.singleton_subset_iff.mp hxF) (hDF F hF hFc)
        have heq : insert x D = F := Finset.eq_of_subset_of_card_le hsub
          (by rw [Finset.card_insert_of_notMem hx, hD, hFc])
        exact K.mem_of_subset hF (heq ▸ hsx) hsne
    · exfalso
      have hall : (Finset.univ : Finset ι) ⊆ T := by
        intro v _
        obtain ⟨-, F, hF, hvF, hFc⟩ := hpure _ (hV v)
        exact hTF F hF hFc (Finset.singleton_subset_iff.mp hvF)
      have := Finset.card_le_card hall
      rw [Finset.card_univ] at this
      omega
  · rintro ⟨D, hD, hK⟩
    refine forall_isLocalSpectralExpanderOf_zero_of_forall_card_inter hd
      (forall_card_inter_of_sunflower_or_subset (Or.inl ⟨D, hD, fun F hF hFc => ?_⟩))
    obtain ⟨-, x, hx, hFx⟩ := (hK F).mp hF
    have heq : F = insert x D := Finset.eq_of_subset_of_card_le hFx
      (by rw [Finset.card_insert_of_notMem hx, hD, hFc])
    rw [heq]
    exact Finset.subset_insert _ _

/-- **Two triangles sharing an edge are universally `0`.** The complex `twoTriangles` of
`Expanders/NegativeRigidity.lean` (triangles `{0, 1, 2}` and `{0, 1, 3}` on `Fin 4`), which shows
there that negative local expansion cannot be relaxed to `lam ≤ 0`, is a `0`-local spectral
expander for every top weight: its triangles form a sunflower with kernel `{0, 1}`. -/
theorem isLocalSpectralExpanderOf_twoTriangles_zero {m : Finset (Fin 4) → ℝ}
    (hm : twoTriangles.IsTopWeight 2 m) : twoTriangles.IsLocalSpectralExpanderOf 2 m 0 := by
  refine forall_isLocalSpectralExpanderOf_zero_of_forall_card_inter (by norm_num)
    (forall_card_inter_of_sunflower_or_subset (Or.inl ⟨{0, 1}, by decide, fun F hF hFc => ?_⟩))
    m hm
  have key : ∀ F : Finset (Fin 4), (F ⊆ {0, 1, 2} ∨ F ⊆ {0, 1, 3}) → #F = 2 + 1 →
      ({0, 1} : Finset (Fin 4)) ⊆ F := by decide
  exact key F (mem_twoTriangles.mp hF).2 hFc

end Fin

/-! ### Connectivity cannot be dropped: two disjoint triangles -/

/-- **Two disjoint triangles**: the complex on `Fin 6` whose faces are the nonempty subsets of
`{0, 1, 2}` and of `{3, 4, 5}`. It is pure of dimension `2`, and every vertex link is a single
edge, so it meets the matching condition of (d′); but it is disconnected and not universally
`0`. -/
def disjointTriangles : PreAbstractSimplicialComplex (Fin 6) where
  faces := {s | s.Nonempty ∧ (s ⊆ {0, 1, 2} ∨ s ⊆ {3, 4, 5})}
  isRelLowerSet_faces := by
    rintro s ⟨hne, hs⟩
    exact ⟨hne, fun t hts ht => ⟨ht, hs.imp hts.trans hts.trans⟩⟩

/-- The faces of `disjointTriangles`, by definition. -/
theorem mem_disjointTriangles {s : Finset (Fin 6)} :
    s ∈ disjointTriangles ↔ s.Nonempty ∧ (s ⊆ {0, 1, 2} ∨ s ⊆ {3, 4, 5}) := Iff.rfl

/-- `disjointTriangles` is pure of dimension `2`: every face lies in one of the two triangles. -/
theorem isPure_disjointTriangles : disjointTriangles.IsPure 2 := by
  intro σ hσ
  rcases (mem_disjointTriangles.mp hσ).2 with h | h
  · exact ⟨(Finset.card_le_card h).trans (by decide), {0, 1, 2},
      mem_disjointTriangles.mpr ⟨by decide, Or.inl subset_rfl⟩, h, by decide⟩
  · exact ⟨(Finset.card_le_card h).trans (by decide), {3, 4, 5},
      mem_disjointTriangles.mpr ⟨by decide, Or.inr subset_rfl⟩, h, by decide⟩

/-- In a vertex link of `disjointTriangles`, an edge is the rest of the triangle of the vertex. -/
private theorem eq_of_mem_link_disjointTriangles {v : Fin 6} {e : Finset (Fin 6)}
    (he : e ∈ disjointTriangles.link {v}) (hec : #e = 2) :
    e = if v ∈ ({0, 1, 2} : Finset (Fin 6)) then ({0, 1, 2} : Finset (Fin 6)).erase v
      else ({3, 4, 5} : Finset (Fin 6)).erase v := by
  obtain ⟨-, hdisj, hmem⟩ := mem_link.mp he
  have hve : v ∉ e := Finset.disjoint_singleton_right.mp hdisj
  rcases (mem_disjointTriangles.mp hmem).2 with h | h
  · have hv : v ∈ ({0, 1, 2} : Finset (Fin 6)) := h (by simp)
    rw [if_pos hv]
    refine Finset.eq_of_subset_of_card_le (fun x hx => Finset.mem_erase.mpr
      ⟨fun hxv => hve (hxv ▸ hx), h (Finset.mem_union_left _ hx)⟩) ?_
    rw [Finset.card_erase_of_mem hv, hec]
    rfl
  · have hv : v ∈ ({3, 4, 5} : Finset (Fin 6)) := h (by simp)
    have hv' : v ∉ ({0, 1, 2} : Finset (Fin 6)) := by
      revert hv
      fin_cases v <;> decide
    rw [if_neg hv']
    refine Finset.eq_of_subset_of_card_le (fun x hx => Finset.mem_erase.mpr
      ⟨fun hxv => hve (hxv ▸ hx), h (Finset.mem_union_left _ hx)⟩) ?_
    rw [Finset.card_erase_of_mem hv, hec]
    rfl

/-- **The connectivity hypothesis of (d′) cannot be dropped.** `disjointTriangles` is pure of
dimension `2` and its vertex links have no two disjoint edges, but it is not a `0`-local spectral
expander for every top weight (its two triangles share no vertex). It is the link of `∅`, i.e. `K`
itself, that is disconnected. -/
theorem disjointTriangles_counterexample :
    disjointTriangles.IsPure 2 ∧ disjointTriangles.NoTwoDisjointLinkEdges 2 ∧
      ¬ ∀ m, disjointTriangles.IsTopWeight 2 m →
        disjointTriangles.IsLocalSpectralExpanderOf 2 m 0 := by
  refine ⟨isPure_disjointTriangles, fun σ _ hσc e he e' he' hec he'c hdisj => ?_, fun h => ?_⟩
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (by omega : #σ = 1)
    have h1 := eq_of_mem_link_disjointTriangles he hec
    have h2 := eq_of_mem_link_disjointTriangles he' he'c
    rw [← h2] at h1
    subst h1
    rw [disjoint_self, Finset.bot_eq_empty] at hdisj
    rw [hdisj, Finset.card_empty] at hec
    omega
  · have := forall_card_inter_of_forall_isLocalSpectralExpanderOf_zero isPure_disjointTriangles h
      {0, 1, 2} (mem_disjointTriangles.mpr ⟨by decide, Or.inl subset_rfl⟩)
      {3, 4, 5} (mem_disjointTriangles.mpr ⟨by decide, Or.inr subset_rfl⟩)
      (by decide) (by decide) (by decide)
    revert this
    decide

end PreAbstractSimplicialComplex
