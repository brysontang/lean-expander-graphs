/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.WeightedComplex

/-!
# Skeleta of weighted local spectral expanders

The `k`-skeleton of a simplicial complex `K` keeps the faces with at most `k + 1` vertices. If `m`
is a weight on the `d`-dimensional faces of `K`, the **induced weight** on the `k`-dimensional
faces gives the face `τ` the total weight `faceWeight m τ` of the top faces through it. These are
Oppenheim's balanced weights, up to the factor `(d − k)!`, which is constant and so changes no
random walk.

The main result, `IsLocalSpectralExpanderOf.skeleton`: for `1 ≤ k ≤ d`, the `k`-skeleton of a
weighted `lam`-local-spectral expander of dimension `d`, with the induced weights, is a
`lam`-local-spectral expander of dimension `k`.

Nothing spectral happens in the proof. A `(k + 1)`-set between `s` and a top face `F ⊇ s` is
chosen by picking `k + 1 − |s|` of the `d + 1 − |s|` vertices of `F \ s`, so the induced weight of
`s` is `C(d + 1 − |s|, k + 1 − |s|)` times its weight in `K` (`faceWeight_skeletonWeight`). Hence
the weighted graph of the link of a face `σ` of dimension at most `k − 2` in the skeleton is the
weighted graph of its link in `K` multiplied by `C(d − 1 − |σ|, k − 1 − |σ|) > 0`
(`linkWeightOf_skeletonWeight`), and the random walk does not see a constant factor
(`walkSecondEigenvalueLE_const_mul_iff`). So these links of the skeleton have *exactly* the
second eigenvalues of the corresponding links of `K`
(`walkSecondEigenvalueLE_linkWeightOf_skeletonWeight_iff`). Their underlying graphs agree too, so
connectivity passes to the skeleton as well (`isConnected_link_skeleton_iff`).

**The weights matter.** With uniform weights the statement is false. The complex with the six
triangles `024, 025, 034, 045, 125, 245` on six vertices, with uniform weights, is a
`0.296535…`-local-spectral expander (the bound is attained by the complex itself; its vertex links
have second eigenvalue `0.2287…` or `−1`). Its `1`-skeleton with the induced edge weights has the
same second eigenvalue `0.296535…`, as the theorem says, but with uniform edge weights it has
`0.390388…`. These values were computed numerically during screening and are **not formalized**
here; an exhaustive search found no counterexample on at most five vertices.

## Definitions
* `PreAbstractSimplicialComplex.skeleton K k`: the faces of `K` with at most `k + 1` vertices.
  **Definition.**
* `PreAbstractSimplicialComplex.skeletonWeight m k`: the induced weight, `faceWeight m τ` on the
  sets `τ` with `k + 1` elements and `0` on all other sets. **Definition.**

## Theorems
* `walkSecondEigenvalueLE_const_mul_iff`: multiplying every weight of a weighted graph by a
  constant `c > 0` does not change the second eigenvalue of its random walk. **Proved.**
* `skeleton_le`, `skeleton_eq_self`, `IsPure.skeleton_eq_self`: the skeleton is a subcomplex,
  equal to `K` once `k` reaches the dimension of `K`. **Proved.**
* `vertices_skeleton`, `oneSkeleton_skeleton`, `isConnected_skeleton_iff`: the skeleton has the
  vertices of `K`, and for `k ≥ 1` also its underlying graph and its connectivity. **Proved.**
* `link_skeleton`: links of skeleta are skeleta of links,
  `(K.skeleton k).link σ = (K.link σ).skeleton (k − |σ|)` for `|σ| ≤ k`. **Proved.**
* `vertices_link_skeleton`, `oneSkeleton_link_skeleton`, `isConnected_link_skeleton_iff`,
  `isConnected_link_skeleton_of_forall`: the link of a face of dimension at most `k − 2` has the
  same vertices, underlying graph and connectivity in the skeleton as in `K`; so the connectivity
  hypothesis of `trickling_down_weighted` passes to skeleta. **Proved.**
* `faceWeight_skeletonWeight`: the counting identity
  `faceWeight (skeletonWeight m k) s = C(d + 1 − |s|, k + 1 − |s|) · faceWeight m s` for
  `|s| ≤ k + 1`. **Proved.**
* `skeletonWeight_self`, `skeletonWeight_eq_zero_of_lt`, `skeletonWeight_uniformWeight`: the
  induced weight for `k = d` is `m`, for `k > d` it is `0`, and for the uniform weight it counts
  the top faces through a `k`-face. **Proved.**
* `linkWeightOf_skeletonWeight`: the weighted graph of the link of `σ` in the skeleton is
  `C(d − 1 − |σ|, k − 1 − |σ|)` times the one in `K`, for `|σ| + 1 ≤ k`. **Proved.**
* `walkSecondEigenvalueLE_linkWeightOf_skeletonWeight_iff`: for `1 ≤ k ≤ d` these links have the
  same second-eigenvalue bounds in the skeleton as in `K`. **Proved.**
* `IsTopWeight.skeleton`: the induced weight is a top weight of the `k`-skeleton, `k ≤ d`.
  **Proved.**
* `IsLocalSpectralExpanderOf.skeleton`: **the main theorem**, as above. **Proved.**
* `IsLocalSpectralExpander.skeleton`: the counting version: the `k`-skeleton of a
  `lam`-local-spectral expander, each `k`-face weighted by the number of top faces through it, is a
  weighted `lam`-local-spectral expander. **Proved.**

## References
* I. Oppenheim, *Local spectral expansion approach to high dimensional expanders Part I: Descent
  of spectral gaps*, Discrete Comput. Geom. 59 (2018), arXiv:1709.04431. Balanced
  weights, determined by the top faces; the proof of Proposition 3.16 uses in passing that the
  `(n − 1)`-skeleton of a pure `n`-complex with connected links again has connected links (the
  connectivity half of `isConnected_link_skeleton_iff`).
* P. Harsha and R. Saptharishi, *A note on the elementary construction of high-dimensional
  expanders of Kaufman and Oppenheim*, arXiv:1912.11225. Definition 2.2 (balanced weights as the
  marginals of the top-face distribution); Corollary 5.8 applies the expansion of a complex to its
  `k`-skeleton, using the present fact implicitly.
* T. Kaufman and I. Oppenheim, *High order random walks: beyond spectral gap*, arXiv:1707.02799
  (definitions).
* R. Gotlib and T. Kaufman, *No where to go but high: a perspective on high dimensional
  expanders*, arXiv:2304.10106, Definition 3.8 (the skeleton).

No source we found states the theorem as a numbered result: in the balanced-weight framework it
is folklore and used without comment. We found no published version of the uniform-weight
counterexample.
-/

open Finset

/-! ### Scale invariance of the random walk -/

/-- **The random walk does not see a constant factor.** Multiplying every weight of a weighted
graph by the same constant `c > 0` leaves the random walk `w u v / deg u` unchanged, so it has
second eigenvalue at most `lam` before exactly when it does after.

In the variational form of `WalkSecondEigenvalueLE`, both the mean-zero condition and the two
sides of the inequality are multiplied by `c`. No symmetry or sign condition on `w` is used, and
`lam` is any real number; for empty `ι` both sides hold trivially. The hypothesis `c > 0` cannot
be dropped: for `c = 0` the left side holds for every `w` and `lam` (the graph has no edges,
`walkSecondEigenvalueLE_of_forall_eq_zero`). For `c < 0` the equivalence fails already for the
path `0 − 1 − 2` with unit weights and `lam = 0`: its random walk has eigenvalues `1, 0, −1`, so
the right side holds, while the left side asks that no `f` of degree-weighted mean zero have
negative quadratic form, and `f = (1, −1, 1)` has quadratic form `−4`. -/
theorem walkSecondEigenvalueLE_const_mul_iff {ι : Type*} [Fintype ι] {w : ι → ι → ℝ}
    {c lam : ℝ} (hc : 0 < c) :
    WalkSecondEigenvalueLE (fun u v => c * w u v) lam ↔ WalkSecondEigenvalueLE w lam := by
  have e1 : ∀ f : ι → ℝ, ∑ u, (∑ v, c * w u v) * f u = c * ∑ u, (∑ v, w u v) * f u := by
    intro f
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [← Finset.mul_sum]; ring
  have e2 : ∀ f : ι → ℝ,
      ∑ u, ∑ v, c * w u v * f u * f v = c * ∑ u, ∑ v, w u v * f u * f v := by
    intro f
    simp only [Finset.mul_sum, mul_assoc]
  unfold WalkSecondEigenvalueLE
  simp only [e1, e2, mul_eq_zero, hc.ne', false_or, mul_left_comm lam c,
    mul_le_mul_iff_right₀ hc]

namespace PreAbstractSimplicialComplex

variable {ι : Type*}

/-! ### The skeleton of a complex -/

/-- The **`k`-skeleton** of `K`: the faces of `K` with at most `k + 1` vertices, that is, of
dimension at most `k`.

Degenerate cases: the `0`-skeleton is the set of vertices of `K` (there is no `(−1)`-skeleton,
since `k : ℕ`). Once `k + 1` bounds the size of every face, the skeleton is `K` itself
(`skeleton_eq_self`); for a pure `d`-dimensional complex this happens for every `k ≥ d`
(`IsPure.skeleton_eq_self`). The skeleton of the complex with no faces has no faces. -/
def skeleton (K : PreAbstractSimplicialComplex ι) (k : ℕ) : PreAbstractSimplicialComplex ι where
  faces := {s | s ∈ K ∧ #s ≤ k + 1}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hcard⟩
    exact ⟨K.nonempty_of_mem hs, fun t hts ht =>
      ⟨K.mem_of_subset hs hts ht, (Finset.card_le_card hts).trans hcard⟩⟩

variable {K : PreAbstractSimplicialComplex ι} {d k : ℕ}

theorem mem_skeleton {s : Finset ι} : s ∈ K.skeleton k ↔ s ∈ K ∧ #s ≤ k + 1 := Iff.rfl

/-- The skeleton is a subcomplex. -/
theorem skeleton_le : K.skeleton k ≤ K := fun _ hs => hs.1

/-- If every face of `K` has at most `k + 1` vertices, the `k`-skeleton of `K` is `K`. -/
theorem skeleton_eq_self (h : ∀ s ∈ K, #s ≤ k + 1) : K.skeleton k = K :=
  SetLike.ext fun _ => mem_skeleton.trans ⟨fun hs => hs.1, fun hs => ⟨hs, h _ hs⟩⟩

/-- The `k`-skeleton of a pure `d`-dimensional complex is the complex itself when `k ≥ d`. -/
theorem IsPure.skeleton_eq_self (hpure : K.IsPure d) (hk : d ≤ k) : K.skeleton k = K :=
  PreAbstractSimplicialComplex.skeleton_eq_self fun s hs => (hpure s hs).1.trans (by omega)

/-- The skeleton has the vertices of `K`, for every `k` (including `k = 0`). -/
theorem vertices_skeleton : (K.skeleton k).vertices = K.vertices := by
  ext v
  simp only [vertices, Set.mem_ofPred_eq, mem_skeleton, Finset.card_singleton, and_iff_left_iff_imp]
  exact fun _ => by omega

section Link

variable [DecidableEq ι]

/-- For `k ≥ 1` the skeleton has the underlying graph of `K`. For `k = 0` it has no edges. -/
theorem oneSkeleton_skeleton (hk : 1 ≤ k) : (K.skeleton k).oneSkeleton = K.oneSkeleton := by
  unfold oneSkeleton
  congr 1
  funext u v
  simp only [mem_skeleton, eq_iff_iff, and_iff_left_iff_imp]
  exact fun _ => Finset.card_le_two.trans (by omega)

/-- For `k ≥ 1` the skeleton is connected exactly when `K` is. -/
theorem isConnected_skeleton_iff (hk : 1 ≤ k) : (K.skeleton k).IsConnected ↔ K.IsConnected := by
  unfold IsConnected
  rw [oneSkeleton_skeleton hk, vertices_skeleton]

/-- **Links of skeleta are skeleta of links.** For `|σ| ≤ k`, the link of `σ` in the
`k`-skeleton is the `(k − |σ|)`-skeleton of the link of `σ` in `K`.

The hypothesis `|σ| ≤ k` keeps the natural-number subtraction `k − |σ|` honest. Without it the
left side has no faces (a face of the link of `σ` together with `σ` has more than `k + 1`
vertices), while the right side is the `0`-skeleton of the link of `σ`, its vertices. `σ` need not
be a face: if it is nonempty and not a face both sides have no faces. -/
theorem link_skeleton {σ : Finset ι} (hσ : #σ ≤ k) :
    (K.skeleton k).link σ = (K.link σ).skeleton (k - #σ) := by
  refine SetLike.ext fun τ => ?_
  simp only [mem_link, mem_skeleton]
  constructor
  · rintro ⟨hne, hdisj, hmem, hcard⟩
    rw [Finset.card_union_of_disjoint hdisj] at hcard
    exact ⟨⟨hne, hdisj, hmem⟩, by omega⟩
  · rintro ⟨⟨hne, hdisj, hmem⟩, hcard⟩
    refine ⟨hne, hdisj, hmem, ?_⟩
    rw [Finset.card_union_of_disjoint hdisj]
    omega

/-- The link of `σ` has the same vertices in the `k`-skeleton as in `K`, when `|σ| ≤ k`. The
hypothesis is needed: for `|σ| > k` the link of `σ` in the skeleton has no vertices. -/
theorem vertices_link_skeleton {σ : Finset ι} (hσ : #σ ≤ k) :
    ((K.skeleton k).link σ).vertices = (K.link σ).vertices := by
  rw [link_skeleton hσ, vertices_skeleton]

/-- The link of a set `σ` of dimension at most `k − 2` has the same underlying graph in the
`k`-skeleton as in `K`. The hypothesis is needed: for `|σ| = k` the link of `σ` in the skeleton
has no edges. -/
theorem oneSkeleton_link_skeleton {σ : Finset ι} (hσ : #σ + 1 ≤ k) :
    ((K.skeleton k).link σ).oneSkeleton = (K.link σ).oneSkeleton := by
  rw [link_skeleton (by omega), oneSkeleton_skeleton (by omega)]

/-- **Connectivity passes to skeleta.** The link of a set `σ` of dimension at most `k − 2` is
connected in the `k`-skeleton exactly when it is connected in `K`. -/
theorem isConnected_link_skeleton_iff {σ : Finset ι} (hσ : #σ + 1 ≤ k) :
    ((K.skeleton k).link σ).IsConnected ↔ (K.link σ).IsConnected := by
  rw [link_skeleton (by omega), isConnected_skeleton_iff (by omega)]

/-- **The connectivity hypothesis of trickling down passes to skeleta.** If `K` and the link of
every face of `K` of dimension at most `k − 3` are connected, the same holds in the `k`-skeleton.
This is the hypothesis `hconn` of `trickling_down_weighted` for the `k`-skeleton; it follows from
the one for `K` in dimension `d ≥ k`, which asks for more.

For `k ≤ 1` there is no such `σ` and both the hypothesis and the conclusion are vacuous. -/
theorem isConnected_link_skeleton_of_forall
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ k → (K.link σ).IsConnected) :
    ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K.skeleton k) → #σ + 2 ≤ k →
      ((K.skeleton k).link σ).IsConnected := fun σ hσ hcard =>
  (isConnected_link_skeleton_iff (by omega)).mpr
    (hconn σ (hσ.imp_right fun h => (mem_skeleton.mp h).1) hcard)

end Link

/-! ### The induced weight -/

section Weights

variable [DecidableEq ι] [Fintype ι] {m : Finset ι → ℝ} {lam : ℝ}

/-- The **weight induced on the `k`-dimensional faces** by a weight `m` on the top faces: a set
`τ` with `k + 1` elements gets the total weight `faceWeight m τ` of the sets containing it, and
every other set gets `0`.

Like `faceWeight`, the definition does not mention a complex. It has its intended meaning when `m`
is a top weight of a `d`-dimensional complex `K` and `k ≤ d`: then it is a top weight of
`K.skeleton k` (`IsTopWeight.skeleton`), the weight of a `k`-face being the weight of the top
faces of `K` through it. Oppenheim's balanced weight of a `k`-face is `(d − k)!` times this, a
constant factor that changes no random walk.

Degenerate cases, when `m` vanishes off the sets with `d + 1` elements: for `k = d` the induced
weight is `m` itself (`skeletonWeight_self`), and for `k > d` it is identically `0`
(`skeletonWeight_eq_zero_of_lt`), since no set with more than `d + 1` elements lies in a top face.
For the uniform weight it counts the top faces through each `k`-face
(`skeletonWeight_uniformWeight`), which is in general *not* the uniform weight of the skeleton. -/
noncomputable def skeletonWeight (m : Finset ι → ℝ) (k : ℕ) (τ : Finset ι) : ℝ :=
  if #τ = k + 1 then faceWeight m τ else 0

/-- **The counting identity.** If `m` vanishes off the sets with `d + 1` elements, the weight that
the induced weight on `k`-faces gives to a set `s` with at most `k + 1` elements is
`C(d + 1 − |s|, k + 1 − |s|)` times the weight `m` gives it: every top face through `s` contains
that many `(k + 1)`-sets through `s`.

No hypothesis `k ≤ d` is needed. For `k > d` both sides are `0`: the binomial coefficient vanishes
when `|s| ≤ d + 1`, and `faceWeight m s = 0` when `|s| > d + 1` (where the natural-number
subtraction `d + 1 − |s|` is `0`). The hypothesis `|s| ≤ k + 1` is needed: for `|s| > k + 1` the
left side is `0`, while `k + 1 − |s|` is `0` in `ℕ` and the right side is `faceWeight m s`, as for
an edge `s` of a single triangle with `d = 2`, `k = 0`. -/
theorem faceWeight_skeletonWeight (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {s : Finset ι}
    (hs : #s ≤ k + 1) :
    faceWeight (skeletonWeight m k) s =
      ((d + 1 - #s).choose (k + 1 - #s) : ℝ) * faceWeight m s := by
  unfold faceWeight skeletonWeight
  -- write the left side as a double sum over `τ` and `F`, and swap
  have h1 : ∀ τ, (if #τ = k + 1 then faceWeight m τ else 0) =
      ∑ F, if #τ = k + 1 ∧ τ ⊆ F then m F else 0 := by
    intro τ
    split_ifs with hτ
    · rw [faceWeight, Finset.sum_filter]
      exact Finset.sum_congr rfl fun F _ => by simp [hτ]
    · exact (Finset.sum_eq_zero fun F _ => by simp [hτ]).symm
  simp only [h1]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_filter (fun F => s ⊆ F)]
  refine Finset.sum_congr rfl fun F _ => ?_
  -- the inner sum is `m F` times the number of `(k + 1)`-sets between `s` and `F`
  have h2 : (∑ τ with s ⊆ τ, if #τ = k + 1 ∧ τ ⊆ F then m F else 0) =
      (#((F.powersetCard (k + 1)).filter (s ⊆ ·)) : ℝ) * m F := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 3
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard]
    tauto
  rw [h2]
  by_cases hsF : s ⊆ F
  · rw [if_pos hsF, Finset.card_filter_powersetCard_subset s F (k + 1) hsF hs]
    by_cases h0 : m F = 0
    · simp [h0]
    · rw [hcard F h0]
  · rw [if_neg hsF]
    have : (F.powersetCard (k + 1)).filter (s ⊆ ·) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun τ hτ hsτ => hsF ?_
      exact hsτ.trans (Finset.mem_powersetCard.mp hτ).1
    simp [this]

/-- **The induced weight on top faces is the weight itself.** If `m` vanishes off the sets with
`d + 1` elements, the weight it induces on the `d`-dimensional faces is `m`. -/
theorem skeletonWeight_self (hcard : ∀ F, m F ≠ 0 → #F = d + 1) : skeletonWeight m d = m := by
  funext τ
  unfold skeletonWeight
  split_ifs with hτ
  · unfold faceWeight
    rw [Finset.sum_eq_single τ]
    · intro F hF hne
      by_contra h
      have := Finset.eq_of_subset_of_card_le (Finset.mem_filter.mp hF).2
        (by rw [hcard F h, hτ])
      exact hne this.symm
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, subset_rfl⟩) h
  · by_contra h
    exact hτ (hcard τ (Ne.symm h))

/-- **Above the top dimension the induced weight is zero.** If `m` vanishes off the sets with
`d + 1` elements and `k > d`, no set with `k + 1` elements lies in a set of nonzero weight, so the
induced weight is identically `0`; it is then not a top weight of anything. -/
theorem skeletonWeight_eq_zero_of_lt (hcard : ∀ F, m F ≠ 0 → #F = d + 1) (hk : d < k) :
    skeletonWeight m k = 0 := by
  funext τ
  unfold skeletonWeight
  split_ifs with hτ
  · exact faceWeight_eq_zero_of_lt_card hcard (by omega)
  · rfl

/-- **The counting case.** For the uniform weight on the `d`-dimensional faces of `K`, the induced
weight of a `k`-face is the number `K.topDegree d τ` of top faces through it. -/
theorem skeletonWeight_uniformWeight (τ : Finset ι) :
    skeletonWeight (K.uniformWeight d) k τ =
      if #τ = k + 1 then (K.topDegree d τ : ℝ) else 0 := by
  rw [skeletonWeight, topDegree_eq_faceWeight]

/-- **Links of the skeleton are scaled links of `K`.** If `m` vanishes off the sets with `d + 1`
elements and `σ` has dimension at most `k − 2`, the weighted graph of the link of `σ` for the
induced weight on `k`-faces is `C(d − 1 − |σ|, k − 1 − |σ|)` times the weighted graph of the
link of `σ` for `m`.

No hypothesis `k ≤ d` is needed. The subtraction `k − 1 − |σ|` is honest by `hσ`. If `|σ| ≥ d`,
the subtraction `d − 1 − |σ|` is truncated to `0`, but both sides vanish anyway: the link of `σ`
has no edges for `m` (`linkWeightOf_eq_zero_of_le_card`). If `k > d` both sides vanish too: the
left side because the induced weight is `0` (`skeletonWeight_eq_zero_of_lt`), the right side
because the factor is `0` when `|σ| < d` and by the previous case otherwise. For `k ≤ d` the
factor is at least `1`, and for `|σ| + 1 = k` it is exactly `1`.

The hypothesis `|σ| + 1 ≤ k` is needed: for `|σ| = k` the left side is `0` (a set with `k + 2`
elements lies in no `k`-face), while the factor is `C(d − 1 − |σ|, 0) = 1` in `ℕ` and the right
side is the weighted graph of the link of `σ` for `m`, which has an edge as soon as `k ≤ d − 1`
and `σ` lies in a top face. -/
theorem linkWeightOf_skeletonWeight (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {σ : Finset ι}
    (hσ : #σ + 1 ≤ k) (u v : ι) :
    linkWeightOf (skeletonWeight m k) σ u v =
      ((d - 1 - #σ).choose (k - 1 - #σ) : ℝ) * linkWeightOf m σ u v := by
  unfold linkWeightOf
  split_ifs with h
  · have hs : #(insert u (insert v σ)) = #σ + 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem h.2.2]
      rw [Finset.mem_insert, not_or]
      exact ⟨h.1, h.2.1⟩
    rw [faceWeight_skeletonWeight hcard (by omega), hs,
      show d + 1 - (#σ + 2) = d - 1 - #σ by omega, show k + 1 - (#σ + 2) = k - 1 - #σ by omega]
  · rw [mul_zero]

/-- **The links of the skeleton have the second eigenvalues of the links of `K`.** If `m`
vanishes off the sets with `d + 1` elements, `k ≤ d`, and `σ` has dimension at most `k − 2`, the
random walk on the weighted graph of the link of `σ` for the induced weight on `k`-faces has
second eigenvalue at most `lam` exactly when the one for `m` does: the two weighted graphs differ
by the factor `C(d − 1 − |σ|, k − 1 − |σ|) ≥ 1` (`linkWeightOf_skeletonWeight`).

`lam` is any real number. For `k > d` the left side would hold for every `lam`, the induced weight
being `0`. -/
theorem walkSecondEigenvalueLE_linkWeightOf_skeletonWeight_iff
    (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {σ : Finset ι} (hσ : #σ + 1 ≤ k) (hk : k ≤ d) :
    WalkSecondEigenvalueLE (linkWeightOf (skeletonWeight m k) σ) lam ↔
      WalkSecondEigenvalueLE (linkWeightOf m σ) lam := by
  have hfun : linkWeightOf (skeletonWeight m k) σ =
      fun u v => ((d - 1 - #σ).choose (k - 1 - #σ) : ℝ) * linkWeightOf m σ u v :=
    funext₂ (linkWeightOf_skeletonWeight hcard hσ)
  rw [hfun]
  exact walkSecondEigenvalueLE_const_mul_iff (Nat.cast_pos.mpr (Nat.choose_pos (by omega)))

/-- **The induced weight is a top weight of the skeleton.** If `m` is a top weight of the
`d`-dimensional complex `K` and `k ≤ d`, the induced weight on `k`-faces is a top weight of the
`k`-skeleton: the skeleton is pure of dimension `k` and has a face, every `k`-face has positive
induced weight (it lies in a top face of `K`), and every other set has induced weight `0`.

This includes `k = 0`, where the skeleton is the vertex set and each vertex is weighted by the top
faces through it. The hypothesis `k ≤ d` is needed: for `k > d` the skeleton is `K`
(`IsPure.skeleton_eq_self`), which has a face but none with `k + 1` vertices, so it is not pure of
dimension `k`; and the induced weight is `0` (`skeletonWeight_eq_zero_of_lt`). -/
theorem IsTopWeight.skeleton (hm : K.IsTopWeight d m) (hk : k ≤ d) :
    (K.skeleton k).IsTopWeight k (skeletonWeight m k) := by
  refine ⟨fun σ hσ => ?_, ?_, fun F hF hcard => ?_, fun F hF => ?_⟩
  · obtain ⟨hσK, hσc⟩ := mem_skeleton.mp hσ
    refine ⟨hσc, ?_⟩
    obtain ⟨-, F, hF, hσF, hFc⟩ := hm.isPure σ hσK
    obtain ⟨τ, hστ, hτF, hτc⟩ := Finset.exists_subsuperset_card_eq hσF hσc (by omega)
    exact ⟨τ, mem_skeleton.mpr ⟨K.mem_of_subset hF hτF (Finset.card_pos.mp (by omega)),
      hτc.le⟩, hστ, hτc⟩
  · obtain ⟨F, hF⟩ := hm.exists_mem
    obtain ⟨v, hv⟩ := K.nonempty_of_mem hF
    exact ⟨{v}, mem_skeleton.mpr ⟨K.mem_of_subset hF (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v), by simp⟩⟩
  · rw [skeletonWeight, if_pos hcard, hm.faceWeight_pos_iff]
    obtain ⟨-, G, hG, hFG, hGc⟩ := hm.isPure F (mem_skeleton.mp hF).1
    exact ⟨G, hG, hGc, hFG⟩
  · unfold skeletonWeight
    split_ifs with hcard
    · by_contra h
      have hpos : 0 < faceWeight m F :=
        lt_of_le_of_ne (faceWeight_nonneg hm.nonneg F) (Ne.symm h)
      obtain ⟨G, hG, -, hFG⟩ := hm.faceWeight_pos_iff.mp hpos
      exact hF ⟨mem_skeleton.mpr ⟨K.mem_of_subset hG hFG (Finset.card_pos.mp (by omega)),
        hcard.le⟩, hcard⟩
    · rfl

/-- **Skeleta of weighted local spectral expanders are local spectral expanders.** If `K`, with
the weight `m` on its `d`-dimensional faces, is a `lam`-local-spectral expander, then for every
`1 ≤ k ≤ d` its `k`-skeleton, with the induced weight on `k`-faces (`skeletonWeight m k`), is a
`lam`-local-spectral expander of dimension `k`, with the same `lam`.

Every link that the definition tests in the skeleton (the skeleton itself and the links of faces
of dimension at most `k − 2`) is a positive multiple of the same link in `K`
(`linkWeightOf_skeletonWeight`), which `K` already tests, so the bound carries over exactly
(`walkSecondEigenvalueLE_linkWeightOf_skeletonWeight_iff`).

Degenerate cases: `d ≥ 1` is forced by the hypothesis. `k = 0` is excluded because no complex is
a `0`-dimensional local spectral expander (`not_isLocalSpectralExpanderOf_zero`), and `k > d`
because the induced weight is then `0` (`skeletonWeight_eq_zero_of_lt`). For `k = 1` only the
weighted underlying graph is tested, and it is exactly `linkWeightOf m ∅` (the factor is
`C(d − 1, 0) = 1`); for `k = d` the statement returns the hypothesis (`IsPure.skeleton_eq_self`,
`skeletonWeight_self`). The theorem is false for uniform weights on the skeleton; see the module
docstring. -/
theorem IsLocalSpectralExpanderOf.skeleton (h : K.IsLocalSpectralExpanderOf d m lam)
    (hk1 : 1 ≤ k) (hk : k ≤ d) :
    (K.skeleton k).IsLocalSpectralExpanderOf k (skeletonWeight m k) lam := by
  refine ⟨hk1, h.isTopWeight.skeleton hk, fun σ hσ hcard => ?_⟩
  have hσK : σ = ∅ ∨ σ ∈ K := hσ.imp_right fun h' => (mem_skeleton.mp h').1
  rw [walkSecondEigenvalueLE_linkWeightOf_skeletonWeight_iff
    h.isTopWeight.card_eq_of_ne_zero hcard hk]
  exact h.walkSecondEigenvalueLE hσK (by omega)

/-- **The counting version.** If `K` is a `lam`-local-spectral expander of dimension `d` (top
faces counted, `IsLocalSpectralExpander`), then for `1 ≤ k ≤ d` its `k`-skeleton, with each
`k`-face weighted by the number of top faces of `K` through it (`skeletonWeight_uniformWeight`), is
a weighted `lam`-local-spectral expander of dimension `k`.

The conclusion is about these induced weights, not about the uniform weight of the skeleton: with
uniform weights on the skeleton the statement is false (see the module docstring). The degenerate
cases are those of `IsLocalSpectralExpanderOf.skeleton`. -/
theorem IsLocalSpectralExpander.skeleton (h : K.IsLocalSpectralExpander d lam) (hk1 : 1 ≤ k)
    (hk : k ≤ d) :
    (K.skeleton k).IsLocalSpectralExpanderOf k (skeletonWeight (K.uniformWeight d) k) lam :=
  ((K.isLocalSpectralExpander_iff_isLocalSpectralExpanderOf).mp h).skeleton hk1 hk

end Weights

end PreAbstractSimplicialComplex
