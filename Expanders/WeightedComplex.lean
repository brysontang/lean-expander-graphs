/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.HighDim
import Expanders.TricklingDownSpectral

/-!
# Weighted simplicial complexes and trickling down

The standard setting for high-dimensional expansion (Oppenheim 2018) puts a positive weight `m F`
on every top-dimensional face `F` of a pure complex. The weighted graph of the link of `σ` then
gives the edge `{u, v}` the total weight of the top faces through `σ ∪ {u, v}`. Counting top
faces, as in `PreAbstractSimplicialComplex.linkWeight`, is the special case `m ≡ 1`
(`linkWeight_eq_linkWeightOf`).

## Definitions
* `PreAbstractSimplicialComplex.faceWeight m s`: the total weight of the sets containing `s`.
* `PreAbstractSimplicialComplex.linkWeightOf m σ`: the weighted graph of the link of `σ`.
* `PreAbstractSimplicialComplex.IsTopWeight K d m`: `m` is a weight on the `d`-dimensional faces
  of the pure, nonempty complex `K`: positive on them and zero on every other set.
* `PreAbstractSimplicialComplex.uniformWeight K d`: weight `1` on every `d`-dimensional face.
* `PreAbstractSimplicialComplex.IsLocalSpectralExpanderOf K d m lam`: `d ≥ 1`, `m` is a top weight
  of `K`, and every link of a face of dimension at most `d − 2` (including the whole complex) has
  random-walk second eigenvalue at most `lam` for the weights `m`.

## Theorems
* `sum_faceWeight_insert`, `sum_linkWeightOf`, `sum_linkWeightOf_insert`,
  `sum_linkWeightOf_insert_right`: double counting, giving the degrees of a link and the
  localisation of a link to its vertex links. These need only that `m` vanishes off the sets with
  `d + 1` elements. **Proved.**
* `IsTopWeight.exists_linkWeightOf_pos`: every link that `IsLocalSpectralExpanderOf` quantifies
  over has an edge, so no instance of its second-eigenvalue bound is vacuous. **Proved.**
* `trickling_down_weighted`: Oppenheim's local-to-global theorem for arbitrary top-face weights,
  and `isLocalSpectralExpanderOf_of_trickling_down_weighted`, its conclusion as a statement that
  the weighted complex is a local spectral expander, for either sign of `lam`. **Proved.**
* `link_walk_lower_bound`: the quadratic form of the link of `σ` is at least `−1 / (d − |σ|)`
  times the degree-weighted norm, so no eigenvalue of the random walk on a link is below
  `−1 / (d − |σ|)`. **Proved.**
* `IsLocalSpectralExpanderOf.neg_one_div_le`: consequently a `lam`-local-spectral expander of
  dimension `d` has `lam ≥ −1/d`. **Proved.**

## Which way the specialisation runs

The weighted graph of a link has the same *edges* for every admissible weight
(`IsTopWeight.linkWeightOf_pos_iff_linkWeight_pos`), so facts that only see which weights are
positive (existence of an edge, connectivity) are proved once, for counts, in
`Expanders/HighDim.lean` and transferred here. Facts that see the *values* of the weights (the
counting identities, trickling down) are proved here once, for arbitrary weights, and
specialised to counts in `Expanders/TricklingDown.lean`.
-/

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*}

/-! ### Weights of faces and of link edges -/

section Weights

variable [DecidableEq ι] [Fintype ι]

/-- The **weight of `s`** induced by a weight `m` on top faces: the total weight `∑ m F` of the
sets `F ⊇ s`.

The definition does not mention a complex: it sums `m` over *all* finite sets containing `s`. It
has its intended meaning when `m` vanishes off the top faces of a complex (`IsTopWeight`), and
then `faceWeight m s` is the weight of the top faces through `s`; `faceWeight m ∅` is the total
weight. (In Oppenheim's normalisation the weight of a `k`-dimensional face is `(d − k)!` times
this; the factor is constant on each link graph and does not affect the random walk.) -/
noncomputable def faceWeight (m : Finset ι → ℝ) (s : Finset ι) : ℝ :=
  ∑ F with s ⊆ F, m F

/-- The **weighted graph of the link of `σ`** for a weight `m` on top faces: two distinct
vertices `u, v` outside `σ` are joined with the total weight of the top faces containing
`σ ∪ {u, v}`. For `σ = ∅` this is the weighted underlying graph of the complex.

Degenerate arguments, all of which give weight `0`:
* `u = v` (no loops), and `u ∈ σ` or `v ∈ σ` (`linkWeightOf_self`,
  `linkWeightOf_eq_zero_of_mem_left`, `linkWeightOf_eq_zero_of_mem_right`). The graph lives on
  all of `ι`; the vertices of `σ`, and every vertex outside the link, are isolated.
* `σ` with at least `d` elements, when `m` is supported on sets with `d + 1` elements: a top face
  through `σ` has at most one further vertex (`linkWeightOf_eq_zero_of_le_card`).
* `σ` nonempty and not a face, when `m` is a top weight of `K`
  (`IsTopWeight.linkWeightOf_eq_zero_of_notMem`).

Like `faceWeight`, the definition reads `m` on every finite set. If `m` takes negative values the
"weights" can be negative; every theorem below states the sign hypothesis it needs. -/
noncomputable def linkWeightOf (m : Finset ι → ℝ) (σ : Finset ι) (u v : ι) : ℝ :=
  if u ≠ v ∧ u ∉ σ ∧ v ∉ σ then faceWeight m (insert u (insert v σ)) else 0

variable {m : Finset ι → ℝ} {d : ℕ}

theorem faceWeight_nonneg (hnn : ∀ F, 0 ≤ m F) (s : Finset ι) : 0 ≤ faceWeight m s :=
  Finset.sum_nonneg fun F _ => hnn F

/-- For nonnegative `m`, a set has positive weight exactly when it lies in a set of positive
weight. -/
theorem faceWeight_pos_iff (hnn : ∀ F, 0 ≤ m F) {s : Finset ι} :
    0 < faceWeight m s ↔ ∃ F, s ⊆ F ∧ 0 < m F := by
  unfold faceWeight
  rw [Finset.sum_pos_iff_of_nonneg fun F _ => hnn F]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- A set with more than `d + 1` elements lies in no top face, so it has weight `0`. -/
theorem faceWeight_eq_zero_of_lt_card (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {s : Finset ι}
    (hs : d + 1 < #s) : faceWeight m s = 0 := by
  refine Finset.sum_eq_zero fun F hF => ?_
  rw [Finset.mem_filter] at hF
  by_contra h
  have hle := Finset.card_le_card hF.2
  rw [hcard F h] at hle
  omega

/-- The weight of `s ∪ {v}`, as a sum over the sets containing `s`. -/
theorem faceWeight_insert (m : Finset ι → ℝ) (v : ι) (s : Finset ι) :
    faceWeight m (insert v s) = ∑ F with s ⊆ F, if v ∈ F then m F else 0 := by
  unfold faceWeight
  rw [← Finset.sum_filter, Finset.filter_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext F
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.insert_subset_iff, and_comm]

theorem linkWeightOf_nonneg (hnn : ∀ F, 0 ≤ m F) (σ : Finset ι) (u v : ι) :
    0 ≤ linkWeightOf m σ u v := by
  unfold linkWeightOf
  split_ifs
  · exact faceWeight_nonneg hnn _
  · exact le_rfl

theorem linkWeightOf_symm (m : Finset ι → ℝ) (σ : Finset ι) (u v : ι) :
    linkWeightOf m σ u v = linkWeightOf m σ v u := by
  unfold linkWeightOf
  rw [Finset.insert_comm u v σ]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.symm, h3, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.symm, h3, h2⟩

/-- The weighted graph of a link has no loops. -/
@[simp]
theorem linkWeightOf_self (m : Finset ι → ℝ) (σ : Finset ι) (u : ι) : linkWeightOf m σ u u = 0 :=
  if_neg fun h => h.1 rfl

/-- A vertex of `σ` is isolated in the weighted graph of the link of `σ`. -/
theorem linkWeightOf_eq_zero_of_mem_left (m : Finset ι → ℝ) {σ : Finset ι} {u : ι} (hu : u ∈ σ)
    (v : ι) : linkWeightOf m σ u v = 0 :=
  if_neg fun h => h.2.1 hu

/-- A vertex of `σ` is isolated in the weighted graph of the link of `σ`. -/
theorem linkWeightOf_eq_zero_of_mem_right (m : Finset ι → ℝ) {σ : Finset ι} (u : ι) {v : ι}
    (hv : v ∈ σ) : linkWeightOf m σ u v = 0 :=
  if_neg fun h => h.2.2 hv

/-- For nonnegative `m`, `u v` is an edge of the link of `σ` exactly when `u ≠ v` lie outside `σ`
and `σ ∪ {u, v}` lies in a set of positive weight. -/
theorem linkWeightOf_pos_iff (hnn : ∀ F, 0 ≤ m F) {σ : Finset ι} {u v : ι} :
    0 < linkWeightOf m σ u v ↔
      u ≠ v ∧ u ∉ σ ∧ v ∉ σ ∧ ∃ F, insert u (insert v σ) ⊆ F ∧ 0 < m F := by
  unfold linkWeightOf
  split_ifs with h
  · rw [faceWeight_pos_iff hnn]
    exact ⟨fun hF => ⟨h.1, h.2.1, h.2.2, hF⟩, fun hF => hF.2.2.2⟩
  · exact ⟨fun h0 => absurd h0 (lt_irrefl _), fun hF => absurd ⟨hF.1, hF.2.1, hF.2.2.1⟩ h⟩

/-- **No edges above dimension `d − 2`.** If `σ` has at least `d` elements, a top face through
`σ` has at most one further vertex, so the weighted graph of the link of `σ` has no edges. -/
theorem linkWeightOf_eq_zero_of_le_card (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {σ : Finset ι}
    (hσ : d ≤ #σ) (u v : ι) : linkWeightOf m σ u v = 0 := by
  unfold linkWeightOf
  split_ifs with h
  · refine faceWeight_eq_zero_of_lt_card hcard ?_
    have huv : u ∉ insert v σ := by
      rw [Finset.mem_insert, not_or]
      exact ⟨h.1, h.2.1⟩
    rw [Finset.card_insert_of_notMem huv, Finset.card_insert_of_notMem h.2.2]
    omega
  · rfl

end Weights

/-! ### Weights on the top faces of a complex -/

/-- `m` is a **top weight** of the `d`-dimensional complex `K`: `K` is pure of dimension `d` and
has at least one face, `m` is positive on every `d`-dimensional face of `K`, and `m` is zero on
every other finite set.

What the conditions exclude:
* *The empty complex* (`exists_mem`). It is pure of every dimension, and without this field the
  zero function would be a top weight of it.
* *Zero or negative weight on a top face* (`pos`). A top face of weight `0` would still be a face
  of `K` but invisible to every weighted graph, so that connectivity of the links of `K` would say
  nothing about the weighted graphs.
* *Weight on anything else* (`eq_zero`): on a face of lower dimension, or on a set that is not a
  face. `faceWeight` and `linkWeightOf` read `m` on every finite set, so this is what ties them to
  `K`. Together with `pos`: `0 < m F` exactly when `F` is a `d`-dimensional face
  (`IsTopWeight.pos_iff`), and `K` is recovered from `m` as the nonempty subsets of its support.

For `d = 0` the top faces are the vertices and `m` is a positive weight on them; every
`linkWeightOf m σ` is then zero (`linkWeightOf_eq_zero_of_le_card`). A complex with a single top
face `F` has exactly the top weights `c · 1_F` with `c > 0`. -/
structure IsTopWeight (K : PreAbstractSimplicialComplex ι) (d : ℕ) (m : Finset ι → ℝ) : Prop where
  /-- `K` is pure of dimension `d`. -/
  isPure : K.IsPure d
  /-- `K` has at least one face. -/
  exists_mem : ∃ F, F ∈ K
  /-- Every `d`-dimensional face has positive weight. -/
  pos : ∀ F ∈ K, #F = d + 1 → 0 < m F
  /-- Every set that is not a `d`-dimensional face has weight zero. -/
  eq_zero : ∀ F, ¬(F ∈ K ∧ #F = d + 1) → m F = 0

namespace IsTopWeight

variable {K : PreAbstractSimplicialComplex ι} {d : ℕ} {m : Finset ι → ℝ}

theorem nonneg (hm : K.IsTopWeight d m) (F : Finset ι) : 0 ≤ m F := by
  by_cases h : F ∈ K ∧ #F = d + 1
  · exact (hm.pos F h.1 h.2).le
  · exact (hm.eq_zero F h).ge

/-- A top weight is positive exactly on the `d`-dimensional faces. -/
theorem pos_iff (hm : K.IsTopWeight d m) {F : Finset ι} : 0 < m F ↔ F ∈ K ∧ #F = d + 1 :=
  ⟨fun h => by_contra fun hF => h.ne' (hm.eq_zero F hF), fun h => hm.pos F h.1 h.2⟩

theorem ne_zero_iff (hm : K.IsTopWeight d m) {F : Finset ι} : m F ≠ 0 ↔ F ∈ K ∧ #F = d + 1 :=
  ⟨fun h => by_contra fun hF => h (hm.eq_zero F hF), fun h => (hm.pos F h.1 h.2).ne'⟩

/-- A top weight is supported on sets with `d + 1` elements. This is the only hypothesis of the
counting identities below. -/
theorem card_eq_of_ne_zero (hm : K.IsTopWeight d m) (F : Finset ι) (h : m F ≠ 0) :
    #F = d + 1 :=
  (hm.ne_zero_iff.mp h).2

/-- A top weight of `K` is supported on faces of `K`. -/
theorem mem_of_ne_zero (hm : K.IsTopWeight d m) {F : Finset ι} (h : m F ≠ 0) : F ∈ K :=
  (hm.ne_zero_iff.mp h).1

/-- A top weight has a top face of positive weight. -/
theorem exists_pos (hm : K.IsTopWeight d m) : ∃ F ∈ K, #F = d + 1 ∧ 0 < m F := by
  obtain ⟨F, hF, hcard⟩ := hm.isPure.exists_card_eq hm.exists_mem
  exact ⟨F, hF, hcard, hm.pos F hF hcard⟩

end IsTopWeight

/-! ### The uniform weight: counting top faces -/

section Uniform

variable (K : PreAbstractSimplicialComplex ι)

open Classical in
/-- The **uniform weight** of a `d`-dimensional complex: `1` on every `d`-dimensional face and
`0` on every other set. The weighted graphs it defines are the counting ones,
`linkWeight_eq_linkWeightOf`. -/
noncomputable def uniformWeight (d : ℕ) (F : Finset ι) : ℝ :=
  if F ∈ K ∧ #F = d + 1 then 1 else 0

theorem uniformWeight_nonneg (d : ℕ) (F : Finset ι) : 0 ≤ K.uniformWeight d F := by
  unfold uniformWeight
  split_ifs <;> norm_num

theorem card_eq_of_uniformWeight_ne_zero (d : ℕ) (F : Finset ι) (h : K.uniformWeight d F ≠ 0) :
    #F = d + 1 := by
  unfold uniformWeight at h
  split_ifs at h with hF
  · exact hF.2
  · exact absurd rfl h

/-- The uniform weight is a top weight exactly when the complex is pure and has a face. -/
theorem isTopWeight_uniformWeight_iff {d : ℕ} :
    K.IsTopWeight d (K.uniformWeight d) ↔ K.IsPure d ∧ ∃ F, F ∈ K := by
  refine ⟨fun h => ⟨h.isPure, h.exists_mem⟩,
    fun h => ⟨h.1, h.2, fun F hF hcard => ?_, fun F hF => ?_⟩⟩
  · rw [uniformWeight, if_pos ⟨hF, hcard⟩]
    exact one_pos
  · rw [uniformWeight, if_neg hF]

theorem isTopWeight_uniformWeight {d : ℕ} (hpure : K.IsPure d) (hne : ∃ F, F ∈ K) :
    K.IsTopWeight d (K.uniformWeight d) :=
  K.isTopWeight_uniformWeight_iff.mpr ⟨hpure, hne⟩

variable [DecidableEq ι] [Fintype ι]

/-- Counting top faces is weighing them uniformly. -/
theorem topDegree_eq_faceWeight (d : ℕ) (s : Finset ι) :
    (K.topDegree d s : ℝ) = faceWeight (K.uniformWeight d) s := by
  classical
  unfold topDegree faceWeight uniformWeight
  rw [Finset.card_filter, Finset.sum_filter]
  push_cast
  refine Finset.sum_congr rfl fun F _ => ?_
  by_cases h1 : s ⊆ F <;> by_cases h2 : F ∈ K ∧ #F = d + 1 <;> simp [h1, h2]

/-- **Counting is the uniform special case.** The weighted graph of the link of `σ` that counts
top faces is the one defined by the uniform weight. -/
theorem linkWeight_eq_linkWeightOf (d : ℕ) (σ : Finset ι) :
    K.linkWeight d σ = linkWeightOf (K.uniformWeight d) σ := by
  funext u v
  unfold linkWeight linkWeightOf
  rw [topDegree_eq_faceWeight]

end Uniform

section Complex

variable [DecidableEq ι] [Fintype ι] {K : PreAbstractSimplicialComplex ι} {d : ℕ}
  {m : Finset ι → ℝ}

/-! ### Edges of the weighted link graphs -/

theorem IsTopWeight.faceWeight_pos_iff (hm : K.IsTopWeight d m) {s : Finset ι} :
    0 < faceWeight m s ↔ ∃ F ∈ K, #F = d + 1 ∧ s ⊆ F := by
  rw [PreAbstractSimplicialComplex.faceWeight_pos_iff hm.nonneg]
  constructor
  · rintro ⟨F, hsF, hF⟩
    obtain ⟨h1, h2⟩ := hm.pos_iff.mp hF
    exact ⟨F, h1, h2, hsF⟩
  · rintro ⟨F, h1, h2, hsF⟩
    exact ⟨F, hsF, hm.pos F h1 h2⟩

/-- For a top weight, `u v` is an edge of the link of `σ` exactly when `u ≠ v` lie outside `σ` and
`σ ∪ {u, v}` lies in a top face. The right-hand side does not depend on `m`. -/
theorem IsTopWeight.linkWeightOf_pos_iff (hm : K.IsTopWeight d m) {σ : Finset ι} {u v : ι} :
    0 < linkWeightOf m σ u v ↔
      u ≠ v ∧ u ∉ σ ∧ v ∉ σ ∧ ∃ F ∈ K, #F = d + 1 ∧ insert u (insert v σ) ⊆ F := by
  unfold linkWeightOf
  split_ifs with h
  · rw [hm.faceWeight_pos_iff]
    exact ⟨fun hF => ⟨h.1, h.2.1, h.2.2, hF⟩, fun hF => hF.2.2.2⟩
  · exact ⟨fun h0 => absurd h0 (lt_irrefl _), fun hF => absurd ⟨hF.1, hF.2.1, hF.2.2.1⟩ h⟩

/-- **Every top weight has the same edges.** The weighted graph of a link has an edge of positive
weight exactly where the counting one does. -/
theorem IsTopWeight.linkWeightOf_pos_iff_linkWeight_pos (hm : K.IsTopWeight d m) {σ : Finset ι}
    {u v : ι} : 0 < linkWeightOf m σ u v ↔ 0 < K.linkWeight d σ u v :=
  hm.linkWeightOf_pos_iff.trans K.linkWeight_pos_iff.symm

/-- A vertex has positive degree in the weighted graph of a link exactly when it does in the
counting one. -/
theorem IsTopWeight.sum_linkWeightOf_pos_iff (hm : K.IsTopWeight d m) {σ : Finset ι} {u : ι} :
    0 < ∑ x, linkWeightOf m σ u x ↔ 0 < ∑ x, K.linkWeight d σ u x := by
  rw [Finset.sum_pos_iff_of_nonneg fun x _ => linkWeightOf_nonneg hm.nonneg σ u x,
    Finset.sum_pos_iff_of_nonneg fun x _ => K.linkWeight_nonneg d σ u x]
  simp only [hm.linkWeightOf_pos_iff_linkWeight_pos]

/-- The weighted graph of the "link" of a nonempty set that is not a face is empty. -/
theorem IsTopWeight.linkWeightOf_eq_zero_of_notMem (hm : K.IsTopWeight d m) {τ : Finset ι}
    (hne : τ.Nonempty) (hτ : τ ∉ K) (u v : ι) : linkWeightOf m τ u v = 0 := by
  by_contra h
  have hpos : 0 < linkWeightOf m τ u v :=
    lt_of_le_of_ne (linkWeightOf_nonneg hm.nonneg τ u v) (Ne.symm h)
  rw [hm.linkWeightOf_pos_iff_linkWeight_pos, K.linkWeight_eq_zero_of_notMem hne hτ] at hpos
  exact lt_irrefl _ hpos

/-- **Non-vacuity.** For a top weight of a `d`-dimensional complex, the weighted graph of the link
of a set `σ` of dimension at most `d − 2` that lies in some face has an edge of positive weight. -/
theorem IsTopWeight.exists_linkWeightOf_pos_of_subset (hm : K.IsTopWeight d m) {σ τ : Finset ι}
    (hτ : τ ∈ K) (hστ : σ ⊆ τ) (hcard : #σ + 1 ≤ d) : ∃ u v, 0 < linkWeightOf m σ u v := by
  obtain ⟨u, v, h⟩ := K.exists_linkWeight_pos hm.isPure hτ hστ hcard
  exact ⟨u, v, hm.linkWeightOf_pos_iff_linkWeight_pos.mpr h⟩

/-- **Non-vacuity of `IsLocalSpectralExpanderOf`.** For a top weight, every link that the
definition of a local spectral expander quantifies over (the complex itself and the link of every
face of dimension at most `d − 2`) has an edge of positive weight. So the second-eigenvalue bound
is never the vacuous one of `walkSecondEigenvalueLE_of_forall_eq_zero`. -/
theorem IsTopWeight.exists_linkWeightOf_pos (hm : K.IsTopWeight d m) {σ : Finset ι}
    (hσ : σ = ∅ ∨ σ ∈ K) (hcard : #σ + 1 ≤ d) : ∃ u v, 0 < linkWeightOf m σ u v := by
  rcases hσ with rfl | hσ
  · obtain ⟨τ, hτ⟩ := hm.exists_mem
    exact hm.exists_linkWeightOf_pos_of_subset hτ (Finset.empty_subset τ) hcard
  · exact hm.exists_linkWeightOf_pos_of_subset hσ subset_rfl hcard

/-- **Connectivity, in weighted form.** If the link of `σ` is connected, a function that is
constant along every edge of positive weight takes a single value on all vertices of positive
degree. -/
theorem IsTopWeight.eq_of_forall_linkWeightOf_pos (hm : K.IsTopWeight d m) {σ : Finset ι}
    (hconn : (K.link σ).IsConnected) (g : ι → ℝ)
    (hg : ∀ u v, 0 < linkWeightOf m σ u v → g u = g v) (u v : ι)
    (hu : 0 < ∑ x, linkWeightOf m σ u x) (hv : 0 < ∑ x, linkWeightOf m σ v x) : g u = g v :=
  K.eq_of_forall_linkWeight_pos hm.isPure hconn g
    (fun a b h => hg a b (hm.linkWeightOf_pos_iff_linkWeight_pos.mpr h)) u v
    (hm.sum_linkWeightOf_pos_iff.mp hu) (hm.sum_linkWeightOf_pos_iff.mp hv)

/-! ### Double counting -/

/-- **Double counting, with a test function.** Summing `g u` times the weight of `s ∪ {u}` over
the vertices `u ∉ s` weighs each set `F ⊇ s` by the sum of `g` over `F \ s`. No hypothesis on
`m`. -/
theorem sum_faceWeight_insert_mul (m : Finset ι → ℝ) (s : Finset ι) (g : ι → ℝ) :
    ∑ u, (if u ∈ s then 0 else faceWeight m (insert u s)) * g u =
      ∑ F with s ⊆ F, m F * ∑ v ∈ F \ s, g v := by
  have h : ∀ u, (if u ∈ s then 0 else faceWeight m (insert u s)) * g u =
      ∑ F with s ⊆ F, if u ∈ F \ s then m F * g u else 0 := by
    intro u
    by_cases hu : u ∈ s
    · rw [if_pos hu, zero_mul]
      exact (Finset.sum_eq_zero fun F _ => if_neg fun h => (Finset.mem_sdiff.mp h).2 hu).symm
    · rw [if_neg hu, faceWeight_insert, Finset.sum_mul]
      refine Finset.sum_congr rfl fun F _ => ?_
      by_cases huF : u ∈ F
      · rw [if_pos huF, if_pos (Finset.mem_sdiff.mpr ⟨huF, hu⟩)]
      · rw [if_neg huF, zero_mul, if_neg fun h => huF (Finset.mem_sdiff.mp h).1]
  rw [Finset.sum_congr rfl fun u _ => h u, Finset.sum_comm]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [Fintype.sum_ite_mem, Finset.mul_sum]

/-- **Double counting.** Every top face through `s` has exactly `d + 1 − |s|` vertices outside
`s`, so summing the weight of `s ∪ {v}` over `v ∉ s` weighs each such face `d + 1 − |s|` times.
The only hypothesis is that `m` vanishes off the sets with `d + 1` elements. -/
theorem sum_faceWeight_insert (hcard : ∀ F, m F ≠ 0 → #F = d + 1) (s : Finset ι) :
    ∑ v, (if v ∈ s then 0 else faceWeight m (insert v s)) =
      ((d : ℝ) + 1 - #s) * faceWeight m s := by
  have h := sum_faceWeight_insert_mul m s fun _ => (1 : ℝ)
  simp only [mul_one] at h
  rw [h, faceWeight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun F hF => ?_
  rw [Finset.mem_filter] at hF
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  by_cases h0 : m F = 0
  · rw [h0, zero_mul, mul_zero]
  · have h1 := Finset.card_sdiff_add_card_eq_card hF.2
    rw [hcard F h0] at h1
    have h2 : (#(F \ s) : ℝ) + #s = (d : ℝ) + 1 := by exact_mod_cast h1
    rw [show (#(F \ s) : ℝ) = (d : ℝ) + 1 - #s by linarith]
    ring

/-- **Degrees in a link.** The degree of `u ∉ τ` in the weighted graph of the link of `τ` is
`d − |τ|` times the weight of `τ ∪ {u}`. -/
theorem sum_linkWeightOf (hcard : ∀ F, m F ≠ 0 → #F = d + 1) (τ : Finset ι) (u : ι) :
    ∑ v, linkWeightOf m τ u v =
      if u ∈ τ then 0 else ((d : ℝ) - #τ) * faceWeight m (insert u τ) := by
  split_ifs with hu
  · exact Finset.sum_eq_zero fun v _ => linkWeightOf_eq_zero_of_mem_left m hu v
  · have h := sum_faceWeight_insert hcard (insert u τ)
    rw [Finset.card_insert_of_notMem hu] at h
    push_cast at h
    rw [show (d : ℝ) - #τ = (d : ℝ) + 1 - (#τ + 1) by ring, ← h]
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold linkWeightOf
    by_cases hv : v ∈ insert u τ
    · rw [if_pos hv, if_neg]
      rintro ⟨h1, -, h3⟩
      rcases Finset.mem_insert.mp hv with h | h
      · exact h1 h.symm
      · exact h3 h
    · rw [if_neg hv, Finset.insert_comm v u]
      rw [Finset.mem_insert, not_or] at hv
      exact if_pos ⟨Ne.symm hv.1, hu, hv.2⟩

/-- **Localisation of weights.** The weight of an edge in the link of `σ` is the average, over
the further vertices `z` of the top faces through it, of its weight in the link of `σ ∪ {z}`:
each top face through `σ ∪ {u, v}` has `d − 1 − |σ|` further vertices. -/
theorem sum_linkWeightOf_insert (hcard : ∀ F, m F ≠ 0 → #F = d + 1) (σ : Finset ι) (u v : ι) :
    ∑ z, (if z ∈ σ then 0 else linkWeightOf m (insert z σ) u v) =
      ((d : ℝ) - 1 - #σ) * linkWeightOf m σ u v := by
  by_cases h : u ≠ v ∧ u ∉ σ ∧ v ∉ σ
  · have hs : #(insert u (insert v σ)) = #σ + 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem h.2.2]
      rw [Finset.mem_insert, not_or]
      exact ⟨h.1, h.2.1⟩
    have h1 := sum_faceWeight_insert hcard (insert u (insert v σ))
    rw [hs] at h1
    push_cast at h1
    rw [linkWeightOf, if_pos h, show (d : ℝ) - 1 - #σ = (d : ℝ) + 1 - (#σ + 2) by ring, ← h1]
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold linkWeightOf
    by_cases hz : z ∈ σ
    · rw [if_pos hz, if_pos (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))]
    · rw [if_neg hz]
      by_cases hz' : z ∈ insert u (insert v σ)
      · rw [if_pos hz', if_neg]
        rintro ⟨-, h2, h3⟩
        simp only [Finset.mem_insert, not_or] at h2 h3
        rcases Finset.mem_insert.mp hz' with rfl | hz'
        · exact h2.1 rfl
        · rcases Finset.mem_insert.mp hz' with rfl | hz'
          · exact h3.1 rfl
          · exact hz hz'
      · rw [if_neg hz', Finset.insert_comm z u, Finset.insert_comm z v]
        simp only [Finset.mem_insert, not_or] at hz'
        refine if_pos ⟨h.1, ?_, ?_⟩
        · rw [Finset.mem_insert, not_or]
          exact ⟨Ne.symm hz'.1, h.2.1⟩
        · rw [Finset.mem_insert, not_or]
          exact ⟨Ne.symm hz'.2.1, h.2.2⟩
  · rw [linkWeightOf, if_neg h, mul_zero]
    refine Finset.sum_eq_zero fun z _ => ?_
    split_ifs with hz
    · rfl
    · unfold linkWeightOf
      refine if_neg fun h' => h ⟨h'.1, ?_, ?_⟩
      · exact fun hu => h'.2.1 (Finset.mem_insert_of_mem hu)
      · exact fun hv => h'.2.2 (Finset.mem_insert_of_mem hv)

/-- **Localisation of degrees.** The degree of `u` in the link of `σ ∪ {z}` is `d − 1 − |σ|`
times the weight of the edge `z u` in the link of `σ`. -/
theorem sum_linkWeightOf_insert_right (hcard : ∀ F, m F ≠ 0 → #F = d + 1) (σ : Finset ι)
    (z u : ι) :
    ∑ v, (if z ∈ σ then 0 else linkWeightOf m (insert z σ) u v) =
      ((d : ℝ) - 1 - #σ) * linkWeightOf m σ z u := by
  by_cases hz : z ∈ σ
  · simp [hz, linkWeightOf_eq_zero_of_mem_left m hz u]
  · simp only [if_neg hz]
    rw [sum_linkWeightOf hcard (insert z σ) u, Finset.card_insert_of_notMem hz]
    by_cases hu : u ∈ insert z σ
    · have h0 : linkWeightOf m σ z u = 0 := by
        unfold linkWeightOf
        refine if_neg ?_
        rintro ⟨h1, -, h3⟩
        rcases Finset.mem_insert.mp hu with h | h
        · exact h1 h.symm
        · exact h3 h
      rw [if_pos hu, h0, mul_zero]
    · rw [if_neg hu]
      rw [Finset.mem_insert, not_or] at hu
      rw [linkWeightOf, if_pos ⟨Ne.symm hu.1, hz, hu.2⟩, Finset.insert_comm z u]
      push_cast
      ring

/-! ### Trickling down -/

/-- **One step of trickling down.** Let `σ` have dimension at most `d − 3` (possibly `σ = ∅`),
with connected link. If the link of every face `σ ∪ {z}` has second eigenvalue at most `μ < 1`,
then the link of `σ` has second eigenvalue at most `μ / (1 − μ)`. -/
theorem IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_step (hm : K.IsTopWeight d m)
    {σ : Finset ι} (hcard : #σ + 2 ≤ d) (hconn : (K.link σ).IsConnected) {μ : ℝ} (hμ : μ < 1)
    (hloc : ∀ z, z ∉ σ → insert z σ ∈ K →
      WalkSecondEigenvalueLE (linkWeightOf m (insert z σ)) μ) :
    WalkSecondEigenvalueLE (linkWeightOf m σ) (μ / (1 - μ)) := by
  have hc : (0 : ℝ) < (d : ℝ) - 1 - #σ := by
    have h : ((#σ + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hcard
    push_cast at h
    linarith
  refine walkSecondEigenvalueLE_of_garland (linkWeightOf_symm m σ)
    (linkWeightOf_nonneg hm.nonneg σ) hμ (hm.eq_of_forall_linkWeightOf_pos hconn) ?_
  refine garland_inequality
    (wz := fun z u v => if z ∈ σ then 0 else linkWeightOf m (insert z σ) u v) hc
    (linkWeightOf_symm m σ) ?_ (sum_linkWeightOf_insert hm.card_eq_of_ne_zero σ)
    (sum_linkWeightOf_insert_right hm.card_eq_of_ne_zero σ) ?_
  · intro z u v
    split_ifs
    · rfl
    · exact linkWeightOf_symm m (insert z σ) u v
  · intro z
    by_cases hz : z ∈ σ
    · intro f _
      simp [hz]
    · by_cases hK : insert z σ ∈ K
      · simpa only [if_neg hz] using hloc z hz hK
      · intro f _
        simp [hz, hm.linkWeightOf_eq_zero_of_notMem (Finset.insert_nonempty z σ) hK]

variable (K) in
/-- **Trickling down (Oppenheim), for weighted complexes.** Let `K` be a pure `d`-dimensional
complex, `d ≥ 2`, with a positive weight `m` on its top faces, in which `K` itself and every link
of a face of dimension at most `d − 3` is connected. If the link of every `(d − 2)`-dimensional
face has second eigenvalue at most `lam`, where `(d − 1) · lam < 1`, then the link of every face
`σ` of dimension at most `d − 2` has second eigenvalue at most
`lam / (1 − (d − 1 − |σ|) · lam)`; taking `σ = ∅`, the weighted underlying graph of `K` has
second eigenvalue at most `lam / (1 − (d − 1) · lam)`.

Connectivity of the links of the `(d − 2)`-dimensional faces is not assumed: their eigenvalue
bound is the hypothesis `hlocal`, and connectivity is used only in the inductive step, for the
links of faces of dimension at most `d − 3` and for `K` itself.

The hypothesis `(d − 1) · lam < 1` (which makes every denominator positive) is broader than the
range in which the conclusion is nontrivial. A bound of `1` or more on the second eigenvalue
holds for every graph with symmetric nonnegative weights, and the bound for the whole complex,
`lam / (1 − (d − 1) · lam)`, is below `1` exactly when `lam < 1/d`. For example, for `d = 2` and
`lam = 3/4` the hypothesis holds but the conclusion only bounds the second eigenvalue of the
underlying graph by `3`.

The proof is by downward induction on `|σ|`; the inductive step
(`IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_step`) localises the quadratic form of a link to
its vertex links (Garland's method, `garland_inequality`) and solves a quadratic inequality for
the second eigenvalue (`walkSecondEigenvalueLE_of_garland`). The weights enter only through the
double-counting identities `sum_linkWeightOf_insert` and `sum_linkWeightOf_insert_right`.

The counting version `trickling_down` is the case `m = K.uniformWeight d`. -/
theorem trickling_down_weighted {d : ℕ} (hd : 2 ≤ d) {m : Finset ι → ℝ} (hm : K.IsTopWeight d m)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ d → (K.link σ).IsConnected)
    {lam : ℝ} (hlam : ((d : ℝ) - 1) * lam < 1)
    (hlocal : ∀ σ ∈ K, #σ + 1 = d → WalkSecondEigenvalueLE (linkWeightOf m σ) lam) :
    ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d →
      WalkSecondEigenvalueLE (linkWeightOf m σ) (lam / (1 - ((d : ℝ) - 1 - #σ) * lam)) := by
  -- every denominator that occurs is positive
  have hpos : ∀ j : ℕ, j + 1 ≤ d → 0 < 1 - (j : ℝ) * lam := by
    intro j hj
    have hj' : (j : ℝ) + 1 ≤ d := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rcases le_or_gt 0 lam with h | h
    · nlinarith
    · nlinarith
  -- induction on `j = d − 1 − |σ|`
  have key : ∀ j : ℕ, ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 + j = d →
      WalkSecondEigenvalueLE (linkWeightOf m σ) (lam / (1 - (j : ℝ) * lam)) := by
    intro j
    induction j with
    | zero =>
      intro σ hσ hcard
      have hσK : σ ∈ K := by
        rcases hσ with rfl | h
        · rw [Finset.card_empty] at hcard
          omega
        · exact h
      simpa using hlocal σ hσK (by omega)
    | succ j ih =>
      intro σ hσ hcard
      have h1 := hpos j (by omega)
      have h2 := hpos (j + 1) (by omega)
      push_cast at h2
      have hμ : lam / (1 - (j : ℝ) * lam) < 1 := by
        rw [div_lt_one h1]
        linarith
      have hstep := hm.walkSecondEigenvalueLE_linkWeightOf_step (σ := σ) (by omega)
        (hconn σ hσ (by omega)) hμ fun z hz hK =>
          ih (insert z σ) (Or.inr hK) (by rw [Finset.card_insert_of_notMem hz]; omega)
      have e : lam / (1 - (j : ℝ) * lam) / (1 - lam / (1 - (j : ℝ) * lam))
          = lam / (1 - ((j : ℝ) + 1) * lam) := by
        have e1 : 1 - lam / (1 - (j : ℝ) * lam)
            = (1 - ((j : ℝ) + 1) * lam) / (1 - (j : ℝ) * lam) := by
          rw [eq_div_iff h1.ne', sub_mul, div_mul_cancel₀ _ h1.ne']
          ring
        rw [e1, div_div_div_cancel_right₀ h1.ne']
      rw [e] at hstep
      simpa using hstep
  intro σ hσ hcard
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hcard
  have hj' : (d : ℝ) - 1 - #σ = j := by
    have h : (d : ℝ) = #σ + 1 + j := by exact_mod_cast hj
    linarith
  rw [hj']
  exact key j σ hσ hj.symm

/-! ### A lower bound for the eigenvalues of a link -/

/-- The weight of an edge of the link of `σ`, as a sum over the sets containing `σ`. -/
theorem linkWeightOf_eq_sum (m : Finset ι → ℝ) (σ : Finset ι) (u v : ι) :
    linkWeightOf m σ u v =
      ∑ F with σ ⊆ F, if u ≠ v ∧ u ∈ F \ σ ∧ v ∈ F \ σ then m F else 0 := by
  unfold linkWeightOf
  by_cases h : u ≠ v ∧ u ∉ σ ∧ v ∉ σ
  · rw [if_pos h, faceWeight, ← Finset.sum_filter, Finset.filter_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.insert_subset_iff,
      Finset.mem_sdiff]
    tauto
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun F _ => if_neg fun h' => h ?_).symm
    exact ⟨h'.1, (Finset.mem_sdiff.mp h'.2.1).2, (Finset.mem_sdiff.mp h'.2.2).2⟩

/-- The sum of `f u * f v` over ordered pairs of distinct elements of `T` is the square of the sum
minus the sum of the squares. -/
private theorem sum_sum_ite_ne_mul (T : Finset ι) (f : ι → ℝ) :
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

/-- **The quadratic form of a link, face by face.** Each set `F ⊇ σ` contributes its weight times
the sum of `f u * f v` over the ordered pairs of distinct vertices of `F \ σ`. No hypothesis on
`m`. -/
theorem sum_linkWeightOf_mul_mul (m : Finset ι → ℝ) (σ : Finset ι) (f : ι → ℝ) :
    ∑ u, ∑ v, linkWeightOf m σ u v * f u * f v =
      ∑ F with σ ⊆ F, m F * ((∑ v ∈ F \ σ, f v) ^ 2 - ∑ v ∈ F \ σ, f v ^ 2) := by
  have h1 : ∀ u v, linkWeightOf m σ u v * f u * f v =
      ∑ F with σ ⊆ F, m F * (if u ≠ v ∧ u ∈ F \ σ ∧ v ∈ F \ σ then f u * f v else 0) := by
    intro u v
    rw [linkWeightOf_eq_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun F _ => ?_
    split_ifs <;> ring
  simp only [h1]
  rw [Finset.sum_congr rfl fun u _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun F _ => ?_
  simp only [← Finset.mul_sum]
  rw [sum_sum_ite_ne_mul]

/-- **A sum of squares.** The quadratic form of the link of `σ`, plus the sum of `f u ^ 2` weighted
by the weight of `σ ∪ {u}`, is the sum over the sets `F ⊇ σ` of the weight of `F` times the square
of the sum of `f` over `F \ σ`. No hypothesis on `m`. -/
theorem sum_linkWeightOf_mul_mul_add (m : Finset ι → ℝ) (σ : Finset ι) (f : ι → ℝ) :
    ∑ u, ∑ v, linkWeightOf m σ u v * f u * f v +
        ∑ u, (if u ∈ σ then 0 else faceWeight m (insert u σ)) * f u ^ 2 =
      ∑ F with σ ⊆ F, m F * (∑ v ∈ F \ σ, f v) ^ 2 := by
  rw [sum_linkWeightOf_mul_mul, sum_faceWeight_insert_mul m σ fun u => f u ^ 2,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun F _ => by ring

/-- **Lower bound on the eigenvalues of a link** (Lemma 5.1 of arXiv:2609.08937). For a
nonnegative weight on sets with `d + 1` elements, the quadratic form of the weighted graph of the
link of `σ` is at least `−1 / (d − |σ|)` times the degree-weighted norm, for *every* `f`. So the
random walk on the link of a face of dimension `k` has no eigenvalue below `−1 / (d − 1 − k)`:
in particular `−1` for the links of `(d − 2)`-dimensional faces, which are graphs, and `−1 / d`
for the complex itself.

With `ℓ = d − |σ|`, the degree of `u` is `ℓ` times the weight of `σ ∪ {u}` (`sum_linkWeightOf`),
so the claim is that the sum of squares in `sum_linkWeightOf_mul_mul_add` is nonnegative.

Only nonnegativity of `m` and its vanishing off the sets with `d + 1` elements are used: no
complex, no purity, no positivity on top faces. There is no hypothesis on `σ` either. If `σ` has
at least `d` elements the link has no edges and both sides are `0` (for `|σ| = d` the coefficient
is `-(1 / 0) = 0` in Lean). -/
theorem link_walk_lower_bound (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = d + 1)
    (σ : Finset ι) (f : ι → ℝ) :
    -(1 / ((d : ℝ) - #σ)) * ∑ u, (∑ v, linkWeightOf m σ u v) * f u ^ 2 ≤
      ∑ u, ∑ v, linkWeightOf m σ u v * f u * f v := by
  rcases eq_or_ne ((d : ℝ) - #σ) 0 with h0 | h0
  · -- `|σ| = d`: no edges
    have hd : d ≤ #σ := by
      have h : (d : ℝ) = #σ := by linarith
      exact (Nat.cast_injective h).le
    simp [linkWeightOf_eq_zero_of_le_card hcard hd]
  · have hdeg : ∑ u, (∑ v, linkWeightOf m σ u v) * f u ^ 2 =
        ((d : ℝ) - #σ) * ∑ u, (if u ∈ σ then 0 else faceWeight m (insert u σ)) * f u ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [sum_linkWeightOf hcard]
      split_ifs <;> ring
    have hsq : 0 ≤ ∑ F with σ ⊆ F, m F * (∑ v ∈ F \ σ, f v) ^ 2 :=
      Finset.sum_nonneg fun F _ => mul_nonneg (hnn F) (sq_nonneg _)
    rw [← sum_linkWeightOf_mul_mul_add m σ f] at hsq
    rw [hdeg, ← mul_assoc, neg_mul, one_div, inv_mul_cancel₀ h0]
    linarith

/-- `link_walk_lower_bound` for a top weight of a complex. -/
theorem IsTopWeight.link_walk_lower_bound (hm : K.IsTopWeight d m) (σ : Finset ι) (f : ι → ℝ) :
    -(1 / ((d : ℝ) - #σ)) * ∑ u, (∑ v, linkWeightOf m σ u v) * f u ^ 2 ≤
      ∑ u, ∑ v, linkWeightOf m σ u v * f u * f v :=
  PreAbstractSimplicialComplex.link_walk_lower_bound hm.nonneg hm.card_eq_of_ne_zero σ f

/-! ### Weighted local spectral expanders -/

/-- `K`, with the weight `m` on its top faces, is a **`lam`-local-spectral expander** of dimension
`d`: `d ≥ 1`, `m` is a top weight of `K` (so `K` is pure of dimension `d` and has a face), and for
every face `σ` of dimension at most `d − 2`, and for `σ = ∅`, the random walk on the weighted graph
of the link of `σ` has second eigenvalue at most `lam`.

Every link in question has an edge of positive weight
(`IsLocalSpectralExpanderOf.exists_linkWeightOf_pos`), so no instance of the bound is the vacuous
one of `walkSecondEigenvalueLE_of_forall_eq_zero`. The condition `1 ≤ d` excludes dimension `0`,
where there is nothing to test: no `σ` has `#σ + 1 ≤ 0`, so without the condition every top weight
of a `0`-dimensional complex (a positive weight on a nonempty set of vertices) would make it a
`lam`-expander for every `lam`. With it, no weighted complex is a `0`-dimensional expander
(`not_isLocalSpectralExpanderOf_zero`); `IsTopWeight` itself still allows `d = 0`. For `d = 1`
only the weighted graph of `K` itself is tested. The definition forces `lam ≥ −1/d`
(`IsLocalSpectralExpanderOf.neg_one_div_le`).

`IsLocalSpectralExpander` is the case `m = K.uniformWeight d`
(`isLocalSpectralExpander_iff_isLocalSpectralExpanderOf`). -/
def IsLocalSpectralExpanderOf (K : PreAbstractSimplicialComplex ι) (d : ℕ) (m : Finset ι → ℝ)
    (lam : ℝ) : Prop :=
  1 ≤ d ∧ K.IsTopWeight d m ∧ ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d →
    WalkSecondEigenvalueLE (linkWeightOf m σ) lam

variable {lam : ℝ}

theorem IsLocalSpectralExpanderOf.one_le (h : K.IsLocalSpectralExpanderOf d m lam) : 1 ≤ d := h.1

theorem IsLocalSpectralExpanderOf.isTopWeight (h : K.IsLocalSpectralExpanderOf d m lam) :
    K.IsTopWeight d m := h.2.1

theorem IsLocalSpectralExpanderOf.walkSecondEigenvalueLE
    (h : K.IsLocalSpectralExpanderOf d m lam) {σ : Finset ι} (hσ : σ = ∅ ∨ σ ∈ K)
    (hcard : #σ + 1 ≤ d) : WalkSecondEigenvalueLE (linkWeightOf m σ) lam :=
  h.2.2 σ hσ hcard

/-- **Non-vacuity of `IsLocalSpectralExpanderOf`.** Every link that the definition quantifies
over has an edge of positive weight. -/
theorem IsLocalSpectralExpanderOf.exists_linkWeightOf_pos
    (h : K.IsLocalSpectralExpanderOf d m lam) {σ : Finset ι} (hσ : σ = ∅ ∨ σ ∈ K)
    (hcard : #σ + 1 ≤ d) : ∃ u v, 0 < linkWeightOf m σ u v :=
  h.isTopWeight.exists_linkWeightOf_pos hσ hcard

/-- **No `0`-dimensional expanders.** A `0`-dimensional complex has no link to test, so the
definition excludes dimension `0`: no complex, with any weight `m`, is a `0`-dimensional local
spectral expander, for any `lam`. -/
theorem not_isLocalSpectralExpanderOf_zero : ¬ K.IsLocalSpectralExpanderOf 0 m lam :=
  fun h => absurd h.one_le (by omega)

/-- **A local spectral expander is no better than a simplex.** A `lam`-local-spectral expander of
dimension `d` has `lam ≥ −1/d`, the second eigenvalue of the complete graph on `d + 1` points.
Dimension `0`, where nothing would be tested, is excluded by the definition
(`not_isLocalSpectralExpanderOf_zero`), so in no dimension is the definition satisfied by every
`lam`.

The weighted underlying graph has an edge `u v`
(`IsLocalSpectralExpanderOf.exists_linkWeightOf_pos`). The function `deg v` at `u`, `−deg u` at
`v` and `0` elsewhere has degree-weighted mean zero and positive norm; compare the bound in the
definition with `link_walk_lower_bound`. -/
theorem IsLocalSpectralExpanderOf.neg_one_div_le (h : K.IsLocalSpectralExpanderOf d m lam) :
    -(1 / (d : ℝ)) ≤ lam := by
  have hd := h.one_le
  have hd' : #(∅ : Finset ι) + 1 ≤ d := by rw [Finset.card_empty]; omega
  obtain ⟨u, v, huv⟩ := h.exists_linkWeightOf_pos (Or.inl rfl) hd'
  have hnn := linkWeightOf_nonneg h.isTopWeight.nonneg ∅
  have hne : u ≠ v := fun e => by
    rw [e, linkWeightOf_self] at huv
    exact lt_irrefl _ huv
  -- the degrees `a` of `u` and `b` of `v` are positive
  obtain ⟨a, ha⟩ : ∃ a, a = ∑ x, linkWeightOf m ∅ u x := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ∑ x, linkWeightOf m ∅ v x := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [ha]
    exact lt_of_lt_of_le huv (Finset.single_le_sum (fun x _ => hnn u x) (Finset.mem_univ v))
  have hb0 : 0 < b := by
    rw [hb]
    rw [linkWeightOf_symm] at huv
    exact lt_of_lt_of_le huv (Finset.single_le_sum (fun x _ => hnn v x) (Finset.mem_univ u))
  -- the test function: `b` at `u`, `−a` at `v`
  obtain ⟨f, hf⟩ : ∃ f : ι → ℝ, f = fun x => if x = u then b else if x = v then -a else 0 :=
    ⟨_, rfl⟩
  have hfu : f u = b := by rw [hf]; exact if_pos rfl
  have hfv : f v = -a := by rw [hf]; simp [hne.symm]
  have hf0 : ∀ x, x ≠ u ∧ x ≠ v → f x = 0 := fun x hx => by rw [hf]; simp [hx.1, hx.2]
  have hmean : ∑ x, (∑ y, linkWeightOf m ∅ x y) * f x = 0 := by
    rw [Finset.sum_eq_add_of_mem u v (Finset.mem_univ _) (Finset.mem_univ _) hne
      fun x _ hx => by rw [hf0 x hx, mul_zero], hfu, hfv, ← ha, ← hb]
    ring
  have hnorm : ∑ x, (∑ y, linkWeightOf m ∅ x y) * f x ^ 2 = a * b ^ 2 + b * a ^ 2 := by
    rw [Finset.sum_eq_add_of_mem u v (Finset.mem_univ _) (Finset.mem_univ _) hne
      fun x _ hx => by rw [hf0 x hx]; ring, hfu, hfv, ← ha, ← hb]
    ring
  have h1 := h.walkSecondEigenvalueLE (Or.inl rfl) hd' f hmean
  have h2 := h.isTopWeight.link_walk_lower_bound ∅ f
  rw [hnorm] at h1 h2
  rw [Finset.card_empty, Nat.cast_zero, sub_zero] at h2
  have hN : 0 < a * b ^ 2 + b * a ^ 2 := by positivity
  exact le_of_mul_le_mul_right (h2.trans h1) hN

variable (K) in
/-- **The unweighted definition is the uniform case of the weighted one.** -/
theorem isLocalSpectralExpander_iff_isLocalSpectralExpanderOf :
    K.IsLocalSpectralExpander d lam ↔ K.IsLocalSpectralExpanderOf d (K.uniformWeight d) lam := by
  unfold IsLocalSpectralExpander IsLocalSpectralExpanderOf
  rw [K.isTopWeight_uniformWeight_iff, and_assoc]
  simp only [K.linkWeight_eq_linkWeightOf]

variable (K) in
/-- Weighted trickling down, packaged: under the hypotheses of `trickling_down_weighted`, the
weighted complex is a `lam / (1 − (d − 1) lam)`-local-spectral expander.

No sign condition on `lam` is needed. Of the bounds `lam / (1 − j lam)`, `0 ≤ j ≤ d − 1`, that
trickling down gives for the links, the one for the whole complex (`j = d − 1`) is the largest
whatever the sign of `lam`: both denominators are positive, and the difference of the
cross-multiplied sides is `−(d − 1 − j) lam² ≤ 0`. -/
theorem isLocalSpectralExpanderOf_of_trickling_down_weighted (hd : 2 ≤ d)
    (hm : K.IsTopWeight d m)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ d → (K.link σ).IsConnected)
    (hlam : ((d : ℝ) - 1) * lam < 1)
    (hlocal : ∀ σ ∈ K, #σ + 1 = d → WalkSecondEigenvalueLE (linkWeightOf m σ) lam) :
    K.IsLocalSpectralExpanderOf d m (lam / (1 - ((d : ℝ) - 1) * lam)) := by
  refine ⟨by omega, hm, fun σ hσ hcard => ?_⟩
  refine (K.trickling_down_weighted hd hm hconn hlam hlocal σ hσ hcard).mono
    (linkWeightOf_nonneg hm.nonneg σ) ?_
  -- `lam / (1 − (d − 1 − |σ|) lam) ≤ lam / (1 − (d − 1) lam)`, for either sign of `lam`.
  have hσ0 : (0 : ℝ) ≤ #σ := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ (d : ℝ) - 1 - #σ := by
    have h : ((#σ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hcard
    push_cast at h
    linarith
  have h1 : 0 < 1 - ((d : ℝ) - 1) * lam := by linarith
  have h2 : 0 < 1 - ((d : ℝ) - 1 - #σ) * lam := by
    rcases le_or_gt 0 lam with h | h
    · nlinarith
    · nlinarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith [mul_nonneg hσ0 (sq_nonneg lam)]

end Complex

end PreAbstractSimplicialComplex
