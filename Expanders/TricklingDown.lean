/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.WeightedComplex

/-!
# Counting top faces, and trickling down for unweighted complexes

The counting versions of the results of `Expanders/WeightedComplex.lean`. When every top face has
weight `1`, the weight of a set is the number `topDegree` of top faces through it, and the weighted
graph of a link is `linkWeight`. Every statement in this file is the case `m = K.uniformWeight d`
of a weighted one, transported along `topDegree_eq_faceWeight` and `linkWeight_eq_linkWeightOf`;
nothing is proved a second time.

## Theorems
* `sum_topDegree_insert`, `sum_linkWeight`, `sum_linkWeight_insert`,
  `sum_linkWeight_insert_right`: double counting of top faces, giving the degrees of a link and
  the localisation of a link to its vertex links. **Proved.**
* `trickling_down`: Oppenheim's local-to-global theorem. **Proved.**
* `isLocalSpectralExpander_of_trickling_down`: its conclusion, as a statement that the complex is
  a local spectral expander. **Proved.**
* `IsLocalSpectralExpander.neg_one_div_le`: a `lam`-local-spectral expander of dimension `d` has
  `lam ≥ −1/d`. **Proved.**
-/

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (K : PreAbstractSimplicialComplex ι)

/-! ### Counting top faces -/

/-- `sum_topDegree_insert` over the reals, as a sum over all vertices. -/
theorem sum_topDegree_insert_real (d : ℕ) (s : Finset ι) :
    ∑ v, (if v ∈ s then 0 else (K.topDegree d (insert v s) : ℝ)) =
      ((d : ℝ) + 1 - #s) * K.topDegree d s := by
  simp only [K.topDegree_eq_faceWeight]
  exact sum_faceWeight_insert (K.card_eq_of_uniformWeight_ne_zero d) s

/-- **Double counting.** Every top face through `s` has exactly `d + 1 − |s|` vertices outside
`s`, so summing `topDegree (s ∪ {v})` over `v ∉ s` counts each such face `d + 1 − |s|` times. -/
theorem sum_topDegree_insert (d : ℕ) (s : Finset ι) :
    ∑ v ∈ sᶜ, K.topDegree d (insert v s) + #s * K.topDegree d s = (d + 1) * K.topDegree d s := by
  have h := K.sum_topDegree_insert_real d s
  have h' : ∑ v, (if v ∈ s then 0 else (K.topDegree d (insert v s) : ℝ))
      = ∑ v ∈ sᶜ, (K.topDegree d (insert v s) : ℝ) := by
    rw [← Finset.sum_compl_add_sum s, Finset.sum_eq_zero (s := s) fun v hv => if_pos hv, add_zero]
    exact Finset.sum_congr rfl fun v hv => if_neg (Finset.mem_compl.mp hv)
  rw [h'] at h
  have h2 : (∑ v ∈ sᶜ, (K.topDegree d (insert v s) : ℝ)) + #s * K.topDegree d s
      = ((d : ℝ) + 1) * K.topDegree d s := by linarith
  exact_mod_cast h2

/-! ### The weighted graph of a link: degrees and localisation -/

/-- **No edges above dimension `d − 2`.** If `σ` has at least `d` elements, a top face through
`σ` has at most one further vertex, so the weighted graph of the link of `σ` has no edges. -/
theorem linkWeight_eq_zero_of_le_card {d : ℕ} {σ : Finset ι} (hσ : d ≤ #σ) (u v : ι) :
    K.linkWeight d σ u v = 0 := by
  rw [K.linkWeight_eq_linkWeightOf]
  exact linkWeightOf_eq_zero_of_le_card (K.card_eq_of_uniformWeight_ne_zero d) hσ u v

/-- **Degrees in a link.** The degree of `u ∉ τ` in the weighted graph of the link of `τ` is
`d − |τ|` times the number of top faces through `τ ∪ {u}`. -/
theorem sum_linkWeight (d : ℕ) (τ : Finset ι) (u : ι) :
    ∑ v, K.linkWeight d τ u v =
      if u ∈ τ then 0 else ((d : ℝ) - #τ) * K.topDegree d (insert u τ) := by
  rw [K.linkWeight_eq_linkWeightOf, K.topDegree_eq_faceWeight]
  exact sum_linkWeightOf (K.card_eq_of_uniformWeight_ne_zero d) τ u

/-- **Localisation of weights.** The weight of an edge in the link of `σ` is the average, over
the further vertices `z` of the top faces through it, of its weight in the link of `σ ∪ {z}`:
each top face through `σ ∪ {u, v}` has `d − 1 − |σ|` further vertices. -/
theorem sum_linkWeight_insert (d : ℕ) (σ : Finset ι) (u v : ι) :
    ∑ z, (if z ∈ σ then 0 else K.linkWeight d (insert z σ) u v) =
      ((d : ℝ) - 1 - #σ) * K.linkWeight d σ u v := by
  simp only [K.linkWeight_eq_linkWeightOf]
  exact sum_linkWeightOf_insert (K.card_eq_of_uniformWeight_ne_zero d) σ u v

/-- **Localisation of degrees.** The degree of `u` in the link of `σ ∪ {z}` is `d − 1 − |σ|`
times the weight of the edge `z u` in the link of `σ`. -/
theorem sum_linkWeight_insert_right (d : ℕ) (σ : Finset ι) (z u : ι) :
    ∑ v, (if z ∈ σ then 0 else K.linkWeight d (insert z σ) u v) =
      ((d : ℝ) - 1 - #σ) * K.linkWeight d σ z u := by
  simp only [K.linkWeight_eq_linkWeightOf]
  exact sum_linkWeightOf_insert_right (K.card_eq_of_uniformWeight_ne_zero d) σ z u

/-! ### Trickling down -/

/-- **One step of trickling down.** Let `σ` have dimension at most `d − 3` (possibly `σ = ∅`),
with connected link. If the link of every face `σ ∪ {z}` has second eigenvalue at most `μ < 1`,
then the link of `σ` has second eigenvalue at most `μ / (1 − μ)`. -/
theorem walkSecondEigenvalueLE_linkWeight_step {d : ℕ} (hpure : K.IsPure d) {σ : Finset ι}
    (hcard : #σ + 2 ≤ d) (hconn : (K.link σ).IsConnected) {μ : ℝ} (hμ : μ < 1)
    (hloc : ∀ z, z ∉ σ → insert z σ ∈ K →
      WalkSecondEigenvalueLE (K.linkWeight d (insert z σ)) μ) :
    WalkSecondEigenvalueLE (K.linkWeight d σ) (μ / (1 - μ)) := by
  -- a connected link has a face `τ`, and then `τ ∪ σ` is a face of `K`
  obtain ⟨τ, hτ⟩ := hconn.exists_mem
  have hm := K.isTopWeight_uniformWeight hpure ⟨τ ∪ σ, (mem_link.mp hτ).2.2⟩
  simp only [K.linkWeight_eq_linkWeightOf] at hloc ⊢
  exact hm.walkSecondEigenvalueLE_linkWeightOf_step hcard hconn hμ hloc

omit [Fintype ι] in
/-- Under the connectivity hypothesis of `trickling_down`, the complex has a face: a connected
complex has a vertex. -/
private theorem exists_mem_of_isConnected_link {d : ℕ} (hd : 2 ≤ d)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ d → (K.link σ).IsConnected) :
    ∃ F, F ∈ K := by
  have h := hconn ∅ (Or.inl rfl) (by rw [Finset.card_empty]; omega)
  rw [link_empty] at h
  exact h.exists_mem

/-- **Trickling down (Oppenheim).** Let `K` be a pure `d`-dimensional complex, `d ≥ 2`, in which
`K` itself and every link of a face of dimension at most `d − 3` is connected. If the link of
every `(d − 2)`-dimensional face has second eigenvalue at most `lam`, where `(d − 1) · lam < 1`,
then the link of every face `σ` of dimension at most `d − 2` has second eigenvalue at most
`lam / (1 − (d − 1 − |σ|) · lam)`; taking `σ = ∅`, the underlying graph of `K` has second
eigenvalue at most `lam / (1 − (d − 1) · lam)`. Expansion of the smallest links forces expansion
everywhere.

Connectivity of the links of the `(d − 2)`-dimensional faces is not assumed: their eigenvalue
bound is the hypothesis `hlocal`. For `d = 2` the only connectivity hypothesis is that `K` itself
is connected.

This is `trickling_down_weighted` for the uniform weight, which is a top weight because `K` is
pure and, being connected, has a face. -/
theorem trickling_down {d : ℕ} (hd : 2 ≤ d) (hpure : K.IsPure d)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ d → (K.link σ).IsConnected)
    {lam : ℝ} (hlam : ((d : ℝ) - 1) * lam < 1)
    (hlocal : ∀ σ ∈ K, #σ + 1 = d → WalkSecondEigenvalueLE (K.linkWeight d σ) lam) :
    ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d →
      WalkSecondEigenvalueLE (K.linkWeight d σ) (lam / (1 - ((d : ℝ) - 1 - #σ) * lam)) := by
  have hm := K.isTopWeight_uniformWeight hpure (K.exists_mem_of_isConnected_link hd hconn)
  simp only [K.linkWeight_eq_linkWeightOf] at hlocal ⊢
  exact K.trickling_down_weighted hd hm hconn hlam hlocal

/-- Trickling down, packaged: under the hypotheses of `trickling_down` with `lam ≥ 0`, the
complex is a `lam / (1 − (d − 1) lam)`-local-spectral expander. -/
theorem isLocalSpectralExpander_of_trickling_down {d : ℕ} (hd : 2 ≤ d) (hpure : K.IsPure d)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 2 ≤ d → (K.link σ).IsConnected)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : ((d : ℝ) - 1) * lam < 1)
    (hlocal : ∀ σ ∈ K, #σ + 1 = d → WalkSecondEigenvalueLE (K.linkWeight d σ) lam) :
    K.IsLocalSpectralExpander d (lam / (1 - ((d : ℝ) - 1) * lam)) := by
  have hm := K.isTopWeight_uniformWeight hpure (K.exists_mem_of_isConnected_link hd hconn)
  rw [K.isLocalSpectralExpander_iff_isLocalSpectralExpanderOf]
  simp only [K.linkWeight_eq_linkWeightOf] at hlocal
  exact K.isLocalSpectralExpanderOf_of_trickling_down_weighted hd hm hconn hlam0 hlam hlocal

variable {K} in
/-- **A local spectral expander is no better than a simplex.** A `lam`-local-spectral expander of
dimension `d` has `lam ≥ −1/d`, the second eigenvalue of the complete graph on `d + 1` points.
Dimension `0`, where nothing would be tested, is excluded by the definition
(`not_isLocalSpectralExpander_zero`). -/
theorem IsLocalSpectralExpander.neg_one_div_le {d : ℕ} {lam : ℝ}
    (h : K.IsLocalSpectralExpander d lam) : -(1 / (d : ℝ)) ≤ lam :=
  ((K.isLocalSpectralExpander_iff_isLocalSpectralExpanderOf).mp h).neg_one_div_le

end PreAbstractSimplicialComplex
