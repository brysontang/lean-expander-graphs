/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.WeightedComplex

/-!
# Up and down walks on the faces of a weighted complex

Let `m` be a nonnegative weight on finite sets of vertices, supported on the sets with `d + 1`
elements (for a top weight `IsTopWeight K d m`, on the top faces of `K`). A function `f` *on level
`k`* is a function on finite sets that is read only on the sets with `k + 1` elements (the
`k`-dimensional faces). Level `k` carries the weights `faceWeight m σ`, the total weight of the top
faces through `σ`. The higher-order random walks on level `k` are:

* the **down-up walk** `DownW_k`: from `σ`, delete a uniformly random vertex to get `η`, then add a
  vertex `u ∉ η` with probability proportional to `faceWeight m (η ∪ {u})`;
* the **up-down walk** `UpW_k`: from `σ`, add a vertex `u ∉ σ` with probability proportional to
  `faceWeight m (σ ∪ {u})`, then delete a uniformly random one of the `k + 2` vertices;
* the **non-lazy up-down walk** `NUpW_k`: the same, but the deleted vertex is never the added one,
  so the walk always moves.

This file does not define these walks as matrices. It works with their quadratic forms, without
normalising: with `Z_k` the total weight of level `k` and `⟨·,·⟩` the inner product of the
stationary distribution `faceWeight / Z_k`,
`levelNormSq m k f = Z_k ⟨f, f⟩`, `downNormSq m d k f = (k + 1) Z_k ⟨f, DownW_k f⟩`,
`upForm m k f = (d − k)(k + 1) Z_k ⟨f, NUpW_k f⟩`, and
`∑_{|τ| = k + 2} faceWeight m τ · (∑_{σ ⊂ τ, |σ| = k + 1} f σ)² = (d − k)(k + 2) Z_k ⟨f, UpW_k f⟩`.
These dictionary entries are not formalised; they only explain the normalisations of the
statements below.

## Definitions
* `PreAbstractSimplicialComplex.levelNormSq m k f`: the weighted squared norm of `f` on level
  `k`.
* `PreAbstractSimplicialComplex.upForm m k f`: the quadratic form of the non-lazy up-down walk:
  pairs of `(k + 1)`-sets meeting in `k` elements, weighted by the weight of their union.
* `PreAbstractSimplicialComplex.downSum m f η`: the weighted sum of `f` over the cofaces
  `η ∪ {u}` of `η`.
* `PreAbstractSimplicialComplex.downNormSq m d k f`: the quadratic form of the down-up walk.

## Theorems
* `sum_linkWeightOf_mul_mul_eq_upForm`, `sum_linkWeightOf_norm_eq`: **localisation**. The quadratic
  forms and the degree-weighted norms of the links of the `k`-element sets add up to `upForm` and
  to `(d − k)(k + 1) · levelNormSq`. **Proved.**
* `sum_faceWeight_mul_sq_sum_powersetCard`: the norm of the up operator is
  `(d − k) · levelNormSq + upForm`, i.e. `UpW_k = 1/(k + 2) · I + (k + 1)/(k + 2) · NUpW_k`.
  **Proved.**
* `sum_downSum_mul`: the up and down operators are adjoint. **Proved.**
* `upForm_le`: **Alev–Lau, Lemma 3.7.** If every link of a `k`-element set has second eigenvalue
  at most `lam`, then `NUpW_k − DownW_k ⪯ lam · (I − DownW_k)`. **Proved.**
  `IsLocalSpectralExpanderOf.upForm_le`: the same for a `lam`-local-spectral expander. **Proved.**
* `downNormSq_le`: `DownW_k ⪯ I`. `upForm_ge`: `NUpW_k − DownW_k ⪰ −1/(d − k) · (I − DownW_k)`,
  the eigenvalue floor of the links (`link_walk_lower_bound`) localised the same way. **Proved.**
* `upDown_gap`: **Alev–Lau, Theorem 3.1 (local-to-global for the up-down walk).** If the links of
  the faces with `i` elements have second eigenvalue at most `lams i ≤ 1` for every `i ≤ k`, then
  the up-down walk on level `k` has second eigenvalue at most
  `1 − (1 / (k + 2)) ∏_{i ≤ k} (1 − lams i)`. **Proved.**
  `IsLocalSpectralExpanderOf.upDown_gap`: for a `lam`-local-spectral expander with `lam ≤ 1`, the
  bound `1 − (1 − lam)^(k + 1) / (k + 2)`. **Proved.**

## References
* V. L. Alev and L. C. Lau, *Improved analysis of higher order random walks and applications*,
  STOC 2020, arXiv:2001.02827. Lemma 3.7 is `upForm_le`; Theorem 3.1 (and Theorem 1.4), with
  their `k` replaced by `k + 1` and their `γ_j` by our `lams (j + 1)`, is `upDown_gap`.
* T. Kaufman and I. Oppenheim, *High order random walks: beyond spectral gap*, APPROX/RANDOM 2018,
  Combinatorica 40 (2020), arXiv:1707.02799. Their Prop. 4.2 / Lemma 4.3 is the localisation
  used here; their Theorem 5.4 is a weaker one-sided bound for the up-down walk.
* Y. Dikstein, I. Dinur, Y. Filmus and P. Harsha, *Boolean function analysis on high-dimensional
  expanders*, APPROX/RANDOM 2018, arXiv:1804.08155, Theorem 5.5 (as cited by Alev–Lau): the
  bound `NUpW_k − DownW_k ⪯ lam · I`, which `upForm_le` refines.
* `upForm_ge` localises the lower bound `link_walk_lower_bound` (Lemma 5.1 of arXiv:2609.08937).
-/

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-! ### Definitions -/

/-- The **weighted squared norm on level `k`**: `∑ faceWeight m σ · f σ²` over the sets `σ` with
`k + 1` elements. In the notation of the module docstring it is `Z_k ⟨f, f⟩`.

The sum runs over all `(k + 1)`-element subsets of `ι`, faces or not; for a top weight a set that
lies in no top face has `faceWeight m σ = 0`. If `ι` has fewer than `k + 1` elements, or `m` is
supported on sets with fewer than `k + 1` elements, the sum is `0`. Only the values of `f` on the
`(k + 1)`-element sets matter. -/
noncomputable def levelNormSq (m : Finset ι → ℝ) (k : ℕ) (f : Finset ι → ℝ) : ℝ :=
  ∑ σ with #σ = k + 1, faceWeight m σ * f σ ^ 2

/-- The **quadratic form of the non-lazy up-down walk on level `k`**: the sum, over the ordered
pairs `(σ, τ)` of `(k + 1)`-element sets that meet in exactly `k` elements, of
`faceWeight m (σ ∪ τ) · f σ · f τ`. In the notation of the module docstring it is
`(d − k)(k + 1) Z_k ⟨f, NUpW_k f⟩`.

The condition `|σ ∩ τ| = k` excludes `σ = τ` and makes `σ ∪ τ` a set with `k + 2` elements. For
`k = 0` the pairs are the pairs of distinct vertices and `upForm m 0 f` is the quadratic form of
the weighted graph `linkWeightOf m ∅` (`sum_linkWeightOf_mul_mul_eq_upForm`). For `m` supported on
the sets with `d + 1` elements, `upForm m k f = 0` once `k ≥ d` (`upForm_eq_zero_of_le`). -/
noncomputable def upForm (m : Finset ι → ℝ) (k : ℕ) (f : Finset ι → ℝ) : ℝ :=
  ∑ σ with #σ = k + 1, ∑ τ with #τ = k + 1,
    if #(σ ∩ τ) = k then faceWeight m (σ ∪ τ) * f σ * f τ else 0

/-- The **down sum** of `f` at `η`: `∑ faceWeight m (η ∪ {u}) · f (η ∪ {u})` over the vertices
`u ∉ η`. Divided by the total weight `∑_{u ∉ η} faceWeight m (η ∪ {u})` of the cofaces it is the
down operator, the weighted average of `f` over the cofaces of `η`; this division is done in
`downNormSq`.

`η` is any finite set; the vertices of `η` contribute nothing. `downSum m f ∅` is the unnormalised
mean `∑_v faceWeight m {v} · f {v}` of `f` on level `0`. -/
noncomputable def downSum (m : Finset ι → ℝ) (f : Finset ι → ℝ) (η : Finset ι) : ℝ :=
  ∑ u, if u ∈ η then 0 else faceWeight m (insert u η) * f (insert u η)

/-- The **quadratic form of the down-up walk on level `k`**: the sum, over the sets `η` with `k`
elements, of `downSum m f η ^ 2 / ((d + 1 − k) · faceWeight m η)`. In the notation of the module
docstring it is `(k + 1) Z_k ⟨f, DownW_k f⟩`. For `m` supported on the sets with `d + 1` elements
the denominator is the total weight of the cofaces of `η` (`sum_faceWeight_insert`).

Junk values: the coefficient `d + 1 − k` is computed in `ℝ`, and a term whose denominator is `0`
is `x / 0 = 0`. This happens when `faceWeight m η = 0` and when `k = d + 1`; for nonnegative `m`
supported on the sets with `d + 1` elements the numerator `downSum m f η` is then `0` as well
(`downSum_eq_zero_of_mul_faceWeight_eq_zero`), so no information is lost. For `k > d + 1` the
coefficient is negative, but then `faceWeight m η = 0`. For `k = 0` the only term is `η = ∅`:
the square of the mean of `f` divided by `(d + 1) · faceWeight m ∅`. -/
noncomputable def downNormSq (m : Finset ι → ℝ) (d k : ℕ) (f : Finset ι → ℝ) : ℝ :=
  ∑ η with #η = k, downSum m f η ^ 2 / (((d : ℝ) + 1 - k) * faceWeight m η)

/-! ### Reindexing sums over faces -/

private theorem sum_ite_mem_zero_eq (η : Finset ι) (X : ι → ℝ) :
    ∑ u, (if u ∈ η then 0 else X u) = ∑ u ∈ ηᶜ, X u := by
  rw [← Fintype.sum_ite_mem ηᶜ X]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u ∈ η <;> simp [hu]

/-- **Flag double counting.** Pairs `(η, u)` with `|η| = k` and `u ∉ η` correspond to pairs
`(σ, u)` with `|σ| = k + 1` and `u ∈ σ`, through `σ = η ∪ {u}` and `η = σ \ {u}`. -/
private theorem sum_card_eq_sum_insert_eq_sum_mem (k : ℕ) (G : Finset ι → ι → ℝ) :
    ∑ η with #η = k, ∑ u, (if u ∈ η then 0 else G (insert u η) u) =
      ∑ σ with #σ = k + 1, ∑ u ∈ σ, G σ u := by
  simp only [sum_ite_mem_zero_eq]
  rw [← Finset.sum_finset_product (r := (univ : Finset (Finset ι × ι)).filter
      (fun p => #p.1 = k ∧ p.2 ∉ p.1)) (f := fun p => G (insert p.2 p.1) p.2) _ _
      (fun p => by simp),
    ← Finset.sum_finset_product (r := (univ : Finset (Finset ι × ι)).filter
      (fun p => #p.1 = k + 1 ∧ p.2 ∈ p.1)) (f := fun p => G p.1 p.2) _ _
      (fun p => by simp)]
  refine Finset.sum_nbij' (fun p => (insert p.2 p.1, p.2)) (fun p => (p.1.erase p.2, p.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨η, u⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    exact ⟨by rw [Finset.card_insert_of_notMem h.2, h.1], Finset.mem_insert_self _ _⟩
  · rintro ⟨σ, u⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    exact ⟨by rw [Finset.card_erase_of_mem h.2, h.1]; rfl, Finset.notMem_erase _ _⟩
  · rintro ⟨η, u⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    simp [Finset.erase_insert h.2]
  · rintro ⟨σ, u⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    simp [Finset.insert_erase h.2]
  · intro p _
    rfl

/-- **Swapping one vertex.** For `|σ| = k + 1`, the `(k + 1)`-sets `τ` with `|σ ∩ τ| = k` are
exactly the sets `(σ \ {u}) ∪ {v}` with `u ∈ σ` and `v ∉ σ`, each obtained once, and then
`σ ∪ τ = σ ∪ {v}`. -/
private theorem sum_card_inter_eq_sum_insert_erase {k : ℕ} {σ : Finset ι} (hσ : #σ = k + 1)
    (Φ : Finset ι → Finset ι → ℝ) :
    ∑ τ with #τ = k + 1, (if #(σ ∩ τ) = k then Φ τ (σ ∪ τ) else 0) =
      ∑ u ∈ σ, ∑ v, (if v ∈ σ then 0 else Φ (insert v (σ.erase u)) (insert v σ)) := by
  simp only [sum_ite_mem_zero_eq]
  rw [← Finset.sum_product (s := σ) (t := σᶜ)
    (f := fun p => Φ (insert p.2 (σ.erase p.1)) (insert p.2 σ)), ← Finset.sum_filter,
    Finset.filter_filter]
  symm
  refine Finset.sum_nbij (fun p => insert p.2 (σ.erase p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ h
    simp only [Finset.mem_product, Finset.mem_compl] at h
    have hv : v ∉ σ.erase u := fun h' => h.2 (Finset.mem_of_mem_erase h')
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by rw [Finset.card_insert_of_notMem hv, Finset.card_erase_of_mem h.1, hσ]; rfl, ?_⟩
    rw [Finset.inter_insert_of_notMem h.2,
      Finset.inter_eq_right.mpr (Finset.erase_subset _ _), Finset.card_erase_of_mem h.1, hσ]
    rfl
  · rintro ⟨u, v⟩ h ⟨u', v'⟩ h' e
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_compl] at h h'
    simp only at e
    have hvv : v = v' := by
      have hv : v ∈ insert v' (σ.erase u') := e ▸ Finset.mem_insert_self v _
      rcases Finset.mem_insert.mp hv with hv | hv
      · exact hv
      · exact absurd (Finset.mem_of_mem_erase hv) h.2
    subst hvv
    have huu : u = u' := by
      by_contra hne
      have hu : u ∈ insert v (σ.erase u') :=
        Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, h.1⟩)
      rw [← e] at hu
      rcases Finset.mem_insert.mp hu with hu | hu
      · exact h.2 (hu ▸ h.1)
      · exact Finset.notMem_erase u σ hu
    rw [huu]
  · intro τ hτ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hτ
    have h1 : #(σ \ τ) = 1 := by
      rw [Finset.card_sdiff, Finset.inter_comm, hσ, hτ.2]; omega
    have h2 : #(τ \ σ) = 1 := by
      rw [Finset.card_sdiff, hτ.1, hτ.2]; omega
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h2
    have hu' : u ∈ σ \ τ := hu ▸ Finset.mem_singleton_self u
    have hv' : v ∈ τ \ σ := hv ▸ Finset.mem_singleton_self v
    rw [Finset.mem_sdiff] at hu' hv'
    refine ⟨(u, v), ?_, ?_⟩
    · simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_compl]
      exact ⟨hu'.1, hv'.2⟩
    · ext x
      simp only [Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨hxu, hx⟩)
        · exact hv'.1
        · by_contra hxτ
          have : x ∈ σ \ τ := Finset.mem_sdiff.mpr ⟨hx, hxτ⟩
          rw [hu, Finset.mem_singleton] at this
          exact hxu this
      · intro hx
        by_cases hxσ : x ∈ σ
        · refine Or.inr ⟨fun hxu => ?_, hxσ⟩
          rw [hxu] at hx
          exact hu'.2 hx
        · left
          have : x ∈ τ \ σ := Finset.mem_sdiff.mpr ⟨hx, hxσ⟩
          rwa [hv, Finset.mem_singleton] at this
  · rintro ⟨u, v⟩ h
    simp only [Finset.mem_product, Finset.mem_compl] at h
    simp only
    congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    tauto

omit [Fintype ι] in
/-- The `(k + 1)`-element subsets of a `(k + 2)`-element set `τ` are the sets `τ \ {u}`,
`u ∈ τ`. -/
private theorem sum_powersetCard_eq_sum_erase {k : ℕ} {τ : Finset ι} (hτ : #τ = k + 2)
    (g : Finset ι → ℝ) :
    ∑ σ ∈ τ.powersetCard (k + 1), g σ = ∑ u ∈ τ, g (τ.erase u) := by
  symm
  refine Finset.sum_nbij (fun u => τ.erase u) ?_ ?_ ?_ fun _ _ => rfl
  · intro u hu
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.erase_subset _ _, by rw [Finset.card_erase_of_mem hu, hτ]; rfl⟩
  · intro u hu u' hu' e
    simp only [Finset.mem_coe] at hu hu' e
    by_contra hne
    have h : u ∈ τ.erase u' := Finset.mem_erase.mpr ⟨hne, hu⟩
    rw [← e] at h
    exact Finset.notMem_erase u τ h
  · intro σ hσ
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hσ
    have h1 : #(τ \ σ) = 1 := by
      rw [Finset.card_sdiff_of_subset hσ.1, hτ, hσ.2]; omega
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
    have hu' : u ∈ τ \ σ := hu ▸ Finset.mem_singleton_self u
    rw [Finset.mem_sdiff] at hu'
    refine ⟨u, hu'.1, ?_⟩
    ext x
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨hxu, hx⟩
      by_contra hxσ
      have : x ∈ τ \ σ := Finset.mem_sdiff.mpr ⟨hx, hxσ⟩
      rw [hu, Finset.mem_singleton] at this
      exact hxu this
    · intro hx
      exact ⟨fun h => hu'.2 (h ▸ hx), hσ.1 hx⟩

/-! ### Localisation to the links -/

/-- **The swap form of `upForm`.** A pair `(σ, τ)` with `|σ ∩ τ| = k` is `σ` together with the
vertex `u ∈ σ` it loses and the vertex `v ∉ σ` it gains. No hypothesis on `m`. -/
theorem upForm_eq_sum_insert_erase (m : Finset ι → ℝ) (k : ℕ) (f : Finset ι → ℝ) :
    upForm m k f = ∑ σ with #σ = k + 1, ∑ u ∈ σ, ∑ v,
      (if v ∈ σ then 0 else faceWeight m (insert v σ) * f σ * f (insert v (σ.erase u))) := by
  unfold upForm
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [Finset.mem_filter] at hσ
  exact sum_card_inter_eq_sum_insert_erase hσ.2 fun τ ρ => faceWeight m ρ * f σ * f τ

/-- **Localisation of the up form** (as in Kaufman–Oppenheim, Prop. 4.2 / Lemma 4.3).
Restrict `f` to the link of each `k`-element set `η`, as the function `u ↦ f (η ∪ {u})` on its
vertices; the quadratic forms of the weighted link graphs `linkWeightOf m η` then add up to
`upForm m k f`. No hypothesis on `m`. For `k = 0` the only `η` is `∅`, and this says that
`upForm m 0 f` is the quadratic form of the weighted graph `linkWeightOf m ∅`. -/
theorem sum_linkWeightOf_mul_mul_eq_upForm (m : Finset ι → ℝ) (k : ℕ) (f : Finset ι → ℝ) :
    ∑ η with #η = k, ∑ u, ∑ v, linkWeightOf m η u v * f (insert u η) * f (insert v η) =
      upForm m k f := by
  rw [upForm_eq_sum_insert_erase, ← sum_card_eq_sum_insert_eq_sum_mem k
    (fun σ u => ∑ v, (if v ∈ σ then 0 else
      faceWeight m (insert v σ) * f σ * f (insert v (σ.erase u))))]
  refine Finset.sum_congr rfl fun η _ => Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u ∈ η
  · rw [if_pos hu]
    exact Finset.sum_eq_zero fun v _ => by
      rw [linkWeightOf_eq_zero_of_mem_left m hu, zero_mul, zero_mul]
  · rw [if_neg hu, Finset.erase_insert hu]
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold linkWeightOf
    by_cases hv : v ∈ insert u η
    · rw [if_pos hv, if_neg, zero_mul, zero_mul]
      rintro ⟨h1, -, h3⟩
      rcases Finset.mem_insert.mp hv with h | h
      · exact h1 h.symm
      · exact h3 h
    · rw [if_neg hv]
      rw [Finset.mem_insert, not_or] at hv
      rw [if_pos ⟨Ne.symm hv.1, hu, hv.2⟩, Finset.insert_comm u v]

/-! ### Centering a function on a weighted graph -/

section Center

omit [DecidableEq ι]

variable {w : ι → ι → ℝ}

private theorem quad_sub_const (hsymm : ∀ u v, w u v = w v u) (f : ι → ℝ) {c : ℝ}
    (hc : c * ∑ u, ∑ v, w u v = ∑ u, (∑ v, w u v) * f u) :
    ∑ u, ∑ v, w u v * (f u - c) * (f v - c) =
      ∑ u, ∑ v, w u v * f u * f v - c * ∑ u, (∑ v, w u v) * f u := by
  have s1 : ∑ u, ∑ v, w u v * f u = ∑ u, (∑ v, w u v) * f u :=
    Finset.sum_congr rfl fun u _ => (Finset.sum_mul _ _ _).symm
  have s2 : ∑ u, ∑ v, w u v * f v = ∑ u, (∑ v, w u v) * f u := by
    rw [Finset.sum_comm, ← s1]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hsymm v u]
  have e : ∀ u v, w u v * (f u - c) * (f v - c) =
      w u v * f u * f v - c * (w u v * f u) - c * (w u v * f v) + c ^ 2 * w u v :=
    fun u v => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, s1, s2]
  linear_combination c * hc

private theorem norm_sub_const (f : ι → ℝ) {c : ℝ}
    (hc : c * ∑ u, ∑ v, w u v = ∑ u, (∑ v, w u v) * f u) :
    ∑ u, (∑ v, w u v) * (f u - c) ^ 2 =
      ∑ u, (∑ v, w u v) * f u ^ 2 - c * ∑ u, (∑ v, w u v) * f u := by
  have e : ∀ u, (∑ v, w u v) * (f u - c) ^ 2 =
      (∑ v, w u v) * f u ^ 2 - 2 * c * ((∑ v, w u v) * f u) + c ^ 2 * (∑ v, w u v) :=
    fun u => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  linear_combination c * hc

private theorem mean_sub_const (f : ι → ℝ) {c : ℝ}
    (hc : c * ∑ u, ∑ v, w u v = ∑ u, (∑ v, w u v) * f u) :
    ∑ u, (∑ v, w u v) * (f u - c) = 0 := by
  calc ∑ u, (∑ v, w u v) * (f u - c) = ∑ u, (∑ v, w u v) * f u - c * ∑ u, ∑ v, w u v := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun u _ => by ring
    _ = 0 := by rw [hc]; ring

end Center

/-! ### The links of the `k`-element sets -/

section Links

variable {m : Finset ι → ℝ} {d k : ℕ}

private theorem faceWeight_insert_le (hnn : ∀ F, 0 ≤ m F) (u : ι) (s : Finset ι) :
    faceWeight m (insert u s) ≤ faceWeight m s := by
  unfold faceWeight
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun F _ _ => hnn F
  intro F
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun h => (Finset.subset_insert u s).trans h

/-- **The `x / 0` branch of `downNormSq` loses nothing.** For nonnegative `m` supported on the
sets with `d + 1` elements, if the denominator `(d + 1 − |η|) · faceWeight m η` of `downNormSq`
vanishes, so does the numerator `downSum m f η`: either `η` lies in no set of positive weight, or
`|η| = d + 1` and `η` has no coface of positive weight. -/
theorem downSum_eq_zero_of_mul_faceWeight_eq_zero (hnn : ∀ F, 0 ≤ m F)
    (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {η : Finset ι}
    (h : ((d : ℝ) + 1 - #η) * faceWeight m η = 0) (f : Finset ι → ℝ) : downSum m f η = 0 := by
  unfold downSum
  refine Finset.sum_eq_zero fun u _ => ?_
  split_ifs with hu
  · rfl
  · rcases mul_eq_zero.mp h with h | h
    · have hη : #η = d + 1 := by
        have : (#η : ℝ) = d + 1 := by linarith
        exact_mod_cast this
      rw [faceWeight_eq_zero_of_lt_card hcard (by rw [Finset.card_insert_of_notMem hu]; omega),
        zero_mul]
    · have h1 := faceWeight_insert_le hnn u η
      have h2 := faceWeight_nonneg hnn (insert u η)
      rw [le_antisymm (h ▸ h1) h2, zero_mul]

/-- The degree of `u` in the link of a `k`-element set `η`. -/
private theorem sum_linkWeightOf_card (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {η : Finset ι}
    (hη : #η = k) (u : ι) :
    ∑ v, linkWeightOf m η u v =
      if u ∈ η then 0 else ((d : ℝ) - k) * faceWeight m (insert u η) := by
  rw [sum_linkWeightOf hcard, hη]

private theorem sum_sum_linkWeightOf (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {η : Finset ι}
    (hη : #η = k) :
    ∑ u, ∑ v, linkWeightOf m η u v = ((d : ℝ) - k) * (((d : ℝ) + 1 - k) * faceWeight m η) := by
  simp only [sum_linkWeightOf_card hcard hη]
  rw [← hη, ← sum_faceWeight_insert hcard η, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs <;> ring

private theorem sum_linkWeightOf_mul (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {η : Finset ι}
    (hη : #η = k) (f : Finset ι → ℝ) :
    ∑ u, (∑ v, linkWeightOf m η u v) * f (insert u η) = ((d : ℝ) - k) * downSum m f η := by
  simp only [sum_linkWeightOf_card hcard hη]
  rw [downSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs <;> ring

private theorem sum_linkWeightOf_mul_sq (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {η : Finset ι}
    (hη : #η = k) (f : Finset ι → ℝ) :
    ∑ u, (∑ v, linkWeightOf m η u v) * f (insert u η) ^ 2 =
      ((d : ℝ) - k) *
        ∑ u, (if u ∈ η then 0 else faceWeight m (insert u η) * f (insert u η) ^ 2) := by
  simp only [sum_linkWeightOf_card hcard hη]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs <;> ring

/-- **Localisation of the norm** (as in Kaufman–Oppenheim, Prop. 4.2 / Lemma 4.3).
Restricting `f` to the links of the `k`-element sets as in `sum_linkWeightOf_mul_mul_eq_upForm`,
the degree-weighted norms add up to `(d − k)(k + 1) · levelNormSq m k f`: each `(k + 1)`-set
lies in the links of its `k + 1` subsets of size `k`, and its degree there is `d − k` times its
weight. The only hypothesis is that `m` vanishes off the sets with `d + 1` elements. For `k ≥ d`
both sides are `0`: the links have no edges, and `d − k = 0` or `levelNormSq m k f = 0`. -/
theorem sum_linkWeightOf_norm_eq (hcard : ∀ F, m F ≠ 0 → #F = d + 1) (k : ℕ)
    (f : Finset ι → ℝ) :
    ∑ η with #η = k, ∑ u, (∑ v, linkWeightOf m η u v) * f (insert u η) ^ 2 =
      ((d : ℝ) - k) * ((k : ℝ) + 1) * levelNormSq m k f := by
  have h1 : ∀ η ∈ (univ : Finset (Finset ι)).filter (fun η => #η = k),
      ∑ u, (∑ v, linkWeightOf m η u v) * f (insert u η) ^ 2 = ((d : ℝ) - k) *
        ∑ u, (if u ∈ η then 0 else faceWeight m (insert u η) * f (insert u η) ^ 2) :=
    fun η hη => sum_linkWeightOf_mul_sq hcard (Finset.mem_filter.mp hη).2 f
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
    sum_card_eq_sum_insert_eq_sum_mem k (fun σ (_ : ι) => faceWeight m σ * f σ ^ 2),
    levelNormSq, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [Finset.mem_filter] at hσ
  rw [Finset.sum_const, hσ.2, nsmul_eq_mul]
  push_cast
  ring

/-- The weighted mean of `f` around `η` (the down operator at `η`), `0` when its denominator
vanishes. -/
private noncomputable def linkMean (m : Finset ι → ℝ) (d : ℕ) (f : Finset ι → ℝ)
    (η : Finset ι) : ℝ :=
  downSum m f η / (((d : ℝ) + 1 - #η) * faceWeight m η)

private theorem linkMean_mul (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = d + 1)
    {η : Finset ι} (hη : #η = k) (f : Finset ι → ℝ) :
    linkMean m d f η * ∑ u, ∑ v, linkWeightOf m η u v =
      ∑ u, (∑ v, linkWeightOf m η u v) * f (insert u η) := by
  rw [sum_sum_linkWeightOf hcard hη, sum_linkWeightOf_mul hcard hη, linkMean]
  by_cases h : ((d : ℝ) + 1 - #η) * faceWeight m η = 0
  · rw [downSum_eq_zero_of_mul_faceWeight_eq_zero hnn hcard h, ← hη, h]
    simp
  · have h1 : (d : ℝ) + 1 - #η ≠ 0 := left_ne_zero_of_mul h
    have h2 : faceWeight m η ≠ 0 := right_ne_zero_of_mul h
    rw [← hη]
    field_simp

private theorem linkMean_mul_sum (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {η : Finset ι}
    (hη : #η = k) (f : Finset ι → ℝ) :
    linkMean m d f η * ∑ u, (∑ v, linkWeightOf m η u v) * f (insert u η) =
      ((d : ℝ) - k) * (downSum m f η ^ 2 / (((d : ℝ) + 1 - k) * faceWeight m η)) := by
  rw [sum_linkWeightOf_mul hcard hη, linkMean, hη]
  ring

/-- On the link of a `k`-element set `η`, the restriction of `f` minus its mean has
degree-weighted mean zero, and centring lowers its quadratic form and its norm by the same
amount, the `η`-term of `(d − k) · downNormSq m d k f`. -/
private theorem link_centered (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = d + 1)
    {η : Finset ι} (hη : #η = k) (f : Finset ι → ℝ) :
    ∑ u, (∑ v, linkWeightOf m η u v) * (f (insert u η) - linkMean m d f η) = 0 ∧
    ∑ u, ∑ v, linkWeightOf m η u v * (f (insert u η) - linkMean m d f η) *
        (f (insert v η) - linkMean m d f η) =
      ∑ u, ∑ v, linkWeightOf m η u v * f (insert u η) * f (insert v η) -
        ((d : ℝ) - k) * (downSum m f η ^ 2 / (((d : ℝ) + 1 - k) * faceWeight m η)) ∧
    ∑ u, (∑ v, linkWeightOf m η u v) * (f (insert u η) - linkMean m d f η) ^ 2 =
      ∑ u, (∑ v, linkWeightOf m η u v) * f (insert u η) ^ 2 -
        ((d : ℝ) - k) * (downSum m f η ^ 2 / (((d : ℝ) + 1 - k) * faceWeight m η)) := by
  have hc := linkMean_mul hnn hcard hη f
  refine ⟨mean_sub_const (fun u => f (insert u η)) hc, ?_, ?_⟩
  · rw [quad_sub_const (linkWeightOf_symm m η) (fun u => f (insert u η)) hc,
      linkMean_mul_sum hcard hη]
  · rw [norm_sub_const (fun u => f (insert u η)) hc, linkMean_mul_sum hcard hη]

end Links

/-! ### Comparing the non-lazy up-down walk with the down-up walk -/

section Compare

variable {m : Finset ι → ℝ} {d k : ℕ}

/-- **Alev–Lau, Lemma 3.7.** Let `m` be nonnegative and vanish off the sets with `d + 1`
elements. If the weighted graph of the link of every `k`-element set has random-walk second
eigenvalue at most `lam`, then for every function `f` on level `k`
`upForm − (d − k) · downNormSq ≤ lam · ((d − k)(k + 1) · levelNormSq − (d − k) · downNormSq)`.
Divided by `(d − k)(k + 1) Z_k` this is `⟨f, NUpW_k f⟩ − ⟨f, DownW_k f⟩ ≤
lam · ⟨f, (I − DownW_k) f⟩`, i.e. `NUpW_k − DownW_k ⪯ lam · (I − DownW_k)`.

Proof: apply the bound on the link of each `η` to the restriction of `f` minus its mean
(`link_centered`), and add up (`sum_linkWeightOf_mul_mul_eq_upForm`, `sum_linkWeightOf_norm_eq`).

Degenerate cases:
* The hypothesis is asked of *every* `k`-element set, not only of faces;
  `IsLocalSpectralExpanderOf.upForm_le` derives it from a bound on the faces, the links of the
  other sets being empty. Each instance of `WalkSecondEigenvalueLE` constrains only the vertices
  of positive degree, and holds for every `lam` when the link has no edges.
* There is no hypothesis on `k`: for `k ≥ d` both sides are `0` (`upForm_eq_zero_of_le`, and
  `d − k = 0` or `downNormSq` and `levelNormSq` vanish).
* `lam` may be any real number; no sign or size condition is needed. -/
theorem upForm_le (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {lam : ℝ}
    (hloc : ∀ η : Finset ι, #η = k → WalkSecondEigenvalueLE (linkWeightOf m η) lam)
    (f : Finset ι → ℝ) :
    upForm m k f - ((d : ℝ) - k) * downNormSq m d k f ≤
      lam * (((d : ℝ) - k) * ((k : ℝ) + 1) * levelNormSq m k f -
        ((d : ℝ) - k) * downNormSq m d k f) := by
  have key : ∀ η ∈ (univ : Finset (Finset ι)).filter (fun η => #η = k),
      ∑ u, ∑ v, linkWeightOf m η u v * f (insert u η) * f (insert v η) -
          ((d : ℝ) - k) * (downSum m f η ^ 2 / (((d : ℝ) + 1 - k) * faceWeight m η)) ≤
        lam * (∑ u, (∑ v, linkWeightOf m η u v) * f (insert u η) ^ 2 -
          ((d : ℝ) - k) * (downSum m f η ^ 2 / (((d : ℝ) + 1 - k) * faceWeight m η))) := by
    intro η hη
    have hη := (Finset.mem_filter.mp hη).2
    obtain ⟨h0, h1, h2⟩ := link_centered hnn hcard hη f
    have h := hloc η hη _ h0
    rwa [h1, h2] at h
  have hsum := Finset.sum_le_sum key
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rwa [sum_linkWeightOf_mul_mul_eq_upForm, sum_linkWeightOf_norm_eq hcard] at hsum

/-- The denominator of `downNormSq` is the total weight of the cofaces of `η`. -/
private theorem coeff_eq_sum (hcard : ∀ F, m F ≠ 0 → #F = d + 1) {η : Finset ι}
    (hη : #η = k) :
    ((d : ℝ) + 1 - k) * faceWeight m η =
      ∑ u, (if u ∈ η then 0 else faceWeight m (insert u η)) := by
  rw [sum_faceWeight_insert hcard η, hη]

private theorem coeff_nonneg (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = d + 1)
    {η : Finset ι} (hη : #η = k) : 0 ≤ ((d : ℝ) + 1 - k) * faceWeight m η := by
  rw [coeff_eq_sum hcard hη]
  refine Finset.sum_nonneg fun u _ => ?_
  split_ifs
  · exact le_rfl
  · exact faceWeight_nonneg hnn _

/-- `downNormSq` is nonnegative for nonnegative `m` supported on the sets with `d + 1` elements:
every denominator is a total weight, and a zero denominator gives the term `x / 0 = 0`. -/
theorem downNormSq_nonneg (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = d + 1) (k : ℕ)
    (f : Finset ι → ℝ) : 0 ≤ downNormSq m d k f :=
  Finset.sum_nonneg fun _ hη =>
    div_nonneg (sq_nonneg _) (coeff_nonneg hnn hcard (Finset.mem_filter.mp hη).2)

/-- `levelNormSq` is nonnegative for nonnegative `m`. -/
theorem levelNormSq_nonneg (hnn : ∀ F, 0 ≤ m F) (k : ℕ) (f : Finset ι → ℝ) :
    0 ≤ levelNormSq m k f :=
  Finset.sum_nonneg fun σ _ => mul_nonneg (faceWeight_nonneg hnn σ) (sq_nonneg _)

/-- **The down-up walk has no eigenvalue above `1`**: `downNormSq m d k f ≤
(k + 1) · levelNormSq m k f`, that is `⟨f, DownW_k f⟩ ≤ ⟨f, f⟩`. By Cauchy–Schwarz on the cofaces
of each `k`-element set. Only nonnegativity of `m` and its vanishing off the sets with `d + 1`
elements are used; there is no condition on `k` (for `k > d` the left side is `0`). -/
theorem downNormSq_le (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = d + 1) (k : ℕ)
    (f : Finset ι → ℝ) : downNormSq m d k f ≤ ((k : ℝ) + 1) * levelNormSq m k f := by
  have key : ∀ η ∈ (univ : Finset (Finset ι)).filter (fun η => #η = k),
      downSum m f η ^ 2 / (((d : ℝ) + 1 - k) * faceWeight m η) ≤
        ∑ u, (if u ∈ η then 0 else faceWeight m (insert u η) * f (insert u η) ^ 2) := by
    intro η hη
    have hη := (Finset.mem_filter.mp hη).2
    have hR : 0 ≤ ∑ u, (if u ∈ η then 0 else faceWeight m (insert u η) * f (insert u η) ^ 2) :=
      Finset.sum_nonneg fun u _ => by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (faceWeight_nonneg hnn _) (sq_nonneg _)
    refine div_le_of_le_mul₀ (coeff_nonneg hnn hcard hη) hR ?_
    rw [coeff_eq_sum hcard hη, mul_comm, downSum]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun u _ => ?_) (fun u _ => ?_)
      (fun u _ => ?_)
    · split_ifs
      · exact le_rfl
      · exact faceWeight_nonneg hnn _
    · split_ifs
      · exact le_rfl
      · exact mul_nonneg (faceWeight_nonneg hnn _) (sq_nonneg _)
    · split_ifs
      · simp
      · exact le_of_eq (by ring)
  refine (Finset.sum_le_sum key).trans (le_of_eq ?_)
  rw [sum_card_eq_sum_insert_eq_sum_mem k (fun σ (_ : ι) => faceWeight m σ * f σ ^ 2),
    levelNormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [Finset.mem_filter] at hσ
  rw [Finset.sum_const, hσ.2, nsmul_eq_mul]
  push_cast
  ring

/-- **`upForm` vanishes from level `d` on.** If `m` vanishes off the sets with `d + 1` elements
and `k ≥ d`, two `(k + 1)`-element sets meeting in `k` elements span `k + 2 > d + 1` vertices, so
every term of `upForm m k f` has weight `0`. -/
theorem upForm_eq_zero_of_le (hcard : ∀ F, m F ≠ 0 → #F = d + 1) (hk : d ≤ k)
    (f : Finset ι → ℝ) : upForm m k f = 0 := by
  unfold upForm
  refine Finset.sum_eq_zero fun σ hσ => Finset.sum_eq_zero fun τ hτ => ?_
  have hσ' := (Finset.mem_filter.mp hσ).2
  have hτ' := (Finset.mem_filter.mp hτ).2
  split_ifs with h
  · have hu := Finset.card_union_add_card_inter σ τ
    rw [faceWeight_eq_zero_of_lt_card hcard (by omega), zero_mul, zero_mul]
  · rfl

/-- **The lower bound: `NUpW_k − DownW_k ⪰ −1/(d − k) · (I − DownW_k)`.** For nonnegative `m`
supported on the sets with `d + 1` elements and every function `f` on level `k`,
`−((k + 1) · levelNormSq − downNormSq) ≤ upForm − (d − k) · downNormSq`. For `k + 1 ≤ d` this is
the floor `−1/(d − k)` on the eigenvalues of the links (`link_walk_lower_bound`), localised as in
`upForm_le`, multiplied through by `d − k > 0`. For `k ≥ d` (no division then) `upForm` vanishes
(`upForm_eq_zero_of_le`) and the inequality follows from `downNormSq_le`. No complex and no
spectral hypothesis are needed. -/
theorem upForm_ge (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = d + 1)
    (f : Finset ι → ℝ) :
    -(((k : ℝ) + 1) * levelNormSq m k f - downNormSq m d k f) ≤
      upForm m k f - ((d : ℝ) - k) * downNormSq m d k f := by
  by_cases hk : k + 1 ≤ d
  · have hdk : (0 : ℝ) < (d : ℝ) - k := by
      have : ((k + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hk
      push_cast at this
      linarith
    have key : ∀ η ∈ (univ : Finset (Finset ι)).filter (fun η => #η = k),
        -(1 / ((d : ℝ) - k)) * (∑ u, (∑ v, linkWeightOf m η u v) * f (insert u η) ^ 2 -
            ((d : ℝ) - k) * (downSum m f η ^ 2 / (((d : ℝ) + 1 - k) * faceWeight m η))) ≤
          ∑ u, ∑ v, linkWeightOf m η u v * f (insert u η) * f (insert v η) -
            ((d : ℝ) - k) * (downSum m f η ^ 2 / (((d : ℝ) + 1 - k) * faceWeight m η)) := by
      intro η hη
      have hη := (Finset.mem_filter.mp hη).2
      obtain ⟨-, h1, h2⟩ := link_centered hnn hcard hη f
      have h := link_walk_lower_bound hnn hcard η fun u => f (insert u η) - linkMean m d f η
      rwa [h1, h2, hη] at h
    have hsum := Finset.sum_le_sum key
    rw [← Finset.mul_sum] at hsum
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    rw [sum_linkWeightOf_mul_mul_eq_upForm, sum_linkWeightOf_norm_eq hcard] at hsum
    have e : -(1 / ((d : ℝ) - k)) * (((d : ℝ) - k) * ((k : ℝ) + 1) * levelNormSq m k f -
        ((d : ℝ) - k) * downNormSq m d k f) =
          -(((k : ℝ) + 1) * levelNormSq m k f - downNormSq m d k f) := by
      field_simp
    exact e.symm.le.trans hsum
  · rw [upForm_eq_zero_of_le hcard (by omega) f]
    have hD := downNormSq_le hnn hcard k f
    have hD0 := downNormSq_nonneg hnn hcard k f
    have hkd : (0 : ℝ) ≤ (k : ℝ) - d := by
      have : (d : ℝ) ≤ k := by exact_mod_cast (show d ≤ k by omega)
      linarith
    nlinarith [mul_nonneg hkd hD0]

end Compare

/-! ### Local spectral expanders -/

section Expander

variable {K : PreAbstractSimplicialComplex ι} {d : ℕ} {m : Finset ι → ℝ}

/-- For a top weight, a bound on the link of every face and of `∅` is a bound on the link of
every set: the link of any other set has no edges. -/
private theorem IsTopWeight.walkSecondEigenvalueLE_of_faces (hm : K.IsTopWeight d m) {lam : ℝ}
    {η : Finset ι} (h : (η = ∅ ∨ η ∈ K) → WalkSecondEigenvalueLE (linkWeightOf m η) lam) :
    WalkSecondEigenvalueLE (linkWeightOf m η) lam := by
  by_cases hη : η = ∅ ∨ η ∈ K
  · exact h hη
  · rw [not_or] at hη
    exact walkSecondEigenvalueLE_of_forall_eq_zero
      (hm.linkWeightOf_eq_zero_of_notMem (Finset.nonempty_iff_ne_empty.mpr hη.1) hη.2) lam

/-- **Alev–Lau, Lemma 3.7, for a local spectral expander.** If `K` with the weight `m` is a
`lam`-local-spectral expander of dimension `d`, then on every level `k`,
`NUpW_k − DownW_k ⪯ lam · (I − DownW_k)` (`upForm_le`). The links that the definition does not
test are empty: the links of nonempty sets that are not faces, and the links of the sets with at
least `d` elements (`linkWeightOf_eq_zero_of_le_card`). So there is no condition on `k`; for
`k ≥ d` both sides are `0`. -/
theorem IsLocalSpectralExpanderOf.upForm_le {lam : ℝ} (h : K.IsLocalSpectralExpanderOf d m lam)
    (k : ℕ) (f : Finset ι → ℝ) :
    upForm m k f - ((d : ℝ) - k) * downNormSq m d k f ≤
      lam * (((d : ℝ) - k) * ((k : ℝ) + 1) * levelNormSq m k f -
        ((d : ℝ) - k) * downNormSq m d k f) := by
  refine PreAbstractSimplicialComplex.upForm_le h.isTopWeight.nonneg
    h.isTopWeight.card_eq_of_ne_zero (fun η hη => ?_) f
  by_cases hkd : k + 1 ≤ d
  · exact h.isTopWeight.walkSecondEigenvalueLE_of_faces fun hσ =>
      h.walkSecondEigenvalueLE hσ (hη ▸ hkd)
  · exact walkSecondEigenvalueLE_of_forall_eq_zero
      (linkWeightOf_eq_zero_of_le_card h.isTopWeight.card_eq_of_ne_zero (by omega)) lam

end Expander

/-! ### The up operator -/

section Up

variable {m : Finset ι → ℝ} {d : ℕ}

/-- **Mean transfer.** Summing `downSum m h` over the `k`-element sets weighs every
`(k + 1)`-element set `k + 1` times. No hypothesis on `m`. For `k = 0` the only set is `∅`, and
`downSum m h ∅` is the mean `∑ faceWeight m σ · h σ` of `h` on level `0`. -/
theorem sum_downSum (m : Finset ι → ℝ) (k : ℕ) (h : Finset ι → ℝ) :
    ∑ η with #η = k, downSum m h η =
      ((k : ℝ) + 1) * ∑ σ with #σ = k + 1, faceWeight m σ * h σ := by
  unfold downSum
  rw [sum_card_eq_sum_insert_eq_sum_mem k (fun σ (_ : ι) => faceWeight m σ * h σ),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [Finset.mem_filter] at hσ
  rw [Finset.sum_const, hσ.2, nsmul_eq_mul]
  push_cast
  ring

/-- **The up and down operators are adjoint.** For `h` on level `k + 1` and `g` on level `k`,
`∑_{|σ| = k + 1} downSum m h σ · g σ = ∑_{|τ| = k + 2} faceWeight m τ · h τ · ∑_{σ ⊂ τ} g σ`,
the inner sum running over the `(k + 1)`-element subsets of `τ`. No hypothesis on `m`. -/
theorem sum_downSum_mul (m : Finset ι → ℝ) (k : ℕ) (h g : Finset ι → ℝ) :
    ∑ σ with #σ = k + 1, downSum m h σ * g σ =
      ∑ τ with #τ = k + 2, faceWeight m τ * h τ * ∑ ρ ∈ τ.powersetCard (k + 1), g ρ := by
  have e : ∀ σ : Finset ι, downSum m h σ * g σ = ∑ u, (if u ∈ σ then 0 else
      faceWeight m (insert u σ) * h (insert u σ) * g ((insert u σ).erase u)) := by
    intro σ
    rw [downSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs with hu
    · simp
    · rw [Finset.erase_insert hu]
  simp only [e]
  rw [sum_card_eq_sum_insert_eq_sum_mem (k + 1)
    (fun τ u => faceWeight m τ * h τ * g (τ.erase u))]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  rw [Finset.mem_filter] at hτ
  rw [sum_powersetCard_eq_sum_erase hτ.2, Finset.mul_sum]

/-- **The norm of the up operator.** For `m` supported on the sets with `d + 1` elements and `g`
on level `k`,
`∑_{|τ| = k + 2} faceWeight m τ · (∑_{σ ⊂ τ, |σ| = k + 1} g σ)² = (d − k) · levelNormSq + upForm`:
the diagonal terms `σ = σ'` give `(d − k) · levelNormSq` (each `σ` has cofaces of total weight
`(d − k) · faceWeight m σ`), and the off-diagonal ones give `upForm`. In walk terms,
`UpW_k = 1/(k + 2) · I + (k + 1)/(k + 2) · NUpW_k`. For `k ≥ d` both sides are `0`. -/
theorem sum_faceWeight_mul_sq_sum_powersetCard (hcard : ∀ F, m F ≠ 0 → #F = d + 1) (k : ℕ)
    (g : Finset ι → ℝ) :
    ∑ τ with #τ = k + 2, faceWeight m τ * (∑ σ ∈ τ.powersetCard (k + 1), g σ) ^ 2 =
      ((d : ℝ) - k) * levelNormSq m k g + upForm m k g := by
  have e1 : ∀ τ ∈ (univ : Finset (Finset ι)).filter (fun τ => #τ = k + 2),
      faceWeight m τ * (∑ σ ∈ τ.powersetCard (k + 1), g σ) ^ 2 =
        ∑ u ∈ τ, faceWeight m τ * g (τ.erase u) * ∑ u' ∈ τ, g (τ.erase u') := by
    intro τ hτ
    rw [sum_powersetCard_eq_sum_erase (Finset.mem_filter.mp hτ).2, sq, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [Finset.sum_congr rfl e1, ← sum_card_eq_sum_insert_eq_sum_mem (k + 1)
    (fun τ u => faceWeight m τ * g (τ.erase u) * ∑ u' ∈ τ, g (τ.erase u'))]
  have e3 : ∀ η ∈ (univ : Finset (Finset ι)).filter (fun η => #η = k + 1),
      ∑ u, (if u ∈ η then 0 else faceWeight m (insert u η) * g ((insert u η).erase u) *
        ∑ u' ∈ insert u η, g ((insert u η).erase u')) =
      ((d : ℝ) - k) * (faceWeight m η * g η ^ 2) + ∑ u' ∈ η, ∑ v,
        (if v ∈ η then 0 else faceWeight m (insert v η) * g η * g (insert v (η.erase u'))) := by
    intro η hη
    have hη := (Finset.mem_filter.mp hη).2
    have e4 : ∀ u, (if u ∈ η then 0 else faceWeight m (insert u η) * g ((insert u η).erase u) *
        ∑ u' ∈ insert u η, g ((insert u η).erase u')) =
        (if u ∈ η then 0 else faceWeight m (insert u η)) * g η ^ 2 + ∑ u' ∈ η,
          (if u ∈ η then 0 else faceWeight m (insert u η) * g η * g (insert u (η.erase u'))) := by
      intro u
      by_cases hu : u ∈ η
      · simp [hu]
      · simp only [if_neg hu]
        have e5 : ∑ u' ∈ η, g ((insert u η).erase u') = ∑ u' ∈ η, g (insert u (η.erase u')) :=
          Finset.sum_congr rfl fun u' hu' => by
            rw [Finset.erase_insert_of_ne (fun h : u = u' => hu (h ▸ hu'))]
        rw [Finset.sum_insert hu, Finset.erase_insert hu, e5]
        rw [mul_add, Finset.mul_sum]
        ring
    rw [Finset.sum_congr rfl fun u _ => e4 u, Finset.sum_add_distrib, ← Finset.sum_mul,
      sum_faceWeight_insert hcard η, hη, Finset.sum_comm]
    push_cast
    ring
  rw [Finset.sum_congr rfl e3, Finset.sum_add_distrib, ← Finset.mul_sum,
    upForm_eq_sum_insert_erase, levelNormSq]

/-- **From the up walk on level `i` to the down walk on level `i + 1`.** If
`‖U g‖² ≤ (d − i) β ‖g‖²` for every mean-zero `g` on level `i`, with `β ≥ 0`, then
`downNormSq m d (i + 1) h ≤ β · levelNormSq m (i + 1) h` for every mean-zero `h` on level `i + 1`.
Take `g` the down operator applied to `h` (it has mean zero), use adjointness and Cauchy–Schwarz.
The sign of `β` is needed when the down operator kills `h`. -/
private theorem downNormSq_succ_le (hnn : ∀ F, 0 ≤ m F) (hcard : ∀ F, m F ≠ 0 → #F = d + 1)
    {i : ℕ} (hi : i + 1 ≤ d) {β : ℝ} (hβ : 0 ≤ β)
    (hup : ∀ g : Finset ι → ℝ, ∑ σ with #σ = i + 1, faceWeight m σ * g σ = 0 →
      ∑ τ with #τ = i + 2, faceWeight m τ * (∑ ρ ∈ τ.powersetCard (i + 1), g ρ) ^ 2 ≤
        ((d : ℝ) - i) * β * levelNormSq m i g)
    (h : Finset ι → ℝ) (hh : ∑ τ with #τ = i + 2, faceWeight m τ * h τ = 0) :
    downNormSq m d (i + 1) h ≤ β * levelNormSq m (i + 1) h := by
  have hdi : (0 : ℝ) < (d : ℝ) - i := by
    have : ((i + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hi
    push_cast at this
    linarith
  obtain ⟨g, hg⟩ : ∃ g : Finset ι → ℝ,
      g = fun σ => downSum m h σ / (((d : ℝ) - i) * faceWeight m σ) := ⟨_, rfl⟩
  have hcoef : ((d : ℝ) + 1 - ((i + 1 : ℕ) : ℝ)) = (d : ℝ) - i := by push_cast; ring
  -- the down norm of `h`, three ways
  have hX1 : downNormSq m d (i + 1) h = ∑ σ with #σ = i + 1, downSum m h σ * g σ := by
    rw [downNormSq, hcoef]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hg]
    ring
  have hX2 : downNormSq m d (i + 1) h = ((d : ℝ) - i) * levelNormSq m i g := by
    rw [downNormSq, hcoef, levelNormSq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hg]
    by_cases h0 : faceWeight m σ = 0
    · simp [h0]
    · field_simp
  -- `g` has mean zero
  have hgmean : ∑ σ with #σ = i + 1, faceWeight m σ * g σ = 0 := by
    have e : ∀ σ ∈ (univ : Finset (Finset ι)).filter (fun σ => #σ = i + 1),
        faceWeight m σ * g σ = downSum m h σ / ((d : ℝ) - i) := by
      intro σ hσ
      rw [hg]
      by_cases h0 : faceWeight m σ = 0
      · have hds : downSum m h σ = 0 :=
          downSum_eq_zero_of_mul_faceWeight_eq_zero hnn hcard (by rw [h0, mul_zero]) h
        simp [h0, hds]
      · field_simp
    rw [Finset.sum_congr rfl e, ← Finset.sum_div, sum_downSum m (i + 1) h]
    have hh' : ∑ σ with #σ = i + 1 + 1, faceWeight m σ * h σ = 0 := hh
    rw [hh', mul_zero, zero_div]
  have hX3 : downNormSq m d (i + 1) h =
      ∑ τ with #τ = i + 2, faceWeight m τ * h τ * ∑ ρ ∈ τ.powersetCard (i + 1), g ρ := by
    rw [hX1, sum_downSum_mul]
  -- Cauchy–Schwarz
  have hCS : downNormSq m d (i + 1) h ^ 2 ≤ levelNormSq m (i + 1) h *
      ∑ τ with #τ = i + 2, faceWeight m τ * (∑ ρ ∈ τ.powersetCard (i + 1), g ρ) ^ 2 := by
    rw [hX3]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun τ _ => mul_nonneg (faceWeight_nonneg hnn τ) (sq_nonneg _))
      (fun τ _ => mul_nonneg (faceWeight_nonneg hnn τ) (sq_nonneg _)) (fun τ _ => le_of_eq ?_)
    ring
  have hU : ∑ τ with #τ = i + 2, faceWeight m τ * (∑ ρ ∈ τ.powersetCard (i + 1), g ρ) ^ 2 ≤
      β * downNormSq m d (i + 1) h := by
    rw [hX2]
    linarith [hup g hgmean]
  have hX0 : 0 ≤ downNormSq m d (i + 1) h := downNormSq_nonneg hnn hcard _ h
  have hL0 : 0 ≤ levelNormSq m (i + 1) h := levelNormSq_nonneg hnn _ h
  have h2 : downNormSq m d (i + 1) h * downNormSq m d (i + 1) h ≤
      (β * levelNormSq m (i + 1) h) * downNormSq m d (i + 1) h := by
    have := mul_le_mul_of_nonneg_left hU hL0
    nlinarith
  rcases hX0.eq_or_lt with h0 | h0
  · rw [← h0]
    exact mul_nonneg hβ hL0
  · exact le_of_mul_le_mul_right h2 h0

end Up

/-! ### Every bound on a link is at least `−1 / (d − |η|)` -/

section Sign

variable {K : PreAbstractSimplicialComplex ι} {d : ℕ} {m : Finset ι → ℝ}

/-- If a weighted graph with an edge `u v` satisfies the lower bound `c` on its quadratic form,
then every upper bound on its second eigenvalue is at least `c`. -/
private theorem le_of_walkSecondEigenvalueLE_of_lower {w : ι → ι → ℝ}
    (hsymm : ∀ u v, w u v = w v u) (hnn : ∀ u v, 0 ≤ w u v) {u v : ι} (hne : u ≠ v)
    (huv : 0 < w u v) {lam c : ℝ} (h : WalkSecondEigenvalueLE w lam)
    (hlow : ∀ f : ι → ℝ, c * ∑ x, (∑ y, w x y) * f x ^ 2 ≤ ∑ x, ∑ y, w x y * f x * f y) :
    c ≤ lam := by
  obtain ⟨a, ha⟩ : ∃ a, a = ∑ x, w u x := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ∑ x, w v x := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [ha]
    exact lt_of_lt_of_le huv (Finset.single_le_sum (fun x _ => hnn u x) (Finset.mem_univ v))
  have hb0 : 0 < b := by
    rw [hb]
    rw [hsymm] at huv
    exact lt_of_lt_of_le huv (Finset.single_le_sum (fun x _ => hnn v x) (Finset.mem_univ u))
  obtain ⟨f, hf⟩ : ∃ f : ι → ℝ, f = fun x => if x = u then b else if x = v then -a else 0 :=
    ⟨_, rfl⟩
  have hfu : f u = b := by rw [hf]; exact if_pos rfl
  have hfv : f v = -a := by rw [hf]; simp [hne.symm]
  have hf0 : ∀ x, x ≠ u ∧ x ≠ v → f x = 0 := fun x hx => by rw [hf]; simp [hx.1, hx.2]
  have hmean : ∑ x, (∑ y, w x y) * f x = 0 := by
    rw [Finset.sum_eq_add_of_mem u v (Finset.mem_univ _) (Finset.mem_univ _) hne
      fun x _ hx => by rw [hf0 x hx, mul_zero], hfu, hfv, ← ha, ← hb]
    ring
  have hnorm : ∑ x, (∑ y, w x y) * f x ^ 2 = a * b ^ 2 + b * a ^ 2 := by
    rw [Finset.sum_eq_add_of_mem u v (Finset.mem_univ _) (Finset.mem_univ _) hne
      fun x _ hx => by rw [hf0 x hx]; ring, hfu, hfv, ← ha, ← hb]
    ring
  have h1 := h f hmean
  have h2 := hlow f
  rw [hnorm] at h1 h2
  have hN : 0 < a * b ^ 2 + b * a ^ 2 := by positivity
  exact le_of_mul_le_mul_right (h2.trans h1) hN

/-- For a top weight, a bound `lam` on the second eigenvalue of the link of a face `η` (or of `∅`)
of dimension at most `d − 2` is at least `−1 / (d − |η|)`: the link has an edge
(`IsTopWeight.exists_linkWeightOf_pos`), and its quadratic form is at least `−1 / (d − |η|)`
times its norm (`link_walk_lower_bound`). -/
private theorem IsTopWeight.neg_one_div_le_of_link_bound (hm : K.IsTopWeight d m)
    {η : Finset ι} (hη : η = ∅ ∨ η ∈ K) (hcard : #η + 1 ≤ d) {lam : ℝ}
    (h : WalkSecondEigenvalueLE (linkWeightOf m η) lam) : -(1 / ((d : ℝ) - #η)) ≤ lam := by
  obtain ⟨u, v, huv⟩ := hm.exists_linkWeightOf_pos hη hcard
  have hne : u ≠ v := fun e => by
    rw [e, linkWeightOf_self] at huv
    exact lt_irrefl _ huv
  exact le_of_walkSecondEigenvalueLE_of_lower (linkWeightOf_symm m η)
    (linkWeightOf_nonneg hm.nonneg η) hne huv h fun f => hm.link_walk_lower_bound η f

omit [DecidableEq ι] [Fintype ι] in
/-- A complex with a top weight has a face, or `∅`, of every size up to `d + 1`. -/
private theorem IsTopWeight.exists_card_eq_of_le (hm : K.IsTopWeight d m) {j : ℕ}
    (hj : j ≤ d + 1) : ∃ η : Finset ι, (η = ∅ ∨ η ∈ K) ∧ #η = j := by
  obtain ⟨F, hF, hFc, -⟩ := hm.exists_pos
  obtain ⟨η, hηF, hηc⟩ := Finset.exists_subset_card_eq (s := F) (n := j) (by omega)
  refine ⟨η, ?_, hηc⟩
  rcases η.eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · exact Or.inr (K.mem_of_subset hF hηF h)

/-- If `−1 / (d − j) ≤ a j ≤ 1` for `j < n ≤ d`, then `∏_{j < n} (1 − a j) ≤ n + 1`: the product
is at most the telescoping product `(d + 1) / (d + 1 − n)`. Equality holds for `n = d` and
`a j = −1 / (d − j)`, the second eigenvalues of the links of the simplex. -/
private theorem prod_one_sub_le {n : ℕ} (hn : n ≤ d) {a : ℕ → ℝ} (h1 : ∀ j < n, a j ≤ 1)
    (h2 : ∀ j < n, -(1 / ((d : ℝ) - j)) ≤ a j) : ∏ j ∈ range n, (1 - a j) ≤ n + 1 := by
  have key : ∀ n : ℕ, n ≤ d → (∀ j < n, a j ≤ 1) → (∀ j < n, -(1 / ((d : ℝ) - j)) ≤ a j) →
      0 ≤ ∏ j ∈ range n, (1 - a j) ∧ ((d : ℝ) + 1 - n) * ∏ j ∈ range n, (1 - a j) ≤ d + 1 := by
    intro n
    induction n with
    | zero => intros; simp
    | succ n ih =>
      intro hn h1 h2
      obtain ⟨hP0, hP⟩ :=
        ih (by omega) (fun j hj => h1 j (by omega)) (fun j hj => h2 j (by omega))
      have hdn : (0 : ℝ) < (d : ℝ) - n := by
        have : ((n + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hn
        push_cast at this
        linarith
      have ha1 := h1 n (by omega)
      have ha2 := h2 n (by omega)
      have ha3 : -1 ≤ a n * ((d : ℝ) - n) := by
        have := mul_le_mul_of_nonneg_right ha2 hdn.le
        rwa [neg_mul, one_div, inv_mul_cancel₀ hdn.ne'] at this
      rw [Finset.prod_range_succ]
      refine ⟨mul_nonneg hP0 (by linarith), ?_⟩
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left ha3 hP0]
  obtain ⟨hP0, hP⟩ := key n hn h1 h2
  have hdn : (0 : ℝ) < (d : ℝ) + 1 - n := by
    have : (n : ℝ) ≤ d := by exact_mod_cast hn
    linarith
  have hnd : (n : ℝ) ≤ d := by exact_mod_cast hn
  have : ((d : ℝ) + 1 - n) * ∏ j ∈ range n, (1 - a j) ≤ ((d : ℝ) + 1 - n) * (n + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact le_of_mul_le_mul_left this hdn

end Sign

/-! ### The spectral gap of the up-down walk -/

section Gap

variable {K : PreAbstractSimplicialComplex ι} {d : ℕ} {m : Finset ι → ℝ}

/-- `upDown_gap` in the range `k + 1 ≤ d`, by induction on the level. The invariant at level `i`
is the bound `downNormSq m d i g ≤ (i + 1 − ∏_{j < i} (1 − lams j)) · levelNormSq m i g` for
mean-zero `g`. It holds at `i = 0` because `downSum m g ∅` is the mean of `g`; `upForm_le` and
`sum_faceWeight_mul_sq_sum_powersetCard` turn it into the bound on the up walk at level `i`, and
`downNormSq_succ_le` turns that into the invariant at level `i + 1`. -/
private theorem upDown_gap_of_lt (hm : K.IsTopWeight d m) {k : ℕ} (hk : k + 1 ≤ d)
    (lams : ℕ → ℝ) (hl1 : ∀ i ≤ k, lams i ≤ 1)
    (hloc : ∀ η : Finset ι, (η = ∅ ∨ η ∈ K) → #η ≤ k →
      WalkSecondEigenvalueLE (linkWeightOf m η) (lams #η))
    (g : Finset ι → ℝ) (hg : ∑ σ with #σ = k + 1, faceWeight m σ * g σ = 0) :
    ∑ τ with #τ = k + 2, faceWeight m τ * (∑ σ ∈ τ.powersetCard (k + 1), g σ) ^ 2 ≤
      ((d : ℝ) - k) * ((k : ℝ) + 2 - ∏ i ∈ range (k + 1), (1 - lams i)) *
        levelNormSq m k g := by
  have hnn := hm.nonneg
  have hcard := hm.card_eq_of_ne_zero
  -- the local bounds hold at every set of each size `i ≤ k`
  have hlocal : ∀ i ≤ k, ∀ η : Finset ι, #η = i →
      WalkSecondEigenvalueLE (linkWeightOf m η) (lams i) := by
    intro i hi η hη
    exact hm.walkSecondEigenvalueLE_of_faces fun hσ => hη ▸ hloc η hσ (hη ▸ hi)
  -- every local bound is at least `−1 / (d − i)`, so the products stay below `i + 2`
  have hneg : ∀ i ≤ k, -(1 / ((d : ℝ) - i)) ≤ lams i := by
    intro i hi
    obtain ⟨η, hη, hηc⟩ := hm.exists_card_eq_of_le (j := i) (by omega)
    have h := hm.neg_one_div_le_of_link_bound hη (by omega) (hloc η hη (by omega))
    rwa [hηc] at h
  have hprod : ∀ i ≤ k, ∏ j ∈ range (i + 1), (1 - lams j) ≤ (i : ℝ) + 2 := by
    intro i hi
    have := prod_one_sub_le (d := d) (n := i + 1) (by omega) (a := lams)
      (fun j hj => hl1 j (by omega)) (fun j hj => hneg j (by omega))
    push_cast at this
    linarith
  -- one step: the bound for the down walk on level `i` gives the bound for the up walk
  have hstep : ∀ i ≤ k, (∀ g : Finset ι → ℝ, ∑ σ with #σ = i + 1, faceWeight m σ * g σ = 0 →
      downNormSq m d i g ≤ ((i : ℝ) + 1 - ∏ j ∈ range i, (1 - lams j)) * levelNormSq m i g) →
      ∀ g : Finset ι → ℝ, ∑ σ with #σ = i + 1, faceWeight m σ * g σ = 0 →
      ∑ τ with #τ = i + 2, faceWeight m τ * (∑ σ ∈ τ.powersetCard (i + 1), g σ) ^ 2 ≤
        ((d : ℝ) - i) * ((i : ℝ) + 2 - ∏ j ∈ range (i + 1), (1 - lams j)) *
          levelNormSq m i g := by
    intro i hi hQ g hg
    have hdi : (0 : ℝ) ≤ (d : ℝ) - i := by
      have : (i : ℝ) + 1 ≤ d := by exact_mod_cast (show i + 1 ≤ d by omega)
      linarith
    have ha := upForm_le hnn hcard (hlocal i hi) g
    have hD := mul_le_mul_of_nonneg_left (hQ g hg) (mul_nonneg hdi (sub_nonneg.mpr (hl1 i hi)))
    rw [sum_faceWeight_mul_sq_sum_powersetCard hcard, Finset.prod_range_succ]
    linarith
  -- induction on the level
  have hQ : ∀ i ≤ k, ∀ g : Finset ι → ℝ, ∑ σ with #σ = i + 1, faceWeight m σ * g σ = 0 →
      downNormSq m d i g ≤ ((i : ℝ) + 1 - ∏ j ∈ range i, (1 - lams j)) * levelNormSq m i g := by
    intro i
    induction i with
    | zero =>
      intro _ g hg
      have hfilt : (univ : Finset (Finset ι)).filter (fun η => #η = 0) = {∅} := by
        ext η
        simp
      have h0 := sum_downSum m 0 g
      rw [hfilt, Finset.sum_singleton, hg, mul_zero] at h0
      rw [downNormSq, hfilt, Finset.sum_singleton, h0]
      simp
    | succ i ih =>
      intro hi h hh
      have hP := hstep i (by omega) (ih (by omega))
      have hβ : 0 ≤ (i : ℝ) + 2 - ∏ j ∈ range (i + 1), (1 - lams j) := by
        linarith [hprod i (by omega)]
      have := downNormSq_succ_le hnn hcard (i := i) (by omega) hβ hP h hh
      have e : ((i + 1 : ℕ) : ℝ) + 1 = (i : ℝ) + 2 := by push_cast; ring
      rw [e]
      exact this
  exact hstep k le_rfl (hQ k le_rfl) g hg

/-- **Alev–Lau, Theorem 3.1: the local-to-global theorem for the up-down walk.** Let `m` be a
top weight of the `d`-dimensional complex `K`. Suppose that for every `i ≤ k`, the link of every
face with `i` elements (`lams 0`: of `∅`, i.e. the weighted underlying graph of `K`) has random-walk
second eigenvalue at most `lams i`, and `lams i ≤ 1`. Then for every `g` on level `k` with mean
zero (`∑ faceWeight m σ · g σ = 0`),
`∑_{|τ| = k + 2} faceWeight m τ · (∑_{σ ⊂ τ, |σ| = k + 1} g σ)² ≤
(d − k)(k + 2 − ∏_{i ≤ k} (1 − lams i)) · levelNormSq m k g`.
Divided by `(d − k)(k + 2) Z_k` this says that the up-down walk `UpW_k` has second eigenvalue at
most `1 − (1/(k + 2)) ∏_{i=0}^{k} (1 − lams i)`, i.e. spectral gap at least
`(1/(k + 2)) ∏_{i=0}^{k} (1 − lams i)`. This is Alev–Lau's Theorem 3.1 with their `k` replaced by
`k + 1`; their `γ_j`, a bound for the links of the `j`-dimensional faces, is our `lams (j + 1)`.

Hypotheses and degenerate cases:
* `hl1` (`lams i ≤ 1`, only for `i ≤ k`) cannot be dropped: on the complete `2`-dimensional
  complex on `4` vertices with `k = 1`, the bounds `lams 0 = lams 1 = 3` are valid (every
  second eigenvalue is at most `1`), but they make the right side `−levelNormSq m 1 g`, which is
  negative for every nonzero mean-zero `g`, while the left side is never negative.
* No lower bound on `lams` is assumed. The proof needs `lams i ≥ −1/(d − i)`, which follows from
  `hloc`: every link in question has an edge, and the eigenvalues of a link are at least
  `−1/(d − i)` (`link_walk_lower_bound`). With it the product is at most `k + 2`, so the right
  side is never negative; for the simplex and `k = d − 1` the product is exactly `k + 2`.
* `hloc` is only asked of faces (and `∅`); the links of the other sets are empty.
* `k ≥ d`: both sides are `0`, since no set with `k + 2` elements has weight, and either
  `d − k = 0` or `levelNormSq m k g = 0`. So `d = 0` is entirely degenerate.
* `k = 0`: the bound is `λ₂(UpW_0) ≤ (1 + lams 0)/2`. Here `UpW_0` is the lazy version of the
  random walk on the weighted graph `linkWeightOf m ∅` of `K`, so the bound is sharp. -/
theorem upDown_gap (hm : K.IsTopWeight d m) {k : ℕ} (lams : ℕ → ℝ) (hl1 : ∀ i ≤ k, lams i ≤ 1)
    (hloc : ∀ η : Finset ι, (η = ∅ ∨ η ∈ K) → #η ≤ k →
      WalkSecondEigenvalueLE (linkWeightOf m η) (lams #η))
    (g : Finset ι → ℝ) (hg : ∑ σ with #σ = k + 1, faceWeight m σ * g σ = 0) :
    ∑ τ with #τ = k + 2, faceWeight m τ * (∑ σ ∈ τ.powersetCard (k + 1), g σ) ^ 2 ≤
      ((d : ℝ) - k) * ((k : ℝ) + 2 - ∏ i ∈ range (k + 1), (1 - lams i)) *
        levelNormSq m k g := by
  by_cases hk : k + 1 ≤ d
  · exact upDown_gap_of_lt hm hk lams hl1 hloc g hg
  · have hcard := hm.card_eq_of_ne_zero
    have hL : ∑ τ with #τ = k + 2,
        faceWeight m τ * (∑ σ ∈ τ.powersetCard (k + 1), g σ) ^ 2 = 0 :=
      Finset.sum_eq_zero fun τ hτ => by
        rw [faceWeight_eq_zero_of_lt_card hcard (by rw [(Finset.mem_filter.mp hτ).2]; omega),
          zero_mul]
    have hR : ((d : ℝ) - k) * levelNormSq m k g = 0 := by
      rcases (show k = d ∨ d + 1 ≤ k by omega) with h | h
      · rw [h, sub_self, zero_mul]
      · have : levelNormSq m k g = 0 := Finset.sum_eq_zero fun σ hσ => by
          rw [faceWeight_eq_zero_of_lt_card hcard (by rw [(Finset.mem_filter.mp hσ).2]; omega),
            zero_mul]
        rw [this, mul_zero]
    rw [hL, mul_right_comm, hR, zero_mul]

/-- **The local-to-global theorem for a local spectral expander.** If `K` with the weight `m` is
a `lam`-local-spectral expander of dimension `d` with `lam ≤ 1`, then for every level `k` and
every mean-zero `g` on level `k`,
`∑_{|τ| = k + 2} faceWeight m τ · (∑_{σ ⊂ τ} g σ)² ≤
(d − k)(k + 2 − (1 − lam)^(k + 1)) · levelNormSq m k g`:
the up-down walk on level `k` has second eigenvalue at most `1 − (1 − lam)^(k + 1)/(k + 2)`. This
is `upDown_gap` with `lams` constant. The condition `lam ≤ 1` is needed (see `upDown_gap`). Links
of sets with `d` or more elements are empty, so `k` is unrestricted; for `k ≥ d` both sides are
`0`. -/
theorem IsLocalSpectralExpanderOf.upDown_gap {lam : ℝ} (h : K.IsLocalSpectralExpanderOf d m lam)
    (hlam : lam ≤ 1) (k : ℕ) (g : Finset ι → ℝ)
    (hg : ∑ σ with #σ = k + 1, faceWeight m σ * g σ = 0) :
    ∑ τ with #τ = k + 2, faceWeight m τ * (∑ σ ∈ τ.powersetCard (k + 1), g σ) ^ 2 ≤
      ((d : ℝ) - k) * ((k : ℝ) + 2 - (1 - lam) ^ (k + 1)) * levelNormSq m k g := by
  have := PreAbstractSimplicialComplex.upDown_gap h.isTopWeight (k := k) (fun _ => lam)
    (fun _ _ => hlam) (fun η hη _ => ?_) g hg
  · rwa [Finset.prod_const, Finset.card_range] at this
  · by_cases hd : #η + 1 ≤ d
    · exact h.walkSecondEigenvalueLE hη hd
    · exact walkSecondEigenvalueLE_of_forall_eq_zero
        (linkWeightOf_eq_zero_of_le_card h.isTopWeight.card_eq_of_ne_zero (by omega)) lam

end Gap

end PreAbstractSimplicialComplex
