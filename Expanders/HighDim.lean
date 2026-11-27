/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.WeightedGraph
import Expanders.TricklingDownSpectral

/-!
# High-dimensional expanders

Simplicial complexes, links, and the "every link is a spectral expander" definition of a
high-dimensional expander, built on Mathlib's `PreAbstractSimplicialComplex` (a collection of
nonempty finite sets closed under taking nonempty subsets).

## Definitions
* `PreAbstractSimplicialComplex.link`: the link of a face.
* `PreAbstractSimplicialComplex.IsPure`: all maximal faces have the same dimension `d`.
* `PreAbstractSimplicialComplex.oneSkeleton`, `IsConnected`: the underlying graph.
* `PreAbstractSimplicialComplex.linkWeight`: the weighted graph on the link of a face, each edge
  weighted by the number of top-dimensional faces through it.
* `PreAbstractSimplicialComplex.IsLocalSpectralExpander`: every link of a face of dimension at
  most `d − 2` (including the whole complex) has random-walk second eigenvalue at most `lam`.

## Theorems
* `link_empty`, `link_link`: basic calculus of links. **Proved.**
* `sum_topDegree_insert`, `sum_linkWeight`, `sum_linkWeight_insert`: double counting of top
  faces, giving the degrees of a link and the localisation of a link to its vertex links.
  **Proved.**
* `trickling_down`: Oppenheim's local-to-global theorem. **Proved.**
-/

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] (K : PreAbstractSimplicialComplex ι)

/-! ### Faces -/

omit [DecidableEq ι] in
theorem nonempty_of_mem {σ : Finset ι} (h : σ ∈ K) : σ.Nonempty :=
  (K.isRelLowerSet_faces h).1

omit [DecidableEq ι] in
/-- Faces are closed under taking nonempty subsets. -/
theorem mem_of_subset {σ τ : Finset ι} (h : σ ∈ K) (hτ : τ ⊆ σ) (hne : τ.Nonempty) : τ ∈ K :=
  (K.isRelLowerSet_faces h).2 hτ hne

/-! ### Links -/

/-- The **link** of `σ` in `K`: the faces `τ` disjoint from `σ` such that `τ ∪ σ` is again a
face. It is the neighbourhood of `σ`, viewed as a complex in its own right. -/
def link (σ : Finset ι) : PreAbstractSimplicialComplex ι where
  faces := {τ | τ.Nonempty ∧ Disjoint τ σ ∧ τ ∪ σ ∈ K}
  isRelLowerSet_faces := by
    rintro τ ⟨hne, hdisj, hmem⟩
    exact ⟨hne, fun ρ hρτ hρ => ⟨hρ, hdisj.mono_left hρτ,
      K.mem_of_subset hmem (union_subset_union_left hρτ) (hρ.mono subset_union_left)⟩⟩

variable {K} in
theorem mem_link {σ τ : Finset ι} :
    τ ∈ K.link σ ↔ τ.Nonempty ∧ Disjoint τ σ ∧ τ ∪ σ ∈ K := Iff.rfl

/-- The link of the empty set is the whole complex. -/
@[simp]
theorem link_empty : K.link ∅ = K := by
  refine SetLike.ext fun τ => ?_
  simp only [mem_link, disjoint_empty_right, union_empty, true_and, and_iff_right_iff_imp]
  exact K.nonempty_of_mem

/-- A link of a link is a link: `(K.link σ).link τ = K.link (σ ∪ τ)` for `τ` disjoint from `σ`. -/
theorem link_link {σ τ : Finset ι} (h : Disjoint τ σ) :
    (K.link σ).link τ = K.link (σ ∪ τ) := by
  refine SetLike.ext fun ρ => ?_
  simp only [mem_link]
  constructor
  · rintro ⟨hne, hρτ, -, hdisj, hmem⟩
    refine ⟨hne, disjoint_union_right.mpr ⟨(disjoint_union_left.mp hdisj).1, hρτ⟩, ?_⟩
    rwa [union_comm σ τ, ← union_assoc]
  · rintro ⟨hne, hdisj, hmem⟩
    rw [disjoint_union_right] at hdisj
    refine ⟨hne, hdisj.2, hne.mono subset_union_left,
      disjoint_union_left.mpr ⟨hdisj.1, h⟩, ?_⟩
    rwa [union_comm σ τ, ← union_assoc] at hmem

/-! ### Dimension, purity, connectivity -/

/-- `K` is **pure of dimension `d`**: every face has at most `d + 1` vertices and is contained
in a face with exactly `d + 1` vertices. -/
def IsPure (d : ℕ) : Prop :=
  ∀ σ ∈ K, #σ ≤ d + 1 ∧ ∃ τ ∈ K, σ ⊆ τ ∧ #τ = d + 1

/-- The vertices of `K`. -/
def vertices : Set ι := {v | {v} ∈ K}

/-- The underlying graph (1-skeleton) of `K`: distinct `u`, `v` are adjacent when `{u, v}` is a
face. -/
def oneSkeleton : SimpleGraph ι :=
  SimpleGraph.fromRel fun u v => ({u, v} : Finset ι) ∈ K

/-- `K` is **connected**: its underlying graph, on the vertices of `K`, is connected. -/
def IsConnected : Prop := (K.oneSkeleton.induce K.vertices).Connected

/-! ### Local spectral expansion -/

variable [Fintype ι]

open Classical in
/-- The number of `d`-dimensional faces of `K` containing the set `s`. -/
noncomputable def topDegree (d : ℕ) (s : Finset ι) : ℕ :=
  #{F : Finset ι | F ∈ K ∧ #F = d + 1 ∧ s ⊆ F}

/-- The **weighted graph of the link of `σ`** in a `d`-dimensional complex: two distinct
vertices `u, v` outside `σ` are joined with weight the number of `d`-dimensional faces
containing `σ ∪ {u, v}`. For `σ = ∅` this is the weighted underlying graph of `K` itself. -/
noncomputable def linkWeight (d : ℕ) (σ : Finset ι) (u v : ι) : ℝ :=
  if u ≠ v ∧ u ∉ σ ∧ v ∉ σ then (K.topDegree d (insert u (insert v σ)) : ℝ) else 0

theorem linkWeight_nonneg (d : ℕ) (σ : Finset ι) (u v : ι) : 0 ≤ K.linkWeight d σ u v := by
  unfold linkWeight
  split_ifs <;> positivity

theorem linkWeight_symm (d : ℕ) (σ : Finset ι) (u v : ι) :
    K.linkWeight d σ u v = K.linkWeight d σ v u := by
  unfold linkWeight
  rw [Finset.insert_comm u v σ]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.symm, h3, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.symm, h3, h2⟩

/-- `K` is a **`lam`-local-spectral expander** of dimension `d` (a *high-dimensional expander*,
in the one-sided sense): for every face `σ` of dimension at most `d − 2`, and for `σ = ∅`, the
random walk on the weighted graph of the link of `σ` has second eigenvalue at most `lam`.

The bound says nothing about a link with no edges (`walkSecondEigenvalueLE_of_forall_eq_zero`).
In a pure `d`-dimensional complex with at least one face every link in question has an edge
(`exists_linkWeight_pos`), so the condition is never vacuous there. The empty complex is the one
exception: it has no faces, and it satisfies this definition for every `lam`. -/
def IsLocalSpectralExpander (d : ℕ) (lam : ℝ) : Prop :=
  ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d →
    WalkSecondEigenvalueLE (K.linkWeight d σ) lam

/-! ### Counting top faces -/

theorem topDegree_pos_iff {d : ℕ} {s : Finset ι} :
    0 < K.topDegree d s ↔ ∃ F ∈ K, #F = d + 1 ∧ s ⊆ F := by
  classical
  unfold topDegree
  rw [Finset.card_pos]
  constructor
  · rintro ⟨F, hF⟩
    rw [Finset.mem_filter] at hF
    exact ⟨F, hF.2⟩
  · rintro ⟨F, hF⟩
    exact ⟨F, Finset.mem_filter.mpr ⟨Finset.mem_univ F, hF⟩⟩

/-- **Double counting.** Every top face through `s` has exactly `d + 1 − |s|` vertices outside
`s`, so summing `topDegree (s ∪ {v})` over `v ∉ s` counts each such face `d + 1 − |s|` times. -/
theorem sum_topDegree_insert (d : ℕ) (s : Finset ι) :
    ∑ v ∈ sᶜ, K.topDegree d (insert v s) + #s * K.topDegree d s = (d + 1) * K.topDegree d s := by
  classical
  unfold topDegree
  generalize hT : ({F : Finset ι | F ∈ K ∧ #F = d + 1 ∧ s ⊆ F} : Finset (Finset ι)) = T
  have hmemT : ∀ F, F ∈ T ↔ F ∈ K ∧ #F = d + 1 ∧ s ⊆ F := by
    intro F
    rw [← hT, Finset.mem_filter]
    simp
  have h1 : ∀ v ∈ sᶜ, #({F : Finset ι | F ∈ K ∧ #F = d + 1 ∧ insert v s ⊆ F} : Finset (Finset ι))
      = #(T.bipartiteAbove (fun (v : ι) (F : Finset ι) => v ∈ F) v) := by
    intro v _
    congr 1
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.bipartiteAbove, hmemT,
      Finset.insert_subset_iff]
    tauto
  rw [Finset.sum_congr rfl h1, Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  have h2 : ∀ F ∈ T, #(sᶜ.bipartiteBelow (fun (v : ι) (F : Finset ι) => v ∈ F) F) + #s = d + 1 := by
    intro F hF
    rw [hmemT] at hF
    have h3 : sᶜ.bipartiteBelow (fun (v : ι) (F : Finset ι) => v ∈ F) F = F \ s := by
      ext v
      simp [Finset.bipartiteBelow, and_comm]
    rw [h3, Finset.card_sdiff_add_card_eq_card hF.2.2, hF.2.1]
  calc ∑ F ∈ T, #(sᶜ.bipartiteBelow (fun (v : ι) (F : Finset ι) => v ∈ F) F) + #s * #T
      = ∑ F ∈ T, (#(sᶜ.bipartiteBelow (fun (v : ι) (F : Finset ι) => v ∈ F) F) + #s) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm #s]
    _ = ∑ _F ∈ T, (d + 1) := Finset.sum_congr rfl h2
    _ = (d + 1) * #T := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- `sum_topDegree_insert` over the reals, as a sum over all vertices. -/
theorem sum_topDegree_insert_real (d : ℕ) (s : Finset ι) :
    ∑ v, (if v ∈ s then 0 else (K.topDegree d (insert v s) : ℝ)) =
      ((d : ℝ) + 1 - #s) * K.topDegree d s := by
  have h : (∑ v ∈ sᶜ, (K.topDegree d (insert v s) : ℝ)) + #s * K.topDegree d s
      = ((d : ℝ) + 1) * K.topDegree d s := by
    exact_mod_cast K.sum_topDegree_insert d s
  have h' : ∑ v, (if v ∈ s then 0 else (K.topDegree d (insert v s) : ℝ))
      = ∑ v ∈ sᶜ, (K.topDegree d (insert v s) : ℝ) := by
    rw [← Finset.sum_compl_add_sum s, Finset.sum_eq_zero (s := s) fun v hv => if_pos hv, add_zero]
    exact Finset.sum_congr rfl fun v hv => if_neg (Finset.mem_compl.mp hv)
  rw [h']
  linarith

/-! ### The weighted graph of a link: degrees, localisation, connectivity -/

theorem linkWeight_pos_iff {d : ℕ} {σ : Finset ι} {u v : ι} :
    0 < K.linkWeight d σ u v ↔
      u ≠ v ∧ u ∉ σ ∧ v ∉ σ ∧ ∃ F ∈ K, #F = d + 1 ∧ insert u (insert v σ) ⊆ F := by
  unfold linkWeight
  split_ifs with h
  · rw [Nat.cast_pos, topDegree_pos_iff]
    exact ⟨fun hF => ⟨h.1, h.2.1, h.2.2, hF⟩, fun hF => hF.2.2.2⟩
  · exact ⟨fun h0 => absurd h0 (lt_irrefl _), fun hF => absurd ⟨hF.1, hF.2.1, hF.2.2.1⟩ h⟩

/-- In a pure `d`-dimensional complex, the weighted graph of the link of a set `σ` of dimension at
most `d − 2` that lies in some face has an edge. So the second-eigenvalue bound in
`IsLocalSpectralExpander` is never vacuous (compare `walkSecondEigenvalueLE_of_forall_eq_zero`). -/
theorem exists_linkWeight_pos {d : ℕ} (hpure : K.IsPure d) {σ τ : Finset ι} (hτ : τ ∈ K)
    (hστ : σ ⊆ τ) (hcard : #σ + 1 ≤ d) : ∃ u v, 0 < K.linkWeight d σ u v := by
  -- a top face `F ⊇ τ ⊇ σ` has `d + 1 − |σ| ≥ 2` vertices outside `σ`
  obtain ⟨-, F, hF, hτF, hFcard⟩ := hpure τ hτ
  have hσF : σ ⊆ F := hστ.trans hτF
  have h2 : 1 < #(F \ σ) := by
    have h := Finset.card_sdiff_add_card_eq_card hσF
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
  rw [Finset.mem_sdiff] at hu hv
  exact ⟨u, v, K.linkWeight_pos_iff.mpr ⟨huv, hu.2, hv.2, F, hF, hFcard,
    Finset.insert_subset hu.1 (Finset.insert_subset hv.1 hσF)⟩⟩

/-- The weighted graph of the "link" of a nonempty set that is not a face is empty. -/
theorem linkWeight_eq_zero_of_notMem {d : ℕ} {τ : Finset ι} (hne : τ.Nonempty) (hτ : τ ∉ K)
    (u v : ι) : K.linkWeight d τ u v = 0 := by
  by_contra h
  have hpos : 0 < K.linkWeight d τ u v :=
    lt_of_le_of_ne (K.linkWeight_nonneg d τ u v) (Ne.symm h)
  obtain ⟨-, -, -, F, hF, -, hsub⟩ := K.linkWeight_pos_iff.mp hpos
  exact hτ (K.mem_of_subset hF
    (fun x hx => hsub (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))) hne)

/-- **Degrees in a link.** The degree of `u ∉ τ` in the weighted graph of the link of `τ` is
`d − |τ|` times the number of top faces through `τ ∪ {u}`. -/
theorem sum_linkWeight (d : ℕ) (τ : Finset ι) (u : ι) :
    ∑ v, K.linkWeight d τ u v =
      if u ∈ τ then 0 else ((d : ℝ) - #τ) * K.topDegree d (insert u τ) := by
  split_ifs with hu
  · refine Finset.sum_eq_zero fun v _ => ?_
    unfold linkWeight
    exact if_neg fun h => h.2.1 hu
  · have h := K.sum_topDegree_insert_real d (insert u τ)
    rw [Finset.card_insert_of_notMem hu] at h
    push_cast at h
    rw [show (d : ℝ) - #τ = (d : ℝ) + 1 - (#τ + 1) by ring, ← h]
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold linkWeight
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
theorem sum_linkWeight_insert (d : ℕ) (σ : Finset ι) (u v : ι) :
    ∑ z, (if z ∈ σ then 0 else K.linkWeight d (insert z σ) u v) =
      ((d : ℝ) - 1 - #σ) * K.linkWeight d σ u v := by
  by_cases h : u ≠ v ∧ u ∉ σ ∧ v ∉ σ
  · have hs : #(insert u (insert v σ)) = #σ + 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem h.2.2]
      rw [Finset.mem_insert, not_or]
      exact ⟨h.1, h.2.1⟩
    have h1 := K.sum_topDegree_insert_real d (insert u (insert v σ))
    rw [hs] at h1
    push_cast at h1
    rw [linkWeight, if_pos h, show (d : ℝ) - 1 - #σ = (d : ℝ) + 1 - (#σ + 2) by ring, ← h1]
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold linkWeight
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
  · rw [linkWeight, if_neg h, mul_zero]
    refine Finset.sum_eq_zero fun z _ => ?_
    split_ifs with hz
    · rfl
    · unfold linkWeight
      refine if_neg fun h' => h ⟨h'.1, ?_, ?_⟩
      · exact fun hu => h'.2.1 (Finset.mem_insert_of_mem hu)
      · exact fun hv => h'.2.2 (Finset.mem_insert_of_mem hv)

/-- **Localisation of degrees.** The degree of `u` in the link of `σ ∪ {z}` is `d − 1 − |σ|`
times the weight of the edge `z u` in the link of `σ`. -/
theorem sum_linkWeight_insert_right (d : ℕ) (σ : Finset ι) (z u : ι) :
    ∑ v, (if z ∈ σ then 0 else K.linkWeight d (insert z σ) u v) =
      ((d : ℝ) - 1 - #σ) * K.linkWeight d σ z u := by
  by_cases hz : z ∈ σ
  · have h0 : K.linkWeight d σ z u = 0 := by
      unfold linkWeight
      exact if_neg fun h => h.2.1 hz
    simp [hz, h0]
  · simp only [if_neg hz]
    rw [K.sum_linkWeight d (insert z σ) u, Finset.card_insert_of_notMem hz]
    by_cases hu : u ∈ insert z σ
    · have h0 : K.linkWeight d σ z u = 0 := by
        unfold linkWeight
        refine if_neg ?_
        rintro ⟨h1, -, h3⟩
        rcases Finset.mem_insert.mp hu with h | h
        · exact h1 h.symm
        · exact h3 h
      rw [if_pos hu, h0, mul_zero]
    · rw [if_neg hu]
      rw [Finset.mem_insert, not_or] at hu
      rw [linkWeight, if_pos ⟨Ne.symm hu.1, hz, hu.2⟩, Finset.insert_comm z u]
      push_cast
      ring

/-- In a pure complex, an edge of the link of `σ` lies in a top face, so it has positive
weight. -/
theorem linkWeight_pos_of_adj {d : ℕ} (hpure : K.IsPure d) {σ : Finset ι} {u v : ι}
    (h : (K.link σ).oneSkeleton.Adj u v) : 0 < K.linkWeight d σ u v := by
  rw [oneSkeleton, SimpleGraph.fromRel_adj] at h
  obtain ⟨hne, h⟩ := h
  have h' : ({u, v} : Finset ι) ∈ K.link σ := by
    rcases h with h | h
    · exact h
    · rwa [Finset.pair_comm]
  obtain ⟨-, hdisj, hmem⟩ := mem_link.mp h'
  obtain ⟨-, τ, hτ, hsub, hcard⟩ := hpure _ hmem
  rw [linkWeight_pos_iff]
  refine ⟨hne, ?_, ?_, τ, hτ, hcard, ?_⟩
  · exact Finset.disjoint_left.mp hdisj (by simp)
  · exact Finset.disjoint_left.mp hdisj (by simp)
  · intro x hx
    refine hsub ?_
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hx ⊢
    tauto

/-- A vertex of positive degree in the weighted graph of the link of `σ` is a vertex of the
link. -/
theorem mem_vertices_link_of_pos {d : ℕ} {σ : Finset ι} {u : ι}
    (h : 0 < ∑ v, K.linkWeight d σ u v) : u ∈ (K.link σ).vertices := by
  obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  have hpos : 0 < K.linkWeight d σ u v :=
    lt_of_le_of_ne (K.linkWeight_nonneg d σ u v) (Ne.symm hv)
  obtain ⟨-, hu, -, F, hF, -, hsub⟩ := K.linkWeight_pos_iff.mp hpos
  refine mem_link.mpr ⟨Finset.singleton_nonempty u, Finset.disjoint_singleton_left.mpr hu,
    K.mem_of_subset hF ?_ ⟨u, by simp⟩⟩
  intro x hx
  refine hsub ?_
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hx ⊢
  tauto

/-- **Connectivity, in weighted form.** If the link of `σ` is connected (and `K` is pure), a
function that is constant along every edge of positive weight takes a single value on all
vertices of positive degree. -/
theorem eq_of_forall_linkWeight_pos {d : ℕ} (hpure : K.IsPure d) {σ : Finset ι}
    (hconn : (K.link σ).IsConnected) (g : ι → ℝ)
    (hg : ∀ u v, 0 < K.linkWeight d σ u v → g u = g v) (u v : ι)
    (hu : 0 < ∑ x, K.linkWeight d σ u x) (hv : 0 < ∑ x, K.linkWeight d σ v x) : g u = g v := by
  have hreach := hconn.preconnected ⟨u, K.mem_vertices_link_of_pos hu⟩
    ⟨v, K.mem_vertices_link_of_pos hv⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have key : ∀ b : (K.link σ).vertices,
      Relation.ReflTransGen ((K.link σ).oneSkeleton.induce (K.link σ).vertices).Adj
        ⟨u, K.mem_vertices_link_of_pos hu⟩ b → g u = g b := by
    intro b hb
    induction hb with
    | refl => rfl
    | tail _ hab ih =>
      exact ih.trans (hg _ _ (K.linkWeight_pos_of_adj hpure (SimpleGraph.comap_adj.mp hab)))
  exact key _ hreach

/-! ### Trickling down -/

/-- **One step of trickling down.** Let `σ` have dimension at most `d − 3` (possibly `σ = ∅`),
with connected link. If the link of every face `σ ∪ {z}` has second eigenvalue at most `μ < 1`,
then the link of `σ` has second eigenvalue at most `μ / (1 − μ)`. -/
theorem walkSecondEigenvalueLE_linkWeight_step {d : ℕ} (hpure : K.IsPure d) {σ : Finset ι}
    (hcard : #σ + 2 ≤ d) (hconn : (K.link σ).IsConnected) {μ : ℝ} (hμ : μ < 1)
    (hloc : ∀ z, z ∉ σ → insert z σ ∈ K →
      WalkSecondEigenvalueLE (K.linkWeight d (insert z σ)) μ) :
    WalkSecondEigenvalueLE (K.linkWeight d σ) (μ / (1 - μ)) := by
  have hc : (0 : ℝ) < (d : ℝ) - 1 - #σ := by
    have h : ((#σ + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hcard
    push_cast at h
    linarith
  refine walkSecondEigenvalueLE_of_garland (K.linkWeight_symm d σ) (K.linkWeight_nonneg d σ) hμ
    (K.eq_of_forall_linkWeight_pos hpure hconn) ?_
  refine garland_inequality
    (wz := fun z u v => if z ∈ σ then 0 else K.linkWeight d (insert z σ) u v) hc
    (K.linkWeight_symm d σ) ?_ (K.sum_linkWeight_insert d σ)
    (K.sum_linkWeight_insert_right d σ) ?_
  · intro z u v
    split_ifs
    · rfl
    · exact K.linkWeight_symm d (insert z σ) u v
  · intro z
    by_cases hz : z ∈ σ
    · intro f _
      simp [hz]
    · by_cases hK : insert z σ ∈ K
      · simpa only [if_neg hz] using hloc z hz hK
      · intro f _
        simp [hz, K.linkWeight_eq_zero_of_notMem (Finset.insert_nonempty z σ) hK]

/-- **Trickling down (Oppenheim).** Let `K` be a pure `d`-dimensional complex, `d ≥ 2`, in which
`K` itself and every link of a face of dimension at most `d − 2` is connected. If the link of
every `(d − 2)`-dimensional face has second eigenvalue at most `lam`, where `(d − 1) · lam < 1`,
then the link of every face `σ` of dimension at most `d − 2` has second eigenvalue at most
`lam / (1 − (d − 1 − |σ|) · lam)`; taking `σ = ∅`, the underlying graph of `K` has second
eigenvalue at most `lam / (1 − (d − 1) · lam)`. Expansion of the smallest links forces expansion
everywhere.

The proof is by downward induction on `|σ|`; the inductive step
(`walkSecondEigenvalueLE_linkWeight_step`) localises the quadratic form of a link to its vertex
links (Garland's method, `garland_inequality`) and solves a quadratic inequality for the second
eigenvalue (`walkSecondEigenvalueLE_of_garland`). -/
theorem trickling_down {d : ℕ} (hd : 2 ≤ d) (hpure : K.IsPure d)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d → (K.link σ).IsConnected)
    {lam : ℝ} (hlam : ((d : ℝ) - 1) * lam < 1)
    (hlocal : ∀ σ ∈ K, #σ + 1 = d → WalkSecondEigenvalueLE (K.linkWeight d σ) lam) :
    ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d →
      WalkSecondEigenvalueLE (K.linkWeight d σ) (lam / (1 - ((d : ℝ) - 1 - #σ) * lam)) := by
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
      WalkSecondEigenvalueLE (K.linkWeight d σ) (lam / (1 - (j : ℝ) * lam)) := by
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
      have hstep := K.walkSecondEigenvalueLE_linkWeight_step hpure (σ := σ) (by omega)
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

/-- Trickling down, packaged: under the hypotheses of `trickling_down` with `lam ≥ 0`, the
complex is a `lam / (1 − (d − 1) lam)`-local-spectral expander. -/
theorem isLocalSpectralExpander_of_trickling_down {d : ℕ} (hd : 2 ≤ d) (hpure : K.IsPure d)
    (hconn : ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d → (K.link σ).IsConnected)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : ((d : ℝ) - 1) * lam < 1)
    (hlocal : ∀ σ ∈ K, #σ + 1 = d → WalkSecondEigenvalueLE (K.linkWeight d σ) lam) :
    K.IsLocalSpectralExpander d (lam / (1 - ((d : ℝ) - 1) * lam)) := by
  intro σ hσ hcard
  refine (K.trickling_down hd hpure hconn hlam hlocal σ hσ hcard).mono
    (K.linkWeight_nonneg d σ) ?_
  -- `lam / (1 − (d − 1 − |σ|) lam) ≤ lam / (1 − (d − 1) lam)` because `lam ≥ 0`.
  have hσ0 : (0 : ℝ) ≤ #σ := Nat.cast_nonneg _
  have h1 : 0 < 1 - ((d : ℝ) - 1) * lam := by linarith
  have h2 : 1 - ((d : ℝ) - 1) * lam ≤ 1 - ((d : ℝ) - 1 - #σ) * lam := by nlinarith
  exact div_le_div_of_nonneg_left hlam0 h1 h2

end PreAbstractSimplicialComplex
