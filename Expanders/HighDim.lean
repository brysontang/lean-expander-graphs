/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.WeightedGraph

/-!
# High-dimensional expanders

Simplicial complexes, links, and the "every link is a spectral expander" definition of a
high-dimensional expander, built on Mathlib's `PreAbstractSimplicialComplex` (a collection of
nonempty finite sets closed under taking nonempty subsets).

This file has the definitions, and the facts that depend only on *which* faces exist. The facts
that depend on *how many* top faces pass through a set (the counting identities and trickling
down) are proved for arbitrary weights on the top faces in `Expanders/WeightedComplex.lean`, and
specialised to counts in `Expanders/TricklingDown.lean`.

## Definitions
* `PreAbstractSimplicialComplex.link`: the link of a face.
* `PreAbstractSimplicialComplex.IsPure`: all maximal faces have the same dimension `d`.
* `PreAbstractSimplicialComplex.oneSkeleton`, `IsConnected`: the underlying graph.
* `PreAbstractSimplicialComplex.linkWeight`: the weighted graph on the link of a face, each edge
  weighted by the number of top-dimensional faces through it.
* `PreAbstractSimplicialComplex.IsLocalSpectralExpander`: a pure `d`-dimensional complex, `d ≥ 1`,
  with at least one face, in which every link of a face of dimension at most `d − 2` (including the
  whole complex) has random-walk second eigenvalue at most `lam`.

## Theorems
* `link_empty`, `link_link`: basic calculus of links. **Proved.**
* `exists_linkWeight_pos`, `IsLocalSpectralExpander.exists_linkWeight_pos`: every link that the
  definition of a local spectral expander quantifies over has an edge, so no instance of its
  second-eigenvalue bound is vacuous. **Proved.**
* `eq_of_forall_linkWeight_pos`: connectivity of a link, as a statement about its weighted graph.
  **Proved.**
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
face. It is the neighbourhood of `σ`, viewed as a complex in its own right.

`σ` is any finite set, not necessarily a face. The link of `∅` is `K` (`link_empty`). The link of
a nonempty set that is not a face has no faces (`notMem_link_of_notMem`), and neither does the
link of a maximal face. No vertex of `σ` is a vertex of its link. -/
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

/-- The link of a nonempty set that is not a face has no faces. -/
theorem notMem_link_of_notMem {σ : Finset ι} (hne : σ.Nonempty) (hσ : σ ∉ K) (τ : Finset ι) :
    τ ∉ K.link σ := fun h =>
  hσ (K.mem_of_subset (mem_link.mp h).2.2 subset_union_right hne)

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
in a face with exactly `d + 1` vertices.

The complex with no faces is pure of every dimension (`isPure_of_forall_notMem`). A definition
that is meant to describe a `d`-dimensional complex therefore asks for a face separately, as
`IsLocalSpectralExpander` and `IsTopWeight` do; a pure complex with a face has a face with `d + 1`
vertices (`IsPure.exists_card_eq`). For `d = 0` a pure complex is a set of vertices. -/
def IsPure (d : ℕ) : Prop :=
  ∀ σ ∈ K, #σ ≤ d + 1 ∧ ∃ τ ∈ K, σ ⊆ τ ∧ #τ = d + 1

omit [DecidableEq ι] in
/-- The complex with no faces is pure of every dimension. -/
theorem isPure_of_forall_notMem (h : ∀ σ, σ ∉ K) (d : ℕ) : K.IsPure d :=
  fun σ hσ => absurd hσ (h σ)

variable {K} in
omit [DecidableEq ι] in
/-- A pure complex with a face has a face of dimension `d`. -/
theorem IsPure.exists_card_eq {d : ℕ} (hpure : K.IsPure d) (hne : ∃ F, F ∈ K) :
    ∃ F ∈ K, #F = d + 1 := by
  obtain ⟨τ, hτ⟩ := hne
  obtain ⟨-, F, hF, -, hcard⟩ := hpure τ hτ
  exact ⟨F, hF, hcard⟩

/-- The vertices of `K`. -/
def vertices : Set ι := {v | {v} ∈ K}

/-- The underlying graph (1-skeleton) of `K`: distinct `u`, `v` are adjacent when `{u, v}` is a
face. -/
def oneSkeleton : SimpleGraph ι :=
  SimpleGraph.fromRel fun u v => ({u, v} : Finset ι) ∈ K

/-- `K` is **connected**: its underlying graph, on the vertices of `K`, is connected.

A connected graph has a vertex, so the complex with no faces is *not* connected
(`IsConnected.exists_mem`). In particular the link of a nonempty set that is not a face is not
connected, nor is the link of a maximal face. -/
def IsConnected : Prop := (K.oneSkeleton.induce K.vertices).Connected

variable {K} in
/-- A connected complex has a face: connectivity includes having a vertex. -/
theorem IsConnected.exists_mem (h : K.IsConnected) : ∃ σ, σ ∈ K := by
  have h' : (K.oneSkeleton.induce K.vertices).Connected := h
  obtain ⟨v, hv⟩ := h'.nonempty
  exact ⟨{v}, hv⟩

/-! ### Local spectral expansion -/

variable [Fintype ι]

open Classical in
/-- The number of `d`-dimensional faces of `K` containing the set `s`.

`s` is any finite set: `topDegree d ∅` is the number of all `d`-dimensional faces, and
`topDegree d s = 0` when `s` lies in no `d`-dimensional face (`topDegree_pos_iff`), for instance
when `s` is nonempty and not a face. -/
noncomputable def topDegree (d : ℕ) (s : Finset ι) : ℕ :=
  #{F : Finset ι | F ∈ K ∧ #F = d + 1 ∧ s ⊆ F}

/-- The **weighted graph of the link of `σ`** in a `d`-dimensional complex: two distinct
vertices `u, v` outside `σ` are joined with weight the number of `d`-dimensional faces
containing `σ ∪ {u, v}`. For `σ = ∅` this is the weighted underlying graph of `K` itself.

The graph lives on all of `ι`. The weight is `0` when `u = v`, when `u` or `v` is a vertex of `σ`,
and when `σ ∪ {u, v}` lies in no `d`-dimensional face (`linkWeight_pos_iff`); so every vertex that
is not a vertex of the link is isolated. The graph has no edges at all when `σ` is nonempty and
not a face (`linkWeight_eq_zero_of_notMem`) or has at least `d` elements
(`linkWeight_eq_zero_of_le_card`).

This is the case of `linkWeightOf` in which every top face has weight `1`
(`linkWeight_eq_linkWeightOf`). -/
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
in the one-sided sense): `d ≥ 1`, `K` is pure of dimension `d` and has at least one face, and for
every face `σ` of dimension at most `d − 2`, and for `σ = ∅`, the random walk on the weighted graph
of the link of `σ` has second eigenvalue at most `lam`.

Purity and the existence of a face are part of the definition because the second-eigenvalue bound
says nothing about a graph with no edges (`walkSecondEigenvalueLE_of_forall_eq_zero`): without
them the complex with no faces would be a `lam`-expander for every `lam`. With them, every link in
question has an edge (`IsLocalSpectralExpander.exists_linkWeight_pos`), so no instance of the
bound is vacuous.

The condition `1 ≤ d` excludes dimension `0`, for a similar reason. No `σ` has `#σ + 1 ≤ 0`, so a
`0`-dimensional complex has no link to test, and without the condition every nonempty set of
vertices would be a `lam`-expander for every `lam`. With it, no complex is a `0`-dimensional
expander (`not_isLocalSpectralExpander_zero`), and the complex itself (`σ = ∅`) is always tested.

Degenerate parameters:
* `d = 1`. Only `σ = ∅` occurs: `K` is a graph with an edge and no isolated vertex, and its
  random walk has second eigenvalue at most `lam`.
* A `σ` that is neither `∅` nor a face is not quantified over. Its weighted graph has no edges
  (`linkWeight_eq_zero_of_notMem`).
* The bound is one-sided and `lam` can be negative: all triangles on five points form a
  `(−1/4)`-expander (`isLocalSpectralExpander_complete_fin5_two`). It cannot be below `−1/d`
  (`IsLocalSpectralExpander.neg_one_div_le`).

This is the case of `IsLocalSpectralExpanderOf` in which every top face has weight `1`
(`isLocalSpectralExpander_iff_isLocalSpectralExpanderOf`). -/
def IsLocalSpectralExpander (d : ℕ) (lam : ℝ) : Prop :=
  1 ≤ d ∧ K.IsPure d ∧ (∃ F, F ∈ K) ∧ ∀ σ : Finset ι, (σ = ∅ ∨ σ ∈ K) → #σ + 1 ≤ d →
    WalkSecondEigenvalueLE (K.linkWeight d σ) lam

/-! ### The weighted graph of a link: edges and connectivity -/

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
`IsLocalSpectralExpander` is never vacuous (compare `walkSecondEigenvalueLE_of_forall_eq_zero`);
see `IsLocalSpectralExpander.exists_linkWeight_pos`. -/
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

/-! ### Local spectral expanders -/

section

variable {K} {d : ℕ} {lam : ℝ}

theorem IsLocalSpectralExpander.one_le (h : K.IsLocalSpectralExpander d lam) : 1 ≤ d := h.1

theorem IsLocalSpectralExpander.isPure (h : K.IsLocalSpectralExpander d lam) : K.IsPure d := h.2.1

theorem IsLocalSpectralExpander.exists_mem (h : K.IsLocalSpectralExpander d lam) : ∃ F, F ∈ K :=
  h.2.2.1

theorem IsLocalSpectralExpander.walkSecondEigenvalueLE (h : K.IsLocalSpectralExpander d lam)
    {σ : Finset ι} (hσ : σ = ∅ ∨ σ ∈ K) (hcard : #σ + 1 ≤ d) :
    WalkSecondEigenvalueLE (K.linkWeight d σ) lam :=
  h.2.2.2 σ hσ hcard

/-- **Non-vacuity of `IsLocalSpectralExpander`.** In a local spectral expander, every link that
the definition quantifies over (the complex itself and the link of every face of dimension at most
`d − 2`) has an edge. So the second-eigenvalue bound is never the vacuous one of
`walkSecondEigenvalueLE_of_forall_eq_zero`. -/
theorem IsLocalSpectralExpander.exists_linkWeight_pos (h : K.IsLocalSpectralExpander d lam)
    {σ : Finset ι} (hσ : σ = ∅ ∨ σ ∈ K) (hcard : #σ + 1 ≤ d) :
    ∃ u v, 0 < K.linkWeight d σ u v := by
  rcases hσ with rfl | hσ
  · obtain ⟨τ, hτ⟩ := h.exists_mem
    exact K.exists_linkWeight_pos h.isPure hτ (Finset.empty_subset τ) hcard
  · exact K.exists_linkWeight_pos h.isPure hσ subset_rfl hcard

/-- **No `0`-dimensional expanders.** A `0`-dimensional complex has no link to test, so the
definition excludes dimension `0`: no complex is a `0`-dimensional local spectral expander, for any
`lam`. -/
theorem not_isLocalSpectralExpander_zero : ¬ K.IsLocalSpectralExpander 0 lam :=
  fun h => absurd h.one_le (by omega)

end

end PreAbstractSimplicialComplex
