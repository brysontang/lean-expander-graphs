/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.Basic

/-!
# The configuration model of random regular graphs

The configuration (or pairing) model of Bender–Canfield and Bollobás turns questions about
uniformly random `d`-regular graphs into questions about uniformly random perfect matchings.

Take `n * d` **points** `Fin n × Fin d`; the point `(v, i)` is the `i`-th half-edge at the vertex
`v`. A **pairing** is a perfect matching of the points, recorded as a fixed-point-free involution.
Contracting the `d` points of each vertex turns a pairing into a `d`-regular multigraph on
`Fin n`; the pairing is **simple** when that multigraph has no loops and no repeated edges, in
which case it is a simple graph `graph π`.

## Definitions
* `ConfigurationModel.IsPairing`, `ConfigurationModel.pairings`: pairings of the points.
* `ConfigurationModel.IsSimple`, `ConfigurationModel.simplePairings`: simple pairings.
* `ConfigurationModel.graph`: the graph of a pairing.
* `ConfigurationModel.cross`: the number of pairs of a pairing leaving a vertex set.
* `ConfigurationModel.IsBad`, `ConfigurationModel.badPairings`: pairings with a sparse cut.

## Results (all proved here; this file has no `sorry`)
* `isRegularOfDegree_graph`: the graph of a simple pairing is `d`-regular.
* `card_edgeBoundary_graph`, `isEdgeExpander_graph_iff`: for a simple pairing the edge boundary
  of `S` in the graph has `cross π S` elements, so the graph is an `ε`-edge-expander exactly when
  the pairing is not `ε`-bad.
* `card_filter_graph_eq`: every `d`-regular graph on `Fin n` is the graph of exactly `(d!)ⁿ`
  simple pairings.
* `card_simplePairings`, `card_simplePairings_filter_isBad`: hence
  `#{simple pairings} = #{d-regular graphs} · (d!)ⁿ`, and likewise for the bad ones.
* `pairings_nonempty`: pairings exist when `n * d` is even.
* `one_sub_card_badPairings_div_le`: the proportion of `d`-regular graphs that are
  `ε`-edge-expanders is at least `1 - #{ε-bad pairings} / #{simple pairings}`.
* `tendsto_card_regular_isEdgeExpander_div`: the reduction. If a positive proportion of pairings
  is simple and the proportion of `ε`-bad pairings tends to `0`, then the proportion of
  `d`-regular graphs that are `ε`-edge-expanders tends to `1`.

The two hypotheses of the reduction live in `Expanders/ConfigurationModelSimple.lean` (proved,
by a switching argument in `Expanders/ConfigurationModelSwitching.lean`) and
`Expanders/ConfigurationModelExpansion.lean` (still open).
-/

open Finset Filter Topology

namespace ConfigurationModel

variable {n d : ℕ}

/-! ## Pairings -/

/-- A **pairing** of the points `Fin n × Fin d`: a perfect matching, recorded as the
fixed-point-free involution that sends each point to its partner. -/
def IsPairing (π : Equiv.Perm (Fin n × Fin d)) : Prop :=
  (∀ p, π (π p) = p) ∧ ∀ p, π p ≠ p

instance : DecidablePred (IsPairing (n := n) (d := d)) := fun π => by
  unfold IsPairing; infer_instance

/-- A pairing is **simple** if no pair joins two points of the same vertex (no loops) and no two
distinct pairs join the same two vertices (no repeated edges).

The second clause reads: two points `p`, `q` of the same vertex whose partners lie in a common
vertex are equal. Applied to `q` and to the partner of `q` this covers both ways in which two
pairs can join the same two vertices. -/
def IsSimple (π : Equiv.Perm (Fin n × Fin d)) : Prop :=
  (∀ p, (π p).1 ≠ p.1) ∧ ∀ p q, p.1 = q.1 → (π p).1 = (π q).1 → p = q

instance : DecidablePred (IsSimple (n := n) (d := d)) := fun π => by
  unfold IsSimple; infer_instance

/-- The pairings of the `n * d` points `Fin n × Fin d`. -/
def pairings (n d : ℕ) : Finset (Equiv.Perm (Fin n × Fin d)) := {π | IsPairing π}

/-- The simple pairings of the `n * d` points `Fin n × Fin d`. -/
def simplePairings (n d : ℕ) : Finset (Equiv.Perm (Fin n × Fin d)) :=
  {π ∈ pairings n d | IsSimple π}

@[simp]
theorem mem_pairings {π : Equiv.Perm (Fin n × Fin d)} : π ∈ pairings n d ↔ IsPairing π := by
  simp [pairings]

@[simp]
theorem mem_simplePairings {π : Equiv.Perm (Fin n × Fin d)} :
    π ∈ simplePairings n d ↔ IsPairing π ∧ IsSimple π := by
  simp [simplePairings]

theorem simplePairings_subset_pairings : simplePairings n d ⊆ pairings n d :=
  filter_subset _ _

/-- The number of pairs of `π` with exactly one endpoint at a vertex of `S`. Each such pair is
counted once, through its endpoint in `S`. -/
def cross (π : Equiv.Perm (Fin n × Fin d)) (S : Finset (Fin n)) : ℕ :=
  #{p : Fin n × Fin d | p.1 ∈ S ∧ (π p).1 ∉ S}

/-- A pairing is **`ε`-bad** if some vertex set `S` containing at most half the vertices has
fewer than `ε|S|` pairs leaving it. (The inequality is strict, so `S = ∅` is never a witness.) -/
def IsBad (ε : ℝ) (π : Equiv.Perm (Fin n × Fin d)) : Prop :=
  ∃ S : Finset (Fin n), 2 * #S ≤ n ∧ (cross π S : ℝ) < ε * #S

open Classical in
/-- The `ε`-bad pairings of the `n * d` points `Fin n × Fin d`. -/
noncomputable def badPairings (n d : ℕ) (ε : ℝ) : Finset (Equiv.Perm (Fin n × Fin d)) :=
  {π ∈ pairings n d | IsBad ε π}

@[simp]
theorem mem_badPairings {ε : ℝ} {π : Equiv.Perm (Fin n × Fin d)} :
    π ∈ badPairings n d ε ↔ IsPairing π ∧ IsBad ε π := by
  simp [badPairings]

/-- Pairings exist as soon as the number `n * d` of points is even. -/
theorem pairings_nonempty (h : Even (n * d)) : (pairings n d).Nonempty := by
  obtain ⟨m, hm⟩ := h
  have hcard : Fintype.card (Fin n × Fin d) = Fintype.card (Fin m ⊕ Fin m) := by simp [hm]
  let e : Fin n × Fin d ≃ Fin m ⊕ Fin m := Fintype.equivOfCardEq hcard
  refine ⟨e.trans ((Equiv.sumComm _ _).trans e.symm), ?_⟩
  rw [mem_pairings]
  refine ⟨fun p => by simp, fun p hp => ?_⟩
  have hswap : (e p).swap = e p := by simpa [Equiv.symm_apply_eq] using hp
  cases h : e p <;> simp [h] at hswap

/-! ## The graph of a pairing -/

/-- The graph of a pairing: `u ~ v` when `u ≠ v` and some point of `u` is paired with some point
of `v`. (Defined for every permutation of the points, by symmetrising.) -/
def graph (π : Equiv.Perm (Fin n × Fin d)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => ∃ i, (π (u, i)).1 = v

variable {π : Equiv.Perm (Fin n × Fin d)}

/-- In the graph of a simple pairing, `u ~ v` exactly when some point of `u` has its partner
at `v`. -/
theorem graph_adj (hπ : IsPairing π) (hs : IsSimple π) {u v : Fin n} :
    (graph π).Adj u v ↔ ∃ i, (π (u, i)).1 = v := by
  rw [graph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨i, hi⟩ | ⟨j, hj⟩⟩
    · exact ⟨i, hi⟩
    · refine ⟨(π (v, j)).2, ?_⟩
      have h : π (v, j) = (u, (π (v, j)).2) := Prod.ext hj rfl
      rw [← h, hπ.1]
  · rintro ⟨i, hi⟩
    exact ⟨fun h => hs.1 (u, i) (by rw [hi, h]), Or.inl ⟨i, hi⟩⟩

/-- **The graph of a simple pairing is `d`-regular**: the neighbours of `v` are the vertices of
the partners of the `d` points of `v`, and these are distinct. -/
theorem isRegularOfDegree_graph (hπ : IsPairing π) (hs : IsSimple π) [(graph π).LocallyFinite] :
    (graph π).IsRegularOfDegree d := by
  classical
  intro v
  have h : (graph π).neighborFinset v = univ.image fun i : Fin d => (π (v, i)).1 := by
    ext w
    rw [SimpleGraph.mem_neighborFinset, graph_adj hπ hs]
    simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, h, card_image_of_injective, card_univ,
    Fintype.card_fin]
  intro i j hij
  exact (Prod.ext_iff.mp (hs.2 (v, i) (v, j) rfl hij)).2

/-- **Boundary edges are crossing pairs**: in the graph of a simple pairing, the edges leaving
`S` correspond to the pairs with exactly one endpoint in `S`. -/
theorem card_edgeBoundary_graph (hπ : IsPairing π) (hs : IsSimple π)
    [DecidableRel (graph π).Adj] (S : Finset (Fin n)) :
    #((graph π).edgeBoundary S) = cross π S := by
  symm
  refine card_bij (fun p _ => (p.1, (π p).1)) ?_ ?_ ?_
  · intro p hp
    obtain ⟨-, h1, h2⟩ := mem_filter.mp hp
    exact SimpleGraph.mem_edgeBoundary.mpr ⟨h1, h2, (graph_adj hπ hs).mpr ⟨p.2, rfl⟩⟩
  · intro p _ q _ h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
    exact hs.2 p q h1 h2
  · rintro ⟨u, v⟩ he
    obtain ⟨hu, hv, hadj⟩ := SimpleGraph.mem_edgeBoundary.mp he
    obtain ⟨i, hi⟩ := (graph_adj hπ hs).mp hadj
    refine ⟨(u, i), mem_filter.mpr ⟨mem_univ _, hu, ?_⟩, Prod.ext rfl hi⟩
    rw [hi]; exact hv

/-- The graph of a simple pairing is an `ε`-edge-expander exactly when the pairing is not
`ε`-bad. -/
theorem isEdgeExpander_graph_iff (hπ : IsPairing π) (hs : IsSimple π)
    [DecidableRel (graph π).Adj] {ε : ℝ} :
    (graph π).IsEdgeExpander ε ↔ ¬ IsBad ε π := by
  simp only [SimpleGraph.IsEdgeExpander, IsBad, card_edgeBoundary_graph hπ hs, Fintype.card_fin,
    not_exists, not_and, not_lt]

/-! ## The fibres of `graph`

A simple pairing whose graph is `G` is the same thing as a choice, at every vertex `v`, of a
bijection between the `d` points of `v` and the neighbours of `v` (the point `(v, i)` is sent to
the vertex of its partner). So a `d`-regular graph is the graph of exactly `(d!)ⁿ` simple
pairings. -/

section Fiber

variable (G : SimpleGraph (Fin n))

/-- The function underlying `ofLabelling`: the partner of the point `(v, i)` is the point of
`w = f v i` that `f w` sends back to `v`. -/
private def ofLabellingFun (f : ∀ v, Fin d ≃ G.neighborSet v) (p : Fin n × Fin d) :
    Fin n × Fin d :=
  ((f p.1 p.2 : Fin n), (f (f p.1 p.2)).symm ⟨p.1, G.adj_symm (f p.1 p.2).2⟩)

private theorem ofLabellingFun_eq_iff (f : ∀ v, Fin d ≃ G.neighborSet v) {v w : Fin n}
    {i j : Fin d} :
    ofLabellingFun G f (v, i) = (w, j) ↔ (f v i : Fin n) = w ∧ (f w j : Fin n) = v := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
    simp only [ofLabellingFun] at h1 h2
    subst h1
    refine ⟨rfl, ?_⟩
    rw [Equiv.symm_apply_eq] at h2
    exact (congrArg Subtype.val h2).symm
  · rintro ⟨rfl, h2⟩
    refine Prod.ext rfl ?_
    simp only [ofLabellingFun]
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext h2.symm

private theorem ofLabellingFun_involutive (f : ∀ v, Fin d ≃ G.neighborSet v) :
    Function.Involutive (ofLabellingFun G f) := by
  rintro ⟨v, i⟩
  obtain ⟨h1, h2⟩ := (ofLabellingFun_eq_iff G f (v := v) (i := i)
    (w := (ofLabellingFun G f (v, i)).1) (j := (ofLabellingFun G f (v, i)).2)).mp rfl
  exact (ofLabellingFun_eq_iff G f).mpr ⟨h2, h1⟩

/-- The pairing determined by a labelling of `G`, that is by a bijection, at every vertex `v`,
between the `d` points of `v` and the neighbours of `v`: the point `(v, i)` is paired with the
point of `w = f v i` that `f w` sends back to `v`. -/
def ofLabelling (f : ∀ v, Fin d ≃ G.neighborSet v) : Equiv.Perm (Fin n × Fin d) :=
  (ofLabellingFun_involutive G f).toPerm _

variable {G}

/-- The defining property of `ofLabelling`: `(v, i)` is paired with `(w, j)` exactly when `f v`
sends `i` to `w` and `f w` sends `j` to `v`. -/
theorem ofLabelling_eq_iff (f : ∀ v, Fin d ≃ G.neighborSet v) {v w : Fin n} {i j : Fin d} :
    ofLabelling G f (v, i) = (w, j) ↔ (f v i : Fin n) = w ∧ (f w j : Fin n) = v :=
  ofLabellingFun_eq_iff G f

theorem ofLabelling_apply_fst (f : ∀ v, Fin d ≃ G.neighborSet v) (p : Fin n × Fin d) :
    (ofLabelling G f p).1 = f p.1 p.2 :=
  rfl

/-- The pairing of a labelling is simple. -/
theorem isSimple_ofLabelling (f : ∀ v, Fin d ≃ G.neighborSet v) : IsSimple (ofLabelling G f) := by
  refine ⟨fun p => ?_, fun p q hpq h => ?_⟩
  · rw [ofLabelling_apply_fst]
    exact (G.ne_of_adj (f p.1 p.2).2).symm
  · obtain ⟨v, i⟩ := p
    obtain ⟨w, j⟩ := q
    obtain rfl : v = w := hpq
    have hij : i = j := (f v).injective (Subtype.ext h)
    rw [hij]

/-- The pairing of a labelling is a pairing. -/
theorem isPairing_ofLabelling (f : ∀ v, Fin d ≃ G.neighborSet v) :
    IsPairing (ofLabelling G f) :=
  ⟨ofLabellingFun_involutive G f, fun p hp =>
    (isSimple_ofLabelling f).1 p (congrArg Prod.fst hp)⟩

/-- The graph of the pairing of a labelling of `G` is `G`. -/
theorem graph_ofLabelling (f : ∀ v, Fin d ≃ G.neighborSet v) : graph (ofLabelling G f) = G := by
  ext u v
  rw [graph_adj (isPairing_ofLabelling f) (isSimple_ofLabelling f)]
  constructor
  · rintro ⟨i, rfl⟩
    exact (f u i).2
  · intro h
    exact ⟨(f u).symm ⟨v, h⟩, by rw [ofLabelling_apply_fst]; simp⟩

/-- Distinct labellings of `G` give distinct pairings. -/
theorem ofLabelling_injective :
    Function.Injective (ofLabelling G : (∀ v, Fin d ≃ G.neighborSet v) → _) := by
  intro f g h
  funext v
  refine Equiv.ext fun i => Subtype.ext ?_
  exact congrArg (fun π : Equiv.Perm (Fin n × Fin d) => (π (v, i)).1) h

/-- The labelling of the graph of a simple pairing: the point `(v, i)` is sent to the vertex of
its partner. -/
noncomputable def labelling (hπ : IsPairing π) (hs : IsSimple π) (v : Fin n) :
    Fin d ≃ (graph π).neighborSet v :=
  Equiv.ofBijective (fun i => ⟨(π (v, i)).1, (graph_adj hπ hs).mpr ⟨i, rfl⟩⟩)
    ⟨fun i j hij => (Prod.ext_iff.mp
        (hs.2 (v, i) (v, j) rfl (congrArg Subtype.val hij))).2,
      fun w => by
        obtain ⟨i, hi⟩ := (graph_adj hπ hs).mp w.2
        exact ⟨i, Subtype.ext hi⟩⟩

/-- A simple pairing is the pairing of its own labelling. -/
theorem ofLabelling_labelling (hπ : IsPairing π) (hs : IsSimple π) :
    ofLabelling (graph π) (labelling hπ hs) = π := by
  ext1 ⟨v, i⟩
  have h : π (v, i) = ((π (v, i)).1, (π (v, i)).2) := rfl
  rw [h, ofLabelling_eq_iff]
  refine ⟨rfl, ?_⟩
  change (π ((π (v, i)).1, (π (v, i)).2)).1 = v
  rw [← h, hπ.1]

/-- **Fibre count.** Every `d`-regular graph on `Fin n` is the graph of exactly `(d!)ⁿ` simple
pairings: one for each choice, at every vertex, of a bijection between its `d` points and its
`d` neighbours. -/
theorem card_filter_graph_eq [DecidableEq (SimpleGraph (Fin n))] (G : SimpleGraph (Fin n))
    [G.LocallyFinite] (hG : G.IsRegularOfDegree d) :
    #{π ∈ simplePairings n d | graph π = G} = d.factorial ^ n := by
  classical
  have himg : ({π ∈ simplePairings n d | graph π = G} : Finset _)
      = univ.image (ofLabelling G : (∀ v, Fin d ≃ G.neighborSet v) → _) := by
    ext π
    simp only [mem_filter, mem_simplePairings, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hπ, hs⟩, rfl⟩
      exact ⟨labelling hπ hs, ofLabelling_labelling hπ hs⟩
    · rintro ⟨f, rfl⟩
      exact ⟨⟨isPairing_ofLabelling f, isSimple_ofLabelling f⟩, graph_ofLabelling f⟩
  have hcard : ∀ v, Fintype.card (Fin d ≃ G.neighborSet v) = d.factorial := by
    intro v
    have hc : Fintype.card (Fin d) = Fintype.card (G.neighborSet v) := by
      rw [Fintype.card_fin, G.card_neighborSet_eq_degree, hG v]
    rw [Fintype.card_equiv (Fintype.equivOfCardEq hc), Fintype.card_fin]
  rw [himg, card_image_of_injective _ ofLabelling_injective, card_univ, Fintype.card_pi]
  simp [hcard]

end Fiber

/-! ## Counting regular graphs through pairings -/

open Classical in
/-- `#{simple pairings} = #{d-regular graphs on n vertices} · (d!)ⁿ`. -/
theorem card_simplePairings (n d : ℕ) :
    #(simplePairings n d)
      = #{G : SimpleGraph (Fin n) | G.IsRegularOfDegree d} * d.factorial ^ n := by
  have hmaps : (simplePairings n d : Set (Equiv.Perm (Fin n × Fin d))).MapsTo graph
      (({G : SimpleGraph (Fin n) | G.IsRegularOfDegree d} : Finset (SimpleGraph (Fin n))) :
        Set (SimpleGraph (Fin n))) := by
    intro π hπ
    obtain ⟨hp, hs⟩ := mem_simplePairings.mp (mem_coe.mp hπ)
    exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, isRegularOfDegree_graph hp hs⟩)
  rw [card_eq_sum_card_fiberwise hmaps,
    sum_congr rfl fun G hG => card_filter_graph_eq G (mem_filter.mp hG).2, sum_const,
    smul_eq_mul]

open Classical in
/-- `#{simple ε-bad pairings} = #{d-regular graphs that are not ε-edge-expanders} · (d!)ⁿ`. -/
theorem card_simplePairings_filter_isBad (n d : ℕ) (ε : ℝ) :
    #{π ∈ simplePairings n d | IsBad ε π}
      = #{G : SimpleGraph (Fin n) | G.IsRegularOfDegree d ∧ ¬ G.IsEdgeExpander ε}
        * d.factorial ^ n := by
  have hmaps : (({π ∈ simplePairings n d | IsBad ε π} : Finset (Equiv.Perm (Fin n × Fin d))) :
        Set (Equiv.Perm (Fin n × Fin d))).MapsTo graph
      (({G : SimpleGraph (Fin n) | G.IsRegularOfDegree d ∧ ¬ G.IsEdgeExpander ε} :
        Finset (SimpleGraph (Fin n))) : Set (SimpleGraph (Fin n))) := by
    intro π hπ
    obtain ⟨hπs, hbad⟩ := mem_filter.mp (mem_coe.mp hπ)
    obtain ⟨hp, hs⟩ := mem_simplePairings.mp hπs
    exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, isRegularOfDegree_graph hp hs,
      fun h => (isEdgeExpander_graph_iff hp hs).mp h hbad⟩)
  have hfib : ∀ G ∈ ({G : SimpleGraph (Fin n) | G.IsRegularOfDegree d ∧ ¬ G.IsEdgeExpander ε} :
      Finset _), #{π ∈ {π ∈ simplePairings n d | IsBad ε π} | graph π = G} = d.factorial ^ n := by
    intro G hG
    obtain ⟨hreg, hnexp⟩ := (mem_filter.mp hG).2
    rw [← card_filter_graph_eq G hreg]
    congr 1
    ext π
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨hs, -⟩, h⟩
      exact ⟨hs, h⟩
    · rintro ⟨hs, rfl⟩
      obtain ⟨hp, hs'⟩ := mem_simplePairings.mp hs
      refine ⟨⟨hs, ?_⟩, rfl⟩
      by_contra hb
      exact hnexp ((isEdgeExpander_graph_iff hp hs').mpr hb)
  rw [card_eq_sum_card_fiberwise hmaps, sum_congr rfl hfib, sum_const, smul_eq_mul]

open Classical in
/-- **Regular graphs versus pairings.** If simple pairings exist, the proportion of `d`-regular
graphs on `n` vertices that are `ε`-edge-expanders is at least
`1 - #{ε-bad pairings} / #{simple pairings}`. -/
theorem one_sub_card_badPairings_div_le (n d : ℕ) (ε : ℝ) (h : (simplePairings n d).Nonempty) :
    1 - (#(badPairings n d ε) : ℝ) / #(simplePairings n d)
      ≤ (#{G : SimpleGraph (Fin n) | G.IsRegularOfDegree d ∧ G.IsEdgeExpander ε} : ℝ)
        / #{G : SimpleGraph (Fin n) | G.IsRegularOfDegree d} := by
  have hs := card_simplePairings n d
  have hsb := card_simplePairings_filter_isBad n d ε
  have hsplit : #{G : SimpleGraph (Fin n) | G.IsRegularOfDegree d ∧ G.IsEdgeExpander ε}
      + #{G : SimpleGraph (Fin n) | G.IsRegularOfDegree d ∧ ¬ G.IsEdgeExpander ε}
      = #{G : SimpleGraph (Fin n) | G.IsRegularOfDegree d} := by
    rw [← card_filter_add_card_filter_not (s := ({G : SimpleGraph (Fin n) |
      G.IsRegularOfDegree d} : Finset _)) (fun G => G.IsEdgeExpander ε), filter_filter,
      filter_filter]
  have hle : #{π ∈ simplePairings n d | IsBad ε π} ≤ #(badPairings n d ε) := by
    refine card_le_card fun π hπ => ?_
    obtain ⟨hπs, hbad⟩ := mem_filter.mp hπ
    exact mem_badPairings.mpr ⟨(mem_simplePairings.mp hπs).1, hbad⟩
  have hspos : (0 : ℝ) < #(simplePairings n d) := by exact_mod_cast h.card_pos
  have hF : (0 : ℝ) < (d.factorial : ℝ) ^ n := by positivity
  have hr : (0 : ℝ) < #{G : SimpleGraph (Fin n) | G.IsRegularOfDegree d} := by
    rw [hs] at hspos
    push_cast at hspos
    exact pos_of_mul_pos_left hspos hF.le
  have hkey : (#{G : SimpleGraph (Fin n) | G.IsRegularOfDegree d ∧ G.IsEdgeExpander ε} : ℝ)
        / #{G : SimpleGraph (Fin n) | G.IsRegularOfDegree d}
      = 1 - (#{π ∈ simplePairings n d | IsBad ε π} : ℝ) / #(simplePairings n d) := by
    rw [hs, hsb, ← hsplit]
    rw [← hsplit] at hr
    push_cast at hr ⊢
    field_simp
    ring
  rw [hkey]
  exact sub_le_sub_left (div_le_div_of_nonneg_right (by exact_mod_cast hle) hspos.le) 1

open Classical in
/-- **The reduction.** Suppose that, for large `n` with `n * d` even, at least a proportion
`c > 0` of the pairings is simple, and that the proportion of `ε`-bad pairings tends to `0`.
Then the proportion of `d`-regular graphs on `n` vertices that are `ε`-edge-expanders tends
to `1`. -/
theorem tendsto_card_regular_isEdgeExpander_div {d : ℕ} {ε c : ℝ} (hc : 0 < c) {N : ℕ}
    (hsimple : ∀ n ≥ N, Even (n * d) → c * #(pairings n d) ≤ #(simplePairings n d))
    (hbad : Tendsto (fun n => (#(badPairings n d ε) : ℝ) / #(pairings n d))
      (atTop ⊓ 𝓟 {n | Even (n * d)}) (𝓝 0)) :
    Tendsto (fun n =>
        (#{G : SimpleGraph (Fin n) | G.IsRegularOfDegree d ∧ G.IsEdgeExpander ε} : ℝ)
          / #{G : SimpleGraph (Fin n) | G.IsRegularOfDegree d})
      (atTop ⊓ 𝓟 {n | Even (n * d)}) (𝓝 1) := by
  have hlow : Tendsto (fun n => 1 - c⁻¹ * ((#(badPairings n d ε) : ℝ) / #(pairings n d)))
      (atTop ⊓ 𝓟 {n | Even (n * d)}) (𝓝 1) := by
    simpa using tendsto_const_nhds (x := (1 : ℝ)) |>.sub (hbad.const_mul c⁻¹)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · rw [eventually_inf_principal]
    filter_upwards [eventually_ge_atTop N] with n hn heven
    have hP : (0 : ℝ) < #(pairings n d) := by exact_mod_cast (pairings_nonempty heven).card_pos
    have hcP : 0 < c * #(pairings n d) := mul_pos hc hP
    have hS : (0 : ℝ) < #(simplePairings n d) := hcP.trans_le (hsimple n hn heven)
    have hne : (simplePairings n d).Nonempty := card_pos.mp (by exact_mod_cast hS)
    refine le_trans (sub_le_sub_left ?_ 1) (one_sub_card_badPairings_div_le n d ε hne)
    calc (#(badPairings n d ε) : ℝ) / #(simplePairings n d)
        ≤ #(badPairings n d ε) / (c * #(pairings n d)) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) hcP (hsimple n hn heven)
      _ = c⁻¹ * ((#(badPairings n d ε) : ℝ) / #(pairings n d)) := by
          field_simp
  · refine Eventually.of_forall fun n => div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
    have hsub : ({G : SimpleGraph (Fin n) | G.IsRegularOfDegree d ∧ G.IsEdgeExpander ε} :
        Finset (SimpleGraph (Fin n))) ⊆
          ({G : SimpleGraph (Fin n) | G.IsRegularOfDegree d} : Finset (SimpleGraph (Fin n))) :=
      fun G hG => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hG).2.1⟩
    exact_mod_cast card_le_card hsub

end ConfigurationModel
