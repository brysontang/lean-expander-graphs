/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.TwoSided
import Expanders.Cheeger
import Expanders.Hypercube
import Expanders.AlonBoppana

/-!
# Connectivity, bipartiteness and the two ends of the spectrum

For a `d`-regular graph `G` on `n` vertices with adjacency eigenvalues
`d = λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ ≥ −d`, the two extreme eigenvalues detect two combinatorial properties:

* `λ₂ < d` exactly when `G` is connected;
* `λₙ = −d` exactly when some connected component of `G` is bipartite; for a connected graph,
  exactly when `G` is bipartite.

Consequently the two-sided parameter `λ(G) = max(|λ₂|, |λₙ|)` of `Expanders/TwoSided.lean` is
strictly below `d` exactly when `G` is connected and not bipartite. The smallest eigenvalue
`smallestAdjEigenvalue` and the two-sided parameter `twoSidedAdjEigenvalue` are the ones defined
in `Expanders/TwoSided.lean`.

## Definitions
This file introduces no public definitions. (A private parity function on bit strings is used to
2-colour the hypercube.)

## Theorems (all proved here)
Cheeger constant and connectivity, for every finite simple graph (no regularity):
* `two_div_card_le_edgeExpansion`: a connected graph on `n ≥ 2` vertices has `h(G) ≥ 2/n`.
* `edgeExpansion_pos_iff_connected`: on `n ≥ 2` vertices, `h(G) > 0` iff `G` is connected.

The second eigenvalue, for a `d`-regular graph on `n ≥ 2` vertices:
* `secondAdjEigenvalue_lt_iff_connected`: `λ₂ < d ↔ G` connected. The proof goes through the two
  directions of Cheeger's inequality (`Expanders/Cheeger.lean`) and the bound above.
* `spectralGap_pos_iff_connected`: the same as `0 < d − λ₂`.
* `two_le_degree_mul_card_sq_mul_spectralGap`: a quantitative form, `d n² (d − λ₂) ≥ 2` for a
  connected graph (valid but weak; by Abdi and Ghorbani the least possible `d − λ₂` is of order
  `d / n²`).

The smallest eigenvalue, for a `d`-regular graph on `n ≥ 1` vertices:
* `sum_adj_add_sq_div_two`: the signless Laplacian form
  `½ Σ_{u ~ v} (x_u + x_v)² = d · xᵀx + xᵀAx` (ordered adjacent pairs).
* `neg_degree_le_smallestAdjEigenvalue`: `−d ≤ λₙ`.
* `smallestAdjEigenvalue_eq_neg_of_isBipartite`: a bipartite graph has `λₙ = −d`.
* `isBipartite_of_smallestAdjEigenvalue_eq_neg`, `smallestAdjEigenvalue_eq_neg_iff`: a connected
  graph with `λₙ = −d` is bipartite, so for connected graphs `λₙ = −d ↔ G` bipartite.
* `smallestAdjEigenvalue_eq_neg_iff_exists_isBipartite`: without connectivity,
  `λₙ = −d ↔` some connected component is bipartite.

The two-sided parameter, for a `d`-regular graph on `n ≥ 2` vertices:
* `twoSidedAdjEigenvalue_lt_iff`: `λ(G) < d ↔ G` is connected and not bipartite.
* `twoSidedAdjEigenvalue_eq_degree_iff`: `λ(G) = d ↔ G` is disconnected or bipartite.

Examples and corollaries:
* `hypercube_isBipartite`, `hypercube_connected`: the cube `Qₘ` is bipartite and connected.
  `hypercube_smallestAdjEigenvalue`: `λₙ(Qₘ) = −m`; `hypercube_twoSidedAdjEigenvalue`:
  `λ(Q_{m+1}) = m + 1`.
* `IsRamanujan.twoSidedAdjEigenvalue_le`: a non-bipartite Ramanujan graph has
  `λ(G) ≤ 2√(d − 1)`; `isRamanujan_iff_of_not_isBipartite`: for a non-bipartite graph, being
  Ramanujan (in the project's bipartite convention, `IsRamanujan`) is the same as being connected
  and an `(n, d, 2√(d − 1))`-graph (`IsTwoSidedSpectralExpander`).

## References
* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Springer (2012), Section 3.1: for a
  `k`-regular graph the multiplicity of `k` is the number of components, and `−k` is an eigenvalue
  iff some component is bipartite.
* C. Godsil and G. Royle, *Algebraic Graph Theory*, Springer (2001), Chapter 8.
* F. R. K. Chung, *Spectral Graph Theory*, AMS (1997), Lemma 1.7 (the normalized Laplacian
  version).
* S. Hoory, N. Linial and A. Wigderson, *Expander graphs and their applications*,
  Bull. AMS 43 (2006), 439–561, Section 2.
* B. Mohar, *Eigenvalues, diameter, and mean distance in graphs*, Graphs Combin. 7 (1991),
  53–64: the much stronger bound `d − λ₂ ≥ 4/(n · diam G)`.
* M. Abdi and E. Ghorbani, *Minimum algebraic connectivity and maximum diameter: Aldous–Fill and
  Guiduli–Mohar conjectures*, arXiv:2212.03571: the least spectral gap of a connected `d`-regular
  graph on `n` vertices is of order `d / n²`.
-/

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The Cheeger constant and connectivity -/

/-- A connected graph on `n ≥ 2` vertices has Cheeger constant `h(G) ≥ 2/n`: every admissible
set `S` (nonempty, `|S| ≤ n/2`) has at least one boundary edge, and `1 ≥ 2|S|/n`.

No regularity is assumed. `Nontrivial V` cannot be dropped: on one vertex the graph is connected
but `edgeExpansion` takes the junk value `0` (there is no admissible `S`), while `2/1 = 2`. The
bound is attained exactly when some set of `n/2` vertices has a single boundary edge, for
instance by a path on an even number of vertices. -/
theorem two_div_card_le_edgeExpansion [Nontrivial V] (h : G.Connected) :
    2 / (Fintype.card V : ℝ) ≤ G.edgeExpansion := by
  refine IsEdgeExpander.le_edgeExpansion fun S hS => ?_
  rcases S.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
  · simp
  obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
    by_contra hcon
    push Not at hcon
    have hS' : S = univ := eq_univ_of_forall hcon
    rw [hS', card_univ] at hS
    have := Fintype.card_pos (α := V)
    omega
  obtain ⟨p⟩ := h u v
  obtain ⟨e, -, he1, he2⟩ := p.exists_boundary_dart (S : Set V) hu hv
  have hmem : (e.fst, e.snd) ∈ G.edgeBoundary S :=
    mem_edgeBoundary.mpr ⟨he1, he2, e.adj⟩
  have hb : (1 : ℝ) ≤ #(G.edgeBoundary S) := by exact_mod_cast card_pos.mpr ⟨_, hmem⟩
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hS' : (2 * #S : ℝ) ≤ Fintype.card V := by exact_mod_cast hS
  calc 2 / (Fintype.card V : ℝ) * #S = 2 * #S / Fintype.card V := by ring
    _ ≤ 1 := (div_le_one hn).mpr hS'
    _ ≤ _ := hb

/-- A graph on `n ≥ 2` vertices has positive Cheeger constant exactly when it is connected.

No regularity is assumed. `Nontrivial V` is needed to rule out a single vertex, where the graph
is connected while `edgeExpansion` is the junk value `0`. -/
theorem edgeExpansion_pos_iff_connected [Nontrivial V] :
    0 < G.edgeExpansion ↔ G.Connected := by
  refine ⟨fun hpos => ?_, fun h =>
    lt_of_lt_of_le (by have := Fintype.card_pos (α := V); positivity)
      (two_div_card_le_edgeExpansion h)⟩
  by_contra hc
  have hpre : ¬ G.Preconnected := fun hp => hc ⟨hp⟩
  simp only [Preconnected, not_forall] at hpre
  obtain ⟨u, v, huv⟩ := hpre
  set C : Finset V := {w | G.Reachable u w} with hC
  have hu : u ∈ C := by simp [C]
  have hv : v ∉ C := by simpa [C] using huv
  have hbd : G.edgeBoundary C = ∅ := by
    ext ⟨a, b⟩
    simp only [mem_edgeBoundary, C, mem_filter, mem_univ, true_and]
    simp only [Finset.notMem_empty, iff_false, not_and]
    intro ha hb hab
    exact hb (ha.trans hab.reachable)
  have hle : G.edgeExpansion ≤ 0 := by
    by_cases h2 : 2 * #C ≤ Fintype.card V
    · have := G.edgeExpansion_le ⟨u, hu⟩ h2
      rwa [hbd, card_empty, Nat.cast_zero, zero_div] at this
    · have hcu := card_le_univ C
      have h2' : 2 * #Cᶜ ≤ Fintype.card V := by rw [card_compl]; omega
      have := G.edgeExpansion_le ⟨v, mem_compl.mpr hv⟩ h2'
      rwa [card_edgeBoundary_compl, hbd, card_empty, Nat.cast_zero, zero_div] at this
  linarith

/-! ### The second eigenvalue and connectivity -/

/-- **`λ₂ < d` iff connected.** A `d`-regular graph on `n ≥ 2` vertices has second adjacency
eigenvalue `λ₂ < d` exactly when it is connected (equivalently, the eigenvalue `d` is simple).

The proof uses Cheeger's inequality in both directions: `(d − λ₂)/2 ≤ h(G)` and
`h(G) ≤ √(2d(d − λ₂))`, together with `edgeExpansion_pos_iff_connected`. Edge cases: for `d = 0`
the graph is edgeless, hence disconnected (it has `n ≥ 2` vertices), and `λ₂ = 0 = d`; for
`d = 1` the graph is a perfect matching, connected only when it is `K₂`, where `λ₂ = −1`.
`Nontrivial V` is needed for `λ₂` to be defined. -/
theorem secondAdjEigenvalue_lt_iff_connected [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    G.secondAdjEigenvalue < d ↔ G.Connected := by
  constructor
  · intro h
    rw [← edgeExpansion_pos_iff_connected]
    have := spectralGap_div_two_le_edgeExpansion hd
    rw [spectralGap_eq hd] at this
    linarith
  · intro h
    have h1 := two_div_card_le_edgeExpansion h
    have h2 := edgeExpansion_le_sqrt hd
    have hn : (0 : ℝ) < 2 / Fintype.card V := by
      have := Fintype.card_pos (α := V); positivity
    have h3 : 0 < Real.sqrt (2 * d * G.spectralGap) := by linarith
    rw [Real.sqrt_pos, spectralGap_eq hd] at h3
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    by_contra hc
    push Not at hc
    nlinarith

/-- A `d`-regular graph on `n ≥ 2` vertices has a positive spectral gap `d − λ₂` exactly when it
is connected. This is `secondAdjEigenvalue_lt_iff_connected` restated with `spectralGap`. -/
theorem spectralGap_pos_iff_connected [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    0 < G.spectralGap ↔ G.Connected := by
  rw [spectralGap_eq hd, sub_pos]
  exact secondAdjEigenvalue_lt_iff_connected hd

/-- A quantitative spectral gap for connected regular graphs: a connected `d`-regular graph on
`n ≥ 2` vertices satisfies `d · n² · (d − λ₂) ≥ 2`, i.e. `d − λ₂ ≥ 2/(d n²)`.

It combines `h(G) ≥ 2/n` with the hard direction of Cheeger's inequality, `h(G)² ≤ 2d(d − λ₂)`.
The constant is not sharp (for `K₂`, `d n² (d − λ₂) = 8`) and the bound is weak in general:
Mohar's bound gives `d − λ₂ ≥ 4/(n(n − 1))`. A connected regular graph on `n ≥ 2` vertices has
`d ≥ 1`, so the factor `d` is never `0` here and the division in `2/(d n²)` is genuine. -/
theorem two_le_degree_mul_card_sq_mul_spectralGap [Nontrivial V] (hd : G.IsRegularOfDegree d)
    (h : G.Connected) : (2 : ℝ) ≤ d * Fintype.card V ^ 2 * G.spectralGap := by
  have h1 := two_div_card_le_edgeExpansion h
  have h2 := edgeExpansion_le_sqrt hd
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hg := G.spectralGap_nonneg
  have hsq : (2 / (Fintype.card V : ℝ)) ^ 2 ≤ 2 * d * G.spectralGap := by
    have h0 : 0 ≤ 2 / (Fintype.card V : ℝ) := by positivity
    calc (2 / (Fintype.card V : ℝ)) ^ 2 ≤ Real.sqrt (2 * d * G.spectralGap) ^ 2 :=
          pow_le_pow_left₀ h0 (h1.trans h2) 2
      _ = 2 * d * G.spectralGap := Real.sq_sqrt (by positivity)
  rw [div_pow, div_le_iff₀ (by positivity)] at hsq
  nlinarith

/-! ### The smallest eigenvalue and bipartiteness -/

omit [DecidableEq V] in
/-- The **signless Laplacian form** of a `d`-regular graph:
`½ Σ_{u ~ v} (x_u + x_v)² = d · xᵀx + xᵀAx`. The sum runs over ordered adjacent pairs, so each
edge is counted twice before halving. Valid for every `d`, including `d = 0` (both sides are
`0`) and the empty vertex type. -/
theorem sum_adj_add_sq_div_two (hd : G.IsRegularOfDegree d) (x : V → ℝ) :
    (∑ u, ∑ v, if G.Adj u v then (x u + x v) ^ 2 else 0) / 2
      = d * (x ⬝ᵥ x) + x ⬝ᵥ G.adjMatrix ℝ *ᵥ x := by
  classical
  have hsub := sum_adj_sub_sq_div_two hd x
  have hl : (∑ u, ∑ v, if G.Adj u v then x u ^ 2 else 0) = d * ∑ u, x u ^ 2 :=
    sum_adj_left hd _
  have hr : (∑ u, ∑ v, if G.Adj u v then x v ^ 2 else 0) = d * ∑ u, x u ^ 2 :=
    sum_adj_right hd (fun u => x u ^ 2)
  have hxx : ∑ u, x u ^ 2 = x ⬝ᵥ x := by simp [dotProduct, sq]
  have key : ∀ u v, (if G.Adj u v then (x u + x v) ^ 2 else 0)
      = 2 * (if G.Adj u v then x u ^ 2 else 0) + 2 * (if G.Adj u v then x v ^ 2 else 0)
        - (if G.Adj u v then (x u - x v) ^ 2 else 0) := by
    intro u v; split_ifs <;> ring
  simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hl, hr, hxx] at *
  linarith

/-- In a `d`-regular graph on a nonempty vertex type, `λₙ ≥ −d`: every adjacency eigenvalue lies
in `[−d, d]`. For `d = 0` this reads `0 ≤ λₙ`, and indeed `λₙ = 0` there. -/
theorem neg_degree_le_smallestAdjEigenvalue [Nonempty V] (hd : G.IsRegularOfDegree d) :
    -(d : ℝ) ≤ G.smallestAdjEigenvalue := by
  obtain ⟨w, hw, hAw⟩ := (G.isHermitian_adjMatrix ℝ).exists_eigenvector_smallest
  exact (abs_le.mp (abs_le_of_adjMatrix_mulVec_eq hd hw hAw)).1

/-- The `±1` value attached to a colour in `Fin 2`; distinct colours get opposite values. -/
private theorem sign_fin_two_eq_neg {a b : Fin 2} (h : a ≠ b) :
    (if b = 0 then (1 : ℝ) else -1) = -(if a = 0 then (1 : ℝ) else -1) := by
  fin_cases a <;> fin_cases b <;> simp_all

/-- **A bipartite regular graph has `λₙ = −d`.** If `G` is `d`-regular and bipartite on a
nonempty vertex type then its smallest adjacency eigenvalue is `−d`: the vector that is `+1` on
one side and `−1` on the other is an eigenvector for `−d`.

Connectivity is not needed. For `d = 0` (an edgeless graph, which is bipartite) this reads
`λₙ = 0`. -/
theorem smallestAdjEigenvalue_eq_neg_of_isBipartite [Nonempty V] (hd : G.IsRegularOfDegree d)
    (hb : G.IsBipartite) : G.smallestAdjEigenvalue = -d := by
  obtain ⟨c⟩ := hb
  set f : V → ℝ := fun v => if c v = 0 then 1 else -1 with hf
  have hAf : G.adjMatrix ℝ *ᵥ f = (-(d : ℝ)) • f := by
    ext v
    rw [adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun u hu =>
      sign_fin_two_eq_neg (c.valid (by simpa using hu))]
    rw [Finset.sum_const, card_neighborFinset_eq_degree, hd v, nsmul_eq_mul]
    ring
  have hf0 : f ≠ 0 := by
    intro h0
    have := congrFun h0 (Classical.arbitrary V)
    simp only [f, Pi.zero_apply] at this
    split_ifs at this <;> norm_num at this
  exact le_antisymm ((G.isHermitian_adjMatrix ℝ).smallest_le_of_mulVec_eq hf0 hAf)
    (neg_degree_le_smallestAdjEigenvalue hd)

omit [DecidableEq V] in
/-- An eigenvector for `−d` of a `d`-regular graph takes opposite values at the two ends of every
edge (the signless Laplacian form vanishes on it). -/
private theorem eq_neg_of_adj_of_mulVec_eq_neg (hd : G.IsRegularOfDegree d) {f : V → ℝ}
    (hAf : G.adjMatrix ℝ *ᵥ f = (-(d : ℝ)) • f) {u v : V} (huv : G.Adj u v) : f v = -f u := by
  have hsum := sum_adj_add_sq_div_two hd f
  rw [hAf, dotProduct_smul, smul_eq_mul] at hsum
  have hzero : (∑ u, ∑ v, if G.Adj u v then (f u + f v) ^ 2 else 0) = 0 := by linarith
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ =>
    Finset.sum_nonneg fun v _ => by split_ifs <;> positivity)).mp hzero u (mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => by
    split_ifs <;> positivity)).mp h1 v (mem_univ _)
  rw [if_pos huv] at h2
  have : f u + f v = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  linarith

/-- If `f` takes opposite values at the ends of every edge, `|f|` is constant along walks. -/
private theorem abs_eq_abs_of_reachable {W : Type*} {H : SimpleGraph W} {f : W → ℝ}
    (hedge : ∀ u v, H.Adj u v → f v = -f u) {u v : W} (h : H.Reachable u v) : |f u| = |f v| := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons ha _ ih => rw [← ih, hedge _ _ ha, abs_neg]

/-- A graph carrying a nowhere-zero function that takes opposite values at the ends of every edge
is bipartite: colour each vertex by the sign of the function. -/
private theorem isBipartite_of_forall_ne_zero {W : Type*} {H : SimpleGraph W} {f : W → ℝ}
    (hne : ∀ v, f v ≠ 0) (hedge : ∀ u v, H.Adj u v → f v = -f u) : H.IsBipartite := by
  refine ⟨Coloring.mk (fun v => if 0 < f v then (0 : Fin 2) else 1) ?_⟩
  intro u v huv
  have h1 := hedge u v huv
  have h2 := hne u
  by_cases hu : 0 < f u
  · have : ¬ 0 < f v := by rw [h1]; linarith
    simp [hu, this]
  · have : 0 < f v := by
      rw [h1]; have := lt_of_le_of_ne (not_lt.mp hu) h2; linarith
    simp [hu, this]

/-- **A connected regular graph with `λₙ = −d` is bipartite.** Take an eigenvector `f` for
`−d`. The signless Laplacian form `½ Σ_{u ~ v} (f_u + f_v)² = d · fᵀf + fᵀAf` vanishes, so `f`
changes sign across every edge; by connectivity `|f|` is a nonzero constant, and the sign of `f`
is a proper 2-colouring.

Connectivity cannot be dropped: the disjoint union of `K₄` and `K_{3,3}` is `3`-regular with
`λₙ = −3` but contains a triangle (see `smallestAdjEigenvalue_eq_neg_iff_exists_isBipartite`
for the general statement). For `d = 0` a connected graph is a single vertex, which is
bipartite. -/
theorem isBipartite_of_smallestAdjEigenvalue_eq_neg [Nonempty V] (hd : G.IsRegularOfDegree d)
    (hc : G.Connected) (h : G.smallestAdjEigenvalue = -d) : G.IsBipartite := by
  obtain ⟨f, hf, hAf⟩ := (G.isHermitian_adjMatrix ℝ).exists_eigenvector_smallest
  change G.adjMatrix ℝ *ᵥ f = G.smallestAdjEigenvalue • f at hAf
  rw [h] at hAf
  have hedge := fun u v (huv : G.Adj u v) => eq_neg_of_adj_of_mulVec_eq_neg hd hAf huv
  obtain ⟨v₀, hv₀⟩ := Function.ne_iff.mp hf
  refine isBipartite_of_forall_ne_zero (f := f) (fun v hv => hv₀ ?_) hedge
  have := abs_eq_abs_of_reachable hedge (hc v₀ v)
  rwa [hv, abs_zero, abs_eq_zero] at this

/-- **`λₙ = −d` iff bipartite**, for connected graphs: a connected `d`-regular graph has smallest
adjacency eigenvalue `−d` exactly when it is bipartite.

Connectivity is needed for the forward direction only (the disjoint union of `K₄` and
`K_{3,3}` is a counterexample without it). For `d = 0` both sides hold (a single vertex). -/
theorem smallestAdjEigenvalue_eq_neg_iff [Nonempty V] (hd : G.IsRegularOfDegree d)
    (hc : G.Connected) : G.smallestAdjEigenvalue = -d ↔ G.IsBipartite :=
  ⟨isBipartite_of_smallestAdjEigenvalue_eq_neg hd hc,
    smallestAdjEigenvalue_eq_neg_of_isBipartite hd⟩

/-- **`λₙ = −d` iff some component is bipartite.** A `d`-regular graph on a nonempty vertex type
has smallest adjacency eigenvalue `−d` exactly when one of its connected components (as a graph
on its own vertex set, `ConnectedComponent.toSimpleGraph`) is bipartite.

Forward: an eigenvector for `−d` changes sign across every edge, so on the component of a vertex
where it is nonzero it is nowhere zero, and its sign 2-colours that component. Backward: the
vector that is `±1` on a bipartite component, according to the colour, and `0` elsewhere is an
eigenvector for `−d`. For `d = 0` both sides hold: `λₙ = 0` and every component is a single
vertex. -/
theorem smallestAdjEigenvalue_eq_neg_iff_exists_isBipartite [Nonempty V]
    (hd : G.IsRegularOfDegree d) :
    G.smallestAdjEigenvalue = -d ↔ ∃ C : G.ConnectedComponent, C.toSimpleGraph.IsBipartite := by
  constructor
  · intro h
    obtain ⟨f, hf, hAf⟩ := (G.isHermitian_adjMatrix ℝ).exists_eigenvector_smallest
    change G.adjMatrix ℝ *ᵥ f = G.smallestAdjEigenvalue • f at hAf
    rw [h] at hAf
    have hedge := fun u v (huv : G.Adj u v) => eq_neg_of_adj_of_mulVec_eq_neg hd hAf huv
    obtain ⟨v₀, hv₀⟩ := Function.ne_iff.mp hf
    refine ⟨G.connectedComponentMk v₀, isBipartite_of_forall_ne_zero
      (f := fun w : G.connectedComponentMk v₀ => f w.1) (fun w hw => hv₀ ?_)
      (fun u v huv => hedge u.1 v.1 huv)⟩
    have := abs_eq_abs_of_reachable hedge
      ((G.connectedComponentMk v₀).reachable_of_mem_supp ConnectedComponent.connectedComponentMk_mem
        w.2)
    rwa [hw, abs_zero, abs_eq_zero] at this
  · rintro ⟨C, ⟨c⟩⟩
    let g : V → ℝ := fun v =>
      if hv : v ∈ C.supp then (if c ⟨v, hv⟩ = 0 then 1 else -1) else 0
    have hAg : G.adjMatrix ℝ *ᵥ g = (-(d : ℝ)) • g := by
      ext v
      rw [adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hv : v ∈ C.supp
      · have hterm : ∀ u ∈ G.neighborFinset v, g u = -g v := by
          intro u hu
          have huv : G.Adj v u := by simpa using hu
          have hu' : u ∈ C.supp := C.mem_supp_of_adj_mem_supp hv huv
          have hcol : c ⟨v, hv⟩ ≠ c ⟨u, hu'⟩ := c.valid huv
          simp only [g, dif_pos hv, dif_pos hu']
          exact sign_fin_two_eq_neg hcol
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_neighborFinset_eq_degree, hd v,
          nsmul_eq_mul]
        ring
      · have hterm : ∀ u ∈ G.neighborFinset v, g u = 0 := by
          intro u hu
          have huv : G.Adj u v := (by simpa using hu : G.Adj v u).symm
          have hu' : u ∉ C.supp := fun hu' => hv (C.mem_supp_of_adj_mem_supp hu' huv)
          simp only [g, dif_neg hu']
        rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero]
        simp only [g, dif_neg hv, mul_zero]
    have hg0 : g ≠ 0 := by
      obtain ⟨v, hv⟩ := C.nonempty_supp
      intro h0
      have := congrFun h0 v
      simp only [g, dif_pos hv, Pi.zero_apply] at this
      split_ifs at this <;> norm_num at this
    exact le_antisymm ((G.isHermitian_adjMatrix ℝ).smallest_le_of_mulVec_eq hg0 hAg)
      (neg_degree_le_smallestAdjEigenvalue hd)

/-! ### The two-sided parameter -/

/-- **The two-sided gap.** A `d`-regular graph on `n ≥ 2` vertices has two-sided parameter
`λ(G) = max(|λ₂|, |λₙ|) < d` exactly when it is connected and not bipartite. In that case every
eigenvalue other than the trivial `λ₁ = d` lies in the open interval `(−d, d)`.

Edge cases: `K₂` (`d = 1`) is connected and bipartite, and `λ(K₂) = 1 = d`; for `d = 0` the graph
is disconnected and `λ(G) = 0 = d`, so both sides are false. `Nontrivial V` is needed for `λ₂`
(and hence `λ(G)`) to be defined. -/
theorem twoSidedAdjEigenvalue_lt_iff [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    G.twoSidedAdjEigenvalue < d ↔ G.Connected ∧ ¬ G.IsBipartite := by
  have h1 := neg_degree_le_smallestAdjEigenvalue hd (G := G)
  have h2 := G.smallestAdjEigenvalue_le_secondAdjEigenvalue
  have h3 := secondAdjEigenvalue_le hd (G := G)
  rw [twoSidedAdjEigenvalue, max_lt_iff, abs_lt, abs_lt]
  constructor
  · rintro ⟨⟨-, h4⟩, ⟨h5, -⟩⟩
    refine ⟨(secondAdjEigenvalue_lt_iff_connected hd).mp h4, fun hb => ?_⟩
    rw [smallestAdjEigenvalue_eq_neg_of_isBipartite hd hb] at h5
    exact lt_irrefl _ h5
  · rintro ⟨hc, hb⟩
    have h4 := (secondAdjEigenvalue_lt_iff_connected hd).mpr hc
    have h5 : -(d : ℝ) < G.smallestAdjEigenvalue := lt_of_le_of_ne h1 fun heq =>
      hb (isBipartite_of_smallestAdjEigenvalue_eq_neg hd hc heq.symm)
    exact ⟨⟨by linarith, h4⟩, ⟨h5, by linarith⟩⟩

/-- A `d`-regular graph on `n ≥ 2` vertices has `λ(G) = d` exactly when it is disconnected or
bipartite (since always `λ(G) ≤ d`, by `twoSidedAdjEigenvalue_le_degree`). This includes `d = 0`
(edgeless, hence disconnected, with `λ(G) = 0`) and `K₂` (bipartite, with `λ(K₂) = 1`). -/
theorem twoSidedAdjEigenvalue_eq_degree_iff [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    G.twoSidedAdjEigenvalue = d ↔ ¬ G.Connected ∨ G.IsBipartite := by
  have hle := twoSidedAdjEigenvalue_le_degree hd (G := G)
  have hiff := twoSidedAdjEigenvalue_lt_iff hd (G := G)
  constructor
  · intro h
    by_contra hcon
    simp only [not_or, not_not] at hcon
    have := hiff.mpr hcon
    rw [h] at this
    exact lt_irrefl _ this
  · intro h
    refine le_antisymm hle (not_lt.mp fun hlt => ?_)
    obtain ⟨hc, hb⟩ := hiff.mp hlt
    rcases h with h | h
    · exact h hc
    · exact hb h

/-! ### The hypercube -/

/-- The parity of the number of `true` bits of a string. -/
private def hypercubeParity {n : ℕ} (u : Fin n → Bool) : ZMod 2 := ∑ i, if u i then 1 else 0

private theorem hypercubeParity_bitFlip {n : ℕ} (u : Fin n → Bool) (i : Fin n) :
    hypercubeParity (hypercube.bitFlip u i) = hypercubeParity u + 1 := by
  unfold hypercubeParity
  rw [← Finset.add_sum_erase _ _ (mem_univ i), ← Finset.add_sum_erase _ _ (mem_univ i)]
  rw [Finset.sum_congr rfl fun j hj => by
    rw [hypercube.bitFlip_apply_of_ne u (Finset.ne_of_mem_erase hj)]]
  rw [hypercube.bitFlip_apply_self]
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  cases u i
  · simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false, zero_add]
    ring
  · simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true, zero_add]
    rw [add_comm (1 : ZMod 2), add_assoc, h2, add_zero]

/-- The hypercube `Qₘ` is bipartite: colour a bit string by the parity of its number of `1`s.
Flipping one bit changes the parity. This includes `m = 0` (one vertex, no edges). -/
theorem hypercube_isBipartite (m : ℕ) : (hypercube m).IsBipartite := by
  have c : (hypercube m).Coloring (ZMod 2) := Coloring.mk hypercubeParity fun {u v} h => by
    obtain ⟨i, rfl⟩ := hypercube.adj_iff.mp h
    rw [hypercubeParity_bitFlip]
    intro h'
    have h1 : (1 : ZMod 2) = 0 := by
      have := congrArg (· - hypercubeParity u) h'
      simpa using this.symm
    exact absurd h1 (by decide)
  simpa using c.colorable

/-- The hypercube `Qₘ` is connected. For `m = 0` it is a single vertex; for `m ≥ 1` this follows
from its spectral gap `2 > 0` (`hypercube_spectralGap`) and `spectralGap_pos_iff_connected`. -/
theorem hypercube_connected (m : ℕ) : (hypercube m).Connected := by
  cases m with
  | zero => exact Connected.mk fun u v => Subsingleton.elim u v ▸ Reachable.refl u
  | succ m =>
    rw [← spectralGap_pos_iff_connected (hypercube_isRegularOfDegree (m + 1)),
      hypercube_spectralGap]
    norm_num

/-- The smallest adjacency eigenvalue of the hypercube `Qₘ` is `−m`, since `Qₘ` is `m`-regular
and bipartite. For `m = 0` (one vertex) it is `0`. -/
theorem hypercube_smallestAdjEigenvalue (m : ℕ) :
    (hypercube m).smallestAdjEigenvalue = -m :=
  smallestAdjEigenvalue_eq_neg_of_isBipartite (hypercube_isRegularOfDegree m)
    (hypercube_isBipartite m)

/-- The two-sided parameter of the cube `Q_{m+1}` is `m + 1 = d`: the cube is a one-sided
expander (spectral gap `2`) but not a two-sided one, because it is bipartite. (`Q₀` has a single
vertex, where `λ(G)` is not defined.) -/
theorem hypercube_twoSidedAdjEigenvalue (m : ℕ) :
    (hypercube (m + 1)).twoSidedAdjEigenvalue = m + 1 := by
  rw [(twoSidedAdjEigenvalue_eq_degree_iff (hypercube_isRegularOfDegree (m + 1))).mpr
    (Or.inr (hypercube_isBipartite (m + 1)))]
  push_cast
  rfl

/-! ### Ramanujan graphs -/

/-- A **non-bipartite Ramanujan graph** has two-sided parameter `λ(G) ≤ 2√(d − 1)`, i.e. it is
Ramanujan also in the strict convention.

`IsRamanujan` (the bipartite convention) exempts the eigenvalues `±d`; for a connected
non-bipartite graph the only exempt eigenvalue is `λ₁ = d`, because `λ₂ < d` and `λₙ > −d`
(`twoSidedAdjEigenvalue_lt_iff`). Degenerate cases: `d = 0` is impossible (a connected
`0`-regular graph has one vertex, excluded by `Nontrivial V`), so the real subtraction `d − 1`
never goes negative and `Real.sqrt` never sees a negative argument here; for `d = 1` the only
connected `1`-regular graph is `K₂`, which is bipartite, so the statement is vacuous (and
`√(1 − 1) = 0`). -/
theorem IsRamanujan.twoSidedAdjEigenvalue_le [Nontrivial V] (h : G.IsRamanujan d)
    (hb : ¬ G.IsBipartite) : G.twoSidedAdjEigenvalue ≤ 2 * Real.sqrt (d - 1) := by
  obtain ⟨hc, hd, hram⟩ := h
  have hlt := (twoSidedAdjEigenvalue_lt_iff hd).mpr ⟨hc, hb⟩
  rw [twoSidedAdjEigenvalue, max_lt_iff] at hlt
  rw [twoSidedAdjEigenvalue]
  refine max_le ?_ ?_
  · rcases hram ⟨1, Fintype.one_lt_card⟩ with h1 | h1
    · rw [← secondAdjEigenvalue_eq_adjEigenvalues] at h1
      linarith [hlt.1]
    · rwa [← secondAdjEigenvalue_eq_adjEigenvalues] at h1
  · rcases hram ⟨Fintype.card V - 1, Nat.sub_lt Fintype.card_pos Nat.one_pos⟩ with h1 | h1
    · rw [← smallestAdjEigenvalue_eq_adjEigenvalues] at h1
      linarith [hlt.2]
    · rwa [← smallestAdjEigenvalue_eq_adjEigenvalues] at h1

/-- A connected `d`-regular graph on `n ≥ 2` vertices with `λ(G) ≤ 2√(d − 1)` is Ramanujan: every
eigenvalue other than `λ₁ = d` lies in `[λₙ, λ₂]`, so its absolute value is at most `λ(G)`.
Bipartiteness plays no role here. For `d = 0` the hypotheses are contradictory (on `n ≥ 2`
vertices `d = 0` forces disconnection), so the junk value `√(0 − 1) = √(−1) = 0` never matters;
for `d = 1`, `√(1 − 1) = 0` and the hypothesis `λ(G) ≤ 0` fails for `K₂`, the only connected
`1`-regular graph. -/
theorem isRamanujan_of_twoSidedAdjEigenvalue_le [Nontrivial V] (hc : G.Connected)
    (hd : G.IsRegularOfDegree d) (h : G.twoSidedAdjEigenvalue ≤ 2 * Real.sqrt (d - 1)) :
    G.IsRamanujan d := by
  refine ⟨hc, hd, fun i => ?_⟩
  rcases Nat.eq_zero_or_pos i.1 with hi | hi
  · left
    have hi' : i = ⟨0, Fintype.card_pos⟩ := Fin.ext hi
    rw [hi', ← largestAdjEigenvalue_eq_adjEigenvalues, largestAdjEigenvalue_eq hd,
      abs_of_nonneg (Nat.cast_nonneg d)]
  · right
    have hle2 : G.adjEigenvalues i ≤ G.secondAdjEigenvalue := by
      rw [secondAdjEigenvalue_eq_adjEigenvalues]
      exact G.adjEigenvalues_antitone (Fin.mk_le_mk.mpr hi)
    have hgen : G.smallestAdjEigenvalue ≤ G.adjEigenvalues i := by
      rw [smallestAdjEigenvalue_eq_adjEigenvalues]
      exact G.adjEigenvalues_antitone (Fin.mk_le_mk.mpr (Nat.le_sub_one_of_lt i.2))
    exact (abs_le_max_abs_abs hgen hle2).trans ((max_comm _ _).le.trans h)

/-- For a **non-bipartite** graph on `n ≥ 2` vertices, being Ramanujan (`IsRamanujan`, the
bipartite convention, which exempts `±d`) is the same as being connected and an
`(n, d, 2√(d − 1))`-graph (`IsTwoSidedSpectralExpander`, the strict convention).

Without `¬ G.IsBipartite` only the backward direction holds: a bipartite Ramanujan graph has
`λₙ = −d`, so `λ(G) = d`, which exceeds `2√(d − 1)` for every `d ≠ 2` (for example `K₂`, where
`√(1 − 1) = 0`, and `K_{3,3}`). For `d = 0` and `d = 1` both sides are false
(see `IsRamanujan.twoSidedAdjEigenvalue_le`). -/
theorem isRamanujan_iff_of_not_isBipartite [Nontrivial V] (hb : ¬ G.IsBipartite) :
    G.IsRamanujan d ↔
      G.Connected ∧ G.IsTwoSidedSpectralExpander d (2 * Real.sqrt (d - 1)) :=
  ⟨fun h => ⟨h.1, h.2.1, h.twoSidedAdjEigenvalue_le hb⟩,
    fun h => isRamanujan_of_twoSidedAdjEigenvalue_le h.1 h.2.1 h.2.2⟩

end SimpleGraph
