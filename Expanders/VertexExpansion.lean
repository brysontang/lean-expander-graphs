/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.TwoSided
import Expanders.Hypercube

/-!
# Vertex expansion: Tanner's spectral bound and vertex versus edge expansion

For a vertex set `S` of a graph `G`, the (open) **neighbourhood** `N(S)` is the set of vertices
adjacent to some vertex of `S`, and the **vertex boundary** is `N(S) \ S`. This file relates these
to the edge boundary `∂S` of `Expanders/Basic.lean` and to the adjacency spectrum.

For a `d`-regular graph on `n` vertices with eigenvalues `d = λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ`, two-sided
parameter `λ(G) = max(|λ₂|, |λₙ|)` (`Expanders/TwoSided.lean`) and `s = |S|`, **Tanner's bound**
reads

  `n d² s ≤ |N(S)| · (d² s + λ(G)² (n − s))`,

i.e. `|N(S)| ≥ d² s / (d² s/n + λ(G)²(1 − s/n))` whenever that denominator is nonzero. It is
stated multiplicatively here, so no division is ever performed. Replacing the adjacency matrix
`A` by `A + c I` for a real shift `c` gives the **shifted bound**

  `n (d + c)² s ≤ |S ∪ N(S)| · ((d + c)² s + μ_c² (n − s))`, `μ_c = max(|λ₂ + c|, |λₙ + c|)`,

for the *closed* neighbourhood `S ∪ N(S)`. For the open neighbourhood and `c ≠ 0` it can fail
(already for `K₂`, `c = 1/2`, `S` a single vertex). With `c = d` one has `μ_d = d + λ₂`, so the
bound only involves `λ₂`; this is the "lazy walk" trick that makes Tanner's bound useful for
bipartite graphs, where `λₙ = −d` and `λ(G) = d`.

## Definitions
* `SimpleGraph.neighborhood S`: the open neighbourhood `N(S) = {v | ∃ u ∈ S, u ~ v}`.
* `SimpleGraph.vertexBoundary S`: the vertex boundary `N(S) \ S`.
* `SimpleGraph.IsVertexExpander ε`: every `S` with `|S| ≤ n/2` has `|N(S) \ S| ≥ ε |S|`.

## Theorems (all proved here)
Vertex versus edge expansion (no spectral input):
* `card_vertexBoundary_le_card_edgeBoundary`: `|N(S) \ S| ≤ |∂S|`, for every graph.
* `card_edgeBoundary_le_mul_card_vertexBoundary`: `|∂S| ≤ d |N(S) \ S|` when every degree is at
  most `d`.
* `IsVertexExpander.isEdgeExpander`, `IsEdgeExpander.mul_card_le_card_vertexBoundary`,
  `IsEdgeExpander.isVertexExpander`: an `ε`-vertex-expander is an `ε`-edge-expander, and an
  `ε`-edge-expander of maximum degree at most `d` is an `ε/d`-vertex-expander.
* `degree_sub_secondAdjEigenvalue_mul_card_le_card_vertexBoundary`,
  `isVertexExpander_degree_sub_secondAdjEigenvalue`: the Cheeger-type bound
  `(d − λ₂) |S| ≤ 2d |N(S) \ S|` for `|S| ≤ n/2` in a `d`-regular graph (easy Cheeger
  inequality plus the previous item).

Spectral bounds, for a `d`-regular graph on `n ≥ 2` vertices:
* `dotProduct_self_adjMatrix_mulVec_add_smul_le`: `‖(A + cI)x‖² ≤ μ_c² ‖x‖²` for `x ⟂ 𝟙`.
* `tanner_of_support_subset`: the core estimate, for any set `T` containing the support of
  `(A + cI) 1_S`.
* `tanner`: **Tanner's bound** for the open neighbourhood, in terms of `λ(G)`.
* `tanner_shift`: the shifted bound for the closed neighbourhood, for every real `c`.
* `tanner_secondAdjEigenvalue`: the case `c = d`, in terms of `λ₂` only.
* `hypercube_tanner`: the case `c = d` on the hypercube `Q_{n+1}`, where `d + λ₂ = 2n`.

## References
* R. M. Tanner, *Explicit concentrators from generalized N-gons*, SIAM J. Algebraic Discrete
  Methods 5 (1984), 287–293.
* S. Hoory, N. Linial and A. Wigderson, *Expander graphs and their applications*, Bull. AMS 43
  (2006), Theorem 4.15 (Tanner's bound, with the same eigenbasis and Cauchy–Schwarz proof).
* N. Kahale, *Eigenvalues and expansion of regular graphs*, J. ACM 42 (1995).
* N. Alon and V. D. Milman, *λ₁, isoperimetric inequalities for graphs, and superconcentrators*,
  J. Combin. Theory Ser. B 38 (1985), and N. Alon, *Eigenvalues and expanders*, Combinatorica 6
  (1986): other one-sided (`λ₂`-based) vertex-expansion bounds, not formalized here.
* For integer `c ≥ 0` the shifted bound is Tanner's bound for `G` with `c` loops at every vertex;
  the case `c = d` is the standard self-loop trick for bipartite graphs. We found no statement
  in the literature for a general real shift; the proof is the same.
-/

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Neighbourhoods and the vertex boundary -/

/-- The (open) **neighbourhood** `N(S)` of a vertex set `S`: the vertices adjacent to at least
one vertex of `S`. It may meet `S`, and `N(∅) = ∅`. -/
def neighborhood (S : Finset V) : Finset V := {v | ∃ u ∈ S, G.Adj u v}

/-- The **vertex boundary** `N(S) \ S` of a vertex set `S`: the vertices outside `S` adjacent to
some vertex of `S`. -/
def vertexBoundary (S : Finset V) : Finset V := G.neighborhood S \ S

/-- `G` is an **`ε`-vertex-expander**: every vertex set `S` containing at most half the vertices
has at least `ε|S|` vertices outside `S` adjacent to it.

As for `IsEdgeExpander`, on fewer than two vertices the only admissible `S` is `∅`, so every
graph there is an `ε`-vertex-expander for every `ε`; the condition is also trivially true for
`ε ≤ 0`. -/
def IsVertexExpander (ε : ℝ) : Prop :=
  ∀ S : Finset V, 2 * #S ≤ Fintype.card V → ε * #S ≤ #(G.vertexBoundary S)

variable {G}

omit [DecidableEq V] in
/-- `v ∈ N(S)` exactly when `v` is adjacent to some `u ∈ S`. -/
@[simp]
theorem mem_neighborhood {S : Finset V} {v : V} :
    v ∈ G.neighborhood S ↔ ∃ u ∈ S, G.Adj u v := by
  simp [neighborhood]

/-- `v ∈ N(S) \ S` exactly when `v ∉ S` and `v` is adjacent to some `u ∈ S`. -/
theorem mem_vertexBoundary {S : Finset V} {v : V} :
    v ∈ G.vertexBoundary S ↔ v ∉ S ∧ ∃ u ∈ S, G.Adj u v := by
  rw [vertexBoundary, Finset.mem_sdiff, mem_neighborhood, and_comm]

/-! ### Vertex versus edge expansion -/

/-- **Vertex boundary versus edge boundary, lower bound**: `|N(S) \ S| ≤ |∂S|` for every graph and
every vertex set `S`. Each vertex of the vertex boundary is the far end of at least one boundary
edge. No regularity or degree bound is needed, and `S = ∅` gives `0 ≤ 0`. -/
theorem card_vertexBoundary_le_card_edgeBoundary (S : Finset V) :
    #(G.vertexBoundary S) ≤ #(G.edgeBoundary S) := by
  refine Finset.card_le_card_of_surjOn Prod.snd ?_
  intro v hv
  obtain ⟨hvS, u, hu, huv⟩ := mem_vertexBoundary.mp (Finset.mem_coe.mp hv)
  exact ⟨(u, v), Finset.mem_coe.mpr (mem_edgeBoundary.mpr ⟨hu, hvS, huv⟩), rfl⟩

/-- **Vertex boundary versus edge boundary, upper bound**: if every vertex has degree at most `d`,
then `|∂S| ≤ d |N(S) \ S|`. Each vertex of the vertex boundary is the far end of at most `d`
boundary edges. For `d = 0` the graph has no edges and both sides are `0`. -/
theorem card_edgeBoundary_le_mul_card_vertexBoundary {d : ℕ} (hd : ∀ v, G.degree v ≤ d)
    (S : Finset V) : #(G.edgeBoundary S) ≤ d * #(G.vertexBoundary S) := by
  refine Finset.card_le_mul_card_image_of_maps_to (f := Prod.snd) ?_ d ?_
  · intro e he
    obtain ⟨h1, h2, h3⟩ := mem_edgeBoundary.mp he
    exact mem_vertexBoundary.mpr ⟨h2, e.1, h1, h3⟩
  · intro v _
    calc #{e ∈ G.edgeBoundary S | e.2 = v} ≤ #(G.neighborFinset v) := by
          refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
          · intro e he
            have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
            have hadj := (mem_edgeBoundary.mp he'.1).2.2
            rw [he'.2] at hadj
            simpa using hadj.symm
          · intro e₁ h₁ e₂ h₂ h
            have h₁' := (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).2
            have h₂' := (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).2
            exact Prod.ext h (h₁'.trans h₂'.symm)
      _ = G.degree v := G.card_neighborFinset_eq_degree v
      _ ≤ d := hd v

/-- An `ε`-vertex-expander is an `ε`-edge-expander (`card_vertexBoundary_le_card_edgeBoundary`).
No degree assumption is needed. -/
theorem IsVertexExpander.isEdgeExpander {ε : ℝ} (h : G.IsVertexExpander ε) :
    G.IsEdgeExpander ε := fun S hS =>
  (h S hS).trans (by exact_mod_cast card_vertexBoundary_le_card_edgeBoundary S)

/-- **Edge expansion gives vertex expansion**: in an `ε`-edge-expander whose degrees are all at
most `d`, every `S` with `|S| ≤ n/2` has `ε |S| ≤ d |N(S) \ S|`. -/
theorem IsEdgeExpander.mul_card_le_card_vertexBoundary {d : ℕ} (hd : ∀ v, G.degree v ≤ d)
    {ε : ℝ} (h : G.IsEdgeExpander ε) {S : Finset V} (hS : 2 * #S ≤ Fintype.card V) :
    ε * #S ≤ d * #(G.vertexBoundary S) :=
  (h S hS).trans (by exact_mod_cast card_edgeBoundary_le_mul_card_vertexBoundary hd S)

/-- An `ε`-edge-expander whose degrees are all at most `d` is an `ε/d`-vertex-expander.

For `d = 0` the quotient is the junk value `ε / 0 = 0`, and the conclusion `IsVertexExpander 0`
holds trivially (an edgeless graph on at least two vertices is an `ε`-edge-expander only for
`ε ≤ 0`). -/
theorem IsEdgeExpander.isVertexExpander {d : ℕ} (hd : ∀ v, G.degree v ≤ d) {ε : ℝ}
    (h : G.IsEdgeExpander ε) : G.IsVertexExpander (ε / d) := by
  intro S hS
  have key := h.mul_card_le_card_vertexBoundary hd hS
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · simp
  · have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
    rw [div_mul_eq_mul_div, div_le_iff₀ hd0', mul_comm _ (d : ℝ)]
    exact key

/-- **Cheeger-type vertex expansion**: in a `d`-regular graph on `n ≥ 2` vertices every `S` with
`|S| ≤ n/2` satisfies `(d − λ₂) |S| ≤ 2d |N(S) \ S|`. This is the easy direction of Cheeger's
inequality (`isEdgeExpander_spectralGap_div_two`) combined with
`card_edgeBoundary_le_mul_card_vertexBoundary`. For `d = 0` it reads `−λ₂ |S| ≤ 0`, true since
then `λ₂ = 0`. Alon and Milman prove other bounds of this kind, not formalized here. -/
theorem degree_sub_secondAdjEigenvalue_mul_card_le_card_vertexBoundary [Nontrivial V] {d : ℕ}
    (hd : G.IsRegularOfDegree d) {S : Finset V} (hS : 2 * #S ≤ Fintype.card V) :
    ((d : ℝ) - G.secondAdjEigenvalue) * #S ≤ 2 * d * #(G.vertexBoundary S) := by
  have h := (isEdgeExpander_spectralGap_div_two hd).mul_card_le_card_vertexBoundary
    (fun v => (hd v).le) hS
  rw [spectralGap_eq hd] at h
  linarith

/-- A `d`-regular graph on `n ≥ 2` vertices is a `(d − λ₂)/(2d)`-vertex-expander. For `d = 0`
(where `λ₂ = 0`) the quotient is the junk value `0 / 0 = 0` and the statement is trivially
true. -/
theorem isVertexExpander_degree_sub_secondAdjEigenvalue [Nontrivial V] {d : ℕ}
    (hd : G.IsRegularOfDegree d) :
    G.IsVertexExpander (((d : ℝ) - G.secondAdjEigenvalue) / (2 * d)) := by
  have h := (isEdgeExpander_spectralGap_div_two hd).isVertexExpander (fun v => (hd v).le)
  rw [spectralGap_eq hd, div_div] at h
  exact h

/-! ### The shifted operator norm on vectors orthogonal to the constants -/

variable {d : ℕ}

/-- **Operator norm of `A + cI` on `𝟙^⊥`**: in a `d`-regular graph on `n ≥ 2` vertices, every
`x` with `Σ x_v = 0` satisfies `‖Ax + cx‖² ≤ max(|λ₂ + c|, |λₙ + c|)² ‖x‖²`, for every real `c`.
For `c = 0` the constant is `λ(G)²`. The proof expands `x` in the eigenbasis and uses
`eigenvalues_mem_Icc_of_coeff_ne_zero`, so it is valid also when `λ₁ = d` is repeated
(disconnected `G`). -/
theorem dotProduct_self_adjMatrix_mulVec_add_smul_le [Nontrivial V] (hd : G.IsRegularOfDegree d)
    (c : ℝ) {x : V → ℝ} (hx : ∑ v, x v = 0) :
    (G.adjMatrix ℝ *ᵥ x + c • x) ⬝ᵥ (G.adjMatrix ℝ *ᵥ x + c • x)
      ≤ (max |G.secondAdjEigenvalue + c| |G.smallestAdjEigenvalue + c|) ^ 2 * (x ⬝ᵥ x) := by
  have hcoeff : ∀ j, (G.isHermitian_adjMatrix ℝ).coeff (G.adjMatrix ℝ *ᵥ x + c • x) j
      = ((G.isHermitian_adjMatrix ℝ).eigenvalues j + c)
        * (G.isHermitian_adjMatrix ℝ).coeff x j := by
    intro j
    have hadd : (G.isHermitian_adjMatrix ℝ).coeff (G.adjMatrix ℝ *ᵥ x + c • x) j
        = (G.isHermitian_adjMatrix ℝ).coeff (G.adjMatrix ℝ *ᵥ x) j
          + (G.isHermitian_adjMatrix ℝ).coeff (c • x) j :=
      dotProduct_add _ _ _
    rw [hadd, Matrix.IsHermitian.coeff_mulVec, Matrix.IsHermitian.coeff_smul]
    ring
  rw [← (G.isHermitian_adjMatrix ℝ).sum_sq_coeff, ← (G.isHermitian_adjMatrix ℝ).sum_sq_coeff,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [hcoeff, mul_pow]
  by_cases hj : (G.isHermitian_adjMatrix ℝ).coeff x j = 0
  · simp [hj]
  · have hmem := eigenvalues_mem_Icc_of_coeff_ne_zero hd hx hj
    have habs : |(G.isHermitian_adjMatrix ℝ).eigenvalues j + c|
        ≤ max |G.secondAdjEigenvalue + c| |G.smallestAdjEigenvalue + c| :=
      (abs_le_max_abs_abs (by linarith [hmem.1]) (by linarith [hmem.2])).trans
        (max_comm _ _).le
    exact mul_le_mul_of_nonneg_right (sq_le_sq' (abs_le.mp habs).1 (abs_le.mp habs).2)
      (sq_nonneg _)

/-! ### Tanner's bound -/

/-- The real arithmetic closing Tanner's argument: from `(k s)² ≤ t (μ² s(1 − s/n) + n (k s/n)²)`
deduce `n k² s ≤ t (k² s + μ² (n − s))`, cancelling a factor `s` (the case `s = 0` is trivial). -/
private theorem tanner_arith {n s t k μ : ℝ} (hn : 0 < n) (hs : 0 ≤ s) (hsn : s ≤ n)
    (ht : 0 ≤ t) (h : (k * s) ^ 2 ≤ t * (μ ^ 2 * (s * (1 - s / n)) + n * (k * s / n) ^ 2)) :
    n * k ^ 2 * s ≤ t * (k ^ 2 * s + μ ^ 2 * (n - s)) := by
  have h1 := mul_le_mul_of_nonneg_left h hn.le
  have e1 : n * (k * s) ^ 2 = s * (n * k ^ 2 * s) := by ring
  have e2 : n * (t * (μ ^ 2 * (s * (1 - s / n)) + n * (k * s / n) ^ 2))
      = s * (t * (k ^ 2 * s + μ ^ 2 * (n - s))) := by
    field_simp
    ring
  rw [e1, e2] at h1
  rcases hs.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    have : 0 ≤ n - s := sub_nonneg.mpr hsn
    positivity
  · exact le_of_mul_le_mul_left h1 hpos

/-- **Tanner's bound, core form.** Let `G` be `d`-regular on `n ≥ 2` vertices, `c` a real shift,
`S` a vertex set with `s = |S|`, and `T` any vertex set outside which `y = (A + cI) 1_S`
vanishes. Then `n (d + c)² s ≤ |T| · ((d + c)² s + μ_c² (n − s))` with
`μ_c = max(|λ₂ + c|, |λₙ + c|)`.

Proof: `Σ_v y_v = (d + c) s`, and Cauchy–Schwarz over `T` gives `((d + c) s)² ≤ |T| ‖y‖²`;
writing `1_S = x + (s/n) 𝟙` with `x ⟂ 𝟙` gives `‖y‖² = (d + c)² s²/n + ‖(A + cI) x‖²` and
`‖(A + cI) x‖² ≤ μ_c² s (n − s)/n`.

Edge cases: for `S = ∅` the left side is `0`; for `c = −d` the left side is `0`; `n − s` is a
real subtraction and is nonnegative. -/
theorem tanner_of_support_subset [Nontrivial V] (hd : G.IsRegularOfDegree d) (c : ℝ)
    (S T : Finset V)
    (hT : ∀ v ∉ T, (G.adjMatrix ℝ *ᵥ fun u => if u ∈ S then (1 : ℝ) else 0) v
      + c * (if v ∈ S then 1 else 0) = 0) :
    (Fintype.card V : ℝ) * ((d : ℝ) + c) ^ 2 * #S
      ≤ #T * (((d : ℝ) + c) ^ 2 * #S
        + (max |G.secondAdjEigenvalue + c| |G.smallestAdjEigenvalue + c|) ^ 2
          * (Fintype.card V - #S)) := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hsn : (#S : ℝ) ≤ Fintype.card V := by exact_mod_cast S.card_le_univ
  obtain ⟨ind, hind⟩ : ∃ ind : V → ℝ, ind = fun u => if u ∈ S then (1 : ℝ) else 0 := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y : V → ℝ, y = fun v => (G.adjMatrix ℝ *ᵥ ind) v + c * ind v :=
    ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z : V → ℝ,
      z = G.adjMatrix ℝ *ᵥ centeredIndicator S + c • centeredIndicator S := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = ((d : ℝ) + c) * #S / Fintype.card V := ⟨_, rfl⟩
  have hind' : ind = centeredIndicator S + ((#S : ℝ) / Fintype.card V) • (1 : V → ℝ) := by
    ext v; simp [hind, centeredIndicator]
  -- `y = z + k 𝟙`.
  have hy : ∀ v, y v = z v + k := by
    intro v
    have h1 : (G.adjMatrix ℝ *ᵥ ind) v
        = (G.adjMatrix ℝ *ᵥ centeredIndicator S) v + #S / Fintype.card V * d := by
      rw [hind', mulVec_add, mulVec_smul, adjMatrix_mulVec_one_of_regular hd]
      simp
    have h2 : ind v = centeredIndicator S v + #S / Fintype.card V := by rw [hind']; simp
    rw [hydef, hzdef, hk]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
    ring
  -- `z ⟂ 𝟙`.
  have hzsum : ∑ v, z v = 0 := by
    rw [← one_dotProduct, hzdef, dotProduct_add, dotProduct_smul, dotProduct_mulVec,
      one_vecMul_adjMatrix_of_regular hd, smul_dotProduct, one_dotProduct,
      sum_centeredIndicator, smul_zero, smul_zero, add_zero]
  -- `Σ_T y = (d + c) s`.
  have hsumT : ∑ v ∈ T, y v = ((d : ℝ) + c) * #S := by
    rw [Finset.sum_subset (Finset.subset_univ T) fun v _ hv => by rw [hydef, hind]; exact hT v hv]
    simp only [hy, Finset.sum_add_distrib, hzsum, Finset.sum_const, card_univ, nsmul_eq_mul,
      zero_add, hk]
    field_simp
  -- `‖y‖² = ‖z‖² + n k²`.
  have hyy : ∑ v, y v ^ 2 = z ⬝ᵥ z + Fintype.card V * k ^ 2 := by
    have : ∀ v, y v ^ 2 = z v * z v + 2 * k * z v + k ^ 2 := fun v => by rw [hy v]; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hzsum, Finset.sum_const,
      card_univ, nsmul_eq_mul, dotProduct]
    ring
  have hzz := dotProduct_self_adjMatrix_mulVec_add_smul_le hd c (sum_centeredIndicator S)
  rw [← hzdef, centeredIndicator_dotProduct_self] at hzz
  have hCS : (∑ v ∈ T, y v) ^ 2 ≤ #T * ∑ v ∈ T, y v ^ 2 := sq_sum_le_card_mul_sum_sq
  have hsub : ∑ v ∈ T, y v ^ 2 ≤ ∑ v, y v ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) fun v _ _ => sq_nonneg _
  have key : (((d : ℝ) + c) * #S) ^ 2
      ≤ #T * ((max |G.secondAdjEigenvalue + c| |G.smallestAdjEigenvalue + c|) ^ 2
          * (#S * (1 - #S / Fintype.card V))
        + Fintype.card V * (((d : ℝ) + c) * #S / Fintype.card V) ^ 2) := by
    rw [← hk, ← hsumT]
    calc (∑ v ∈ T, y v) ^ 2 ≤ #T * ∑ v ∈ T, y v ^ 2 := hCS
      _ ≤ #T * ∑ v, y v ^ 2 := mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _)
      _ ≤ _ := by
        rw [hyy]
        exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  exact tanner_arith hn (Nat.cast_nonneg _) hsn (Nat.cast_nonneg _) key

/-- Outside the neighbourhood `N(S)`, the vector `A 1_S` vanishes. -/
private theorem adjMatrix_mulVec_indicator_eq_zero_of_not_mem_neighborhood {S : Finset V}
    {v : V} (hv : v ∉ G.neighborhood S) :
    (G.adjMatrix ℝ *ᵥ fun u => if u ∈ S then (1 : ℝ) else 0) v = 0 := by
  rw [adjMatrix_mulVec_apply]
  refine Finset.sum_eq_zero fun u hu => ?_
  rw [mem_neighborFinset] at hu
  rw [if_neg]
  exact fun huS => hv (mem_neighborhood.mpr ⟨u, huS, hu.symm⟩)

/-- **Tanner's bound** (Tanner 1984; Hoory–Linial–Wigderson, Theorem 4.15). For a `d`-regular
graph on `n ≥ 2` vertices with two-sided parameter `λ(G) = max(|λ₂|, |λₙ|)` and every vertex set
`S` with `s = |S|`,

  `n d² s ≤ |N(S)| · (d² s + λ(G)² (n − s))`,

where `N(S)` is the open neighbourhood. For `d ≥ 1` (so that `λ(G) ≥ 1`) this is
`|N(S)| ≥ d² s / (d² s/n + λ(G)²(1 − s/n))`; the multiplicative form avoids the division, whose
denominator is `0` for `d = 0`, where the quotient would be the junk value `x / 0 = 0`.
Degenerate cases: for `S = ∅` or `d = 0` the left side is `0`; for `S = V` and `d ≥ 1` the bound
is an equality. `n − s` is a real
subtraction, nonnegative since `s ≤ n`. `n ≥ 2` (`Nontrivial V`) is needed only because `λ₂` is. -/
theorem tanner [Nontrivial V] (hd : G.IsRegularOfDegree d) (S : Finset V) :
    (Fintype.card V : ℝ) * d ^ 2 * #S
      ≤ #(G.neighborhood S)
        * ((d : ℝ) ^ 2 * #S + G.twoSidedAdjEigenvalue ^ 2 * (Fintype.card V - #S)) := by
  have h := tanner_of_support_subset hd 0 S (G.neighborhood S) fun v hv => by
    rw [zero_mul, add_zero]
    exact adjMatrix_mulVec_indicator_eq_zero_of_not_mem_neighborhood hv
  simpa [twoSidedAdjEigenvalue] using h

/-- **Tanner's bound with a spectral shift.** For a `d`-regular graph on `n ≥ 2` vertices, every
real `c` and every vertex set `S` with `s = |S|`,

  `n (d + c)² s ≤ |S ∪ N(S)| · ((d + c)² s + max(|λ₂ + c|, |λₙ + c|)² (n − s))`.

This is Tanner's argument for the matrix `A + cI`, whose "neighbourhood" of `S` is the closed
neighbourhood `S ∪ N(S)`; for the open neighbourhood `N(S)` it can fail when `c ≠ 0` (e.g. `K₂`,
`c = 1/2`, one vertex). For `c = 0` it is `tanner` with `N(S)` enlarged to `S ∪ N(S)`. Degenerate
cases: `c = −d`, `d = 0` with `c = 0`, and `S = ∅` make the left side `0`; `n − s` is a
nonnegative real subtraction. -/
theorem tanner_shift [Nontrivial V] (hd : G.IsRegularOfDegree d) (c : ℝ) (S : Finset V) :
    (Fintype.card V : ℝ) * ((d : ℝ) + c) ^ 2 * #S
      ≤ #(S ∪ G.neighborhood S) * (((d : ℝ) + c) ^ 2 * #S
        + (max |G.secondAdjEigenvalue + c| |G.smallestAdjEigenvalue + c|) ^ 2
          * (Fintype.card V - #S)) := by
  refine tanner_of_support_subset hd c S _ fun v hv => ?_
  rw [Finset.mem_union, not_or] at hv
  rw [adjMatrix_mulVec_indicator_eq_zero_of_not_mem_neighborhood hv.2, if_neg hv.1, mul_zero,
    add_zero]

/-- **Tanner's bound in terms of `λ₂` alone** (the shift `c = d`). For a `d`-regular graph on
`n ≥ 2` vertices and every vertex set `S` with `s = |S|`,

  `n (2d)² s ≤ |S ∪ N(S)| · ((2d)² s + (d + λ₂)² (n − s))`.

Here `max(|λ₂ + d|, |λₙ + d|) = d + λ₂` because `−d ≤ λₙ ≤ λ₂`. Unlike `tanner`, this is
informative for bipartite graphs as long as `λ₂ < d`: there `λₙ = −d`, so `λ(G) = d` and `tanner`
only gives `|N(S)| ≥ |S|`, which already follows by double counting. For `d = 0` both sides
are `0`. -/
theorem tanner_secondAdjEigenvalue [Nontrivial V] (hd : G.IsRegularOfDegree d) (S : Finset V) :
    (Fintype.card V : ℝ) * (2 * (d : ℝ)) ^ 2 * #S
      ≤ #(S ∪ G.neighborhood S) * ((2 * (d : ℝ)) ^ 2 * #S
        + ((d : ℝ) + G.secondAdjEigenvalue) ^ 2 * (Fintype.card V - #S)) := by
  have h := tanner_shift hd (d : ℝ) S
  have h1 : -(d : ℝ) ≤ G.smallestAdjEigenvalue :=
    (abs_le.mp ((le_max_right _ _).trans (twoSidedAdjEigenvalue_le_degree hd))).1
  have h2 := G.smallestAdjEigenvalue_le_secondAdjEigenvalue
  have hmax : max |G.secondAdjEigenvalue + d| |G.smallestAdjEigenvalue + d|
      = d + G.secondAdjEigenvalue := by
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), max_eq_left (by linarith)]
    ring
  have e : (d : ℝ) + d = 2 * d := by ring
  rw [hmax, e] at h
  exact h

/-- Tanner's bound with shift `c = d` on the hypercube `Q_{n+1}` (degree `n + 1`, `2^{n+1}`
vertices, `λ₂ = n − 1`, so `d + λ₂ = 2n`): for every set `S` of bit strings,

  `2^{n+1} (2(n+1))² |S| ≤ |S ∪ N(S)| · ((2(n+1))² |S| + (2n)² (2^{n+1} − |S|))`.

The bound is weak: for a single vertex it gives
`|S ∪ N(S)| ≥ (n+1)² 2^{n+1} / ((n+1)² + n² (2^{n+1} − 1))`, which tends to `((n+1)/n)²` as
`n → ∞`, while the true value is `n + 2`. For `n = 0` (`Q₁ = K₂`)
the right-hand factor `(2n)²` vanishes and the bound says `|S ∪ N(S)| ≥ 2` for nonempty `S`. -/
theorem hypercube_tanner (n : ℕ) (S : Finset (Fin (n + 1) → Bool)) :
    (2 : ℝ) ^ (n + 1) * (2 * ((n : ℝ) + 1)) ^ 2 * #S
      ≤ #(S ∪ (hypercube (n + 1)).neighborhood S)
        * ((2 * ((n : ℝ) + 1)) ^ 2 * #S + (2 * (n : ℝ)) ^ 2 * (2 ^ (n + 1) - #S)) := by
  have h := tanner_secondAdjEigenvalue (hypercube_isRegularOfDegree (n + 1)) S
  have hcard : (Fintype.card (Fin (n + 1) → Bool) : ℝ) = 2 ^ (n + 1) := by simp
  rw [hypercube_secondAdjEigenvalue, hcard] at h
  have e : ((n + 1 : ℕ) : ℝ) + ((n : ℝ) - 1) = 2 * n := by push_cast; ring
  rw [e] at h
  push_cast at h
  exact h

end SimpleGraph
