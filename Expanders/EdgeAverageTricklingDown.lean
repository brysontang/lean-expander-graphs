/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.EdgeAverageTricklingDownCore
import Expanders.TricklingDown

/-!
# Edge-average trickling down

Oppenheim's trickling down bounds the second eigenvalue `μ` of the underlying graph of a pure
complex through a bound `lam` that holds for **every** vertex link: `μ ≤ lam / (1 − lam)`. This
file proves that the uniform bound can be replaced by its **average over each edge**.

## The result

Let `K` be a pure `d`-dimensional complex, `d ≥ 2`, with a positive weight `m` on its top faces
(`IsTopWeight`). Let `w = linkWeightOf m ∅` be its weighted underlying graph, and
`w_z = linkWeightOf m {z}` the weighted graph of the link of the vertex `z`. Let the link of `z`
have second eigenvalue at most `lam z`. Put
`Λ = max_{u v edge of w} (lam u + lam v) / 2`.
If `K` is connected, and every vertex link with `lam z ≥ 1` is connected, then

  `μ / (1 + μ) ≤ Λ`, i.e. `μ ≤ l / (1 − l)` for every `l` with `Λ ≤ l < 1`

(`IsTopWeight.walkSecondEigenvalueLE_of_edge_average`; for counts,
`walkSecondEigenvalueLE_linkWeight_of_edge_average`). The same holds for the link of any face
`σ` with `|σ| ≤ d − 2`, in terms of the links of the faces `σ ∪ {z}`
(`IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_of_edge_average`).

With `lam` constant this is the one-step Oppenheim bound
(`IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_step_of_edge_average`, which recovers
`IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_step` with the same hypotheses). The edge
average can be much smaller than the maximum. In the cone over a graph `G` (the triangles
`{apex, u, v}` for the edges `u v` of `G`), the apex has link `G` and every other vertex has a
star as link (second eigenvalue `0`). So if `λ(G) ≥ 0` the largest link bound is `λ(G)`, while
`Λ = λ(G)/2`. Here in fact `μ = λ(G)/2`, checked numerically for `G` = `C₅` and the Petersen
graph.

### Hypotheses, and why each is there
* `d ≥ 2`: for a graph (`d = 1`) the vertex links have no edges, and every `lam` is allowed.
* `K` connected: two disjoint triangles have `μ = 1` while every link is an edge (`lam = −1`).
* Vertex links connected, but only where `lam z ≥ 1`. A bound `lam z < 1` already forces the link
  to be connected (`EdgeAverageTricklingDown.eq_of_walkSecondEigenvalueLE_lt_one`). Some
  connectivity is needed: the bowtie (two triangles sharing one vertex) has `Λ = 0` but `μ = 1/2`.
  The shared vertex has a disconnected link (`lam = 1`), and the other four vertices have a
  single edge as link (`lam = −1`).
* `l < 1`: for `l ≥ 1` the bound `l / (1 − l)` is negative (or, in Lean, `0` at `l = 1`). For
  `1/2 ≤ l < 1` it is at least `1`, and the conclusion holds for every graph.
* No hypothesis on vertices in no triangle, and no lower bound on `lam`. Every vertex link with an
  edge forces `lam z ≥ −1`, so `l ≥ −1` as soon as `K` has an edge.

## How it was found

By computation. The statement was proposed after numerical experiments on random weighted
2-complexes. It then survived an independent attempt at refutation:
* all `2^20` labelled 2-complexes on 6 points;
* millions of random uniform and lognormal-weighted complexes on 7–12 points;
* adversarial (SLSQP) weight optimisation up to 17 points, including clique complexes, cones,
  multi-cones, and a constrained search forcing the bound strictly below Oppenheim's;
* a first-order perturbation analysis at the equality points.
The worst observed violation was `6 · 10⁻¹⁵`. The proposer also showed that the natural scalar
route fails. Garland's method, which averages `lam z` with weights the local variances of the
eigenfunction, does *not* give the edge average: the exploration reported that the
variance-weighted average exceeds `Λ` on about 0.1% of random 7-point complexes (a figure reported
by that run and not re-derived here). A proof has to use more of each link than its second
eigenvalue.

It was then proved. The proof is Chen and Liu's integrated Bochner method (arXiv:2609.19514,
Section 2), with each link's gap kept separate instead of being replaced by the minimum. The one
new line is that the sum `Σ_z lam z · L_z` of the local Laplacians regroups by edges as
`Σ_{u v} (lam u + lam v) · L_{u v}`. Here the method is run on the *edge* walk and without the
spectral theorem on triangles:
* `Expanders/EdgeAverageTricklingDownLocal.lean`: the Bochner inequality of one link
  (`L_z² ⪰ (1 − lam z) L_z`), by an explicit sum-of-squares certificate;
* `Expanders/EdgeAverageTricklingDownCore.lean`: the edge-walk argument for an abstract
  triangle weight, with an eigenfunction of the edge walk supplied by
  `exists_walk_eigenfunction_of_lt`.

## What the literature search found

The literature search covered Oppenheim (arXiv:1709.04431, 1110.5724, 1111.1385), Kaufman–Oppenheim,
Alev–Lau, Dikstein–Dinur–Filmus–Harsha, Ballmann–Świątkowski and Żuk (through its restatement in
Oppenheim 1111.1385), the matrix trickle-down of Abdolazimi–Liu–Oveis Gharan (2106.03845), and the
2025–26 papers of Leake, Liu and Oveis Gharan (C-Lorentzian), Chen–Liu (2609.19514), Guo–Zhang
(2608.06172) and Brändén–Leake–Oveis Gharan (2609.13138). On the spectral graph theory side it
covered Bauer–Jost and curvature. It found:
* **No explicit statement** of the edge-average bound. The averaged trickle-down results found
  are type-based, for partite complexes, not edge-based for general complexes:
  Abdolazimi–Oveis Gharan (arXiv:2208.04486), whose average is over the types of the
  codimension-2 faces, and Chen–Liu Theorem 1.2 (spectral influence between parts). A further
  web search, done while formalizing, also found no edge-based statement.
* **It is a short consequence of a published proof.** Chen–Liu's Propositions 2.2 and 2.3 and
  their Lemma 1.4 are stated in the generality needed. Keeping the gaps separate in their proof of
  Theorem 1.1 gives `L² ⪰ (1 − 2Λ) L` on functions of the triangles, and Lemma 1.4 converts this
  to `μ ≤ Λ / (1 − Λ)`. By the rule that a short consequence of a published result counts as
  known, the result should be credited to their method, **not presented as new**.
* Oppenheim's vertex-level Garland argument (1110.5724, Proposition 3.7; 1709.04431) is stated
  for a bound that is uniform over the vertex links. The literature check computed that running it
  with separate local bounds gives only `(2Λ − lam_min) / (1 − lam_min)`; that computation is
  reported here and was not re-derived.

## Theorems
* `linkTriangleWeight`, `isTriangleWeight_linkTriangleWeight`: the vertex links of the link of
  `σ`, as one triangle weight. **Proved.**
* `IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_of_edge_average`: edge-average trickling down
  for the link of any `σ` with `|σ| + 2 ≤ d`. **Proved.**
* `IsTopWeight.walkSecondEigenvalueLE_of_edge_average`: the case `σ = ∅`, the statement above.
  **Proved.**
* `walkSecondEigenvalueLE_linkWeight_of_edge_average`: the same for unweighted complexes
  (`linkWeight`, counting top faces). **Proved.**
* `IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_step_of_edge_average`: the uniform case is
  Oppenheim's step, with exactly the hypotheses of
  `IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_step`. **Proved.**

## References
* X. Chen, K. Liu, *Spectral gap of down-up walks via trickle-down: a simplified and sharpened
  analysis*, arXiv:2609.19514 (2026), Section 2 (Propositions 2.2, 2.3) and Appendix A
  (Lemma 1.4).
* V. L. Alev, L. C. Lau, *Improved analysis of higher order random walks and applications*,
  arXiv:2001.02827.
* V. Abdolazimi, S. Oveis Gharan, *An improved trickle-down theorem for partite complexes*,
  arXiv:2208.04486.
* I. Oppenheim, *Local spectral expansion approach to high dimensional expanders, Part I:
  descent of spectral gaps*, Discrete Comput. Geom. 59 (2018), arXiv:1709.04431.
* H. Garland, *p-adic curvature and the cohomology of discrete subgroups of p-adic groups*,
  Ann. of Math. 97 (1973).
-/

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-! ### The vertex links of a link, as one triangle weight -/

/-- The weighted graphs of the links of the faces `σ ∪ {a}`, as one function of three points:
`linkTriangleWeight m σ a b c` is the weight of the edge `b c` in the link of `σ ∪ {a}`, that is,
the total weight of the top faces containing `σ ∪ {a, b, c}`. It is `0` when `a ∈ σ`, so that it
is symmetric in `a, b, c` (`isTriangleWeight_linkTriangleWeight`). For `σ = ∅` it is
`linkWeightOf m {a} b c`. -/
noncomputable def linkTriangleWeight (m : Finset ι → ℝ) (σ : Finset ι) (a b c : ι) : ℝ :=
  if a ∈ σ then 0 else linkWeightOf m (insert a σ) b c

theorem linkTriangleWeight_of_mem (m : Finset ι → ℝ) {σ : Finset ι} {a : ι} (ha : a ∈ σ) :
    linkTriangleWeight m σ a = fun _ _ => 0 := by
  funext b c
  exact if_pos ha

theorem linkTriangleWeight_of_notMem (m : Finset ι → ℝ) {σ : Finset ι} {a : ι} (ha : a ∉ σ) :
    linkTriangleWeight m σ a = linkWeightOf m (insert a σ) := by
  funext b c
  exact if_neg ha

theorem linkTriangleWeight_swap12 (m : Finset ι → ℝ) (σ : Finset ι) (a b c : ι) :
    linkTriangleWeight m σ a b c = linkTriangleWeight m σ b a c := by
  unfold linkTriangleWeight
  by_cases ha : a ∈ σ
  · rw [if_pos ha]
    by_cases hb : b ∈ σ
    · rw [if_pos hb]
    · rw [if_neg hb, linkWeightOf_eq_zero_of_mem_left m (Finset.mem_insert_of_mem ha)]
  · by_cases hb : b ∈ σ
    · rw [if_pos hb, if_neg ha, linkWeightOf_eq_zero_of_mem_left m (Finset.mem_insert_of_mem hb)]
    · rw [if_neg ha, if_neg hb]
      unfold linkWeightOf
      have hset : insert b (insert c (insert a σ)) = insert a (insert c (insert b σ)) := by
        ext x
        simp only [Finset.mem_insert]
        tauto
      rw [hset]
      refine if_congr ?_ rfl rfl
      simp only [Finset.mem_insert, not_or]
      constructor
      · rintro ⟨h1, ⟨h2, -⟩, h4, h5⟩
        exact ⟨fun h => h4 h.symm, ⟨fun h => h2 h.symm, ha⟩, fun h => h1 h.symm, h5⟩
      · rintro ⟨h1, ⟨h2, -⟩, h4, h5⟩
        exact ⟨fun h => h4 h.symm, ⟨fun h => h2 h.symm, hb⟩, fun h => h1 h.symm, h5⟩

/-- For a nonnegative weight `m`, the vertex links of the link of `σ` form a triangle weight. -/
theorem isTriangleWeight_linkTriangleWeight {m : Finset ι → ℝ} (hnn : ∀ F, 0 ≤ m F)
    (σ : Finset ι) : EdgeAverageTricklingDown.IsTriangleWeight (linkTriangleWeight m σ) where
  swap12 a b c := linkTriangleWeight_swap12 m σ a b c
  swap23 a b c := by
    unfold linkTriangleWeight
    split_ifs
    · rfl
    · exact linkWeightOf_symm m _ b c
  nonneg a b c := by
    unfold linkTriangleWeight
    split_ifs
    · exact le_rfl
    · exact linkWeightOf_nonneg hnn _ b c
  loop a b := by
    unfold linkTriangleWeight
    split_ifs
    · rfl
    · exact linkWeightOf_self m _ b

/-! ### Edge-average trickling down -/

variable {K : PreAbstractSimplicialComplex ι} {d : ℕ} {m : Finset ι → ℝ}

/-- **Edge-average trickling down, for the link of a face.** Let `m` be a top weight of the pure
`d`-dimensional complex `K`, and let `σ` (possibly `∅`) have `|σ| + 2 ≤ d`. Suppose:
* the link of `σ` is connected;
* for every `z ∉ σ` with `σ ∪ {z}` a face, the link of `σ ∪ {z}` has second eigenvalue at most
  `lam z`, and is connected if `lam z ≥ 1`;
* `(lam u + lam v) / 2 ≤ l` for every edge `u v` of the link of `σ`, where `l < 1`.

Then the link of `σ` has second eigenvalue at most `l / (1 − l)`.

Degenerate cases:
* `l ≥ 1/2`: the conclusion is a bound `≥ 1` and holds for every graph.
* `σ` neither `∅` nor a face: the link of `σ` is not connected (it has no faces), so the
  theorem does not apply. Its weighted graph is empty anyway.
* `z ∈ σ`, and `z` with `σ ∪ {z}` not a face: these points are not vertices of the link of `σ`
  and carry no condition.
* A vertex link with `lam z < 1` is automatically connected
  (`EdgeAverageTricklingDown.eq_of_walkSecondEigenvalueLE_lt_one`), hence the restriction of the
  connectivity hypothesis to `lam z ≥ 1`.

With `lam` constant this is `IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_step`
(`IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_step_of_edge_average`). -/
theorem IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_of_edge_average
    (hm : K.IsTopWeight d m) {σ : Finset ι} (hcard : #σ + 2 ≤ d)
    (hconn : (K.link σ).IsConnected) {lam : ι → ℝ}
    (hlam : ∀ z, z ∉ σ → insert z σ ∈ K →
      WalkSecondEigenvalueLE (linkWeightOf m (insert z σ)) (lam z))
    (hlink : ∀ z, z ∉ σ → insert z σ ∈ K → 1 ≤ lam z → (K.link (insert z σ)).IsConnected)
    {l : ℝ} (hl : l < 1) (hedge : ∀ u v, 0 < linkWeightOf m σ u v → (lam u + lam v) / 2 ≤ l) :
    WalkSecondEigenvalueLE (linkWeightOf m σ) (l / (1 - l)) := by
  have hk : (0 : ℝ) < (d : ℝ) - 1 - #σ := by
    have h : ((#σ + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hcard
    push_cast at h
    linarith
  refine (isTriangleWeight_linkTriangleWeight hm.nonneg σ).walkSecondEigenvalueLE_of_edge_average
    hk (fun a b => sum_linkWeightOf_insert_right hm.card_eq_of_ne_zero σ a b)
    (fun F hF u v hu hv => hm.eq_of_forall_linkWeightOf_pos hconn F hF u v hu hv)
    (fun z => ?_) (fun z hz1 F hF u v hu hv => ?_) hl hedge
  · -- the link bounds
    by_cases hz : z ∈ σ
    · rw [linkTriangleWeight_of_mem m hz]
      exact walkSecondEigenvalueLE_of_forall_eq_zero (fun _ _ => rfl) _
    rw [linkTriangleWeight_of_notMem m hz]
    by_cases hK : insert z σ ∈ K
    · exact hlam z hz hK
    · exact walkSecondEigenvalueLE_of_forall_eq_zero
        (hm.linkWeightOf_eq_zero_of_notMem (Finset.insert_nonempty z σ) hK) _
  · -- connectivity of the links with `lam z ≥ 1`
    by_cases hz : z ∈ σ
    · rw [linkTriangleWeight_of_mem m hz] at hu
      simp at hu
    rw [linkTriangleWeight_of_notMem m hz] at hF hu hv
    by_cases hK : insert z σ ∈ K
    · exact hm.eq_of_forall_linkWeightOf_pos (hlink z hz hK hz1) F hF u v hu hv
    · simp [hm.linkWeightOf_eq_zero_of_notMem (Finset.insert_nonempty z σ) hK] at hu

/-- **Edge-average trickling down.** Let `m` be a top weight of the pure `d`-dimensional complex
`K`, `d ≥ 2`, with `K` connected. Let the link of every vertex `z` have second eigenvalue at most
`lam z`, and let it be connected if `lam z ≥ 1`. If `(lam u + lam v) / 2 ≤ l` for every edge
`u v` of the weighted underlying graph, where `l < 1`, then the weighted underlying graph has
second eigenvalue at most `l / (1 − l)`.

Equivalently: its second eigenvalue `μ` satisfies `μ / (1 + μ) ≤ Λ`, where `Λ` is the largest
edge average `(lam u + lam v) / 2`. The two forms agree because `μ ≥ −1/d > −1` and `x ↦ x/(1+x)`
is increasing; when `Λ ≥ 1/2` both are automatic.

Degenerate cases:
* `d = 1` is excluded: a graph's vertex links have no edges, so every `lam` would be allowed.
* `l ≥ 1/2`: automatic, since `l / (1 − l) ≥ 1`.
* The connectivity of `K` cannot be dropped (two disjoint triangles: `μ = 1`, `Λ = −1`). Nor can
  that of the vertex links with `lam z ≥ 1` (the bowtie: `μ = 1/2`, `Λ = 0`).
* Points that are not vertices of `K` carry no condition.

For `d ≥ 3` this is the 2-dimensional statement for the triangle weights
`m'(t) = Σ_{F ⊇ t} m F`, whose vertex links are those of `K`. This is the reduction used in the
proof: `linkWeightOf m {a} b c` is the weight `m'({a, b, c})`. -/
theorem IsTopWeight.walkSecondEigenvalueLE_of_edge_average (hm : K.IsTopWeight d m)
    (hd : 2 ≤ d) (hconn : K.IsConnected) {lam : ι → ℝ}
    (hlam : ∀ z, {z} ∈ K → WalkSecondEigenvalueLE (linkWeightOf m {z}) (lam z))
    (hlink : ∀ z, {z} ∈ K → 1 ≤ lam z → (K.link {z}).IsConnected)
    {l : ℝ} (hl : l < 1) (hedge : ∀ u v, 0 < linkWeightOf m ∅ u v → (lam u + lam v) / 2 ≤ l) :
    WalkSecondEigenvalueLE (linkWeightOf m ∅) (l / (1 - l)) := by
  have e : ∀ z : ι, insert z (∅ : Finset ι) = {z} := fun z => by simp
  refine hm.walkSecondEigenvalueLE_linkWeightOf_of_edge_average (σ := ∅)
    (by rw [Finset.card_empty]; omega) (by rw [link_empty]; exact hconn)
    (fun z _ hz => ?_) (fun z _ hz hz1 => ?_) hl hedge
  · rw [e] at hz ⊢; exact hlam z hz
  · rw [e] at hz ⊢; exact hlink z hz hz1

/-- **Edge-average trickling down, counting top faces.** The case `m = K.uniformWeight d` of
`IsTopWeight.walkSecondEigenvalueLE_of_edge_average`, for the weighted graphs `linkWeight` of
`IsLocalSpectralExpander`. Here `K` is pure of dimension `d ≥ 2` and connected (so it has a
face), the link of every vertex `z` has second eigenvalue at most `lam z` and is connected if
`lam z ≥ 1`, and `(lam u + lam v) / 2 ≤ l < 1` on every edge. Then the underlying graph has
second eigenvalue at most `l / (1 − l)`. The degenerate cases are those of the weighted
version. -/
theorem walkSecondEigenvalueLE_linkWeight_of_edge_average (hpure : K.IsPure d) (hd : 2 ≤ d)
    (hconn : K.IsConnected) {lam : ι → ℝ}
    (hlam : ∀ z, {z} ∈ K → WalkSecondEigenvalueLE (K.linkWeight d {z}) (lam z))
    (hlink : ∀ z, {z} ∈ K → 1 ≤ lam z → (K.link {z}).IsConnected)
    {l : ℝ} (hl : l < 1) (hedge : ∀ u v, 0 < K.linkWeight d ∅ u v → (lam u + lam v) / 2 ≤ l) :
    WalkSecondEigenvalueLE (K.linkWeight d ∅) (l / (1 - l)) := by
  have hm := K.isTopWeight_uniformWeight hpure hconn.exists_mem
  simp only [K.linkWeight_eq_linkWeightOf] at hlam hedge ⊢
  exact hm.walkSecondEigenvalueLE_of_edge_average hd hconn hlam hlink hl hedge

/-- **The uniform case is Oppenheim's step.** With `lam z = μ < 1` for every vertex, the edge
average is `μ`, no vertex link needs a connectivity hypothesis, and
`IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_of_edge_average` gives the bound `μ / (1 − μ)`
under exactly the hypotheses of `IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_step`. The
degenerate cases are those of that theorem (`σ` of dimension at most `d − 3`, connected link). -/
theorem IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_step_of_edge_average
    (hm : K.IsTopWeight d m) {σ : Finset ι} (hcard : #σ + 2 ≤ d)
    (hconn : (K.link σ).IsConnected) {μ : ℝ} (hμ : μ < 1)
    (hloc : ∀ z, z ∉ σ → insert z σ ∈ K →
      WalkSecondEigenvalueLE (linkWeightOf m (insert z σ)) μ) :
    WalkSecondEigenvalueLE (linkWeightOf m σ) (μ / (1 - μ)) :=
  hm.walkSecondEigenvalueLE_linkWeightOf_of_edge_average (lam := fun _ => μ) hcard hconn hloc
    (fun _ _ _ h => absurd h (not_le.mpr hμ)) hμ (fun _ _ _ => by simp)

end PreAbstractSimplicialComplex
