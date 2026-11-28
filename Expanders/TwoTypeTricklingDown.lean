/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.TwoTypeTricklingDownCore
import Expanders.TwoTypeTricklingDownOneApex
import Expanders.TwoTypeTricklingDownPhi
import Expanders.EdgeAverageTricklingDown

/-!
# Two-type trickling down with an independent heavy set

Oppenheim's trickling down bounds the second eigenvalue `μ` of the underlying graph of a pure
complex by `lam / (1 − lam)` when every vertex link has second eigenvalue at most `lam`. The
edge-average version (`Expanders/EdgeAverageTricklingDown.lean`) replaces `lam` by the largest
average `(lam u + lam v)/2` over an edge. This file proves a bound for complexes whose large link
eigenvalues sit on an **independent set** of vertices. At `q = 0` the bound is attained, on a
family of cones over weighted paths (`fan`).

## The result

Let `K` be a pure `d`-dimensional complex, `d ≥ 2`, with a positive weight `m` on its top faces,
and with connected underlying graph. Let `A` be a set of vertices with no edge of `K` inside it,
and let `0 ≤ q ≤ p ≤ 1/2`. If the link of every vertex of `A` has second eigenvalue at most `p`,
and the link of every other vertex has second eigenvalue at most `q`, then the weighted
underlying graph has second eigenvalue at most

  `β(p, q) = (b + (1 + p) √Δ) / (4 (1 − q)(2 − p)(3 − p))`,

the larger root of `N(μ) = 2 (1 − q)(2 − p)(3 − p) μ² − b μ − c`, where
`b = p³ + 4p²q − 7p² − 13pq + 14p + 7q − 2`, `c = p³ + 2p²q − 4p² − 3pq + p + q` and
`Δ = p⁴ − 8p³ + 6p²q + 20p² − 24pq − 16p + q² + 20q + 4`
(`IsTopWeight.walkSecondEigenvalueLE_of_two_type`; `twoTypeBound`). No connectivity of the vertex
links is assumed.

* `β(p, p) = p/(1 − p)` is Oppenheim's bound, and `β(p, 0) = p/2`.
* For `q < p`, `β(p, q) < (p + q)/(2 − p − q)`, the edge-average bound for this class
  (`twoTypeBound_lt_edgeAverage`).
* With `q = 0` the bound is `p/2` (`IsTopWeight.walkSecondEigenvalueLE_half_of_cone_type`), and
  this is attained: the cone over a weighted path (`fan`) has apex link eigenvalue exactly `p` and
  underlying second eigenvalue exactly `p/2`, for every `0 < p ≤ 1/2` (`exists_isLeast_fan`). The
  edge-average bound there is `p/(2 − p)`.

## How it was found

By computation. The starting point was the conjectured edge-interpolated bound
`μ ≤ max_{uv} Φ(lam u, lam v)`, `Φ(a, b) = s + ab/(1 − s)`, `s = (a + b)/2`, which is still open.
To look for proofs, a family of proof certificates was set up: at each vertex a polynomial
`r(P_x) ≥ 0` on `[−1, lam_x]` applied to the eigenfunction restricted to the link, plus the
vertex identity `E[c(x) f(x) (f(y) − μ f(x))] = 0` and the edge identity
`E[g(x, y) f(x) (f(z) − h(x, y))] = 0`, with all multipliers chosen so that every per-triangle
quadratic form is negative semidefinite. Finding the multipliers is a semidefinite program. A
search over multipliers that depend only on the type (in `A` or not) of each vertex found a
degree-2 certificate (quadratic local polynomials) that excludes every eigenvalue above `β(p, q)`;
the search reports it as the best certificate of that kind, a claim not re-checked here. The
multipliers were then solved in closed form and the sign conditions reduced to three polynomial
inequalities, certified by exact Bernstein expansions. Two independent checks (symbolic and
numerical) preceded the formalization; this file and its companion files are the proof. The
one-apex variant is a second certificate of the same kind, found by a parallel search in the
same round.

## What the literature search found

The search covered Oppenheim (arXiv:1709.04431, 1110.5724, 1111.1385), Kaufman–Oppenheim,
Garland's method, the matrix trickle-down of Abdolazimi–Liu–Oveis Gharan (arXiv:2106.03845), the
partite trickle-down of Abdolazimi–Oveis Gharan (arXiv:2208.04486), Leake–Oveis Gharan
(arXiv:2510.06549), Leake–Lindberg–Oveis Gharan (arXiv:2503.01005) and Chen–Liu
(arXiv:2609.19514); a further web search was done while formalizing. It found:
* **A bound in terms of an independent set of high-eigenvalue vertices, or the value `β(p, q)`,
  was not found in this search.**
* For **partite** complexes there are type-based bounds. On a 3-partite complex with `A` one of the
  parts, the spectral-influence bound of Chen–Liu (Theorem 1.2) and Leake–Oveis Gharan gives
  `l/(2 − l)` with `l = (p + √(p² + 8q²))/2`. A numerical comparison (not formalized) shows that
  this published bound is the smaller one on most of the range: it is below `β(p, q)` once `q`
  exceeds a threshold `q_c(p)`, about `0.05 p` at `p = 0.1`, `0.13 p` at `p = 0.3` and `0.17 p`
  at `p = 1/2`, which is about 86% of the region `0 ≤ q ≤ p ≤ 1/2`. The two agree at `q = p`, and
  `β` is smaller only near `q = 0` (at `q = 0`: `p/2` against `p/(2 − p)`). So on 3-partite
  complexes the theorem here is mostly weaker than a known result. What it adds is outside the
  partite setting: it does not assume a partite complex and allows triangles with no vertex in
  `A`, where the partite formula can fail.
* The matrix trickle-down of Abdolazimi–Liu–Oveis Gharan is stated with complex-specific matrices;
  it gives no formula in terms of the link eigenvalues alone.

## Theorems
* `IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_of_two_type`: the bound for the link of any
  face `σ` with `|σ| + 2 ≤ d`. **Proved.**
* `IsTopWeight.walkSecondEigenvalueLE_of_two_type`: the case `σ = ∅`, the statement above.
  **Proved.**
* `IsTopWeight.walkSecondEigenvalueLE_half_of_cone_type`: `q = 0` gives `μ ≤ p/2`. **Proved.**
* `IsTopWeight.walkSecondEigenvalueLE_of_two_type_lt_edgeAverage`: for `q < p` the bound is
  strictly below the edge-average bound `(p + q)/(2 − p − q)`. **Proved.**
* `IsTopWeight.walkSecondEigenvalueLE_edgePhi_of_two_type`: for `p ≤ 111/400` or `q = 0` the
  bound is at most `Φ(p, q)`; so the `Φ` conjecture holds when the extreme pair `(p, q)` is
  realised on an edge leaving `A`. **Proved.**
* `fan`, `fanWeight`, `fan_sharp`, `exists_isLeast_fan`: the cone over the path `1 2 3 4` with
  weights `1, t, 1`; its apex link has second eigenvalue exactly `1/(1 + t)` and its underlying
  graph exactly `1/(2 (1 + t))`, so the bound `p/2` is attained for every `0 < p ≤ 1/2`.
  **Proved.**
* `IsTopWeight.walkSecondEigenvalueLE_half_of_one_apex` (in
  `Expanders/TwoTypeTricklingDownOneApex.lean`): if every triangle has exactly one vertex in
  `A`, the links of `A` are at most `p` and the others at most `0`, and `0 ≤ p < p* ≈ 0.7551`
  (root of `2p³ + 3p² − 14p + 8`), then `μ ≤ p/2`. A second certificate, diagonal on each
  triangle. **Proved.**

The algebra (`β`, the side polynomials, the per-triangle forms and the explicit multipliers) is in
`Expanders/TwoTypeTricklingDownAlgebra.lean`, the two local inequalities in
`Expanders/TwoTypeTricklingDownLocal.lean`, the argument for an abstract triangle weight in
`Expanders/TwoTypeTricklingDownCore.lean`, and the one-apex variant in
`Expanders/TwoTypeTricklingDownOneApex.lean`.

The comparisons with `Φ` (`β ≤ Φ` for `p ≤ 111/400`, `Φ < β` for `p > r₀ ≈ 0.27775` and small
`q > 0`) and the value `β(2/5, 1/5) = (379 + 7 √1641)/1664` are in
`Expanders/TwoTypeTricklingDownPhi.lean`.

## Not covered here
* The edge-interpolated conjecture `μ ≤ max Φ` itself, at `max lam ≤ 1/2`: neither proved nor
  refuted.
* Two-type bounds for `p > 1/2`; the one-apex variant for `p ≥ p*`.
* The combined bound `min (l/(1 − l), β)` over all choices of `A` is not stated separately: it is
  the conjunction of this theorem and the edge-average theorem for each choice.
-/

open Finset TwoTypeTricklingDown

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-! ### Two-type trickling down for complexes -/

variable {K : PreAbstractSimplicialComplex ι} {d : ℕ} {m : Finset ι → ℝ}

/-- **Two-type trickling down, for the link of a face.** Let `m` be a top weight of the pure
`d`-dimensional complex `K`, and let `σ` (possibly `∅`) have `|σ| + 2 ≤ d`. Suppose:
* the link of `σ` is connected;
* `A` is a set of points with no edge of the link of `σ` inside it;
* `0 ≤ q ≤ p ≤ 1/2`;
* for `z ∈ A` (resp. `z ∉ A`) with `z ∉ σ` and `σ ∪ {z}` a face, the link of `σ ∪ {z}` has second
  eigenvalue at most `p` (resp. `q`).

Then the link of `σ` has second eigenvalue at most `β(p, q)` (`twoTypeBound`).

Degenerate cases:
* Points `z ∈ σ`, and points with `σ ∪ {z}` not a face, are not vertices of the link of `σ` and
  carry no condition.
* `σ` neither `∅` nor a face: the link of `σ` has no faces and is not connected, so the theorem
  does not apply.
* `q = p` (for any `A`, for example `A = ∅`): Oppenheim's bound `p/(1 − p)`
  (`twoTypeBound_self`), which the proof uses as an input. So this case is not a new proof of
  Oppenheim's theorem.
* No connectivity of the links of the faces `σ ∪ {z}` is needed. -/
theorem IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_of_two_type (hm : K.IsTopWeight d m)
    {σ : Finset ι} (hcard : #σ + 2 ≤ d) (hconn : (K.link σ).IsConnected) (A : Set ι)
    (hA : ∀ a ∈ A, ∀ b ∈ A, linkWeightOf m σ a b = 0) {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p)
    (hp : p ≤ 1 / 2)
    (hlamA : ∀ z ∈ A, z ∉ σ → insert z σ ∈ K →
      WalkSecondEigenvalueLE (linkWeightOf m (insert z σ)) p)
    (hlamQ : ∀ z ∉ A, z ∉ σ → insert z σ ∈ K →
      WalkSecondEigenvalueLE (linkWeightOf m (insert z σ)) q) :
    WalkSecondEigenvalueLE (linkWeightOf m σ) (twoTypeBound p q) := by
  have hk : (0 : ℝ) < (d : ℝ) - 1 - #σ := by
    have h : ((#σ + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hcard
    push_cast at h
    linarith
  have hlink : ∀ (z : ι) (r : ℝ), (z ∉ σ → insert z σ ∈ K →
      WalkSecondEigenvalueLE (linkWeightOf m (insert z σ)) r) →
      WalkSecondEigenvalueLE (linkTriangleWeight m σ z) r := by
    intro z r hz
    by_cases hzσ : z ∈ σ
    · rw [linkTriangleWeight_of_mem m hzσ]
      exact walkSecondEigenvalueLE_of_forall_eq_zero (fun _ _ => rfl) _
    rw [linkTriangleWeight_of_notMem m hzσ]
    by_cases hK : insert z σ ∈ K
    · exact hz hzσ hK
    · exact walkSecondEigenvalueLE_of_forall_eq_zero
        (hm.linkWeightOf_eq_zero_of_notMem (Finset.insert_nonempty z σ) hK) _
  exact (isTriangleWeight_linkTriangleWeight hm.nonneg σ).walkSecondEigenvalueLE_of_two_type hk
    (fun a b => sum_linkWeightOf_insert_right hm.card_eq_of_ne_zero σ a b)
    (fun F hF u v hu hv => hm.eq_of_forall_linkWeightOf_pos hconn F hF u v hu hv)
    A hA hq hqp hp (fun z hz => hlink z p (hlamA z hz)) (fun z hz => hlink z q (hlamQ z hz))

/-- **Two-type trickling down.** Let `m` be a top weight of the pure `d`-dimensional complex `K`,
`d ≥ 2`, with `K` connected. Let `A` be a set of vertices with no edge of `K` inside it
(`linkWeightOf m ∅ a b = 0` for `a, b ∈ A`), and let `0 ≤ q ≤ p ≤ 1/2`. If the link of every
vertex of `A` has second eigenvalue at most `p`, and the link of every other vertex has second
eigenvalue at most `q`, then the weighted underlying graph has second eigenvalue at most
`β(p, q)` (`twoTypeBound`).

Degenerate cases:
* `d = 1` is excluded: a graph's vertex links have no edges, so every bound would be allowed.
* `q = p` (for any `A`, for example `A = ∅`): this is Oppenheim's bound,
  `β(p, p) = p/(1 − p)` (`twoTypeBound_self`).
* `q = 0`: `β(p, 0) = p/2` (`IsTopWeight.walkSecondEigenvalueLE_half_of_cone_type`), attained on
  the fan, a cone over a weighted path (`exists_isLeast_fan`).
* No connectivity of the vertex links is assumed: a link bound below `1` forces it.
* A vertex whose link is a single edge has link eigenvalue `−1`, within either bound.
* Points that are not vertices of `K` carry no condition.
* `K` must be connected: two disjoint triangles have `μ = 1` while every link is a single edge.

For `d ≥ 3` this is the 2-dimensional statement for the triangle weights `m'(t) = Σ_{F ⊇ t} m F`,
whose vertex links are those of `K`. -/
theorem IsTopWeight.walkSecondEigenvalueLE_of_two_type (hm : K.IsTopWeight d m) (hd : 2 ≤ d)
    (hconn : K.IsConnected) (A : Set ι) (hA : ∀ a ∈ A, ∀ b ∈ A, linkWeightOf m ∅ a b = 0)
    {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 1 / 2)
    (hlamA : ∀ z ∈ A, {z} ∈ K → WalkSecondEigenvalueLE (linkWeightOf m {z}) p)
    (hlamQ : ∀ z ∉ A, {z} ∈ K → WalkSecondEigenvalueLE (linkWeightOf m {z}) q) :
    WalkSecondEigenvalueLE (linkWeightOf m ∅) (twoTypeBound p q) := by
  have e : ∀ z : ι, insert z (∅ : Finset ι) = {z} := fun z => by simp
  refine hm.walkSecondEigenvalueLE_linkWeightOf_of_two_type (σ := ∅)
    (by rw [Finset.card_empty]; omega) (by rw [link_empty]; exact hconn) A hA hq hqp hp
    (fun z hz _ hK => ?_) (fun z hz _ hK => ?_)
  · rw [e] at hK ⊢; exact hlamA z hz hK
  · rw [e] at hK ⊢; exact hlamQ z hz hK

/-- **The cone bound.** Let `m` be a top weight of the connected pure `d`-dimensional complex `K`,
`d ≥ 2`, and let `A` be a set of vertices with no edge of `K` inside it. If `0 ≤ p ≤ 1/2`, the
link of every vertex of `A` has second eigenvalue at most `p`, and the link of every other vertex
has second eigenvalue at most `0`, then the underlying graph has second eigenvalue at most `p/2`.

This is `q = 0` in `IsTopWeight.walkSecondEigenvalueLE_of_two_type`. Triangles with no vertex in
`A` are allowed. The bound is attained on the fan, a cone over a weighted path, for every
`0 < p ≤ 1/2` (`exists_isLeast_fan`); equality on every cone over a graph with second eigenvalue
`p` is true by a short argument but is not formalized. The hypothesis `0 ≤ p` cannot be dropped:
with `p < 0` and `A = ∅` the
octahedron boundary (every link eigenvalue `0`, `μ = 0`) would violate `μ ≤ p/2`. -/
theorem IsTopWeight.walkSecondEigenvalueLE_half_of_cone_type (hm : K.IsTopWeight d m)
    (hd : 2 ≤ d) (hconn : K.IsConnected) (A : Set ι)
    (hA : ∀ a ∈ A, ∀ b ∈ A, linkWeightOf m ∅ a b = 0) {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hlamA : ∀ z ∈ A, {z} ∈ K → WalkSecondEigenvalueLE (linkWeightOf m {z}) p)
    (hlamQ : ∀ z ∉ A, {z} ∈ K → WalkSecondEigenvalueLE (linkWeightOf m {z}) 0) :
    WalkSecondEigenvalueLE (linkWeightOf m ∅) (p / 2) := by
  have h := hm.walkSecondEigenvalueLE_of_two_type hd hconn A hA le_rfl hp0 hp hlamA hlamQ
  rwa [twoTypeBound_zero hp] at h

/-- **Strictly below the edge-average bound.** Under the hypotheses of
`IsTopWeight.walkSecondEigenvalueLE_of_two_type` with `q < p`, the underlying graph has second
eigenvalue at most `β(p, q)`, and `β(p, q) < (p + q)/(2 − p − q)`. The right side is `s/(1 − s)`
with `s = (p + q)/2`, the value of the edge-average theorem
(`IsTopWeight.walkSecondEigenvalueLE_of_edge_average`) on a complex in which some edge joins a
vertex of eigenvalue `p` to one of eigenvalue `q`. At `q = p` the two bounds agree. -/
theorem IsTopWeight.walkSecondEigenvalueLE_of_two_type_lt_edgeAverage (hm : K.IsTopWeight d m)
    (hd : 2 ≤ d) (hconn : K.IsConnected) (A : Set ι)
    (hA : ∀ a ∈ A, ∀ b ∈ A, linkWeightOf m ∅ a b = 0) {p q : ℝ} (hq : 0 ≤ q) (hqp : q < p)
    (hp : p ≤ 1 / 2)
    (hlamA : ∀ z ∈ A, {z} ∈ K → WalkSecondEigenvalueLE (linkWeightOf m {z}) p)
    (hlamQ : ∀ z ∉ A, {z} ∈ K → WalkSecondEigenvalueLE (linkWeightOf m {z}) q) :
    WalkSecondEigenvalueLE (linkWeightOf m ∅) (twoTypeBound p q) ∧
      twoTypeBound p q < (p + q) / (2 - p - q) :=
  ⟨hm.walkSecondEigenvalueLE_of_two_type hd hconn A hA hq hqp.le hp hlamA hlamQ,
    twoTypeBound_lt_edgeAverage hq hqp hp⟩

/-- **Special cases of the `Φ` conjecture.** Under the hypotheses of
`IsTopWeight.walkSecondEigenvalueLE_of_two_type`, suppose moreover `p ≤ 111/400`, or `q = 0`. Then
the underlying graph has second eigenvalue at most `Φ(p, q)` (`edgePhi`), since
`β(p, q) ≤ Φ(p, q)` there (`twoTypeBound_le_edgePhi`, and `β(p, 0) = p/2 = Φ(p, 0)`).

If some edge `a b` with `a ∈ A` has link eigenvalues exactly `p` at `a` and `q` at `b`, then
`Φ(p, q)` is one of the terms of `max_{uv} Φ(lam u, lam v)`, so this proves the edge-interpolated
conjecture for such a complex. Beyond `p ≈ 0.27775` the bound `β` does not imply `Φ` for small
`q > 0`: there `Φ(p, q) < β(p, q)` (`exists_edgePhi_lt_twoTypeBound`). -/
theorem IsTopWeight.walkSecondEigenvalueLE_edgePhi_of_two_type (hm : K.IsTopWeight d m)
    (hd : 2 ≤ d) (hconn : K.IsConnected) (A : Set ι)
    (hA : ∀ a ∈ A, ∀ b ∈ A, linkWeightOf m ∅ a b = 0) {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p)
    (hp : p ≤ 1 / 2) (hcase : p ≤ 111 / 400 ∨ q = 0)
    (hlamA : ∀ z ∈ A, {z} ∈ K → WalkSecondEigenvalueLE (linkWeightOf m {z}) p)
    (hlamQ : ∀ z ∉ A, {z} ∈ K → WalkSecondEigenvalueLE (linkWeightOf m {z}) q) :
    WalkSecondEigenvalueLE (linkWeightOf m ∅) (edgePhi p q) := by
  have h := hm.walkSecondEigenvalueLE_of_two_type hd hconn A hA hq hqp hp hlamA hlamQ
  refine h.mono (linkWeightOf_nonneg hm.nonneg ∅) ?_
  rcases hcase with h1 | h0
  · exact twoTypeBound_le_edgePhi hq hqp h1
  · subst h0
    exact (twoTypeBound_zero hp).le.trans (edgePhi_zero p).symm.le

/-! ### Sharpness: the fan -/

/-- The **fan** on `Fin 5`: the cone with apex `0` over the path `1 2 3 4`, with the three
triangles `{0, 1, 2}`, `{0, 2, 3}`, `{0, 3, 4}`. -/
def fan : PreAbstractSimplicialComplex (Fin 5) where
  faces := {s | s.Nonempty ∧ (s ⊆ {0, 1, 2} ∨ s ⊆ {0, 2, 3} ∨ s ⊆ {0, 3, 4})}
  isRelLowerSet_faces := by
    rintro s ⟨hne, hs⟩
    refine ⟨hne, fun t hts ht => ⟨ht, ?_⟩⟩
    rcases hs with h | h | h
    · exact Or.inl (hts.trans h)
    · exact Or.inr (Or.inl (hts.trans h))
    · exact Or.inr (Or.inr (hts.trans h))

/-- The faces of `fan`, by definition. -/
theorem mem_fan {s : Finset (Fin 5)} :
    s ∈ fan ↔ s.Nonempty ∧ (s ⊆ {0, 1, 2} ∨ s ⊆ {0, 2, 3} ∨ s ⊆ {0, 3, 4}) := Iff.rfl

/-- The weight `m_t` on the triangles of `fan`: `1` on `{0, 1, 2}` and `{0, 3, 4}`, `t` on the
middle triangle `{0, 2, 3}`, and `0` on every other set. The apex link is the path `1 2 3 4` with
edge weights `1, t, 1`. -/
noncomputable def fanWeight (t : ℝ) (s : Finset (Fin 5)) : ℝ :=
  if s = {0, 1, 2} ∨ s = {0, 3, 4} then 1 else if s = {0, 2, 3} then t else 0

private theorem fan_eq_of_subset_three {s T : Finset (Fin 5)} (hT : #T = 3) (hs : #s = 2 + 1)
    (h : s ⊆ T) : s = T :=
  Finset.eq_of_subset_of_card_le h (by rw [hT, hs])

/-- For `t > 0`, `fanWeight t` is a top weight of the pure `2`-dimensional complex `fan`. For
`t ≤ 0` it is not: the middle triangle would get weight `≤ 0`. -/
theorem isTopWeight_fan {t : ℝ} (ht : 0 < t) : fan.IsTopWeight 2 (fanWeight t) where
  isPure := by
    intro σ hσ
    rcases (mem_fan.mp hσ).2 with h | h | h
    all_goals
      refine ⟨(card_le_card h).trans (by decide), _, mem_fan.mpr ⟨by decide, ?_⟩, h, by decide⟩
      simp
  exists_mem := ⟨{0, 1, 2}, mem_fan.mpr ⟨by decide, by simp⟩⟩
  pos := by
    intro F hF hFc
    rcases (mem_fan.mp hF).2 with h | h | h <;>
      · rw [fan_eq_of_subset_three (by decide) hFc h]
        unfold fanWeight
        simp (config := {decide := true}) [ht]
  eq_zero := by
    intro F hF
    unfold fanWeight
    split_ifs with h1 h2
    · rcases h1 with rfl | rfl
      · exact absurd ⟨mem_fan.mpr ⟨by decide, by simp⟩, by decide⟩ hF
      · exact absurd ⟨mem_fan.mpr ⟨by decide, by simp⟩, by decide⟩ hF
    · subst h2
      exact absurd ⟨mem_fan.mpr ⟨by decide, by simp⟩, by decide⟩ hF
    · rfl

/-- `fan` is connected: every point is joined to the apex `0`. -/
theorem isConnected_fan : fan.IsConnected := by
  rw [IsConnected, SimpleGraph.connected_iff]
  have hv : ∀ v : Fin 5, v ∈ fan.vertices := by
    intro v
    show {v} ∈ fan
    rw [mem_fan]
    fin_cases v <;> decide
  have hadj : ∀ a b : Fin 5, a ≠ b → ({a, b} : Finset (Fin 5)) ∈ fan →
      (fan.oneSkeleton.induce fan.vertices).Adj ⟨a, hv a⟩ ⟨b, hv b⟩ := by
    intro a b hab h
    rw [SimpleGraph.induce_adj, oneSkeleton, SimpleGraph.fromRel_adj]
    exact ⟨hab, Or.inl h⟩
  have hr : ∀ a : fan.vertices, (fan.oneSkeleton.induce fan.vertices).Reachable a ⟨0, hv 0⟩ := by
    rintro ⟨a, ha⟩
    fin_cases a
    · rfl
    · exact (hadj 1 0 (by decide) (by rw [mem_fan]; decide)).reachable
    · exact (hadj 2 0 (by decide) (by rw [mem_fan]; decide)).reachable
    · exact (hadj 3 0 (by decide) (by rw [mem_fan]; decide)).reachable
    · exact (hadj 4 0 (by decide) (by rw [mem_fan]; decide)).reachable
  exact ⟨fun a b => (hr a).trans (hr b).symm, ⟨⟨0, hv 0⟩⟩⟩

/-- `fanWeight t` as a sum of point masses on the three triangles. -/
theorem fanWeight_eq (t : ℝ) (F : Finset (Fin 5)) :
    fanWeight t F = (if F = {0, 1, 2} then 1 else 0) + (if F = {0, 2, 3} then t else 0) +
      (if F = {0, 3, 4} then 1 else 0) := by
  unfold fanWeight
  by_cases h1 : F = {0, 1, 2}
  · subst h1; simp (config := {decide := true})
  by_cases h2 : F = {0, 2, 3}
  · subst h2; simp (config := {decide := true})
  by_cases h3 : F = {0, 3, 4}
  · subst h3; simp (config := {decide := true})
  simp [h1, h2, h3]

/-- The weight of a set `s` in `fan`: the total weight of the triangles containing it. -/
theorem faceWeight_fanWeight (t : ℝ) (s : Finset (Fin 5)) :
    faceWeight (fanWeight t) s = (if s ⊆ {0, 1, 2} then 1 else 0) +
      (if s ⊆ {0, 2, 3} then t else 0) + (if s ⊆ {0, 3, 4} then 1 else 0) := by
  unfold faceWeight
  simp only [fanWeight_eq, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- Evaluation of the link weights of `fan`. -/
theorem linkWeightOf_fan (t : ℝ) (σ : Finset (Fin 5)) (u v : Fin 5) :
    linkWeightOf (fanWeight t) σ u v =
      if u ≠ v ∧ u ∉ σ ∧ v ∉ σ then
        (if insert u (insert v σ) ⊆ {0, 1, 2} then 1 else 0) +
          (if insert u (insert v σ) ⊆ {0, 2, 3} then t else 0) +
          (if insert u (insert v σ) ⊆ {0, 3, 4} then 1 else 0)
      else 0 := by
  rw [linkWeightOf, faceWeight_fanWeight]

/-- **The weighted path.** On the path `a b c e` with edge weights `1, t, 1` (degrees
`1, 1 + t, 1 + t, 1`), `t > 0`, the random walk has second eigenvalue at most `x = 1/(1 + t)`.
Certificate: on the mean-zero hyperplane, `2 (2 + t) (‖f‖² − (1 + t) Q f)` equals
`2 (1 + t)(a − b − c + e)² + (2 + t)(a − (1 + t) b + (1 + t) c − e)²`, the two terms being the
components along the eigenvectors for `−1/(1 + t)` and `−1`. -/
theorem path_ineq {t x : ℝ} (ht : 0 < t) (hx : x * (1 + t) = 1) {a b c e : ℝ}
    (hf : a + (1 + t) * b + (1 + t) * c + e = 0) :
    2 * (a * b + t * b * c + c * e) ≤
      x * (a ^ 2 + (1 + t) * b ^ 2 + (1 + t) * c ^ 2 + e ^ 2) := by
  have key : 2 * (2 + t) * ((a ^ 2 + (1 + t) * b ^ 2 + (1 + t) * c ^ 2 + e ^ 2)
      - (1 + t) * (2 * (a * b + t * b * c + c * e))) =
      2 * (1 + t) * (a - b - c + e) ^ 2 + (2 + t) * (a - (1 + t) * b + (1 + t) * c - e) ^ 2
        - t * (a + (1 + t) * b + (1 + t) * c + e) ^ 2 := by ring
  rw [hf] at key
  have h0 : 0 ≤ (a ^ 2 + (1 + t) * b ^ 2 + (1 + t) * c ^ 2 + e ^ 2)
      - (1 + t) * (2 * (a * b + t * b * c + c * e)) := by
    have : 0 ≤ 2 * (1 + t) * (a - b - c + e) ^ 2
        + (2 + t) * (a - (1 + t) * b + (1 + t) * c - e) ^ 2 := by positivity
    have h2 : 0 < 2 * (2 + t) := by positivity
    nlinarith
  have hx0 : 0 ≤ x := by nlinarith
  have e2 : x * (a ^ 2 + (1 + t) * b ^ 2 + (1 + t) * c ^ 2 + e ^ 2)
      - 2 * (a * b + t * b * c + c * e) = x * ((a ^ 2 + (1 + t) * b ^ 2 + (1 + t) * c ^ 2 + e ^ 2)
      - (1 + t) * (2 * (a * b + t * b * c + c * e))) := by
    linear_combination (2 * (a * b + t * b * c + c * e)) * hx
  nlinarith [mul_nonneg hx0 h0]

/-- **The apex link of `fan`** is the path `1 2 3 4` with weights `1, t, 1`, with second
eigenvalue at most `x = 1/(1 + t)` (`path_ineq`). -/
theorem walkSecondEigenvalueLE_fan_apex {t x : ℝ} (ht : 0 < t) (hx : x * (1 + t) = 1) :
    WalkSecondEigenvalueLE (linkWeightOf (fanWeight t) {0}) x := by
  intro f hf
  simp only [Fin.sum_univ_five, linkWeightOf_fan] at hf ⊢
  simp (config := {decide := true}) only [if_true, if_false] at hf ⊢
  norm_num at hf ⊢
  linarith [path_ineq ht hx (a := f 1) (b := f 2) (c := f 3) (e := f 4) (by linarith)]

/-- **The other links of `fan`** have second eigenvalue at most `0`: the links of `1` and `4` are
single edges (second eigenvalue `−1`) and the links of `2` and `3` are stars with centre `0`
(second eigenvalue `0`). -/
theorem walkSecondEigenvalueLE_fan_base {t : ℝ} (ht : 0 < t) {z : Fin 5} (hz : z ≠ 0) :
    WalkSecondEigenvalueLE (linkWeightOf (fanWeight t) {z}) 0 := by
  intro f hf
  simp only [Fin.sum_univ_five, linkWeightOf_fan] at hf ⊢
  fin_cases z
  · exact absurd rfl hz
  all_goals simp (config := {decide := true}) only [if_true, if_false] at hf ⊢
  all_goals norm_num at hf ⊢
  · have hl : f 0 + f 2 = 0 := by linarith
    have h2 := congrArg (fun y => f 0 * y) hl
    simp only [mul_zero] at h2
    nlinarith [sq_nonneg (f 0)]
  · have hl : (1 + t) * f 0 + f 1 + t * f 3 = 0 := by linarith
    have h2 := congrArg (fun y => f 0 * y) hl
    simp only [mul_zero] at h2
    nlinarith [sq_nonneg (f 0), mul_nonneg ht.le (sq_nonneg (f 0))]
  · have hl : (1 + t) * f 0 + t * f 2 + f 4 = 0 := by linarith
    have h2 := congrArg (fun y => f 0 * y) hl
    simp only [mul_zero] at h2
    nlinarith [sq_nonneg (f 0), mul_nonneg ht.le (sq_nonneg (f 0))]
  · have hl : f 0 + f 3 = 0 := by linarith
    have h2 := congrArg (fun y => f 0 * y) hl
    simp only [mul_zero] at h2
    nlinarith [sq_nonneg (f 0)]

/-- The eigenfunction of `fan`: `0` at the apex and `1 + t, 1, −1, −(1 + t)` along the path. It is
an eigenfunction both of the apex link (eigenvalue `1/(1 + t)`) and of the underlying graph
(eigenvalue `1/(2 (1 + t))`). -/
def fanEigen (t : ℝ) (v : Fin 5) : ℝ :=
  if v = 1 then 1 + t else if v = 2 then 1 else if v = 3 then -1 else if v = 4 then -(1 + t)
  else 0

private theorem fan_eigen_apex {t x : ℝ} (hx : x * (1 + t) = 1) (u : Fin 5) :
    ∑ v, linkWeightOf (fanWeight t) {0} u v * fanEigen t v =
      x * (∑ v, linkWeightOf (fanWeight t) {0} u v) * fanEigen t u := by
  simp only [Fin.sum_univ_five, linkWeightOf_fan, fanEigen]
  fin_cases u
  all_goals simp (config := {decide := true}) only [if_true, if_false]
  all_goals norm_num
  all_goals first
    | ring1
    | linear_combination hx
    | linear_combination (-1 : ℝ) * hx

private theorem fan_eigen {t x : ℝ} (hx : x * (1 + t) = 1) (u : Fin 5) :
    ∑ v, linkWeightOf (fanWeight t) ∅ u v * fanEigen t v =
      x / 2 * (∑ v, linkWeightOf (fanWeight t) ∅ u v) * fanEigen t u := by
  simp only [Fin.sum_univ_five, linkWeightOf_fan, fanEigen]
  fin_cases u
  all_goals simp (config := {decide := true}) only [if_true, if_false]
  all_goals norm_num
  all_goals first
    | ring1
    | linear_combination hx
    | linear_combination (-1 : ℝ) * hx

/-- A function with a nonzero value at a vertex of positive degree has positive norm. -/
private theorem fan_norm_pos {w : Fin 5 → Fin 5 → ℝ} (hnn : ∀ u v, 0 ≤ w u v) {h : Fin 5 → ℝ}
    (u : Fin 5) (hu : 0 < ∑ v, w u v) (hh : h u ≠ 0) : 0 < ∑ u, (∑ v, w u v) * h u ^ 2 :=
  Finset.sum_pos' (fun x _ => mul_nonneg (Finset.sum_nonneg fun v _ => hnn x v) (sq_nonneg _))
    ⟨u, Finset.mem_univ u, mul_pos hu (by positivity)⟩

/-- **The fan is sharp for the cone bound.** Let `t > 0` and `x = 1/(1 + t)` with `x ≤ 1/2`
(that is, `t ≥ 1`). In `fan` with weight `fanWeight t`:
* the apex link (the path `1 2 3 4` with weights `1, t, 1`) has second eigenvalue exactly `x`;
* every other vertex link has second eigenvalue at most `0`;
* the weighted underlying graph has second eigenvalue exactly `x/2 = β(x, 0)`, the value of
  `IsTopWeight.walkSecondEigenvalueLE_half_of_cone_type` for `A = {0}`;
* the edge-average bound is weaker: the largest edge average of the link bounds `x, 0` is `x/2`,
  and `x/2 < (x/2)/(1 − x/2) = x/(2 − x)`.

"Exactly `a`" is `IsLeast {μ | WalkSecondEigenvalueLE … μ} a`. The eigenfunction is `fanEigen t`.
For `t < 1` the apex link eigenvalue `x` exceeds `1/2`, outside the range of the theorem. -/
theorem fan_sharp {t x : ℝ} (ht : 0 < t) (hx : x * (1 + t) = 1) (hx2 : x ≤ 1 / 2) :
    IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf (fanWeight t) {0}) μ} x ∧
    (∀ z : Fin 5, z ≠ 0 → WalkSecondEigenvalueLE (linkWeightOf (fanWeight t) {z}) 0) ∧
    IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf (fanWeight t) ∅) μ} (x / 2) ∧
    twoTypeBound x 0 = x / 2 ∧ x / 2 < x / (2 - x) := by
  have hx0 : 0 < x := by nlinarith
  have hm := isTopWeight_fan ht
  have hapex := walkSecondEigenvalueLE_fan_apex ht hx
  have hbase := fun z (hz : z ≠ 0) => walkSecondEigenvalueLE_fan_base ht (z := z) hz
  have h1 : (1 + t) ≠ 0 := by positivity
  have hv1 : fanEigen t 1 ≠ 0 := by
    simp (config := {decide := true}) only [fanEigen, if_true]; positivity
  refine ⟨⟨hapex, fun μ hμ => ?_⟩, hbase, ⟨?_, fun μ hμ => ?_⟩, twoTypeBound_zero hx2, ?_⟩
  · -- the apex link: the eigenfunction `fanEigen t` has eigenvalue `x`
    by_contra hlt
    rw [not_le] at hlt
    refine not_walkSecondEigenvalueLE_of_eigen (linkWeightOf_symm _ {0}) (fan_eigen_apex hx)
      (by linarith) ?_ hlt hμ
    refine fan_norm_pos (linkWeightOf_nonneg hm.nonneg {0}) 1 ?_ hv1
    simp only [Fin.sum_univ_five, linkWeightOf_fan]
    simp (config := {decide := true}) only [if_true, if_false]
    norm_num
  · -- the upper bound, from the cone bound with `A = {0}`
    refine hm.walkSecondEigenvalueLE_half_of_cone_type le_rfl isConnected_fan {0} ?_ hx0.le hx2
      (fun z hz _ => ?_) (fun z hz _ => hbase z hz)
    · intro a ha b hb
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb, linkWeightOf_self]
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hapex
  · -- the lower bound, from the eigenfunction `fanEigen t`
    by_contra hlt
    rw [not_le] at hlt
    refine not_walkSecondEigenvalueLE_of_eigen (linkWeightOf_symm _ ∅) (fan_eigen hx)
      (by linarith) ?_ hlt hμ
    refine fan_norm_pos (linkWeightOf_nonneg hm.nonneg ∅) 1 ?_ hv1
    simp only [Fin.sum_univ_five, linkWeightOf_fan]
    simp (config := {decide := true}) only [if_true, if_false]
    norm_num
  · rw [lt_div_iff₀ (by linarith)]
    nlinarith

/-- **The cone bound `p/2` is attained for every `0 < p ≤ 1/2`.** For each such `p` there is a
top weight `m` on the connected pure `2`-dimensional complex `fan` (on five points) such that the
apex `0` is an independent set `A = {0}`, the apex link has second eigenvalue exactly `p`, every
other vertex link has second eigenvalue at most `0`, and the weighted underlying graph has second
eigenvalue exactly `p/2 = β(p, 0)`. So `IsTopWeight.walkSecondEigenvalueLE_half_of_cone_type`
(and hence `IsTopWeight.walkSecondEigenvalueLE_of_two_type` at `q = 0`) cannot be improved. The
weight is `1` on `{0, 1, 2}` and `{0, 3, 4}` and `t = (1 − p)/p` on `{0, 2, 3}`.

Degenerate values: `p = 0` would need `t = ∞`; for `p > 1/2` the theorem does not apply. -/
theorem exists_isLeast_fan {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 2) :
    ∃ m : Finset (Fin 5) → ℝ, fan.IsTopWeight 2 m ∧ fan.IsConnected ∧
      IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf m {0}) μ} p ∧
      (∀ z : Fin 5, z ≠ 0 → WalkSecondEigenvalueLE (linkWeightOf m {z}) 0) ∧
      IsLeast {μ | WalkSecondEigenvalueLE (linkWeightOf m ∅) μ} (p / 2) := by
  have ht : 0 < (1 - p) / p := div_pos (by linarith) hp0
  have hx : p * (1 + (1 - p) / p) = 1 := by field_simp; ring
  obtain ⟨h1, h2, h3, -, -⟩ := fan_sharp ht hx hp
  exact ⟨fanWeight ((1 - p) / p), isTopWeight_fan ht, isConnected_fan, h1, h2, h3⟩

end PreAbstractSimplicialComplex
