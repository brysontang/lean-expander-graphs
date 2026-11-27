/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.Basic

/-!
# Weighted graphs: the second eigenvalue of the random walk

High-dimensional expanders are defined through graphs that are weighted and not regular (the
links of a simplicial complex), so "second-largest eigenvalue" has to mean the second eigenvalue
of the *random walk* `M(u, v) = w(u, v) / deg(u)`. That operator is self-adjoint for the
degree-weighted inner product, with top eigenvalue `1` on constant functions, so its second
eigenvalue is `max ⟨f, Mf⟩ / ⟨f, f⟩` over `f` orthogonal to constants. We take that variational
description as the definition:

* `WalkSecondEigenvalueLE w lam`: the random walk on the weighted graph `w` has second
  eigenvalue at most `lam`.
* `SimpleGraph.walkSecondEigenvalueLE_adjMatrix_iff`: for a `d`-regular graph this is exactly
  `λ₂ ≤ lam · d`, so the definition agrees with the adjacency-eigenvalue one. **Proved.**
* `walkSecondEigenvalueLE_of_forall_eq_zero`: the degenerate case. A graph with no edges
  satisfies the bound for every `lam`.

For graphs that are not regular, `walkSecondEigenvalueLE_iff_secondEigenvalue_le` in
`Expanders/WalkSpectrum.lean` shows the definition is exactly a bound on the second-largest
eigenvalue of the symmetrised random-walk matrix, provided every degree is positive.
-/

open Finset Matrix

/-- The random walk on the weighted graph `w` (symmetric, nonnegative weights) has
**second-largest eigenvalue at most `lam`**: for every `f` with degree-weighted mean zero,
`Σ_{u,v} w(u,v) f(u) f(v) ≤ lam · Σ_u deg(u) f(u)²`, where `deg(u) = Σ_v w(u,v)`. -/
def WalkSecondEigenvalueLE {ι : Type*} [Fintype ι] (w : ι → ι → ℝ) (lam : ℝ) : Prop :=
  ∀ f : ι → ℝ, ∑ u, (∑ v, w u v) * f u = 0 →
    ∑ u, ∑ v, w u v * f u * f v ≤ lam * ∑ u, (∑ v, w u v) * f u ^ 2

theorem WalkSecondEigenvalueLE.mono {ι : Type*} [Fintype ι] {w : ι → ι → ℝ} {lam lam' : ℝ}
    (h : WalkSecondEigenvalueLE w lam) (hw : ∀ u v, 0 ≤ w u v) (hle : lam ≤ lam') :
    WalkSecondEigenvalueLE w lam' := fun f hf =>
  (h f hf).trans (mul_le_mul_of_nonneg_right hle
    (Finset.sum_nonneg fun u _ => mul_nonneg (Finset.sum_nonneg fun v _ => hw u v) (sq_nonneg _)))

/-- **Degenerate case: no edges.** If every weight is zero, both sides of the defining
inequality vanish, so the bound holds for every `lam`. An edgeless graph has no random walk and
so no second eigenvalue to constrain. Anything that uses `WalkSecondEigenvalueLE` as a notion of
expansion therefore needs a hypothesis ruling this case out: `trickling_down` assumes
connectivity, and `PreAbstractSimplicialComplex.exists_linkWeight_pos` shows that the links of a
pure complex which the definition of a high-dimensional expander quantifies over always have an
edge. -/
theorem walkSecondEigenvalueLE_of_forall_eq_zero {ι : Type*} [Fintype ι] {w : ι → ι → ℝ}
    (hw : ∀ u v, w u v = 0) (lam : ℝ) : WalkSecondEigenvalueLE w lam := by
  intro f _
  simp [hw]

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- **The variational definition agrees with the eigenvalue definition.** For a `d`-regular graph
with `d > 0`, the random walk has second eigenvalue at most `lam` exactly when the second
adjacency eigenvalue is at most `lam · d`. -/
theorem walkSecondEigenvalueLE_adjMatrix_iff [Nontrivial V] (hd : G.IsRegularOfDegree d)
    (hd0 : 0 < d) {lam : ℝ} :
    WalkSecondEigenvalueLE (fun u v => G.adjMatrix ℝ u v) lam ↔
      G.secondAdjEigenvalue ≤ lam * d := by
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hdeg : ∀ u, ∑ v, G.adjMatrix ℝ u v = d := by
    intro u
    have := congrFun (adjMatrix_mulVec_one_of_regular hd) u
    simpa [mulVec, dotProduct] using this
  have hquad : ∀ f : V → ℝ,
      ∑ u, ∑ v, G.adjMatrix ℝ u v * f u * f v = f ⬝ᵥ G.adjMatrix ℝ *ᵥ f := by
    intro f
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  have hnorm : ∀ f : V → ℝ, ∑ u, (d : ℝ) * f u ^ 2 = d * (f ⬝ᵥ f) := by
    intro f
    simp only [dotProduct, Finset.mul_sum, sq]
  unfold WalkSecondEigenvalueLE
  constructor
  · intro h
    obtain ⟨x, hx, hx0, hle⟩ := exists_sum_eq_zero_secondAdjEigenvalue_mul_le G
    have h1 := h x (by simp only [hdeg, ← Finset.mul_sum, hx0, mul_zero])
    simp only [hdeg, hquad, hnorm] at h1
    have hpos := Matrix.IsHermitian.dotProduct_self_pos hx
    have h2 : G.secondAdjEigenvalue * (x ⬝ᵥ x) ≤ lam * d * (x ⬝ᵥ x) := by linarith
    exact le_of_mul_le_mul_right h2 hpos
  · intro h f hf
    simp only [hdeg, ← Finset.mul_sum] at hf
    simp only [hdeg, hquad, hnorm]
    have hf0 : ∑ v, f v = 0 := (mul_eq_zero.mp hf).resolve_left hd0'.ne'
    have h1 := dotProduct_adjMatrix_mulVec_le hd hf0
    have hff : 0 ≤ f ⬝ᵥ f := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right h hff]

end SimpleGraph
