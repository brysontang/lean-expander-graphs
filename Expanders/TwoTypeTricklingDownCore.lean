/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.TwoTypeTricklingDownAlgebra
import Expanders.TwoTypeTricklingDownLocal
import Expanders.EdgeAverageTricklingDownCore
import Expanders.TricklingDownEquality

/-!
# Two-type trickling down, part 3: triangle weights

This file proves the two-type bound for an abstract triangle weight
`T : ι → ι → ι → ℝ` (`EdgeAverageTricklingDown.IsTriangleWeight`), with underlying graph `w`,
`Σ_c T a b c = k · w a b`, `k > 0`. The link of `z` is the weighted graph `T z`.

## The theorem (`EdgeAverageTricklingDown.IsTriangleWeight.walkSecondEigenvalueLE_of_two_type`)

Let `w` be connected, let `A` be a set of vertices with no edge of `w` inside it, and let
`0 ≤ q ≤ p ≤ 1/2`. If the link of every `z ∈ A` has second eigenvalue at most `p` and the link of
every `z ∉ A` has second eigenvalue at most `q`, then `w` has second eigenvalue at most
`β(p, q)` (`twoTypeBound`).

## Proof

Suppose not. The spectral theorem (`exists_walk_eigenfunction_of_lt`) gives an eigenfunction `g`
of `w` with eigenvalue `γ > β`, not orthogonal to the test function. Then:
1. `γ ≤ 1`, and `γ ≠ 1` since `w` is connected; so `g` has mean zero. The edge-average theorem
   with every link bound replaced by `p` (Oppenheim's step) gives `γ ≤ p/(1 − p)`. Since
   `β ≥ p/2`, `(p, γ)` lies in the region of `exists_good`, and `N(γ) > 0`.
2. Let `h a b` be the average of `g` over the link of the edge `a b`. At every vertex `a` apply
   the local inequality: `local_garland_mean` with weight `aP` if `a ∈ A`, `local_quadratic_mean`
   with weight `1` otherwise. Add the vertex identity `Σ T · c(a) g a (g b − γ g a) = 0` and the
   edge identity `Σ T · G(a, b) g a (g c − h a b) = 0`. The result is `Σ_{a b c} T a b c · J ≥ 0`
   with `J = triJ`.
3. Relabelling the triple sum six ways, `6 Σ T J = Σ T · q_T` with `q_T = triQ` the symmetrised
   form. Every triangle of positive weight has at most one vertex in `A`, so after a relabelling
   `q_T` is a QQQ or a PQQ form, which is `≤ 0` (`triQ_QQQ_nonpos`, `triQ_PQQ_nonpos`).
4. Hence every `q_T` vanishes, and by rigidity (`eq_of_triQ_QQQ_eq_zero`,
   `eq_zero_of_triQ_PQQ_eq_zero`) `g` is equal at the ends of every edge. Connectivity makes `g`
   constant, so `g` is orthogonal to the mean-zero test function: a contradiction.

## Theorems
* `sum_tri_swap12`, `sum_tri_swap23`, `sum_tri_cycle`, `sum_tri_cycle'`, `sum_tri_swap13`:
  relabelling a triple sum against a triangle weight. **Proved.**
* `EdgeAverageTricklingDown.IsTriangleWeight.walkSecondEigenvalueLE_of_two_type`: the theorem.
  **Proved.**
-/

open Finset

namespace TwoTypeTricklingDown

open EdgeAverageTricklingDown TwoTypeMultipliers

variable {ι : Type*} [Fintype ι] {T : ι → ι → ι → ℝ}

/-! ### Relabelling triple sums -/

/-- Relabelling `a ↔ b` in a triple sum against a triangle weight. -/
theorem sum_tri_swap12 (hT : IsTriangleWeight T) (F : ι → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, T a b c * F b a c = ∑ a, ∑ b, ∑ c, T a b c * F a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => by rw [hT.swap12 b a c]

/-- Relabelling `b ↔ c` in a triple sum against a triangle weight. -/
theorem sum_tri_swap23 (hT : IsTriangleWeight T) (F : ι → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, T a b c * F a c b = ∑ a, ∑ b, ∑ c, T a b c * F a b c := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [hT.swap23 a c b]

/-- Relabelling `(a, b, c) ↦ (b, c, a)` in a triple sum against a triangle weight. -/
theorem sum_tri_cycle (hT : IsTriangleWeight T) (F : ι → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, T a b c * F b c a = ∑ a, ∑ b, ∑ c, T a b c * F a b c :=
  (sum_tri_swap12 hT (fun x y z => F x z y)).trans (sum_tri_swap23 hT F)

/-- Relabelling `(a, b, c) ↦ (c, a, b)` in a triple sum against a triangle weight. -/
theorem sum_tri_cycle' (hT : IsTriangleWeight T) (F : ι → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, T a b c * F c a b = ∑ a, ∑ b, ∑ c, T a b c * F a b c :=
  (sum_tri_swap23 hT (fun x y z => F y x z)).trans (sum_tri_swap12 hT F)

/-- Relabelling `a ↔ c` in a triple sum against a triangle weight. -/
theorem sum_tri_swap13 (hT : IsTriangleWeight T) (F : ι → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, T a b c * F c b a = ∑ a, ∑ b, ∑ c, T a b c * F a b c :=
  (sum_tri_cycle hT (fun x y z => F y x z)).trans (sum_tri_swap12 hT F)

/-- **Six relabellings.** Six times `Σ T F` is `Σ T` times the sum of `F` over the six
orderings of its arguments. -/
theorem six_mul_sum_tri (hT : IsTriangleWeight T) (F : ι → ι → ι → ℝ) :
    6 * ∑ a, ∑ b, ∑ c, T a b c * F a b c =
      ∑ a, ∑ b, ∑ c, T a b c * (F a b c + F a c b + F b a c + F b c a + F c a b + F c b a) := by
  have e : ∀ a b c, T a b c * (F a b c + F a c b + F b a c + F b c a + F c a b + F c b a) =
      T a b c * F a b c + T a b c * F a c b + T a b c * F b a c + T a b c * F b c a
        + T a b c * F c a b + T a b c * F c b a := fun a b c => by ring
  simp only [e, Finset.sum_add_distrib]
  rw [sum_tri_swap23 hT F, sum_tri_swap12 hT F, sum_tri_cycle hT F, sum_tri_cycle' hT F,
    sum_tri_swap13 hT F]
  ring

/-- A triple sum of nonpositive terms that is `≥ 0` has every term `0`. -/
private theorem eq_zero_of_sum_tri {F : ι → ι → ι → ℝ} (hle : ∀ a b c, F a b c ≤ 0)
    (hsum : 0 ≤ ∑ a, ∑ b, ∑ c, F a b c) (a b c : ι) : F a b c = 0 := by
  have h2 : ∀ a b, ∑ c, F a b c ≤ 0 := fun a b => Finset.sum_nonpos fun c _ => hle a b c
  have h1 : ∀ a, ∑ b, ∑ c, F a b c ≤ 0 := fun a => Finset.sum_nonpos fun b _ => h2 a b
  have h0 : ∑ a, ∑ b, ∑ c, F a b c = 0 :=
    le_antisymm (Finset.sum_nonpos fun a _ => h1 a) hsum
  have e1 := (Finset.sum_eq_zero_iff_of_nonpos fun a _ => h1 a).mp h0 a (Finset.mem_univ a)
  have e2 := (Finset.sum_eq_zero_iff_of_nonpos fun b _ => h2 a b).mp e1 b (Finset.mem_univ b)
  exact (Finset.sum_eq_zero_iff_of_nonpos fun c _ => hle a b c).mp e2 c (Finset.mem_univ c)

/-! ### The theorem -/

/-- **Two-type trickling down, for a triangle weight.** Let `T` be a triangle weight and `w` a
weighted graph with `Σ_c T a b c = k · w a b`, `k > 0`. Suppose:
* `w` is connected: a function constant along its edges is constant on the vertices of positive
  degree;
* `A` is a set of vertices with no edge of `w` inside it (`w a b = 0` for `a, b ∈ A`);
* `0 ≤ q ≤ p ≤ 1/2`;
* the link `T z` of every `z ∈ A` has second eigenvalue at most `p`, and that of every `z ∉ A`
  at most `q`.

Then the random walk on `w` has second eigenvalue at most `β(p, q)` (`twoTypeBound`).

Degenerate cases:
* `w` with no edges: the conclusion is vacuous (`walkSecondEigenvalueLE_of_forall_eq_zero`).
* `A = ∅`, or `q = p`: the hypotheses are Oppenheim's, and `β(p, p) = p/(1 − p)`
  (`twoTypeBound_self`); the proof uses Oppenheim's bound (in the form of the edge-average theorem
  with constant link bounds) as an input, so this case is not a new proof of it.
* `q = 0`: `β(p, 0) = p/2` (`twoTypeBound_zero`), the cone value.
* No connectivity of the links is assumed: a bound `< 1` already forces it.
* Vertices in no triangle carry no condition beyond the link bound, which is then vacuous.
* A vertex whose link is a single edge has link eigenvalue `−1`, which satisfies either bound.

Without connectivity of `w` the conclusion fails (two disjoint triangles: `μ = 1`). -/
theorem _root_.EdgeAverageTricklingDown.IsTriangleWeight.walkSecondEigenvalueLE_of_two_type
    (hT : IsTriangleWeight T) {w : ι → ι → ℝ} {k : ℝ}
    (hk : 0 < k) (hw : ∀ a b, ∑ c, T a b c = k * w a b)
    (hconn : ∀ F : ι → ℝ, (∀ u v, 0 < w u v → F u = F v) →
      ∀ u v, 0 < ∑ x, w u x → 0 < ∑ x, w v x → F u = F v)
    (A : Set ι) (hA : ∀ a ∈ A, ∀ b ∈ A, w a b = 0) {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p)
    (hp : p ≤ 1 / 2) (hlamA : ∀ z ∈ A, WalkSecondEigenvalueLE (T z) p)
    (hlamQ : ∀ z ∉ A, WalkSecondEigenvalueLE (T z) q) :
    WalkSecondEigenvalueLE w (twoTypeBound p q) := by
  classical
  intro f hf
  by_contra hcon
  push Not at hcon
  -- the graph `w`
  have hwk : ∀ a b, w a b = (∑ c, T a b c) / k := fun a b => by
    rw [hw, mul_div_cancel_left₀ _ hk.ne']
  have hwsymm : ∀ a b, w a b = w b a := fun a b => by
    rw [hwk, hwk]; congr 1; exact Finset.sum_congr rfl fun c _ => hT.swap12 a b c
  have hwnn : ∀ a b, 0 ≤ w a b := fun a b => by
    rw [hwk]; exact div_nonneg (Finset.sum_nonneg fun c _ => hT.nonneg a b c) hk.le
  have hD0 : ∀ u, 0 ≤ ∑ v, w u v := fun u => Finset.sum_nonneg fun v _ => hwnn u v
  -- an eigenfunction above `β`
  obtain ⟨g, γ, hγ, heig, hgf⟩ := exists_walk_eigenfunction_of_lt hwsymm hwnn hcon
  -- `g` is not constant on the vertices of positive degree
  have hnc : ¬ ∀ u v, 0 < ∑ x, w u x → 0 < ∑ x, w v x → g u = g v := by
    intro hc
    obtain ⟨u₀, -, hu₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hgf
    have hDu₀ : 0 < ∑ v, w u₀ v :=
      lt_of_le_of_ne (hD0 u₀) (Ne.symm fun h => hu₀ (by rw [h]; ring))
    apply hgf
    have hconst : ∀ u, (∑ v, w u v) * g u * f u = g u₀ * ((∑ v, w u v) * f u) := by
      intro u
      rcases (hD0 u).eq_or_lt with h0 | h0
      · rw [← h0]; ring
      · rw [hc u u₀ h0 hDu₀]; ring
    simp only [hconst, ← Finset.mul_sum, hf, mul_zero]
  have hg2 : 0 < ∑ u, (∑ v, w u v) * g u ^ 2 := by
    obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hgf
    have hDu : ∑ v, w u v ≠ 0 := fun h => hu (by rw [h]; ring)
    have hgu : g u ≠ 0 := fun h => hu (by rw [h]; ring)
    exact Finset.sum_pos' (fun v _ => mul_nonneg (hD0 v) (sq_nonneg _))
      ⟨u, Finset.mem_univ u, mul_pos (lt_of_le_of_ne (hD0 u) (Ne.symm hDu)) (by positivity)⟩
  have hγ1 : γ ≤ 1 := eigen_le_one hwsymm hwnn heig hg2
  have hγne : γ ≠ 1 := by
    rintro rfl
    exact hnc (eq_of_eigen_one hwsymm hwnn hconn heig)
  have hmean : ∑ u, (∑ v, w u v) * g u = 0 := sum_deg_mul_eq_zero_of_eigen hwsymm heig hγne
  have hQg := sum_mul_mul_eq_of_eigen heig
  -- the Oppenheim cut `γ ≤ p / (1 − p)`
  have hp0 : 0 ≤ p := hq.trans hqp
  have hcut : γ * (1 - p) ≤ p := by
    have hlam : ∀ z, WalkSecondEigenvalueLE (T z) ((fun _ => p) z) := fun z => by
      by_cases hz : z ∈ A
      · exact hlamA z hz
      · exact (hlamQ z hz).mono (hT.nonneg z) hqp
    have hO := hT.walkSecondEigenvalueLE_of_edge_average hk hw hconn hlam
      (fun z h1 => absurd h1 (not_le.mpr (by linarith))) (by linarith : p < 1)
      (fun u v _ => by linarith)
    have h1 := hO g hmean
    rw [hQg] at h1
    have h2 : γ ≤ p / (1 - p) := le_of_mul_le_mul_right h1 hg2
    rwa [le_div_iff₀ (by linarith)] at h2
  -- the region of the certificate
  have hq1 : q < 1 := by linarith
  have hhalf := half_le_twoTypeBound hp0 hp hq hq1
  have hN := twoTypeN_pos_of_lt hp0 hp hq hq1 hγ
  have hpp : 0 < p := by
    rcases hp0.eq_or_lt with h | h
    · subst h
      norm_num at hcut hhalf
      linarith
    · exact h
  have hγ1' : γ < 1 := lt_of_le_of_ne hγ1 hγne
  obtain ⟨M, hM⟩ := exists_good hpp hp (by linarith : p / 2 ≤ γ) hcut hγ1' hN
  -- the edge averages `h a b` of `g`
  obtain ⟨h, hhdef⟩ : ∃ h : ι → ι → ℝ,
      h = fun a b => (∑ c, T a b c * g c) / ∑ c, T a b c := ⟨_, rfl⟩
  have hh : ∀ a b, ∑ c, T a b c * g c = h a b * ∑ c, T a b c := by
    intro a b
    rcases (Finset.sum_nonneg fun c _ => hT.nonneg a b c :
        (0 : ℝ) ≤ ∑ c, T a b c).eq_or_lt with h0 | h0
    · have hT0 : ∀ c, T a b c = 0 := fun c =>
        (Finset.sum_eq_zero_iff_of_nonneg fun c _ => hT.nonneg a b c).mp h0.symm c
          (Finset.mem_univ c)
      simp [hT0]
    · rw [hhdef]; exact (div_mul_cancel₀ _ h0.ne').symm
  have hhsymm : ∀ a b, h a b = h b a := fun a b => by
    rw [hhdef]
    simp only
    congr 1 <;> exact Finset.sum_congr rfl fun c _ => by rw [hT.swap12]
  -- the mean of `g` on the link of `a` is `γ g a`
  have hmloc : ∀ a, ∑ b, (∑ c, T a b c) * g b = (γ * g a) * ∑ b, ∑ c, T a b c := by
    intro a
    have e1 : ∑ b, (∑ c, T a b c) * g b = k * ∑ b, w a b * g b := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [hw]; ring
    have e2 : ∑ b, ∑ c, T a b c = k * ∑ b, w a b := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => hw a b
    rw [e1, e2, heig a]
    ring
  -- the integrand and its three parts
  obtain ⟨J, hJ⟩ : ∃ J : ι → ι → ι → ℝ, J = fun a b c =>
      triJ M p q γ (decide (a ∈ A)) (decide (b ∈ A)) (g a) (g b) (g c) (h a b) := ⟨_, rfl⟩
  obtain ⟨Lf, hLf⟩ : ∃ Lf : ι → ι → ι → ℝ, Lf = fun a b c =>
      if a ∈ A then M.aP * (p * g b ^ 2 - g b * g c - (p - 1) * γ ^ 2 * g a ^ 2)
      else q * g b ^ 2 + (q - 1) * g b * g c - h a b ^ 2 - 2 * (q - 1) * γ ^ 2 * g a ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc : ι → ℝ, cc = fun a => if a ∈ A then M.cP else M.cQ := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ι → ι → ℝ, G = fun a b =>
      if a ∈ A then (if b ∈ A then 0 else M.gPQ) else (if b ∈ A then M.gQP else M.gQQ) :=
    ⟨_, rfl⟩
  have hJsplit : ∀ a b c, J a b c =
      Lf a b c + cc a * g a * (g b - γ * g a) + G a b * g a * (g c - h a b) := by
    intro a b c
    simp only [hJ, hLf, hcc, hG, triJ, decide_eq_true_eq]
    split_ifs <;> ring
  -- the local inequalities
  have hL : ∀ a, 0 ≤ ∑ b, ∑ c, T a b c * Lf a b c := by
    intro a
    have s2 : ∀ x : ι → ℝ, ∑ b, ∑ c, T a b c * x b = ∑ b, (∑ c, T a b c) * x b := fun x =>
      Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm
    by_cases ha : a ∈ A
    · have hloc := local_garland_mean (hT.swap23 a) (hlamA a ha) g (γ * g a) (hmloc a)
      have e : ∀ b c, T a b c * Lf a b c = M.aP * p * (T a b c * g b ^ 2)
          - M.aP * (T a b c * g b * g c) - M.aP * (p - 1) * γ ^ 2 * g a ^ 2 * T a b c := by
        intro b c
        simp only [hLf, if_pos ha]
        ring
      simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [s2 (fun b => g b ^ 2)]
      have := mul_nonneg hM.aP_nonneg (by linarith : (0 : ℝ) ≤
        p * ∑ b, (∑ c, T a b c) * g b ^ 2 - ∑ b, ∑ c, T a b c * g b * g c
          - (p - 1) * (γ * g a) ^ 2 * ∑ b, ∑ c, T a b c)
      nlinarith
    · have hloc := local_quadratic_mean (hT.swap23 a) (hT.nonneg a) (hlamQ a ha)
        (by linarith) g (h a) (γ * g a) (hh a) (hmloc a)
      have e : ∀ b c, T a b c * Lf a b c = q * (T a b c * g b ^ 2)
          + (q - 1) * (T a b c * g b * g c) - T a b c * h a b ^ 2
          - 2 * (q - 1) * γ ^ 2 * g a ^ 2 * T a b c := by
        intro b c
        simp only [hLf, if_neg ha]
        ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [s2 (fun b => g b ^ 2), s2 (fun b => h a b ^ 2)]
      nlinarith
  -- the vertex identity
  have hV : ∀ a, ∑ b, ∑ c, T a b c * (cc a * g a * (g b - γ * g a)) = 0 := by
    intro a
    have e : ∀ b, ∑ c, T a b c * (cc a * g a * (g b - γ * g a)) =
        k * cc a * g a * (w a b * g b) - k * cc a * g a * γ * g a * w a b := by
      intro b
      rw [← Finset.sum_mul, hw]
      ring
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [heig a]
    ring
  -- the edge identity
  have hE : ∀ a b, ∑ c, T a b c * (G a b * g a * (g c - h a b)) = 0 := by
    intro a b
    have e : ∀ c, T a b c * (G a b * g a * (g c - h a b)) =
        G a b * g a * (T a b c * g c) - G a b * g a * h a b * T a b c := fun c => by ring
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hh a b]
    ring
  -- so the integrand has nonnegative expectation
  have hJ0 : 0 ≤ ∑ a, ∑ b, ∑ c, T a b c * J a b c := by
    have e : ∀ a, ∑ b, ∑ c, T a b c * J a b c = ∑ b, ∑ c, T a b c * Lf a b c
        + ∑ b, ∑ c, T a b c * (cc a * g a * (g b - γ * g a))
        + ∑ b, ∑ c, T a b c * (G a b * g a * (g c - h a b)) := by
      intro a
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by
        rw [hJsplit]; ring
    simp only [e, hV, hE, Finset.sum_const_zero, add_zero]
    exact Finset.sum_nonneg fun a _ => hL a
  -- the symmetrised per-triangle forms
  obtain ⟨tq, htq⟩ : ∃ tq : ι → ι → ι → ℝ, tq = fun a b c =>
      triQ M p q γ (decide (a ∈ A)) (decide (b ∈ A)) (decide (c ∈ A)) (g a) (g b) (g c)
        (h a b) (h a c) (h b c) := ⟨_, rfl⟩
  have hsymJ : ∀ a b c, J a b c + J a c b + J b a c + J b c a + J c a b + J c b a = tq a b c := by
    intro a b c
    simp only [hJ, htq, triQ]
    rw [hhsymm b a, hhsymm c a, hhsymm c b]
  have htq0 : 0 ≤ ∑ a, ∑ b, ∑ c, T a b c * tq a b c := by
    have := six_mul_sum_tri hT J
    simp only [hsymJ] at this
    linarith
  -- at most one vertex of a triangle lies in `A`
  have hTpos : ∀ a b c, a ∈ A → b ∈ A → T a b c = 0 := by
    intro a b c ha hb
    have h0 : ∑ x, T a b x = 0 := by rw [hw, hA a ha b hb, mul_zero]
    exact (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hT.nonneg a b x).mp h0 c
      (Finset.mem_univ c)
  -- every per-triangle form of a triangle of positive weight is `≤ 0`, with rigidity
  have htri : ∀ a b c, 0 < T a b c → tq a b c ≤ 0 ∧ (tq a b c = 0 → g a = g b) := by
    intro a b c hpos
    simp only [htq]
    by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> by_cases hc : c ∈ A
    · exact absurd (hTpos a b c ha hb) hpos.ne'
    · exact absurd (hTpos a b c ha hb) hpos.ne'
    · exact absurd (by rw [hT.swap23]; exact hTpos a c b ha hc) hpos.ne'
    · rw [decide_eq_true ha, decide_eq_false hb, decide_eq_false hc]
      refine ⟨triQ_PQQ_nonpos hM _ _ _ _ _ _, fun h0 => ?_⟩
      obtain ⟨e0, e1, -⟩ := eq_zero_of_triQ_PQQ_eq_zero hM h0
      rw [e0, e1]
    · exact absurd (by rw [hT.cycle]; exact hTpos b c a hb hc) hpos.ne'
    · rw [decide_eq_false ha, decide_eq_true hb, decide_eq_false hc, triQ_swap01]
      refine ⟨triQ_PQQ_nonpos hM _ _ _ _ _ _, fun h0 => ?_⟩
      obtain ⟨e0, e1, -⟩ := eq_zero_of_triQ_PQQ_eq_zero hM h0
      rw [e0, e1]
    · rw [decide_eq_false ha, decide_eq_false hb, decide_eq_true hc, triQ_swap02]
      refine ⟨triQ_PQQ_nonpos hM _ _ _ _ _ _, fun h0 => ?_⟩
      obtain ⟨e0, e1, e2⟩ := eq_zero_of_triQ_PQQ_eq_zero hM h0
      rw [e1, e2]
    · rw [decide_eq_false ha, decide_eq_false hb, decide_eq_false hc]
      exact ⟨triQ_QQQ_nonpos hM _ _ _ _ _ _, fun h0 => (eq_of_triQ_QQQ_eq_zero hM h0).1⟩
  -- every term vanishes
  have hterm : ∀ a b c, T a b c * tq a b c = 0 := by
    refine eq_zero_of_sum_tri (fun a b c => ?_) htq0
    rcases (hT.nonneg a b c).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos h0.le (htri a b c h0).1
  -- so `g` is constant along every edge, hence constant: a contradiction
  apply hnc
  refine hconn g fun u v huv => ?_
  have hd : 0 < ∑ c, T u v c := by rw [hw]; exact mul_pos hk huv
  obtain ⟨c0, -, hc0⟩ := (Finset.sum_pos_iff_of_nonneg fun c _ => hT.nonneg u v c).mp hd
  have h0 : tq u v c0 = 0 := (mul_eq_zero.mp (hterm u v c0)).resolve_left hc0.ne'
  exact (htri u v c0 hc0).2 h0

end TwoTypeTricklingDown
