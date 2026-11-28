/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.TwoTypeTricklingDownCore
import Expanders.EdgeAverageTricklingDown

/-!
# Two-type trickling down, part 4: one vertex of `A` in every triangle

A second certificate of the same kind as the two-type one, for the more special class in which
**every triangle has exactly one vertex in `A`**: if the links of the vertices of `A` have second
eigenvalue at most `p`, the other links at most `0`, and `0 ≤ p < p* ≈ 0.7551` (the root in
`(0, 1)` of `2p³ + 3p² − 14p + 8`), then the underlying graph has second eigenvalue at most
`p/2`. Unlike `IsTopWeight.walkSecondEigenvalueLE_half_of_cone_type`, `p` may exceed `1/2`.

## Proof
Let `g` be an eigenfunction with eigenvalue `γ > p/2`. The edge-average theorem gives
`γ ≤ p/(2 − p)`, because every edge joins a vertex of `A` to one outside (edge average `p/2`) or
two vertices outside (`0`). On `(p/2, p/(2 − p)]` the following certificate excludes `γ`:
* at the vertices of `A` the polynomial `(p − v)(r − v)` (`local_prod_mean`), with `r` slightly
  above `2γ`; at the other vertices `−v (1 + v)` (`local_quadratic_mean` with `q = 0`);
* the vertex identity with weights `2 − p − r` on `A` and `p + r` off `A`; no edge identity.
Each triangle `a b c` with `a ∈ A` then has the diagonal form
`q_T = α f_a² + β (f_b² + f_c²) − 2 h_bc²` (`oneQ_PQQ`), where `β = (2γ − p)(2γ − r) < 0` and
`α = −2γ ((1 − p)(1 − r) γ + 2 − p − r)`. At `r = 2γ` the bracket is
`F(γ) = 2 − p − 2 (1 − p) γ² − (1 + p) γ`, and `(2 − p)² F(p/(2 − p)) = 2p³ + 3p² − 14p + 8`, so
`F(γ) > 0` on the whole interval when `p < p*`; `r = 2γ + F(γ) / (2 (1 + (1 − p) γ))` keeps half
of it. So every `q_T < 0` unless `g` vanishes on the triangle, which contradicts
`Σ m(T) q_T ≥ 0`.

## Remarks
* The threshold `p*` comes from this certificate, not from the class. A structural argument
  reported by an independent check of this result (not formalized here) shows that the class
  consists of the joins `A * G` with product weights, where `μ = max(λ₂(G)/2, …) ≤ p/2` for every
  `p < 1`.
* At `p ≤ 1/2` the statement is also a case of the cone bound
  (`IsTopWeight.walkSecondEigenvalueLE_half_of_cone_type`).

## Theorems
* `local_prod_mean`: `⟨f, (p − P)(r − P) f⟩ ≥ (p − 1)(r − 1) m² D` for `r ≥ p`. **Proved.**
* `oneJ`, `oneQ`, `oneQ_PQQ`, `oneQ_PQQ_nonpos`, `eq_zero_of_oneQ_PQQ_eq_zero`: the per-triangle
  form and its rigidity. **Proved.**
* `EdgeAverageTricklingDown.IsTriangleWeight.walkSecondEigenvalueLE_half_of_one_apex`: the
  theorem for a triangle weight. **Proved.**
* `PreAbstractSimplicialComplex.IsTopWeight.walkSecondEigenvalueLE_half_of_one_apex`: the theorem
  for a weighted pure complex. **Proved.**
-/

open Finset

namespace TwoTypeTricklingDown

open EdgeAverageTricklingDown

variable {ι : Type*} [Fintype ι]

/-! ### The local inequality for `(p − v)(r − v)` -/

/-- **The local inequality for `(p − v)(r − v)`.** Let `T` be symmetric and nonnegative with
random-walk second eigenvalue at most `p`, and `p ≤ r`. Let `f` have degree-weighted mean `m` and
walk average `a`. Then `(p − 1)(r − 1) m² D ≤ p r Σ d f² − (p + r) Σ T f f + Σ d a²`.

On the mean-zero part `g` this is `⟨g, (p − P)(r − P) g⟩ = ‖p g − P g‖² + (r − p) ⟨g, (p − P) g⟩`,
a square plus a multiple of the Garland inequality; no spectral theorem is used. The hypothesis
`p ≤ r` is what makes the polynomial nonnegative on `[−1, p]`. -/
theorem local_prod_mean {T : ι → ι → ℝ} (hsymm : ∀ b c, T b c = T c b)
    (hnn : ∀ b c, 0 ≤ T b c) {p r : ℝ} (hlam : WalkSecondEigenvalueLE T p) (hpr : p ≤ r)
    (f a : ι → ℝ) (m : ℝ) (ha : ∀ b, ∑ c, T b c * f c = a b * ∑ c, T b c)
    (hm : ∑ b, (∑ c, T b c) * f b = m * ∑ b, ∑ c, T b c) :
    (p - 1) * (r - 1) * m ^ 2 * ∑ b, ∑ c, T b c ≤
      p * r * ∑ b, (∑ c, T b c) * f b ^ 2 - (p + r) * ∑ b, ∑ c, T b c * f b * f c
        + ∑ b, (∑ c, T b c) * a b ^ 2 := by
  obtain ⟨D, hD⟩ : ∃ D, D = ∑ b, ∑ c, T b c := ⟨_, rfl⟩
  rw [← hD] at hm ⊢
  -- the centred functions
  have s1 : ∑ b, ∑ c, T b c * f b = m * D := by
    rw [← hm]; exact Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm
  have s2 : ∑ b, ∑ c, T b c * f c = m * D := by
    rw [Finset.sum_comm, ← s1]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [hsymm c b]
  have sa : ∑ b, (∑ c, T b c) * a b = m * D := by
    rw [← s2]
    exact Finset.sum_congr rfl fun b _ => by rw [ha b]; ring
  have hmean : ∑ b, (∑ c, T b c) * (f b - m) = 0 := by
    have e : ∑ b, (∑ c, T b c) * (f b - m) = ∑ b, (∑ c, T b c) * f b - m * D := by
      rw [hD, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e, hm]; ring
  -- Garland at the centred function
  have hG := hlam (fun b => f b - m) hmean
  -- the square `‖p (f − m) − (a − m)‖² ≥ 0`
  have hsq : 0 ≤ ∑ b, (∑ c, T b c) * (p * (f b - m) - (a b - m)) ^ 2 :=
    Finset.sum_nonneg fun b _ =>
      mul_nonneg (Finset.sum_nonneg fun c _ => hnn b c) (sq_nonneg _)
  -- expansions
  have hfa : ∑ b, (∑ c, T b c) * f b * a b = ∑ b, ∑ c, T b c * f b * f c := by
    refine Finset.sum_congr rfl fun b _ => ?_
    have : ∑ c, T b c * f b * f c = f b * ∑ c, T b c * f c := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
    rw [this, ha b]; ring
  have eQ : ∑ b, ∑ c, T b c * (f b - m) * (f c - m) =
      ∑ b, ∑ c, T b c * f b * f c - m ^ 2 * D := by
    have e : ∀ b c, T b c * (f b - m) * (f c - m) =
        T b c * f b * f c - m * (T b c * f b) - m * (T b c * f c) + m ^ 2 * T b c :=
      fun b c => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [s1, s2, ← hD]
    ring
  have eN : ∑ b, (∑ c, T b c) * (f b - m) ^ 2 = ∑ b, (∑ c, T b c) * f b ^ 2 - m ^ 2 * D := by
    have e : ∀ b, (∑ c, T b c) * (f b - m) ^ 2 =
        (∑ c, T b c) * f b ^ 2 - 2 * m * ((∑ c, T b c) * f b) + m ^ 2 * ∑ c, T b c :=
      fun b => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hm, ← hD]
    ring
  have eS : ∑ b, (∑ c, T b c) * (p * (f b - m) - (a b - m)) ^ 2 =
      p ^ 2 * ∑ b, (∑ c, T b c) * f b ^ 2 - 2 * p * ∑ b, ∑ c, T b c * f b * f c
        + ∑ b, (∑ c, T b c) * a b ^ 2 - (p - 1) ^ 2 * m ^ 2 * D := by
    have e : ∀ b, (∑ c, T b c) * (p * (f b - m) - (a b - m)) ^ 2 =
        p ^ 2 * ((∑ c, T b c) * f b ^ 2) - 2 * p * ((∑ c, T b c) * f b * a b)
          + (∑ c, T b c) * a b ^ 2 - 2 * p * (p - 1) * m * ((∑ c, T b c) * f b)
          + 2 * (p - 1) * m * ((∑ c, T b c) * a b) + (p - 1) ^ 2 * m ^ 2 * ∑ c, T b c :=
      fun b => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hfa, hm, sa, ← hD]
    ring
  rw [eQ, eN] at hG
  rw [eS] at hsq
  have hrp : 0 ≤ (r - p) * (p * (∑ b, (∑ c, T b c) * f b ^ 2 - m ^ 2 * D)
      - (∑ b, ∑ c, T b c * f b * f c - m ^ 2 * D)) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-! ### The per-triangle form -/

/-- **The integrand of the one-apex certificate** at an ordered triangle `(x, y, z)`, with `x` of
type `tx` (`true` = in `A`): the local term `(p − v)(r − v)` or `−v (1 + v)` at `x`, plus the
vertex identity with weight `2 − p − r` on `A` and `p + r` off `A`. -/
def oneJ (p r μ : ℝ) (tx : Bool) (fx fy fz hxy : ℝ) : ℝ :=
  if tx then p * r * fy ^ 2 - (p + r) * fy * fz + hxy ^ 2 - (p - 1) * (r - 1) * μ ^ 2 * fx ^ 2
      + (2 - p - r) * fx * (fy - μ * fx)
  else -(fy * fz) - hxy ^ 2 + 2 * μ ^ 2 * fx ^ 2 + (p + r) * fx * (fy - μ * fx)

/-- **The per-triangle form of the one-apex certificate**: `oneJ` summed over the six orderings of
a triangle with types `t0, t1, t2`, values `f0, f1, f2` and edge values `h01, h02, h12`. -/
def oneQ (p r μ : ℝ) (t0 t1 t2 : Bool) (f0 f1 f2 h01 h02 h12 : ℝ) : ℝ :=
  oneJ p r μ t0 f0 f1 f2 h01 + oneJ p r μ t0 f0 f2 f1 h02 + oneJ p r μ t1 f1 f0 f2 h01
    + oneJ p r μ t1 f1 f2 f0 h12 + oneJ p r μ t2 f2 f0 f1 h02 + oneJ p r μ t2 f2 f1 f0 h12

/-- `oneQ` is symmetric: exchanging the vertices `0` and `1`. -/
theorem oneQ_swap01 (p r μ : ℝ) (t0 t1 t2 : Bool) (f0 f1 f2 h01 h02 h12 : ℝ) :
    oneQ p r μ t0 t1 t2 f0 f1 f2 h01 h02 h12 = oneQ p r μ t1 t0 t2 f1 f0 f2 h01 h12 h02 := by
  unfold oneQ
  ring

/-- `oneQ` is symmetric: exchanging the vertices `0` and `2`. -/
theorem oneQ_swap02 (p r μ : ℝ) (t0 t1 t2 : Bool) (f0 f1 f2 h01 h02 h12 : ℝ) :
    oneQ p r μ t0 t1 t2 f0 f1 f2 h01 h02 h12 = oneQ p r μ t2 t1 t0 f2 f1 f0 h12 h02 h01 := by
  unfold oneQ
  ring

/-- **The one-apex form is diagonal.** For a triangle whose vertex `0` is in `A` and whose other
two vertices are not, `q_T = α f0² + β (f1² + f2²) − 2 h12²` with
`α = −2μ ((1 − p)(1 − r) μ + 2 − p − r)` and `β = (2μ − p)(2μ − r)`: the terms in `h01`, `h02`
cancel between the apex and the base. -/
theorem oneQ_PQQ (p r μ f0 f1 f2 h01 h02 h12 : ℝ) :
    oneQ p r μ true false false f0 f1 f2 h01 h02 h12 =
      -2 * μ * ((1 - p) * (1 - r) * μ + 2 - p - r) * f0 ^ 2
        + (2 * μ - p) * (2 * μ - r) * (f1 ^ 2 + f2 ^ 2) - 2 * h12 ^ 2 := by
  simp only [oneQ, oneJ, Bool.false_eq_true, ↓reduceIte]
  ring

/-- With `α, β < 0`, **the one-apex form is `≤ 0`**. -/
theorem oneQ_PQQ_nonpos {p r μ : ℝ} (hα : -2 * μ * ((1 - p) * (1 - r) * μ + 2 - p - r) < 0)
    (hβ : (2 * μ - p) * (2 * μ - r) < 0) (f0 f1 f2 h01 h02 h12 : ℝ) :
    oneQ p r μ true false false f0 f1 f2 h01 h02 h12 ≤ 0 := by
  rw [oneQ_PQQ]
  have t1 := mul_nonpos_of_nonpos_of_nonneg hα.le (sq_nonneg f0)
  have t2 := mul_nonpos_of_nonpos_of_nonneg hβ.le
    (add_nonneg (sq_nonneg f1) (sq_nonneg f2))
  nlinarith [sq_nonneg h12]

/-- **Rigidity of the one-apex form**: with `α, β < 0`, a vanishing form has `f0 = f1 = f2 = 0`. -/
theorem eq_zero_of_oneQ_PQQ_eq_zero {p r μ : ℝ}
    (hα : -2 * μ * ((1 - p) * (1 - r) * μ + 2 - p - r) < 0)
    (hβ : (2 * μ - p) * (2 * μ - r) < 0) {f0 f1 f2 h01 h02 h12 : ℝ}
    (h : oneQ p r μ true false false f0 f1 f2 h01 h02 h12 = 0) :
    f0 = 0 ∧ f1 = 0 ∧ f2 = 0 := by
  rw [oneQ_PQQ] at h
  have t1 := mul_nonpos_of_nonpos_of_nonneg hα.le (sq_nonneg f0)
  have t2 := mul_nonpos_of_nonpos_of_nonneg hβ.le
    (add_nonneg (sq_nonneg f1) (sq_nonneg f2))
  have t3 : 0 ≤ 2 * h12 ^ 2 := by positivity
  have z1 : -2 * μ * ((1 - p) * (1 - r) * μ + 2 - p - r) * f0 ^ 2 = 0 := by linarith
  have z2 : (2 * μ - p) * (2 * μ - r) * (f1 ^ 2 + f2 ^ 2) = 0 := by linarith
  have e0 : f0 ^ 2 = 0 := (mul_eq_zero.mp z1).resolve_left hα.ne
  have e12 : f1 ^ 2 + f2 ^ 2 = 0 := (mul_eq_zero.mp z2).resolve_left hβ.ne
  have e1 : f1 ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg f2]) (sq_nonneg _)
  have e2 : f2 ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg f1]) (sq_nonneg _)
  exact ⟨pow_eq_zero_iff two_ne_zero |>.mp e0, pow_eq_zero_iff two_ne_zero |>.mp e1,
    pow_eq_zero_iff two_ne_zero |>.mp e2⟩

/-! ### The theorem for a triangle weight -/

variable {T : ι → ι → ι → ℝ}

/-- **One vertex of `A` in every triangle, for a triangle weight.** Let `T` be a triangle weight
and `w` a connected weighted graph with `Σ_c T a b c = k · w a b`, `k > 0`. Let `A` be a set of
vertices such that every triangle of positive weight has exactly one vertex in `A`: no edge of
`w` lies inside `A` (`hA`), and no triangle lies outside `A` (`hB`). If `0 ≤ p < 1`,
`2p³ + 3p² − 14p + 8 > 0` (that is, `p < p* ≈ 0.7551`), the links of the vertices of `A` have
second eigenvalue at most `p`, and the other links at most `0`, then `w` has second eigenvalue at
most `p/2`.

Degenerate cases: `w` with no edges makes the conclusion vacuous; vertices in no triangle carry no
condition; no connectivity of the links is assumed. For `p ≥ p*` the certificate no longer covers
the interval left open by the edge-average bound, and the statement is not proved here. -/
theorem _root_.EdgeAverageTricklingDown.IsTriangleWeight.walkSecondEigenvalueLE_half_of_one_apex
    (hT : IsTriangleWeight T) {w : ι → ι → ℝ} {k : ℝ} (hk : 0 < k)
    (hw : ∀ a b, ∑ c, T a b c = k * w a b)
    (hconn : ∀ F : ι → ℝ, (∀ u v, 0 < w u v → F u = F v) →
      ∀ u v, 0 < ∑ x, w u x → 0 < ∑ x, w v x → F u = F v)
    (A : Set ι) (hA : ∀ a ∈ A, ∀ b ∈ A, w a b = 0)
    (hB : ∀ a b c, a ∉ A → b ∉ A → c ∉ A → T a b c = 0) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hpstar : 0 < 2 * p ^ 3 + 3 * p ^ 2 - 14 * p + 8)
    (hlamA : ∀ z ∈ A, WalkSecondEigenvalueLE (T z) p)
    (hlamQ : ∀ z ∉ A, WalkSecondEigenvalueLE (T z) 0) :
    WalkSecondEigenvalueLE w (p / 2) := by
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
  -- an eigenfunction above `p/2`
  obtain ⟨g, γ, hγ, heig, hgf⟩ := exists_walk_eigenfunction_of_lt hwsymm hwnn hcon
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
  have hγne : γ ≠ 1 := by
    rintro rfl
    exact hnc (eq_of_eigen_one hwsymm hwnn hconn heig)
  have hmean : ∑ u, (∑ v, w u v) * g u = 0 := sum_deg_mul_eq_zero_of_eigen hwsymm heig hγne
  have hQg := sum_mul_mul_eq_of_eigen heig
  -- the edge-average cut `γ ≤ p/(2 − p)`
  have hcut : γ * (2 - p) ≤ p := by
    have hlam : ∀ z, WalkSecondEigenvalueLE (T z) ((fun z => if z ∈ A then p else 0) z) := by
      intro z
      by_cases hz : z ∈ A
      · show WalkSecondEigenvalueLE (T z) (if z ∈ A then p else 0)
        rw [if_pos hz]; exact hlamA z hz
      · show WalkSecondEigenvalueLE (T z) (if z ∈ A then p else 0)
        rw [if_neg hz]; exact hlamQ z hz
    have hlt : ∀ z, (fun z => if z ∈ A then p else 0) z < 1 := fun z => by
      show (if z ∈ A then p else 0) < 1
      split_ifs <;> linarith
    have hedge : ∀ u v, 0 < w u v → ((fun z => if z ∈ A then p else 0) u
        + (fun z => if z ∈ A then p else 0) v) / 2 ≤ p / 2 := by
      intro u v huv
      show ((if u ∈ A then p else 0) + (if v ∈ A then p else 0)) / 2 ≤ p / 2
      by_cases hu : u ∈ A <;> by_cases hv : v ∈ A
      · exact absurd (hA u hu v hv) huv.ne'
      · rw [if_pos hu, if_neg hv]; linarith
      · rw [if_neg hu, if_pos hv]; linarith
      · rw [if_neg hu, if_neg hv]; linarith
    have hO := hT.walkSecondEigenvalueLE_of_edge_average hk hw hconn hlam
      (fun z h1 => absurd h1 (not_le.mpr (hlt z))) (by linarith : p / 2 < 1) hedge
    have h1 := hO g hmean
    rw [hQg] at h1
    have h2 : γ ≤ p / 2 / (1 - p / 2) := le_of_mul_le_mul_right h1 hg2
    rw [le_div_iff₀ (by linarith)] at h2
    linarith
  -- the parameter `r`
  have hγ0 : 0 < γ := by linarith
  have h1p : 0 < 1 - p := by linarith
  have hF : 0 < 2 - p - 2 * (1 - p) * γ ^ 2 - (1 + p) * γ := by
    have hs0 : 0 ≤ γ * (2 - p) := mul_nonneg hγ0.le (by linarith)
    have key : (2 - p) ^ 2 * (2 - p - 2 * (1 - p) * γ ^ 2 - (1 + p) * γ) =
        (2 - p) ^ 3 - 2 * (1 - p) * (γ * (2 - p)) ^ 2 - (1 + p) * (2 - p) * (γ * (2 - p)) := by
      ring
    have k1 : 2 * (1 - p) * (γ * (2 - p)) ^ 2 ≤ 2 * (1 - p) * p ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hcut 2) (by linarith)
    have k2 : (1 + p) * (2 - p) * (γ * (2 - p)) ≤ (1 + p) * (2 - p) * p :=
      mul_le_mul_of_nonneg_left hcut (by nlinarith)
    have k3 : (2 - p) ^ 3 - 2 * (1 - p) * p ^ 2 - (1 + p) * (2 - p) * p =
        2 * p ^ 3 + 3 * p ^ 2 - 14 * p + 8 := by ring
    have h2p : 0 < (2 - p) ^ 2 := by nlinarith
    have : 0 < (2 - p) ^ 2 * (2 - p - 2 * (1 - p) * γ ^ 2 - (1 + p) * γ) := by
      rw [key]; linarith
    exact pos_of_mul_pos_right this h2p.le
  have hden : 0 < 2 * (1 + (1 - p) * γ) := by
    have := mul_pos h1p hγ0
    linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 2 * γ + (2 - p - 2 * (1 - p) * γ ^ 2 - (1 + p) * γ) /
      (2 * (1 + (1 - p) * γ)) := ⟨_, rfl⟩
  have hr2 : 2 * γ < r := by rw [hr]; have := div_pos hF hden; linarith
  have e1 : 2 * ((r - 2 * γ) * (1 + (1 - p) * γ)) =
      2 - p - 2 * (1 - p) * γ ^ 2 - (1 + p) * γ := by
    have : (r - 2 * γ) * (2 * (1 + (1 - p) * γ)) = 2 - p - 2 * (1 - p) * γ ^ 2 - (1 + p) * γ := by
      rw [hr, add_sub_cancel_left, div_mul_cancel₀ _ hden.ne']
    linarith
  have hG : 0 < (1 - p) * (1 - r) * γ + 2 - p - r := by
    have : (1 - p) * (1 - r) * γ + 2 - p - r = (2 - p - 2 * (1 - p) * γ ^ 2 - (1 + p) * γ)
        - (r - 2 * γ) * (1 + (1 - p) * γ) := by ring
    rw [this]; linarith
  have hα : -2 * γ * ((1 - p) * (1 - r) * γ + 2 - p - r) < 0 := by
    have := mul_pos hγ0 hG
    linarith
  have hβ : (2 * γ - p) * (2 * γ - r) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have hpr : p ≤ r := by linarith
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
  -- the integrand and its two parts
  obtain ⟨J, hJ⟩ : ∃ J : ι → ι → ι → ℝ, J = fun a b c =>
      oneJ p r γ (decide (a ∈ A)) (g a) (g b) (g c) (h a b) := ⟨_, rfl⟩
  obtain ⟨Lf, hLf⟩ : ∃ Lf : ι → ι → ι → ℝ, Lf = fun a b c =>
      if a ∈ A then p * r * g b ^ 2 - (p + r) * g b * g c + h a b ^ 2
        - (p - 1) * (r - 1) * γ ^ 2 * g a ^ 2
      else -(g b * g c) - h a b ^ 2 + 2 * γ ^ 2 * g a ^ 2 := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc : ι → ℝ, cc = fun a => if a ∈ A then 2 - p - r else p + r := ⟨_, rfl⟩
  have hJsplit : ∀ a b c, J a b c = Lf a b c + cc a * g a * (g b - γ * g a) := by
    intro a b c
    simp only [hJ, hLf, hcc, oneJ, decide_eq_true_eq]
    split_ifs <;> ring
  have s2 : ∀ a (x : ι → ℝ), ∑ b, ∑ c, T a b c * x b = ∑ b, (∑ c, T a b c) * x b := fun a x =>
    Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm
  have hL : ∀ a, 0 ≤ ∑ b, ∑ c, T a b c * Lf a b c := by
    intro a
    by_cases ha : a ∈ A
    · have hloc := local_prod_mean (hT.swap23 a) (hT.nonneg a) (hlamA a ha) hpr g (h a)
        (γ * g a) (hh a) (hmloc a)
      have e : ∀ b c, T a b c * Lf a b c = p * r * (T a b c * g b ^ 2)
          - (p + r) * (T a b c * g b * g c) + T a b c * h a b ^ 2
          - (p - 1) * (r - 1) * γ ^ 2 * g a ^ 2 * T a b c := by
        intro b c
        simp only [hLf, if_pos ha]
        ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [s2 a (fun b => g b ^ 2), s2 a (fun b => h a b ^ 2)]
      nlinarith
    · have hloc := local_quadratic_mean (hT.swap23 a) (hT.nonneg a) (hlamQ a ha)
        (by norm_num) g (h a) (γ * g a) (hh a) (hmloc a)
      have e : ∀ b c, T a b c * Lf a b c = -(T a b c * g b * g c) - T a b c * h a b ^ 2
          + 2 * γ ^ 2 * g a ^ 2 * T a b c := by
        intro b c
        simp only [hLf, if_neg ha]
        ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        ← Finset.mul_sum]
      rw [s2 a (fun b => h a b ^ 2)]
      nlinarith
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
  have hJ0 : 0 ≤ ∑ a, ∑ b, ∑ c, T a b c * J a b c := by
    have e : ∀ a, ∑ b, ∑ c, T a b c * J a b c = ∑ b, ∑ c, T a b c * Lf a b c
        + ∑ b, ∑ c, T a b c * (cc a * g a * (g b - γ * g a)) := by
      intro a
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by
        rw [hJsplit]; ring
    simp only [e, hV, add_zero]
    exact Finset.sum_nonneg fun a _ => hL a
  -- the symmetrised per-triangle forms
  obtain ⟨tq, htq⟩ : ∃ tq : ι → ι → ι → ℝ, tq = fun a b c =>
      oneQ p r γ (decide (a ∈ A)) (decide (b ∈ A)) (decide (c ∈ A)) (g a) (g b) (g c)
        (h a b) (h a c) (h b c) := ⟨_, rfl⟩
  have hsymJ : ∀ a b c, J a b c + J a c b + J b a c + J b c a + J c a b + J c b a = tq a b c := by
    intro a b c
    simp only [hJ, htq, oneQ]
    rw [hhsymm b a, hhsymm c a, hhsymm c b]
  have htq0 : 0 ≤ ∑ a, ∑ b, ∑ c, T a b c * tq a b c := by
    have := six_mul_sum_tri hT J
    simp only [hsymJ] at this
    linarith
  have hTA : ∀ a b c, a ∈ A → b ∈ A → T a b c = 0 := by
    intro a b c ha hb
    have h0 : ∑ x, T a b x = 0 := by rw [hw, hA a ha b hb, mul_zero]
    exact (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hT.nonneg a b x).mp h0 c
      (Finset.mem_univ c)
  have htri : ∀ a b c, 0 < T a b c → tq a b c ≤ 0 ∧ (tq a b c = 0 → g a = g b) := by
    intro a b c hpos
    simp only [htq]
    by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> by_cases hc : c ∈ A
    · exact absurd (hTA a b c ha hb) hpos.ne'
    · exact absurd (hTA a b c ha hb) hpos.ne'
    · exact absurd (by rw [hT.swap23]; exact hTA a c b ha hc) hpos.ne'
    · rw [decide_eq_true ha, decide_eq_false hb, decide_eq_false hc]
      refine ⟨oneQ_PQQ_nonpos hα hβ _ _ _ _ _ _, fun h0 => ?_⟩
      obtain ⟨e0, e1, -⟩ := eq_zero_of_oneQ_PQQ_eq_zero hα hβ h0
      rw [e0, e1]
    · exact absurd (by rw [hT.cycle]; exact hTA b c a hb hc) hpos.ne'
    · rw [decide_eq_false ha, decide_eq_true hb, decide_eq_false hc, oneQ_swap01]
      refine ⟨oneQ_PQQ_nonpos hα hβ _ _ _ _ _ _, fun h0 => ?_⟩
      obtain ⟨e0, e1, -⟩ := eq_zero_of_oneQ_PQQ_eq_zero hα hβ h0
      rw [e0, e1]
    · rw [decide_eq_false ha, decide_eq_false hb, decide_eq_true hc, oneQ_swap02]
      refine ⟨oneQ_PQQ_nonpos hα hβ _ _ _ _ _ _, fun h0 => ?_⟩
      obtain ⟨e0, e1, e2⟩ := eq_zero_of_oneQ_PQQ_eq_zero hα hβ h0
      rw [e1, e2]
    · exact absurd (hB a b c ha hb hc) hpos.ne'
  have hterm : ∀ a b c, T a b c * tq a b c = 0 := by
    intro a b c
    have hle : ∀ a b c, T a b c * tq a b c ≤ 0 := fun a b c => by
      rcases (hT.nonneg a b c).eq_or_lt with h0 | h0
      · rw [← h0, zero_mul]
      · exact mul_nonpos_of_nonneg_of_nonpos h0.le (htri a b c h0).1
    have h2 : ∀ a b, ∑ c, T a b c * tq a b c ≤ 0 := fun a b =>
      Finset.sum_nonpos fun c _ => hle a b c
    have h1 : ∀ a, ∑ b, ∑ c, T a b c * tq a b c ≤ 0 := fun a =>
      Finset.sum_nonpos fun b _ => h2 a b
    have h0 : ∑ a, ∑ b, ∑ c, T a b c * tq a b c = 0 :=
      le_antisymm (Finset.sum_nonpos fun a _ => h1 a) htq0
    have z1 := (Finset.sum_eq_zero_iff_of_nonpos fun a _ => h1 a).mp h0 a (Finset.mem_univ a)
    have z2 := (Finset.sum_eq_zero_iff_of_nonpos fun b _ => h2 a b).mp z1 b (Finset.mem_univ b)
    exact (Finset.sum_eq_zero_iff_of_nonpos fun c _ => hle a b c).mp z2 c (Finset.mem_univ c)
  apply hnc
  refine hconn g fun u v huv => ?_
  have hd : 0 < ∑ c, T u v c := by rw [hw]; exact mul_pos hk huv
  obtain ⟨c0, -, hc0⟩ := (Finset.sum_pos_iff_of_nonneg fun c _ => hT.nonneg u v c).mp hd
  have h0 : tq u v c0 = 0 := (mul_eq_zero.mp (hterm u v c0)).resolve_left hc0.ne'
  exact (htri u v c0 hc0).2 h0

end TwoTypeTricklingDown

namespace PreAbstractSimplicialComplex

open TwoTypeTricklingDown

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {K : PreAbstractSimplicialComplex ι} {d : ℕ}
  {m : Finset ι → ℝ}

/-- **One vertex of `A` in every triangle.** Let `m` be a top weight of the connected pure
`d`-dimensional complex `K`, `d ≥ 2`. Let `A` be a set of vertices such that every triangle of `K`
has exactly one vertex in `A`: no edge of `K` lies inside `A` (`hA`), and no triangle
`{a, b, c}` lies outside `A` (`hB`; `linkWeightOf m {a} b c` is the weight of the triangle). If
`0 ≤ p < 1` with `2p³ + 3p² − 14p + 8 > 0` (`p < p* ≈ 0.7551`), the link of every vertex of `A`
has second eigenvalue at most `p` and the link of every other vertex at most `0`, then the
underlying graph has second eigenvalue at most `p/2`.

For `p ≤ 1/2` this is also a case of `IsTopWeight.walkSecondEigenvalueLE_half_of_cone_type`. The
value `p/2` is attained on the fan for `p ≤ 1/2` (`exists_isLeast_fan`). The threshold `p*` comes
from the certificate, not from the class: a structural argument that is not formalized here (the
class consists of joins `A * G` with product weights) gives the bound for every `p < 1`, so this
theorem is weaker than what is true. Points that are not vertices carry no condition, and no
connectivity of the links is assumed. -/
theorem IsTopWeight.walkSecondEigenvalueLE_half_of_one_apex (hm : K.IsTopWeight d m)
    (hd : 2 ≤ d) (hconn : K.IsConnected) (A : Set ι)
    (hA : ∀ a ∈ A, ∀ b ∈ A, linkWeightOf m ∅ a b = 0)
    (hB : ∀ a b c, a ∉ A → b ∉ A → c ∉ A → linkWeightOf m {a} b c = 0) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p < 1) (hpstar : 0 < 2 * p ^ 3 + 3 * p ^ 2 - 14 * p + 8)
    (hlamA : ∀ z ∈ A, {z} ∈ K → WalkSecondEigenvalueLE (linkWeightOf m {z}) p)
    (hlamQ : ∀ z ∉ A, {z} ∈ K → WalkSecondEigenvalueLE (linkWeightOf m {z}) 0) :
    WalkSecondEigenvalueLE (linkWeightOf m ∅) (p / 2) := by
  have e : ∀ z : ι, insert z (∅ : Finset ι) = {z} := fun z => by simp
  have hk : (0 : ℝ) < (d : ℝ) - 1 - #(∅ : Finset ι) := by
    rw [Finset.card_empty]
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast
    linarith
  have hT : ∀ z, linkTriangleWeight m ∅ z = linkWeightOf m {z} := fun z => by
    rw [linkTriangleWeight_of_notMem m (Finset.notMem_empty z), e]
  have hlink : ∀ (z : ι) (r : ℝ), ({z} ∈ K → WalkSecondEigenvalueLE (linkWeightOf m {z}) r) →
      WalkSecondEigenvalueLE (linkTriangleWeight m ∅ z) r := by
    intro z r hz
    rw [hT z]
    by_cases hK : {z} ∈ K
    · exact hz hK
    · exact walkSecondEigenvalueLE_of_forall_eq_zero
        (hm.linkWeightOf_eq_zero_of_notMem (Finset.singleton_nonempty z) hK) _
  exact (isTriangleWeight_linkTriangleWeight hm.nonneg ∅).walkSecondEigenvalueLE_half_of_one_apex
    hk (fun a b => sum_linkWeightOf_insert_right hm.card_eq_of_ne_zero ∅ a b)
    (fun F hF u v hu hv => hm.eq_of_forall_linkWeightOf_pos (by rw [link_empty]; exact hconn)
      F hF u v hu hv)
    A hA (fun a b c ha hb hc => by rw [hT a]; exact hB a b c ha hb hc) hp0 hp1 hpstar
    (fun z hz => hlink z p (hlamA z hz)) (fun z hz => hlink z 0 (hlamQ z hz))

end PreAbstractSimplicialComplex
