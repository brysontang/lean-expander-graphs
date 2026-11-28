/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.EdgeAverageTricklingDownLocal

/-!
# Two-type trickling down, part 2: two local inequalities of one link

This file is about a single weighted graph `T : ι → ι → ℝ` (symmetric, and nonnegative where
stated), with degrees `d b = Σ_c T b c` and total weight `D = Σ_b d b`. In the application `T` is
the link of a vertex `z`, and the function `f` on it is an eigenfunction of the underlying graph
restricted to the link. The walk on `T` is `P`, with stationary measure proportional to `d`.

For a real polynomial `r ≥ 0` on `[−1, lam]`, where `lam` bounds the second eigenvalue of `P`,
the spectral theorem gives `⟨f, r(P) f⟩ ≥ r(1) · m² · D`, where `m` is the mean of `f`. The two
polynomials used by the two-type certificate are proved here **without the spectral theorem**:
* `local_garland_mean`: `r = p − v`. This is the definition of `WalkSecondEigenvalueLE`,
  applied to `f − m`. **Proved.**
* `local_quadratic_mean`: `r = (q − v)(1 + v)`, for `q > −1`. Write `g = f − m`, `a = P g`.
  The hypothesis applied to the mean-zero function `g + a`, together with
  `Σ T (x b + x c)² ≥ 0` for `x = q g − a`, gives `(1 + q) ⟨g, r(P) g⟩ ≥ 0`. **Proved.**

In both, the moments are `⟨f, f⟩ = Σ d f²`, `⟨f, P f⟩ = Σ T f f` and `⟨f, P² f⟩ = Σ d a²`, where
`a` is the walk average of `f` (`Σ_c T b c f c = a b · d b`). The value of `a` at a vertex of
degree `0` is irrelevant.
-/

open Finset

namespace TwoTypeTricklingDown

variable {ι : Type*} [Fintype ι]

/-- **The Garland inequality with a mean.** Let `T` be symmetric with random-walk second
eigenvalue at most `p`, and let `f` have degree-weighted mean `m`
(`Σ_b d b f b = m · D`). Then `(p − 1) m² D ≤ p Σ d f² − Σ T f f`.

This is `⟨f, (p − P) f⟩ ≥ (p − 1) · m² · D`. No sign condition on `T` or `p` is needed. If `D = 0`
the hypothesis on `m` is empty and both sides are `0` when `T` is nonnegative. -/
theorem local_garland_mean {T : ι → ι → ℝ} (hsymm : ∀ b c, T b c = T c b) {p : ℝ}
    (hlam : WalkSecondEigenvalueLE T p) (f : ι → ℝ) (m : ℝ)
    (hm : ∑ b, (∑ c, T b c) * f b = m * ∑ b, ∑ c, T b c) :
    (p - 1) * m ^ 2 * ∑ b, ∑ c, T b c ≤
      p * ∑ b, (∑ c, T b c) * f b ^ 2 - ∑ b, ∑ c, T b c * f b * f c := by
  obtain ⟨D, hD⟩ : ∃ D, D = ∑ b, ∑ c, T b c := ⟨_, rfl⟩
  rw [← hD] at hm ⊢
  have s1 : ∑ b, ∑ c, T b c * f b = m * D := by
    rw [← hm]; exact Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm
  have s2 : ∑ b, ∑ c, T b c * f c = m * D := by
    rw [Finset.sum_comm, ← s1]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [hsymm c b]
  have hmean : ∑ b, (∑ c, T b c) * (f b - m) = 0 := by
    have e : ∑ b, (∑ c, T b c) * (f b - m) = ∑ b, (∑ c, T b c) * f b - m * D := by
      rw [hD, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e, hm]; ring
  have h := hlam (fun b => f b - m) hmean
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
  rw [eQ, eN] at h
  nlinarith

/-- **The quadratic local inequality, mean-zero case.** Let `T` be symmetric and nonnegative, with
random-walk second eigenvalue at most `q`, `q > −1`. Let `g` have degree-weighted mean zero and
walk average `a` (`Σ_c T b c g c = a b · d b`). Then `q Σ d g² + (q − 1) Σ T g g − Σ d a² ≥ 0`,
i.e. `⟨g, (q − P)(1 + P) g⟩ ≥ 0`.

Proof: with `G = Σ d g²`, `Q = Σ T g g`, `A = Σ d a²`, `B = Σ T a a`, the hypothesis applied to
the mean-zero function `g + a` reads `Q + 2A + B ≤ q (G + 2Q + A)`, and `Σ T (x b + x c)² ≥ 0`
for `x = q g − a` reads `q² G − 2q Q + A + q² Q − 2q A + B ≥ 0`. Their sum is
`(1 + q) (q G + (q − 1) Q − A) ≥ 0`. -/
theorem local_quadratic_of_sum_eq_zero {T : ι → ι → ℝ} (hsymm : ∀ b c, T b c = T c b)
    (hnn : ∀ b c, 0 ≤ T b c) {q : ℝ} (hlam : WalkSecondEigenvalueLE T q) (hq : -1 < q)
    (g a : ι → ℝ) (ha : ∀ b, ∑ c, T b c * g c = a b * ∑ c, T b c)
    (hmean : ∑ b, (∑ c, T b c) * g b = 0) :
    0 ≤ q * ∑ b, (∑ c, T b c) * g b ^ 2 + (q - 1) * ∑ b, ∑ c, T b c * g b * g c
      - ∑ b, (∑ c, T b c) * a b ^ 2 := by
  obtain ⟨G, hG⟩ : ∃ G, G = ∑ b, (∑ c, T b c) * g b ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∑ b, ∑ c, T b c * g b * g c := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ b, (∑ c, T b c) * a b ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ b, ∑ c, T b c * a b * a c := ⟨_, rfl⟩
  rw [← hG, ← hQ, ← hA]
  -- the mixed moments
  have I1 : ∀ x y : ι → ℝ, ∑ b, ∑ c, T b c * x b * y c = ∑ b, x b * ∑ c, T b c * y c := by
    intro x y
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  have I2 : ∀ x y : ι → ℝ, ∑ b, ∑ c, T b c * x b * y c = ∑ b, ∑ c, T b c * y b * x c := by
    intro x y
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [hsymm c b]; ring
  have hga : ∑ b, (∑ c, T b c) * g b * a b = Q := by
    rw [hQ, I1]
    exact Finset.sum_congr rfl fun b _ => by rw [ha b]; ring
  have hTga : ∑ b, ∑ c, T b c * g b * a c = A := by
    rw [I2, I1, hA]
    exact Finset.sum_congr rfl fun b _ => by rw [ha b]; ring
  have hTag : ∑ b, ∑ c, T b c * a b * g c = A := by rw [I2]; exact hTga
  -- `u = g + a` has mean zero
  have hamean : ∑ b, (∑ c, T b c) * a b = 0 := by
    calc ∑ b, (∑ c, T b c) * a b = ∑ b, ∑ c, T b c * g c :=
          Finset.sum_congr rfl fun b _ => by rw [ha b]; ring
      _ = ∑ c, (∑ b, T c b) * g c := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ => by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun b _ => by rw [hsymm]
      _ = 0 := hmean
  have humean : ∑ b, (∑ c, T b c) * (g b + a b) = 0 := by
    have e : ∑ b, (∑ c, T b c) * (g b + a b) =
        ∑ b, (∑ c, T b c) * g b + ∑ b, (∑ c, T b c) * a b := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e, hmean, hamean]; ring
  have H := hlam (fun b => g b + a b) humean
  have eHl : ∑ b, ∑ c, T b c * (g b + a b) * (g c + a c) = Q + 2 * A + B := by
    have e : ∀ b c, T b c * (g b + a b) * (g c + a c) =
        T b c * g b * g c + T b c * g b * a c + T b c * a b * g c + T b c * a b * a c :=
      fun b c => by ring
    simp only [e, Finset.sum_add_distrib]
    rw [← hQ, hTga, hTag, ← hB]
    ring
  have eHr : ∑ b, (∑ c, T b c) * (g b + a b) ^ 2 = G + 2 * Q + A := by
    have e : ∀ b, (∑ c, T b c) * (g b + a b) ^ 2 =
        (∑ c, T b c) * g b ^ 2 + 2 * ((∑ c, T b c) * g b * a b) + (∑ c, T b c) * a b ^ 2 :=
      fun b => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← hG, hga, ← hA]
  rw [eHl, eHr] at H
  -- positivity of `I + P` at `x = q g − a`
  have hP := EdgeAverageTricklingDown.sum_sum_mul_add_sq hsymm (fun b => q * g b - a b)
  have hP0 : 0 ≤ ∑ b, ∑ c, T b c * ((q * g b - a b) + (q * g c - a c)) ^ 2 :=
    Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => mul_nonneg (hnn b c) (sq_nonneg _)
  have ePd : ∑ b, (∑ c, T b c) * (q * g b - a b) ^ 2 = q ^ 2 * G - 2 * q * Q + A := by
    have e : ∀ b, (∑ c, T b c) * (q * g b - a b) ^ 2 =
        q ^ 2 * ((∑ c, T b c) * g b ^ 2) - 2 * q * ((∑ c, T b c) * g b * a b)
          + (∑ c, T b c) * a b ^ 2 := fun b => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← hG, hga, ← hA]
  have ePt : ∑ b, ∑ c, T b c * (q * g b - a b) * (q * g c - a c) =
      q ^ 2 * Q - 2 * q * A + B := by
    have e : ∀ b c, T b c * (q * g b - a b) * (q * g c - a c) =
        q ^ 2 * (T b c * g b * g c) - q * (T b c * g b * a c) - q * (T b c * a b * g c)
          + T b c * a b * a c := fun b c => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← hQ, hTga, hTag, ← hB]
    ring
  rw [ePd, ePt] at hP
  have key : 0 ≤ (1 + q) * (q * G + (q - 1) * Q - A) := by nlinarith
  exact nonneg_of_mul_nonneg_right (by linarith [mul_comm (1 + q) (q * G + (q - 1) * Q - A)])
    (by linarith : (0 : ℝ) < 1 + q)

/-- **The quadratic local inequality with a mean.** Let `T` be symmetric and nonnegative, with
random-walk second eigenvalue at most `q`, `q > −1`. Let `f` have degree-weighted mean `m`
(`Σ_b d b f b = m · D`) and walk average `a` (`Σ_c T b c f c = a b · d b`). Then
`2 (q − 1) m² D ≤ q Σ d f² + (q − 1) Σ T f f − Σ d a²`.

This is `⟨f, (q − P)(1 + P) f⟩ ≥ r(1) m² D` with `r(1) = 2 (q − 1)`. The case `q = −1` is not
covered (it is not needed: the application has `q ≥ 0`). -/
theorem local_quadratic_mean {T : ι → ι → ℝ} (hsymm : ∀ b c, T b c = T c b)
    (hnn : ∀ b c, 0 ≤ T b c) {q : ℝ} (hlam : WalkSecondEigenvalueLE T q) (hq : -1 < q)
    (f a : ι → ℝ) (m : ℝ) (ha : ∀ b, ∑ c, T b c * f c = a b * ∑ c, T b c)
    (hm : ∑ b, (∑ c, T b c) * f b = m * ∑ b, ∑ c, T b c) :
    2 * (q - 1) * m ^ 2 * ∑ b, ∑ c, T b c ≤
      q * ∑ b, (∑ c, T b c) * f b ^ 2 + (q - 1) * ∑ b, ∑ c, T b c * f b * f c
        - ∑ b, (∑ c, T b c) * a b ^ 2 := by
  obtain ⟨D, hD⟩ : ∃ D, D = ∑ b, ∑ c, T b c := ⟨_, rfl⟩
  rw [← hD] at hm ⊢
  have s1 : ∑ b, ∑ c, T b c * f b = m * D := by
    rw [← hm]; exact Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm
  have s2 : ∑ b, ∑ c, T b c * f c = m * D := by
    rw [Finset.sum_comm, ← s1]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [hsymm c b]
  have sa : ∑ b, (∑ c, T b c) * a b = m * D := by
    rw [← s2]
    exact Finset.sum_congr rfl fun b _ => by rw [ha b]; ring
  have ha' : ∀ b, ∑ c, T b c * (f c - m) = (a b - m) * ∑ c, T b c := by
    intro b
    have : ∑ c, T b c * (f c - m) = ∑ c, T b c * f c - m * ∑ c, T b c := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [this, ha b]; ring
  have hmean : ∑ b, (∑ c, T b c) * (f b - m) = 0 := by
    have e : ∑ b, (∑ c, T b c) * (f b - m) = ∑ b, (∑ c, T b c) * f b - m * D := by
      rw [hD, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e, hm]; ring
  have key := local_quadratic_of_sum_eq_zero hsymm hnn hlam hq (fun b => f b - m)
    (fun b => a b - m) ha' hmean
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
  have eA : ∑ b, (∑ c, T b c) * (a b - m) ^ 2 = ∑ b, (∑ c, T b c) * a b ^ 2 - m ^ 2 * D := by
    have e : ∀ b, (∑ c, T b c) * (a b - m) ^ 2 =
        (∑ c, T b c) * a b ^ 2 - 2 * m * ((∑ c, T b c) * a b) + m ^ 2 * ∑ c, T b c :=
      fun b => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [sa, ← hD]
    ring
  rw [eQ, eN, eA] at key
  nlinarith

end TwoTypeTricklingDown
