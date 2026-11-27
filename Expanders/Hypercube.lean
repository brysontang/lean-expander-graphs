/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.Cheeger

/-!
# The hypercube

The `n`-dimensional hypercube `Qₙ` has the bit strings of length `n` as vertices, two strings being
adjacent when they differ in exactly one coordinate. It is `n`-regular, and this file computes its
spectral gap and its Cheeger constant exactly.

## Definitions
* `SimpleGraph.hypercube`: the hypercube graph on `Fin n → Bool`.
* `SimpleGraph.hypercube.bitFlip`: flipping one bit of a string; the neighbours of `u` are exactly
  the strings `bitFlip u i`.

## Theorems
* `hypercube_isRegularOfDegree`: `Qₙ` is `n`-regular. **Proved.**
* `hypercube.variance_le`: the **Poincaré inequality on the cube**,
  `2ᴺ Σ x_v² − (Σ x_v)² ≤ 2ᴺ/4 · Σ_{u ~ v} (x_u − x_v)²` (ordered adjacent pairs), by
  induction on the dimension (tensorization). **Proved.**
* `hypercube_secondAdjEigenvalue`: `λ₂(Q_{n+1}) = (n + 1) − 2`. **Proved.**
* `hypercube_spectralGap`: the spectral gap of `Q_{n+1}` is `2`. **Proved.**
* `hypercube_edgeExpansion`: the Cheeger constant of `Q_{n+1}` is `1`, so the easy direction
  of Cheeger's inequality is attained. **Proved.**
-/

open Finset Matrix

namespace SimpleGraph

/-- The `n`-dimensional hypercube: vertices are bit strings of length `n`, adjacent when they
differ in exactly one coordinate. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := #{i | u i ≠ v i} = 1
  symm := ⟨fun u v h => by simpa only [ne_comm] using h⟩
  loopless := ⟨fun u h => by simp at h⟩

/-- Adjacency in the hypercube is decidable: it is an equality of natural numbers. -/
instance (n : ℕ) : DecidableRel (hypercube n).Adj :=
  fun u v => inferInstanceAs (Decidable (#{i | u i ≠ v i} = 1))

namespace hypercube

variable {n : ℕ}

/-- Flip the `i`-th bit of the string `u`. -/
def bitFlip (u : Fin n → Bool) (i : Fin n) : Fin n → Bool := Function.update u i (!u i)

theorem bitFlip_apply_self (u : Fin n → Bool) (i : Fin n) : bitFlip u i i = !u i := by
  simp [bitFlip]

theorem bitFlip_apply_of_ne (u : Fin n → Bool) {i j : Fin n} (h : j ≠ i) :
    bitFlip u i j = u j := by
  simp [bitFlip, Function.update_of_ne h]

theorem bitFlip_bitFlip (u : Fin n → Bool) (i : Fin n) : bitFlip (bitFlip u i) i = u := by
  simp [bitFlip]

theorem bitFlip_injective (u : Fin n → Bool) : Function.Injective (bitFlip u) := by
  intro i j hij
  by_contra h
  have := congrFun hij i
  rw [bitFlip_apply_self, bitFlip_apply_of_ne u h] at this
  simp at this

/-- Two strings are adjacent in the hypercube exactly when one is obtained from the other by
flipping a single bit. -/
theorem adj_iff {u v : Fin n → Bool} : (hypercube n).Adj u v ↔ ∃ i, bitFlip u i = v := by
  change #{i | u i ≠ v i} = 1 ↔ _
  rw [card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    have hj : ∀ j, u j ≠ v j ↔ j = i := by
      intro j
      have := congrArg (j ∈ ·) hi
      simpa using this
    refine ⟨i, funext fun j => ?_⟩
    by_cases hji : j = i
    · rw [hji, bitFlip_apply_self]
      have := (hj i).mpr rfl
      cases h1 : u i <;> cases h2 : v i <;> simp_all
    · rw [bitFlip_apply_of_ne u hji]
      by_contra hne
      exact hji ((hj j).mp hne)
  · rintro ⟨i, rfl⟩
    refine ⟨i, ext fun j => ?_⟩
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    by_cases hji : j = i
    · subst hji
      simp [bitFlip_apply_self]
    · simp [bitFlip_apply_of_ne u hji, hji]

/-- The neighbours of `u` are the `n` strings obtained by flipping one bit of `u`. -/
theorem filter_adj_eq_image (u : Fin n → Bool) :
    ({v | (hypercube n).Adj u v} : Finset _) = univ.image (bitFlip u) := by
  ext v
  simp [adj_iff]

/-- Summing over the neighbours of `u` is summing over the bit flips of `u`. -/
theorem sum_adj {M : Type*} [AddCommMonoid M] (u : Fin n → Bool) (f : (Fin n → Bool) → M) :
    (∑ v, if (hypercube n).Adj u v then f v else 0) = ∑ i, f (bitFlip u i) := by
  rw [← Finset.sum_filter, filter_adj_eq_image,
    sum_image fun i _ j _ h => bitFlip_injective u h]

/-- A sum over `(n+1)`-bit strings splits according to the first bit. -/
theorem sum_eq_sum_cons {M : Type*} [AddCommMonoid M] (g : (Fin (n + 1) → Bool) → M) :
    ∑ u, g u = ∑ w : Fin n → Bool, (g (Fin.cons false w) + g (Fin.cons true w)) := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => add_comm _ _

theorem bitFlip_cons_zero (b : Bool) (w : Fin n → Bool) :
    bitFlip (Fin.cons b w : Fin (n + 1) → Bool) 0 = Fin.cons (!b) w := by
  simp [bitFlip, Fin.update_cons_zero]

theorem bitFlip_cons_succ (b : Bool) (w : Fin n → Bool) (j : Fin n) :
    bitFlip (Fin.cons b w : Fin (n + 1) → Bool) j.succ = Fin.cons b (bitFlip w j) := by
  simp [bitFlip, ← Fin.cons_update]

/-- The Laplacian form of the hypercube, written with bit flips. -/
theorem sum_adj_sub_sq (x : (Fin n → Bool) → ℝ) :
    (∑ u, ∑ v, if (hypercube n).Adj u v then (x u - x v) ^ 2 else 0)
      = ∑ u, ∑ i, (x u - x (bitFlip u i)) ^ 2 :=
  Finset.sum_congr rfl fun u _ => sum_adj u fun v => (x u - x v) ^ 2

/-- **Poincaré inequality on the hypercube** (variance form):
`2ᴺ Σ x_v² − (Σ x_v)² ≤ 2ᴺ/4 · Σ_u Σ_i (x_u − x_{u ⊕ eᵢ})²`.
Proved by induction on the dimension, splitting off the first bit (tensorization). -/
theorem variance_le (N : ℕ) (x : (Fin N → Bool) → ℝ) :
    (2 : ℝ) ^ N * ∑ v, x v ^ 2 - (∑ v, x v) ^ 2
      ≤ (2 : ℝ) ^ N / 4 * ∑ u, ∑ i, (x u - x (bitFlip u i)) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    set x₀ : (Fin N → Bool) → ℝ := fun w => x (Fin.cons false w) with hx₀
    set x₁ : (Fin N → Bool) → ℝ := fun w => x (Fin.cons true w) with hx₁
    have h₀ := ih x₀
    have h₁ := ih x₁
    have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin N → Bool)))
      (f := fun w => x₀ w - x₁ w)
    have hcard : ((#(univ : Finset (Fin N → Bool)) : ℕ) : ℝ) = 2 ^ N := by simp
    rw [hcard, sum_sub_distrib] at hcs
    have hE : ∑ u, ∑ i, (x u - x (bitFlip u i)) ^ 2
        = 2 * ∑ w, (x₀ w - x₁ w) ^ 2 + ∑ u, ∑ i, (x₀ u - x₀ (bitFlip u i)) ^ 2
          + ∑ u, ∑ i, (x₁ u - x₁ (bitFlip u i)) ^ 2 := by
      rw [sum_eq_sum_cons, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [Fin.sum_univ_succ, bitFlip_cons_zero, bitFlip_cons_succ, Bool.not_false,
        Bool.not_true, hx₀, hx₁]
      ring
    have hQ : ∑ v, x v ^ 2 = ∑ w, x₀ w ^ 2 + ∑ w, x₁ w ^ 2 := by
      rw [sum_eq_sum_cons, sum_add_distrib]
    have hS : ∑ v, x v = ∑ w, x₀ w + ∑ w, x₁ w := by
      rw [sum_eq_sum_cons, sum_add_distrib]
    rw [hE, hQ, hS, pow_succ]
    linarith

end hypercube

open hypercube

/-- The `n`-cube is `n`-regular. -/
theorem hypercube_isRegularOfDegree (n : ℕ) : (hypercube n).IsRegularOfDegree n := by
  intro u
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, filter_adj_eq_image,
    card_image_of_injective _ (bitFlip_injective u), card_univ, Fintype.card_fin]

/-- On the `N`-cube, `xᵀAx ≤ (N − 2) xᵀx` for every `x` orthogonal to the constants. -/
theorem hypercube.dotProduct_adjMatrix_mulVec_le (N : ℕ) {x : (Fin N → Bool) → ℝ}
    (hx : ∑ v, x v = 0) :
    x ⬝ᵥ (hypercube N).adjMatrix ℝ *ᵥ x ≤ ((N : ℝ) - 2) * (x ⬝ᵥ x) := by
  have h1 := variance_le N x
  have h2 := sum_adj_sub_sq_div_two (hypercube_isRegularOfDegree N) x
  rw [sum_adj_sub_sq] at h2
  have hxx : x ⬝ᵥ x = ∑ v, x v ^ 2 := by simp [dotProduct, sq]
  rw [hx] at h1
  rw [hxx] at h2 ⊢
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have h3 : ∑ v, x v ^ 2 ≤ (∑ u, ∑ i, (x u - x (bitFlip u i)) ^ 2) / 4 := by
    refine le_of_mul_le_mul_left ?_ hpos
    linarith
  linarith

/-- `λ₂(Q_{n+1}) ≤ n − 1`: the Poincaré inequality on the cube. -/
theorem hypercube_secondAdjEigenvalue_le (n : ℕ) :
    (hypercube (n + 1)).secondAdjEigenvalue ≤ (n : ℝ) - 1 := by
  obtain ⟨x, hx0, hxs, hle⟩ :=
    (hypercube (n + 1)).exists_sum_eq_zero_secondAdjEigenvalue_mul_le
  have h := hypercube.dotProduct_adjMatrix_mulVec_le (n + 1) hxs
  have hnn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hpos : 0 < x ⬝ᵥ x := lt_of_le_of_ne hnn (Ne.symm (dotProduct_self_eq_zero.not.mpr hx0))
  push_cast at h
  refine le_of_mul_le_mul_right ?_ hpos
  linarith

/-- `n − 1 ≤ λ₂(Q_{n+1})`, witnessed by the character `χ(u) = (−1)^{u₀}`, an eigenvector with
eigenvalue `(n + 1) − 2`. -/
theorem le_hypercube_secondAdjEigenvalue (n : ℕ) :
    (n : ℝ) - 1 ≤ (hypercube (n + 1)).secondAdjEigenvalue := by
  set χ : (Fin (n + 1) → Bool) → ℝ := fun u => if u 0 then -1 else 1 with hχ
  have hreg := hypercube_isRegularOfDegree (n + 1)
  have hsum : ∑ u, χ u = 0 := by
    rw [sum_eq_sum_cons]
    simp [χ]
  have hcard : (Fintype.card (Fin (n + 1) → Bool) : ℝ) = 2 ^ (n + 1) := by simp
  have hχχ : χ ⬝ᵥ χ = 2 ^ (n + 1) := by
    have : ∀ u, χ u * χ u = 1 := by
      intro u
      simp only [χ]
      split_ifs <;> norm_num
    simp only [dotProduct, this, sum_const, card_univ, nsmul_eq_mul, mul_one]
    exact hcard
  have hE : ∑ u, ∑ i, (χ u - χ (bitFlip u i)) ^ 2 = 4 * 2 ^ (n + 1) := by
    have hterm : ∀ u, ∑ i, (χ u - χ (bitFlip u i)) ^ 2 = 4 := by
      intro u
      rw [Fin.sum_univ_succ]
      have h0 : (χ u - χ (bitFlip u 0)) ^ 2 = 4 := by
        simp only [χ, bitFlip_apply_self]
        cases u 0 <;> norm_num
      have hs : ∀ j : Fin n, (χ u - χ (bitFlip u j.succ)) ^ 2 = 0 := by
        intro j
        simp only [χ, bitFlip_apply_of_ne u (Fin.succ_ne_zero j).symm]
        ring
      simp [h0, hs]
    simp only [hterm, sum_const, card_univ, nsmul_eq_mul]
    rw [hcard]
    ring
  have h2 := sum_adj_sub_sq_div_two hreg χ
  rw [sum_adj_sub_sq, hE, hχχ] at h2
  have h3 := SimpleGraph.dotProduct_adjMatrix_mulVec_le hreg hsum
  rw [hχχ] at h3
  have hpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  push_cast at h2
  refine le_of_mul_le_mul_right ?_ hpos
  linarith

/-- The second-largest adjacency eigenvalue of the `(n+1)`-cube is `(n + 1) − 2`. -/
theorem hypercube_secondAdjEigenvalue (n : ℕ) :
    (hypercube (n + 1)).secondAdjEigenvalue = (n : ℝ) - 1 :=
  le_antisymm (hypercube_secondAdjEigenvalue_le n) (le_hypercube_secondAdjEigenvalue n)

/-- The spectral gap of the `(n+1)`-cube is `2`. -/
theorem hypercube_spectralGap (n : ℕ) : (hypercube (n + 1)).spectralGap = 2 := by
  rw [spectralGap_eq (hypercube_isRegularOfDegree (n + 1)), hypercube_secondAdjEigenvalue]
  push_cast
  ring

/-- The half-cube `{u | u₀ = false}` has exactly one boundary edge per vertex, so
`h(Q_{n+1}) ≤ 1`. -/
theorem hypercube_edgeExpansion_le_one (n : ℕ) : (hypercube (n + 1)).edgeExpansion ≤ 1 := by
  set S : Finset (Fin (n + 1) → Bool) := {u | u 0 = false}
  have hflip0 : ∀ u : Fin (n + 1) → Bool, bitFlip u 0 0 = !u 0 := fun u => bitFlip_apply_self u 0
  -- Flipping the first bit swaps `S` and its complement.
  have hSc : #Sᶜ = #S := by
    refine card_bij' (fun u _ => bitFlip u 0) (fun u _ => bitFlip u 0) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [S, mem_compl, mem_filter, mem_univ, true_and, Bool.not_eq_false] at hu ⊢
      simp [hflip0, hu]
    · intro u hu
      simp only [S, mem_compl, mem_filter, mem_univ, true_and] at hu ⊢
      simp [hflip0, hu]
    · intro u _
      exact bitFlip_bitFlip u 0
    · intro u _
      exact bitFlip_bitFlip u 0
  have hcard : 2 * #S = Fintype.card (Fin (n + 1) → Bool) := by
    have := card_add_card_compl S
    omega
  have hne : S.Nonempty := ⟨fun _ => false, by simp [S]⟩
  -- The boundary edges of `S` are the pairs `(u, bitFlip u 0)` with `u ∈ S`.
  have hbd : (hypercube (n + 1)).edgeBoundary S = S.image fun u => (u, bitFlip u 0) := by
    ext ⟨u, v⟩
    simp only [mem_edgeBoundary, mem_image, adj_iff, S, mem_filter, mem_univ, true_and,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hu, hv, i, rfl⟩
      refine ⟨u, hu, rfl, ?_⟩
      by_contra hi
      have hi' : i ≠ 0 := fun h => hi (by rw [h])
      exact hv (by rw [bitFlip_apply_of_ne u (Ne.symm hi'), hu])
    · rintro ⟨w, hw, rfl, rfl⟩
      exact ⟨hw, by simp [hflip0, hw], 0, rfl⟩
  have hinj : Function.Injective fun u : Fin (n + 1) → Bool => (u, bitFlip u 0) :=
    fun a b h => congrArg Prod.fst h
  have h := (hypercube (n + 1)).edgeExpansion_le hne hcard.le
  rw [hbd, card_image_of_injective _ hinj, div_self] at h
  · exact h
  · exact_mod_cast hne.card_pos.ne'

/-- The Cheeger constant of the hypercube is exactly `1`; the easy direction of Cheeger's
inequality, `(d − λ₂)/2 ≤ h(G)`, is an equality here. -/
theorem hypercube_edgeExpansion (n : ℕ) : (hypercube (n + 1)).edgeExpansion = 1 := by
  refine le_antisymm (hypercube_edgeExpansion_le_one n) ?_
  have h := spectralGap_div_two_le_edgeExpansion (hypercube_isRegularOfDegree (n + 1))
  rw [hypercube_spectralGap] at h
  linarith

end SimpleGraph
