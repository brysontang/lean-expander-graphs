/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Mathlib

/-!
# Real symmetric matrices in an eigenbasis

Linear-algebra groundwork for spectral graph theory. For a real symmetric matrix `A` with
eigenvalues `λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ` (Mathlib's `Matrix.IsHermitian.eigenvalues₀`, sorted decreasingly)
we prove the two variational facts everything else leans on:

* `Matrix.IsHermitian.dotProduct_mulVec_le_largest`: `xᵀAx ≤ λ₁ · xᵀx` for every `x`;
* `Matrix.IsHermitian.dotProduct_mulVec_le_second`: if `w` is an eigenvector for `λ₁` and
  `x ⟂ w`, then `xᵀAx ≤ λ₂ · xᵀx`. (The `λ₂` case of Courant–Fischer.)
* `Matrix.IsHermitian.exists_orthogonal_second_le`: that bound is attained.
* `Matrix.IsHermitian.exists_eigenvector_second`: there is an eigenvector for `λ₂` orthogonal
  to a given eigenvector for `λ₁`.

Everything is phrased for plain vectors `n → ℝ` and `dotProduct`, so graph-theoretic files never
have to touch `EuclideanSpace`.
-/

open Finset Matrix

namespace Matrix.IsHermitian

/-- A real Hermitian matrix is symmetric. -/
theorem transpose_eq_self {n : Type*} {A : Matrix n n ℝ} (hA : A.IsHermitian) : Aᵀ = A :=
  (conjTranspose_eq_transpose_of_trivial A).symm.trans hA.eq

theorem dotProduct_self_pos {n : Type*} [Fintype n] {w : n → ℝ} (hw : w ≠ 0) : 0 < w ⬝ᵥ w :=
  lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (w i))
    (Ne.symm (mt dotProduct_self_eq_zero.mp hw))

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian)

/-! ### The eigenbasis, as plain vectors -/

/-- The `j`-th vector of Mathlib's orthonormal eigenbasis of `A`, as a plain function. -/
noncomputable def eigvec (j : n) : n → ℝ := WithLp.ofLp (hA.eigenvectorBasis j)

/-- The coefficient of `x` along the `j`-th eigenvector. -/
noncomputable def coeff (x : n → ℝ) (j : n) : ℝ := hA.eigvec j ⬝ᵥ x

theorem mulVec_eigvec (j : n) : A *ᵥ hA.eigvec j = hA.eigenvalues j • hA.eigvec j :=
  hA.mulVec_eigenvectorBasis j

theorem eigvec_dotProduct_eigvec (i j : n) :
    hA.eigvec i ⬝ᵥ hA.eigvec j = if i = j then 1 else 0 := by
  have h := orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [dotProduct_comm]
  simpa [eigvec] using h

theorem eigvec_ne_zero (j : n) : hA.eigvec j ≠ 0 := by
  intro h
  have := hA.eigvec_dotProduct_eigvec j j
  simp [h] at this

@[simp]
theorem coeff_smul (c : ℝ) (x : n → ℝ) (j : n) : hA.coeff (c • x) j = c * hA.coeff x j := by
  simp [coeff, dotProduct_smul]

/-- Polarised Parseval identity: `Σⱼ cⱼ(x) cⱼ(y) = x ⬝ y`. -/
theorem sum_coeff_mul_coeff (x y : n → ℝ) : ∑ j, hA.coeff x j * hA.coeff y j = x ⬝ᵥ y := by
  have h := hA.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
  rw [dotProduct_comm x y, ← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [coeff, eigvec, dotProduct_comm]

/-- Parseval: `Σⱼ cⱼ(x)² = x ⬝ x`. -/
theorem sum_sq_coeff (x : n → ℝ) : ∑ j, hA.coeff x j ^ 2 = x ⬝ᵥ x := by
  simpa [sq] using hA.sum_coeff_mul_coeff x x

/-- `A` acts diagonally on coefficients: `cⱼ(Ax) = λⱼ cⱼ(x)`. -/
theorem coeff_mulVec (x : n → ℝ) (j : n) :
    hA.coeff (A *ᵥ x) j = hA.eigenvalues j * hA.coeff x j := by
  unfold coeff
  rw [dotProduct_mulVec, ← mulVec_transpose, hA.transpose_eq_self, mulVec_eigvec,
    smul_dotProduct, smul_eq_mul]

/-- The quadratic form of `A` is diagonal in the eigenbasis: `xᵀAx = Σⱼ λⱼ cⱼ(x)²`. -/
theorem dotProduct_mulVec_eq_sum (x : n → ℝ) :
    x ⬝ᵥ A *ᵥ x = ∑ j, hA.eigenvalues j * hA.coeff x j ^ 2 := by
  rw [← hA.sum_coeff_mul_coeff x (A *ᵥ x)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_mulVec]
  ring

/-! ### The two largest eigenvalues -/

/-- The largest eigenvalue `λ₁` of a real symmetric matrix. -/
noncomputable def largestEigenvalue [Nonempty n] : ℝ :=
  hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩

/-- The second-largest eigenvalue `λ₂` of a real symmetric matrix, counted with multiplicity
(so `λ₂ = λ₁` exactly when the top eigenspace has dimension at least two). -/
noncomputable def secondEigenvalue [Nontrivial n] : ℝ :=
  hA.eigenvalues₀ ⟨1, Fintype.one_lt_card⟩

/-- The index (in Mathlib's unsorted indexing by `n`) carrying the largest eigenvalue. -/
noncomputable def topIndex (n : Type*) [Fintype n] [Nonempty n] : n :=
  Fintype.equivOfCardEq (Fintype.card_fin _) (⟨0, Fintype.card_pos⟩ : Fin (Fintype.card n))

theorem secondEigenvalue_le_largestEigenvalue [Nontrivial n] :
    hA.secondEigenvalue ≤ hA.largestEigenvalue :=
  hA.eigenvalues₀_antitone (by simp)

theorem eigenvalues_le_largestEigenvalue [Nonempty n] (j : n) :
    hA.eigenvalues j ≤ hA.largestEigenvalue :=
  hA.eigenvalues₀_antitone (by simp)

theorem eigenvalues_topIndex [Nonempty n] :
    hA.eigenvalues (topIndex n) = hA.largestEigenvalue := by
  simp [eigenvalues, topIndex, largestEigenvalue]

theorem eigenvalues_le_secondEigenvalue [Nontrivial n] {j : n} (hj : j ≠ topIndex n) :
    hA.eigenvalues j ≤ hA.secondEigenvalue := by
  have hi0 : ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j :
      Fin (Fintype.card n)).val ≠ 0 := by
    intro h
    refine hj ?_
    have h0 : (Fintype.equivOfCardEq (Fintype.card_fin _)).symm j
        = (⟨0, Fintype.card_pos⟩ : Fin (Fintype.card n)) := Fin.ext h
    rw [topIndex, ← h0, Equiv.apply_symm_apply]
  exact hA.eigenvalues₀_antitone (Fin.mk_le_of_le_val (Nat.one_le_iff_ne_zero.mpr hi0))

/-- The index (in Mathlib's unsorted indexing by `n`) carrying the second-largest eigenvalue. -/
noncomputable def secondIndex (n : Type*) [Fintype n] [Nontrivial n] : n :=
  Fintype.equivOfCardEq (Fintype.card_fin _) (⟨1, Fintype.one_lt_card⟩ : Fin (Fintype.card n))

theorem eigenvalues_secondIndex [Nontrivial n] :
    hA.eigenvalues (secondIndex n) = hA.secondEigenvalue := by
  simp [eigenvalues, secondIndex, secondEigenvalue]

omit [DecidableEq n] in
theorem topIndex_ne_secondIndex [Nontrivial n] : topIndex n ≠ secondIndex n := by
  intro h
  simp [topIndex, secondIndex] at h

/-- `λ₁` really is an eigenvalue: it has a nonzero eigenvector. -/
theorem exists_eigenvector_largest [Nonempty n] :
    ∃ w : n → ℝ, w ≠ 0 ∧ A *ᵥ w = hA.largestEigenvalue • w :=
  ⟨hA.eigvec (topIndex n), hA.eigvec_ne_zero _, by
    rw [mulVec_eigvec, eigenvalues_topIndex]⟩

/-! ### Variational bounds -/

/-- **Rayleigh bound**: `xᵀAx ≤ λ₁ · xᵀx`. -/
theorem dotProduct_mulVec_le_largest [Nonempty n] (x : n → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ hA.largestEigenvalue * (x ⬝ᵥ x) := by
  rw [hA.dotProduct_mulVec_eq_sum, ← hA.sum_sq_coeff, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (hA.eigenvalues_le_largestEigenvalue j) (sq_nonneg _)

/-- Every eigenvalue is at most `λ₁`. -/
theorem le_largest_of_mulVec_eq [Nonempty n] {μ : ℝ} {w : n → ℝ} (hw : w ≠ 0)
    (h : A *ᵥ w = μ • w) : μ ≤ hA.largestEigenvalue := by
  have h1 := hA.dotProduct_mulVec_le_largest w
  rw [h, dotProduct_smul, smul_eq_mul] at h1
  exact le_of_mul_le_mul_right h1 (dotProduct_self_pos hw)

/-- **Courant–Fischer for `λ₂`**: if `w` is an eigenvector for the largest eigenvalue and
`x ⟂ w`, then `xᵀAx ≤ λ₂ · xᵀx`. -/
theorem dotProduct_mulVec_le_second [Nontrivial n] {w : n → ℝ} (hw : w ≠ 0)
    (hAw : A *ᵥ w = hA.largestEigenvalue • w) {x : n → ℝ} (hx : x ⬝ᵥ w = 0) :
    x ⬝ᵥ A *ᵥ x ≤ hA.secondEigenvalue * (x ⬝ᵥ x) := by
  rcases hA.secondEigenvalue_le_largestEigenvalue.eq_or_lt with heq | hlt
  · -- `λ₂ = λ₁`: the Rayleigh bound already suffices.
    rw [heq]
    exact hA.dotProduct_mulVec_le_largest x
  · -- `λ₂ < λ₁`: the top eigenspace is a line, so `w` lives on the top eigenvector alone.
    have hcw : ∀ j, j ≠ topIndex n → hA.coeff w j = 0 := by
      intro j hj
      have h1 : hA.coeff (A *ᵥ w) j = hA.eigenvalues j * hA.coeff w j := hA.coeff_mulVec w j
      rw [hAw, coeff_smul] at h1
      have h2 : hA.eigenvalues j < hA.largestEigenvalue :=
        (hA.eigenvalues_le_secondEigenvalue hj).trans_lt hlt
      have h3 : (hA.largestEigenvalue - hA.eigenvalues j) * hA.coeff w j = 0 := by
        rw [sub_mul]; linarith
      rcases mul_eq_zero.mp h3 with h | h
      · linarith
      · exact h
    have hcw0 : hA.coeff w (topIndex n) ≠ 0 := by
      intro h0
      refine hw (dotProduct_self_eq_zero.mp ?_)
      rw [← hA.sum_sq_coeff]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j = topIndex n
      · rw [hj, h0]; ring
      · rw [hcw j hj]; ring
    -- hence `x ⟂ w` kills the top coefficient of `x`.
    have hcx : hA.coeff x (topIndex n) = 0 := by
      have h := hA.sum_coeff_mul_coeff x w
      rw [hx, Finset.sum_eq_single (topIndex n)
        (fun j _ hj => by rw [hcw j hj, mul_zero]) (by simp)] at h
      exact (mul_eq_zero.mp h).resolve_right hcw0
    rw [hA.dotProduct_mulVec_eq_sum, ← hA.sum_sq_coeff, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j = topIndex n
    · rw [hj, hcx]; simp
    · exact mul_le_mul_of_nonneg_right (hA.eigenvalues_le_secondEigenvalue hj) (sq_nonneg _)

/-- The bound of `dotProduct_mulVec_le_second` is attained: for any `w` there is a nonzero
`x ⟂ w` with `λ₂ · xᵀx ≤ xᵀAx`. Together the two statements say
`λ₂ = max { xᵀAx / xᵀx : x ≠ 0, x ⟂ w }` whenever `w` is an eigenvector for `λ₁`. -/
theorem exists_orthogonal_second_le [Nontrivial n] (w : n → ℝ) :
    ∃ x : n → ℝ, x ≠ 0 ∧ x ⬝ᵥ w = 0 ∧ hA.secondEigenvalue * (x ⬝ᵥ x) ≤ x ⬝ᵥ A *ᵥ x := by
  have h00 : hA.eigvec (topIndex n) ⬝ᵥ hA.eigvec (topIndex n) = 1 := by
    simp [eigvec_dotProduct_eigvec]
  have h11 : hA.eigvec (secondIndex n) ⬝ᵥ hA.eigvec (secondIndex n) = 1 := by
    simp [eigvec_dotProduct_eigvec]
  have h01 : hA.eigvec (topIndex n) ⬝ᵥ hA.eigvec (secondIndex n) = 0 := by
    simp [eigvec_dotProduct_eigvec, topIndex_ne_secondIndex]
  have h10 : hA.eigvec (secondIndex n) ⬝ᵥ hA.eigvec (topIndex n) = 0 := by
    rw [dotProduct_comm]; exact h01
  have hA0 : A *ᵥ hA.eigvec (topIndex n) = hA.largestEigenvalue • hA.eigvec (topIndex n) := by
    rw [mulVec_eigvec, eigenvalues_topIndex]
  have hA1 : A *ᵥ hA.eigvec (secondIndex n)
      = hA.secondEigenvalue • hA.eigvec (secondIndex n) := by
    rw [mulVec_eigvec, eigenvalues_secondIndex]
  -- Work inside the plane spanned by the top two eigenvectors `u₀`, `u₁`.
  generalize hA.eigvec (topIndex n) = u₀ at h00 h01 h10 hA0
  generalize hA.eigvec (secondIndex n) = u₁ at h11 h01 h10 hA1
  by_cases hab : u₀ ⬝ᵥ w = 0 ∧ u₁ ⬝ᵥ w = 0
  · refine ⟨u₁, ?_, hab.2, ?_⟩
    · intro h; rw [h] at h11; simp at h11
    · rw [hA1, dotProduct_smul, smul_eq_mul, h11]
  · -- `x = (u₁ ⬝ w) u₀ − (u₀ ⬝ w) u₁` is orthogonal to `w` and nonzero.
    have hxx : ((u₁ ⬝ᵥ w) • u₀ - (u₀ ⬝ᵥ w) • u₁) ⬝ᵥ ((u₁ ⬝ᵥ w) • u₀ - (u₀ ⬝ᵥ w) • u₁)
        = (u₁ ⬝ᵥ w) ^ 2 + (u₀ ⬝ᵥ w) ^ 2 := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        h00, h11, h01, h10]
      ring
    refine ⟨(u₁ ⬝ᵥ w) • u₀ - (u₀ ⬝ᵥ w) • u₁, ?_, ?_, ?_⟩
    · intro hx
      rw [hx] at hxx
      simp only [zero_dotProduct] at hxx
      exact hab ⟨by nlinarith [sq_nonneg (u₀ ⬝ᵥ w), sq_nonneg (u₁ ⬝ᵥ w)],
        by nlinarith [sq_nonneg (u₀ ⬝ᵥ w), sq_nonneg (u₁ ⬝ᵥ w)]⟩
    · simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
      ring
    · rw [hxx, mulVec_sub, mulVec_smul, mulVec_smul, hA0, hA1]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        h00, h11, h01, h10]
      nlinarith [mul_le_mul_of_nonneg_right hA.secondEigenvalue_le_largestEigenvalue
        (sq_nonneg (u₁ ⬝ᵥ w))]

/-- An eigenvector for the largest eigenvalue has no component along any eigenvector whose
eigenvalue is strictly smaller. -/
theorem coeff_eq_zero_of_lt [Nonempty n] {w : n → ℝ}
    (hAw : A *ᵥ w = hA.largestEigenvalue • w) {j : n}
    (hj : hA.eigenvalues j < hA.largestEigenvalue) : hA.coeff w j = 0 := by
  have h1 : hA.coeff (A *ᵥ w) j = hA.eigenvalues j * hA.coeff w j := hA.coeff_mulVec w j
  rw [hAw, coeff_smul] at h1
  have h3 : (hA.largestEigenvalue - hA.eigenvalues j) * hA.coeff w j = 0 := by
    rw [sub_mul]; linarith
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · exact h

/-- **An eigenvector for `λ₂` orthogonal to a given top eigenvector.** If `A w = λ₁ w`, there
is a nonzero `x ⟂ w` with `A x = λ₂ x`. -/
theorem exists_eigenvector_second [Nontrivial n] {w : n → ℝ}
    (hAw : A *ᵥ w = hA.largestEigenvalue • w) :
    ∃ x : n → ℝ, x ≠ 0 ∧ x ⬝ᵥ w = 0 ∧ A *ᵥ x = hA.secondEigenvalue • x := by
  have h11 : hA.eigvec (secondIndex n) ⬝ᵥ hA.eigvec (secondIndex n) = 1 := by
    simp [eigvec_dotProduct_eigvec]
  have hA1 : A *ᵥ hA.eigvec (secondIndex n)
      = hA.secondEigenvalue • hA.eigvec (secondIndex n) := by
    rw [mulVec_eigvec, eigenvalues_secondIndex]
  rcases hA.secondEigenvalue_le_largestEigenvalue.eq_or_lt with heq | hlt
  · -- `λ₂ = λ₁`: the top eigenspace contains the plane spanned by `u₀`, `u₁`.
    have h00 : hA.eigvec (topIndex n) ⬝ᵥ hA.eigvec (topIndex n) = 1 := by
      simp [eigvec_dotProduct_eigvec]
    have h01 : hA.eigvec (topIndex n) ⬝ᵥ hA.eigvec (secondIndex n) = 0 := by
      simp [eigvec_dotProduct_eigvec, topIndex_ne_secondIndex]
    have h10 : hA.eigvec (secondIndex n) ⬝ᵥ hA.eigvec (topIndex n) = 0 := by
      rw [dotProduct_comm]; exact h01
    have hA0 : A *ᵥ hA.eigvec (topIndex n)
        = hA.secondEigenvalue • hA.eigvec (topIndex n) := by
      rw [mulVec_eigvec, eigenvalues_topIndex, heq]
    generalize hA.eigvec (topIndex n) = u₀ at h00 h01 h10 hA0
    generalize hA.eigvec (secondIndex n) = u₁ at h11 h01 h10 hA1
    by_cases hab : u₀ ⬝ᵥ w = 0 ∧ u₁ ⬝ᵥ w = 0
    · refine ⟨u₁, ?_, hab.2, hA1⟩
      intro h; rw [h] at h11; simp at h11
    · have hxx : ((u₁ ⬝ᵥ w) • u₀ - (u₀ ⬝ᵥ w) • u₁) ⬝ᵥ ((u₁ ⬝ᵥ w) • u₀ - (u₀ ⬝ᵥ w) • u₁)
          = (u₁ ⬝ᵥ w) ^ 2 + (u₀ ⬝ᵥ w) ^ 2 := by
        simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
          h00, h11, h01, h10]
        ring
      refine ⟨(u₁ ⬝ᵥ w) • u₀ - (u₀ ⬝ᵥ w) • u₁, ?_, ?_, ?_⟩
      · intro hx
        rw [hx] at hxx
        simp only [zero_dotProduct] at hxx
        exact hab ⟨by nlinarith [sq_nonneg (u₀ ⬝ᵥ w), sq_nonneg (u₁ ⬝ᵥ w)],
          by nlinarith [sq_nonneg (u₀ ⬝ᵥ w), sq_nonneg (u₁ ⬝ᵥ w)]⟩
      · simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
        ring
      · rw [mulVec_sub, mulVec_smul, mulVec_smul, hA0, hA1]
        ext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
  · -- `λ₂ < λ₁`: `w` has no component along the second eigenvector.
    refine ⟨hA.eigvec (secondIndex n), hA.eigvec_ne_zero _, ?_, hA1⟩
    exact hA.coeff_eq_zero_of_lt hAw (by rw [eigenvalues_secondIndex]; exact hlt)

end Matrix.IsHermitian
