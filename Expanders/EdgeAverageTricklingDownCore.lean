/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.EdgeAverageTricklingDownLocal
import Expanders.TricklingDownSpectral

/-!
# Edge-average trickling down, part 2: triangle weights

This file proves the edge-average trickling-down theorem for an abstract **triangle weight**
`T : ι → ι → ι → ℝ` (`IsTriangleWeight`): symmetric in its three arguments, nonnegative, and
zero when two arguments agree. Think of `T a b c` as the weight of the triangle `{a, b, c}`. Then:
* the link of `z` is the weighted graph `T z` (edge `b c` of weight `T z b c`);
* the underlying graph is `w`, with `Σ_c T a b c = k · w a b` for a constant `k > 0`.

For a pure `d`-dimensional complex with top weight `m`, `T a b c = linkWeightOf m {a} b c` is a
triangle weight with `k = d − 1` (`Expanders/EdgeAverageTricklingDown.lean`).

## The theorem (`walkSecondEigenvalueLE_of_edge_average`)

Let `w` be connected. Let the link `T z` have second eigenvalue at most `lam z`, and be
connected if `lam z ≥ 1` (a link with `lam z < 1` is connected anyway:
`eq_of_walkSecondEigenvalueLE_lt_one`). Suppose `(lam u + lam v) / 2 ≤ l` on every edge `u v`
of `w`, where `l < 1`. Then `w` has second eigenvalue at most `l / (1 − l)`.

## Proof

The proof does not go through vertex eigenfunctions. It goes through the **edge walk**, the
random walk on (ordered) pairs `edgeWalkWeight T`: from the edge `a b`, choose `c` with
probability proportional to `T a b c`, then move to `a c` or `b c`. Around a vertex `a` the
edge walk is the walk on the link of `a`. This is Chen–Liu's integrated Bochner method
(arXiv:2609.19514, Section 2) for facets of size three, written on the edge level.

1. *A vertex function gives an edge function.* For `f` of mean zero, put
   `φ (a, b) = f a + f b`. Its Rayleigh quotient for the edge walk is `(N + 3Q) / (2N + 2Q)`,
   where `N = Σ deg f²` and `Q = Σ w f f`. So if `Q > (l / (1 − l)) N`, the edge walk has
   Rayleigh quotient above `1/2 + l` at `φ`.
2. *An eigenfunction.* By `exists_walk_eigenfunction_of_lt` (the spectral theorem), the edge walk
   then has an eigenfunction `g` with eigenvalue `α > 1/2 + l`, not orthogonal to `φ`.
   Symmetrising `g` keeps both properties.
3. *Bochner on every link* (`edge_eigen_ineq`). On the triangles through `z`, consider the
   function `g z b + g z c + g b c`. The eigenvalue equation makes its average around `b` equal
   to `(1 + 2α) g z b`. Apply `local_bochner` at every `z` and sum over `z`. The local gaps enter
   as `Σ_z lam z · Σ_b V z b`, where `V z b ≥ 0` is the variance on the link of the edge `z b`,
   and `V` is symmetric. So they average over edges:
   `Σ_z lam z Σ_b V z b = ½ Σ_{z,b} (lam z + lam b) V z b ≤ l Σ V`.
   This is the one place where the edge average replaces the minimum. Every remaining sum is a
   multiple of `G₂ = Σ w g²`, and the result is `(1 + 2α)(1 − α)(1 + 2l − 2α) G₂ ≥ 0`.
4. Since `α > 1/2 + l ≥ −1/2`, this forces `α ≥ 1`. Then
   `Σ T a b c (g a b − g a c)² = 2 (1 − α) G₂ ≤ 0`, so `g a b = g a c` on every triangle. The
   links are connected (by hypothesis where `lam a ≥ 1`, by the gap where `lam a < 1`), so
   `g a ·` is constant. Connectivity of `w` makes `g` constant, so `g` is orthogonal to `φ`.
   This is a contradiction.

## Theorems
* `eq_of_walkSecondEigenvalueLE_lt_one`: a weighted graph whose second eigenvalue is at most
  `lam < 1` is connected. **Proved.**
* `IsTriangleWeight.cycle`, `sum_mul_sq_fst`, `sum_mul_sq_snd`, `sum_mul_sq_third`,
  `sum_mul_mul_shared_b`, `sum_mul_mul_shared_c`: relabelling triple sums. **Proved.**
* `IsTriangleWeight.sum_mul_mul_eq_of_eigen`, `IsTriangleWeight.sum_sq_sub_eq_of_eigen`:
  moments of an eigenfunction of the edge walk. **Proved.**
* `IsTriangleWeight.edge_eigen_ineq`: the eigenvalue inequality of step 3. **Proved.**
* `edgeWalkWeight`, `sum_edgeWalkWeight_mul`, `sum_edgeWalkWeight`,
  `IsTriangleWeight.edgeWalkWeight_symm`: the edge walk as a weighted graph on `ι × ι`.
  **Proved.**
* `IsTriangleWeight.walkSecondEigenvalueLE_of_edge_average`: the theorem. **Proved.**
-/

open Finset

namespace EdgeAverageTricklingDown

variable {ι : Type*} [Fintype ι]

/-- `T` is a **triangle weight**: `T a b c` is symmetric in `a, b, c`, nonnegative, and zero
when two arguments agree. (`swap12`, `swap23` generate all permutations; with them `loop` gives
zero whenever any two arguments agree: `loop_left`, `loop_mid`.)

For a pure complex with top weight `m`, `T a b c = linkWeightOf m {a} b c` is a triangle weight,
whatever the dimension. Nothing requires `T` to come from a complex: any nonnegative weight on
the 3-subsets of `ι` is one. -/
structure IsTriangleWeight (T : ι → ι → ι → ℝ) : Prop where
  /-- Symmetry in the first two arguments. -/
  swap12 : ∀ a b c, T a b c = T b a c
  /-- Symmetry in the last two arguments. -/
  swap23 : ∀ a b c, T a b c = T a c b
  /-- Nonnegativity. -/
  nonneg : ∀ a b c, 0 ≤ T a b c
  /-- No degenerate triangles. -/
  loop : ∀ a b, T a b b = 0

namespace IsTriangleWeight

variable {T : ι → ι → ι → ℝ}

omit [Fintype ι] in
theorem cycle (hT : IsTriangleWeight T) (a b c : ι) : T a b c = T b c a := by
  rw [hT.swap12 a b c, hT.swap23 b a c]

omit [Fintype ι] in
theorem loop_mid (hT : IsTriangleWeight T) (a b : ι) : T a b a = 0 := by
  rw [hT.swap12 a b a, hT.loop b a]

omit [Fintype ι] in
theorem loop_left (hT : IsTriangleWeight T) (a b : ι) : T a a b = 0 := by
  rw [hT.swap23 a a b, hT.loop_mid a b]

/-! ### Relabelling triple sums -/

theorem sum_mul_sq_fst (g : ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, T a b c * g a b ^ 2 = ∑ a, ∑ b, (∑ c, T a b c) * g a b ^ 2 :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (Finset.sum_mul _ _ _).symm

theorem sum_mul_sq_snd (hT : IsTriangleWeight T) (g : ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, T a b c * g a c ^ 2 = ∑ a, ∑ b, (∑ c, T a b c) * g a b ^ 2 := by
  rw [← sum_mul_sq_fst]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by
    rw [hT.swap23 a c b]

theorem sum_mul_sq_third (hT : IsTriangleWeight T) (g : ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, T a b c * g b c ^ 2 = ∑ a, ∑ b, (∑ c, T a b c) * g a b ^ 2 := by
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by rw [hT.cycle a b c]

/-- Two edges of a triangle sharing their second vertex, relabelled to share the first. -/
theorem sum_mul_mul_shared_b (hT : IsTriangleWeight T) {g : ι → ι → ℝ}
    (hg : ∀ a b, g a b = g b a) :
    ∑ a, ∑ b, ∑ c, T a b c * g a b * g b c = ∑ a, ∑ b, ∑ c, T a b c * g a b * g a c := by
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => by rw [hT.swap12 b a c, hg b a]

/-- Two edges of a triangle sharing their last vertex, relabelled to share the first. -/
theorem sum_mul_mul_shared_c (hT : IsTriangleWeight T) {g : ι → ι → ℝ}
    (hg : ∀ a b, g a b = g b a) :
    ∑ a, ∑ b, ∑ c, T a b c * g a c * g b c = ∑ a, ∑ b, ∑ c, T a b c * g a b * g a c := by
  have e : ∀ a, ∑ b, ∑ c, T a b c * g a c * g b c = ∑ c, ∑ b, T a b c * g a c * g b c :=
    fun a => Finset.sum_comm
  rw [Finset.sum_congr rfl fun a _ => e a]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => by rw [← hT.cycle a b c, hg b a, hg c a]

end IsTriangleWeight

/-- **A gap forces connectivity.** If the random walk on `w` (symmetric, nonnegative) has second
eigenvalue at most `lam < 1`, then `w` is connected: a function constant along every edge of
positive weight takes one value on the vertices of positive degree.

Proof: if `F u ≠ F v`, let `g` be the indicator of `{x | F x = F u}`, `D` the total degree and
`D₁ = Σ deg · g`. The function `D g − D₁` has mean zero, and both sides of the defining inequality
equal `D D₁ (D − D₁) > 0` on it, which forces `lam ≥ 1`.

This is the same statement as `WalkSecondEigenvalueLE.eq_of_forall_pos` in
`Expanders/WeightedCheeger.lean`; it is repeated here so that this file does not import that one. -/
theorem eq_of_walkSecondEigenvalueLE_lt_one {w : ι → ι → ℝ} (hsymm : ∀ u v, w u v = w v u)
    (hnn : ∀ u v, 0 ≤ w u v) {lam : ℝ} (h : WalkSecondEigenvalueLE w lam) (hlam : lam < 1)
    (F : ι → ℝ) (hF : ∀ u v, 0 < w u v → F u = F v) (u v : ι) (hu : 0 < ∑ x, w u x)
    (hv : 0 < ∑ x, w v x) : F u = F v := by
  classical
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g : ι → ℝ, g = fun x => if F x = F u then 1 else 0 := ⟨_, rfl⟩
  have hD0 : ∀ x, 0 ≤ ∑ y, w x y := fun x => Finset.sum_nonneg fun y _ => hnn x y
  have hgedge : ∀ x y, w x y * g y = w x y * g x := by
    intro x y
    rcases (hnn x y).eq_or_lt with h0 | h0
    · rw [← h0]; ring
    · simp only [hg, hF x y h0]
  have hgsq : ∀ x, g x ^ 2 = g x := fun x => by simp only [hg]; split_ifs <;> norm_num
  have hg01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1 := fun x => by simp only [hg]; split_ifs <;> norm_num
  have hgu : g u = 1 := by rw [hg]; exact if_pos rfl
  have hgv : g v = 0 := by rw [hg]; exact if_neg fun h => hne h.symm
  obtain ⟨D, hD⟩ : ∃ D, D = ∑ x, ∑ y, w x y := ⟨_, rfl⟩
  obtain ⟨D1, hD1⟩ : ∃ D1, D1 = ∑ x, (∑ y, w x y) * g x := ⟨_, rfl⟩
  have hQg : ∑ x, ∑ y, w x y * g x * g y = D1 := by
    rw [hD1]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [mul_assoc, mul_comm (g x), ← mul_assoc, hgedge x y, mul_assoc, ← sq, hgsq]
  have hS1 : ∑ x, ∑ y, w x y * g x = D1 := by
    rw [hD1]; exact Finset.sum_congr rfl fun x _ => (Finset.sum_mul _ _ _).symm
  have hS2 : ∑ x, ∑ y, w x y * g y = D1 := by
    rw [Finset.sum_comm, ← hS1]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [hsymm y x]
  have hN1 : ∑ x, (∑ y, w x y) * g x ^ 2 = D1 := by
    rw [hD1]; exact Finset.sum_congr rfl fun x _ => by rw [hgsq]
  -- `D₁ ≥ deg u > 0` and `D − D₁ ≥ deg v > 0`
  have hD1u : 0 < D1 := by
    rw [hD1]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun x _ =>
      mul_nonneg (hD0 x) (hg01 x).1) (Finset.mem_univ u))
    rw [hgu, mul_one]; exact hu
  have hD2v : 0 < D - D1 := by
    have e : D - D1 = ∑ x, (∑ y, w x y) * (1 - g x) := by
      rw [hD, hD1, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun x _ =>
      mul_nonneg (hD0 x) (by linarith [(hg01 x).2])) (Finset.mem_univ v))
    rw [hgv, sub_zero, mul_one]; exact hv
  -- the test function `D g − D₁`
  have hmean : ∑ x, (∑ y, w x y) * (D * g x - D1) = 0 := by
    have e : ∑ x, (∑ y, w x y) * (D * g x - D1) =
        D * ∑ x, (∑ y, w x y) * g x - D1 * ∑ x, ∑ y, w x y := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e, ← hD1, ← hD]; ring
  have h1 := h (fun x => D * g x - D1) hmean
  have eQ : ∑ x, ∑ y, w x y * (D * g x - D1) * (D * g y - D1) = D * D1 * (D - D1) := by
    have e : ∀ x y, w x y * (D * g x - D1) * (D * g y - D1) =
        D ^ 2 * (w x y * g x * g y) - D * D1 * (w x y * g x) - D * D1 * (w x y * g y)
          + D1 ^ 2 * w x y := fun x y => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hQg, hS1, hS2, ← hD]
    ring
  have eN : ∑ x, (∑ y, w x y) * (D * g x - D1) ^ 2 = D * D1 * (D - D1) := by
    have e : ∀ x, (∑ y, w x y) * (D * g x - D1) ^ 2 =
        D ^ 2 * ((∑ y, w x y) * g x ^ 2) - 2 * D * D1 * ((∑ y, w x y) * g x)
          + D1 ^ 2 * ∑ y, w x y := fun x => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hN1, ← hD1, ← hD]
    ring
  rw [eQ, eN] at h1
  have hpos : 0 < D * D1 * (D - D1) := by
    have hDpos : 0 < D := by linarith
    positivity
  nlinarith [mul_pos (sub_pos.mpr hlam) hpos]

namespace IsTriangleWeight

variable {T : ι → ι → ι → ℝ}

/-! ### Eigenfunctions of the edge walk -/

/-- For a symmetric eigenfunction `g` of the edge walk with eigenvalue `α`, in the form
`Σ_c T a b c (g a c + g b c) = 2α (Σ_c T a b c) g a b`, the correlation of `g` along pairs of
edges of a triangle is `α` times `G₂ = Σ w g²`. -/
theorem sum_mul_mul_eq_of_eigen (hT : IsTriangleWeight T) {g : ι → ι → ℝ}
    (hg : ∀ a b, g a b = g b a) {α : ℝ}
    (heig : ∀ a b, ∑ c, T a b c * (g a c + g b c) = 2 * α * (∑ c, T a b c) * g a b) :
    ∑ a, ∑ b, ∑ c, T a b c * g a b * g a c = α * ∑ a, ∑ b, (∑ c, T a b c) * g a b ^ 2 := by
  have h1 : ∑ a, ∑ b, g a b * ∑ c, T a b c * (g a c + g b c) =
      2 * α * ∑ a, ∑ b, (∑ c, T a b c) * g a b ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [heig a b]; ring
  have h2 : ∑ a, ∑ b, g a b * ∑ c, T a b c * (g a c + g b c) =
      ∑ a, ∑ b, ∑ c, T a b c * g a b * g a c + ∑ a, ∑ b, ∑ c, T a b c * g a b * g b c := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hT.sum_mul_mul_shared_b hg] at h2
  linarith

/-- For a symmetric eigenfunction of the edge walk with eigenvalue `α`,
`Σ T a b c (g a b − g a c)² = 2 (1 − α) G₂`. -/
theorem sum_sq_sub_eq_of_eigen (hT : IsTriangleWeight T) {g : ι → ι → ℝ}
    (hg : ∀ a b, g a b = g b a) {α : ℝ}
    (heig : ∀ a b, ∑ c, T a b c * (g a c + g b c) = 2 * α * (∑ c, T a b c) * g a b) :
    ∑ a, ∑ b, ∑ c, T a b c * (g a b - g a c) ^ 2 =
      2 * (1 - α) * ∑ a, ∑ b, (∑ c, T a b c) * g a b ^ 2 := by
  have e : ∀ a b c, T a b c * (g a b - g a c) ^ 2 =
      T a b c * g a b ^ 2 + T a b c * g a c ^ 2 - 2 * (T a b c * g a b * g a c) :=
    fun a b c => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_mul_sq_fst, hT.sum_mul_sq_snd, hT.sum_mul_mul_eq_of_eigen hg heig]
  ring

/-- **The eigenvalue inequality.** Let `T` be a triangle weight. Let every link `T z` have second
eigenvalue at most `lam z`, and let `lam u + lam v ≤ 2l` whenever `Σ_c T u v c > 0`. If `g` is a
symmetric eigenfunction of the edge walk with eigenvalue `α`, in the form
`Σ_c T a b c (g a c + g b c) = 2α (Σ_c T a b c) g a b`, then
`(1 + 2α)(1 − α)(1 + 2l − 2α) · Σ_{a,b} (Σ_c T a b c) g a b² ≥ 0`.

Degenerate cases: if `g` vanishes on every edge the inequality is `0 ≤ 0`. No connectivity is
assumed. A disconnected link has `lam z ≥ 1`, which is allowed, and `local_bochner` covers it.
Vertices in no triangle contribute nothing, whatever `lam z` is there. -/
theorem edge_eigen_ineq (hT : IsTriangleWeight T) {lam : ι → ℝ}
    (hlam : ∀ z, WalkSecondEigenvalueLE (T z) (lam z)) {l : ℝ}
    (hedge : ∀ u v, 0 < ∑ c, T u v c → lam u + lam v ≤ 2 * l)
    {g : ι → ι → ℝ} (hg : ∀ a b, g a b = g b a) {α : ℝ}
    (heig : ∀ a b, ∑ c, T a b c * (g a c + g b c) = 2 * α * (∑ c, T a b c) * g a b) :
    0 ≤ (1 + 2 * α) * (1 - α) * (1 + 2 * l - 2 * α) *
      ∑ a, ∑ b, (∑ c, T a b c) * g a b ^ 2 := by
  obtain ⟨G2, hG2⟩ : ∃ G2, G2 = ∑ a, ∑ b, (∑ c, T a b c) * g a b ^ 2 := ⟨_, rfl⟩
  rw [← hG2]
  have hQ := hT.sum_mul_mul_eq_of_eigen hg heig
  rw [← hG2] at hQ
  -- the average around `b`, in the link of `z`, of the function `g z b + g z c + g b c`
  have hH : ∀ z b, ∑ c, T z b c * (g z b + g z c + g b c) =
      (1 + 2 * α) * g z b * ∑ c, T z b c := by
    intro z b
    have e : ∑ c, T z b c * (g z b + g z c + g b c) =
        g z b * ∑ c, T z b c + ∑ c, T z b c * (g z c + g b c) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e, heig z b]; ring
  -- the three moments of every link
  obtain ⟨SZ, hSZ⟩ : ∃ SZ : ι → ℝ,
      SZ = fun z => ∑ b, ∑ c, T z b c * (g z b + g z c + g b c) ^ 2 := ⟨_, rfl⟩
  obtain ⟨AZ, hAZ⟩ : ∃ AZ : ι → ℝ,
      AZ = fun z => ∑ b, (∑ c, T z b c) * ((1 + 2 * α) * g z b) ^ 2 := ⟨_, rfl⟩
  obtain ⟨BZ, hBZ⟩ : ∃ BZ : ι → ℝ,
      BZ = fun z => ∑ b, ∑ c, T z b c * ((1 + 2 * α) * g z b) * ((1 + 2 * α) * g z c) :=
    ⟨_, rfl⟩
  -- the Bochner inequality of every link
  have hloc : ∀ z, 0 ≤ (2 + 2 * lam z) * SZ z - (4 + 2 * lam z) * AZ z + 2 * BZ z := by
    intro z
    simp only [hSZ, hAZ, hBZ]
    exact local_bochner (hT.swap23 z) (hT.nonneg z) (hT.loop z) (hlam z)
      (fun b c => g z b + g z c + g b c)
      (fun b c => by
        show g z b + g z c + g b c = g z c + g z b + g c b
        rw [hg b c]; ring)
      (fun b => (1 + 2 * α) * g z b) (fun b => hH z b)
  have hsum : 0 ≤ ∑ z, ((2 + 2 * lam z) * SZ z - (4 + 2 * lam z) * AZ z + 2 * BZ z) :=
    Finset.sum_nonneg fun z _ => hloc z
  have hsplit : ∑ z, ((2 + 2 * lam z) * SZ z - (4 + 2 * lam z) * AZ z + 2 * BZ z) =
      2 * ∑ z, SZ z - 4 * ∑ z, AZ z + 2 * ∑ z, BZ z + 2 * ∑ z, lam z * (SZ z - AZ z) := by
    have e : ∀ z, (2 + 2 * lam z) * SZ z - (4 + 2 * lam z) * AZ z + 2 * BZ z =
        2 * SZ z - 4 * AZ z + 2 * BZ z + 2 * (lam z * (SZ z - AZ z)) := fun z => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- the sums over `z`, in terms of `G₂`
  have eS : ∑ z, SZ z = (3 + 6 * α) * G2 := by
    simp only [hSZ]
    have e : ∀ z b c, T z b c * (g z b + g z c + g b c) ^ 2 =
        T z b c * g z b ^ 2 + T z b c * g z c ^ 2 + T z b c * g b c ^ 2
          + 2 * (T z b c * g z b * g z c) + 2 * (T z b c * g z b * g b c)
          + 2 * (T z b c * g z c * g b c) := fun z b c => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_mul_sq_fst, hT.sum_mul_sq_snd, hT.sum_mul_sq_third, hT.sum_mul_mul_shared_b hg,
      hT.sum_mul_mul_shared_c hg, hQ, ← hG2]
    ring
  have eA : ∑ z, AZ z = (1 + 2 * α) ^ 2 * G2 := by
    simp only [hAZ, hG2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun b _ => by ring
  have eB : ∑ z, BZ z = (1 + 2 * α) ^ 2 * (α * G2) := by
    rw [← hQ]
    simp only [hBZ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => by ring
  -- the edge variances `V z b`
  obtain ⟨V, hV⟩ : ∃ V : ι → ι → ℝ, V = fun z b =>
      ∑ c, T z b c * (g z b + g z c + g b c - (1 + 2 * α) * g z b) ^ 2 := ⟨_, rfl⟩
  have hVsum : ∀ z, ∑ b, V z b = SZ z - AZ z := by
    intro z
    simp only [hV, hSZ, hAZ, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e : ∀ c, T z b c * (g z b + g z c + g b c - (1 + 2 * α) * g z b) ^ 2 =
        T z b c * (g z b + g z c + g b c) ^ 2
          - 2 * ((1 + 2 * α) * g z b) * (T z b c * (g z b + g z c + g b c))
          + ((1 + 2 * α) * g z b) ^ 2 * T z b c := fun c => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hH z b]
    ring
  have hVnn : ∀ z b, 0 ≤ V z b := fun z b => by
    simp only [hV]
    exact Finset.sum_nonneg fun c _ => mul_nonneg (hT.nonneg z b c) (sq_nonneg _)
  have hVsymm : ∀ z b, V z b = V b z := fun z b => by
    simp only [hV]
    exact Finset.sum_congr rfl fun c _ => by rw [hT.swap12 z b c, hg z b]; ring
  have hVzero : ∀ z b, ¬ 0 < ∑ c, T z b c → V z b = 0 := by
    intro z b h
    have h0 : ∑ c, T z b c = 0 :=
      le_antisymm (not_lt.mp h) (Finset.sum_nonneg fun c _ => hT.nonneg z b c)
    have hT0 : ∀ c, T z b c = 0 := fun c =>
      (Finset.sum_eq_zero_iff_of_nonneg fun c _ => hT.nonneg z b c).mp h0 c (Finset.mem_univ c)
    simp only [hV, hT0, zero_mul, Finset.sum_const_zero]
  -- **the edge average**: the local gaps only enter through `lam z + lam b` on edges `z b`
  have havg : ∑ z, lam z * (SZ z - AZ z) ≤ l * (∑ z, SZ z - ∑ z, AZ z) := by
    rw [← Finset.sum_sub_distrib]
    simp only [← hVsum]
    have e1 : ∑ z, lam z * ∑ b, V z b = ∑ z, ∑ b, lam z * V z b :=
      Finset.sum_congr rfl fun z _ => Finset.mul_sum _ _ _
    have e2 : ∑ z, ∑ b, lam z * V z b = ∑ z, ∑ b, lam b * V z b := by
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun b _ => by rw [hVsymm b z]
    have e3 : ∑ z, ∑ b, (lam z + lam b) * V z b ≤ ∑ z, ∑ b, 2 * l * V z b := by
      refine Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun b _ => ?_
      by_cases hp : 0 < ∑ c, T z b c
      · exact mul_le_mul_of_nonneg_right (hedge z b hp) (hVnn z b)
      · rw [hVzero z b hp]; simp
    have e4 : ∑ z, ∑ b, (lam z + lam b) * V z b =
        ∑ z, ∑ b, lam z * V z b + ∑ z, ∑ b, lam b * V z b := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    have e5 : ∑ z, ∑ b, 2 * l * V z b = 2 * (l * ∑ z, ∑ b, V z b) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun b _ => by ring
    rw [e1]
    linarith
  rw [hsplit, eS, eA, eB] at hsum
  rw [eS, eA] at havg
  have key : (1 + 2 * α) * (1 - α) * (1 + 2 * l - 2 * α) * G2 =
      (2 * ((3 + 6 * α) * G2) - 4 * ((1 + 2 * α) ^ 2 * G2) + 2 * ((1 + 2 * α) ^ 2 * (α * G2))
        + 2 * (l * ((3 + 6 * α) * G2 - (1 + 2 * α) ^ 2 * G2))) / 2 := by ring
  rw [key]
  linarith

end IsTriangleWeight

/-! ### The edge walk -/

variable [DecidableEq ι]

/-- The **edge walk** of a triangle weight, as a weighted graph on ordered pairs. The pair `p`
is joined to every pair `q` that shares a vertex with it and completes it to a triangle, with
weight that triangle's weight (four terms, one for each way the vertices can coincide).

On a symmetric function `g` of pairs its walk is
`g ↦ (a b ↦ Σ_c T a b c (g a c + g b c) / (2 Σ_c T a b c))`: from `a b`, choose `c` with
probability proportional to `T a b c`, then move to `a c` or `b c` (`sum_edgeWalkWeight_mul`).
Its degrees are `4 Σ_c T a b c` (`sum_edgeWalkWeight`). The pairs `(a, a)`, and the pairs in no
triangle, are isolated. -/
def edgeWalkWeight (T : ι → ι → ι → ℝ) (p q : ι × ι) : ℝ :=
  (if p.1 = q.1 then T p.1 p.2 q.2 else 0) + (if p.1 = q.2 then T p.1 p.2 q.1 else 0) +
    (if p.2 = q.1 then T p.1 p.2 q.2 else 0) + (if p.2 = q.2 then T p.1 p.2 q.1 else 0)

omit [DecidableEq ι] in
theorem sum_ite_fst_eq (a : ι) (F : ι × ι → ℝ) [DecidablePred fun q : ι × ι => a = q.1] :
    ∑ q : ι × ι, (if a = q.1 then F q else 0) = ∑ c, F (a, c) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · exact Finset.sum_congr rfl fun c _ => if_pos rfl
  · intro b _ hb
    exact Finset.sum_eq_zero fun c _ => if_neg (Ne.symm hb)
  · intro h
    exact absurd (Finset.mem_univ a) h

omit [DecidableEq ι] in
theorem sum_ite_snd_eq (a : ι) (F : ι × ι → ℝ) [DecidablePred fun q : ι × ι => a = q.2] :
    ∑ q : ι × ι, (if a = q.2 then F q else 0) = ∑ c, F (c, a) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single a]
  · exact if_pos rfl
  · intro b _ hb
    exact if_neg (Ne.symm hb)
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The walk operator of `edgeWalkWeight`, in closed form. -/
theorem sum_edgeWalkWeight_mul (T : ι → ι → ι → ℝ) (g : ι × ι → ℝ) (p : ι × ι) :
    ∑ q, edgeWalkWeight T p q * g q =
      ∑ c, T p.1 p.2 c * (g (p.1, c) + g (c, p.1) + g (p.2, c) + g (c, p.2)) := by
  have e : ∀ q : ι × ι, edgeWalkWeight T p q * g q =
      (if p.1 = q.1 then T p.1 p.2 q.2 * g q else 0) +
        (if p.1 = q.2 then T p.1 p.2 q.1 * g q else 0) +
        (if p.2 = q.1 then T p.1 p.2 q.2 * g q else 0) +
        (if p.2 = q.2 then T p.1 p.2 q.1 * g q else 0) := by
    intro q
    unfold edgeWalkWeight
    split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib]
  rw [sum_ite_fst_eq p.1 (fun q => T p.1 p.2 q.2 * g q),
    sum_ite_snd_eq p.1 (fun q => T p.1 p.2 q.1 * g q),
    sum_ite_fst_eq p.2 (fun q => T p.1 p.2 q.2 * g q),
    sum_ite_snd_eq p.2 (fun q => T p.1 p.2 q.1 * g q)]
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- The degrees of the edge walk. -/
theorem sum_edgeWalkWeight (T : ι → ι → ι → ℝ) (p : ι × ι) :
    ∑ q, edgeWalkWeight T p q = 4 * ∑ c, T p.1 p.2 c := by
  have h := sum_edgeWalkWeight_mul T (fun _ => (1 : ℝ)) p
  simp only [mul_one] at h
  rw [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

namespace IsTriangleWeight

variable {T : ι → ι → ι → ℝ}

omit [Fintype ι] in
theorem edgeWalkWeight_nonneg (hT : IsTriangleWeight T) (p q : ι × ι) :
    0 ≤ edgeWalkWeight T p q := by
  unfold edgeWalkWeight
  have h1 := hT.nonneg p.1 p.2 q.1
  have h2 := hT.nonneg p.1 p.2 q.2
  split_ifs <;> linarith

omit [Fintype ι] in
theorem edgeWalkWeight_symm (hT : IsTriangleWeight T) (p q : ι × ι) :
    edgeWalkWeight T p q = edgeWalkWeight T q p := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  unfold edgeWalkWeight
  simp only
  have e1 : (if p1 = q1 then T p1 p2 q2 else 0) = (if q1 = p1 then T q1 q2 p2 else 0) := by
    by_cases h : p1 = q1
    · subst h; rw [if_pos rfl, if_pos rfl]; exact hT.swap23 _ _ _
    · rw [if_neg h, if_neg (Ne.symm h)]
  have e2 : (if p1 = q2 then T p1 p2 q1 else 0) = (if q2 = p1 then T q1 q2 p2 else 0) := by
    by_cases h : p1 = q2
    · subst h; rw [if_pos rfl, if_pos rfl]; exact (hT.cycle q1 p1 p2).symm
    · rw [if_neg h, if_neg (Ne.symm h)]
  have e3 : (if p2 = q1 then T p1 p2 q2 else 0) = (if q1 = p2 then T q1 q2 p1 else 0) := by
    by_cases h : p2 = q1
    · subst h; rw [if_pos rfl, if_pos rfl]; exact hT.cycle p1 p2 q2
    · rw [if_neg h, if_neg (Ne.symm h)]
  have e4 : (if p2 = q2 then T p1 p2 q1 else 0) = (if q2 = p2 then T q1 q2 p1 else 0) := by
    by_cases h : p2 = q2
    · subst h; rw [if_pos rfl, if_pos rfl, hT.swap12 p1 p2 q1, hT.swap23 p2 p1 q1,
        hT.swap12 p2 q1 p1]
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [e1, e2, e3, e4]
  ring

/-! ### The theorem -/

/-- **Edge-average trickling down, for a triangle weight.** Let `T` be a triangle weight and `w` a
weighted graph with `Σ_c T a b c = k · w a b`, `k > 0`. Suppose:
* `w` is connected: a function constant along its edges is constant on the vertices of positive
  degree;
* every link `T z` has second eigenvalue at most `lam z`;
* every link `T z` with `lam z ≥ 1` is connected, in the same sense. Where `lam z < 1` this
  follows from the gap (`eq_of_walkSecondEigenvalueLE_lt_one`);
* `(lam u + lam v) / 2 ≤ l` for every edge `u v` of `w`, with `l < 1`.

Then the random walk on `w` has second eigenvalue at most `l / (1 − l)`. Equivalently, its second
eigenvalue `μ` satisfies `μ / (1 + μ) ≤ l`.

Degenerate cases:
* `w` with no edges: the conclusion is vacuous (`walkSecondEigenvalueLE_of_forall_eq_zero`).
* `1/2 ≤ l < 1`: then `l / (1 − l) ≥ 1` and the conclusion holds for every graph.
* `l ≥ 1` is excluded. For `l > 1` the bound `l / (1 − l)` is negative and false in general. For
  `l = 1`, Lean's `1 / 0 = 0` would make the claim `μ ≤ 0`.
* `l < −1` cannot occur once `w` has an edge, since every link with an edge has `lam ≥ −1`.
* Vertices in no triangle carry no condition: their `lam` is unconstrained by the link bound and
  enters no edge average.

The connectivity hypotheses cannot be dropped. Two disjoint triangles have disconnected `w`
and `μ = 1`, but `l = −1`. The bowtie (two triangles sharing a vertex) has a disconnected link
at the shared vertex; there `l = 0`, but `μ = 1/2`.

With every `lam z = lam` this is the one-step Oppenheim bound `lam / (1 − lam)`
(`IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_step` for `σ = ∅`). -/
theorem walkSecondEigenvalueLE_of_edge_average (hT : IsTriangleWeight T) {w : ι → ι → ℝ}
    {k : ℝ} (hk : 0 < k) (hw : ∀ a b, ∑ c, T a b c = k * w a b)
    (hconn : ∀ F : ι → ℝ, (∀ u v, 0 < w u v → F u = F v) →
      ∀ u v, 0 < ∑ x, w u x → 0 < ∑ x, w v x → F u = F v)
    {lam : ι → ℝ} (hlam : ∀ z, WalkSecondEigenvalueLE (T z) (lam z))
    (hlink : ∀ z, 1 ≤ lam z → ∀ F : ι → ℝ, (∀ u v, 0 < T z u v → F u = F v) →
      ∀ u v, 0 < ∑ x, T z u x → 0 < ∑ x, T z v x → F u = F v)
    {l : ℝ} (hl : l < 1) (hedge : ∀ u v, 0 < w u v → (lam u + lam v) / 2 ≤ l) :
    WalkSecondEigenvalueLE w (l / (1 - l)) := by
  intro f hf
  by_contra hcon
  push Not at hcon
  obtain ⟨N, hN⟩ : ∃ N, N = ∑ u, (∑ x, w u x) * f u ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∑ u, ∑ x, w u x * f u * f x := ⟨_, rfl⟩
  rw [← hN, ← hQ] at hcon
  have h1l : 0 < 1 - l := by linarith
  have hlQ : l * N < Q * (1 - l) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ h1l] at hcon; exact hcon
  -- the graph `w`
  have hwk : ∀ a b, w a b = (∑ c, T a b c) / k := fun a b => by
    rw [hw, mul_div_cancel_left₀ _ hk.ne']
  have hwsymm : ∀ a b, w a b = w b a := fun a b => by
    rw [hwk, hwk]; congr 1; exact Finset.sum_congr rfl fun c _ => hT.swap12 a b c
  have hwnn : ∀ a b, 0 ≤ w a b := fun a b => by
    rw [hwk]; exact div_nonneg (Finset.sum_nonneg fun c _ => hT.nonneg a b c) hk.le
  have hpos_iff : ∀ a b, 0 < ∑ c, T a b c ↔ 0 < w a b := fun a b => by
    rw [hw]; exact mul_pos_iff_of_pos_left hk
  -- `w` has an edge, and so `l ≥ −1`
  obtain ⟨a0, b0, hab0⟩ : ∃ a b, 0 < w a b := by
    by_contra hne
    push Not at hne
    have hw0 : ∀ a b, w a b = 0 := fun a b => le_antisymm (hne a b) (hwnn a b)
    simp only [hN, hQ, hw0, zero_mul, Finset.sum_const_zero, mul_zero] at hcon
    exact lt_irrefl _ hcon
  have hl1 : -1 ≤ l := by
    have hd : 0 < ∑ c, T a0 b0 c := (hpos_iff a0 b0).mpr hab0
    obtain ⟨c0, -, hc0⟩ := (Finset.sum_pos_iff_of_nonneg fun c _ => hT.nonneg a0 b0 c).mp hd
    have hbc : b0 ≠ c0 := fun h => by rw [h, hT.loop] at hc0; exact lt_irrefl _ hc0
    have hac : a0 ≠ c0 := fun h => by rw [h, hT.loop_mid] at hc0; exact lt_irrefl _ hc0
    have h1 := neg_one_le_of_walkSecondEigenvalueLE (hT.swap23 a0) (hT.nonneg a0) (hlam a0)
      hbc hc0
    have h2 := neg_one_le_of_walkSecondEigenvalueLE (hT.swap23 b0) (hT.nonneg b0) (hlam b0)
      hac (by rw [hT.swap12]; exact hc0)
    have h3 := hedge a0 b0 hab0
    linarith
  -- the edge function `φ (a, b) = f a + f b`, and its Rayleigh quotient
  have hdeg : ∀ p : ι × ι, ∑ q, edgeWalkWeight T p q = 4 * k * w p.1 p.2 := fun p => by
    rw [sum_edgeWalkWeight, hw]; ring
  have hsq := sum_sum_mul_add_sq hwsymm f
  rw [← hN, ← hQ] at hsq
  have hnorm : ∑ p : ι × ι, (∑ q, edgeWalkWeight T p q) * (f p.1 + f p.2) ^ 2 =
      4 * k * (2 * N + 2 * Q) := by
    simp only [hdeg, Fintype.sum_prod_type]
    rw [← hsq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hTfa : ∑ a, ∑ b, ∑ c, T a b c * f a * f c = k * Q := by
    rw [hQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul,
      Finset.sum_congr rfl fun b _ => hT.swap23 a b c, hw]
    ring
  have hTfb : ∑ a, ∑ b, ∑ c, T a b c * f b * f c = k * Q := by
    rw [← hTfa]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => by rw [hT.swap12]
  have hquad : ∑ p : ι × ι, ∑ q, edgeWalkWeight T p q * (f p.1 + f p.2) * (f q.1 + f q.2) =
      k * (4 * N + 12 * Q) := by
    have e1 : ∀ p : ι × ι, ∑ q, edgeWalkWeight T p q * (f p.1 + f p.2) * (f q.1 + f q.2) =
        (f p.1 + f p.2) * ∑ c, T p.1 p.2 c * (2 * f p.1 + 2 * f p.2 + 4 * f c) := by
      intro p
      have h := sum_edgeWalkWeight_mul T (fun q => f q.1 + f q.2) p
      simp only at h
      have h' : ∑ q, edgeWalkWeight T p q * (f p.1 + f p.2) * (f q.1 + f q.2) =
          (f p.1 + f p.2) * ∑ q, edgeWalkWeight T p q * (f q.1 + f q.2) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
      rw [h', h]
      congr 1
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [Finset.sum_congr rfl fun p _ => e1 p, Fintype.sum_prod_type]
    simp only
    have e2 : ∀ a b, (f a + f b) * ∑ c, T a b c * (2 * f a + 2 * f b + 4 * f c) =
        2 * ∑ c, T a b c * (f a + f b) ^ 2 + 4 * ∑ c, T a b c * f a * f c
          + 4 * ∑ c, T a b c * f b * f c := by
      intro a b
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    simp only [e2, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hTfa, hTfb]
    have e3 : ∑ a, ∑ b, ∑ c, T a b c * (f a + f b) ^ 2 = k * (2 * N + 2 * Q) := by
      rw [← hsq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_mul, hw]; ring
    rw [e3]
    ring
  have hRay : (1 / 2 + l) * ∑ p : ι × ι, (∑ q, edgeWalkWeight T p q) * (f p.1 + f p.2) ^ 2 <
      ∑ p : ι × ι, ∑ q, edgeWalkWeight T p q * (f p.1 + f p.2) * (f q.1 + f q.2) := by
    rw [hnorm, hquad]
    nlinarith [mul_pos hk (by linarith : (0 : ℝ) < Q * (1 - l) - l * N)]
  -- an eigenfunction of the edge walk with eigenvalue `γ > 1/2 + l`
  obtain ⟨g, γ, hγ, heig, hgφ⟩ :=
    exists_walk_eigenfunction_of_lt hT.edgeWalkWeight_symm hT.edgeWalkWeight_nonneg hRay
  -- its symmetrisation
  obtain ⟨gs, hgs⟩ : ∃ gs : ι → ι → ℝ, gs = fun a b => (g (a, b) + g (b, a)) / 2 := ⟨_, rfl⟩
  have hgss : ∀ a b, gs a b = gs b a := fun a b => by rw [hgs]; ring
  have heig' : ∀ a b, ∑ c, T a b c * (gs a c + gs b c) = 2 * γ * (∑ c, T a b c) * gs a b := by
    intro a b
    have h1 := heig (a, b)
    have h2 := heig (b, a)
    rw [sum_edgeWalkWeight_mul, sum_edgeWalkWeight] at h1 h2
    simp only at h1 h2
    have hsw : ∑ c, T b a c = ∑ c, T a b c := Finset.sum_congr rfl fun c _ => hT.swap12 b a c
    have hX : ∑ c, T b a c * (g (b, c) + g (c, b) + g (a, c) + g (c, a)) =
        ∑ c, T a b c * (g (a, c) + g (c, a) + g (b, c) + g (c, b)) :=
      Finset.sum_congr rfl fun c _ => by rw [hT.swap12 b a c]; ring
    rw [hX, hsw] at h2
    have hY : ∑ c, T a b c * (gs a c + gs b c) =
        (∑ c, T a b c * (g (a, c) + g (c, a) + g (b, c) + g (c, b))) / 2 := by
      rw [hgs, Finset.sum_div]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [hY, hgs]
    simp only
    linarith
  -- `gs` is not orthogonal to `φ`, so `G₂ > 0`
  have hgφ' : ∑ a, ∑ b, (∑ c, T a b c) * gs a b * (f a + f b) ≠ 0 := by
    have e1 : ∑ p : ι × ι, (∑ q, edgeWalkWeight T p q) * g p * (f p.1 + f p.2) =
        4 * ∑ a, ∑ b, (∑ c, T a b c) * g (a, b) * (f a + f b) := by
      simp only [sum_edgeWalkWeight]
      simp only [Fintype.sum_prod_type]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    have e2 : ∑ a, ∑ b, (∑ c, T a b c) * g (b, a) * (f a + f b) =
        ∑ a, ∑ b, (∑ c, T a b c) * g (a, b) * (f a + f b) := by
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_congr rfl fun c _ => hT.swap12 b a c]
      ring
    have e3 : ∑ a, ∑ b, (∑ c, T a b c) * gs a b * (f a + f b) =
        (∑ a, ∑ b, (∑ c, T a b c) * g (a, b) * (f a + f b) +
          ∑ a, ∑ b, (∑ c, T a b c) * g (b, a) * (f a + f b)) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun b _ => by rw [hgs]; ring
    rw [e3, e2]
    intro h0
    apply hgφ
    rw [e1]
    linarith
  have hG2 : 0 < ∑ a, ∑ b, (∑ c, T a b c) * gs a b ^ 2 := by
    have hnn : ∀ a b, 0 ≤ (∑ c, T a b c) * gs a b ^ 2 := fun a b =>
      mul_nonneg (Finset.sum_nonneg fun c _ => hT.nonneg a b c) (sq_nonneg _)
    rcases (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hnn a b :
        0 ≤ ∑ a, ∑ b, (∑ c, T a b c) * gs a b ^ 2).eq_or_lt with h0 | h0
    · exfalso
      apply hgφ'
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => hnn a b).mp h0.symm a (Finset.mem_univ a)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => hnn a b).mp h1 b (Finset.mem_univ b)
      rcases mul_eq_zero.mp h2 with h | h
      · rw [h]; ring
      · rw [pow_eq_zero_iff two_ne_zero] at h; rw [h]; ring
    · exact h0
  -- the eigenvalue inequality forces `γ ≥ 1`
  have hedge' : ∀ u v, 0 < ∑ c, T u v c → lam u + lam v ≤ 2 * l := fun u v h => by
    have := hedge u v ((hpos_iff u v).mp h); linarith
  have hineq := hT.edge_eigen_ineq hlam hedge' hgss heig'
  have hγ1 : 1 ≤ γ := by
    by_contra hlt
    push Not at hlt
    have hA : 0 < (1 + 2 * γ) * (1 - γ) * (∑ a, ∑ b, (∑ c, T a b c) * gs a b ^ 2) :=
      mul_pos (mul_pos (by linarith) (by linarith)) hG2
    have hB : (1 + 2 * l - 2 * γ) < 0 := by linarith
    have := mul_neg_of_pos_of_neg hA hB
    linarith [show (1 + 2 * γ) * (1 - γ) * (1 + 2 * l - 2 * γ) *
        ∑ a, ∑ b, (∑ c, T a b c) * gs a b ^ 2 =
        (1 + 2 * γ) * (1 - γ) * (∑ a, ∑ b, (∑ c, T a b c) * gs a b ^ 2) *
          (1 + 2 * l - 2 * γ) by ring]
  -- so `gs` is harmonic: constant along every triangle
  have hharm0 := hT.sum_sq_sub_eq_of_eigen hgss heig'
  have hsq0 : ∑ a, ∑ b, ∑ c, T a b c * (gs a b - gs a c) ^ 2 = 0 := by
    have hnn3 : 0 ≤ ∑ a, ∑ b, ∑ c, T a b c * (gs a b - gs a c) ^ 2 :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ =>
        mul_nonneg (hT.nonneg a b c) (sq_nonneg _)
    have : 2 * (1 - γ) * ∑ a, ∑ b, (∑ c, T a b c) * gs a b ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hG2.le
    linarith
  have hharm : ∀ a b c, 0 < T a b c → gs a b = gs a c := by
    intro a b c hpos
    have hnn3 : ∀ a b c, 0 ≤ T a b c * (gs a b - gs a c) ^ 2 := fun a b c =>
      mul_nonneg (hT.nonneg a b c) (sq_nonneg _)
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      Finset.sum_nonneg fun c _ => hnn3 a b c).mp hsq0 a (Finset.mem_univ a)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => Finset.sum_nonneg fun c _ =>
      hnn3 a b c).mp h1 b (Finset.mem_univ b)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun c _ => hnn3 a b c).mp h2 c
      (Finset.mem_univ c)
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hpos.ne'
    · exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)
  -- connectivity of the links: `gs a ·` is constant on the link of `a`
  obtain ⟨Kf, hKf⟩ : ∃ Kf : ι → ℝ,
      Kf = fun a => (∑ b, (∑ c, T a b c) * gs a b) / ∑ b, ∑ c, T a b c := ⟨_, rfl⟩
  have hK : ∀ a b, 0 < ∑ c, T a b c → gs a b = Kf a := by
    intro a b hb
    have hconst : ∀ u v, 0 < ∑ x, T a u x → 0 < ∑ x, T a v x → gs a u = gs a v := by
      rcases lt_or_ge (lam a) 1 with hlt | hge
      · exact eq_of_walkSecondEigenvalueLE_lt_one (hT.swap23 a) (hT.nonneg a) (hlam a) hlt
          (gs a) (fun u v huv => hharm a u v huv)
      · exact hlink a hge (gs a) (fun u v huv => hharm a u v huv)
    have hDa : 0 < ∑ b, ∑ c, T a b c :=
      lt_of_lt_of_le hb (Finset.single_le_sum (fun b _ =>
        Finset.sum_nonneg fun c _ => hT.nonneg a b c) (Finset.mem_univ b))
    have hsum : ∑ b', (∑ c, T a b' c) * gs a b' = (∑ b', ∑ c, T a b' c) * gs a b := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rcases (Finset.sum_nonneg fun c _ => hT.nonneg a b' c :
          (0 : ℝ) ≤ ∑ c, T a b' c).eq_or_lt with h0 | h0
      · rw [← h0]; ring
      · rw [hconst b' b h0 hb]
    rw [hKf]
    simp only
    rw [hsum, mul_div_cancel_left₀ _ hDa.ne']
  -- connectivity of `w`: `Kf` is constant
  have hKedge : ∀ u v, 0 < w u v → Kf u = Kf v := by
    intro u v huv
    have h1 : 0 < ∑ c, T u v c := (hpos_iff u v).mpr huv
    have h2 : 0 < ∑ c, T v u c := (hpos_iff v u).mpr (by rw [hwsymm]; exact huv)
    rw [← hK u v h1, ← hK v u h2, hgss]
  have hdeg0 : 0 < ∑ x, w a0 x :=
    lt_of_lt_of_le hab0 (Finset.single_le_sum (fun x _ => hwnn a0 x) (Finset.mem_univ b0))
  have hconst : ∀ a b, 0 < ∑ c, T a b c → gs a b = Kf a0 := by
    intro a b hab
    have hwab : 0 < w a b := (hpos_iff a b).mp hab
    have hdega : 0 < ∑ x, w a x :=
      lt_of_lt_of_le hwab (Finset.single_le_sum (fun x _ => hwnn a x) (Finset.mem_univ b))
    rw [hK a b hab, hconn Kf hKedge a a0 hdega hdeg0]
  -- hence `gs` is orthogonal to `φ`: a contradiction
  apply hgφ'
  have e1 : ∑ a, ∑ b, (∑ c, T a b c) * gs a b * (f a + f b) =
      Kf a0 * ∑ a, ∑ b, (∑ c, T a b c) * (f a + f b) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases (Finset.sum_nonneg fun c _ => hT.nonneg a b c :
        (0 : ℝ) ≤ ∑ c, T a b c).eq_or_lt with h0 | h0
    · rw [← h0]; ring
    · rw [hconst a b h0]; ring
  have e2 : ∑ a, ∑ b, (∑ c, T a b c) * (f a + f b) = 2 * k * ∑ u, (∑ x, w u x) * f u := by
    have s1 : ∑ a, ∑ b, (∑ c, T a b c) * f a = k * ∑ u, (∑ x, w u x) * f u := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_mul, Finset.sum_congr rfl fun b _ => hw a b, ← Finset.mul_sum]
      ring
    have s2 : ∑ a, ∑ b, (∑ c, T a b c) * f b = ∑ a, ∑ b, (∑ c, T a b c) * f a := by
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [Finset.sum_congr rfl fun c _ => hT.swap12 b a c]
    have : ∑ a, ∑ b, (∑ c, T a b c) * (f a + f b) =
        ∑ a, ∑ b, (∑ c, T a b c) * f a + ∑ a, ∑ b, (∑ c, T a b c) * f b := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this, s2, s1]; ring
  rw [e1, e2, hf]
  ring

end IsTriangleWeight

end EdgeAverageTricklingDown
