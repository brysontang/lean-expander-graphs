/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.Cheeger
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Fourier.ZMod

/-!
# Cycles: exact spectrum, exact Cheeger constant, and sharpness of Cheeger's inequality

For `N ≥ 3` the cycle `C_N` (Mathlib's `cycleGraph N` on `Fin N`, where `u ~ v` when
`u − v = ±1` mod `N`) is `2`-regular. This file computes its second adjacency eigenvalue and its
Cheeger constant exactly:

  `λ₂(C_N) = 2 cos(2π/N)`,   `h(C_N) = 2 / ⌊N/2⌋`.

Since the spectral gap `2 − 2 cos(2π/N) ≤ (2π/N)²` is of order `1/N²` while `h(C_N)` is of order
`1/N`, the cycles show that the square-root ("hard") side `h(G) ≤ √(2d(d − λ₂))` of Cheeger's
inequality (`SimpleGraph.edgeExpansion_le_sqrt`) is tight up to the constant factor `π`, and that
its exponent `1/2` cannot be raised.

Throughout, the cycle is written `cycleGraph (n + 3)`, so `N = n + 3 ≥ 3`. The small cases are
excluded because they are genuinely different: `cycleGraph 0` and `cycleGraph 1` have no edges,
and `cycleGraph 2` is the complete graph `⊤` on `Fin 2`, which is `1`-regular.

## Definitions
This file makes no new definitions. It uses Mathlib's `SimpleGraph.cycleGraph` and the project's
`edgeBoundary`, `edgeExpansion`, `secondAdjEigenvalue` and `spectralGap`
(`Expanders/Basic.lean`).

## Theorems (all proved)
* `cycleGraph_isRegularOfDegree`: `C_N` is `2`-regular.
* `cycleGraph_adj_val`: adjacency in `C_N` described on the values `u.val`, `v.val` without `%`.
* `two_le_card_edgeBoundary_cycleGraph`: every nonempty proper vertex set has at least two
  boundary edges.
* `cycleGraph_edgeExpansion`: **the Cheeger constant**, `h(C_N) = 2 / ⌊N/2⌋`.
* `le_cycleGraph_secondAdjEigenvalue`: `2 cos(2π/N) ≤ λ₂(C_N)`, by the test vector
  `j ↦ cos(2πj/N)`.
* `cycleGraph_secondAdjEigenvalue_le`: `λ₂(C_N) ≤ 2 cos(2π/N)`, by the discrete Fourier
  transform on `ZMod N`.
* `cycleGraph_secondAdjEigenvalue`: **the second eigenvalue**, `λ₂(C_N) = 2 cos(2π/N)`.
* `cycleGraph_spectralGap`: the spectral gap is `2 − 2 cos(2π/N)`.
* `cycleGraph_spectralGap_le`: the spectral gap is at most `(2π/N)²`.
* `sqrt_div_pi_le_cycleGraph_edgeExpansion`: `√(2·2·(2 − λ₂))/π ≤ h(C_N)`, so the hard side of
  Cheeger's inequality is tight up to the factor `π`.
* `cycleGraph_edgeExpansion_le_sqrt`: the hard side itself on cycles,
  `h(C_N) ≤ √(2·2·(2 − λ₂))`.
* `eventually_cycleGraph_rpow_lt_edgeExpansion`, `exists_cycleGraph_rpow_lt_edgeExpansion`: for
  every constant `C` and exponent `α > 1/2`, `C · (2 − λ₂(C_N))^α < h(C_N)` for all large `N`
  (in particular for some `N`), so no inequality `h ≤ C · gap^α` with `α > 1/2` holds for all
  `2`-regular graphs.

## References
* L. Trevisan, lecture notes CS278 (2008), Lecture 10, and CS359G, Lecture 6: the cycle as the
  example showing that the square-root side of Cheeger's inequality is tight up to a constant.
* L. C. Lau, CS860 (2022) lecture notes, *04 Cheeger*.
* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Springer (2012), §1.4.3: the spectrum
  `{2 cos(2πk/N)}` of the cycle.
* K. Fan, O. Taussky and J. Todd, *Discrete analogs of inequalities of Wirtinger*,
  Monatsh. Math. 59 (1955): the same spectral fact in Laplacian (Wirtinger) form.
* The value `h(C_N) = 2/⌊N/2⌋` (attained by an arc of `⌊N/2⌋` consecutive vertices) is folklore.
-/

open Real Finset Matrix

namespace SimpleGraph

/-! ### Combinatorics of the cycle -/

/-- The cycle `C_{n+3}` is `2`-regular. The shift by `3` excludes the cycles on fewer than three
vertices: `cycleGraph 0` and `cycleGraph 1` are edgeless (`0`-regular) and `cycleGraph 2 = ⊤` on
`Fin 2` is `1`-regular. -/
theorem cycleGraph_isRegularOfDegree (n : ℕ) : (cycleGraph (n + 3)).IsRegularOfDegree 2 :=
  fun _ => cycleGraph_degree_three_le

/-- Adjacency in the cycle `C_{n+3}` on the values of the vertices: `u ~ v` exactly when
`u + 1 = v` or `v + 1 = u` as natural numbers, or `{u, v} = {0, n + 2}` (the edge that closes the
cycle). This form avoids `%` with a variable modulus, so `omega` can use it. -/
theorem cycleGraph_adj_val {n : ℕ} {u v : Fin (n + 3)} :
    (cycleGraph (n + 3)).Adj u v ↔
      u.val + 1 = v.val ∨ v.val + 1 = u.val ∨ (u.val = 0 ∧ v.val = n + 2) ∨
        (u.val = n + 2 ∧ v.val = 0) := by
  rw [cycleGraph_adj']
  have hu := u.isLt
  have hv := v.isLt
  rcases le_or_gt v u with h | h
  · rw [Fin.coe_sub_iff_le.mpr h]
    rcases eq_or_lt_of_le h with h' | h'
    · subst h'; simp only [sub_self, Fin.val_zero]; omega
    · rw [Fin.coe_sub_iff_lt.mpr h']
      have : v.val < u.val := h'
      omega
  · rw [Fin.coe_sub_iff_lt.mpr h, Fin.coe_sub_iff_le.mpr h.le]
    have : u.val < v.val := h
    omega

open Fin.NatCast in
/-- A nonempty proper subset of `Fin N` has an element `u` with `u + 1` outside it (addition
mod `N`): otherwise it would contain `a, a + 1, a + 2, …`, which is everything. -/
private theorem exists_mem_add_one_not_mem_of_ne_univ {N : ℕ} [NeZero N] {S : Finset (Fin N)}
    (hne : S.Nonempty) (hS : S ≠ univ) : ∃ u ∈ S, u + 1 ∉ S := by
  by_contra! h
  obtain ⟨a, ha⟩ := hne
  apply hS
  have key : ∀ k : ℕ, a + (k : Fin N) ∈ S := by
    intro k
    induction k with
    | zero => simpa using ha
    | succ k ih => simpa [add_assoc] using h _ ih
  refine eq_univ_of_forall fun v => ?_
  simpa using key (v - a).val

/-- In the cycle `C_{n+3}` every vertex set `S` that is neither empty nor everything has at least
two boundary edges: there is an edge `(u, u + 1)` leaving `S` and an edge `(w + 1, w)` leaving
`S` from the other side, and they differ because `n + 3 ≥ 3`. Both hypotheses are needed, since
`∅` and `univ` have empty boundary. (In `cycleGraph 2 = ⊤` a single vertex has one boundary
edge.) Each edge is counted once, as an ordered pair `(u, v)` with `u ∈ S`, as in
`edgeBoundary`. -/
theorem two_le_card_edgeBoundary_cycleGraph {n : ℕ} {S : Finset (Fin (n + 3))}
    (hne : S.Nonempty) (hS : S ≠ univ) : 2 ≤ #((cycleGraph (n + 3)).edgeBoundary S) := by
  obtain ⟨u, hu, hu'⟩ := exists_mem_add_one_not_mem_of_ne_univ hne hS
  have hSc : Sᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]; exact hS
  have hSc' : Sᶜ ≠ univ := by
    rw [Ne, Finset.compl_eq_univ_iff]; exact hne.ne_empty
  obtain ⟨w, hw, hw'⟩ := exists_mem_add_one_not_mem_of_ne_univ hSc hSc'
  simp only [mem_compl, not_not] at hw hw'
  have h1 : (u, u + 1) ∈ (cycleGraph (n + 3)).edgeBoundary S :=
    mem_edgeBoundary.mpr ⟨hu, hu', by simp [cycleGraph_adj]⟩
  have h2 : (w + 1, w) ∈ (cycleGraph (n + 3)).edgeBoundary S :=
    mem_edgeBoundary.mpr ⟨hw', hw, by simp [cycleGraph_adj]⟩
  have hne' : (u, u + 1) ≠ (w + 1, w) := by
    intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [← h2] at h1
    have hu := u.isLt
    have : ¬ (u.val = (u.val + 1 + 1) % (n + 3)) := by
      rcases lt_or_ge (u.val + 1 + 1) (n + 3) with h | h
      · rw [Nat.mod_eq_of_lt h]; omega
      · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
    exact this (by simpa [Fin.ext_iff, Fin.val_add] using h1)
  calc 2 = #({(u, u + 1), (w + 1, w)} : Finset _) := (card_pair hne').symm
    _ ≤ _ := card_le_card (by
      intro e he
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl <;> assumption)

/-- **The Cheeger constant of the cycle**: `h(C_{n+3}) = 2 / ⌊(n + 3)/2⌋`.

The minimum is attained by an arc of `⌊(n + 3)/2⌋` consecutive vertices, which has exactly two
boundary edges, and no admissible set has fewer than two (`two_le_card_edgeBoundary_cycleGraph`).
Here `(n + 3) / 2` is natural-number (floor) division; it is at least `1`, so the real division
`2 / ⌊(n + 3)/2⌋` is never a division by zero. The shift by `3` matters: for `cycleGraph 2 = ⊤`
on `Fin 2` the Cheeger constant is `1`, not `2 / 1`. -/
theorem cycleGraph_edgeExpansion (n : ℕ) :
    (cycleGraph (n + 3)).edgeExpansion = 2 / (((n + 3) / 2 : ℕ) : ℝ) := by
  set m := (n + 3) / 2 with hm_def
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 * m ≤ n + 3 := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  refine le_antisymm ?_ ?_
  · -- the arc `{i | i < m}`
    set S : Finset (Fin (n + 3)) := Finset.Iio ⟨m, by omega⟩ with hS
    have hcard : #S = m := by simp [S]
    have hne : S.Nonempty := ⟨0, by simp [S, Fin.lt_def]; omega⟩
    have h := (cycleGraph (n + 3)).edgeExpansion_le hne (by simpa [hcard] using hm2)
    have hsub : (cycleGraph (n + 3)).edgeBoundary S ⊆
        {((⟨m - 1, by omega⟩ : Fin (n + 3)), (⟨m, by omega⟩ : Fin (n + 3))),
          (0, ⟨n + 2, by omega⟩)} := by
      intro e he
      obtain ⟨hu, hv, hadj⟩ := mem_edgeBoundary.mp he
      simp only [S, mem_Iio, Fin.lt_def] at hu hv
      rw [cycleGraph_adj_val] at hadj
      simp only [mem_insert, mem_singleton, Prod.ext_iff, Fin.ext_iff, Fin.val_zero]
      omega
    have hb : (#((cycleGraph (n + 3)).edgeBoundary S) : ℝ) ≤ 2 := by
      exact_mod_cast (card_le_card hsub).trans (card_le_two)
    rw [hcard] at h
    exact h.trans (div_le_div_of_nonneg_right hb hmpos.le)
  · refine IsEdgeExpander.le_edgeExpansion fun S hS2 => ?_
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    · have hSu : S ≠ univ := by
        rintro rfl
        simp at hS2
      have h2 := two_le_card_edgeBoundary_cycleGraph hne hSu
      have hSm : #S ≤ m := by simp at hS2; omega
      have hSm' : (#S : ℝ) ≤ m := by exact_mod_cast hSm
      have h2' : (2 : ℝ) ≤ #((cycleGraph (n + 3)).edgeBoundary S) := by exact_mod_cast h2
      calc 2 / (m : ℝ) * #S ≤ 2 / m * m := by gcongr
        _ = 2 := by field_simp
        _ ≤ _ := h2'

/-! ### The second eigenvalue: lower bound by a test vector -/

/-- `cos (2π/N · a)` depends only on `a mod N`. -/
private theorem cos_two_pi_div_mul_mod (N : ℕ) (hN : 0 < N) (a : ℕ) :
    cos (2 * π / N * ((a % N : ℕ) : ℝ)) = cos (2 * π / N * a) := by
  have h := Nat.mod_add_div a N
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcast : (a : ℝ) = ((a % N : ℕ) : ℝ) + N * ((a / N : ℕ) : ℝ) := by
    exact_mod_cast h.symm
  have : 2 * π / N * (a : ℝ)
      = 2 * π / N * ((a % N : ℕ) : ℝ) + ((a / N : ℕ) : ℝ) * (2 * π) := by
    rw [hcast]; field_simp
  rw [this, cos_add_nat_mul_two_pi]

/-- `2 cos(2π/(n + 3)) ≤ λ₂(C_{n+3})`. The vector `x j = cos(2πj/(n + 3))` is an eigenvector of
the adjacency matrix with eigenvalue `2 cos(2π/(n + 3))`; this eigenvalue is not `2`, so `x` is
orthogonal to the constants, and the variational bound `xᵀAx ≤ λ₂ xᵀx` gives the claim. (Here
`n + 3` is a real number at least `3`, so the division is never by zero.) -/
theorem le_cycleGraph_secondAdjEigenvalue (n : ℕ) :
    2 * cos (2 * π / (n + 3)) ≤ (cycleGraph (n + 3)).secondAdjEigenvalue := by
  set N := n + 3 with hN
  set θ : ℝ := 2 * π / N with hθ
  have hNpos : (0 : ℝ) < N := by positivity
  have hθN : θ * N = 2 * π := by rw [hθ]; field_simp
  set x : Fin (n + 3) → ℝ := fun j => cos (θ * j.val) with hx
  have hreg := cycleGraph_isRegularOfDegree n
  have hne : ∀ j : Fin (n + 3), j - 1 ≠ j + 1 := by
    intro j
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc j, left_eq_add]
    exact ne_of_beq_false rfl
  have hplus : ∀ j : Fin (n + 3), x (j + 1) = cos (θ * j.val + θ) := by
    intro j
    simp only [hx, Fin.val_add, Fin.val_one]
    have := cos_two_pi_div_mul_mod N (by omega) (j.val + 1)
    rw [hθ, this]; push_cast; ring_nf
  have hminus : ∀ j : Fin (n + 3), x (j - 1) = cos (θ * j.val - θ) := by
    intro j
    simp only [hx, Fin.val_sub, Fin.val_one]
    have := cos_two_pi_div_mul_mod N (by omega) (n + 3 - 1 + j.val)
    rw [hθ, this]
    have h1 : ((n + 3 - 1 + j.val : ℕ) : ℝ) = N - 1 + j.val := by
      rw [hN]; push_cast [Nat.cast_sub (by omega : 1 ≤ n + 3)]; ring
    rw [h1, ← hθ]
    have : θ * (N - 1 + j.val) = (θ * j.val - θ) + 2 * π := by rw [← hθN]; ring
    rw [this, cos_add_two_pi]
  have hAx : (cycleGraph (n + 3)).adjMatrix ℝ *ᵥ x = (2 * cos θ) • x := by
    ext j
    rw [adjMatrix_mulVec_apply, cycleGraph_neighborFinset, sum_pair (hne j), hplus, hminus]
    simp only [Pi.smul_apply, smul_eq_mul, hx, cos_add, cos_sub]
    ring
  have hcos : cos θ ≠ 1 := by
    intro h
    have hθpos : 0 < θ := by positivity
    have hθlt : θ < 2 * π := by
      rw [hθ, div_lt_iff₀ hNpos]
      have : (1 : ℝ) < N := by rw [hN]; push_cast; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
      nlinarith [pi_pos]
    exact hθpos.ne' ((cos_eq_one_iff_of_lt_of_lt (by linarith) hθlt).mp h)
  have hsum : ∑ j, x j = 0 := by
    have e1 : (1 : Fin (n + 3) → ℝ) ⬝ᵥ ((cycleGraph (n + 3)).adjMatrix ℝ *ᵥ x)
        = 2 * ∑ j, x j := by
      rw [dotProduct_mulVec, ← mulVec_transpose, transpose_adjMatrix,
        adjMatrix_mulVec_one_of_regular hreg, smul_dotProduct, one_dotProduct]
      simp
    rw [hAx, dotProduct_smul, one_dotProduct, smul_eq_mul] at e1
    have : (2 * cos θ - 2) * ∑ j, x j = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by linarith : cos θ = 1) hcos
    · exact h
  have hx0 : x ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [hx] at this
  have hxx : 0 < x ⬝ᵥ x := by
    have hnn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
    exact lt_of_le_of_ne hnn (Ne.symm (dotProduct_self_eq_zero.not.mpr hx0))
  have hle := dotProduct_adjMatrix_mulVec_le hreg hsum
  rw [hAx, dotProduct_smul, smul_eq_mul] at hle
  have hθ' : θ = 2 * π / ((n : ℝ) + 3) := by simp [hθ, hN]
  rw [← hθ']
  exact le_of_mul_le_mul_right hle hxx

/-! ### The second eigenvalue: upper bound by the discrete Fourier transform -/

open ZMod in
/-- The discrete Fourier transform of a shift: `𝓕(Φ(· + a)) k = e(a k) · 𝓕Φ k`. -/
private theorem dft_comp_add_right_cycle {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (a k : ZMod N) :
    𝓕 (fun j => Φ (j + a)) k = stdAddChar (a * k) * 𝓕 Φ k := by
  rw [dft_apply, dft_apply, Finset.mul_sum]
  rw [← (Equiv.subRight a).sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.subRight_apply, sub_add_cancel, smul_eq_mul]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- For `1 ≤ k < N`, `cos(2πk/N) ≤ cos(2π/N)`: the frequency `k` is at least as far from `0`
around the circle as the frequency `1`. -/
private theorem cos_two_pi_mul_div_le {N : ℕ} (k : ℕ) (hk1 : 1 ≤ k) (hkN : k < N) :
    cos (2 * π * k / N) ≤ cos (2 * π / N) := by
  have hN : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  rcases le_or_gt (2 * k) N with h | h
  · have h' : (2 * k : ℝ) ≤ N := by exact_mod_cast h
    apply cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · rw [div_le_iff₀ hN]; nlinarith [pi_pos]
    · rw [div_le_div_iff_of_pos_right hN]; nlinarith [pi_pos]
  · have h' : (N : ℝ) < 2 * k := by exact_mod_cast h
    have hkN' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hkN
    have : cos (2 * π * k / N) = cos (2 * π * (N - k) / N) := by
      rw [show 2 * π * (N - k) / N = 2 * π - 2 * π * k / N by field_simp, cos_two_pi_sub]
    rw [this]
    apply cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · rw [div_le_iff₀ hN]; nlinarith [pi_pos]
    · rw [div_le_div_iff_of_pos_right hN]; nlinarith [pi_pos]

open ZMod in
/-- `λ₂(C_{n+3}) ≤ 2 cos(2π/(n + 3))`. Take an eigenvector `f` for `λ₂` with `Σ f = 0`, view it
as a complex function on `ZMod (n + 3)` and apply the discrete Fourier transform. The relation
`f(j − 1) + f(j + 1) = λ₂ f(j)` becomes `(e(−k) + e(k)) 𝓕f(k) = λ₂ 𝓕f(k)`. Since `f ≠ 0` and
`𝓕f(0) = Σ f = 0`, some frequency `k ≠ 0` has `𝓕f(k) ≠ 0`, so
`λ₂ = 2 cos(2πk/(n + 3)) ≤ 2 cos(2π/(n + 3))`. (The real division by `n + 3 ≥ 3` is never by
zero.) -/
theorem cycleGraph_secondAdjEigenvalue_le (n : ℕ) :
    (cycleGraph (n + 3)).secondAdjEigenvalue ≤ 2 * cos (2 * π / (n + 3)) := by
  obtain ⟨f, hf0, hfs, hAf⟩ :=
    exists_eigenvector_secondAdjEigenvalue (cycleGraph_isRegularOfDegree n)
  set μ := (cycleGraph (n + 3)).secondAdjEigenvalue
  have hne : ∀ j : Fin (n + 3), j - 1 ≠ j + 1 := by
    intro j
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc j, left_eq_add]
    exact ne_of_beq_false rfl
  have hrec : ∀ j : Fin (n + 3), f (j + -1) + f (j + 1) = μ * f j := by
    intro j
    have := congrFun hAf j
    rw [adjMatrix_mulVec_apply, cycleGraph_neighborFinset, sum_pair (hne j)] at this
    simpa [sub_eq_add_neg] using this
  -- complexify on `ZMod (n + 3)`, which is definitionally `Fin (n + 3)`
  let F : ZMod (n + 3) → ℂ := fun j => (f j : ℂ)
  have hF : (fun j => F (j + -1)) + (fun j => F (j + 1)) = (μ : ℂ) • F := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, F]
    exact_mod_cast hrec j
  have hFne : F ≠ 0 := by
    intro h
    apply hf0
    funext j
    have h' : ((f j : ℝ) : ℂ) = 0 := congrFun h j
    show f j = 0
    exact_mod_cast h'
  have hdne : 𝓕 F ≠ 0 := by
    intro h
    exact hFne ((LinearEquiv.map_eq_zero_iff _).mp h)
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hdne
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hk
    rw [dft_apply_zero]
    have : ∑ j : ZMod (n + 3), F j = ((∑ v : Fin (n + 3), f v : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]; rfl
    rw [this, hfs, Complex.ofReal_zero, Pi.zero_apply]
  have key := congrFun (congrArg 𝓕 hF) k
  rw [map_add, _root_.map_smul, Pi.add_apply, Pi.smul_apply, dft_comp_add_right_cycle,
    dft_comp_add_right_cycle, smul_eq_mul, ← add_mul] at key
  have hμ : (μ : ℂ) = stdAddChar (-1 * k) + stdAddChar (1 * k) :=
    (mul_right_cancel₀ hk key).symm
  rw [neg_one_mul, one_mul, AddChar.map_neg_eq_inv, stdAddChar_apply, toCircle_apply] at hμ
  have hval : μ = 2 * cos (2 * π * k.val / ((n + 3 : ℕ) : ℝ)) := by
    have : ((2 * cos (2 * π * k.val / ((n + 3 : ℕ) : ℝ)) : ℝ) : ℂ)
        = (Complex.exp (2 * π * Complex.I * k.val / ((n + 3 : ℕ) : ℂ)))⁻¹ +
          Complex.exp (2 * π * Complex.I * k.val / ((n + 3 : ℕ) : ℂ)) := by
      rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_ofNat, Complex.two_cos,
        ← Complex.exp_neg, add_comm]
      congr 2 <;> push_cast <;> ring
    exact Complex.ofReal_injective (hμ.trans this.symm)
  rw [hval]
  have hk1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero k).mpr hk0)
  have hkN : k.val < n + 3 := ZMod.val_lt k
  have := cos_two_pi_mul_div_le (N := n + 3) k.val hk1 hkN
  push_cast at this ⊢
  linarith

/-- **The second eigenvalue of the cycle**: `λ₂(C_{n+3}) = 2 cos(2π/(n + 3))`, counted with
multiplicity as in `secondAdjEigenvalue` (the value has multiplicity two, from the frequencies
`1` and `n + 2`). For example `λ₂(C₃) = −1` and `λ₂(C₄) = 0`. The real division by `n + 3 ≥ 3`
is never by zero. The shift by `3` matters: for `cycleGraph 2 = ⊤` on `Fin 2` the second
eigenvalue is `−1`, while `2 cos(2π/2) = −2`. -/
theorem cycleGraph_secondAdjEigenvalue (n : ℕ) :
    (cycleGraph (n + 3)).secondAdjEigenvalue = 2 * cos (2 * π / (n + 3)) :=
  le_antisymm (cycleGraph_secondAdjEigenvalue_le n) (le_cycleGraph_secondAdjEigenvalue n)

/-- **The spectral gap of the cycle**: `λ₁ − λ₂ = 2 − 2 cos(2π/(n + 3))` for `C_{n+3}`
(equivalently `4 sin²(π/(n + 3))`). The real division by `n + 3 ≥ 3` is never by zero. -/
theorem cycleGraph_spectralGap (n : ℕ) :
    (cycleGraph (n + 3)).spectralGap = 2 - 2 * cos (2 * π / (n + 3)) := by
  rw [spectralGap_eq (cycleGraph_isRegularOfDegree n), cycleGraph_secondAdjEigenvalue]
  push_cast
  ring

/-- The spectral gap of `C_{n+3}` is at most `(2π/(n + 3))²`, from `1 − x²/2 ≤ cos x`. Only the
easy half `2 cos(2π/(n + 3)) ≤ λ₂` of `cycleGraph_secondAdjEigenvalue` is used. -/
theorem cycleGraph_spectralGap_le (n : ℕ) :
    (cycleGraph (n + 3)).spectralGap ≤ (2 * π / (n + 3)) ^ 2 := by
  rw [spectralGap_eq (cycleGraph_isRegularOfDegree n)]
  have h1 := le_cycleGraph_secondAdjEigenvalue n
  have h2 := one_sub_sq_div_two_le_cos (x := 2 * π / (n + 3))
  push_cast
  linarith

/-! ### Sharpness of the hard side of Cheeger's inequality -/

/-- `h(C_{n+3}) ≥ 4/(n + 3)`, since `2 ⌊(n + 3)/2⌋ ≤ n + 3`. -/
private theorem four_div_le_cycleGraph_edgeExpansion (n : ℕ) :
    4 / ((n : ℝ) + 3) ≤ (cycleGraph (n + 3)).edgeExpansion := by
  rw [cycleGraph_edgeExpansion]
  have hm1 : 1 ≤ (n + 3) / 2 := by omega
  have hm2 : 2 * ((n + 3) / 2) ≤ n + 3 := by omega
  have hmpos : (0 : ℝ) < ((n + 3) / 2 : ℕ) := by exact_mod_cast hm1
  have hm2' : 2 * (((n + 3) / 2 : ℕ) : ℝ) ≤ n + 3 := by exact_mod_cast hm2
  rw [div_le_div_iff₀ (by positivity) hmpos]
  linarith

/-- **The hard side of Cheeger's inequality is tight up to the factor `π` on cycles**:
`√(2 · 2 · (λ₁ − λ₂)) / π ≤ h(C_{n+3})`. Together with `cycleGraph_edgeExpansion_le_sqrt`,

  `√(2d(d − λ₂)) / π ≤ h(C_{n+3}) ≤ √(2d(d − λ₂))`  with `d = 2`.

The proof combines `λ₁ − λ₂ ≤ (2π/(n + 3))²` with `h(C_{n+3}) = 2/⌊(n + 3)/2⌋ ≥ 4/(n + 3)`. The
square root is of a nonnegative number (`spectralGap_nonneg`), so `Real.sqrt` takes no junk value
here; the division is by `π > 0`. The ratio `h / √(4(λ₁ − λ₂))` tends to `1/π` as `n → ∞`, so
the factor `π` cannot be lowered for large cycles; that limit is not proved here. -/
theorem sqrt_div_pi_le_cycleGraph_edgeExpansion (n : ℕ) :
    √(2 * 2 * (cycleGraph (n + 3)).spectralGap) / π ≤ (cycleGraph (n + 3)).edgeExpansion := by
  have hN : (0 : ℝ) < n + 3 := by positivity
  have hg := cycleGraph_spectralGap_le n
  have hsq : √(2 * 2 * (cycleGraph (n + 3)).spectralGap) ≤ 4 * π / (n + 3) := by
    rw [show 4 * π / (n + 3) = √((4 * π / (n + 3)) ^ 2) from
      (sqrt_sq (by positivity)).symm]
    apply sqrt_le_sqrt
    have : (4 * π / (n + 3)) ^ 2 = 4 * (2 * π / (n + 3)) ^ 2 := by ring
    rw [this]; linarith
  rw [div_le_iff₀ pi_pos]
  calc √(2 * 2 * (cycleGraph (n + 3)).spectralGap) ≤ 4 * π / (n + 3) := hsq
    _ = 4 / ((n : ℝ) + 3) * π := by ring
    _ ≤ (cycleGraph (n + 3)).edgeExpansion * π :=
      mul_le_mul_of_nonneg_right (four_div_le_cycleGraph_edgeExpansion n) pi_pos.le

/-- The hard side of Cheeger's inequality (`edgeExpansion_le_sqrt`) specialised to the
`2`-regular cycle: `h(C_{n+3}) ≤ √(2 · 2 · (λ₁ − λ₂))`. The square root is of a nonnegative
number (`spectralGap_nonneg`). -/
theorem cycleGraph_edgeExpansion_le_sqrt (n : ℕ) :
    (cycleGraph (n + 3)).edgeExpansion ≤ √(2 * 2 * (cycleGraph (n + 3)).spectralGap) := by
  have h := edgeExpansion_le_sqrt (cycleGraph_isRegularOfDegree n)
  norm_num at h ⊢
  exact h

/-- **The exponent `1/2` in Cheeger's inequality is optimal**: for every real `C` and every
`α > 1/2`, the cycles satisfy `C · (λ₁ − λ₂)^α < h(C_{n+3})` for all sufficiently large `n`.
Hence no bound `h(G) ≤ C · (d − λ₂)^α` with `α > 1/2` holds for all `2`-regular graphs.

Here `^` is the real power `Real.rpow`; its base `λ₁ − λ₂` is nonnegative (`spectralGap_nonneg`),
so the junk values of `Real.rpow` at negative bases do not occur. Any `C` is allowed: for `C ≤ 0`
the left side is `≤ 0 < h(C_{n+3})` for every `n`. The hypothesis `1/2 < α` cannot be weakened to
`α = 1/2`, since `h(C_{n+3}) ≤ 2 · (λ₁ − λ₂)^(1/2)` for all `n`
(`cycleGraph_edgeExpansion_le_sqrt`). The witnesses can be astronomically large: by a numerical
estimate, for `C = 10` and `α = 0.51` they start at roughly `10^60` vertices. -/
theorem eventually_cycleGraph_rpow_lt_edgeExpansion (C : ℝ) {α : ℝ} (hα : 1 / 2 < α) :
    ∀ᶠ n : ℕ in Filter.atTop,
      C * (cycleGraph (n + 3)).spectralGap ^ α < (cycleGraph (n + 3)).edgeExpansion := by
  rcases le_or_gt C 0 with hC | hC
  · refine Filter.Eventually.of_forall fun n => ?_
    have hg : 0 ≤ (cycleGraph (n + 3)).spectralGap ^ α :=
      rpow_nonneg (spectralGap_nonneg _) _
    have h4 := four_div_le_cycleGraph_edgeExpansion n
    have : (0 : ℝ) < 4 / ((n : ℝ) + 3) := by positivity
    nlinarith
  · -- `C · gap^α ≤ C (2π)^(2α) / (n + 3)^(2α)` and `(n + 3)^(2α − 1) → ∞`
    set K : ℝ := C * (2 * π) ^ (2 * α) / 4
    have hβ : 0 < 2 * α - 1 := by linarith
    have ht : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 3) ^ (2 * α - 1)) Filter.atTop
        Filter.atTop :=
      (tendsto_rpow_atTop hβ).comp
        (Filter.tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop)
    filter_upwards [ht.eventually_gt_atTop K] with n hn
    have hN : (0 : ℝ) < n + 3 := by positivity
    have hg0 := spectralGap_nonneg (cycleGraph (n + 3))
    have hg := cycleGraph_spectralGap_le n
    have h1 : (cycleGraph (n + 3)).spectralGap ^ α ≤ ((2 * π / (n + 3)) ^ 2) ^ α :=
      rpow_le_rpow hg0 hg (by linarith)
    have h2 : ((2 * π / ((n : ℝ) + 3)) ^ 2) ^ α
        = (2 * π) ^ (2 * α) / (((n : ℝ) + 3) ^ (2 * α - 1) * ((n : ℝ) + 3)) := by
      rw [← rpow_natCast, ← rpow_mul (by positivity), div_rpow (by positivity) hN.le,
        ← rpow_add_one hN.ne']
      norm_num
    have h3 : C * ((2 * π) ^ (2 * α) / (((n : ℝ) + 3) ^ (2 * α - 1) * ((n : ℝ) + 3)))
        < 4 / ((n : ℝ) + 3) := by
      have hp : 0 < ((n : ℝ) + 3) ^ (2 * α - 1) := by positivity
      rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) hN]
      have : C * (2 * π) ^ (2 * α) < 4 * ((n : ℝ) + 3) ^ (2 * α - 1) := by
        have := hn; simp only [K] at this; linarith
      nlinarith
    calc C * (cycleGraph (n + 3)).spectralGap ^ α
        ≤ C * ((2 * π / (n + 3)) ^ 2) ^ α := by gcongr
      _ = _ := by rw [h2]
      _ < 4 / ((n : ℝ) + 3) := h3
      _ ≤ _ := four_div_le_cycleGraph_edgeExpansion n

/-- **The exponent `1/2` in Cheeger's inequality is optimal** (existential form of
`eventually_cycleGraph_rpow_lt_edgeExpansion`): for every real `C` and every `α > 1/2` some cycle
`C_{n+3}` has `C · (λ₁ − λ₂)^α < h(C_{n+3})`. Here `^` is `Real.rpow`, applied to the nonnegative
spectral gap; `C ≤ 0` is allowed (then `n = 0` works), and `α = 1/2` is excluded because then the
statement fails for `C = 2`. -/
theorem exists_cycleGraph_rpow_lt_edgeExpansion (C : ℝ) {α : ℝ} (hα : 1 / 2 < α) :
    ∃ n : ℕ,
      C * (cycleGraph (n + 3)).spectralGap ^ α < (cycleGraph (n + 3)).edgeExpansion :=
  (eventually_cycleGraph_rpow_lt_edgeExpansion C hα).exists

end SimpleGraph
