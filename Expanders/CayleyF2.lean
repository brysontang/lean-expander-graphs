/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.Cheeger
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Cayley graphs of `(ℤ/2)ⁿ`: exact `λ₂` and exact Cheeger constant

For a finite set `S ⊆ (ℤ/2)ⁿ` the Cayley graph `Cay((ℤ/2)ⁿ, S)` joins `u` and `v` when
`v − u ∈ S`. Its adjacency matrix is diagonalised by the characters `χₐ(x) = (−1)^{a·x}`: `χₐ` is
an eigenvector with eigenvalue `|S| − 2 w_S(a)`, where the *dual weight* `w_S(a)` counts the
generators `s ∈ S` with `a·s = 1`. From this, for `S ⊆ (ℤ/2)^{n+1}` with `0 ∉ S`,

  `λ₂ = |S| − 2 w_min`,  `d − λ₂ = 2 w_min`,  `h = w_min = (d − λ₂) / 2`,

with `w_min = min_{a ≠ 0} w_S(a)`. So for every Cayley graph of `(ℤ/2)ⁿ` the easy direction of
Cheeger's inequality, `(d − λ₂)/2 ≤ h(G)` (`SimpleGraph.spectralGap_div_two_le_edgeExpansion`), is
an equality. This mathematically generalises `Expanders/Hypercube.lean`, which is the case where
`S` is the standard basis (`w_min = 1`), via `Bool ≃ ZMod 2`; no formal isomorphism with
`hypercube` is proved here, so the `hypercube_*` results are not derived from this file. Other
instances: `S` = all nonzero vectors gives the complete graph `K_{2^{n+1}}` (`w_min = 2ⁿ`,
`λ₂ = −1`); a non-spanning `S` (for instance `S = ∅`) gives `w_min = 0`, `λ₂ = |S|` and `h = 0`.

## Definitions
* `SimpleGraph.f2Cayley S`: the Cayley graph of `Fin n → ZMod 2` with generator set `S`
  (Mathlib's `circulantGraph`). **Definition.**
* `SimpleGraph.f2Char a`: the real character `x ↦ (−1)^{a ⬝ᵥ x}`. **Definition.**
* `SimpleGraph.dualWeight S a`: the number of `s ∈ S` with `a ⬝ᵥ s ≠ 0`. **Definition.**
* `SimpleGraph.minDualWeight S`: the minimum of `dualWeight S a` over nonzero
  `a : Fin (n + 1) → ZMod 2`. **Definition.**

## Theorems (all proved here)
* `f2Cayley_adj`: `u ~ v ↔ u ≠ v ∧ v − u ∈ S`; `f2Cayley_erase_zero`: the generator `0` is
  irrelevant.
* `f2Cayley_isRegularOfDegree`: for `0 ∉ S` the graph is `|S|`-regular
  (`f2Cayley_isRegularOfDegree_erase_zero`: `|S \ {0}|`-regular for every `S`).
* Characters: `sum_f2Char` (`Σₓ χₐ(x) = 2ⁿ [a = 0]`), `f2Char_dotProduct_f2Char`
  (orthogonality), `sum_f2Char_mul` (completeness) and `sum_f2Char_dotProduct_mul`
  (**Fourier inversion** on `(ℤ/2)ⁿ`).
* `f2Cayley_adjMatrix_mulVec_f2Char`: for `0 ∉ S`, `A χₐ = (|S| − 2 w_S(a)) χₐ`
  (`f2Cayley_adjMatrix_mulVec_f2Char_erase_zero`: the same with `|S \ {0}|`, for every `S`).
* `f2Cayley_secondAdjEigenvalue`: for `0 ∉ S`, `λ₂ = |S| − 2 · minDualWeight S`
  (`f2Cayley_secondAdjEigenvalue_erase_zero`: `λ₂ = |S \ {0}| − 2 · minDualWeight S` for
  every `S`).
* `f2Cayley_spectralGap`: the spectral gap is `2 · minDualWeight S`, for every `S`.
* `f2Cayley_halfSpace`: for every `S` and every `a ≠ 0`, the half-space `H = {x | a ⬝ᵥ x = 0}`
  has `2 |H| = 2^{n+1}` and `|∂H| = w_S(a) · |H|`.
* `f2Cayley_edgeExpansion`: the Cheeger constant is `minDualWeight S`, for every `S`.
* `f2Cayley_halfSpace_attains_edgeExpansion`: for a minimising `a ≠ 0`, the half-space
  `{x | a ⬝ᵥ x = 0}` attains the minimum, `|∂H| / |H| = h(G)`;
  `f2Cayley_exists_halfSpace_attains_edgeExpansion`: such a half-space exists.
* `f2Cayley_edgeExpansion_eq_spectralGap_div_two`: `h(G) = (d − λ₂) / 2`, for every `S`.

The eigenvalues `|S| − 2 w_S(a)`, `a ∈ (ℤ/2)ⁿ`, are in fact the whole spectrum with multiplicity
(the `2ⁿ` characters form an orthogonal basis of eigenvectors, by `f2Char_dotProduct_f2Char` and
`f2Cayley_adjMatrix_mulVec_f2Char`), but the multiset identity for `adjEigenvalues` is not stated
here; only `λ₁ = |S|` (`SimpleGraph.largestAdjEigenvalue_eq`) and `λ₂` are.

## Proof
1. `A χₐ (u) = Σ_{s ∈ S} χₐ(u + s) = χₐ(u) Σ_{s ∈ S} χₐ(s) = (|S| − 2 w_S(a)) χₐ(u)`.
2. `λ₂ ≤ |S| − 2 w_min`: take an eigenvector `f ⟂ 𝟙` for `λ₂`
   (`exists_eigenvector_secondAdjEigenvalue`). By Fourier inversion some `χₐ ⬝ f ≠ 0`, and
   `a ≠ 0` because `Σ f = 0`. Symmetry of `A` gives `(|S| − 2 w_S(a)) (χₐ ⬝ f) = λ₂ (χₐ ⬝ f)`.
3. `λ₂ ≥ |S| − 2 w_min`: the character of a minimising `a ≠ 0` is orthogonal to `𝟙`, so the
   variational bound `dotProduct_adjMatrix_mulVec_le` applies to it.
4. `h ≤ w_min`: for the half-space `H = {x | a ⬝ᵥ x = 0}`, `a ≠ 0`, one has `𝟙_H − ½ = ½ χₐ`, so
   the Laplacian form (`sum_adj_sub_sq_div_two`, `sum_adj_indicator_sub_sq`) gives
   `|∂H| = w_S(a) · 2ⁿ`, and `|H| = 2ⁿ` follows from `Σ χₐ = 0` (`f2Cayley_halfSpace`). Take `a`
   minimising.
5. `h ≥ w_min`: the easy direction of Cheeger's inequality. With 4 this also shows that the
   half-space of a minimising `a` attains `h`.

## References
* B. Nica, *A Brief Introduction to Spectral Graph Theory*, EMS Textbooks in Mathematics, 2018
  (arXiv:1609.08072), §12: Theorem 12.7 (`β ≥ λ₂/2`), Theorem 12.8 and Corollary 12.9
  (equality when `λ₂` has a `{±1}`-valued eigenfunction), and the remark after Example 12.11
  (`β = λ₂/2` for every Cayley graph of `(ℤ₂)ⁿ`). Nica's `λ₂` is the Laplacian eigenvalue
  `d − λ₂` of this file.
* The character formula for the spectrum of an abelian Cayley graph is classical:
  L. Lovász, *Spectra of graphs with transitive groups*, Period. Math. Hungar. 6 (1975), 191–195;
  L. Babai, *Spectra of Cayley graphs*, J. Combin. Theory Ser. B 27 (1979), 180–189.
-/

open Finset Matrix

namespace SimpleGraph

variable {n : ℕ}

/-! ### Definitions -/

/-- The **Cayley graph of `(ℤ/2)ⁿ`** with generator set `S`: vertices are the vectors
`Fin n → ZMod 2`, and `u ~ v` exactly when `u ≠ v` and `v − u ∈ S` (`f2Cayley_adj`). It is
Mathlib's `circulantGraph` on `S`, whose condition `u − v ∈ S ∨ v − u ∈ S` collapses because
`−x = x` in `(ℤ/2)ⁿ`.

Degenerate cases. A generator `0 ∈ S` would be a loop, which a simple graph does not have, so it
contributes no edge: `f2Cayley (S.erase 0) = f2Cayley S` (`f2Cayley_erase_zero`) and the degree is
`|S \ {0}|`, which equals `|S|` only when `0 ∉ S`. `S = ∅` gives the edgeless graph. For `n = 0`
the vertex type has a single element and the graph has no edges. -/
abbrev f2Cayley (S : Finset (Fin n → ZMod 2)) : SimpleGraph (Fin n → ZMod 2) :=
  circulantGraph (S : Set (Fin n → ZMod 2))

/-- The **character** `χₐ(x) = (−1)^{a·x}` of `(ℤ/2)ⁿ`, as a real-valued function of `x`: it is
`1` when the dot product `a ⬝ᵥ x`, computed in `ZMod 2`, is `0`, and `−1` otherwise. For `a = 0`
it is the constant function `1` (`f2Char_zero_left`); for `n = 0` that is the only character. -/
def f2Char (a x : Fin n → ZMod 2) : ℝ := if a ⬝ᵥ x = 0 then 1 else -1

/-- The **dual weight** `w_S(a) = #{s ∈ S | a ⬝ᵥ s ≠ 0}`: the number of generators on which the
character `χₐ` takes the value `−1`; equivalently the Hamming weight of the word `(a ⬝ᵥ s)_{s ∈ S}`.
The generator `0` is never counted (`dualWeight_erase_zero`), `w_S(0) = 0`, and `w_∅(a) = 0`. -/
def dualWeight (S : Finset (Fin n → ZMod 2)) (a : Fin n → ZMod 2) : ℕ := #{s ∈ S | a ⬝ᵥ s ≠ 0}

/-- The **minimum dual weight** `w_min(S) = min_{a ≠ 0} w_S(a)` of a set `S ⊆ (ℤ/2)^{n+1}`.

It is defined only in dimension `n + 1 ≥ 1`, where nonzero vectors exist (the minimum is over a
nonempty set, so there is no junk value); in dimension `0` the Cayley graph has a single vertex
and `λ₂` is not defined. `w_min(S) = 0` exactly when some nonzero `a` is orthogonal to every
element of `S`, which happens for `S = ∅` and, more generally, when `S` does not span; when `S`
spans, `w_min(S)` is the minimum distance of the binary linear code whose generator matrix has
the elements of `S` as columns. -/
noncomputable def minDualWeight (S : Finset (Fin (n + 1) → ZMod 2)) : ℕ :=
  (univ.erase 0).inf' ⟨Pi.single 0 1, by simp⟩ (dualWeight S)

/-! ### Arithmetic in `(ℤ/2)ⁿ` -/

private theorem neg_eq_self_zmod_two (x : Fin n → ZMod 2) : -x = x :=
  funext fun _ => ZMod.neg_eq_self_mod_two _

private theorem add_eq_zero_iff_eq_zmod_two {u v : Fin n → ZMod 2} : u + v = 0 ↔ u = v := by
  rw [add_eq_zero_iff_eq_neg, neg_eq_self_zmod_two]

/-! ### The graph -/

/-- Adjacency in `f2Cayley S`: `u ~ v` exactly when `u ≠ v` and `v − u ∈ S`. -/
theorem f2Cayley_adj {S : Finset (Fin n → ZMod 2)} {u v : Fin n → ZMod 2} :
    (f2Cayley S).Adj u v ↔ u ≠ v ∧ v - u ∈ S := by
  have hs : u - v = v - u := by rw [← neg_sub, neg_eq_self_zmod_two]
  simp only [circulantGraph_adj, Finset.mem_coe, hs, or_self]

/-- The generator `0` contributes no edge: `f2Cayley (S.erase 0) = f2Cayley S`. -/
theorem f2Cayley_erase_zero (S : Finset (Fin n → ZMod 2)) : f2Cayley (S.erase 0) = f2Cayley S := by
  ext u v
  simp only [f2Cayley_adj, mem_erase, sub_ne_zero]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, Ne.symm h.1, h.2⟩⟩

/-- The neighbours of `u` are the translates `u + s` by the nonzero generators `s ∈ S \ {0}`. -/
theorem f2Cayley_neighborFinset (S : Finset (Fin n → ZMod 2)) (u : Fin n → ZMod 2) :
    (f2Cayley S).neighborFinset u = (S.erase 0).image (u + ·) := by
  ext v
  simp only [mem_neighborFinset, f2Cayley_adj, mem_image, mem_erase]
  constructor
  · rintro ⟨huv, h⟩
    exact ⟨v - u, ⟨sub_ne_zero.mpr (Ne.symm huv), h⟩, by abel⟩
  · rintro ⟨s, ⟨hs0, hs⟩, rfl⟩
    exact ⟨fun h => hs0 (by simpa using h), by simpa using hs⟩

/-- `f2Cayley S` is `|S \ {0}|`-regular, for every generator set `S`. -/
theorem f2Cayley_isRegularOfDegree_erase_zero (S : Finset (Fin n → ZMod 2)) :
    (f2Cayley S).IsRegularOfDegree #(S.erase 0) := by
  intro u
  rw [← card_neighborFinset_eq_degree, f2Cayley_neighborFinset,
    card_image_of_injective _ (add_right_injective u)]

/-- For `0 ∉ S`, the Cayley graph `f2Cayley S` is `|S|`-regular. (With `0 ∈ S` the degree is
`|S| − 1`, see `f2Cayley_isRegularOfDegree_erase_zero`.) -/
theorem f2Cayley_isRegularOfDegree {S : Finset (Fin n → ZMod 2)}
    (h0 : (0 : Fin n → ZMod 2) ∉ S) : (f2Cayley S).IsRegularOfDegree #S := by
  have h := f2Cayley_isRegularOfDegree_erase_zero S
  rwa [erase_eq_of_notMem h0] at h

/-! ### Characters and Fourier inversion -/

/-- `χₐ` is a homomorphism to `{±1}`: `χₐ(x + y) = χₐ(x) χₐ(y)`. -/
theorem f2Char_add (a x y : Fin n → ZMod 2) : f2Char a (x + y) = f2Char a x * f2Char a y := by
  have key : ∀ p q : ZMod 2, (if p + q = 0 then (1 : ℝ) else -1)
      = (if p = 0 then 1 else -1) * (if q = 0 then 1 else -1) := by
    have h01 : ∀ p : ZMod 2, p = 0 ∨ p = 1 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := rfl
    have h1 : (1 : ZMod 2) ≠ 0 := by decide
    intro p q
    rcases h01 p with rfl | rfl <;> rcases h01 q with rfl | rfl <;> simp [h11, h1]
  simp only [f2Char, dotProduct_add]
  exact key _ _

/-- `χₐ(x) = χₓ(a)`. -/
theorem f2Char_comm (a x : Fin n → ZMod 2) : f2Char a x = f2Char x a := by
  simp [f2Char, dotProduct_comm]

/-- `χₐ` takes values in `{±1}`, so `χₐ(x)² = 1`. -/
theorem f2Char_mul_self (a x : Fin n → ZMod 2) : f2Char a x * f2Char a x = 1 := by
  unfold f2Char; split_ifs <;> norm_num

/-- The trivial character `χ₀` is the constant function `1`. -/
theorem f2Char_zero_left (x : Fin n → ZMod 2) : f2Char 0 x = 1 := by simp [f2Char]

/-- **Orthogonality to the constants**: `Σₓ χₐ(x) = 2ⁿ` if `a = 0` and `0` otherwise. -/
theorem sum_f2Char (a : Fin n → ZMod 2) :
    ∑ x, f2Char a x = if a = 0 then (2 : ℝ) ^ n else 0 := by
  split_ifs with ha
  · subst ha
    simp [f2Char_zero_left, ZMod.card]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    have hi' : a i ≠ 0 := hi
    have he : f2Char a (Pi.single i 1) = -1 := by
      simp [f2Char, dotProduct_single, hi']
    have h := Fintype.sum_equiv (Equiv.addRight (Pi.single i 1))
      (fun x => f2Char a (x + Pi.single i 1)) (fun x => f2Char a x) (fun x => rfl)
    simp only [f2Char_add, he, mul_neg, mul_one, Finset.sum_neg_distrib] at h
    linarith

/-- **Orthogonality of characters**: `χₐ ⬝ χ_b = 2ⁿ` if `a = b` and `0` otherwise. -/
theorem f2Char_dotProduct_f2Char (a b : Fin n → ZMod 2) :
    f2Char a ⬝ᵥ f2Char b = if a = b then (2 : ℝ) ^ n else 0 := by
  have h : ∀ x, f2Char a x * f2Char b x = f2Char x (a + b) := by
    intro x
    rw [f2Char_add, f2Char_comm a, f2Char_comm b]
  simp only [dotProduct, h]
  simp_rw [← f2Char_comm (a + b), sum_f2Char, add_eq_zero_iff_eq_zmod_two]

/-- Every character has squared norm `χₐ ⬝ χₐ = 2ⁿ`, the number of vertices. -/
theorem f2Char_dotProduct_self (a : Fin n → ZMod 2) : f2Char a ⬝ᵥ f2Char a = (2 : ℝ) ^ n := by
  simp [f2Char_dotProduct_f2Char]

/-- **Completeness of characters**: `Σₐ χₐ(u) χₐ(v) = 2ⁿ` if `u = v` and `0` otherwise. -/
theorem sum_f2Char_mul (u v : Fin n → ZMod 2) :
    ∑ a, f2Char a u * f2Char a v = if u = v then (2 : ℝ) ^ n else 0 := by
  simp_rw [← f2Char_add, f2Char_comm _ (u + v), sum_f2Char, add_eq_zero_iff_eq_zmod_two]

/-- **Fourier inversion on `(ℤ/2)ⁿ`**: `Σₐ (χₐ ⬝ f) χₐ(u) = 2ⁿ f(u)` for every `f`. -/
theorem sum_f2Char_dotProduct_mul (f : (Fin n → ZMod 2) → ℝ) (u : Fin n → ZMod 2) :
    ∑ a, (f2Char a ⬝ᵥ f) * f2Char a u = (2 : ℝ) ^ n * f u := by
  simp only [dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_comm (f2Char _ _) (f _), mul_assoc, ← Finset.mul_sum, sum_f2Char_mul]
  simp [mul_comm]

/-- A function orthogonal to every character is zero. -/
theorem eq_zero_of_forall_f2Char_dotProduct_eq_zero {f : (Fin n → ZMod 2) → ℝ}
    (h : ∀ a, f2Char a ⬝ᵥ f = 0) : f = 0 := by
  funext u
  have := sum_f2Char_dotProduct_mul f u
  simp only [h, zero_mul, Finset.sum_const_zero] at this
  have hpos : (2 : ℝ) ^ n ≠ 0 := by positivity
  simpa [hpos] using this.symm

/-! ### Dual weights -/

/-- `Σ_{s ∈ S} χₐ(s) = |S| − 2 w_S(a)` (the subtraction is in `ℝ`). -/
theorem sum_f2Char_eq_card_sub_dualWeight (S : Finset (Fin n → ZMod 2)) (a : Fin n → ZMod 2) :
    ∑ s ∈ S, f2Char a s = (#S : ℝ) - 2 * dualWeight S a := by
  have h := card_filter_add_card_filter_not (s := S) (p := fun s => a ⬝ᵥ s ≠ 0)
  simp only [f2Char, sum_ite, sum_const, nsmul_eq_mul, mul_one, mul_neg, dualWeight]
  simp only [not_not] at h
  have h' : ((#{s ∈ S | a ⬝ᵥ s = 0} : ℕ) : ℝ) = #S - #{s ∈ S | a ⬝ᵥ s ≠ 0} := by
    rw [← h]; push_cast; ring
  rw [h']
  ring

/-- The generator `0` is never counted by the dual weight. -/
theorem dualWeight_erase_zero (S : Finset (Fin n → ZMod 2)) (a : Fin n → ZMod 2) :
    dualWeight (S.erase 0) a = dualWeight S a := by
  unfold dualWeight
  rw [filter_erase, erase_eq_of_notMem]
  simp

/-- `minDualWeight S ≤ w_S(a)` for every nonzero `a`. -/
theorem minDualWeight_le (S : Finset (Fin (n + 1) → ZMod 2)) {a : Fin (n + 1) → ZMod 2}
    (ha : a ≠ 0) : minDualWeight S ≤ dualWeight S a :=
  Finset.inf'_le _ (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩)

/-- The minimum dual weight is attained by some nonzero `a`. -/
theorem exists_dualWeight_eq_minDualWeight (S : Finset (Fin (n + 1) → ZMod 2)) :
    ∃ a, a ≠ 0 ∧ dualWeight S a = minDualWeight S := by
  obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_inf' (s := univ.erase (0 : Fin (n + 1) → ZMod 2))
    ⟨Pi.single 0 1, by simp⟩ (dualWeight S)
  exact ⟨a, (Finset.mem_erase.mp ha).1, he.symm⟩

/-! ### The spectrum -/

/-- Every character is an eigenvector of `f2Cayley S`, for every generator set `S`:
`A χₐ = (|S \ {0}| − 2 w_S(a)) χₐ`, the subtraction being in `ℝ`. -/
theorem f2Cayley_adjMatrix_mulVec_f2Char_erase_zero (S : Finset (Fin n → ZMod 2))
    (a : Fin n → ZMod 2) :
    (f2Cayley S).adjMatrix ℝ *ᵥ f2Char a
      = ((#(S.erase 0) : ℝ) - 2 * dualWeight S a) • f2Char a := by
  ext u
  rw [adjMatrix_mulVec_apply, f2Cayley_neighborFinset,
    sum_image fun x _ y _ h => add_left_cancel h, Pi.smul_apply, smul_eq_mul,
    ← dualWeight_erase_zero S a, ← sum_f2Char_eq_card_sub_dualWeight, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [f2Char_add, mul_comm]

/-- **The characters diagonalise the Cayley graph.** For `0 ∉ S`, every character `χₐ` is an
eigenvector of the adjacency matrix of `f2Cayley S` with eigenvalue `|S| − 2 w_S(a)`. The
subtraction is in `ℝ`, and the eigenvalue can be negative (it is `−|S|` when `a ⬝ᵥ s = 1` for
every `s ∈ S`). The trivial character `a = 0` gives the eigenvalue `|S|`. With `0 ∈ S` the
eigenvalue is `|S| − 1 − 2 w_S(a)` (`f2Cayley_adjMatrix_mulVec_f2Char_erase_zero`). -/
theorem f2Cayley_adjMatrix_mulVec_f2Char {S : Finset (Fin n → ZMod 2)}
    (h0 : (0 : Fin n → ZMod 2) ∉ S) (a : Fin n → ZMod 2) :
    (f2Cayley S).adjMatrix ℝ *ᵥ f2Char a = ((#S : ℝ) - 2 * dualWeight S a) • f2Char a := by
  have h := f2Cayley_adjMatrix_mulVec_f2Char_erase_zero S a
  rwa [erase_eq_of_notMem h0] at h

/-- Upper bound `λ₂ ≤ |S \ {0}| − 2 · minDualWeight S`: an eigenvector for `λ₂` orthogonal to the
constants pairs nontrivially with some nontrivial character, whose eigenvalue is then `λ₂`. -/
theorem f2Cayley_secondAdjEigenvalue_le (S : Finset (Fin (n + 1) → ZMod 2)) :
    (f2Cayley S).secondAdjEigenvalue ≤ (#(S.erase 0) : ℝ) - 2 * minDualWeight S := by
  obtain ⟨f, hf0, hfs, hAf⟩ :=
    exists_eigenvector_secondAdjEigenvalue (f2Cayley_isRegularOfDegree_erase_zero S)
  -- Pairing the eigen-equation with each character.
  have hpair : ∀ a, ((#(S.erase 0) : ℝ) - 2 * dualWeight S a) * (f2Char a ⬝ᵥ f)
      = (f2Cayley S).secondAdjEigenvalue * (f2Char a ⬝ᵥ f) := by
    intro a
    have h1 : f2Char a ⬝ᵥ (f2Cayley S).adjMatrix ℝ *ᵥ f
        = ((f2Cayley S).adjMatrix ℝ *ᵥ f2Char a) ⬝ᵥ f := by
      rw [dotProduct_mulVec, ← mulVec_transpose, transpose_adjMatrix]
    rw [hAf, f2Cayley_adjMatrix_mulVec_f2Char_erase_zero, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, smul_eq_mul] at h1
    exact h1.symm
  -- Some character pairs nontrivially with `f`, and it is not the trivial one.
  obtain ⟨a, ha⟩ := not_forall.mp (mt eq_zero_of_forall_f2Char_dotProduct_eq_zero hf0)
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply ha
    simp [dotProduct, f2Char_zero_left, hfs]
  have heq := mul_right_cancel₀ ha (hpair a)
  have hle : (minDualWeight S : ℝ) ≤ dualWeight S a := by exact_mod_cast minDualWeight_le S ha0
  linarith

/-- Lower bound `|S \ {0}| − 2 · minDualWeight S ≤ λ₂`: the character of a minimising `a ≠ 0` is
an eigenvector orthogonal to the constants. -/
theorem le_f2Cayley_secondAdjEigenvalue (S : Finset (Fin (n + 1) → ZMod 2)) :
    (#(S.erase 0) : ℝ) - 2 * minDualWeight S ≤ (f2Cayley S).secondAdjEigenvalue := by
  obtain ⟨a, ha0, ha⟩ := exists_dualWeight_eq_minDualWeight S
  have hsum : ∑ v, f2Char a v = 0 := by rw [sum_f2Char, if_neg ha0]
  have h := dotProduct_adjMatrix_mulVec_le (f2Cayley_isRegularOfDegree_erase_zero S) hsum
  rw [f2Cayley_adjMatrix_mulVec_f2Char_erase_zero, dotProduct_smul, smul_eq_mul,
    f2Char_dotProduct_self, ha] at h
  exact le_of_mul_le_mul_right h (by positivity)

/-- The second adjacency eigenvalue of `f2Cayley S` on `(ℤ/2)^{n+1}`, for every generator set `S`:
`λ₂ = |S \ {0}| − 2 · minDualWeight S`, the subtraction being in `ℝ`. -/
theorem f2Cayley_secondAdjEigenvalue_erase_zero (S : Finset (Fin (n + 1) → ZMod 2)) :
    (f2Cayley S).secondAdjEigenvalue = (#(S.erase 0) : ℝ) - 2 * minDualWeight S :=
  le_antisymm (f2Cayley_secondAdjEigenvalue_le S) (le_f2Cayley_secondAdjEigenvalue S)

/-- **The second eigenvalue of a Cayley graph of `(ℤ/2)^{n+1}`.** For a generator set `S` with
`0 ∉ S`, `λ₂ = |S| − 2 · minDualWeight S`.

The vertex type has `2^{n+1} ≥ 2` elements, so `λ₂` is defined; dimension `0` is excluded by the
indexing. The subtraction is in `ℝ`, and the value can be negative: for `S` = all nonzero vectors
(the complete graph `K_{2^{n+1}}`) it is `(2^{n+1} − 1) − 2 · 2ⁿ = −1`. If `S` does not span (for
instance `S = ∅`) then `minDualWeight S = 0` and `λ₂ = |S|`. The hypothesis `0 ∉ S` is needed:
for `S = {0}` in `(ℤ/2)¹` the graph has no edges, so `λ₂ = 0`, while `|S| − 2 · 0 = 1`. For general
`S` see `f2Cayley_secondAdjEigenvalue_erase_zero`. -/
theorem f2Cayley_secondAdjEigenvalue {S : Finset (Fin (n + 1) → ZMod 2)}
    (h0 : (0 : Fin (n + 1) → ZMod 2) ∉ S) :
    (f2Cayley S).secondAdjEigenvalue = (#S : ℝ) - 2 * minDualWeight S := by
  rw [f2Cayley_secondAdjEigenvalue_erase_zero, erase_eq_of_notMem h0]

/-- **The spectral gap of a Cayley graph of `(ℤ/2)^{n+1}`** is `d − λ₂ = 2 · minDualWeight S`.
This holds for every generator set `S`: a generator `0 ∈ S` adds no edge (`f2Cayley_erase_zero`),
so the degree is `|S \ {0}|` and `λ₂ = |S \ {0}| − 2 · minDualWeight S`, and the difference is
unaffected. The gap is `0` exactly when `minDualWeight S = 0`, for instance when `S = ∅`. -/
theorem f2Cayley_spectralGap (S : Finset (Fin (n + 1) → ZMod 2)) :
    (f2Cayley S).spectralGap = 2 * minDualWeight S := by
  rw [spectralGap_eq (f2Cayley_isRegularOfDegree_erase_zero S),
    f2Cayley_secondAdjEigenvalue_erase_zero]
  ring

/-! ### The Cheeger constant -/

/-- **Half-spaces of `(ℤ/2)^{n+1}`.** For every generator set `S` and every nonzero `a`, the
half-space `H = {x | a ⬝ᵥ x = 0}` contains exactly half of the `2^{n+1}` vertices, and exactly
`w_S(a)` edges of `f2Cayley S` leave it per vertex: `2 |H| = 2^{n+1}` and `|∂H| = w_S(a) · |H|`.

Proof: `𝟙_H − ½ = ½ χₐ`, so the Laplacian form (`sum_adj_sub_sq_div_two`,
`sum_adj_indicator_sub_sq`) evaluated on the eigenvector `χₐ` gives `|∂H| = w_S(a) · 2ⁿ`, and
`|H| = 2ⁿ` follows from `Σ χₐ = 0`. -/
theorem f2Cayley_halfSpace (S : Finset (Fin (n + 1) → ZMod 2)) {a : Fin (n + 1) → ZMod 2}
    (ha0 : a ≠ 0) :
    2 * #({x | a ⬝ᵥ x = 0} : Finset (Fin (n + 1) → ZMod 2))
        = Fintype.card (Fin (n + 1) → ZMod 2) ∧
      #((f2Cayley S).edgeBoundary {x | a ⬝ᵥ x = 0})
        = dualWeight S a * #({x | a ⬝ᵥ x = 0} : Finset (Fin (n + 1) → ZMod 2)) := by
  have hreg := f2Cayley_isRegularOfDegree_erase_zero S
  set H : Finset (Fin (n + 1) → ZMod 2) := {x | a ⬝ᵥ x = 0} with hH
  -- The shifted indicator of the half-space is half the character.
  set x : (Fin (n + 1) → ZMod 2) → ℝ := fun v => (if v ∈ H then (1 : ℝ) else 0) - 1 / 2 with hx
  have hxχ : x = (1 / 2 : ℝ) • f2Char a := by
    funext v
    simp only [hx, hH, Finset.mem_filter, Finset.mem_univ, true_and, Pi.smul_apply,
      smul_eq_mul, f2Char]
    split_ifs <;> norm_num
  have hbd := sum_adj_sub_sq_div_two hreg x
  rw [sum_adj_indicator_sub_sq (G := f2Cayley S) H (1 / 2)] at hbd
  rw [hxχ, dotProduct_smul, smul_dotProduct, mulVec_smul, dotProduct_smul, smul_dotProduct,
    f2Cayley_adjMatrix_mulVec_f2Char_erase_zero, dotProduct_smul, f2Char_dotProduct_self] at hbd
  simp only [smul_eq_mul] at hbd
  -- `|H| = 2ⁿ`, from `Σ χₐ = 0`.
  have hsum : ∑ v, f2Char a v = 0 := by rw [sum_f2Char, if_neg ha0]
  have hχ : ∀ v, f2Char a v = 2 * (if v ∈ H then (1 : ℝ) else 0) - 1 := by
    intro v
    simp only [hH, Finset.mem_filter, Finset.mem_univ, true_and, f2Char]
    split_ifs <;> norm_num
  have hHcard : (#H : ℝ) = 2 ^ n := by
    simp only [hχ, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
      Finset.sum_const, card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun, ZMod.card,
      Fintype.card_fin] at hsum
    have : ((#{v | v ∈ H} : ℕ) : ℝ) = #H := by simp
    push_cast at hsum
    rw [this] at hsum
    rw [pow_succ] at hsum
    linarith
  have hHcard' : 2 * #H = Fintype.card (Fin (n + 1) → ZMod 2) := by
    have : ((2 * #H : ℕ) : ℝ) = (Fintype.card (Fin (n + 1) → ZMod 2) : ℕ) := by
      push_cast; rw [hHcard]; simp [ZMod.card, pow_succ]; ring
    exact_mod_cast this
  refine ⟨hHcard', ?_⟩
  have hR : (#((f2Cayley S).edgeBoundary H) : ℝ) = dualWeight S a * #H := by
    rw [hbd, hHcard]
    ring
  exact_mod_cast hR

/-- `h(G) ≤ minDualWeight S`: the half-space `{x | a ⬝ᵥ x = 0}` of a minimising `a ≠ 0` is
admissible in the definition of `h(G)` and has `minDualWeight S` boundary edges per vertex
(`f2Cayley_halfSpace`). -/
theorem f2Cayley_edgeExpansion_le (S : Finset (Fin (n + 1) → ZMod 2)) :
    (f2Cayley S).edgeExpansion ≤ minDualWeight S := by
  obtain ⟨a, ha0, ha⟩ := exists_dualWeight_eq_minDualWeight S
  obtain ⟨hcard, hbd⟩ := f2Cayley_halfSpace S ha0
  have hne : ({x | a ⬝ᵥ x = 0} : Finset (Fin (n + 1) → ZMod 2)).Nonempty := ⟨0, by simp⟩
  have hpos : (0 : ℝ) < #({x | a ⬝ᵥ x = 0} : Finset (Fin (n + 1) → ZMod 2)) := by
    exact_mod_cast hne.card_pos
  refine ((f2Cayley S).edgeExpansion_le hne hcard.le).trans_eq ?_
  rw [hbd, ← ha]
  push_cast
  field_simp

/-- **The Cheeger constant of a Cayley graph of `(ℤ/2)^{n+1}`** is `h(G) = minDualWeight S`, for
every generator set `S` (a generator `0 ∈ S` adds no edge and is not counted by the dual weight).
The vertex count is at least `2`, so the infimum defining `edgeExpansion` runs over a nonempty
family and its junk value `0` for one-vertex graphs does not arise. If `S` does not span (for
instance `S = ∅`) then `h(G) = 0`. The upper bound comes from a half-space
(`f2Cayley_edgeExpansion_le`), the lower bound from the easy direction of Cheeger's inequality
(`degree_sub_secondAdjEigenvalue_div_two_le`); the minimum in the definition of `h(G)` is attained
by the half-space of any minimising `a` (`f2Cayley_halfSpace_attains_edgeExpansion`). -/
theorem f2Cayley_edgeExpansion (S : Finset (Fin (n + 1) → ZMod 2)) :
    (f2Cayley S).edgeExpansion = minDualWeight S := by
  refine le_antisymm (f2Cayley_edgeExpansion_le S) ?_
  have h := degree_sub_secondAdjEigenvalue_div_two_le (f2Cayley_isRegularOfDegree_erase_zero S)
  rw [f2Cayley_secondAdjEigenvalue_erase_zero] at h
  linarith

/-- **The half-space of a minimising `a` attains the Cheeger constant.** If `a ≠ 0` and
`w_S(a) = minDualWeight S`, the half-space `H = {x | a ⬝ᵥ x = 0}` is admissible in the definition
of `h(G)` (it is nonempty and `2 |H| = 2^{n+1}`, by `f2Cayley_halfSpace`) and
`|∂H| / |H| = h(G)`. Its centred indicator `𝟙_H − ½ = ½ χₐ` is a two-valued eigenfunction for
`λ₂`, which is the equality case of Cheeger's easy inequality (Nica, Theorem 12.8). A minimising
`a` exists by `exists_dualWeight_eq_minDualWeight`; see
`f2Cayley_exists_halfSpace_attains_edgeExpansion`. -/
theorem f2Cayley_halfSpace_attains_edgeExpansion (S : Finset (Fin (n + 1) → ZMod 2))
    {a : Fin (n + 1) → ZMod 2} (ha0 : a ≠ 0) (ha : dualWeight S a = minDualWeight S) :
    (#((f2Cayley S).edgeBoundary {x | a ⬝ᵥ x = 0}) : ℝ)
        / #({x | a ⬝ᵥ x = 0} : Finset (Fin (n + 1) → ZMod 2))
      = (f2Cayley S).edgeExpansion := by
  obtain ⟨-, hbd⟩ := f2Cayley_halfSpace S ha0
  have hne : ({x | a ⬝ᵥ x = 0} : Finset (Fin (n + 1) → ZMod 2)).Nonempty := ⟨0, by simp⟩
  have hpos : (0 : ℝ) < #({x | a ⬝ᵥ x = 0} : Finset (Fin (n + 1) → ZMod 2)) := by
    exact_mod_cast hne.card_pos
  rw [f2Cayley_edgeExpansion, hbd, ← ha]
  push_cast
  field_simp

/-- **The minimum defining `h(G)` is attained by a half-space**: there is a nonzero `a` whose
half-space `H = {x | a ⬝ᵥ x = 0}` contains exactly half of the vertices (`2 |H| = 2^{n+1}`) and
has `|∂H| / |H| = h(G) = minDualWeight S`. -/
theorem f2Cayley_exists_halfSpace_attains_edgeExpansion (S : Finset (Fin (n + 1) → ZMod 2)) :
    ∃ a : Fin (n + 1) → ZMod 2, a ≠ 0 ∧
      2 * #({x | a ⬝ᵥ x = 0} : Finset (Fin (n + 1) → ZMod 2))
          = Fintype.card (Fin (n + 1) → ZMod 2) ∧
      (#((f2Cayley S).edgeBoundary {x | a ⬝ᵥ x = 0}) : ℝ)
          / #({x | a ⬝ᵥ x = 0} : Finset (Fin (n + 1) → ZMod 2))
        = (f2Cayley S).edgeExpansion := by
  obtain ⟨a, ha0, ha⟩ := exists_dualWeight_eq_minDualWeight S
  exact ⟨a, ha0, (f2Cayley_halfSpace S ha0).1, f2Cayley_halfSpace_attains_edgeExpansion S ha0 ha⟩

/-- **Cheeger's easy inequality is an equality for every Cayley graph of `(ℤ/2)^{n+1}`**:
`h(G) = (d − λ₂) / 2`, for every generator set `S` (including `S = ∅`, where both sides are `0`,
and `0 ∈ S`). -/
theorem f2Cayley_edgeExpansion_eq_spectralGap_div_two (S : Finset (Fin (n + 1) → ZMod 2)) :
    (f2Cayley S).edgeExpansion = (f2Cayley S).spectralGap / 2 := by
  rw [f2Cayley_edgeExpansion, f2Cayley_spectralGap]
  ring

end SimpleGraph
