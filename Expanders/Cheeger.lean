import Expanders.Basic

/-!
# Cheeger's inequality

The combinatorial and spectral definitions of expansion agree up to constants: for a `d`-regular
graph with second adjacency eigenvalue `λ₂` and Cheeger constant `h(G)`,

  `(d − λ₂) / 2 ≤ h(G) ≤ √(2 d (d − λ₂))`.

* `SimpleGraph.spectralGap_div_two_le_edgeExpansion`: the left ("easy") inequality. **Proved.**
* `SimpleGraph.edgeExpansion_le_sqrt`: the right ("hard") inequality. **Stated, not yet proved.**
-/

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Summing the indicator of a set of ordered pairs over all pairs counts the set. -/
private theorem sum_sum_indicator (F : Finset (V × V)) :
    (∑ u, ∑ v, if (u, v) ∈ F then (1 : ℝ) else 0) = #F := by
  rw [← Finset.sum_product', Finset.univ_product_univ]
  simp

/-- The Laplacian quadratic form of a shifted indicator function counts boundary edges:
`½ Σ_{u ~ v} (x_u − x_v)² = |∂S|` for `x = 𝟙_S − c`. -/
theorem sum_adj_indicator_sub_sq (S : Finset V) (c : ℝ) :
    (∑ u, ∑ v, if G.Adj u v then
        (((if u ∈ S then (1 : ℝ) else 0) - c) - ((if v ∈ S then (1 : ℝ) else 0) - c)) ^ 2
      else 0) / 2 = #(G.edgeBoundary S) := by
  have hterm : ∀ u v, (if G.Adj u v then
        (((if u ∈ S then (1 : ℝ) else 0) - c) - ((if v ∈ S then (1 : ℝ) else 0) - c)) ^ 2
      else 0)
      = (if (u, v) ∈ G.edgeBoundary S then (1 : ℝ) else 0)
        + (if (u, v) ∈ G.edgeBoundary Sᶜ then (1 : ℝ) else 0) := by
    intro u v
    rw [show ((if u ∈ S then (1 : ℝ) else 0) - c) - ((if v ∈ S then (1 : ℝ) else 0) - c)
        = (if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then (1 : ℝ) else 0) by ring]
    by_cases ha : G.Adj u v <;> by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
      simp [mem_edgeBoundary, ha, hu, hv]
  simp only [hterm, Finset.sum_add_distrib, sum_sum_indicator, G.card_edgeBoundary_compl]
  ring

/-- **Cheeger's inequality, easy direction (set form).** In a `d`-regular graph every set `S`
with at most half the vertices has at least `(d − λ₂)/2 · |S|` edges leaving it. -/
theorem isEdgeExpander_spectralGap_div_two [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    G.IsEdgeExpander (G.spectralGap / 2) := by
  intro S hS
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hs0 : (0 : ℝ) ≤ #S := Nat.cast_nonneg _
  have hS' : 2 * (#S : ℝ) ≤ Fintype.card V := by exact_mod_cast hS
  -- Test vector: the indicator of `S`, shifted to be orthogonal to the all-ones vector.
  let x : V → ℝ := fun v => (if v ∈ S then (1 : ℝ) else 0) - #S / Fintype.card V
  have h1 : ∑ v : V, (if v ∈ S then (1 : ℝ) else 0) = #S := by simp
  have hsum : ∑ v, x v = 0 := by
    simp only [x, Finset.sum_sub_distrib, h1, Finset.sum_const, card_univ, nsmul_eq_mul]
    field_simp
    ring
  have hxx : x ⬝ᵥ x = #S * (Fintype.card V - #S) / Fintype.card V := by
    have hterm : ∀ v, x v * x v = (if v ∈ S then (1 : ℝ) else 0)
        * (1 - 2 * (#S / Fintype.card V)) + (#S / Fintype.card V : ℝ) ^ 2 := by
      intro v
      by_cases hv : v ∈ S <;> simp [x, hv] <;> ring
    simp only [dotProduct, hterm, Finset.sum_add_distrib, ← Finset.sum_mul, h1, Finset.sum_const,
      card_univ, nsmul_eq_mul]
    field_simp
    ring
  have key := spectralGap_mul_le hd hsum
  rw [hxx, sum_adj_indicator_sub_sq] at key
  -- `|S| ≤ n/2` gives `|S|(n − |S|)/n ≥ |S|/2`.
  have h2 : (#S : ℝ) / 2 ≤ #S * (Fintype.card V - #S) / Fintype.card V := by
    rw [div_le_div_iff₀ (by norm_num) hn]
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hS')]
  calc G.spectralGap / 2 * #S = G.spectralGap * (#S / 2) := by ring
    _ ≤ G.spectralGap * (#S * (Fintype.card V - #S) / Fintype.card V) :=
        mul_le_mul_of_nonneg_left h2 G.spectralGap_nonneg
    _ ≤ #(G.edgeBoundary S) := key

/-- **Cheeger's inequality, easy direction**: `(d − λ₂) / 2 ≤ h(G)`.
A spectral gap forces combinatorial expansion. -/
theorem spectralGap_div_two_le_edgeExpansion [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    G.spectralGap / 2 ≤ G.edgeExpansion :=
  (isEdgeExpander_spectralGap_div_two hd).le_edgeExpansion

/-- The easy direction with the gap written out as `d − λ₂`. -/
theorem degree_sub_secondAdjEigenvalue_div_two_le [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    ((d : ℝ) - G.secondAdjEigenvalue) / 2 ≤ G.edgeExpansion := by
  rw [← spectralGap_eq hd]
  exact spectralGap_div_two_le_edgeExpansion hd

/-- **Cheeger's inequality, hard direction**: `h(G) ≤ √(2 d (d − λ₂))`.
Combinatorial expansion forces a spectral gap.

Not yet proved. The standard proof takes an eigenvector for `λ₂`, truncates it to its positive
part, and finds a sparse cut among its level sets (the "sweep cut" / co-area argument). -/
theorem edgeExpansion_le_sqrt [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    G.edgeExpansion ≤ Real.sqrt (2 * d * G.spectralGap) := by
  sorry

/-- **Cheeger's inequality**: the two notions of expansion agree up to constants,
`(d − λ₂)/2 ≤ h(G) ≤ √(2d(d − λ₂))`. (Depends on the unproved hard direction.) -/
theorem cheeger [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    G.spectralGap / 2 ≤ G.edgeExpansion ∧
      G.edgeExpansion ≤ Real.sqrt (2 * d * G.spectralGap) :=
  ⟨spectralGap_div_two_le_edgeExpansion hd, edgeExpansion_le_sqrt hd⟩

end SimpleGraph
