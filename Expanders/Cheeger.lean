/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.Basic

/-!
# Cheeger's inequality

The combinatorial and spectral definitions of expansion agree up to constants: for a `d`-regular
graph with second adjacency eigenvalue `λ₂` and Cheeger constant `h(G)`,

  `(d − λ₂) / 2 ≤ h(G) ≤ √(2 d (d − λ₂))`.

* `SimpleGraph.spectralGap_div_two_le_edgeExpansion`: the left ("easy") inequality. **Proved.**
* `SimpleGraph.edgeExpansion_le_sqrt`: the right ("hard") inequality. **Proved.**
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

/-! ### The hard direction -/

/-- The indicator of `S`, summed with absolute values over ordered adjacent pairs, counts each
boundary edge twice: `Σ_{u ~ v} |𝟙_S u − 𝟙_S v| = 2 |∂S|`. -/
theorem sum_adj_abs_indicator_sub (S : Finset V) :
    (∑ u, ∑ v, if G.Adj u v then
        |(if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then (1 : ℝ) else 0)| else 0)
      = 2 * #(G.edgeBoundary S) := by
  have hterm : ∀ u v, (if G.Adj u v then
        |(if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then (1 : ℝ) else 0)| else 0)
      = (if G.Adj u v then
        (((if u ∈ S then (1 : ℝ) else 0) - 0) - ((if v ∈ S then (1 : ℝ) else 0) - 0)) ^ 2
        else 0) := by
    intro u v
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]
  simp only [hterm]
  have h := sum_adj_indicator_sub_sq (G := G) S 0
  linarith

/-- **Co-area inequality.** For a nonnegative function `φ` supported on a set `S` with at most
half the vertices, `2 h(G) Σ_v φ v ≤ Σ_{u ~ v} |φ u − φ v|` (ordered pairs). Proved by strong
induction on `S`, peeling off the minimum level of `φ` on `S`. -/
theorem two_mul_edgeExpansion_mul_sum_le (S : Finset V) (hS : 2 * #S ≤ Fintype.card V)
    (φ : V → ℝ) (hφ : ∀ v, 0 ≤ φ v) (hφS : ∀ v ∉ S, φ v = 0) :
    2 * G.edgeExpansion * ∑ v, φ v ≤ ∑ u, ∑ v, if G.Adj u v then |φ u - φ v| else 0 := by
  induction S using Finset.strongInduction generalizing φ with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have h0 : ∀ v, φ v = 0 := fun v => hφS v (Finset.notMem_empty v)
    simp [h0]
  -- Peel off the minimum level `m` of `φ` on `S`.
  obtain ⟨v₀, hv₀, hmin⟩ := S.exists_min_image φ hne
  set m := φ v₀ with hm_def
  have hm : 0 ≤ m := hφ v₀
  set φ' : V → ℝ := fun v => if v ∈ S then φ v - m else 0 with hφ'_def
  have hφ' : ∀ v, 0 ≤ φ' v := by
    intro v
    by_cases hv : v ∈ S
    · simp only [φ', hv, if_true]; linarith [hmin v hv]
    · simp [φ', hv]
  have hφ'S : ∀ v ∉ S.erase v₀, φ' v = 0 := by
    intro v hv
    by_cases hvS : v ∈ S
    · have : v = v₀ := by
        by_contra hne'
        exact hv (Finset.mem_erase.mpr ⟨hne', hvS⟩)
      subst this
      simp [φ', hvS, hm_def]
    · simp [φ', hvS]
  have hS' : 2 * #(S.erase v₀) ≤ Fintype.card V :=
    le_trans (Nat.mul_le_mul_left 2 (Finset.card_erase_le)) hS
  have ih' := ih (S.erase v₀) (Finset.erase_ssubset hv₀) hS' φ' hφ' hφ'S
  -- Decompose `φ = m 𝟙_S + φ'`.
  have hdecomp : ∀ v, φ v = m * (if v ∈ S then (1 : ℝ) else 0) + φ' v := by
    intro v
    by_cases hv : v ∈ S
    · simp [φ', hv]
    · simp [φ', hv, hφS v hv]
  have hsum : ∑ v, φ v = m * #S + ∑ v, φ' v := by
    simp only [hdecomp, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have habs : ∀ u v, (if G.Adj u v then |φ u - φ v| else 0)
      = m * (if G.Adj u v then
          |(if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then (1 : ℝ) else 0)| else 0)
        + (if G.Adj u v then |φ' u - φ' v| else 0) := by
    intro u v
    by_cases ha : G.Adj u v
    · simp only [ha, if_true]
      have hu' := hφ' u
      have hv' := hφ' v
      by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
      · have e1 : φ u - φ v = φ' u - φ' v := by simp [φ', hu, hv]
        rw [e1]; simp [hu, hv]
      · have e1 : φ u - φ v = m + φ' u := by simp [φ', hu, hφS v hv]
        have e2 : φ' v = 0 := by simp [φ', hv]
        rw [e1, e2, abs_of_nonneg (by linarith), sub_zero, abs_of_nonneg hu']
        simp [hu, hv]
      · have e1 : φ u - φ v = -(m + φ' v) := by simp [φ', hv, hφS u hu]
        have e2 : φ' u = 0 := by simp [φ', hu]
        rw [e1, e2, abs_neg, abs_of_nonneg (by linarith), zero_sub, abs_neg, abs_of_nonneg hv']
        simp [hu, hv]
      · simp [φ', hu, hv, hφS u hu, hφS v hv]
    · simp [ha]
  have hexp := G.isEdgeExpander_edgeExpansion S hS
  have hcut := sum_adj_abs_indicator_sub (G := G) S
  simp only [habs, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hcut, hsum]
  nlinarith [mul_le_mul_of_nonneg_left hexp hm]

omit [DecidableEq V] in
/-- In a `d`-regular graph, `Σ_u Σ_{v ~ u} x u = d Σ_u x u`. -/
theorem sum_adj_left (hd : G.IsRegularOfDegree d) (x : V → ℝ) :
    (∑ u, ∑ v, if G.Adj u v then x u else 0) = d * ∑ u, x u := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, ← G.neighborFinset_eq_filter,
    card_neighborFinset_eq_degree, hd u, nsmul_eq_mul, mul_comm]

omit [DecidableEq V] in
/-- In a `d`-regular graph, `Σ_u Σ_{v ~ u} x v = d Σ_v x v`. -/
theorem sum_adj_right (hd : G.IsRegularOfDegree d) (x : V → ℝ) :
    (∑ u, ∑ v, if G.Adj u v then x v else 0) = d * ∑ u, x u := by
  rw [Finset.sum_comm, ← sum_adj_left hd x]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  simp only [G.adj_comm v u]

/-- The core of the hard direction: an eigenvector for `λ₂` whose positive part is supported on
at most half the vertices certifies `h(G)² ≤ 2 d (d − λ₂)`. -/
theorem edgeExpansion_sq_le_of_eigenvector [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {f : V → ℝ} (hf : f ≠ 0) (hf0 : ∑ v, f v = 0)
    (hAf : G.adjMatrix ℝ *ᵥ f = G.secondAdjEigenvalue • f)
    (hhalf : 2 * #{v | 0 < f v} ≤ Fintype.card V) :
    G.edgeExpansion ^ 2 ≤ 2 * d * G.spectralGap := by
  -- The positive part `g` of `f`.
  set g : V → ℝ := fun v => max (f v) 0 with hg_def
  have hg0 : ∀ v, 0 ≤ g v := fun v => le_max_right _ _
  have hgf : ∀ v, g v * f v = g v * g v := by
    intro v
    rcases le_total (f v) 0 with h | h
    · simp [g, max_eq_right h]
    · simp [g, max_eq_left h]
  have hpos : ∃ v, 0 < f v := by
    by_contra hcon
    push Not at hcon
    apply hf
    have := (Finset.sum_eq_zero_iff_of_nonpos (fun v _ => hcon v)).mp hf0
    funext v
    exact this v (mem_univ v)
  obtain ⟨v₀, hv₀⟩ := hpos
  set Q := g ⬝ᵥ g with hQ_def
  have hQ : 0 < Q := by
    have h1 : 0 < g v₀ * g v₀ := by
      have : g v₀ = f v₀ := max_eq_left hv₀.le
      rw [this]; exact mul_pos hv₀ hv₀
    exact lt_of_lt_of_le h1
      (Finset.single_le_sum (f := fun v => g v * g v) (fun v _ => mul_self_nonneg (g v))
        (mem_univ v₀))
  -- Energy bound: `Σ_{u ~ v} (g u − g v)² ≤ 2 (d − λ₂) gᵀg`.
  have hAg : ∀ v, G.secondAdjEigenvalue * f v ≤ (G.adjMatrix ℝ *ᵥ g) v := by
    intro v
    have h := congrFun hAf v
    rw [Pi.smul_apply, smul_eq_mul] at h
    rw [← h, adjMatrix_mulVec_apply, adjMatrix_mulVec_apply]
    exact Finset.sum_le_sum fun u _ => le_max_left _ _
  have hgAg : G.secondAdjEigenvalue * Q ≤ g ⬝ᵥ G.adjMatrix ℝ *ᵥ g := by
    simp only [Q, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    calc G.secondAdjEigenvalue * (g v * g v) = g v * (G.secondAdjEigenvalue * f v) := by
          rw [← hgf v]; ring
      _ ≤ g v * (G.adjMatrix ℝ *ᵥ g) v := mul_le_mul_of_nonneg_left (hAg v) (hg0 v)
  set E := ∑ u, ∑ v, if G.Adj u v then (g u - g v) ^ 2 else 0 with hE_def
  have hE : E ≤ 2 * G.spectralGap * Q := by
    have := sum_adj_sub_sq_div_two hd g
    rw [spectralGap_eq hd]
    nlinarith
  have hE0 : 0 ≤ E :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => by split_ifs <;> positivity
  -- `Σ_{u ~ v} (g u + g v)² ≤ 4 d gᵀg`.
  set P := ∑ u, ∑ v, if G.Adj u v then (g u + g v) ^ 2 else 0 with hP_def
  have hP : P ≤ 4 * d * Q := by
    have hPE : P + E = 2 * (∑ u, ∑ v, if G.Adj u v then g u ^ 2 else 0)
        + 2 * (∑ u, ∑ v, if G.Adj u v then g v ^ 2 else 0) := by
      simp only [P, E, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> ring
    rw [sum_adj_left hd, sum_adj_right hd] at hPE
    have hQ' : ∑ u, g u ^ 2 = Q := by simp [Q, dotProduct, sq]
    rw [hQ'] at hPE
    linarith
  have hP0 : 0 ≤ P :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => by split_ifs <;> positivity
  -- Co-area applied to `g²`, supported on `{f > 0}`.
  set T := ∑ u, ∑ v, if G.Adj u v then |g u ^ 2 - g v ^ 2| else 0 with hT_def
  have hcoarea : 2 * G.edgeExpansion * Q ≤ T := by
    have h := two_mul_edgeExpansion_mul_sum_le (G := G) {v | 0 < f v} hhalf
      (fun v => g v ^ 2) (fun v => sq_nonneg _) (by
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv
        simp [g, max_eq_right hv])
    have hQ' : ∑ v, g v ^ 2 = Q := by simp [Q, dotProduct, sq]
    simpa only [hQ'] using h
  -- Cauchy–Schwarz over ordered adjacent pairs: `T² ≤ E P`.
  have hCS : T ^ 2 ≤ E * P := by
    let a : V → V → ℝ := fun u v => if G.Adj u v then |g u - g v| else 0
    let b : V → V → ℝ := fun u v => if G.Adj u v then g u + g v else 0
    have e1 : ∀ u v, (if G.Adj u v then |g u ^ 2 - g v ^ 2| else 0) = a u v * b u v := by
      intro u v
      simp only [a, b]
      split_ifs
      · rw [show g u ^ 2 - g v ^ 2 = (g u - g v) * (g u + g v) by ring, abs_mul,
          abs_of_nonneg (add_nonneg (hg0 u) (hg0 v))]
      · simp
    have e2 : ∀ u v, (if G.Adj u v then (g u - g v) ^ 2 else 0) = a u v ^ 2 := by
      intro u v
      simp only [a]
      split_ifs <;> simp [sq_abs]
    have e3 : ∀ u v, (if G.Adj u v then (g u + g v) ^ 2 else 0) = b u v ^ 2 := by
      intro u v
      simp only [b]
      split_ifs <;> simp
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (V × V))
      (fun p => a p.1 p.2) (fun p => b p.1 p.2)
    simp only [Fintype.sum_prod_type] at hcs
    simp only [T, E, P, e1, e2, e3]
    exact hcs
  -- Combine.
  have hh := G.edgeExpansion_nonneg
  have hgap := G.spectralGap_nonneg
  have h1 : (2 * G.edgeExpansion * Q) ^ 2 ≤ T ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcoarea 2
  have h2 : E * P ≤ (2 * G.spectralGap * Q) * (4 * d * Q) :=
    mul_le_mul hE hP hP0 (by positivity)
  have h3 : G.edgeExpansion ^ 2 * (4 * Q ^ 2) ≤ (2 * d * G.spectralGap) * (4 * Q ^ 2) := by
    nlinarith
  exact le_of_mul_le_mul_right h3 (by positivity)

/-- **Cheeger's inequality, hard direction**: `h(G) ≤ √(2 d (d − λ₂))`.
Combinatorial expansion forces a spectral gap.

The proof takes an eigenvector for `λ₂`, truncates it to its positive part `g` (choosing the sign
so that the support has at most half the vertices), and applies the co-area inequality to `g²`
together with Cauchy–Schwarz (the "sweep cut" argument). -/
theorem edgeExpansion_le_sqrt [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    G.edgeExpansion ≤ Real.sqrt (2 * d * G.spectralGap) := by
  obtain ⟨f, hf, hf0, hAf⟩ := exists_eigenvector_secondAdjEigenvalue hd
  have key : G.edgeExpansion ^ 2 ≤ 2 * d * G.spectralGap := by
    have hcount : #{v | 0 < f v} + #{v | 0 < (-f) v} ≤ Fintype.card V := by
      have h1 : #{v | 0 < (-f) v} ≤ #{v | ¬ 0 < f v} := by
        refine Finset.card_le_card fun v hv => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.neg_apply] at hv ⊢
        linarith
      have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset V))
        (fun v => 0 < f v)
      rw [card_univ] at h2
      omega
    by_cases h : 2 * #{v | 0 < f v} ≤ Fintype.card V
    · exact edgeExpansion_sq_le_of_eigenvector hd hf hf0 hAf h
    · refine edgeExpansion_sq_le_of_eigenvector hd (neg_ne_zero.mpr hf) ?_ ?_ (by omega)
      · simp [hf0]
      · rw [mulVec_neg, hAf, smul_neg]
  exact (le_abs_self _).trans (Real.abs_le_sqrt key)

/-- **Cheeger's inequality**: the two notions of expansion agree up to constants,
`(d − λ₂)/2 ≤ h(G) ≤ √(2d(d − λ₂))`. -/
theorem cheeger [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    G.spectralGap / 2 ≤ G.edgeExpansion ∧
      G.edgeExpansion ≤ Real.sqrt (2 * d * G.spectralGap) :=
  ⟨spectralGap_div_two_le_edgeExpansion hd, edgeExpansion_le_sqrt hd⟩

end SimpleGraph
