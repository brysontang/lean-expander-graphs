import Expanders.SymmetricSpectrum

/-!
# Expander graphs: the two definitions

For a finite simple graph `G` on vertex type `V` this file sets up both ways of saying
"`G` has no bottlenecks", together with the basic facts each one needs.

## Combinatorial side
* `SimpleGraph.edgeBoundary`: the edges leaving a vertex set `S`.
* `SimpleGraph.edgeExpansion`: the Cheeger constant `h(G) = min_{0 < |S| ≤ n/2} |∂S| / |S|`.
* `SimpleGraph.IsEdgeExpander`: every `S` with `|S| ≤ n/2` has `|∂S| ≥ ε |S|`.

## Spectral side
* `SimpleGraph.adjEigenvalues`: adjacency eigenvalues `λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ`.
* `SimpleGraph.spectralGap`: `λ₁ − λ₂`.
* `SimpleGraph.IsSpectralExpander`: the spectral gap is at least `δ`.

## Basic theorems (all proved here)
* `largestAdjEigenvalue_eq`: for a `d`-regular graph the largest eigenvalue is exactly `d`.
* `abs_le_of_adjMatrix_mulVec_eq`: every eigenvalue of a `d`-regular graph lies in `[-d, d]`.
* `dotProduct_adjMatrix_mulVec_le`: `xᵀAx ≤ λ₂ · xᵀx` for `x ⟂ 𝟙`.
* `spectralGap_mul_le`: the Poincaré inequality
  `(d − λ₂) · Σ x_v² ≤ ½ Σ_{u ~ v} (x_u − x_v)²` for `Σ x_v = 0`.
* `exists_sum_eq_zero_secondAdjEigenvalue_mul_le`: that bound on `λ₂` is attained.
* `card_edgeBoundary_le`: `|∂S| ≤ d |S|`; `isEdgeExpander_iff`: `IsEdgeExpander ε ↔ ε ≤ h(G)`.
-/

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Combinatorial expansion -/

/-- The **edge boundary** `∂S` of a vertex set: the edges leaving `S`, recorded as ordered pairs
`(u, v)` with `u ∈ S`, `v ∉ S` and `u ~ v`. Each edge leaving `S` appears exactly once. -/
def edgeBoundary (S : Finset V) : Finset (V × V) := G.interedges S Sᶜ

variable {G} in
theorem mem_edgeBoundary {S : Finset V} {e : V × V} :
    e ∈ G.edgeBoundary S ↔ e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2 := by
  simp [edgeBoundary, mem_interedges_iff]

@[simp]
theorem edgeBoundary_empty : G.edgeBoundary ∅ = ∅ := by
  simp [edgeBoundary, interedges_empty_left]

/-- A set and its complement have the same number of boundary edges. -/
theorem card_edgeBoundary_compl (S : Finset V) :
    #(G.edgeBoundary Sᶜ) = #(G.edgeBoundary S) := by
  have := G.symm
  unfold edgeBoundary
  rw [compl_compl]
  exact Rel.card_interedges_comm _ _

/-- At most `d|S|` edges leave `S` in a `d`-regular graph. -/
theorem card_edgeBoundary_le {d : ℕ} (hd : G.IsRegularOfDegree d) (S : Finset V) :
    #(G.edgeBoundary S) ≤ d * #S := by
  have hfib : #(G.edgeBoundary S)
      = ∑ u ∈ S, #{e ∈ G.edgeBoundary S | e.1 = u} :=
    Finset.card_eq_sum_card_fiberwise fun e he => (mem_edgeBoundary.mp he).1
  rw [hfib, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [← hd u, ← G.card_neighborFinset_eq_degree u]
  refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
  · intro e he
    have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
    have hadj := (mem_edgeBoundary.mp he'.1).2.2
    rw [he'.2] at hadj
    simpa using hadj
  · intro e₁ h₁ e₂ h₂ h
    have h₁' := (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).2
    have h₂' := (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).2
    exact Prod.ext (h₁'.trans h₂'.symm) h

/-- The **edge expansion** (Cheeger constant)
`h(G) = min { |∂S| / |S| : S ≠ ∅, |S| ≤ n/2 }`.

(On fewer than two vertices there is no admissible `S` and the value is the junk value `0`.) -/
noncomputable def edgeExpansion : ℝ :=
  ⨅ S : {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V},
    (#(G.edgeBoundary S.1) : ℝ) / #S.1

/-- `G` is an **`ε`-edge-expander**: every vertex set `S` containing at most half the vertices
has at least `ε|S|` edges leaving it. -/
def IsEdgeExpander (ε : ℝ) : Prop :=
  ∀ S : Finset V, 2 * #S ≤ Fintype.card V → ε * #S ≤ #(G.edgeBoundary S)

theorem edgeExpansion_nonneg : 0 ≤ G.edgeExpansion :=
  Real.iInf_nonneg fun _ => by positivity

theorem edgeExpansion_le {S : Finset V} (hS : S.Nonempty) (h : 2 * #S ≤ Fintype.card V) :
    G.edgeExpansion ≤ #(G.edgeBoundary S) / #S :=
  ciInf_le (f := fun S : {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V} =>
      (#(G.edgeBoundary S.1) : ℝ) / #S.1)
    ⟨0, by rintro _ ⟨S, rfl⟩; positivity⟩ ⟨S, hS, h⟩

variable {G} in
theorem IsEdgeExpander.mono {ε ε' : ℝ} (h : G.IsEdgeExpander ε') (hε : ε ≤ ε') :
    G.IsEdgeExpander ε := fun S hS =>
  (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)).trans (h S hS)

/-- A graph is an `h(G)`-edge-expander. -/
theorem isEdgeExpander_edgeExpansion : G.IsEdgeExpander G.edgeExpansion := by
  intro S h
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · have hpos : (0 : ℝ) < #S := by exact_mod_cast hS.card_pos
    exact (le_div_iff₀ hpos).mp (G.edgeExpansion_le hS h)

variable {G} in
theorem IsEdgeExpander.le_edgeExpansion [Nontrivial V] {ε : ℝ} (h : G.IsEdgeExpander ε) :
    ε ≤ G.edgeExpansion := by
  have : Nonempty {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V} :=
    ⟨⟨{Classical.arbitrary V}, singleton_nonempty _, by
      have := Fintype.one_lt_card (α := V)
      rw [card_singleton]; omega⟩⟩
  refine le_ciInf fun S => ?_
  have hpos : (0 : ℝ) < #S.1 := by exact_mod_cast S.2.1.card_pos
  exact (le_div_iff₀ hpos).mpr (h S.1 S.2.2)

/-- `G` is an `ε`-edge-expander exactly when `ε` is at most the Cheeger constant. -/
theorem isEdgeExpander_iff [Nontrivial V] {ε : ℝ} :
    G.IsEdgeExpander ε ↔ ε ≤ G.edgeExpansion :=
  ⟨fun h => h.le_edgeExpansion, fun h => G.isEdgeExpander_edgeExpansion.mono h⟩

/-- The Cheeger constant of a `d`-regular graph is at most `d`. -/
theorem edgeExpansion_le_degree [Nontrivial V] {d : ℕ} (hd : G.IsRegularOfDegree d) :
    G.edgeExpansion ≤ d := by
  have h2 : 2 * #({Classical.arbitrary V} : Finset V) ≤ Fintype.card V := by
    have := Fintype.one_lt_card (α := V)
    rw [card_singleton]; omega
  have h := G.isEdgeExpander_edgeExpansion _ h2
  have hb := G.card_edgeBoundary_le hd {Classical.arbitrary V}
  have hb' : (#(G.edgeBoundary {Classical.arbitrary V}) : ℝ) ≤ d := by exact_mod_cast (by simpa using hb)
  simpa using h.trans hb'

/-! ## Spectral expansion -/

/-- The eigenvalues of the adjacency matrix, in decreasing order `λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ`
(indexed from `0`). -/
noncomputable def adjEigenvalues : Fin (Fintype.card V) → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀

theorem adjEigenvalues_antitone : Antitone G.adjEigenvalues :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀_antitone

/-- The largest adjacency eigenvalue `λ₁`. -/
noncomputable def largestAdjEigenvalue [Nonempty V] : ℝ :=
  (G.isHermitian_adjMatrix ℝ).largestEigenvalue

/-- The second-largest adjacency eigenvalue `λ₂`, counted with multiplicity. -/
noncomputable def secondAdjEigenvalue [Nontrivial V] : ℝ :=
  (G.isHermitian_adjMatrix ℝ).secondEigenvalue

theorem largestAdjEigenvalue_eq_adjEigenvalues [Nonempty V] :
    G.largestAdjEigenvalue = G.adjEigenvalues ⟨0, Fintype.card_pos⟩ := rfl

theorem secondAdjEigenvalue_eq_adjEigenvalues [Nontrivial V] :
    G.secondAdjEigenvalue = G.adjEigenvalues ⟨1, Fintype.one_lt_card⟩ := rfl

/-- The **spectral gap** `λ₁ − λ₂` of the adjacency matrix. For a `d`-regular graph this is
`d − λ₂` (`SimpleGraph.spectralGap_eq`). -/
noncomputable def spectralGap [Nontrivial V] : ℝ :=
  G.largestAdjEigenvalue - G.secondAdjEigenvalue

/-- `G` is a **spectral expander with gap `δ`**: the second-largest adjacency eigenvalue is at
least `δ` below the largest. -/
def IsSpectralExpander [Nontrivial V] (δ : ℝ) : Prop := δ ≤ G.spectralGap

theorem spectralGap_nonneg [Nontrivial V] : 0 ≤ G.spectralGap :=
  sub_nonneg.mpr (G.isHermitian_adjMatrix ℝ).secondEigenvalue_le_largestEigenvalue

variable {G} {d : ℕ}

omit [DecidableEq V] in
/-- In a `d`-regular graph the all-ones vector is an eigenvector with eigenvalue `d`. -/
theorem adjMatrix_mulVec_one_of_regular (hd : G.IsRegularOfDegree d) :
    G.adjMatrix ℝ *ᵥ (1 : V → ℝ) = (d : ℝ) • (1 : V → ℝ) := by
  ext v
  simp [adjMatrix_mulVec_apply, hd v]

omit [DecidableEq V] in
/-- Every adjacency eigenvalue of a `d`-regular graph lies in `[-d, d]`. -/
theorem abs_le_of_adjMatrix_mulVec_eq (hd : G.IsRegularOfDegree d) {μ : ℝ} {w : V → ℝ}
    (hw : w ≠ 0) (h : G.adjMatrix ℝ *ᵥ w = μ • w) : |μ| ≤ d := by
  -- Look at a coordinate of largest absolute value.
  obtain ⟨u₀, hu₀⟩ := Function.ne_iff.mp hw
  obtain ⟨v, -, hv⟩ := Finset.exists_max_image univ (fun v => |w v|) ⟨u₀, mem_univ _⟩
  have hpos : 0 < |w v| := lt_of_lt_of_le (abs_pos.mpr hu₀) (hv u₀ (mem_univ _))
  have hv' := congrFun h v
  rw [adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] at hv'
  have key : |μ| * |w v| ≤ d * |w v| :=
    calc |μ| * |w v| = |∑ u ∈ G.neighborFinset v, w u| := by rw [hv', abs_mul]
      _ ≤ ∑ u ∈ G.neighborFinset v, |w u| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _u ∈ G.neighborFinset v, |w v| := Finset.sum_le_sum fun u _ => hv u (mem_univ _)
      _ = d * |w v| := by
        rw [Finset.sum_const, card_neighborFinset_eq_degree, hd v, nsmul_eq_mul]
  exact le_of_mul_le_mul_right key hpos

/-- **The largest eigenvalue of a `d`-regular graph is `d`.** -/
theorem largestAdjEigenvalue_eq [Nonempty V] (hd : G.IsRegularOfDegree d) :
    G.largestAdjEigenvalue = d := by
  have h1 : (1 : V → ℝ) ≠ 0 := fun h => one_ne_zero (congrFun h (Classical.arbitrary V))
  refine le_antisymm ?_ ?_
  · obtain ⟨w, hw, hAw⟩ := (G.isHermitian_adjMatrix ℝ).exists_eigenvector_largest
    exact (le_abs_self _).trans (abs_le_of_adjMatrix_mulVec_eq hd hw hAw)
  · exact (G.isHermitian_adjMatrix ℝ).le_largest_of_mulVec_eq h1
      (adjMatrix_mulVec_one_of_regular hd)

theorem secondAdjEigenvalue_le [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    G.secondAdjEigenvalue ≤ d :=
  (G.isHermitian_adjMatrix ℝ).secondEigenvalue_le_largestEigenvalue.trans
    (largestAdjEigenvalue_eq hd).le

/-- For a `d`-regular graph the spectral gap is `d − λ₂`. -/
theorem spectralGap_eq [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    G.spectralGap = d - G.secondAdjEigenvalue := by
  rw [spectralGap, largestAdjEigenvalue_eq hd]

/-- **Variational bound for `λ₂`**: in a `d`-regular graph, `xᵀAx ≤ λ₂ · xᵀx` for every `x`
orthogonal to the all-ones vector. -/
theorem dotProduct_adjMatrix_mulVec_le [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {x : V → ℝ} (hx : ∑ v, x v = 0) :
    x ⬝ᵥ G.adjMatrix ℝ *ᵥ x ≤ G.secondAdjEigenvalue * (x ⬝ᵥ x) := by
  have h1 : (1 : V → ℝ) ≠ 0 := fun h => one_ne_zero (congrFun h (Classical.arbitrary V))
  refine (G.isHermitian_adjMatrix ℝ).dotProduct_mulVec_le_second h1 ?_ ?_
  · rw [adjMatrix_mulVec_one_of_regular hd]
    exact congrArg (· • (1 : V → ℝ)) (largestAdjEigenvalue_eq hd).symm
  · rw [dotProduct_one, hx]

/-- **Poincaré inequality for regular graphs**: if `Σ x_v = 0` then
`(d − λ₂) · Σ x_v² ≤ ½ Σ_{u ~ v} (x_u − x_v)²`, the right-hand side being the Laplacian
quadratic form (each edge counted once). -/
theorem spectralGap_mul_le [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {x : V → ℝ} (hx : ∑ v, x v = 0) :
    G.spectralGap * (x ⬝ᵥ x)
      ≤ (∑ u, ∑ v, if G.Adj u v then (x u - x v) ^ 2 else 0) / 2 := by
  rw [← G.lapMatrix_toLinearMap₂' ℝ x, toLinearMap₂'_apply', lapMatrix, sub_mulVec,
    dotProduct_sub, dotProduct_mulVec_degMatrix, spectralGap_eq hd, sub_mul]
  have hdeg : ∑ i, (G.degree i : ℝ) * x i * x i = d * (x ⬝ᵥ x) := by
    simp only [hd.degree_eq, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hdeg]
  linarith [dotProduct_adjMatrix_mulVec_le hd hx]

variable (G) in
/-- The variational bound for `λ₂` is attained: some nonzero `x ⟂ 𝟙` has `λ₂ · xᵀx ≤ xᵀAx`.
With `dotProduct_adjMatrix_mulVec_le` this says that for a regular graph
`λ₂ = max { xᵀAx / xᵀx : x ≠ 0, Σ x_v = 0 }`. -/
theorem exists_sum_eq_zero_secondAdjEigenvalue_mul_le [Nontrivial V] :
    ∃ x : V → ℝ, x ≠ 0 ∧ ∑ v, x v = 0 ∧
      G.secondAdjEigenvalue * (x ⬝ᵥ x) ≤ x ⬝ᵥ G.adjMatrix ℝ *ᵥ x := by
  obtain ⟨x, hx, hx1, hle⟩ := (G.isHermitian_adjMatrix ℝ).exists_orthogonal_second_le 1
  exact ⟨x, hx, by rwa [dotProduct_one] at hx1, hle⟩

/-- A `d`-regular graph has an eigenvector for `λ₂` orthogonal to the constants:
some `f ≠ 0` with `Σ f_v = 0` and `A f = λ₂ f`. -/
theorem exists_eigenvector_secondAdjEigenvalue [Nontrivial V] (hd : G.IsRegularOfDegree d) :
    ∃ f : V → ℝ, f ≠ 0 ∧ ∑ v, f v = 0 ∧
      G.adjMatrix ℝ *ᵥ f = G.secondAdjEigenvalue • f := by
  have h1 : G.adjMatrix ℝ *ᵥ (1 : V → ℝ)
      = (G.isHermitian_adjMatrix ℝ).largestEigenvalue • (1 : V → ℝ) := by
    rw [adjMatrix_mulVec_one_of_regular hd]
    exact congrArg (· • (1 : V → ℝ)) (largestAdjEigenvalue_eq hd).symm
  obtain ⟨x, hx, hx1, hAx⟩ := (G.isHermitian_adjMatrix ℝ).exists_eigenvector_second h1
  exact ⟨x, hx, by rwa [dotProduct_one] at hx1, hAx⟩

/-- The Laplacian quadratic form of a `d`-regular graph:
`½ Σ_{u ~ v} (x_u − x_v)² = d · xᵀx − xᵀAx` (the sum runs over ordered adjacent pairs, so each
edge is counted twice before halving). -/
theorem sum_adj_sub_sq_div_two (hd : G.IsRegularOfDegree d) (x : V → ℝ) :
    (∑ u, ∑ v, if G.Adj u v then (x u - x v) ^ 2 else 0) / 2
      = d * (x ⬝ᵥ x) - x ⬝ᵥ G.adjMatrix ℝ *ᵥ x := by
  rw [← G.lapMatrix_toLinearMap₂' ℝ x, toLinearMap₂'_apply', lapMatrix, sub_mulVec,
    dotProduct_sub, dotProduct_mulVec_degMatrix]
  congr 1
  simp only [hd.degree_eq, dotProduct, Finset.mul_sum, mul_assoc]

end SimpleGraph
