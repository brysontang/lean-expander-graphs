/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.Basic

/-!
# The Alon–Boppana bound and Ramanujan graphs

The spectral gap of a `d`-regular graph has a ceiling: `λ₂` cannot stay far below `2√(d − 1)`
once the graph is large. Graphs that meet this ceiling are called *Ramanujan*.

* `SimpleGraph.IsRamanujan`: the definition.
* `SimpleGraph.alon_boppana`: the bound `λ₂ ≥ 2√(d − 1) − o(1)`.

## Proof of the bound

The proof is a pointwise variant of Nilli's argument; everything it needs lives in the namespace
`SimpleGraph.AlonBoppana`.

1. *Radial functions* (`radial`). Fix a centre `v₀` and a profile `g : ℕ → ℝ`, and let
   `F v = g (dist v₀ v)` (and `F v = 0` if `v` is not reachable from `v₀`). Distances are
   `SimpleGraph.edist`, so unreachable vertices are at distance `⊤` and need no special care.
2. *The local estimate* (`mul_radial_le_adjMatrix_mulVec`). A vertex at distance `n + 1` has a
   neighbour at distance `n`, and all its neighbours are at distance at most `n + 2`. So if `g`
   is nonnegative and nonincreasing with `μ g(0) ≤ d g(1)` and
   `μ g(n + 1) ≤ g(n) + (d − 1) g(n + 2)`, then `μ F ≤ A F` pointwise, hence `μ ⟨F, F⟩ ≤ ⟨F, A F⟩`.
   No counting of the distance layers is needed.
3. *The profile* (`exists_profile`). For `μ = 2√(d − 1) − ε` such a `g` exists with finite
   support: `g(i) = (d − 1)^(−i/2) h(i)` with `h` a tent (`tent`), rising linearly to a high peak
   and then falling linearly to `0`. The tent is harmonic except at its peak, where the defect is
   absorbed by `ε`. (For `d ≤ 1` one has `μ < 0` and the indicator of the centre works.)
4. *Two far-apart centres* (`le_secondAdjEigenvalue_of_lt_edist`). If `g` vanishes from `K` on
   and `dist v₀ v₁ > 2K`, the radial functions `F₁`, `F₂` around `v₀`, `v₁` have disjoint supports
   with no edge between them, so the combination `x = (Σ F₂) F₁ − (Σ F₁) F₂` is orthogonal to the
   constants and still has Rayleigh quotient at least `μ`; the variational bound
   `SimpleGraph.dotProduct_adjMatrix_mulVec_le` gives `μ ≤ λ₂`.
5. *Far-apart centres exist* (`exists_lt_edist`). A ball of radius `r` has at most `(d + 1) ^ r`
   vertices, so a graph on more than `(d + 1) ^ (2K)` vertices has two vertices at distance
   more than `2K`.
-/

open Finset Matrix

namespace SimpleGraph

/-- A `d`-regular graph is **Ramanujan** if every adjacency eigenvalue `μ` other than `±d`
satisfies `|μ| ≤ 2√(d − 1)`: its spectral gap is as large as the Alon–Boppana bound allows. -/
def IsRamanujan {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) : Prop :=
  G.IsRegularOfDegree d ∧
    ∀ i, |G.adjEigenvalues i| = d ∨ |G.adjEigenvalues i| ≤ 2 * Real.sqrt (d - 1)

namespace AlonBoppana

/-! ## Graph distance: the two facts about distance layers that the proof uses -/

section Layers

variable {V : Type*} {G : SimpleGraph V}

/-- Adjacent vertices lie in consecutive (or equal) distance layers. -/
theorem edist_le_edist_add_one {w u v : V} (h : G.Adj u v) :
    G.edist w u ≤ G.edist w v + 1 := by
  have h1 : G.edist v u = 1 := edist_eq_one_iff_adj.mpr h.symm
  calc G.edist w u ≤ G.edist w v + G.edist v u := G.edist_triangle
    _ = G.edist w v + 1 := by rw [h1]

/-- A vertex at distance `n + 1` from `w` has a neighbour at distance `n` from `w`. -/
theorem exists_adj_edist_eq {w v : V} {n : ℕ} (h : G.edist w v = (n + 1 : ℕ)) :
    ∃ u, G.Adj v u ∧ G.edist w u = n := by
  have h' := h
  rw [edist_comm] at h'
  obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_coe h'
  cases p with
  | nil => simp at hp
  | @cons _ u _ hadj q =>
    refine ⟨u, hadj, ?_⟩
    have hq : q.length = n := by simpa using hp
    have hle : G.edist w u ≤ n := by
      rw [edist_comm, ← hq]; exact edist_le q
    obtain ⟨k, hk, hkn⟩ := ENat.le_natCast_iff.mp hle
    have h2 : G.edist w v ≤ G.edist w u + 1 := edist_le_edist_add_one hadj
    rw [h, hk] at h2
    have h3 : n + 1 ≤ k + 1 := by exact_mod_cast h2
    rw [hk]
    have : k = n := by omega
    rw [this]

end Layers

/-! ## Radial functions -/

section Radial

variable {V : Type*} {G : SimpleGraph V}

open Classical in
/-- The radial function around `v₀` with profile `g`: it takes the value `g n` on the vertices at
distance exactly `n` from `v₀`, and `0` on the vertices not reachable from `v₀`. -/
noncomputable def radial (G : SimpleGraph V) (v₀ : V) (g : ℕ → ℝ) (v : V) : ℝ :=
  if G.edist v₀ v = ⊤ then 0 else g (G.edist v₀ v).toNat

theorem radial_of_edist_eq {v₀ v : V} {g : ℕ → ℝ} {n : ℕ} (h : G.edist v₀ v = n) :
    radial G v₀ g v = g n := by
  simp [radial, h]

theorem radial_of_edist_eq_top {v₀ v : V} {g : ℕ → ℝ} (h : G.edist v₀ v = ⊤) :
    radial G v₀ g v = 0 := by
  simp [radial, h]

theorem radial_self (v₀ : V) (g : ℕ → ℝ) : radial G v₀ g v₀ = g 0 :=
  radial_of_edist_eq (by simp)

theorem radial_nonneg {g : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i) (v₀ v : V) : 0 ≤ radial G v₀ g v := by
  unfold radial
  split_ifs
  · exact le_rfl
  · exact hg _

/-- A radial function with profile vanishing from `K` on is supported in the ball of radius
`K - 1`. -/
theorem exists_edist_eq_of_radial_ne_zero {v₀ v : V} {g : ℕ → ℝ} {K : ℕ}
    (hK : ∀ i, K ≤ i → g i = 0) (h : radial G v₀ g v ≠ 0) :
    ∃ n, n < K ∧ G.edist v₀ v = n := by
  rcases eq_or_ne (G.edist v₀ v) ⊤ with htop | htop
  · exact absurd (radial_of_edist_eq_top htop) h
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    refine ⟨n, ?_, hn.symm⟩
    by_contra hlt
    exact h (by rw [radial_of_edist_eq hn.symm]; exact hK n (not_lt.mp hlt))

/-- Radial functions around far-apart centres have disjoint supports with no edge between them. -/
theorem radial_mul_radial_eq_zero {v₀ v₁ v u : V} {g : ℕ → ℝ} {K : ℕ}
    (hK : ∀ i, K ≤ i → g i = 0) (hfar : ((2 * K : ℕ) : ℕ∞) < G.edist v₀ v₁)
    (hvu : G.edist v u ≤ 1) : radial G v₀ g v * radial G v₁ g u = 0 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨a, ha, hav⟩ := exists_edist_eq_of_radial_ne_zero hK h1
  obtain ⟨b, hb, hbu⟩ := exists_edist_eq_of_radial_ne_zero hK h2
  have h3 : G.edist v₀ v₁ ≤ G.edist v₀ v + G.edist v u + G.edist u v₁ :=
    G.edist_triangle.trans (add_le_add_left G.edist_triangle _)
  have h4 : G.edist v₀ v₁ ≤ (a : ℕ∞) + 1 + b := by
    rw [edist_comm (u := u), hbu, hav] at h3
    exact h3.trans (by gcongr)
  have h5 : ((2 * K : ℕ) : ℕ∞) < ((a + 1 + b : ℕ) : ℕ∞) := by
    refine lt_of_lt_of_le hfar ?_
    push_cast
    exact h4
  have h6 : 2 * K < a + 1 + b := by exact_mod_cast h5
  omega

end Radial

section Regular

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- **The local estimate.** If the profile `g` is a nonnegative, nonincreasing subsolution of
the radial eigenvalue equation of the `d`-regular tree with eigenvalue `μ`, then the radial
function `F` around any vertex of a `d`-regular graph satisfies `μ F ≤ A F` pointwise. -/
theorem mul_radial_le_adjMatrix_mulVec (hd : G.IsRegularOfDegree d) (v₀ : V) {g : ℕ → ℝ} {μ : ℝ}
    (hanti : Antitone g) (hnn : ∀ i, 0 ≤ g i) (h0 : μ * g 0 ≤ d * g 1)
    (hstep : ∀ i, μ * g (i + 1) ≤ g i + ((d : ℝ) - 1) * g (i + 2)) (v : V) :
    μ * radial G v₀ g v ≤ (G.adjMatrix ℝ *ᵥ radial G v₀ g) v := by
  rw [adjMatrix_mulVec_apply]
  rcases eq_or_ne (G.edist v₀ v) ⊤ with htop | htop
  · rw [radial_of_edist_eq_top htop, mul_zero]
    exact Finset.sum_nonneg fun u _ => radial_nonneg hnn v₀ u
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  have hcard : #(G.neighborFinset v) = d := by
    rw [card_neighborFinset_eq_degree, hd v]
  -- every neighbour is at distance at most `n + 1`, so its value is at least `g (n + 1)`
  have hnbr : ∀ u ∈ G.neighborFinset v, g (n + 1) ≤ radial G v₀ g u := by
    intro u hu
    have hadj : G.Adj v u := (G.mem_neighborFinset v u).mp hu
    have hle : G.edist v₀ u ≤ ((n + 1 : ℕ) : ℕ∞) := by
      have := edist_le_edist_add_one (w := v₀) hadj.symm
      rw [← hn] at this
      exact_mod_cast this
    obtain ⟨k, hk, hkn⟩ := ENat.le_natCast_iff.mp hle
    rw [radial_of_edist_eq hk]
    exact hanti hkn
  cases n with
  | zero =>
    rw [radial_of_edist_eq hn.symm]
    calc μ * g 0 ≤ d * g 1 := h0
      _ = #(G.neighborFinset v) • g (0 + 1) := by rw [hcard, nsmul_eq_mul]
      _ ≤ ∑ u ∈ G.neighborFinset v, radial G v₀ g u :=
        Finset.card_nsmul_le_sum _ _ _ hnbr
  | succ n =>
    rw [radial_of_edist_eq hn.symm]
    obtain ⟨u₀, hadj, hu₀⟩ := exists_adj_edist_eq hn.symm
    have hmem : u₀ ∈ G.neighborFinset v := (G.mem_neighborFinset v u₀).mpr hadj
    have hd1 : 1 ≤ d := by
      rw [← hcard]; exact Finset.card_pos.mpr ⟨u₀, hmem⟩
    have hcard' : (#((G.neighborFinset v).erase u₀) : ℝ) = (d : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem hmem, hcard, Nat.cast_sub hd1, Nat.cast_one]
    calc μ * g (n + 1) ≤ g n + ((d : ℝ) - 1) * g (n + 2) := hstep n
      _ = radial G v₀ g u₀ + #((G.neighborFinset v).erase u₀) • g (n + 1 + 1) := by
        rw [radial_of_edist_eq hu₀, nsmul_eq_mul, hcard']
      _ ≤ radial G v₀ g u₀ + ∑ u ∈ (G.neighborFinset v).erase u₀, radial G v₀ g u := by
        gcongr
        exact Finset.card_nsmul_le_sum _ _ _ fun u hu => hnbr u (Finset.mem_of_mem_erase hu)
      _ = ∑ u ∈ G.neighborFinset v, radial G v₀ g u := Finset.add_sum_erase _ _ hmem

/-- The Rayleigh quotient of the radial function is at least `μ`. -/
theorem mul_radial_dotProduct_le (hd : G.IsRegularOfDegree d) (v₀ : V) {g : ℕ → ℝ} {μ : ℝ}
    (hanti : Antitone g) (hnn : ∀ i, 0 ≤ g i) (h0 : μ * g 0 ≤ d * g 1)
    (hstep : ∀ i, μ * g (i + 1) ≤ g i + ((d : ℝ) - 1) * g (i + 2)) :
    μ * (radial G v₀ g ⬝ᵥ radial G v₀ g)
      ≤ radial G v₀ g ⬝ᵥ G.adjMatrix ℝ *ᵥ radial G v₀ g := by
  simp only [dotProduct, Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have h := mul_radial_le_adjMatrix_mulVec hd v₀ hanti hnn h0 hstep v
  have hv := radial_nonneg (G := G) hnn v₀ v
  nlinarith [mul_le_mul_of_nonneg_left h hv]

/-- Balls in a `d`-regular graph are small: the ball of radius `r` has at most `(d + 1) ^ r`
vertices. -/
theorem exists_finset_edist_le (hd : G.IsRegularOfDegree d) (v₀ : V) (r : ℕ) :
    ∃ B : Finset V, (∀ v, G.edist v₀ v ≤ r → v ∈ B) ∧ #B ≤ (d + 1) ^ r := by
  induction r with
  | zero =>
    refine ⟨{v₀}, fun v hv => ?_, by simp⟩
    have h0 : G.edist v₀ v = 0 := by simpa using hv
    exact Finset.mem_singleton.mpr (edist_eq_zero_iff.mp h0).symm
  | succ r ih =>
    obtain ⟨B, hB, hcard⟩ := ih
    refine ⟨B ∪ B.biUnion fun u => G.neighborFinset u, fun v hv => ?_, ?_⟩
    · obtain ⟨k, hk, hkr⟩ := ENat.le_natCast_iff.mp hv
      rw [Finset.mem_union]
      rcases Nat.lt_or_ge k (r + 1) with hlt | hge
      · exact Or.inl (hB v (by rw [hk]; exact_mod_cast Nat.lt_succ_iff.mp hlt))
      · right
        have hkeq : k = r + 1 := le_antisymm hkr hge
        obtain ⟨u, hadj, hu⟩ := exists_adj_edist_eq (hkeq ▸ hk)
        exact Finset.mem_biUnion.mpr
          ⟨u, hB u hu.le, (G.mem_neighborFinset u v).mpr hadj.symm⟩
    · calc #(B ∪ B.biUnion fun u => G.neighborFinset u)
          ≤ #B + #(B.biUnion fun u => G.neighborFinset u) := Finset.card_union_le _ _
        _ ≤ #B + #B * d := by
          gcongr
          exact Finset.card_biUnion_le_card_mul _ _ _ fun u _ => by
            rw [card_neighborFinset_eq_degree, hd u]
        _ = #B * (d + 1) := by ring
        _ ≤ (d + 1) ^ r * (d + 1) := by gcongr
        _ = (d + 1) ^ (r + 1) := by ring

/-- A large `d`-regular graph has a vertex far from any given one. -/
theorem exists_lt_edist (hd : G.IsRegularOfDegree d) (v₀ : V) {r : ℕ}
    (hr : (d + 1) ^ r < Fintype.card V) : ∃ v₁, (r : ℕ∞) < G.edist v₀ v₁ := by
  obtain ⟨B, hB, hcard⟩ := exists_finset_edist_le hd v₀ r
  by_contra hcon
  have hB' : B = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun v => hB v (not_lt.mp fun h => hcon ⟨v, h⟩)
  rw [hB', Finset.card_univ] at hcard
  omega

/-- **Two far-apart radial functions give a lower bound on `λ₂`.** -/
theorem le_secondAdjEigenvalue_of_lt_edist [Nontrivial V] (hd : G.IsRegularOfDegree d)
    {v₀ v₁ : V} {g : ℕ → ℝ} {μ : ℝ} {K : ℕ}
    (hanti : Antitone g) (hnn : ∀ i, 0 ≤ g i) (hpos : 0 < g 0) (hK : ∀ i, K ≤ i → g i = 0)
    (h0 : μ * g 0 ≤ d * g 1)
    (hstep : ∀ i, μ * g (i + 1) ≤ g i + ((d : ℝ) - 1) * g (i + 2))
    (hfar : ((2 * K : ℕ) : ℕ∞) < G.edist v₀ v₁) :
    μ ≤ G.secondAdjEigenvalue := by
  have hfar' : ((2 * K : ℕ) : ℕ∞) < G.edist v₁ v₀ := by rwa [edist_comm]
  have hR₁ := mul_radial_dotProduct_le hd v₀ hanti hnn h0 hstep
  have hR₂ := mul_radial_dotProduct_le hd v₁ hanti hnn h0 hstep
  generalize hF₁ : radial G v₀ g = F₁ at hR₁
  generalize hF₂ : radial G v₁ g = F₂ at hR₂
  have hF₁nn : ∀ v, 0 ≤ F₁ v := fun v => hF₁ ▸ radial_nonneg hnn v₀ v
  have hF₂nn : ∀ v, 0 ≤ F₂ v := fun v => hF₂ ▸ radial_nonneg hnn v₁ v
  have hF₁v₀ : F₁ v₀ = g 0 := hF₁ ▸ radial_self v₀ g
  have hF₂v₁ : F₂ v₁ = g 0 := hF₂ ▸ radial_self v₁ g
  -- the cross terms vanish
  have h12 : F₁ ⬝ᵥ F₂ = 0 := by
    subst hF₁ hF₂
    simp only [dotProduct]
    exact Finset.sum_eq_zero fun v _ => radial_mul_radial_eq_zero hK hfar (by simp)
  have h1A2 : F₁ ⬝ᵥ G.adjMatrix ℝ *ᵥ F₂ = 0 := by
    subst hF₁ hF₂
    simp only [dotProduct, adjMatrix_mulVec_apply, Finset.mul_sum]
    exact Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun u hu =>
      radial_mul_radial_eq_zero hK hfar
        (edist_eq_one_iff_adj.mpr ((G.mem_neighborFinset v u).mp hu)).le
  have h2A1 : F₂ ⬝ᵥ G.adjMatrix ℝ *ᵥ F₁ = 0 := by
    subst hF₁ hF₂
    simp only [dotProduct, adjMatrix_mulVec_apply, Finset.mul_sum]
    exact Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun u hu =>
      radial_mul_radial_eq_zero hK hfar'
        (edist_eq_one_iff_adj.mpr ((G.mem_neighborFinset v u).mp hu)).le
  -- positivity
  have hpos₁ : 0 < F₁ ⬝ᵥ F₁ := by
    refine Matrix.IsHermitian.dotProduct_self_pos fun h => ?_
    rw [h] at hF₁v₀
    exact hpos.ne hF₁v₀
  have hnn₂ : 0 ≤ F₂ ⬝ᵥ F₂ := Finset.sum_nonneg fun v _ => mul_self_nonneg (F₂ v)
  have ha : 0 < ∑ v, F₂ v :=
    lt_of_lt_of_le (hF₂v₁ ▸ hpos) (Finset.single_le_sum (fun v _ => hF₂nn v) (mem_univ v₁))
  generalize hadef : ∑ v, F₂ v = a at ha
  generalize hbdef : ∑ v, F₁ v = b
  -- the test vector
  have hx : ∑ v, (a • F₁ - b • F₂) v = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hadef, hbdef]
    ring
  have hxx : (a • F₁ - b • F₂) ⬝ᵥ (a • F₁ - b • F₂)
      = a ^ 2 * (F₁ ⬝ᵥ F₁) + b ^ 2 * (F₂ ⬝ᵥ F₂) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm F₂ F₁, h12]
    ring
  have hxAx : (a • F₁ - b • F₂) ⬝ᵥ G.adjMatrix ℝ *ᵥ (a • F₁ - b • F₂)
      = a ^ 2 * (F₁ ⬝ᵥ G.adjMatrix ℝ *ᵥ F₁) + b ^ 2 * (F₂ ⬝ᵥ G.adjMatrix ℝ *ᵥ F₂) := by
    simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, h1A2, h2A1]
    ring
  have hvar := dotProduct_adjMatrix_mulVec_le hd hx
  rw [hxx, hxAx] at hvar
  have hxxpos : 0 < a ^ 2 * (F₁ ⬝ᵥ F₁) + b ^ 2 * (F₂ ⬝ᵥ F₂) := by positivity
  refine le_of_mul_le_mul_right ?_ hxxpos
  nlinarith [mul_le_mul_of_nonneg_left hR₁ (sq_nonneg a),
    mul_le_mul_of_nonneg_left hR₂ (sq_nonneg b)]

end Regular

/-! ## The profile -/

section Profile

/-- The tent: it rises linearly with slope `m * c` from `m * (c + 2)` up to its peak at `i = m`
and then falls linearly to `0` at `i = 2 * m`. -/
noncomputable def tent (c : ℝ) (m i : ℕ) : ℝ :=
  if i ≤ m then m * (c + 2 + c * i) else (c + 2 + c * m) * ((2 * m - i : ℕ) : ℝ)

theorem tent_of_le {c : ℝ} {m i : ℕ} (h : i ≤ m) : tent c m i = m * (c + 2 + c * i) :=
  if_pos h

theorem tent_of_ge {c : ℝ} {m i : ℕ} (h : m ≤ i) :
    tent c m i = (c + 2 + c * m) * ((2 * m - i : ℕ) : ℝ) := by
  rcases h.eq_or_lt with rfl | hlt
  · rw [tent_of_le le_rfl]
    have : 2 * m - m = m := by omega
    rw [this]
    ring
  · exact if_neg (not_le.mpr hlt)

theorem tent_nonneg {c : ℝ} (hc : 0 ≤ c) (m i : ℕ) : 0 ≤ tent c m i := by
  unfold tent
  split_ifs <;> positivity

/-- The tent is almost harmonic: `(2 - δ) h (i + 1) ≤ h i + h (i + 2)` once `δ m ≥ 2`. -/
theorem tent_add_tent {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) {m : ℕ} (hm : 2 ≤ δ * m) (i : ℕ) :
    2 * tent c m (i + 1) - δ * tent c m (i + 1) ≤ tent c m i + tent c m (i + 2) := by
  rcases Nat.lt_or_ge (i + 1) m with h1 | h1
  · -- the rising part
    rw [tent_of_le (by omega : i ≤ m), tent_of_le (by omega : i + 1 ≤ m),
      tent_of_le (by omega : i + 2 ≤ m)]
    have h : 0 ≤ δ * ((m : ℝ) * (c + 2 + c * ((i + 1 : ℕ) : ℝ))) := by positivity
    push_cast at h ⊢
    linarith
  rcases h1.eq_or_lt with h1 | h1
  · -- the peak
    subst h1
    rw [tent_of_le (by omega : i ≤ i + 1), tent_of_le le_rfl,
      tent_of_ge (by omega : i + 1 ≤ i + 2)]
    have hsub : 2 * (i + 1) - (i + 2) = i := by omega
    rw [hsub]
    have hH : 0 ≤ c + 2 + c * ((i + 1 : ℕ) : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_right hm hH
    have hci : 0 ≤ c * (i : ℝ) := by positivity
    push_cast at h ⊢
    nlinarith
  · -- the falling part
    rw [tent_of_ge (by omega : m ≤ i), tent_of_ge (by omega : m ≤ i + 1),
      tent_of_ge (by omega : m ≤ i + 2)]
    have hnat : 2 * (2 * m - (i + 1)) ≤ (2 * m - i) + (2 * m - (i + 2)) := by omega
    have hcast : (2 : ℝ) * ((2 * m - (i + 1) : ℕ) : ℝ)
        ≤ ((2 * m - i : ℕ) : ℝ) + ((2 * m - (i + 2) : ℕ) : ℝ) := by exact_mod_cast hnat
    have hH : 0 ≤ c + 2 + c * (m : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left hcast hH
    have h' : 0 ≤ δ * ((c + 2 + c * (m : ℝ)) * ((2 * m - (i + 1) : ℕ) : ℝ)) := by positivity
    linarith

/-- The tent grows by a factor of at most `1 / t` per step. -/
theorem mul_tent_succ_le {c t : ℝ} (hc : 0 ≤ c) (ht1 : t ≤ 1)
    (ht : 2 * (t * (c + 1)) ≤ c + 2) (m i : ℕ) : t * tent c m (i + 1) ≤ tent c m i := by
  rcases Nat.lt_or_ge i m with h | h
  · rw [tent_of_le h.le, tent_of_le (by omega : i + 1 ≤ m)]
    have h1 : t * (c + 2 + c * ((i + 1 : ℕ) : ℝ)) ≤ c + 2 + c * (i : ℝ) := by
      have := mul_nonneg (mul_nonneg hc (Nat.cast_nonneg i)) (sub_nonneg.mpr ht1)
      push_cast
      nlinarith
    calc t * ((m : ℝ) * (c + 2 + c * ((i + 1 : ℕ) : ℝ)))
        = (m : ℝ) * (t * (c + 2 + c * ((i + 1 : ℕ) : ℝ))) := by ring
      _ ≤ (m : ℝ) * (c + 2 + c * (i : ℝ)) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg m)
  · rw [tent_of_ge h, tent_of_ge (by omega : m ≤ i + 1)]
    have hnat : 2 * m - (i + 1) ≤ 2 * m - i := by omega
    have hcast : ((2 * m - (i + 1) : ℕ) : ℝ) ≤ ((2 * m - i : ℕ) : ℝ) := by exact_mod_cast hnat
    have hH : 0 ≤ c + 2 + c * (m : ℝ) := by positivity
    have hb : 0 ≤ ((2 * m - (i + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    calc t * ((c + 2 + c * (m : ℝ)) * ((2 * m - (i + 1) : ℕ) : ℝ))
        ≤ 1 * ((c + 2 + c * (m : ℝ)) * ((2 * m - (i + 1) : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right ht1 (mul_nonneg hH hb)
      _ = (c + 2 + c * (m : ℝ)) * ((2 * m - (i + 1) : ℕ) : ℝ) := one_mul _
      _ ≤ (c + 2 + c * (m : ℝ)) * ((2 * m - i : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hcast hH

/-- **The profile.** For every degree `d` and every `ε > 0` there is a finitely supported,
nonnegative, nonincreasing profile that is a subsolution of the radial eigenvalue equation of
the `d`-regular tree with eigenvalue `2√(d − 1) − ε`. -/
theorem exists_profile (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (K : ℕ) (g : ℕ → ℝ), Antitone g ∧ (∀ i, 0 ≤ g i) ∧ 0 < g 0 ∧ (∀ i, K ≤ i → g i = 0) ∧
      (2 * Real.sqrt (d - 1) - ε) * g 0 ≤ d * g 1 ∧
      ∀ i, (2 * Real.sqrt (d - 1) - ε) * g (i + 1) ≤ g i + ((d : ℝ) - 1) * g (i + 2) := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · -- `d ≤ 1`: the eigenvalue is negative and the indicator of the centre works
    have hs : Real.sqrt ((d : ℝ) - 1) = 0 := Real.sqrt_eq_zero_of_nonpos (by
      have : (d : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hd
      linarith)
    refine ⟨1, fun i => if i = 0 then 1 else 0, antitone_nat_of_succ_le fun n => ?_,
      fun i => ?_, ?_, fun i hi => ?_, ?_, fun i => ?_⟩ <;> beta_reduce
    · rw [if_neg (Nat.succ_ne_zero n)]
      split_ifs <;> norm_num
    · split_ifs <;> norm_num
    · simp
    · rw [if_neg (by omega)]
    · simp [hs, hε.le]
    · rw [if_neg (Nat.succ_ne_zero i), if_neg (Nat.succ_ne_zero (i + 1)), mul_zero, mul_zero,
        add_zero]
      split_ifs <;> norm_num
  · -- `d ≥ 2`: the tent, damped by `(d - 1) ^ (-i / 2)`
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    set s : ℝ := Real.sqrt ((d : ℝ) - 1) with hs_def
    have hs2 : s ^ 2 = (d : ℝ) - 1 := Real.sq_sqrt (by linarith)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs1 : 1 ≤ s := by
      by_contra h
      have h' := not_le.mp h
      nlinarith
    obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = s⁻¹ := ⟨_, rfl⟩
    have hst : s * t = 1 := by rw [ht_def]; exact mul_inv_cancel₀ (by linarith)
    have ht0 : 0 < t := by rw [ht_def]; exact inv_pos.mpr (by linarith)
    have ht1 : t ≤ 1 := by nlinarith
    obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = (d : ℝ) - 2 := ⟨_, rfl⟩
    have hc : 0 ≤ c := by linarith
    have hcs : c + 1 = s ^ 2 := by linarith
    have hts : t * (c + 1) = s := by rw [hcs]; linear_combination s * hst
    have hct2 : (c + 1) * t ^ 2 = 1 := by rw [hcs]; linear_combination (s * t + 1) * hst
    obtain ⟨m₀, hm₀⟩ := exists_nat_ge (2 / (ε * t))
    obtain ⟨m, hm_def⟩ : ∃ m : ℕ, m = m₀ + 1 := ⟨_, rfl⟩
    have hεt : 0 < ε * t := mul_pos hε ht0
    have hm : 2 ≤ ε * t * (m : ℝ) := by
      have h1 : 2 ≤ ε * t * (m₀ : ℝ) := by
        have := (div_le_iff₀ hεt).mp hm₀
        linarith
      have h2 : (m₀ : ℝ) ≤ m := by rw [hm_def]; push_cast; linarith
      nlinarith
    have hm1 : 1 ≤ m := by omega
    have key := fun i => tent_add_tent (m := m) hc hεt.le hm i
    have hmono := mul_tent_succ_le hc ht1 (by rw [hts]; nlinarith [sq_nonneg (s - 1)]) m
    refine ⟨2 * m, fun i => t ^ i * tent c m i, antitone_nat_of_succ_le fun n => ?_,
      fun i => mul_nonneg (pow_nonneg ht0.le i) (tent_nonneg hc m i), ?_, fun i hi => ?_, ?_,
      fun i => ?_⟩
    · -- antitone
      show t ^ (n + 1) * tent c m (n + 1) ≤ t ^ n * tent c m n
      calc t ^ (n + 1) * tent c m (n + 1) = t ^ n * (t * tent c m (n + 1)) := by ring
        _ ≤ t ^ n * tent c m n := mul_le_mul_of_nonneg_left (hmono n) (pow_nonneg ht0.le n)
    · -- positive at the centre
      show 0 < t ^ 0 * tent c m 0
      rw [pow_zero, one_mul, tent_of_le (Nat.zero_le m)]
      have : (0 : ℝ) < m := by exact_mod_cast hm1
      positivity
    · -- finitely supported
      show t ^ i * tent c m i = 0
      rw [tent_of_ge (by omega : m ≤ i), Nat.sub_eq_zero_of_le hi]
      simp
    · -- the equation at the centre
      show (2 * s - ε) * (t ^ 0 * tent c m 0) ≤ d * (t ^ 1 * tent c m 1)
      rw [tent_of_le (Nat.zero_le m), tent_of_le hm1]
      have hdc : (d : ℝ) = c + 2 := by linarith
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have e : (d : ℝ) * (t ^ 1 * ((m : ℝ) * (c + 2 + c * ((1 : ℕ) : ℝ))))
          = 2 * s * ((m : ℝ) * (c + 2)) := by
        rw [hdc, ← hts]; push_cast; ring
      rw [e]
      have : 0 ≤ ε * ((m : ℝ) * (c + 2)) := by positivity
      push_cast
      nlinarith
    · -- the equation away from the centre
      show (2 * s - ε) * (t ^ (i + 1) * tent c m (i + 1))
        ≤ t ^ i * tent c m i + ((d : ℝ) - 1) * (t ^ (i + 2) * tent c m (i + 2))
      have hd1 : (d : ℝ) - 1 = c + 1 := by linarith
      have e1 : (2 * s - ε) * (t ^ (i + 1) * tent c m (i + 1))
          = t ^ i * (2 * tent c m (i + 1) - ε * t * tent c m (i + 1)) := by
        rw [pow_succ]; linear_combination (2 * t ^ i * tent c m (i + 1)) * hst
      have e2 : t ^ i * tent c m i + ((d : ℝ) - 1) * (t ^ (i + 2) * tent c m (i + 2))
          = t ^ i * (tent c m i + tent c m (i + 2)) := by
        rw [hd1, pow_add]; linear_combination (t ^ i * tent c m (i + 2)) * hct2
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left (key i) (pow_nonneg ht0.le i)

end Profile

end AlonBoppana

/-- **Alon–Boppana bound.** For every degree `d` and every `ε > 0`, all sufficiently large
`d`-regular graphs have `λ₂ ≥ 2√(d − 1) − ε`. So no infinite family of `d`-regular graphs has
spectral gap bounded above `d − 2√(d − 1)`.

The proof (after Nilli) builds a test function supported on two far-apart balls and feeds it to
the variational bound `SimpleGraph.dotProduct_adjMatrix_mulVec_le`; see the module docstring.
Any `N > (d + 1) ^ (2K)` works, where `K` is the radius of the profile from
`SimpleGraph.AlonBoppana.exists_profile`. -/
theorem alon_boppana (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree d → N ≤ Fintype.card V →
        2 * Real.sqrt (d - 1) - ε ≤ G.secondAdjEigenvalue := by
  obtain ⟨K, g, hanti, hnn, hpos, hK, h0, hstep⟩ := AlonBoppana.exists_profile d hε
  refine ⟨(d + 1) ^ (2 * K) + 1, fun V _ _ _ G _ hd hN => ?_⟩
  obtain ⟨v₀⟩ : Nonempty V := inferInstance
  obtain ⟨v₁, hfar⟩ := AlonBoppana.exists_lt_edist hd v₀ (r := 2 * K) (by omega)
  exact AlonBoppana.le_secondAdjEigenvalue_of_lt_edist hd hanti hnn hpos hK h0 hstep hfar

end SimpleGraph
