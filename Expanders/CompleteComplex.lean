/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.TricklingDown

/-!
# The complete complex: trickling down on a worked example

The complete `d`-dimensional complex on `ι` has as faces all nonempty sets of at most `d + 1`
points. We check that "all triangles on five points", `complete (Fin 5) 2`, meets every hypothesis
of `PreAbstractSimplicialComplex.trickling_down`, and apply that theorem to it.

## Definitions
* `PreAbstractSimplicialComplex.complete`: the complete `d`-dimensional complex on `ι`.

## Theorems
* `topDegree_eq_one`: a top face lies in exactly one top face, itself. **Proved.**
* `isPure_complete`, `isConnected_link_complete`: the complete complex on at least `d + 1` points
  is pure, and the link of a set of dimension at most `d − 2` is connected. **Proved.**
* `walkSecondEigenvalueLE_complete_fin5_two_link_singleton`: every vertex link of
  `complete (Fin 5) 2` is the complete graph `K₄`, with second eigenvalue `−1/3`. **Proved.**
* `complete_fin5_two_walkSecondEigenvalueLE`: trickling down bounds the second eigenvalue of the
  underlying graph of `complete (Fin 5) 2` by `−1/4`. **Proved.**
* `not_complete_fin5_two_walkSecondEigenvalueLE`: that bound is sharp. **Proved.**
* `isLocalSpectralExpander_complete_fin5_two`: `complete (Fin 5) 2` is a `(−1/4)`-local-spectral
  expander, so that definition is satisfiable. **Proved.**
-/

open Finset

namespace PreAbstractSimplicialComplex

/-- The complete `d`-dimensional complex on `ι`: every nonempty set of at most `d + 1` points is
a face. -/
def complete (ι : Type*) (d : ℕ) : PreAbstractSimplicialComplex ι where
  faces := {s | s.Nonempty ∧ #s ≤ d + 1}
  isRelLowerSet_faces := by
    rintro s ⟨hne, hcard⟩
    exact ⟨hne, fun t hts ht => ⟨ht, (card_le_card hts).trans hcard⟩⟩

theorem mem_complete {ι : Type*} {d : ℕ} {s : Finset ι} :
    s ∈ complete ι d ↔ s.Nonempty ∧ #s ≤ d + 1 := Iff.rfl

variable {ι : Type*} [DecidableEq ι]

/-! ### General facts -/

/-- A top face lies in exactly one top face, itself. -/
theorem topDegree_eq_one [Fintype ι] (K : PreAbstractSimplicialComplex ι) {d : ℕ}
    {s : Finset ι} (hs : s ∈ K) (hcard : #s = d + 1) : K.topDegree d s = 1 := by
  unfold topDegree
  rw [card_eq_one]
  refine ⟨s, ext fun F => ?_⟩
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨-, hF, hsF⟩
    exact (eq_of_subset_of_card_le hsF (by omega)).symm
  · rintro rfl
    exact ⟨hs, hcard, subset_rfl⟩

omit [DecidableEq ι] in
/-- The complete `d`-dimensional complex on at least `d + 1` points is pure of dimension `d`. -/
theorem isPure_complete [Fintype ι] {d : ℕ} (h : d + 1 ≤ Fintype.card ι) :
    (complete ι d).IsPure d := by
  rintro σ ⟨-, hσ⟩
  obtain ⟨τ, hστ, -, hτ⟩ :=
    exists_subsuperset_card_eq (subset_univ σ) hσ (by rwa [card_univ])
  exact ⟨hσ, τ, ⟨card_pos.mp (by omega), by omega⟩, hστ, hτ⟩

/-- In the complete `d`-dimensional complex, the link of a set `σ` of dimension at most `d − 2`
is connected as soon as some point lies outside `σ`: its vertices are the points outside `σ`, and
any two of them span an edge. -/
theorem isConnected_link_complete {d : ℕ} {σ : Finset ι} (hcard : #σ + 1 ≤ d) {x : ι}
    (hx : x ∉ σ) : ((complete ι d).link σ).IsConnected := by
  have hvert : ∀ u, u ∈ ((complete ι d).link σ).vertices ↔ u ∉ σ := by
    intro u
    change {u} ∈ (complete ι d).link σ ↔ _
    rw [mem_link, mem_complete]
    constructor
    · rintro ⟨-, hdisj, -⟩
      exact disjoint_singleton_left.mp hdisj
    · intro hu
      refine ⟨singleton_nonempty u, disjoint_singleton_left.mpr hu,
        (singleton_nonempty u).mono subset_union_left, ?_⟩
      calc #({u} ∪ σ) ≤ #{u} + #σ := card_union_le _ _
        _ ≤ d + 1 := by rw [card_singleton]; omega
  rw [IsConnected, SimpleGraph.connected_iff]
  refine ⟨fun a b => ?_, ⟨⟨x, (hvert x).mpr hx⟩⟩⟩
  by_cases hab : a = b
  · rw [hab]
  refine SimpleGraph.Adj.reachable ?_
  rw [SimpleGraph.induce_adj, oneSkeleton, SimpleGraph.fromRel_adj]
  refine ⟨fun h => hab (Subtype.ext h), Or.inl ?_⟩
  have ha := (hvert a).mp a.2
  have hb := (hvert b).mp b.2
  refine mem_link.mpr ⟨insert_nonempty _ _, ?_, mem_complete.mpr ⟨?_, ?_⟩⟩
  · exact disjoint_insert_left.mpr ⟨ha, disjoint_singleton_left.mpr hb⟩
  · exact (insert_nonempty _ _).mono subset_union_left
  · calc #({(a : ι), (b : ι)} ∪ σ) ≤ #({(a : ι), (b : ι)} : Finset ι) + #σ := card_union_le _ _
      _ ≤ d + 1 := by have := card_le_two (a := (a : ι)) (b := (b : ι)); omega

/-! ### All triangles on five points -/

/-- All triangles on five points form a pure `2`-dimensional complex. -/
theorem isPure_complete_fin5_two : (complete (Fin 5) 2).IsPure 2 :=
  isPure_complete (by simp)

/-- **Connectivity of all triangles on five points.** The link of every set of dimension at most
`0` is connected: this covers the complex itself (`σ = ∅`) and every vertex link (`σ = {z}`). -/
theorem isConnected_complete_fin5_two_link (σ : Finset (Fin 5)) (hσ : #σ + 1 ≤ 2) :
    ((complete (Fin 5) 2).link σ).IsConnected := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ σ := by
    by_contra h
    simp only [not_exists, not_not] at h
    rw [eq_univ_of_forall h, card_univ, Fintype.card_fin] at hσ
    omega
  exact isConnected_link_complete hσ hx

/-- In all triangles on five points, the weighted graph of the link of a vertex `z` is the
complete graph on the other four points, every edge with weight `1`: the only triangle through
`{u, v, z}` is itself. -/
theorem linkWeight_complete_fin5_two_singleton (z u v : Fin 5) :
    (complete (Fin 5) 2).linkWeight 2 {z} u v = if u ≠ v ∧ u ≠ z ∧ v ≠ z then 1 else 0 := by
  by_cases h : u ≠ v ∧ u ≠ z ∧ v ≠ z
  · rw [if_pos h, linkWeight, if_pos (by simpa using h)]
    obtain ⟨huv, huz, hvz⟩ := h
    have hcard : #(insert u (insert v {z}) : Finset (Fin 5)) = 3 :=
      card_eq_three.mpr ⟨u, v, z, huv, huz, hvz, rfl⟩
    rw [topDegree_eq_one _ (mem_complete.mpr ⟨insert_nonempty _ _, hcard.le⟩) hcard, Nat.cast_one]
  · rw [if_neg h, linkWeight, if_neg (by simpa using h)]

/-- **The vertex links are `K₄`.** In all triangles on five points, the random walk on the link
of any vertex `z` (the complete graph on the other four points) has second eigenvalue at most
`−1/3`.

On paper: every `u ≠ z` has degree `3`, so the condition is `Σ_{u ≠ z} f(u) = 0`, and then
`Σ_{u ≠ v, both ≠ z} f(u) f(v) = (Σ_{u ≠ z} f(u))² − Σ_{u ≠ z} f(u)² = −Σ_{u ≠ z} f(u)²`, which
is `(−1/3) · Σ_{u ≠ z} 3 f(u)²`. -/
theorem walkSecondEigenvalueLE_complete_fin5_two_link_singleton (z : Fin 5) :
    WalkSecondEigenvalueLE ((complete (Fin 5) 2).linkWeight 2 {z}) (-1 / 3) := by
  intro f hf
  simp only [linkWeight_complete_fin5_two_singleton] at hf ⊢
  fin_cases z <;> simp only [Fin.sum_univ_five] at hf ⊢ <;> simp +decide at hf ⊢
  all_goals nlinarith [hf]

/-- The bound produced by `trickling_down` for all triangles on five points, with `d = 2`,
`σ = ∅` and `lam = −1/3`: `(−1/3) / (1 − (2 − 1 − 0) · (−1/3)) = (−1/3) / (4/3) = −1/4`. -/
theorem trickling_down_bound_complete_fin5_two :
    (-1 / 3 : ℝ) / (1 - (((2 : ℕ) : ℝ) - 1 - (#(∅ : Finset (Fin 5)) : ℝ)) * (-1 / 3)) =
      -1 / 4 := by
  rw [card_empty]
  norm_num

/-- **Trickling down on all triangles on five points.** Each vertex link is the complete graph
`K₄`, whose random walk has second eigenvalue `−1/3`; trickling down then bounds the second
eigenvalue of the whole underlying graph by `(−1/3) / (1 + 1/3) = −1/4`. -/
theorem complete_fin5_two_walkSecondEigenvalueLE :
    WalkSecondEigenvalueLE ((complete (Fin 5) 2).linkWeight 2 ∅) (-1 / 4) := by
  have h := (complete (Fin 5) 2).trickling_down le_rfl isPure_complete_fin5_two
    (fun σ _ hσ => isConnected_complete_fin5_two_link σ hσ) (lam := -1 / 3) (by norm_num)
    (fun σ _ hσ => by
      obtain ⟨z, rfl⟩ := card_eq_one.mp (by omega : #σ = 1)
      exact walkSecondEigenvalueLE_complete_fin5_two_link_singleton z)
    ∅ (Or.inl rfl) (by simp)
  rwa [trickling_down_bound_complete_fin5_two] at h

/-- **All triangles on five points form a local spectral expander**, with `lam = −1/4`: the
complex is pure and has a face, its underlying graph has second eigenvalue at most `−1/4`
(`complete_fin5_two_walkSecondEigenvalueLE`), and every vertex link has second eigenvalue at most
`−1/3 ≤ −1/4`. So `IsLocalSpectralExpander` is satisfiable, here with a negative `lam`. -/
theorem isLocalSpectralExpander_complete_fin5_two :
    (complete (Fin 5) 2).IsLocalSpectralExpander 2 (-1 / 4) := by
  refine ⟨isPure_complete_fin5_two, ⟨{0}, mem_complete.mpr ⟨singleton_nonempty 0, by simp⟩⟩,
    fun σ hσ hcard => ?_⟩
  rcases hσ with rfl | hσ
  · exact complete_fin5_two_walkSecondEigenvalueLE
  · have hpos : 0 < #σ := card_pos.mpr (mem_complete.mp hσ).1
    obtain ⟨z, rfl⟩ := card_eq_one.mp (by omega : #σ = 1)
    exact (walkSecondEigenvalueLE_complete_fin5_two_link_singleton z).mono
      (linkWeight_nonneg _ 2 {z}) (by norm_num)

/-! ### Sharpness -/

/-- In all triangles on five points, every edge `{u, v}` lies in exactly three triangles: by
double counting (`sum_topDegree_insert`), one through each of the three remaining points. -/
theorem topDegree_complete_fin5_two_pair {u v : Fin 5} (huv : u ≠ v) :
    (complete (Fin 5) 2).topDegree 2 {u, v} = 3 := by
  have h := (complete (Fin 5) 2).sum_topDegree_insert 2 {u, v}
  have h1 : ∀ w ∈ ({u, v} : Finset (Fin 5))ᶜ,
      (complete (Fin 5) 2).topDegree 2 (insert w {u, v}) = 1 := by
    intro w hw
    simp only [mem_compl, mem_insert, mem_singleton, not_or] at hw
    have hcard : #(insert w {u, v} : Finset (Fin 5)) = 3 :=
      card_eq_three.mpr ⟨w, u, v, hw.1, hw.2, huv, rfl⟩
    exact topDegree_eq_one _ (mem_complete.mpr ⟨insert_nonempty _ _, hcard.le⟩) hcard
  rw [sum_congr rfl h1, sum_const, smul_eq_mul, mul_one, card_compl, Fintype.card_fin,
    card_pair huv] at h
  omega

/-- The weighted underlying graph of all triangles on five points is the complete graph `K₅`,
every edge with weight `3`. -/
theorem linkWeight_complete_fin5_two_empty (u v : Fin 5) :
    (complete (Fin 5) 2).linkWeight 2 ∅ u v = if u ≠ v then 3 else 0 := by
  by_cases h : u ≠ v
  · rw [if_pos h, linkWeight, if_pos ⟨h, notMem_empty u, notMem_empty v⟩, insert_empty,
      topDegree_complete_fin5_two_pair h, Nat.cast_ofNat]
  · rw [if_neg h, linkWeight, if_neg fun h' => h h'.1]

/-- **The bound `−1/4` is sharp.** The underlying graph of all triangles on five points is `K₅`
with every edge of weight `3`, whose random walk has second eigenvalue exactly `−1/4`: the test
function `f = (1, −1, 0, 0, 0)` has `Σ_{u,v} w(u,v) f(u) f(v) = −6` and
`Σ_u deg(u) f(u)² = 24`, so no bound below `−1/4` holds. -/
theorem not_complete_fin5_two_walkSecondEigenvalueLE {μ : ℝ} (hμ : μ < -1 / 4) :
    ¬ WalkSecondEigenvalueLE ((complete (Fin 5) 2).linkWeight 2 ∅) μ := by
  intro h
  have h1 := h ![1, -1, 0, 0, 0] (by
    simp only [linkWeight_complete_fin5_two_empty, Fin.sum_univ_five]
    simp +decide)
  simp only [linkWeight_complete_fin5_two_empty, Fin.sum_univ_five] at h1
  simp +decide at h1
  linarith

end PreAbstractSimplicialComplex
