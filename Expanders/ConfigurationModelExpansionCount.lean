/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.ConfigurationModelCount

/-!
# A first-moment bound using closed sets of points

Remove from a vertex set the points paired outside it. The remaining points form an invariant
set of the pairing. Counting all pairings preserving that set gives an upper bound without
having to encode the crossing edges. Odd-sized invariant sets contribute zero.
-/

open Finset
open scoped Nat

namespace ConfigurationModel

universe u

/-- Number of pairings of `N` labelled points, including zero for odd `N`. -/
def pairingCount (N : ℕ) : ℕ := if Even N then (N - 1)‼ else 0

/-- The existing even/odd counts combined into a single formula. -/
theorem card_fixedPointFree_involutions_eq_pairingCount {α : Type*}
    [Fintype α] [DecidableEq α] :
    #{π : Equiv.Perm α | (∀ a, π (π a) = a) ∧ ∀ a, π a ≠ a} =
      pairingCount (Fintype.card α) := by
  by_cases h : Even (Fintype.card α)
  · obtain ⟨m, hm⟩ := h
    have hm' : Fintype.card α = 2 * m := by omega
    rw [card_fixedPointFree_involutions hm', pairingCount, if_pos ⟨m, hm⟩, hm']
  · rw [card_fixedPointFree_involutions_of_odd (Nat.not_even_iff_odd.mp h),
      pairingCount, if_neg h]

/-- Restricting a fixed-point-free involution to an invariant predicate preserves both
properties. -/
private theorem restriction_pairing {α : Type*} {π : Equiv.Perm α}
    (hπ : (∀ a, π (π a) = a) ∧ ∀ a, π a ≠ a) {p : α → Prop}
    (hp : ∀ a, p a ↔ p (π a)) :
    (∀ a, π.subtypeEquiv hp (π.subtypeEquiv hp a) = a) ∧
      ∀ a, π.subtypeEquiv hp a ≠ a := by
  exact ⟨fun a => Subtype.ext (hπ.1 a),
    fun a ha => hπ.2 a (congrArg Subtype.val ha)⟩

/-- A pairing preserving a point set is determined by its restrictions to that set and its
complement. This injection suffices for the first-moment bound. -/
theorem card_preserving_le {α : Type u} [Fintype α] [DecidableEq α] (T : Finset α) :
    #{π : Equiv.Perm α | ((∀ a, π (π a) = a) ∧ ∀ a, π a ≠ a) ∧
      ∀ a, a ∈ T ↔ π a ∈ T} ≤
        pairingCount #T * pairingCount (Fintype.card α - #T) := by
  classical
  let P (β : Type u) [Fintype β] :=
    {π : Equiv.Perm β // (∀ a, π (π a) = a) ∧ ∀ a, π a ≠ a}
  let C := {π : Equiv.Perm α // ((∀ a, π (π a) = a) ∧ ∀ a, π a ≠ a) ∧
    ∀ a, a ∈ T ↔ π a ∈ T}
  let f : C → P {a // a ∈ T} × P {a // a ∉ T} := fun π =>
    (⟨π.val.subtypeEquiv π.property.2, restriction_pairing π.property.1 π.property.2⟩,
      ⟨π.val.subtypeEquiv (fun a => not_congr (π.property.2 a)),
        restriction_pairing π.property.1 (fun a => not_congr (π.property.2 a))⟩)
  have hf : Function.Injective f := by
    intro π σ h
    apply Subtype.ext
    apply Equiv.ext
    intro a
    by_cases ha : a ∈ T
    · exact congrArg (fun q : P {a // a ∈ T} × P {a // a ∉ T} =>
        ((q.1.val) ⟨a, ha⟩).val) h
    · exact congrArg (fun q : P {a // a ∈ T} × P {a // a ∉ T} =>
        ((q.2.val) ⟨a, ha⟩).val) h
  have h := Fintype.card_le_of_injective f hf
  have hneg : #{a : α | a ∉ T} = Fintype.card α - #T := by
    simpa only [Fintype.card_subtype, filter_mem_eq_inter, univ_inter] using
      Fintype.card_subtype_compl (fun a => a ∈ T)
  simpa only [C, P, Fintype.card_prod, Fintype.card_subtype,
    card_fixedPointFree_involutions_eq_pairingCount, filter_mem_eq_inter,
    univ_inter, hneg] using h

/-- All crossing points belong to the `d * #S` points above `S`. -/
theorem cross_le_degree_mul_card {n d : ℕ} (π : Equiv.Perm (Fin n × Fin d))
    (S : Finset (Fin n)) : cross π S ≤ d * #S := by
  have h : ({p : Fin n × Fin d | p.1 ∈ S ∧ (π p).1 ∉ S} : Finset _) ⊆
      S ×ˢ (univ : Finset (Fin d)) := by
    intro p hp
    exact mem_product.mpr ⟨(mem_filter.mp hp).2.1, mem_univ _⟩
  simpa [cross, card_product, mul_comm] using card_le_card h

/-- Deleting the crossing endpoints leaves an invariant set of exactly `d * #S - cross π S`
points above `S`. -/
theorem exists_preserved_subset {n d : ℕ} {π : Equiv.Perm (Fin n × Fin d)}
    (hπ : IsPairing π) (S : Finset (Fin n)) :
    ∃ T ∈ (S ×ˢ (univ : Finset (Fin d))).powersetCard (d * #S - cross π S),
      ∀ p, p ∈ T ↔ π p ∈ T := by
  let A := S ×ˢ (univ : Finset (Fin d))
  let T := A.filter (fun p => (π p).1 ∈ S)
  have hA : #A = d * #S := by simp [A, mul_comm]
  have hsplit : #T + cross π S = d * #S := by
    have h := card_filter_add_card_filter_not (s := A) (fun p : Fin n × Fin d => (π p).1 ∈ S)
    have heq : A.filter (fun p => (π p).1 ∉ S) =
        ({p : Fin n × Fin d | p.1 ∈ S ∧ (π p).1 ∉ S} : Finset _) := by
      ext p
      simp [A]
    rw [heq, hA] at h
    exact h
  refine ⟨T, mem_powersetCard.mpr ⟨filter_subset _ _, by omega⟩, ?_⟩
  intro p
  simp only [T, A, mem_filter, mem_product, mem_univ, and_true, hπ.1]
  exact and_comm

open Classical in
/-- A cut with `k` crossing points determines a preserved point subset. Counting possible
subsets and the pairings preserving each one gives this (intentionally inexact) bound. -/
theorem card_cross_eq_le {n d : ℕ} (S : Finset (Fin n)) {k : ℕ} (hk : k ≤ d * #S) :
    #{π ∈ pairings n d | cross π S = k} ≤
      (d * #S).choose k * pairingCount (d * #S - k) *
        pairingCount (n * d - (d * #S - k)) := by
  classical
  let A := S ×ˢ (univ : Finset (Fin d))
  let B := A.powersetCard (d * #S - k)
  let C (T : Finset (Fin n × Fin d)) :=
    {π ∈ pairings n d | ∀ p, p ∈ T ↔ π p ∈ T}
  have hcover : {π ∈ pairings n d | cross π S = k} ⊆ B.biUnion C := by
    intro π hπ
    obtain ⟨hp, hc⟩ := mem_filter.mp hπ
    obtain ⟨T, hT, hpres⟩ := exists_preserved_subset (mem_pairings.mp hp) S
    rw [hc] at hT
    exact mem_biUnion.mpr ⟨T, hT, mem_filter.mpr ⟨hp, hpres⟩⟩
  have hC (T : Finset (Fin n × Fin d)) (hT : T ∈ B) :
      #(C T) ≤ pairingCount (d * #S - k) * pairingCount (n * d - (d * #S - k)) := by
    have hc := (mem_powersetCard.mp hT).2
    have heq : C T = ({π : Equiv.Perm (Fin n × Fin d) |
        ((∀ a, π (π a) = a) ∧ ∀ a, π a ≠ a) ∧ ∀ a, a ∈ T ↔ π a ∈ T} : Finset _) := by
      ext π
      simp [C, IsPairing]
    rw [heq]
    simpa only [hc, Fintype.card_prod, Fintype.card_fin] using card_preserving_le T
  calc
    _ ≤ #(B.biUnion C) := card_le_card hcover
    _ ≤ ∑ T ∈ B, #(C T) := card_biUnion_le
    _ ≤ ∑ _T ∈ B, pairingCount (d * #S - k) *
        pairingCount (n * d - (d * #S - k)) := sum_le_sum hC
    _ = _ := by
      simp only [sum_const, smul_eq_mul, B, card_powersetCard, A, card_product,
        card_univ, Fintype.card_fin]
      rw [mul_comm #S d, Nat.choose_symm hk, mul_assoc]

open Classical in
/-- The closed-point-set first-moment numerator. The inner index is the number of crossing
points removed from the `d * s` points at the selected vertices. -/
noncomputable def closedCutBound (n d : ℕ) (ε : ℝ) : ℕ :=
  ∑ s ∈ Icc 1 (n / 2), n.choose s *
    ∑ k ∈ (range (d * s + 1)).filter (fun k : ℕ => (k : ℝ) < ε * s),
      (d * s).choose k * pairingCount (d * s - k) *
        pairingCount (n * d - (d * s - k))

open Classical in
/-- Sum the fixed-crossing-count bound over the allowed crossing counts for a fixed cut. -/
theorem card_sparseCut_le {n d : ℕ} (S : Finset (Fin n)) (ε : ℝ) :
    #{π ∈ pairings n d | (cross π S : ℝ) < ε * #S} ≤
      ∑ k ∈ (range (d * #S + 1)).filter (fun k : ℕ => (k : ℝ) < ε * #S),
        (d * #S).choose k * pairingCount (d * #S - k) *
          pairingCount (n * d - (d * #S - k)) := by
  classical
  let K := (range (d * #S + 1)).filter (fun k : ℕ => (k : ℝ) < ε * #S)
  have hmaps : (({π ∈ pairings n d | (cross π S : ℝ) < ε * #S} :
      Finset (Equiv.Perm (Fin n × Fin d))) : Set (Equiv.Perm (Fin n × Fin d))).MapsTo
      (fun π => cross π S) (K : Set ℕ) := by
    intro π hπ
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (cross_le_degree_mul_card π S)),
      (mem_filter.mp hπ).2⟩
  rw [card_eq_sum_card_fiberwise hmaps]
  apply sum_le_sum
  intro k hk
  calc
    _ ≤ #{π ∈ pairings n d | cross π S = k} := card_le_card (by
      intro π hπ
      obtain ⟨hp, he⟩ := mem_filter.mp hπ
      exact mem_filter.mpr ⟨(mem_filter.mp hp).1, he⟩)
    _ ≤ _ := card_cross_eq_le S (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hk).1))

/-- The first-moment inequality; no parity assumption on `n * d` is needed. -/
theorem card_badPairings_le_closedCutBound (n d : ℕ) (ε : ℝ) :
    #(badPairings n d ε) ≤ closedCutBound n d ε := by
  classical
  let C (S : Finset (Fin n)) := {π ∈ pairings n d | (cross π S : ℝ) < ε * #S}
  let U (s : ℕ) := ((univ : Finset (Fin n)).powersetCard s).biUnion C
  have hcover : badPairings n d ε ⊆ (Icc 1 (n / 2)).biUnion U := by
    intro π hπ
    obtain ⟨hp, S, hhalf, hcross⟩ := mem_badPairings.mp hπ
    have hspos : 1 ≤ #S := by
      by_contra h
      have hz : #S = 0 := by omega
      rw [hz, Nat.cast_zero, mul_zero] at hcross
      exact (Nat.cast_nonneg (cross π S)).not_gt hcross
    refine mem_biUnion.mpr ⟨#S, mem_Icc.mpr ⟨hspos, by omega⟩, ?_⟩
    exact mem_biUnion.mpr ⟨S, mem_powersetCard.mpr ⟨subset_univ _, rfl⟩,
      mem_filter.mpr ⟨mem_pairings.mpr hp, hcross⟩⟩
  calc
    _ ≤ #((Icc 1 (n / 2)).biUnion U) := card_le_card hcover
    _ ≤ ∑ s ∈ Icc 1 (n / 2), #(U s) := card_biUnion_le
    _ ≤ closedCutBound n d ε := by
      apply sum_le_sum
      intro s hs
      calc
        #(U s) ≤ ∑ S ∈ (univ : Finset (Fin n)).powersetCard s, #(C S) := card_biUnion_le
        _ ≤ ∑ _S ∈ (univ : Finset (Fin n)).powersetCard s,
            ∑ k ∈ (range (d * s + 1)).filter (fun k : ℕ => (k : ℝ) < ε * s),
              (d * s).choose k * pairingCount (d * s - k) *
                pairingCount (n * d - (d * s - k)) := by
          apply sum_le_sum
          intro S hS
          simpa only [C, (mem_powersetCard.mp hS).2] using card_sparseCut_le S ε
        _ = _ := by simp only [sum_const, smul_eq_mul, card_powersetCard,
          card_univ, Fintype.card_fin]

end ConfigurationModel
