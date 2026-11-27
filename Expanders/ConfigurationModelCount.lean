/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.ConfigurationModel

/-!
# Counting pairings in the configuration model

A pairing of the `n * d` points of the configuration model is a fixed-point-free involution of
`Fin n × Fin d`. This file counts them: there are `(2m − 1)‼` fixed-point-free involutions of a
type with `2m` elements, and none of a type with an odd number of elements.

## Main results
* `ConfigurationModel.card_fixedPointFree_involutions`: a type with `2m` elements has exactly
  `(2m − 1)‼` fixed-point-free involutions (including `m = 0`, where the count is `0‼ = 1`).
* `ConfigurationModel.card_fixedPointFree_involutions_of_odd`: a type with an odd number of
  elements has none.
* `ConfigurationModel.card_pairings`, `ConfigurationModel.card_pairings_of_odd`: the same counts
  for `ConfigurationModel.pairings n d`.

## Proof
A permutation of a type with `2m` elements is a fixed-point-free involution exactly when its
cycle type is `m` copies of `2`. Mathlib counts permutations of a given cycle type
(`Equiv.Perm.card_of_cycleType_mul_eq`), giving `(2m)! / (2ᵐ m!)`, and
`(2m)! = (2m − 1)‼ · (2m)‼ = (2m − 1)‼ · 2ᵐ m!`.
-/

open Finset
open scoped Nat

namespace ConfigurationModel

/-- A permutation of a type with `2m` elements is a fixed-point-free involution exactly when its
cycle type consists of `m` two-cycles. -/
theorem fixedPointFree_involution_iff_cycleType {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (h : Fintype.card α = 2 * m) (π : Equiv.Perm α) :
    ((∀ a, π (π a) = a) ∧ ∀ a, π a ≠ a) ↔ π.cycleType = Multiset.replicate m 2 := by
  constructor
  · rintro ⟨hinv, hfix⟩
    have hsq : π ^ 2 = 1 := Equiv.ext fun a => by simp [sq, hinv]
    have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one hsq
    have hsupp : π.support = univ :=
      eq_univ_of_forall fun a => Equiv.Perm.mem_support.mpr (hfix a)
    have hsum := π.sum_cycleType
    rw [hsupp, card_univ, h, hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
    rw [hrep, show Multiset.card π.cycleType = m by lia]
  · intro hc
    have hsq : π ^ 2 = 1 :=
      Equiv.Perm.pow_prime_eq_one_iff.mpr fun c hc' => by
        rw [hc] at hc'
        exact Multiset.eq_of_mem_replicate hc'
    have hsum := π.sum_cycleType
    rw [hc, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hsupp : π.support = univ := eq_univ_of_card _ (by rw [← hsum, h, mul_comm])
    refine ⟨fun a => ?_, fun a => ?_⟩
    · have := congrArg (· a) hsq
      simpa [sq] using this
    · exact Equiv.Perm.mem_support.mp (hsupp ▸ mem_univ a)

/-- `(2m)! = (2m − 1)‼ · 2ᵐ · m!`, including `m = 0` with truncated subtraction. -/
theorem factorial_two_mul_eq (m : ℕ) : (2 * m)! = (2 * m - 1)‼ * (2 ^ m * m !) := by
  rcases m with _ | m
  · rfl
  · rw [← Nat.doubleFactorial_two_mul,
      show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.factorial_eq_mul_doubleFactorial,
      Nat.add_sub_cancel, mul_comm]

/-- The number of fixed-point-free involutions of a type with `2m` elements is `(2m − 1)‼`. -/
theorem card_fixedPointFree_involutions {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (h : Fintype.card α = 2 * m) :
    #{π : Equiv.Perm α | (∀ a, π (π a) = a) ∧ ∀ a, π a ≠ a} = (2 * m - 1)‼ := by
  rw [filter_congr fun π _ => fixedPointFree_involution_iff_cycleType h π]
  have key := Equiv.Perm.card_of_cycleType_mul_eq α (Multiset.replicate m 2)
  have hprod : ∏ n ∈ (Multiset.replicate m 2).toFinset,
      (Multiset.count n (Multiset.replicate m 2))! = m ! := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Multiset.toFinset_replicate, if_neg hm.ne', prod_singleton,
        Multiset.count_replicate_self]
  rw [hprod, Multiset.sum_replicate, Multiset.prod_replicate, smul_eq_mul, h,
    if_pos ⟨by rw [mul_comm], fun a ha => (Multiset.eq_of_mem_replicate ha).ge⟩,
    show 2 * m - m * 2 = 0 by lia, Nat.factorial_zero, one_mul, factorial_two_mul_eq] at key
  exact Nat.eq_of_mul_eq_mul_right (by positivity) key

/-- A type with an odd number of elements has no fixed-point-free involution. -/
theorem card_fixedPointFree_involutions_of_odd {α : Type*} [Fintype α] [DecidableEq α]
    (h : Odd (Fintype.card α)) :
    #{π : Equiv.Perm α | (∀ a, π (π a) = a) ∧ ∀ a, π a ≠ a} = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro π - ⟨hinv, hfix⟩
  have hsq : π ^ 2 = 1 := Equiv.ext fun a => by simp [sq, hinv]
  have hsupp : π.support = univ :=
    eq_univ_of_forall fun a => Equiv.Perm.mem_support.mpr (hfix a)
  have h2 := Equiv.Perm.two_dvd_card_support hsq
  rw [hsupp, card_univ] at h2
  exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)

/-- The number of pairings in the configuration model is `(nd − 1)‼` when `nd` is even. -/
theorem card_pairings {n d m : ℕ} (h : n * d = 2 * m) : #(pairings n d) = (2 * m - 1)‼ := by
  have hcard : Fintype.card (Fin n × Fin d) = 2 * m := by simp [h]
  rw [← card_fixedPointFree_involutions hcard]
  rfl

/-- There are no pairings in the configuration model when `nd` is odd. -/
theorem card_pairings_of_odd {n d : ℕ} (h : Odd (n * d)) : #(pairings n d) = 0 := by
  have hcard : Odd (Fintype.card (Fin n × Fin d)) := by simpa using h
  rw [← card_fixedPointFree_involutions_of_odd hcard]
  rfl

end ConfigurationModel
