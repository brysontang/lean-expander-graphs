/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.ConfigurationModelExpansionCount
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Binomial inequalities for the closed-set first moment

This file collects the purely numerical input to
`ConfigurationModel.closedCutTerm_le_geometric`. Write `M = pairingCount`, so
`M (2 * p) = (2 * p)! / (2 ^ p * p !)` and `M` vanishes on odd arguments.

## Pairing counts

* `pairingCount_mul_pairingCount_mul_choose`:
  `M (2 p) * M (2 q) * C (2 (p + q), 2 p) = M (2 (p + q)) * C (p + q, p)`.
* `pairingCount_sq_mul_choose_le`: for even `a ≤ N` with `N` even,
  `(M a * M (N - a)) ^ 2 * C (N, a) ≤ M N ^ 2`. This is the square-root-free form of
  `M a * M (N - a) / M N ≤ C (N, a) ^ (-1 / 2)`; it follows from the identity above and the
  Vandermonde bound `C (p + q, p) ^ 2 ≤ C (2 (p + q), 2 p)`.

## Binomial coefficients

* `choose_mul_choose_le_add_choose`: one term of Vandermonde's identity.
* `choose_pow_le`, `choose_pow_mul_choose_le`: super-multiplicativity,
  `C (n, s) ^ d ≤ C (n d, s d)` and `C (n, s) ^ d * C (n, j) ≤ C (n (d + 1), s d + j)`.
* `two_pow_le_choose`: `2 ^ j ≤ C (m, j)` when `2 j ≤ m`.
* `sq_mul_two_pow_le_choose`: `n ^ 2 * 2 ^ j ≤ 8 j ^ 2 * C (n, j)` when `2 ≤ j` and `2 j ≤ n`;
  this is where the factor `1 / n` in the final estimate comes from.

## The combined estimate

* `closedCutTerm_core`: for `d ≥ 3`, `2 s ≤ n`, `1000 k < s`, and `d ≥ 4` or `s ≥ 2`,
  `4 ^ (k + 1) * n ^ 2 * 16 ^ s * C (n, s) ^ 2 * C (d s, k) ^ 2 ≤
  10 ^ 4 * 9 ^ s * C (n d, d s - k)`.
  For `k = 0` it follows from `closedCutTerm_core_zero`, which only uses the two lower bounds
  for binomial coefficients above and `s ^ 2 * 8 ^ s ≤ 128 * 9 ^ s`. For `k ≥ 1` (so
  `s > 1000`) it follows from `closedCutTerm_core_pos`, where `C (d s, k) ≤ (d s) ^ k / k !` and
  `x ^ k / k ! ≤ exp x` with `x = s / 1000` show that the extra factors grow like `c ^ s` with
  `c` barely above `1`; the slack is collected in `closedCutTerm_exp_slack`.
* `closedCutSummand_le`: the resulting bound for one summand of the closed-set term,
  `C (n, s) * C (d s, k) * M (d s - k) * M (n d - (d s - k)) * (n * 4 ^ s * 2 ^ (k + 1)) ≤
  100 * 3 ^ s * M (n d)`, i.e. the summand divided by `M (n d)` is at most
  `(100 / n) * (3 / 4) ^ s / 2 ^ (k + 1)`.
-/

open Finset
open scoped Nat

namespace ConfigurationModel

/-! ### Vandermonde-type lower bounds -/

/-- One term of Vandermonde's identity. -/
theorem choose_mul_choose_le_add_choose (a b i j : ℕ) :
    a.choose i * b.choose j ≤ (a + b).choose (i + j) := by
  rw [Nat.add_choose_eq]
  exact single_le_sum (f := fun ij : ℕ × ℕ => a.choose ij.1 * b.choose ij.2)
    (fun _ _ => Nat.zero_le _) (show (i, j) ∈ antidiagonal (i + j) from mem_antidiagonal.mpr rfl)

/-- Binomial coefficients are super-multiplicative along multiples. -/
theorem choose_pow_le (n s d : ℕ) : n.choose s ^ d ≤ (n * d).choose (s * d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc n.choose s ^ (d + 1) = n.choose s ^ d * n.choose s := pow_succ _ _
      _ ≤ (n * d).choose (s * d) * n.choose s := Nat.mul_le_mul_right _ ih
      _ ≤ (n * d + n).choose (s * d + s) := choose_mul_choose_le_add_choose _ _ _ _
      _ = (n * (d + 1)).choose (s * (d + 1)) := by rw [Nat.mul_succ, Nat.mul_succ]

/-- Super-multiplicativity with one block of a different size. -/
theorem choose_pow_mul_choose_le (n s j d : ℕ) :
    n.choose s ^ d * n.choose j ≤ (n * (d + 1)).choose (s * d + j) := by
  calc n.choose s ^ d * n.choose j
      ≤ (n * d).choose (s * d) * n.choose j := Nat.mul_le_mul_right _ (choose_pow_le n s d)
    _ ≤ (n * d + n).choose (s * d + j) := choose_mul_choose_le_add_choose _ _ _ _
    _ = (n * (d + 1)).choose (s * d + j) := by rw [Nat.mul_succ]

/-- The square of a binomial coefficient is at most the doubled binomial coefficient. -/
theorem choose_sq_le (p q : ℕ) : (p + q).choose p ^ 2 ≤ (2 * (p + q)).choose (2 * p) := by
  have h := choose_mul_choose_le_add_choose (p + q) (p + q) p p
  rw [sq, two_mul, two_mul]
  exact h

/-- Below the middle, a binomial coefficient is at least a power of two. -/
theorem two_pow_le_choose : ∀ {j m : ℕ}, 2 * j ≤ m → 2 ^ j ≤ m.choose j
  | 0, m, _ => by simp
  | j + 1, m, h => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    have ih := two_pow_le_choose (j := j) (m := m) (by omega)
    have h1 : m.choose j ≤ (m + 1).choose j := Nat.choose_le_succ m j
    have h2 : m.choose j ≤ (m + 1).choose (j + 1) := by
      rw [Nat.choose_succ_succ']
      exact Nat.le_add_right _ _
    rw [Nat.choose_succ_succ' (m + 1) j, pow_succ]
    omega

/-- A binomial coefficient below the middle with lower index at least two is at least a
quadratic in the upper index times a power of two. -/
theorem sq_mul_two_pow_le_choose {n j : ℕ} (hj : 2 ≤ j) (hjn : 2 * j ≤ n) :
    n ^ 2 * 2 ^ j ≤ 8 * j ^ 2 * n.choose j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 := Nat.add_one_mul_choose_eq m i
  have h2 := Nat.add_one_mul_choose_eq (m + 1) (i + 1)
  have h3 : 2 ^ i ≤ m.choose i := two_pow_le_choose (by omega)
  have h4 : (m + 2) * (m + 1) * m.choose i = (i + 2) * (i + 1) * (m + 2).choose (i + 2) := by
    calc (m + 2) * (m + 1) * m.choose i = (m + 2) * ((m + 1) * m.choose i) := by ring
      _ = (m + 2) * ((m + 1).choose (i + 1) * (i + 1)) := by rw [h1]
      _ = ((m + 1 + 1) * (m + 1).choose (i + 1)) * (i + 1) := by ring
      _ = ((m + 1 + 1).choose (i + 1 + 1) * (i + 1 + 1)) * (i + 1) := by rw [h2]
      _ = (i + 2) * (i + 1) * (m + 2).choose (i + 2) := by ring
  have h5 : 4 * (m + 2) ^ 2 ≤ 8 * ((m + 2) * (m + 1)) := by nlinarith
  have h6 : 8 * ((i + 2) * (i + 1)) ≤ 8 * (i + 2) ^ 2 := by nlinarith
  calc (m + 2) ^ 2 * 2 ^ (i + 2) = 4 * (m + 2) ^ 2 * 2 ^ i := by ring
    _ ≤ 4 * (m + 2) ^ 2 * m.choose i := Nat.mul_le_mul_left _ h3
    _ ≤ 8 * ((m + 2) * (m + 1)) * m.choose i := Nat.mul_le_mul_right _ h5
    _ = 8 * ((i + 2) * (i + 1)) * (m + 2).choose (i + 2) := by
      rw [mul_assoc 8, h4]
      ring
    _ ≤ 8 * (i + 2) ^ 2 * (m + 2).choose (i + 2) := Nat.mul_le_mul_right _ h6

/-! ### Pairing counts -/

/-- The pairing count of an even number is positive. -/
theorem pairingCount_pos {N : ℕ} (hN : Even N) : 0 < pairingCount N := by
  rw [pairingCount, if_pos hN]
  exact Nat.doubleFactorial_pos _

/-- The factorial formula `(2 p - 1)‼ * (2 ^ p * p !) = (2 p)!`. -/
theorem pairingCount_two_mul (p : ℕ) : pairingCount (2 * p) * (2 ^ p * p !) = (2 * p)! := by
  rw [pairingCount, if_pos (even_two_mul p)]
  cases p with
  | zero => simp
  | succ p =>
    rw [← Nat.doubleFactorial_two_mul, show 2 * (p + 1) = 2 * p + 1 + 1 by ring,
      Nat.add_sub_cancel, Nat.factorial_eq_mul_doubleFactorial, mul_comm]

/-- Splitting a perfect matching count: the exact identity behind the closed-set estimate. -/
theorem pairingCount_mul_pairingCount_mul_choose (p q : ℕ) :
    pairingCount (2 * p) * pairingCount (2 * q) * (2 * (p + q)).choose (2 * p) =
      pairingCount (2 * (p + q)) * (p + q).choose p := by
  have hp := pairingCount_two_mul p
  have hq := pairingCount_two_mul q
  have hpq := pairingCount_two_mul (p + q)
  have hc : (2 * (p + q)).choose (2 * p) * (2 * p)! * (2 * q)! = (2 * (p + q))! := by
    have h := Nat.add_choose_mul_factorial_mul_factorial (2 * q) (2 * p)
    rw [show 2 * (p + q) = 2 * q + 2 * p by ring, ← h]
    ring
  have hc' : (p + q).choose p * q ! * p ! = (p + q)! := by
    have h := Nat.add_choose_mul_factorial_mul_factorial q p
    rw [add_comm p q]
    exact h
  have hpos : 0 < 2 ^ p * p ! * (2 ^ q * q !) := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc pairingCount (2 * p) * pairingCount (2 * q) * (2 * (p + q)).choose (2 * p) *
        (2 ^ p * p ! * (2 ^ q * q !))
      = (2 * (p + q)).choose (2 * p) * (pairingCount (2 * p) * (2 ^ p * p !)) *
          (pairingCount (2 * q) * (2 ^ q * q !)) := by ring
    _ = (2 * (p + q))! := by rw [hp, hq, hc]
    _ = pairingCount (2 * (p + q)) * (2 ^ (p + q) * (p + q)!) := hpq.symm
    _ = pairingCount (2 * (p + q)) * (p + q).choose p * (2 ^ p * p ! * (2 ^ q * q !)) := by
      rw [← hc']
      ring

/-- Square-root-free form of `M a * M (N - a) / M N ≤ C (N, a) ^ (-1 / 2)`. -/
theorem pairingCount_sq_mul_choose_le {a N : ℕ} (ha : Even a) (hN : Even N) (haN : a ≤ N) :
    (pairingCount a * pairingCount (N - a)) ^ 2 * N.choose a ≤ pairingCount N ^ 2 := by
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨m, rfl⟩ := hN
  obtain ⟨q, rfl⟩ : ∃ q, m = p + q := ⟨m - p, by omega⟩
  have e1 : p + p = 2 * p := (two_mul p).symm
  have e2 : p + q + (p + q) - (p + p) = 2 * q := by omega
  have e3 : p + q + (p + q) = 2 * (p + q) := (two_mul _).symm
  rw [e2, e3, e1]
  have hid := pairingCount_mul_pairingCount_mul_choose p q
  have hsq := choose_sq_le p q
  have hcpos : 0 < (2 * (p + q)).choose (2 * p) := Nat.choose_pos (by omega)
  apply Nat.le_of_mul_le_mul_right _ hcpos
  calc (pairingCount (2 * p) * pairingCount (2 * q)) ^ 2 * (2 * (p + q)).choose (2 * p) *
        (2 * (p + q)).choose (2 * p)
      = (pairingCount (2 * p) * pairingCount (2 * q) * (2 * (p + q)).choose (2 * p)) ^ 2 := by
        ring
    _ = pairingCount (2 * (p + q)) ^ 2 * (p + q).choose p ^ 2 := by
      rw [hid]
      ring
    _ ≤ pairingCount (2 * (p + q)) ^ 2 * (2 * (p + q)).choose (2 * p) :=
      Nat.mul_le_mul_left _ hsq

/-! ### Elementary numerical inequalities -/

/-- A quadratic is dominated by `(9 / 8) ^ s`. -/
theorem sq_mul_eight_pow_le (s : ℕ) : s ^ 2 * 8 ^ s ≤ 128 * 9 ^ s := by
  have h : ∀ s : ℕ, (s ^ 2 + 15 * s + 128) * 8 ^ s ≤ 128 * 9 ^ s := by
    intro s
    induction s with
    | zero => norm_num
    | succ s ih =>
      have hs : s ≤ s ^ 2 := by nlinarith
      have hq : 8 * ((s + 1) ^ 2 + 15 * (s + 1) + 128) ≤ 9 * (s ^ 2 + 15 * s + 128) := by
        nlinarith
      calc ((s + 1) ^ 2 + 15 * (s + 1) + 128) * 8 ^ (s + 1)
          = 8 * ((s + 1) ^ 2 + 15 * (s + 1) + 128) * 8 ^ s := by ring
        _ ≤ 9 * (s ^ 2 + 15 * s + 128) * 8 ^ s := Nat.mul_le_mul_right _ hq
        _ = 9 * ((s ^ 2 + 15 * s + 128) * 8 ^ s) := by ring
        _ ≤ 9 * (128 * 9 ^ s) := Nat.mul_le_mul_left _ ih
        _ = 128 * 9 ^ (s + 1) := by ring
  exact le_trans (Nat.mul_le_mul_right _ (by omega)) (h s)

/-- The case `k = 0` of the combined estimate, after cancelling `C (n, s) ^ 2`. -/
theorem closedCutTerm_core_zero {n s e : ℕ} (hs : 1 ≤ s) (hhalf : 2 * s ≤ n) (he : 1 ≤ e)
    (h : 2 ≤ e ∨ 2 ≤ s) :
    4 * n ^ 2 * 16 ^ s ≤ 10 ^ 4 * 9 ^ s * n.choose s ^ e := by
  by_cases hs2 : 2 ≤ s
  · have hd := sq_mul_two_pow_le_choose hs2 hhalf
    have hp := sq_mul_eight_pow_le s
    have hcpos : 0 < n.choose s := Nat.choose_pos (by omega)
    have hce : n.choose s ≤ n.choose s ^ e := Nat.le_self_pow (by omega) _
    have h16 : (16 : ℕ) ^ s = 2 ^ s * 8 ^ s := by rw [← mul_pow]; norm_num
    calc 4 * n ^ 2 * 16 ^ s = 4 * 8 ^ s * (n ^ 2 * 2 ^ s) := by rw [h16]; ring
      _ ≤ 4 * 8 ^ s * (8 * s ^ 2 * n.choose s) := Nat.mul_le_mul_left _ hd
      _ = 32 * n.choose s * (s ^ 2 * 8 ^ s) := by ring
      _ ≤ 32 * n.choose s * (128 * 9 ^ s) := Nat.mul_le_mul_left _ hp
      _ = 4096 * 9 ^ s * n.choose s := by ring
      _ ≤ 10 ^ 4 * 9 ^ s * n.choose s ^ e :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num)) hce
  · have hs1 : s = 1 := by omega
    have he2 : 2 ≤ e := by omega
    subst hs1
    rw [Nat.choose_one_right]
    have hpow : n ^ 2 ≤ n ^ e := Nat.pow_le_pow_right (by omega) he2
    calc 4 * n ^ 2 * 16 ^ 1 = 64 * n ^ 2 := by ring
      _ ≤ 10 ^ 4 * 9 ^ 1 * n ^ e := Nat.mul_le_mul (by norm_num) hpow

/-- `exp (1 / 10) ≤ 9 / 8`, from `1 - x ≤ exp (-x)`. -/
theorem exp_one_div_ten_le : Real.exp (1 / 10) ≤ 9 / 8 := by
  have h := Real.add_one_le_exp (-(1 / 10 : ℝ))
  rw [Real.exp_neg] at h
  have hpos := Real.exp_pos (1 / 10 : ℝ)
  have h2 : (9 / 10 : ℝ) * Real.exp (1 / 10) ≤ 1 := by
    calc (9 / 10 : ℝ) * Real.exp (1 / 10)
        ≤ (Real.exp (1 / 10))⁻¹ * Real.exp (1 / 10) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos.le
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  linarith

/-- The exponential slack: when `1000 * k < s` and `k ≥ 1`, factors exponential in `k` and
polynomial in `s` are absorbed by `(9 / 8) ^ s`. -/
theorem closedCutTerm_exp_slack {s k : ℕ} (hk1 : 1 ≤ k) (hk : 1000 * k < s) :
    32 * (512000000 : ℝ) ^ k * (s : ℝ) ^ 2 * Real.exp ((s : ℝ) / 500) ≤
      10 ^ 4 * (9 / 8 : ℝ) ^ s := by
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hks : (1000 : ℝ) * k ≤ s := by exact_mod_cast hk.le
  -- `s ^ 2 ≤ 10 ^ 4 * exp (s / 50)`
  have e1 : (s : ℝ) ≤ 100 * Real.exp ((s : ℝ) / 100) := by
    have h := Real.add_one_le_exp ((s : ℝ) / 100)
    linarith
  have e2 : (s : ℝ) ^ 2 ≤ 10 ^ 4 * Real.exp ((s : ℝ) / 50) := by
    have hexp : Real.exp ((s : ℝ) / 100) ^ 2 = Real.exp ((s : ℝ) / 50) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    calc (s : ℝ) ^ 2 ≤ (100 * Real.exp ((s : ℝ) / 100)) ^ 2 := pow_le_pow_left₀ hs0 e1 2
      _ = 10 ^ 4 * Real.exp ((s : ℝ) / 50) := by
        rw [mul_pow, hexp]
        norm_num
  -- `exp (s / 10) ≤ (9 / 8) ^ s`
  have e3 : Real.exp ((s : ℝ) / 10) ≤ (9 / 8 : ℝ) ^ s := by
    have h : Real.exp ((s : ℝ) / 10) = Real.exp (1 / 10) ^ s := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [h]
    exact pow_le_pow_left₀ (Real.exp_pos _).le exp_one_div_ten_le s
  -- `32 * 512000000 ^ k ≤ exp (39 * s / 500)`
  have e4 : 32 * (512000000 : ℝ) ^ k ≤ Real.exp (39 * (s : ℝ) / 500) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h78 : (16384000000 : ℝ) ≤ Real.exp 78 := by
      have h : Real.exp 78 = Real.exp 1 ^ 78 := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [h]
      calc (16384000000 : ℝ) ≤ 2 ^ 78 := by norm_num
        _ ≤ Real.exp 1 ^ 78 := pow_le_pow_left₀ (by norm_num) h2 78
    have h32 : (32 : ℝ) ≤ 32 ^ k := by
      calc (32 : ℝ) = 32 ^ 1 := (pow_one _).symm
        _ ≤ 32 ^ k := pow_le_pow_right₀ (by norm_num) hk1
    calc 32 * (512000000 : ℝ) ^ k ≤ 32 ^ k * 512000000 ^ k :=
          mul_le_mul_of_nonneg_right h32 (by positivity)
      _ = 16384000000 ^ k := by
        rw [← mul_pow]
        norm_num
      _ ≤ Real.exp 78 ^ k := pow_le_pow_left₀ (by norm_num) h78 k
      _ = Real.exp ((k : ℝ) * 78) := (Real.exp_nat_mul 78 k).symm
      _ ≤ Real.exp (39 * (s : ℝ) / 500) := Real.exp_le_exp.mpr (by linarith)
  have hsplit : Real.exp ((s : ℝ) / 10) =
      Real.exp (39 * (s : ℝ) / 500) * Real.exp ((s : ℝ) / 50) * Real.exp ((s : ℝ) / 500) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hW : 0 ≤ Real.exp ((s : ℝ) / 500) := (Real.exp_pos _).le
  calc 32 * (512000000 : ℝ) ^ k * (s : ℝ) ^ 2 * Real.exp ((s : ℝ) / 500)
      ≤ Real.exp (39 * (s : ℝ) / 500) * (10 ^ 4 * Real.exp ((s : ℝ) / 50)) *
          Real.exp ((s : ℝ) / 500) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul e4 e2 (by positivity) (Real.exp_pos _).le) hW
    _ = 10 ^ 4 * Real.exp ((s : ℝ) / 10) := by
      rw [hsplit]
      ring
    _ ≤ 10 ^ 4 * (9 / 8 : ℝ) ^ s := mul_le_mul_of_nonneg_left e3 (by norm_num)

/-- The case `k ≥ 1` of the combined estimate, after cancelling `C (n, s) ^ 2`. Here
`s > 1000`, and the bounds `C (d s, k) ≤ (d s) ^ k / k !` and `x ^ k / k ! ≤ exp x` are used. -/
theorem closedCutTerm_core_pos {n d s k : ℕ} (hd : 3 ≤ d) (hk1 : 1 ≤ k) (hk : 1000 * k < s)
    (hhalf : 2 * s ≤ n) :
    4 ^ (k + 1) * n ^ 2 * 16 ^ s * (d * s).choose k ^ 2 ≤
      10 ^ 4 * 9 ^ s * (n.choose s ^ (d - 3) * n.choose (s - k)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
  rw [Nat.add_sub_cancel]
  -- the dependence on `d`: `d ^ (2 k) ≤ 64 ^ k * C (n, s) ^ (d - 3)`
  have hc : (e + 3) ^ (2 * k) ≤ 64 ^ k * n.choose s ^ e := by
    calc (e + 3) ^ (2 * k) ≤ (2 ^ (e + 3)) ^ (2 * k) :=
          Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = 64 ^ k * (2 ^ (2 * k)) ^ e := by
        rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring
      _ ≤ 64 ^ k * (2 ^ s) ^ e :=
        Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (by omega)) _)
      _ ≤ 64 ^ k * n.choose s ^ e :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (two_pow_le_choose hhalf) _)
  -- the factor `n ^ 2`
  have hdn : n ^ 2 * 2 ^ s ≤ 8 * s ^ 2 * n.choose (s - k) * 2 ^ k := by
    have h := sq_mul_two_pow_le_choose (n := n) (j := s - k) (by omega) (by omega)
    have hsk : 8 * (s - k) ^ 2 ≤ 8 * s ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.sub_le _ _) 2)
    calc n ^ 2 * 2 ^ s = n ^ 2 * 2 ^ (s - k) * 2 ^ k := by
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
      _ ≤ 8 * (s - k) ^ 2 * n.choose (s - k) * 2 ^ k := Nat.mul_le_mul_right _ h
      _ ≤ 8 * s ^ 2 * n.choose (s - k) * 2 ^ k :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hsk)
  -- pass to the reals
  set D : ℝ := ((e + 3 : ℕ) : ℝ) with hD
  set c : ℝ := (((e + 3) * s).choose k : ℝ) with hcdef
  set P : ℝ := (n.choose s : ℝ) ^ e with hP
  set Q : ℝ := (n.choose (s - k) : ℝ) with hQ
  set W : ℝ := Real.exp ((s : ℝ) / 500) with hWdef
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := Nat.cast_nonneg _
  have hW0 : 0 ≤ W := (Real.exp_pos _).le
  have hcR : D ^ (2 * k) ≤ 64 ^ k * P := by
    rw [hD, hP]
    exact_mod_cast hc
  have hdnR : (n : ℝ) ^ 2 * 2 ^ s ≤ 8 * (s : ℝ) ^ 2 * Q * 2 ^ k := by
    rw [hQ]
    exact_mod_cast hdn
  have hslack : 32 * (512000000 : ℝ) ^ k * (s : ℝ) ^ 2 * W ≤ 10 ^ 4 * (9 / 8 : ℝ) ^ s :=
    closedCutTerm_exp_slack hk1 hk
  -- the binomial coefficient `C (d s, k)`
  have hch : c ≤ D ^ k * 1000 ^ k * Real.exp ((s : ℝ) / 1000) := by
    have h1 : c ≤ (((e + 3) * s : ℕ) : ℝ) ^ k / (k ! : ℝ) := Nat.choose_le_pow_div k _
    have h2 := Real.pow_div_factorial_le_exp (x := (s : ℝ) / 1000) (by positivity) k
    calc c ≤ (((e + 3) * s : ℕ) : ℝ) ^ k / (k ! : ℝ) := h1
      _ = D ^ k * 1000 ^ k * (((s : ℝ) / 1000) ^ k / (k ! : ℝ)) := by
        rw [hD, Nat.cast_mul, div_pow, mul_pow]
        field_simp
      _ ≤ D ^ k * 1000 ^ k * Real.exp ((s : ℝ) / 1000) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
  have hch2 : c ^ 2 ≤ D ^ (2 * k) * 1000000 ^ k * W := by
    have hexp : Real.exp ((s : ℝ) / 1000) ^ 2 = W := by
      rw [hWdef, sq, ← Real.exp_add]
      congr 1
      ring
    calc c ^ 2 ≤ (D ^ k * 1000 ^ k * Real.exp ((s : ℝ) / 1000)) ^ 2 :=
          pow_le_pow_left₀ hc0 hch 2
      _ = D ^ (2 * k) * 1000000 ^ k * W := by
        rw [mul_pow, mul_pow, hexp, show (1000000 : ℝ) = 1000 ^ 2 by norm_num,
          ← pow_mul, ← pow_mul, ← pow_mul, mul_comm k 2]
  have h16 : (16 : ℝ) ^ s = 2 ^ s * 8 ^ s := by
    rw [← mul_pow]
    norm_num
  have h512 : (512000000 : ℝ) ^ k = 4 ^ k * 64 ^ k * 1000000 ^ k * 2 ^ k := by
    rw [← mul_pow, ← mul_pow, ← mul_pow]
    norm_num
  have h9 : (9 : ℝ) ^ s = (9 / 8) ^ s * 8 ^ s := by
    rw [← mul_pow]
    norm_num
  have hfinal :
      (4 : ℝ) ^ (k + 1) * (n : ℝ) ^ 2 * 16 ^ s * c ^ 2 ≤ 10 ^ 4 * 9 ^ s * (P * Q) := by
    calc (4 : ℝ) ^ (k + 1) * (n : ℝ) ^ 2 * 16 ^ s * c ^ 2
        ≤ (4 : ℝ) ^ (k + 1) * (n : ℝ) ^ 2 * 16 ^ s * (64 ^ k * P * 1000000 ^ k * W) :=
          mul_le_mul_of_nonneg_left
            (hch2.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcR (by positivity)) hW0)) (by positivity)
      _ = (4 : ℝ) ^ (k + 1) * 8 ^ s * 64 ^ k * 1000000 ^ k * W * P * ((n : ℝ) ^ 2 * 2 ^ s) := by
        rw [h16]
        ring
      _ ≤ (4 : ℝ) ^ (k + 1) * 8 ^ s * 64 ^ k * 1000000 ^ k * W * P *
            (8 * (s : ℝ) ^ 2 * Q * 2 ^ k) :=
          mul_le_mul_of_nonneg_left hdnR (by positivity)
      _ = 32 * (512000000 : ℝ) ^ k * (s : ℝ) ^ 2 * W * (8 ^ s * (P * Q)) := by
        rw [h512]
        ring
      _ ≤ 10 ^ 4 * (9 / 8 : ℝ) ^ s * (8 ^ s * (P * Q)) :=
          mul_le_mul_of_nonneg_right hslack (by positivity)
      _ = 10 ^ 4 * 9 ^ s * (P * Q) := by
        rw [h9]
        ring
  rw [hcdef, hP, hQ] at hfinal
  exact_mod_cast hfinal

/-- The combined binomial estimate: the product of the squared prefactors of one summand is
exponentially smaller than the binomial coefficient controlling the pairing counts. -/
theorem closedCutTerm_core {n d s k : ℕ} (hd : 3 ≤ d) (hs : 1 ≤ s) (hhalf : 2 * s ≤ n)
    (hk : 1000 * k < s) (h : 4 ≤ d ∨ 2 ≤ s) :
    4 ^ (k + 1) * n ^ 2 * 16 ^ s * n.choose s ^ 2 * (d * s).choose k ^ 2 ≤
      10 ^ 4 * 9 ^ s * (n * d).choose (d * s - k) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · have h0 := closedCutTerm_core_zero (e := e + 1) hs hhalf (by omega) (by omega)
    have hv := choose_pow_le n s (e + 3)
    calc 4 ^ (0 + 1) * n ^ 2 * 16 ^ s * n.choose s ^ 2 * ((e + 3) * s).choose 0 ^ 2
        = 4 * n ^ 2 * 16 ^ s * n.choose s ^ 2 := by simp
      _ ≤ 10 ^ 4 * 9 ^ s * n.choose s ^ (e + 1) * n.choose s ^ 2 := Nat.mul_le_mul_right _ h0
      _ = 10 ^ 4 * 9 ^ s * n.choose s ^ (e + 3) := by ring
      _ ≤ 10 ^ 4 * 9 ^ s * (n * (e + 3)).choose (s * (e + 3)) := Nat.mul_le_mul_left _ hv
      _ = 10 ^ 4 * 9 ^ s * (n * (e + 3)).choose ((e + 3) * s - 0) := by
        rw [Nat.sub_zero, mul_comm s]
  · have h1 := closedCutTerm_core_pos (n := n) (d := e + 3) (by omega) hkpos hk hhalf
    rw [Nat.add_sub_cancel] at h1
    have hv := choose_pow_mul_choose_le n s (s - k) (e + 2)
    have hidx : s * (e + 2) + (s - k) = (e + 3) * s - k := by
      have h3 : (e + 3) * s = s * (e + 2) + s := by ring
      omega
    calc 4 ^ (k + 1) * n ^ 2 * 16 ^ s * n.choose s ^ 2 * ((e + 3) * s).choose k ^ 2
        = 4 ^ (k + 1) * n ^ 2 * 16 ^ s * ((e + 3) * s).choose k ^ 2 * n.choose s ^ 2 := by ring
      _ ≤ 10 ^ 4 * 9 ^ s * (n.choose s ^ e * n.choose (s - k)) * n.choose s ^ 2 :=
        Nat.mul_le_mul_right _ h1
      _ = 10 ^ 4 * 9 ^ s * (n.choose s ^ (e + 2) * n.choose (s - k)) := by ring
      _ ≤ 10 ^ 4 * 9 ^ s * (n * (e + 2 + 1)).choose (s * (e + 2) + (s - k)) :=
        Nat.mul_le_mul_left _ hv
      _ = 10 ^ 4 * 9 ^ s * (n * (e + 3)).choose ((e + 3) * s - k) := by rw [hidx]

/-- One summand of the closed-set term, cleared of denominators: the summand divided by
`pairingCount (n * d)` is at most `(100 / n) * (3 / 4) ^ s / 2 ^ (k + 1)`. Summands with
`d * s - k` odd vanish. -/
theorem closedCutSummand_le {n d s k : ℕ} (hd : 3 ≤ d) (hn : Even (n * d)) (hs : 1 ≤ s)
    (hhalf : 2 * s ≤ n) (hk : 1000 * k < s) :
    n.choose s * ((d * s).choose k * pairingCount (d * s - k) *
      pairingCount (n * d - (d * s - k))) * (n * 4 ^ s * 2 ^ (k + 1)) ≤
        100 * 3 ^ s * pairingCount (n * d) := by
  by_cases ha : Even (d * s - k)
  · -- parity excludes the only case, `d = 3` and `s = 1`, in which the core estimate fails
    have hds : 4 ≤ d ∨ 2 ≤ s := by
      by_contra hcon
      have hd3 : d = 3 := by omega
      have hs1 : s = 1 := by omega
      have hk0 : k = 0 := by omega
      subst hd3 hs1 hk0
      exact absurd ha (by decide)
    have haN : d * s - k ≤ n * d := by
      have h1 : d * s ≤ d * n := Nat.mul_le_mul_left _ (by omega)
      have h2 : d * n = n * d := mul_comm _ _
      omega
    have hX := pairingCount_sq_mul_choose_le ha hn haN
    have hcore := closedCutTerm_core hd hs hhalf hk hds
    have h16 : (16 : ℕ) ^ s = (4 ^ s) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h4 : (4 : ℕ) ^ (k + 1) = (2 ^ (k + 1)) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h9 : (9 : ℕ) ^ s = (3 ^ s) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [← Nat.pow_le_pow_iff_left (n := 2) two_ne_zero]
    calc (n.choose s * ((d * s).choose k * pairingCount (d * s - k) *
          pairingCount (n * d - (d * s - k))) * (n * 4 ^ s * 2 ^ (k + 1))) ^ 2
        = 4 ^ (k + 1) * n ^ 2 * 16 ^ s * n.choose s ^ 2 * (d * s).choose k ^ 2 *
            (pairingCount (d * s - k) * pairingCount (n * d - (d * s - k))) ^ 2 := by
          rw [h16, h4]
          ring
      _ ≤ 10 ^ 4 * 9 ^ s * (n * d).choose (d * s - k) *
            (pairingCount (d * s - k) * pairingCount (n * d - (d * s - k))) ^ 2 :=
          Nat.mul_le_mul_right _ hcore
      _ = 10 ^ 4 * 9 ^ s * ((pairingCount (d * s - k) *
            pairingCount (n * d - (d * s - k))) ^ 2 * (n * d).choose (d * s - k)) := by ring
      _ ≤ 10 ^ 4 * 9 ^ s * pairingCount (n * d) ^ 2 := Nat.mul_le_mul_left _ hX
      _ = (100 * 3 ^ s * pairingCount (n * d)) ^ 2 := by
          rw [h9]
          ring
  · have h0 : pairingCount (d * s - k) = 0 := by rw [pairingCount, if_neg ha]
    rw [h0]
    simp

end ConfigurationModel
