/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.Existence
import Expanders.Cheeger
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Random regular graphs are `d / 100`-edge-expanders

`Expanders/Existence.lean` shows that for every `d ≥ 3` almost every `d`-regular graph is an
`ε`-edge-expander for the fixed constant `ε = 1 / 1000`, which does not grow with `d`. This file
reruns the first-moment argument of the configuration model with `ε = d / 100` and shows that
the expansion constant can be taken to grow linearly in the degree. The counting argument
(`ConfigurationModel.card_badPairings_le_closedCutBound`) and the reduction from pairings to
graphs (`ConfigurationModel.tendsto_card_regular_isEdgeExpander_div`) are reused unchanged; only
the numerical estimate of the closed-set first moment is new.

There are no new definitions; everything below is a theorem.

## The numerical estimate (namespace `ConfigurationModel`)

Write `M = pairingCount`, `N = n d` and `a = d s - k`.

* `closedCutSummand_le_linear`: for `d ≥ 3`, `2 s ≤ n` and `100 k < d s`, one summand of the
  closed-set first moment satisfies
  `C (n, s) * C (d s, k) * M a * M (N - a) * (n * 32 ^ s * 2 ^ (k + 1)) ≤ 600 * 31 ^ s * M N`,
  i.e. divided by `M N` it is at most `(600 / n) * (31 / 32) ^ s / 2 ^ (k + 1)`.
* `closedCutTerm_le_geometric_linear`: hence the vertex sets of size `s` contribute at most
  `(600 / n) * (31 / 32) ^ s` to the normalized first moment with `ε = d / 100`.
* `closedCutBound_div_le_linear`: summing over `s`, the normalized first moment is at most
  `19200 / n`.
* `card_badPairings_div_le_linear`: hence at most a proportion `19200 / n` of the pairings is
  `(d / 100)`-bad, for every `n`.
* `tendsto_bad_fraction_linear`: the proportion of `(d / 100)`-bad pairings tends to `0`.

All four estimates hold for every `n`, with no parity hypothesis: when `n d` is odd there are no
pairings, `M N = 0`, and the normalized quantities take the junk value `x / 0 = 0`.

The proof of the summand bound runs as follows. Summands with `a` or `N - a` odd vanish.
Otherwise `(M a * M (N - a)) ^ 2 * C (N, a) ≤ M N ^ 2` (`pairingCount_sq_mul_choose_le`). The
lower bound `n ^ 2 * 2 ^ (a - 2 s) * C (n, s) ^ 2 ≤ 8 s ^ 2 * C (N, a)` comes from one term of
Vandermonde's identity, `C (n, s) ^ 2 * C (n (d - 2), a - 2 s) ≤ C (N, a)`, together with
`m ^ 2 * 2 ^ j ≤ 8 j ^ 2 * C (m, j)` for `m = n (d - 2)` and `j = a - 2 s ≤ (d - 2) s`; the factor
`(d - 2) ^ 2` cancels. What is left is an inequality free of `n`,
`32 * 8 ^ k * 4096 ^ s * s ^ 2 * C (d s, k) ^ 2 ≤ 360000 * 961 ^ s * 2 ^ (d s)`, proved in `ℝ`
from `C (d s, k) ≤ 100 ^ k * exp (d s / 100)`, `s ^ 2 ≤ 10 ^ 4 * exp (s / 50)`,
`80000 ≤ 2 ^ 17`, `4096 ≤ 961 * exp (163 / 100)` and `log 2 > 0.69`. It is here that `d ≥ 3`
is used: the exponent `1.65 s + d s / 50 + 17 k log 2` stays below `d s log 2` only because
`d s ≥ 3 s` and `100 k < d s`. The ratio `31 / 32` leaves room for these crude bounds. With the
ratio `7 / 8` they no longer suffice at `d = 3`, and with the ratio `3 / 4` of
`ConfigurationModel.closedCutTerm_le_geometric` the `n`-free inequality is false for every
constant: at `d = 3` its left side divided by its right side grows exponentially in `s`.

## Random regular graphs (namespace `SimpleGraph`)

* `tendsto_regularExpanderFraction_linear`: for `d ≥ 3` the proportion of `d`-regular graphs on
  `n` labelled vertices that are `(d / 100)`-edge-expanders tends to `1` along the `n` with
  `n d` even.
* `exists_regular_isEdgeExpander_linear`: hence there are arbitrarily large `d`-regular
  `(d / 100)`-edge-expanders.
* `exists_regular_isSpectralExpander_linear`: by the hard direction of Cheeger's inequality,
  `h(G) ≤ √(2 d (d − λ₂))` (`edgeExpansion_le_sqrt`, packaged as
  `IsEdgeExpander.isSpectralExpander`), there are arbitrarily large `d`-regular graphs with
  spectral gap at least `d / 20000`.

The hypothesis `d ≥ 3` cannot be weakened to `d ≥ 1`: a `1`-regular graph on `n ≥ 4` vertices
is a perfect matching, and the two endpoints of one edge form a set with no boundary edge; a
`2`-regular graph on `n ≥ 202` vertices is a disjoint union of cycles, and either a component
or an arc of `⌊n / 2⌋` consecutive vertices of a Hamiltonian cycle is a set with fewer than
`|S| / 50` boundary edges. For `d = 0` the statements hold trivially (`ε = 0`), but they are
stated for `d ≥ 3` only. The constants `100`, `600`, `19200` and `20000` are far from sharp.

## References
* B. Bollobás, *The isoperimetric number of random regular graphs*, European J. Combin. 9
  (1988), 241–244. The first-moment method in the configuration model gives a.a.s. edge
  expansion at least `d / 2 - √(d log 2)` for large `d`; the bound `d / 100` here is a much
  weaker special case.
* B. Kolesnik and N. Wormald, *Lower bounds for the isoperimetric numbers of random regular
  graphs*, SIAM J. Discrete Math. 28 (2014), 553–575, arXiv:1311.6555.
* J. Friedman, *A proof of Alon's second eigenvalue conjecture and related problems*, Mem.
  Amer. Math. Soc. 195 (2008). With the easy direction of Cheeger's inequality it gives edge
  expansion `(d - 2 √(d - 1) - o(1)) / 2` a.a.s.
* N. Alon, *On the edge-expansion of graphs*, Combin. Probab. Comput. 6 (1997), 145–152: the
  `√d` correction is necessary.
-/

open Finset Filter Topology
open scoped Nat

namespace ConfigurationModel

/-! ### The lower bound for the binomial coefficient -/

/-- Below the middle, after splitting off two blocks of size `s`:
`n ^ 2 * 2 ^ (a - 2 s) * C (n, s) ^ 2 ≤ 8 s ^ 2 * C (n d, a)` when `2 s + 2 ≤ a ≤ d s`. -/
private theorem sq_mul_two_pow_mul_choose_sq_le_linear {n d s a : ℕ} (hd : 3 ≤ d)
    (hhalf : 2 * s ≤ n) (ha2 : 2 * s + 2 ≤ a) (ha : a ≤ d * s) :
    n ^ 2 * 2 ^ (a - 2 * s) * n.choose s ^ 2 ≤ 8 * s ^ 2 * (n * d).choose a := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have he : 1 ≤ e := by omega
  have hds : (e + 2) * s = e * s + 2 * s := by ring
  have hj2 : 2 ≤ a - 2 * s := by omega
  have hje : a - 2 * s ≤ e * s := by omega
  have hjn : 2 * (a - 2 * s) ≤ n * e := by
    have h1 : e * (2 * s) ≤ e * n := Nat.mul_le_mul_left e hhalf
    have h2 : 2 * (e * s) = e * (2 * s) := by ring
    have h3 : e * n = n * e := mul_comm _ _
    omega
  have hb := sq_mul_two_pow_le_choose hj2 hjn
  have hjsq : (a - 2 * s) ^ 2 ≤ (e * s) ^ 2 := Nat.pow_le_pow_left hje 2
  have hb' : n ^ 2 * 2 ^ (a - 2 * s) ≤ 8 * s ^ 2 * (n * e).choose (a - 2 * s) := by
    have hpos : 0 < e ^ 2 := by positivity
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc e ^ 2 * (n ^ 2 * 2 ^ (a - 2 * s)) = (n * e) ^ 2 * 2 ^ (a - 2 * s) := by ring
      _ ≤ 8 * (a - 2 * s) ^ 2 * (n * e).choose (a - 2 * s) := hb
      _ ≤ 8 * (e * s) ^ 2 * (n * e).choose (a - 2 * s) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hjsq)
      _ = e ^ 2 * (8 * s ^ 2 * (n * e).choose (a - 2 * s)) := by ring
  have hv : n.choose s ^ 2 * (n * e).choose (a - 2 * s) ≤ (n * (e + 2)).choose a := by
    calc n.choose s ^ 2 * (n * e).choose (a - 2 * s)
        ≤ (n * 2).choose (s * 2) * (n * e).choose (a - 2 * s) :=
          Nat.mul_le_mul_right _ (choose_pow_le n s 2)
      _ ≤ (n * 2 + n * e).choose (s * 2 + (a - 2 * s)) := choose_mul_choose_le_add_choose _ _ _ _
      _ = (n * (e + 2)).choose a := by
          congr 1
          · ring
          · omega
  calc n ^ 2 * 2 ^ (a - 2 * s) * n.choose s ^ 2
      ≤ 8 * s ^ 2 * (n * e).choose (a - 2 * s) * n.choose s ^ 2 := Nat.mul_le_mul_right _ hb'
    _ = 8 * s ^ 2 * (n.choose s ^ 2 * (n * e).choose (a - 2 * s)) := by ring
    _ ≤ 8 * s ^ 2 * (n * (e + 2)).choose a := Nat.mul_le_mul_left _ hv

/-! ### The numerical core -/

/-- `4096 ≤ 961 * exp (163 / 100)`, from `e > 2.718` and `1 + x ≤ exp x`. -/
private theorem four_thousand_ninety_six_le_exp : (4096 : ℝ) ≤ 961 * Real.exp (163 / 100) := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp (63 / 100 : ℝ)
  have h3 : Real.exp (163 / 100) = Real.exp 1 * Real.exp (63 / 100) := by
    rw [← Real.exp_add]
    norm_num
  have h4 : (2.7182818283 : ℝ) * (63 / 100 + 1) ≤ Real.exp 1 * Real.exp (63 / 100) :=
    mul_le_mul h1.le h2 (by norm_num) (Real.exp_pos 1).le
  rw [h3]
  linarith

/-- The `n`-free core of the summand bound: for `d ≥ 3` and `100 k < d s`,
`32 * 8 ^ k * 4096 ^ s * s ^ 2 * C (d s, k) ^ 2 ≤ 360000 * 961 ^ s * 2 ^ (d s)`. -/
private theorem linear_core {d s k : ℕ} (hd : 3 ≤ d) (hk : 100 * k < d * s) :
    32 * 8 ^ k * 4096 ^ s * s ^ 2 * (d * s).choose k ^ 2 ≤ 360000 * 961 ^ s * 2 ^ (d * s) := by
  set x : ℝ := ((d * s : ℕ) : ℝ) with hx
  have hx3 : 3 * (s : ℝ) ≤ x := by
    rw [hx]
    exact_mod_cast Nat.mul_le_mul_right s hd
  have hkx : 100 * (k : ℝ) < x := by
    rw [hx]
    exact_mod_cast hk
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  set L : ℝ := Real.log 2 with hL
  have hL1 : (69 / 100 : ℝ) < L := by
    have := Real.log_two_gt_d9
    linarith
  have hL0 : 0 < L := by linarith
  -- `C (d s, k) ≤ 100 ^ k * exp (d s / 100)`
  have hc : (((d * s).choose k : ℕ) : ℝ) ≤ 100 ^ k * Real.exp (x / 100) := by
    have h1 : (((d * s).choose k : ℕ) : ℝ) ≤ x ^ k / (k ! : ℝ) := Nat.choose_le_pow_div k _
    have h2 := Real.pow_div_factorial_le_exp (x := x / 100) (by positivity) k
    calc (((d * s).choose k : ℕ) : ℝ) ≤ x ^ k / (k ! : ℝ) := h1
      _ = 100 ^ k * ((x / 100) ^ k / (k ! : ℝ)) := by
        rw [div_pow]
        field_simp
      _ ≤ 100 ^ k * Real.exp (x / 100) := mul_le_mul_of_nonneg_left h2 (by positivity)
  -- `s ^ 2 ≤ 10 ^ 4 * exp (s / 50)`
  have hsq : (s : ℝ) ^ 2 ≤ 10 ^ 4 * Real.exp ((s : ℝ) / 50) := by
    have e1 : (s : ℝ) ≤ 100 * Real.exp ((s : ℝ) / 100) := by
      have h := Real.add_one_le_exp ((s : ℝ) / 100)
      linarith
    have hexp : Real.exp ((s : ℝ) / 100) ^ 2 = Real.exp ((s : ℝ) / 50) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    calc (s : ℝ) ^ 2 ≤ (100 * Real.exp ((s : ℝ) / 100)) ^ 2 := pow_le_pow_left₀ hs0 e1 2
      _ = 10 ^ 4 * Real.exp ((s : ℝ) / 50) := by
        rw [mul_pow, hexp]
        norm_num
  -- `8 ^ k * (100 ^ k) ^ 2 ≤ 2 ^ (17 k) = exp (17 k log 2)`
  have h8 : (8 : ℝ) ^ k * (100 ^ k) ^ 2 ≤ Real.exp (17 * k * L) := by
    have h1 : Real.exp (17 * k * L) = (131072 : ℝ) ^ k := by
      rw [show 17 * (k : ℝ) * L = ((17 * k : ℕ) : ℝ) * L by push_cast; ring, Real.exp_nat_mul,
        hL, Real.exp_log two_pos, pow_mul]
      norm_num
    have h2 : (8 : ℝ) ^ k * (100 ^ k) ^ 2 = 80000 ^ k := by
      rw [← pow_mul, mul_comm k 2, pow_mul, ← mul_pow]
      norm_num
    rw [h1, h2]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
  -- `4096 ^ s ≤ 961 ^ s * exp (163 s / 100)`
  have h4096 : (4096 : ℝ) ^ s ≤ 961 ^ s * Real.exp (163 / 100 * s) := by
    have h : Real.exp (163 / 100 * s) = Real.exp (163 / 100) ^ s := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [h, ← mul_pow]
    exact pow_le_pow_left₀ (by norm_num) four_thousand_ninety_six_le_exp s
  -- `2 ^ (d s) = exp (d s log 2)`
  have h2 : (2 : ℝ) ^ (d * s) = Real.exp (x * L) := by
    rw [hx, Real.exp_nat_mul, hL, Real.exp_log two_pos]
  -- the exponents
  have hexpo : 17 * k * L + (163 / 100 * s + s / 50 + x / 50) ≤ x * L := by
    have h1 : 100 * (k : ℝ) * L ≤ x * L := mul_le_mul_of_nonneg_right hkx.le hL0.le
    have h2 : 69 / 100 * x ≤ L * x := mul_le_mul_of_nonneg_right hL1.le hx0
    nlinarith
  have hsplit : Real.exp (17 * k * L + (163 / 100 * s + s / 50 + x / 50)) =
      Real.exp (17 * k * L) * Real.exp (163 / 100 * s) * Real.exp ((s : ℝ) / 50) *
        Real.exp (x / 100) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hfinal : (32 : ℝ) * 8 ^ k * 4096 ^ s * (s : ℝ) ^ 2 * (((d * s).choose k : ℕ) : ℝ) ^ 2 ≤
      360000 * 961 ^ s * 2 ^ (d * s) := by
    have hc0 : (0 : ℝ) ≤ (((d * s).choose k : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (32 : ℝ) * 8 ^ k * 4096 ^ s * (s : ℝ) ^ 2 * (((d * s).choose k : ℕ) : ℝ) ^ 2
        ≤ 32 * 8 ^ k * (961 ^ s * Real.exp (163 / 100 * s)) *
            (10 ^ 4 * Real.exp ((s : ℝ) / 50)) * (100 ^ k * Real.exp (x / 100)) ^ 2 := by
          gcongr
      _ = 320000 * 961 ^ s * ((8 : ℝ) ^ k * (100 ^ k) ^ 2) *
            (Real.exp (163 / 100 * s) * Real.exp ((s : ℝ) / 50) * Real.exp (x / 100) ^ 2) := by
          ring
      _ ≤ 320000 * 961 ^ s * Real.exp (17 * k * L) *
            (Real.exp (163 / 100 * s) * Real.exp ((s : ℝ) / 50) * Real.exp (x / 100) ^ 2) := by
          gcongr
      _ = 320000 * 961 ^ s * Real.exp (17 * k * L + (163 / 100 * s + s / 50 + x / 50)) := by
          rw [hsplit]
          ring
      _ ≤ 320000 * 961 ^ s * Real.exp (x * L) := by
          gcongr
      _ ≤ 360000 * 961 ^ s * 2 ^ (d * s) := by
          rw [h2]
          gcongr
          norm_num
  exact_mod_cast hfinal

/-! ### One summand -/

/-- **One summand of the closed-set first moment, for `ε = d / 100`.** Let `d ≥ 3`, let `s`
(the size of a vertex set) satisfy `2 s ≤ n`, and let `k` (the number of crossing points) satisfy
`100 k < d s`. Then
`C (n, s) * C (d s, k) * M (d s - k) * M (n d - (d s - k)) * (n * 32 ^ s * 2 ^ (k + 1)) ≤
600 * 31 ^ s * M (n d)` with `M = pairingCount`. Equivalently, the summand divided by
`M (n d)` is at most `(600 / n) * (31 / 32) ^ s / 2 ^ (k + 1)`.

The hypothesis `100 k < d s` forces `s ≥ 1`, and with `2 s ≤ n` also `n ≥ 2`. No parity
hypothesis is needed: if `n d` is odd then one of `d s - k` and `n d - (d s - k)` is odd, so
the left side is `0` (as is `M (n d)`). The natural-number subtractions are genuine
subtractions, since `k < d s ≤ n d`. The case `k = 0` is included. -/
theorem closedCutSummand_le_linear {n d s k : ℕ} (hd : 3 ≤ d) (hhalf : 2 * s ≤ n)
    (hk : 100 * k < d * s) :
    n.choose s * ((d * s).choose k * pairingCount (d * s - k) *
      pairingCount (n * d - (d * s - k))) * (n * 32 ^ s * 2 ^ (k + 1)) ≤
        600 * 31 ^ s * pairingCount (n * d) := by
  have h3 : 3 * s ≤ d * s := Nat.mul_le_mul_right s hd
  have haN : d * s - k ≤ n * d := by
    have h1 : d * s ≤ d * n := Nat.mul_le_mul_left _ (by omega)
    have h2 : d * n = n * d := mul_comm _ _
    omega
  by_cases ha : Even (d * s - k)
  · by_cases hN : Even (n * d)
    · -- the only small case, `d = 3`, `s = 1`, `k = 0`, is excluded by parity
      have ha2 : 2 * s + 2 ≤ d * s - k := by
        by_contra hcon
        have hk0 : k = 0 := by omega
        have hs1 : s = 1 := by
          rcases Nat.lt_or_ge s 2 with h | h
          · interval_cases s
            · simp at hk
            · rfl
          · omega
        subst hk0 hs1
        have hd3 : d = 3 := by omega
        subst hd3
        exact absurd ha (by decide)
      have hX := pairingCount_sq_mul_choose_le ha hN haN
      have hL := sq_mul_two_pow_mul_choose_sq_le_linear (a := d * s - k) hd hhalf ha2
        (Nat.sub_le _ _)
      have hcore := linear_core hd hk
      set P := pairingCount (d * s - k) * pairingCount (n * d - (d * s - k)) with hP
      set c := (d * s).choose k with hc
      set B := (n * d).choose (d * s - k) with hB
      set T := 2 ^ (d * s - k - 2 * s) with hT
      have hTU : T * 2 ^ (2 * s + k) = 2 ^ (d * s) := by
        rw [hT, ← pow_add]
        congr 1
        omega
      have hpos : 0 < T * 2 ^ (2 * s + k) := by positivity
      have h1024 : ((32 : ℕ) ^ s) ^ 2 = 1024 ^ s := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      have h4 : ((2 : ℕ) ^ (k + 1)) ^ 2 = 4 * 4 ^ k := by
        rw [← pow_mul, mul_comm, pow_mul, pow_succ]
        norm_num
        ring
      have hU : (2 : ℕ) ^ (2 * s + k) = 4 ^ s * 2 ^ k := by rw [pow_add, pow_mul]; norm_num
      have h8 : (8 : ℕ) ^ k = 4 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
      have h4096 : (4096 : ℕ) ^ s = 1024 ^ s * 4 ^ s := by rw [← mul_pow]; norm_num
      have h961 : (961 : ℕ) ^ s = 31 ^ (2 * s) := by rw [pow_mul]; norm_num
      rw [← Nat.pow_le_pow_iff_left (n := 2) two_ne_zero]
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      calc (n.choose s * (c * pairingCount (d * s - k) * pairingCount (n * d - (d * s - k))) *
            (n * 32 ^ s * 2 ^ (k + 1))) ^ 2 * (T * 2 ^ (2 * s + k))
          = (n ^ 2 * T * n.choose s ^ 2) *
              ((32 ^ s) ^ 2 * (2 ^ (k + 1)) ^ 2 * 2 ^ (2 * s + k) * c ^ 2) * P ^ 2 := by
            rw [hP]
            ring
        _ ≤ (8 * s ^ 2 * B) * ((32 ^ s) ^ 2 * (2 ^ (k + 1)) ^ 2 * 2 ^ (2 * s + k) * c ^ 2) *
              P ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hL)
        _ = (32 * 8 ^ k * 4096 ^ s * s ^ 2 * c ^ 2) * (P ^ 2 * B) := by
            rw [h1024, h4, hU, h8, h4096]
            ring
        _ ≤ (360000 * 961 ^ s * 2 ^ (d * s)) * (P ^ 2 * B) := Nat.mul_le_mul_right _ hcore
        _ ≤ (360000 * 961 ^ s * 2 ^ (d * s)) * pairingCount (n * d) ^ 2 :=
            Nat.mul_le_mul_left _ hX
        _ = (600 * 31 ^ s * pairingCount (n * d)) ^ 2 * (T * 2 ^ (2 * s + k)) := by
            rw [hTU, h961]
            ring
    · have hodd : ¬Even (n * d - (d * s - k)) := by
        rw [Nat.even_sub haN]
        tauto
      have h0 : pairingCount (n * d - (d * s - k)) = 0 := by rw [pairingCount, if_neg hodd]
      rw [h0]
      simp
  · have h0 : pairingCount (d * s - k) = 0 := by rw [pairingCount, if_neg ha]
    rw [h0]
    simp

/-! ### Summing the envelope -/

/-- **The geometric envelope for `ε = d / 100`.** For `d ≥ 3` and `2 s ≤ n`, the vertex sets
of size `s` contribute at most `(600 / n) * (31 / 32) ^ s` to the normalized closed-set first
moment with `ε = d / 100`.

Degenerate cases: for `s = 0` the inner sum is empty (no `k` satisfies `k < 0`), so the term is
`0`. If `n d` is odd then `pairingCount (n * d) = 0` and the term is `x / 0 = 0` in Lean. For
`n = 0` the hypothesis forces `s = 0`, and the bound `600 / 0` is the junk value `0`. No parity
hypothesis and no hypothesis `s ≥ 1` is needed. -/
theorem closedCutTerm_le_geometric_linear {n d s : ℕ} (hd : 3 ≤ d) (hhalf : 2 * s ≤ n) :
    closedCutTerm n d s ((d : ℝ) / 100) ≤ (600 / (n : ℝ)) * (31 / 32 : ℝ) ^ s := by
  have hB0 : (0 : ℝ) ≤ (600 / (n : ℝ)) * (31 / 32 : ℝ) ^ s := by positivity
  rcases Nat.eq_zero_or_pos (pairingCount (n * d)) with hM0 | hMpos
  · simp only [closedCutTerm, hM0, Nat.cast_zero, div_zero]
    exact hB0
  have hM : (0 : ℝ) < pairingCount (n * d) := by exact_mod_cast hMpos
  -- each summand is bounded by the envelope times a geometric weight
  have hterm : ∀ k : ℕ, (k : ℝ) < (d : ℝ) / 100 * s →
      ((n.choose s * ((d * s).choose k * pairingCount (d * s - k) *
        pairingCount (n * d - (d * s - k))) : ℕ) : ℝ) / pairingCount (n * d) ≤
          (600 / (n : ℝ)) * (31 / 32 : ℝ) ^ s * (1 / 2) ^ (k + 1) := by
    intro k hk
    have hk' : 100 * k < d * s := by
      have h2 : ((100 * k : ℕ) : ℝ) < ((d * s : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h2
    have hs : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with h | h
      · subst h
        simp at hk'
      · exact h
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hreal : ((n.choose s * ((d * s).choose k * pairingCount (d * s - k) *
        pairingCount (n * d - (d * s - k))) : ℕ) : ℝ) * ((n : ℝ) * 32 ^ s * 2 ^ (k + 1)) ≤
          600 * 31 ^ s * pairingCount (n * d) := by
      exact_mod_cast closedCutSummand_le_linear hd hhalf hk'
    have hpos : (0 : ℝ) < (n : ℝ) * 32 ^ s * 2 ^ (k + 1) := by positivity
    have hrew : (600 / (n : ℝ)) * (31 / 32 : ℝ) ^ s * (1 / 2) ^ (k + 1) * pairingCount (n * d) =
        (600 * 31 ^ s * pairingCount (n * d)) / ((n : ℝ) * 32 ^ s * 2 ^ (k + 1)) := by
      rw [div_pow, div_pow, one_pow]
      field_simp
    rw [div_le_iff₀ hM, hrew, le_div_iff₀ hpos]
    exact hreal
  -- the geometric weights sum to at most one
  have hgeo : ∀ m : ℕ, ∑ k ∈ range m, (1 / 2 : ℝ) ^ (k + 1) = 1 - (1 / 2) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, ih]
      ring
  unfold closedCutTerm
  rw [mul_sum, Nat.cast_sum, sum_div]
  calc
    _ ≤ ∑ k ∈ (range (d * s + 1)).filter (fun k : ℕ => (k : ℝ) < (d : ℝ) / 100 * s),
        (600 / (n : ℝ)) * (31 / 32 : ℝ) ^ s * (1 / 2) ^ (k + 1) :=
      sum_le_sum fun k hk => hterm k (mem_filter.mp hk).2
    _ ≤ ∑ k ∈ range (d * s + 1), (600 / (n : ℝ)) * (31 / 32 : ℝ) ^ s * (1 / 2) ^ (k + 1) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
    _ = (600 / (n : ℝ)) * (31 / 32 : ℝ) ^ s * (1 - (1 / 2) ^ (d * s + 1)) := by
      rw [← mul_sum, hgeo]
    _ ≤ (600 / (n : ℝ)) * (31 / 32 : ℝ) ^ s := by
      have hp : (0 : ℝ) < (1 / 2) ^ (d * s + 1) := by positivity
      nlinarith [mul_nonneg hB0 hp.le]

/-- **The first moment for `ε = d / 100` is `O(1 / n)`.** For every `d ≥ 3` and every `n`, the
number of pairings counted by the closed-set union bound with `ε = d / 100`, divided by the
number of pairings `pairingCount (n * d)`, is at most `19200 / n`.

The constant is `600 * 32`, from summing `(31 / 32) ^ s`. Junk values: for `n d` odd the
denominator `pairingCount (n * d)` is `0` and the left side is `x / 0 = 0`; for `n = 0` the
right side is `19200 / 0 = 0`, and the left side is `0` too, since the sum over
`1 ≤ s ≤ n / 2` is empty. -/
theorem closedCutBound_div_le_linear {n d : ℕ} (hd : 3 ≤ d) :
    (closedCutBound n d ((d : ℝ) / 100) : ℝ) / pairingCount (n * d) ≤ 19200 / (n : ℝ) := by
  rw [closedCutBound_div_eq_sum]
  have hsum : ∑ s ∈ Icc 1 (n / 2), (31 / 32 : ℝ) ^ s ≤ 32 := by
    have h := (summable_geometric_of_lt_one (r := (31 / 32 : ℝ))
      (by norm_num) (by norm_num)).sum_le_tsum (Icc 1 (n / 2)) (fun _ _ => by positivity)
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h
    norm_num at h ⊢
    exact h
  calc
    _ ≤ ∑ s ∈ Icc 1 (n / 2), (600 / (n : ℝ)) * (31 / 32 : ℝ) ^ s := by
      apply sum_le_sum
      intro s hs
      exact closedCutTerm_le_geometric_linear hd (by
        have := (mem_Icc.mp hs).2
        omega)
    _ = (600 / (n : ℝ)) * ∑ s ∈ Icc 1 (n / 2), (31 / 32 : ℝ) ^ s := (mul_sum _ _ _).symm
    _ ≤ (600 / (n : ℝ)) * 32 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 19200 / (n : ℝ) := by ring

/-- **At most a proportion `19200 / n` of the pairings has a cut sparser than `d / 100`.** For
every `d ≥ 3` and every `n`, the number of configuration-model pairings of the `n * d` points
that are `(d / 100)`-bad (some vertex set `S` with `2 |S| ≤ n` has fewer than `(d / 100) |S|`
crossing pairs), divided by the number of all pairings, is at most `19200 / n`.

Junk values: when `n d` is odd there are no pairings at all, and the left side is
`0 / 0 = 0`; for `n = 0` the right side is `19200 / 0 = 0`, and the left side is `0 / 1 = 0`
(the empty pairing is not bad, since the strict inequality fails for `S = ∅`). -/
theorem card_badPairings_div_le_linear {d : ℕ} (hd : 3 ≤ d) (n : ℕ) :
    (#(badPairings n d ((d : ℝ) / 100)) : ℝ) / #(pairings n d) ≤ 19200 / (n : ℝ) := by
  have hcount : #(pairings n d) = pairingCount (n * d) := by
    have h := card_fixedPointFree_involutions_eq_pairingCount (α := Fin n × Fin d)
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
    exact h
  rw [hcount]
  exact (div_le_div_of_nonneg_right
    (by exact_mod_cast card_badPairings_le_closedCutBound n d ((d : ℝ) / 100))
    (Nat.cast_nonneg _)).trans (closedCutBound_div_le_linear hd)

/-- **Almost no pairing has a cut sparser than `d / 100`.** For every `d ≥ 3`, the proportion
of configuration-model pairings of `n * d` points that are `(d / 100)`-bad tends to `0` as
`n → ∞` (it is at most `19200 / n`, `card_badPairings_div_le_linear`).

The limit is taken along all `n`, with no parity restriction: when `n d` is odd there are no
pairings and no bad pairings, and the proportion is the junk value `0 / 0 = 0`. The statement
along the `n` with `n d` even, in the form required by
`tendsto_card_regular_isEdgeExpander_div`, follows by restricting the filter. -/
theorem tendsto_bad_fraction_linear {d : ℕ} (hd : 3 ≤ d) :
    Tendsto (fun n => (#(badPairings n d ((d : ℝ) / 100)) : ℝ) / #(pairings n d))
      atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat (19200 : ℝ))
    (fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (card_badPairings_div_le_linear hd)

end ConfigurationModel

namespace SimpleGraph

/-- **A random `d`-regular graph is a `(d / 100)`-edge-expander.** For every `d ≥ 3`, the
proportion of `d`-regular graphs on `n` labelled vertices that are `(d / 100)`-edge-expanders
tends to `1` as `n → ∞` along the `n` with `n d` even. So the expansion constant grows linearly
with the degree, in contrast with the fixed `ε = 1 / 1000` of `tendsto_regularExpanderFraction`.

The parity restriction is necessary: for `n d` odd there is no `d`-regular graph on `n`
vertices and `regularExpanderFraction` takes the junk value `0 / 0 = 0`. For small `n` with `n d`
even and no `d`-regular graph (for example `d = 3`, `n = 2`) the value is also `0`, which does
not affect the limit. The hypothesis `d ≥ 3` cannot be weakened to `d ≥ 1`: for `d = 1` and
`n ≥ 4`, and for `d = 2` and `n ≥ 202`, no `d`-regular graph is a `(d / 100)`-edge-expander, so
the proportion is `0` for all large `n`. For `d = 0` the statement is true but trivial: the
only `0`-regular graph is the empty graph, every graph is a `0`-edge-expander, and the
proportion is `1` for every `n`.

Proved from `ConfigurationModel.exists_simple_card_lower_bound` (a positive proportion of
pairings is simple), `ConfigurationModel.tendsto_bad_fraction_linear` and the reduction
`ConfigurationModel.tendsto_card_regular_isEdgeExpander_div`. -/
theorem tendsto_regularExpanderFraction_linear {d : ℕ} (hd : 3 ≤ d) :
    Tendsto (fun n => regularExpanderFraction d n ((d : ℝ) / 100))
      (atTop ⊓ 𝓟 {n | Even (n * d)}) (𝓝 1) := by
  obtain ⟨c, hc, N, hsimple⟩ := ConfigurationModel.exists_simple_card_lower_bound d
  exact ConfigurationModel.tendsto_card_regular_isEdgeExpander_div hc hsimple
    ((ConfigurationModel.tendsto_bad_fraction_linear hd).mono_left inf_le_left)

/-- **Expanders with expansion linear in the degree.** For every `d ≥ 3` there are arbitrarily
large `d`-regular `(d / 100)`-edge-expanders: for every `N` some `d`-regular graph on `n ≥ N`
labelled vertices has at least `(d / 100) |S|` edges leaving every vertex set `S` with
`2 |S| ≤ n`.

The content is that `N` is arbitrary. On fewer than two vertices every graph is an
`ε`-edge-expander for every `ε` (only `S = ∅` is admissible), so for `N ≤ 1` the conclusion
alone says little; `exists_regular_isSpectralExpander_linear` builds the bound `n + 2 ≥ 2` into
the vertex type.

Proved from `tendsto_regularExpanderFraction_linear`: a proportion tending to `1` is eventually
positive, so the set it counts is nonempty. -/
theorem exists_regular_isEdgeExpander_linear {d : ℕ} (hd : 3 ≤ d) (N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.IsRegularOfDegree d ∧ G.IsEdgeExpander ((d : ℝ) / 100) := by
  classical
  have hlim := tendsto_regularExpanderFraction_linear hd
  have hev : ∀ᶠ n in atTop ⊓ 𝓟 {n | Even (n * d)},
      (0 : ℝ) < regularExpanderFraction d n ((d : ℝ) / 100) :=
    hlim.eventually (lt_mem_nhds one_pos)
  rw [Filter.eventually_inf_principal, Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  have hpos := hN₀ (2 * max N N₀) (by omega) (by simp [mul_assoc])
  refine ⟨2 * max N N₀, by omega, ?_⟩
  rcases Finset.eq_empty_or_nonempty
      ({G : SimpleGraph (Fin (2 * max N N₀)) |
        G.IsRegularOfDegree d ∧ G.IsEdgeExpander ((d : ℝ) / 100)} : Finset _) with h0 | ⟨G, hG⟩
  · simp [regularExpanderFraction, h0] at hpos
  · exact ⟨G, _, (Finset.mem_filter.mp hG).2.1, (Finset.mem_filter.mp hG).2.2⟩

/-- **Spectral expanders with gap linear in the degree.** For every `d ≥ 3` and every `N` there
is a `d`-regular graph on `n + 2 ≥ N + 2` labelled vertices whose spectral gap `d - λ₂` is at
least `d / 20000`.

This is `exists_regular_isEdgeExpander_linear` followed by the hard direction of Cheeger's
inequality, `h(G) ≤ √(2 d (d − λ₂))` (`edgeExpansion_le_sqrt`, packaged as
`IsEdgeExpander.isSpectralExpander`), which turns edge expansion `ε = d / 100` into the gap
`ε ^ 2 / (2 d) = d / 20000`. The vertex type is written `Fin (n + 2)` because
`IsSpectralExpander` (through `secondAdjEigenvalue`) needs at least two vertices. -/
theorem exists_regular_isSpectralExpander_linear {d : ℕ} (hd : 3 ≤ d) (N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ (G : SimpleGraph (Fin (n + 2))) (_ : DecidableRel G.Adj),
      G.IsSpectralExpander d ((d : ℝ) / 20000) := by
  obtain ⟨m, hm, G, _, hreg, hexp⟩ := exists_regular_isEdgeExpander_linear hd (N + 2)
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  refine ⟨n, by omega, G, inferInstance, ?_⟩
  have h := hexp.isSpectralExpander hreg (by positivity)
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have heq : ((d : ℝ) / 100) ^ 2 / (2 * d) = (d : ℝ) / 20000 := by
    field_simp
    ring
  rwa [heq] at h

end SimpleGraph
