/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.ConfigurationModel

/-!
# Open lemma A: a positive proportion of pairings is simple

This file contains one statement, `ConfigurationModel.exists_simple_card_lower_bound`, and it is
**not yet proved**. It is one of the two inputs of the reduction
`ConfigurationModel.tendsto_card_regular_isEdgeExpander_div`; the other is in
`Expanders/ConfigurationModelExpansion.lean`.

## References
* E. A. Bender, E. R. Canfield, *The asymptotic number of labeled graphs with given degree
  sequences*, J. Combin. Theory Ser. A 24 (1978), 296–307.
* B. Bollobás, *A probabilistic proof of an asymptotic formula for the number of labelled regular
  graphs*, European J. Combin. 1 (1980), 311–316.
* B. D. McKay, *Asymptotics for symmetric 0-1 matrices with prescribed row sums*,
  Ars Combin. 19A (1985), 15–25.
-/

open Finset

namespace ConfigurationModel

/-- **Open lemma A (simplicity).** For every degree `d`, a positive proportion of the pairings of
`n * d` points is simple, uniformly in large `n` with `n * d` even.

Not yet proved. In fact the proportion of simple pairings converges to `exp (-(d² - 1) / 4)` for
`d ≥ 1` (Bender–Canfield 1978, Bollobás 1980): in a uniformly random pairing the number of loops
and the number of pairs of parallel pairs are asymptotically independent Poisson variables with
means `(d - 1) / 2` and `(d - 1)² / 4`. The classical proof is the method of moments. An
elementary proof of the lower bound goes through *switchings* (McKay 1985): a switching replaces
two pairs `{p₁, p₂}`, `{p₃, p₄}` by `{p₁, p₃}`, `{p₂, p₄}`; counting the switchings that destroy
a loop (or a double pair) against those that create one compares the number of pairings with
`ℓ` loops and `m` double pairs with the number having `ℓ - 1` (or `m - 1`), and summing these
ratios bounds the total number of pairings by a constant multiple of the number of simple ones.

Sanity checks on the statement. For `d = 0` (no points, one empty pairing) and `d = 1` (every
vertex has a single point) every pairing is simple, so `c = 1` works. The threshold `N` cannot
be dropped: for `0 < n ≤ d` with `n * d` even there are pairings but no simple ones, since a
`d`-regular simple graph needs more than `d` vertices. For `n * d` odd there are no
pairings at all and the inequality would read `0 ≤ 0`; the hypothesis `Even (n * d)` only
records that this case is not needed. -/
theorem exists_simple_card_lower_bound (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
      c * #(pairings n d) ≤ #(simplePairings n d) := by
  sorry

end ConfigurationModel
