/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.ConfigurationModel

/-!
# Open lemma B: almost no pairing has a sparse cut

This file contains one statement, `ConfigurationModel.exists_tendsto_bad_fraction`, and it is
**not yet proved**. It is one of the two inputs of the reduction
`ConfigurationModel.tendsto_card_regular_isEdgeExpander_div`; the other is in
`Expanders/ConfigurationModelSimple.lean`.

## References
* B. Bollobás, *The isoperimetric number of random regular graphs*,
  European J. Combin. 9 (1988), 241–244.
-/

open Finset Filter Topology

namespace ConfigurationModel

/-- **Open lemma B (expansion).** For every degree `d ≥ 3` there is an `ε > 0` such that the
proportion of `ε`-bad pairings of `n * d` points tends to `0` as `n → ∞` with `n * d` even.
Here all pairings are counted, not only the simple ones, and a pairing is `ε`-bad
(`ConfigurationModel.IsBad`) if some vertex set `S` with `2|S| ≤ n` has fewer than `ε|S|` pairs
leaving it.

Not yet proved. This is the configuration-model form of Bollobás 1988. The proof is a first
moment (union bound) count. Write `M(2m) = (2m - 1)!!` for the number of pairings of `2m` points.
For a fixed set `S` of `s` vertices, the number of pairings with exactly `k` pairs leaving `S` is

  `(ds choose k) * (d(n - s) choose k) * k! * M(ds - k) * M(d(n - s) - k)`

(choose the `k` endpoints on each side, match them up, and pair off the remaining points on each
side), and the total number of pairings is `M(dn)`. So the proportion of `ε`-bad pairings is at
most the sum of `(n choose s)` times that product over `1 ≤ s ≤ n / 2` and `k < ε s`, divided by
`M(dn)`, and Stirling-type estimates show that this sum tends to `0` when `d ≥ 3` and `ε` is
small. For small `s` the dominant term is `k = 0`, of order `n ^ (s - ds / 2)`; this is where
`d ≥ 3` is needed, and the statement is false for `d = 2`, where a random pairing is a union of
cycles and has a short one with probability bounded away from `0`.

Sanity checks on the statement. The inequality in `IsBad` is strict, so `S = ∅` never makes a
pairing bad. The constant cannot be taken larger than `d - 2`: a vertex carrying a loop has at
most `d - 2` pairs leaving it, and a random pairing has a loop with probability bounded away
from `0`. For `n * d` odd there are no pairings and the ratio is `0 / 0 = 0`. -/
theorem exists_tendsto_bad_fraction {d : ℕ} (hd : 3 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧
      Tendsto (fun n => (#(badPairings n d ε) : ℝ) / #(pairings n d))
        (atTop ⊓ 𝓟 {n | Even (n * d)}) (𝓝 0) := by
  sorry

end ConfigurationModel
