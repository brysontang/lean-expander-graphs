/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.ConfigurationModelExpansionEstimates

/-!
# Almost no configuration-model pairing has a sparse cut

The main theorem is reduced to a first-moment bound with `ε = 1 / 1000`.
`ConfigurationModelExpansionCount` proves the finite counting argument without gaps: deleting
the crossing endpoints leaves a preserved set of points, and restriction to this set and its
complement gives the required injection.

**Status:** proved without gaps. The numerical estimate
`ConfigurationModel.closedCutTerm_le_geometric` in `ConfigurationModelExpansionEstimates` is
proved from the binomial inequalities in `ConfigurationModelBinomial`. The geometric summation,
limit argument, and reduction below are proved from it.

## References
* B. Bollobás, *The isoperimetric number of random regular graphs*,
  European J. Combin. 9 (1988), 241–244.
-/

open Finset Filter Topology

namespace ConfigurationModel

/-- For every degree `d ≥ 3`, the proportion of `ε`-bad pairings tends to zero along
`n * d` even, for `ε = 1 / 1000`. The number of bad pairings is bounded by an explicit sum
(`card_badPairings_le_closedCutBound`), and that sum is controlled by the uniform numerical
bound `closedCutTerm_le_geometric`. -/
theorem exists_tendsto_bad_fraction {d : ℕ} (hd : 3 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧
      Tendsto (fun n => (#(badPairings n d ε) : ℝ) / #(pairings n d))
        (atTop ⊓ 𝓟 {n | Even (n * d)}) (𝓝 0) := by
  refine ⟨1 / 1000, by norm_num, ?_⟩
  have hcount (n : ℕ) (heven : Even (n * d)) :
      #(pairings n d) = pairingCount (n * d) := by
    obtain ⟨m, hm⟩ := heven
    have hm' : n * d = 2 * m := by omega
    rw [card_pairings hm', pairingCount, if_pos ⟨m, hm⟩, hm']
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_closedCutBound_div hd) ?_ ?_
  · exact Filter.Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rw [eventually_inf_principal]
    exact Filter.Eventually.of_forall fun n hn => by
      rw [hcount n hn]
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast card_badPairings_le_closedCutBound n d (1 / 1000))
        (Nat.cast_nonneg _)

end ConfigurationModel
