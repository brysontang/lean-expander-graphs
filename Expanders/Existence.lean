/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders.Basic
import Expanders.ConfigurationModelSimple
import Expanders.ConfigurationModelExpansion

/-!
# Existence of expanders

Expanders exist in abundance: for every fixed degree `d ≥ 3`, almost every `d`-regular graph is
an expander. (Writing one down explicitly is a different and much harder problem.)

* `SimpleGraph.regularExpanderFraction`: the proportion of `d`-regular graphs on `n` labelled
  vertices that are `ε`-edge-expanders.
* `SimpleGraph.tendsto_regularExpanderFraction`: that proportion tends to `1`.
  **Proved from two lemmas** about the configuration model, by the reduction in
  `Expanders/ConfigurationModel.lean`. One of them is proved:
  `ConfigurationModel.exists_simple_card_lower_bound` (a positive proportion of pairings is
  simple). The other is still open: `ConfigurationModel.exists_tendsto_bad_fraction` (almost no
  pairing has a sparse cut). It is the only use of `sorry` this theorem depends on.
* `SimpleGraph.exists_regular_isEdgeExpander`: hence arbitrarily large `d`-regular
  `ε`-edge-expanders exist. **Proved from the statement above**, so it rests on the same one
  open lemma.
-/

open Finset Filter Topology

namespace SimpleGraph

open Classical in
/-- The proportion of `d`-regular graphs on the vertex set `Fin n` that are `ε`-edge-expanders,
i.e. the probability that a uniformly random `d`-regular graph on `n` labelled vertices is an
`ε`-edge-expander. (Junk value `0` when there are no `d`-regular graphs on `n` vertices.) -/
noncomputable def regularExpanderFraction (d n : ℕ) (ε : ℝ) : ℝ :=
  (#{G : SimpleGraph (Fin n) | G.IsRegularOfDegree d ∧ G.IsEdgeExpander ε} : ℝ) /
    #{G : SimpleGraph (Fin n) | G.IsRegularOfDegree d}

/-- **A random regular graph is almost always an expander.** For every `d ≥ 3` there is an
`ε > 0` such that the proportion of `d`-regular graphs on `n` vertices that are
`ε`-edge-expanders tends to `1` as `n → ∞` (along those `n` for which `d`-regular graphs exist,
namely `n d` even).

Proved here from two lemmas about the configuration model.
`ConfigurationModel.exists_simple_card_lower_bound`, a positive proportion of pairings is
simple, is proved. `ConfigurationModel.exists_tendsto_bad_fraction`, the proportion of pairings
with a sparse cut tends to `0`, is still open, so this theorem still depends on `sorry`. The
passage from pairings to regular graphs,
`ConfigurationModel.tendsto_card_regular_isEdgeExpander_div`, is fully proved: every `d`-regular
graph is the graph of exactly `(d!)ⁿ` simple pairings. -/
theorem tendsto_regularExpanderFraction {d : ℕ} (hd : 3 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧
      Tendsto (fun n => regularExpanderFraction d n ε) (atTop ⊓ 𝓟 {n | Even (n * d)}) (𝓝 1) := by
  obtain ⟨c, hc, N, hsimple⟩ := ConfigurationModel.exists_simple_card_lower_bound d
  obtain ⟨ε, hε, hbad⟩ := ConfigurationModel.exists_tendsto_bad_fraction hd
  exact ⟨ε, hε, ConfigurationModel.tendsto_card_regular_isEdgeExpander_div hc hsimple hbad⟩

/-- **Expander families exist.** For every `d ≥ 3` there is an `ε > 0` such that there are
arbitrarily large `d`-regular `ε`-edge-expanders.

Proved here as a corollary of `tendsto_regularExpanderFraction` (which rests on one open lemma
about the configuration model): a proportion tending to `1` is eventually positive, so the set
it counts is nonempty. -/
theorem exists_regular_isEdgeExpander {d : ℕ} (hd : 3 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n, N ≤ n ∧
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        G.IsRegularOfDegree d ∧ G.IsEdgeExpander ε := by
  classical
  obtain ⟨ε, hε, hlim⟩ := tendsto_regularExpanderFraction hd
  refine ⟨ε, hε, fun N => ?_⟩
  have hev : ∀ᶠ n in atTop ⊓ 𝓟 {n | Even (n * d)}, (0 : ℝ) < regularExpanderFraction d n ε :=
    hlim.eventually (lt_mem_nhds one_pos)
  rw [Filter.eventually_inf_principal, Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  have hpos := hN₀ (2 * max N N₀) (by omega) (by simp [mul_assoc])
  refine ⟨2 * max N N₀, by omega, ?_⟩
  rcases Finset.eq_empty_or_nonempty
      ({G : SimpleGraph (Fin (2 * max N N₀)) | G.IsRegularOfDegree d ∧ G.IsEdgeExpander ε} :
        Finset _) with h0 | ⟨G, hG⟩
  · simp [regularExpanderFraction, h0] at hpos
  · exact ⟨G, _, (Finset.mem_filter.mp hG).2.1, (Finset.mem_filter.mp hG).2.2⟩

end SimpleGraph
