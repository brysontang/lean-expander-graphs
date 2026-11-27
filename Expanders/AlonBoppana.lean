import Expanders.Basic

/-!
# The Alon–Boppana bound and Ramanujan graphs

The spectral gap of a `d`-regular graph has a ceiling: `λ₂` cannot stay far below `2√(d − 1)`
once the graph is large. Graphs that meet this ceiling are called *Ramanujan*.

* `SimpleGraph.IsRamanujan`: the definition.
* `SimpleGraph.alon_boppana`: the bound `λ₂ ≥ 2√(d − 1) − o(1)`. **Stated, not yet proved.**
-/

open Finset

namespace SimpleGraph

/-- A `d`-regular graph is **Ramanujan** if every adjacency eigenvalue `μ` other than `±d`
satisfies `|μ| ≤ 2√(d − 1)`: its spectral gap is as large as the Alon–Boppana bound allows. -/
def IsRamanujan {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) : Prop :=
  G.IsRegularOfDegree d ∧
    ∀ i, |G.adjEigenvalues i| = d ∨ |G.adjEigenvalues i| ≤ 2 * Real.sqrt (d - 1)

/-- **Alon–Boppana bound.** For every degree `d` and every `ε > 0`, all sufficiently large
`d`-regular graphs have `λ₂ ≥ 2√(d − 1) − ε`. So no infinite family of `d`-regular graphs has
spectral gap bounded above `d − 2√(d − 1)`.

Not yet proved. The standard proof (Nilli) builds a test function supported on two far-apart
balls and feeds it to the variational bound `SimpleGraph.dotProduct_adjMatrix_mulVec_le`. -/
theorem alon_boppana (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree d → N ≤ Fintype.card V →
        2 * Real.sqrt (d - 1) - ε ≤ G.secondAdjEigenvalue := by
  sorry

end SimpleGraph
