/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders

/-!
# Axiom audit

Run with `lake env lean Audit.lean` after `lake build`. The file fails to check (non-zero exit
code) if either

* a theorem listed under `#assert_proved` depends on anything other than Lean's three standard
  axioms `propext`, `Classical.choice`, `Quot.sound` (in particular on `sorryAx`), or
* a theorem listed under `#assert_open` no longer depends on `sorryAx`, so the list of open
  statements cannot silently go stale.

Continuous integration runs this file on every push.
-/

open Lean Elab Command

/-- The axioms a finished proof is allowed to depend on. -/
def Audit.standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#assert_proved A B …` fails unless every listed declaration depends only on the three
standard axioms. -/
elab "#assert_proved " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← collectAxioms n
    let bad := axs.toList.filter (· ∉ Audit.standardAxioms)
    unless bad.isEmpty do
      throwErrorAt id "{n} is listed as proved but depends on {bad}"
  logInfo m!"proved: {ids.size} declarations depend only on {Audit.standardAxioms}"

/-- `#assert_open A B …` fails unless every listed declaration still depends on `sorryAx`. -/
elab "#assert_open " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← collectAxioms n
    unless axs.contains ``sorryAx do
      throwErrorAt id "{n} is listed as open but no longer depends on `sorry`; move it to #assert_proved"
  logInfo m!"open: {ids.size} declarations still depend on an unproved statement"

#assert_proved
  Matrix.IsHermitian.dotProduct_mulVec_le_largest
  Matrix.IsHermitian.dotProduct_mulVec_le_second
  Matrix.IsHermitian.exists_orthogonal_second_le
  SimpleGraph.card_edgeBoundary_le
  SimpleGraph.isEdgeExpander_iff
  SimpleGraph.edgeExpansion_le_degree
  SimpleGraph.abs_le_of_adjMatrix_mulVec_eq
  SimpleGraph.largestAdjEigenvalue_eq
  SimpleGraph.dotProduct_adjMatrix_mulVec_le
  SimpleGraph.exists_sum_eq_zero_secondAdjEigenvalue_mul_le
  SimpleGraph.spectralGap_mul_le
  SimpleGraph.exists_eigenvector_secondAdjEigenvalue
  SimpleGraph.sum_adj_sub_sq_div_two
  SimpleGraph.isEdgeExpander_spectralGap_div_two
  SimpleGraph.spectralGap_div_two_le_edgeExpansion
  SimpleGraph.edgeExpansion_le_sqrt
  SimpleGraph.cheeger
  SimpleGraph.alon_boppana
  SimpleGraph.walkSecondEigenvalueLE_adjMatrix_iff
  PreAbstractSimplicialComplex.link_empty
  PreAbstractSimplicialComplex.link_link
  PreAbstractSimplicialComplex.linkWeight_symm
  garland_inequality
  walkSecondEigenvalueLE_of_garland
  PreAbstractSimplicialComplex.trickling_down
  PreAbstractSimplicialComplex.isLocalSpectralExpander_of_trickling_down
  walkSecondEigenvalueLE_of_forall_eq_zero
  walkMatrix_largestEigenvalue
  walkSecondEigenvalueLE_iff_secondEigenvalue_le
  PreAbstractSimplicialComplex.exists_linkWeight_pos
  PreAbstractSimplicialComplex.complete_fin5_two_walkSecondEigenvalueLE
  PreAbstractSimplicialComplex.not_complete_fin5_two_walkSecondEigenvalueLE
  ConfigurationModel.isRegularOfDegree_graph
  ConfigurationModel.card_filter_graph_eq
  ConfigurationModel.card_edgeBoundary_graph
  ConfigurationModel.isEdgeExpander_graph_iff
  ConfigurationModel.card_simplePairings
  ConfigurationModel.tendsto_card_regular_isEdgeExpander_div
  ConfigurationModel.card_fixedPointFree_involutions
  ConfigurationModel.card_pairings
  ConfigurationModel.card_pairings_of_odd
  SimpleGraph.hypercube_isRegularOfDegree
  SimpleGraph.hypercube_secondAdjEigenvalue
  SimpleGraph.hypercube_spectralGap
  SimpleGraph.hypercube_edgeExpansion

#assert_open
  ConfigurationModel.exists_simple_card_lower_bound
  ConfigurationModel.exists_tendsto_bad_fraction
  SimpleGraph.tendsto_regularExpanderFraction
  SimpleGraph.exists_regular_isEdgeExpander
