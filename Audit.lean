/-
Copyright (c) 2026 Bryson Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryson Tang
-/
import Expanders

/-!
# Axiom audit

Run with `lake env lean Audit.lean` after `lake build`. The file fails to check (non-zero exit
code) if any of the following holds.

* `#assert_project_sorry_free`: some declaration in a module `Expanders.*` is declared as an
  axiom, or mentions `sorryAx` directly. Every use of `sorry` in the project is caught this way,
  whether or not the theorem is named in the list below.
* `#assert_proved`: a listed theorem depends on anything other than Lean's three standard axioms
  `propext`, `Classical.choice`, `Quot.sound`. This is the full transitive check, applied to the
  results the README advertises.
* `#assert_open`: a listed theorem no longer depends on `sorryAx`. The project currently has no
  open statements, so the command is unused; it is kept for when new statements are added ahead
  of their proofs.

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

/-- `#assert_project_sorry_free` scans every declaration defined in a module whose name starts
with `Expanders` and fails if one of them is an axiom or refers to `sorryAx` in its type or
value. -/
elab "#assert_project_sorry_free" : command => do
  let env ← getEnv
  -- Read declarations from the kernel environment: the elaborator's view of an imported
  -- theorem does not include its proof term.
  let kenv := env.checked.get
  let mut bad : Array Name := #[]
  let mut count : Nat := 0
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless (`Expanders).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    let some ci := kenv.find? n | continue
    count := count + 1
    let isAx := match ci with
      | .axiomInfo _ => true
      | _ => false
    -- `ConstantInfo.value?` returns nothing for theorems, so match on the constructors.
    let val? : Option Expr := match ci with
      | .thmInfo v => some v.value
      | .defnInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    let used := ci.type.getUsedConstants ++ ((val?.map (·.getUsedConstants)).getD #[])
    if isAx || used.contains ``sorryAx then bad := bad.push n
  unless bad.isEmpty do
    throwError "these project declarations are axioms or use `sorry`: {bad.toList}"
  logInfo m!"project: none of the {count} declarations in `Expanders.*` is an axiom or uses `sorry`"

#assert_project_sorry_free

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
  SimpleGraph.IsSpectralExpander.isEdgeExpander
  SimpleGraph.IsEdgeExpander.isSpectralExpander
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
  ConfigurationModel.switching_card_bound
  ConfigurationModel.exp_mul_card_pairings_le
  ConfigurationModel.exists_simple_card_lower_bound
  PreAbstractSimplicialComplex.linkWeight_eq_linkWeightOf
  PreAbstractSimplicialComplex.trickling_down_weighted
  PreAbstractSimplicialComplex.link_walk_lower_bound
  PreAbstractSimplicialComplex.IsTopWeight.exists_linkWeightOf_pos
  PreAbstractSimplicialComplex.isLocalSpectralExpander_iff_isLocalSpectralExpanderOf
  PreAbstractSimplicialComplex.IsLocalSpectralExpanderOf.neg_one_div_le
  PreAbstractSimplicialComplex.isLocalSpectralExpander_complete_fin5_two
  PreAbstractSimplicialComplex.not_isLocalSpectralExpander_zero
  PreAbstractSimplicialComplex.not_isLocalSpectralExpanderOf_zero
  ConfigurationModel.card_badPairings_le_closedCutBound
  ConfigurationModel.closedCutTerm_le_geometric
  ConfigurationModel.exists_tendsto_bad_fraction
  SimpleGraph.tendsto_regularExpanderFraction
  SimpleGraph.exists_regular_isEdgeExpander
