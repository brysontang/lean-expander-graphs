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
  Matrix.IsHermitian.smallestEigenvalue
  Matrix.IsHermitian.smallestEigenvalue_le_eigenvalues
  Matrix.IsHermitian.smallest_mul_le_dotProduct_mulVec
  Matrix.IsHermitian.smallest_le_of_mulVec_eq
  Matrix.IsHermitian.exists_eigenvector_smallest
  Matrix.IsHermitian.dotProduct_mulVec_eq_sum_coeff
  Matrix.IsHermitian.coeff_topIndex_eq_zero
  SimpleGraph.smallestAdjEigenvalue
  SimpleGraph.twoSidedAdjEigenvalue
  SimpleGraph.IsTwoSidedSpectralExpander
  SimpleGraph.smallestAdjEigenvalue_le_secondAdjEigenvalue
  SimpleGraph.smallestAdjEigenvalue_nonpos
  SimpleGraph.smallestAdjEigenvalue_le_neg_one
  SimpleGraph.twoSidedAdjEigenvalue_nonneg
  SimpleGraph.one_le_twoSidedAdjEigenvalue
  SimpleGraph.twoSidedAdjEigenvalue_eq_max
  SimpleGraph.twoSidedAdjEigenvalue_le_degree
  SimpleGraph.eigenvalues_mem_Icc_of_coeff_ne_zero
  SimpleGraph.abs_eigenvalues_le_twoSidedAdjEigenvalue
  SimpleGraph.sq_dotProduct_adjMatrix_mulVec_le
  SimpleGraph.indicator_dotProduct_adjMatrix_mulVec
  SimpleGraph.card_interedges_eq_add_dotProduct_centeredIndicator
  SimpleGraph.expander_mixing_lemma
  SimpleGraph.expander_mixing_lemma_sqrt_card_mul
  SimpleGraph.IsTwoSidedSpectralExpander.expander_mixing_lemma
  SimpleGraph.IsTwoSidedSpectralExpander.isSpectralExpander
  SimpleGraph.card_interedges_self_le
  SimpleGraph.le_card_interedges_self
  SimpleGraph.IsIndepSet.interedges_self_eq_empty
  SimpleGraph.IsIndepSet.card_mul_degree_sub_smallestAdjEigenvalue_le
  SimpleGraph.indepNum_mul_degree_sub_smallestAdjEigenvalue_le
  SimpleGraph.hoffman_ratio_bound
  SimpleGraph.Colorable.degree_sub_smallestAdjEigenvalue_le
  SimpleGraph.Colorable.one_sub_degree_div_smallestAdjEigenvalue_le
  SimpleGraph.hoffman_chromatic_bound
  SimpleGraph.two_div_card_le_edgeExpansion
  SimpleGraph.edgeExpansion_pos_iff_connected
  SimpleGraph.secondAdjEigenvalue_lt_iff_connected
  SimpleGraph.spectralGap_pos_iff_connected
  SimpleGraph.two_le_degree_mul_card_sq_mul_spectralGap
  SimpleGraph.sum_adj_add_sq_div_two
  SimpleGraph.neg_degree_le_smallestAdjEigenvalue
  SimpleGraph.smallestAdjEigenvalue_eq_neg_of_isBipartite
  SimpleGraph.isBipartite_of_smallestAdjEigenvalue_eq_neg
  SimpleGraph.smallestAdjEigenvalue_eq_neg_iff
  SimpleGraph.smallestAdjEigenvalue_eq_neg_iff_exists_isBipartite
  SimpleGraph.twoSidedAdjEigenvalue_lt_iff
  SimpleGraph.twoSidedAdjEigenvalue_eq_degree_iff
  SimpleGraph.hypercube_isBipartite
  SimpleGraph.hypercube_connected
  SimpleGraph.hypercube_smallestAdjEigenvalue
  SimpleGraph.hypercube_twoSidedAdjEigenvalue
  SimpleGraph.IsRamanujan.twoSidedAdjEigenvalue_le
  SimpleGraph.isRamanujan_of_twoSidedAdjEigenvalue_le
  SimpleGraph.isRamanujan_iff_of_not_isBipartite
  SimpleGraph.cycleGraph_isRegularOfDegree
  SimpleGraph.cycleGraph_adj_val
  SimpleGraph.two_le_card_edgeBoundary_cycleGraph
  SimpleGraph.cycleGraph_edgeExpansion
  SimpleGraph.le_cycleGraph_secondAdjEigenvalue
  SimpleGraph.cycleGraph_secondAdjEigenvalue_le
  SimpleGraph.cycleGraph_secondAdjEigenvalue
  SimpleGraph.cycleGraph_spectralGap
  SimpleGraph.cycleGraph_spectralGap_le
  SimpleGraph.sqrt_div_pi_le_cycleGraph_edgeExpansion
  SimpleGraph.cycleGraph_edgeExpansion_le_sqrt
  SimpleGraph.eventually_cycleGraph_rpow_lt_edgeExpansion
  SimpleGraph.exists_cycleGraph_rpow_lt_edgeExpansion
  SimpleGraph.f2Cayley_isRegularOfDegree
  SimpleGraph.f2Cayley_adjMatrix_mulVec_f2Char
  SimpleGraph.sum_f2Char_dotProduct_mul
  SimpleGraph.f2Cayley_secondAdjEigenvalue
  SimpleGraph.f2Cayley_spectralGap
  SimpleGraph.f2Cayley_halfSpace
  SimpleGraph.f2Cayley_edgeExpansion_le
  SimpleGraph.f2Cayley_edgeExpansion
  SimpleGraph.f2Cayley_halfSpace_attains_edgeExpansion
  SimpleGraph.f2Cayley_exists_halfSpace_attains_edgeExpansion
  SimpleGraph.f2Cayley_edgeExpansion_eq_spectralGap_div_two
  Matrix.IsHermitian.mulVec_eq_secondEigenvalue_smul_of_eq
  SimpleGraph.cutVector
  SimpleGraph.crossDegree
  SimpleGraph.cutVector_dotProduct_adjMatrix_mulVec
  SimpleGraph.adjMatrix_mulVec_cutVector_apply
  SimpleGraph.adjMatrix_mulVec_cutVector_eq_iff
  SimpleGraph.spectralGap_mul_card_mul_card_compl_le
  SimpleGraph.isEdgeExpander_spectralGap_mul_ceil
  SimpleGraph.spectralGap_mul_ceil_div_le_edgeExpansion
  SimpleGraph.IsSpectralExpander.isEdgeExpander_ceil
  SimpleGraph.exists_edgeExpansion_eq
  SimpleGraph.two_mul_card_eq_of_cutVector
  SimpleGraph.card_edgeBoundary_eq_of_cutVector
  SimpleGraph.edgeExpansion_eq_of_cutVector
  SimpleGraph.balanced_of_card_edgeBoundary_le
  SimpleGraph.balanced_of_edgeExpansion_eq
  SimpleGraph.edgeExpansion_eq_spectralGap_div_two_iff
  SimpleGraph.edgeExpansion_eq_spectralGap_div_two_iff_exists
  SimpleGraph.spectralGap_div_two_lt_edgeExpansion_of_odd
  SimpleGraph.exists_nat_of_edgeExpansion_eq_spectralGap_div_two
  SimpleGraph.spectralGap_div_two_lt_edgeExpansion_of_lt_two
  SimpleGraph.hypercube_exists_crossDegree_eq_one
  SimpleGraph.secondAdjEigenvalue_top
  SimpleGraph.spectralGap_top
  SimpleGraph.card_edgeBoundary_top
  SimpleGraph.edgeExpansion_top
  SimpleGraph.forall_mul_spectralGap_le_edgeExpansion_iff
  SimpleGraph.forall_isSpectralExpander_isEdgeExpander_mul_iff
  SimpleGraph.forall_regular_mul_spectralGap_le_edgeExpansion_iff
  SimpleGraph.forall_regular_isSpectralExpander_isEdgeExpander_mul_iff
  WalkSecondEigenvalueLE.mul_vol_le_cut
  WalkSecondEigenvalueLE.weightCut_ge
  WalkSecondEigenvalueLE.weightCut_pos
  WalkSecondEigenvalueLE.eq_of_forall_pos
  two_mul_sum_deg_mul_le_sum_mul_abs_sub
  sq_le_two_mul_one_sub_of_eigenfunction
  walkSecondEigenvalueLE_of_weightCut_ge
  WalkSecondEigenvalueLE.one_sub_div_two_le_conductance
  walkSecondEigenvalueLE_conductance
  walk_cheeger
  conductance_le
  le_conductance
  exists_weightVol_pos_of_ne
  PreAbstractSimplicialComplex.IsTopWeight.isConnected_link_of_walkSecondEigenvalueLE
  SimpleGraph.AlonBoppana.exists_profile_cos
  SimpleGraph.AlonBoppana.radial_mul_radial_eq_zero_of_le_edist
  SimpleGraph.AlonBoppana.le_secondAdjEigenvalue_of_le_edist
  SimpleGraph.cos_le_secondAdjEigenvalue_of_le_edist
  SimpleGraph.cos_le_secondAdjEigenvalue_of_lt_edist
  SimpleGraph.cos_le_secondAdjEigenvalue_of_le_ediam
  SimpleGraph.cos_le_secondAdjEigenvalue_of_pow_lt_card
  SimpleGraph.sub_le_secondAdjEigenvalue_of_le_edist
  SimpleGraph.sub_le_secondAdjEigenvalue_of_pow_lt_card
  SimpleGraph.alonBoppanaRadius
  SimpleGraph.alonBoppanaCard
  SimpleGraph.one_le_alonBoppanaRadius
  SimpleGraph.pi_sq_mul_sqrt_le_mul_alonBoppanaRadius
  SimpleGraph.alonBoppanaRadius_le
  SimpleGraph.alon_boppana_explicit
  SimpleGraph.abs_adjMatrix_pow_apply_sub_le
  SimpleGraph.abs_adjMatrix_add_degree_pow_apply_sub_le
  SimpleGraph.degree_add_secondAdjEigenvalue_nonneg
  SimpleGraph.exists_walk_length_eq_of_mul_twoSidedAdjEigenvalue_pow_lt
  SimpleGraph.connected_and_diam_le_of_mul_twoSidedAdjEigenvalue_pow_lt
  SimpleGraph.connected_and_diam_le_of_mul_degree_add_secondAdjEigenvalue_pow_lt
  SimpleGraph.exists_walk_length_eq_floor_log_add_one
  SimpleGraph.connected_and_diam_le_floor_log_twoSidedAdjEigenvalue
  SimpleGraph.connected_and_diam_le_floor_log_secondAdjEigenvalue
  SimpleGraph.dotProduct_self_adjMatrix_pow_mulVec_sub_le
  SimpleGraph.sum_abs_adjMatrix_pow_mulVec_sub_le
  SimpleGraph.sum_abs_randomWalk_pow_mulVec_sub_le
  SimpleGraph.neighborhood
  SimpleGraph.vertexBoundary
  SimpleGraph.IsVertexExpander
  SimpleGraph.mem_neighborhood
  SimpleGraph.mem_vertexBoundary
  SimpleGraph.card_vertexBoundary_le_card_edgeBoundary
  SimpleGraph.card_edgeBoundary_le_mul_card_vertexBoundary
  SimpleGraph.IsVertexExpander.isEdgeExpander
  SimpleGraph.IsEdgeExpander.mul_card_le_card_vertexBoundary
  SimpleGraph.IsEdgeExpander.isVertexExpander
  SimpleGraph.degree_sub_secondAdjEigenvalue_mul_card_le_card_vertexBoundary
  SimpleGraph.isVertexExpander_degree_sub_secondAdjEigenvalue
  SimpleGraph.dotProduct_self_adjMatrix_mulVec_add_smul_le
  SimpleGraph.tanner_of_support_subset
  SimpleGraph.tanner
  SimpleGraph.tanner_shift
  SimpleGraph.tanner_secondAdjEigenvalue
  SimpleGraph.hypercube_tanner
  ConfigurationModel.closedCutSummand_le_linear
  ConfigurationModel.closedCutTerm_le_geometric_linear
  ConfigurationModel.closedCutBound_div_le_linear
  ConfigurationModel.card_badPairings_div_le_linear
  ConfigurationModel.tendsto_bad_fraction_linear
  SimpleGraph.tendsto_regularExpanderFraction_linear
  SimpleGraph.exists_regular_isEdgeExpander_linear
  SimpleGraph.exists_regular_isSpectralExpander_linear
  PreAbstractSimplicialComplex.trickling_down_lower
  PreAbstractSimplicialComplex.walkSmallestEigenvalueGE_linkWeightOf_step
  PreAbstractSimplicialComplex.trickling_down_lower_weighted
  PreAbstractSimplicialComplex.trickling_down_two_sided
  PreAbstractSimplicialComplex.isTwoSidedLocalSpectralExpanderOf_of_trickling_down
  walkSmallestEigenvalueGE_iff_le_eigenvalues
  garland_inequality_lower
  WalkSmallestEigenvalueGE.lt_zero
  PreAbstractSimplicialComplex.isTwoSidedLocalSpectralExpanderOf_complete_fin5_two_iff
  PreAbstractSimplicialComplex.IsTwoSidedLocalSpectralExpanderOf.mono
  WalkSecondEigenvalueLE.mul_loop_sub_sq_le
  WalkSecondEigenvalueLE.neg_deg_le
  WalkSecondEigenvalueLE.neg_one_div_card_le
  walkSecondEigenvalueLE_neg_one_div_card_iff
  PreAbstractSimplicialComplex.le_card_pos_degree_linkWeightOf
  PreAbstractSimplicialComplex.IsTopWeight.le_card_pos_degree_link
  PreAbstractSimplicialComplex.neg_one_div_le_of_walkSecondEigenvalueLE_linkWeightOf
  PreAbstractSimplicialComplex.IsTopWeight.neg_one_div_le_of_walkSecondEigenvalueLE_link
  PreAbstractSimplicialComplex.walkSecondEigenvalueLE_linkWeightOf_neg_one_div_iff
  PreAbstractSimplicialComplex.sum_linkWeightOf_mul_mul_eq_neg_one_div_mul
  PreAbstractSimplicialComplex.IsTopWeight.sum_linkWeightOf_mul_mul_eq_neg_one_div_mul
  PreAbstractSimplicialComplex.IsTopWeight.forall_eq_of_subset_iff_topDegree_le_one
  PreAbstractSimplicialComplex.IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_neg_one_div_iff
  PreAbstractSimplicialComplex.IsPure.succ_le_ncard_vertices
  PreAbstractSimplicialComplex.IsTopWeight.sum_linkWeightOf_empty_pos_iff
  PreAbstractSimplicialComplex.IsLocalSpectralExpanderOf.neg_one_div_ncard_vertices_le
  PreAbstractSimplicialComplex.IsLocalSpectralExpander.neg_one_div_ncard_vertices_le
  PreAbstractSimplicialComplex.isLocalSpectralExpanderOf_neg_one_div_iff
  PreAbstractSimplicialComplex.isLocalSpectralExpander_neg_one_div_iff
  PreAbstractSimplicialComplex.isLocalSpectralExpander_complete_fin_succ_neg_one_div
  PreAbstractSimplicialComplex.walkSecondEigenvalueLE_cliqueWeight_iff
  PreAbstractSimplicialComplex.topDegree_complete_eq_choose
  PreAbstractSimplicialComplex.linkWeight_complete_eq_choose
  PreAbstractSimplicialComplex.walkSecondEigenvalueLE_linkWeight_complete_iff
  PreAbstractSimplicialComplex.trickling_down_bound_complete
  PreAbstractSimplicialComplex.walkSecondEigenvalueLE_linkWeight_complete_iff_tricklingBound
  PreAbstractSimplicialComplex.trickling_down_complete
  PreAbstractSimplicialComplex.isLocalSpectralExpander_complete_iff_le
  PreAbstractSimplicialComplex.neg_one_div_card_le_of_walkSecondEigenvalueLE
  PreAbstractSimplicialComplex.IsLocalSpectralExpanderOf.neg_one_div_natCard_vertices_le
  PreAbstractSimplicialComplex.isLeast_setOf_isLocalSpectralExpanderOf
  PreAbstractSimplicialComplex.exists_lt_neg_one_div_succ_isLocalSpectralExpanderOf_iff
  WalkSecondEigenvalueLE.neg_two_mul_weight_le
  WalkSecondEigenvalueLE.weight_pos_of_neg
  WalkSecondEigenvalueLE.neg_one_div_le_of_support
  PreAbstractSimplicialComplex.IsTopWeight.mem_of_trickling_down_neg
  PreAbstractSimplicialComplex.IsTopWeight.eq_complete_of_trickling_down_neg
  PreAbstractSimplicialComplex.mem_of_trickling_down_neg
  PreAbstractSimplicialComplex.eq_complete_of_trickling_down_neg
  PreAbstractSimplicialComplex.IsLocalSpectralExpanderOf.mem_of_neg
  PreAbstractSimplicialComplex.IsLocalSpectralExpanderOf.eq_complete_of_neg
  PreAbstractSimplicialComplex.IsLocalSpectralExpander.mem_of_neg
  PreAbstractSimplicialComplex.IsLocalSpectralExpander.eq_complete_of_neg
  PreAbstractSimplicialComplex.walkSecondEigenvalueLE_complete_codimTwo_link_iff
  PreAbstractSimplicialComplex.complete_isLocalSpectralExpander_iff
  PreAbstractSimplicialComplex.trickling_down_hypotheses_neg_iff
  PreAbstractSimplicialComplex.exists_neg_isLocalSpectralExpander_iff
  PreAbstractSimplicialComplex.twoTriangles_sharp_at_zero
  PreAbstractSimplicialComplex.IsLocalSpectralExpanderOf.skeleton
  PreAbstractSimplicialComplex.IsLocalSpectralExpander.skeleton
  PreAbstractSimplicialComplex.IsTopWeight.skeleton
  PreAbstractSimplicialComplex.faceWeight_skeletonWeight
  PreAbstractSimplicialComplex.linkWeightOf_skeletonWeight
  PreAbstractSimplicialComplex.walkSecondEigenvalueLE_linkWeightOf_skeletonWeight_iff
  walkSecondEigenvalueLE_const_mul_iff
  PreAbstractSimplicialComplex.link_skeleton
  PreAbstractSimplicialComplex.isConnected_link_skeleton_iff
  PreAbstractSimplicialComplex.isConnected_link_skeleton_of_forall
  PreAbstractSimplicialComplex.oneSkeleton_link_skeleton
  PreAbstractSimplicialComplex.vertices_link_skeleton
  PreAbstractSimplicialComplex.vertices_skeleton
  PreAbstractSimplicialComplex.oneSkeleton_skeleton
  PreAbstractSimplicialComplex.isConnected_skeleton_iff
  PreAbstractSimplicialComplex.skeletonWeight_self
  PreAbstractSimplicialComplex.skeletonWeight_eq_zero_of_lt
  PreAbstractSimplicialComplex.skeletonWeight_uniformWeight
  PreAbstractSimplicialComplex.skeleton_eq_self
  PreAbstractSimplicialComplex.IsPure.skeleton_eq_self
  PreAbstractSimplicialComplex.skeleton_le
  PreAbstractSimplicialComplex.mem_skeleton
  PreAbstractSimplicialComplex.upForm_le
  PreAbstractSimplicialComplex.IsLocalSpectralExpanderOf.upForm_le
  PreAbstractSimplicialComplex.downNormSq_le
  PreAbstractSimplicialComplex.upForm_ge
  PreAbstractSimplicialComplex.upDown_gap
  PreAbstractSimplicialComplex.IsLocalSpectralExpanderOf.upDown_gap
  PreAbstractSimplicialComplex.sum_linkWeightOf_mul_mul_eq_upForm
  PreAbstractSimplicialComplex.sum_linkWeightOf_norm_eq
  PreAbstractSimplicialComplex.sum_faceWeight_mul_sq_sum_powersetCard
  PreAbstractSimplicialComplex.sum_downSum_mul
  PreAbstractSimplicialComplex.sum_downSum
  PreAbstractSimplicialComplex.upForm_eq_sum_insert_erase
  PreAbstractSimplicialComplex.upForm_eq_zero_of_le
  PreAbstractSimplicialComplex.downSum_eq_zero_of_mul_faceWeight_eq_zero
  PreAbstractSimplicialComplex.downNormSq_nonneg
  PreAbstractSimplicialComplex.levelNormSq_nonneg
