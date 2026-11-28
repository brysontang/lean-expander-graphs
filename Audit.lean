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
  PreAbstractSimplicialComplex.tfae_forall_isLocalSpectralExpanderOf_zero
  PreAbstractSimplicialComplex.forall_isLocalSpectralExpanderOf_zero_iff
  PreAbstractSimplicialComplex.exists_isTopWeight_not_walkSecondEigenvalueLE_zero
  PreAbstractSimplicialComplex.IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_zero
  PreAbstractSimplicialComplex.forall_isLocalSpectralExpanderOf_zero_of_forall_card_inter
  PreAbstractSimplicialComplex.forall_card_inter_of_forall_isLocalSpectralExpanderOf_zero
  PreAbstractSimplicialComplex.forall_card_inter_iff_sunflower_or_subset
  PreAbstractSimplicialComplex.sunflower_or_subset_of_forall_card_inter
  PreAbstractSimplicialComplex.forall_card_inter_of_sunflower_or_subset
  PreAbstractSimplicialComplex.isMatroidComplex_of_forall_card_inter
  PreAbstractSimplicialComplex.noTwoDisjointLinkEdges_of_forall_card_inter
  PreAbstractSimplicialComplex.forall_card_inter_of_isMatroidComplex
  PreAbstractSimplicialComplex.isConnected_link_of_forall_card_inter
  PreAbstractSimplicialComplex.forall_card_inter_of_isConnected_link
  PreAbstractSimplicialComplex.forall_isLocalSpectralExpanderOf_zero_of_card_le
  PreAbstractSimplicialComplex.forall_isLocalSpectralExpanderOf_zero_iff_cone
  PreAbstractSimplicialComplex.disjointTriangles_counterexample
  PreAbstractSimplicialComplex.isLocalSpectralExpanderOf_twoTriangles_zero
  Finset.sunflower_or_subset_of_card_inter
  PreAbstractSimplicialComplex.IsTopWeight.walkSecondEigenvalueLE_of_edge_average
  PreAbstractSimplicialComplex.IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_of_edge_average
  PreAbstractSimplicialComplex.walkSecondEigenvalueLE_linkWeight_of_edge_average
  PreAbstractSimplicialComplex.IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_step_of_edge_average
  EdgeAverageTricklingDown.IsTriangleWeight.walkSecondEigenvalueLE_of_edge_average
  EdgeAverageTricklingDown.local_bochner
  EdgeAverageTricklingDown.eq_of_walkSecondEigenvalueLE_lt_one
  PreAbstractSimplicialComplex.tricklingEquality_iff
  PreAbstractSimplicialComplex.walkEigenspace_eq_edgeKernel
  PreAbstractSimplicialComplex.finrank_walkEigenspace_eq_finrank_edgeKernel
  PreAbstractSimplicialComplex.eigen_of_edgeOperator_eq_zero
  PreAbstractSimplicialComplex.IsTopWeight.tricklingEquality_iff_upWalk
  PreAbstractSimplicialComplex.upWalk_liftSum_eq_iff
  PreAbstractSimplicialComplex.IsPure.eq_of_liftSum_eq
  PreAbstractSimplicialComplex.IsTopWeight.isLeast_iff_exists_edgeOperator_eq_zero
  PreAbstractSimplicialComplex.IsTopWeight.eigen_eq_one_or_le
  PreAbstractSimplicialComplex.IsTopWeight.eq_of_eigen_one
  eq_of_eigen_one
  PreAbstractSimplicialComplex.edgeOperator_const_half
  PreAbstractSimplicialComplex.IsTopWeight.not_isLeast_half
  PreAbstractSimplicialComplex.IsTopWeight.exists_extremal_edge_of_isLeast
  PreAbstractSimplicialComplex.eq_mul_of_link_lt
  PreAbstractSimplicialComplex.eq_zero_of_link_lt_of_link_lt
  PreAbstractSimplicialComplex.IsTopWeight.isLeast_zero_iff_det_eq_zero
  PreAbstractSimplicialComplex.IsTopWeight.mem_of_link_neg
  PreAbstractSimplicialComplex.complete_two_isLeast
  PreAbstractSimplicialComplex.twoHeavyWeight_spec
  PreAbstractSimplicialComplex.tetraPendant_sharp
  PreAbstractSimplicialComplex.tetraPendant_root_existsUnique
  PreAbstractSimplicialComplex.tetraPendant_root_strictMono
  PreAbstractSimplicialComplex.tetraPendant_root_of_mem_Ioo
  PreAbstractSimplicialComplex.exists_isLeast_trickling_down_two
  PreAbstractSimplicialComplex.pendantTwo_sharp
  PreAbstractSimplicialComplex.pendantTwo_root
  PreAbstractSimplicialComplex.pendantTwo_isLocalSpectralExpander_iff
  PreAbstractSimplicialComplex.tetraPendantWeight_one_eq_uniformWeight
  PreAbstractSimplicialComplex.octahedron_sharp
  exists_eigen_of_isLeast
  ne_one_of_isLeast
  WalkSecondEigenvalueLE.eigen_of_le
  garland_eigen_iff
  PreAbstractSimplicialComplex.OptimalWeights.isLocalSpectralExpanderOf_complete_neg_one_div_iff
  PreAbstractSimplicialComplex.OptimalWeights.walkSecondEigenvalueLE_linkWeightOf_empty_complete_iff
  PreAbstractSimplicialComplex.OptimalWeights.fin_six_counterexample
  PreAbstractSimplicialComplex.OptimalWeights.forall_isLocalSpectralExpanderOf_complete_eq_mul_uniformWeight_iff
  PreAbstractSimplicialComplex.OptimalWeights.eq_of_pairBalanced_of_le
  PreAbstractSimplicialComplex.OptimalWeights.isLocalSpectralExpanderOf_complete_of_ratio
  PreAbstractSimplicialComplex.OptimalWeights.exists_nhds_uniformWeight_isLocalSpectralExpanderOf
  PreAbstractSimplicialComplex.OptimalWeights.isLocalSpectralExpanderOf_const_mul
  PreAbstractSimplicialComplex.OptimalWeights.exists_isClosed_isLocalSpectralExpanderOf_iff
  PreAbstractSimplicialComplex.OptimalWeights.walkSecondEigenvalueLE_of_le_of_le
  PreAbstractSimplicialComplex.OptimalWeights.faceWeight_tradeWeight_pair
  PreAbstractSimplicialComplex.OptimalWeights.isLocalSpectralExpanderOf_uniformAddTrade
  PreAbstractSimplicialComplex.OptimalWeights.abs_le_of_walkSecondEigenvalueLE_uniformAddTrade
  PreAbstractSimplicialComplex.OptimalWeights.convex_setOf_vertexLinks
  PreAbstractSimplicialComplex.OptimalWeights.convex_setOf_isLocalSpectralExpanderOf_complete
  walkMatrix_vertex_bound
  walkMatrix_edge_bound
  walkMatrix_trace_bound
  walkMatrix_stability
  walkMatrix_eigenvalues_of_sum_sq_eq
  WalkSecondEigenvalueLE.neg_stationary_div_le
  WalkSecondEigenvalueLE.neg_two_mul_weight_div_le
  WalkSecondEigenvalueLE.walkSmallestEigenvalueGE_trace
  WalkSecondEigenvalueLE.sum_sq_div_sub_le
  WalkSecondEigenvalueLE.stationary_le
  WalkSecondEigenvalueLE.weight_div_sqrt_le
  WalkSecondEigenvalueLE.le_stationary
  WalkSecondEigenvalueLE.sub_le_two_mul_weight_div
  WalkSecondEigenvalueLE.weight_pos_of_lt
  WalkSmallestEigenvalueGE.le_neg_stationary_div
  WalkSmallestEigenvalueGE.le_neg_weight_div_sqrt
  starWeight_le_stationary_sharp
  starWeight_stationary_le_sharp
  edgeWeight_sub_le_two_mul_weight_div_sharp
  edgeWeight_weight_div_sqrt_le_sharp
  exists_starWeight_le_stationary_eq
  exists_starWeight_stationary_le_eq
  exists_edgeWeight_sub_le_two_mul_weight_div_eq
  exists_edgeWeight_weight_div_sqrt_le_eq
  starWeight_trace_bound_eq
  edgeWeight_trace_bound_eq
  bipartiteWeight_trace_bound_eq
  starWeight_walkMatrix_spectrum
  edgeWeight_walkMatrix_spectrum
  bipartiteWeight_walkMatrix_spectrum
  walkSecondEigenvalueLE_starWeight_iff_of_le_one
  walkSecondEigenvalueLE_starWeight_iff_of_one_le
  walkSecondEigenvalueLE_edgeWeight_light_iff
  walkSecondEigenvalueLE_edgeWeight_heavy_iff
  walkSecondEigenvalueLE_bipartiteWeight_iff
  EdgeAverageTricklingDown.IsTriangleWeight.walkSecondEigenvalueLE_half_of_one_apex
  EdgeAverageTricklingDown.IsTriangleWeight.walkSecondEigenvalueLE_of_two_type
  PreAbstractSimplicialComplex.exists_isLeast_fan
  PreAbstractSimplicialComplex.faceWeight_fanWeight
  PreAbstractSimplicialComplex.fan_sharp
  PreAbstractSimplicialComplex.fanWeight_eq
  PreAbstractSimplicialComplex.isConnected_fan
  PreAbstractSimplicialComplex.isTopWeight_fan
  PreAbstractSimplicialComplex.IsTopWeight.walkSecondEigenvalueLE_edgePhi_of_two_type
  PreAbstractSimplicialComplex.IsTopWeight.walkSecondEigenvalueLE_half_of_cone_type
  PreAbstractSimplicialComplex.IsTopWeight.walkSecondEigenvalueLE_half_of_one_apex
  PreAbstractSimplicialComplex.IsTopWeight.walkSecondEigenvalueLE_linkWeightOf_of_two_type
  PreAbstractSimplicialComplex.IsTopWeight.walkSecondEigenvalueLE_of_two_type
  PreAbstractSimplicialComplex.IsTopWeight.walkSecondEigenvalueLE_of_two_type_lt_edgeAverage
  PreAbstractSimplicialComplex.linkWeightOf_fan
  PreAbstractSimplicialComplex.mem_fan
  PreAbstractSimplicialComplex.path_ineq
  PreAbstractSimplicialComplex.walkSecondEigenvalueLE_fan_apex
  PreAbstractSimplicialComplex.walkSecondEigenvalueLE_fan_base
  TwoTypeTricklingDown.bernH_neg
  TwoTypeTricklingDown.bernP2_neg
  TwoTypeTricklingDown.bernP3_neg
  TwoTypeTricklingDown.bernP5_pos
  TwoTypeTricklingDown.edgePhi_self
  TwoTypeTricklingDown.edgePhi_two_fifths
  TwoTypeTricklingDown.edgePhi_zero
  TwoTypeTricklingDown.eq_of_triQ_QQQ_eq_zero
  TwoTypeTricklingDown.eq_zero_of_oneQ_PQQ_eq_zero
  TwoTypeTricklingDown.eq_zero_of_triQ_PQQ_eq_zero
  TwoTypeTricklingDown.exists_edgePhi_lt_twoTypeBound
  TwoTypeTricklingDown.exists_good
  TwoTypeTricklingDown.exists_unit_param
  TwoTypeTricklingDown.four_mul_twoTypeN
  TwoTypeTricklingDown.half_le_twoTypeBound
  TwoTypeTricklingDown.local_garland_mean
  TwoTypeTricklingDown.local_prod_mean
  TwoTypeTricklingDown.local_quadratic_mean
  TwoTypeTricklingDown.local_quadratic_of_sum_eq_zero
  TwoTypeTricklingDown.lt_twoTypeBound_of_twoTypeN_neg
  TwoTypeTricklingDown.oneQ_PQQ
  TwoTypeTricklingDown.oneQ_PQQ_nonpos
  TwoTypeTricklingDown.oneQ_swap01
  TwoTypeTricklingDown.oneQ_swap02
  TwoTypeTricklingDown.phiH_eq_bernH
  TwoTypeTricklingDown.phiH_neg
  TwoTypeTricklingDown.phiH_zero
  TwoTypeTricklingDown.sideP2_neg
  TwoTypeTricklingDown.sideP3_neg
  TwoTypeTricklingDown.sideP5_pos
  TwoTypeTricklingDown.six_mul_sum_tri
  TwoTypeTricklingDown.sum_tri_cycle
  TwoTypeTricklingDown.sum_tri_cycle'
  TwoTypeTricklingDown.sum_tri_swap12
  TwoTypeTricklingDown.sum_tri_swap13
  TwoTypeTricklingDown.sum_tri_swap23
  TwoTypeTricklingDown.triQ_PQQ
  TwoTypeTricklingDown.triQ_PQQ_nonpos
  TwoTypeTricklingDown.triQ_QQQ
  TwoTypeTricklingDown.triQ_QQQ_nonpos
  TwoTypeTricklingDown.triQ_swap01
  TwoTypeTricklingDown.triQ_swap02
  TwoTypeTricklingDown.twoType_package
  TwoTypeTricklingDown.twoTypeBound_le_edgePhi
  TwoTypeTricklingDown.twoTypeBound_le_of_twoTypeN_nonneg
  TwoTypeTricklingDown.twoTypeBound_lt_edgeAverage
  TwoTypeTricklingDown.twoTypeBound_lt_of_twoTypeN_pos
  TwoTypeTricklingDown.twoTypeBound_self
  TwoTypeTricklingDown.twoTypeBound_two_fifths
  TwoTypeTricklingDown.twoTypeBound_zero
  TwoTypeTricklingDown.twoTypeDelta_nonneg
  TwoTypeTricklingDown.twoTypeMult_aP
  TwoTypeTricklingDown.twoTypeMult_pqqF
  TwoTypeTricklingDown.twoTypeMult_pqqS
  TwoTypeTricklingDown.twoTypeMult_pqqU
  TwoTypeTricklingDown.twoTypeMult_pqqX
  TwoTypeTricklingDown.twoTypeMult_qqqD
  TwoTypeTricklingDown.twoTypeMult_qqqS
  TwoTypeTricklingDown.TwoTypeMultipliers.Good.aP_nonneg
  TwoTypeTricklingDown.TwoTypeMultipliers.Good.pqqF_neg
  TwoTypeTricklingDown.TwoTypeMultipliers.Good.pqqS_neg
  TwoTypeTricklingDown.TwoTypeMultipliers.Good.pqqU_neg
  TwoTypeTricklingDown.TwoTypeMultipliers.Good.pqqX_eq
  TwoTypeTricklingDown.TwoTypeMultipliers.Good.qqqD_neg
  TwoTypeTricklingDown.TwoTypeMultipliers.Good.qqqS_nonpos
  TwoTypeTricklingDown.twoTypeN_edgePhi
  TwoTypeTricklingDown.twoTypeN_half
  TwoTypeTricklingDown.twoTypeN_pos_of_lt
