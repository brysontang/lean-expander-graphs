import Expanders
open SimpleGraph PreAbstractSimplicialComplex
-- fully proved (expect only propext, Classical.choice, Quot.sound)
#print axioms Matrix.IsHermitian.dotProduct_mulVec_le_largest
#print axioms Matrix.IsHermitian.dotProduct_mulVec_le_second
#print axioms Matrix.IsHermitian.exists_orthogonal_second_le
#print axioms SimpleGraph.card_edgeBoundary_le
#print axioms SimpleGraph.isEdgeExpander_iff
#print axioms SimpleGraph.edgeExpansion_le_degree
#print axioms SimpleGraph.abs_le_of_adjMatrix_mulVec_eq
#print axioms SimpleGraph.largestAdjEigenvalue_eq
#print axioms SimpleGraph.dotProduct_adjMatrix_mulVec_le
#print axioms SimpleGraph.exists_sum_eq_zero_secondAdjEigenvalue_mul_le
#print axioms SimpleGraph.spectralGap_mul_le
#print axioms SimpleGraph.exists_eigenvector_secondAdjEigenvalue
#print axioms SimpleGraph.sum_adj_sub_sq_div_two
#print axioms SimpleGraph.isEdgeExpander_spectralGap_div_two
#print axioms SimpleGraph.spectralGap_div_two_le_edgeExpansion
#print axioms SimpleGraph.edgeExpansion_le_sqrt
#print axioms SimpleGraph.cheeger
#print axioms SimpleGraph.walkSecondEigenvalueLE_adjMatrix_iff
#print axioms PreAbstractSimplicialComplex.link_empty
#print axioms PreAbstractSimplicialComplex.link_link
#print axioms PreAbstractSimplicialComplex.linkWeight_symm
#print axioms garland_inequality
#print axioms walkSecondEigenvalueLE_of_garland
#print axioms PreAbstractSimplicialComplex.trickling_down
#print axioms PreAbstractSimplicialComplex.isLocalSpectralExpander_of_trickling_down
-- stated only, or resting on a stated-only theorem (expect sorryAx)
#print axioms SimpleGraph.alon_boppana
#print axioms SimpleGraph.tendsto_regularExpanderFraction
#print axioms SimpleGraph.exists_regular_isEdgeExpander
