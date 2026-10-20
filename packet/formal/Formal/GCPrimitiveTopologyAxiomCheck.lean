import Formal.GCPrimitiveDecision
import Formal.GCChallengeQuotient
import Formal.StandardAxiomGate

/-! Every new proof and executable-free definition is checked transitively.
The independent challenge main is absent, not an axiom available to these proofs. -/
standard_axioms
  R002.GCPrimitiveSurface.neighborFace_injective
  R002.GCPrimitiveSurface.direction_injective
  R002.GCPrimitiveSurface.landing_position_injective
  R002.GCPrimitiveSurface.stepNeighbor
  R002.GCPrimitiveSurface.stepNeighbor_landing
  R002.GCPrimitiveSurface.stepNeighbor_bijective
  R002.GCPrimitiveSurface.ordinaryNeighborsEquiv
  R002.GCPrimitiveSurface.ordinary_neighbor_card
  R002.GCPrimitiveSurface.parentNeighbor
  R002.GCPrimitiveSurface.parentNeighbor_bijective
  R002.GCPrimitiveSurface.parentNeighborsEquiv
  R002.GCPrimitiveSurface.incident_card
  R002.GCPrimitiveSurface.parent_neighbor_card
  R002.GCPrimitiveSurface.all_neighbor_card
  R002.GCPrimitiveSurface.locallyFinite
  R002.GCPrimitiveSurface.graph_degree
  R002.GCPrimitive.frame_next_corner
  R002.GCPrimitive.frame_third_corner
  R002.GCPrimitive.unit_opposite_iff
  R002.GCPrimitive.unit_swap_opposite
  R002.GCPrimitive.norm_gt_step
  R002.GCPrimitive.opposite_third_no_unit
  R002.GCPrimitiveSurface.ordinary_raw_adj_iff
  R002.GCPrimitiveSurface.parent_point_adj_iff
  R002.GCPrimitiveSurface.no_parent_parent
  R002.GCPrimitiveSurface.same_face_adj_iff_unit
  R002.GCPrimitiveSurface.shared_corners
  R002.GCPrimitiveSurface.corner_seam_unit
  R002.GCPrimitiveSurface.ordinary_seam_adj_iff
  R002.GCPrimitiveSurface.parent_seam_adj_iff
  R002.GCPrimitiveSurface.corners_no_seam_unit
  R002.GCPrimitiveSurface.seam_adj_iff_unit
  R002.GCPrimitive.right_sector_positive_x
  R002.GCPrimitive.left_sector_negative_x
  R002.GCPrimitive.outside_02_no_unit
  R002.GCPrimitive.outside_distinct_no_unit
  R002.GCPrimitiveSurface.neighbor_faces_not_adjacent
  R002.GCPrimitiveSurface.distinct_neighbor_no_adj
  R002.GCPrimitiveSurface.onFace_neighbor_adj_iff
  R002.GCPrimitiveSurface.landing_adj_iff_unit
  R002.GCPrimitiveSurface.unit_translate
  R002.GCPrimitiveSurface.direction_cycle
  R002.GCPrimitiveSurface.cycle_two_distinct
  R002.GCPrimitiveSurface.around
  R002.GCPrimitiveSurface.around_injective
  R002.GCPrimitiveSurface.around_complete
  R002.GCPrimitiveSurface.around_adj
  R002.GCPrimitiveSurface.around_link
  R002.GCPrimitiveSurface.ordinary_two_common
  R002.GCPrimitiveSurface.two_common_neighbors
  R002.GCPrimitiveSurface.SmallTriangle
  R002.GCPrimitiveSurface.smallTriangle_iff_edges
  R002.GCPrimitiveSurface.Triangle
  R002.GCPrimitiveSurface.triangle_iff_edges
  ClaudeChallenge.rot
  ClaudeChallenge.rotN
  ClaudeChallenge.unitVec
  ClaudeChallenge.face
  ClaudeChallenge.corner
  ClaudeChallenge.InTri
  ClaudeChallenge.CornerAt
  ClaudeChallenge.Glue
  ClaudeChallenge.SamePoint
  ClaudeChallenge.vtx
  ClaudeChallenge.StepTo
  ClaudeChallenge.AdjRaw
  ClaudeChallenge.gcGraph
  ClaudeChallenge.deg
  ClaudeChallenge.LiteralPath
  ClaudeChallenge.criterion
  R002.GCChallengeBridge.faceMap
  R002.GCChallengeBridge.cornerMap
  R002.GCChallengeBridge.posMap
  R002.GCChallengeBridge.posInverse
  R002.GCChallengeBridge.faceMap_bijective
  R002.GCChallengeBridge.labels_agree
  R002.GCChallengeBridge.cornerMap_add_one
  R002.GCChallengeBridge.posInverse_posMap
  R002.GCChallengeBridge.posMap_posInverse
  R002.GCChallengeBridge.posMap_injective
  R002.GCChallengeBridge.inTri_iff_closed
  R002.GCChallengeBridge.posMap_closed
  R002.GCChallengeBridge.posInverse_closed
  R002.GCChallengeBridge.corners_agree
  R002.GCChallengeBridge.rawSite
  R002.GCChallengeBridge.rawSite_injective
  R002.GCChallengeBridge.rawSite_surjective
  R002.GCChallengeBridge.siteEquiv
  R002.GCChallengeBridge.affine_unfold
  R002.GCChallengeBridge.challenge_corner_eq
  R002.GCChallengeBridge.challenge_face_injective
  R002.GCChallengeBridge.cornerSite
  R002.GCChallengeBridge.unfold_corner_start
  R002.GCChallengeBridge.unfold_corner_end
  R002.GCChallengeBridge.aligned_glue
  R002.GCChallengeBridge.samePoint_corners
  R002.GCChallengeBridge.rawSite_corner
  R002.GCChallengeBridge.glue_to_samePoint
  R002.GCChallengeBridge.vtx_respects
  R002.GCChallengeBridge.toChallenge
  R002.GCChallengeBridge.toChallenge_vertex
  R002.GCChallengeBridge.toChallenge_surjective
  R002.GCChallengeBridge.literal_path_iff
  R002.GCChallengeBridge.primitive_challenge_degree
  R002.GCChallengeBridge.primitive_literal_path_iff
  R002.GCPrimitiveSurface.encodePoint
  R002.GCPrimitiveSurface.encodePoint_injective
  R002.GCPrimitiveSurface.pointFintype
  R002.GCPrimitiveSurface.vertexFintype
  R002.GCPrimitiveSurface.primitive_finite_decision

#check R002.GCPrimitiveSurface.graph_degree
#print axioms R002.GCPrimitiveSurface.graph_degree

#check R002.GCPrimitiveSurface.two_common_neighbors
#print axioms R002.GCPrimitiveSurface.two_common_neighbors

#check R002.GCPrimitiveSurface.triangle_iff_edges
#print axioms R002.GCPrimitiveSurface.triangle_iff_edges

#check R002.GCPrimitiveSurface.primitive_finite_decision
#print axioms R002.GCPrimitiveSurface.primitive_finite_decision

#check R002.GCChallengeBridge.siteEquiv
#print axioms R002.GCChallengeBridge.siteEquiv

#check R002.GCChallengeBridge.toChallenge_surjective
#print axioms R002.GCChallengeBridge.toChallenge_surjective

#check R002.GCChallengeBridge.literal_path_iff
#print axioms R002.GCChallengeBridge.literal_path_iff
