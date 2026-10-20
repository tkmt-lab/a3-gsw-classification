import Formal.GCChallengeTransport
import Formal.StandardAxiomGate

/-! Full primitive comparator bridge. No independent main or arithmetic classification premise
is asserted by the gate. All new definitions and theorems are checked transitively. -/
standard_axioms
  R002.GCChallengeBridge.rotN_reduced
  R002.GCChallengeBridge.affine_unique
  R002.GCChallengeBridge.cornerMap_bijective
  R002.GCChallengeBridge.pair_oriented
  R002.GCChallengeBridge.two_labels_mate
  R002.GCChallengeBridge.frame_posMap
  R002.GCChallengeBridge.unfold_posMap
  R002.GCChallengeBridge.oriented_affine_normal
  R002.GCChallengeBridge.glue_normal
  R002.GCChallengeBridge.seam_equal_vertices
  R002.GCChallengeBridge.samePoint_vertex
  R002.GCChallengeBridge.fromChallenge
  R002.GCChallengeBridge.fromChallenge_toChallenge
  R002.GCChallengeBridge.toChallenge_injective
  R002.GCChallengeBridge.challengeVertexEquiv
  R002.GCChallengeBridge.direction_mem
  R002.GCChallengeBridge.mem_direction
  R002.GCChallengeBridge.unit_list_iff
  R002.GCChallengeBridge.posMap_unit
  R002.GCChallengeBridge.seam_glue
  R002.GCChallengeBridge.same_face_step
  R002.GCChallengeBridge.seam_step
  R002.GCChallengeBridge.step_reflects
  R002.GCChallengeBridge.rawEdge_steps
  R002.GCChallengeBridge.adjRaw_reflects
  R002.GCChallengeBridge.toChallenge_adj_iff
  R002.GCChallengeBridge.challengeGraphIso
  R002.GCChallengeBridge.challengeGraphIso_apply
  R002.GCChallengeBridge.iso_degree
  R002.GCChallengeBridge.iso_literal_path
  R002.GCChallengeBridge.challenge_degree
  R002.GCChallengeBridge.challenge_degrees_five_six
  R002.GCChallengeBridge.challenge_literal_path_iff
  R002.GCChallengeBridge.challenge_has_path_iff
  R002.GCChallengeBridge.primitive_comparator
  R002.GCChallengeBridge.iso_two_common_neighbors
  R002.GCChallengeBridge.challenge_two_common_neighbors
  R002.GCChallengeBridge.challengeFintype
  R002.GCChallengeBridge.challenge_finite_decision

#check R002.GCChallengeBridge.toChallenge_injective
#print axioms R002.GCChallengeBridge.toChallenge_injective
#check R002.GCChallengeBridge.challengeVertexEquiv
#print axioms R002.GCChallengeBridge.challengeVertexEquiv
#check R002.GCChallengeBridge.toChallenge_adj_iff
#print axioms R002.GCChallengeBridge.toChallenge_adj_iff
#check R002.GCChallengeBridge.challengeGraphIso
#print axioms R002.GCChallengeBridge.challengeGraphIso
#check R002.GCChallengeBridge.challenge_degree
#print axioms R002.GCChallengeBridge.challenge_degree
#check R002.GCChallengeBridge.challenge_literal_path_iff
#print axioms R002.GCChallengeBridge.challenge_literal_path_iff
#check R002.GCChallengeBridge.challenge_has_path_iff
#print axioms R002.GCChallengeBridge.challenge_has_path_iff
#check R002.GCChallengeBridge.primitive_comparator
#print axioms R002.GCChallengeBridge.primitive_comparator
#check R002.GCChallengeBridge.challenge_finite_decision
#print axioms R002.GCChallengeBridge.challenge_finite_decision
