import Formal.GCTwoStartOrbits
import Formal.GCParentRotationAction
import Formal.GCNonprimitiveInvariant
import Formal.StandardAxiomGate

/-! Primitive all-start reduction and nonprimitive preparation. No classification or absence claim. -/
standard_axioms
  R002.Icosahedron.Rotation
  R002.Icosahedron.rotationFaces
  R002.Icosahedron.rotationLabels
  R002.Icosahedron.inverseRotation
  R002.Icosahedron.rotateDart
  R002.Icosahedron.rotateLabel
  R002.Icosahedron.rotate_root
  R002.Icosahedron.rotate_next
  R002.Icosahedron.rotate_mate
  R002.Icosahedron.rotate_turn
  R002.Icosahedron.rotate_labels
  R002.Icosahedron.rotate_inverse
  R002.Icosahedron.inverse_rotate
  R002.Icosahedron.rotate_transitive
  R002.Icosahedron.rotate_identity
  R002.Icosahedron.labels_bijective
  R002.Icosahedron.dartRotation
  R002.Icosahedron.rotation_distinct
  R002.Icosahedron.rotation_card
  R002.GCPrimitive.unframe_add
  R002.GCPrimitive.unframe_corner_add
  R002.GCPrimitive.frame_shift_cancel
  R002.GCPrimitive.unframe_unit
  R002.GCPrimitiveSurface.rotatePoint
  R002.GCPrimitiveSurface.rotateRaw
  R002.GCPrimitiveSurface.rotateRaw_corner
  R002.GCPrimitiveSurface.rotateRaw_position
  R002.GCPrimitiveSurface.rotateRaw_inverse
  R002.GCPrimitiveSurface.rotateRaw_right_inverse
  R002.GCPrimitiveSurface.rotateRaw_glue
  R002.GCPrimitiveSurface.rotateRaw_respects
  R002.GCPrimitiveSurface.rotateVertex
  R002.GCPrimitiveSurface.rotateVertex_vertex
  R002.GCPrimitiveSurface.rotationEquiv
  R002.GCPrimitiveSurface.rotateRaw_across
  R002.GCPrimitiveSurface.rotateRaw_edge
  R002.GCPrimitiveSurface.rotateVertex_adj
  R002.GCPrimitiveSurface.rotationGraphIso
  R002.GCPrimitiveSurface.rotationGraphIso_apply
  R002.Icosahedron.dartMove
  R002.Icosahedron.followWord
  R002.Icosahedron.rootWord
  R002.Icosahedron.rootWord_covers
  R002.Icosahedron.rotate_move
  R002.Icosahedron.rotate_word
  R002.Icosahedron.rotate_compose
  R002.GCPrimitiveSurface.rotateRaw_compose
  R002.GCPrimitiveSurface.rotateRaw_identity
  R002.GCPrimitiveSurface.rotateVertex_compose
  R002.GCPrimitiveSurface.rotateVertex_identity
  R002.GCPrimitiveSurface.parent
  R002.GCPrimitiveSurface.fan
  R002.GCPrimitiveSurface.parent_turn
  R002.GCPrimitiveSurface.parent_turn_iterate
  R002.GCPrimitiveSurface.fan_adj_parent
  R002.GCPrimitiveSurface.fanPoint_injective
  R002.GCPrimitiveSurface.fan_injective
  R002.GCPrimitiveSurface.fan_turn_adj
  R002.GCPrimitiveSurface.thirdDart
  R002.GCPrimitiveSurface.thirdDart_parent
  R002.GCPrimitiveSurface.thirdDart_distinct
  R002.GCPrimitiveSurface.fan_third_adj
  R002.GCPrimitiveSurface.startTriangle
  R002.GCPrimitiveSurface.start_parent_degree
  R002.GCPrimitiveSurface.start_fan_degree
  R002.GCPrimitiveSurface.Start
  R002.GCPrimitiveSurface.parametrizedStart
  R002.GCPrimitiveSurface.common_exhaust
  R002.GCPrimitiveSurface.orderedTriangle_ext
  R002.GCPrimitiveSurface.parametrizedStart_injective
  R002.GCPrimitiveSurface.parametrizedStart_surjective
  R002.GCPrimitiveSurface.startsEquiv
  R002.GCPrimitiveSurface.all_starts_card
  R002.GCPrimitiveSurface.mapTriangle
  R002.GCPrimitiveSurface.mapStart
  R002.GCPrimitiveSurface.rotate_parent
  R002.GCPrimitiveSurface.rotate_fan
  R002.GCPrimitiveSurface.rotate_turn_iterate
  R002.GCPrimitiveSurface.rotate_third
  R002.GCPrimitiveSurface.rotate_startTriangle
  R002.GCPrimitiveSurface.rotate_start
  R002.GCPrimitiveSurface.same_rotation_orbit_iff
  R002.GCPrimitiveSurface.representative
  R002.GCPrimitiveSurface.exactly_two_start_orbits
  R002.GCPrimitiveSurface.sixty_distinct_graph_rotations
  R002.GCPrimitiveSurface.each_orbit_card
  R002.GCPrimitiveSurface.PathFromTriangle
  R002.GCPrimitiveSurface.map_path_from
  R002.GCPrimitiveSurface.map_path_from_iff
  R002.GCPrimitiveSurface.all_paths_iff_two_starts
  R002.GCPrimitiveSurface.challenge_paths_iff_two_starts
  R002.GCNonprimitive.rot_scaled_iff
  R002.GCNonprimitive.rotN_scaled_iff
  R002.GCNonprimitive.corner_scaled
  R002.GCNonprimitive.cornerAt_scaled
  R002.GCNonprimitive.scaled_sub
  R002.GCNonprimitive.add_scaled_iff
  R002.GCNonprimitive.glue_translation_scaled
  R002.GCNonprimitive.samePoint_scaled_iff
  R002.GCNonprimitive.eqv_scaled_iff
  R002.GCNonprimitive.scaledVertex
  R002.GCNonprimitive.scaledVertex_vtx
  R002.GCNonprimitive.edgePoint
  R002.GCNonprimitive.edge_slices
  R002.GCNonprimitive.edgePoint_closed
  R002.GCNonprimitive.edgePoint_not_interior
  R002.GCNonprimitive.edgePoint_not_corner
  R002.GCNonprimitive.edgePoint_missing_from_primitive_raw
  R002.GCNonprimitive.edgeSite
  R002.GCNonprimitive.unimodular_row_not_scaled

#check R002.GCPrimitiveSurface.all_starts_card
#print axioms R002.GCPrimitiveSurface.all_starts_card
#check R002.GCPrimitiveSurface.rotationGraphIso
#print axioms R002.GCPrimitiveSurface.rotationGraphIso
#check R002.GCPrimitiveSurface.rotateVertex_compose
#print axioms R002.GCPrimitiveSurface.rotateVertex_compose
#check R002.GCPrimitiveSurface.exactly_two_start_orbits
#print axioms R002.GCPrimitiveSurface.exactly_two_start_orbits
#check R002.GCPrimitiveSurface.all_paths_iff_two_starts
#print axioms R002.GCPrimitiveSurface.all_paths_iff_two_starts
#check R002.GCPrimitiveSurface.challenge_paths_iff_two_starts
#print axioms R002.GCPrimitiveSurface.challenge_paths_iff_two_starts
#check R002.GCNonprimitive.scaledVertex
#print axioms R002.GCNonprimitive.scaledVertex
#check R002.GCNonprimitive.edgePoint_missing_from_primitive_raw
#print axioms R002.GCNonprimitive.edgePoint_missing_from_primitive_raw
#check R002.GCNonprimitive.unimodular_row_not_scaled
#print axioms R002.GCNonprimitive.unimodular_row_not_scaled
