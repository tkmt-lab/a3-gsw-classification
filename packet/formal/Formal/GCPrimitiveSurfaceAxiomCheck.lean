import Formal.GCPrimitiveConvexity
import Formal.StandardAxiomGate

/-! Fresh transitive standard-axiom gate for the general discrete surface layer. -/
standard_axioms
  R002.GCPrimitive.integer_strip
  R002.GCPrimitive.no_positive_strip
  R002.GCPrimitive.unit_turn
  R002.GCPrimitive.unit_opposite
  R002.GCPrimitive.unit_symm
  R002.GCPrimitive.unit_ne
  R002.GCPrimitive.oa_right_bound
  R002.GCPrimitive.oa_left_bound
  R002.GCPrimitive.diagonal_right_bound
  R002.GCPrimitive.diagonal_left_bound
  R002.GCPrimitive.exit_width_complete
  R002.GCPrimitive.negative_b_lands
  R002.GCPrimitive.unframe_frame
  R002.GCPrimitive.frame_unframe
  R002.GCPrimitive.frame_injective
  R002.GCPrimitive.closed_frame
  R002.GCPrimitive.interior_frame
  R002.GCPrimitive.interior_unframe
  R002.GCPrimitive.frame_unit
  R002.GCPrimitive.b_frames
  R002.GCPrimitive.outside_has_negative
  R002.GCPrimitive.unit_step_covered
  R002.GCPrimitive.neighbor_unique_negative
  R002.GCPrimitive.adjacent_chart_unique
  R002.GCPrimitive.neighbor_not_closed
  R002.GCPrimitive.corner_closed
  R002.GCPrimitive.corner_not_interior
  R002.GCPrimitive.corner_injective
  R002.GCPrimitive.closed_origin_fan
  R002.GCPrimitiveSurface.canonical_glue
  R002.GCPrimitiveSurface.canonical_respects
  R002.GCPrimitiveSurface.toCanonical_vertex
  R002.GCPrimitiveSurface.corner_turns
  R002.GCPrimitiveSurface.canonical_exact
  R002.GCPrimitiveSurface.toCanonical_injective
  R002.GCPrimitiveSurface.parent_representative
  R002.GCPrimitiveSurface.toCanonical_surjective
  R002.GCPrimitiveSurface.position_closed
  R002.GCPrimitiveSurface.closed_has_raw
  R002.GCPrimitiveSurface.position_injective_in_face
  R002.GCPrimitiveSurface.interior_raw_unique
  R002.GCPrimitiveSurface.same_face_vertex_injective
  R002.GCPrimitiveSurface.onNeighbor_interior
  R002.GCPrimitiveSurface.onFace_closed
  R002.GCPrimitiveSurface.landing_exists
  R002.GCPrimitiveSurface.onNeighbor_unique
  R002.GCPrimitiveSurface.landing_unique
  R002.GCPrimitiveSurface.unit_step_unique_lift
  R002.GCPrimitiveSurface.unit_seam_swap
  R002.GCPrimitiveSurface.across_symm
  R002.GCPrimitiveSurface.rawEdge_symm
  R002.GCPrimitiveSurface.across_ne
  R002.GCPrimitiveSurface.rawEdge_ne
  R002.GCPrimitiveSurface.rawEdge_adj
  R002.GCPrimitiveSurface.landing_is_edge
  R002.GCPrimitiveSurface.across_to_step
  R002.GCPrimitiveSurface.ordinary_adjacency_iff_directions
  R002.GCPrimitiveSurface.six_steps_total
  R002.GCPrimitiveSurface.across_iff_cut
  R002.GCPrimitive.frame_corner
  R002.GCPrimitive.closed_corner_fan
  R002.GCPrimitive.no_internal_lattice_point
  R002.GCPrimitiveSurface.unit_from_corner
  R002.GCPrimitiveSurface.corner_no_across
  R002.GCPrimitiveSurface.parent_adjacency_iff_fans
  R002.GCPrimitive.rhombus_is_two_faces
  R002.GCPrimitive.segment_slices
  R002.GCPrimitive.weighted_interval
  R002.GCPrimitive.homogeneous_rhombus_convex
  R002.GCPrimitiveSurface.vertexEquiv
  R002.GCPrimitiveSurface.graph

#check R002.GCPrimitive.unit_step_covered
#print axioms R002.GCPrimitive.unit_step_covered

#check R002.GCPrimitiveSurface.vertexEquiv
#print axioms R002.GCPrimitiveSurface.vertexEquiv

#check R002.GCPrimitiveSurface.unit_step_unique_lift
#print axioms R002.GCPrimitiveSurface.unit_step_unique_lift

#check R002.GCPrimitiveSurface.ordinary_adjacency_iff_directions
#print axioms R002.GCPrimitiveSurface.ordinary_adjacency_iff_directions

#check R002.GCPrimitiveSurface.six_steps_total
#print axioms R002.GCPrimitiveSurface.six_steps_total

#check R002.GCPrimitiveSurface.parent_adjacency_iff_fans
#print axioms R002.GCPrimitiveSurface.parent_adjacency_iff_fans

#check R002.GCPrimitiveSurface.across_iff_cut
#print axioms R002.GCPrimitiveSurface.across_iff_cut

#check R002.GCPrimitive.homogeneous_rhombus_convex
#print axioms R002.GCPrimitive.homogeneous_rhombus_convex

#check R002.GCPrimitive.no_internal_lattice_point
#print axioms R002.GCPrimitive.no_internal_lattice_point
