import Formal.GCNegCriterion
import Formal.StandardAxiomGate

/-! All three remaining sectors and complete primitive necessity. -/
standard_axioms
  R002.GCNeg.Region
  R002.GCNeg.Atlas
  R002.GCNeg.Atlas.hk
  R002.GCNeg.tiles_cover
  R002.GCNeg.chartPoint
  R002.GCNeg.chartVertex
  R002.GCNeg.chart_degree
  R002.GCNeg.chart_landing
  R002.GCNeg.chart_adjacent
  R002.GCNeg.stripTile
  R002.GCNeg.stripTile_interior
  R002.GCNeg.stripTile_active
  R002.GCNeg.stripVertex
  R002.GCNeg.stripVertex_eq_chart
  R002.GCNeg.strip_degree
  R002.GCNeg.strip_landing
  R002.GCNeg.strip_adjacent
  R002.GCNeg.strip_neighbor_injective
  R002.GCNeg.rectangle_zero
  R002.GCNeg.closed_interior_of_no_coarse
  R002.GCNeg.compAtlas
  R002.GCNeg.comp_return_local
  R002.GCNeg.comp_return_dart
  R002.GCNeg.comp_return_vertex
  R002.GCNeg.comp_no_challenge_path
  R002.GCNeg.phase3
  R002.GCNeg.compatible_rotate
  R002.GCNeg.phase3_compatible
  R002.GCNeg.phase3_zero
  R002.GCNeg.comp_wrap
  R002.GCNeg.comp_wrap_rev
  R002.GCNeg.comp_terminal
  R002.GCNeg.comp_terminal_rev
  R002.GCNeg.comp_cap12
  R002.GCNeg.comp_cap21
  R002.GCNeg.comp_cap23
  R002.GCNeg.comp_cap32
  R002.GCNeg.comp_cap34
  R002.GCNeg.comp_cap43
  R002.GCNeg.compDart
  R002.GCNeg.comp_dart_top
  R002.GCNeg.comp_dart_lower
  R002.GCNeg.comp_dart_reg0
  R002.GCNeg.comp_dart_reg1
  R002.GCNeg.comp_dart_cap0
  R002.GCNeg.comp_dart_cap1
  R002.GCNeg.index_up
  R002.GCNeg.index_down
  R002.GCNeg.comp_reg0
  R002.GCNeg.comp_reg1
  R002.GCNeg.comp_seams
  R002.GCNeg.Rule
  R002.GCNeg.interior_residue
  R002.GCNeg.large_no_path
  R002.GCNeg.double_no_path
  R002.GCNeg.primitive_criterion_necessary
  R002.GCNeg.primitive_negative
  R002.GCNeg.S_bounds
  R002.GCNeg.top_tile
  R002.GCNeg.MinusActive
  R002.GCNeg.minus_active
  R002.GCNeg.chi_above
  R002.GCNeg.chi_below
  R002.GCNeg.chi_step
  R002.GCNeg.chi_prev
  R002.GCNeg.minus_seams
  R002.GCNeg.plusAtlas
  R002.GCNeg.minusAtlas
  R002.GCNeg.psi_source_index
  R002.GCNeg.chi_source_index
  R002.GCNeg.base_plus0
  R002.GCNeg.base_plus1
  R002.GCNeg.base_minus
  R002.GCNeg.psi_position
  R002.GCNeg.chi_position
  R002.GCNeg.plus_bounds
  R002.GCNeg.minus_bounds
  R002.GCNeg.plus_no_coarse
  R002.GCNeg.minus_no_coarse
  R002.GCNeg.plus_top
  R002.GCNeg.plus_lower
  R002.GCNeg.plus_reg
  R002.GCNeg.plus_cap0
  R002.GCNeg.plus_cap1
  R002.GCNeg.minus_top
  R002.GCNeg.minus_lower
  R002.GCNeg.minus_initial
  R002.GCNeg.minus_upper
  R002.GCNeg.minus_bottom
  R002.GCNeg.minus_cap0
  R002.GCNeg.minus_cap1
  R002.GCNeg.same_symm
  R002.GCNeg.plus_same
  R002.GCNeg.minus_same
  R002.GCNeg.plus_no_challenge_path
  R002.GCNeg.minus_no_challenge_path
  R002.GCNeg.phasePsi
  R002.GCNeg.phaseChi
  R002.GCNeg.psi_zero
  R002.GCNeg.chi_zero
  R002.GCNeg.psi_compatible
  R002.GCNeg.chi_compatible
  R002.GCNeg.psi_wrap
  R002.GCNeg.psi_wrap_rev
  R002.GCNeg.psi_terminal
  R002.GCNeg.psi_terminal_rev
  R002.GCNeg.gDart
  R002.GCNeg.hDart
  R002.GCNeg.psi_caps
  R002.GCNeg.minusBase
  R002.GCNeg.chi_seams
  R002.GCNeg.chi_initial
  R002.GCNeg.chi_terminal
  R002.GCNeg.chi_caps
  R002.GCNeg.minus_diag
  R002.GCNeg.plusDart
  R002.GCNeg.minusDart
  R002.GCNeg.psi_index_up
  R002.GCNeg.psi_index_down
  R002.GCNeg.PlusActive
  R002.GCNeg.plus_active
  R002.GCNeg.plus_seams
  R002.GCNeg.Same
  R002.GCNeg.same_of_charts
  R002.GCNeg.rotated_position
  R002.GCNeg.no_G_path
  R002.GCNeg.no_H_path
  R002.GCNeg.plus_slices
  R002.GCNeg.plus_source_tile
  R002.GCNeg.plus_source_dart0
  R002.GCNeg.plus_source_dart1
  R002.GCNeg.minus_source_dart
  R002.GCNeg.plus_local0
  R002.GCNeg.plus_local1
  R002.GCNeg.minus_local
  R002.GCNeg.zigzag_region
  R002.GCNeg.start_local
  R002.GCNeg.start_face
  R002.GCNeg.start_interior
  R002.GCNeg.second_local
  R002.GCNeg.second_interior
  R002.GCNeg.trace
  R002.GCNeg.trace_zero
  R002.GCNeg.trace_strip
  R002.GCNeg.trace_one
  R002.GCNeg.trace_two
  R002.GCNeg.trace_degree
  R002.GCNeg.trace_root_degree
  R002.GCNeg.trace_adjacent
  R002.GCNeg.trace_skip
  R002.GCNeg.trace_no_backtrack
  R002.GCNeg.trace_forced
  R002.GCNeg.no_path_of_repeat
  R002.GCNeg.no_challenge_of_repeats

#check R002.GCNeg.comp_no_challenge_path
#print axioms R002.GCNeg.comp_no_challenge_path
#check R002.GCNeg.plus_no_challenge_path
#print axioms R002.GCNeg.plus_no_challenge_path
#check R002.GCNeg.minus_no_challenge_path
#print axioms R002.GCNeg.minus_no_challenge_path
#check R002.GCNeg.primitive_criterion_necessary
#print axioms R002.GCNeg.primitive_criterion_necessary
#check R002.GCNeg.primitive_negative
#print axioms R002.GCNeg.primitive_negative
#check R002.GCNeg.plus_source_tile
#print axioms R002.GCNeg.plus_source_tile
#check R002.GCNeg.rectangle_zero
#print axioms R002.GCNeg.rectangle_zero
#check R002.GCNeg.no_G_path
#print axioms R002.GCNeg.no_G_path
#check R002.GCNeg.no_H_path
#print axioms R002.GCNeg.no_H_path
