import Formal.GCUnitPath
import Formal.GCUnitGeometry
import Formal.StandardAxiomGate

/-! Final dependency checks for the bounded l=1 prototype. The build wrapper
elaborates this file afresh even when the library build hits its cache. -/
standard_axioms
  R002.Icosahedron.faceVertex_injective
  R002.Icosahedron.mate_involutive
  R002.Icosahedron.mate_other_face
  R002.Icosahedron.mate_reverses
  R002.Icosahedron.five_corners
  R002.Icosahedron.turn_preserves_vertex
  R002.Icosahedron.turn_five
  R002.Icosahedron.turn_no_early_return
  R002.Icosahedron.turn_covers_vertex
  R002.Icosahedron.faces_connected
  R002.Icosahedron.parent_euler
  R002.GCUnit.parent_degree
  R002.GCUnit.corner_degree
  R002.GCUnit.unit_width_path
  R002.GCUnit.Geometry.inside_iff
  R002.GCUnit.Geometry.coord_inside
  R002.GCUnit.Geometry.coord_injective
  R002.GCUnit.Geometry.coord_surjective
  R002.GCUnit.Geometry.edge_OA
  R002.GCUnit.Geometry.edge_OB
  R002.GCUnit.Geometry.edge_AB
  R002.GCUnit.Geometry.chartTurn_coord
  R002.GCUnit.Geometry.chartAdj_iff

#print axioms R002.GCUnit.unit_width_path
#print axioms R002.GCUnit.Geometry.chartAdj_iff
#print axioms R002.Icosahedron.faces_connected
