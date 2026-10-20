import Formal.GCUnitProperties

/-! Small-triangle charts and their relationship with the quotient edges. -/
namespace R002.GCUnitSurfaceBridge
open Icosahedron GCUnit
variable {n : ℕ}

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem frame_unit (e : Corner) (p q : GCUnitSurfaceSpec.Lattice) :
    GCUnitSurfaceSpec.unit (GCUnitSurfaceSpec.frame (n+1) e p)
      (GCUnitSurfaceSpec.frame (n+1) e q) ↔ GCUnitSurfaceSpec.unit p q := by
  fin_cases e <;> simp [GCUnitSurfaceSpec.frame,GCUnitSurfaceSpec.turn,GCUnitSurfaceSpec.unit] <;> omega

theorem opposite_unit (p q : GCUnitSurfaceSpec.Lattice) :
    GCUnitSurfaceSpec.unit (GCUnitSurfaceSpec.opposite (n+1) p)
      (GCUnitSurfaceSpec.opposite (n+1) q) ↔ GCUnitSurfaceSpec.unit p q := by
  simp only [GCUnitSurfaceSpec.unit,GCUnitSurfaceSpec.opposite]
  omega

theorem opposite_swap (p q : GCUnitSurfaceSpec.Lattice) :
    GCUnitSurfaceSpec.unit p (GCUnitSurfaceSpec.opposite (n+1) q) ↔
      GCUnitSurfaceSpec.unit q (GCUnitSurfaceSpec.opposite (n+1) p) := by
  simp only [GCUnitSurfaceSpec.unit,GCUnitSurfaceSpec.opposite]
  omega

theorem corner_seam_unit (hn : 1≤n) (d e m : Corner) (p : Point n) :
    GCUnitSurfaceSpec.unit
      (GCUnitSurfaceSpec.frame (n+1) d (GCUnitSurfaceSpec.corner (n+1) e))
      (GCUnitSurfaceSpec.opposite (n+1) (Geometry.normal m p)) ↔
      (e=d ∧ p=Point.corner n (m+1)) ∨ (e=d+1 ∧ p=Point.corner n m) := by
  have hp := p.total
  fin_cases d <;> fin_cases e <;> fin_cases m <;>
    simp [GCUnitSurfaceSpec.frame,GCUnitSurfaceSpec.turn,GCUnitSurfaceSpec.corner,
      GCUnitSurfaceSpec.unit,GCUnitSurfaceSpec.opposite,Geometry.normal,
      Geometry.inverseRotateAt,Geometry.coord,Point.corner,Point.edge,
      Point.rotateAt,Point.rotate,Point.ext_iff] <;> omega

theorem corners_no_seam_unit (d e m c : Corner) :
    ¬ GCUnitSurfaceSpec.unit
      (GCUnitSurfaceSpec.frame (n+1) d (GCUnitSurfaceSpec.corner (n+1) e))
      (GCUnitSurfaceSpec.opposite (n+1)
        (GCUnitSurfaceSpec.frame (n+1) m (GCUnitSurfaceSpec.corner (n+1) c))) := by
  fin_cases d <;> fin_cases e <;> fin_cases m <;> fin_cases c <;>
    simp [GCUnitSurfaceSpec.frame,GCUnitSurfaceSpec.turn,GCUnitSurfaceSpec.corner,
      GCUnitSurfaceSpec.unit,GCUnitSurfaceSpec.opposite] <;> omega

theorem parent_opposite (f : Face) (d e : Corner) (p : Point n) :
    (graph n).Adj (.inl (faceVertex f e)) (.inr ((mate (f,d)).1,p)) ↔
      (e=d ∧ p=Point.corner n ((mate (f,d)).2+1)) ∨
      (e=d+1 ∧ p=Point.corner n (mate (f,d)).2) := by
  rw [graph_adj_parent_patch]
  simp only [shared_corners,or_and_right,exists_or,and_assoc,exists_eq_left]
  tauto

theorem seam_unit_iff (hn : 1≤n) (d : Dart)
    (u v : Corner ⊕ {p : GCUnitSurfaceSpec.Lattice // GCUnitSurfaceSpec.interior (n+1) p}) :
    GCUnitSurfaceSpec.unit
      (GCUnitSurfaceSpec.frame (n+1) d.2 (GCUnitSurfaceSpec.position (d.1,u)))
      (GCUnitSurfaceSpec.opposite (n+1)
        (GCUnitSurfaceSpec.frame (n+1) (mate d).2 (GCUnitSurfaceSpec.position ((mate d).1,v)))) ↔
      (graph n).Adj (rawArray (d.1,u)) (rawArray ((mate d).1,v)) := by
  cases u with
  | inl e =>
    cases v with
    | inl c =>
      simp only [GCUnitSurfaceSpec.position,rawArray,corners_no_seam_unit,adj_parent_parent]
    | inr q =>
      change GCUnitSurfaceSpec.unit _ (GCUnitSurfaceSpec.opposite _
        (GCUnitSurfaceSpec.frame _ _ q.val)) ↔ _
      rw [← arrayPoint_coord q,frame_coord]
      dsimp only [GCUnitSurfaceSpec.position]
      rw [corner_seam_unit hn]
      exact (parent_opposite d.1 d.2 e (arrayPoint q)).symm
  | inr p =>
    cases v with
    | inl c =>
      rw [opposite_swap]
      change GCUnitSurfaceSpec.unit _ (GCUnitSurfaceSpec.opposite _
        (GCUnitSurfaceSpec.frame _ _ p.val)) ↔ _
      rw [← arrayPoint_coord p,frame_coord]
      dsimp only [GCUnitSurfaceSpec.position]
      rw [corner_seam_unit hn]
      have hh := parent_opposite (mate d).1 (mate d).2 c (arrayPoint p)
      have hm := mate_involutive d
      simpa only [hm,rawArray] using hh.symm.trans ((graph n).adj_comm _ _)
    | inr q =>
      change GCUnitSurfaceSpec.unit (GCUnitSurfaceSpec.frame (n+1) d.2 p.val)
        (GCUnitSurfaceSpec.opposite (n+1) (GCUnitSurfaceSpec.frame (n+1) (mate d).2 q.val)) ↔
        (graph n).Adj (.inr (d.1,arrayPoint p)) (.inr ((mate d).1,arrayPoint q))
      rw [← arrayPoint_coord p,← arrayPoint_coord q,frame_coord,frame_coord]
      have hf := (mate_other_face d).symm
      rw [graph_adj_patch_patch]
      simp only [hf,false_and,false_or,cross_normal,
        (neighborFace_injective d.1).eq_iff,exists_eq_left]
      change Geometry.Unit _ (Geometry.seam ((n:ℤ)+1) _) ↔ _
      exact Geometry.unit_seam_iff (Geometry.inverseRotateAt d.2 (arrayPoint p))
        (Geometry.inverseRotateAt (mate d).2 (arrayPoint q))

/-- Any two points in a developed chart have a quotient edge exactly when their
coordinates differ by a unit step. No triangle-adjacency hypothesis is assumed. -/
theorem developed_unit_iff (hn : 1≤n) (o : GCUnitSurfaceSpec.Owner)
    (u v : GCUnitSurfaceSpec.Raw (n+1)) (p q : GCUnitSurfaceSpec.Lattice)
    (hu : GCUnitSurfaceSpec.developed o u=some p)
    (hv : GCUnitSurfaceSpec.developed o v=some q) :
    GCUnitSurfaceSpec.unit p q ↔ (graph n).Adj (rawArray u) (rawArray v) := by
  rcases u with ⟨fu,up⟩; rcases v with ⟨fv,vp⟩
  cases o with
  | face f =>
    dsimp only [GCUnitSurfaceSpec.developed] at hu hv
    split_ifs at hu hv
    all_goals try contradiction
    all_goals subst fu; subst fv; cases hu; cases hv
    exact same_face_unit f up vp
  | seam d =>
    dsimp only [GCUnitSurfaceSpec.developed] at hu hv
    split_ifs at hu with hfu hfu <;> split_ifs at hv with hfv hfv
    all_goals try contradiction
    all_goals subst fu; subst fv; cases hu; cases hv
    · exact (frame_unit _ _ _).trans (same_face_unit _ _ _)
    · exact seam_unit_iff hn d up vp
    · exact (spec_unit_comm _ _).trans
        ((seam_unit_iff hn d vp up).trans ((graph n).adj_comm _ _))
    · exact (opposite_unit _ _).trans ((frame_unit _ _ _).trans (same_face_unit _ _ _))

theorem triangle_edges (hn : 1≤n) (v : Fin 3 → GCUnitSurfaceSpec.Vertex (n+1))
    (h : GCUnitSurfaceSpec.Triangle v) :
    (GCUnitSurfaceSpec.graph (n+1)).Adj (v 0) (v 1) ∧
    (GCUnitSurfaceSpec.graph (n+1)).Adj (v 1) (v 2) ∧
    (GCUnitSurfaceSpec.graph (n+1)).Adj (v 2) (v 0) := by
  obtain ⟨hinj,o,u,hu,hvalid,hsupport,p,hp,h01,h12,h20⟩ := h
  have hh : ∀ i j, GCUnitSurfaceSpec.unit (p i) (p j) →
      (GCUnitSurfaceSpec.graph (n+1)).Adj (v i) (v j) := by
    intro i j hij
    rw [← hu i,← hu j,graph_adj_iff,toArray_vertex,toArray_vertex]
    exact (developed_unit_iff hn o (u i) (u j) (p i) (p j) (hp i) (hp j)).mp hij
  exact ⟨hh 0 1 h01,hh 1 2 h12,hh 2 0 h20⟩

end R002.GCUnitSurfaceBridge
