import Formal.GCUnitLocal

/-! Uniform local links. Finite parent-table facts are separated from the
coordinate proof; no enumeration of the unbounded parameter n is used. -/
namespace R002.GCUnit
open Icosahedron Geometry
variable {n : ℕ}

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem neighborFace_injective : ∀ f : Face,
    Function.Injective (fun e : Corner => (mate (f,e)).1) := by decide +kernel

theorem neighborFaces_no_edge : ∀ (f : Face) (e d c : Corner), e≠d →
    (mate ((mate (f,e)).1,c)).1 ≠ (mate (f,d)).1 := by decide +kernel

theorem shared_corners : ∀ (f : Face) (e d c : Corner),
    faceVertex (mate (f,d)).1 c=faceVertex f e ↔
      (c=(mate (f,d)).2 ∧ e=d+1) ∨ (c=(mate (f,d)).2+1 ∧ e=d) := by decide +kernel

theorem next_corner_ne : ∀ e : Corner, e+1≠e := by decide +kernel

theorem adj_same_face (f : Face) (p q : Point n) :
    (graph n).Adj (.inr (f,p)) (.inr (f,q)) ↔ Point.UnitAdjacent p q := by
  rw [graph_adj_patch_patch]
  have hc : ¬ Cross f p f q := by
    rintro ⟨e,i,j,hi,hj,hf,_⟩
    exact mate_other_face (f,e) hf
  simp [hc]

theorem edge_unit (e : Corner) (i j : ℕ) (hi : i≤n) (hj : j≤n) :
    Point.UnitAdjacent (Point.edge n e i hi) (Point.edge n e j hj) ↔
      i+1=j ∨ j+1=i := by
  fin_cases e <;> simp [Point.UnitAdjacent,Point.edge,Point.rotateAt,Point.rotate] <;> omega

theorem edge_corner (hn : 1≤n) (e c : Corner) (i : ℕ) (hi : i≤n) :
    Point.edge n e i hi=Point.corner n c ↔ (c=e ∧ i=0) ∨ (c=e+1 ∧ i=n) := by
  fin_cases e <;> fin_cases c <;>
    simp [Point.edge,Point.corner,Point.rotateAt,Point.rotate,Point.ext_iff] <;> omega

theorem inverse_edge (e : Corner) (i : ℕ) (hi : i≤n) :
    inverseRotateAt e (Point.edge n e i hi)=Point.edge n 0 i hi :=
  inverse_rotateAt e _

theorem adj_patch_across (f : Face) (p : Point n) (e : Corner) (j : ℕ) (hj : j≤n) :
    (graph n).Adj (.inr (f,p)) (across f e j hj) ↔
      (inverseRotateAt e p).y=0 ∧
      ((inverseRotateAt e p).x+j=n ∨ (inverseRotateAt e p).x+j=n+1) := by
  dsimp only [across]
  rw [graph_adj_patch_patch,cross_normal]
  have hf := (mate_other_face (f,e)).symm
  simp only [hf,false_and,false_or,(neighborFace_injective f).eq_iff,exists_eq_left,inverse_edge]
  simp [Point.edge,Point.rotateAt]

theorem adj_across_patch (f : Face) (p : Point n) (e : Corner) (j : ℕ) (hj : j≤n) :
    (graph n).Adj (across f e j hj) (.inr (f,p)) ↔
      (inverseRotateAt e p).y=0 ∧
      ((inverseRotateAt e p).x+j=n ∨ (inverseRotateAt e p).x+j=n+1) :=
  ((graph n).adj_comm _ _).trans (adj_patch_across f p e j hj)

theorem adj_across_across (f : Face) (e d : Corner) (i j : ℕ) (hi : i≤n) (hj : j≤n) :
    (graph n).Adj (across f e i hi) (across f d j hj) ↔ e=d ∧ (i+1=j ∨ j+1=i) := by
  by_cases he : e=d
  · subst d
    dsimp only [across]
    rw [adj_same_face,edge_unit]
    simp
  · simp only [he,false_and,iff_false]
    intro h
    rcases (graph_adj_patch_patch _ _ _ _ _).mp h with ⟨hf,_⟩ | hc
    · exact he (neighborFace_injective f hf)
    · obtain ⟨c,a,b,ha,hb,hf,_⟩ := hc
      exact neighborFaces_no_edge f e d c he hf

theorem adj_parent_patch (f : Face) (e : Corner) (p : Point n) :
    (graph n).Adj (.inl (faceVertex f e)) (.inr (f,p)) ↔ p=Point.corner n e := by
  rw [graph_adj_parent_patch]
  simp only [(faceVertex_injective f).eq_iff,exists_eq_left]

theorem adj_patch_parent (f : Face) (e : Corner) (p : Point n) :
    (graph n).Adj (.inr (f,p)) (.inl (faceVertex f e)) ↔ p=Point.corner n e :=
  ((graph n).adj_comm _ _).trans (adj_parent_patch f e p)

theorem adj_parent_parent (a b : ParentVertex) :
    (graph n).Adj (.inl a) (.inl b) ↔ False := Iff.rfl

theorem adj_parent_across (hn : 1≤n) (f : Face) (e d : Corner) (j : ℕ) (hj : j≤n) :
    (graph n).Adj (.inl (faceVertex f e)) (across f d j hj) ↔
      (e=d ∧ j=n) ∨ (e=d+1 ∧ j=0) := by
  dsimp only [across]
  rw [graph_adj_parent_patch]
  simp only [shared_corners,edge_corner hn,or_and_right,and_or_left,exists_or,and_assoc,exists_eq_left]
  have hh := next_corner_ne (mate (f,d)).2
  try simp only [hh,hh.symm,false_and,and_false,false_or,or_false,true_and,and_true]
  tauto

theorem adj_across_parent (hn : 1≤n) (f : Face) (e d : Corner) (j : ℕ) (hj : j≤n) :
    (graph n).Adj (across f d j hj) (.inl (faceVertex f e)) ↔
      (e=d ∧ j=n) ∨ (e=d+1 ∧ j=0) :=
  ((graph n).adj_comm _ _).trans (adj_parent_across hn f e d j hj)

def CycleSix (i j : Fin 6) : Prop := i+1=j ∨ j+1=i

theorem around_link (hn : 1≤n) (f : Face) (p : Point n) (i j : Fin 6) :
    (graph n).Adj (around f p i) (around f p j) ↔ CycleSix i j := by
  have hp := p.total
  fin_cases i <;> fin_cases j <;> dsimp [around]
  all_goals split_ifs
  all_goals simp [-graph_adj_parent_patch,-graph_adj_patch_patch,adj_same_face,adj_patch_across,adj_across_patch,adj_across_across,
    adj_parent_patch,adj_patch_parent,adj_parent_parent,adj_parent_across hn,adj_across_parent hn,
    Point.UnitAdjacent,Point.corner,Point.edge,Point.rotateAt,Point.rotate,inverseRotateAt,
    Point.ext_iff,CycleSix] <;> omega

end R002.GCUnit
