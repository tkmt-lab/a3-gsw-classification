import Formal.GCUnitDegree
import Formal.GCUnitGeometry
import Formal.ForcedContinuation
import Mathlib.Tactic

/-! Local links of the unit-width array graph. The six neighbours are literal
vertices, not an assumed rotation system. -/
namespace R002.GCUnit
open Icosahedron Geometry

variable {n : ℕ}

def across (f : Face) (e : Corner) (i : ℕ) (hi : i ≤ n) : Vertex n :=
  .inr ((mate (f,e)).1, Point.edge n (mate (f,e)).2 i hi)

/-- Clockwise order S, SE, E, NE, NW, W in a face chart. -/
def around (f : Face) (p : Point n) : Fin 6 → Vertex n := by
  have ht := p.total
  exact ![
    if h : 0 < p.y then .inr (f,⟨p.x,p.y-1,p.z+1,by omega⟩)
    else if hx : p.x=0 then .inl (faceVertex f 0)
    else across f 0 (n+1-p.x) (by omega),
    if h : 0 < p.y then .inr (f,⟨p.x+1,p.y-1,p.z,by omega⟩)
    else across f 0 (n-p.x) (by omega),
    if h : 0 < p.z then .inr (f,⟨p.x+1,p.y,p.z-1,by omega⟩)
    else if hy : p.y=0 then .inl (faceVertex f 1)
    else across f 1 (n+1-p.y) (by omega),
    if h : 0 < p.z then .inr (f,⟨p.x,p.y+1,p.z-1,by omega⟩)
    else across f 1 (n-p.y) (by omega),
    if h : 0 < p.x then .inr (f,⟨p.x-1,p.y+1,p.z,by omega⟩)
    else if hz : p.z=0 then .inl (faceVertex f 2)
    else across f 2 (n+1-p.z) (by omega),
    if h : 0 < p.x then .inr (f,⟨p.x-1,p.y,p.z+1,by omega⟩)
    else across f 2 (n-p.z) (by omega)]

theorem cross_normal (f g : Face) (p q : Point n) :
    Cross f p g q ↔ ∃ e : Corner, (mate (f,e)).1=g ∧
      (inverseRotateAt e p).y=0 ∧ (inverseRotateAt (mate (f,e)).2 q).y=0 ∧
      ((inverseRotateAt e p).x+(inverseRotateAt (mate (f,e)).2 q).x=n ∨
       (inverseRotateAt e p).x+(inverseRotateAt (mate (f,e)).2 q).x=n+1) := by
  have h := normal_seam_iff (n:=n)
  simp only [normal,unit_seam_iff] at h
  simp only [Cross]
  constructor
  · rintro ⟨e,i,j,hi,hj,hg,hp,hq,hs⟩
    exact ⟨e,hg,(h e (mate (f,e)).2 p q).mpr ⟨i,j,hi,hj,hp,hq,hs⟩⟩
  · rintro ⟨e,hg,hh⟩
    obtain ⟨i,j,hi,hj,hp,hq,hs⟩ := (h e (mate (f,e)).2 p q).mp hh
    exact ⟨e,i,j,hi,hj,hg,hp,hq,hs⟩

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem around_adj (f : Face) (p : Point n) (i : Fin 6) :
    (graph n).Adj (.inr (f,p)) (around f p i) := by
  have hp := p.total
  fin_cases i <;> dsimp [around]
  all_goals split_ifs
  all_goals try dsimp only [across]
  all_goals first
    | (apply (graph_adj_patch_patch _ _ _ _ _).mpr
       left; refine ⟨rfl,?_⟩; simp [Point.UnitAdjacent] <;> omega)
    | (change ∃ e : Corner, faceVertex f e=_ ∧ p=Point.corner n e
       first | refine ⟨0,rfl,?_⟩ | refine ⟨1,rfl,?_⟩ | refine ⟨2,rfl,?_⟩
       apply Point.ext <;> simp [Point.corner,Point.edge,Point.rotateAt,Point.rotate] <;> omega)
    | (apply (graph_adj_patch_patch _ _ _ _ _).mpr; right
       first
       | refine ⟨0,p.x,_,by omega,?_,rfl,?_,rfl,?_⟩
       | refine ⟨1,p.y,_,by omega,?_,rfl,?_,rfl,?_⟩
       | refine ⟨2,p.z,_,by omega,?_,rfl,?_,rfl,?_⟩
       all_goals first
         | omega
         | (apply Point.ext <;> simp [Point.edge,Point.rotateAt,Point.rotate] <;> omega))

theorem around_complete (f : Face) (p : Point n) (w : Vertex n)
    (h : (graph n).Adj (.inr (f,p)) w) : ∃ i : Fin 6, around f p i=w := by
  have hp := p.total
  cases w with
  | inl a =>
    obtain ⟨e,he,hp⟩ := h
    rw [hp,← he]
    fin_cases e
    · exact ⟨0,by simp [around,Point.corner,Point.edge,Point.rotateAt,Point.rotate]⟩
    · exact ⟨2,by simp [around,Point.corner,Point.edge,Point.rotateAt,Point.rotate]⟩
    · exact ⟨4,by simp [around,Point.corner,Point.edge,Point.rotateAt,Point.rotate]⟩
  | inr w =>
    rcases w with ⟨g,q⟩
    have hq := q.total
    rcases (graph_adj_patch_patch _ _ _ _ _).mp h with ⟨hf,hu⟩ | hc
    · subst g
      rcases hu with hu | hu | hu | hu | hu | hu
      · refine ⟨1,?_⟩
        simp [around,show 0<p.y by omega,Point.ext_iff]; omega
      · refine ⟨4,?_⟩
        simp [around,show 0<p.x by omega,Point.ext_iff]; omega
      · refine ⟨2,?_⟩
        simp [around,show 0<p.z by omega,Point.ext_iff]; omega
      · refine ⟨5,?_⟩
        simp [around,show 0<p.x by omega,Point.ext_iff]; omega
      · refine ⟨3,?_⟩
        simp [around,show 0<p.z by omega,Point.ext_iff]; omega
      · refine ⟨0,?_⟩
        simp [around,show 0<p.y by omega,Point.ext_iff]; omega
    · obtain ⟨e,i,j,hi,hj,hg,hpe,hqe,hs⟩ := hc
      subst g
      fin_cases e
      · rcases hs with hs | hs
        · have hj' : j=n-i := by omega
          have hi' : 0 ≤ i := by omega
          refine ⟨1,?_⟩
          rw [hpe,hqe]
          simp [around,Point.edge,Point.rotateAt,Point.rotate,across,hj',hi',Nat.ne_of_gt]
        · have hj' : j=n+1-i := by omega
          have hi' : 0 < i := by omega
          refine ⟨0,?_⟩
          rw [hpe,hqe]
          simp [around,Point.edge,Point.rotateAt,Point.rotate,across,hj',hi',Nat.ne_of_gt]
      · rcases hs with hs | hs
        · have hj' : j=n-i := by omega
          have hi' : 0 ≤ i := by omega
          refine ⟨3,?_⟩
          rw [hpe,hqe]
          simp [around,Point.edge,Point.rotateAt,Point.rotate,across,hj',hi',Nat.ne_of_gt]
        · have hj' : j=n+1-i := by omega
          have hi' : 0 < i := by omega
          refine ⟨2,?_⟩
          rw [hpe,hqe]
          simp [around,Point.edge,Point.rotateAt,Point.rotate,across,hj',hi',Nat.ne_of_gt]
      · rcases hs with hs | hs
        · have hj' : j=n-i := by omega
          have hi' : 0 ≤ i := by omega
          refine ⟨5,?_⟩
          rw [hpe,hqe]
          simp [around,Point.edge,Point.rotateAt,Point.rotate,across,hj',hi',Nat.ne_of_gt]
        · have hj' : j=n+1-i := by omega
          have hi' : 0 < i := by omega
          refine ⟨4,?_⟩
          rw [hpe,hqe]
          simp [around,Point.edge,Point.rotateAt,Point.rotate,across,hj',hi',Nat.ne_of_gt]

theorem around_neighbors (f : Face) (p : Point n) (w : Vertex n) :
    (graph n).Adj (.inr (f,p)) w ↔ ∃ i : Fin 6, around f p i=w := by
  constructor
  · exact around_complete f p w
  · rintro ⟨i,rfl⟩
    exact around_adj f p i

end R002.GCUnit
