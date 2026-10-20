import Formal.IcosahedronGluing
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! An explicit triangular-patch graph for the l=1 construction. Here n=k-1.
Parent vertices are separate from the strictly interior lattice points of each
face. Geometric identification with a standard GC surface is a separate layer.
No property of the desired path occurs in the graph definition. -/
namespace R002.GCUnit
open Icosahedron

@[ext] structure Point (n : ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  total : x + y + z = n
  deriving DecidableEq

namespace Point
variable {n : ℕ}

def bounded (p : Point n) : Fin (n+1) × Fin (n+1) × Fin (n+1) :=
  (⟨p.x, by have := p.total; omega⟩,
   ⟨p.y, by have := p.total; omega⟩,
   ⟨p.z, by have := p.total; omega⟩)

theorem bounded_injective : Function.Injective (@bounded n) := by
  intro p q h
  have hx := congrArg (fun a => a.1.val) h
  have hy := congrArg (fun a => a.2.1.val) h
  have hz := congrArg (fun a => a.2.2.val) h
  exact Point.ext hx hy hz

noncomputable instance : Fintype (Point n) := Fintype.ofInjective bounded bounded_injective

def rotate (p : Point n) : Point n := ⟨p.z,p.x,p.y, by have := p.total; omega⟩

def rotateAt (e : Corner) (p : Point n) : Point n :=
  if e = 0 then p else if e = 1 then p.rotate else p.rotate.rotate

@[simp] theorem rotate_three (p : Point n) : p.rotate.rotate.rotate = p := by rfl

def edge (n : ℕ) (e : Corner) (i : ℕ) (hi : i ≤ n) : Point n :=
  rotateAt e ⟨i,0,n-i, by omega⟩

def corner (n : ℕ) (e : Corner) : Point n := edge n e 0 (by omega)

def UnitAdjacent (p q : Point n) : Prop :=
  (p.x+1=q.x ∧ p.y=q.y+1 ∧ p.z=q.z) ∨
  (p.x=q.x+1 ∧ p.y+1=q.y ∧ p.z=q.z) ∨
  (p.x+1=q.x ∧ p.y=q.y ∧ p.z=q.z+1) ∨
  (p.x=q.x+1 ∧ p.y=q.y ∧ p.z+1=q.z) ∨
  (p.x=q.x ∧ p.y+1=q.y ∧ p.z=q.z+1) ∨
  (p.x=q.x ∧ p.y=q.y+1 ∧ p.z+1=q.z)

theorem unitAdjacent_symm (p q : Point n) : UnitAdjacent p q → UnitAdjacent q p := by
  rintro (h | h | h | h | h | h)
  · exact Or.inr (Or.inl ⟨h.1.symm,h.2.1.symm,h.2.2.symm⟩)
  · exact Or.inl ⟨h.1.symm,h.2.1.symm,h.2.2.symm⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1.symm,h.2.1.symm,h.2.2.symm⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨h.1.symm,h.2.1.symm,h.2.2.symm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1.symm,h.2.1.symm,h.2.2.symm⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1.symm,h.2.1.symm,h.2.2.symm⟩))))

theorem unitAdjacent_irrefl (p : Point n) : ¬ UnitAdjacent p p := by
  simp only [UnitAdjacent]; omega

def nearX (n : ℕ) (hn : 1 ≤ n) : Point n := ⟨1,0,n-1,by omega⟩
def nearY (n : ℕ) (hn : 1 ≤ n) : Point n := ⟨0,1,n-1,by omega⟩

theorem edge_injective (e : Corner) (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
    edge n e i hi = edge n e j hj ↔ i=j := by
  fin_cases e <;> simp [edge,rotateAt,rotate,Point.ext_iff] <;> omega

theorem corner_injective (hn : 1 ≤ n) : Function.Injective (corner n) := by
  intro e d h
  have hx := congrArg Point.x h
  have hy := congrArg Point.y h
  fin_cases e <;> fin_cases d <;> try rfl
  all_goals simp [corner,edge,rotateAt,rotate] at hx hy
  all_goals omega

theorem corner_zero_on_edge (hn : 1 ≤ n) (e : Corner) (i : ℕ) (hi : i ≤ n) :
    corner n 0 = edge n e i hi ↔ (e=0 ∧ i=0) ∨ (e=2 ∧ i=n) := by
  fin_cases e <;> simp [corner,edge,rotateAt,rotate,Point.ext_iff] <;> omega

theorem neighbors_corner_zero (hn : 1 ≤ n) (p : Point n) :
    UnitAdjacent (corner n 0) p ↔ p=nearX n hn ∨ p=nearY n hn := by
  have := p.total
  simp [UnitAdjacent,corner,edge,rotateAt,nearX,nearY,Point.ext_iff]
  omega

end Point

abbrev Vertex (n : ℕ) := ParentVertex ⊕ (Face × Point n)

/-- Across one oriented edge, the two boundary rows alternate: i+j=n or n+1. -/
def Cross {n : ℕ} (f : Face) (p : Point n) (g : Face) (q : Point n) : Prop :=
  ∃ e : Corner, ∃ i j : ℕ, ∃ hi : i ≤ n, ∃ hj : j ≤ n,
    (mate (f,e)).1 = g ∧
    p = Point.edge n e i hi ∧ q = Point.edge n (mate (f,e)).2 j hj ∧
    (i+j=n ∨ i+j=n+1)

theorem cross_symm {n : ℕ} {f g : Face} {p q : Point n}
    (h : Cross f p g q) : Cross g q f p := by
  obtain ⟨e,i,j,hi,hj,hf,hp,hq,hs⟩ := h
  have hm : mate (g,(mate (f,e)).2) = (f,e) := by
    rw [← hf]
    exact mate_involutive (f,e)
  refine ⟨(mate (f,e)).2,j,i,hj,hi,?_,hq,?_,?_⟩
  · exact congrArg Prod.fst hm
  · simpa only [hm] using hp
  · omega

/-- Symmetric seam relation, without any decision criterion in its definition. -/
def Adj {n : ℕ} : Vertex n → Vertex n → Prop
  | .inl _, .inl _ => False
  | .inl a, .inr (f,p) => ∃ e : Corner, faceVertex f e = a ∧ p = Point.corner n e
  | .inr (f,p), .inl a => ∃ e : Corner, faceVertex f e = a ∧ p = Point.corner n e
  | .inr (f,p), .inr (g,q) =>
      (f=g ∧ Point.UnitAdjacent p q) ∨ Cross f p g q ∨ Cross g q f p

theorem adj_symm {n : ℕ} : ∀ a b : Vertex n, Adj a b → Adj b a := by
  intro a b h
  cases a with
  | inl a => cases b <;> exact h
  | inr a =>
    rcases a with ⟨f,p⟩
    cases b with
    | inl b => exact h
    | inr b =>
      rcases b with ⟨g,q⟩
      rcases h with ⟨hf,hpq⟩ | h | h
      · exact Or.inl ⟨hf.symm,Point.unitAdjacent_symm p q hpq⟩
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)

theorem adj_irrefl {n : ℕ} : ∀ a : Vertex n, ¬ Adj a a := by
  intro a h
  cases a with
  | inl a => exact h
  | inr a =>
    rcases a with ⟨f,p⟩
    rcases h with ⟨_,h⟩ | h | h
    · exact Point.unitAdjacent_irrefl p h
    all_goals
      obtain ⟨e,i,j,hi,hj,hf,_⟩ := h
      exact mate_other_face (f,e) hf

def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj := Adj
  symm := ⟨adj_symm⟩
  loopless := ⟨adj_irrefl⟩

noncomputable instance (n : ℕ) : DecidableRel (graph n).Adj := Classical.decRel _

@[simp] theorem graph_adj_parent_patch (n : ℕ) (a : ParentVertex) (f : Face) (p : Point n) :
    (graph n).Adj (.inl a) (.inr (f,p)) ↔
      ∃ e : Corner, faceVertex f e = a ∧ p = Point.corner n e := Iff.rfl

@[simp] theorem graph_adj_patch_patch (n : ℕ) (f g : Face) (p q : Point n) :
    (graph n).Adj (.inr (f,p)) (.inr (g,q)) ↔
      (f=g ∧ Point.UnitAdjacent p q) ∨ Cross f p g q := by
  change ((f=g ∧ _) ∨ _ ∨ _) ↔ _
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (cross_symm h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end R002.GCUnit

