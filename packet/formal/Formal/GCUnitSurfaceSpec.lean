import Formal.IcosahedronGluing
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Standalone specification of the discrete l=1 chart quotient.
Only the literal fixed-parent table is imported from the research development.
No array, neighbour certificate, path or classification definition is imported.
Coordinates use the 60-degree triangular-lattice basis. k is at least 2 in
all comparison theorems. This specifies a discrete mesh, not a topological
classification of its continuous realization. -/
namespace R002.GCUnitSurfaceSpec
open Icosahedron

abbrev Lattice := ℤ × ℤ

def interior (k : ℕ) (p : Lattice) : Prop :=
  0 < ((k:ℤ)+1)*p.1+p.2 ∧ 0 < -p.1+(k:ℤ)*p.2 ∧
    (k:ℤ)*p.1+((k:ℤ)+1)*p.2 < (k:ℤ)*(k:ℤ)+(k:ℤ)+1

/-- The closed parent triangle, for checking that no boundary lattice points are omitted. -/
def closed (k : ℕ) (p : Lattice) : Prop :=
  0 ≤ ((k:ℤ)+1)*p.1+p.2 ∧ 0 ≤ -p.1+(k:ℤ)*p.2 ∧
    (k:ℤ)*p.1+((k:ℤ)+1)*p.2 ≤ (k:ℤ)*(k:ℤ)+(k:ℤ)+1

/-- The three corners and the strictly interior lattice points, before gluing. -/
abbrev Raw (k : ℕ) := Face × (Corner ⊕ {p : Lattice // interior k p})

/-- Glue the start of each directed edge to the end of its oppositely directed mate.
For l=1 primitive sides have no other lattice vertices. -/
def Glue (k : ℕ) (u v : Raw k) : Prop :=
  ∃ d : Dart, u=(d.1,.inl d.2) ∧ v=((mate d).1,.inl ((mate d).2+1))

abbrev Vertex (k : ℕ) := Quotient (Relation.EqvGen.setoid (Glue k))

def vertex {k : ℕ} (u : Raw k) : Vertex k := Quotient.mk _ u

def corner (k : ℕ) : Corner → Lattice := ![(0,0),((k:ℤ),1),(-1,(k:ℤ)+1)]

def position {k : ℕ} (u : Raw k) : Lattice :=
  match u.2 with
  | .inl e => corner k e
  | .inr p => p.1

def unit (p q : Lattice) : Prop :=
  (q.1=p.1+1 ∧ q.2=p.2) ∨ (q.1=p.1-1 ∧ q.2=p.2) ∨
  (q.1=p.1 ∧ q.2=p.2+1) ∨ (q.1=p.1 ∧ q.2=p.2-1) ∨
  (q.1=p.1+1 ∧ q.2=p.2-1) ∨ (q.1=p.1-1 ∧ q.2=p.2+1)

def turn (k : ℕ) (p : Lattice) : Lattice := ((k:ℤ)-p.1-p.2,p.1+1)

def frame (k : ℕ) (e : Corner) (p : Lattice) : Lattice :=
  if e=0 then p else if e=1 then turn k (turn k p) else turn k p

def opposite (k : ℕ) (p : Lattice) : Lattice := ((k:ℤ)-p.1,1-p.2)

/-- Face interiors own within-face edges; each seam is owned by its smaller face. -/
inductive Owner where
  | face : Face → Owner
  | seam : Dart → Owner

def validOwner : Owner → Prop
  | .face _ => True
  | .seam d => d.1.val < (mate d).1.val

/-- Develop the two faces of a seam into one triangular lattice chart. -/
def developed {k : ℕ} (o : Owner) (u : Raw k) : Option Lattice :=
  match o with
  | .face f => if u.1=f then some (position u) else none
  | .seam d =>
      if u.1=d.1 then some (frame k d.2 (position u))
      else if u.1=(mate d).1 then
        some (opposite k (frame k (mate d).2 (position u))) else none

/-- Only strictly interior vertices use a seam edge; corner edges have a face owner. -/
def OwnsPair {k : ℕ} : Owner → Raw k → Raw k → Prop
  | .face f, u, v => u.1=f ∧ v.1=f
  | .seam d, u, v => u.1=d.1 ∧ v.1=(mate d).1 ∧
      (∃ p, u.2=Sum.inr p) ∧ (∃ q, v.2=Sum.inr q)

def OwnedEdge {k : ℕ} (o : Owner) (u v : Raw k) : Prop :=
  validOwner o ∧ OwnsPair o u v ∧
    ∃ p q, developed o u=some p ∧ developed o v=some q ∧ unit p q

/-- A quotient edge is a unit segment in an owning chart, in either orientation. -/
def Adj {k : ℕ} (x y : Vertex k) : Prop :=
  x≠y ∧ ∃ o u v, vertex u=x ∧ vertex v=y ∧ (OwnedEdge o u v ∨ OwnedEdge o v u)

def graph (k : ℕ) : SimpleGraph (Vertex k) where
  Adj := Adj
  symm := ⟨by
    rintro x y ⟨hne,o,u,v,hx,hy,h⟩
    exact ⟨hne.symm,o,v,u,hy,hx,h.elim Or.inr Or.inl⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A small triangle is an equilateral unit triangle in an owning developed chart.
A seam triangle has interior vertices on both sides; a corner representative,
if present, is taken from the smaller face. This excludes duplicate face owners. -/
def OwnedTriangle {k : ℕ} (o : Owner) (u : Fin 3 → Raw k) : Prop :=
  validOwner o ∧
  (match o with
   | .face f => ∀ i, (u i).1=f
   | .seam d =>
       (∃ i p, u i=(d.1,.inr p)) ∧ (∃ j q, u j=((mate d).1,.inr q)) ∧
       ∀ i e, (u i).2=.inl e → (u i).1=d.1) ∧
  ∃ p : Fin 3 → Lattice, (∀ i, developed o (u i)=some (p i)) ∧
    unit (p 0) (p 1) ∧ unit (p 1) (p 2) ∧ unit (p 2) (p 0)

def Triangle {k : ℕ} (v : Fin 3 → Vertex k) : Prop :=
  Function.Injective v ∧ ∃ o u, (∀ i, vertex (u i)=v i) ∧ OwnedTriangle o u

end R002.GCUnitSurfaceSpec
