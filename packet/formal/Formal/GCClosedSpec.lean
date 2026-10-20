import Formal.GCChallengeEdges
import Formal.GCNonprimitiveInvariant

/-! Closed charts retain every parent-edge lattice point. No coprimality hypothesis
occurs in the definitions, and no old primitive Raw is used as the vertex type. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive

abbrev Site (k l : ℤ) := {s : Face × Lattice // Closed k l s.2}

def unfold (k l : ℤ) (d : Dart) (p : Lattice) : Lattice :=
  unframe k l (mate d).2 (opposite k l (frame k l d.2 p))

def Seam (k l : ℤ) (s t : Site k l) : Prop :=
  ∃ e : Corner, t.val.1 = (mate (s.val.1, e)).1 ∧
    unfold k l (s.val.1, e) s.val.2 = t.val.2

abbrev Vertex (k l : ℤ) := Quot (Relation.EqvGen (Seam k l))
def vtx {k l : ℤ} (s : Site k l) : Vertex k l := Quot.mk _ s

def Step (k l : ℤ) (s t : Site k l) : Prop :=
  (s.val.1 = t.val.1 ∧ Unit s.val.2 t.val.2) ∨
  ∃ e : Corner, t.val.1 = (mate (s.val.1, e)).1 ∧
    Unit s.val.2 (unfold k l (mate (s.val.1, e)) t.val.2)

def AdjRaw (k l : ℤ) (v w : Vertex k l) : Prop :=
  ∃ s t : Site k l, vtx s = v ∧ vtx t = w ∧ Step k l s t

def graph (k l : ℤ) : SimpleGraph (Vertex k l) where
  Adj v w := v ≠ w ∧ (AdjRaw k l v w ∨ AdjRaw k l w v)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem unfold_involutive (k l : ℤ) (d : Dart) (p : Lattice) :
    unfold k l (mate d) (unfold k l d p) = p := by
  simp only [unfold, mate_involutive, frame_unframe, opposite_involution, unframe_frame]

theorem unfold_unit (k l : ℤ) (d : Dart) (p q : Lattice) :
    Unit (unfold k l d p) (unfold k l d q) ↔ Unit p q := by
  have hu := frame_unit k l (mate d).2 (unfold k l d p) (unfold k l d q)
  simp only [unfold, frame_unframe] at hu
  exact hu.symm.trans ((unit_opposite_iff k l _ _).trans (frame_unit k l d.2 p q))

theorem seam_symm {k l : ℤ} (s t : Site k l) (h : Seam k l s t) : Seam k l t s := by
  obtain ⟨e, hf, hp⟩ := h
  refine ⟨(mate (s.val.1, e)).2, ?_, ?_⟩
  · rw [hf]; exact (congrArg Prod.fst (mate_involutive (s.val.1, e))).symm
  · rw [hf, ← hp]; exact unfold_involutive k l (s.val.1, e) s.val.2

theorem step_symm {k l : ℤ} (s t : Site k l) (h : Step k l s t) : Step k l t s := by
  rcases h with ⟨hf, hu⟩ | ⟨e, hf, hu⟩
  · exact Or.inl ⟨hf.symm, unit_symm _ _ hu⟩
  · refine Or.inr ⟨(mate (s.val.1, e)).2, ?_, ?_⟩
    · rw [hf]; exact (congrArg Prod.fst (mate_involutive (s.val.1, e))).symm
    · rw [hf, mate_involutive]
      have hh := (unfold_unit k l (s.val.1, e) _ _).mpr hu
      have he := unfold_involutive k l (mate (s.val.1, e)) t.val.2
      rw [mate_involutive] at he
      rw [he] at hh
      exact unit_symm _ _ hh

end R002.GCClosed
