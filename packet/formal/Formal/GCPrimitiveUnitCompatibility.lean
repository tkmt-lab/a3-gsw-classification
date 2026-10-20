import Formal.GCPrimitiveInterior
import Formal.GCPrimitiveIntersection
import Formal.GCUnitSurfaceSpec

/-! Local compatibility with the already formalized l=1 surface charts.
This does not identify a general primitive global quotient. -/
namespace R002.GCPrimitive

theorem interior_l1 (k : ℕ) (p : Lattice) :
    Interior k 1 p ↔ GCUnitSurfaceSpec.interior k p := by
  dsimp [Interior,a,b,c,norm,GCUnitSurfaceSpec.interior]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;>
    exact ⟨by nlinarith,by nlinarith,by nlinarith⟩

theorem closed_l1 (k : ℕ) (p : Lattice) :
    Closed k 1 p ↔ GCUnitSurfaceSpec.closed k p := by
  dsimp [Closed,a,b,c,norm,GCUnitSurfaceSpec.closed]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;>
    exact ⟨by nlinarith,by nlinarith,by nlinarith⟩

theorem unit_l1 (p q : Lattice) : Unit p q ↔ GCUnitSurfaceSpec.unit p q := by
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [direction,GCUnitSurfaceSpec.unit] <;> ring
  · rintro (h | h | h | h | h | h)
    · exact ⟨0,by ext <;> simp [direction,h.1,h.2]⟩
    · exact ⟨3,by ext <;> simp [direction,h.1,h.2] <;> ring⟩
    · exact ⟨1,by ext <;> simp [direction,h.1,h.2]⟩
    · exact ⟨4,by ext <;> simp [direction,h.1,h.2] <;> ring⟩
    · exact ⟨5,by ext <;> simp [direction,h.1,h.2] <;> ring⟩
    · exact ⟨2,by ext <;> simp [direction,h.1,h.2] <;> ring⟩

theorem turn_l1 (k : ℕ) (p : Lattice) : turn k 1 p=GCUnitSurfaceSpec.turn k p := by
  ext <;> dsimp [turn,GCUnitSurfaceSpec.turn] <;> ring

theorem opposite_l1 (k : ℕ) (p : Lattice) :
    opposite k 1 p=GCUnitSurfaceSpec.opposite k p := rfl

/-- The first cut row disappears at l=1 because its integer height range is empty. -/
theorem first_cut_empty_l1 (k : ℤ) (p : Lattice) : ¬ Cut k 1 p 0 := by
  intro h
  have hb := cut_height k 1 p 0 h
  norm_num [width,eval] at hb
  omega

end R002.GCPrimitive
