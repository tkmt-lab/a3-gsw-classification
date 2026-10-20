import Formal.GCClosedChartTransition
import Formal.GCClosedFiniteStrip

/-! Chart motions preserve the strip recurrence and d-lattice predicate. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {d k l : ℤ}

theorem frame_scaled_iff (hdk : d ∣ k) (hdl : d ∣ l) (e : Corner) (p : Lattice) :
    InScaledLattice d (frame k l e p) ↔ InScaledLattice d p := by
  fin_cases e <;> simp [frame, turn_scaled_iff hdk hdl]

theorem unframe_scaled_iff (hdk : d ∣ k) (hdl : d ∣ l) (e : Corner) (p : Lattice) :
    InScaledLattice d (unframe k l e p) ↔ InScaledLattice d p := by
  fin_cases e <;> simp [unframe, turn_scaled_iff hdk hdl]

theorem opposite_scaled_iff (hdk : d ∣ k) (hdl : d ∣ l) (p : Lattice) :
    InScaledLattice d (opposite k l p) ↔ InScaledLattice d p := by
  change (d ∣ k-p.1 ∧ d ∣ l-p.2) ↔ (d ∣ p.1 ∧ d ∣ p.2)
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨by simpa using dvd_sub hdk hx, by simpa using dvd_sub hdl hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨dvd_sub hdk hx, dvd_sub hdl hy⟩

theorem unfold_scaled_iff (hdk : d ∣ k) (hdl : d ∣ l) (e : Dart) (p : Lattice) :
    InScaledLattice d (unfold k l e p) ↔ InScaledLattice d p := by
  unfold unfold
  rw [unframe_scaled_iff hdk hdl, opposite_scaled_iff hdk hdl, frame_scaled_iff hdk hdl]

theorem landing_scaled_iff (hdk : d ∣ k) (hdl : d ∣ l) (f : Face) (p : Lattice)
    (v : Vertex k l) (h : Landing f p v) : Scaled d k l hdk hdl v ↔ InScaledLattice d p := by
  rcases h with ⟨s, _, hp, rfl⟩ | ⟨e, s, _, hp, rfl⟩
  · rw [scaled_vtx, hp]
  · rw [scaled_vtx, ← hp, unfold_scaled_iff hdk hdl]

theorem unfold_next (e : Dart) (a' b' c' : Lattice) :
    unfold k l e (b'+c'-a') = unfold k l e b'+unfold k l e c'-unfold k l e a' := by
  rcases e with ⟨f, i⟩
  simp only [unfold]
  generalize (mate (f, i)).2 = j
  fin_cases i <;> fin_cases j <;>
    ext <;> simp [unframe, frame, opposite, GCPrimitive.turn] <;> ring

structure Motion (d : ℤ) where
  map : Lattice → Lattice
  next : ∀ a b c, map (b+c-a) = map b+map c-map a
  scaled : ∀ p, InScaledLattice d (map p) ↔ InScaledLattice d p

def Motion.identity (d : ℤ) : Motion d := ⟨id, fun _ _ _ => rfl, fun _ => Iff.rfl⟩

def Motion.compose (F G : Motion d) : Motion d where
  map := F.map ∘ G.map
  next := by intro a b c; simp only [Function.comp_apply, G.next, F.next]
  scaled := fun p => (F.scaled (G.map p)).trans (G.scaled p)

def seamMotion (hdk : d ∣ k) (hdl : d ∣ l) (e : Dart) : Motion d :=
  ⟨unfold k l e, unfold_next e, unfold_scaled_iff hdk hdl e⟩

theorem direction_triangle_det : ∀ i j : Fin 6, Unit (direction i) (direction j) →
    (direction j).1*(direction i).2-(direction j).2*(direction i).1 = 1 ∨
    (direction j).1*(direction i).2-(direction j).2*(direction i).1= -1 := by
  unfold GCPrimitive.Unit
  decide +kernel

theorem unit_triangle_det (p q r : Lattice) (hq : Unit p q) (hr : Unit p r) (hqr : Unit q r) :
    (r.1-p.1)*(q.2-p.2)-(r.2-p.2)*(q.1-p.1) = 1 ∨
    (r.1-p.1)*(q.2-p.2)-(r.2-p.2)*(q.1-p.1)= -1 := by
  obtain ⟨i, rfl⟩ := hq
  obtain ⟨j, rfl⟩ := hr
  have hh := (GCPrimitiveSurface.unit_translate p (direction i) (direction j)).mp hqr
  simpa using direction_triangle_det i j hh

theorem direction_other_common : ∀ i j h : Fin 6,
    Unit (direction i) (direction j) → Unit (direction j) (direction i+direction h) →
    direction i+direction h ≠ 0 → direction h = direction j := by
  unfold GCPrimitive.Unit
  decide +kernel

theorem unit_other_common (p q r x : Lattice)
    (hq : Unit p q) (hr : Unit p r) (hqr : Unit q r)
    (hqx : Unit q x) (hrx : Unit r x) (hne : x ≠ p) : x = q+r-p := by
  obtain ⟨i, rfl⟩ := hq
  obtain ⟨j, rfl⟩ := hr
  obtain ⟨h, rfl⟩ := hqx
  have h1 := (GCPrimitiveSurface.unit_translate p (direction i) (direction j)).mp hqr
  have h2 : Unit (direction j) (direction i+direction h) := by
    apply (GCPrimitiveSurface.unit_translate p _ _).mp
    simpa only [add_assoc] using hrx
  have h3 : direction i+direction h ≠ 0 := by
    intro he
    exact hne (by rw [add_assoc, he, add_zero])
  have hh := direction_other_common i j h h1 h2 h3
  rw [hh]
  abel

end R002.GCClosed
