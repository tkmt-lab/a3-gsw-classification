import Formal.GCPrimitiveSurfaceCorners

/-! Rational segment convexity, encoded with integer homogeneous coordinates. -/
namespace R002.GCPrimitive

def Rhombus (k l : ℤ) (p : Lattice) : Prop :=
  0≤a k l p ∧ a k l p≤norm k l ∧
  0≤a k l p+b k l p ∧ a k l p+b k l p≤norm k l

theorem rhombus_is_two_faces (k l : ℤ) (p : Lattice) :
    Rhombus k l p ↔ Closed k l p ∨ Closed k l (opposite k l p) := by
  simp only [Rhombus,Closed,(opposite_slices k l p).1,
    (opposite_slices k l p).2.1,(opposite_slices k l p).2.2,c]
  omega

def segmentNumerator (p q : Lattice) (w m : ℤ) : Lattice :=
  ((w-m)*p.1+m*q.1,(w-m)*p.2+m*q.2)

theorem segment_slices (k l : ℤ) (p q : Lattice) (w m : ℤ) :
    a k l (segmentNumerator p q w m)=(w-m)*a k l p+m*a k l q ∧
    b k l (segmentNumerator p q w m)=(w-m)*b k l p+m*b k l q := by
  dsimp [a,b,segmentNumerator]
  constructor <;> ring

theorem weighted_interval (t u v w m : ℤ) (hu : 0≤u ∧ u≤t) (hv : 0≤v ∧ v≤t)
    (hm : 0≤m) (hmw : m≤w) : 0≤(w-m)*u+m*v ∧ (w-m)*u+m*v≤w*t := by
  have hw : 0≤w-m := by omega
  constructor
  · exact add_nonneg (mul_nonneg hw hu.1) (mul_nonneg hm hv.1)
  · have h1 := mul_nonneg hw (show 0≤t-u by omega)
    have h2 := mul_nonneg hm (show 0≤t-v by omega)
    nlinarith

/-- Every rational point of the segment remains in the developed rhombus.
For w>0 these are the rhombus inequalities after division by w. -/
theorem homogeneous_rhombus_convex (k l : ℤ) (p q : Lattice) (w m : ℤ)
    (hp : Rhombus k l p) (hq : Rhombus k l q) (hm : 0≤m) (hmw : m≤w) :
    0≤a k l (segmentNumerator p q w m) ∧
    a k l (segmentNumerator p q w m)≤w*norm k l ∧
    0≤a k l (segmentNumerator p q w m)+b k l (segmentNumerator p q w m) ∧
    a k l (segmentNumerator p q w m)+b k l (segmentNumerator p q w m)≤w*norm k l := by
  rw [(segment_slices k l p q w m).1,(segment_slices k l p q w m).2]
  have ha := weighted_interval _ _ _ w m ⟨hp.1,hp.2.1⟩ ⟨hq.1,hq.2.1⟩ hm hmw
  have hs := weighted_interval _ _ _ w m hp.2.2 hq.2.2 hm hmw
  exact ⟨ha.1,ha.2,by nlinarith [hs.1],by nlinarith [hs.2]⟩

end R002.GCPrimitive
