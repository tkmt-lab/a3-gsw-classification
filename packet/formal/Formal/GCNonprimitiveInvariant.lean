import Formal.GCParentRotations
import Formal.GCArithmetic

/-! Preparation for the nonprimitive obstruction on the independent closed-site quotient.
This does NOT prove no literal path: degree identification and finite strip development
are explicit remaining obligations. In particular, primitive Raw omits genuine edge sites. -/
namespace R002.GCNonprimitive
open GCPrimitive Icosahedron

theorem rot_scaled_iff (d : ℤ) (p : Lattice) :
    InScaledLattice d (ClaudeChallenge.rot p) ↔ InScaledLattice d p := by
  change (d ∣ -p.2 ∧ d ∣ p.1+p.2) ↔ (d ∣ p.1 ∧ d ∣ p.2)
  constructor
  · rintro ⟨h2,h12⟩
    have hy := dvd_neg.mp h2
    exact ⟨by simpa using dvd_sub h12 hy,hy⟩
  · rintro ⟨h1,h2⟩
    exact ⟨dvd_neg.mpr h2,dvd_add h1 h2⟩

theorem rotN_scaled_iff (d : ℤ) (j : ℕ) (p : Lattice) :
    InScaledLattice d (ClaudeChallenge.rotN j p) ↔ InScaledLattice d p := by
  induction j with
  | zero => rfl
  | succ j ih => exact (rot_scaled_iff d _).trans ih

theorem corner_scaled (d k l : ℤ) (hdk : d ∣ k) (hdl : d ∣ l) (e : Fin 3) :
    InScaledLattice d (ClaudeChallenge.corner k l e) := by
  fin_cases e
  · exact ⟨dvd_zero _,dvd_zero _⟩
  · exact ⟨hdk,hdl⟩
  · exact ⟨dvd_neg.mpr hdl,dvd_add hdk hdl⟩

theorem cornerAt_scaled (d k l : ℤ) (hdk : d ∣ k) (hdl : d ∣ l)
    (f : Fin 20) (v : Fin 12) (p : Lattice) (hp : ClaudeChallenge.CornerAt k l f v p) :
    InScaledLattice d p := by
  obtain ⟨e,_,rfl⟩ := hp
  exact corner_scaled d k l hdk hdl e

theorem scaled_sub (d : ℤ) (p q : Lattice)
    (hp : InScaledLattice d p) (hq : InScaledLattice d q) : InScaledLattice d (p-q) :=
  ⟨dvd_sub hp.1 hq.1,dvd_sub hp.2 hq.2⟩

theorem add_scaled_iff (d : ℤ) (p t : Lattice) (ht : InScaledLattice d t) :
    InScaledLattice d (p+t) ↔ InScaledLattice d p := by
  constructor
  · intro h
    simpa only [add_sub_cancel_right] using scaled_sub d (p+t) t h ht
  · intro h
    exact ⟨dvd_add h.1 ht.1,dvd_add h.2 ht.2⟩

/-- Every shared-edge affine gluing translates by the d-multiple lattice. -/
theorem glue_translation_scaled (d k l : ℤ) (hdk : d ∣ k) (hdl : d ∣ l)
    (g f : Fin 20) (j : ℕ) (t : Lattice) (hg : ClaudeChallenge.Glue k l g f j t) :
    InScaledLattice d t := by
  obtain ⟨_,v,w,_,pa,pb,qa,qb,hpa,_,hqa,_,he,_⟩ := hg
  have hp := (rotN_scaled_iff d j pa).mpr (cornerAt_scaled d k l hdk hdl g v pa hpa)
  have hq := cornerAt_scaled d k l hdk hdl f v qa hqa
  have h := scaled_sub d qa (ClaudeChallenge.rotN j pa) hq hp
  rw [← he,add_sub_cancel_left] at h
  exact h

theorem samePoint_scaled_iff (d k l : ℤ) (hdk : d ∣ k) (hdl : d ∣ l)
    (s t : ClaudeChallenge.Site k l) (h : ClaudeChallenge.SamePoint k l s t) :
    InScaledLattice d s.val.2 ↔ InScaledLattice d t.val.2 := by
  obtain ⟨j,v,hg,he⟩ := h
  rw [← he]
  exact ((add_scaled_iff d _ v (glue_translation_scaled d k l hdk hdl _ _ j v hg)).trans
    (rotN_scaled_iff d j s.val.2)).symm

theorem eqv_scaled_iff (d k l : ℤ) (hdk : d ∣ k) (hdl : d ∣ l)
    (s t : ClaudeChallenge.Site k l) (h : Relation.EqvGen (ClaudeChallenge.SamePoint k l) s t) :
    InScaledLattice d s.val.2 ↔ InScaledLattice d t.val.2 := by
  induction h with
  | rel s t h => exact samePoint_scaled_iff d k l hdk hdl s t h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- A well-defined predicate on the actual independent quotient, with boundary sites included. -/
def scaledVertex (d k l : ℤ) (hdk : d ∣ k) (hdl : d ∣ l) : ClaudeChallenge.Vertex k l → Prop :=
  Quot.lift (fun s => InScaledLattice d s.val.2)
    (fun s t h => propext (eqv_scaled_iff d k l hdk hdl s t h))

@[simp] theorem scaledVertex_vtx (d k l : ℤ) (hdk : d ∣ k) (hdl : d ∣ l)
    (s : ClaudeChallenge.Site k l) :
    scaledVertex d k l hdk hdl (ClaudeChallenge.vtx s) ↔ InScaledLattice d s.val.2 := Iff.rfl

def edgePoint (a b j : ℤ) : Lattice := (j*a,j*b)

theorem edge_slices (d a' b' j : ℤ) :
    a (d*a') (d*b') (edgePoint a' b' j)=d*j*norm a' b' ∧
    b (d*a') (d*b') (edgePoint a' b' j)=0 ∧
    c (d*a') (d*b') (edgePoint a' b' j)=d*(d-j)*norm a' b' := by
  dsimp [a,b,c,GCPrimitive.norm,edgePoint]
  constructor
  · ring
  constructor <;> ring

theorem edgePoint_closed (d a' b' j : ℤ) (ha : 0<a') (hb : 0≤b')
    (hj : 0≤j) (hjd : j≤d) : Closed (d*a') (d*b') (edgePoint a' b' j) := by
  obtain ⟨h1,h2,h3⟩ := edge_slices d a' b' j
  have hn := (norm_pos a' b' ha hb).le
  dsimp [Closed]
  rw [h1,h2,h3]
  exact ⟨mul_nonneg (mul_nonneg (by omega) hj) hn,le_refl _,
    mul_nonneg (mul_nonneg (by omega) (by omega)) hn⟩

theorem edgePoint_not_interior (d a' b' j : ℤ) :
    ¬Interior (d*a') (d*b') (edgePoint a' b' j) := by
  intro h
  have he := (edge_slices d a' b' j).2.1
  have hh := h.2.1
  rw [he] at hh
  omega

theorem edgePoint_not_corner (d a' b' j : ℤ) (ha : 0<a') (hb : 0<b')
    (hj : 0<j) (hjd : j<d) (e : Corner) :
    edgePoint a' b' j≠corner (d*a') (d*b') e := by
  intro h
  have hx := congrArg Prod.fst h
  have hp := mul_pos hj ha
  have hd := mul_pos (show 0<d by omega) hb
  have hlt := mul_lt_mul_of_pos_right hjd ha
  fin_cases e <;> simp [edgePoint,corner,A,B] at hx <;> omega

/-- This generic edge point is in Challenge.Site but has no primitive-Raw representative.
Thus the primitive graph cannot simply be reused with its coprimality assumption deleted. -/
theorem edgePoint_missing_from_primitive_raw (d a' b' j : ℤ) (ha : 0<a') (hb : 0<b')
    (hj : 0<j) (hjd : j<d) (u : GCPrimitiveSurface.Raw (d*a') (d*b')) :
    GCPrimitiveSurface.position u≠edgePoint a' b' j := by
  rcases u with ⟨f,e|p⟩
  · exact Ne.symm (edgePoint_not_corner d a' b' j ha hb hj hjd e)
  · intro h
    exact edgePoint_not_interior d a' b' j (h ▸ p.property)

def edgeSite (d a' b' j : ℤ) (ha : 0<a') (hb : 0≤b') (hj : 0≤j) (hjd : j≤d)
    (f : Fin 20) : ClaudeChallenge.Site (d*a') (d*b') :=
  ⟨(f,edgePoint a' b' j), (GCChallengeBridge.inTri_iff_closed _).mpr
    (edgePoint_closed d a' b' j ha hb hj hjd)⟩

/-- Arithmetic obstruction for a developed odd strip row in any unimodular direction.
Supplying that development from an arbitrary literal surface path is still required. -/
theorem unimodular_row_not_scaled (d t : ℤ) (hd : 2≤d) (u v : Lattice)
    (hdet : u.1*v.2-u.2*v.1=1 ∨ u.1*v.2-u.2*v.1= -1) :
    ¬InScaledLattice d (t*u.1+v.1,t*u.2+v.2) := by
  intro h
  have hh : d ∣ u.1*(t*u.2+v.2)-u.2*(t*u.1+v.1) :=
    dvd_sub (dvd_mul_of_dvd_right h.2 _) (dvd_mul_of_dvd_right h.1 _)
  have he : u.1*(t*u.2+v.2)-u.2*(t*u.1+v.1)=u.1*v.2-u.2*v.1 := by ring
  rw [he] at hh
  have hone : d ∣ 1 := by
    rcases hdet with hdet|hdet
    · rwa [hdet] at hh
    · rw [hdet] at hh
      exact dvd_neg.mp hh
  exact odd_row_not_scaled d 0 hd ⟨hone,dvd_zero _⟩

end R002.GCNonprimitive
