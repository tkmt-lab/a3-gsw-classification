import Formal.GCClosedBridge

/-! Global barycentric weights separate closed-site quotient representatives.
All coordinates are integer numerators; no division or primitivity is used. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

def coeff (k l : ℤ) (p : Lattice) (e : Corner) : ℤ :=
  if e = 0 then c k l p else if e = 1 then a k l p else b k l p

def weight (k l : ℤ) (f : Face) (p : Lattice) (v : ParentVertex) : ℤ :=
  ∑ e : Corner, if faceVertex f e = v then coeff k l p e else 0

theorem coeff_nonneg (p : Lattice) (hp : Closed k l p) (e : Corner) :
    0 ≤ coeff k l p e := by
  dsimp [Closed] at hp
  fin_cases e <;> simp [coeff] <;> omega

theorem coeff_sum (p : Lattice) : (∑ e : Corner, coeff k l p e) = norm k l := by
  simp [Fin.sum_univ_three, coeff, c]; ring

theorem weight_at (f : Face) (p : Lattice) (e : Corner) :
    weight k l f p (faceVertex f e) = coeff k l p e := by
  unfold weight
  rw [Finset.sum_eq_single e]
  · simp
  · intro i _ hne
    have hn : faceVertex f i ≠ faceVertex f e := fun h => hne (faceVertex_injective f h)
    simp [hn]
  · simp

theorem weight_absent (f : Face) (p : Lattice) (v : ParentVertex)
    (h : ∀ e, faceVertex f e ≠ v) : weight k l f p v = 0 := by
  simp [weight, h]

theorem weight_nonneg (f : Face) (p : Lattice) (hp : Closed k l p) (v : ParentVertex) :
    0 ≤ weight k l f p v := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact coeff_nonneg p hp e
  · exact le_refl _

theorem coeff_frame (e i : Corner) (p : Lattice) :
    coeff k l (frame k l e p) i = coeff k l p (e+i) := by
  fin_cases e <;> fin_cases i <;>
    simp [coeff, frame, turn_slices]

theorem weight_frame (f : Face) (e : Corner) (p : Lattice) (v : ParentVertex) :
    weight k l f p v=
      ∑ i : Corner, if faceVertex f (e+i) = v then coeff k l (frame k l e p) i else 0 := by
  simp only [coeff_frame]
  fin_cases e <;> simp [weight, Fin.sum_univ_three] <;> ring

theorem seam_zero (d : Dart) (p : Lattice)
    (hp : Closed k l p) (hq : Closed k l (unfold k l d p)) :
    b k l (frame k l d.2 p) = 0 := by
  have h1 := ((closed_frame k l d.2 p).mpr hp).2.1
  have h2 := ((closed_frame k l (mate d).2 _).mpr hq).2.1
  simp only [unfold, frame_unframe, (opposite_slices k l _).2.1] at h2
  omega

theorem weight_on_seam (f : Face) (e : Corner) (p : Lattice)
    (hb : b k l (frame k l e p) = 0) (v : ParentVertex) :
    weight k l f p v = (if faceVertex f e = v then c k l (frame k l e p) else 0)+
      (if faceVertex f (e+1) = v then a k l (frame k l e p) else 0) := by
  rw [weight_frame f e p v]
  simp [Fin.sum_univ_three, coeff, hb]

theorem seam_weights (s t : Site k l) (h : Seam k l s t) (v : ParentVertex) :
    weight k l s.val.1 s.val.2 v = weight k l t.val.1 t.val.2 v := by
  obtain ⟨e, hf, hp⟩ := h
  have hb := seam_zero (s.val.1, e) s.val.2 s.property (hp.symm ▸ t.property)
  have ht : frame k l (mate (s.val.1, e)).2 t.val.2 = opposite k l (frame k l e s.val.2) := by
    rw [← hp, unfold, frame_unframe]
  have hb' : b k l (frame k l (mate (s.val.1, e)).2 t.val.2) = 0 := by
    rw [ht, (opposite_slices k l _).2.1, hb]; ring
  rw [weight_on_seam _ _ _ hb v, hf, weight_on_seam _ _ _ hb' v, ht,
    (mate_reverses (s.val.1, e)).1, (mate_reverses (s.val.1, e)).2,
    (opposite_slices k l _).1, (opposite_slices k l _).2.2]
  dsimp [c]
  rw [hb]
  split_ifs <;> ring

theorem eqv_weights (s t : Site k l) (h : Relation.EqvGen (Seam k l) s t) :
    weight k l s.val.1 s.val.2 = weight k l t.val.1 t.val.2 := by
  induction h with
  | rel s t h => exact funext (seam_weights s t h)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

def vertexWeight : Vertex k l → ParentVertex → ℤ :=
  Quot.lift (fun s => weight k l s.val.1 s.val.2) (fun s t h => eqv_weights s t h)

@[simp] theorem vertexWeight_vtx (s : Site k l) :
    vertexWeight (vtx s) = weight k l s.val.1 s.val.2 := rfl

theorem slices_injective (hk : 0 < k) (hl : 0 ≤ l) (p q : Lattice)
    (ha : a k l p = a k l q) (hb : b k l p = b k l q) : p = q := by
  have hn := norm_pos k l hk hl
  have hx : norm k l*(p.1-q.1) = 0 := by
    dsimp [a, b] at ha hb
    dsimp [GCPrimitive.norm]
    linear_combination k*ha-l*hb
  have hy : norm k l*(p.2-q.2) = 0 := by
    dsimp [a, b] at ha hb
    dsimp [GCPrimitive.norm]
    linear_combination l*ha+(k+l)*hb
  exact Prod.ext (by nlinarith [hx]) (by nlinarith [hy])

theorem weight_injective (hk : 0 < k) (hl : 0 ≤ l) (f : Face) :
    Function.Injective (weight k l f) := by
  intro p q h
  have ha := congrFun h (faceVertex f 1)
  have hb := congrFun h (faceVertex f 2)
  simp only [weight_at, coeff, Fin.isValue, ite_false, ite_true] at ha hb
  exact slices_injective hk hl p q ha hb

theorem same_face_vtx_injective (hk : 0 < k) (hl : 0 ≤ l) (s t : Site k l)
    (hf : s.val.1 = t.val.1) (h : vtx s = vtx t) : s = t := by
  have hw := congrArg vertexWeight h
  change weight k l s.val.1 s.val.2 = weight k l t.val.1 t.val.2 at hw
  rw [← hf] at hw
  exact Subtype.ext (Prod.ext hf (weight_injective hk hl _ hw))

end R002.GCClosed
