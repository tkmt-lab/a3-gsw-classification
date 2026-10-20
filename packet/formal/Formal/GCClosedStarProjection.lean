import Formal.GCClosedCanonical

/-! A linear map from global barycentric weights develops all four charts in
one face star. This proves position uniqueness even for boundary representatives. -/
namespace R002.GCClosed
open Icosahedron GCPrimitive
variable {k l : ℤ}

def starLabel (f : Face) : Fin 6 → ParentVertex := ![
  faceVertex f 0, faceVertex f 1, faceVertex f 2,
  faceVertex (mate (f, 0)).1 ((mate (f, 0)).2+2),
  faceVertex (mate (f, 1)).1 ((mate (f, 1)).2+2),
  faceVertex (mate (f, 2)).1 ((mate (f, 2)).2+2)]

theorem starLabel_injective : ∀ f, Function.Injective (starLabel f) := by decide +kernel

def starPosition (k l : ℤ) : Fin 6 → Lattice := ![
  (0, 0), A k l, B k l, A k l-B k l, A k l+B k l, B k l-A k l]

def parentPlace (k l : ℤ) (f : Face) (v : ParentVertex) : Lattice :=
  ∑ i : Fin 6, if starLabel f i = v then starPosition k l i else 0

theorem parentPlace_at (f : Face) (i : Fin 6) :
    parentPlace k l f (starLabel f i) = starPosition k l i := by
  unfold parentPlace
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hne
    have hn : starLabel f j ≠ starLabel f i := fun h => hne (starLabel_injective f h)
    simp [hn]
  · simp

theorem parentPlace_face (f : Face) (e : Corner) :
    parentPlace k l f (faceVertex f e) = corner k l e := by
  have hh := parentPlace_at (k:=k) (l:=l) f (Fin.castLE (by decide : 3 ≤ 6) e)
  fin_cases e <;> simpa [starLabel, starPosition, corner] using hh

def neighborIndex (e m i : Corner) : Fin 6 :=
  if i = m then Fin.castLE (by decide : 3 ≤ 6) (e+1)
  else if i = m+1 then Fin.castLE (by decide : 3 ≤ 6) e else Fin.natAdd 3 e

theorem neighbor_label : ∀ (f : Face) (e i : Corner),
    starLabel f (neighborIndex e (mate (f, e)).2 i) = faceVertex (mate (f, e)).1 i := by
  decide +kernel

theorem neighbor_position (e m i : Corner) :
    starPosition k l (neighborIndex e m i) = unframe k l e (opposite k l (frame k l m (corner k l i))) := by
  fin_cases e <;> fin_cases m <;> fin_cases i <;>
    ext <;> simp [starPosition, neighborIndex, unframe, frame, opposite, corner, A, B, GCPrimitive.turn]
      <;> ring

theorem parentPlace_neighbor (f : Face) (e i : Corner) :
    parentPlace k l f (faceVertex (mate (f, e)).1 i) = unfold k l (mate (f, e)) (corner k l i) := by
  rw [← neighbor_label f e i, parentPlace_at, neighbor_position]
  simp only [unfold, mate_involutive]

def project (k l : ℤ) (f : Face) (w : ParentVertex → ℤ) : Lattice :=
  ∑ v : ParentVertex, w v • parentPlace k l f v

theorem weight_sum (f : Face) (p : Lattice) (F : ParentVertex → Lattice) :
    (∑ v : ParentVertex, weight k l f p v • F v)=
      ∑ e : Corner, coeff k l p e • F (faceVertex f e) := by
  simp only [weight, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  congr 1
  funext e
  simp

theorem coeff_position_sum (p : Lattice) :
    (∑ e : Corner, coeff k l p e • corner k l e) = norm k l • p := by
  ext <;> simp [Fin.sum_univ_three, coeff, corner, A, B, a, b, c, GCPrimitive.norm,
    Prod.smul_mk, smul_eq_mul] <;> ring

theorem project_face (f : Face) (p : Lattice) :
    project k l f (weight k l f p) = norm k l • p := by
  rw [project, weight_sum]
  simp_rw [parentPlace_face]
  exact coeff_position_sum p

theorem coeff_unfold_sum (d : Dart) (p : Lattice) :
    (∑ e : Corner, coeff k l p e • unfold k l d (corner k l e)) = norm k l • unfold k l d p := by
  rcases d with ⟨f, m⟩
  simp only [unfold]
  generalize (mate (f, m)).2 = e
  fin_cases m <;> fin_cases e <;>
    ext <;> simp [Fin.sum_univ_three, coeff, unfold, unframe, frame, opposite,
      corner, A, B, a, b, c, GCPrimitive.norm, GCPrimitive.turn, Prod.smul_mk, smul_eq_mul] <;> ring

theorem project_neighbor (f : Face) (e : Corner) (p : Lattice) :
    project k l f (weight k l (mate (f, e)).1 p) = norm k l • unfold k l (mate (f, e)) p := by
  rw [project, weight_sum]
  simp_rw [parentPlace_neighbor]
  exact coeff_unfold_sum _ p

def Landing (f : Face) (q : Lattice) (v : Vertex k l) : Prop :=
  (∃ s : Site k l, s.val.1 = f ∧ s.val.2 = q ∧ vtx s = v) ∨
  ∃ (e : Corner) (s : Site k l), s.val.1 = (mate (f, e)).1 ∧
    unfold k l (mate (f, e)) s.val.2 = q ∧ vtx s = v

theorem landing_project (f : Face) (q : Lattice) (v : Vertex k l) (h : Landing f q v) :
    project k l f (vertexWeight v) = norm k l • q := by
  rcases h with ⟨s, hf, hp, rfl⟩ | ⟨e, s, hf, hp, rfl⟩
  · change project k l f (weight k l s.val.1 s.val.2) = _
    rw [hf, hp, project_face]
  · change project k l f (weight k l s.val.1 s.val.2) = _
    rw [hf, project_neighbor, hp]

theorem landing_position_injective (hk : 0 < k) (hl : 0 ≤ l) (f : Face)
    (p q : Lattice) (v : Vertex k l) (hp : Landing f p v) (hq : Landing f q v) : p = q := by
  have he := (landing_project f p v hp).symm.trans (landing_project f q v hq)
  have hx := congrArg (fun z : Lattice => z.1) he
  have hy := congrArg (fun z : Lattice => z.2) he
  have hn := norm_pos k l hk hl
  change norm k l*p.1 = norm k l*q.1 at hx
  change norm k l*p.2 = norm k l*q.2 at hy
  exact Prod.ext (by nlinarith) (by nlinarith)

end R002.GCClosed
