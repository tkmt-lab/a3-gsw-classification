import Formal.GCUnitSurfaceSpec
import Formal.GCUnitGeometry
import Mathlib.Tactic.FinCases

/-! Comparison of the standalone discrete chart quotient with the array model.
Neither the quotient vertex bijection nor its adjacency theorem is a claim
about an independently formalized continuous orbifold. -/
namespace R002.GCUnitSurfaceBridge
open Icosahedron GCUnit

variable {n : ℕ}

theorem interior_iff (p : GCUnitSurfaceSpec.Lattice) :
    GCUnitSurfaceSpec.interior (n+1) p ↔ GCUnit.Geometry.inside ((n:ℤ)+1) p := by
  simp only [GCUnitSurfaceSpec.interior,GCUnit.Geometry.inside,GCUnit.Geometry.norm,Nat.cast_add,Nat.cast_one]

/-- The Raw type includes every integer point of the closed parent triangle. -/
theorem closed_partition (p : GCUnitSurfaceSpec.Lattice) :
    GCUnitSurfaceSpec.closed (n+1) p ↔ GCUnitSurfaceSpec.interior (n+1) p ∨
      ∃ e : Corner, p=GCUnitSurfaceSpec.corner (n+1) e := by
  rcases p with ⟨x,y⟩
  let K : ℤ := (n:ℤ)+1
  let T := K*K+K+1
  let U := (K+1)*x+y
  let V := -x+K*y
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hn0 : (0:ℤ) ≤ n := Nat.cast_nonneg n
  have hsum : U+V=K*x+(K+1)*y := by dsimp [U,V]; ring
  have hT : 0 < T := by dsimp [T]; nlinarith
  have bound : ∀ z : ℤ, 0 ≤ T*z → T*z ≤ T → 0 ≤ z ∧ z ≤ 1 := by
    intro z hz hl
    exact ⟨(mul_nonneg_iff_of_pos_left hT).mp hz,
      le_of_mul_le_mul_left (by simpa using hl) hT⟩
  constructor
  · intro h
    have hh : 0 ≤ U ∧ 0 ≤ V ∧ U+V ≤ T := by
      rw [hsum]
      simpa [GCUnitSurfaceSpec.closed,K,U,V,T] using h
    by_cases hi : 0 < U ∧ 0 < V ∧ U+V < T
    · left
      rw [hsum] at hi
      simpa [GCUnitSurfaceSpec.interior,K,U,V,T] using hi
    right
    have hb : U=0 ∨ V=0 ∨ U+V=T := by omega
    rcases hb with hu | hv | hw
    · have hm : T*(-x)=V := by
        calc
          T*(-x) = V-K*U := by dsimp [T,U,V]; ring
          _ = V := by rw [hu]; ring
      obtain ⟨hx0,hx1⟩ := bound (-x) (by rw [hm]; exact hh.2.1)
        (by rw [hm]; omega)
      have hl : y=-(K+1)*x := by dsimp [U] at hu; linarith
      rcases GCUnit.Geometry.edge_OB K x y hl (by omega) (by omega) with hp | hp
      · exact ⟨0,by simpa [GCUnitSurfaceSpec.corner] using hp⟩
      · exact ⟨2,by simpa [GCUnitSurfaceSpec.corner,K] using hp⟩
    · have hm : T*y=U := by
        calc
          T*y = U+(K+1)*V := by dsimp [T,U,V]; ring
          _ = U := by rw [hv]; ring
      obtain ⟨hy0,hy1⟩ := bound y (by rw [hm]; exact hh.1) (by rw [hm]; omega)
      have hl : x=K*y := by dsimp [V] at hv; linarith
      rcases GCUnit.Geometry.edge_OA K x y hl hy0 hy1 with hp | hp
      · exact ⟨0,by simpa [GCUnitSurfaceSpec.corner] using hp⟩
      · exact ⟨1,by simpa [GCUnitSurfaceSpec.corner,K] using hp⟩
    · have hm : T*(x+y-K)=U := by
        calc
          T*(x+y-K) = U-K*(T-U-V) := by dsimp [T,U,V]; ring
          _ = U := by
            have hh' : T-U-V=0 := by omega
            rw [hh']
            ring
      obtain ⟨hs0,hs1⟩ := bound (x+y-K) (by rw [hm]; exact hh.1) (by rw [hm]; omega)
      have hl : K*x+(K+1)*y=GCUnit.Geometry.norm K := by
        dsimp [U,V,T,GCUnit.Geometry.norm] at *
        linarith
      rcases GCUnit.Geometry.edge_AB K x y hl (by omega) (by omega) with hp | hp
      · exact ⟨1,by simpa [GCUnitSurfaceSpec.corner,K] using hp⟩
      · exact ⟨2,by simpa [GCUnitSurfaceSpec.corner,K] using hp⟩
  · rintro (h | ⟨e,he⟩)
    · exact ⟨h.1.le,h.2.1.le,h.2.2.le⟩
    · rw [he]
      fin_cases e <;> dsimp [GCUnitSurfaceSpec.closed,GCUnitSurfaceSpec.corner]
      all_goals refine ⟨?_,?_,?_⟩ <;> push_cast <;> nlinarith [sq_nonneg (n:ℤ)]

noncomputable def arrayPoint (p : {p : GCUnitSurfaceSpec.Lattice // GCUnitSurfaceSpec.interior (n+1) p}) : Point n :=
  Classical.choose (GCUnit.Geometry.coord_surjective p.val ((interior_iff p.val).mp p.property))

theorem arrayPoint_coord (p : {p : GCUnitSurfaceSpec.Lattice // GCUnitSurfaceSpec.interior (n+1) p}) :
    GCUnit.Geometry.coord (arrayPoint p)=p.val :=
  Classical.choose_spec (GCUnit.Geometry.coord_surjective p.val ((interior_iff p.val).mp p.property))

def rawPoint (p : Point n) : {p : GCUnitSurfaceSpec.Lattice // GCUnitSurfaceSpec.interior (n+1) p} :=
  ⟨GCUnit.Geometry.coord p,(interior_iff _).mpr (GCUnit.Geometry.coord_inside p)⟩

@[simp] theorem array_raw_point (p : Point n) : arrayPoint (rawPoint p)=p := by
  apply GCUnit.Geometry.coord_injective
  exact arrayPoint_coord _

@[simp] theorem raw_array_point (p : {p : GCUnitSurfaceSpec.Lattice // GCUnitSurfaceSpec.interior (n+1) p}) :
    rawPoint (arrayPoint p)=p := by
  apply Subtype.ext
  exact arrayPoint_coord _

noncomputable def rawArray (u : GCUnitSurfaceSpec.Raw (n+1)) : GCUnit.Vertex n :=
  match u.2 with
  | .inl e => .inl (faceVertex u.1 e)
  | .inr p => .inr (u.1,arrayPoint p)

theorem rawArray_glue (u v : GCUnitSurfaceSpec.Raw (n+1)) (h : GCUnitSurfaceSpec.Glue (n+1) u v) :
    rawArray u=rawArray v := by
  obtain ⟨d,rfl,rfl⟩ := h
  exact congrArg Sum.inl (mate_reverses d).2.symm

theorem rawArray_respects (u v : GCUnitSurfaceSpec.Raw (n+1))
    (h : Relation.EqvGen (GCUnitSurfaceSpec.Glue (n+1)) u v) : rawArray u=rawArray v := by
  induction h with
  | rel x y h => exact rawArray_glue x y h
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

noncomputable def toArray : GCUnitSurfaceSpec.Vertex (n+1) → GCUnit.Vertex n :=
  Quotient.lift rawArray rawArray_respects

@[simp] theorem toArray_vertex (u : GCUnitSurfaceSpec.Raw (n+1)) : toArray (GCUnitSurfaceSpec.vertex u)=rawArray u := rfl

theorem corner_turns (k : ℕ) (d : Dart) (m : ℕ) :
    Relation.EqvGen (GCUnitSurfaceSpec.Glue k) (d.1,.inl d.2)
      (((Icosahedron.turn^[m]) d).1,.inl ((Icosahedron.turn^[m]) d).2) := by
  induction m with
  | zero => exact .refl _
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact .trans _ _ _ ih (.rel _ _ ⟨(Icosahedron.turn^[m]) d,rfl,rfl⟩)

theorem rawArray_exact (u v : GCUnitSurfaceSpec.Raw (n+1)) (h : rawArray u=rawArray v) :
    Relation.EqvGen (GCUnitSurfaceSpec.Glue (n+1)) u v := by
  rcases u with ⟨f,e|p⟩ <;> rcases v with ⟨g,d|q⟩
  · have he : faceVertex f e=faceVertex g d := Sum.inl.inj h
    obtain ⟨i,hi⟩ := turn_covers_vertex (f,e) (g,d) he
    have hh := corner_turns (n+1) (f,e) i.val
    simpa only [hi] using hh
  · simp [rawArray] at h
  · simp [rawArray] at h
  · have he := Sum.inr.inj h
    have hf := congrArg Prod.fst he
    have hp := congrArg Prod.snd he
    change arrayPoint p=arrayPoint q at hp
    change f=g at hf
    have hpq : p=q := by
      rw [← raw_array_point p,← raw_array_point q,hp]
    subst g; subst q
    exact .refl _

theorem toArray_injective : Function.Injective (@toArray n) := by
  intro u v
  refine Quotient.inductionOn₂ u v ?_
  intro a b h
  exact Quotient.sound (rawArray_exact a b h)

theorem parent_representative : ∀ a : ParentVertex, ∃ d : Dart, faceVertex d.1 d.2=a := by
  decide +kernel

theorem toArray_surjective : Function.Surjective (@toArray n) := by
  intro v
  cases v with
  | inl a =>
    obtain ⟨d,hd⟩ := parent_representative a
    exact ⟨GCUnitSurfaceSpec.vertex (d.1,.inl d.2),congrArg Sum.inl hd⟩
  | inr v =>
    rcases v with ⟨f,p⟩
    exact ⟨GCUnitSurfaceSpec.vertex (f,.inr (rawPoint p)),by simp [rawArray]⟩

noncomputable def vertexEquiv (n : ℕ) : GCUnitSurfaceSpec.Vertex (n+1) ≃ GCUnit.Vertex n :=
  Equiv.ofBijective toArray ⟨toArray_injective,toArray_surjective⟩

theorem spec_unit_comm (p q : GCUnitSurfaceSpec.Lattice) :
    GCUnitSurfaceSpec.unit p q ↔ GCUnitSurfaceSpec.unit q p := by
  simp only [GCUnitSurfaceSpec.unit]; omega

theorem unit_corner_iff (e : Corner) (p : Point n) :
    GCUnitSurfaceSpec.unit (GCUnitSurfaceSpec.corner (n+1) e) (GCUnit.Geometry.coord p) ↔
      p=Point.corner n e := by
  have hp := p.total
  fin_cases e <;>
    simp [GCUnitSurfaceSpec.unit,GCUnitSurfaceSpec.corner,GCUnit.Geometry.coord,
      Point.corner,Point.edge,Point.rotateAt,Point.rotate,Point.ext_iff] <;> omega

theorem no_unit_corners (e d : Corner) :
    ¬ GCUnitSurfaceSpec.unit (GCUnitSurfaceSpec.corner (n+1) e)
      (GCUnitSurfaceSpec.corner (n+1) d) := by
  fin_cases e <;> fin_cases d <;>
    simp [GCUnitSurfaceSpec.unit,GCUnitSurfaceSpec.corner] <;> omega

theorem frame_coord (e : Corner) (p : Point n) :
    GCUnitSurfaceSpec.frame (n+1) e (GCUnit.Geometry.coord p)=GCUnit.Geometry.normal e p := by
  have hp := p.total
  fin_cases e <;> apply Prod.ext <;>
    simp [GCUnitSurfaceSpec.frame,GCUnitSurfaceSpec.turn,GCUnit.Geometry.normal,
      GCUnit.Geometry.inverseRotateAt,GCUnit.Geometry.coord,Point.rotate] <;> omega

theorem owned_face_iff (f : Face)
    (u v : Corner ⊕ {p : GCUnitSurfaceSpec.Lattice // GCUnitSurfaceSpec.interior (n+1) p}) :
    GCUnitSurfaceSpec.OwnedEdge (.face f) (f,u) (f,v) ↔
      GCUnitSurfaceSpec.unit (GCUnitSurfaceSpec.position (f,u))
        (GCUnitSurfaceSpec.position (f,v)) := by
  simp [GCUnitSurfaceSpec.OwnedEdge,GCUnitSurfaceSpec.validOwner,
    GCUnitSurfaceSpec.OwnsPair,GCUnitSurfaceSpec.developed]

theorem corner_patch (f : Face) (e : Corner) (p : Point n) :
    (graph n).Adj (.inl (faceVertex f e)) (.inr (f,p)) ↔ p=Point.corner n e := by
  rw [graph_adj_parent_patch]
  simp only [(faceVertex_injective f).eq_iff,exists_eq_left]

theorem same_face_unit (f : Face)
    (u v : Corner ⊕ {p : GCUnitSurfaceSpec.Lattice // GCUnitSurfaceSpec.interior (n+1) p}) :
    GCUnitSurfaceSpec.unit (GCUnitSurfaceSpec.position (f,u))
      (GCUnitSurfaceSpec.position (f,v)) ↔
      (graph n).Adj (rawArray (f,u)) (rawArray (f,v)) := by
  cases u with
  | inl e =>
    cases v with
    | inl d =>
      simp only [GCUnitSurfaceSpec.position,rawArray,no_unit_corners]
      rfl
    | inr p =>
      change GCUnitSurfaceSpec.unit (GCUnitSurfaceSpec.corner (n+1) e) p.val ↔ _
      rw [← arrayPoint_coord p,unit_corner_iff]
      exact (corner_patch f e (arrayPoint p)).symm
  | inr p =>
    cases v with
    | inl e =>
      rw [spec_unit_comm]
      change GCUnitSurfaceSpec.unit (GCUnitSurfaceSpec.corner (n+1) e) p.val ↔ _
      rw [← arrayPoint_coord p,unit_corner_iff]
      exact (((graph n).adj_comm _ _).trans (corner_patch f e (arrayPoint p))).symm
    | inr q =>
      change GCUnitSurfaceSpec.unit p.val q.val ↔ _
      rw [← arrayPoint_coord p,← arrayPoint_coord q]
      change GCUnit.Geometry.Unit _ _ ↔ (graph n).Adj (.inr (f,_)) (.inr (f,_))
      rw [GCUnit.Geometry.unit_coord_iff,graph_adj_patch_patch]
      have hc : ¬ Cross f (arrayPoint p) f (arrayPoint q) := by
        rintro ⟨e,i,j,hi,hj,hf,_⟩
        exact mate_other_face (f,e) hf
      simp [hc]

theorem owned_seam_iff (d : Dart) (p q : Point n) :
    GCUnitSurfaceSpec.OwnedEdge (.seam d)
      (d.1,.inr (rawPoint p)) ((mate d).1,.inr (rawPoint q)) ↔
      d.1.val < (mate d).1.val ∧
      GCUnit.Geometry.Unit (GCUnit.Geometry.normal d.2 p)
        (GCUnit.Geometry.seam ((n:ℤ)+1) (GCUnit.Geometry.normal (mate d).2 q)) := by
  have ho := mate_other_face d
  simp [GCUnitSurfaceSpec.OwnedEdge,GCUnitSurfaceSpec.validOwner,
    GCUnitSurfaceSpec.OwnsPair,GCUnitSurfaceSpec.developed,ho,
    GCUnitSurfaceSpec.position,rawPoint,frame_coord,GCUnitSurfaceSpec.unit,
    GCUnitSurfaceSpec.opposite,GCUnit.Geometry.Unit,GCUnit.Geometry.seam]

theorem owned_edge_sound (o : GCUnitSurfaceSpec.Owner) (u v : GCUnitSurfaceSpec.Raw (n+1))
    (h : GCUnitSurfaceSpec.OwnedEdge o u v) : (graph n).Adj (rawArray u) (rawArray v) := by
  cases o with
  | face f =>
    rcases u with ⟨fu,up⟩; rcases v with ⟨fv,vp⟩
    obtain ⟨hu,hv⟩ := h.2.1
    change fu=f at hu; change fv=f at hv
    subst fu; subst fv
    exact (same_face_unit f up vp).mp ((owned_face_iff f up vp).mp h)
  | seam d =>
    rcases u with ⟨fu,up⟩; rcases v with ⟨fv,vp⟩
    obtain ⟨hu,hv,⟨p,hp⟩,⟨q,hq⟩⟩ := h.2.1
    change fu=d.1 at hu; change fv=(mate d).1 at hv
    change up=.inr p at hp; change vp=.inr q at hq
    subst fu; subst fv; subst up; subst vp
    rw [← raw_array_point p,← raw_array_point q] at h
    have hh := ((owned_seam_iff d (arrayPoint p) (arrayPoint q)).mp h).2
    obtain ⟨i,j,hi,hj,hp,hq,hs⟩ :=
      (GCUnit.Geometry.normal_seam_iff d.2 (mate d).2 (arrayPoint p) (arrayPoint q)).mp hh
    exact (graph_adj_patch_patch _ _ _ _ _).mpr
      (Or.inr ⟨d.2,i,j,hi,hj,rfl,hp,hq,hs⟩)

theorem unit_seam_swap (p q : GCUnit.Geometry.Lattice) :
    GCUnit.Geometry.Unit p (GCUnit.Geometry.seam ((n:ℤ)+1) q) ↔
      GCUnit.Geometry.Unit q (GCUnit.Geometry.seam ((n:ℤ)+1) p) := by
  simp only [GCUnit.Geometry.Unit,GCUnit.Geometry.seam]; omega

/-- Every model edge has an owner in the independent chart specification. -/
theorem model_edge_owned (a b : GCUnit.Vertex n) (h : (graph n).Adj a b) :
    ∃ o u v, rawArray u=a ∧ rawArray v=b ∧
      (GCUnitSurfaceSpec.OwnedEdge o u v ∨ GCUnitSurfaceSpec.OwnedEdge o v u) := by
  have parentCase : ∀ (c : ParentVertex) (f : Face) (p : Point n),
      (graph n).Adj (.inl c) (.inr (f,p)) →
      ∃ o u v, rawArray u=.inl c ∧ rawArray v=.inr (f,p) ∧
        GCUnitSurfaceSpec.OwnedEdge o u v := by
    intro c f p hc
    obtain ⟨e,he,hp⟩ := hc
    refine ⟨.face f,(f,.inl e),(f,.inr (rawPoint p)),?_,?_,?_⟩
    · exact congrArg Sum.inl he
    · simp [rawArray]
    · rw [owned_face_iff]
      exact (unit_corner_iff e p).mpr hp
  cases a with
  | inl c =>
    cases b with
    | inl d => exact False.elim h
    | inr b =>
      rcases b with ⟨f,p⟩
      obtain ⟨o,u,v,hu,hv,hh⟩ := parentCase c f p h
      exact ⟨o,u,v,hu,hv,Or.inl hh⟩
  | inr a =>
    rcases a with ⟨f,p⟩
    cases b with
    | inl c =>
      obtain ⟨o,u,v,hu,hv,hh⟩ := parentCase c f p h.symm
      exact ⟨o,v,u,hv,hu,Or.inr hh⟩
    | inr b =>
      rcases b with ⟨g,q⟩
      rcases (graph_adj_patch_patch _ _ _ _ _).mp h with ⟨hf,hpq⟩ | hc
      · subst g
        refine ⟨.face f,(f,.inr (rawPoint p)),(f,.inr (rawPoint q)),by simp [rawArray],
          by simp [rawArray],Or.inl ?_⟩
        rw [owned_face_iff]
        exact (GCUnit.Geometry.unit_coord_iff p q).mpr hpq
      · obtain ⟨e,i,j,hi,hj,hg,hp,hq,hs⟩ := hc
        subst g
        have hu := (GCUnit.Geometry.normal_seam_iff e (mate (f,e)).2 p q).mpr
          ⟨i,j,hi,hj,hp,hq,hs⟩
        by_cases hf : f.val < (mate (f,e)).1.val
        · refine ⟨.seam (f,e),(f,.inr (rawPoint p)),
            ((mate (f,e)).1,.inr (rawPoint q)),by simp [rawArray],by simp [rawArray],Or.inl ?_⟩
          exact (owned_seam_iff (f,e) p q).mpr ⟨hf,hu⟩
        · have hneq := mate_other_face (f,e)
          have hm := mate_involutive (f,e)
          have hf' : (mate (f,e)).1.val < f.val := by
            have hn : (mate (f,e)).1.val ≠ f.val := fun h => hneq (Fin.ext h)
            omega
          refine ⟨.seam (mate (f,e)),(f,.inr (rawPoint p)),
            ((mate (f,e)).1,.inr (rawPoint q)),by simp [rawArray],by simp [rawArray],Or.inr ?_⟩
          have hh := (owned_seam_iff (mate (f,e)) q p).mpr (by
            rw [hm]
            exact ⟨hf',(unit_seam_swap _ _).mp hu⟩)
          simpa only [hm] using hh

theorem graph_adj_iff (u v : GCUnitSurfaceSpec.Vertex (n+1)) :
    (GCUnitSurfaceSpec.graph (n+1)).Adj u v ↔ (graph n).Adj (toArray u) (toArray v) := by
  constructor
  · rintro ⟨hne,o,a,b,ha,hb,h⟩
    have hh : (graph n).Adj (rawArray a) (rawArray b) := h.elim
      (owned_edge_sound o a b) (fun h => (owned_edge_sound o b a h).symm)
    simpa only [← ha,← hb,toArray_vertex] using hh
  · intro h
    obtain ⟨o,a,b,ha,hb,hh⟩ := model_edge_owned _ _ h
    refine ⟨?_,o,a,b,?_,?_,hh⟩
    · intro he
      exact (graph n).loopless.irrefl (toArray u) (he ▸ h)
    · exact toArray_injective ha
    · exact toArray_injective hb

noncomputable def graphIso (n : ℕ) : GCUnitSurfaceSpec.graph (n+1) ≃g graph n where
  toEquiv := vertexEquiv n
  map_rel_iff' := (graph_adj_iff _ _).symm

end R002.GCUnitSurfaceBridge
