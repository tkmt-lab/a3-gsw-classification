import Formal.GCUnitSurfaceFaces

/-! Every model triangle has one of the specified face or seam charts. -/
namespace R002.GCUnitSurfaceBridge
open Icosahedron GCUnit
open GCUnitSurfaceSpec (Raw Owner Triangle developed vertex)
variable {n : ℕ}

noncomputable def lift (a : GCUnit.Vertex n) : GCUnitSurfaceSpec.Vertex (n+1) :=
  (vertexEquiv n).symm a

@[simp] theorem toArray_lift (a : GCUnit.Vertex n) : toArray (lift a)=a :=
  (vertexEquiv n).apply_symm_apply a

@[simp] theorem lift_raw (u : Raw (n+1)) : lift (rawArray u)=vertex u :=
  (vertexEquiv n).symm_apply_apply (vertex u)

def Supports (o : Owner) (u : Fin 3 → Raw (n+1)) : Prop :=
  match o with
  | .face f => ∀ i, (u i).1=f
  | .seam d =>
      (∃ i p, u i=(d.1,.inr p)) ∧ (∃ j q, u j=((mate d).1,.inr q)) ∧
      ∀ i e, (u i).2=.inl e → (u i).1=d.1

theorem triangle_from_chart (hn : 1≤n) (o : Owner) (u : Fin 3 → Raw (n+1))
    (ho : GCUnitSurfaceSpec.validOwner o) (hs : Supports o u)
    (hf : ∀ i, ∃ p, developed o (u i)=some p)
    (h01 : (graph n).Adj (rawArray (u 0)) (rawArray (u 1)))
    (h12 : (graph n).Adj (rawArray (u 1)) (rawArray (u 2)))
    (h20 : (graph n).Adj (rawArray (u 2)) (rawArray (u 0))) :
    Triangle (fun i => lift (rawArray (u i))) := by
  classical
  have hinj : Function.Injective (fun i => vertex (u i)) := by
    intro i j h
    have hh := congrArg toArray h
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals exfalso
    all_goals first
      | exact h01.ne hh | exact h01.ne hh.symm
      | exact h12.ne hh | exact h12.ne hh.symm
      | exact h20.ne hh | exact h20.ne hh.symm
  let p : Fin 3 → GCUnitSurfaceSpec.Lattice := fun i => Classical.choose (hf i)
  have hp : ∀ i, developed o (u i)=some (p i) := fun i => Classical.choose_spec (hf i)
  have htri : Triangle (fun i => vertex (u i)) :=
    ⟨hinj,o,u,fun _ => rfl,ho,hs,p,hp,
      (developed_unit_iff hn o _ _ _ _ (hp 0) (hp 1)).mpr h01,
      (developed_unit_iff hn o _ _ _ _ (hp 1) (hp 2)).mpr h12,
      (developed_unit_iff hn o _ _ _ _ (hp 2) (hp 0)).mpr h20⟩
  simpa only [lift_raw] using htri

def rot {α : Type*} (v : Fin 3 → α) : Fin 3 → α := fun i => v (i+1)

@[simp] theorem rot_vec {α : Type*} (a b c : α) : rot ![a,b,c]=![b,c,a] := by
  funext i; fin_cases i <;> rfl

theorem triangle_rotate (v : Fin 3 → GCUnitSurfaceSpec.Vertex (n+1))
    (h : Triangle v) : Triangle (rot v) := by
  obtain ⟨hinj,o,u,hu,hvalid,hs,p,hp,h01,h12,h20⟩ := h
  have hri : Function.Injective (fun i : Fin 3 => i+1) := by decide +kernel
  have hidx : ∀ i : Fin 3, (i+2)+1=i := by decide +kernel
  refine ⟨hinj.comp hri,o,rot u,fun i => hu (i+1),hvalid,?_,rot p,fun i => hp (i+1),h12,h20,h01⟩
  cases o with
  | face f => exact fun i => hs (i+1)
  | seam d =>
    obtain ⟨⟨i,a,hi⟩,⟨j,b,hj⟩,hc⟩ := hs
    refine ⟨⟨i+2,a,?_⟩,⟨j+2,b,?_⟩,fun i e => hc (i+1) e⟩
    · simpa only [rot,hidx] using hi
    · simpa only [rot,hidx] using hj

theorem patches_in_two_faces (hn : 1≤n) (d : Dart) (f : Fin 3 → Face) (p : Fin 3 → Point n)
    (hf : ∀ i, f i=d.1 ∨ f i=(mate d).1)
    (hl : ∃ i, f i=d.1) (hr : ∃ i, f i=(mate d).1)
    (h01 : (graph n).Adj (.inr (f 0,p 0)) (.inr (f 1,p 1)))
    (h12 : (graph n).Adj (.inr (f 1,p 1)) (.inr (f 2,p 2)))
    (h20 : (graph n).Adj (.inr (f 2,p 2)) (.inr (f 0,p 0))) :
    Triangle (fun i => lift (.inr (f i,p i))) := by
  let u : Fin 3 → Raw (n+1) := fun i => (f i,.inr (rawPoint (p i)))
  have hu : ∀ i, rawArray (u i)=.inr (f i,p i) := by intro i; simp [u,rawArray]
  have build : ∀ d : Dart, d.1.val < (mate d).1.val →
      (∀ i, f i=d.1 ∨ f i=(mate d).1) → (∃ i, f i=d.1) → (∃ i, f i=(mate d).1) →
      Triangle (fun i => lift (.inr (f i,p i))) := by
    intro d hd hf hl hr
    have hs : Supports (.seam d) u := by
      obtain ⟨i,hi⟩ := hl; obtain ⟨j,hj⟩ := hr
      refine ⟨⟨i,rawPoint (p i),by simp [u,hi]⟩,⟨j,rawPoint (p j),by simp [u,hj]⟩,?_⟩
      intro i e h; exact False.elim (by simpa [u] using h)
    have fits : ∀ i, ∃ q, developed (.seam d) (u i)=some q := by
      intro i
      rcases hf i with hi | hi
      · simp [developed,u,hi]
      · simp [developed,u,hi,mate_other_face d]
    have ht := triangle_from_chart hn (.seam d) u hd hs fits
      (by simpa only [hu] using h01) (by simpa only [hu] using h12) (by simpa only [hu] using h20)
    simpa only [hu] using ht
  by_cases hd : d.1.val < (mate d).1.val
  · exact build d hd hf hl hr
  · have he : (mate d).1.val ≠ d.1.val := fun h => mate_other_face d (Fin.ext h)
    have hm := mate_involutive d
    apply build (mate d) (by rw [hm]; omega)
    · intro i; simpa only [hm,or_comm] using hf i
    · exact hr
    · simpa only [hm] using hl

theorem third_face (f g h : Face) (p q r : Point n) (e : Corner)
    (hg : (mate (f,e)).1=g)
    (h12 : (graph n).Adj (.inr (g,q)) (.inr (h,r)))
    (h20 : (graph n).Adj (.inr (h,r)) (.inr (f,p))) : h=f ∨ h=g := by
  by_cases hf : h=f
  · exact Or.inl hf
  by_cases hh : h=g
  · exact Or.inr hh
  exfalso
  obtain ⟨d,a,b,ha,hb,hd,_⟩ := ((graph_adj_patch_patch _ _ _ _ _).mp h20.symm).resolve_left
    (fun he => hf he.1.symm)
  obtain ⟨c,a,b,ha,hb,hc,_⟩ := ((graph_adj_patch_patch _ _ _ _ _).mp h12).resolve_left
    (fun he => hh he.1.symm)
  have hed : e≠d := by intro he; subst d; exact hh (hd.symm.trans hg)
  exact neighborFaces_no_edge f e d c hed (by simpa only [hg,hd] using hc)

theorem three_patch_triangle (hn : 1≤n) (f g h : Face) (p q r : Point n)
    (h01 : (graph n).Adj (.inr (f,p)) (.inr (g,q)))
    (h12 : (graph n).Adj (.inr (g,q)) (.inr (h,r)))
    (h20 : (graph n).Adj (.inr (h,r)) (.inr (f,p))) :
    Triangle ![lift (.inr (f,p)),lift (.inr (g,q)),lift (.inr (h,r))] := by
  by_cases hfg : f=g
  · subst g
    by_cases hfh : f=h
    · subst h
      let u : Fin 3 → Raw (n+1) := ![(f,.inr (rawPoint p)),(f,.inr (rawPoint q)),(f,.inr (rawPoint r))]
      have hu : ∀ i, rawArray (u i)=![.inr (f,p),.inr (f,q),.inr (f,r)] i := by
        intro i; fin_cases i <;> simp [u,rawArray]
      have hs : Supports (.face f) u := by intro i; fin_cases i <;> rfl
      have fits : ∀ i, ∃ x, developed (.face f) (u i)=some x := by
        intro i; fin_cases i <;> simp [developed,u]
      have ht := triangle_from_chart hn (.face f) u trivial hs fits
        (by simpa [u,rawArray] using h01) (by simpa [u,rawArray] using h12) (by simpa [u,rawArray] using h20)
      convert ht using 1 <;> funext i <;> fin_cases i <;> simp [u,rawArray]
    · obtain ⟨e,a,b,ha,hb,he,_⟩ := ((graph_adj_patch_patch _ _ _ _ _).mp h20.symm).resolve_left
        (fun hh => hfh hh.1)
      have ht := patches_in_two_faces hn (f,e) ![f,f,h] ![p,q,r]
        (by intro i; fin_cases i <;> simp [he]) ⟨0,rfl⟩ ⟨2,he.symm⟩ h01 h12 h20
      convert ht using 1 <;> funext i <;> fin_cases i <;> rfl
  · obtain ⟨e,a,b,ha,hb,he,_⟩ := ((graph_adj_patch_patch _ _ _ _ _).mp h01).resolve_left
      (fun hh => hfg hh.1)
    have hh := third_face f g h p q r e he h12 h20
    have ht := patches_in_two_faces hn (f,e) ![f,g,h] ![p,q,r]
      (by intro i; fin_cases i <;> simp [he,hh]) ⟨0,rfl⟩ ⟨1,he.symm⟩ h01 h12 h20
    convert ht using 1 <;> funext i <;> fin_cases i <;> rfl

theorem cone_patch_triangle (hn : 1≤n) (a : ParentVertex) (f g : Face) (p q : Point n)
    (h01 : (graph n).Adj (.inl a) (.inr (f,p)))
    (h12 : (graph n).Adj (.inr (f,p)) (.inr (g,q)))
    (h20 : (graph n).Adj (.inr (g,q)) (.inl a)) :
    Triangle ![lift (.inl a),lift (.inr (f,p)),lift (.inr (g,q))] := by
  have h01copy := h01
  obtain ⟨e,he,hp⟩ := h01
  obtain ⟨c,hc,hq⟩ := h20.symm
  have hfg : f≠g := by
    intro hf; subst g
    have hec := faceVertex_injective f (he.trans hc.symm)
    have hpq : p=q := by rw [hp,hq,hec]
    exact h12.ne (congrArg (fun r => Sum.inr (f,r)) hpq)
  obtain ⟨d,i,j,hi,hj,hd,_⟩ := ((graph_adj_patch_patch _ _ _ _ _).mp h12).resolve_left
    (fun hh => hfg hh.1)
  have build : ∀ (d : Dart) (e : Corner), faceVertex d.1 e=a →
      d.1.val < (mate d).1.val →
      ((f=d.1 ∧ g=(mate d).1) ∨ (g=d.1 ∧ f=(mate d).1)) →
      Triangle ![lift (.inl a),lift (.inr (f,p)),lift (.inr (g,q))] := by
    intro d e he hv horder
    let u : Fin 3 → Raw (n+1) := ![(d.1,.inl e),(f,.inr (rawPoint p)),(g,.inr (rawPoint q))]
    have hs : Supports (.seam d) u := by
      refine ⟨?_,?_,?_⟩
      · rcases horder with ⟨hf,hg⟩ | ⟨hg,hf⟩
        · exact ⟨1,rawPoint p,by simp [u,hf]⟩
        · exact ⟨2,rawPoint q,by simp [u,hg]⟩
      · rcases horder with ⟨hf,hg⟩ | ⟨hg,hf⟩
        · exact ⟨2,rawPoint q,by simp [u,hg]⟩
        · exact ⟨1,rawPoint p,by simp [u,hf]⟩
      · intro i c hi
        fin_cases i <;> simp [u] at *
    have fits : ∀ i, ∃ x, developed (.seam d) (u i)=some x := by
      intro i
      rcases horder with ⟨hf,hg⟩ | ⟨hg,hf⟩
      all_goals fin_cases i <;> simp [developed,u,hf,hg,mate_other_face d]
    have ht := triangle_from_chart hn (.seam d) u hv hs fits
      (by simpa [u,rawArray,he] using h01copy)
      (by simpa [u,rawArray] using h12)
      (by simpa [u,rawArray,he] using h20)
    convert ht using 1 <;> funext i <;> fin_cases i <;> simp [u,rawArray,he]
  by_cases hv : f.val < g.val
  · exact build (f,d) e he (by simpa only [hd] using hv) (Or.inl ⟨rfl,hd.symm⟩)
  · have hm := mate_involutive (f,d)
    have hv' : g.val < f.val := by
      have hh : f.val≠g.val := fun hh => hfg (Fin.ext hh)
      omega
    apply build (mate (f,d)) c (by simpa only [hd] using hc)
      (by simpa only [hm,hd] using hv')
    exact Or.inr ⟨hd.symm,by simp only [hm]⟩

theorem model_triangle (hn : 1≤n) (a b c : GCUnit.Vertex n)
    (h01 : (graph n).Adj a b) (h12 : (graph n).Adj b c) (h20 : (graph n).Adj c a) :
    Triangle ![lift a,lift b,lift c] := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact False.elim h01
    | inr b =>
      cases c with
      | inl c => exact False.elim h20
      | inr c => exact cone_patch_triangle hn a b.1 c.1 b.2 c.2 h01 h12 h20
  | inr a =>
    cases b with
    | inl b =>
      cases c with
      | inl c => exact False.elim h12
      | inr c =>
        have ht := cone_patch_triangle hn b c.1 a.1 c.2 a.2 h12 h20 h01
        have hh := triangle_rotate _ (triangle_rotate _ ht)
        simpa only [rot_vec] using hh
    | inr b =>
      cases c with
      | inl c =>
        have ht := cone_patch_triangle hn c a.1 b.1 a.2 b.2 h20 h01 h12
        simpa only [rot_vec] using triangle_rotate _ ht
      | inr c => exact three_patch_triangle hn a.1 b.1 c.1 a.2 b.2 c.2 h01 h12 h20

/-- The independently defined small triangles are exactly the graph triangles. -/
theorem triangle_iff_edges (hn : 1≤n) (v : Fin 3 → GCUnitSurfaceSpec.Vertex (n+1)) :
    Triangle v ↔
      (GCUnitSurfaceSpec.graph (n+1)).Adj (v 0) (v 1) ∧
      (GCUnitSurfaceSpec.graph (n+1)).Adj (v 1) (v 2) ∧
      (GCUnitSurfaceSpec.graph (n+1)).Adj (v 2) (v 0) := by
  refine ⟨triangle_edges hn v,?_⟩
  rintro ⟨h01,h12,h20⟩
  have ht := model_triangle hn (toArray (v 0)) (toArray (v 1)) (toArray (v 2))
    ((graph_adj_iff _ _).mp h01) ((graph_adj_iff _ _).mp h12) ((graph_adj_iff _ _).mp h20)
  have hv : ![lift (toArray (v 0)),lift (toArray (v 1)),lift (toArray (v 2))]=v := by
    funext i; fin_cases i <;> exact (vertexEquiv n).symm_apply_apply _
  simpa only [hv] using ht

end R002.GCUnitSurfaceBridge
