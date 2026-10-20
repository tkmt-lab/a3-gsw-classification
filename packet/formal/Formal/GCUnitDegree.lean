import Formal.GCUnitPatch

/-! Exact degree certificates for the vertices used at the two ends of the
unit-width path. They concern the defined graph, not a separate cone predicate. -/
namespace R002.GCUnit
open Icosahedron

noncomputable def incident (a : ParentVertex) : Finset Dart :=
  Finset.univ.filter (fun d => faceVertex d.1 d.2 = a)

def patchCorner (n : ℕ) (d : Dart) : Vertex n := .inr (d.1,Point.corner n d.2)

theorem patchCorner_injOn (n : ℕ) (a : ParentVertex) :
    Set.InjOn (patchCorner n) (incident a) := by
  intro d hd e he h
  have hd' : faceVertex d.1 d.2 = a := (Finset.mem_filter.mp hd).2
  have he' : faceVertex e.1 e.2 = a := (Finset.mem_filter.mp he).2
  have hf := congrArg Prod.fst (Sum.inr.inj h)
  change d.1 = e.1 at hf
  apply Prod.ext hf
  apply faceVertex_injective d.1
  exact hd'.trans (by simpa only [← hf] using he'.symm)

theorem parent_neighbors (n : ℕ) (a : ParentVertex) :
    (graph n).neighborFinset (.inl a) = (incident a).image (patchCorner n) := by
  classical
  ext w
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_image]
  cases w with
  | inl b => simp [graph,Adj,patchCorner]
  | inr w =>
    rcases w with ⟨f,p⟩
    constructor
    · rintro ⟨e,he,hp⟩
      refine ⟨(f,e),?_,?_⟩
      · simp [incident,he]
      · simp [patchCorner,hp]
    · rintro ⟨⟨g,e⟩,hd,he⟩
      have hp := Sum.inr.inj he
      have hf := congrArg Prod.fst hp
      change g=f at hf
      subst g
      exact ⟨e,(Finset.mem_filter.mp hd).2,(congrArg Prod.snd hp).symm⟩

theorem parent_degree (n : ℕ) (a : ParentVertex) : (graph n).degree (.inl a) = 5 := by
  classical
  rw [SimpleGraph.degree,parent_neighbors,Finset.card_image_of_injOn (patchCorner_injOn n a)]
  exact five_corners a

variable {n : ℕ}

theorem cross_corner_zero (hn : 1 ≤ n) (f g : Face) (q : Point n) :
    Cross f (Point.corner n 0) g q ↔
      (g=(mate (f,0)).1 ∧ q=Point.edge n (mate (f,0)).2 n (by omega)) ∨
      (g=(mate (f,2)).1 ∧
        (q=Point.edge n (mate (f,2)).2 0 (by omega) ∨
         q=Point.edge n (mate (f,2)).2 1 (by omega))) := by
  constructor
  · rintro ⟨e,i,j,hi,hj,hg,hp,hq,hs⟩
    rcases (Point.corner_zero_on_edge hn e i hi).mp hp with ⟨he,hi0⟩ | ⟨he,hin⟩
    · subst e; subst i
      have hjn : j=n := by omega
      subst j
      exact Or.inl ⟨hg.symm,hq⟩
    · subst e; subst i
      have hj01 : j=0 ∨ j=1 := by omega
      refine Or.inr ⟨hg.symm,?_⟩
      rcases hj01 with hj0 | hj1
      · subst j; exact Or.inl hq
      · subst j; exact Or.inr hq
  · rintro (⟨hg,hq⟩ | ⟨hg,hq | hq⟩)
    · subst g; subst q
      exact ⟨0,0,n,by omega,by omega,rfl,rfl,rfl,Or.inl (by omega)⟩
    · subst g; subst q
      refine ⟨2,n,0,by omega,by omega,rfl,?_,rfl,Or.inl (by omega)⟩
      exact (Point.corner_zero_on_edge hn 2 n (by omega)).mpr (Or.inr ⟨rfl,rfl⟩)
    · subst g; subst q
      refine ⟨2,n,1,by omega,by omega,rfl,?_,rfl,Or.inr (by omega)⟩
      exact (Point.corner_zero_on_edge hn 2 n (by omega)).mpr (Or.inr ⟨rfl,rfl⟩)

def sixNeighbors (n : ℕ) (hn : 1 ≤ n) (f : Face) : Fin 6 → Vertex n := ![
  .inl (faceVertex f 0),
  .inr (f,Point.nearX n hn),
  .inr (f,Point.nearY n hn),
  .inr ((mate (f,0)).1,Point.edge n (mate (f,0)).2 n (by omega)),
  .inr ((mate (f,2)).1,Point.edge n (mate (f,2)).2 0 (by omega)),
  .inr ((mate (f,2)).1,Point.edge n (mate (f,2)).2 1 (by omega))]

theorem corner_parent_iff (hn : 1 ≤ n) (f : Face) (a : ParentVertex) :
    (graph n).Adj (.inr (f,Point.corner n 0)) (.inl a) ↔ a=faceVertex f 0 := by
  change (∃ e, faceVertex f e=a ∧ Point.corner n 0=Point.corner n e) ↔ _
  constructor
  · rintro ⟨e,he,hp⟩
    have he0 := Point.corner_injective hn hp
    subst e
    exact he.symm
  · intro h; exact ⟨0,h.symm,rfl⟩

theorem corner_neighbors_iff (hn : 1 ≤ n) (f : Face) (w : Vertex n) :
    (graph n).Adj (.inr (f,Point.corner n 0)) w ↔ ∃ i : Fin 6, sixNeighbors n hn f i = w := by
  cases w with
  | inl a => simp [corner_parent_iff hn,sixNeighbors,Fin.exists_fin_succ,eq_comm]
  | inr w =>
    rcases w with ⟨g,q⟩
    rw [graph_adj_patch_patch,Point.neighbors_corner_zero hn,cross_corner_zero hn]
    simp [sixNeighbors,Fin.exists_fin_succ,eq_comm,and_or_left,or_assoc]

theorem sixNeighbors_injective (hn : 1 ≤ n) (f : Face) :
    Function.Injective (sixNeighbors n hn f) := by
  intro i j hij
  have h0 := mate_other_face (f,0)
  have h2 := mate_other_face (f,2)
  have h02 := different_neighbors f
  have hedge := Point.edge_injective (mate (f,2)).2 0 1 (by omega) (by omega)
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals dsimp [sixNeighbors] at hij
  all_goals simp only [Sum.inr.injEq,Sum.inl_ne_inr,
    Sum.inr_ne_inl,Prod.mk.injEq] at hij
  all_goals first
    | exact False.elim (h0 hij.1.symm)
    | exact False.elim (h0 hij.1)
    | exact False.elim (h2 hij.1.symm)
    | exact False.elim (h2 hij.1)
    | exact False.elim (h02 hij.1)
    | exact False.elim (h02 hij.1.symm)
    | have hx := congrArg Point.x hij.2; simp [Point.nearX,Point.nearY] at hx
    | have h01 := hedge.mp hij.2; omega
    | have h01 := hedge.mp hij.2.symm; omega

theorem corner_degree (hn : 1 ≤ n) (f : Face) :
    (graph n).degree (.inr (f,Point.corner n 0)) = 6 := by
  classical
  have hset : (graph n).neighborFinset (.inr (f,Point.corner n 0)) =
      Finset.univ.image (sixNeighbors n hn f) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_image,Finset.mem_univ,true_and]
    exact corner_neighbors_iff hn f w
  rw [SimpleGraph.degree,hset,Finset.card_image_of_injective _ (sixNeighbors_injective hn f)]
  simp

end R002.GCUnit
