import Formal.GCUnitLink
import Formal.GCUnitSurfaceBridge

/-! Degree and the exact two-common-neighbours property, transferred to the
independently stated discrete chart quotient. -/
namespace R002.GCUnit
open Icosahedron
variable {n : ℕ}

theorem cycle_rows_separate : ∀ i j : Fin 6,
    (∀ k, CycleSix i k ↔ CycleSix j k) → i=j := by
  unfold CycleSix
  decide +kernel

theorem cycle_neighbors : ∀ i j : Fin 6, CycleSix i j ↔ j=i+1 ∨ j=i+5 := by
  unfold CycleSix
  decide +kernel

theorem cycle_two_distinct : ∀ i : Fin 6, i+1≠i+5 := by decide +kernel

theorem around_injective (hn : 1≤n) (f : Face) (p : Point n) :
    Function.Injective (around f p) := by
  intro i j hij
  apply cycle_rows_separate i j
  intro k
  rw [← around_link hn f p i k,← around_link hn f p j k,hij]

theorem ordinary_degree (hn : 1≤n) (f : Face) (p : Point n) :
    (graph n).degree (.inr (f,p))=6 := by
  classical
  have hs : (graph n).neighborFinset (.inr (f,p))=Finset.univ.image (around f p) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_image,Finset.mem_univ,true_and]
    exact around_neighbors f p w
  rw [SimpleGraph.degree,hs,Finset.card_image_of_injective _ (around_injective hn f p)]
  simp

theorem patch_two_common (hn : 1≤n) (f : Face) (p : Point n) (c : Vertex n)
    (hc : (graph n).Adj (.inr (f,p)) c) :
    ∃ x y, x≠y ∧ ∀ v, ((graph n).Adj (.inr (f,p)) v ∧ (graph n).Adj c v) ↔
      v=x ∨ v=y := by
  obtain ⟨i,rfl⟩ := around_complete f p c hc
  refine ⟨around f p (i+1),around f p (i+5),?_,?_⟩
  · intro h
    exact cycle_two_distinct i (around_injective hn f p h)
  · intro v
    constructor
    · rintro ⟨hv,hiv⟩
      obtain ⟨j,rfl⟩ := around_complete f p v hv
      have hj := (cycle_neighbors i j).mp ((around_link hn f p i j).mp hiv)
      exact hj.elim (fun h => Or.inl (congrArg (around f p) h))
        (fun h => Or.inr (congrArg (around f p) h))
    · rintro (rfl | rfl)
      · exact ⟨around_adj f p _,(around_link hn f p _ _).mpr
          ((cycle_neighbors _ _).mpr (Or.inl rfl))⟩
      · exact ⟨around_adj f p _,(around_link hn f p _ _).mpr
          ((cycle_neighbors _ _).mpr (Or.inr rfl))⟩

theorem two_common_neighbors (hn : 1≤n) : R002.TwoCommonNeighbors (graph n) := by
  intro b c h
  cases b with
  | inr b =>
    rcases b with ⟨f,p⟩
    exact patch_two_common hn f p c h
  | inl a =>
    cases c with
    | inl b => exact False.elim h
    | inr c =>
      rcases c with ⟨f,p⟩
      obtain ⟨x,y,hxy,hh⟩ := patch_two_common hn f p (.inl a) h.symm
      exact ⟨x,y,hxy,fun v => and_comm.trans (hh v)⟩

end R002.GCUnit

namespace R002.GCUnitSurfaceBridge
open Icosahedron GCUnit

noncomputable instance surfaceFintype (n : ℕ) : Fintype (GCUnitSurfaceSpec.Vertex (n+1)) :=
  Fintype.ofEquiv (GCUnit.Vertex n) (vertexEquiv n).symm

noncomputable instance surfaceDecidableAdj (n : ℕ) :
    DecidableRel (GCUnitSurfaceSpec.graph (n+1)).Adj := Classical.decRel _

theorem surface_degree {n : ℕ} (hn : 1≤n) (v : GCUnitSurfaceSpec.Vertex (n+1)) :
    (GCUnitSurfaceSpec.graph (n+1)).degree v =
      match toArray v with | .inl _ => 5 | .inr _ => 6 := by
  rw [← (graphIso n).degree_eq v]
  change (graph n).degree (toArray v)=_
  cases hv : toArray v with
  | inl a => exact parent_degree n a
  | inr w =>
    rcases w with ⟨f,p⟩
    exact ordinary_degree hn f p

theorem surface_two_common {n : ℕ} (hn : 1≤n) :
    R002.TwoCommonNeighbors (GCUnitSurfaceSpec.graph (n+1)) := by
  intro b c h
  obtain ⟨x,y,hxy,hh⟩ := two_common_neighbors hn _ _ ((graph_adj_iff b c).mp h)
  let e := vertexEquiv n
  refine ⟨e.symm x,e.symm y,?_,?_⟩
  · exact fun h => hxy (e.symm.injective h)
  · intro v
    have hx : toArray v=x ↔ v=e.symm x := by
      exact ⟨fun h => e.injective (h.trans (e.apply_symm_apply x).symm),
        fun h => by rw [h]; exact e.apply_symm_apply x⟩
    have hy : toArray v=y ↔ v=e.symm y := by
      exact ⟨fun h => e.injective (h.trans (e.apply_symm_apply y).symm),
        fun h => by rw [h]; exact e.apply_symm_apply y⟩
    rw [graph_adj_iff,graph_adj_iff,hh,hx,hy]

end R002.GCUnitSurfaceBridge
