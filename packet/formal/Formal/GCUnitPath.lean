import Formal.GCUnitDegree
import Formal.FiniteLiteralPath

/-! Explicit two-face zigzag. Indices count edges from zero; the final index
is 2*n+3, so the path has 2*k+2 vertices for k=n+1. -/
namespace R002.GCUnit
open Icosahedron

variable {n : ℕ}

def sideA (n j : ℕ) (hj : j ≤ n) : Vertex n := .inr (0,Point.edge n 0 j hj)
def sideB (n j : ℕ) (hj : j ≤ n) : Vertex n :=
  .inr (4,Point.edge n 0 (n-j) (by omega))

def zigzag (n i : ℕ) : Vertex n :=
  if h0 : i=0 then .inl 0 else if he : 2*n+3 ≤ i then .inl 1 else
  if ho : i%2=1 then sideA n (i/2) (by omega)
  else sideB n (i/2-1) (by omega)

@[simp] theorem zigzag_zero (n : ℕ) : zigzag n 0 = .inl 0 := by simp [zigzag]
@[simp] theorem zigzag_end (n : ℕ) : zigzag n (2*n+3) = .inl 1 := by simp [zigzag]

theorem zigzag_odd (j : ℕ) (hj : j ≤ n) : zigzag n (2*j+1) = sideA n j hj := by
  have he : ¬ 2*n+3 ≤ 2*j+1 := by omega
  have hm : (2*j+1)%2=1 := by omega
  have hd : (2*j+1)/2=j := by omega
  simp [zigzag,he,hm,hd]

theorem zigzag_even (j : ℕ) (hj : j ≤ n) : zigzag n (2*j+2) = sideB n j hj := by
  have he : ¬ 2*n+3 ≤ 2*j+2 := by omega
  simp [zigzag,he]

/-- A left inverse on the closed prefix proves absence of every repeated vertex. -/
def pathIndex (n : ℕ) : Vertex n → ℕ
  | .inl a => if a=0 then 0 else 2*n+3
  | .inr (f,p) => if f=0 then 2*p.x+1 else 2*(n-p.x)+2

theorem pathIndex_zigzag (i : ℕ) (hi : i ≤ 2*n+3) : pathIndex n (zigzag n i)=i := by
  by_cases h0 : i=0
  · subst i; simp [pathIndex]
  by_cases he : 2*n+3 ≤ i
  · have heq : i=2*n+3 := by omega
    subst i; simp [pathIndex]
  by_cases ho : i%2=1
  · simp [zigzag,h0,he,ho,sideA,pathIndex,Point.edge,Point.rotateAt]
    omega
  · have hd : i/2-1 ≤ n := by omega
    simp [zigzag,h0,he,ho,sideB,pathIndex,Point.edge,Point.rotateAt]
    omega

theorem zigzag_injective : PrefixInjective (zigzag n) (2*n+3) := by
  intro i hi j hj hij
  have h := congrArg (pathIndex n) hij
  simpa only [pathIndex_zigzag i hi,pathIndex_zigzag j hj] using h

theorem edge_step (i : ℕ) (hi : i+1 ≤ n) :
    Point.UnitAdjacent (Point.edge n 0 i (by omega)) (Point.edge n 0 (i+1) hi) := by
  apply Or.inr; apply Or.inr; apply Or.inl
  simp [Point.edge,Point.rotateAt]; omega

theorem adjacent_AB (j : ℕ) (hj : j ≤ n) : (graph n).Adj (sideA n j hj) (sideB n j hj) := by
  simp only [sideA,sideB]
  rw [graph_adj_patch_patch]
  apply Or.inr
  exact ⟨0,j,n-j,hj,by omega,rfl,rfl,rfl,Or.inl (by omega)⟩

theorem adjacent_BA (j : ℕ) (hj : j+1 ≤ n) :
    (graph n).Adj (sideB n j (by omega)) (sideA n (j+1) hj) := by
  apply SimpleGraph.Adj.symm
  simp only [sideA,sideB]
  rw [graph_adj_patch_patch]
  apply Or.inr
  exact ⟨0,j+1,n-j,hj,by omega,rfl,rfl,rfl,Or.inr (by omega)⟩

theorem adjacent_AA (j : ℕ) (hj : j+1 ≤ n) :
    (graph n).Adj (sideA n j (by omega)) (sideA n (j+1) hj) := by
  exact (graph_adj_patch_patch _ _ _ _ _).mpr (Or.inl ⟨rfl,edge_step j hj⟩)

theorem adjacent_BB (j : ℕ) (hj : j+1 ≤ n) :
    (graph n).Adj (sideB n j (by omega)) (sideB n (j+1) hj) := by
  simp only [sideB]
  rw [graph_adj_patch_patch]
  apply Or.inl; refine ⟨rfl,?_⟩
  have h := Point.unitAdjacent_symm _ _ (edge_step (n:=n) (n-(j+1)) (by omega))
  have he : n-(j+1)+1=n-j := by omega
  simpa only [he] using h

theorem start_A : (graph n).Adj (.inl 0) (sideA n 0 (by omega)) :=
  ⟨0,rfl,rfl⟩
theorem start_B : (graph n).Adj (.inl 0) (sideB n 0 (by omega)) := by
  refine ⟨1,rfl,?_⟩
  apply Point.ext <;> simp [Point.edge,Point.corner,Point.rotateAt,Point.rotate]
theorem finish_A : (graph n).Adj (sideA n n (by omega)) (.inl 1) := by
  refine ⟨1,rfl,?_⟩
  apply Point.ext <;> simp [Point.edge,Point.corner,Point.rotateAt,Point.rotate]
theorem finish_B : (graph n).Adj (sideB n n (by omega)) (.inl 1) := by
  refine ⟨0,rfl,?_⟩
  simp [Point.edge,Point.corner]

theorem interior_index (i : ℕ) (h0 : 0 < i) (he : i < 2*n+3) :
    (∃ j ≤ n, i=2*j+1) ∨ ∃ j ≤ n, i=2*j+2 := by
  by_cases ho : i%2=1
  · exact Or.inl ⟨i/2,by omega,by omega⟩
  · exact Or.inr ⟨i/2-1,by omega,by omega⟩

theorem zigzag_adjacent (i : ℕ) (hi : i+1 ≤ 2*n+3) :
    (graph n).Adj (zigzag n i) (zigzag n (i+1)) := by
  by_cases h0 : i=0
  · subst i
    rw [zigzag_zero,show 0+1=2*0+1 by omega,zigzag_odd 0 (by omega)]
    exact start_A
  rcases interior_index (n:=n) i (by omega) (by omega) with ⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩
  · rw [zigzag_odd j hj,show 2*j+1+1=2*j+2 by omega,zigzag_even j hj]
    exact adjacent_AB j hj
  · rw [zigzag_even j hj]
    by_cases hjn : j=n
    · subst j
      rw [show 2*n+2+1=2*n+3 by omega,zigzag_end]
      exact finish_B
    · rw [show 2*j+2+1=2*(j+1)+1 by omega,zigzag_odd (j+1) (by omega)]
      exact adjacent_BA j (by omega)

theorem zigzag_skip (i : ℕ) (hi : i+2 ≤ 2*n+3) :
    (graph n).Adj (zigzag n i) (zigzag n (i+2)) := by
  by_cases h0 : i=0
  · subst i
    rw [zigzag_zero,show 0+2=2*0+2 by omega,zigzag_even 0 (by omega)]
    exact start_B
  rcases interior_index (n:=n) i (by omega) (by omega) with ⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩
  · rw [zigzag_odd j hj]
    by_cases hjn : j=n
    · subst j
      rw [show 2*n+1+2=2*n+3 by omega,zigzag_end]
      exact finish_A
    · rw [show 2*j+1+2=2*(j+1)+1 by omega,zigzag_odd (j+1) (by omega)]
      exact adjacent_AA j (by omega)
  · rw [zigzag_even j hj,show 2*j+2+2=2*(j+1)+2 by omega,
      zigzag_even (j+1) (by omega)]
    exact adjacent_BB j (by omega)

/-- Actual degrees are included: no unproved interpretation of a cone predicate. -/
structure DegreeLiteralPath {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : ℕ → V) (e : ℕ) : Prop where
  finitePath : FiniteTrianglePath G p e
  minIndex : 3 ≤ e
  oddIndex : e%2=1
  startDegree : G.degree (p 0)=5
  endDegree : G.degree (p e)=5
  secondDegree : G.degree (p 1)=6
  penultimateDegree : G.degree (p (e-1))=6

theorem zigzag_literal (hn : 1 ≤ n) :
    DegreeLiteralPath (graph n) (zigzag n) (2*n+3) := by
  refine ⟨⟨zigzag_injective,zigzag_adjacent,zigzag_skip⟩,by omega,by omega,?_,?_,?_,?_⟩
  · rw [zigzag_zero]; exact parent_degree n 0
  · rw [zigzag_end]; exact parent_degree n 1
  · rw [show 1=2*0+1 by omega,zigzag_odd 0 (by omega)]
    exact corner_degree hn 0
  · rw [show 2*n+3-1=2*n+2 by omega,zigzag_even n (by omega)]
    have hB : sideB n n (by omega) = .inr (4,Point.corner n 0) := by
      dsimp only [sideB]
      apply congrArg Sum.inr
      apply congrArg (fun p : Point n => ((4 : Face),p))
      apply Point.ext <;> simp [Point.edge,Point.rotateAt,Point.corner]
    rw [hB]
    exact corner_degree hn 4

/-- The unit-width family, with n=k-1 replaced by k=n+1. -/
theorem unit_width_path (k : ℕ) (hk : 2 ≤ k) :
    ∃ p : ℕ → Vertex (k-1), DegreeLiteralPath (graph (k-1)) p (2*k+1) := by
  have hn : 1 ≤ k-1 := by omega
  have he : 2*(k-1)+3=2*k+1 := by omega
  exact ⟨zigzag (k-1),he ▸ zigzag_literal hn⟩

end R002.GCUnit
