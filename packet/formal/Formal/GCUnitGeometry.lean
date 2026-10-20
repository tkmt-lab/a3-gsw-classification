import Formal.GCUnitPatch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Cartesian meaning of the triangular arrays and seams. The three inequalities
are oriented cross products for O=(0,0), A=(k,1), B=(-1,k+1).
This layer contains no path construction or classification criterion. -/
namespace R002.GCUnit.Geometry

abbrev Lattice := ℤ × ℤ

def norm (k : ℤ) : ℤ := k*k+k+1

def inside (k : ℤ) (p : Lattice) : Prop :=
  0 < (k+1)*p.1+p.2 ∧ 0 < -p.1+k*p.2 ∧
    k*p.1+(k+1)*p.2 < norm k

theorem inside_iff (k x y : ℤ) (hk : 1 ≤ k) :
    inside k (x,y) ↔ 0 ≤ x ∧ 1 ≤ y ∧ x+y ≤ k := by
  have hT : 0 < norm k := by dsimp [norm]; nlinarith
  constructor
  · rintro ⟨hu,hv,hw⟩
    dsimp at hu hv hw
    let u := (k+1)*x+y
    let v := -x+k*y
    let w := norm k-k*x-(k+1)*y
    have hu' : 0 < u := hu
    have hv' : 0 < v := hv
    have hw' : 0 < w := by dsimp [w]; linarith
    have hxu : norm k*(x+1)=(k+1)*u+w := by dsimp [norm,u,w]; ring
    have hyv : norm k*y=u+(k+1)*v := by dsimp [norm,u,v]; ring
    have hsw : norm k*(k+1-x-y)=v+(k+1)*w := by dsimp [norm,v,w]; ring
    have hx : 0 ≤ x := by
      by_contra hx
      have hneg : x+1 ≤ 0 := by omega
      have hh := mul_nonpos_of_nonneg_of_nonpos hT.le hneg
      have hpos := mul_pos (show 0 < k+1 by omega) hu'
      linarith
    have hy : 1 ≤ y := by
      by_contra hy
      have hneg : y ≤ 0 := by omega
      have hh := mul_nonpos_of_nonneg_of_nonpos hT.le hneg
      have hpos := mul_pos (show 0 < k+1 by omega) hv'
      linarith
    have hs : x+y ≤ k := by
      by_contra hs
      have hneg : k+1-x-y ≤ 0 := by omega
      have hh := mul_nonpos_of_nonneg_of_nonpos hT.le hneg
      have hpos := mul_pos (show 0 < k+1 by omega) hw'
      linarith
    exact ⟨hx,hy,hs⟩
  · rintro ⟨hx,hy,hs⟩
    have hnx := mul_nonneg (show 0 ≤ k+1 by omega) hx
    have hny := mul_nonneg (show 0 ≤ k by omega) (show 0 ≤ y-1 by omega)
    have hns := mul_nonneg (show 0 ≤ k by omega) (show 0 ≤ k-x-y by omega)
    dsimp [inside,norm]
    constructor
    · linarith
    constructor <;> nlinarith

def coord {n : ℕ} (p : Point n) : Lattice := (p.x,p.y+1)

theorem coord_inside {n : ℕ} (p : Point n) : inside (n+1) (coord p) := by
  rw [inside_iff _ _ _ (by omega)]
  have ht := p.total
  dsimp [coord]
  omega

theorem coord_injective {n : ℕ} : Function.Injective (@coord n) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hp := p.total
  have hq := q.total
  dsimp [coord] at hx hy
  apply Point.ext <;> omega

theorem coord_surjective {n : ℕ} (p : Lattice) (hp : inside (n+1) p) :
    ∃ q : Point n, coord q=p := by
  obtain ⟨x,y⟩ := p
  obtain ⟨hx,hy,hs⟩ := (inside_iff _ _ _ (by omega)).mp hp
  have hxy : x.toNat+(y-1).toNat ≤ n := by omega
  refine ⟨⟨x.toNat,(y-1).toNat,n-x.toNat-(y-1).toNat,by omega⟩,?_⟩
  apply Prod.ext <;> dsimp [coord] <;> omega

/-- Six unit differences in the triangular lattice. -/
def Unit (p q : Lattice) : Prop :=
  (q.1=p.1+1 ∧ q.2=p.2) ∨ (q.1=p.1-1 ∧ q.2=p.2) ∨
  (q.1=p.1 ∧ q.2=p.2+1) ∨ (q.1=p.1 ∧ q.2=p.2-1) ∨
  (q.1=p.1+1 ∧ q.2=p.2-1) ∨ (q.1=p.1-1 ∧ q.2=p.2+1)

theorem unit_coord_iff {n : ℕ} (p q : Point n) :
    Unit (coord p) (coord q) ↔ Point.UnitAdjacent p q := by
  have hp := p.total
  have hq := q.total
  constructor
  · rintro (h | h | h | h | h | h)
    all_goals dsimp [coord] at h
    all_goals simp only [Point.UnitAdjacent]
    all_goals omega
  · rintro (h | h | h | h | h | h)
    all_goals simp only [Unit,coord]
    all_goals omega

/-- Opposite edge frames differ by a half turn around the edge midpoint. -/
def seam (k : ℤ) (p : Lattice) : Lattice := (k-p.1,1-p.2)

theorem unit_seam_iff {n : ℕ} (p q : Point n) :
    Unit (coord p) (seam (n+1) (coord q)) ↔
      p.y=0 ∧ q.y=0 ∧ (p.x+q.x=n ∨ p.x+q.x=n+1) := by
  simp only [Unit,coord,seam]
  omega

theorem unit_origin_iff {n : ℕ} (p : Point n) :
    Unit (0,0) (coord p) ↔ p=Point.corner n 0 := by
  have hp := p.total
  simp [Unit,coord,Point.corner,Point.edge,Point.rotateAt,Point.ext_iff]
  omega

/-- Primitive boundary edges contain no other integer points. The interval
hypotheses are the affine segment parameters (y, -x, or x+y respectively). -/
theorem edge_OA (k x y : ℤ) (hline : x=k*y) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    (x,y)=(0,0) ∨ (x,y)=(k,1) := by
  have h : y=0 ∨ y=1 := by omega
  rcases h with rfl | rfl <;> simp_all

theorem edge_OB (k x y : ℤ) (hline : y=-(k+1)*x) (h0 : -1 ≤ x) (h1 : x ≤ 0) :
    (x,y)=(0,0) ∨ (x,y)=(-1,k+1) := by
  have h : x=0 ∨ x = -1 := by omega
  rcases h with rfl | rfl <;> simp_all

theorem edge_AB (k x y : ℤ) (hline : k*x+(k+1)*y=norm k)
    (h0 : k ≤ x+y) (h1 : x+y ≤ k+1) :
    (x,y)=(k,1) ∨ (x,y)=(-1,k+1) := by
  have h : x+y=k ∨ x+y=k+1 := by omega
  dsimp [norm] at hline
  rcases h with h | h
  · right
    have hh := congrArg (fun z : ℤ => k*z) h
    have hy : y=k+1 := by nlinarith
    apply Prod.ext <;> dsimp <;> omega
  · left
    have hh := congrArg (fun z : ℤ => k*z) h
    have hy : y=1 := by nlinarith
    apply Prod.ext <;> dsimp <;> omega

open Icosahedron

def chartTurn (k : ℤ) (p : Lattice) : Lattice := (k-p.1-p.2,p.1+1)

theorem chartTurn_coord {n : ℕ} (p : Point n) :
    chartTurn (n+1) (coord p)=coord p.rotate := by
  have hp := p.total
  apply Prod.ext <;> dsimp [chartTurn,coord,Point.rotate] <;> omega

def inverseRotateAt {n : ℕ} (e : Corner) (p : Point n) : Point n :=
  if e=0 then p else if e=1 then p.rotate.rotate else p.rotate

theorem inverse_rotateAt {n : ℕ} (e : Corner) (p : Point n) :
    inverseRotateAt e (Point.rotateAt e p)=p := by
  fin_cases e <;> rfl

theorem rotateAt_inverse {n : ℕ} (e : Corner) (p : Point n) :
    Point.rotateAt e (inverseRotateAt e p)=p := by
  fin_cases e <;> rfl

theorem inverse_eq_iff {n : ℕ} (e : Corner) (p q : Point n) :
    inverseRotateAt e p=q ↔ p=Point.rotateAt e q := by
  constructor
  · intro h
    rw [← h,rotateAt_inverse]
  · intro h
    rw [h,inverse_rotateAt]

def normal {n : ℕ} (e : Corner) (p : Point n) : Lattice := coord (inverseRotateAt e p)

theorem normal_origin_iff {n : ℕ} (e : Corner) (p : Point n) :
    Unit (0,0) (normal e p) ↔ p=Point.corner n e := by
  rw [normal,unit_origin_iff,inverse_eq_iff]
  rfl

theorem zero_row {n : ℕ} (p : Point n) :
    p.y=0 ↔ ∃ i : ℕ, ∃ hi : i ≤ n, p=Point.edge n 0 i hi := by
  constructor
  · intro hy
    have ht := p.total
    refine ⟨p.x,by omega,?_⟩
    apply Point.ext <;> simp [Point.edge,Point.rotateAt] <;> omega
  · rintro ⟨i,hi,hp⟩
    rw [hp]
    rfl

theorem normal_seam_iff {n : ℕ} (e d : Corner) (p q : Point n) :
    Unit (normal e p) (seam (n+1) (normal d q)) ↔
      ∃ i j : ℕ, ∃ hi : i ≤ n, ∃ hj : j ≤ n,
        p=Point.edge n e i hi ∧ q=Point.edge n d j hj ∧
          (i+j=n ∨ i+j=n+1) := by
  rw [normal,normal,unit_seam_iff]
  constructor
  · rintro ⟨hp,hq,hs⟩
    obtain ⟨i,hi,hiEq⟩ := (zero_row _).mp hp
    obtain ⟨j,hj,hjEq⟩ := (zero_row _).mp hq
    refine ⟨i,j,hi,hj,?_,?_,?_⟩
    · exact (inverse_eq_iff e p _).mp hiEq
    · exact (inverse_eq_iff d q _).mp hjEq
    · rw [hiEq,hjEq] at hs
      exact hs
  · rintro ⟨i,j,hi,hj,hp,hq,hs⟩
    have hp' : inverseRotateAt e p=Point.edge n 0 i hi := (inverse_eq_iff e p _).mpr hp
    have hq' : inverseRotateAt d q=Point.edge n 0 j hj := (inverse_eq_iff d q _).mpr hq
    rw [hp',hq']
    exact ⟨rfl,rfl,hs⟩

/-- The same chart gluing, specified by Cartesian unit differences, independently
of the row-sum shortcut used in the executable-style combinatorial definition. -/
def ChartAdj {n : ℕ} : Vertex n → Vertex n → Prop
  | .inl _, .inl _ => False
  | .inl a, .inr (f,p) => ∃ e : Corner, faceVertex f e=a ∧ Unit (0,0) (normal e p)
  | .inr (f,p), .inl a => ∃ e : Corner, faceVertex f e=a ∧ Unit (0,0) (normal e p)
  | .inr (f,p), .inr (g,q) =>
      (f=g ∧ Unit (coord p) (coord q)) ∨
      ∃ e : Corner, (mate (f,e)).1=g ∧
        Unit (normal e p) (seam (n+1) (normal (mate (f,e)).2 q))

theorem chartAdj_iff {n : ℕ} (u v : Vertex n) : ChartAdj u v ↔ (graph n).Adj u v := by
  cases u with
  | inl a =>
    cases v with
    | inl b => rfl
    | inr w =>
      rcases w with ⟨f,p⟩
      simp only [ChartAdj,graph_adj_parent_patch,normal_origin_iff]
  | inr w =>
    rcases w with ⟨f,p⟩
    cases v with
    | inl a => change (∃ e, _ ∧ _) ↔ (∃ e, _ ∧ _); simp only [normal_origin_iff]
    | inr w =>
      rcases w with ⟨g,q⟩
      rw [graph_adj_patch_patch]
      simp only [ChartAdj,unit_coord_iff,normal_seam_iff,Cross]
      constructor
      · rintro (h | ⟨e,hg,i,j,hi,hj,hp,hq,hs⟩)
        · exact Or.inl h
        · exact Or.inr ⟨e,i,j,hi,hj,hg,hp,hq,hs⟩
      · rintro (h | ⟨e,i,j,hi,hj,hg,hp,hq,hs⟩)
        · exact Or.inl h
        · exact Or.inr ⟨e,hg,i,j,hi,hj,hp,hq,hs⟩

end R002.GCUnit.Geometry
