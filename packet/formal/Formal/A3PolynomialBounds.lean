import Formal.A3Arithmetic

/-! AU §4: exact polynomial certificates, exported by AV.
Each equality is proved by ring and each strict sign by positivity.
No finite evaluation or Python assertion is trusted by Lean. -/
namespace R002.A3

theorem au_c1_a_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 1*l+w;
    let N := norm k l;
    let a := (1+1)*s*k+(s-5)*l-1;
    let b := (1*s+5)*k+(1+1)*s*l-1;
    0 < a := by
  dsimp only
  calc
    0 < 25 + 6*E + 7*D + 42*S + 9*S*E + 12*S*D + 12*S^2 + 3*S^2*E + 3*S^2*D := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c1_b_minus_a_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 1*l+w;
    let N := norm k l;
    let a := (1+1)*s*k+(s-5)*l-1;
    let b := (1*s+5)*k+(1+1)*s*l-1;
    0 < b-a := by
  dsimp only
  calc
    0 < 112 + 23*E + 33*D + 36*S + 9*S*E + 9*S*D := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c1_N_minus_b_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 1*l+w;
    let N := norm k l;
    let a := (1+1)*s*k+(s-5)*l-1;
    let b := (1*s+5)*k+(1+1)*s*l-1;
    0 < N-b := by
  dsimp only
  calc
    0 < 299 + 153*E + 19*E^2 + 214*D + 53*D*E + 37*D^2 + 210*S + 114*S*E + 15*S*E^2 + 135*S*D + 36*S*D*E + 21*S*D^2 + 36*S^2 + 21*S^2*E + 3*S^2*E^2 + 21*S^2*D + 6*S^2*D*E + 3*S^2*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c1_v_upper_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 1*l+w;
    let N := norm k l;
    let a := (1+1)*s*k+(s-5)*l-1;
    let b := (1*s+5)*k+(1+1)*s*l-1;
    0 < (1*s+1+2)*N-k*b-k-l := by
  dsimp only
  calc
    0 < 238 + 88*E + 8*E^2 + 155*D + 29*D*E + 25*D^2 + 228*S + 101*S*E + 11*S*E^2 + 129*S*D + 29*S*D*E + 18*S*D^2 + 48*S^2 + 24*S^2*E + 3*S^2*E^2 + 24*S^2*D + 6*S^2*D*E + 3*S^2*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c1_sum_upper_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 1*l+w;
    let N := norm k l;
    let a := (1+1)*s*k+(s-5)*l-1;
    let b := (1*s+5)*k+(1+1)*s*l-1;
    0 < ((1+1)*s+1+3)*N-(k+l)*b-k := by
  dsimp only
  calc
    0 < 186 + 72*E + 7*E^2 + 109*D + 21*D*E + 16*D^2 + 204*S + 91*S*E + 10*S*E^2 + 111*S*D + 25*S*D*E + 15*S*D^2 + 48*S^2 + 24*S^2*E + 3*S^2*E^2 + 24*S^2*D + 6*S^2*D*E + 3*S^2*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c1_v_late_lower_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 1*l+w;
    let N := norm k l;
    let a := (1+1)*s*k+(s-5)*l-1;
    let b := (1*s+5)*k+(1+1)*s*l-1;
    0 < k*b-l-(1*s+1+1)*N := by
  dsimp only
  calc
    0 < 164 + 87*E + 11*E^2 + 89*D + 24*D*E + 12*D^2 + 48*S + 28*S*E + 4*S*E^2 + 24*S*D + 7*S*D*E + 3*S*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c1_sum_late_lower_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 1*l+w;
    let N := norm k l;
    let a := (1+1)*s*k+(s-5)*l-1;
    let b := (1*s+5)*k+(1+1)*s*l-1;
    0 < (k+l)*b-((1+1)*s+1+2)*N := by
  dsimp only
  calc
    0 < 236 + 107*E + 12*E^2 + 141*D + 32*D*E + 21*D^2 + 80*S + 40*S*E + 5*S*E^2 + 44*S*D + 11*S*D*E + 6*S*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c1_early_inside_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 1*l+w;
    let N := norm k l;
    let a := (1+1)*s*k+(s-5)*l-1;
    let b := (1*s+5)*k+(1+1)*s*l-1;
    0 < N-w*a-(1+1)*k-l := by
  dsimp only
  calc
    0 < 298 + 125*E + 13*E^2 + 190*D + 40*D*E + 30*D^2 + 108*S + 51*S*E + 6*S*E^2 + 63*S*D + 15*S*D*E + 9*S*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c1_endpoint_bound_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 1*l+w;
    let N := norm k l;
    let a := (1+1)*s*k+(s-5)*l-1;
    let b := (1*s+5)*k+(1+1)*s*l-1;
    0 < (s+2)*N-k-l-l*b := by
  dsimp only
  calc
    0 < 350 + 159*E + 18*E^2 + 198*D + 45*D*E + 28*D^2 + 252*S + 119*S*E + 14*S*E^2 + 135*S*D + 32*S*D*E + 18*S*D^2 + 48*S^2 + 24*S^2*E + 3*S^2*E^2 + 24*S^2*D + 6*S^2*D*E + 3*S^2*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c2_a_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 1;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l+w;
    let N := norm k l;
    let a := (2+1)*s*k+(s-5)*l-1;
    let b := (2*s+5)*k+(2+1)*s*l-1;
    0 < a := by
  dsimp only
  calc
    0 < 23 + 5*E + 7*D + 62*S + 12*S*E + 19*S*D + 28*S^2 + 7*S^2*E + 7*S^2*D := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c2_b_minus_a_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 1;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l+w;
    let N := norm k l;
    let a := (2+1)*s*k+(s-5)*l-1;
    let b := (2*s+5)*k+(2+1)*s*l-1;
    0 < b-a := by
  dsimp only
  calc
    0 < 106 + 19*E + 34*D + 56*S + 14*S*E + 14*S*D := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c2_N_minus_b_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 1;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l+w;
    let N := norm k l;
    let a := (2+1)*s*k+(s-5)*l-1;
    let b := (2*s+5)*k+(2+1)*s*l-1;
    0 < N-b := by
  dsimp only
  calc
    0 < 259 + 118*E + 13*E^2 + 205*D + 45*D*E + 39*D^2 + 298*S + 154*S*E + 19*S*E^2 + 203*S*D + 52*S*D*E + 33*S*D^2 + 84*S^2 + 49*S^2*E + 7*S^2*E^2 + 49*S^2*D + 14*S^2*D*E + 7*S^2*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c2_v_upper_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 1;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l+w;
    let N := norm k l;
    let a := (2+1)*s*k+(s-5)*l-1;
    let b := (2*s+5)*k+(2+1)*s*l-1;
    0 < (2*s+2+2)*N-k*b-k-l := by
  dsimp only
  calc
    0 < 242 + 77*E + 6*E^2 + 168*D + 27*D*E + 29*D^2 + 340*S + 141*S*E + 14*S*E^2 + 201*S*D + 43*S*D*E + 29*S*D^2 + 112*S^2 + 56*S^2*E + 7*S^2*E^2 + 56*S^2*D + 14*S^2*D*E + 7*S^2*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c2_sum_upper_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 1;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l+w;
    let N := norm k l;
    let a := (2+1)*s*k+(s-5)*l-1;
    let b := (2*s+5)*k+(2+1)*s*l-1;
    0 < ((2+1)*s+2+3)*N-(k+l)*b-k := by
  dsimp only
  calc
    0 < 250 + 89*E + 8*E^2 + 158*D + 28*D*E + 25*D^2 + 340*S + 145*S*E + 15*S*E^2 + 193*S*D + 42*S*D*E + 27*S*D^2 + 112*S^2 + 56*S^2*E + 7*S^2*E^2 + 56*S^2*D + 14*S^2*D*E + 7*S^2*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c2_v_late_lower_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 1;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l+w;
    let N := norm k l;
    let a := (2+1)*s*k+(s-5)*l-1;
    let b := (2*s+5)*k+(2+1)*s*l-1;
    0 < k*b-l-(2*s+2+1)*N := by
  dsimp only
  calc
    0 < 118 + 60*E + 7*E^2 + 69*D + 18*D*E + 10*D^2 + 60*S + 35*S*E + 5*S*E^2 + 31*S*D + 9*S*D*E + 4*S*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c2_sum_late_lower_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 1;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l+w;
    let N := norm k l;
    let a := (2+1)*s*k+(s-5)*l-1;
    let b := (2*s+5)*k+(2+1)*s*l-1;
    0 < (k+l)*b-((2+1)*s+2+2)*N := by
  dsimp only
  calc
    0 < 122 + 50*E + 5*E^2 + 83*D + 17*D*E + 14*D^2 + 68*S + 33*S*E + 4*S*E^2 + 41*S*D + 10*S*D*E + 6*S*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c2_early_inside_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 1;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l+w;
    let N := norm k l;
    let a := (2+1)*s*k+(s-5)*l-1;
    let b := (2*s+5)*k+(2+1)*s*l-1;
    0 < N-w*a-(2+1)*k-l := by
  dsimp only
  calc
    0 < 242 + 89*E + 8*E^2 + 178*D + 33*D*E + 32*D^2 + 140*S + 63*S*E + 7*S*E^2 + 91*S*D + 21*S*D*E + 14*S*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_c2_endpoint_bound_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 1;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l+w;
    let N := norm k l;
    let a := (2+1)*s*k+(s-5)*l-1;
    let b := (2*s+5)*k+(2+1)*s*l-1;
    0 < (s+2)*N-k-l-l*b := by
  dsimp only
  calc
    0 < 368 + 149*E + 15*E^2 + 227*D + 46*D*E + 35*D^2 + 400*S + 180*S*E + 20*S*E^2 + 224*S*D + 51*S*D*E + 31*S*D^2 + 112*S^2 + 56*S^2*E + 7*S^2*E^2 + 56*S^2*D + 14*S^2*D*E + 7*S^2*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_neg_a_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l-w;
    let N := norm k l;
    let a := (2*s-5)*k+3*s*l-1;
    let b := 3*s*k+(s+5)*l-1;
    0 < a := by
  dsimp only
  calc
    0 < 43 + 9*E + 13*D + 78*S + 16*S*E + 23*S*D + 28*S^2 + 7*S^2*E + 7*S^2*D := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_neg_b_minus_a_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l-w;
    let N := norm k l;
    let a := (2*s-5)*k+3*s*l-1;
    let b := 3*s*k+(s+5)*l-1;
    0 < b-a := by
  dsimp only
  calc
    0 < 122 + 23*E + 38*D + 56*S + 14*S*E + 14*S*D := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_neg_N_minus_b_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l-w;
    let N := norm k l;
    let a := (2*s-5)*k+3*s*l-1;
    let b := 3*s*k+(s+5)*l-1;
    0 < N-b := by
  dsimp only
  calc
    0 < 351 + 166*E + 19*E^2 + 267*D + 61*D*E + 49*D^2 + 346*S + 182*S*E + 23*S*E^2 + 231*S*D + 60*S*D*E + 37*S*D^2 + 84*S^2 + 49*S^2*E + 7*S^2*E^2 + 49*S^2*D + 14*S^2*D*E + 7*S^2*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_neg_u_upper_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l-w;
    let N := norm k l;
    let a := (2*s-5)*k+3*s*l-1;
    let b := 3*s*k+(s+5)*l-1;
    0 < (s+2)*N-k-l-l*b := by
  dsimp only
  calc
    0 < 388 + 137*E + 12*E^2 + 259*D + 46*D*E + 43*D^2 + 424*S + 182*S*E + 19*S*E^2 + 246*S*D + 54*S*D*E + 35*S*D^2 + 112*S^2 + 56*S^2*E + 7*S^2*E^2 + 56*S^2*D + 14*S^2*D*E + 7*S^2*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_neg_sum_upper_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l-w;
    let N := norm k l;
    let a := (2*s-5)*k+3*s*l-1;
    let b := 3*s*k+(s+5)*l-1;
    0 < (3*s+3)*N-(k+l)*b-k := by
  dsimp only
  calc
    0 < 338 + 122*E + 11*E^2 + 211*D + 38*D*E + 33*D^2 + 396*S + 171*S*E + 18*S*E^2 + 223*S*D + 49*S*D*E + 31*S*D^2 + 112*S^2 + 56*S^2*E + 7*S^2*E^2 + 56*S^2*D + 14*S^2*D*E + 7*S^2*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_neg_u_late_lower_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l-w;
    let N := norm k l;
    let a := (2*s-5)*k+3*s*l-1;
    let b := 3*s*k+(s+5)*l-1;
    0 < l*b-k-(s+1)*N := by
  dsimp only
  calc
    0 < 86 + 53*E + 7*E^2 + 46*D + 15*D*E + 6*D^2 + 36*S + 25*S*E + 4*S*E^2 + 17*S*D + 6*S*D*E + 2*S*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_neg_sum_late_lower_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l-w;
    let N := norm k l;
    let a := (2*s-5)*k+3*s*l-1;
    let b := 3*s*k+(s+5)*l-1;
    0 < (k+l)*b-(3*s+2)*N := by
  dsimp only
  calc
    0 < 162 + 73*E + 8*E^2 + 102*D + 23*D*E + 16*D^2 + 76*S + 39*S*E + 5*S*E^2 + 43*S*D + 11*S*D*E + 6*S*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

theorem au_neg_early_inside_pos (S D E : ℤ) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    let s := S + 2;
    let w := D + E + 4;
    let d := D + 2;
    let l := s*w+d;
    let k := 2*l-w;
    let N := norm k l;
    let a := (2*s-5)*k+3*s*l-1;
    let b := 3*s*k+(s+5)*l-1;
    0 < N-w*a-2*k-3*l := by
  dsimp only
  calc
    0 < 282 + 107*E + 10*E^2 + 204*D + 39*D*E + 36*D^2 + 140*S + 63*S*E + 7*S*E^2 + 91*S*D + 21*S*D*E + 14*S*D^2 := by positivity
    _ = _ := by (try dsimp [norm]); ring

#print axioms au_c1_a_pos
#print axioms au_c1_b_minus_a_pos
#print axioms au_c1_N_minus_b_pos
#print axioms au_c1_v_upper_pos
#print axioms au_c1_sum_upper_pos
#print axioms au_c1_v_late_lower_pos
#print axioms au_c1_sum_late_lower_pos
#print axioms au_c1_early_inside_pos
#print axioms au_c1_endpoint_bound_pos
#print axioms au_c2_a_pos
#print axioms au_c2_b_minus_a_pos
#print axioms au_c2_N_minus_b_pos
#print axioms au_c2_v_upper_pos
#print axioms au_c2_sum_upper_pos
#print axioms au_c2_v_late_lower_pos
#print axioms au_c2_sum_late_lower_pos
#print axioms au_c2_early_inside_pos
#print axioms au_c2_endpoint_bound_pos
#print axioms au_neg_a_pos
#print axioms au_neg_b_minus_a_pos
#print axioms au_neg_N_minus_b_pos
#print axioms au_neg_u_upper_pos
#print axioms au_neg_sum_upper_pos
#print axioms au_neg_u_late_lower_pos
#print axioms au_neg_sum_late_lower_pos
#print axioms au_neg_early_inside_pos
end R002.A3
