import Formal.GCParentRotations

namespace R002.Icosahedron

def dartMove (b : Bool) (d : Dart) : Dart := if b then mate d else (d.1,d.2+1)
def followWord : List Bool → Dart → Dart
  | [], d => d
  | b::w, d => followWord w (dartMove b d)

def rootWord : Face → Corner → List Bool :=
![
  ![[],[false],[false,false]],
  ![[false,false,true],[false,false,true,false],[false,false,true,false,false]],
  ![[false,false,true,false,false,true],[false,false,true,false,false,true,false],[true,false,true,false,true]],
  ![[true,false,true,false],[true,false,true,false,false],[true,false,true]],
  ![[true],[true,false],[true,false,false]],
  ![[false,true,false],[false,true,false,false],[false,true]],
  ![[false,false,true,false,true,false],[false,false,true,false,true,false,false],[false,false,true,false,true]],
  ![[false,false,true,false,false,true,false,true,false],[false,false,true,false,false,true,false,true,false,false],[false,false,true,false,false,true,false,true]],
  ![[true,false,true,false,false,true,false],[true,false,false,true,false,true,false,true],[true,false,true,false,false,true]],
  ![[true,false,false,true,false],[false,true,false,true,false,true],[true,false,false,true]],
  ![[false,true,false,false,true],[false,true,false,false,true,false],[false,false,true,false,true,false,true]],
  ![[false,false,true,false,true,false,false,true],[false,false,true,false,true,false,false,true,false],[false,false,true,false,false,true,false,true,false,true]],
  ![[true,false,true,false,false,true,false,true,false],[true,false,true,false,false,true,false,true,false,false],[true,false,true,false,false,true,false,true]],
  ![[true,false,false,true,false,true,false],[true,false,false,true,false,true,false,false],[true,false,false,true,false,true]],
  ![[false,true,false,true,false],[false,true,false,true,false,false],[false,true,false,true]],
  ![[false,true,false,false,true,false,true,false,false],[false,true,false,false,true,false,true],[false,true,false,false,true,false,true,false]],
  ![[false,true,false,false,true,false,true,false,false,true,false],[false,false,true,false,true,false,false,true,false,true],[false,true,false,false,true,false,true,false,false,true]],
  ![[true,false,false,true,false,true,false,false,true,false,true],[true,false,true,false,false,true,false,true,false,false,true],[false,true,false,false,true,false,true,false,false,true,false,true]],
  ![[false,true,false,true,false,false,true,false,true],[true,false,false,true,false,true,false,false,true],[true,false,false,true,false,true,false,false,true,false]],
  ![[false,true,false,false,true,false,true,false,true],[false,true,false,true,false,false,true],[false,true,false,true,false,false,true,false]]]

theorem rootWord_covers (d : Dart) : followWord (rootWord d.1 d.2) (0,0)=d := by
  revert d
  decide +kernel

theorem rotate_move (r : Rotation) (b : Bool) (d : Dart) :
    rotateDart r (dartMove b d)=dartMove b (rotateDart r d) := by
  cases b
  · exact rotate_next r d
  · exact rotate_mate r d

theorem rotate_word (r : Rotation) (w : List Bool) (d : Dart) :
    rotateDart r (followWord w d)=followWord w (rotateDart r d) := by
  induction w generalizing d with
  | nil => rfl
  | cons b w ih => simp only [followWord,ih,rotate_move]

/-- Rooted connectedness makes composition determined by the root dart image. -/
theorem rotate_compose (r s : Rotation) (d : Dart) :
    rotateDart r (rotateDart s d)=rotateDart (rotateDart r s) d := by
  conv_lhs => rw [← rootWord_covers d]
  rw [rotate_word,rotate_root,rotate_word]
  conv_rhs => rw [← rootWord_covers d]
  rw [rotate_word,rotate_root]

end R002.Icosahedron

namespace R002.GCPrimitiveSurface
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem rotateRaw_compose (r s : Rotation) (u : Raw k l) :
    rotateRaw r (rotateRaw s u)=rotateRaw (rotateDart r s) u := by
  rcases u with ⟨f,e|p⟩
  · exact congrArg (fun d : Dart => ((d.1,Sum.inl d.2) : Raw k l)) (rotate_compose r s (f,e))
  · have hf := congrArg Prod.fst (rotate_compose r s (f,0))
    have he := congrArg Prod.snd (rotate_compose r s (f,0))
    change (rotationFaces r.1 r.2 (rotationFaces s.1 s.2 f).1).1=
      (rotationFaces (rotateDart r s).1 (rotateDart r s).2 f).1 at hf
    change (0+(rotationFaces s.1 s.2 f).2)+
      (rotationFaces r.1 r.2 (rotationFaces s.1 s.2 f).1).2=
      0+(rotationFaces (rotateDart r s).1 (rotateDart r s).2 f).2 at he
    apply Prod.ext
    · exact hf
    apply congrArg Sum.inr
    apply Subtype.ext
    change unframe k l _ (unframe k l _ p.val)=unframe k l _ p.val
    rw [unframe_add]
    simpa only [zero_add,rotateRaw] using congrArg (fun e => unframe k l e p.val) he

theorem rotateRaw_identity (u : Raw k l) : rotateRaw (0,0) u=u := by
  rcases u with ⟨f,e|p⟩
  · exact congrArg (fun d : Dart => ((d.1,Sum.inl d.2) : Raw k l)) (rotate_identity (f,e))
  · have hf := congrArg Prod.fst (rotate_identity (f,0))
    have he := congrArg Prod.snd (rotate_identity (f,0))
    change (rotationFaces 0 0 f).1=f at hf
    change 0+(rotationFaces 0 0 f).2=0 at he
    apply Prod.ext
    · exact hf
    apply congrArg Sum.inr
    apply Subtype.ext
    change unframe k l _ p.val=p.val
    have he' : (rotationFaces 0 0 f).2=0 := by simpa only [zero_add] using he
    rw [he']; rfl

theorem rotateVertex_compose (r s : Rotation) (x : Vertex k l) :
    rotateVertex r (rotateVertex s x)=rotateVertex (rotateDart r s) x := by
  refine Quotient.inductionOn x ?_
  intro u
  exact congrArg vertex (rotateRaw_compose r s u)

theorem rotateVertex_identity (x : Vertex k l) : rotateVertex (0,0) x=x := by
  refine Quotient.inductionOn x ?_
  intro u
  exact congrArg vertex (rotateRaw_identity u)

end R002.GCPrimitiveSurface
