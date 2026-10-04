import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMaxNormSquareBoundaryFaceCollision
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Each literal square corner has exactly two face-parameter presentations.
The interval parameters are original face endpoints, including bottom corners. -/
theorem actual_square_corner_face_parameter_count
    (i : Fin 4) (bit : Fin 2) :
    {r : Fin 4 × Interval | actualMaxNormSquareBoundaryFace r.1 r.2=
      actualMaxNormSquareBoundaryFace i (if bit=0 then 0 else 1)}.ncard=2 := by
  classical
  have h00 : {r : Fin 4 × Interval | actualMaxNormSquareBoundaryFace r.1 r.2=
      actualMaxNormSquareBoundaryFace 0 0}={(0,0),(3,0)} := by
    ext r
    constructor
    · intro he
      change actualMaxNormSquareBoundaryFace r.1 r.2=actualMaxNormSquareBoundaryFace 0 0 at he
      have hx := congrArg (fun z => z.val.1) he
      have hy := congrArg (fun z => z.val.2) he
      rcases r with ⟨j,t⟩
      fin_cases j <;> norm_num [actualMaxNormSquareBoundaryFace] at hx <;> norm_num [actualMaxNormSquareBoundaryFace] at hy
      all_goals simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      all_goals first
        | left; exact Prod.ext (by rfl) (by assumption)
        | right; exact Prod.ext (by rfl) (by assumption)
    · intro he
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at he
      rcases he with rfl | rfl
      all_goals apply Subtype.ext; apply Prod.ext <;> norm_num [actualMaxNormSquareBoundaryFace]
  have h01 : {r : Fin 4 × Interval | actualMaxNormSquareBoundaryFace r.1 r.2=
      actualMaxNormSquareBoundaryFace 0 1}={(0,1),(1,0)} := by
    ext r
    constructor
    · intro he
      change actualMaxNormSquareBoundaryFace r.1 r.2=actualMaxNormSquareBoundaryFace 0 1 at he
      have hx := congrArg (fun z => z.val.1) he
      have hy := congrArg (fun z => z.val.2) he
      rcases r with ⟨j,t⟩
      fin_cases j <;> norm_num [actualMaxNormSquareBoundaryFace] at hx <;> norm_num [actualMaxNormSquareBoundaryFace] at hy
      all_goals simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      all_goals first
        | left; exact Prod.ext (by rfl) (by apply Subtype.ext; change t.val=1; linarith only [hx,hy])
        | right; exact Prod.ext (by rfl) (by assumption)
    · intro he
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at he
      rcases he with rfl | rfl
      all_goals apply Subtype.ext; apply Prod.ext <;> norm_num [actualMaxNormSquareBoundaryFace]
  have h11 : {r : Fin 4 × Interval | actualMaxNormSquareBoundaryFace r.1 r.2=
      actualMaxNormSquareBoundaryFace 1 1}={(1,1),(2,1)} := by
    ext r
    constructor
    · intro he
      change actualMaxNormSquareBoundaryFace r.1 r.2=actualMaxNormSquareBoundaryFace 1 1 at he
      have hx := congrArg (fun z => z.val.1) he
      have hy := congrArg (fun z => z.val.2) he
      rcases r with ⟨j,t⟩
      fin_cases j <;> norm_num [actualMaxNormSquareBoundaryFace] at hx <;> norm_num [actualMaxNormSquareBoundaryFace] at hy
      all_goals simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      all_goals first
        | left; exact Prod.ext (by rfl) (by apply Subtype.ext; change t.val=1; linarith only [hx,hy])
        | right; exact Prod.ext (by rfl) (by apply Subtype.ext; change t.val=1; linarith only [hx,hy])
    · intro he
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at he
      rcases he with rfl | rfl
      all_goals apply Subtype.ext; apply Prod.ext <;> norm_num [actualMaxNormSquareBoundaryFace]
  have h20 : {r : Fin 4 × Interval | actualMaxNormSquareBoundaryFace r.1 r.2=
      actualMaxNormSquareBoundaryFace 2 0}={(2,0),(3,1)} := by
    ext r
    constructor
    · intro he
      change actualMaxNormSquareBoundaryFace r.1 r.2=actualMaxNormSquareBoundaryFace 2 0 at he
      have hx := congrArg (fun z => z.val.1) he
      have hy := congrArg (fun z => z.val.2) he
      rcases r with ⟨j,t⟩
      fin_cases j <;> norm_num [actualMaxNormSquareBoundaryFace] at hx <;> norm_num [actualMaxNormSquareBoundaryFace] at hy
      all_goals simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      all_goals first
        | left; exact Prod.ext (by rfl) (by assumption)
        | right; exact Prod.ext (by rfl) (by apply Subtype.ext; change t.val=1; linarith only [hx,hy])
    · intro he
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at he
      rcases he with rfl | rfl
      all_goals apply Subtype.ext; apply Prod.ext <;> norm_num [actualMaxNormSquareBoundaryFace]
  have he10 : actualMaxNormSquareBoundaryFace 1 0=actualMaxNormSquareBoundaryFace 0 1 := by ext <;> norm_num [actualMaxNormSquareBoundaryFace]
  have he21 : actualMaxNormSquareBoundaryFace 2 1=actualMaxNormSquareBoundaryFace 1 1 := by ext <;> norm_num [actualMaxNormSquareBoundaryFace]
  have he30 : actualMaxNormSquareBoundaryFace 3 0=actualMaxNormSquareBoundaryFace 0 0 := by ext <;> norm_num [actualMaxNormSquareBoundaryFace]
  have he31 : actualMaxNormSquareBoundaryFace 3 1=actualMaxNormSquareBoundaryFace 2 0 := by ext <;> norm_num [actualMaxNormSquareBoundaryFace]
  fin_cases i <;> fin_cases bit <;> norm_num <;>
    first
      | rw [h00]; exact Set.ncard_pair (by decide)
      | rw [h01]; exact Set.ncard_pair (by decide)
      | rw [h11]; exact Set.ncard_pair (by decide)
      | rw [h20]; exact Set.ncard_pair (by decide)
      | rw [he10,h01]; exact Set.ncard_pair (by decide)
      | rw [he21,h11]; exact Set.ncard_pair (by decide)
      | rw [he30,h00]; exact Set.ncard_pair (by decide)
      | rw [he31,h20]; exact Set.ncard_pair (by decide)
end CurveComplex.HyperellipticModel
