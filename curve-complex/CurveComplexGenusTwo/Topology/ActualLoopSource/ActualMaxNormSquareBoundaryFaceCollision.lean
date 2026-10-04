import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualOrderedMeshSubintervalCollision
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The literal four square faces are compatible: different faces meet only
at their actual corners. -/
theorem actual_max_norm_square_boundary_face_collision
    (i j : Fin 4) (t u : Interval)
    (he : actualMaxNormSquareBoundaryFace i t=actualMaxNormSquareBoundaryFace j u) :
    (i=j ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1)) := by
  by_cases hij : i=j
  · exact Or.inl ⟨hij,(actual_max_norm_square_boundary_face_embedding i).injective (hij ▸ he)⟩
  · have hh := congrArg Subtype.val he
    have hx := congrArg Prod.fst hh
    have hy := congrArg Prod.snd hh
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals norm_num [actualMaxNormSquareBoundaryFace] at hx
    all_goals norm_num [actualMaxNormSquareBoundaryFace] at hy
    all_goals right
    all_goals constructor
    all_goals first
      | exact Or.inl hx
      | exact Or.inl hy
      | exact Or.inr hx
      | exact Or.inr hy
      | left; apply Subtype.ext; change _=0; nlinarith only [hx,hy]
      | right; apply Subtype.ext; change _=1; nlinarith only [hx,hy]
end CurveComplex.HyperellipticModel
