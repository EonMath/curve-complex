import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualNegativeBoundaryMeshNodeIncidenceKernelRecovery
namespace CurveComplex.LocalSurgery
open Set
noncomputable section
private def h1BoundaryFaceRaw (i : Fin 4) (t : Interval) : ℝ × ℝ :=
  if i.val=0 then (2*t.val-1,-1) else if i.val=1 then (1,2*t.val-1)
  else if i.val=2 then (2*t.val-1,1) else (-1,2*t.val-1)
theorem h1BoundaryCornerParameterIsEndpoint (i j : Fin 4) (t u : Interval)
    (ht : t=0 ∨ t=1) (he :
      (if j.val=0 then (2*u.val-1,-1) else if j.val=1 then (1,2*u.val-1)
       else if j.val=2 then (2*u.val-1,1) else (-1,2*u.val-1)) =
      (if i.val=0 then (2*t.val-1,-1) else if i.val=1 then (1,2*t.val-1)
       else if i.val=2 then (2*t.val-1,1) else (-1,2*t.val-1) : ℝ × ℝ)) : u=0 ∨ u=1 := by
  have hf := congrArg Prod.fst he
  have hs := congrArg Prod.snd he
  fin_cases i <;> rcases ht with rfl | rfl <;> fin_cases j
  all_goals norm_num at hf
  all_goals norm_num at hs
  all_goals first |
    (left;exact_mod_cast hf) | (left;exact_mod_cast hs) |
    (right;exact_mod_cast hf) | (right;exact_mod_cast hs) |
    (left;apply Subtype.ext;change u.val=0;linarith only [hf,hs]) |
    (right;apply Subtype.ext;change u.val=1;linarith only [hf,hs])
end
end CurveComplex.LocalSurgery
