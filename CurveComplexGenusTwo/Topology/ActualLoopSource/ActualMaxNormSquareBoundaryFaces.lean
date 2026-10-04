import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareConeFiniteFaceContactArcs
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The four literal boundary sides of the product max-norm square. -/
noncomputable def actualMaxNormSquareBoundaryFace (i : Fin 4) :
    C(Interval,{z : ℝ × ℝ // ‖z‖=1}) := by
  let raw : Interval → ℝ × ℝ := fun t =>
    if i.val=0 then (2*t.val-1,-1) else if i.val=1 then (1,2*t.val-1)
    else if i.val=2 then (2*t.val-1,1) else (-1,2*t.val-1)
  have hn (t : Interval) : ‖raw t‖=1 := by
    have ha : |2*t.val-1|≤1 := abs_le.mpr (by
      constructor <;> linarith only [t.property.1,t.property.2])
    fin_cases i <;> simp [raw,Prod.norm_def,Real.norm_eq_abs,max_eq_left ha,max_eq_right ha]
  exact ⟨fun t => ⟨raw t,hn t⟩,by fin_cases i <;> simp [raw] <;> fun_prop⟩
/-- Each actual boundary side is embedded, without assuming a boundary graph. -/
theorem actual_max_norm_square_boundary_face_embedding (i : Fin 4) :
    IsEmbedding (actualMaxNormSquareBoundaryFace i) := by
  refine (actualMaxNormSquareBoundaryFace i).continuous.isClosedEmbedding ?_ |>.isEmbedding
  intro x y he
  have hh := congrArg Subtype.val he
  fin_cases i
  · have hk := congrArg Prod.fst hh
    apply Subtype.ext
    change 2*x.val-1=2*y.val-1 at hk
    linarith only [hk]
  · have hk := congrArg Prod.snd hh
    apply Subtype.ext
    change 2*x.val-1=2*y.val-1 at hk
    linarith only [hk]
  · have hk := congrArg Prod.fst hh
    apply Subtype.ext
    change 2*x.val-1=2*y.val-1 at hk
    linarith only [hk]
  · have hk := congrArg Prod.snd hh
    apply Subtype.ext
    change 2*x.val-1=2*y.val-1 at hk
    linarith only [hk]
end CurveComplex.HyperellipticModel
