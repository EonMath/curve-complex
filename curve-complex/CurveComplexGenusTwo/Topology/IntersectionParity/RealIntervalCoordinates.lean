import Mathlib
open Set Topology

namespace CurveComplex.LocalSurgery

/-- Extend interval coordinates to the real line by the genuine continuous
clamping map. This permits finite ordered-event induction with real endpoints. -/
noncomputable def clampToUnitInterval : C(ℝ, unitInterval) :=
  ⟨Set.projIcc 0 1 (by norm_num), continuous_projIcc⟩

/-- An actual continuous interval path, viewed on the real line. -/
noncomputable def realIntervalPath
    {X : Type*} [TopologicalSpace X] (g : C(unitInterval, X)) : C(ℝ, X) :=
  g.comp clampToUnitInterval

end CurveComplex.LocalSurgery
