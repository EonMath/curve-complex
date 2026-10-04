import CurveComplexGenusTwo.Topology.IntersectionParity.CutCoverDefinitions
import CurveComplexGenusTwo.Topology.IntersectionParity.ActualLoopSweep
open scoped unitInterval
open Set Topology

namespace CurveComplex.LocalSurgery

/-- The actual sheet label on the complement of the cut curve. -/
noncomputable def cutCoverComplementSheet
    {S : Type*} [TopologicalSpace S] {a : Curve S} (A : CurveCutCover a) :
    C({z : A.core.TotalSpace // A.core.proj z ∉ a.image}, ZMod 2) := by
  refine ⟨fun z => (A.complementTriv z.val).2, ?_⟩
  apply continuous_snd.comp
  apply A.complementTriv.continuousOn.comp_continuous continuous_subtype_val
  intro z
  apply A.complementTriv.mem_source.mpr
  rw [A.complement_baseSet]
  exact z.property

/-- The continuous covering lift of the actual curve loop.  The starting point
is an actual total-space point over the loop's basepoint. -/
noncomputable def cutCoverCurveLift
    {S : Type*} [TopologicalSpace S] {a : Curve S} (A : CurveCutCover a)
    (b : Curve S) : C(I, A.core.TotalSpace) :=
  curveInitialCoverLift
    (FiberBundle.isCoveringMap (F := ZMod 2) (E := A.core.Fiber))
    b ⟨intervalCurveLoop b 0, (0 : ZMod 2)⟩ rfl

/-- Off-cut sheet coordinates along any actual lifted path. -/
noncomputable def cutCoverLiftSheet
    {S : Type*} [TopologicalSpace S] {a : Curve S} (A : CurveCutCover a)
    (g : C(I, A.core.TotalSpace)) :
    C({u : I // A.core.proj (g u) ∉ a.image}, ZMod 2) :=
  (cutCoverComplementSheet A).comp
    ⟨fun u => ⟨g u.val, u.property⟩,
      (g.continuous.comp continuous_subtype_val).subtype_mk _⟩

end CurveComplex.LocalSurgery
