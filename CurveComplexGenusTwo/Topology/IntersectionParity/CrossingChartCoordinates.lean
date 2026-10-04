import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import Mathlib
namespace CurveComplex.LocalSurgery

/-- Convert the actual subtype homeomorphism in CrossesAt into Mathlib's
open partial coordinate chart, with no extension outside the open sets used. -/
noncomputable def crossingPartialChart
    {S : Type*} [TopologicalSpace S]
    (U : Set S) (V : Set (ℝ × ℝ))
    (hU : IsOpen U) (hV : IsOpen V) (p : U) (h : U ≃ₜ V) :
    OpenPartialHomeomorph S (ℝ × ℝ) :=
  ((⟨U, hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
      ⟨p⟩).symm.trans
    (h.toOpenPartialHomeomorph.trans
      ((⟨V, hV⟩ : TopologicalSpace.Opens (ℝ × ℝ)).openPartialHomeomorphSubtypeCoe
        ⟨h p⟩))

/-- The coordinate change between two actual open plane charts. -/
noncomputable def axisChartChange
    {S : Type*} [TopologicalSpace S]
    (h k : OpenPartialHomeomorph S (ℝ × ℝ)) :
    OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) := h.symm.trans k

end CurveComplex.LocalSurgery
