import CurveComplexGenusTwo.Topology.Extraction
import CurveComplexGenusTwo.Topology.TopologicalArcJoin
import Schoenflies.ArcComplement
import Schoenflies.Concatenate
import Schoenflies.SkeletonAccess
import Schoenflies.Accessible
import Schoenflies.Subarc

open Set Metric unitInterval
namespace Schoenflies

/-- Planar Jordan-arc completion, the geometric input needed to obtain an
exact regular disk/core pair for an arbitrary embedded arc. This is a helper
obligation for the regular-neighborhood producer in Lemma 4.10, not a quoted
standalone statement of that lemma. No polygonal or smooth hypothesis is made.

REVIEW STATUS: approved in REPORT_BATCH3.md and guarded as astra_arc2_jordan.
The proof reduces to the explicit endpoint-access construction below. -/
theorem exists_jordan_completion_of_isArcBetween
    {P : Set Plane} {a b : Plane} (hP : IsArcBetween P a b) :
    ∃ A : Set Plane, IsArcBetween A a b ∧
      A ∩ P = {a, b} ∧ IsJordanCurve (A ∪ P) := by
  obtain ⟨E₁, u, hE₁, hu, havoid₁⟩ := endpoint_access_of_isArcBetween hP
  obtain ⟨E₂, v, hE₂, hv, havoid₂⟩ := endpoint_access_of_isArcBetween hP.reverse
  exact jordan_completion_of_access_arcs hP hE₁ hE₂ hu hv havoid₁ havoid₂

end Schoenflies

#print axioms Schoenflies.exists_jordan_completion_of_isArcBetween
