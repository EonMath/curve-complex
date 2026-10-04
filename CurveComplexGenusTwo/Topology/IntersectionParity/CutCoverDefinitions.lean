import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib
open Set Topology

namespace CurveComplex.LocalSurgery

/-- Actual local geometry of the cut-and-double cover of a curve.
The defining condition prescribes how sheet coordinates differ on the two
sides of each local axis chart. It does not assume intersection parity. -/
structure CurveCutCover {S : Type*} [TopologicalSpace S] (a : Curve S) where
  core : FiberBundleCore (Option a.image) S (ZMod 2)
  complementTriv : Bundle.Trivialization (ZMod 2) core.proj
  complement_baseSet : complementTriv.baseSet = a.imageᶜ
  localCut : ∀ p ∈ a.image,
    ∃ chart : OpenPartialHomeomorph S (ℝ × ℝ),
      p ∈ chart.source ∧ chart p = (0, 0) ∧
      (∀ x ∈ chart.source, x ∈ a.image ↔ (chart x).1 = 0) ∧
      ∃ t : Bundle.Trivialization (ZMod 2) core.proj,
        t.baseSet = chart.source ∧
        ∀ z : core.TotalSpace,
          core.proj z ∈ chart.source → core.proj z ∉ a.image →
          (complementTriv z).2 = (t z).2 +
            (if 0 < (chart (core.proj z)).1 then (1 : ZMod 2) else 0)

end CurveComplex.LocalSurgery
