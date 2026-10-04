import Mathlib
namespace CurveComplex.LocalSurgery
open Set Topology
open scoped unitInterval
/-- Actual local two-sided transverse trace in every chart adapted to the given carrier. -/
def actualPhysicalTraceTransverse {S : Type*} [TopologicalSpace S]
    (A : Set S) (β : C(unitInterval,S)) : Prop :=
  ∀ u : unitInterval,β u∈A →
    ∀ C : OpenPartialHomeomorph S (ℝ × ℝ),β u∈C.source →
    (∀ x∈C.source,x∈A ↔ (C x).1=0) →
    ∃ δ : ℝ,0<δ ∧ ∀ v w : unitInterval,
      u.val-δ<v.val → v<u → u<w → w.val<u.val+δ →
      β v∈C.source ∧ β w∈C.source ∧
      (C (β v)).1≠0 ∧ (C (β w)).1≠0 ∧
      ((C (β v)).1<0 ↔ ¬(C (β w)).1<0)
end CurveComplex.LocalSurgery
