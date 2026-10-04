import CurveComplexGenusTwo.Topology.IntersectionParity.AxisChart
import CurveComplexGenusTwo.Topology.IntersectionParity.CrossingChartCoordinates
namespace CurveComplex.LocalSurgery

noncomputable def selectedAxisChart
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (a : Curve S) (p : a.image) : OpenPartialHomeomorph S (ℝ × ℝ) := by
  let H := embedded_curve_has_local_axis_chart a p p.property
  let U := H.choose
  let V := H.choose_spec.choose
  let hp := H.choose_spec.choose_spec.choose
  let h := H.choose_spec.choose_spec.choose_spec.choose
  let spec := H.choose_spec.choose_spec.choose_spec.choose_spec
  exact crossingPartialChart U V spec.1 spec.2.1 ⟨p, hp⟩ h

/-- The complement is the distinguished global sheet chart; the remaining
indices are actual points on the embedded curve with their chosen axis charts. -/
noncomputable def cutAtlasDomain
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (a : Curve S) : Option a.image → Set S
  | none => a.imageᶜ
  | some p => (selectedAxisChart a p).source

noncomputable def cutAtlasIndexAt
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (a : Curve S) (x : S) : Option a.image := by
  classical
  exact if hx : x ∈ a.image then some ⟨x, hx⟩ else none

noncomputable def cutAtlasOffAxisLabel
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (a : Curve S) : Option a.image → S → ZMod 2
  | none, _ => 0
  | some p, x => if 0 < (selectedAxisChart a p x).1 then 1 else 0

end CurveComplex.LocalSurgery
