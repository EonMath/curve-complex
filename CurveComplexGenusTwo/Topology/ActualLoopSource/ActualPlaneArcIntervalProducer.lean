import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSurfaceEndpointCap
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
/-- An actual original planar boundary arc constructs its embedded
unit-interval parametrization, with exact original image and endpoints. -/
theorem actual_plane_arc_interval_producer {A : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) :
    ∃ f : C(unitInterval,Plane), IsEmbedding f ∧ range f=A ∧ f 0=p ∧ f 1=q := by
  obtain ⟨g,hgc,hgi,himage,h0,h1⟩ := hA
  let f : C(unitInterval,Plane) := ⟨fun t => g t, hgc.domRestrict⟩
  have hfi : Function.Injective f := by
    intro s t he
    exact Subtype.ext (hgi s.property t.property he)
  have hrange : range f=g '' unitInterval := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨t.val,t.property,rfl⟩
    · rintro ⟨t,ht,rfl⟩; exact ⟨⟨t,ht⟩,rfl⟩
  exact ⟨f,(f.continuous.isClosedEmbedding hfi).isEmbedding,hrange.trans himage,h0,h1⟩
end CurveComplex.HyperellipticModel
