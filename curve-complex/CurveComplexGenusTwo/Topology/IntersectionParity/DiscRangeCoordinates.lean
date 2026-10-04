import CurveComplexGenusTwo.Foundations.Definitions

namespace CurveComplex.LocalSurgery

/-- Actual continuous lift through an embedded closed disk, using its inverse
homeomorphism onto its range. -/
noncomputable def curveInDiscLift
    {S : Type*} [TopologicalSpace S]
    (c : Curve S)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d) (hc : c.image ⊆ Set.range d) :
    C(Circle, Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  ⟨fun z => hd.toHomeomorph.symm ⟨c.map z, hc ⟨z, rfl⟩⟩,
    hd.toHomeomorph.symm.continuous.comp
      (c.embedded.continuous.subtype_mk (fun z => hc ⟨z, rfl⟩))⟩

noncomputable def curveInDiscCoordinates
    {S : Type*} [TopologicalSpace S]
    (c : Curve S)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d) (hc : c.image ⊆ Set.range d) :
    C(Circle, EuclideanSpace ℝ (Fin 2)) :=
  ⟨fun z => (curveInDiscLift c d hd hc z).val,
    continuous_subtype_val.comp (curveInDiscLift c d hd hc).continuous⟩

end CurveComplex.LocalSurgery
