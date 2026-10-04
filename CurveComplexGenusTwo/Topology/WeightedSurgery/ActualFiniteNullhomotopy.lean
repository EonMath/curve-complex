import CurveComplexGenusTwo.Topology.WeightedSurgery.FiniteRealizationTransport
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Foundations.SingularComparison

namespace CurveComplex.HyperellipticModel.ArcSurgery

open CurveGenusTwo.Filtration CurveComplex.WeightedFlowScratch
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

noncomputable def activeArcClass (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (v : EssentialArcClass M) :
    ActiveVertex (actualA M) := by
  refine ⟨v, ?_⟩
  change IsArcSimplex M {v}
  refine ⟨fun _ => Quotient.out v, ?_, ?_⟩
  · intro w
    have hw : w.val = v := Finset.mem_singleton.mp w.property
    exact (Quotient.out_eq v).trans hw.symm
  · intro w u hwu
    exfalso
    apply hwu
    apply Subtype.ext
    exact (Finset.mem_singleton.mp w.property).trans
      (Finset.mem_singleton.mp u.property).symm

end CurveComplex.HyperellipticModel.ArcSurgery
