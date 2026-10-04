import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects
namespace CurveComplex.HyperellipticModel
open Set CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance integrationLocalInstance_ActualObjectEndpointUniformHeaders_1 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
theorem actual_object_endpoint_labels_uniform (M : HyperellipticModel E S) (σ : Finset (EssentialArcClass M))
    (O : Finset (EssentialArcClass M)) (hO : O ∈ actualObjectFamily M σ) :
    ∃ v ∈ σ, ∀ w ∈ O, classEndpoints M w = classEndpoints M v := by
  classical
  simp only [actualObjectFamily,Finset.mem_union,Finset.mem_image,Finset.mem_filter] at hO
  rcases hO with ⟨v,⟨hv,hloop⟩,rfl⟩ | ⟨v,⟨hv,hn,hcard⟩,rfl⟩
  · refine ⟨v,hv,?_⟩
    intro w hw
    exact congrArg (classEndpoints M) (Finset.mem_singleton.mp hw)
  · refine ⟨v,hv,?_⟩
    intro w hw
    exact (Finset.mem_filter.mp hw).2.2
end CurveComplex.HyperellipticModel
