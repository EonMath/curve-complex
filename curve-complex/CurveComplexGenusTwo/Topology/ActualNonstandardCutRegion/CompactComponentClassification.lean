import CurveComplexGenusTwo.Topology.ActualNonstandardCutRegion.ManifoldCoreConnected
import ClassificationOfSurfaces.EvalStatement

open Set Topology
open scoped Manifold
open LeanEval.Topology.ClassificationOfSurfaces

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

/-- The actual interior in each compact connected cut component is connected;
the component is selected in the existing carrier, with its inherited charts. -/
theorem compact_component_intrinsic_core_connected
    (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    (core : Set M) (hdense : Dense core)
    (hcore : core = ModelWithCorners.interior (I := 𝓡∂ 2) M)
    (z : M) : IsConnected (connectedComponent z ∩ core) := by
  letI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 2) M
  let K : TopologicalSpace.Opens M := ⟨connectedComponent z, isOpen_connectedComponent⟩
  letI : ConnectedSpace K := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hdK : Dense ((Subtype.val : K → M) ⁻¹' core) :=
    hdense.preimage K.isOpenEmbedding'.isOpenMap
  have hcoreK : (Subtype.val : K → M) ⁻¹' core =
      ModelWithCorners.interior (I := 𝓡∂ 2) K := by
    rw [hcore, ModelWithCorners.interior_open]
  rw [hcoreK] at hdK
  have hc := connected_intrinsic_interior_of_dense K hdK
  rw [← hcoreK] at hc
  have himage : (Subtype.val : K → M) '' ((Subtype.val : K → M) ⁻¹' core) =
      connectedComponent z ∩ core := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hxK, hxcore⟩
      exact ⟨⟨x, hxK⟩, hxcore, rfl⟩
  rw [← himage]
  exact hc.image _ continuous_subtype_val.continuousOn

/-- Classify a selected compact connected component using the proved surface
classification theorem; the inherited manifold is constructed automatically. -/
theorem compact_halfspace_connected_component_normal_form
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] [IsManifold (𝓡∂ 2) 0 M]
    (z : M) :
    Nonempty ((connectedComponent z) ≃ₜ SphereRepresentative) ∨
      ∃ p n,
        ((1 ≤ p ∨ 1 ≤ n) ∧
          Nonempty ((connectedComponent z) ≃ₜ Quot (OrientableRel p n))) ∨
        (1 ≤ p ∧
          Nonempty ((connectedComponent z) ≃ₜ Quot (NonOrientableRel p n))) := by
  letI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 2) M
  let K : TopologicalSpace.Opens M := ⟨connectedComponent z, isOpen_connectedComponent⟩
  letI : ConnectedSpace K := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  letI : CompactSpace K := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  exact classification_of_surfaces K

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut

#print axioms CurveComplexGenusTwo.SourceTopology.ThreeArcCut.compact_component_intrinsic_core_connected
#print axioms CurveComplexGenusTwo.SourceTopology.ThreeArcCut.compact_halfspace_connected_component_normal_form
