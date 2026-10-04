import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
namespace CurveComplex.HyperellipticModel
open Set
theorem open_embedding_bounded_face_transport {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Topology.IsOpenEmbedding f) (H G : Set X)
    (hG : IsComplementComponent H G) (ho : IsOpen G)
    (hk : IsCompact (closure G)) (hfr : frontier G ⊆ H) :
    IsComplementComponent (f '' H) (f '' G) := by
  have hc : IsConnected (f '' G) := hG.2.1.image f hf.continuous.continuousOn
  have hopen : IsOpen (f '' G) := hf.isOpenMap G ho
  have hdis : f '' G ⊆ (f '' H)ᶜ := by
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hzy⟩
    exact hG.2.2.1 hx (hf.injective hzy ▸ hz)
  refine ⟨hc.nonempty, hc, hdis, ?_⟩
  intro V hV hsub hVc
  apply Set.Subset.antisymm
  · apply hV.isPreconnected.subset_of_closure_inter_subset hopen
    · obtain ⟨y, hy⟩ := hc.nonempty
      exact ⟨y, hsub hy, hy⟩
    · intro y hy
      have hcl : closure (f '' G) ⊆ f '' closure G :=
        closure_minimal (image_mono subset_closure) (hk.image hf.continuous).isClosed
      obtain ⟨x, hx, rfl⟩ := hcl hy.1
      by_cases hxG : x ∈ G
      · exact ⟨x, hxG, rfl⟩
      · have hxfr : x ∈ frontier G := ho.frontier_eq ▸ ⟨hx, hxG⟩
        exact False.elim (hVc hy.2 ⟨x, hfr hxfr, rfl⟩)
  · exact hsub

end CurveComplex.HyperellipticModel
