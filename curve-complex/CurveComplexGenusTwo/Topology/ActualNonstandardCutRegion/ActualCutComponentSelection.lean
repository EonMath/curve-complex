import CurveComplexGenusTwo.Topology.ActualCompactSideDoubledCut.OriginalCompactSideDoubledCut
import CurveComplexGenusTwo.Topology.ActualNonstandardCutRegion.CompactComponentClassification
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry

open CurveComplex Set Topology
open scoped Manifold
open CurveComplex.HyperellipticModel

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

/-- Select the actual compact cut component above the caller's literal U.
Its open core projects exactly to U and its compact image exactly to closure U.
All incidences are on the same supplied side-doubled cut. -/
theorem actual_cut_component_above_original_region
    (S : Type) [TopologicalSpace S] [T2Space S]
    (Q B F : Set S) {n : ℕ} (a : Fin n → C(Interval, ↥Q))
    (C : CompactSideDoubledCut S Q B Fᶜ a)
    (U : Set S) (hU : IsComplementComponent F U) :
    letI : TopologicalSpace C.Carrier := C.topology
    ∃ z : C.Carrier,
      IsConnected (connectedComponent z ∩ C.core) ∧
      (fun w => (C.projection w).val) '' (connectedComponent z ∩ C.core) = U ∧
      (fun w => (C.projection w).val) '' connectedComponent z = closure U := by
  classical
  letI : TopologicalSpace C.Carrier := C.topology
  letI : CompactSpace C.Carrier := C.compact
  letI : T2Space C.Carrier := C.hausdorff
  letI : ChartedSpace (EuclideanHalfSpace 2) C.Carrier := C.charts
  letI : LocallyConnectedSpace C.Carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 2) C.Carrier
  have hcdense : Dense C.core := dense_iff_closure_eq.mpr C.core_dense
  obtain ⟨x, hx⟩ := hU.1
  let zc : C.core := C.coreEquiv.symm ⟨x, hU.2.2.1 hx⟩
  let z := zc.val
  let f : U → C.Carrier := fun y =>
    (C.coreEquiv.symm ⟨y.val, hU.2.2.1 y.property⟩).val
  have hfc : Continuous f := continuous_subtype_val.comp
    (C.coreEquiv.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
  letI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hU.2.1
  have hlifts : IsConnected (Set.range f) := by
    simpa only [Set.image_univ] using isConnected_univ.image f hfc.continuousOn
  have hzlift : z ∈ Set.range f := ⟨⟨x, hx⟩, rfl⟩
  have hliftK : Set.range f ⊆ connectedComponent z :=
    hlifts.isPreconnected.subset_connectedComponent hzlift
  let π : C(C.Carrier, S) :=
    ⟨fun w => (C.projection w).val, continuous_subtype_val.comp C.projection.continuous⟩
  have hconn : IsConnected (connectedComponent z ∩ C.core) :=
    compact_component_intrinsic_core_connected C.Carrier C.core hcdense
      C.core_eq_manifold_interior z
  have hsubset : π '' (connectedComponent z ∩ C.core) ⊆ Fᶜ := by
    rintro y ⟨w, ⟨hwK, hwcore⟩, rfl⟩
    have hagree := C.core_agrees ⟨w, hwcore⟩
    change (C.projection w).val ∈ Fᶜ
    rw [hagree]
    exact (C.coreEquiv ⟨w, hwcore⟩).property
  have hcontains : U ⊆ π '' (connectedComponent z ∩ C.core) := by
    intro y hy
    let v : C.core := C.coreEquiv.symm ⟨y, hU.2.2.1 hy⟩
    refine ⟨v.val, ⟨hliftK ⟨⟨y, hy⟩, rfl⟩, v.property⟩, ?_⟩
    change (C.projection v.val).val = y
    rw [C.core_agrees v]
    exact congrArg Subtype.val (C.coreEquiv.apply_symm_apply _)
  have hcoreimage : π '' (connectedComponent z ∩ C.core) = U :=
    hU.2.2.2 _ (hconn.image π π.continuous.continuousOn) hcontains hsubset
  have hdenseK : connectedComponent z ⊆ closure (connectedComponent z ∩ C.core) := by
    intro w hw
    rw [mem_closure_iff]
    intro V hVo hwV
    obtain ⟨y, hycore, hyV, hyK⟩ :=
      hcdense.exists_mem_open (hVo.inter isOpen_connectedComponent) ⟨w, hwV, hw⟩
    exact ⟨y, hyV, hyK, hycore⟩
  have hclosedimage : IsClosed (π '' connectedComponent z) :=
    (isClosed_connectedComponent.isCompact.image π.continuous).isClosed
  have himage : π '' connectedComponent z = closure U := by
    apply Set.Subset.antisymm
    · rintro y ⟨w, hw, rfl⟩
      rw [← hcoreimage]
      exact mem_closure_image π.continuous.continuousAt (hdenseK hw)
    · apply closure_minimal
      · rw [← hcoreimage]
        exact Set.image_mono Set.inter_subset_left
      · exact hclosedimage
  exact ⟨z, hconn, hcoreimage, himage⟩

/-- The selected compact component's core identifies homeomorphically with
the literal original region, using the same cut projection. -/
theorem selected_cut_component_core_homeomorph
    (S : Type) [TopologicalSpace S]
    (Q B F : Set S) {n : ℕ} (a : Fin n → C(Interval, ↥Q))
    (C : CompactSideDoubledCut S Q B Fᶜ a) :
    letI : TopologicalSpace C.Carrier := C.topology
    ∀ (z : C.Carrier) (U : Set S),
      (fun w => (C.projection w).val) '' (connectedComponent z ∩ C.core) = U →
      Nonempty (↥(connectedComponent z ∩ C.core) ≃ₜ ↥U) := by
  letI : TopologicalSpace C.Carrier := C.topology
  intro z U hcoreimage
  let K := connectedComponent z ∩ C.core
  let inc : K → C.core := Set.inclusion Set.inter_subset_right
  let f : K → S := fun w => (C.projection w.val).val
  have heq : f = (Subtype.val : ↥(Fᶜ) → S) ∘ C.coreEquiv ∘ inc := by
    funext w
    exact C.core_agrees (inc w)
  have hf : IsEmbedding f := by
    rw [heq]
    exact Topology.IsEmbedding.subtypeVal.comp
      (C.coreEquiv.isEmbedding.comp (Topology.IsEmbedding.inclusion _))
  have hmem : ∀ w : K, f w ∈ U := by
    intro w
    rw [← hcoreimage]
    exact ⟨w.val, w.property, rfl⟩
  let g : K → U := fun w => ⟨f w, hmem w⟩
  have hg : IsEmbedding g := hf.codRestrict U hmem
  have hgs : Function.Surjective g := by
    intro y
    have hy : y.val ∈ (fun w => (C.projection w).val) '' K :=
      hcoreimage.symm ▸ y.property
    obtain ⟨w, hw, hwy⟩ := hy
    exact ⟨⟨w, hw⟩, Subtype.ext hwy⟩
  exact ⟨IsHomeomorph.homeomorph g
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hg, hgs⟩)⟩

/-- The actual cut projection embeds the full open core. Boundary-side
identifications have no bearing on this assertion. -/
theorem cut_core_projection_isEmbedding
    (S : Type) [TopologicalSpace S]
    (Q B F : Set S) {n : ℕ} (a : Fin n → C(Interval, ↥Q))
    (C : CompactSideDoubledCut S Q B Fᶜ a) :
    letI : TopologicalSpace C.Carrier := C.topology
    IsEmbedding (fun w : C.core => C.projection w.val) := by
  letI : TopologicalSpace C.Carrier := C.topology
  have heq : (fun w : C.core => (C.projection w.val).val) =
      (Subtype.val : ↥(Fᶜ) → S) ∘ C.coreEquiv := by
    funext w
    exact C.core_agrees w
  have hf : IsEmbedding (fun w : C.core => (C.projection w.val).val) := by
    rw [heq]
    exact Topology.IsEmbedding.subtypeVal.comp C.coreEquiv.isEmbedding
  exact Topology.IsEmbedding.subtypeVal.of_comp_iff.mp hf

/-- Every actual compact cut boundary point projects to the original
forbidden set; base boundary and both arc sides are explicitly exhausted. -/
theorem cut_boundary_projects_to_forbidden
    (S : Type) [TopologicalSpace S]
    (Q B F : Set S) {n : ℕ} (a : Fin n → C(Interval, ↥Q))
    (C : CompactSideDoubledCut S Q B Fᶜ a)
    (hB : B ⊆ F) (ha : ∀ i t, (a i t).val ∈ F) :
    letI : TopologicalSpace C.Carrier := C.topology
    ∀ w : C.Carrier, w ∉ C.core → (C.projection w).val ∈ F := by
  letI : TopologicalSpace C.Carrier := C.topology
  intro w hw
  have hboundary : w ∈ C.coreᶜ := hw
  rw [C.boundary_exhaustion] at hboundary
  rcases hboundary with hwB | hwside
  · apply hB
    exact (Set.ext_iff.mp C.base_boundary_image (C.projection w).val).mp
      ⟨⟨w, hwB⟩, rfl⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hwside
    rcases hi with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [C.side_agrees]
      exact ha i t
    · rw [C.side_agrees]
      exact ha i t

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut

#print axioms CurveComplexGenusTwo.SourceTopology.ThreeArcCut.actual_cut_component_above_original_region
#print axioms CurveComplexGenusTwo.SourceTopology.ThreeArcCut.selected_cut_component_core_homeomorph
#print axioms CurveComplexGenusTwo.SourceTopology.ThreeArcCut.cut_boundary_projects_to_forbidden
