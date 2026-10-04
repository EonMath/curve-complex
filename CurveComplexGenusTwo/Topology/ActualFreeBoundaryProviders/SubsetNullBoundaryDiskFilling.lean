import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.ActualTwoSideDiskSubsetDescent
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalDiskContainment

namespace CoherentEndpointMotion
open CurveComplex Set Topology Schoenflies

/-- A nullhomotopic embedded circle in the caller's literal subset bounds an
actual embedded disk there, using ambient filling and checked containment. -/
theorem subset_nullhomotopic_curve_bounds_literal_disk
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (c : Curve ↥F)
    (hc : (⟨c.map,c.embedded.continuous⟩ : C(Circle,↥F)).Nullhomotopic) :
    ∃ d : C(Metric.closedBall (0 : Plane) 1,↥F),
      IsEmbedding d ∧
      d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = c.image := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  let valMap : C(↥F,S) := ⟨Subtype.val,continuous_subtype_val⟩
  let cS : Curve S := ⟨Subtype.val ∘ c.map,IsEmbedding.subtypeVal.comp c.embedded⟩
  have hcS : (⟨cS.map,cS.embedded.continuous⟩ : C(Circle,S)).Nullhomotopic :=
    hc.comp_right valMap
  obtain ⟨d,hd,hbd⟩ := RegionalEmbeddedFamily.nullhomotopic_curve_bounds_disk_on_closed_surface
    S (cS.map 1) cS hcS
  have himage : cS.image = Subtype.val '' c.image := Set.range_comp Subtype.val c.map
  have hbdF : d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      Subtype.val '' c.image := hbd.trans himage
  have hinside : range d ⊆ F :=
    RegionalEmbeddedFamily.embedded_disk_with_region_nullhomotopic_boundary_lies_in_region
      S g hg hS F c hc d hd hbdF
  let D : C(Metric.closedBall (0 : Plane) 1,↥F) :=
    ⟨fun z => ⟨d z,hinside (Set.mem_range_self z)⟩,d.continuous.subtype_mk _⟩
  have hD : IsEmbedding D := (D.continuous.isClosedEmbedding (by
    intro z w he
    exact hd.injective (congrArg Subtype.val he))).isEmbedding
  refine ⟨D,hD,?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩
    obtain ⟨w,hw,he⟩ := hbdF ▸ Set.mem_image_of_mem d hz
    have he : w = D z := Subtype.ext he
    exact he ▸ hw
  · intro y hy
    obtain ⟨z,hz,he⟩ := hbdF.symm ▸
      (show y.val ∈ Subtype.val '' c.image from ⟨y,hy,rfl⟩)
    exact ⟨z,hz,Subtype.ext he⟩

end CoherentEndpointMotion
