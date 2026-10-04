import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedDiskFreeDescent
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.MarkedDescentCandidate
import CurveComplexGenusTwo.Topology.ActualMain14CNext.actual_given_paired_component_reference_returning_diskNamedPROVED
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
open LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain
open scoped Manifold ContDiff
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Schoenflies.Plane E]
set_option maxHeartbeats 10000000
theorem circle24_full_preimage_isotopy_descends_marked
    (M : HyperellipticModel E S) (c d : Circle24 M)
    (hup : AmbientIsotopy.Rel (M.cover.projection ⁻¹' c.val.image)
      (M.cover.projection ⁻¹' d.val.image)) :
    MarkedIsotopyRel M c.val.image d.val.image := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have hDiskFree := M.actual_original_circle24_paired_four_crosspair_disk_free_preparation c d hup
  obtain ⟨c',d',hci,hdi,htbase,a0,a1,b0,b1,H,ha,hb,hAd,hBd,hDA,hDB,hH0,hH1,hap0,hap1,hbp0,hbp1,hAc0,hAc1,hBc0,hBc1,ht00,ht01,ht10,ht11,hfree00,hfree01,hfree10,hfree11⟩ := hDiskFree
  have hp0 : b0.val.image ⊆ M.cover.projection ⁻¹' d'.val.image := by
    intro x hx
    have hh : x ∈ b0.val.image ∪ b1.val.image := Or.inl hx
    rw [hb] at hh
    exact hh
  have hp1 : b1.val.image ⊆ M.cover.projection ⁻¹' d'.val.image := by
    intro x hx
    have hh : x ∈ b0.val.image ∪ b1.val.image := Or.inr hx
    rw [hb] at hh
    exact hh
  have hiso0 : AmbientIsotopy.Rel a0.val.image b0.val.image := ⟨H,hH0⟩
  have hiso1 : AmbientIsotopy.Rel a1.val.image b1.val.image := ⟨H,hH1⟩
  have hdisjoint : Disjoint c'.val.image d'.val.image := by
    apply Set.disjoint_left.mpr
    intro y hyc hyd
    obtain ⟨x,rfl⟩ := M.cover.projection_surjective y
    have hxa : x ∈ a0.val.image ∪ a1.val.image := by rw [ha]; exact hyc
    have hxb : x ∈ b0.val.image ∪ b1.val.image := by rw [hb]; exact hyd
    rcases hxa with hx0 | hx1 <;> rcases hxb with hy0 | hy1
    · exact hfree00.false (M.actual_given_paired_component_reference_returning_disk a0 b0 b0 d'.val hp0 hp0 ht00 hiso0 ⟨x,hx0,hy0⟩).some
    · exact hfree01.false (M.actual_given_paired_component_reference_returning_disk a0 b0 b1 d'.val hp0 hp1 ht01 hiso0 ⟨x,hx0,hy1⟩).some
    · exact hfree10.false (M.actual_given_paired_component_reference_returning_disk a1 b1 b0 d'.val hp1 hp0 ht10 hiso1 ⟨x,hx1,hy0⟩).some
    · exact hfree11.false (M.actual_given_paired_component_reference_returning_disk a1 b1 b1 d'.val hp1 hp1 ht11 hiso1 ⟨x,hx1,hy1⟩).some
  have hup' : AmbientIsotopy.Rel (M.cover.projection ⁻¹' c'.val.image) (M.cover.projection ⁻¹' d'.val.image) := by
    refine ⟨H,?_⟩
    rw [←ha,←hb,Set.image_union,hH0,hH1]
  have hTerminal := M.actual_original_disjoint_circle24_full_preimage_isotopy_descends_marked c' d' hup' hdisjoint
  exact (markedIsotopy_equivalence M).trans hci
    ((markedIsotopy_equivalence M).trans hTerminal ((markedIsotopy_equivalence M).symm hdi))

end CurveComplex.HyperellipticModel
