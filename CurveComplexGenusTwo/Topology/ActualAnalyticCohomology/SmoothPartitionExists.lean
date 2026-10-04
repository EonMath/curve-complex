import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.SerreIntegrationData
import Mathlib.Geometry.Manifold.PartitionOfUnity

open TopologicalSpace
open scoped Manifold ContDiff

namespace SameAtlasAnalyticCohomology

universe u v

section ApprovedDefinitions

variable {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]

end ApprovedDefinitions

/-- Finite subordinate smooth partitions exist on the given compact Riemann
surface. The partition uses real-smooth weights in every preferred chart of
this same complex atlas. McMullen, printed pp.72–73; used on pp.79–80. -/
theorem exists_subordinateSmoothPartition
    {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E]
    (U : OpenCover E) [Fintype U.Index]
    [T2Space E] [CompactSpace E] [Nonempty E] [PreconnectedSpace E] :
    Nonempty (SubordinateSmoothPartition U) := by
  classical
  let : IsManifold 𝓘(ℝ, ℂ) ∞ E := by
    apply isManifold_of_contDiffOn
    intro e e' he he'
    have hc := StructureGroupoid.compatible
      (G := contDiffGroupoid ∞ 𝓘(ℂ)) he he'
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hc
    have hs : ContDiffOn ℂ ∞ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
      simpa only [contDiffPregroupoid, Function.comp_def, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Set.preimage_id, Set.range_id,
        Set.inter_univ, id_eq] using hc.1
    simpa only [Function.comp_def, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Set.preimage_id, Set.range_id,
      Set.inter_univ, id_eq] using hs.restrict_scalars ℝ
  have hcover : (Set.univ : Set E) ⊆ ⋃ i, (U.opens i : Set E) := by
    rw [← Opens.coe_iSup, U.covers]
    exact Set.Subset.rfl
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, ℂ) isClosed_univ (fun i => (U.opens i : Set E))
    (fun i => (U.opens i).isOpen) hcover
  refine ⟨{
    weight := fun i x => ρ i x
    smoothWeight := ?_
    nonnegativeWeight := fun i x => ρ.nonneg i x
    supportWeight := fun i => hρ i
    partitionOne := ?_ }⟩
  · intro i a
    have h := (ρ i).contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) a)
    simpa only [contMDiffOn_iff_contDiffOn, extChartAt_coe_symm, extChartAt_target,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.comp_def, Set.preimage_id, Set.range_id,
      Set.inter_univ, id_eq] using h
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)


end SameAtlasAnalyticCohomology
