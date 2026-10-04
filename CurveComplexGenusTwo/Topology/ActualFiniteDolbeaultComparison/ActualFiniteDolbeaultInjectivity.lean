import CurveComplexGenusTwo.Topology.ActualFiniteDolbeaultComparison.ActualFiniteDolbeaultInjectivityStatement
open scoped Manifold ContDiff Bundle
open SameAtlasAnalyticCohomology SameAtlasRRLocal TopologicalSpace
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
namespace CanonicalDimensionTwo
universe v
/-- Inhabitant of the exact approved finite-cover injectivity contract. -/
theorem actualFiniteDolbeaultInjectivity
    (E : Type) [TopologicalSpace E] [T2Space E] [CompactSpace E]
    [Nonempty E] [PreconnectedSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualFiniteDolbeaultInjectivityStatement.{v} E := by
  classical
  intro U instU P
  have hker (t : CechHOne U) (ht : cechDolbeaultComparison U P t = 0) : t = 0 := by
    obtain ⟨g,hg⟩ := classOf_surjective U t
    subst t
    rw [cechDolbeaultComparison_classOf] at ht
    change (Submodule.Quotient.mk (cechToDolbeault U P g) : DolbeaultHZeroOne E) = 0 at ht
    have hr : cechToDolbeault U P g ∈ (dolbeaultDbar (E := E)).range :=
      (Submodule.Quotient.mk_eq_zero _).mp ht
    obtain ⟨F,hF⟩ := hr
    let H (i : U.Index) (x : E) : ℂ := F.1 x - localPartitionPrimitive U P g i x
    have hHol (i : U.Index) : IsHolOn (U.opens i) (fun x => H i x) := by
      apply localSmooth_zero_chartDbar_isHolOn
      · intro a x hxi hxa
        have hf := (F.property a).contDiffAt
          (extChartAt_target_mem_nhds' ((extChartAt 𝓘(ℂ) a).map_source hxa))
        exact hf.sub (localPartitionPrimitive_contDiffAt U P g i a x hxi hxa)
      · intro a x hxi hxa
        have hf := ((F.property a).contDiffAt
          (extChartAt_target_mem_nhds' ((extChartAt 𝓘(ℂ) a).map_source hxa))).differentiableAt (by simp)
        have hi := (localPartitionPrimitive_contDiffAt U P g i a x hxi hxa).differentiableAt (by simp)
        have he := congrArg (fun α : SmoothZeroOne E => α.1 a x) hF
        rw [cechToDolbeault_local U P a x hxa g i hxi] at he
        change (if x ∈ (extChartAt 𝓘(ℂ) a).source then chartDbar a F.1 x else 0) = _ at he
        rw [ite_eq_left hxa, ← localPartitionPrimitive_chartDbar U P g i a x hxi hxa] at he
        have hd : chartDbar a (H i) x = chartDbar a F.1 x -
            chartDbar a (localPartitionPrimitive U P g i) x := by
          unfold chartDbar
          dsimp only [H]
          rw [fderiv_fun_sub hf hi]
          simp only [sub_apply]
          ring
        rw [hd,he,sub_self]
    let h : CechZero U := fun i => ⟨fun x => H i x, hHol i⟩
    have hδ : deltaZero U h = g.1 := by
      funext i k
      apply Subtype.ext
      funext x
      simp only [deltaZero, LinearMap.coe_mk, AddHom.coe_mk, HolOn.restrict,
        Submodule.coe_sub, Pi.sub_apply]
      dsimp only [h,H]
      have hov := localPartitionPrimitive_overlap U P g i k x.1 x.property.1 x.property.2
      linear_combination hov
    apply Subtype.ext
    change (Submodule.Quotient.mk g.1 : cochainQuotient U) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨h,hδ⟩
  intro x y hxy
  have hs : cechDolbeaultComparison U P (x-y) = 0 := by
    rw [map_sub,hxy,sub_self]
  exact sub_eq_zero.mp (hker (x-y) hs)

end CanonicalDimensionTwo
