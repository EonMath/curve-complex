import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual finite pair crossings give finite source contact parameters even
for marked loops; only the marked closure fiber is noninjective. -/
theorem actual_loop_allowed_all_contact_parameters_finite
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hfinite : (ArcSurgery.crossings M a b).Finite) :
    {t : Interval | b.val.map t ∈ a.val.image}.Finite := by
  have hinj : InjOn b.val.map (b.val.map ⁻¹' ArcSurgery.crossings M a b) := by
    intro s hs t ht he
    rcases b.val.injective_except_loop_closure s t he with h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact h
    · exact False.elim (hs.2.2 b.val.start_marked)
    · exact False.elim (hs.2.2 b.val.end_marked)
  apply ((hfinite.preimage hinj).union ((finite_singleton (1 : Interval)).insert 0)).subset
  intro t ht
  by_cases ht0 : t=0
  · right; simp [ht0]
  by_cases ht1 : t=1
  · right; simp [ht1]
  left
  have hnotmark : b.val.map t ∉ (M.cover.branch : Set S) := fun hm =>
    (b.val.marked_only_at_ends t hm).elim ht0 ht1
  exact ⟨⟨ht,hnotmark⟩,⟨t,rfl⟩,hnotmark⟩
end CurveComplex.HyperellipticModel
