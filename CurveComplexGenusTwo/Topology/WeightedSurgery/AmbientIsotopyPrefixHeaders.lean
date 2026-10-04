import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers

namespace CurveComplex.HyperellipticModel.ArcSurgery

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/- Restricting an actual marked ambient isotopy to time t gives an actual
quotient equality for every intermediate essential arc, not just at time 1. -/
theorem marked_ambient_isotopy_prefix_preserves_class (M : HyperellipticModel E S) (A : AmbientIsotopy S)
    (hfix : ∀ r p, p ∈ M.cover.branch → A.map (r, p) = p)
    (a b : EssentialMarkedArc M) (t : Interval)
    (hb : b.val.image = (fun p => A.map (t, p)) '' a.val.image) :
    vertex M a = vertex M b := by
  let scale : Interval → Interval := fun r =>
    ⟨t.val * r.val, mul_nonneg t.property.1 r.property.1,
      by calc
        t.val * r.val ≤ t.val * 1 := mul_le_mul_of_nonneg_left r.property.2 t.property.1
        _ = t.val := mul_one _
        _ ≤ 1 := t.property.2⟩
  have hscale : Continuous scale := by
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val
  have hz : scale ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
    apply Subtype.ext
    exact mul_zero _
  have ho : scale ⟨1, by norm_num⟩ = t := by
    apply Subtype.ext
    exact mul_one _
  let B : AmbientIsotopy S := {
    map := ⟨fun z => A.map (scale z.1, z.2),
      A.map.continuous.comp ((hscale.comp continuous_fst).prodMk continuous_snd)⟩
    homeomorphism_at := fun r => A.homeomorphism_at (scale r)
    at_zero := fun p => by change A.map (scale ⟨0, by norm_num⟩, p) = p; rw [hz]; exact A.at_zero p }
  apply Quotient.sound
  refine ⟨B, ?_, ?_⟩
  · intro r p hp
    exact hfix (scale r) p hp
  · change (fun p => A.map (scale ⟨1, by norm_num⟩, p)) '' a.val.image = b.val.image
    rw [ho]
    exact hb.symm

end CurveComplex.HyperellipticModel.ArcSurgery
