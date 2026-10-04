import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualDepthParametrizedTrace

namespace CurveComplex.WeightedFlowScratch

theorem bandClock_actual_scale (scale width depth first prior : ℝ) (hs : 0 < scale) :
    scale * min width (max 0 ((depth-first)/scale-prior)) =
      min (scale*width) (max 0 (depth-(first+scale*prior))) := by
  rw [mul_min_of_nonneg _ _ hs.le, mul_max_of_nonneg _ _ hs.le,
    mul_zero, mul_sub]
  have hc : scale * ((depth-first)/scale) = depth-first := by
    field_simp
  rw [hc]
  congr 2
  ring

end CurveComplex.WeightedFlowScratch
namespace CurveComplex.HyperellipticModel.ArcSurgery.ActualFiniteEventTrace
open CurveGenusTwo.Filtration CurveComplex.WeightedFlowScratch
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
variable {M : HyperellipticModel E S} [LinearOrder (EssentialArcClass M)]
  {anchor : EssentialMarkedArc M}
local notation "K" => geometricComplex (actualA M)
local notation "Stage" σ => CurveComplex.RealizationPoint (CurveComplex.fullSubcomplex K (· ∈ σ))

theorem cut_band_prefix {σ : Finset (ActiveVertex (actualA M))}
    (c : ActualEventCertificate M anchor σ) (T : ActualFiniteEventTrace M anchor c.nextFace)
    (p : Stage σ) (j : ℕ) :
    (∑ k ∈ Finset.range (j+1), (ActualFiniteEventTrace.cut c T).bandWidth k p) =
      c.selectedMass p + c.endpointScale p *
        ∑ k ∈ Finset.range j, T.bandWidth k (c.endpointToNext p) := by
  rw [Finset.sum_range_succ']
  simp only [bandWidth, ← Finset.mul_sum]
  ring

/-- Actual tail normalization agrees with the unnormalized prefix clock. -/
theorem cut_band_depth_rescaling {σ : Finset (ActiveVertex (actualA M))}
    (c : ActualEventCertificate M anchor σ) (T : ActualFiniteEventTrace M anchor c.nextFace)
    (p : Stage σ) (j : ℕ) (depth : ℝ) :
    min ((ActualFiniteEventTrace.cut c T).bandWidth (j+1) p)
      (max 0 (depth-∑ k ∈ Finset.range (j+1),
        (ActualFiniteEventTrace.cut c T).bandWidth k p)) =
      c.endpointScale p * min (T.bandWidth j (c.endpointToNext p))
        (max 0 ((depth-c.selectedMass p)/c.endpointScale p -
          ∑ k ∈ Finset.range j, T.bandWidth k (c.endpointToNext p))) := by
  rw [cut_band_prefix, bandWidth]
  exact (bandClock_actual_scale _ _ _ _ _ (c.endpointScale_positive p)).symm

/-- A zero-width actual band is deleted without a time interval or pause in
the depth-parametrized trace; the tail receives the constructed same point. -/
theorem atDepth_cut_zeroMass {σ : Finset (ActiveVertex (actualA M))}
    (c : ActualEventCertificate M anchor σ) (T : ActualFiniteEventTrace M anchor c.nextFace)
    (p : Stage σ) (hz : c.selectedMass p = 0)
    (depth : ℝ) (hd : 0 ≤ depth) :
    (ActualFiniteEventTrace.cut c T).atDepth (depth,p) =
      T.atDepth (depth,c.endpointToNext p) := by
  have hs : c.endpointScale p = 1 := by simp [ActualEventCertificate.endpointScale, hz]
  rw [atDepth, hz]
  split_ifs with ht
  · have he : depth = 0 := le_antisymm ht hd
    subst depth
    rw [c.clampedEvent_before _ 0 le_rfl, T.atDepth_before _ 0 le_rfl,
      c.endpointToNext_ambient]
    exact (actualSurgeryFullStageEvent_zeroWeight_fixed M anchor c.classes c.position
      c.crossing c.surgery _ c.face c.contains c.selected_mem p 1 hz).symm
  · rw [hs, sub_zero, div_one]

end CurveComplex.HyperellipticModel.ArcSurgery.ActualFiniteEventTrace
