import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.FirstHeightPortTrim
namespace CurveComplex
open Set Schoenflies

/-- Positivity at one actual end of a half-port propagates along its entire
positive clock when the actual original-axis zero set is only the center. -/
theorem actual_half_port_positive_side_retention
    (P : C(Interval,Plane))
    (hzero : ∀ t, P t 1=0 ↔ t=0) (hend : 0<P 1 1) :
    ∀ t : Interval, 0<(t:ℝ) → 0<P t 1 := by
  intro t ht
  by_contra hn
  have htn : t ≠ 0 := by intro he; subst t; norm_num at ht
  have hneg : P t 1 < 0 := lt_of_le_of_ne (le_of_not_gt hn)
    (fun he => htn ((hzero t).mp he))
  have hc : Continuous (fun t : Interval => P t 1) := by fun_prop
  obtain ⟨s,hs,hse⟩ := intermediate_value_Icc (show t ≤ (1:Interval) from t.property.2) hc.continuousOn
    (show (0:ℝ) ∈ Icc (P t 1) (P 1 1) from ⟨hneg.le,hend.le⟩)
  have hs0 : s=0 := (hzero s).mp hse
  have hts : (t:ℝ) ≤ (s:ℝ) := hs.1
  rw [hs0] at hts
  norm_num at hts
  linarith

/-- The negative side is likewise retained everywhere; reflection therefore
produces an actual positive lower half-port for the two-rectangle assembly. -/
theorem actual_half_port_negative_side_retention
    (P : C(Interval,Plane))
    (hzero : ∀ t, P t 1=0 ↔ t=0) (hend : P 1 1<0) :
    ∀ t : Interval, 0<(t:ℝ) → P t 1<0 := by
  let N : C(Interval,Plane) := ⟨fun t => Plane.mk (P t 0) (-(P t 1)),by fun_prop⟩
  have hz : ∀ t,N t 1=0 ↔ t=0 := by intro t; change -(P t 1)=0 ↔ t=0; rw [neg_eq_zero,hzero]
  have he : 0<N 1 1 := by change 0< -(P 1 1); linarith
  intro t ht
  have hh := actual_half_port_positive_side_retention N hz he t ht
  change 0< -(P t 1) at hh
  linarith
end CurveComplex
