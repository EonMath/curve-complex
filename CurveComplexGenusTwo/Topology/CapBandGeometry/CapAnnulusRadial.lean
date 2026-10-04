import CurveComplexGenusTwo.Topology.CapBandGeometry.InternalProducer
import CurveComplexGenusTwo.Topology.CapBandGeometry.OutsideProducer

noncomputable section
open Set Topology unitInterval
namespace CurveComplex.CapBandGeometry

def capInnerDisk : Set CapDisk := {z | (z : CapPlane) ∈ Metric.closedBall 0 (1/2)}
def CapOuter := {z : CapDisk | 1/2 < ‖(z : CapPlane)‖}

def capAnnulusRadial (p : I × CapOuter) : CapDisk :=
  ⟨((1-(p.1:ℝ))+(p.1:ℝ)/‖(p.2.1:CapPlane)‖) • (p.2.1:CapPlane), by
    have hn : 0 < ‖(p.2.1:CapPlane)‖ := by
      have hh : 1/2 < ‖(p.2.1:CapPlane)‖ := p.2.2
      linarith
    have hle : ‖(p.2.1:CapPlane)‖ ≤ 1 := by
      have hh : dist (p.2.1:CapPlane) 0 ≤ 1 := p.2.1.2
      simpa only [dist_zero_right] using hh
    have hs : 0 ≤ (p.1:ℝ) ∧ (p.1:ℝ) ≤ 1 := p.1.2
    have hs1 : 0 ≤ 1-(p.1:ℝ) := by linarith
    have hc : 0 ≤ (1-(p.1:ℝ))+(p.1:ℝ)/‖(p.2.1:CapPlane)‖ := add_nonneg hs1 (div_nonneg hs.1 hn.le)
    change dist _ 0 ≤ 1
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
    rw [add_mul,div_mul_cancel₀ _ hn.ne']
    nlinarith⟩

theorem capAnnulusRadial_norm (p : I × CapOuter) :
    ‖(capAnnulusRadial p : CapPlane)‖ =
      (1-(p.1:ℝ))*‖(p.2.1:CapPlane)‖+(p.1:ℝ) := by
  have hn : 0 < ‖(p.2.1:CapPlane)‖ := by
      have hh : 1/2 < ‖(p.2.1:CapPlane)‖ := p.2.2
      linarith
  have hs : 0 ≤ (p.1:ℝ) ∧ (p.1:ℝ) ≤ 1 := p.1.2
  have hs1 : 0 ≤ 1-(p.1:ℝ) := by linarith
  have hc : 0 ≤ (1-(p.1:ℝ))+(p.1:ℝ)/‖(p.2.1:CapPlane)‖ := add_nonneg hs1 (div_nonneg hs.1 hn.le)
  change ‖(_ : ℝ) • _‖ = _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc,add_mul,div_mul_cancel₀ _ hn.ne']

theorem capAnnulusRadial_continuous : Continuous capAnnulusRadial := by
  apply Continuous.subtype_mk
  have hn : ∀ p : I × CapOuter, ‖(p.2.1:CapPlane)‖ ≠ 0 := by
    intro p
    exact ne_of_gt (by
      have hh : 1/2 < ‖(p.2.1:CapPlane)‖ := p.2.2
      linarith)
  exact ((continuous_const.sub (by fun_prop)).add
    ((by fun_prop : Continuous (fun p : I × CapOuter => (p.1:ℝ))).div
      (by fun_prop) hn)).smul (by fun_prop)

theorem capAnnulusRadial_outer (p : I × CapOuter) :
    1/2 < ‖(capAnnulusRadial p : CapPlane)‖ := by
  rw [capAnnulusRadial_norm]
  have hs : 0 ≤ (p.1:ℝ) ∧ (p.1:ℝ) ≤ 1 := p.1.2
  have hs1 : 0 ≤ 1-(p.1:ℝ) := by linarith
  have hh : 1/2 < ‖(p.2.1:CapPlane)‖ := p.2.2
  have hle : ‖(p.2.1:CapPlane)‖ ≤ 1 := by
    have hh : dist (p.2.1:CapPlane) 0 ≤ 1 := p.2.1.2
    simpa only [dist_zero_right] using hh
  nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hle)]

theorem capAnnulusRadial_zero (z : CapOuter) : capAnnulusRadial (0,z) = z.1 := by
  apply Subtype.ext
  simp [capAnnulusRadial]

theorem capAnnulusRadial_one (z : CapOuter) : capAnnulusRadial (1,z) ∈ capBoundary := by
  change dist (capAnnulusRadial (1,z) : CapPlane) 0 = 1
  rw [dist_zero_right,capAnnulusRadial_norm]
  simp

theorem capAnnulusRadial_boundary (s : I) (z : CapOuter)
    (hz : z.1 ∈ capBoundary) : capAnnulusRadial (s,z) = z.1 := by
  have hn : ‖(z.1:CapPlane)‖ = 1 := by simpa [capBoundary,dist_zero_right] using hz
  apply Subtype.ext
  simp [capAnnulusRadial,hn]

#print axioms capAnnulusRadial_continuous
end CurveComplex.CapBandGeometry
