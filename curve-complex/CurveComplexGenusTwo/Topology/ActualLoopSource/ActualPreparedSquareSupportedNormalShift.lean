import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareFourBoundaryWall
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedCoreUniformNormalMargin
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteNormalCoordinateShift
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual finite interior vertices and the constructed square cutoff produce
one boundary-fixed normal shift. Its size is chosen from the compact strip
support, rather than supplied as a perturbation certificate. -/
theorem actual_prepared_square_supported_normal_shift
    (T A : Set (Interval × Interval)) (hA : IsClosed A) (hAT : A ⊆ T)
    (ψ : C(T,ℝ)) (hψ : ∀ x,ψ x<1)
    (cutoff : C(Interval × Interval,ℝ))
    (hcutoff : ∀ z,cutoff z ∈ Icc (0:ℝ) 1)
    {ι : Type} [Finite ι] (point : ι → T)
    (hpoint : ∀ i,0<(point i).val.1.val ∧ (point i).val.1.val<1 ∧
      0<(point i).val.2.val ∧ (point i).val.2.val<1)
    (hzero : ∀ i,ψ (point i)=0 → cutoff (point i).val=1) :
    ∃ (δ : ℝ) (weight : C(Interval × Interval,ℝ)),
      0<δ ∧
      (∀ z,weight z=cutoff z*(z.1.val*(1-z.1.val)*z.2.val*(1-z.2.val))) ∧
      (∀ z,weight z ∈ Icc (0:ℝ) 1) ∧
      (∀ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → weight z=0) ∧
      (∀ i,ψ (point i)+δ*weight (point i).val≠0) ∧
      (∀ z (hz : z ∈ A),ψ ⟨z,hAT hz⟩+δ*weight z<1) := by
  obtain ⟨wall,hwall,hwallBounds,hwallBoundary,hwallPos⟩ :=
    actual_square_four_boundary_wall
  let weight : C(Interval × Interval,ℝ) :=
    ⟨fun z => cutoff z*wall z,by fun_prop⟩
  have hweight : ∀ z,weight z ∈ Icc (0:ℝ) 1 := by
    intro z
    constructor
    · exact mul_nonneg (hcutoff z).1 (hwallBounds z).1
    · exact (mul_le_mul_of_nonneg_right (hcutoff z).2 (hwallBounds z).1).trans
        (by simpa only [one_mul] using (hwallBounds z).2)
  obtain ⟨margin,hmargin,hmarginBound⟩ :=
    actual_prepared_core_uniform_normal_margin T A hA hAT ψ hψ
  have hvertexWeight : ∀ i,ψ (point i)=0 → weight (point i).val≠0 := by
    intro i hi
    have hp := hpoint i
    have hpos := hwallPos (point i).val hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    change cutoff (point i).val*wall (point i).val≠0
    rw [hzero i hi,one_mul]
    exact ne_of_gt hpos
  obtain ⟨δ,hδ,hδmargin,hclear⟩ := actual_finite_normal_coordinate_shift
    (fun i => ψ (point i)) (fun i => weight (point i).val) hvertexWeight margin hmargin
  refine ⟨δ,weight,hδ,?_,hweight,?_,hclear,?_⟩
  · intro z
    change cutoff z*wall z=_
    rw [hwall z]
  · intro z hz
    change cutoff z*wall z=0
    rw [hwallBoundary z hz,mul_zero]
  · intro z hz
    have hw := (hweight z).2
    have hshift : δ*weight z≤δ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hw (le_of_lt hδ)
    have hbound := hmarginBound z hz
    linarith only [hshift,hδmargin,hbound]
end CurveComplex.HyperellipticModel
