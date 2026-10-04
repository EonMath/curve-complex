import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualPuncturedCylinderDoublePlaneProof
open Set Topology
namespace CurveComplex.Hyperbolic
theorem actual_cylinder_real_plane_homeomorph :
    let Q := {z : ℝ×ℝ // z≠((0:ℝ),0) ∧ z≠((1:ℝ),0)}
    ∃ e : ActualPuncturedCylinder ≃ₜ Q,
      ∀ z,(e z).val=(Real.exp z.val.2*(z.val.1 : ℂ).re,Real.exp z.val.2*(z.val.1 : ℂ).im) := by
  intro Q
  let h : ℂ ≃ₜ ℝ×ℝ := Complex.equivRealProdCLM.toHomeomorph
  have h0 (z : ℂ) : h z=((0:ℝ),0) ↔ z=0 := by
    change (z.re,z.im)=((0:ℝ),0) ↔ z=0
    constructor
    · intro hz;exact Complex.ext (congrArg Prod.fst hz) (congrArg Prod.snd hz)
    · rintro rfl;rfl
  have h1 (z : ℂ) : h z=((1:ℝ),0) ↔ z=1 := by
    change (z.re,z.im)=((1:ℝ),0) ↔ z=1
    constructor
    · intro hz;exact Complex.ext (congrArg Prod.fst hz) (congrArg Prod.snd hz)
    · rintro rfl;rfl
  let real : {z : ℂ // z≠0 ∧ z≠1} ≃ₜ Q := h.subtype
    (fun z=>and_congr (not_congr (h0 z)).symm (not_congr (h1 z)).symm)
  obtain ⟨polar,hpolar,hbase⟩ := actual_punctured_cylinder_double_punctured_plane_homeomorph
  refine ⟨polar.trans real,?_⟩
  intro z
  change ((polar z).val.re,(polar z).val.im)=_
  rw [hpolar]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
end CurveComplex.Hyperbolic
