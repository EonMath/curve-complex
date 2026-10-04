import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPuncturedPlaneGermLogarithm
namespace CurveComplex.HyperellipticModel
open Set Topology
theorem actual_continuous_logarithm_stripe (d : ℝ) (hd : 0<d) (L : C(Ioc (0:ℝ) d,ℂ))
    (hslit : ∀ t,Complex.exp (L t) ∈ Complex.slitPlane) :
    ∃ n : ℤ,(∀ t,L t=Complex.log (Complex.exp (L t))+n*(2*(Real.pi:ℂ)*Complex.I)) ∧
      ∀ t,(L t).im ∈ Ioo (-Real.pi+(n:ℝ)*(2*Real.pi)) (Real.pi+(n:ℝ)*(2*Real.pi)) := by
  let : ContractibleSpace (Ioc (0:ℝ) d) := (convex_Ioc (𝕜:=ℝ) (0:ℝ) d).contractibleSpace
    ⟨d,hd,le_rfl⟩
  let base : Ioc (0:ℝ) d := ⟨d,hd,le_rfl⟩
  obtain ⟨n,hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp
    (Complex.exp_log (Complex.exp_ne_zero (L base))).symm
  let Q : Ioc (0:ℝ) d → ℂ := fun t => Complex.log (Complex.exp (L t))+n*(2*(Real.pi:ℂ)*Complex.I)
  have hlogcont : Continuous (fun t => Complex.log (Complex.exp (L t))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp (f := fun t : Ioc (0:ℝ) d => Complex.exp (L t)) (x := t)
      (Complex.expOpenPartialHomeomorph.symm.continuousAt (hslit t))
      ((Complex.continuous_exp.comp L.continuous).continuousAt (x := t))
  have hQ : Continuous Q := hlogcont.add continuous_const
  have hcomp : (fun z => (⟨Complex.exp z,Complex.exp_ne_zero z⟩ : {z : ℂ // z≠0})) ∘ L =
      (fun z => (⟨Complex.exp z,Complex.exp_ne_zero z⟩ : {z : ℂ // z≠0})) ∘ Q := by
    funext t
    apply Subtype.ext
    exact ((Complex.exp_eq_exp_iff_exists_int.mpr ⟨n,rfl⟩).trans
      (Complex.exp_log (Complex.exp_ne_zero (L t)))).symm
  have he : (L : Ioc (0:ℝ) d → ℂ)=Q := Complex.isCoveringMap_exp.eq_of_comp_eq
    L.continuous hQ hcomp base hn
  refine ⟨n,fun t => congrFun he t,?_⟩
  intro t
  have hb := Complex.expOpenPartialHomeomorph.map_target (hslit t)
  change (Complex.log (Complex.exp (L t))).im ∈ Ioo (-Real.pi) Real.pi at hb
  have him : ((n:ℂ)*(2*(Real.pi:ℂ)*Complex.I)).im=(n:ℝ)*(2*Real.pi) := by
    simp [Complex.mul_im,Complex.mul_re]
  rw [congrFun he t,Complex.add_im,him]
  constructor <;> linarith only [hb.1,hb.2]
end CurveComplex.HyperellipticModel
