import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualSameAtlasRealSmooth
import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualLocalTangentPerturbation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualTwoDirectionCoreStability
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualFiniteCoreInduction
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.Module.Equiv.Basic
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualRealTangentTransitionDifferentiable
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualRealTangentTransitionEventually
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualLiteralTangentCoefficientSmooth
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.VectorBundle.Basic
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.VerifiedRealNondegenerateIndex
import Mathlib.Topology.TietzeExtension
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCircleSourceWindingTransport
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualCircleMapWindingHomotopySourceReviewRequest
open Set Metric Topology
open scoped ContDiff
open scoped unitInterval
open Set Topology
set_option backward.isDefEq.respectTransparency false
private theorem actual_circle_power_homotopy_exponent_unique (m n : ℤ)
    (h : (⟨fun z : Circle => z ^ m, continuous_zpow m⟩ : C(Circle,Circle)).Homotopic
      ⟨fun z : Circle => z ^ n, continuous_zpow n⟩) : m = n := by
  obtain ⟨H⟩ := h
  let G : C(CurveComplex.Interval × ℝ,Circle) :=
    ⟨fun tx => H (tx.1,Circle.exp tx.2), by fun_prop⟩
  let F : C(ℝ,ℝ) := ⟨fun x => (m : ℝ)*x, by fun_prop⟩
  have hzero (x : ℝ) : G (0,x) = Circle.exp (F x) := by
    change H (0,Circle.exp x) = Circle.exp ((m : ℝ)*x)
    rw [H.apply_zero]
    simpa only [zsmul_eq_mul,ContinuousMap.coe_mk] using (Circle.exp_zsmul x m).symm
  have hGperiod (t : CurveComplex.Interval) (k : ℤ) (x : ℝ) :
      G (t,x+(k:ℝ)*(2*Real.pi)) = G (t,x) := by
    dsimp only [G,ContinuousMap.coe_mk]
    rw [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
  have hFperiod (k : ℤ) (x : ℝ) :
      F (x+(k:ℝ)*(2*Real.pi)) = F x+((k*m:ℤ):ℝ)*(2*Real.pi) := by
    simp only [F,ContinuousMap.coe_mk,Int.cast_mul]
    ring
  obtain ⟨A,hAlift,hA0,hAperiod⟩ :=
    actual_circle_source_homotopy_retains_integer_winding G F m hzero hGperiod hFperiod
  have hA1 (x : ℝ) : Circle.exp (A (1,x)) = (Circle.exp x)^n := by
    exact (hAlift 1 x).trans (H.apply_one (Circle.exp x))
  have hA10 : Circle.exp (A (1,0)) = 1 := by simpa using hA1 0
  have heq : (fun x : ℝ => A (1,x)) = (fun x : ℝ => (n:ℝ)*x + A (1,0)) := by
    apply Circle.isCoveringMap_exp.eq_of_comp_eq
      (A.continuous.comp (continuous_const.prodMk continuous_id))
      (by fun_prop) ?_ 0 (by simp)
    funext x
    change Circle.exp (A (1,x)) = Circle.exp ((n:ℝ)*x + A (1,0))
    rw [hA1, Circle.exp_add, hA10, mul_one]
    simpa only [zsmul_eq_mul,ContinuousMap.coe_mk] using (Circle.exp_zsmul x n).symm
  have hp := hAperiod 1 1 0
  rw [congrFun heq _,congrFun heq _] at hp
  have hm : (m:ℝ)*(2*Real.pi) = (n:ℝ)*(2*Real.pi) := by
    simpa only [zero_add,Int.cast_one,one_mul,mul_zero,zero_add] using
      (add_right_cancel (show (n:ℝ)*(2*Real.pi)+A (1,0) =
        (m:ℝ)*(2*Real.pi)+A (1,0) by simpa [add_comm] using hp)).symm
  exact_mod_cast mul_right_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero) hm

private noncomputable def actualCircleMapDegree (f : C(Circle,Circle)) : ℤ :=
  Classical.choose (actual_circle_map_winding_homotopy_source f)

private theorem actual_circle_map_degree_of_power_homotopy (f : C(Circle,Circle)) (n : ℤ)
    (h : f.Homotopic ⟨fun z : Circle => z^n,continuous_zpow n⟩) : actualCircleMapDegree f = n := by
  have hd : f.Homotopic ⟨fun z : Circle => z^(actualCircleMapDegree f),continuous_zpow _⟩ :=
    Classical.choose_spec (actual_circle_map_winding_homotopy_source f)
  exact actual_circle_power_homotopy_exponent_unique _ _ (hd.symm.trans h)

private theorem actual_circle_map_degree_homotopy_invariant (f g : C(Circle,Circle))
    (h : f.Homotopic g) : actualCircleMapDegree f = actualCircleMapDegree g := by
  apply actual_circle_map_degree_of_power_homotopy
  exact h.trans (Classical.choose_spec (actual_circle_map_winding_homotopy_source g))

open scoped Manifold Bundle
open Bundle

private theorem actual_circle_map_degree_const (u : Circle) :
    actualCircleMapDegree (ContinuousMap.const Circle u) = 0 := by
  let p := PathConnectedSpace.somePath u (1 : Circle)
  apply actual_circle_map_degree_of_power_homotopy
  let K : C(unitInterval × Circle,Circle) := ⟨fun tz => p tz.1, p.continuous.comp continuous_fst⟩
  refine ⟨{ toContinuousMap := K, map_zero_left := ?_, map_one_left := ?_ }⟩
  · intro z
    exact p.source
  · intro z
    change p 1 = z ^ (0 : ℤ)
    simpa only [zpow_zero] using p.target

private theorem actual_circle_boundary_degree_zero_of_disk_extension
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (G : C(Metric.closedBall z₀ ρ, Circle))
    (f : C(Circle,Circle))
    (hboundary : ∀ z : Circle, ∀ hz : z₀+(ρ:ℂ)*z ∈ Metric.closedBall z₀ ρ,
      f z = G ⟨z₀+(ρ:ℂ)*z,hz⟩) : actualCircleMapDegree f = 0 := by
  let R : unitInterval × Circle → ℂ :=
    fun p => z₀ + ((((1-(p.1:ℝ))*ρ : ℝ) : ℂ)) * (p.2:ℂ)
  have hR : Continuous R := by dsimp [R]; fun_prop
  have hRmem (p : unitInterval × Circle) : R p ∈ Metric.closedBall z₀ ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    dsimp [R]
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr p.1.2.2) hρ.le)]
    nlinarith [p.1.2.1,p.1.2.2]
  let c : Circle := G ⟨z₀, Metric.mem_closedBall_self hρ.le⟩
  have hh : f.Homotopic (ContinuousMap.const Circle c) := by
    let K : C(unitInterval × Circle,Circle) := ⟨fun p => G ⟨R p,hRmem p⟩,
      G.continuous.comp (hR.subtype_mk hRmem)⟩
    refine ⟨{ toContinuousMap := K, map_zero_left := ?_, map_one_left := ?_ }⟩
    · intro z
      have hz : z₀+(ρ:ℂ)*z ∈ Metric.closedBall z₀ ρ := by simpa [R] using hRmem (0,z)
      change G ⟨R (0,z),hRmem (0,z)⟩ = f z
      simpa [R] using (hboundary z hz).symm
    · intro z
      apply congrArg G
      apply Subtype.ext
      simp [R,c]
  exact (actual_circle_map_degree_homotopy_invariant _ _ hh).trans
    (actual_circle_map_degree_const c)

private theorem actual_nonvanishing_literal_disc_coefficient_boundary_degree_zero
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (b : C(Metric.closedBall z₀ ρ,ℂ)) (hb : ∀ x, b x ≠ 0)
    (f : C(Circle,Circle))
    (hf : ∀ z : Circle, ∀ hz : z₀+(ρ:ℂ)*z ∈ Metric.closedBall z₀ ρ,
      (f z : ℂ) = b ⟨z₀+(ρ:ℂ)*z,hz⟩ /
        (‖b ⟨z₀+(ρ:ℂ)*z,hz⟩‖:ℂ)) : actualCircleMapDegree f = 0 := by
  have hn (x : Metric.closedBall z₀ ρ) : (‖b x‖:ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (hb x)
  have hu (x : Metric.closedBall z₀ ρ) : b x/(‖b x‖:ℂ) ∈ Submonoid.unitSphere ℂ := by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm]
    exact div_self (norm_ne_zero_iff.mpr (hb x))
  let G : C(Metric.closedBall z₀ ρ,Circle) :=
    ⟨fun x => ⟨b x/(‖b x‖:ℂ),hu x⟩,
      (b.continuous.div (Complex.continuous_ofReal.comp b.continuous.norm) hn).subtype_mk hu⟩
  apply actual_circle_boundary_degree_zero_of_disk_extension z₀ ρ hρ G f
  intro z hz
  apply Circle.coe_injective
  exact hf z hz

private theorem actual_real_tangent_literal_closed_chart_disc_coefficient
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hV : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (V x)))
    (q : E) (ρ : ℝ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    ∃ b : C(closedBall ((chartAt ℂ q) q) ρ,ℂ),
      (∀ d, b d =
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
          (TotalSpace.mk' ℂ ((chartAt ℂ q).symm d.val) (V ((chartAt ℂ q).symm d.val)))).2) ∧
      ∀ d, b d = 0 ↔ V ((chartAt ℂ q).symm d.val) = 0 := by
  let c := chartAt ℂ q
  let e := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  let D := closedBall (c q) ρ
  let m : C(D,E) := ⟨fun d => c.symm d.val,
    c.symm.continuousOn.comp_continuous continuous_subtype_val (fun d => htarget d.property)⟩
  have hm (d : D) : m d ∈ e.baseSet := by
    have hx := c.map_target (htarget d.property)
    simpa only [e,m,c,ContinuousMap.coe_mk,TangentBundle.trivializationAt_baseSet] using hx
  have hbOn : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞
      (fun x => (e (TotalSpace.mk' ℂ x (V x))).2) e.baseSet :=
    (e.contMDiffOn_section_baseSet_iff).mp hV.contMDiffOn
  let b : C(D,ℂ) := ⟨fun d => (e (TotalSpace.mk' ℂ (m d) (V (m d)))).2,
    hbOn.continuousOn.comp_continuous m.continuous hm⟩
  refine ⟨b,fun d => rfl,?_⟩
  intro d
  change (e (TotalSpace.mk' ℂ (m d) (V (m d)))).2 = 0 ↔ _
  rw [e.apply_eq_prod_continuousLinearEquivAt ℝ (m d) (hm d)]
  change (e.continuousLinearEquivAt ℝ (m d) (hm d)) (V (m d)) = 0 ↔ V (m d) = 0
  exact ContinuousLinearEquiv.map_eq_zero_iff _

private theorem actual_normalized_nonzero_literal_circle_coefficient_exists
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (b : C(closedBall z₀ ρ,ℂ))
    (hb : ∀ z : Circle, ∀ hz : z₀+(ρ:ℂ)*z ∈ closedBall z₀ ρ,
      b ⟨z₀+(ρ:ℂ)*z,hz⟩ ≠ 0) :
    ∃ f : C(Circle,Circle), ∀ z : Circle,
      ∀ hz : z₀+(ρ:ℂ)*z ∈ closedBall z₀ ρ,
        (f z:ℂ) = b ⟨z₀+(ρ:ℂ)*z,hz⟩ /(‖b ⟨z₀+(ρ:ℂ)*z,hz⟩‖:ℂ) := by
  have hz (z : Circle) : z₀+(ρ:ℂ)*z ∈ closedBall z₀ ρ := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ,Circle.norm_coe,mul_one]
  let γ : C(Circle,closedBall z₀ ρ) :=
    ⟨fun z => ⟨z₀+(ρ:ℂ)*z,hz z⟩,(by fun_prop : Continuous (fun z : Circle => z₀+(ρ:ℂ)*z)).subtype_mk hz⟩
  let a := b.comp γ
  have ha (z : Circle) : a z ≠ 0 := hb z (hz z)
  have hn (z : Circle) : (‖a z‖:ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (ha z)
  have hu (z : Circle) : a z/(‖a z‖:ℂ) ∈ Submonoid.unitSphere ℂ := by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm]
    exact div_self (norm_ne_zero_iff.mpr (ha z))
  let f : C(Circle,Circle) := ⟨fun z => ⟨a z/(‖a z‖:ℂ),hu z⟩,
    (a.continuous.div (Complex.continuous_ofReal.comp a.continuous.norm) hn).subtype_mk hu⟩
  exact ⟨f,fun z hz => rfl⟩

private theorem actual_given_reference_field_union_boundary_models_at_given_radius
    {E : Type} [DecidableEq E] [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hV : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (V x)))
    (S T : Finset E) (hT : (T : Set E) = {x | V x = 0})
    (D : T → (ℂ ≃L[ℝ] ℂ))
    (r : T → ℝ) (hr : ∀ q, 0 < r q)
    (hmodel : ∀ q : T, ∀ ρ : ℝ, 0 < ρ → ρ < r q →
      let b : ℂ → ℂ := fun w =>
        let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+w);
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
          (TotalSpace.mk' ℂ x (V x))).2;
      (∀ z : Circle, b ((ρ:ℂ)*z) ≠ 0) ∧
      ∀ f : C(Circle,Circle),
        (∀ z : Circle, (f z:ℂ) = b ((ρ:ℂ)*z)/(‖b ((ρ:ℂ)*z)‖:ℂ)) →
        actualCircleMapDegree f =
          if 0 < (D q 1).re*(D q Complex.I).im -
            (D q Complex.I).re*(D q 1).im then 1 else -1) :
      ∀ ρ : ↥(S ∪ T) → ℝ, (∀ q, 0 < ρ q) →
      (∀ q, closedBall ((chartAt ℂ q.val) q.val) (ρ q) ⊆ (chartAt ℂ q.val).target) →
      (∀ q (hq : q.val ∈ T), ρ q < r ⟨q.val,hq⟩) →
      (∀ q : ↥(S ∪ T), ∀ x ∈ (chartAt ℂ q.val).symm ''
        closedBall ((chartAt ℂ q.val) q.val) (ρ q), x ∈ S ∪ T → x = q.val) →
      ∃ f : ↥(S ∪ T) → C(Circle,Circle),
        (∀ q, ∀ z : Circle,
          let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+(ρ q:ℂ)*z);
          let b := (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
            (TotalSpace.mk' ℂ x (V x))).2;
          (f q z:ℂ) = b/(‖b‖:ℂ)) ∧
        ∀ q, actualCircleMapDegree (f q) =
          if hq : q.val ∈ T then
            if 0 < (D ⟨q.val,hq⟩ 1).re*(D ⟨q.val,hq⟩ Complex.I).im -
              (D ⟨q.val,hq⟩ Complex.I).re*(D ⟨q.val,hq⟩ 1).im then 1 else -1
          else 0 := by
  classical
  intro ρ hρ htarget hsmall hisolation
  have hmodels (q : ↥(S ∪ T)) : ∃ f : C(Circle,Circle),
      (∀ z : Circle,
        let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+(ρ q:ℂ)*z);
        let b := (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
          (TotalSpace.mk' ℂ x (V x))).2;
        (f z:ℂ) = b/(‖b‖:ℂ)) ∧
      actualCircleMapDegree f =
        if hq : q.val ∈ T then
          if 0 < (D ⟨q.val,hq⟩ 1).re*(D ⟨q.val,hq⟩ Complex.I).im -
            (D ⟨q.val,hq⟩ Complex.I).re*(D ⟨q.val,hq⟩ 1).im then 1 else -1
        else 0 := by
    obtain ⟨b,hb,hbz⟩ := actual_real_tangent_literal_closed_chart_disc_coefficient
      V hV q.val (ρ q) (htarget q)
    have hboundary (z : Circle) : (chartAt ℂ q.val) q.val+(ρ q:ℂ)*z ∈
        closedBall ((chartAt ℂ q.val) q.val) (ρ q) := by
      rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_mul,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hρ q),Circle.norm_coe,mul_one]
    have hnonzero : ∀ z : Circle, ∀ hz, b ⟨(chartAt ℂ q.val) q.val+(ρ q:ℂ)*z,hz⟩ ≠ 0 := by
      intro z hz
      by_cases hq : q.val ∈ T
      · have hn := (hmodel ⟨q.val,hq⟩ (ρ q) (hρ q) (hsmall q hq)).1 z
        simpa only [hb] using hn
      · intro hzero
        have hvzero := (hbz ⟨(chartAt ℂ q.val) q.val+(ρ q:ℂ)*z,hz⟩).mp hzero
        have hxT : (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+(ρ q:ℂ)*z) ∈ T := by
          change _ ∈ (T : Set E)
          rw [hT]
          exact hvzero
        have he := hisolation q _ ⟨_,hz,rfl⟩ (Finset.mem_union.mpr (Or.inr hxT))
        exact hq (he ▸ hxT)
    obtain ⟨f,hf⟩ := actual_normalized_nonzero_literal_circle_coefficient_exists
      ((chartAt ℂ q.val) q.val) (ρ q) (hρ q) b hnonzero
    have hflit : ∀ z : Circle,
        let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+(ρ q:ℂ)*z);
        let b := (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
          (TotalSpace.mk' ℂ x (V x))).2;
        (f z:ℂ) = b/(‖b‖:ℂ) := by
      intro z
      simpa only [hb] using hf z (hboundary z)
    refine ⟨f,hflit,?_⟩
    by_cases hq : q.val ∈ T
    · rw [dif_pos hq]
      exact (hmodel ⟨q.val,hq⟩ (ρ q) (hρ q) (hsmall q hq)).2 f hflit
    · rw [dif_neg hq]
      have hall : ∀ d, b d ≠ 0 := by
        intro d hzero
        have hxT : (chartAt ℂ q.val).symm d.val ∈ T := by
          change _ ∈ (T : Set E)
          rw [hT]
          exact (hbz d).mp hzero
        have he := hisolation q _ ⟨d.val,d.property,rfl⟩ (Finset.mem_union.mpr (Or.inr hxT))
        exact hq (he ▸ hxT)
      exact actual_nonvanishing_literal_disc_coefficient_boundary_degree_zero
        ((chartAt ℂ q.val) q.val) (ρ q) (hρ q) b hall f hf
  choose f hflit hdegree using hmodels
  exact ⟨f,hflit,hdegree⟩


private theorem actual_union_field_boundary_models_from_supported_loops
    {E : Type} [DecidableEq E] [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hV : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (V x)))
    (S T : Finset E) (hS : (S : Set E) = {x | V x = 0})
    (ρ : ↥(S ∪ T) → ℝ) (hρ : ∀ q, 0 < ρ q)
    (htarget : ∀ q, closedBall ((chartAt ℂ q.val) q.val) (ρ q) ⊆ (chartAt ℂ q.val).target)
    (hisolation : ∀ q : ↥(S ∪ T), ∀ x ∈ (chartAt ℂ q.val).symm ''
      closedBall ((chartAt ℂ q.val) q.val) (ρ q), x ∈ S ∪ T → x = q.val)
    (fS : S → C(Circle,Circle))
    (hfS : ∀ q : S, ∀ z : Circle,
      let u : ↥(S ∪ T) := ⟨q.val,Finset.mem_union.mpr (Or.inl q.property)⟩;
      let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+(ρ u:ℂ)*z);
      let b := (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
        (TotalSpace.mk' ℂ x (V x))).2;
      (fS q z:ℂ) = b/(‖b‖:ℂ)) :
    ∃ f : ↥(S ∪ T) → C(Circle,Circle),
      (∀ q, ∀ z : Circle,
        let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+(ρ q:ℂ)*z);
        let b := (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
          (TotalSpace.mk' ℂ x (V x))).2;
        (f q z:ℂ) = b/(‖b‖:ℂ)) ∧
      ∀ q, actualCircleMapDegree (f q) =
        if hq : q.val ∈ S then actualCircleMapDegree (fS ⟨q.val,hq⟩) else 0 := by
  classical
  have hmodels (q : ↥(S ∪ T)) : ∃ f : C(Circle,Circle),
      (∀ z : Circle,
        let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+(ρ q:ℂ)*z);
        let b := (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
          (TotalSpace.mk' ℂ x (V x))).2;
        (f z:ℂ) = b/(‖b‖:ℂ)) ∧
      actualCircleMapDegree f =
        if hq : q.val ∈ S then actualCircleMapDegree (fS ⟨q.val,hq⟩) else 0 := by
    by_cases hq : q.val ∈ S
    · refine ⟨fS ⟨q.val,hq⟩,?_,by simp only [dif_pos hq]⟩
      exact hfS ⟨q.val,hq⟩
    · obtain ⟨b,hb,hbz⟩ := actual_real_tangent_literal_closed_chart_disc_coefficient
        V hV q.val (ρ q) (htarget q)
      have hall : ∀ d, b d ≠ 0 := by
        intro d hzero
        have hxS : (chartAt ℂ q.val).symm d.val ∈ S := by
          change _ ∈ (S : Set E)
          rw [hS]
          exact (hbz d).mp hzero
        have he := hisolation q _ ⟨d.val,d.property,rfl⟩ (Finset.mem_union.mpr (Or.inl hxS))
        exact hq (he ▸ hxS)
      have hboundary (z : Circle) : (chartAt ℂ q.val) q.val+(ρ q:ℂ)*z ∈
          closedBall ((chartAt ℂ q.val) q.val) (ρ q) := by
        rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_mul,
          Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hρ q),Circle.norm_coe,mul_one]
      obtain ⟨f,hf⟩ := actual_normalized_nonzero_literal_circle_coefficient_exists
        ((chartAt ℂ q.val) q.val) (ρ q) (hρ q) b (fun z hz => hall _)
      refine ⟨f,?_,?_⟩
      · intro z
        simpa only [hb] using hf z (hboundary z)
      · rw [dif_neg hq]
        exact actual_nonvanishing_literal_disc_coefficient_boundary_degree_zero
          ((chartAt ℂ q.val) q.val) (ρ q) (hρ q) b hall f hf
  choose f hflit hdegree using hmodels
  exact ⟨f,hflit,hdegree⟩
