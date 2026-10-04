import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.Taskwave78_actual_circle_angular_h1
import CurveComplexGenusTwo.CWHurewicz.PairExactnessInterface
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseCircleFundamentalCycle
import CurveComplexGenusTwo.CWHurewicz.ConnectingNaturality
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCircleSourceWindingTransport
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualCircleMapWindingHomotopySourceReviewRequest
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
open CategoryTheory CurveComplexGenusTwo.CWHurewicz
private theorem actual_uniform_relative_caps_force_circle_boundary_degree_sum_zero
    {E : Type} [TopologicalSpace E] (P : Set E)
    {ι : Type} [Fintype ι]
    (r : relativeHomology E P 2) (caps : ι → relativeHomology E P 2)
    (β : ι → C(Circle,P)) (k : ℤ) (hk : k ≠ 0)
    (hr : r = k • ∑ i, caps i)
    (hboundary : relativeConnecting E P 1 r = 0)
    (hcaps : ∀ i, relativeConnecting E P 1 (caps i) =
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (β i))) CircleFundamentalCycle.fundamentalClass)
    (R : C(P,Circle)) :
    (∑ i, actualCircleMapDegree (R.comp (β i))) = 0 := by
  classical
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  have haction (i : ι) : F.map (TopCat.ofHom (R.comp (β i)))
      CircleFundamentalCycle.fundamentalClass =
      actualCircleMapDegree (R.comp (β i)) • CircleFundamentalCycle.fundamentalClass := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "Taskwave78_actual_circle_angular_h1") 0)
        "actual_circle_angular_degree_induced_h1_action"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) _))
  have hcomp (i : ι) :
      F.map (TopCat.ofHom R) (F.map (TopCat.ofHom (β i)) CircleFundamentalCycle.fundamentalClass) =
      actualCircleMapDegree (R.comp (β i)) • CircleFundamentalCycle.fundamentalClass := by
    rw [← haction]
    have hf := F.map_comp (TopCat.ofHom (β i)) (TopCat.ofHom R)
    exact (congrArg (fun m => m CircleFundamentalCycle.fundamentalClass) hf).symm
  have hz : k • (∑ i, actualCircleMapDegree (R.comp (β i)) •
      CircleFundamentalCycle.fundamentalClass) = 0 := by
    have hh := congrArg (fun t => F.map (TopCat.ofHom R) (relativeConnecting E P 1 t)) hr
    rw [hboundary,map_zero] at hh
    have hh' : k • (∑ i, F.map (TopCat.ofHom R)
        (F.map (TopCat.ofHom (β i)) CircleFundamentalCycle.fundamentalClass)) = 0 := by
      simpa only [map_zsmul,map_sum,hcaps] using hh.symm
    simpa only [hcomp] using hh'
  have hn := congrArg CircleHomologyComputation.circleH1Iso.hom hz
  simp only [map_zero,map_zsmul,map_sum] at hn
  change k * (∑ i, actualCircleMapDegree (R.comp (β i)) *
    CircleHomologyComputation.circleH1Iso.hom CircleFundamentalCycle.fundamentalClass) = 0 at hn
  rw [CircleFundamentalCycle.fundamentalClass_coordinate] at hn
  simp only [mul_neg_one,Finset.sum_neg_distrib] at hn
  have hsum : -(∑ i, actualCircleMapDegree (R.comp (β i))) = 0 :=
    (mul_eq_zero.mp hn).resolve_left hk
  exact neg_eq_zero.mp hsum

open Bundle Topology
open scoped Manifold ContDiff Bundle
set_option backward.isDefEq.respectTransparency false
private theorem actual_complex_line_ratio_independent_of_coordinates
    {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℂ F]
    (c d : F ≃L[ℂ] ℂ) (v w : F) (hv : v ≠ 0) :
    c w / c v = d w / d v := by
  have hcv : c v ≠ 0 := fun h => hv (c.injective (by simpa using h))
  have hdv : d v ≠ 0 := fun h => hv (d.injective (by simpa using h))
  have hw : w = (c w / c v) • v := by
    apply c.injective
    rw [c.map_smul]
    change c w = (c w / c v) * c v
    exact (div_mul_cancel₀ (c w) hcv).symm
  have hdw := congrArg d hw
  rw [d.map_smul] at hdw
  rw [hdw]
  change _ = ((c w / c v) * d v) / d v
  rw [mul_div_cancel_right₀ _ hdv]

private noncomputable def actualComplexTangentFieldRatio
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (V W : ∀ x : E, TangentSpace 𝓘(ℂ) x) (x : E) : ℂ :=
    (tangentSpaceCastModel 𝓘(ℂ) x (W x)) /
      (tangentSpaceCastModel 𝓘(ℂ) x (V x))

private theorem actual_complex_tangent_field_ratio_continuous_at
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E]
    (V W : ∀ x : E, TangentSpace 𝓘(ℂ) x) (q : E)
    (hV : ContinuousAt (fun x => TotalSpace.mk' ℂ x (V x)) q)
    (hW : ContinuousAt (fun x => TotalSpace.mk' ℂ x (W x)) q)
    (hq : V q ≠ 0) :
    ContinuousAt (actualComplexTangentFieldRatio V W) q := by
  let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℂ) x) q
  have hbase : q ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  have hcV : ContinuousAt (fun x => (e (TotalSpace.mk' ℂ x (V x))).2) q :=
    (FiberBundle.continuousAt_section ℂ q).mp hV
  have hcW : ContinuousAt (fun x => (e (TotalSpace.mk' ℂ x (W x))).2) q :=
    (FiberBundle.continuousAt_section ℂ q).mp hW
  have hqcoord : (e (TotalSpace.mk' ℂ q (V q))).2 ≠ 0 := by
    have hc : e.continuousLinearEquivAt ℂ q hbase (V q) ≠ 0 := by
      intro h
      apply hq
      apply (e.continuousLinearEquivAt ℂ q hbase).injective
      rw [map_zero]
      exact h
    rw [e.apply_eq_prod_continuousLinearEquivAt ℂ q hbase]
    exact hc
  apply (hcW.div hcV hqcoord).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hbase, hcV.eventually_ne hqcoord] with x hx hvx
  have hv : V x ≠ 0 := by
    intro hz
    apply hvx
    rw [hz,e.apply_eq_prod_continuousLinearEquivAt ℂ x hx,map_zero]
  change actualComplexTangentFieldRatio V W x =
    (e (TotalSpace.mk' ℂ x (W x))).2 / (e (TotalSpace.mk' ℂ x (V x))).2
  rw [e.apply_eq_prod_continuousLinearEquivAt ℂ x hx,
    e.apply_eq_prod_continuousLinearEquivAt ℂ x hx]
  exact (actual_complex_line_ratio_independent_of_coordinates
    (tangentSpaceCastModel 𝓘(ℂ) x) (e.continuousLinearEquivAt ℂ x hx) (V x) (W x) hv)

private theorem actual_complex_tangent_nonvanishing_fields_have_literal_circle_ratio
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E]
    (V W : ∀ x : E, TangentSpace 𝓘(ℂ) x)
    (hV : Continuous (fun x => TotalSpace.mk' ℂ x (V x)))
    (hW : Continuous (fun x => TotalSpace.mk' ℂ x (W x)))
    (U : Set E) (hVU : ∀ x ∈ U, V x ≠ 0) (hWU : ∀ x ∈ U, W x ≠ 0) :
    ∃ R : C(U,Circle), ∀ x,
      (R x : ℂ) = actualComplexTangentFieldRatio V W x.val /
        (‖actualComplexTangentFieldRatio V W x.val‖ : ℂ) := by
  let a : U → ℂ := fun x => actualComplexTangentFieldRatio V W x.val
  have ha : Continuous a := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (actual_complex_tangent_field_ratio_continuous_at V W x.val
      hV.continuousAt hW.continuousAt (hVU x.val x.property)).comp continuous_subtype_val.continuousAt
  have hane (x : U) : a x ≠ 0 := by
    apply div_ne_zero
    · intro h
      apply hWU x.val x.property
      apply (tangentSpaceCastModel 𝓘(ℂ) x.val).injective
      rw [map_zero]
      exact h
    · intro h
      apply hVU x.val x.property
      apply (tangentSpaceCastModel 𝓘(ℂ) x.val).injective
      rw [map_zero]
      exact h
  let R : U → Circle := fun x => ⟨a x / (‖a x‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm,div_self (norm_ne_zero_iff.mpr (hane x))]⟩
  have hR : Continuous R := by
    apply Continuous.subtype_mk
    apply ha.div (Complex.continuous_ofReal.comp ha.norm)
    intro x
    change (‖a x‖ : ℂ) ≠ 0
    exact_mod_cast norm_ne_zero_iff.mpr (hane x)
  exact ⟨⟨R,hR⟩,fun x => rfl⟩

private theorem actual_normalized_complex_ratio_eq_quotient_of_normalizations
    (v w : ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    (w/v)/(‖w/v‖:ℂ) = (w/(‖w‖:ℂ))/(v/(‖v‖:ℂ)) := by
  have hnv : (‖v‖:ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hv
  have hnw : (‖w‖:ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  rw [norm_div,Complex.ofReal_div]
  field_simp

private theorem actual_global_tangent_circle_ratio_literal_chart_relation
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (V W : ∀ x : E, TangentSpace 𝓘(ℂ) x)
    (U : Set E) (R : C(U,Circle))
    (hR : ∀ x, (R x : ℂ) = actualComplexTangentFieldRatio V W x.val /
      (‖actualComplexTangentFieldRatio V W x.val‖:ℂ))
    (q : U) (hV : V q.val ≠ 0) (hW : W q.val ≠ 0)
    (e : TangentSpace 𝓘(ℂ) q.val ≃L[ℂ] ℂ) :
    (R q : ℂ) = (e (W q.val)/(‖e (W q.val)‖:ℂ)) /
      (e (V q.val)/(‖e (V q.val)‖:ℂ)) := by
  rw [hR]
  have hr : actualComplexTangentFieldRatio V W q.val = e (W q.val)/e (V q.val) :=
    actual_complex_line_ratio_independent_of_coordinates
      (tangentSpaceCastModel 𝓘(ℂ) q.val) e (V q.val) (W q.val) hV
  rw [hr]
  apply actual_normalized_complex_ratio_eq_quotient_of_normalizations
  · intro h
    apply hV
    apply e.injective
    rw [map_zero]
    exact h
  · intro h
    apply hW
    apply e.injective
    rw [map_zero]
    exact h
private theorem actual_circle_map_degree_mul (f g : C(Circle,Circle)) :
    actualCircleMapDegree (f * g) = actualCircleMapDegree f + actualCircleMapDegree g := by
  obtain ⟨Hf⟩ := Classical.choose_spec (actual_circle_map_winding_homotopy_source f)
  obtain ⟨Hg⟩ := Classical.choose_spec (actual_circle_map_winding_homotopy_source g)
  apply actual_circle_map_degree_of_power_homotopy
  let K : C(unitInterval × Circle,Circle) := ⟨fun p => Hf p * Hg p, Hf.continuous.mul Hg.continuous⟩
  refine ⟨{ toContinuousMap := K, map_zero_left := ?_, map_one_left := ?_ }⟩
  · intro z
    change Hf (0,z) * Hg (0,z) = f z * g z
    rw [Hf.apply_zero, Hg.apply_zero]
  · intro z
    change Hf (1,z) * Hg (1,z) = z ^ (actualCircleMapDegree f + actualCircleMapDegree g)
    rw [Hf.apply_one, Hg.apply_one]
    exact (zpow_add _ _ _).symm

private theorem actual_circle_map_degree_inv (f : C(Circle,Circle)) :
    actualCircleMapDegree f⁻¹ = -actualCircleMapDegree f := by
  obtain ⟨Hf⟩ := Classical.choose_spec (actual_circle_map_winding_homotopy_source f)
  apply actual_circle_map_degree_of_power_homotopy
  let K : C(unitInterval × Circle,Circle) := ⟨fun p => (Hf p)⁻¹, Hf.continuous.inv⟩
  refine ⟨{ toContinuousMap := K, map_zero_left := ?_, map_one_left := ?_ }⟩
  · intro z
    change (Hf (0,z))⁻¹ = (f z)⁻¹
    rw [Hf.apply_zero]
  · intro z
    change (Hf (1,z))⁻¹ = z ^ (-actualCircleMapDegree f)
    rw [Hf.apply_one]
    exact (zpow_neg _ _).symm

private theorem actual_circle_map_degree_div (f g : C(Circle,Circle)) :
    actualCircleMapDegree (f / g) = actualCircleMapDegree f - actualCircleMapDegree g := by
  rw [div_eq_mul_inv, actual_circle_map_degree_mul, actual_circle_map_degree_inv, sub_eq_add_neg]

private theorem actual_two_tangent_fields_uniform_caps_boundary_index_invariance
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (P : Set E)
    {ι : Type} [Fintype ι]
    (V W : ∀ x : E, TangentSpace 𝓘(ℂ) x)
    (hV : Continuous (fun x => TotalSpace.mk' ℂ x (V x)))
    (hW : Continuous (fun x => TotalSpace.mk' ℂ x (W x)))
    (hVP : ∀ x ∈ P, V x ≠ 0) (hWP : ∀ x ∈ P, W x ≠ 0)
    (r : relativeHomology E P 2) (caps : ι → relativeHomology E P 2)
    (β : ι → C(Circle,P)) (k : ℤ) (hk : k ≠ 0)
    (hr : r = k • ∑ i, caps i)
    (hboundary : relativeConnecting E P 1 r = 0)
    (hcaps : ∀ i, relativeConnecting E P 1 (caps i) =
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (β i))) CircleFundamentalCycle.fundamentalClass)
    (c : ∀ i z, TangentSpace 𝓘(ℂ) (β i z).val ≃L[ℂ] ℂ)
    (u v : ι → C(Circle,Circle))
    (hu : ∀ i z, (u i z : ℂ) = c i z (V (β i z).val) /
      (‖c i z (V (β i z).val)‖:ℂ))
    (hv : ∀ i z, (v i z : ℂ) = c i z (W (β i z).val) /
      (‖c i z (W (β i z).val)‖:ℂ)) :
    (∑ i, actualCircleMapDegree (v i)) = ∑ i, actualCircleMapDegree (u i) := by
  classical
  obtain ⟨R,hR⟩ := actual_complex_tangent_nonvanishing_fields_have_literal_circle_ratio
    V W hV hW P hVP hWP
  have hratio (i : ι) : R.comp (β i) = v i / u i := by
    ext z
    change (R (β i z) : ℂ) = (v i z : ℂ) / (u i z : ℂ)
    rw [hu,hv]
    exact actual_global_tangent_circle_ratio_literal_chart_relation
      V W P R hR (β i z) (hVP _ (β i z).property) (hWP _ (β i z).property) (c i z)
  have hsum := actual_uniform_relative_caps_force_circle_boundary_degree_sum_zero
    P r caps β k hk hr hboundary hcaps R
  have hdiff : (∑ i, actualCircleMapDegree (v i)) -
      (∑ i, actualCircleMapDegree (u i)) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [hratio,actual_circle_map_degree_div] using hsum
  exact sub_eq_zero.mp hdiff
