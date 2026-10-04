import Mathlib
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import ClassificationJordanCurve.Arcs
import Schoenflies.JordanSchoenflies
open Set Topology Metric
open scoped Pointwise
set_option maxHeartbeats 0
private theorem actualCenter (a : EuclideanSpace ℝ (Fin 2)) (ha : ‖a‖ < 1) :
    ∃ F : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      F a=0 ∧ F '' closedBall 0 1=closedBall 0 1 ∧ F '' sphere 0 1=sphere 0 1 := by
  let s : Set (EuclideanSpace ℝ (Fin 2)) := (-a)+ᵥ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
  let t : Set (EuclideanSpace ℝ (Fin 2)) := closedBall 0 1
  have hsc : Convex ℝ s := (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).vadd (-a)
  have htc : Convex ℝ t := convex_closedBall 0 1
  have hsImage : s=(fun x => -a+x) '' closedBall 0 1 := rfl
  have hsCompact : IsCompact s := by
    rw [hsImage]
    exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).image
      (continuous_const.add continuous_id)
  have hsb : Bornology.IsVonNBounded ℝ s := NormedSpace.isVonNBounded_of_isBounded _ hsCompact.isBounded
  have htb : Bornology.IsVonNBounded ℝ t := NormedSpace.isVonNBounded_closedBall ℝ (EuclideanSpace ℝ (Fin 2)) 1
  have haBall : a ∈ ball 0 1 := by simpa only [mem_ball,dist_zero_right] using ha
  have hsInterior : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior s := by
    simpa [s,interior_vadd,interior_closedBall,mem_vadd_set_iff_neg_vadd_mem] using haBall
  have hs0 : s ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 2)) := mem_interior_iff_mem_nhds.mp hsInterior
  have ht0 : t ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 2)) := by
    apply mem_interior_iff_mem_nhds.mp
    simp [t,interior_closedBall]
  let G := gaugeRescaleHomeomorph s t hsc hs0 hsb htc ht0 htb
  let F := (Homeomorph.addLeft (-a)).trans G
  have hFa : F a=0 := by
    change gaugeRescale s t (-a+a)=0
    simp only [neg_add_cancel,gaugeRescale_zero]
  have hGImage : G '' s=t := by
    have h := image_gaugeRescaleHomeomorph_closure hsc hs0 hsb htc ht0 htb
    simpa only [hsCompact.isClosed.closure_eq, t, isClosed_closedBall.closure_eq] using h
  have hFImage : F '' closedBall 0 1=closedBall 0 1 := by
    change (G ∘ (fun x => -a+x)) '' closedBall 0 1=closedBall 0 1
    rw [Set.image_comp,←hsImage]
    exact hGImage
  refine ⟨F,hFa,hFImage,?_⟩
  have h := F.image_frontier (closedBall 0 1)
  rw [hFImage] at h
  simpa only [frontier_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (by norm_num : (1 : ℝ) ≠ 0)] using h

open ClassificationJordanCurve.Arcs CurveComplex
private theorem actualNormalize (c : Curve Plane) : ∃ F : Plane ≃ₜ Plane,
    ∀ z : Circle, F (c.map z) = complexLIE z := by
  let r : C(Circle, Plane) := ⟨fun z => (circleHomeoSphere z : Plane),
    continuous_subtype_val.comp circleHomeoSphere.continuous⟩
  have hr : Topology.IsEmbedding r :=
    Topology.IsEmbedding.subtypeVal.comp circleHomeoSphere.isEmbedding
  have hrange : Set.range r = sphere (0 : Plane) 1 := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩; exact (circleHomeoSphere z).property
    · intro hx
      refine ⟨circleHomeoSphere.symm ⟨x,hx⟩,?_⟩
      change (circleHomeoSphere (circleHomeoSphere.symm ⟨x,hx⟩) : Plane)=x
      rw [circleHomeoSphere.apply_symm_apply]
  have hJ := isJordanCurve_range_of_isEmbedding_circle r hr
  rw [hrange] at hJ
  -- the range homeomorphism has the opposite direction here
  let ec : c.image ≃ₜ sphere (0 : Plane) 1 := c.embedded.toHomeomorph.symm.trans circleHomeoSphere
  obtain ⟨F,hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    (isJordanCurve_range_of_isEmbedding_circle ⟨c.map,c.embedded.continuous⟩ c.embedded) hJ ec
  refine ⟨F,fun z => ?_⟩
  have h := hF ⟨c.map z,⟨z,rfl⟩⟩
  simpa [ec] using h

private theorem actualInsideNorm (x : Plane) (hx : x ∈ Schoenflies.inside (sphere (0 : Plane) 1)) : ‖x‖ < 1 := by
  let r : C(Circle, Plane) := ⟨fun z => (circleHomeoSphere z : Plane),
    continuous_subtype_val.comp circleHomeoSphere.continuous⟩
  have hr : Topology.IsEmbedding r :=
    Topology.IsEmbedding.subtypeVal.comp circleHomeoSphere.isEmbedding
  have hrange : Set.range r = sphere (0 : Plane) 1 := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩; exact (circleHomeoSphere z).property
    · intro hy
      refine ⟨circleHomeoSphere.symm ⟨y,hy⟩,?_⟩
      change (circleHomeoSphere (circleHomeoSphere.symm ⟨y,hy⟩) : Plane)=y
      rw [circleHomeoSphere.apply_symm_apply]
  have hJ := isJordanCurve_range_of_isEmbedding_circle r hr
  rw [hrange] at hJ
  let d : C(closedBall (0 : Plane) 1, Plane) := ⟨Subtype.val,continuous_subtype_val⟩
  have hb : d '' {z : closedBall (0 : Plane) 1 | z.val ∈ sphere (0 : Plane) 1} = sphere (0 : Plane) 1 := by
    ext z
    constructor
    · rintro ⟨q,hq,rfl⟩; exact hq
    · intro hz; exact ⟨⟨z,sphere_subset_closedBall hz⟩,hz,rfl⟩
  have h := embedded_disc_range_eq_closed_inside d Topology.IsEmbedding.subtypeVal _ hJ hb
  have hxrange : x ∈ Set.range d := by rw [h]; exact Or.inl hx
  obtain ⟨q,hq⟩ := hxrange
  have hle : ‖x‖ ≤ 1 := by
    have hp := q.property
    rw [mem_closedBall,dist_zero_right] at hp
    exact hq ▸ hp
  apply lt_of_le_of_ne hle
  intro heq
  exact hx.1 (mem_sphere_zero_iff_norm.mpr heq)

private noncomputable def actualRadialCircle : C({x : Plane // x ≠ 0}, Circle) where
  toFun x := ⟨(‖complexLIE.symm x.val‖⁻¹ : ℝ) • complexLIE.symm x.val, by
    apply mem_sphere_zero_iff_norm.mpr
    change ‖(‖complexLIE.symm x.val‖⁻¹ : ℝ) • complexLIE.symm x.val‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (fun h => x.property (complexLIE.symm.injective (by simpa using h)))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine Continuous.smul (f := fun x : {x : Plane // x ≠ 0} => (‖complexLIE.symm x.val‖⁻¹ : ℝ))
      (g := fun x : {x : Plane // x ≠ 0} => complexLIE.symm x.val) ?_ ?_
    · apply Continuous.inv₀
      · exact continuous_norm.comp (complexLIE.symm.continuous.comp continuous_subtype_val)
      · intro x
        exact norm_ne_zero_iff.mpr (fun h => x.property (complexLIE.symm.injective (by simpa using h)))
    · exact complexLIE.symm.continuous.comp continuous_subtype_val

private theorem actualCircleNotNull : ¬ (ContinuousMap.id Circle).Nullhomotopic := by
  intro hNull
  letI : ContractibleSpace Circle := (contractible_iff_id_nullhomotopic Circle).mpr hNull
  letI : SimplyConnectedSpace Circle := inferInstance
  let G := AddSubgroup.zmultiples (2*Real.pi)
  let e := Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
    (x := Circle.exp 0) ⟨0,rfl⟩
  let a : G := ⟨0,(AddSubgroup.zmultiples (2*Real.pi)).zero_mem⟩
  let b : G := ⟨2*Real.pi,AddSubgroup.mem_zmultiples (2*Real.pi)⟩
  have hab : MulOpposite.op (Multiplicative.ofAdd a) =
      MulOpposite.op (Multiplicative.ofAdd b) := by
    apply e.symm.injective
    exact Subsingleton.elim _ _
  have hv : (0 : ℝ)=2*Real.pi :=
    congrArg (fun z : (Multiplicative G)ᵐᵒᵖ => ((MulOpposite.unop z).toAdd : ℝ)) hab
  linarith [Real.pi_pos]

namespace CurveComplex
open Set Topology
theorem actual_planar_jordan_inside_subset_nullhomotopy_range
    (c : Curve (EuclideanSpace ℝ (Fin 2))) (y : EuclideanSpace ℝ (Fin 2))
    (H : ContinuousMap.Homotopy
      (⟨c.map, c.embedded.continuous⟩ : C(Circle, EuclideanSpace ℝ (Fin 2)))
      (ContinuousMap.const Circle y)) :
    Schoenflies.inside c.image ⊆ Set.range H := by
  classical
  intro x hx
  by_contra hxH
  obtain ⟨F,hF⟩ := actualNormalize c
  have himage : F '' c.image = sphere (0 : Plane) 1 := by
    ext q
    constructor
    · rintro ⟨w,⟨z,rfl⟩,rfl⟩
      rw [hF]; exact (circleHomeoSphere z).property
    · intro hq
      refine ⟨c.map (circleHomeoSphere.symm ⟨q,hq⟩),⟨_,rfl⟩,?_⟩
      rw [hF]
      exact congrArg Subtype.val (circleHomeoSphere.apply_symm_apply ⟨q,hq⟩)
  have hFx : F x ∈ Schoenflies.inside (sphere (0 : Plane) 1) := by
    rw [←himage,←jordan_inside_homeomorph_image]
    exact ⟨x,hx,rfl⟩
  obtain ⟨G,hGx,hGball,hGsphere⟩ := actualCenter (F x) (actualInsideNorm _ hFx)
  have hGiff : ∀ q : Plane, q ∈ sphere 0 1 ↔ G q ∈ sphere 0 1 := by
    intro q
    constructor
    · intro hq; rw [←hGsphere]; exact ⟨q,hq,rfl⟩
    · intro hq
      rw [←hGsphere] at hq
      obtain ⟨w,hw,heq⟩ := hq
      exact G.injective heq ▸ hw
  let j : Circle ≃ₜ Circle := circleHomeoSphere.trans
    ((G.subtype hGiff).trans circleHomeoSphere.symm)
  have hj : ∀ z : Circle, G (F (c.map z)) = complexLIE (j z) := by
    intro z
    rw [hF]
    have ht := congrArg Subtype.val (circleHomeoSphere.apply_symm_apply
      ((G.subtype hGiff) (circleHomeoSphere z)))
    exact ht.symm
  have havoid : ∀ t : unitInterval × Circle, G (F (H t)) ≠ 0 := by
    intro t heq
    have hh : H t=x := F.injective (G.injective (heq.trans hGx.symm))
    exact hxH ⟨t,hh⟩
  let R : C(unitInterval × Circle, Circle) := actualRadialCircle.comp
    ⟨fun t => ⟨G (F (H t)),havoid t⟩,
      (G.continuous.comp (F.continuous.comp H.continuous)).subtype_mk _⟩
  have hRzero : ∀ z : Circle, R (0,z)=j z := by
    intro z
    apply Subtype.ext
    change (‖complexLIE.symm (G (F (H (0,z))))‖⁻¹ : ℝ) •
      complexLIE.symm (G (F (H (0,z)))) = (j z : ℂ)
    have hzero : H (0,z)=c.map z := H.map_zero_left z
    rw [hzero,hj]
    simp [(j z).norm_coe]
  have hRone : ∀ z : Circle, R (1,z)=R (1,1) := by
    intro z
    change actualRadialCircle ⟨G (F (H (1,z))),_⟩ =
      actualRadialCircle ⟨G (F (H (1,1))),_⟩
    congr 1
    apply Subtype.ext
    have hone : H (1,z)=y := H.map_one_left z
    have hone1 : H (1,(1 : Circle))=y := H.map_one_left 1
    exact congrArg (fun w => G (F w)) (hone.trans hone1.symm)
  let HR : ContinuousMap.Homotopy (⟨j,j.continuous⟩ : C(Circle,Circle))
      (ContinuousMap.const Circle (R (1,1))) := {
    toFun := R
    continuous_toFun := R.continuous
    map_zero_left := hRzero
    map_one_left := hRone }
  have hn : (⟨j,j.continuous⟩ : C(Circle,Circle)).Nullhomotopic := ⟨_,⟨HR⟩⟩
  have hnid := hn.comp_left (⟨j.symm,j.symm.continuous⟩ : C(Circle,Circle))
  apply actualCircleNotNull
  convert hnid using 1
  ext z
  simpa using congrArg (fun w : Circle => (w : ℂ)) (j.apply_symm_apply z).symm
end CurveComplex

#print axioms CurveComplex.actual_planar_jordan_inside_subset_nullhomotopy_range
