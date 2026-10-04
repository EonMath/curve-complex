import CurveComplexGenusTwo.Topology.LocalOrientation.LocalReflectionGerm
import CurveComplexGenusTwo.CWHurewicz.HomotopyHomologyIso
import CurveComplexGenusTwo.CWHurewicz.ConnectingNaturality
import CurveComplexGenusTwo.CWHurewicz.PairExactnessInterface
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseStatements
import CurveComplexGenusTwo.CWHurewicz.ExcisionDifferentialTransport
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.ContinuousMap.Sigma
import Mathlib.LinearAlgebra.Finsupp.SumProd
open CategoryTheory CategoryTheory.Limits Set Metric Topology Convexity
open CurveComplexGenusTwo.CWHurewicz
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

private theorem actual_literal_punctured_disc_boundary_deformation
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    let D := closedBall z₀ ρ;
    let B : Set D := {x | dist x.val z₀ = ρ};
    let P : Set D := {x | x.val ≠ z₀};
    ∃ (r : C(P,B)) (i : C(B,P)),
      (∀ x, (i x).val = x.val) ∧
      r.comp i = ContinuousMap.id B ∧
      Nonempty (ContinuousMap.Homotopy (ContinuousMap.id P) (i.comp r)) := by
  dsimp only
  let D := closedBall z₀ ρ
  let B : Set D := {x | dist x.val z₀ = ρ}
  let P : Set D := {x | x.val ≠ z₀}
  have hn (x : P) : 0 < ‖x.val.val-z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr x.property)
  have hnle (x : P) : ‖x.val.val-z₀‖ ≤ ρ := by
    simpa only [D,mem_closedBall,dist_eq_norm] using x.val.property
  let a (x : P) : ℝ := ρ / ‖x.val.val-z₀‖
  have ha (x : P) : 0 < a x := div_pos hρ (hn x)
  have han (x : P) : a x * ‖x.val.val-z₀‖ = ρ := by
    dsimp [a]; exact div_mul_cancel₀ ρ (hn x).ne'
  have hrnorm (x : P) : dist (z₀+a x • (x.val.val-z₀)) z₀ = ρ := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (ha x),han]
  let r : C(P,B) := ⟨fun x => ⟨⟨z₀+a x • (x.val.val-z₀),by rw [mem_closedBall,hrnorm]⟩,hrnorm x⟩,by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hv : Continuous (fun x : P => x.val.val-z₀) := by fun_prop
    exact continuous_const.add ((continuous_const.div hv.norm (fun x => (hn x).ne')).smul hv)⟩
  have hbne (x : B) : x.val.val ≠ z₀ := by
    intro he; have hd : dist x.val.val z₀ = ρ := x.property
    rw [he,dist_self] at hd
    exact hρ.ne' hd.symm
  let i : C(B,P) := ⟨fun x => ⟨x.val,hbne x⟩,continuous_subtype_val.subtype_mk hbne⟩
  have hri : r.comp i = ContinuousMap.id B := by
    ext x
    have hnx : ‖x.val.val-z₀‖ = ρ := by simpa only [B,mem_setOf_eq,dist_eq_norm] using x.property
    change z₀ + (ρ/‖x.val.val-z₀‖) • (x.val.val-z₀) = x.val.val
    rw [hnx,div_self hρ.ne',one_smul]
    abel
  let c (t : unitInterval) (x : P) : ℝ := 1-(t:ℝ)+(t:ℝ)*a x
  have hc (t : unitInterval) (x : P) : 0 < c t x := by
    have ht₀ := t.property.1; have ht₁ := t.property.2
    dsimp [c]
    by_cases ht : (t:ℝ)=0
    · simp only [ht,sub_zero,zero_mul,add_zero]; norm_num
    · have hp := mul_pos (lt_of_le_of_ne ht₀ (Ne.symm ht)) (ha x)
      linarith
  have hcn (t : unitInterval) (x : P) : c t x * ‖x.val.val-z₀‖ ≤ ρ := by
    have ht₀ := t.property.1; have ht₁ := t.property.2
    have he := han x; have hb := hnle x
    dsimp [c]
    nlinarith
  have hclosed (t : unitInterval) (x : P) : z₀+c t x • (x.val.val-z₀) ∈ D := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_pos (hc t x)]
    exact hcn t x
  have hne (t : unitInterval) (x : P) : z₀+c t x • (x.val.val-z₀) ≠ z₀ := by
    intro he
    have hz : c t x • (x.val.val-z₀) = 0 := by
      have hh := congrArg (fun z : ℂ => z-z₀) he
      simpa only [add_sub_cancel_left,sub_self] using hh
    exact (smul_ne_zero (hc t x).ne' (sub_ne_zero.mpr x.property)) hz
  let H : ContinuousMap.Homotopy (ContinuousMap.id P) (i.comp r) := {
    toFun := fun tx => ⟨⟨z₀+c tx.1 tx.2 • (tx.2.val.val-z₀),hclosed tx.1 tx.2⟩,hne tx.1 tx.2⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      have ht : Continuous (fun tx : unitInterval × P => (tx.1:ℝ)) := by fun_prop
      have hv : Continuous (fun tx : unitInterval × P => tx.2.val.val-z₀) := by fun_prop
      have hav : Continuous (fun tx : unitInterval × P => a tx.2) :=
        continuous_const.div hv.norm (fun tx => (hn tx.2).ne')
      exact continuous_const.add (((continuous_const.sub ht).add (ht.mul hav)).smul hv)
    map_zero_left := by
      intro x
      apply Subtype.ext; apply Subtype.ext
      change z₀+(1-(0:ℝ)+(0:ℝ)*a x) • (x.val.val-z₀) = x.val.val
      simp
    map_one_left := by
      intro x
      apply Subtype.ext; apply Subtype.ext
      change z₀+(1-(1:ℝ)+(1:ℝ)*a x) • (x.val.val-z₀) = z₀+a x • (x.val.val-z₀)
      simp }
  exact ⟨r,i,fun x => rfl,hri,⟨H⟩⟩

private theorem actual_literal_punctured_disc_boundary_fixed_deformation
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    let D := closedBall z₀ ρ;
    let P : Set D := {x | x.val ≠ z₀};
    let B : Set P := {x | dist x.val.val z₀ = ρ};
    ∃ r : C(P,P),
      (∀ x, dist (r x).val.val z₀ = ρ) ∧
      Nonempty (ContinuousMap.HomotopyRel (ContinuousMap.id P) r B) := by
  dsimp only
  let D := closedBall z₀ ρ
  let P : Set D := {x | x.val ≠ z₀}
  let B : Set P := {x | dist x.val.val z₀ = ρ}
  have hn (x : P) : 0 < ‖x.val.val-z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr x.property)
  have hnle (x : P) : ‖x.val.val-z₀‖ ≤ ρ := by
    simpa only [D,mem_closedBall,dist_eq_norm] using x.val.property
  let a (x : P) : ℝ := ρ / ‖x.val.val-z₀‖
  have ha (x : P) : 0 < a x := div_pos hρ (hn x)
  have han (x : P) : a x * ‖x.val.val-z₀‖ = ρ := by
    dsimp [a]; exact div_mul_cancel₀ ρ (hn x).ne'
  have hrnorm (x : P) : dist (z₀+a x • (x.val.val-z₀)) z₀ = ρ := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (ha x),han]
  let c (t : unitInterval) (x : P) : ℝ := 1-(t:ℝ)+(t:ℝ)*a x
  have hc (t : unitInterval) (x : P) : 0 < c t x := by
    have ht₀ := t.property.1; have ht₁ := t.property.2
    dsimp [c]
    by_cases ht : (t:ℝ)=0
    · simp only [ht,sub_zero,zero_mul,add_zero]; norm_num
    · have hp := mul_pos (lt_of_le_of_ne ht₀ (Ne.symm ht)) (ha x)
      linarith
  have hcn (t : unitInterval) (x : P) : c t x * ‖x.val.val-z₀‖ ≤ ρ := by
    have ht₀ := t.property.1; have ht₁ := t.property.2
    have he := han x; have hb := hnle x
    dsimp [c]
    nlinarith
  have hclosed (t : unitInterval) (x : P) : z₀+c t x • (x.val.val-z₀) ∈ D := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_pos (hc t x)]
    exact hcn t x
  have hne (t : unitInterval) (x : P) : z₀+c t x • (x.val.val-z₀) ≠ z₀ := by
    intro he
    have hz : c t x • (x.val.val-z₀) = 0 := by
      have hh := congrArg (fun z : ℂ => z-z₀) he
      simpa only [add_sub_cancel_left,sub_self] using hh
    exact (smul_ne_zero (hc t x).ne' (sub_ne_zero.mpr x.property)) hz
  let r : C(P,P) := ⟨fun x => ⟨⟨z₀+a x • (x.val.val-z₀),
      by rw [mem_closedBall,hrnorm]⟩, by
        intro he
        have hz : a x • (x.val.val-z₀) = 0 := by
          have hh := congrArg (fun z : ℂ => z-z₀) he
          simpa only [add_sub_cancel_left,sub_self] using hh
        exact (smul_ne_zero (ha x).ne' (sub_ne_zero.mpr x.property)) hz⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hv : Continuous (fun x : P => x.val.val-z₀) := by fun_prop
    exact continuous_const.add ((continuous_const.div hv.norm (fun x => (hn x).ne')).smul hv)⟩
  let H : ContinuousMap.HomotopyRel (ContinuousMap.id P) r B := {
    toFun := fun tx => ⟨⟨z₀+c tx.1 tx.2 • (tx.2.val.val-z₀),
      hclosed tx.1 tx.2⟩, hne tx.1 tx.2⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      have ht : Continuous (fun tx : unitInterval × P => (tx.1:ℝ)) := by fun_prop
      have hv : Continuous (fun tx : unitInterval × P => tx.2.val.val-z₀) := by fun_prop
      have hav : Continuous (fun tx : unitInterval × P => a tx.2) :=
        continuous_const.div hv.norm (fun tx => (hn tx.2).ne')
      exact continuous_const.add (((continuous_const.sub ht).add (ht.mul hav)).smul hv)
    map_zero_left := by
      intro x
      apply Subtype.ext; apply Subtype.ext
      change z₀+(1-(0:ℝ)+(0:ℝ)*a x) • (x.val.val-z₀) = x.val.val
      simp
    map_one_left := by
      intro x
      apply Subtype.ext; apply Subtype.ext
      change z₀+(1-(1:ℝ)+(1:ℝ)*a x) • (x.val.val-z₀) = z₀+a x • (x.val.val-z₀)
      simp
    prop' := by
      intro t x hx
      apply Subtype.ext; apply Subtype.ext
      have hnx : ‖x.val.val-z₀‖ = ρ := by
        have hx' : dist x.val.val z₀ = ρ := hx
        simpa only [dist_eq_norm] using hx'
      change z₀+c t x • (x.val.val-z₀) = x.val.val
      have haone : a x = 1 := by dsimp [a]; rw [hnx,div_self hρ.ne']
      simp only [c,haone,mul_one,sub_add_cancel,one_smul]
      abel }
  exact ⟨r,hrnorm,⟨H⟩⟩
#print axioms actual_literal_punctured_disc_boundary_fixed_deformation

private theorem actual_literal_closed_disc_connecting_any_subspace_isIso
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (A : Set (closedBall z₀ ρ)) :
    IsIso (relativeConnecting (closedBall z₀ ρ) A 1) := by
  let D := closedBall z₀ ρ
  letI : ContractibleSpace D :=
    (convex_closedBall z₀ ρ).contractibleSpace ⟨z₀,mem_closedBall_self hρ.le⟩
  have hz₁ : IsZero (H D 1) :=
    CircleHomologyComputation.contractible_positive_homology D 1 (by omega)
  have hz₂ : IsZero (H D 2) :=
    CircleHomologyComputation.contractible_positive_homology D 2 (by omega)
  obtain ⟨_,hex₂⟩ := pairHomology_exact_at_relative D A 1
  obtain ⟨_,hex₁⟩ := pairHomology_exact_at_subspace D A 1
  haveI : Mono (relativeConnecting D A 1) := hex₂.mono_g (hz₂.eq_of_src _ _)
  haveI : Epi (relativeConnecting D A 1) := hex₁.epi_f (hz₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

private theorem actual_literal_disc_boundary_to_puncture_relative_isIso
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    let D := closedBall z₀ ρ;
    let B : Set D := {x | dist x.val z₀ = ρ};
    let P : Set D := {x | x.val ≠ z₀};
    ∃ h : ∀ x ∈ B, (ContinuousMap.id D) x ∈ P,
      IsIso (pairRelativeHomologyMap B P (ContinuousMap.id D) h 2) := by
  dsimp only
  let D := closedBall z₀ ρ
  let B : Set D := {x | dist x.val z₀ = ρ}
  let P : Set D := {x | x.val ≠ z₀}
  obtain ⟨r,i,hi,hri,⟨H⟩⟩ := actual_literal_punctured_disc_boundary_deformation z₀ ρ hρ
  have hBP : ∀ x ∈ B, (ContinuousMap.id D) x ∈ P := by
    intro x hx
    have h := (i ⟨x,hx⟩).property
    change (i ⟨x,hx⟩).val.val ≠ z₀ at h
    rw [hi] at h
    exact h
  refine ⟨hBP,?_⟩
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  let e := singularHomologyIsoOfHomotopyInverse (ModuleCat.of ℤ ℤ) 1 r i
    ⟨H.symm⟩ (hri ▸ ⟨ContinuousMap.Homotopy.refl _⟩)
  haveI : IsIso (F.map (TopCat.ofHom i)) := e.isIso_inv
  have heq : pairMapOnSubspace B P (ContinuousMap.id D) hBP = TopCat.ofHom i := by
    ext x
    exact (congrArg Subtype.val (hi x)).symm
  haveI : IsIso (F.map (pairMapOnSubspace B P (ContinuousMap.id D) hBP)) := by
    rw [heq]; infer_instance
  haveI : IsIso (relativeConnecting D B 1) :=
    actual_literal_closed_disc_connecting_any_subspace_isIso z₀ ρ hρ B
  haveI : IsIso (relativeConnecting D P 1) :=
    actual_literal_closed_disc_connecting_any_subspace_isIso z₀ ρ hρ P
  have hn := relativeConnecting_natural B P (ContinuousMap.id D) hBP 1
  haveI : IsIso (pairRelativeHomologyMap B P (ContinuousMap.id D) hBP 2 ≫
      relativeConnecting D P 1) := by rw [← hn]; infer_instance
  exact IsIso.of_isIso_comp_right _ (relativeConnecting D P 1)

private theorem actual_literal_closed_chart_disc_puncture_localization_isIso
    (E : Type) [TopologicalSpace E] [T1Space E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ) (hρ : 0 < ρ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    let D := closedBall ((chartAt ℂ q) q) ρ;
    let P : Set D := {x | x.val ≠ (chartAt ℂ q) q};
    ∃ (f : C(D,E)) (h : ∀ x ∈ P, f x ∈ ({q}ᶜ : Set E)),
      (∀ d, f d = (chartAt ℂ q).symm d.val) ∧
      IsIso (pairRelativeHomologyMap P ({q}ᶜ) f h 2) := by
  dsimp only
  let cq := chartAt ℂ q
  let D := closedBall (cq q) ρ
  let P : Set D := {x | x.val ≠ cq q}
  let W : Set E := cq.source ∩ cq ⁻¹' D
  let U : Set E := cq.source ∩ cq ⁻¹' ball (cq q) ρ
  have hU : IsOpen U := cq.isOpen_inter_preimage isOpen_ball
  have hqU : q ∈ U := ⟨mem_chart_source ℂ q,mem_ball_self hρ⟩
  have hUW : U ⊆ W := fun y hy => ⟨hy.1,ball_subset_closedBall hy.2⟩
  have hqW : q ∈ interior W := mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hU.mem_nhds hqU) hUW)
  have hexc : closure Wᶜ ⊆ interior ({q}ᶜ : Set E) := by
    rw [isOpen_compl_singleton.interior_eq,closure_compl]
    intro y hy
    change y ≠ q
    intro heq; subst y
    exact hy hqW
  let e : D ≃ₜ W := {
    toFun := fun z => ⟨cq.symm z,⟨cq.map_target (htarget z.property),by
      change cq (cq.symm z.val) ∈ D
      rw [cq.right_inv (htarget z.property)];exact z.property⟩⟩
    invFun := fun y => ⟨cq y,y.property.2⟩
    left_inv := fun z => Subtype.ext (cq.right_inv (htarget z.property))
    right_inv := fun y => Subtype.ext (cq.left_inv y.property.1)
    continuous_toFun := (cq.symm.continuousOn.comp_continuous continuous_subtype_val
      (fun z => htarget z.property)).subtype_mk _
    continuous_invFun := (cq.continuousOn.comp_continuous continuous_subtype_val
      (fun y => y.property.1)).subtype_mk _ }
  let WP : Set W := {y | y.val ≠ q}
  have hp : ∀ z ∈ P, e z ∈ WP := by
    intro z hz heq
    apply hz
    have he := congrArg cq heq
    change cq (cq.symm z.val) = cq q at he
    rw [cq.right_inv (htarget z.property)] at he
    exact he
  have hpi : ∀ y ∈ WP, e.symm y ∈ P := by
    intro y hy heq
    apply hy
    exact cq.injOn y.property.1 (mem_chart_source ℂ q) heq
  let k : C(D,W) := ⟨e,e.continuous⟩
  let j : C(W,E) := ReflectionGermProof.inclusion W
  let f : C(D,E) := j.comp k
  have hj : ∀ y ∈ WP, j y ∈ ({q}ᶜ : Set E) := fun y hy => hy
  have hf : ∀ z ∈ P, f z ∈ ({q}ᶜ : Set E) := fun z hz => hj (k z) (hp z hz)
  haveI : IsIso (pairRelativeHomologyMap P WP k hp 2) :=
    ReflectionGermProof.pairHomeo_isIso P WP e hp hpi 2
  haveI : IsIso (pairRelativeHomologyMap WP ({q}ᶜ) j hj 2) :=
    ReflectionGermProof.inclusion_isIso ({q}ᶜ) W hexc
  refine ⟨f,hf,fun d => rfl,?_⟩
  rw [pairRelativeHomologyMap_comp P WP ({q}ᶜ) k j hp hj 2]
  infer_instance

private theorem actual_literal_disc_boundary_chart_point_localization_isIso
    (E : Type) [TopologicalSpace E] [T1Space E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ) (hρ : 0 < ρ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    let D := closedBall ((chartAt ℂ q) q) ρ;
    let B : Set D := {x | dist x.val ((chartAt ℂ q) q) = ρ};
    ∀ f : C(D,E), (∀ d, f d = (chartAt ℂ q).symm d.val) →
      ∃ h : ∀ x ∈ B, f x ∈ ({q}ᶜ : Set E),
        IsIso (pairRelativeHomologyMap B ({q}ᶜ) f h 2) := by
  dsimp only
  let D := closedBall ((chartAt ℂ q) q) ρ
  let B : Set D := {x | dist x.val ((chartAt ℂ q) q) = ρ}
  let P : Set D := {x | x.val ≠ (chartAt ℂ q) q}
  intro f hf
  obtain ⟨g,hg,hglit,hgiso⟩ :=
    actual_literal_closed_chart_disc_puncture_localization_isIso E q ρ hρ htarget
  have hfg : f = g := ContinuousMap.ext (fun d => (hf d).trans (hglit d).symm)
  subst g
  obtain ⟨hBP,hBPiso⟩ := actual_literal_disc_boundary_to_puncture_relative_isIso
    ((chartAt ℂ q) q) ρ hρ
  let hb : ∀ x ∈ B, f x ∈ ({q}ᶜ : Set E) := fun x hx => hg x (hBP x hx)
  refine ⟨hb,?_⟩
  haveI := hgiso
  haveI := hBPiso
  have hm := pairRelativeHomologyMap_comp B P ({q}ᶜ) (ContinuousMap.id D) f hBP hg 2
  have heq : pairRelativeHomologyMap B ({q}ᶜ) f hb 2 =
      pairRelativeHomologyMap B P (ContinuousMap.id D) hBP 2 ≫
      pairRelativeHomologyMap P ({q}ᶜ) f hg 2 := by
    simpa only [ContinuousMap.comp_id] using hm
  rw [heq]
  infer_instance

private theorem actual_literal_complex_closed_disc_relative_cap_class
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    let D := closedBall z₀ ρ;
    let B : Set D := {x | dist x.val z₀ = ρ};
    ∃ γ : C(Circle,B),
      (∀ z, ((γ z).val.val : ℂ) = z₀+(ρ:ℂ)*z) ∧
      ∃ r : relativeHomology D B 2,
        relativeConnecting D B 1 r =
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ)) CircleFundamentalCycle.fundamentalClass := by
  let D := closedBall z₀ ρ
  let B : Set D := {x | dist x.val z₀ = ρ}
  have hnorm (z : Circle) : dist (z₀+(ρ:ℂ)*z) z₀ = ρ := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hρ,Circle.norm_coe,mul_one]
  have hD (z : Circle) : z₀+(ρ:ℂ)*z ∈ D := by rw [mem_closedBall,hnorm]
  let γ₀ : C(Circle,D) :=
    ⟨fun z => ⟨z₀+(ρ:ℂ)*z,hD z⟩,
      (show Continuous (fun z : Circle => z₀+(ρ:ℂ)*z) from by fun_prop).subtype_mk hD⟩
  let γ : C(Circle,B) :=
    ⟨fun z => ⟨γ₀ z,hnorm z⟩, γ₀.continuous.subtype_mk (fun z => hnorm z)⟩
  refine ⟨γ,fun z => rfl,?_⟩
  letI : Nonempty D := ⟨⟨z₀,mem_closedBall_self hρ.le⟩⟩
  letI : ContractibleSpace D := (convex_closedBall z₀ ρ).contractibleSpace ⟨z₀,mem_closedBall_self hρ.le⟩
  have hz : IsZero (H D 1) := CircleHomologyComputation.contractible_positive_homology D 1 (by omega)
  let c : H B 1 :=
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ)) CircleFundamentalCycle.fundamentalClass
  have hcz : homologyInclusion D B 1 c = 0 := by
    letI : Subsingleton (H D 1) := ModuleCat.subsingleton_of_isZero hz
    exact Subsingleton.elim _ _
  obtain ⟨_,hexact⟩ := pairHomology_exact_at_subspace D B 1
  exact (ShortComplex.moduleCat_exact_iff _).mp hexact c hcz


private theorem actual_literal_scaled_circle_boundary_surjective
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (γ : C(Circle, {x : closedBall z₀ ρ | dist x.val z₀ = ρ}))
    (hγ : ∀ z, (γ z).val.val = z₀+(ρ:ℂ)*z) : Function.Surjective γ := by
  intro d
  have hnorm : ‖d.val.val-z₀‖ = ρ := by
    have hd : dist d.val.val z₀ = ρ := d.property
    simpa only [dist_eq_norm] using hd
  have hρc : (ρ:ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hunit : (d.val.val-z₀)/(ρ:ℂ) ∈ Submonoid.unitSphere ℂ := by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,hnorm,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ,div_self hρ.ne']
  let z : Circle := ⟨(d.val.val-z₀)/(ρ:ℂ),hunit⟩
  refine ⟨z,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rw [hγ]
  change z₀+(ρ:ℂ)*((d.val.val-z₀)/(ρ:ℂ))=d.val.val
  field_simp
  <;> ring

private theorem actual_literal_chart_boundary_has_disc_supported_relative_cap
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ) (hρ : 0 < ρ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target)
    (P : Set E) (β : C(Circle,P))
    (hβ : ∀ z, (β z : E) = (chartAt ℂ q).symm ((chartAt ℂ q) q + (ρ:ℂ)*z)) :
    let D := closedBall ((chartAt ℂ q) q) ρ;
    let B : Set D := {x | dist x.val ((chartAt ℂ q) q) = ρ};
    ∃ (γ : C(Circle,B)) (fD : C(D,E)) (hpair : ∀ x ∈ B, fD x ∈ P) (rD : relativeHomology D B 2),
      (∀ z, (γ z).val.val = (chartAt ℂ q) q+(ρ:ℂ)*z) ∧
      (∀ d, fD d = (chartAt ℂ q).symm d.val) ∧
      (relativeConnecting D B 1 rD =
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ)) CircleFundamentalCycle.fundamentalClass) ∧
      relativeConnecting E P 1 (pairRelativeHomologyMap B P fD hpair 2 rD) =
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom β)) CircleFundamentalCycle.fundamentalClass := by
  classical
  let D := closedBall ((chartAt ℂ q) q) ρ
  let B : Set D := {x | dist x.val ((chartAt ℂ q) q) = ρ}
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)
  obtain ⟨γ,hγ,rD,hδ⟩ := actual_literal_complex_closed_disc_relative_cap_class ((chartAt ℂ q) q) ρ hρ
  let fD : C(D,E) := ⟨fun d => (chartAt ℂ q).symm d.val,
    (chartAt ℂ q).symm.continuousOn.comp_continuous continuous_subtype_val (fun d => htarget d.property)⟩
  have hfγ (z : Circle) : fD (γ z).val = (β z : E) := by
    change (chartAt ℂ q).symm (γ z).val.val = (β z : E)
    rw [hγ]
    exact (hβ z).symm
  have hpair : ∀ x ∈ B, fD x ∈ P := by
    intro x hx
    obtain ⟨z,hz⟩ := actual_literal_scaled_circle_boundary_surjective _ ρ hρ γ hγ ⟨x,hx⟩
    have hxγ : (γ z).val = x := congrArg Subtype.val hz
    rw [← hxγ,hfγ]
    exact (β z).property
  have hcomp : TopCat.ofHom γ ≫ pairMapOnSubspace B P fD hpair = TopCat.ofHom β := by
    ext z
    exact hfγ z
  have hmaps : F.map (pairMapOnSubspace B P fD hpair)
      (F.map (TopCat.ofHom γ) CircleFundamentalCycle.fundamentalClass) =
      F.map (TopCat.ofHom β) CircleFundamentalCycle.fundamentalClass := by
    change (F.map (TopCat.ofHom γ) ≫ F.map (pairMapOnSubspace B P fD hpair))
      CircleFundamentalCycle.fundamentalClass = _
    rw [← F.map_comp,hcomp]
  have hn := congrArg (fun f => f rD) (relativeConnecting_natural B P fD hpair 1)
  change F.map (pairMapOnSubspace B P fD hpair) (relativeConnecting D B 1 rD) =
    relativeConnecting E P 1 (pairRelativeHomologyMap B P fD hpair 2 rD) at hn
  rw [hδ,hmaps] at hn
  exact ⟨γ,fD,hpair,rD,hγ,fun d => rfl,hδ,hn.symm⟩

private theorem actual_literal_complex_disc_connecting_isIso
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    let D := closedBall z₀ ρ;
    let B : Set D := {x | dist x.val z₀ = ρ};
    IsIso (relativeConnecting D B 1) := by
  let D := closedBall z₀ ρ
  let B : Set D := {x | dist x.val z₀ = ρ}
  letI : ContractibleSpace D :=
    (convex_closedBall z₀ ρ).contractibleSpace ⟨z₀,mem_closedBall_self hρ.le⟩
  have hz₁ : IsZero (H D 1) :=
    CircleHomologyComputation.contractible_positive_homology D 1 (by omega)
  have hz₂ : IsZero (H D 2) :=
    CircleHomologyComputation.contractible_positive_homology D 2 (by omega)
  obtain ⟨_,hex₂⟩ := pairHomology_exact_at_relative D B 1
  obtain ⟨_,hex₁⟩ := pairHomology_exact_at_subspace D B 1
  haveI : Mono (relativeConnecting D B 1) := hex₂.mono_g (hz₂.eq_of_src _ _)
  haveI : Epi (relativeConnecting D B 1) := hex₁.epi_f (hz₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

private theorem actual_literal_complex_disc_normalized_cap_unique
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    let D := closedBall z₀ ρ;
    let B : Set D := {x | dist x.val z₀ = ρ};
    ∀ (r t : relativeHomology D B 2),
      relativeConnecting D B 1 r = relativeConnecting D B 1 t → r = t := by
  let D := closedBall z₀ ρ
  let B : Set D := {x | dist x.val z₀ = ρ}
  haveI : IsIso (relativeConnecting D B 1) :=
    actual_literal_complex_disc_connecting_isIso z₀ ρ hρ
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

private theorem actual_literal_scaled_circle_boundary_homeomorph
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (γ : C(Circle, {x : closedBall z₀ ρ | dist x.val z₀ = ρ}))
    (hγ : ∀ z, (γ z).val.val = z₀+(ρ:ℂ)*z) :
    ∃ e : Circle ≃ₜ {x : closedBall z₀ ρ | dist x.val z₀ = ρ},
      ∀ z, e z = γ z := by
  have hinj : Function.Injective γ := by
    intro z w heq
    have h := congrArg (fun d => d.val.val) heq
    rw [hγ,hγ] at h
    apply Subtype.ext
    exact mul_left_cancel₀ (by exact_mod_cast hρ.ne' : (ρ:ℂ) ≠ 0)
      (add_left_cancel h)
  have hsurj := actual_literal_scaled_circle_boundary_surjective z₀ ρ hρ γ hγ
  exact ⟨(Equiv.ofBijective γ ⟨hinj,hsurj⟩).toHomeomorphOfContinuousClosed
    γ.continuous γ.continuous.isClosedMap, fun z => rfl⟩

private theorem actual_literal_scaled_circle_boundary_h1_isIso
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (γ : C(Circle, {x : closedBall z₀ ρ | dist x.val z₀ = ρ}))
    (hγ : ∀ z, (γ z).val.val = z₀+(ρ:ℂ)*z) :
    IsIso ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ))) := by
  obtain ⟨e,he⟩ := actual_literal_scaled_circle_boundary_homeomorph z₀ ρ hρ γ hγ
  have heq : (TopCat.isoOfHomeo e).hom = TopCat.ofHom γ := by ext z; exact congrArg (fun d => d.val.val) (he z)
  haveI : IsIso (TopCat.ofHom γ) := by rw [← heq]; infer_instance
  infer_instance

private theorem actual_literal_complex_disc_normalized_cap_generates
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    let D := closedBall z₀ ρ;
    let B : Set D := {x | dist x.val z₀ = ρ};
    ∀ (γ : C(Circle,B)) (hγ : ∀ z, (γ z).val.val = z₀+(ρ:ℂ)*z)
      (r : relativeHomology D B 2),
      relativeConnecting D B 1 r =
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ))
            CircleFundamentalCycle.fundamentalClass →
      ∀ t : relativeHomology D B 2, ∃ n : ℤ, n • r = t := by
  dsimp only
  let D := closedBall z₀ ρ
  let B : Set D := {x | dist x.val z₀ = ρ}
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  intro γ hγ r hr t
  let f := F.map (TopCat.ofHom γ)
  haveI : IsIso f := actual_literal_scaled_circle_boundary_h1_isIso z₀ ρ hρ γ hγ
  obtain ⟨n,hn⟩ := CircleFundamentalCycle.fundamentalClass_generates
    (inv f (relativeConnecting D B 1 t))
  refine ⟨n,?_⟩
  apply actual_literal_complex_disc_normalized_cap_unique z₀ ρ hρ
  rw [map_zsmul,hr]
  change n • f CircleFundamentalCycle.fundamentalClass = relativeConnecting D B 1 t
  rw [← map_zsmul,hn]
  exact IsIso.inv_hom_id_apply f _

private theorem actual_literal_complex_disc_normalized_cap_no_integer_torsion
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    let D := closedBall z₀ ρ;
    let B : Set D := {x | dist x.val z₀ = ρ};
    ∀ (γ : C(Circle,B)) (hγ : ∀ z, (γ z).val.val = z₀+(ρ:ℂ)*z)
      (r : relativeHomology D B 2),
      relativeConnecting D B 1 r =
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ))
            CircleFundamentalCycle.fundamentalClass →
      ∀ n : ℤ, n • r = 0 → n = 0 := by
  dsimp only
  let D := closedBall z₀ ρ
  let B : Set D := {x | dist x.val z₀ = ρ}
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  intro γ hγ r hr n hn
  let f := F.map (TopCat.ofHom γ)
  haveI : IsIso f := actual_literal_scaled_circle_boundary_h1_isIso z₀ ρ hρ γ hγ
  have h := congrArg (relativeConnecting D B 1) hn
  rw [map_zsmul,hr,map_zero] at h
  have hf : n • CircleFundamentalCycle.fundamentalClass = 0 := by
    apply (ModuleCat.mono_iff_injective f).mp inferInstance
    rw [map_zsmul,map_zero]
    exact h
  have hc := congrArg CircleHomologyComputation.circleH1Iso.hom hf
  rw [map_zsmul,CircleFundamentalCycle.fundamentalClass_coordinate,map_zero] at hc
  change n * (-1:ℤ) = 0 at hc
  simpa using hc


private theorem actual_literal_normalized_disc_cap_point_local_generator
    (E : Type) [TopologicalSpace E] [T1Space E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ) (hρ : 0 < ρ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    let D := closedBall ((chartAt ℂ q) q) ρ;
    let B : Set D := {x | dist x.val ((chartAt ℂ q) q) = ρ};
    ∀ (f : C(D,E)) (hf : ∀ d, f d = (chartAt ℂ q).symm d.val)
      (γ : C(Circle,B)) (hγ : ∀ z, (γ z).val.val = (chartAt ℂ q) q+(ρ:ℂ)*z)
      (r : relativeHomology D B 2)
      (hr : relativeConnecting D B 1 r =
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ)) CircleFundamentalCycle.fundamentalClass)
      (h : ∀ x ∈ B, f x ∈ ({q}ᶜ : Set E)),
      (∀ t : relativeHomology E ({q}ᶜ) 2,
        ∃ n : ℤ, n • pairRelativeHomologyMap B ({q}ᶜ) f h 2 r = t) ∧
      (∀ n : ℤ, n • pairRelativeHomologyMap B ({q}ᶜ) f h 2 r = 0 → n = 0) := by
  dsimp only
  intro f hf γ hγ r hr h
  let m := pairRelativeHomologyMap
    {x : closedBall ((chartAt ℂ q) q) ρ | dist x.val ((chartAt ℂ q) q) = ρ}
    ({q}ᶜ) f h 2
  obtain ⟨h',hm⟩ := actual_literal_disc_boundary_chart_point_localization_isIso E q ρ hρ htarget f hf
  haveI : IsIso m := hm
  constructor
  · intro t
    obtain ⟨n,hn⟩ := actual_literal_complex_disc_normalized_cap_generates
      ((chartAt ℂ q) q) ρ hρ γ hγ r hr (inv m t)
    refine ⟨n,?_⟩
    change n • m r = t
    rw [← map_zsmul,hn]
    exact IsIso.inv_hom_id_apply m t
  · intro n hn
    apply actual_literal_complex_disc_normalized_cap_no_integer_torsion
      ((chartAt ℂ q) q) ρ hρ γ hγ r hr n
    apply (ModuleCat.mono_iff_injective m).mp inferInstance
    rw [map_zsmul,map_zero]
    exact hn

-- Independent exact finite-excision source request, explicitly unproved.
private theorem actual_relativeHomology_univ_isZero
    (X : Type) [TopologicalSpace X] (n : ℕ) :
    IsZero (relativeHomology X Set.univ n) := by
  have hi : pairInclusion X Set.univ =
      (TopCat.isoOfHomeo (Homeomorph.Set.univ X)).hom := by
    ext x
    rfl
  haveI : IsIso (pairInclusion X Set.univ) := by
    rw [hi]
    infer_instance
  haveI : Epi (((AlgebraicTopology.singularChainComplexFunctor
      (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      (pairInclusion X Set.univ)) := inferInstance
  have hz : IsZero (relativeSingularChains X Set.univ) :=
    isZero_cokernel_of_epi _
  exact Functor.map_isZero
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n) hz
#print axioms actual_relativeHomology_univ_isZero
private theorem actual_literal_chart_closedBall_image_isClosed
    (E : Type) [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    IsClosed ((chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) ρ) := by
  exact ((isCompact_closedBall ((chartAt ℂ q) q) ρ).image_of_continuousOn
    ((chartAt ℂ q).symm.continuousOn.mono htarget)).isClosed
#print axioms actual_literal_chart_closedBall_image_isClosed
private theorem actual_literal_chart_ball_image_isOpen
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    IsOpen ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) ρ) := by
  exact (chartAt ℂ q).isOpen_image_symm_of_subset_target isOpen_ball
    (ball_subset_closedBall.trans htarget)
#print axioms actual_literal_chart_ball_image_isOpen

private theorem actual_literal_chart_disc_exterior_closed_cover
    (E : Type) [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    let K := (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) ρ;
    let P := ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) ρ)ᶜ;
    IsClosed K ∧ IsClosed P ∧ K ∪ P = Set.univ := by
  dsimp only
  let K := (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) ρ
  let P := ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) ρ)ᶜ
  refine ⟨actual_literal_chart_closedBall_image_isClosed E q ρ htarget,
    (actual_literal_chart_ball_image_isOpen E q ρ htarget).isClosed_compl, ?_⟩
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ P
  · exact Or.inr hx
  · apply Or.inl
    exact Set.image_mono ball_subset_closedBall (not_not.mp hx)
#print axioms actual_literal_chart_disc_exterior_closed_cover

private theorem actual_literal_chart_closed_disc_homeomorph_image
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    ∃ e : closedBall ((chartAt ℂ q) q) ρ ≃ₜ
        ((chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) ρ),
      (∀ d, (e d).val = (chartAt ℂ q).symm d.val) ∧
      (∀ y, (e.symm y).val = (chartAt ℂ q) y.val) := by
  let cq := chartAt ℂ q
  let D := closedBall (cq q) ρ
  let K := cq.symm '' D
  have hsource (y : K) : y.val ∈ cq.source := by
    obtain ⟨z,hz,he⟩ := y.property
    rw [← he]
    exact cq.map_target (htarget hz)
  have hD (y : K) : cq y.val ∈ D := by
    obtain ⟨z,hz,he⟩ := y.property
    rw [← he,cq.right_inv (htarget hz)]
    exact hz
  let e : D ≃ₜ K := {
    toFun := fun d => ⟨cq.symm d.val, ⟨d.val,d.property,rfl⟩⟩
    invFun := fun y => ⟨cq y.val, hD y⟩
    left_inv := by
      intro d
      apply Subtype.ext
      exact cq.right_inv (htarget d.property)
    right_inv := by
      intro y
      apply Subtype.ext
      exact cq.left_inv (hsource y)
    continuous_toFun := (cq.symm.continuousOn.comp_continuous continuous_subtype_val
      (fun d => htarget d.property)).subtype_mk _
    continuous_invFun := (cq.continuousOn.comp_continuous continuous_subtype_val
      hsource).subtype_mk hD }
  exact ⟨e,fun _ => rfl,fun _ => rfl⟩
#print axioms actual_literal_chart_closed_disc_homeomorph_image

private theorem actual_literal_chart_puncture_local_radial
    (E : Type) [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ) (hρ : 0 < ρ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    let K := (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) ρ;
    let P := ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) ρ)ᶜ;
    let Q : Set E := {q}ᶜ;
    ∃ loc : C(unitInterval × {x : Q | x.val ∈ K}, Q),
      (∀ x : {x : Q | x.val ∈ K}, loc (0,x) = x.val) ∧
      (∀ x : {x : Q | x.val ∈ K}, (loc (1,x)).val ∈ P) ∧
      (∀ (t : unitInterval) (x : {x : Q | x.val ∈ K}), x.val.val ∈ P →
        loc (t,x) = x.val) := by
  dsimp only
  let cq := chartAt ℂ q
  let z₀ := cq q
  let D := closedBall z₀ ρ
  let K := cq.symm '' D
  let P := (cq.symm '' ball z₀ ρ)ᶜ
  let Q : Set E := {q}ᶜ
  let S : Set Q := {x | x.val ∈ K}
  obtain ⟨e,heval,heinv⟩ := actual_literal_chart_closed_disc_homeomorph_image
    E q ρ htarget
  let V : Set D := {d | d.val ≠ z₀}
  let B : Set V := {d | dist d.val.val z₀ = ρ}
  obtain ⟨r,hr,⟨H⟩⟩ :=
    actual_literal_punctured_disc_boundary_fixed_deformation z₀ ρ hρ
  have hsource (x : S) : x.val.val ∈ cq.source := by
    obtain ⟨z,hz,he⟩ := x.property
    rw [← he]
    exact cq.map_target (htarget hz)
  have hjne (x : S) : (e.symm ⟨x.val.val,x.property⟩).val ≠ z₀ := by
    intro he
    apply x.val.property
    have hxchart : cq x.val.val = z₀ := by
      rw [← heinv ⟨x.val.val,x.property⟩]
      exact he
    exact cq.injOn (hsource x) (mem_chart_source ℂ q) hxchart
  let j : C(S,V) := ⟨fun x => ⟨e.symm ⟨x.val.val,x.property⟩,hjne x⟩, by
    apply Continuous.subtype_mk
    apply e.symm.continuous.comp
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun x => x.property)⟩
  have hgne (d : V) : (e d.val).val ≠ q := by
    intro he
    have hh := congrArg cq he
    rw [heval,cq.right_inv (htarget d.val.property)] at hh
    exact d.property hh
  let g : C(V,Q) := ⟨fun d => ⟨(e d.val).val,hgne d⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (e.continuous.comp continuous_subtype_val)⟩
  have hgj (x : S) : g (j x) = x.val := by
    apply Subtype.ext
    change (e (e.symm ⟨x.val.val,x.property⟩)).val = x.val.val
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x.val.val,x.property⟩)
  let loc : C(unitInterval × S,Q) := ⟨fun tx => g (H (tx.1,j tx.2)),
    g.continuous.comp (H.continuous.comp
      (continuous_fst.prodMk (j.continuous.comp continuous_snd)))⟩
  refine ⟨loc,?_,?_,?_⟩
  · intro x
    change g (H (0,j x)) = x.val
    rw [H.apply_zero]
    exact hgj x
  · intro x
    change (g (H (1,j x))).val ∈ P
    rw [H.apply_one]
    intro hy
    obtain ⟨w,hw,hew⟩ := hy
    have htargetw : w ∈ cq.target := htarget (ball_subset_closedBall hw)
    have hzw : w = (r (j x)).val.val := by
      have hh := congrArg cq hew
      change cq (cq.symm w) = cq ((e (r (j x)).val).val) at hh
      rw [heval,cq.right_inv htargetw,
        cq.right_inv (htarget (r (j x)).val.property)] at hh
      exact hh
    have hlt : dist (r (j x)).val.val z₀ < ρ := by
      rw [← hzw]
      exact hw
    rw [hr (j x)] at hlt
    exact (lt_irrefl ρ) hlt
  · intro t x hxP
    have hboundary : j x ∈ B := by
      have hle : dist (j x).val.val z₀ ≤ ρ := (j x).val.property
      have hnot : ¬ dist (j x).val.val z₀ < ρ := by
        intro hlt
        apply hxP
        refine ⟨(j x).val.val,hlt,?_⟩
        have hh := congrArg Subtype.val (e.apply_symm_apply ⟨x.val.val,x.property⟩)
        change cq.symm (e.symm ⟨x.val.val,x.property⟩).val = x.val.val
        simpa only [heval] using hh
      exact le_antisymm hle (le_of_not_gt hnot)
    change g (H (t,j x)) = x.val
    rw [H.eq_fst t hboundary]
    exact hgj x
#print axioms actual_literal_chart_puncture_local_radial

private theorem actual_closed_cover_relative_retraction
    (X : Type) [TopologicalSpace X] (K P Q : Set X)
    (hK : IsClosed K) (hP : IsClosed P) (hcover : K ∪ P = Set.univ)
    (hPQ : P ⊆ Q)
    (loc : C(unitInterval × {x : Q | x.val ∈ K}, Q))
    (hzero : ∀ x : {x : Q | x.val ∈ K}, loc (0,x) = x.val)
    (hone : ∀ x : {x : Q | x.val ∈ K}, (loc (1,x)).val ∈ P)
    (hfix : ∀ (t : unitInterval) (x : {x : Q | x.val ∈ K}), x.val.val ∈ P →
      loc (t,x) = x.val) :
    ∃ r : C(Q,P),
      r.comp (ContinuousMap.inclusion hPQ) = ContinuousMap.id P ∧
      Nonempty (ContinuousMap.Homotopy (ContinuousMap.id Q)
        ((ContinuousMap.inclusion hPQ).comp r)) := by
  classical
  let S : Set Q := {x | x.val ∈ K}
  let T : Set Q := {x | x.val ∈ P}
  have hS : IsClosed S := hK.preimage continuous_subtype_val
  have hT : IsClosed T := hP.preimage continuous_subtype_val
  have hST : S ∪ T = Set.univ := by
    ext x
    change (x.val ∈ K ∨ x.val ∈ P) ↔ True
    simp only [iff_true]
    have hh : x.val ∈ K ∪ P := by rw [hcover]; trivial
    simpa only [mem_union] using hh
  let F : unitInterval × Q → Q := fun tx =>
    if hx : tx.2 ∈ S then loc (tx.1, ⟨tx.2,hx⟩) else tx.2
  have hFs : ContinuousOn F (Prod.snd ⁻¹' S) := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun tx : (Prod.snd ⁻¹' S : Set (unitInterval × Q)) => F tx.val)
    let k : (Prod.snd ⁻¹' S : Set (unitInterval × Q)) →
        unitInterval × S := fun tx => (tx.val.1, ⟨tx.val.2,tx.property⟩)
    have hk : Continuous k := by
      apply Continuous.prodMk
      · fun_prop
      · exact (continuous_snd.comp continuous_subtype_val).subtype_mk
          (fun tx => tx.property)
    have he : (fun tx : (Prod.snd ⁻¹' S : Set (unitInterval × Q)) => F tx.val) =
        loc ∘ k := by
      funext tx
      dsimp only [F, k, Function.comp_apply]
      rw [dif_pos (show tx.val.2 ∈ S from tx.property)]
    rw [he]
    exact loc.continuous.comp hk
  have hFt : ContinuousOn F (Prod.snd ⁻¹' T) := by
    have he : Set.EqOn F Prod.snd (Prod.snd ⁻¹' T) := by
      intro tx htx
      dsimp only [F]
      split_ifs with hx
      · exact hfix tx.1 ⟨tx.2,hx⟩ htx
      · rfl
    exact continuous_snd.continuousOn.congr he
  have hFc : Continuous F := by
    rw [← continuousOn_univ]
    have hcover' : ((Prod.snd : unitInterval × Q → Q) ⁻¹' S) ∪
        ((Prod.snd : unitInterval × Q → Q) ⁻¹' T) = Set.univ := by
      rw [← preimage_union, hST, preimage_univ]
    rw [← hcover']
    exact hFs.union_of_isClosed hFt
      (hS.preimage continuous_snd) (hT.preimage continuous_snd)
  have hFzero (x : Q) : F (0,x) = x := by
    dsimp only [F]
    split_ifs with hx
    · exact hzero ⟨x,hx⟩
    · rfl
  have hFone (x : Q) : (F (1,x)).val ∈ P := by
    dsimp only [F]
    split_ifs with hx
    · exact hone ⟨x,hx⟩
    · have hmem : x ∈ S ∪ T := hST.symm ▸ mem_univ x
      exact hmem.resolve_left hx
  let r : C(Q,P) := ⟨fun x => ⟨(F (1,x)).val,hFone x⟩,
    (continuous_subtype_val.comp (hFc.comp (continuous_const.prodMk continuous_id))).subtype_mk _⟩
  have hri : r.comp (ContinuousMap.inclusion hPQ) = ContinuousMap.id P := by
    ext x
    change (F (1,⟨x.val,hPQ x.property⟩)).val = x.val
    dsimp only [F]
    split_ifs with hx
    · exact congrArg Subtype.val (hfix 1 ⟨⟨x.val,hPQ x.property⟩,hx⟩ x.property)
    · rfl
  let H : ContinuousMap.Homotopy (ContinuousMap.id Q)
      ((ContinuousMap.inclusion hPQ).comp r) := {
    toFun := F
    continuous_toFun := hFc
    map_zero_left := hFzero
    map_one_left := by
      intro x
      rfl }
  exact ⟨r,hri,⟨H⟩⟩
#print axioms actual_closed_cover_relative_retraction

private theorem actual_pair_relative_injective_of_subspace_maps
    (E : Type) [TopologicalSpace E] (P Q : Set E)
    (hPQ : P ⊆ Q)
    (h₁ : Function.Injective
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map
        (pairMapOnSubspace P Q (ContinuousMap.id E) (fun x hx => hPQ hx)))))
    (h₂ : Function.Surjective
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).map
        (pairMapOnSubspace P Q (ContinuousMap.id E) (fun x hx => hPQ hx))))) :
    Function.Injective
      (pairRelativeHomologyMap P Q (ContinuousMap.id E)
        (fun x hx => hPQ hx) 2) := by
  let f₁ := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map
    (pairMapOnSubspace P Q (ContinuousMap.id E) (fun x hx => hPQ hx))
  let f₂ := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).map
    (pairMapOnSubspace P Q (ContinuousMap.id E) (fun x hx => hPQ hx))
  let m := pairRelativeHomologyMap P Q (ContinuousMap.id E)
    (fun x hx => hPQ hx) 2
  have hδ := relativeConnecting_natural P Q (ContinuousMap.id E)
    (fun x hx => hPQ hx) 1
  have hι := pairHomologyInclusion_commutes P Q (ContinuousMap.id E)
    (fun x hx => hPQ hx) 2
  have hη := pairRelativeHomologyMap_commutes P Q (ContinuousMap.id E)
    (fun x hx => hPQ hx) 2
  suffices hker : ∀ a : relativeHomology E P 2, m a = 0 → a = 0 by
    intro a b hab
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hab, sub_self]
  intro a ha
  have hconn : relativeConnecting E P 1 a = 0 := by
    apply h₁
    have he := congrArg (fun f => f a) hδ
    change f₁ (relativeConnecting E P 1 a) =
      relativeConnecting E Q 1 (m a) at he
    rw [ha, map_zero] at he
    simpa using he
  obtain ⟨_, hexP⟩ := pairHomology_exact_at_relative E P 1
  obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff _).mp hexP a hconn
  change homologyToRelative E P 2 t = a at ht
  have htQ : homologyToRelative E Q 2 t = 0 := by
    have hη' : homologyToRelative E P 2 ≫ m =
        homologyToRelative E Q 2 := by simpa using hη
    have he := congrArg (fun f => f t) hη'
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at he
    rw [ht, ha] at he
    exact he.symm
  obtain ⟨_, hexQ⟩ := pairHomology_exact_at_absolute E Q 2
  obtain ⟨u, hu⟩ := (ShortComplex.moduleCat_exact_iff _).mp hexQ t htQ
  change homologyInclusion E Q 2 u = t at hu
  obtain ⟨v, hv⟩ := h₂ u
  have htP : homologyInclusion E P 2 v = t := by
    have hι' : homologyInclusion E P 2 =
        f₂ ≫ homologyInclusion E Q 2 := by simpa using hι
    have he := congrArg (fun f => f v) hι'
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at he
    rw [hv, hu] at he
    exact he
  obtain ⟨hzP, _⟩ := pairHomology_exact_at_absolute E P 2
  have ha0 : a = 0 := by
    rw [← ht, ← htP]
    exact congrArg (fun f => f v) hzP
  exact ha0
#print axioms actual_pair_relative_injective_of_subspace_maps

private theorem actual_literal_chart_disc_exterior_point_detection
    (E : Type) [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ) (hρ : 0 < ρ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target) :
    let P : Set E :=
      ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) ρ)ᶜ;
    ∃ havoid : ∀ x ∈ P, x ≠ q,
      Function.Injective
        (pairRelativeHomologyMap P ({q}ᶜ)
          (ContinuousMap.id E) havoid 2) := by
  dsimp only
  let P : Set E := ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) ρ)ᶜ
  have hq : q ∈ ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) ρ) := by
    refine ⟨(chartAt ℂ q) q, mem_ball_self hρ, ?_⟩
    exact (chartAt ℂ q).left_inv (mem_chart_source ℂ q)
  let havoid : ∀ x ∈ P, x ≠ q := by
    intro x hx he
    exact hx (he ▸ hq)
  refine ⟨havoid, ?_⟩
  let K := (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) ρ
  let Q : Set E := {q}ᶜ
  obtain ⟨hK,hP,hcover⟩ :=
    actual_literal_chart_disc_exterior_closed_cover E q ρ htarget
  obtain ⟨loc,hzero,hone,hfix⟩ :=
    actual_literal_chart_puncture_local_radial E q ρ hρ htarget
  let i : C(P,Q) := ContinuousMap.inclusion havoid
  obtain ⟨r,hri,⟨H⟩⟩ :=
    actual_closed_cover_relative_retraction E K P Q hK hP hcover havoid
      loc hzero hone hfix
  have hmap (n : ℕ) :
      IsIso ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map
        (pairMapOnSubspace P Q (ContinuousMap.id E) havoid))) := by
    have heq : pairMapOnSubspace P Q (ContinuousMap.id E) havoid =
        TopCat.ofHom i := by ext x; rfl
    rw [heq]
    have hPht : (r.comp i).Homotopic (ContinuousMap.id P) := by
      rw [hri]
    have hQht : (i.comp r).Homotopic (ContinuousMap.id Q) := ⟨H.symm⟩
    let e := singularHomologyIsoOfHomotopyInverse (ModuleCat.of ℤ ℤ) n i r
      hPht hQht
    exact e.isIso_hom
  apply actual_pair_relative_injective_of_subspace_maps E P Q havoid
  · haveI := hmap 1
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  · haveI := hmap 2
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
#print axioms actual_literal_chart_disc_exterior_point_detection

private theorem actual_finite_literal_chart_closed_cover
    (E : Type) [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    (Z : Finset E) (ρ : Z → ℝ)
    (htarget : ∀ q : Z, closedBall ((chartAt ℂ q.val) q.val) (ρ q) ⊆
      (chartAt ℂ q.val).target) :
    let K : Set E := ⋃ q : Z,
      (chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρ q);
    let P : Set E := (⋃ q : Z,
      (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρ q))ᶜ;
    IsClosed K ∧ IsClosed P ∧ K ∪ P = Set.univ := by
  dsimp only
  have hK : IsClosed (⋃ q : Z,
      (chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρ q)) :=
    isClosed_iUnion_of_finite (fun q =>
      actual_literal_chart_closedBall_image_isClosed E q.val (ρ q) (htarget q))
  have hP : IsClosed (⋃ q : Z,
      (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρ q))ᶜ := by
    apply IsOpen.isClosed_compl
    exact isOpen_iUnion (fun q =>
      actual_literal_chart_ball_image_isOpen E q.val (ρ q) (htarget q))
  refine ⟨hK,hP,?_⟩
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ (⋃ q : Z,
      (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρ q))ᶜ
  · exact Or.inr hx
  · apply Or.inl
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp (not_not.mp hx)
    exact Set.mem_iUnion.mpr ⟨q, Set.image_mono ball_subset_closedBall hq⟩
#print axioms actual_finite_literal_chart_closed_cover

private theorem actual_singular_simplex_sigma_lift
    (ι : Type) (K : ι → Type) [∀ i, TopologicalSpace (K i)] (n : ℕ)
    (f : C(StdSimplex ℝ (Fin (n + 1)), Sigma K)) :
    ∃ i : ι, ∃ g : C(StdSimplex ℝ (Fin (n + 1)), K i),
      ∀ t, f t = ⟨i, g t⟩ := by
  obtain ⟨i,g,hg,he⟩ := Continuous.exists_lift_sigma f.continuous
  exact ⟨i,⟨g,hg⟩,fun t => congrFun he t⟩
#print axioms actual_singular_simplex_sigma_lift

private theorem actual_finite_disjoint_closed_piece_isClopen
    (E : Type) [TopologicalSpace E]
    (Z : Finset E) (K : Z → Set E)
    (hK : ∀ q, IsClosed (K q))
    (hd : Set.univ.Pairwise (fun q r : Z => Disjoint (K q) (K r)))
    (q : Z) :
    IsClopen {x : (⋃ p : Z, K p) | x.val ∈ K q} := by
  let T : Set E := ⋃ p : Z, K p
  let S : Set T := {x | x.val ∈ K q}
  have hSclosed : IsClosed S := (hK q).preimage continuous_subtype_val
  have hScompl : Sᶜ = {x : T | x.val ∈ ⋃ p : {p : Z // p ≠ q}, K p.val} := by
    ext x
    constructor
    · intro hx
      have hxT : x.val ∈ ⋃ p : Z, K p := x.property
      obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hxT
      have hpq : p ≠ q := by
        intro he
        subst p
        exact hx hp
      exact Set.mem_iUnion.mpr ⟨⟨p,hpq⟩,hp⟩
    · intro hx hq
      obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hx
      exact (Set.disjoint_left.mp (hd (Set.mem_univ _) (Set.mem_univ _) p.property.symm)) hq hp
  have hother : IsClosed (⋃ p : {p : Z // p ≠ q}, K p.val) :=
    isClosed_iUnion_of_finite (fun p => hK p.val)
  have hScomplClosed : IsClosed Sᶜ := by
    rw [hScompl]
    exact hother.preimage continuous_subtype_val
  exact ⟨hSclosed, by simpa only [compl_compl] using hScomplClosed.isOpen_compl⟩
#print axioms actual_finite_disjoint_closed_piece_isClopen

private theorem actual_finite_compact_pairwise_open_neighborhoods
    (E ι : Type) [TopologicalSpace E] [T2Space E] [RegularSpace E]
    (s : Finset ι) (K : ι → Set E)
    (hcompact : ∀ i, IsCompact (K i))
    (hdisjoint : (s : Set ι).Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ V : ι → Set E,
      (∀ i ∈ s, IsOpen (V i) ∧ K i ⊆ V i) ∧
      (s : Set ι).Pairwise (fun i j => Disjoint (V i) (V j)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨fun _ => ∅, by simp, by simp⟩
  | @insert a t ha ih =>
      have htpair : (t : Set ι).Pairwise (fun i j => Disjoint (K i) (K j)) := by
        intro i hi j hj hij
        exact hdisjoint (Finset.mem_insert_of_mem hi)
          (Finset.mem_insert_of_mem hj) hij
      obtain ⟨V,hV,hVpair⟩ := ih htpair
      let R : Set E := ⋃ b : t, K b.val
      have hRclosed : IsClosed R :=
        isClosed_iUnion_of_finite (fun b => (hcompact b.val).isClosed)
      have hKR : Disjoint (K a) R := by
        apply Set.disjoint_left.mpr
        intro x hx hxR
        obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hxR
        exact (Set.disjoint_left.mp
          (hdisjoint (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem b.property)
            (by intro he; exact ha (he ▸ b.property)))) hx hb
      have hsep : SeparatedNhds (K a) R :=
        SeparatedNhds.of_isCompact_isClosed (hcompact a) hRclosed hKR
      change ∃ A B : Set E, IsOpen A ∧ IsOpen B ∧ K a ⊆ A ∧ R ⊆ B ∧
        Disjoint A B at hsep
      obtain ⟨A,B,hAopen,hBopen,hKA,hRB,hAB⟩ := hsep
      let W : ι → Set E := fun i => if i = a then A else V i ∩ B
      refine ⟨W, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hit
        · simp only [W, ↓reduceIte]
          exact ⟨hAopen,hKA⟩
        · have hia : i ≠ a := by intro he; subst i; exact ha hit
          simp only [W, if_neg hia]
          exact ⟨(hV i hit).1.inter hBopen,
            fun x hx => ⟨(hV i hit).2 hx, hRB (Set.mem_iUnion.mpr ⟨⟨i,hit⟩,hx⟩)⟩⟩
      · intro i hi j hj hij
        rcases Finset.mem_insert.mp hi with rfl | hit
        · have hjt : j ∈ t := (Finset.mem_insert.mp hj).resolve_left hij.symm
          simpa only [W, if_pos rfl, if_neg hij.symm] using
            hAB.mono_right Set.inter_subset_right
        · rcases Finset.mem_insert.mp hj with rfl | hjt
          · simpa only [W, if_pos rfl, if_neg hij] using
              hAB.symm.mono_left Set.inter_subset_right
          · have hia : i ≠ a := by intro he; exact ha (he ▸ hit)
            have hja : j ≠ a := by intro he; exact ha (he ▸ hjt)
            simpa only [W, if_neg hia, if_neg hja] using
              (hVpair hit hjt hij).mono Set.inter_subset_left Set.inter_subset_left
#print axioms actual_finite_compact_pairwise_open_neighborhoods

private noncomputable def actual_finite_disjoint_closed_union_homeomorph
    (E : Type) [TopologicalSpace E]
    (Z : Finset E) (K : Z → Set E)
    (hK : ∀ q, IsClosed (K q))
    (hd : Set.univ.Pairwise (fun q r : Z => Disjoint (K q) (K r))) :
    (Σ q : Z, K q) ≃ₜ (⋃ q : Z, K q) := by
  let T : Set E := ⋃ q : Z, K q
  let f : (Σ q : Z, K q) → T := fun x =>
    ⟨x.2.val, Set.mem_iUnion.mpr ⟨x.1, x.2.property⟩⟩
  have hfcont : Continuous f := by
    apply continuous_sigma
    intro q
    exact (continuous_subtype_val.subtype_mk fun x =>
      Set.mem_iUnion.mpr ⟨q, x.property⟩)
  have hfinj : Function.Injective f := by
    intro x y hxy
    have hv : x.2.val = y.2.val := congrArg Subtype.val hxy
    have hq : x.1 = y.1 := by
      by_contra hne
      exact (Set.disjoint_left.mp
        (hd (Set.mem_univ _) (Set.mem_univ _) hne)) x.2.property
          (hv ▸ y.2.property)
    cases x with
    | mk i xi =>
      cases y with
      | mk j yj =>
        cases hq
        congr
        exact Subtype.ext hv
  have hfsurj : Function.Surjective f := by
    intro x
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp x.property
    exact ⟨⟨q, ⟨x.val,hq⟩⟩, Subtype.ext rfl⟩
  have hfclosed : IsClosedMap f := by
    intro S hS
    have hSq (q : Z) : IsClosed ((fun x : K q => (⟨q,x⟩ : Σ p : Z, K p)) ⁻¹' S) := by
      simpa only using (isClosed_sigma_iff.mp hS q)
    have hjclosed (q : Z) : IsClosedMap
        (fun x : K q => (⟨x.val, Set.mem_iUnion.mpr ⟨q,x.property⟩⟩ : T)) :=
      (hK q).isClosedMap_inclusion (Set.subset_iUnion K q)
    have heq : f '' S = ⋃ q : Z,
        (fun x : K q => (⟨x.val, Set.mem_iUnion.mpr ⟨q,x.property⟩⟩ : T)) ''
          ((fun x : K q => (⟨q,x⟩ : Σ p : Z, K p)) ⁻¹' S) := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact Set.mem_iUnion.mpr ⟨y.1, ⟨y.2,hy,rfl⟩⟩
      · intro hx
        obtain ⟨q,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
        exact ⟨⟨q,y⟩,hy,rfl⟩
    rw [heq]
    exact isClosed_iUnion_of_finite (fun q => hjclosed q _ (hSq q))
  exact (Equiv.ofBijective f ⟨hfinj,hfsurj⟩).toHomeomorphOfContinuousClosed
    hfcont hfclosed
#print axioms actual_finite_disjoint_closed_union_homeomorph

private noncomputable def actual_finite_literal_chart_closed_discs_homeomorph
    (E : Type) [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    (Z : Finset E) (ρ : Z → ℝ)
    (htarget : ∀ q : Z, closedBall ((chartAt ℂ q.val) q.val) (ρ q) ⊆
      (chartAt ℂ q.val).target)
    (hdisjoint : Set.univ.Pairwise (fun q r : Z => Disjoint
      ((chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρ q))
      ((chartAt ℂ r.val).symm '' closedBall ((chartAt ℂ r.val) r.val) (ρ r)))) :
    (Σ q : Z,
      (chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρ q)) ≃ₜ
    (⋃ q : Z,
      (chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρ q)) :=
  actual_finite_disjoint_closed_union_homeomorph E Z _
    (fun q => actual_literal_chart_closedBall_image_isClosed E q.val (ρ q) (htarget q))
    hdisjoint
#print axioms actual_finite_literal_chart_closed_discs_homeomorph

private theorem actual_finite_literal_chart_excision_collar
    (E : Type) [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    (Z : Finset E) (ρ : Z → ℝ)
    (htarget : ∀ q : Z, closedBall ((chartAt ℂ q.val) q.val) (ρ q) ⊆
      (chartAt ℂ q.val).target)
    (hdisjoint : Set.univ.Pairwise (fun q r : Z => Disjoint
      ((chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρ q))
      ((chartAt ℂ r.val).symm '' closedBall ((chartAt ℂ r.val) r.val) (ρ r)))) :
    let K : Z → Set E := fun q =>
      (chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρ q);
    let P : Set E := (⋃ q : Z,
      (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρ q))ᶜ;
    ∃ V : Z → Set E,
      (∀ q, IsOpen (V q) ∧ K q ⊆ V q) ∧
      Set.univ.Pairwise (fun q r : Z => Disjoint (V q) (V r)) ∧
      closure (⋃ q : Z, V q)ᶜ ⊆ interior P := by
  classical
  dsimp only
  let K : Z → Set E := fun q =>
    (chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρ q)
  let P : Set E := (⋃ q : Z,
    (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρ q))ᶜ
  letI : LocallyCompactSpace E := ChartedSpace.locallyCompactSpace ℂ E
  haveI : RegularSpace E := inferInstance
  have hcompact (q : Z) : IsCompact (K q) :=
    (isCompact_closedBall ((chartAt ℂ q.val) q.val) (ρ q)).image_of_continuousOn
      ((chartAt ℂ q.val).symm.continuousOn.mono (htarget q))
  obtain ⟨V,hV,hVdisjoint⟩ := actual_finite_compact_pairwise_open_neighborhoods
    E Z Finset.univ K hcompact (by simpa only [Finset.coe_univ] using hdisjoint)
  have hV' (q : Z) : IsOpen (V q) ∧ K q ⊆ V q := hV q (Finset.mem_univ q)
  have hVdisjoint' : Set.univ.Pairwise (fun q r : Z => Disjoint (V q) (V r)) := by
    simpa only [Finset.coe_univ] using hVdisjoint
  refine ⟨V,hV',hVdisjoint',?_⟩
  let N : Set E := ⋃ q : Z, V q
  have hNopen : IsOpen N := isOpen_iUnion (fun q => (hV' q).1)
  have hKN : (⋃ q : Z, K q) ⊆ N := by
    intro x hx
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨q,(hV' q).2 hq⟩
  have hKclosed : IsClosed (⋃ q : Z, K q) :=
    isClosed_iUnion_of_finite (fun q => (hcompact q).isClosed)
  have hKcP : (⋃ q : Z, K q)ᶜ ⊆ P := by
    intro x hxK hxB
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hxB
    exact hxK (Set.mem_iUnion.mpr ⟨q, Set.image_mono ball_subset_closedBall hq⟩)
  have hKcInt : (⋃ q : Z, K q)ᶜ ⊆ interior P :=
    interior_maximal hKcP hKclosed.isOpen_compl
  have hU : closure Nᶜ = Nᶜ := hNopen.isClosed_compl.closure_eq
  change closure Nᶜ ⊆ interior P
  rw [hU]
  exact (Set.compl_subset_compl.mpr hKN).trans hKcInt
#print axioms actual_finite_literal_chart_excision_collar

private noncomputable def actual_disjoint_open_union_homeomorph
    (E ι : Type) [TopologicalSpace E]
    (V : ι → Set E) (hV : ∀ i, IsOpen (V i))
    (hd : Set.univ.Pairwise (fun i j : ι => Disjoint (V i) (V j))) :
    (Σ i : ι, V i) ≃ₜ (⋃ i, V i) := by
  let N : Set E := ⋃ i, V i
  let f : (Σ i, V i) → N := fun x =>
    ⟨x.2.val, Set.mem_iUnion.mpr ⟨x.1, x.2.property⟩⟩
  have hfcont : Continuous f := by
    apply continuous_sigma
    intro i
    exact continuous_subtype_val.subtype_mk (fun x =>
      Set.mem_iUnion.mpr ⟨i,x.property⟩)
  have hfinj : Function.Injective f := by
    intro x y hxy
    have hv : x.2.val = y.2.val := congrArg Subtype.val hxy
    have hi : x.1 = y.1 := by
      by_contra hne
      exact (Set.disjoint_left.mp
        (hd (Set.mem_univ _) (Set.mem_univ _) hne)) x.2.property
          (hv ▸ y.2.property)
    cases x with
    | mk i xi =>
      cases y with
      | mk j yj =>
        cases hi
        congr
        exact Subtype.ext hv
  have hfsurj : Function.Surjective f := by
    intro x
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp x.property
    exact ⟨⟨i, ⟨x.val,hi⟩⟩, Subtype.ext rfl⟩
  have hfopen : IsOpenMap f := by
    intro S hS
    have hSi (i : ι) : IsOpen ((fun x : V i => (⟨i,x⟩ : Σ j : ι, V j)) ⁻¹' S) :=
      isOpen_sigma_iff.mp hS i
    have hiopen (i : ι) : IsOpenMap
        (fun x : V i => (⟨x.val, Set.mem_iUnion.mpr ⟨i,x.property⟩⟩ : N)) :=
      (hV i).isOpenMap_inclusion (Set.subset_iUnion V i)
    have heq : f '' S = ⋃ i : ι,
        (fun x : V i => (⟨x.val, Set.mem_iUnion.mpr ⟨i,x.property⟩⟩ : N)) ''
          ((fun x : V i => (⟨i,x⟩ : Σ j : ι, V j)) ⁻¹' S) := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact Set.mem_iUnion.mpr ⟨y.1, ⟨y.2,hy,rfl⟩⟩
      · intro hx
        obtain ⟨i,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
        exact ⟨⟨i,y⟩,hy,rfl⟩
    rw [heq]
    exact isOpen_iUnion (fun i => hiopen i _ (hSi i))
  exact (Equiv.ofBijective f ⟨hfinj,hfsurj⟩).toHomeomorphOfContinuousOpen
    hfcont hfopen
#print axioms actual_disjoint_open_union_homeomorph

private noncomputable def actual_singular_simplex_sigma_equiv
    (ι : Type) (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (n : ℕ) :
    (TopCat.toSSet.obj (TopCat.of (Σ i, K i))).obj
      (Opposite.op (SimplexCategory.mk n)) ≃
      (Σ i, (TopCat.toSSet.obj (TopCat.of (K i))).obj
        (Opposite.op (SimplexCategory.mk n))) :=
  (TopCat.toSSetObjEquiv (TopCat.of (Σ i, K i))
    (Opposite.op (SimplexCategory.mk n))).trans
    ((ContinuousMap.sigmaCodHomeomorph
      (StdSimplex ℝ (Fin (n + 1))) K).toEquiv.trans
      (Equiv.sigmaCongrRight fun i =>
        (TopCat.toSSetObjEquiv (TopCat.of (K i))
          (Opposite.op (SimplexCategory.mk n))).symm))
#print axioms actual_singular_simplex_sigma_equiv

private noncomputable def actual_singular_sigma_chains_equiv
    (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of (Σ i, K i))).obj
      (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) ≃ₗ[ℤ]
      (∀ i, (TopCat.toSSet.obj (TopCat.of (K i))).obj
        (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :=
  (Finsupp.domLCongr (R := ℤ) (M := ℤ)
    (actual_singular_simplex_sigma_equiv ι K n)).trans
    (Finsupp.sigmaFinsuppLEquivPiFinsupp ℤ)
#print axioms actual_singular_sigma_chains_equiv

private theorem actual_singular_simplex_sigma_equiv_face
    (ι : Type) (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (n : ℕ) (j : Fin (n + 2))
    (x : (TopCat.toSSet.obj (TopCat.of (Σ i, K i))).obj
      (Opposite.op (SimplexCategory.mk (n + 1)))) :
    (actual_singular_simplex_sigma_equiv ι K n)
      ((TopCat.toSSet.obj (TopCat.of (Σ i, K i))).δ j x) =
      ⟨(actual_singular_simplex_sigma_equiv ι K (n + 1) x).1,
        (TopCat.toSSet.obj
          (TopCat.of (K (actual_singular_simplex_sigma_equiv ι K (n + 1) x).1))).δ j
          (actual_singular_simplex_sigma_equiv ι K (n + 1) x).2⟩ := by
  apply (actual_singular_simplex_sigma_equiv ι K n).symm.injective
  simp only [Equiv.symm_apply_apply]
  apply (TopCat.toSSetObjEquiv (TopCat.of (Σ i, K i))
    (Opposite.op (SimplexCategory.mk n))).injective
  let e := actual_singular_simplex_sigma_equiv ι K (n + 1)
  let y := e x
  have hx : x = e.symm y := (e.symm_apply_apply x).symm
  rw [hx]
  have hy : actual_singular_simplex_sigma_equiv ι K (n + 1) (e.symm y) = y :=
    e.apply_symm_apply y
  rw [hy]
  obtain ⟨i,g⟩ := y
  apply ContinuousMap.ext
  intro t
  simp only [TopCat.toSSetObjEquiv_δ_apply]
  rfl
#print axioms actual_singular_simplex_sigma_equiv_face

private theorem actual_singular_sigma_chains_equiv_apply
    (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of (Σ i, K i))).obj
      (Opposite.op (SimplexCategory.mk n)) →₀ ℤ)
    (i : ι)
    (x : (TopCat.toSSet.obj (TopCat.of (K i))).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (actual_singular_sigma_chains_equiv ι K n c) i x =
      c ((actual_singular_simplex_sigma_equiv ι K n).symm ⟨i,x⟩) := by
  rfl
#print axioms actual_singular_sigma_chains_equiv_apply

private theorem actual_singular_sigma_chains_single_same
    (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (n : ℕ) (p : ι)
    (x : (TopCat.toSSet.obj (TopCat.of (K p))).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (actual_singular_sigma_chains_equiv ι K n
      (Finsupp.single
        ((actual_singular_simplex_sigma_equiv ι K n).symm ⟨p,x⟩) 1)) p =
      Finsupp.single x 1 := by
  ext y
  rw [actual_singular_sigma_chains_equiv_apply]
  by_cases hxy : y = x
  · subst y
    rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
  · have hne : (actual_singular_simplex_sigma_equiv ι K n).symm ⟨p,y⟩ ≠
        (actual_singular_simplex_sigma_equiv ι K n).symm ⟨p,x⟩ := by
      intro he
      exact hxy (eq_of_heq (Sigma.mk.inj_iff.mp
        ((actual_singular_simplex_sigma_equiv ι K n).symm.injective he)).2)
    rw [Finsupp.single_eq_of_ne hne, Finsupp.single_eq_of_ne hxy]
#print axioms actual_singular_sigma_chains_single_same

private theorem actual_singular_sigma_chains_single_other
    (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (n : ℕ) (p q : ι) (hpq : q ≠ p)
    (x : (TopCat.toSSet.obj (TopCat.of (K p))).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (actual_singular_sigma_chains_equiv ι K n
      (Finsupp.single
        ((actual_singular_simplex_sigma_equiv ι K n).symm ⟨p,x⟩) 1)) q = 0 := by
  ext y
  rw [actual_singular_sigma_chains_equiv_apply]
  have hne : (actual_singular_simplex_sigma_equiv ι K n).symm ⟨q,y⟩ ≠
      (actual_singular_simplex_sigma_equiv ι K n).symm ⟨p,x⟩ := by
    intro he
    exact hpq (congrArg Sigma.fst
      ((actual_singular_simplex_sigma_equiv ι K n).symm.injective he))
  simp [hne]
#print axioms actual_singular_sigma_chains_single_other

private theorem actual_singular_sigma_chains_boundary
    (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of (Σ i, K i))).obj
      (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ) :
    actual_singular_sigma_chains_equiv ι K n
      (singularBoundaryFinsupp (TopCat.of (Σ i, K i)) n c) =
    fun i => singularBoundaryFinsupp (TopCat.of (K i)) n
      ((actual_singular_sigma_chains_equiv ι K (n + 1) c) i) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero =>
      funext i
      simp
  | add a b ha hb =>
      simp only [map_add, ha, hb]
      funext i
      simp only [Pi.add_apply, map_add]
  | single x a =>
      have ha : Finsupp.single x a = a • Finsupp.single x 1 := by simp
      rw [ha]
      simp only [map_smul, Pi.smul_apply]
      congr 1
      let e := actual_singular_simplex_sigma_equiv ι K (n + 1)
      let z := e x
      have hx : x = e.symm z := (e.symm_apply_apply x).symm
      obtain ⟨p,y⟩ := z
      rw [hx]
      have hface (j : Fin (n + 2)) :
          (TopCat.toSSet.obj (TopCat.of (Σ i, K i))).δ j (e.symm ⟨p,y⟩) =
          (actual_singular_simplex_sigma_equiv ι K n).symm
            ⟨p,(TopCat.toSSet.obj (TopCat.of (K p))).δ j y⟩ := by
        apply (actual_singular_simplex_sigma_equiv ι K n).injective
        have hj := actual_singular_simplex_sigma_equiv_face ι K n j (e.symm ⟨p,y⟩)
        rw [show (actual_singular_simplex_sigma_equiv ι K (n + 1))
          (e.symm ⟨p,y⟩) = ⟨p,y⟩ from e.apply_symm_apply _] at hj
        simpa only [Equiv.apply_symm_apply] using hj
      funext q
      rw [singularBoundaryFinsupp_single]
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
      by_cases hqp : q = p
      · subst q
        rw [actual_singular_sigma_chains_single_same ι K (n + 1) p y]
        rw [singularBoundaryFinsupp_single]
        congr 1
        funext j
        rw [hface j, actual_singular_sigma_chains_single_same ι K n p
          ((TopCat.toSSet.obj (TopCat.of (K p))).δ j y)]
      · rw [actual_singular_sigma_chains_single_other ι K (n + 1) p q hqp y]
        simp only [map_zero]
        apply Finset.sum_eq_zero
        intro j _
        rw [hface j, actual_singular_sigma_chains_single_other ι K n p q hqp
          ((TopCat.toSSet.obj (TopCat.of (K p))).δ j y)]
        simp
#print axioms actual_singular_sigma_chains_boundary

private theorem actual_singular_simplex_sigma_equiv_symm_eval
    (ι : Type) (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (n : ℕ) (p : ι)
    (g : (TopCat.toSSet.obj (TopCat.of (K p))).obj
      (Opposite.op (SimplexCategory.mk n)))
    (t : StdSimplex ℝ (Fin (n + 1))) :
    (TopCat.toSSetObjEquiv (TopCat.of (Σ i, K i))
      (Opposite.op (SimplexCategory.mk n))
      ((actual_singular_simplex_sigma_equiv ι K n).symm ⟨p,g⟩)) t =
      ⟨p,(TopCat.toSSetObjEquiv (TopCat.of (K p))
        (Opposite.op (SimplexCategory.mk n)) g) t⟩ := by
  rfl
#print axioms actual_singular_simplex_sigma_equiv_symm_eval

private theorem actual_singular_simplex_sigma_supported_iff
    (ι : Type) (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (A : ∀ i, Set (K i)) (n : ℕ) (p : ι)
    (g : (TopCat.toSSet.obj (TopCat.of (K p))).obj
      (Opposite.op (SimplexCategory.mk n))) :
    Set.range (TopCat.toSSetObjEquiv (TopCat.of (Σ i, K i))
      (Opposite.op (SimplexCategory.mk n))
      ((actual_singular_simplex_sigma_equiv ι K n).symm ⟨p,g⟩)) ⊆
      {z : Σ i, K i | z.2 ∈ A z.1} ↔
    Set.range (TopCat.toSSetObjEquiv (TopCat.of (K p))
      (Opposite.op (SimplexCategory.mk n)) g) ⊆ A p := by
  simp only [Set.range_subset_iff, Set.mem_setOf_eq,
    actual_singular_simplex_sigma_equiv_symm_eval]
  constructor
  · intro h t
    have ht := h t
    rw [actual_singular_simplex_sigma_equiv_symm_eval] at ht
    exact ht
  · intro h t
    rw [actual_singular_simplex_sigma_equiv_symm_eval]
    exact h t
#print axioms actual_singular_simplex_sigma_supported_iff

private theorem actual_singular_sigma_subspace_chains_supported_iff
    (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (A : ∀ i, Set (K i)) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of (Σ i, K i))).obj
      (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :
    c ∈ excisionSubspaceChains (TopCat.of (Σ i, K i))
      {z : Σ i, K i | z.2 ∈ A z.1} n ↔
    ∀ i, (actual_singular_sigma_chains_equiv ι K n c) i ∈
      excisionSubspaceChains (TopCat.of (K i)) (A i) n := by
  classical
  constructor
  · intro hc i
    apply (Finsupp.mem_supported' ℤ _).2
    intro y hy
    have hnot : ¬ Set.range (TopCat.toSSetObjEquiv (TopCat.of (Σ j, K j))
        (Opposite.op (SimplexCategory.mk n))
        ((actual_singular_simplex_sigma_equiv ι K n).symm ⟨i,y⟩)) ⊆
        {z : Σ j, K j | z.2 ∈ A z.1} := by
      exact mt (actual_singular_simplex_sigma_supported_iff ι K A n i y).mp hy
    have hz := (Finsupp.mem_supported' ℤ c).1 hc _ hnot
    simpa only [actual_singular_sigma_chains_equiv_apply] using hz
  · intro hc
    apply (Finsupp.mem_supported' ℤ c).2
    intro x hx
    let e := actual_singular_simplex_sigma_equiv ι K n
    let y := e x
    have hxy : x = e.symm y := (e.symm_apply_apply x).symm
    obtain ⟨i,g⟩ := y
    have hxy' : x = (actual_singular_simplex_sigma_equiv ι K n).symm ⟨i,g⟩ := hxy
    rw [hxy'] at hx ⊢
    have hnot : ¬ Set.range (TopCat.toSSetObjEquiv (TopCat.of (K i))
        (Opposite.op (SimplexCategory.mk n)) g) ⊆ A i := by
      apply mt (actual_singular_simplex_sigma_supported_iff ι K A n i g).mpr
      exact hx
    have hg := (Finsupp.mem_supported' ℤ
      ((actual_singular_sigma_chains_equiv ι K n c) i)).1 (hc i) g hnot
    rw [actual_singular_sigma_chains_equiv_apply] at hg
    exact hg
#print axioms actual_singular_sigma_subspace_chains_supported_iff

private theorem actual_singular_sigma_relative_cycles_iff
    (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (A : ∀ i, Set (K i)) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of (Σ i, K i))).obj
      (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ) :
    c ∈ excisionRelativeCycles (TopCat.of (Σ i, K i))
      {z : Σ i, K i | z.2 ∈ A z.1} n ↔
    ∀ i, (actual_singular_sigma_chains_equiv ι K (n + 1) c) i ∈
      excisionRelativeCycles (TopCat.of (K i)) (A i) n := by
  change singularBoundaryFinsupp (TopCat.of (Σ i, K i)) n c ∈
      excisionSubspaceChains (TopCat.of (Σ i, K i))
        {z : Σ i, K i | z.2 ∈ A z.1} n ↔
    ∀ i, singularBoundaryFinsupp (TopCat.of (K i)) n
      ((actual_singular_sigma_chains_equiv ι K (n + 1) c) i) ∈
        excisionSubspaceChains (TopCat.of (K i)) (A i) n
  rw [actual_singular_sigma_subspace_chains_supported_iff]
  rw [actual_singular_sigma_chains_boundary]
#print axioms actual_singular_sigma_relative_cycles_iff

private theorem actual_singular_sigma_boundary_range_iff
    (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of (Σ i, K i))).obj
      (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :
    c ∈ LinearMap.range (singularBoundaryFinsupp (TopCat.of (Σ i, K i)) n) ↔
    ∀ i, (actual_singular_sigma_chains_equiv ι K n c) i ∈
      LinearMap.range (singularBoundaryFinsupp (TopCat.of (K i)) n) := by
  classical
  constructor
  · rintro ⟨d,rfl⟩ i
    refine ⟨(actual_singular_sigma_chains_equiv ι K (n + 1) d) i, ?_⟩
    exact congrFun (actual_singular_sigma_chains_boundary ι K n d) i |>.symm
  · intro hc
    choose d hd using hc
    let dsrc := (actual_singular_sigma_chains_equiv ι K (n + 1)).symm d
    refine ⟨dsrc, ?_⟩
    apply (actual_singular_sigma_chains_equiv ι K n).injective
    rw [actual_singular_sigma_chains_boundary]
    funext i
    simpa only [dsrc, LinearEquiv.apply_symm_apply] using hd i
#print axioms actual_singular_sigma_boundary_range_iff

private theorem actual_singular_sigma_relative_boundaries_iff
    (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (A : ∀ i, Set (K i)) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of (Σ i, K i))).obj
      (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ) :
    c ∈ excisionRelativeBoundaries (TopCat.of (Σ i, K i))
      {z : Σ i, K i | z.2 ∈ A z.1} n ↔
    ∀ i, (actual_singular_sigma_chains_equiv ι K (n + 1) c) i ∈
      excisionRelativeBoundaries (TopCat.of (K i)) (A i) n := by
  classical
  constructor
  · intro hc i
    obtain ⟨u,hu,v,hv,heq⟩ := Submodule.mem_sup.mp hc
    apply Submodule.mem_sup.mpr
    refine ⟨(actual_singular_sigma_chains_equiv ι K (n + 1) u) i,
      (actual_singular_sigma_boundary_range_iff ι K (n + 1) u).mp hu i,
      (actual_singular_sigma_chains_equiv ι K (n + 1) v) i,
      (actual_singular_sigma_subspace_chains_supported_iff ι K A (n + 1) v).mp hv i,
      ?_⟩
    have h := congrArg (actual_singular_sigma_chains_equiv ι K (n + 1)) heq
    simpa only [map_add, Pi.add_apply] using congrFun h i
  · intro hc
    choose u hu v hv heq using fun i => Submodule.mem_sup.mp (hc i)
    let U := (actual_singular_sigma_chains_equiv ι K (n + 1)).symm u
    let V := (actual_singular_sigma_chains_equiv ι K (n + 1)).symm v
    have hU : U ∈ LinearMap.range
        (singularBoundaryFinsupp (TopCat.of (Σ i, K i)) (n + 1)) := by
      apply (actual_singular_sigma_boundary_range_iff ι K (n + 1) U).mpr
      intro i
      simpa only [U, LinearEquiv.apply_symm_apply] using hu i
    have hV : V ∈ excisionSubspaceChains (TopCat.of (Σ i, K i))
        {z : Σ i, K i | z.2 ∈ A z.1} (n + 1) := by
      apply (actual_singular_sigma_subspace_chains_supported_iff ι K A (n + 1) V).mpr
      intro i
      simpa only [V, LinearEquiv.apply_symm_apply] using hv i
    have hsum : U + V = c := by
      apply (actual_singular_sigma_chains_equiv ι K (n + 1)).injective
      funext i
      simpa only [map_add, Pi.add_apply, U, V, LinearEquiv.apply_symm_apply]
        using heq i
    exact Submodule.mem_sup.mpr ⟨U,hU,V,hV,hsum⟩
#print axioms actual_singular_sigma_relative_boundaries_iff

private theorem actual_relative_cycle_lift
    (M : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (x : M.X (n + 1)) (hx : M.d (n + 1) n x = 0) :
    ∃ z : M.cycles (n + 1), M.iCycles (n + 1) z = x := by
  let v : (M.sc (n + 1)).moduleCatLeftHomologyData.K := ⟨x, by
    change M.d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) x = 0
    rw [(ComplexShape.down ℕ).next_eq'
      (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]
    exact hx⟩
  refine ⟨(M.sc (n + 1)).moduleCatCyclesIso.inv v, ?_⟩
  exact congrArg (fun q => q v) ((M.sc (n + 1)).moduleCatCyclesIso_inv_iCycles)
#print axioms actual_relative_cycle_lift

private theorem actual_relative_homology_class_eq_iff_boundary
    (M : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (z w : M.cycles (n + 1)) :
    M.homologyπ (n + 1) z = M.homologyπ (n + 1) w ↔
    ∃ b : M.X (n + 2), M.d (n + 2) (n + 1) b =
      M.iCycles (n + 1) z - M.iCycles (n + 1) w := by
  rw [← (ModuleCat.mono_iff_injective (M.homologyι (n + 1))).mp
    inferInstance |>.eq_iff]
  have hh := M.homology_π_ι (n + 1)
  change (M.homologyπ (n + 1) ≫ M.homologyι (n + 1)) z =
    (M.homologyπ (n + 1) ≫ M.homologyι (n + 1)) w ↔ _
  rw [hh]
  have h := (M.sc (n + 1)).moduleCat_pOpcycles_eq_iff
    (M.iCycles (n + 1) z) (M.iCycles (n + 1) w)
  change _ ↔ ∃ b : M.X ((ComplexShape.down ℕ).prev (n + 1)),
    M.d _ (n + 1) b = M.iCycles (n + 1) z - M.iCycles (n + 1) w at h
  rw [(ComplexShape.down ℕ).prev_eq'
    (show (ComplexShape.down ℕ).Rel (n+2) (n+1) from rfl)] at h
  exact h
#print axioms actual_relative_homology_class_eq_iff_boundary

private theorem actual_canonical_relative_projection_cycle
    (X : TopCat) (A : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ)
    (hc : c ∈ excisionRelativeCycles X A n) :
    (relativeSingularChains X A).d (n + 1) n
      (canonicalRelativeProjection X A (n + 1) c) = 0 := by
  rw [canonicalRelativeProjection_boundary]
  change singularBoundaryFinsupp X n c ∈ excisionSubspaceChains X A n at hc
  have hker : singularBoundaryFinsupp X n c ∈
      LinearMap.ker (canonicalRelativeProjection X A n) := by
    rw [canonicalRelativeProjection_kernel]
    exact hc
  exact hker
#print axioms actual_canonical_relative_projection_cycle

private noncomputable def actual_relative_cycle_class
    (X : TopCat) (A : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ)
    (hc : c ∈ excisionRelativeCycles X A n) :
    relativeHomology X A (n + 1) :=
  (relativeSingularChains X A).homologyπ (n + 1)
    (Classical.choose (actual_relative_cycle_lift (relativeSingularChains X A) n
      (canonicalRelativeProjection X A (n + 1) c)
      (actual_canonical_relative_projection_cycle X A n c hc)))
#print axioms actual_relative_cycle_class

private theorem actual_relative_cycle_class_rep
    (X : TopCat) (A : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ)
    (hc : c ∈ excisionRelativeCycles X A n) :
    (relativeSingularChains X A).iCycles (n + 1)
      (Classical.choose (actual_relative_cycle_lift (relativeSingularChains X A) n
        (canonicalRelativeProjection X A (n + 1) c)
        (actual_canonical_relative_projection_cycle X A n c hc))) =
      canonicalRelativeProjection X A (n + 1) c :=
  Classical.choose_spec (actual_relative_cycle_lift (relativeSingularChains X A) n
    (canonicalRelativeProjection X A (n + 1) c)
    (actual_canonical_relative_projection_cycle X A n c hc))
#print axioms actual_relative_cycle_class_rep

private theorem actual_relative_cycle_class_zero_iff_boundary
    (X : TopCat) (A : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ)
    (hc : c ∈ excisionRelativeCycles X A n) :
    actual_relative_cycle_class X A n c hc = 0 ↔
      c ∈ excisionRelativeBoundaries X A n := by
  let L := relativeSingularChains X A
  let z := Classical.choose (actual_relative_cycle_lift L n
    (canonicalRelativeProjection X A (n + 1) c)
    (actual_canonical_relative_projection_cycle X A n c hc))
  have hz : L.iCycles (n + 1) z = canonicalRelativeProjection X A (n + 1) c :=
    actual_relative_cycle_class_rep X A n c hc
  constructor
  · intro hzero
    have heq : L.homologyπ (n + 1) z = L.homologyπ (n + 1) 0 := by
      change actual_relative_cycle_class X A n c hc = _
      simpa only [map_zero] using hzero
    obtain ⟨b,hb⟩ := (actual_relative_homology_class_eq_iff_boundary L n z 0).mp heq
    simp only [map_zero,sub_zero,hz] at hb
    obtain ⟨d,rfl⟩ := canonicalRelativeProjection_surjective X A (n + 2) b
    rw [canonicalRelativeProjection_boundary] at hb
    have hs : c - singularBoundaryFinsupp X (n + 1) d ∈
        excisionSubspaceChains X A (n + 1) := by
      rw [← canonicalRelativeProjection_kernel]
      change canonicalRelativeProjection X A (n + 1)
        (c - singularBoundaryFinsupp X (n + 1) d) = 0
      rw [map_sub, ← hb, sub_self]
    apply Submodule.mem_sup.mpr
    exact ⟨singularBoundaryFinsupp X (n + 1) d, ⟨d,rfl⟩,
      c - singularBoundaryFinsupp X (n + 1) d, hs, by abel⟩
  · intro hbound
    obtain ⟨u,⟨d,rfl⟩,v,hv,heq⟩ := Submodule.mem_sup.mp hbound
    have hvzero : canonicalRelativeProjection X A (n + 1) v = 0 := by
      have hker : v ∈ LinearMap.ker (canonicalRelativeProjection X A (n + 1)) := by
        rw [canonicalRelativeProjection_kernel]
        exact hv
      exact hker
    have hproj : canonicalRelativeProjection X A (n + 1) c =
        L.d (n + 2) (n + 1) (canonicalRelativeProjection X A (n + 2) d) := by
      have hh := congrArg (canonicalRelativeProjection X A (n + 1)) heq
      rw [map_add, hvzero, add_zero, ← canonicalRelativeProjection_boundary] at hh
      exact hh.symm
    have hclass : L.homologyπ (n + 1) z = L.homologyπ (n + 1) 0 := by
      apply (actual_relative_homology_class_eq_iff_boundary L n z 0).mpr
      refine ⟨canonicalRelativeProjection X A (n + 2) d, ?_⟩
      simpa only [map_zero,sub_zero,hz] using hproj.symm
    change L.homologyπ (n + 1) z = 0
    simpa only [map_zero] using hclass
#print axioms actual_relative_cycle_class_zero_iff_boundary

private theorem actual_relative_cycle_class_surjective
    (X : TopCat) (A : Set X) (n : ℕ)
    (r : relativeHomology X A (n + 1)) :
    ∃ c : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ,
      ∃ hc : c ∈ excisionRelativeCycles X A n,
        actual_relative_cycle_class X A n c hc = r := by
  let L := relativeSingularChains X A
  obtain ⟨z,rfl⟩ :=
    (ModuleCat.epi_iff_surjective (L.homologyπ (n + 1))).mp inferInstance r
  obtain ⟨c,hproj⟩ := canonicalRelativeProjection_surjective X A (n + 1)
    (L.iCycles (n + 1) z)
  have hc : c ∈ excisionRelativeCycles X A n := by
    change singularBoundaryFinsupp X n c ∈ excisionSubspaceChains X A n
    rw [← canonicalRelativeProjection_kernel]
    change canonicalRelativeProjection X A n (singularBoundaryFinsupp X n c) = 0
    rw [← canonicalRelativeProjection_boundary, hproj]
    exact congrArg (fun q => q z) (L.iCycles_d (n + 1) n)
  refine ⟨c,hc,?_⟩
  let w := Classical.choose (actual_relative_cycle_lift L n
    (canonicalRelativeProjection X A (n + 1) c)
    (actual_canonical_relative_projection_cycle X A n c hc))
  have hw : L.iCycles (n + 1) w = L.iCycles (n + 1) z := by
    rw [actual_relative_cycle_class_rep X A n c hc, hproj]
  have hwz : w = z :=
    (ModuleCat.mono_iff_injective (L.iCycles (n + 1))).mp inferInstance hw
  change L.homologyπ (n + 1) w = L.homologyπ (n + 1) z
  rw [hwz]
#print axioms actual_relative_cycle_class_surjective

private theorem actual_canonical_relative_projection_pair_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X,Y))
    (h : ∀ x ∈ A, f x ∈ B) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :
    (pairRelativeChainMap A B f h).f n
      (canonicalRelativeProjection (TopCat.of X) A n c) =
    canonicalRelativeProjection (TopCat.of Y) B n
      (singularFinsuppPush (TopCat.ofHom f) n c) := by
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)
  have hπ : cokernel.π (F.map (pairInclusion X A)) ≫
      pairRelativeChainMap A B f h =
      F.map (TopCat.ofHom f) ≫ cokernel.π (F.map (pairInclusion Y B)) :=
    cokernel.π_desc _ _ _
  have hn := congrArg (fun g => g.f n) hπ
  change (cokernel.π (F.map (pairInclusion X A))).f n ≫
    (pairRelativeChainMap A B f h).f n = _ at hn
  change ((cokernel.π (F.map (pairInclusion X A))).f n ≫
    (pairRelativeChainMap A B f h).f n)
      ((singularChainsFinsuppIso (TopCat.of X) n).inv c) = _
  rw [hn]
  change (cokernel.π (F.map (pairInclusion Y B))).f n
    ((F.map (TopCat.ofHom f)).f n
      ((singularChainsFinsuppIso (TopCat.of X) n).inv c)) = _
  rw [singularRepresentation_basis_naturality]
  rfl
#print axioms actual_canonical_relative_projection_pair_natural

private theorem actual_singular_push_simplex_supported
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X,Y))
    (h : ∀ x ∈ A, f x ∈ B) (n : ℕ)
    (x : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk n)))
    (hx : Set.range (TopCat.toSSetObjEquiv (TopCat.of X)
      (Opposite.op (SimplexCategory.mk n)) x) ⊆ A) :
    Set.range (TopCat.toSSetObjEquiv (TopCat.of Y)
      (Opposite.op (SimplexCategory.mk n))
      ((TopCat.toSSet.map (TopCat.ofHom f)).app
        (Opposite.op (SimplexCategory.mk n)) x)) ⊆ B := by
  intro y hy
  obtain ⟨t,rfl⟩ := hy
  change f ((TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk n)) x) t) ∈ B
  exact h _ (hx (Set.mem_range_self t))
#print axioms actual_singular_push_simplex_supported

private theorem actual_singular_push_subspace_supported
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X,Y))
    (h : ∀ x ∈ A, f x ∈ B) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk n)) →₀ ℤ)
    (hc : c ∈ excisionSubspaceChains (TopCat.of X) A n) :
    singularFinsuppPush (TopCat.ofHom f) n c ∈
      excisionSubspaceChains (TopCat.of Y) B n := by
  classical
  change c ∈ Finsupp.supported ℤ ℤ _ at hc
  change singularFinsuppPush (TopCat.ofHom f) n c ∈ Finsupp.supported ℤ ℤ _
  rw [Finsupp.supported_eq_span_single] at hc ⊢
  induction hc using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨x,hx,rfl⟩ := hz
      change Finsupp.lmapDomain ℤ ℤ _ (Finsupp.single x 1) ∈ _
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      apply Submodule.subset_span
      exact ⟨_, actual_singular_push_simplex_supported A B f h n x hx, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  | smul a c _ hc =>
      rw [map_smul]
      exact Submodule.smul_mem _ a hc
#print axioms actual_singular_push_subspace_supported

private theorem actual_singular_push_relative_cycle
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X,Y))
    (h : ∀ x ∈ A, f x ∈ B) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ)
    (hc : c ∈ excisionRelativeCycles (TopCat.of X) A n) :
    singularFinsuppPush (TopCat.ofHom f) (n + 1) c ∈
      excisionRelativeCycles (TopCat.of Y) B n := by
  change singularBoundaryFinsupp (TopCat.of Y) n
      (singularFinsuppPush (TopCat.ofHom f) (n + 1) c) ∈
        excisionSubspaceChains (TopCat.of Y) B n
  rw [singularFinsuppPush_boundary]
  exact actual_singular_push_subspace_supported A B f h n
    (singularBoundaryFinsupp (TopCat.of X) n c) hc
#print axioms actual_singular_push_relative_cycle

private theorem actual_relative_cycle_class_pair_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X,Y))
    (h : ∀ x ∈ A, f x ∈ B) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ)
    (hc : c ∈ excisionRelativeCycles (TopCat.of X) A n) :
    pairRelativeHomologyMap A B f h (n + 1)
      (actual_relative_cycle_class (TopCat.of X) A n c hc) =
    actual_relative_cycle_class (TopCat.of Y) B n
      (singularFinsuppPush (TopCat.ofHom f) (n + 1) c)
      (actual_singular_push_relative_cycle A B f h n c hc) := by
  let L := relativeSingularChains X A
  let M := relativeSingularChains Y B
  let F := pairRelativeChainMap A B f h
  let z := Classical.choose (actual_relative_cycle_lift L n
    (canonicalRelativeProjection (TopCat.of X) A (n + 1) c)
    (actual_canonical_relative_projection_cycle (TopCat.of X) A n c hc))
  let cp := singularFinsuppPush (TopCat.ofHom f) (n + 1) c
  let hcp := actual_singular_push_relative_cycle A B f h n c hc
  let w := Classical.choose (actual_relative_cycle_lift M n
    (canonicalRelativeProjection (TopCat.of Y) B (n + 1) cp)
    (actual_canonical_relative_projection_cycle (TopCat.of Y) B n cp hcp))
  change (L.homologyπ (n + 1) ≫ HomologicalComplex.homologyMap F (n + 1)) z =
    M.homologyπ (n + 1) w
  rw [HomologicalComplex.homologyπ_naturality]
  apply congrArg (M.homologyπ (n + 1))
  apply (ModuleCat.mono_iff_injective (M.iCycles (n + 1))).mp inferInstance
  have hi := congrArg (fun g => g z) (HomologicalComplex.cyclesMap_i F (n + 1))
  change M.iCycles (n + 1) (HomologicalComplex.cyclesMap F (n + 1) z) =
    F.f (n + 1) (L.iCycles (n + 1) z) at hi
  erw [hi]
  rw [actual_relative_cycle_class_rep (TopCat.of X) A n c hc]
  rw [actual_canonical_relative_projection_pair_natural]
  exact (actual_relative_cycle_class_rep (TopCat.of Y) B n cp hcp).symm
#print axioms actual_relative_cycle_class_pair_natural

private theorem actual_finite_sigma_relative_class_component_detection
    (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (A : ∀ i, Set (K i)) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of (Σ i, K i))).obj
      (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ)
    (hc : c ∈ excisionRelativeCycles (TopCat.of (Σ i, K i))
      {z : Σ i, K i | z.2 ∈ A z.1} n)
    (hzero : ∀ i,
      actual_relative_cycle_class (TopCat.of (K i)) (A i) n
        ((actual_singular_sigma_chains_equiv ι K (n + 1) c) i)
        ((actual_singular_sigma_relative_cycles_iff ι K A n c).mp hc i) = 0) :
    actual_relative_cycle_class (TopCat.of (Σ i, K i))
      {z : Σ i, K i | z.2 ∈ A z.1} n c hc = 0 := by
  apply (actual_relative_cycle_class_zero_iff_boundary _ _ n c hc).mpr
  apply (actual_singular_sigma_relative_boundaries_iff ι K A n c).mpr
  intro i
  exact (actual_relative_cycle_class_zero_iff_boundary
    (TopCat.of (K i)) (A i) n
    ((actual_singular_sigma_chains_equiv ι K (n + 1) c) i)
    ((actual_singular_sigma_relative_cycles_iff ι K A n c).mp hc i)).mp (hzero i)
#print axioms actual_finite_sigma_relative_class_component_detection

private theorem actual_singular_sigma_chain_decompose
    (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
    (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of (Σ i, K i))).obj
      (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :
    c = ∑ i : ι,
      singularFinsuppPush (TopCat.ofHom (ContinuousMap.sigmaMk i)) n
        ((actual_singular_sigma_chains_equiv ι K n c) i) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp only [map_add, Pi.add_apply, map_add, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) ha hb
  | single x a =>
      have ha : Finsupp.single x a = a • Finsupp.single x 1 := by simp
      rw [ha]
      simp only [map_smul, Pi.smul_apply]
      rw [← Finset.smul_sum]
      congr 1
      let e := actual_singular_simplex_sigma_equiv ι K n
      let z := e x
      have hx : x = e.symm z := (e.symm_apply_apply x).symm
      obtain ⟨p,y⟩ := z
      rw [hx]
      rw [Finset.sum_eq_single p]
      · rw [actual_singular_sigma_chains_single_same]
        simp only [singularFinsuppPush, Finsupp.lmapDomain_apply,
          Finsupp.mapDomain_single]
        congr 1
      · intro i _ hip
        rw [actual_singular_sigma_chains_single_other ι K n p i hip y]
        exact map_zero _
      · simp
#print axioms actual_singular_sigma_chain_decompose

private theorem actual_relative_homeomorph_pair_map_injective
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y)
    (he : ∀ x ∈ A, e x ∈ B)
    (he' : ∀ y ∈ B, e.symm y ∈ A) (n : ℕ) :
    Function.Injective (pairRelativeHomologyMap A B
      ⟨e,e.continuous⟩ he n) := by
  intro x y hxy
  let f : C(X,Y) := ⟨e,e.continuous⟩
  let g : C(Y,X) := ⟨e.symm,e.symm.continuous⟩
  have hfg : g.comp f = ContinuousMap.id X := by
    ext z
    exact e.symm_apply_apply z
  have hcomp := pairRelativeHomologyMap_comp A B A f g he he' n
  have hid := pairRelativeHomologyMap_id A n
  have hmap := congrArg
    (fun f : relativeHomology X A n ⟶ relativeHomology X A n => f x)
    (hcomp.symm.trans (by simpa only [hfg] using hid))
  have hmap' := congrArg
    (fun f : relativeHomology X A n ⟶ relativeHomology X A n => f y)
    (hcomp.symm.trans (by simpa only [hfg] using hid))
  simpa only [CategoryTheory.id_apply] using hmap.symm.trans
    ((congrArg (fun z => pairRelativeHomologyMap B A
      g he' n z) hxy).trans hmap')
#print axioms actual_relative_homeomorph_pair_map_injective

private theorem actual_relative_homeomorph_pair_map_surjective
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y)
    (he : ∀ x ∈ A, e x ∈ B)
    (he' : ∀ y ∈ B, e.symm y ∈ A) (n : ℕ) :
    Function.Surjective (pairRelativeHomologyMap A B
      ⟨e,e.continuous⟩ he n) := by
  let f : C(X,Y) := ⟨e,e.continuous⟩
  let g : C(Y,X) := ⟨e.symm,e.symm.continuous⟩
  have hgf : f.comp g = ContinuousMap.id Y := by
    ext z
    exact e.apply_symm_apply z
  have hcomp := pairRelativeHomologyMap_comp B A B g f he' he n
  have hid := pairRelativeHomologyMap_id B n
  have hright : pairRelativeHomologyMap B A g he' n ≫
      pairRelativeHomologyMap A B f he n =
      𝟙 (relativeHomology Y B n) :=
    hcomp.symm.trans (by simpa only [hgf] using hid)
  intro y
  refine ⟨pairRelativeHomologyMap B A g he' n y, ?_⟩
  have hh := congrArg (fun m : relativeHomology Y B n ⟶
    relativeHomology Y B n => m y) hright
  simpa only [CategoryTheory.id_apply, CategoryTheory.comp_apply] using hh
#print axioms actual_relative_homeomorph_pair_map_surjective

private theorem actual_relative_boundary_delete_subspace
    (X : TopCat) (A : Set X) (n : ℕ)
    (c d : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ)
    (hc : c ∈ excisionRelativeBoundaries X A n)
    (hcd : c - d ∈ excisionSubspaceChains X A (n + 1)) :
    d ∈ excisionRelativeBoundaries X A n := by
  have hsub : excisionSubspaceChains X A (n + 1) ≤
      excisionRelativeBoundaries X A n :=
    le_sup_right
  have hdiff : c - d ∈ excisionRelativeBoundaries X A n := hsub hcd
  have heq : d = c - (c - d) := by abel
  rw [heq]
  exact (excisionRelativeBoundaries X A n).sub_mem hc hdiff
#print axioms actual_relative_boundary_delete_subspace

private theorem actual_singular_push_whole_supported
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (B : Set Y) (f : C(X,Y)) (hf : ∀ x, f x ∈ B) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :
    singularFinsuppPush (TopCat.ofHom f) n c ∈
      excisionSubspaceChains (TopCat.of Y) B n := by
  apply actual_singular_push_subspace_supported Set.univ B f (by simp [hf]) n c
  change c ∈ Finsupp.supported ℤ ℤ _
  simp
#print axioms actual_singular_push_whole_supported

private theorem actual_singular_push_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X,Y)) (g : C(Y,Z)) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :
    singularFinsuppPush (TopCat.ofHom (g.comp f)) n c =
      singularFinsuppPush (TopCat.ofHom g) n
        (singularFinsuppPush (TopCat.ofHom f) n c) := by
  classical
  unfold singularFinsuppPush
  simp only [Finsupp.lmapDomain_apply]
  rw [← Finsupp.mapDomain_comp]
  congr 1
#print axioms actual_singular_push_comp

private theorem actual_relative_cycle_class_subspace_zero
    (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ)
    (hc : c ∈ excisionRelativeCycles (TopCat.of X) A n)
    (hsub : c ∈ excisionSubspaceChains (TopCat.of X) A (n + 1)) :
    actual_relative_cycle_class (TopCat.of X) A n c hc = 0 := by
  apply (actual_relative_cycle_class_zero_iff_boundary
    (TopCat.of X) A n c hc).mpr
  exact (show excisionSubspaceChains (TopCat.of X) A (n + 1) ≤
      excisionRelativeBoundaries (TopCat.of X) A n from le_sup_right) hsub
#print axioms actual_relative_cycle_class_subspace_zero

private theorem actual_sigma_push_offdiagonal_supported
    (ι : Type) [Fintype ι] (K : ι → Type)
    [∀ i, TopologicalSpace (K i)]
    (Y : Type) [TopologicalSpace Y] (B : Set Y)
    (f : C((Σ i, K i),Y)) (p : ι)
    (hother : ∀ i, i ≠ p → ∀ x : K i, f ⟨i,x⟩ ∈ B)
    (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of (Σ i, K i))).obj
      (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :
    singularFinsuppPush (TopCat.ofHom f) n c -
      singularFinsuppPush
        (TopCat.ofHom (f.comp (ContinuousMap.sigmaMk p))) n
        ((actual_singular_sigma_chains_equiv ι K n c) p) ∈
      excisionSubspaceChains (TopCat.of Y) B n := by
  classical
  let cp := actual_singular_sigma_chains_equiv ι K n c
  have hdecomp := actual_singular_sigma_chain_decompose ι K n c
  have hsum : singularFinsuppPush (TopCat.ofHom f) n c =
      ∑ i : ι, singularFinsuppPush
        (TopCat.ofHom (f.comp (ContinuousMap.sigmaMk i))) n (cp i) := by
    rw [hdecomp, map_sum]
    congr 1
    funext i
    exact (actual_singular_push_comp (ContinuousMap.sigmaMk i) f n (cp i)).symm
  rw [hsum]
  have hrest : ∀ i : ι, i ≠ p →
      singularFinsuppPush
        (TopCat.ofHom (f.comp (ContinuousMap.sigmaMk i))) n (cp i) ∈
      excisionSubspaceChains (TopCat.of Y) B n := by
    intro i hi
    exact actual_singular_push_whole_supported B
      (f.comp (ContinuousMap.sigmaMk i))
      (fun x => hother i hi x) n (cp i)
  rw [← Finset.add_sum_erase Finset.univ
    (fun i => singularFinsuppPush
      (TopCat.ofHom (f.comp (ContinuousMap.sigmaMk i))) n (cp i))
    (Finset.mem_univ p)]
  rw [show (singularFinsuppPush
      (TopCat.ofHom (f.comp (ContinuousMap.sigmaMk p))) n (cp p)) +
      (∑ i ∈ Finset.univ.erase p, singularFinsuppPush
        (TopCat.ofHom (f.comp (ContinuousMap.sigmaMk i))) n (cp i)) -
      singularFinsuppPush
        (TopCat.ofHom (f.comp (ContinuousMap.sigmaMk p))) n (cp p) =
      ∑ i ∈ Finset.univ.erase p, singularFinsuppPush
        (TopCat.ofHom (f.comp (ContinuousMap.sigmaMk i))) n (cp i) by abel]
  exact Submodule.sum_mem _ (fun i hi =>
    hrest i (Finset.ne_of_mem_erase hi))
#print axioms actual_sigma_push_offdiagonal_supported

private theorem actual_sigma_point_boundary_component
    (ι : Type) [Fintype ι] (K : ι → Type)
    [∀ i, TopologicalSpace (K i)]
    (Y : Type) [TopologicalSpace Y] (B : Set Y)
    (f : C((Σ i, K i),Y)) (p : ι)
    (hother : ∀ i, i ≠ p → ∀ x : K i, f ⟨i,x⟩ ∈ B)
    (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of (Σ i, K i))).obj
      (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ)
    (hbound : singularFinsuppPush (TopCat.ofHom f) (n + 1) c ∈
      excisionRelativeBoundaries (TopCat.of Y) B n) :
    singularFinsuppPush
      (TopCat.ofHom (f.comp (ContinuousMap.sigmaMk p))) (n + 1)
      ((actual_singular_sigma_chains_equiv ι K (n + 1) c) p) ∈
      excisionRelativeBoundaries (TopCat.of Y) B n := by
  let d := singularFinsuppPush (TopCat.ofHom f) (n + 1) c
  let e := singularFinsuppPush
    (TopCat.ofHom (f.comp (ContinuousMap.sigmaMk p))) (n + 1)
    ((actual_singular_sigma_chains_equiv ι K (n + 1) c) p)
  have hde : d - e ∈ excisionSubspaceChains (TopCat.of Y) B (n + 1) :=
    actual_sigma_push_offdiagonal_supported ι K Y B f p hother (n + 1) c
  exact actual_relative_boundary_delete_subspace (TopCat.of Y) B n d e hbound hde
#print axioms actual_sigma_point_boundary_component

private theorem actual_disjoint_component_exterior_eq
    (E ι : Type) [TopologicalSpace E]
    (D V : ι → Set E) (hDV : ∀ i, D i ⊆ V i)
    (hdisj : Set.univ.Pairwise (fun i j : ι => Disjoint (V i) (V j)))
    (p : ι) (x : V p) :
    x.val ∈ (⋃ i, D i)ᶜ ↔ x.val ∈ (D p)ᶜ := by
  constructor
  · intro hx hd
    exact hx (Set.mem_iUnion.mpr ⟨p,hd⟩)
  · intro hx hsome
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hsome
    by_cases hip : i = p
    · subst i
      exact hx hi
    · have hnot : Disjoint (V i) (V p) :=
        hdisj (Set.mem_univ _) (Set.mem_univ _) hip
      exact (Set.disjoint_left.mp hnot) (hDV i hi) x.property
#print axioms actual_disjoint_component_exterior_eq

private theorem actual_literal_single_component_collar
    (E : Type) [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    (q : E) (r : ℝ)
    (htarget : closedBall ((chartAt ℂ q) q) r ⊆ (chartAt ℂ q).target)
    (V : Set E) (hVopen : IsOpen V)
    (hKV : (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) r ⊆ V) :
    closure Vᶜ ⊆ interior
      ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) r)ᶜ := by
  let K : Set E := (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) r
  have hKclosed : IsClosed K :=
    actual_literal_chart_closedBall_image_isClosed E q r htarget
  have hKcP : Kᶜ ⊆
      ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) r)ᶜ :=
    Set.compl_subset_compl.mpr (Set.image_mono ball_subset_closedBall)
  rw [hVopen.isClosed_compl.closure_eq]
  exact (Set.compl_subset_compl.mpr hKV).trans
    (interior_maximal hKcP hKclosed.isOpen_compl)
#print axioms actual_literal_single_component_collar

set_option maxHeartbeats 1000000 in
private theorem actual_disjoint_literal_chart_discs_relative_point_detection
    (E : Type) [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    (Z : Finset E) (ρ : Z → ℝ) (hρ : ∀ q, 0 < ρ q)
    (htarget : ∀ q : Z, closedBall ((chartAt ℂ q.val) q.val) (ρ q) ⊆
      (chartAt ℂ q.val).target)
    (hdisjoint : Set.univ.Pairwise (fun q r : Z => Disjoint
      ((chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρ q))
      ((chartAt ℂ r.val).symm '' closedBall ((chartAt ℂ r.val) r.val) (ρ r)))) :
    let P : Set E := (⋃ q : Z,
      (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρ q))ᶜ;
    ∃ havoid : ∀ q : Z, ∀ x ∈ P, x ≠ q.val,
      Function.Injective (fun r : relativeHomology E P 2 =>
        fun q : Z => pairRelativeHomologyMap P ({q.val}ᶜ)
          (ContinuousMap.id E) (havoid q) 2 r) := by
  classical
  dsimp only
  have hcenter (q : Z) : q.val ∈ (⋃ p : Z,
      (chartAt ℂ p.val).symm '' ball ((chartAt ℂ p.val) p.val) (ρ p)) := by
    apply Set.mem_iUnion.mpr
    refine ⟨q, (chartAt ℂ q.val) q.val, mem_ball_self (hρ q), ?_⟩
    exact (chartAt ℂ q.val).left_inv (mem_chart_source ℂ q.val)
  let havoid : ∀ q : Z, ∀ x ∈ (⋃ p : Z,
      (chartAt ℂ p.val).symm '' ball ((chartAt ℂ p.val) p.val) (ρ p))ᶜ,
      x ≠ q.val := by
    intro q x hx he
    exact hx (he ▸ hcenter q)
  refine ⟨havoid, ?_⟩
  by_cases hZ : Z = ∅
  · subst Z
    have hP : (⋃ q : (∅ : Finset E),
        (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρ q))ᶜ =
        (Set.univ : Set E) := by simp
    intro r s _
    haveI : Subsingleton (relativeHomology E (⋃ q : (∅ : Finset E),
        (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρ q))ᶜ 2) := by
      rw [hP]
      exact ModuleCat.subsingleton_of_isZero (actual_relativeHomology_univ_isZero E 2)
    exact Subsingleton.elim r s
  · by_cases hcard : Z.card = 1
    · obtain ⟨q, hZq⟩ := Finset.card_eq_one.mp hcard
      subst Z
      let q' : ({q} : Finset E) := ⟨q, Finset.mem_singleton_self q⟩
      have hP : (⋃ p : ({q} : Finset E),
          (chartAt ℂ p.val).symm '' ball ((chartAt ℂ p.val) p.val) (ρ p))ᶜ =
          ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) (ρ q'))ᶜ := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_iUnion]
        constructor
        · intro hx hy
          apply hx
          exact ⟨q', hy⟩
        · intro hx hy
          obtain ⟨p,hpx⟩ := hy
          have hp : p = q' := Subtype.ext (Finset.mem_singleton.mp p.property)
          subst p
          exact hx hpx
      obtain ⟨havoid',hinj⟩ := actual_literal_chart_disc_exterior_point_detection
        E q (ρ q') (hρ q') (htarget q')
      have hsingle : ∃ hav : ∀ x ∈ (⋃ p : ({q} : Finset E),
          (chartAt ℂ p.val).symm '' ball ((chartAt ℂ p.val) p.val) (ρ p))ᶜ,
          x ≠ q,
          Function.Injective (pairRelativeHomologyMap
            (⋃ p : ({q} : Finset E),
              (chartAt ℂ p.val).symm '' ball ((chartAt ℂ p.val) p.val) (ρ p))ᶜ
            ({q}ᶜ) (ContinuousMap.id E) hav 2) := by
        exact hP.symm ▸ ⟨havoid',hinj⟩
      obtain ⟨hav,hinj1⟩ := hsingle
      intro r s hrs
      have heq := congrFun hrs q'
      exact hinj1 (by simpa only using heq)
    · let P : Set E := (⋃ q : Z,
          (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρ q))ᶜ
      obtain ⟨V,hV,hVdisjoint,hU⟩ :=
        actual_finite_literal_chart_excision_collar E Z ρ htarget hdisjoint
      let U : Set E := (⋃ q : Z, V q)ᶜ
      have hIso : IsIso (excisionHomologyMap_connecting P U 2) := by
        change IsIso (HomologicalComplex.homologyMap (excisionRelativeChainMap P U) 2)
        exact canonicalExcisionHomologyMap_isIso E P U hU 1
      let N : Set E := Uᶜ
      have hNeq : (⋃ q : Z, V q) = N := by
        ext x
        simp only [N, U, Set.mem_compl_iff, not_not]
      let D : Z → Set E := fun q =>
        (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρ q)
      let K : Z → Set E := fun q =>
        (chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρ q)
      have hDN (q : Z) : D q ⊆ V q :=
        (Set.image_mono ball_subset_closedBall).trans (hV q).2
      let eN : (Σ q : Z, V q) ≃ₜ N :=
        (actual_disjoint_open_union_homeomorph E Z V
          (fun q => (hV q).1) hVdisjoint).trans (Homeomorph.setCongr hNeq)
      let A : ∀ q : Z, Set (V q) := fun q =>
        {x | x.val ∈ P}
      let AS : Set (Σ q : Z, V q) :=
        {z | z.2 ∈ A z.1}
      let AN : Set N := {x | x.val ∈ P}
      have heNval (z : Σ q : Z, V q) : (eN z).val = z.2.val := by
        rfl
      have hAN : ∀ z ∈ AS, eN z ∈ AN := by
        intro z hz
        change (eN z).val ∈ P
        rw [heNval]
        exact hz
      have hAN' : ∀ x ∈ AN, eN.symm x ∈ AS := by
        intro x hx
        change x.val ∈ P at hx
        have hv : (eN (eN.symm x)).val ∈ P := by
          rw [eN.apply_symm_apply]
          exact hx
        change (eN.symm x).2.val ∈ P
        rw [← heNval]
        exact hv
      have hSigmaSurj : Function.Surjective
          (pairRelativeHomologyMap AS AN
            ⟨eN,eN.continuous⟩ hAN 2) :=
        actual_relative_homeomorph_pair_map_surjective AS AN eN hAN hAN' 2
      have hAq (q : Z) (x : V q) :
          x ∈ A q ↔ x.val ∈ (D q)ᶜ :=
        actual_disjoint_component_exterior_eq E Z D V hDN hVdisjoint q x
      have hcomponentIso (q : Z) :
          IsIso (excisionHomologyMap_connecting (D q)ᶜ (V q)ᶜ 2) := by
        change IsIso (HomologicalComplex.homologyMap
          (excisionRelativeChainMap (D q)ᶜ (V q)ᶜ) 2)
        exact canonicalExcisionHomologyMap_isIso E (D q)ᶜ (V q)ᶜ
          (actual_literal_single_component_collar E q.val (ρ q)
            (htarget q) (V q) (hV q).1 (hV q).2) 1
      intro r s hrs
      let t : relativeHomology E P 2 := r - s
      have htpoint (q : Z) : pairRelativeHomologyMap P ({q.val}ᶜ)
          (ContinuousMap.id E) (havoid q) 2 t = 0 := by
        change pairRelativeHomologyMap P ({q.val}ᶜ)
          (ContinuousMap.id E) (havoid q) 2 (r - s) = 0
        rw [map_sub, sub_eq_zero]
        exact congrFun hrs q
      obtain ⟨tN,htN⟩ :=
        (ModuleCat.epi_iff_surjective (excisionHomologyMap_connecting P U 2)).mp
          inferInstance t
      obtain ⟨tS,htS⟩ := hSigmaSurj tN
      obtain ⟨c,hc,hclass⟩ := actual_relative_cycle_class_surjective
        (TopCat.of (Σ q : Z, V q)) AS 1 tS
      let inc : C(N,E) := ⟨Subtype.val, continuous_subtype_val⟩
      let fS : C((Σ q : Z, V q),E) :=
        inc.comp ⟨eN,eN.continuous⟩
      have hfSval (z : Σ q : Z, V q) : fS z = z.2.val := heNval z
      have hSP : ∀ z ∈ AS, fS z ∈ P := by
        intro z hz
        rw [hfSval]
        exact hz
      have hSpoint (q : Z) : ∀ z ∈ AS, fS z ≠ q.val := by
        intro z hz
        exact havoid q (fS z) (hSP z hz)
      have hother (q j : Z) (hjq : j ≠ q) (x : V j) :
          fS ⟨j,x⟩ ≠ q.val := by
        rw [hfSval]
        intro hx
        have hqD : q.val ∈ D q := by
          refine ⟨(chartAt ℂ q.val) q.val, mem_ball_self (hρ q), ?_⟩
          exact (chartAt ℂ q.val).left_inv (mem_chart_source ℂ q.val)
        have hqV : q.val ∈ V q := hDN q hqD
        exact (Set.disjoint_left.mp
          (hVdisjoint (Set.mem_univ _) (Set.mem_univ _) hjq))
          x.property (hx ▸ hqV)
      have hFactor : t = pairRelativeHomologyMap AS P fS hSP 2 tS := by
        have hinc : ∀ x ∈ AN, inc x ∈ P := by
          intro x hx
          exact hx
        have hincmap : pairRelativeHomologyMap AN P inc hinc 2 =
            excisionHomologyMap_connecting P U 2 := rfl
        have hcomp := pairRelativeHomologyMap_comp AS AN P
          ⟨eN,eN.continuous⟩ inc hAN hinc 2
        have heq : pairRelativeHomologyMap AS P fS hSP 2 =
            pairRelativeHomologyMap AS AN ⟨eN,eN.continuous⟩ hAN 2 ≫
              pairRelativeHomologyMap AN P inc hinc 2 := by
          exact hcomp
        calc
          t = excisionHomologyMap_connecting P U 2 tN := htN.symm
          _ = pairRelativeHomologyMap AS P fS hSP 2 tS := by
            rw [heq, CategoryTheory.comp_apply, htS]
            exact congrArg (fun m => m tN) hincmap.symm
      have hzeroSpoint (q : Z) :
          pairRelativeHomologyMap AS ({q.val}ᶜ) fS
            (hSpoint q) 2 tS = 0 := by
        have h := htpoint q
        rw [hFactor] at h
        have hcomp := pairRelativeHomologyMap_comp AS P ({q.val}ᶜ)
          fS (ContinuousMap.id E) hSP (havoid q) 2
        have heq : pairRelativeHomologyMap AS ({q.val}ᶜ) fS
            (hSpoint q) 2 =
            pairRelativeHomologyMap AS P fS hSP 2 ≫
              pairRelativeHomologyMap P ({q.val}ᶜ)
                (ContinuousMap.id E) (havoid q) 2 := by
          simpa only [ContinuousMap.id_comp] using hcomp
        rw [heq, CategoryTheory.comp_apply]
        exact h
      have hboundPoint (q : Z) :
          singularFinsuppPush (TopCat.ofHom fS) 2 c ∈
            excisionRelativeBoundaries (TopCat.of E) ({q.val}ᶜ) 1 := by
        have hcy := actual_singular_push_relative_cycle AS ({q.val}ᶜ)
          fS (hSpoint q) 1 c hc
        apply (actual_relative_cycle_class_zero_iff_boundary
          (TopCat.of E) ({q.val}ᶜ) 1 _ hcy).mp
        rw [← actual_relative_cycle_class_pair_natural AS ({q.val}ᶜ)
          fS (hSpoint q) 1 c hc, hclass]
        exact hzeroSpoint q
      have hboundComponent (q : Z) :
          singularFinsuppPush
            (TopCat.ofHom (fS.comp (ContinuousMap.sigmaMk q))) 2
            ((actual_singular_sigma_chains_equiv Z (fun j => (V j : Type)) 2 c) q) ∈
              excisionRelativeBoundaries (TopCat.of E) ({q.val}ᶜ) 1 :=
        actual_sigma_point_boundary_component Z (fun j => (V j : Type)) E ({q.val}ᶜ)
          fS q (hother q) 1 c (hboundPoint q)
      have hcomponentPointInj (q : Z) :
          Function.Injective (pairRelativeHomologyMap (A q) ({q.val}ᶜ)
            (fS.comp (ContinuousMap.sigmaMk (X := fun j : Z => (V j : Type)) q))
            (fun x hx => by exact hSpoint q ⟨q,x⟩ hx) 2) := by
        let gq : C((V q),E) := fS.comp
          (ContinuousMap.sigmaMk (X := fun j : Z => (V j : Type)) q)
        have hgq : gq = ⟨Subtype.val,continuous_subtype_val⟩ := by
          ext x
          exact hfSval ⟨q,x⟩
        have hgD : ∀ x ∈ A q, gq x ∈ (D q)ᶜ := by
          intro x hx
          rw [hgq]
          exact (hAq q x).mp hx
        obtain ⟨havQ,hinjQ⟩ := actual_literal_chart_disc_exterior_point_detection
          E q.val (ρ q) (hρ q) (htarget q)
        let Q : Set E := (V q)ᶜ
        let eQ : (V q) ≃ₜ Excised E Q :=
          Homeomorph.setCongr (by simp [Q] : V q = Qᶜ)
        have heQval (x : V q) : (eQ x).val = x.val := rfl
        let BQ : Set (Excised E Q) := excisedSubspace (D q)ᶜ Q
        have hABQ : ∀ x ∈ A q, eQ x ∈ BQ := by
          intro x hx
          change (eQ x).val ∈ (D q)ᶜ
          rw [heQval]
          exact (hAq q x).mp hx
        have hBQA : ∀ x ∈ BQ, eQ.symm x ∈ A q := by
          intro x hx
          change (eQ.symm x).val ∈ P
          have hv : (eQ (eQ.symm x)).val ∈ (D q)ᶜ := by
            rw [eQ.apply_symm_apply]
            exact hx
          rw [heQval] at hv
          exact (hAq q (eQ.symm x)).mpr hv
        let jQ : C(Excised E Q,E) := ⟨Subtype.val,continuous_subtype_val⟩
        have hjQ : ∀ x ∈ BQ, jQ x ∈ (D q)ᶜ := by
          intro x hx
          exact hx
        have hgj : gq = jQ.comp ⟨eQ,eQ.continuous⟩ := by
          ext x
          rw [hgq]
          exact (heQval x).symm
        have hJmap : pairRelativeHomologyMap BQ (D q)ᶜ jQ hjQ 2 =
            excisionHomologyMap_connecting (D q)ᶜ Q 2 := rfl
        have hmapDInj : Function.Injective
            (pairRelativeHomologyMap (A q) (D q)ᶜ gq hgD 2) := by
          have hcompD := pairRelativeHomologyMap_comp (A q) BQ (D q)ᶜ
            ⟨eQ,eQ.continuous⟩ jQ hABQ hjQ 2
          have heq : pairRelativeHomologyMap (A q) (D q)ᶜ gq hgD 2 =
              pairRelativeHomologyMap (A q) BQ ⟨eQ,eQ.continuous⟩ hABQ 2 ≫
                pairRelativeHomologyMap BQ (D q)ᶜ jQ hjQ 2 := by
            simpa only [hgj] using hcompD
          rw [heq, hJmap]
          exact ((ModuleCat.mono_iff_injective
            (excisionHomologyMap_connecting (D q)ᶜ Q 2)).mp inferInstance).comp
            (actual_relative_homeomorph_pair_map_injective
              (A q) BQ eQ hABQ hBQA 2)
        have hcomp := pairRelativeHomologyMap_comp (A q) (D q)ᶜ
          ({q.val}ᶜ) gq (ContinuousMap.id E) hgD havQ 2
        have hpointEq : pairRelativeHomologyMap (A q) ({q.val}ᶜ) gq
            (fun x hx => by change fS ⟨q,x⟩ ≠ q.val; exact hSpoint q ⟨q,x⟩ hx) 2 =
            pairRelativeHomologyMap (A q) (D q)ᶜ gq hgD 2 ≫
              pairRelativeHomologyMap (D q)ᶜ ({q.val}ᶜ)
                (ContinuousMap.id E) havQ 2 := by
          simpa only [ContinuousMap.id_comp] using hcomp
        rw [hpointEq]
        exact hinjQ.comp hmapDInj
      have hcomponentZero (q : Z) :
          actual_relative_cycle_class (TopCat.of (V q)) (A q) 1
            ((actual_singular_sigma_chains_equiv Z
              (fun j => (V j : Type)) 2 c) q)
            ((actual_singular_sigma_relative_cycles_iff Z
              (fun j => (V j : Type)) A 1 c).mp hc q) = 0 := by
        let cq := (actual_singular_sigma_chains_equiv Z
          (fun j => (V j : Type)) 2 c) q
        let hcq := (actual_singular_sigma_relative_cycles_iff Z
          (fun j => (V j : Type)) A 1 c).mp hc q
        let gq : C((V q),E) := fS.comp
          (ContinuousMap.sigmaMk (X := fun j : Z => (V j : Type)) q)
        have hgpoint : ∀ x ∈ A q, gq x ∈ ({q.val}ᶜ : Set E) := by
          intro x hx
          exact hSpoint q ⟨q,x⟩ hx
        apply hcomponentPointInj q
        simp only [map_zero]
        rw [actual_relative_cycle_class_pair_natural (A q) ({q.val}ᶜ)
          gq hgpoint 1 cq hcq]
        apply (actual_relative_cycle_class_zero_iff_boundary
          (TopCat.of E) ({q.val}ᶜ) 1 _ _).mpr
        exact hboundComponent q
      have hSigmaZero : actual_relative_cycle_class
          (TopCat.of (Σ q : Z, V q)) AS 1 c hc = 0 :=
        actual_finite_sigma_relative_class_component_detection Z
          (fun j => (V j : Type)) A 1 c hc hcomponentZero
      have htSzero : tS = 0 := by
        rw [← hclass]
        exact hSigmaZero
      have htzero : t = 0 := by
        rw [hFactor, htSzero, map_zero]
      exact sub_eq_zero.mp htzero
#print axioms actual_disjoint_literal_chart_discs_relative_point_detection
