import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalPathClassUniversalCover
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisChart

open CurveComplex Set Topology Schoenflies Metric
namespace RegionalEmbeddedFamily
open CurveComplex.LocalSurgery
set_option maxHeartbeats 2000000

theorem contact_chart_sphere_is_curve (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (E : OpenPartialHomeomorph S Plane) (p : Plane) (R : ℝ) (hR : 0<R)
    (htarget : closedBall p R ⊆ E.target) :
    ∃ c : Curve S, c.image=E.symm '' sphere p R := by
  classical
  let L : ℂ ≃L[ℝ] Plane := Complex.equivRealProdCLM.trans
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
      (EuclideanSpace.equiv (Fin 2) ℝ).symm)
  have hnorm (z : ℂ) : ‖L z‖=‖z‖ := by
    change ‖Plane.mk z.re z.im‖=‖z‖
    simp [EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk,
      Complex.norm_def,Complex.normSq_apply,Real.norm_eq_abs,pow_two]
  let q : Circle → Plane := fun z => p+R • L (z:ℂ)
  have hqmem (z : Circle) : q z∈sphere p R := by
    rw [mem_sphere,dist_eq_norm]
    dsimp [q]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hR,hnorm,Circle.norm_coe,mul_one]
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hqi : Function.Injective q := by
    intro z w he
    have hs : R • L (z:ℂ)=R • L (w:ℂ) := add_left_cancel he
    exact Subtype.ext (L.injective ((smul_right_injective Plane hR.ne') hs))
  have hqr : range q=sphere p R := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      exact hqmem z
    · intro hy
      let v : Plane := R⁻¹ • (y-p)
      have hv : ‖v‖=1 := by
        dsimp [v]
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
        have hn : ‖y-p‖=R := by simpa [mem_sphere,dist_eq_norm] using hy
        rw [hn,inv_mul_cancel₀ hR.ne']
      have hz : ‖L.symm v‖=1 := by rw [←hnorm (L.symm v),L.apply_symm_apply,hv]
      let z : Circle := ⟨L.symm v,by change L.symm v∈sphere (0:ℂ) 1; simpa only [mem_sphere,dist_zero_right] using hz⟩
      refine ⟨z,?_⟩
      dsimp [q,z]
      rw [L.apply_symm_apply]
      dsimp [v]
      rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
      abel
  have hqt (z : Circle) : q z∈E.target := htarget (sphere_subset_closedBall (hqmem z))
  let f : Circle → S := E.symm ∘ q
  have hfc : Continuous f := E.continuousOn_symm.comp_continuous hqc hqt
  have hfi : Function.Injective f := by
    intro z w he
    exact hqi (E.symm.injOn (hqt z) (hqt w) he)
  let c : Curve S := ⟨f,(hfc.isClosedEmbedding hfi).isEmbedding⟩
  refine ⟨c,?_⟩
  change range (E.symm ∘ q)=_
  rw [range_comp,hqr]

/-- View a homeomorphism of open subsets as an ambient partial chart. -/
theorem contact_chart_from_open_subtypes
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {U : Set X} {V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    (h : U ≃ₜ V) (x₀ : U) :
    ∃ E : OpenPartialHomeomorph X Y, E.source = U ∧ E.target = V ∧
      ∀ (x : X) (hx : x ∈ U), E x = (h ⟨x,hx⟩).val := by
  classical
  let f : X → Y := fun x => if hx : x ∈ U then (h ⟨x,hx⟩).val else (h x₀).val
  let g : Y → X := fun y => if hy : y ∈ V then (h.symm ⟨y,hy⟩).val else x₀.val
  let E : OpenPartialHomeomorph X Y := {
    toFun := f
    invFun := g
    source := U
    target := V
    map_source' := by intro x hx; simp [f,hx]
    map_target' := by intro y hy; simp [g,hy]
    left_inv' := by intro x hx; simp [f,g,hx,(h ⟨x,hx⟩).property]
    right_inv' := by intro y hy; simp [f,g,hy,(h.symm ⟨y,hy⟩).property]
    open_source := hU
    open_target := hV
    continuousOn_toFun := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (continuous_subtype_val.comp h.continuous).congr
        (fun x => by simp [f,x.property])
    continuousOn_invFun := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (continuous_subtype_val.comp h.symm.continuous).congr
        (fun x => by simp [g,x.property]) }
  exact ⟨E,rfl,rfl,fun x hx => dite_eq_left hx⟩

/-- A connected set missing a closed set's frontier lies wholly on one side. -/
theorem contact_connected_set_missing_frontier
    {X : Type*} [TopologicalSpace X] (F A : Set X)
    (hF : IsClosed F) (hA : IsPreconnected A)
    (hclear : Disjoint A (frontier F)) : A ⊆ F ∨ A ⊆ Fᶜ := by
  have hsub : A ⊆ interior F ∪ Fᶜ := by
    intro x hx
    by_cases h : x ∈ F
    · exact Or.inl ((mem_interior_iff_notMem_frontier h).mpr
        (fun hf => Set.disjoint_left.mp hclear hx hf))
    · exact Or.inr h
  have hd : Disjoint (interior F) Fᶜ :=
    Set.disjoint_left.mpr (fun _ hi hf => hf (interior_subset hi))
  exact (hA.subset_or_subset isOpen_interior hF.isOpen_compl hd hsub).imp
    (fun h => h.trans interior_subset) id

/-- A straight local frontier gives a contractible relative neighborhood of a closed set. -/
theorem contact_axis_frontier_contractible_neighborhood
    {X : Type*} [TopologicalSpace X] (F : Set X) (hF : IsClosed F)
    (p : ↥F) (E : OpenPartialHomeomorph X (ℝ × ℝ))
    (hp : p.val ∈ E.source) (hzero : E p.val = 0)
    (haxis : ∀ x ∈ E.source, x ∈ frontier F ↔ (E x).1 = 0)
    (W : Set ↥F) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ U : Set ↥F, p ∈ U ∧ IsOpen U ∧ U ⊆ W ∧ ContractibleSpace U := by
  obtain ⟨O,hO,rfl⟩ := isOpen_induced_iff.mp hW
  have hpO : p.val ∈ O := hpW
  have hZ : IsOpen (E.target ∩ E.symm ⁻¹' O) := E.isOpen_inter_preimage_symm hO
  have h0Z : (0 : ℝ × ℝ) ∈ E.target ∩ E.symm ⁻¹' O := by
    rw [← hzero]
    exact ⟨E.map_source hp,by simpa only [Set.mem_preimage,E.left_inv hp] using hpO⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hZ 0 h0Z
  let B := Metric.ball (0 : ℝ × ℝ) r
  have hBT : B ⊆ E.target := fun _ hy => (hball hy).1
  let Q := B ∩ E.symm ⁻¹' F
  have hminus : IsPreconnected (E.symm '' (B ∩ {y : ℝ × ℝ | y.1 < 0})) := by
    have hl : IsLinearMap ℝ (fun y : ℝ × ℝ => y.1) :=
      ⟨by intros; rfl,by intros; rfl⟩
    exact ((convex_ball (0 : ℝ × ℝ) r).inter (convex_halfSpace_lt hl 0)).isPreconnected.image
      E.symm (E.symm.continuousOn.mono (Set.inter_subset_left.trans hBT))
  have hplus : IsPreconnected (E.symm '' (B ∩ {y : ℝ × ℝ | 0 < y.1})) := by
    have hl : IsLinearMap ℝ (fun y : ℝ × ℝ => y.1) :=
      ⟨by intros; rfl,by intros; rfl⟩
    exact ((convex_ball (0 : ℝ × ℝ) r).inter (convex_halfSpace_gt hl 0)).isPreconnected.image
      E.symm (E.symm.continuousOn.mono (Set.inter_subset_left.trans hBT))
  have hmc : Disjoint (E.symm '' (B ∩ {y : ℝ × ℝ | y.1 < 0})) (frontier F) := by
    rw [Set.disjoint_left]
    rintro _ ⟨y,hy,rfl⟩ hf
    have hh := (haxis _ (E.map_target (hBT hy.1))).mp hf
    rw [E.right_inv (hBT hy.1)] at hh
    exact hy.2.ne hh
  have hpc : Disjoint (E.symm '' (B ∩ {y : ℝ × ℝ | 0 < y.1})) (frontier F) := by
    rw [Set.disjoint_left]
    rintro _ ⟨y,hy,rfl⟩ hf
    have hh := (haxis _ (E.map_target (hBT hy.1))).mp hf
    rw [E.right_inv (hBT hy.1)] at hh
    exact hy.2.ne' hh
  have hm := contact_connected_set_missing_frontier F _ hF hminus hmc
  have hp' := contact_connected_set_missing_frontier F _ hF hplus hpc
  have hmprop {x y : ℝ × ℝ} (hx : x ∈ Q) (hy : y ∈ B)
      (hxneg : x.1 < 0) (hyneg : y.1 < 0) : E.symm y ∈ F := by
    rcases hm with hm | hm
    · exact hm ⟨y,⟨hy,hyneg⟩,rfl⟩
    · exact False.elim ((hm ⟨x,⟨hx.1,hxneg⟩,rfl⟩) hx.2)
  have hpprop {x y : ℝ × ℝ} (hx : x ∈ Q) (hy : y ∈ B)
      (hxpos : 0 < x.1) (hypos : 0 < y.1) : E.symm y ∈ F := by
    rcases hp' with hh | hh
    · exact hh ⟨y,⟨hy,hypos⟩,rfl⟩
    · exact False.elim ((hh ⟨x,⟨hx.1,hxpos⟩,rfl⟩) hx.2)
  have hQ : Convex ℝ Q := by
    intro x hx y hy a b ha hb hab
    have hz : a • x + b • y ∈ B := (convex_ball (0 : ℝ × ℝ) r) hx.1 hy.1 ha hb hab
    refine ⟨hz,?_⟩
    rcases lt_trichotomy (a * x.1 + b * y.1) 0 with hn | he | hpos
    · have hc : x.1 < 0 ∨ y.1 < 0 := by
        by_contra hn'
        push Not at hn'
        nlinarith [mul_nonneg ha hn'.1,mul_nonneg hb hn'.2]
      exact hc.elim (fun hh => hmprop hx hz hh hn) (fun hh => hmprop hy hz hh hn)
    · apply hF.frontier_subset
      apply (haxis _ (E.map_target (hBT hz))).mpr
      rw [E.right_inv (hBT hz)]
      exact he
    · have hc : 0 < x.1 ∨ 0 < y.1 := by
        by_contra hn'
        push Not at hn'
        nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hn'.1,
          mul_nonpos_of_nonneg_of_nonpos hb hn'.2]
      exact hc.elim (fun hh => hpprop hx hz hh hpos) (fun hh => hpprop hy hz hh hpos)
  have hpQ : E p.val ∈ Q := by
    refine ⟨by rw [hzero]; exact Metric.mem_ball_self hr,?_⟩
    change E.symm (E p.val) ∈ F
    simpa only [E.left_inv hp] using p.property
  let U : Set ↥F := Subtype.val ⁻¹' (E.symm '' B)
  have hpU : p ∈ U := ⟨E p.val,hpQ.1,E.left_inv hp⟩
  have hU : IsOpen U :=
    (E.isOpen_image_symm_of_subset_target Metric.isOpen_ball hBT).preimage continuous_subtype_val
  have hUW : U ⊆ Subtype.val ⁻¹' O := by
    rintro x ⟨y,hy,he⟩
    change x.val ∈ O
    rw [← he]
    exact (hball hy).2
  have hUsource (x : U) : x.val.val ∈ E.source := by
    obtain ⟨y,hy,he⟩ := x.property
    exact he ▸ E.map_target (hBT hy)
  have hUQ (x : U) : E x.val.val ∈ Q := by
    obtain ⟨y,hy,he⟩ := x.property
    refine ⟨?_,?_⟩
    · rw [← he,E.right_inv (hBT hy)]
      exact hy
    · simpa only [Set.mem_preimage,E.left_inv (hUsource x)] using x.val.property
  let e : Q ≃ₜ U := {
    toFun := fun y => ⟨⟨E.symm y.val,y.property.2⟩,⟨y.val,y.property.1,rfl⟩⟩
    invFun := fun x => ⟨E x.val.val,hUQ x⟩
    left_inv := by intro y; apply Subtype.ext; exact E.right_inv (hBT y.property.1)
    right_inv := by intro x; apply Subtype.ext; apply Subtype.ext; exact E.left_inv (hUsource x)
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact E.symm.continuousOn.comp_continuous continuous_subtype_val
        (fun y => hBT y.property.1)
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact E.continuousOn.comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val) hUsource }
  let : ContractibleSpace Q := hQ.contractibleSpace ⟨E p.val,hpQ⟩
  exact ⟨U,hpU,hU,hUW,e.symm.contractibleSpace⟩

/-- Transfer an ambient contractible subset into a containing subspace. -/
theorem contact_contractible_subset_subtype
    {X : Type*} [TopologicalSpace X] (F A : Set X) (hAF : A ⊆ F)
    [ContractibleSpace A] : ContractibleSpace (Subtype.val ⁻¹' A : Set ↥F) := by
  let e : A ≃ₜ (Subtype.val ⁻¹' A : Set ↥F) := {
    toFun := fun x => ⟨⟨x.val,hAF x.property⟩,x.property⟩
    invFun := fun x => ⟨x.val.val,x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact e.symm.contractibleSpace

/-- Finite disjoint embedded-circle frontier supplies the actual subspace's local basis. -/
theorem contact_finite_circle_frontier_contractible_basis
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (F : Set S) (hF : IsClosed F) {I : Type} [Fintype I]
    (c : I → Curve S)
    (hdis : ∀ i j, i ≠ j → Disjoint (c i).image (c j).image)
    (hfront : frontier F = ⋃ i, (c i).image)
    (p : ↥F) (W : Set ↥F) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ U : Set ↥F, p ∈ U ∧ IsOpen U ∧ U ⊆ W ∧ ContractibleSpace U := by
  classical
  by_cases hpfront : p.val ∈ frontier F
  · obtain ⟨i,hpi⟩ := Set.mem_iUnion.mp (hfront ▸ hpfront)
    obtain ⟨U,V,hpU,h,hU,hV,hzero,haxis⟩ := embedded_curve_has_local_axis_chart (c i) p.val hpi
    obtain ⟨E,hEU,hEV,hE⟩ := contact_chart_from_open_subtypes hU hV h ⟨p.val,hpU⟩
    let G : Set S := ⋃ j : {j : I // j ≠ i}, (c j.val).image
    have hG : IsClosed G := (isCompact_iUnion
      (fun j : {j : I // j ≠ i} => isCompact_range (c j.val).embedded.continuous)).isClosed
    have hpG : p.val ∉ G := by
      intro hh
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hh
      exact Set.disjoint_left.mp (hdis j.val i j.property) hj hpi
    let K := E.restr Gᶜ
    have hKs : K.source = U ∩ Gᶜ := by rw [E.restr_source' _ hG.isOpen_compl,hEU]
    have hpK : p.val ∈ K.source := by rw [hKs]; exact ⟨hpU,hpG⟩
    have hzK : K p.val = 0 := by
      change E p.val = 0
      rw [hE p.val hpU]
      exact hzero
    have hKaxis : ∀ x ∈ K.source, x ∈ frontier F ↔ (K x).1 = 0 := by
      intro x hx
      rw [hKs] at hx
      change x ∈ frontier F ↔ (E x).1 = 0
      rw [hE x hx.1,← haxis x hx.1,hfront]
      constructor
      · intro hxfront
        obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hxfront
        by_cases he : j = i
        · simpa only [he] using hj
        · exact False.elim (hx.2 (Set.mem_iUnion.mpr ⟨⟨j,he⟩,hj⟩))
      · exact fun hx => Set.mem_iUnion.mpr ⟨i,hx⟩
    exact contact_axis_frontier_contractible_neighborhood F hF p K hpK hzK hKaxis W hW hpW
  · obtain ⟨O,hO,rfl⟩ := isOpen_induced_iff.mp hW
    have hpint : p.val ∈ interior F :=
      (mem_interior_iff_notMem_frontier p.property).mpr hpfront
    obtain ⟨A,hpA,hA,hAO,hcA⟩ := charted_surface_contractible_neighborhood p.val
      (interior F ∩ O) (isOpen_interior.inter hO) ⟨hpint,hpW⟩
    let : ContractibleSpace A := hcA
    refine ⟨Subtype.val ⁻¹' A,hpA,hA.preimage continuous_subtype_val,
      (fun x hx => (hAO hx).2),?_⟩
    exact contact_contractible_subset_subtype F A (fun x hx => interior_subset (hAO hx).1)

end RegionalEmbeddedFamily
