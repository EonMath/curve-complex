import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualMarkedEndpointSourceFanChart
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualMarkedInteriorContactFanPreprocessing
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedFiniteSurfaceReplacement
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.GapMatchingTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.UniformContactPatchTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.CornerGeometryTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualChartArcTools

import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedAffineCrossingDisk
import CurveComplexGenusTwo.Topology.Smoothing.PrescribedPairRadializationProof
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.DiskExteriorHalfTools
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEmbeddedAnchorPointChart
import Mathlib.Topology.LocalAtTarget
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedEmptyBigonCleanSides
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualRawTailBigonReplacement
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkFreeBigonLoopExclusion
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance (M : HyperellipticModel E S) : DecidableEq (EssentialArcClass M) := Classical.decEq _
open ArcSurgery Set Topology Metric Schoenflies CurveComplex.ActualCrossingSlide
open scoped BigOperators
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
theorem hActualInteriorParameterHomeomorph (M : HyperellipticModel E S) [T2Space S] (c : EssentialMarkedArc M) :
    ∃ e : (c.val.map ⁻¹' arcInterior M c) ≃ₜ arcInterior M c,
      ∀ t, (e t).val=c.val.map t.val := by
  let f := (arcInterior M c).restrictPreimage c.val.map
  have hf : Continuous f := (c.val.continuous.comp continuous_subtype_val).subtype_mk _
  have hfi : Function.Injective f := by
    intro t u he
    have hh : c.val.map t.val=c.val.map u.val := congrArg Subtype.val he
    rcases c.val.injective_except_loop_closure _ _ hh with hh|hh|hh
    · exact Subtype.ext hh
    · have hm : c.val.map t.val ∈ M.cover.branch := hh.1.symm ▸ c.val.start_marked
      exact (t.property.2 hm).elim
    · have hm : c.val.map t.val ∈ M.cover.branch := hh.1.symm ▸ c.val.end_marked
      exact (t.property.2 hm).elim
  have hfs : Function.Surjective f := by
    intro x
    obtain ⟨t,ht⟩ := x.property.1
    refine ⟨⟨t,?_⟩,?_⟩
    · change c.val.map t ∈ arcInterior M c
      exact ht.symm ▸ x.property
    · exact Subtype.ext ht
  have hfc : IsClosedMap f := c.val.continuous.isClosedMap.restrictPreimage _
  let q := Equiv.ofBijective f ⟨hfi,hfs⟩
  exact ⟨q.toHomeomorphOfContinuousClosed hf hfc,fun _ => rfl⟩

theorem hExplicitMarkedAxisStripChart (M : HyperellipticModel E S) [T2Space S]
    (anchor : EssentialMarkedArc M)
    (B : Interval × Icc (-1:ℝ) 1 → S) (hB : IsEmbedding B)
    (hmarks : ∀ z, B z ∉ M.cover.branch)
    (haxis : ∀ z, B z ∈ anchor.val.image ↔ z.2.val = 0) :
    ∃ U : Set S, ∃ V : Set Plane, ∃ _hU : IsOpen U, ∃ e : U ≃ₜ V,
      IsOpen V ∧ Plane.closedSquare 0 1 ⊆ V ∧ Disjoint U (M.cover.branch : Set S) ∧
      (∀ q : U, q.val ∈ anchor.val.image ↔ (e q).val 1 = 0) ∧
      (∀ t : Interval, 0 < t.val → t.val < 1 →
        ∃ ht : B (t,⟨0,by norm_num⟩) ∈ U,
          (e ⟨B (t,⟨0,by norm_num⟩),ht⟩).val=Plane.mk (4*t.val-2) 0) ∧
      ∃ hp : B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩) ∈ U,
        (e ⟨B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩),hp⟩).val = 0 := by
  let := (actualSphereSmoothAtlas M).charts
  let q : UnitBox → Interval × Icc (-1:ℝ) 1 := fun z =>
    (⟨(z.val.1+1)/2,by have h := abs_lt.mp z.property.1; constructor <;> linarith⟩,
      ⟨z.val.2,(abs_lt.mp z.property.2).1.le,(abs_lt.mp z.property.2).2.le⟩)
  have hqc : Continuous q := by unfold q; fun_prop
  let inv : Interval × Icc (-1:ℝ) 1 → ℝ × ℝ := fun z => (2*z.1.val-1,z.2.val)
  have hinv : Continuous inv := by unfold inv; fun_prop
  have hqi : IsEmbedding q := by
    apply IsEmbedding.of_comp hqc hinv
    have he : inv ∘ q = (Subtype.val : UnitBox → ℝ × ℝ) := by
      funext z; apply Prod.ext
      · dsimp [inv,q]; ring
      · rfl
    rw [he]
    exact IsEmbedding.subtypeVal
  let f : UnitBox → S := B ∘ q
  have hf : IsEmbedding f := hB.comp hqi
  let U : Set S := range f
  let F : Plane → S := fun z => B (projIcc 0 1 zero_le_one ((z 0+1)/2),
    projIcc (-1) 1 (by norm_num) (z 1))
  have hFc : Continuous F := by
    apply hB.continuous.comp
    exact (continuous_projIcc.comp (by fun_prop)).prodMk (continuous_projIcc.comp (by fun_prop))
  have hFU : F '' Plane.openSquare 0 1 = U := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hz' : |z 0| < 1 ∧ |z 1| < 1 :=
        max_lt_iff.mp (mem_openSquare_zero_one.mp hz)
      refine ⟨⟨(z 0,z 1),hz'⟩,?_⟩
      apply congrArg B
      apply Prod.ext <;> apply Subtype.ext
      · have h := abs_lt.mp hz'.1
        rw [projIcc_of_mem zero_le_one
          (show (z 0+1)/2 ∈ Icc (0:ℝ) 1 by constructor <;> linarith)]
      · rw [projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1)
          ⟨(abs_lt.mp hz'.2).1.le,(abs_lt.mp hz'.2).2.le⟩]
    · rintro ⟨z,rfl⟩
      refine ⟨Plane.mk z.val.1 z.val.2,?_,?_⟩
      · apply mem_openSquare_zero_one.mpr
        exact max_lt_iff.mpr z.property
      · apply congrArg B
        apply Prod.ext <;> apply Subtype.ext
        · have h := abs_lt.mp z.property.1
          change (projIcc 0 1 zero_le_one ((z.val.1+1)/2)).val = (z.val.1+1)/2
          rw [projIcc_of_mem zero_le_one (show (z.val.1+1)/2 ∈ Icc (0:ℝ) 1 by constructor <;> linarith)]
        · change (projIcc (-1) 1 (by norm_num) z.val.2).val = z.val.2
          rw [projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1)
              ⟨(abs_lt.mp z.property.2).1.le,(abs_lt.mp z.property.2).2.le⟩]
  have hFi : InjOn F (Plane.openSquare 0 1) := by
    intro z hz w hw he
    have hz' := max_lt_iff.mp (mem_openSquare_zero_one.mp hz)
    have hw' := max_lt_iff.mp (mem_openSquare_zero_one.mp hw)
    have hqcoord (z : Plane) (hz : |z 0| < 1 ∧ |z 1| < 1) :
        F z = f ⟨(z 0,z 1),hz⟩ := by
      apply congrArg B
      apply Prod.ext <;> apply Subtype.ext
      · have h := abs_lt.mp hz.1
        rw [projIcc_of_mem zero_le_one
          (show (z 0+1)/2 ∈ Icc (0:ℝ) 1 by constructor <;> linarith)]
      · rw [projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1)
          ⟨(abs_lt.mp hz.2).1.le,(abs_lt.mp hz.2).2.le⟩]
    rw [hqcoord z hz',hqcoord w hw'] at he
    have h := congrArg Subtype.val (hf.injective he)
    ext i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hU : IsOpen U := hFU ▸ surface_invariance_of_domain_probe F _
    (Plane.isOpen_openSquare 0 1) hFc.continuousOn hFi
  let j : UnitBox ≃ₜ U := hf.toHomeomorph
  let V : Set Plane := doublePlaneCoordinates '' {z : ℝ × ℝ | |z.1|<1 ∧ |z.2|<1}
  let e : U ≃ₜ V := j.symm.trans (doublePlaneCoordinates.image _)
  have hVOpen : IsOpen V := doublePlaneCoordinates.isOpenMap _
    ((isOpen_lt continuous_fst.abs continuous_const).inter
      (isOpen_lt continuous_snd.abs continuous_const))
  have hCV : Plane.closedSquare 0 1 ⊆ V := by
    intro z hz
    have h := max_le_iff.mp (mem_closedSquare_zero_one.mp hz)
    refine ⟨(z 0/2,z 1/2),?_,?_⟩
    · change |z 0/2| < 1 ∧ |z 1/2| < 1
      rw [abs_div,abs_div]; norm_num
      constructor <;> linarith [h.1,h.2]
    · apply planeCoordinates.injective
      apply Prod.ext
      · change 2*(z 0/2) = z 0; ring
      · change 2*(z 1/2) = z 1; ring
  have hj (z : U) : B (q (j.symm z)) = z.val := congrArg Subtype.val (j.apply_symm_apply z)
  let z0 : UnitBox := ⟨(0,0),by norm_num⟩
  have hz0 : f z0 = B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩) := by
    apply congrArg B
    apply Prod.ext <;> apply Subtype.ext <;> norm_num [q,z0]
  have hpU : B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩) ∈ U := ⟨z0,hz0⟩
  refine ⟨U,V,hU,e,hVOpen,hCV,?_,?_,?_,hpU,?_⟩
  · apply Set.disjoint_left.mpr
    rintro z ⟨w,rfl⟩ hz
    exact hmarks (q w) hz
  · intro z
    rw [← hj z,haxis]
    change (j.symm z).val.2 = 0 ↔ 2*(j.symm z).val.2 = 0
    constructor <;> intro h <;> linarith
  · intro t ht0 ht1
    let z : UnitBox := ⟨(2*t.val-1,0),by
      constructor
      · rw [abs_lt]; constructor <;> linarith
      · norm_num⟩
    have hz : f z=B (t,⟨0,by norm_num⟩) := by
      apply congrArg B
      apply Prod.ext <;> apply Subtype.ext
      · change (2*t.val-1+1)/2=t.val
        ring
      · rfl
    have ht : B (t,⟨0,by norm_num⟩) ∈ U := ⟨z,hz⟩
    refine ⟨ht,?_⟩
    have he : j.symm ⟨B (t,⟨0,by norm_num⟩),ht⟩=z := by
      apply j.injective
      rw [j.apply_symm_apply]
      apply Subtype.ext
      exact hz.symm
    change doublePlaneCoordinates (j.symm _).val=Plane.mk (4*t.val-2) 0
    rw [he]
    ext i
    fin_cases i
    · change 2*(2*t.val-1)=4*t.val-2
      ring
    · change 2*(0:ℝ)=0
      ring
  · have he : j.symm ⟨B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩),hpU⟩ = z0 := by
      apply j.injective
      rw [j.apply_symm_apply]
      apply Subtype.ext
      exact hz0.symm
    change doublePlaneCoordinates (j.symm _).val = 0
    rw [he]
    apply planeCoordinates.injective
    apply Prod.ext
    · change 2*(0:ℝ) = 0; ring
    · change 2*(0:ℝ) = 0; ring

theorem hActualWholeInteriorAxisChart (M : HyperellipticModel E S) [T2Space S] (c : EssentialMarkedArc M)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1) :
    ∃ U : Set S, ∃ V : Set Plane, ∃ hU : IsOpen U, ∃ e : U ≃ₜ V,
      IsOpen V ∧ Plane.closedSquare 0 1 ⊆ V ∧ Disjoint U (M.cover.branch : Set S) ∧
      (∀ q : U, q.val ∈ c.val.image ↔ (e q).val 1=0) ∧
      ∀ θ ∈ Set.Ioo α β,
        ∃ hx : c.val.map (Set.projIcc 0 1 zero_le_one θ) ∈ U,
          (e ⟨c.val.map (Set.projIcc 0 1 zero_le_one θ),hx⟩).val=
            Plane.mk (4*((θ-α)/(β-α))-2) 0 := by
  obtain ⟨B,hB,hcenter,hmarks,haxis⟩ := actual_anchor_interior_core_exact_strip M c α β hα hβ hαβ
  obtain ⟨U,V,hU,e,hV,hCV,hUMarks,hUAxis,hcover,hmid,hmid0⟩ :=
    hExplicitMarkedAxisStripChart M c B hB hmarks haxis
  refine ⟨U,V,hU,e,hV,hCV,hUMarks,hUAxis,?_⟩
  intro θ hθ
  have hd : 0 < β-α := sub_pos.mpr hαβ
  let t : Interval := ⟨(θ-α)/(β-α),
    (div_pos (sub_pos.mpr hθ.1) hd).le,
    ((div_lt_one hd).mpr (by linarith [hθ.2])).le⟩
  have ht0 : 0 < t.val := div_pos (sub_pos.mpr hθ.1) hd
  have ht1 : t.val < 1 := (div_lt_one hd).mpr (by linarith [hθ.2])
  have hparam : actualCoreParameter α β hα.le hβ.le hαβ.le t=Set.projIcc 0 1 zero_le_one θ := by
    rw [Set.projIcc_of_mem zero_le_one ⟨hα.le.trans hθ.1.le,hθ.2.le.trans hβ.le⟩]
    apply Subtype.ext
    dsimp [actualCoreParameter,t]
    field_simp
    ring
  have htmap : B (t,⟨0,by norm_num⟩)=c.val.map (Set.projIcc 0 1 zero_le_one θ) :=
    (hcenter t).trans (congrArg c.val.map hparam)
  obtain ⟨ht,hcoord⟩ := hcover t ht0 ht1
  have hx : c.val.map (Set.projIcc 0 1 zero_le_one θ) ∈ U := htmap ▸ ht
  refine ⟨hx,?_⟩
  have he : (⟨B (t,⟨0,by norm_num⟩),ht⟩ : U)=
      ⟨c.val.map (Set.projIcc 0 1 zero_le_one θ),hx⟩ := Subtype.ext htmap
  rw [he] at hcoord
  exact hcoord

theorem hActualCompactMarkFreeCarrierAxisChart (M : HyperellipticModel E S) [T2Space S] (c : EssentialMarkedArc M)
    (f : C(Interval,S)) (hf : IsEmbedding f) (hsub : range f ⊆ arcInterior M c) :
    ∃ U : Set S, ∃ V : Set Plane, ∃ hU : IsOpen U, ∃ e : U ≃ₜ V,
      IsOpen V ∧ Plane.closedSquare 0 1 ⊆ V ∧ Disjoint U (M.cover.branch : Set S) ∧
      (∀ q : U, q.val ∈ c.val.image ↔ (e q).val 1=0) ∧
      ∃ hfU : range f ⊆ U, ∃ χ : C(Interval,ℝ),
        (StrictMono χ ∨ StrictAnti χ) ∧
        ∀ t, (e ⟨f t,hfU (Set.mem_range_self t)⟩).val=Plane.mk (χ t) 0 := by
  obtain ⟨q,hq⟩ := hActualInteriorParameterHomeomorph M c
  let point : C(Interval,arcInterior M c) :=
    ⟨fun t => ⟨f t,hsub (Set.mem_range_self t)⟩,f.continuous.subtype_mk _⟩
  let τ : C(Interval,ℝ) := ⟨fun t => (q.symm (point t)).val.val,
    continuous_subtype_val.comp (continuous_subtype_val.comp (q.symm.continuous.comp point.continuous))⟩
  have hτf (t : Interval) : c.val.map (q.symm (point t)).val=f t := by
    rw [← hq]
    exact congrArg Subtype.val (q.apply_symm_apply _)
  have hτ01 (t : Interval) : 0 < τ t ∧ τ t < 1 := by
    have hm : c.val.map (q.symm (point t)).val ∉ M.cover.branch := (q.symm (point t)).property.2
    constructor
    · have hn : (q.symm (point t)).val ≠ 0 := fun he => hm (he.symm ▸ c.val.start_marked)
      exact lt_of_le_of_ne (q.symm (point t)).val.property.1 (fun he => hn (Subtype.ext he.symm))
    · have hn : (q.symm (point t)).val ≠ 1 := fun he => hm (he.symm ▸ c.val.end_marked)
      exact lt_of_le_of_ne (q.symm (point t)).val.property.2 (fun he => hn (Subtype.ext he))
  let C : Set ℝ := range τ
  have hC : IsCompact C := isCompact_range τ.continuous
  have hCne : C.Nonempty := Set.range_nonempty τ
  let l := sInf C
  let u := sSup C
  have hl : l ∈ C := hC.isClosed.csInf_mem hCne hC.bddBelow
  have hu : u ∈ C := hC.isClosed.csSup_mem hCne hC.bddAbove
  have hl0 : 0 < l := by obtain ⟨t,ht⟩ := hl; exact ht ▸ (hτ01 t).1
  have hu1 : u < 1 := by obtain ⟨t,ht⟩ := hu; exact ht ▸ (hτ01 t).2
  have hlu : l ≤ u := csInf_le hC.bddBelow hu
  let α := l/2
  let β := (u+1)/2
  have hα : 0 < α := half_pos hl0
  have hβ : β < 1 := by dsimp [β]; linarith
  have hαβ : α < β := by dsimp [α,β]; linarith
  obtain ⟨U,V,hU,e,hV,hCV,hUMark,hAxis,hCover⟩ := hActualWholeInteriorAxisChart M c α β hα hαβ hβ
  have hfU : range f ⊆ U := by
    rintro x ⟨t,rfl⟩
    have hτC : τ t ∈ C := Set.mem_range_self t
    have hτlo : l ≤ τ t := csInf_le hC.bddBelow hτC
    have hτhi : τ t ≤ u := le_csSup hC.bddAbove hτC
    have hτAB : τ t ∈ Set.Ioo α β := by dsimp [α,β]; constructor <;> linarith
    obtain ⟨hx,hcoord⟩ := hCover (τ t) hτAB
    have htmap : c.val.map (Set.projIcc 0 1 zero_le_one (τ t))=f t := by
      rw [Set.projIcc_of_mem zero_le_one ⟨(hτ01 t).1.le,(hτ01 t).2.le⟩]
      exact hτf t
    exact htmap ▸ hx
  have hτinj : Function.Injective τ := by
    intro t s he
    have heq : (q.symm (point t)).val=(q.symm (point s)).val := Subtype.ext he
    exact hf.injective ((hτf t).symm.trans ((congrArg c.val.map heq).trans (hτf s)))
  let χ : C(Interval,ℝ) := ⟨fun t => 4*((τ t-α)/(β-α))-2,by fun_prop⟩
  have hχinj : Function.Injective χ := by
    intro t s he
    apply hτinj
    change 4*((τ t-α)/(β-α))-2=4*((τ s-α)/(β-α))-2 at he
    field_simp [ne_of_gt (sub_pos.mpr hαβ)] at he
    nlinarith
  refine ⟨U,V,hU,e,hV,hCV,hUMark,hAxis,hfU,χ,
    χ.continuous.strictMono_of_inj_boundedOrder' hχinj,?_⟩
  intro t
  have hτC : τ t ∈ C := Set.mem_range_self t
  have hτlo : l ≤ τ t := csInf_le hC.bddBelow hτC
  have hτhi : τ t ≤ u := le_csSup hC.bddAbove hτC
  have hτAB : τ t ∈ Set.Ioo α β := by dsimp [α,β]; constructor <;> linarith
  obtain ⟨hx,hcoord⟩ := hCover (τ t) hτAB
  have htmap : c.val.map (Set.projIcc 0 1 zero_le_one (τ t))=f t := by
    rw [Set.projIcc_of_mem zero_le_one ⟨(hτ01 t).1.le,(hτ01 t).2.le⟩]
    exact hτf t
  have he : (⟨c.val.map (Set.projIcc 0 1 zero_le_one (τ t)),hx⟩ : U)=
      ⟨f t,hfU (Set.mem_range_self t)⟩ := Subtype.ext htmap
  rw [he] at hcoord
  exact hcoord

theorem actual_compact_mark_free_increasing_axis_chart
    (M : HyperellipticModel E S) [T2Space S] (c : EssentialMarkedArc M)
    (f : C(Interval,S)) (hf : IsEmbedding f) (hsub : range f ⊆ arcInterior M c) :
    ∃ F : OpenPartialHomeomorph S Plane, ∃ χ : C(Interval,ℝ),
      StrictMono χ ∧ range f ⊆ F.source ∧
      Disjoint F.source (M.cover.branch : Set S) ∧
      (∀ x ∈ F.source, x ∈ c.val.image ↔ F x 1=0) ∧
      ∀ t, F (f t)=Plane.mk (χ t) 0 := by
  obtain ⟨U,V,hU,e,hV,hCV,hMark,hAxis,hfU,χ,hχ,hCoord⟩ :=
    hActualCompactMarkFreeCarrierAxisChart M c f hf hsub
  have : Nonempty U := ⟨⟨f 0,hfU (Set.mem_range_self 0)⟩⟩
  let coeU : OpenPartialHomeomorph U S := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  let z : U → Plane := fun u => (e u).val
  have hz : IsOpenEmbedding z := hV.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  let coeE := hz.toOpenPartialHomeomorph z
  let F0 := coeU.symm.trans coeE
  have hs : F0.source=U := by simp [F0,coeU,coeE,IsOpenEmbedding.toOpenPartialHomeomorph_target]
  have hValue (x : S) (hx : x ∈ U) : F0 x=(e ⟨x,hx⟩).val := by
    have hu : coeU.symm x=⟨x,hx⟩ :=
      hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv (x := ⟨x,hx⟩)
    change z (coeU.symm x)=_
    rw [hu]
  have hfS : range f ⊆ F0.source := hs.symm ▸ hfU
  have hFMark : Disjoint F0.source (M.cover.branch : Set S) := hs.symm ▸ hMark
  have hFAxis (x : S) (hx : x ∈ F0.source) : x ∈ c.val.image ↔ F0 x 1=0 := by
    rw [hValue x (hs ▸ hx)]
    exact hAxis ⟨x,hs ▸ hx⟩
  have hFCoord (t : Interval) : F0 (f t)=Plane.mk (χ t) 0 := by
    rw [hValue _ (hfU (Set.mem_range_self t))]
    exact hCoord t
  rcases hχ with hχ|hχ
  · exact ⟨F0,χ,hχ,hfS,hFMark,hFAxis,hFCoord⟩
  · let N : Plane ≃ₜ Plane := {
      toFun := fun z => Plane.mk (-z 0) (z 1)
      invFun := fun z => Plane.mk (-z 0) (z 1)
      left_inv := by intro z; ext i; fin_cases i <;> simp
      right_inv := by intro z; ext i; fin_cases i <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let F := F0.transHomeomorph N
    let χ' : C(Interval,ℝ) := ⟨fun t => -χ t,χ.continuous.neg⟩
    have hχ' : StrictMono χ' := by
      intro a b hab
      exact neg_lt_neg (hχ hab)
    refine ⟨F,χ',hχ',hfS,hFMark,?_,?_⟩
    · intro x hx
      exact hFAxis x hx
    · intro t
      change N (F0 (f t))=Plane.mk (-χ t) 0
      rw [hFCoord]
      rfl

end CurveComplex.HyperellipticModel
