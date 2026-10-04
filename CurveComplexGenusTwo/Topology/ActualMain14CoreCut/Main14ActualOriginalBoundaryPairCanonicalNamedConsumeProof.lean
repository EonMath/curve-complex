import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14RecoveryActualRawCorePairAmbientMotionFastLocalNamedPROVED
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenSphereAnnulusExteriorPartitionLocal
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualEmbeddedAnnulusComplementComponentLocal
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenCylinderExteriorShrinkLocal
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenCylinderSupportedCollarCalibrationLocalNamedPROVED
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.TerminalAnnulusMotionPROVED
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualConfinedCylinderCoordinateTransportLocalNamedPROVED
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.TerminalAnnulusMotionPROVED
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenCoreConfinedComparisonSourceLocalNamedPROVED
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualIntervalTwoLevelCalibrationLocal
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenCoreConfinedComparisonSourceLocalNamedPROVED
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualConfinedCylinderCoordinateTransportLocalNamedPROVED
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualConfinedCylinderCoordinateTransportLocalNamedPROVED
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenCoreSmallComparisonCylindersWithGapLocal
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenCoreNestedHalfCylindersWithRangeLocal
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualEmbeddedAnnulusComplementComponentLocal
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualThreeGivenAnnuliCutConfinementLocal
import CurveComplexGenusTwo.Topology.ActualMarkedAnnulus.Main14ActualMarkedAnnulusPackage
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenToConstructedCommonPairLocal
open Lean Elab Tactic in
elab "audit_main14_base3 " ts:tacticSeq : tactic => do
  let g ← getMainGoal
  evalTacticSeq ts
  let pf ← instantiateMVars (mkMVar g)
  let mut found : NameSet := {}
  for c in pf.getUsedConstants do
    for ax in ← collectAxioms c do
      found := found.insert ax
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in Main14 local source proof: {ax}"
  logInfo m!"Main14 local proof axiom audit: {found.toList}"

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]

set_option maxHeartbeats 30000000 in
theorem actual_nonloop_regular_neighborhood_boundaries_isotopic_of_cores
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (Na : ArcNeighborhood a) (Nb : ArcNeighborhood b)
    (pa : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ Na.closedSet)
    (pb : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ Nb.closedSet)
    (hca : (fun z => (pa z : S)) '' ClassificationSchoenflies.standardArcCore = a.image)
    (hcb : (fun z => (pb z : S)) '' ClassificationSchoenflies.standardArcCore = b.image)
    (hup : AmbientIsotopy.Rel (M.cover.projection ⁻¹' a.image)
      (M.cover.projection ⁻¹' b.image)) :
    AmbientIsotopy.Rel (M.cover.projection ⁻¹' Na.boundary.image)
      (M.cover.projection ⁻¹' Nb.boundary.image) := by
  have ht : ∃ h : E ≃ₜ E, ∃ H : Circle × Interval ≃ₜ h '' (M.cover.projection ⁻¹' Na.closedSet),
        Set.range (fun z : Circle => (H (z,⟨1/2,by norm_num⟩)).val) =
          M.cover.projection ⁻¹' b.image ∧
        Set.range (fun z : Circle => (H (z,0)).val) ∪
          Set.range (fun z : Circle => (H (z,1)).val) =
          h '' (M.cover.projection ⁻¹' Na.boundary.image) ∧
        AmbientIsotopy.Rel (M.cover.projection ⁻¹' Na.boundary.image)
          (h '' (M.cover.projection ⁻¹' Na.boundary.image)) := by
    all_goals
      obtain ⟨K,hK⟩ := hup
      obtain ⟨h,hh⟩ := K.homeomorphism_at 1
      have hf : (h : E → E) = K.finalMap := by
        funext x
        exact hh x
      obtain ⟨A,hAc,hAb⟩ :=
        M.actual_nonloop_regular_neighborhood_lift_core_annulus a Na pa hca
      let H := A.trans (h.image (M.cover.projection ⁻¹' Na.closedSet))
      have he (t : Interval) : Set.range (fun z : Circle => (H (z,t)).val) =
          h '' Set.range (fun z : Circle => (A (z,t)).val) := by
        change Set.range (fun z : Circle => h (A (z,t)).val) = _
        exact Set.range_comp h (fun z : Circle => (A (z,t)).val)
      refine ⟨h,H,?_,?_,?_⟩
      · rw [he,hAc,hf]
        exact hK
      · rw [he,he,← Set.image_union,hAb]
      · exact ⟨K,by rw [← hf]⟩
  obtain ⟨h,T,hTc,hTb,hmove⟩ := ht
  obtain ⟨B,hBc,hBb⟩ := M.actual_nonloop_regular_neighborhood_lift_core_annulus b Nb pb hcb
  have ha : ∃ r : Circle ≃ₜ Circle, ∀ z : Circle,
      (B (r z,⟨1/2,by norm_num⟩)).val = (T (z,⟨1/2,by norm_num⟩)).val := by
    all_goals
      let c : Interval := ⟨1/2,by norm_num⟩
      have hTce : Topology.IsEmbedding (fun z : Circle => (T (z,c)).val) :=
        Topology.IsEmbedding.subtypeVal.comp
          (T.isEmbedding.comp (isEmbedding_prodMkLeft c))
      have hBce : Topology.IsEmbedding (fun z : Circle => (B (z,c)).val) :=
        Topology.IsEmbedding.subtypeVal.comp
          (B.isEmbedding.comp (isEmbedding_prodMkLeft c))
      let ea : Circle ≃ₜ (M.cover.projection ⁻¹' b.image) := hTce.toHomeomorph.trans (Homeomorph.setCongr hTc)
      let eb : Circle ≃ₜ (M.cover.projection ⁻¹' b.image) := hBce.toHomeomorph.trans (Homeomorph.setCongr hBc)
      refine ⟨ea.trans eb.symm,?_⟩
      intro z
      have hh := congrArg Subtype.val (eb.apply_symm_apply (ea z))
      exact hh
  obtain ⟨r,hr⟩ := ha
  have hband : ∃ V : Set Interval, IsOpen V ∧ (⟨1/2,by norm_num⟩ : Interval) ∈ V ∧
        ∀ z : Circle, ∀ t ∈ V,
          M.cover.projection (T (z,t)).val ∈ interior Nb.closedSet := by
    all_goals
      let c : Interval := ⟨1/2,by norm_num⟩
      let f : Circle × Interval → S := fun p => M.cover.projection (T p).val
      have hc : Continuous f := M.cover.projection_continuous.comp
        (continuous_subtype_val.comp T.continuous)
      have hopen : IsOpen (f ⁻¹' interior Nb.closedSet) := isOpen_interior.preimage hc
      have hmid : (Set.univ : Set Circle) ×ˢ {c} ⊆ f ⁻¹' interior Nb.closedSet := by
        rintro ⟨z,t⟩ ⟨_,ht⟩
        have he : t = c := ht
        subst t
        have hh : (T (z,c)).val ∈ M.cover.projection ⁻¹' b.image := by
          rw [← hTc]
          exact Set.mem_range_self z
        exact Nb.arc_inside hh
      obtain ⟨W,V,hW,hV,hall,hcV,hWV⟩ :=
        generalized_tube_lemma (isCompact_univ : IsCompact (Set.univ : Set Circle))
          (isCompact_singleton : IsCompact ({c} : Set Interval)) hopen hmid
      refine ⟨V,hV,hcV (Set.mem_singleton c),?_⟩
      intro z t ht
      exact hWV ⟨hall (Set.mem_univ z),ht⟩
  obtain ⟨V,hV,hcV,hbandV⟩ := hband
  have htransition : ∃ F : C(Circle × V, Circle × Interval), Topology.IsEmbedding F ∧
        (∀ z : Circle, ∀ t : V, (B (F (z,t))).val = (T (z,t.val)).val) ∧
        ∀ z : Circle, F (z,⟨⟨1/2,by norm_num⟩,hcV⟩) = (r z,⟨1/2,by norm_num⟩) := by
    all_goals
      let f : Circle × V → M.cover.projection ⁻¹' Nb.closedSet := fun p =>
        ⟨(T (p.1,p.2.val)).val, (show M.cover.projection (T (p.1,p.2.val)).val ∈ Nb.closedSet from interior_subset (hbandV p.1 p.2.val p.2.property))⟩
      have hfc : Continuous f :=
        (continuous_subtype_val.comp (T.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))).subtype_mk _
      let F : C(Circle × V, Circle × Interval) := ⟨fun p => B.symm (f p),
        B.symm.continuous.comp hfc⟩
      have hfe : Topology.IsEmbedding f := by
        apply Topology.IsEmbedding.of_comp hfc continuous_subtype_val
        change Topology.IsEmbedding (fun p : Circle × V => (T (p.1,p.2.val)).val)
        exact Topology.IsEmbedding.subtypeVal.comp (T.isEmbedding.comp
          ((Homeomorph.refl Circle).isEmbedding.prodMap Topology.IsEmbedding.subtypeVal))
      refine ⟨F,B.symm.isEmbedding.comp hfe,?_,?_⟩
      · intro z t
        exact congrArg Subtype.val (B.apply_symm_apply (f (z,t)))
      · intro z
        apply B.injective
        apply Subtype.ext
        change (B (B.symm (f (z,⟨⟨1/2,by norm_num⟩,hcV⟩)))).val = _
        rw [B.apply_symm_apply]
        exact (hr z).symm
  obtain ⟨F,hFe,hF,hFcore⟩ := htransition
  let U : Set E := h '' (M.cover.projection ⁻¹' Na.closedSet)
  have hcommon : ∃ W : Set E, ∃ A : Circle × Interval ≃ₜ W,
        W ⊆ U ∧ W ⊆ M.cover.projection ⁻¹' interior Nb.closedSet ∧
        Disjoint W (Set.range (fun z : Circle => (T (z,0)).val) ∪
          Set.range (fun z : Circle => (T (z,1)).val)) ∧
        Disjoint W (M.cover.projection ⁻¹' Nb.boundary.image) ∧
        Set.range (fun z : Circle => (A (z,⟨1/2,by norm_num⟩)).val) =
          M.cover.projection ⁻¹' b.image ∧
        (∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧ ∀ z (u : Interval),
          ∃ v : Interval, (v:ℝ) = 1/2+δ*(2*(u:ℝ)-1) ∧
            (A (z,u)).val = (T (z,v)).val) ∧
        ∃ H : AmbientIsotopy E, ∃ J : C(Interval × E,E),
          H.finalMap ''
            (Set.range (fun z : Circle => (A (z,⟨1/6,by norm_num⟩)).val) ∪
              Set.range (fun z : Circle => (A (z,⟨5/6,by norm_num⟩)).val)) =
            Set.range (fun z : Circle => (A (z,⟨1/3,by norm_num⟩)).val) ∪
              Set.range (fun z : Circle => (A (z,⟨2/3,by norm_num⟩)).val) ∧
          (∀ t z, H.map (t,(A (z,⟨1/2,by norm_num⟩)).val) =
            (A (z,⟨1/2,by norm_num⟩)).val) ∧
          (∀ t x, x ∉ W → H.map (t,x) = x) ∧
          (∀ t x, J (t,H.map (t,x)) = x) ∧
          (∀ t x, H.map (t,J (t,x)) = x) := by
    all_goals
      have hMove (U : Set E) (T : Circle × Interval ≃ₜ U) : ∃ H : AmbientIsotopy E, ∃ J : C(Interval × E,E),
            H.finalMap ''
              (Set.range (fun z : Circle => (T (z,⟨1/6,by norm_num⟩)).val) ∪
                Set.range (fun z : Circle => (T (z,⟨5/6,by norm_num⟩)).val)) =
              Set.range (fun z : Circle => (T (z,⟨1/3,by norm_num⟩)).val) ∪
                Set.range (fun z : Circle => (T (z,⟨2/3,by norm_num⟩)).val) ∧
            (∀ t z, H.map (t,(T (z,⟨1/2,by norm_num⟩)).val) =
              (T (z,⟨1/2,by norm_num⟩)).val) ∧
            (∀ t x, x ∉ U → H.map (t,x) = x) ∧
            (∀ t x, J (t,H.map (t,x)) = x) ∧
            (∀ t x, H.map (t,J (t,x)) = x) := by
        letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
        have actual_embedded_annulus_interior_isOpen
            (B : Circle × Interval → E) (hB : IsEmbedding B) :
            IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
          rw [isOpen_iff_forall_mem_open]
          rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
          have hu0 : (0:ℝ) < (u : ℝ) := hu.1
          have hu1 : (u : ℝ) < 1 := hu.2
          let lo : ℝ := (u : ℝ)/2
          let hi : ℝ := ((u : ℝ)+1)/2
          have hlu : lo < (u : ℝ) := by dsimp [lo]; exact half_lt_self (by exact hu.1)
          have huh : (u : ℝ) < hi := by dsimp [hi]; linarith [hu1]
          have hl0 : 0 < lo := by dsimp [lo]; exact half_pos (by exact hu.1)
          have hh1 : hi < 1 := by dsimp [hi]; linarith [hu1]
          have hlh : lo ≤ hi := (hlu.trans huh).le
          let width : ℝ → Interval := fun s =>
            ⟨(Set.projIcc lo hi hlh s : ℝ),
              ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
                le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
          have hwc : Continuous width :=
            (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
          let θ := Complex.arg (z : ℂ)
          let f : EuclideanSpace ℝ (Fin 2) → E := fun x => B (Circle.exp (x 1),width (x 0))
          have hfc : Continuous f := hB.continuous.comp
            ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
          let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
            {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
          have hΩ : IsOpen Ω :=
            (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
          have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
              (width (x 0) : ℝ) = x 0 :=
            congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
          have hfi : Set.InjOn f Ω := by
            intro x hx w hw he
            have hp := hB.injective he
            have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
              (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
              ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
            have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
            change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
            rw [hclip x hx,hclip w hw] at hwidth
            ext i
            fin_cases i
            · exact hwidth
            · exact hangle
          have hopen : IsOpen (f '' Ω) :=
            CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
          have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) := by
            rintro q ⟨x,hx,rfl⟩
            refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
            · change 0 < (width (x 0) : ℝ)
              rw [hclip x hx]
              exact hl0.trans hx.1.1
            · change (width (x 0) : ℝ) < 1
              rw [hclip x hx]
              exact hx.1.2.trans hh1
          let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
          have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
          have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
          have hx : x ∈ Ω := by
            refine ⟨?_,?_⟩
            · rw [hx0]; exact ⟨hlu,huh⟩
            · rw [hx1]; constructor <;> linarith [Real.pi_pos]
          have hwu : width (u : ℝ) = u := by
            apply Subtype.ext
            change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
            exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
          have hpoint : f x = B (z,u) := by
            dsimp [f]
            rw [hx0,hx1,hwu,Circle.exp_arg]
          exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩
        let L : Circle × Interval → E := fun p =>
          (T (p.1,⟨(p.2 : ℝ)/2,by constructor <;> linarith [p.2.property.1,p.2.property.2]⟩)).val
        let R : Circle × Interval → E := fun p =>
          (T (p.1,⟨1-(p.2 : ℝ)/2,by constructor <;> linarith [p.2.property.1,p.2.property.2]⟩)).val
        have hLc : Continuous L := by dsimp [L]; fun_prop
        have hRc : Continuous R := by dsimp [R]; fun_prop
        have hLi : Function.Injective L := by
          intro p q he
          have hh := T.injective (Subtype.ext he)
          apply Prod.ext
          · have hx := congrArg (fun x : Circle × Interval => x.1) hh
            exact hx
          · apply Subtype.ext
            have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
            change (p.2 : ℝ)/2 = (q.2 : ℝ)/2 at hc
            linarith
        have hRi : Function.Injective R := by
          intro p q he
          have hh := T.injective (Subtype.ext he)
          apply Prod.ext
          · have hx := congrArg (fun x : Circle × Interval => x.1) hh
            exact hx
          · apply Subtype.ext
            have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
            change 1-(p.2 : ℝ)/2 = 1-(q.2 : ℝ)/2 at hc
            linarith
        have hL : Topology.IsEmbedding L := (hLc.isClosedEmbedding hLi).isEmbedding
        have hR : Topology.IsEmbedding R := (hRc.isClosedEmbedding hRi).isEmbedding
        let UL := L '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
        let UR := R '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
        have hUL : IsOpen UL := actual_embedded_annulus_interior_isOpen L hL
        have hUR : IsOpen UR := actual_embedded_annulus_interior_isOpen R hR
        obtain ⟨K,V,hleft,hright,hzero,hone,hfinal⟩ := CurveComplex.G3Review.actual_circle_band_ambient_motion
        have hfixL (t : Interval) (y : Circle × Interval) (hy : L y ∉ UL) : K.map (t,y) = y := by
          by_cases hy0 : y.2 = 0
          · rw [show y = (y.1,0) from Prod.ext rfl hy0]
            exact hzero t y.1
          by_cases hy1 : y.2 = 1
          · rw [show y = (y.1,1) from Prod.ext rfl hy1]
            exact hone t y.1
          have h0 : (0 : Interval) < y.2 := lt_of_le_of_ne (by exact y.2.property.1) (fun he => hy0 he.symm)
          have h1 : y.2 < (1 : Interval) := lt_of_le_of_ne (by exact y.2.property.2) hy1
          exact False.elim (hy ⟨y,⟨Set.mem_univ _,h0,h1⟩,rfl⟩)
        have hfixR (t : Interval) (y : Circle × Interval) (hy : R y ∉ UR) : K.map (t,y) = y := by
          by_cases hy0 : y.2 = 0
          · rw [show y = (y.1,0) from Prod.ext rfl hy0]
            exact hzero t y.1
          by_cases hy1 : y.2 = 1
          · rw [show y = (y.1,1) from Prod.ext rfl hy1]
            exact hone t y.1
          have h0 : (0 : Interval) < y.2 := lt_of_le_of_ne (by exact y.2.property.1) (fun he => hy0 he.symm)
          have h1 : y.2 < (1 : Interval) := lt_of_le_of_ne (by exact y.2.property.2) hy1
          exact False.elim (hy ⟨y,⟨Set.mem_univ _,h0,h1⟩,rfl⟩)
        obtain ⟨HL,JL,hHL,hLout,hJLleft,hJLright⟩ :=
          CurveComplex.G3Review.actual_compact_embedded_motion_extension L hL UL hUL
            (Set.image_subset_range _ _) K V hleft hright hfixL
        obtain ⟨HR,JR,hHR,hRout,hJRleft,hJRright⟩ :=
          CurveComplex.G3Review.actual_compact_embedded_motion_extension R hR UR hUR
            (Set.image_subset_range _ _) K V hleft hright hfixR
        have hLow (z : Circle) (u : Interval) (hu : (u : ℝ) ≤ 1/2) : (T (z,u)).val ∉ UR := by
          rintro ⟨p,⟨_,hp⟩,he⟩
          have hh := T.injective (Subtype.ext he)
          have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
          change 1-(p.2 : ℝ)/2 = (u : ℝ) at hc
          have hp1 : (p.2 : ℝ) < 1 := hp.2
          linarith
        have hHigh (z : Circle) (u : Interval) (hu : 1/2 ≤ (u : ℝ)) : (T (z,u)).val ∉ UL := by
          rintro ⟨p,⟨_,hp⟩,he⟩
          have hh := T.injective (Subtype.ext he)
          have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
          change (p.2 : ℝ)/2 = (u : ℝ) at hc
          have hp1 : (p.2 : ℝ) < 1 := hp.2
          linarith
        let H : AmbientIsotopy E := {
          map := ⟨fun p => HR.map (p.1,HL.map (p.1,p.2)),HR.map.continuous.comp
            (continuous_fst.prodMk (HL.map.continuous.comp (continuous_fst.prodMk continuous_snd)))⟩
          homeomorphism_at := by
            intro t
            obtain ⟨l,hl⟩ := HL.homeomorphism_at t
            obtain ⟨r,hr⟩ := HR.homeomorphism_at t
            exact ⟨l.trans r,fun x => by change r (l x) = HR.map (t,HL.map (t,x)); rw [hl,hr]⟩
          at_zero := by
            intro x
            change HR.map (⟨0,by norm_num⟩,HL.map (⟨0,by norm_num⟩,x)) = x
            rw [HL.at_zero,HR.at_zero] }
        let J : C(Interval × E,E) := ⟨fun p => JL (p.1,JR (p.1,p.2)),JL.continuous.comp
          (continuous_fst.prodMk (JR.continuous.comp (continuous_fst.prodMk continuous_snd)))⟩
        have hLf (z : Circle) : HL.finalMap (T (z,⟨1/6,by norm_num⟩)).val =
            (T (z,⟨1/3,by norm_num⟩)).val := by
          have h := hHL 1 (z,⟨1/3,by norm_num⟩)
          have hk := hfinal z
          change K.map (1,(z,⟨1/3,by norm_num⟩)) = (z,⟨2/3,by norm_num⟩) at hk
          rw [hk] at h
          norm_num [AmbientIsotopy.finalMap,L] at h ⊢
          exact h
        have hRf (z : Circle) : HR.finalMap (T (z,⟨5/6,by norm_num⟩)).val =
            (T (z,⟨2/3,by norm_num⟩)).val := by
          have h := hHR 1 (z,⟨1/3,by norm_num⟩)
          have hk := hfinal z
          change K.map (1,(z,⟨1/3,by norm_num⟩)) = (z,⟨2/3,by norm_num⟩) at hk
          rw [hk] at h
          norm_num [AmbientIsotopy.finalMap,R] at h ⊢
          exact h
        have hHfL (z : Circle) : H.finalMap (T (z,⟨1/6,by norm_num⟩)).val =
            (T (z,⟨1/3,by norm_num⟩)).val := by
          change HR.finalMap (HL.finalMap _) = _
          rw [hLf]
          exact hRout 1 _ (hLow z _ (by norm_num))
        have hHfR (z : Circle) : H.finalMap (T (z,⟨5/6,by norm_num⟩)).val =
            (T (z,⟨2/3,by norm_num⟩)).val := by
          change HR.finalMap (HL.finalMap _) = _
          rw [show HL.finalMap (T (z,⟨5/6,by norm_num⟩)).val = (T (z,⟨5/6,by norm_num⟩)).val from
            hLout 1 _ (hHigh z _ (by norm_num))]
          exact hRf z
        refine ⟨H,J,?_,?_,?_,?_,?_⟩
        · rw [Set.image_union,← Set.range_comp,← Set.range_comp]
          exact congrArg₂ Set.union (congrArg Set.range (funext hHfL)) (congrArg Set.range (funext hHfR))
        · intro t z
          change HR.map (t,HL.map (t,_)) = _
          rw [hLout t _ (hHigh z _ (by norm_num)),hRout t _ (hLow z _ (by norm_num))]
        · intro t x hx
          have hxL : x ∉ UL := by
            rintro ⟨p,hp,rfl⟩
            exact hx (T _).property
          have hxR : x ∉ UR := by
            rintro ⟨p,hp,rfl⟩
            exact hx (T _).property
          change HR.map (t,HL.map (t,x)) = x
          rw [hLout t x hxL,hRout t x hxR]
        · intro t x
          change JL (t,JR (t,HR.map (t,HL.map (t,x)))) = x
          rw [hJRleft,hJLleft]
        · intro t x
          change HR.map (t,HL.map (t,JL (t,JR (t,x)))) = x
          rw [hJLright,hJRright]
      let c : Interval := ⟨1/2,by norm_num⟩
      let f : Circle × Interval → S := fun p => M.cover.projection (T p).val
      have hc : Continuous f := M.cover.projection_continuous.comp
        (continuous_subtype_val.comp T.continuous)
      have hopen : IsOpen (f ⁻¹' interior Nb.closedSet) := isOpen_interior.preimage hc
      have hmid : (Set.univ : Set Circle) ×ˢ {c} ⊆ f ⁻¹' interior Nb.closedSet := by
        rintro ⟨z,t⟩ ⟨_,ht⟩
        have he : t = c := ht
        subst t
        have hh : (T (z,c)).val ∈ M.cover.projection ⁻¹' b.image := by
          rw [← hTc]
          exact Set.mem_range_self z
        exact Nb.arc_inside hh
      obtain ⟨D,V,hD,hV,hall,hcV,hDV⟩ :=
        generalized_tube_lemma (isCompact_univ : IsCompact (Set.univ : Set Circle))
          (isCompact_singleton : IsCompact ({c} : Set Interval)) hopen hmid
      have hbandV (z : Circle) (t : Interval) (ht : t ∈ V) :
          M.cover.projection (T (z,t)).val ∈ interior Nb.closedSet :=
        hDV ⟨hall (Set.mem_univ z),ht⟩
      let clip : ℝ → Interval := Set.projIcc 0 1 (by norm_num)
      have hclip : Continuous clip := continuous_projIcc
      have hpre : IsOpen (clip ⁻¹' V) := hV.preimage hclip
      have hhalf : (1/2 : ℝ) ∈ clip ⁻¹' V := by
        have hcclip : clip (1/2) = c := by
          exact Set.projIcc_of_mem (by norm_num) (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)
        change clip (1/2) ∈ V
        rw [hcclip]
        exact hcV (Set.mem_singleton c)
      obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hpre (1/2) hhalf
      let δ : ℝ := min (ε/2) (1/4)
      have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
      have hδsmall : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
      have hδquarter : δ ≤ 1/4 := min_le_right _ _
      let q : Interval → Interval := fun u =>
        ⟨1/2 + δ*(2*(u:ℝ)-1),by constructor <;> nlinarith [u.property.1,u.property.2]⟩
      have hqc : Continuous q := by dsimp [q]; fun_prop
      have hqi : Function.Injective q := by
        intro u v he
        apply Subtype.ext
        have hh := congrArg Subtype.val he
        change 1/2 + δ*(2*(u:ℝ)-1) = 1/2 + δ*(2*(v:ℝ)-1) at hh
        nlinarith
      have hqmid : q c = c := by apply Subtype.ext; dsimp [q,c]; ring
      have hqV (u : Interval) : q u ∈ V := by
        have hnear : (q u : ℝ) ∈ Metric.ball (1/2) ε := by
          rw [Metric.mem_ball,Real.dist_eq,abs_lt]
          dsimp [q]
          constructor <;> nlinarith [u.property.1,u.property.2]
        have hv := hball hnear
        change clip (q u : ℝ) ∈ V at hv
        rw [show clip (q u : ℝ) = q u from Set.projIcc_of_mem (by norm_num) (q u).property] at hv
        exact hv
      let B : Circle × Interval → E := fun p => (T (p.1,q p.2)).val
      have hBc : Continuous B := by dsimp [B]; fun_prop
      have hBi : Function.Injective B := by
        intro p w he
        have hh := T.injective (Subtype.ext he)
        apply Prod.ext
        · have hz := congrArg (fun x : Circle × Interval => x.1) hh
          exact hz
        · exact hqi (congrArg Prod.snd hh)
      letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
      have hBe : Topology.IsEmbedding B := (hBc.isClosedEmbedding hBi).isEmbedding
      let W := Set.range B
      let A : Circle × Interval ≃ₜ W := hBe.toHomeomorph
      have hA (p : Circle × Interval) : (A p).val = (T (p.1,q p.2)).val := rfl
      refine ⟨W,A,?_,?_,?_,?_,?_,⟨δ,hδ,hδquarter,fun z u => ⟨q u,rfl,rfl⟩⟩,hMove W A⟩
      · rintro x ⟨p,rfl⟩
        exact (T _).property
      · rintro x ⟨p,rfl⟩
        exact hbandV p.1 (q p.2) (hqV p.2)
      · apply Set.disjoint_left.mpr
        rintro x ⟨p,rfl⟩ (⟨z,he⟩ | ⟨z,he⟩)
        · have hh := T.injective (Subtype.ext he)
          have hs := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
          change 0 = 1/2 + δ*(2*(p.2:ℝ)-1) at hs
          nlinarith [p.2.property.1,p.2.property.2]
        · have hh := T.injective (Subtype.ext he)
          have hs := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
          change 1 = 1/2 + δ*(2*(p.2:ℝ)-1) at hs
          nlinarith [p.2.property.1,p.2.property.2]
      · apply Set.disjoint_left.mpr
        rintro x ⟨p,rfl⟩ hx
        have hin := hbandV p.1 (q p.2) (hqV p.2)
        have hfront : M.cover.projection (B p) ∈ frontier Nb.closedSet := by
          rw [← Nb.boundary_eq_frontier]
          exact hx
        exact Set.disjoint_left.mp disjoint_interior_frontier hin hfront
      · have hh : (fun z : Circle => (A (z,c)).val) =
            (fun z : Circle => (T (z,c)).val) := by
          funext z
          rw [hA,hqmid]
        exact (congrArg Set.range hh).trans hTc
  obtain ⟨W,A,hWU,hWN,hWdisT,hWdisNb,hAc,⟨δ,hδ,hδquarter,hAcoordinates⟩,HM,JM,hPair,hCoreFix,hOutside,hLeft,hRight⟩ := hcommon
  have hOuterFixed (t : Interval) (x : E)
      (hx : x ∈ h '' (M.cover.projection ⁻¹' Na.boundary.image) ∪
        (M.cover.projection ⁻¹' Nb.boundary.image)) : HM.map (t,x) = x := by
    apply hOutside t x
    intro hw
    rcases hx with hx | hx
    · have hxT : x ∈ Set.range (fun z : Circle => (T (z,0)).val) ∪
          Set.range (fun z : Circle => (T (z,1)).val) := by
        rw [hTb]
        exact hx
      exact Set.disjoint_left.mp hWdisT hw hxT
    · exact Set.disjoint_left.mp hWdisNb hw hx
  have hproper : ∃ G : C(Circle × Interval,Circle × Interval), Topology.IsEmbedding G ∧
        (∀ p, (B (G p)).val = (A p).val) ∧
        Set.range G ⊆ Set.univ ×ˢ Set.Ioo (0:Interval) 1 ∧
        ∃ r : Circle ≃ₜ Circle, ∀ z,
          G (z,⟨1/2,by norm_num⟩) = (r z,⟨1/2,by norm_num⟩) := by
    all_goals
      let f : Circle × Interval → M.cover.projection ⁻¹' Nb.closedSet := fun p =>
        ⟨(A p).val,(show M.cover.projection (A p).val ∈ Nb.closedSet from
          interior_subset (hWN (A p).property))⟩
      have hfc : Continuous f := (continuous_subtype_val.comp A.continuous).subtype_mk _
      let G : C(Circle × Interval,Circle × Interval) :=
        ⟨fun p => B.symm (f p),B.symm.continuous.comp hfc⟩
      have hfe : Topology.IsEmbedding f := by
        apply Topology.IsEmbedding.of_comp hfc continuous_subtype_val
        change Topology.IsEmbedding (fun p : Circle × Interval => (A p).val)
        exact Topology.IsEmbedding.subtypeVal.comp A.isEmbedding
      have hG (p : Circle × Interval) : (B (G p)).val = (A p).val :=
        congrArg Subtype.val (B.apply_symm_apply (f p))
      have hnobound (p : Circle × Interval) : (G p).2 ≠ 0 ∧ (G p).2 ≠ 1 := by
        constructor
        · intro he
          have hx : (A p).val ∈ M.cover.projection ⁻¹' Nb.boundary.image := by
            rw [← hBb]
            apply Or.inl
            refine ⟨(G p).1,?_⟩
            have hh : ((G p).1,0) = G p := Prod.ext rfl he.symm
            change (B ((G p).1,0)).val = (A p).val
            rw [hh,hG]
          have hi := hWN (A p).property
          have hf : M.cover.projection (A p).val ∈ frontier Nb.closedSet := by
            rw [← Nb.boundary_eq_frontier]
            exact hx
          exact Set.disjoint_left.mp disjoint_interior_frontier hi hf
        · intro he
          have hx : (A p).val ∈ M.cover.projection ⁻¹' Nb.boundary.image := by
            rw [← hBb]
            apply Or.inr
            refine ⟨(G p).1,?_⟩
            have hh : ((G p).1,1) = G p := Prod.ext rfl he.symm
            change (B ((G p).1,1)).val = (A p).val
            rw [hh,hG]
          have hi := hWN (A p).property
          have hf : M.cover.projection (A p).val ∈ frontier Nb.closedSet := by
            rw [← Nb.boundary_eq_frontier]
            exact hx
          exact Set.disjoint_left.mp disjoint_interior_frontier hi hf
      refine ⟨G,B.symm.isEmbedding.comp hfe,hG,?_,?_⟩
      · rintro p ⟨x,rfl⟩
        exact ⟨Set.mem_univ _,lt_of_le_of_ne
          (show (0:Interval) ≤ (G x).2 from (G x).2.property.1) (hnobound x).1.symm,
          lt_of_le_of_ne (show (G x).2 ≤ (1:Interval) from (G x).2.property.2) (hnobound x).2⟩
      · let c : Interval := ⟨1/2,by norm_num⟩
        have hAe : Topology.IsEmbedding (fun z : Circle => (A (z,c)).val) :=
          Topology.IsEmbedding.subtypeVal.comp (A.isEmbedding.comp (isEmbedding_prodMkLeft c))
        have hBe : Topology.IsEmbedding (fun z : Circle => (B (z,c)).val) :=
          Topology.IsEmbedding.subtypeVal.comp (B.isEmbedding.comp (isEmbedding_prodMkLeft c))
        let ea : Circle ≃ₜ (M.cover.projection ⁻¹' b.image) :=
          hAe.toHomeomorph.trans (Homeomorph.setCongr hAc)
        let eb : Circle ≃ₜ (M.cover.projection ⁻¹' b.image) :=
          hBe.toHomeomorph.trans (Homeomorph.setCongr hBc)
        refine ⟨ea.trans eb.symm,?_⟩
        intro z
        apply B.injective
        apply Subtype.ext
        rw [hG]
        exact (congrArg Subtype.val (eb.apply_symm_apply (ea z))).symm
  obtain ⟨G,hGe,hG,hGrange,rCommon,hGcore⟩ := hproper
  have hSides :
      ((∀ z (u : Interval), (u:ℝ) < 1/2 → ((G (z,u)).2:ℝ) < 1/2) ∧
        (∀ z (u : Interval), 1/2 < (u:ℝ) → 1/2 < ((G (z,u)).2:ℝ))) ∨
      ((∀ z (u : Interval), (u:ℝ) < 1/2 → 1/2 < ((G (z,u)).2:ℝ)) ∧
        (∀ z (u : Interval), 1/2 < (u:ℝ) → ((G (z,u)).2:ℝ) < 1/2)) := by
    all_goals
      have hSidesLocal (G : C(Circle × Interval,Circle × Interval))
          (hG : Topology.IsEmbedding G) (r : Circle ≃ₜ Circle)
          (hcore : ∀ z, G (z,⟨1/2,by norm_num⟩) = (r z,⟨1/2,by norm_num⟩))
          (hopen : IsOpen (G '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1))) :
          ((∀ z (u : Interval), (u:ℝ) < 1/2 → ((G (z,u)).2:ℝ) < 1/2) ∧
            (∀ z (u : Interval), 1/2 < (u:ℝ) → 1/2 < ((G (z,u)).2:ℝ))) ∨
          ((∀ z (u : Interval), (u:ℝ) < 1/2 → 1/2 < ((G (z,u)).2:ℝ)) ∧
            (∀ z (u : Interval), 1/2 < (u:ℝ) → ((G (z,u)).2:ℝ) < 1/2)) := by
        all_goals
          let c : Interval := ⟨1/2,by norm_num⟩
          let L := G '' (Set.univ ×ˢ Set.Iio c)
          let R := G '' (Set.univ ×ˢ Set.Ioi c)
          let O := G '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
          let Vlo : Set (Circle × Interval) := {p | p.2 < c}
          let Vhi : Set (Circle × Interval) := {p | c < p.2}
          have hLconn : IsPreconnected L := by
            letI : ConnectedSpace (Set.Ico (0:ℝ) (1/2)) :=
              Subtype.connectedSpace (isConnected_Ico (by norm_num : (0:ℝ) < 1/2))
            let f : Circle × Set.Ico (0:ℝ) (1/2) → Circle × Interval := fun p =>
              (p.1,⟨p.2.val,⟨p.2.property.1,p.2.property.2.le.trans (by norm_num)⟩⟩)
            have hf : Continuous f := by dsimp [f]; fun_prop
            have hr : Set.range (G ∘ f) = L := by
              ext p
              constructor
              · rintro ⟨⟨z,u⟩,rfl⟩
                exact ⟨f (z,u),⟨Set.mem_univ _,u.property.2⟩,rfl⟩
              · rintro ⟨⟨z,u⟩,⟨_,hu⟩,rfl⟩
                exact ⟨(z,⟨u.val,⟨u.property.1,hu⟩⟩),rfl⟩
            rw [← hr]
            exact (isConnected_range (G.continuous.comp hf)).isPreconnected
          have hRconn : IsPreconnected R := by
            letI : ConnectedSpace (Set.Ioc (1/2:ℝ) 1) :=
              Subtype.connectedSpace (isConnected_Ioc (by norm_num : (1/2:ℝ) < 1))
            let f : Circle × Set.Ioc (1/2:ℝ) 1 → Circle × Interval := fun p =>
              (p.1,⟨p.2.val,⟨(by norm_num : (0:ℝ) ≤ 1/2).trans p.2.property.1.le,p.2.property.2⟩⟩)
            have hf : Continuous f := by dsimp [f]; fun_prop
            have hr : Set.range (G ∘ f) = R := by
              ext p
              constructor
              · rintro ⟨⟨z,u⟩,rfl⟩
                exact ⟨f (z,u),⟨Set.mem_univ _,u.property.1⟩,rfl⟩
              · rintro ⟨⟨z,u⟩,⟨_,hu⟩,rfl⟩
                exact ⟨(z,⟨u.val,⟨hu,u.property.2⟩⟩),rfl⟩
            rw [← hr]
            exact (isConnected_range (G.continuous.comp hf)).isPreconnected
          have havoid (z : Circle) (u : Interval) (hu : u ≠ c) : (G (z,u)).2 ≠ c := by
            intro he
            let w := r.symm (G (z,u)).1
            have hg : G (w,c) = G (z,u) := by
              rw [hcore]
              exact Prod.ext (r.apply_symm_apply _) he.symm
            exact hu (congrArg Prod.snd (hG.injective hg)).symm
          have hsub (D : Set (Circle × Interval))
              (hD : ∀ p ∈ D, p.2 ≠ c) : D ⊆ Vlo ∪ Vhi := by
            intro p hp
            exact lt_or_gt_of_ne (hD p hp)
          have hdis : Disjoint Vlo Vhi := by
            apply Set.disjoint_left.mpr
            intro p hp hq
            change p.2 < c at hp
            change c < p.2 at hq
            exact lt_asymm hp hq
          have hld : L ⊆ Vlo ∨ L ⊆ Vhi :=
            IsPreconnected.subset_or_subset (isOpen_Iio.preimage continuous_snd)
              (isOpen_Ioi.preimage continuous_snd)
              hdis
              (hsub L (by rintro _ ⟨⟨z,u⟩,⟨_,hu⟩,rfl⟩; exact havoid z u hu.ne)) hLconn
          have hrd : R ⊆ Vlo ∨ R ⊆ Vhi :=
            IsPreconnected.subset_or_subset (isOpen_Iio.preimage continuous_snd)
              (isOpen_Ioi.preimage continuous_snd)
              hdis
              (hsub R (by rintro _ ⟨⟨z,u⟩,⟨_,hu⟩,rfl⟩; exact havoid z u hu.ne')) hRconn
          have hmid : (r 1,c) ∈ O := ⟨(1,c),⟨Set.mem_univ _,by change (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1; norm_num⟩,hcore 1⟩
          have hnotlo : ¬ (L ⊆ Vlo ∧ R ⊆ Vlo) := by
            rintro ⟨hl,hr⟩
            have hO : ∀ p ∈ O, p.2 ≤ c := by
              rintro _ ⟨⟨z,u⟩,hu,rfl⟩
              rcases lt_trichotomy u c with hh | hh | hh
              · exact (hl ⟨(z,u),⟨Set.mem_univ _,hh⟩,rfl⟩).le
              · rw [hh,hcore]
              · exact (hr ⟨(z,u),⟨Set.mem_univ _,hh⟩,rfl⟩).le
            have hc : (r 1,c) ∈ closure ((Set.univ : Set Circle) ×ˢ Set.Ioo c 1) := by
              rw [closure_prod_eq,closure_univ,closure_Ioo (show c ≠ 1 by intro hh; have hv := congrArg Subtype.val hh; norm_num [c] at hv)]
              exact ⟨Set.mem_univ _,le_rfl,by change (1/2:ℝ) ≤ 1; norm_num⟩
            obtain ⟨p,hpO,hp⟩ := mem_closure_iff.mp hc O hopen hmid
            exact not_lt_of_ge (hO p hpO) hp.2.1
          have hnothi : ¬ (L ⊆ Vhi ∧ R ⊆ Vhi) := by
            rintro ⟨hl,hr⟩
            have hO : ∀ p ∈ O, c ≤ p.2 := by
              rintro _ ⟨⟨z,u⟩,hu,rfl⟩
              rcases lt_trichotomy u c with hh | hh | hh
              · exact (hl ⟨(z,u),⟨Set.mem_univ _,hh⟩,rfl⟩).le
              · rw [hh,hcore]
              · exact (hr ⟨(z,u),⟨Set.mem_univ _,hh⟩,rfl⟩).le
            have hc : (r 1,c) ∈ closure ((Set.univ : Set Circle) ×ˢ Set.Ioo 0 c) := by
              rw [closure_prod_eq,closure_univ,closure_Ioo (show (0:Interval) ≠ c by intro hh; have hv := congrArg Subtype.val hh; norm_num [c] at hv)]
              exact ⟨Set.mem_univ _,by change (0:ℝ) ≤ 1/2; norm_num,le_rfl⟩
            obtain ⟨p,hpO,hp⟩ := mem_closure_iff.mp hc O hopen hmid
            exact not_lt_of_ge (hO p hpO) hp.2.2
          rcases hld with hl | hl <;> rcases hrd with hr | hr
          · exact False.elim (hnotlo ⟨hl,hr⟩)
          · exact Or.inl ⟨fun z u hu => hl ⟨(z,u),⟨Set.mem_univ _,hu⟩,rfl⟩,
              fun z u hu => hr ⟨(z,u),⟨Set.mem_univ _,hu⟩,rfl⟩⟩
          · exact Or.inr ⟨fun z u hu => hl ⟨(z,u),⟨Set.mem_univ _,hu⟩,rfl⟩,
              fun z u hu => hr ⟨(z,u),⟨Set.mem_univ _,hu⟩,rfl⟩⟩
          · exact False.elim (hnothi ⟨hl,hr⟩)
      have actual_embedded_annulus_interior_isOpen
          (B : Circle × Interval → E) (hB : IsEmbedding B) :
          IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
        rw [isOpen_iff_forall_mem_open]
        rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
        have hu0 : (0:ℝ) < (u : ℝ) := hu.1
        have hu1 : (u : ℝ) < 1 := hu.2
        let lo : ℝ := (u : ℝ)/2
        let hi : ℝ := ((u : ℝ)+1)/2
        have hlu : lo < (u : ℝ) := by dsimp [lo]; exact half_lt_self (by exact hu.1)
        have huh : (u : ℝ) < hi := by dsimp [hi]; linarith [hu1]
        have hl0 : 0 < lo := by dsimp [lo]; exact half_pos (by exact hu.1)
        have hh1 : hi < 1 := by dsimp [hi]; linarith [hu1]
        have hlh : lo ≤ hi := (hlu.trans huh).le
        let width : ℝ → Interval := fun s =>
          ⟨(Set.projIcc lo hi hlh s : ℝ),
            ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
              le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
        have hwc : Continuous width :=
          (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
        let θ := Complex.arg (z : ℂ)
        let f : EuclideanSpace ℝ (Fin 2) → E := fun x => B (Circle.exp (x 1),width (x 0))
        have hfc : Continuous f := hB.continuous.comp
          ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
        let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
          {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
        have hΩ : IsOpen Ω :=
          (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
        have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
            (width (x 0) : ℝ) = x 0 :=
          congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
        have hfi : Set.InjOn f Ω := by
          intro x hx w hw he
          have hp := hB.injective he
          have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
            (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
            ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
          have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
          change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
          rw [hclip x hx,hclip w hw] at hwidth
          ext i
          fin_cases i
          · exact hwidth
          · exact hangle
        have hopen : IsOpen (f '' Ω) :=
          CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
        have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) := by
          rintro q ⟨x,hx,rfl⟩
          refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
          · change 0 < (width (x 0) : ℝ)
            rw [hclip x hx]
            exact hl0.trans hx.1.1
          · change (width (x 0) : ℝ) < 1
            rw [hclip x hx]
            exact hx.1.2.trans hh1
        let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
        have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
        have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
        have hx : x ∈ Ω := by
          refine ⟨?_,?_⟩
          · rw [hx0]; exact ⟨hlu,huh⟩
          · rw [hx1]; constructor <;> linarith [Real.pi_pos]
        have hwu : width (u : ℝ) = u := by
          apply Subtype.ext
          change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
          exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
        have hpoint : f x = B (z,u) := by
          dsimp [f]
          rw [hx0,hx1,hwu,Circle.exp_arg]
        exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩
      have hAo : IsOpen ((fun p : Circle × Interval => (A p).val) ''
          (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) :=
        actual_embedded_annulus_interior_isOpen _
          (Topology.IsEmbedding.subtypeVal.comp A.isEmbedding)
      have hEq : G '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) =
          (fun p : Circle × Interval => (B p).val) ⁻¹'
            ((fun p : Circle × Interval => (A p).val) ''
              (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
        ext p
        constructor
        · rintro ⟨w,hw,rfl⟩
          exact ⟨w,hw,(hG w).symm⟩
        · rintro ⟨w,hw,he⟩
          exact ⟨w,hw,B.injective (Subtype.ext ((hG w).trans he))⟩
      have hGo : IsOpen (G '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
        rw [hEq]
        exact hAo.preimage (continuous_subtype_val.comp B.continuous)
      exact hSidesLocal G hGe rCommon hGcore hGo
  have hFamily (U V : Set E) (A : Circle × Interval ≃ₜ U)
      (B : Circle × Interval ≃ₜ V)
      (G : C(Circle × Interval,Circle × Interval))
      (hGe : Topology.IsEmbedding G)
      (hG : ∀ p, (B (G p)).val = (A p).val)
      (r : Circle ≃ₜ Circle)
      (hcore : ∀ z, G (z,⟨1/2,by norm_num⟩) = (r z,⟨1/2,by norm_num⟩))
      (hsides :
        ((∀ z (u : Interval), (u:ℝ) < 1/2 → ((G (z,u)).2:ℝ) < 1/2) ∧
          (∀ z (u : Interval), 1/2 < (u:ℝ) → 1/2 < ((G (z,u)).2:ℝ))) ∨
        ((∀ z (u : Interval), (u:ℝ) < 1/2 → 1/2 < ((G (z,u)).2:ℝ)) ∧
          (∀ z (u : Interval), 1/2 < (u:ℝ) → ((G (z,u)).2:ℝ) < 1/2))) :
      ∃ F0 F1 : C(Interval × Circle,E),
        (∀ z, F0 (0,z) = (A (z,0)).val) ∧
        (∀ z, F1 (0,z) = (A (z,1)).val) ∧
        Set.range (fun z => F0 (1,z)) ∪ Set.range (fun z => F1 (1,z)) =
          Set.range (fun z : Circle => (B (z,⟨1/4,by norm_num⟩)).val) ∪
            Set.range (fun z : Circle => (B (z,⟨3/4,by norm_num⟩)).val) ∧
        (∀ t, Topology.IsEmbedding (fun z => F0 (t,z)) ∧ Topology.IsEmbedding (fun z => F1 (t,z))) ∧
        (∀ t, Disjoint (Set.range (fun z => F0 (t,z)))
          (Set.range (fun z => F1 (t,z)))) ∧
        (∀ t, Disjoint (Set.range (fun z => F0 (t,z)) ∪ Set.range (fun z => F1 (t,z)))
          (Set.range (fun z : Circle => (B (z,⟨1/2,by norm_num⟩)).val))) := by
    all_goals
      let c : Interval := ⟨1/2,by norm_num⟩
      let q : Interval := ⟨1/4,by norm_num⟩
      let s : Interval := ⟨3/4,by norm_num⟩
      let w (t u : Interval) : Interval :=
        ⟨(1-(t:ℝ))*(u:ℝ)+(t:ℝ)/2,by constructor <;> nlinarith [t.property.1,t.property.2,u.property.1,u.property.2]⟩
      -- Both source levels move toward the SAME midpoint of the actual G.
      -- A positive affine map of the TARGET height retains injectivity of every slice.
      let f (a b : Interval) : C(Interval × Circle,Circle × Interval) :=
        ⟨fun p => ((G (p.2,w p.1 a)).1,
          ⟨(1-(p.1:ℝ)/2)*((G (p.2,w p.1 a)).2:ℝ)+(p.1:ℝ)*(b:ℝ)/2,by
            constructor <;> nlinarith [p.1.property.1,p.1.property.2,b.property.1,b.property.2,
              (G (p.2,w p.1 a)).2.property.1,(G (p.2,w p.1 a)).2.property.2]⟩),by dsimp [w]; fun_prop⟩
      have hf0 (a b : Interval) (z : Circle) : f a b (0,z) = G (z,a) := by
        have hw : w 0 a = a := Subtype.ext (by simp [w])
        apply Prod.ext
        · simp [f,hw]
        · apply Subtype.ext
          simp [f,hw]
      have hf1 (a b : Interval) (z : Circle) :
          f a b (1,z) = (r z,⟨1/4+(b:ℝ)/2,by constructor <;> linarith [b.property.1,b.property.2]⟩) := by
        have hw : w 1 a = c := Subtype.ext (by simp [w,c])
        apply Prod.ext
        · change (G (z,w 1 a)).1 = r z
          rw [hw]
          exact congrArg Prod.fst (hcore z)
        · apply Subtype.ext
          have hc : ((G (z,c)).2:ℝ) = 1/2 := congrArg (fun p : Circle × Interval => (p.2:ℝ)) (hcore z)
          change (1-(1:ℝ)/2)*((G (z,w 1 a)).2:ℝ)+(1:ℝ)*(b:ℝ)/2 = _
          rw [hw,hc]
          ring
      have hfi (a b t : Interval) : Topology.IsEmbedding (fun z : Circle => f a b (t,z)) := by
        have hc : Continuous (fun z : Circle => f a b (t,z)) :=
          (f a b).continuous.comp (continuous_const.prodMk continuous_id)
        have hi : Function.Injective (fun z : Circle => f a b (t,z)) := by
          intro z z' he
          have hz := congrArg Prod.fst he
          have hv := congrArg (fun p : Circle × Interval => (p.2:ℝ)) he
          have hfactor : 0 < 1-(t:ℝ)/2 := by linarith [t.property.2]
          have hheight : ((G (z,w t a)).2:ℝ) = ((G (z',w t a)).2:ℝ) := by
            change (1-(t:ℝ)/2)*((G (z,w t a)).2:ℝ)+(t:ℝ)*(b:ℝ)/2 =
              (1-(t:ℝ)/2)*((G (z',w t a)).2:ℝ)+(t:ℝ)*(b:ℝ)/2 at hv
            exact (mul_left_cancel₀ hfactor.ne' (add_right_cancel hv))
          have hg := hGe.injective (Prod.ext hz (Subtype.ext hheight))
          exact congrArg Prod.fst hg
        exact (hc.isClosedEmbedding hi).isEmbedding
      have hlo (a : Interval)
          (ha : ∀ t : Interval, (t:ℝ) < 1 → ∀ z, ((G (z,w t a)).2:ℝ) < 1/2)
          (t : Interval) (z : Circle) : ((f a 0 (t,z)).2:ℝ) < 1/2 := by
        by_cases ht : (t:ℝ) = 1
        · have htI : t = 1 := Subtype.ext ht
          rw [htI,hf1]
          change (1/4:ℝ)+(0:ℝ)/2 < 1/2
          norm_num
        · have ht1 : (t:ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
          have hh := ha t ht1 z
          change (1-(t:ℝ)/2)*((G (z,w t a)).2:ℝ)+(t:ℝ)*(0:ℝ)/2 < 1/2
          have hfactor : 0 < 1-(t:ℝ)/2 := by linarith [t.property.2]
          nlinarith [mul_pos hfactor (sub_pos.mpr hh),t.property.1]
      have hhi (a : Interval)
          (ha : ∀ t : Interval, (t:ℝ) < 1 → ∀ z, 1/2 < ((G (z,w t a)).2:ℝ))
          (t : Interval) (z : Circle) : 1/2 < ((f a 1 (t,z)).2:ℝ) := by
        by_cases ht : (t:ℝ) = 1
        · have htI : t = 1 := Subtype.ext ht
          rw [htI,hf1]
          change (1/2:ℝ) < 1/4+(1:ℝ)/2
          norm_num
        · have ht1 : (t:ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
          have hh := ha t ht1 z
          change 1/2 < (1-(t:ℝ)/2)*((G (z,w t a)).2:ℝ)+(t:ℝ)*(1:ℝ)/2
          have hfactor : 0 < 1-(t:ℝ)/2 := by linarith [t.property.2]
          nlinarith [mul_pos hfactor (sub_pos.mpr hh),t.property.1]
      have hBuild (a0 a1 : Interval)
          (hlevels : (a0 = 0 ∧ a1 = 1) ∨ (a0 = 1 ∧ a1 = 0))
          (hseparate : ∀ t z z', (f 0 a0 (t,z)).2 ≠ (f 1 a1 (t,z')).2)
          (havoid0 : ∀ t z, (f 0 a0 (t,z)).2 ≠ c)
          (havoid1 : ∀ t z, (f 1 a1 (t,z)).2 ≠ c) :
          ∃ F0 F1 : C(Interval × Circle,E),
            (∀ z, F0 (0,z) = (A (z,0)).val) ∧
            (∀ z, F1 (0,z) = (A (z,1)).val) ∧
            Set.range (fun z => F0 (1,z)) ∪ Set.range (fun z => F1 (1,z)) =
              Set.range (fun z : Circle => (B (z,q)).val) ∪
                Set.range (fun z : Circle => (B (z,s)).val) ∧
            (∀ t, Topology.IsEmbedding (fun z => F0 (t,z)) ∧ Topology.IsEmbedding (fun z => F1 (t,z))) ∧
            (∀ t, Disjoint (Set.range (fun z => F0 (t,z))) (Set.range (fun z => F1 (t,z)))) ∧
            (∀ t, Disjoint (Set.range (fun z => F0 (t,z)) ∪ Set.range (fun z => F1 (t,z)))
              (Set.range (fun z : Circle => (B (z,c)).val))) := by
        let F0 : C(Interval × Circle,E) :=
          ⟨fun p => (B (f 0 a0 p)).val,continuous_subtype_val.comp (B.continuous.comp (f 0 a0).continuous)⟩
        let F1 : C(Interval × Circle,E) :=
          ⟨fun p => (B (f 1 a1 p)).val,continuous_subtype_val.comp (B.continuous.comp (f 1 a1).continuous)⟩
        have hrange (a b : Interval) :
            Set.range (fun z => (B (f a b (1,z))).val) = Set.range (fun z : Circle => (B (z,⟨1/4+(b:ℝ)/2,by constructor <;> linarith [b.property.1,b.property.2]⟩)).val) := by
          simp_rw [hf1]
          ext x
          constructor
          · rintro ⟨z,rfl⟩
            exact Set.mem_range_self (r z)
          · rintro ⟨z,rfl⟩
            exact ⟨r.symm z,by simp⟩
        refine ⟨F0,F1,?_,?_,?_,?_,?_,?_⟩
        · intro z; change (B (f 0 a0 (0,z))).val = _; rw [hf0,hG]
        · intro z; change (B (f 1 a1 (0,z))).val = _; rw [hf0,hG]
        · change Set.range (fun z => (B (f 0 a0 (1,z))).val) ∪
            Set.range (fun z => (B (f 1 a1 (1,z))).val) = _
          rw [hrange,hrange]
          have hzero : (⟨1/4+((0:Interval):ℝ)/2,by norm_num⟩ : Interval) = q :=
            Subtype.ext (by norm_num [q])
          have hone : (⟨1/4+((1:Interval):ℝ)/2,by norm_num⟩ : Interval) = s :=
            Subtype.ext (by norm_num [s])
          rcases hlevels with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · rw [hzero,hone]
          · rw [hzero,hone]
            exact Set.union_comm _ _
        · intro t
          exact ⟨Topology.IsEmbedding.subtypeVal.comp (B.isEmbedding.comp (hfi 0 a0 t)),
            Topology.IsEmbedding.subtypeVal.comp (B.isEmbedding.comp (hfi 1 a1 t))⟩
        · intro t
          apply Set.disjoint_left.mpr
          rintro x ⟨z,rfl⟩ ⟨z',hz'⟩
          have he := B.injective (Subtype.ext hz')
          exact hseparate t z z' (congrArg Prod.snd he).symm
        · intro t
          apply Set.disjoint_left.mpr
          rintro x (⟨z,rfl⟩ | ⟨z,rfl⟩) ⟨z',hz'⟩
          · have he := B.injective (Subtype.ext hz')
            exact havoid0 t z (congrArg Prod.snd he).symm
          · have he := B.injective (Subtype.ext hz')
            exact havoid1 t z (congrArg Prod.snd he).symm
      have hwlo (t : Interval) (ht : (t:ℝ) < 1) : (w t 0:ℝ) < 1/2 := by
        change (1-(t:ℝ))*(0:ℝ)+(t:ℝ)/2 < 1/2
        linarith
      have hwhi (t : Interval) (ht : (t:ℝ) < 1) : 1/2 < (w t 1:ℝ) := by
        change 1/2 < (1-(t:ℝ))*(1:ℝ)+(t:ℝ)/2
        linarith
      rcases hsides with ⟨hl,hr⟩ | ⟨hl,hr⟩
      · have hL := hlo 0 (fun t ht z => hl z (w t 0) (hwlo t ht))
        have hR := hhi 1 (fun t ht z => hr z (w t 1) (hwhi t ht))
        exact hBuild 0 1 (Or.inl ⟨rfl,rfl⟩)
          (fun t z z' he => by have hh := congrArg Subtype.val he; have := hL t z; have := hR t z'; linarith)
          (fun t z he => by have hh := congrArg Subtype.val he; have := hL t z; change _ = (1/2:ℝ) at hh; linarith)
          (fun t z he => by have hh := congrArg Subtype.val he; have := hR t z; change _ = (1/2:ℝ) at hh; linarith)
      · have hL := hhi 0 (fun t ht z => hl z (w t 0) (hwlo t ht))
        have hR := hlo 1 (fun t ht z => hr z (w t 1) (hwhi t ht))
        exact hBuild 1 0 (Or.inr ⟨rfl,rfl⟩)
          (fun t z z' he => by have hh := congrArg Subtype.val he; have := hL t z; have := hR t z'; linarith)
          (fun t z he => by have hh := congrArg Subtype.val he; have := hL t z; change _ = (1/2:ℝ) at hh; linarith)
          (fun t z he => by have hh := congrArg Subtype.val he; have := hR t z; change _ = (1/2:ℝ) at hh; linarith)
  obtain ⟨F0,F1,hF0,hF1,hFend,hFembedded,hFdisjoint,hFavoid⟩ :=
    hFamily W (M.cover.projection ⁻¹' Nb.closedSet) A B G hGe hG rCommon hGcore hSides
  rw [hBc] at hFavoid
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have hTrack (F0 F1 : C(Interval × Circle,E))
      (he : ∀ t, Topology.IsEmbedding (fun z => F0 (t,z)) ∧ Topology.IsEmbedding (fun z => F1 (t,z)))
      (hd : ∀ t, Disjoint (Set.range (fun z => F0 (t,z))) (Set.range (fun z => F1 (t,z)))) :
      let T : (Interval × Circle) ⊕ (Interval × Circle) → Interval × E :=
        Sum.elim (fun p => (p.1,F0 p)) (fun p => (p.1,F1 p))
      ∃ P : ((Interval × Circle) ⊕ (Interval × Circle)) ≃ₜ Set.range T,
        (∀ p, (P p).val = T p) ∧
        ∀ x, Sum.elim Prod.fst Prod.fst (P.symm x) = x.val.1 := by
    all_goals
      dsimp only
      let T : (Interval × Circle) ⊕ (Interval × Circle) → Interval × E :=
        Sum.elim (fun p => (p.1,F0 p)) (fun p => (p.1,F1 p))
      have hc : Continuous T :=
        (continuous_fst.prodMk F0.continuous).sumElim (continuous_fst.prodMk F1.continuous)
      have hi : Function.Injective T := by
        rintro (⟨t,z⟩ | ⟨t,z⟩) (⟨s,w⟩ | ⟨s,w⟩) hh
        all_goals have ht : t = s := congrArg Prod.fst hh
        all_goals subst s
        all_goals have hx := congrArg Prod.snd hh
        · have hz := (he t).1.injective hx
          subst w
          rfl
        · exact False.elim (Set.disjoint_left.mp (hd t) (Set.mem_range_self z) ⟨w,hx.symm⟩)
        · exact False.elim (Set.disjoint_left.mp (hd t) ⟨w,hx.symm⟩ (Set.mem_range_self z))
        · have hz := (he t).2.injective hx
          subst w
          rfl
      have hT : Topology.IsEmbedding T := (hc.isClosedEmbedding hi).isEmbedding
      let P := hT.toHomeomorph
      refine ⟨P,fun p => rfl,?_⟩
      intro x
      have hh : (P (P.symm x)).val = x.val := congrArg Subtype.val (P.apply_symm_apply x)
      have ht := congrArg Prod.fst hh
      change (T (P.symm x)).1 = x.val.1 at ht
      have htime (p : (Interval × Circle) ⊕ (Interval × Circle)) :
          (T p).1 = Sum.elim Prod.fst Prod.fst p := by cases p <;> rfl
      rw [htime] at ht
      exact ht
  obtain ⟨PairTrack,hPairTrack,hPairTime⟩ := hTrack F0 F1 hFembedded hFdisjoint
  have hCompression (a : NonLoopArc M) (N : ArcNeighborhood a)
      (h : E ≃ₜ E)
      (T : Circle × Interval ≃ₜ h '' (M.cover.projection ⁻¹' N.closedSet))
      (hTb : Set.range (fun z : Circle => (T (z,0)).val) ∪
        Set.range (fun z : Circle => (T (z,1)).val) =
        h '' (M.cover.projection ⁻¹' N.boundary.image)) :
      ∃ H : AmbientIsotopy E, ∃ J : C(Interval × E,E),
        H.finalMap '' (h '' (M.cover.projection ⁻¹' N.boundary.image)) =
          Set.range (fun z : Circle => (T (z,⟨1/4,by norm_num⟩)).val) ∪
            Set.range (fun z : Circle => (T (z,⟨3/4,by norm_num⟩)).val) ∧
        (∀ t z, H.map (t,(T (z,⟨1/2,by norm_num⟩)).val) =
          (T (z,⟨1/2,by norm_num⟩)).val) ∧
        (∀ t x, J (t,H.map (t,x)) = x) ∧
        (∀ t x, H.map (t,J (t,x)) = x) := by
    all_goals
      have hExtension : ∃ Q : C(Circle × Interval,E), Topology.IsEmbedding Q ∧
            (∀ z, Q (z,⟨1/3,by norm_num⟩) = (T (z,0)).val) ∧
            (∀ z, Q (z,⟨2/3,by norm_num⟩) = (T (z,1)).val) ∧
            (∀ z (s : Interval), Q (z,⟨((s:ℝ)+1)/3,by constructor <;> linarith [s.property.1,s.property.2]⟩) =
              (T (z,s)).val) ∧
            IsOpen (Q '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
        all_goals
          letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
          let U := h '' (M.cover.projection ⁻¹' N.closedSet)
          have hfront : Set.range (fun z : Circle => (T (z,0)).val) ∪
                Set.range (fun z : Circle => (T (z,1)).val) =
                frontier (h '' (M.cover.projection ⁻¹' N.closedSet)) := by
            all_goals
              letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
              letI : T2Space S := M.sphere.symm.t2Space
              have hopen : IsOpenMap M.cover.projection := by
                have hcl : IsClosedMap M.cover.projection := M.cover.projection_continuous.isClosedMap
                have hq := hcl.isQuotientMap M.cover.projection_continuous M.cover.projection_surjective
                intro U hU
                rw [← hq.isCoinducing.isOpen_preimage]
                have heq : M.cover.projection ⁻¹' (M.cover.projection '' U) =
                    U ∪ M.cover.deck ⁻¹' U := by
                  ext x
                  constructor
                  · rintro ⟨y,hy,hxy⟩
                    rcases (M.cover.fiber_pair x y).mp hxy.symm with hh | hh
                    · exact Or.inl (hh ▸ hy)
                    · exact Or.inr (by change M.cover.deck x ∈ U; simpa only [hh] using hy)
                  · rintro (hx | hx)
                    · exact ⟨x,hx,rfl⟩
                    · exact ⟨M.cover.deck x,hx,M.cover.projection_deck x⟩
                rw [heq]
                exact hU.union (hU.preimage M.cover.deck.continuous)
              rw [hTb,N.boundary_eq_frontier,
                hopen.preimage_frontier_eq_frontier_preimage M.cover.projection_continuous,
                h.image_frontier]
          have hCollars (U W : Set E)
              (T : Circle × Interval ≃ₜ U) (A : Circle × Interval ≃ₜ W)
              (hWdis : Disjoint W (Set.range (fun z : Circle => (T (z,0)).val) ∪
                Set.range (fun z : Circle => (T (z,1)).val))) :
              ∃ e₀ e₁ : C(Set.Ioo (-1:ℝ) 1 × Circle,E), ∃ ε₀ ε₁ : ℝ,
                Topology.IsOpenEmbedding e₀ ∧ Topology.IsOpenEmbedding e₁ ∧
                (∀ z, e₀ (⟨0,by norm_num⟩,z) = (T (z,0)).val) ∧
                (∀ z, e₁ (⟨0,by norm_num⟩,z) = (T (z,1)).val) ∧
                0 < ε₀ ∧ ε₀ < 1 ∧ 0 < ε₁ ∧ ε₁ < 1 ∧
                Disjoint (e₀ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₀})
                  (e₁ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₁}) ∧
                Disjoint (e₀ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₀}) W ∧
                Disjoint (e₁ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₁}) W := by
            all_goals
              letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
              letI : CompactSpace W := A.compactSpace
              have hWclosed : IsClosed W := by
                have hh := (isCompact_univ : IsCompact (Set.univ : Set W)).image
                  (continuous_subtype_val : Continuous (Subtype.val : W → E))
                have he : (Subtype.val : W → E) '' Set.univ = W := by
                  rw [Set.image_univ,Subtype.range_coe_subtype]
                  rfl
                exact (he ▸ hh).isClosed
              let c₀ : Curve E := ⟨fun z => (T (z,0)).val,
                Topology.IsEmbedding.subtypeVal.comp (T.isEmbedding.comp (isEmbedding_prodMkLeft 0))⟩
              let c₁ : Curve E := ⟨fun z => (T (z,1)).val,
                Topology.IsEmbedding.subtypeVal.comp (T.isEmbedding.comp (isEmbedding_prodMkLeft 1))⟩
              have hd : Disjoint c₀.image c₁.image := by
                apply Set.disjoint_left.mpr
                rintro x ⟨z,hz⟩ ⟨w,hw⟩
                have hh := T.injective (Subtype.ext (hz.trans hw.symm))
                have hu := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
                norm_num at hu
              have hc₀ : IsClosed c₀.image := by
                simpa [Curve.image] using (isCompact_univ.image c₀.embedded.continuous).isClosed
              have hc₁ : IsClosed c₁.image := by
                simpa [Curve.image] using (isCompact_univ.image c₁.embedded.continuous).isClosed
              obtain ⟨O₀,O₁,hO₀,hO₁,hcO₀,hcO₁,hOdis⟩ := normal_separation hc₀ hc₁ hd
              let V₀ := O₀ ∩ Wᶜ
              let V₁ := O₁ ∩ Wᶜ
              have hV₀ : IsOpen V₀ := hO₀.inter hWclosed.isOpen_compl
              have hV₁ : IsOpen V₁ := hO₁.inter hWclosed.isOpen_compl
              have hcV₀ (z : Circle) : c₀.map z ∈ V₀ := by
                refine ⟨hcO₀ (Set.mem_range_self z),?_⟩
                intro hw
                exact Set.disjoint_left.mp hWdis hw (Or.inl (Set.mem_range_self z))
              have hcV₁ (z : Circle) : c₁.map z ∈ V₁ := by
                refine ⟨hcO₁ (Set.mem_range_self z),?_⟩
                intro hw
                exact Set.disjoint_left.mp hWdis hw (Or.inr (Set.mem_range_self z))
              have hcollar (c : Curve E) : ∃ e : C(Set.Ioo (-1:ℝ) 1 × Circle,E),
                  Topology.IsOpenEmbedding e ∧ ∀ z, e (⟨0,by norm_num⟩,z) = c.map z := by
                rcases LocalSurgery.embedded_circle_annular_collar_or_local_reflection E c with hc | ⟨x,⟨F⟩⟩
                · exact hc
                · exact False.elim (GenusOrientationCandidate.no_local_reflection_witness 2 M.genusTwo x
                    (GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x) F)
              obtain ⟨e₀,he₀,hcenter₀⟩ := hcollar c₀
              obtain ⟨e₁,he₁,hcenter₁⟩ := hcollar c₁
              -- Uniform restriction is the actual G3 compact-circle clearance argument.
              have hclear (e : C(Set.Ioo (-1:ℝ) 1 × Circle,E)) (O : Set E)
                  (hO : IsOpen O) (hcenter : ∀ z, e (⟨0,by norm_num⟩,z) ∈ O) :
                  ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
                    ∀ w : Set.Ioo (-1:ℝ) 1, |(w:ℝ)| < ε → ∀ z : Circle, e (w,z) ∈ O := by
                let w0 : Set.Ioo (-1:ℝ) 1 := ⟨0,by norm_num⟩
                let Ω := e ⁻¹' O
                have hΩ : IsOpen Ω := hO.preimage e.continuous
                have hbase : ({w0} : Set (Set.Ioo (-1:ℝ) 1)) ×ˢ (Set.univ : Set Circle) ⊆ Ω := by
                  rintro ⟨w,z⟩ ⟨hw,_⟩
                  have hh : w = w0 := hw
                  subst w
                  exact hcenter z
                obtain ⟨P,Q,hP,hQ,h0,hall,hPQ⟩ :=
                  generalized_tube_lemma isCompact_singleton
                    (isCompact_univ : IsCompact (Set.univ : Set Circle)) hΩ hbase
                have hw0 : w0 ∈ P := h0 (Set.mem_singleton w0)
                obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hP.mem_nhds hw0)
                let ε := min δ (1/2)
                have hε : 0 < ε := lt_min hδ (by norm_num)
                refine ⟨ε,hε,lt_of_le_of_lt (min_le_right _ _) (by norm_num),?_⟩
                intro w hw z
                have hwd : |(w:ℝ)| < δ := lt_of_lt_of_le hw (min_le_left _ _)
                have hwP : w ∈ P := hball (by
                  change dist (w:ℝ) (w0:ℝ) < δ
                  simpa [w0,Real.dist_eq] using hwd)
                exact hPQ ⟨hwP,hall (Set.mem_univ z)⟩
              obtain ⟨ε₀,hε₀,hε₀one,hclear₀⟩ := hclear e₀ V₀ hV₀ (fun z => by rw [hcenter₀]; exact hcV₀ z)
              obtain ⟨ε₁,hε₁,hε₁one,hclear₁⟩ := hclear e₁ V₁ hV₁ (fun z => by rw [hcenter₁]; exact hcV₁ z)
              refine ⟨e₀,e₁,ε₀,ε₁,he₀,he₁,hcenter₀,hcenter₁,hε₀,hε₀one,hε₁,hε₁one,?_,?_,?_⟩
              · apply Set.disjoint_left.mpr
                rintro x ⟨p,hp,hpe⟩ ⟨q,hq,hqe⟩
                have h0 := (hclear₀ p.1 hp p.2).1
                have h1 := (hclear₁ q.1 hq q.2).1
                rw [hpe] at h0
                rw [hqe] at h1
                exact Set.disjoint_left.mp hOdis h0 h1
              · apply Set.disjoint_left.mpr
                rintro x ⟨p,hp,rfl⟩ hw
                exact (hclear₀ p.1 hp p.2).2 hw
              · apply Set.disjoint_left.mpr
                rintro x ⟨p,hp,rfl⟩ hw
                exact (hclear₁ p.1 hp p.2).2 hw
          have hSide (U : Set E)
              (T : Circle × Interval ≃ₜ U)
              (hfront : Set.range (fun z : Circle => (T (z,0)).val) ∪
                Set.range (fun z : Circle => (T (z,1)).val) = frontier U)
              (e : C(Set.Ioo (-1:ℝ) 1 × Circle,E)) (he : Topology.IsOpenEmbedding e)
              (hcenter : ∀ z, e (⟨0,by norm_num⟩,z) = (T (z,0)).val)
              (ε : ℝ) (hε : 0 < ε) (hεone : ε < 1)
              (hclear : Disjoint (e '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε})
                (Set.range (fun z : Circle => (T (z,1)).val))) :
              (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε → ∀ z, e (w,z) ∈ interior U) ∧
                (∀ w : Set.Ioo (-1:ℝ) 1, -ε < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e (w,z) ∉ U) ∨
              (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε → ∀ z, e (w,z) ∉ U) ∧
                (∀ w : Set.Ioo (-1:ℝ) 1, -ε < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e (w,z) ∈ interior U) := by
            audit_main14_side_base3
              letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
              letI : CompactSpace U := T.compactSpace
              have hclosed : IsClosed U := by
                have hh := (isCompact_univ : IsCompact (Set.univ : Set U)).image
                  (continuous_subtype_val : Continuous (Subtype.val : U → E))
                have hr : (Subtype.val : U → E) '' Set.univ = U := by
                  rw [Set.image_univ,Subtype.range_coe_subtype]
                  rfl
                exact (hr ▸ hh).isClosed
              have actual_embedded_annulus_interior_isOpen
                  (B : Circle × Interval → E) (hB : IsEmbedding B) :
                  IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
                rw [isOpen_iff_forall_mem_open]
                rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
                have hu0 : (0:ℝ) < (u : ℝ) := hu.1
                have hu1 : (u : ℝ) < 1 := hu.2
                let lo : ℝ := (u : ℝ)/2
                let hi : ℝ := ((u : ℝ)+1)/2
                have hlu : lo < (u : ℝ) := by dsimp [lo]; exact half_lt_self (by exact hu.1)
                have huh : (u : ℝ) < hi := by dsimp [hi]; linarith [hu1]
                have hl0 : 0 < lo := by dsimp [lo]; exact half_pos (by exact hu.1)
                have hh1 : hi < 1 := by dsimp [hi]; linarith [hu1]
                have hlh : lo ≤ hi := (hlu.trans huh).le
                let width : ℝ → Interval := fun s =>
                  ⟨(Set.projIcc lo hi hlh s : ℝ),
                    ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
                      le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
                have hwc : Continuous width :=
                  (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
                let θ := Complex.arg (z : ℂ)
                let f : EuclideanSpace ℝ (Fin 2) → E := fun x => B (Circle.exp (x 1),width (x 0))
                have hfc : Continuous f := hB.continuous.comp
                  ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
                let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
                  {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
                have hΩ : IsOpen Ω :=
                  (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
                have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
                    (width (x 0) : ℝ) = x 0 :=
                  congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
                have hfi : Set.InjOn f Ω := by
                  intro x hx w hw he
                  have hp := hB.injective he
                  have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
                    (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
                    ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
                  have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
                  change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
                  rw [hclip x hx,hclip w hw] at hwidth
                  ext i
                  fin_cases i
                  · exact hwidth
                  · exact hangle
                have hopen : IsOpen (f '' Ω) :=
                  CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
                have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) := by
                  rintro q ⟨x,hx,rfl⟩
                  refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
                  · change 0 < (width (x 0) : ℝ)
                    rw [hclip x hx]
                    exact hl0.trans hx.1.1
                  · change (width (x 0) : ℝ) < 1
                    rw [hclip x hx]
                    exact hx.1.2.trans hh1
                let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
                have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
                have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
                have hx : x ∈ Ω := by
                  refine ⟨?_,?_⟩
                  · rw [hx0]; exact ⟨hlu,huh⟩
                  · rw [hx1]; constructor <;> linarith [Real.pi_pos]
                have hwu : width (u : ℝ) = u := by
                  apply Subtype.ext
                  change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
                  exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
                have hpoint : f x = B (z,u) := by
                  dsimp [f]
                  rw [hx0,hx1,hwu,Circle.exp_arg]
                exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩
              let f : Circle × Interval → E := fun p => (T p).val
              have hfe : Topology.IsEmbedding f := Topology.IsEmbedding.subtypeVal.comp T.isEmbedding
              let I := f '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
              have hIo : IsOpen I := actual_embedded_annulus_interior_isOpen f hfe
              have hIU : I ⊆ U := by rintro x ⟨p,hp,rfl⟩; exact (T p).property
              have hIint : I ⊆ interior U := hIo.subset_interior_iff.mpr hIU
              have hdense : U ⊆ closure (interior U) := by
                intro x hx
                let p := T.symm ⟨x,hx⟩
                have hp : p ∈ closure ((Set.univ : Set Circle) ×ˢ Set.Ioo (0:Interval) 1) := by
                  rw [closure_prod_eq,closure_univ,closure_Ioo (show (0:Interval) ≠ 1 by norm_num)]
                  exact ⟨Set.mem_univ _,p.2.property.1,p.2.property.2⟩
                have him : f p ∈ closure I := image_closure_subset_closure_image hfe.continuous ⟨p,hp,rfl⟩
                have heq : f p = x := congrArg Subtype.val (T.apply_symm_apply ⟨x,hx⟩)
                rw [heq] at him
                exact closure_mono hIint him
              let w0 : Set.Ioo (-1:ℝ) 1 := ⟨0,by norm_num⟩
              let wp : Set.Ioo (-1:ℝ) 1 := ⟨ε,by constructor <;> linarith⟩
              let wn : Set.Ioo (-1:ℝ) 1 := ⟨-ε,by constructor <;> linarith⟩
              let P := e '' (Set.Ioo w0 wp ×ˢ (Set.univ : Set Circle))
              let Q := e '' (Set.Ioo wn w0 ×ˢ (Set.univ : Set Circle))
              let O := e '' (Set.Ioo wn wp ×ˢ (Set.univ : Set Circle))
              have h0p : w0 < wp := hε
              have hn0 : wn < w0 := by change -ε < 0; linarith
              have hInterval (a b : Set.Ioo (-1:ℝ) 1) (hab : a < b) : IsConnected (Set.Ioo a b) := by
                letI : ConnectedSpace (Set.Ioo (a:ℝ) (b:ℝ)) := Subtype.connectedSpace (isConnected_Ioo (show (a:ℝ) < (b:ℝ) from hab))
                let inc : Set.Ioo (a:ℝ) (b:ℝ) → Set.Ioo (-1:ℝ) 1 := fun x =>
                  ⟨x.val,⟨a.property.1.trans x.property.1,x.property.2.trans b.property.2⟩⟩
                have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
                have hr : Set.range inc = Set.Ioo a b := by
                  ext x
                  constructor
                  · rintro ⟨y,rfl⟩
                    exact y.property
                  · intro hx
                    exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩
                rw [← hr]
                exact isConnected_range hinc
              have hP : IsPreconnected P :=
                ((hInterval w0 wp h0p).prod isConnected_univ).isPreconnected.image e e.continuous.continuousOn
              have hQ : IsPreconnected Q :=
                ((hInterval wn w0 hn0).prod isConnected_univ).isPreconnected.image e e.continuous.continuousOn
              have hO : IsOpen O := he.isOpenMap _ (isOpen_Ioo.prod isOpen_univ)
              have hOcenter (z : Circle) : e (w0,z) ∈ O :=
                ⟨(w0,z),⟨⟨hn0,h0p⟩,Set.mem_univ _⟩,rfl⟩
              have hAvoid (w : Set.Ioo (-1:ℝ) 1) (hw : |(w:ℝ)| < ε)
                  (hn : (w:ℝ) ≠ 0) (z : Circle) : e (w,z) ∉ frontier U := by
                intro hx
                rw [← hfront] at hx
                rcases hx with ⟨v,hv⟩ | hx
                · have hh : e (w,z) = e (w0,v) := by rw [hcenter]; exact hv.symm
                  have heq := congrArg (fun p : Set.Ioo (-1:ℝ) 1 × Circle => (p.1:ℝ))
                    (he.injective hh)
                  exact hn heq
                · exact Set.disjoint_left.mp hclear ⟨(w,z),hw,rfl⟩ hx
              have hPavoid : P ⊆ (frontier U)ᶜ := by
                rintro x ⟨⟨w,z⟩,⟨hw,_⟩,rfl⟩
                have hw0 : 0 < (w:ℝ) := hw.1
                have hwε : (w:ℝ) < ε := hw.2
                exact hAvoid w (by rw [abs_of_pos hw0]; exact hwε) hw0.ne' z
              have hQavoid : Q ⊆ (frontier U)ᶜ := by
                rintro x ⟨⟨w,z⟩,⟨hw,_⟩,rfl⟩
                have hw0 : (w:ℝ) < 0 := hw.2
                have hwε : -ε < (w:ℝ) := hw.1
                exact hAvoid w (by rw [abs_of_neg hw0]; linarith) hw0.ne z
              have hsub (D : Set E) (hD : D ⊆ (frontier U)ᶜ) : D ⊆ interior U ∪ Uᶜ := by
                intro x hx
                by_cases hxu : x ∈ U
                · apply Or.inl
                  by_contra hn
                  exact hD hx ((mem_frontier_iff_notMem_interior hxu).mpr hn)
                · exact Or.inr hxu
              have hid : Disjoint (interior U) Uᶜ := Set.disjoint_left.mpr
                (fun x hx hn => hn (interior_subset hx))
              have hPd : P ⊆ interior U ∨ P ⊆ Uᶜ :=
                IsPreconnected.subset_or_subset isOpen_interior hclosed.isOpen_compl hid (hsub P hPavoid) hP
              have hQd : Q ⊆ interior U ∨ Q ⊆ Uᶜ :=
                IsPreconnected.subset_or_subset isOpen_interior hclosed.isOpen_compl hid (hsub Q hQavoid) hQ
              have hcenterFront (z : Circle) : e (w0,z) ∈ frontier U := by
                rw [hcenter,← hfront]
                exact Or.inl (Set.mem_range_self z)
              have hsplit (x : E) (hx : x ∈ O) : x ∈ P ∨ x ∈ Q ∨ ∃ z, x = e (w0,z) := by
                obtain ⟨⟨w,z⟩,⟨hw,_⟩,rfl⟩ := hx
                rcases lt_trichotomy w w0 with hh | hh | hh
                · exact Or.inr (Or.inl ⟨(w,z),⟨⟨hw.1,hh⟩,Set.mem_univ _⟩,rfl⟩)
                · exact Or.inr (Or.inr ⟨z,by rw [hh]⟩)
                · exact Or.inl ⟨(w,z),⟨⟨hh,hw.2⟩,Set.mem_univ _⟩,rfl⟩
              have hnotbothin : ¬ (P ⊆ interior U ∧ Q ⊆ interior U) := by
                rintro ⟨hp,hq⟩
                have hOU : O ⊆ U := by
                  intro x hx
                  rcases hsplit x hx with hx | hx | ⟨z,rfl⟩
                  · exact interior_subset (hp hx)
                  · exact interior_subset (hq hx)
                  · rw [hcenter]
                    exact (T (z,0)).property
                have hint : e (w0,1) ∈ interior U := hO.subset_interior_iff.mpr hOU (hOcenter 1)
                exact Set.disjoint_left.mp disjoint_interior_frontier hint (hcenterFront 1)
              have hnotbothout : ¬ (P ⊆ Uᶜ ∧ Q ⊆ Uᶜ) := by
                rintro ⟨hp,hq⟩
                have hcU : e (w0,1) ∈ U := by rw [hcenter]; exact (T (1,0)).property
                have hccl := hdense hcU
                obtain ⟨x,hxO,hxi⟩ := mem_closure_iff.mp hccl O hO (hOcenter 1)
                rcases hsplit x hxO with hx | hx | ⟨z,rfl⟩
                · exact hp hx (interior_subset hxi)
                · exact hq hx (interior_subset hxi)
                · exact Set.disjoint_left.mp disjoint_interior_frontier hxi (hcenterFront z)
              have hPmem (w : Set.Ioo (-1:ℝ) 1) (h0 : 0 < (w:ℝ)) (h1 : (w:ℝ) < ε) (z : Circle) :
                  e (w,z) ∈ P := ⟨(w,z),⟨⟨h0,h1⟩,Set.mem_univ _⟩,rfl⟩
              have hQmem (w : Set.Ioo (-1:ℝ) 1) (h0 : -ε < (w:ℝ)) (h1 : (w:ℝ) < 0) (z : Circle) :
                  e (w,z) ∈ Q := ⟨(w,z),⟨⟨h0,h1⟩,Set.mem_univ _⟩,rfl⟩
              rcases hPd with hp | hp <;> rcases hQd with hq | hq
              · exact False.elim (hnotbothin ⟨hp,hq⟩)
              · exact Or.inl ⟨fun w h0 h1 z => hp (hPmem w h0 h1 z),fun w h0 h1 z => hq (hQmem w h0 h1 z)⟩
              · exact Or.inr ⟨fun w h0 h1 z => hp (hPmem w h0 h1 z),fun w h0 h1 z => hq (hQmem w h0 h1 z)⟩
              · exact False.elim (hnotbothout ⟨hp,hq⟩)
          have hHalf (U : Set E)
              (e : C(Set.Ioo (-1:ℝ) 1 × Circle,E)) (he : Topology.IsOpenEmbedding e)
              (ε : ℝ) (hε : 0 < ε) (hεone : ε < 1)
              (hchoice : (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε → ∀ z, e (w,z) ∉ U) ∨
                (∀ w : Set.Ioo (-1:ℝ) 1, -ε < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e (w,z) ∉ U)) :
              ∃ L : C(Circle × Interval,E), Topology.IsEmbedding L ∧
                (∀ z, L (z,0) = e (⟨0,by norm_num⟩,z)) ∧
                (∀ (z : Circle) (u : Interval), 0 < (u:ℝ) → L (z,u) ∉ U) ∧
                Set.range L ⊆ e '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε} := by
            all_goals
              letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
              obtain ⟨σ,hσ,hout⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
                  ∀ w : Set.Ioo (-1:ℝ) 1, 0 < σ*(w:ℝ) → σ*(w:ℝ) < ε → ∀ z, e (w,z) ∉ U := by
                rcases hchoice with hp | hn
                · exact ⟨1,Or.inl rfl,fun w h0 h1 z => hp w (by simpa using h0) (by simpa using h1) z⟩
                · refine ⟨-1,Or.inr rfl,?_⟩
                  intro w h0 h1 z
                  exact hn w (by linarith) (by linarith) z
              let q : Interval → Set.Ioo (-1:ℝ) 1 := fun u =>
                ⟨σ*ε/2*(u:ℝ),by rcases hσ with hs | hs <;> rw [hs] <;>
                  constructor <;> nlinarith [u.property.1,u.property.2]⟩
              have hqc : Continuous q := by dsimp [q]; fun_prop
              have hqi : Function.Injective q := by
                intro u v h
                apply Subtype.ext
                have hh := congrArg Subtype.val h
                change σ*ε/2*(u:ℝ) = σ*ε/2*(v:ℝ) at hh
                rcases hσ with hs | hs <;> rw [hs] at hh <;> nlinarith
              have hq0 : q 0 = ⟨0,by norm_num⟩ := by apply Subtype.ext; dsimp [q]; ring
              have hqabs (u : Interval) : |(q u:ℝ)| < ε := by
                rw [abs_lt]
                dsimp [q]
                rcases hσ with hs | hs <;> rw [hs] <;> constructor <;>
                  nlinarith [u.property.1,u.property.2]
              let L : C(Circle × Interval,E) := ⟨fun p => e (q p.2,p.1),
                e.continuous.comp ((hqc.comp continuous_snd).prodMk continuous_fst)⟩
              have hLi : Function.Injective L := by
                intro p w h
                have hh := he.injective h
                apply Prod.ext
                · have hz := congrArg (fun p : Set.Ioo (-1:ℝ) 1 × Circle => p.2) hh
                  exact hz
                · exact hqi (congrArg Prod.fst hh)
              refine ⟨L,(L.continuous.isClosedEmbedding hLi).isEmbedding,?_,?_,?_⟩
              · intro z
                change e (q 0,z) = _
                rw [hq0]
              · intro z u hu
                apply hout (q u)
                · dsimp [q]
                  rcases hσ with hs | hs <;> rw [hs] <;> nlinarith
                · dsimp [q]
                  rcases hσ with hs | hs <;> rw [hs] <;> nlinarith [u.property.2]
              · rintro x ⟨p,rfl⟩
                exact ⟨(q p.2,p.1),hqabs p.2,rfl⟩
          have hGlue (U : Set E)
              (T : Circle × Interval ≃ₜ U)
              (L R : C(Circle × Interval,E)) (hL : Topology.IsEmbedding L) (hR : Topology.IsEmbedding R)
              (hLzero : ∀ z, L (z,0) = (T (z,0)).val)
              (hRzero : ∀ z, R (z,0) = (T (z,1)).val)
              (hLoutside : ∀ (z : Circle) (t : Interval), 0 < (t:ℝ) → L (z,t) ∉ U)
              (hRoutside : ∀ (z : Circle) (t : Interval), 0 < (t:ℝ) → R (z,t) ∉ U)
              (hLR : Disjoint (Set.range L) (Set.range R)) :
              ∃ g : C(Circle × Set.Icc (-1:ℝ) 2,E), Topology.IsEmbedding g ∧
                (∀ z, g (z,⟨0,by norm_num⟩) = (T (z,0)).val) ∧
                (∀ z, g (z,⟨1,by norm_num⟩) = (T (z,1)).val) ∧
                ∀ p : Circle × Set.Icc (-1:ℝ) 2,
                  ∀ hp0 : 0 ≤ (p.2:ℝ), ∀ hp1 : (p.2:ℝ) ≤ 1,
                    g p = (T (p.1,⟨p.2.val,hp0,hp1⟩)).val := by
            all_goals
              letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
              let q : C(Circle × Interval,E) := ⟨fun p => (T p).val,continuous_subtype_val.comp T.continuous⟩
              have hq : Topology.IsEmbedding q := Topology.IsEmbedding.subtypeVal.comp T.isEmbedding
              have hLq (z : Circle) (t : Interval) (w : Circle) (v : Interval)
                  (he : L (z,t) = q (w,v)) : t = 0 ∧ v = 0 ∧ z = w := by
                by_cases ht : t = 0
                · rw [ht,hLzero] at he
                  have hh := T.injective (Subtype.ext he)
                  have hv := congrArg (fun p : Circle × Interval => p.2) hh
                  have hz := congrArg (fun p : Circle × Interval => p.1) hh
                  exact ⟨ht,hv.symm,hz⟩
                · have htp : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (fun hn => ht (Subtype.ext hn.symm))
                  exact False.elim (hLoutside z t htp (he.symm ▸ (T (w,v)).property))
              have hRq (z : Circle) (t : Interval) (w : Circle) (v : Interval)
                  (he : R (z,t) = q (w,v)) : t = 0 ∧ v = 1 ∧ z = w := by
                by_cases ht : t = 0
                · rw [ht,hRzero] at he
                  have hh := T.injective (Subtype.ext he)
                  have hv := congrArg (fun p : Circle × Interval => p.2) hh
                  have hz := congrArg (fun p : Circle × Interval => p.1) hh
                  exact ⟨ht,hv.symm,hz⟩
                · have htp : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (fun hn => ht (Subtype.ext hn.symm))
                  exact False.elim (hRoutside z t htp (he.symm ▸ (T (w,v)).property))
              let X := Set.Icc (-1 : ℝ) 2
              let τL : X → Interval := fun r => projIcc 0 1 zero_le_one (-(r:ℝ))
              let τQ : X → Interval := fun r => projIcc 0 1 zero_le_one (r:ℝ)
              let τR : X → Interval := fun r => projIcc 0 1 zero_le_one (((r:ℝ)-1))
              have hτL (r : X) (hr : (r:ℝ) ≤ 0) : (τL r:ℝ) = -(r:ℝ) := by
                dsimp only [τL]
                rw [projIcc_of_mem zero_le_one (show -(r:ℝ) ∈ Icc (0:ℝ) 1 by
                  constructor <;> linarith [r.property.1])]
              have hτQ (r : X) (hr0 : 0 ≤ (r:ℝ)) (hr1 : (r:ℝ) ≤ 1) : (τQ r:ℝ) = r := by
                dsimp only [τQ]; rw [projIcc_of_mem zero_le_one ⟨hr0,hr1⟩]
              have hτR (r : X) (hr : 1 ≤ (r:ℝ)) : (τR r:ℝ) = ((r:ℝ)-1) := by
                dsimp only [τR]
                rw [projIcc_of_mem zero_le_one (show ((r:ℝ)-1) ∈ Icc (0:ℝ) 1 by
                  constructor <;> linarith [r.property.2])]
              let ℓ : Circle × X → E := fun p => L (p.1,τL p.2)
              let m : Circle × X → E := fun p => q (p.1,τQ p.2)
              let r : Circle × X → E := fun p => R (p.1,τR p.2)
              have hℓcont : Continuous ℓ := L.continuous.comp
                (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
              have hmcont : Continuous m := q.continuous.comp
                (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
              have hrcont : Continuous r := R.continuous.comp
                (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
              let k : Circle × X → E := fun p => if (p.2:ℝ) ≤ 1 then m p else r p
              have hkcont : Continuous k := by
                apply continuous_if_le (by fun_prop) continuous_const hmcont.continuousOn hrcont.continuousOn
                intro p hp
                have hq1 : τQ p.2 = 1 := Subtype.ext (by rw [hτQ p.2 (by linarith) hp.le]; exact hp)
                have hr0 : τR p.2 = 0 := Subtype.ext (by rw [hτR p.2 hp.ge]; simp [hp])
                dsimp only [m,r]
                rw [hq1,hr0,hRzero]
                rfl
              let G : Circle × X → E := fun p => if (p.2:ℝ) ≤ 0 then ℓ p else k p
              have hGcont : Continuous G := by
                apply continuous_if_le (by fun_prop) continuous_const hℓcont.continuousOn hkcont.continuousOn
                intro p hp
                have hL0 : τL p.2 = 0 := Subtype.ext (by rw [hτL p.2 hp.le]; simp [hp])
                have hq0 : τQ p.2 = 0 := Subtype.ext (by rw [hτQ p.2 hp.ge (by linarith)]; exact hp)
                dsimp only [ℓ,k]
                rw [ite_eq_left (show (p.2:ℝ) ≤ 1 by linarith)]
                dsimp only [m]
                rw [hL0,hq0,hLzero]
                rfl
              have hℓinj (p s : Circle × X) (hp : (p.2:ℝ) ≤ 0) (hs : (s.2:ℝ) ≤ 0)
                  (he : ℓ p = ℓ s) : p = s := by
                have hh := hL.injective he
                have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
                apply Prod.ext hz
                apply Subtype.ext
                have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
                change (τL p.2:ℝ) = (τL s.2:ℝ) at hval
                rw [hτL p.2 hp,hτL s.2 hs] at hval
                linarith
              have hminj (p s : Circle × X) (hp0 : 0 ≤ (p.2:ℝ)) (hp1 : (p.2:ℝ) ≤ 1)
                  (hs0 : 0 ≤ (s.2:ℝ)) (hs1 : (s.2:ℝ) ≤ 1) (he : m p = m s) : p = s := by
                have hh := hq.injective he
                have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
                apply Prod.ext hz
                apply Subtype.ext
                have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
                change (τQ p.2:ℝ) = (τQ s.2:ℝ) at hval
                rwa [hτQ p.2 hp0 hp1,hτQ s.2 hs0 hs1] at hval
              have hrinj (p s : Circle × X) (hp : 1 ≤ (p.2:ℝ)) (hs : 1 ≤ (s.2:ℝ))
                  (he : r p = r s) : p = s := by
                have hh := hR.injective he
                have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
                apply Prod.ext hz
                apply Subtype.ext
                have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
                change (τR p.2:ℝ) = (τR s.2:ℝ) at hval
                rw [hτR p.2 hp,hτR s.2 hs] at hval
                linarith
              have hℓm (p s : Circle × X) (hs0 : 0 < (s.2:ℝ)) (hs1 : (s.2:ℝ) ≤ 1) : ℓ p ≠ m s := by
                intro he
                have hh := (hLq p.1 (τL p.2) s.1 (τQ s.2) he).2.1
                have hv := congrArg Subtype.val hh
                change (τQ s.2:ℝ) = 0 at hv
                rw [hτQ s.2 hs0.le hs1] at hv
                linarith
              have hmr (p s : Circle × X) (hs : 1 < (s.2:ℝ)) : m p ≠ r s := by
                intro he
                have hh := (hRq s.1 (τR s.2) p.1 (τQ p.2) he.symm).1
                have hv := congrArg Subtype.val hh
                change (τR s.2:ℝ) = 0 at hv
                rw [hτR s.2 hs.le] at hv
                linarith
              have hℓr (p s : Circle × X) : ℓ p ≠ r s := by
                intro he
                exact Set.disjoint_left.mp hLR (Set.mem_range_self (p.1,τL p.2))
                  ⟨(s.1,τR s.2),he.symm⟩
              have hGinj : Function.Injective G := by
                intro p s he
                dsimp only [G,k] at he
                by_cases hp0 : (p.2:ℝ) ≤ 0
                · rw [ite_eq_left hp0] at he
                  by_cases hs0 : (s.2:ℝ) ≤ 0
                  · rw [ite_eq_left hs0] at he; exact hℓinj p s hp0 hs0 he
                  · rw [ite_eq_right hs0] at he
                    by_cases hs1 : (s.2:ℝ) ≤ 1
                    · rw [ite_eq_left hs1] at he; exact False.elim (hℓm p s (by linarith) hs1 he)
                    · rw [ite_eq_right hs1] at he; exact False.elim (hℓr p s he)
                · rw [ite_eq_right hp0] at he
                  by_cases hp1 : (p.2:ℝ) ≤ 1
                  · rw [ite_eq_left hp1] at he
                    by_cases hs0 : (s.2:ℝ) ≤ 0
                    · rw [ite_eq_left hs0] at he; exact False.elim (hℓm s p (by linarith) hp1 he.symm)
                    · rw [ite_eq_right hs0] at he
                      by_cases hs1 : (s.2:ℝ) ≤ 1
                      · rw [ite_eq_left hs1] at he; exact hminj p s (by linarith) hp1 (by linarith) hs1 he
                      · rw [ite_eq_right hs1] at he; exact False.elim (hmr p s (by linarith) he)
                  · rw [ite_eq_right hp1] at he
                    by_cases hs0 : (s.2:ℝ) ≤ 0
                    · rw [ite_eq_left hs0] at he; exact False.elim (hℓr s p he.symm)
                    · rw [ite_eq_right hs0] at he
                      by_cases hs1 : (s.2:ℝ) ≤ 1
                      · rw [ite_eq_left hs1] at he; exact False.elim (hmr s p (by linarith) he.symm)
                      · rw [ite_eq_right hs1] at he; exact hrinj p s (by linarith) (by linarith) he
              let g : C(Circle × X,E) := ⟨G,hGcont⟩
              have hg : Topology.IsEmbedding g := (hGcont.isClosedEmbedding hGinj).isEmbedding
              have hg0 (z : Circle) : g (z,⟨0,by dsimp [X]; norm_num⟩) = q (z,0) := by
                change G (z,⟨0,by dsimp [X]; norm_num⟩) = q (z,0)
                simp only [G,le_refl,if_true,ℓ,τL,neg_zero,
                  projIcc_of_mem zero_le_one (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)]
                exact hLzero z
              have hg1 (z : Circle) : g (z,⟨1,by dsimp [X]; norm_num⟩) = q (z,1) := by
                change G (z,⟨1,by dsimp [X]; norm_num⟩) = q (z,1)
                simp only [G,show ¬(1:ℝ)≤0 by norm_num,if_false,k,le_refl,if_true,m,τQ,
                  projIcc_of_mem zero_le_one (show (1:ℝ)∈Icc (0:ℝ) 1 by simp)]
                congr 1
              have hgmid (p : Circle × X) (hp0 : 0 ≤ (p.2:ℝ)) (hp1 : (p.2:ℝ) ≤ 1) :
                  g p = q (p.1,⟨p.2.val,hp0,hp1⟩) := by
                by_cases hp : (p.2:ℝ) = 0
                · have he : p.2 = ⟨0,by dsimp [X]; norm_num⟩ := Subtype.ext hp
                  calc
                    g p = g (p.1,⟨0,by dsimp [X]; norm_num⟩) := congrArg g (Prod.ext rfl he)
                    _ = q (p.1,0) := hg0 p.1
                    _ = q (p.1,⟨p.2.val,hp0,hp1⟩) := congrArg q (Prod.ext rfl (Subtype.ext hp.symm))
                · change G p = _
                  have hpp : 0 < (p.2:ℝ) := lt_of_le_of_ne hp0 (Ne.symm hp)
                  dsimp only [G,k]
                  rw [ite_eq_right (not_le_of_gt hpp),ite_eq_left hp1]
                  change q (p.1,τQ p.2) = _
                  congr 1
                  apply Prod.ext
                  · rfl
                  · apply Subtype.ext; exact hτQ p.2 hp0 hp1
              exact ⟨g,hg,hg0,hg1,hgmid⟩
          have actual_embedded_annulus_interior_isOpen
              (B : Circle × Interval → E) (hB : IsEmbedding B) :
              IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
            rw [isOpen_iff_forall_mem_open]
            rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
            have hu0 : (0:ℝ) < (u : ℝ) := hu.1
            have hu1 : (u : ℝ) < 1 := hu.2
            let lo : ℝ := (u : ℝ)/2
            let hi : ℝ := ((u : ℝ)+1)/2
            have hlu : lo < (u : ℝ) := by dsimp [lo]; exact half_lt_self (by exact hu.1)
            have huh : (u : ℝ) < hi := by dsimp [hi]; linarith [hu1]
            have hl0 : 0 < lo := by dsimp [lo]; exact half_pos (by exact hu.1)
            have hh1 : hi < 1 := by dsimp [hi]; linarith [hu1]
            have hlh : lo ≤ hi := (hlu.trans huh).le
            let width : ℝ → Interval := fun s =>
              ⟨(Set.projIcc lo hi hlh s : ℝ),
                ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
                  le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
            have hwc : Continuous width :=
              (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
            let θ := Complex.arg (z : ℂ)
            let f : EuclideanSpace ℝ (Fin 2) → E := fun x => B (Circle.exp (x 1),width (x 0))
            have hfc : Continuous f := hB.continuous.comp
              ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
            let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
              {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
            have hΩ : IsOpen Ω :=
              (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
            have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
                (width (x 0) : ℝ) = x 0 :=
              congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
            have hfi : Set.InjOn f Ω := by
              intro x hx w hw he
              have hp := hB.injective he
              have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
                (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
                ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
              have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
              change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
              rw [hclip x hx,hclip w hw] at hwidth
              ext i
              fin_cases i
              · exact hwidth
              · exact hangle
            have hopen : IsOpen (f '' Ω) :=
              CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
            have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) := by
              rintro q ⟨x,hx,rfl⟩
              refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
              · change 0 < (width (x 0) : ℝ)
                rw [hclip x hx]
                exact hl0.trans hx.1.1
              · change (width (x 0) : ℝ) < 1
                rw [hclip x hx]
                exact hx.1.2.trans hh1
            let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
            have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
            have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
            have hx : x ∈ Ω := by
              refine ⟨?_,?_⟩
              · rw [hx0]; exact ⟨hlu,huh⟩
              · rw [hx1]; constructor <;> linarith [Real.pi_pos]
            have hwu : width (u : ℝ) = u := by
              apply Subtype.ext
              change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
              exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
            have hpoint : f x = B (z,u) := by
              dsimp [f]
              rw [hx0,hx1,hwu,Circle.exp_arg]
            exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩
          let q : Interval → Interval := fun u => ⟨1/4+(u:ℝ)/2,by constructor <;> linarith [u.property.1,u.property.2]⟩
          let f : Circle × Interval → E := fun p => (T (p.1,q p.2)).val
          have hfc : Continuous f := by dsimp [f,q]; fun_prop
          have hfi : Function.Injective f := by
            intro p w he
            have hh := T.injective (Subtype.ext he)
            apply Prod.ext
            · have hz := congrArg (fun p : Circle × Interval => p.1) hh
              exact hz
            · apply Subtype.ext
              have hv := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
              change 1/4+(p.2:ℝ)/2 = 1/4+(w.2:ℝ)/2 at hv
              linarith
          have hfe : Topology.IsEmbedding f := (hfc.isClosedEmbedding hfi).isEmbedding
          let W := Set.range f
          let A : Circle × Interval ≃ₜ W := hfe.toHomeomorph
          have hWdis : Disjoint W (Set.range (fun z : Circle => (T (z,0)).val) ∪
              Set.range (fun z : Circle => (T (z,1)).val)) := by
            apply Set.disjoint_left.mpr
            rintro x ⟨p,rfl⟩ (⟨z,he⟩ | ⟨z,he⟩)
            · have hh := T.injective (Subtype.ext he)
              have hv := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
              change 0 = 1/4+(p.2:ℝ)/2 at hv
              linarith [p.2.property.1]
            · have hh := T.injective (Subtype.ext he)
              have hv := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
              change 1 = 1/4+(p.2:ℝ)/2 at hv
              linarith [p.2.property.2]
          obtain ⟨e₀,e₁,ε₀,ε₁,he₀,he₁,hcenter₀,hcenter₁,hε₀,hε₀one,hε₁,hε₁one,hedis,heW₀,heW₁⟩ :=
            hCollars U W T A hWdis
          have hclear₀ : Disjoint (e₀ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₀})
              (Set.range (fun z : Circle => (T (z,1)).val)) := by
            apply hedis.mono_right
            rintro x ⟨z,rfl⟩
            exact ⟨(⟨0,by norm_num⟩,z),by simpa using hε₁,hcenter₁ z⟩
          have hclear₁ : Disjoint (e₁ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₁})
              (Set.range (fun z : Circle => (T (z,0)).val)) := by
            apply hedis.symm.mono_right
            rintro x ⟨z,rfl⟩
            exact ⟨(⟨0,by norm_num⟩,z),by simpa using hε₀,hcenter₀ z⟩
          have hs₀ := hSide U T hfront e₀ he₀ hcenter₀ ε₀ hε₀ hε₀one hclear₀
          have hc₀ : (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε₀ → ∀ z, e₀ (w,z) ∉ U) ∨
              (∀ w : Set.Ioo (-1:ℝ) 1, -ε₀ < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e₀ (w,z) ∉ U) := by
            rcases hs₀ with ⟨hin,hout⟩ | ⟨hout,hin⟩
            · exact Or.inr hout
            · exact Or.inl hout
          let T' := (Homeomorph.prodCongr (Homeomorph.refl Circle) unitInterval.symmHomeomorph).trans T
          have hT'₀ (z : Circle) : (T' (z,0)).val = (T (z,1)).val := by simp [T',unitInterval.symmHomeomorph,unitInterval.symm]
          have hT'₁ (z : Circle) : (T' (z,1)).val = (T (z,0)).val := by simp [T',unitInterval.symmHomeomorph,unitInterval.symm]
          have hfront' : Set.range (fun z : Circle => (T' (z,0)).val) ∪
              Set.range (fun z : Circle => (T' (z,1)).val) = frontier U := by
            simp_rw [hT'₀,hT'₁]
            rw [Set.union_comm]
            exact hfront
          have hcenter₁' (z : Circle) : e₁ (⟨0,by norm_num⟩,z) = (T' (z,0)).val :=
            (hcenter₁ z).trans (hT'₀ z).symm
          have hclear₁' : Disjoint (e₁ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₁})
              (Set.range (fun z : Circle => (T' (z,1)).val)) := by
            simp_rw [hT'₁]
            exact hclear₁
          have hs₁ := hSide U T' hfront' e₁ he₁ hcenter₁' ε₁ hε₁ hε₁one hclear₁'
          have hc₁ : (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε₁ → ∀ z, e₁ (w,z) ∉ U) ∨
              (∀ w : Set.Ioo (-1:ℝ) 1, -ε₁ < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e₁ (w,z) ∉ U) := by
            rcases hs₁ with ⟨hin,hout⟩ | ⟨hout,hin⟩
            · exact Or.inr hout
            · exact Or.inl hout
          obtain ⟨L,hL,hL0,hLout,hLsub⟩ := hHalf U e₀ he₀ ε₀ hε₀ hε₀one hc₀
          obtain ⟨R,hR,hR0,hRout,hRsub⟩ := hHalf U e₁ he₁ ε₁ hε₁ hε₁one hc₁
          have hLzero (z : Circle) : L (z,0) = (T (z,0)).val := (hL0 z).trans (hcenter₀ z)
          have hRzero (z : Circle) : R (z,0) = (T (z,1)).val := (hR0 z).trans (hcenter₁ z)
          have hLR : Disjoint (Set.range L) (Set.range R) := hedis.mono hLsub hRsub
          obtain ⟨g,hg,hg0,hg1,hgmid⟩ := hGlue U T L R hL hR hLzero hRzero hLout hRout hLR
          let k : Interval → Set.Icc (-1:ℝ) 2 := fun u =>
            ⟨3*(u:ℝ)-1,by constructor <;> linarith [u.property.1,u.property.2]⟩
          let Q : C(Circle × Interval,E) := ⟨fun p => g (p.1,k p.2),
            g.continuous.comp (continuous_fst.prodMk (by dsimp [k]; fun_prop))⟩
          have hQi : Function.Injective Q := by
            intro p w he
            have hh := hg.injective he
            apply Prod.ext
            · have hz := congrArg (fun p : Circle × Set.Icc (-1:ℝ) 2 => p.1) hh
              exact hz
            · apply Subtype.ext
              have hv := congrArg (fun p : Circle × Set.Icc (-1:ℝ) 2 => (p.2:ℝ)) hh
              change 3*(p.2:ℝ)-1 = 3*(w.2:ℝ)-1 at hv
              linarith
          have hQ : Topology.IsEmbedding Q := (Q.continuous.isClosedEmbedding hQi).isEmbedding
          have hQold (z : Circle) (s : Interval) :
              Q (z,⟨((s:ℝ)+1)/3,by constructor <;> linarith [s.property.1,s.property.2]⟩) = (T (z,s)).val := by
            have hk : k ⟨((s:ℝ)+1)/3,by constructor <;> linarith [s.property.1,s.property.2]⟩ =
                ⟨s.val,by constructor <;> linarith [s.property.1,s.property.2]⟩ := by
              apply Subtype.ext
              dsimp [k]
              ring
            change g (z,k _) = _
            rw [hk]
            exact hgmid _ s.property.1 s.property.2
          refine ⟨Q,hQ,?_,?_,hQold,actual_embedded_annulus_interior_isOpen Q hQ⟩
          · intro z
            simpa using hQold z 0
          · intro z
            have hh := hQold z 1
            norm_num at hh
            exact hh
      have hMove (U : Set E)
          (T : Circle × Interval ≃ₜ U) :
          ∃ H : AmbientIsotopy E, ∃ J : C(Interval × E,E),
            H.finalMap ''
              (Set.range (fun z : Circle => (T (z,⟨1/6,by norm_num⟩)).val) ∪
                Set.range (fun z : Circle => (T (z,⟨5/6,by norm_num⟩)).val)) =
              Set.range (fun z : Circle => (T (z,⟨1/3,by norm_num⟩)).val) ∪
                Set.range (fun z : Circle => (T (z,⟨2/3,by norm_num⟩)).val) ∧
            (∀ t z, H.map (t,(T (z,⟨1/2,by norm_num⟩)).val) =
              (T (z,⟨1/2,by norm_num⟩)).val) ∧
            (∀ t x, x ∉ U → H.map (t,x) = x) ∧
            (∀ t x, J (t,H.map (t,x)) = x) ∧
            (∀ t x, H.map (t,J (t,x)) = x) := by
        all_goals
          letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
          have actual_embedded_annulus_interior_isOpen
              (B : Circle × Interval → E) (hB : IsEmbedding B) :
              IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
            rw [isOpen_iff_forall_mem_open]
            rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
            have hu0 : (0:ℝ) < (u : ℝ) := hu.1
            have hu1 : (u : ℝ) < 1 := hu.2
            let lo : ℝ := (u : ℝ)/2
            let hi : ℝ := ((u : ℝ)+1)/2
            have hlu : lo < (u : ℝ) := by dsimp [lo]; exact half_lt_self (by exact hu.1)
            have huh : (u : ℝ) < hi := by dsimp [hi]; linarith [hu1]
            have hl0 : 0 < lo := by dsimp [lo]; exact half_pos (by exact hu.1)
            have hh1 : hi < 1 := by dsimp [hi]; linarith [hu1]
            have hlh : lo ≤ hi := (hlu.trans huh).le
            let width : ℝ → Interval := fun s =>
              ⟨(Set.projIcc lo hi hlh s : ℝ),
                ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
                  le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
            have hwc : Continuous width :=
              (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
            let θ := Complex.arg (z : ℂ)
            let f : EuclideanSpace ℝ (Fin 2) → E := fun x => B (Circle.exp (x 1),width (x 0))
            have hfc : Continuous f := hB.continuous.comp
              ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
            let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
              {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
            have hΩ : IsOpen Ω :=
              (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
            have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
                (width (x 0) : ℝ) = x 0 :=
              congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
            have hfi : Set.InjOn f Ω := by
              intro x hx w hw he
              have hp := hB.injective he
              have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
                (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
                ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
              have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
              change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
              rw [hclip x hx,hclip w hw] at hwidth
              ext i
              fin_cases i
              · exact hwidth
              · exact hangle
            have hopen : IsOpen (f '' Ω) :=
              CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
            have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) := by
              rintro q ⟨x,hx,rfl⟩
              refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
              · change 0 < (width (x 0) : ℝ)
                rw [hclip x hx]
                exact hl0.trans hx.1.1
              · change (width (x 0) : ℝ) < 1
                rw [hclip x hx]
                exact hx.1.2.trans hh1
            let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
            have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
            have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
            have hx : x ∈ Ω := by
              refine ⟨?_,?_⟩
              · rw [hx0]; exact ⟨hlu,huh⟩
              · rw [hx1]; constructor <;> linarith [Real.pi_pos]
            have hwu : width (u : ℝ) = u := by
              apply Subtype.ext
              change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
              exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
            have hpoint : f x = B (z,u) := by
              dsimp [f]
              rw [hx0,hx1,hwu,Circle.exp_arg]
            exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩
          let L : Circle × Interval → E := fun p =>
            (T (p.1,⟨(p.2 : ℝ)/2,by constructor <;> linarith [p.2.property.1,p.2.property.2]⟩)).val
          let R : Circle × Interval → E := fun p =>
            (T (p.1,⟨1-(p.2 : ℝ)/2,by constructor <;> linarith [p.2.property.1,p.2.property.2]⟩)).val
          have hLc : Continuous L := by dsimp [L]; fun_prop
          have hRc : Continuous R := by dsimp [R]; fun_prop
          have hLi : Function.Injective L := by
            intro p q he
            have hh := T.injective (Subtype.ext he)
            apply Prod.ext
            · have hx := congrArg (fun x : Circle × Interval => x.1) hh
              exact hx
            · apply Subtype.ext
              have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
              change (p.2 : ℝ)/2 = (q.2 : ℝ)/2 at hc
              linarith
          have hRi : Function.Injective R := by
            intro p q he
            have hh := T.injective (Subtype.ext he)
            apply Prod.ext
            · have hx := congrArg (fun x : Circle × Interval => x.1) hh
              exact hx
            · apply Subtype.ext
              have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
              change 1-(p.2 : ℝ)/2 = 1-(q.2 : ℝ)/2 at hc
              linarith
          have hL : Topology.IsEmbedding L := (hLc.isClosedEmbedding hLi).isEmbedding
          have hR : Topology.IsEmbedding R := (hRc.isClosedEmbedding hRi).isEmbedding
          let UL := L '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
          let UR := R '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
          have hUL : IsOpen UL := actual_embedded_annulus_interior_isOpen L hL
          have hUR : IsOpen UR := actual_embedded_annulus_interior_isOpen R hR
          obtain ⟨K,V,hleft,hright,hzero,hone,hfinal⟩ := CurveComplex.G3Review.actual_circle_band_ambient_motion
          have hfixL (t : Interval) (y : Circle × Interval) (hy : L y ∉ UL) : K.map (t,y) = y := by
            by_cases hy0 : y.2 = 0
            · rw [show y = (y.1,0) from Prod.ext rfl hy0]
              exact hzero t y.1
            by_cases hy1 : y.2 = 1
            · rw [show y = (y.1,1) from Prod.ext rfl hy1]
              exact hone t y.1
            have h0 : (0 : Interval) < y.2 := lt_of_le_of_ne (by exact y.2.property.1) (fun he => hy0 he.symm)
            have h1 : y.2 < (1 : Interval) := lt_of_le_of_ne (by exact y.2.property.2) hy1
            exact False.elim (hy ⟨y,⟨Set.mem_univ _,h0,h1⟩,rfl⟩)
          have hfixR (t : Interval) (y : Circle × Interval) (hy : R y ∉ UR) : K.map (t,y) = y := by
            by_cases hy0 : y.2 = 0
            · rw [show y = (y.1,0) from Prod.ext rfl hy0]
              exact hzero t y.1
            by_cases hy1 : y.2 = 1
            · rw [show y = (y.1,1) from Prod.ext rfl hy1]
              exact hone t y.1
            have h0 : (0 : Interval) < y.2 := lt_of_le_of_ne (by exact y.2.property.1) (fun he => hy0 he.symm)
            have h1 : y.2 < (1 : Interval) := lt_of_le_of_ne (by exact y.2.property.2) hy1
            exact False.elim (hy ⟨y,⟨Set.mem_univ _,h0,h1⟩,rfl⟩)
          obtain ⟨HL,JL,hHL,hLout,hJLleft,hJLright⟩ :=
            CurveComplex.G3Review.actual_compact_embedded_motion_extension L hL UL hUL
              (Set.image_subset_range _ _) K V hleft hright hfixL
          obtain ⟨HR,JR,hHR,hRout,hJRleft,hJRright⟩ :=
            CurveComplex.G3Review.actual_compact_embedded_motion_extension R hR UR hUR
              (Set.image_subset_range _ _) K V hleft hright hfixR
          have hLow (z : Circle) (u : Interval) (hu : (u : ℝ) ≤ 1/2) : (T (z,u)).val ∉ UR := by
            rintro ⟨p,⟨_,hp⟩,he⟩
            have hh := T.injective (Subtype.ext he)
            have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
            change 1-(p.2 : ℝ)/2 = (u : ℝ) at hc
            have hp1 : (p.2 : ℝ) < 1 := hp.2
            linarith
          have hHigh (z : Circle) (u : Interval) (hu : 1/2 ≤ (u : ℝ)) : (T (z,u)).val ∉ UL := by
            rintro ⟨p,⟨_,hp⟩,he⟩
            have hh := T.injective (Subtype.ext he)
            have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
            change (p.2 : ℝ)/2 = (u : ℝ) at hc
            have hp1 : (p.2 : ℝ) < 1 := hp.2
            linarith
          let H : AmbientIsotopy E := {
            map := ⟨fun p => HR.map (p.1,HL.map (p.1,p.2)),HR.map.continuous.comp
              (continuous_fst.prodMk (HL.map.continuous.comp (continuous_fst.prodMk continuous_snd)))⟩
            homeomorphism_at := by
              intro t
              obtain ⟨l,hl⟩ := HL.homeomorphism_at t
              obtain ⟨r,hr⟩ := HR.homeomorphism_at t
              exact ⟨l.trans r,fun x => by change r (l x) = HR.map (t,HL.map (t,x)); rw [hl,hr]⟩
            at_zero := by
              intro x
              change HR.map (⟨0,by norm_num⟩,HL.map (⟨0,by norm_num⟩,x)) = x
              rw [HL.at_zero,HR.at_zero] }
          let J : C(Interval × E,E) := ⟨fun p => JL (p.1,JR (p.1,p.2)),JL.continuous.comp
            (continuous_fst.prodMk (JR.continuous.comp (continuous_fst.prodMk continuous_snd)))⟩
          have hLf (z : Circle) : HL.finalMap (T (z,⟨1/6,by norm_num⟩)).val =
              (T (z,⟨1/3,by norm_num⟩)).val := by
            have h := hHL 1 (z,⟨1/3,by norm_num⟩)
            have hk := hfinal z
            change K.map (1,(z,⟨1/3,by norm_num⟩)) = (z,⟨2/3,by norm_num⟩) at hk
            rw [hk] at h
            norm_num [AmbientIsotopy.finalMap,L] at h ⊢
            exact h
          have hRf (z : Circle) : HR.finalMap (T (z,⟨5/6,by norm_num⟩)).val =
              (T (z,⟨2/3,by norm_num⟩)).val := by
            have h := hHR 1 (z,⟨1/3,by norm_num⟩)
            have hk := hfinal z
            change K.map (1,(z,⟨1/3,by norm_num⟩)) = (z,⟨2/3,by norm_num⟩) at hk
            rw [hk] at h
            norm_num [AmbientIsotopy.finalMap,R] at h ⊢
            exact h
          have hHfL (z : Circle) : H.finalMap (T (z,⟨1/6,by norm_num⟩)).val =
              (T (z,⟨1/3,by norm_num⟩)).val := by
            change HR.finalMap (HL.finalMap _) = _
            rw [hLf]
            exact hRout 1 _ (hLow z _ (by norm_num))
          have hHfR (z : Circle) : H.finalMap (T (z,⟨5/6,by norm_num⟩)).val =
              (T (z,⟨2/3,by norm_num⟩)).val := by
            change HR.finalMap (HL.finalMap _) = _
            rw [show HL.finalMap (T (z,⟨5/6,by norm_num⟩)).val = (T (z,⟨5/6,by norm_num⟩)).val from
              hLout 1 _ (hHigh z _ (by norm_num))]
            exact hRf z
          refine ⟨H,J,?_,?_,?_,?_,?_⟩
          · rw [Set.image_union,← Set.range_comp,← Set.range_comp]
            exact congrArg₂ Set.union (congrArg Set.range (funext hHfL)) (congrArg Set.range (funext hHfR))
          · intro t z
            change HR.map (t,HL.map (t,_)) = _
            rw [hLout t _ (hHigh z _ (by norm_num)),hRout t _ (hLow z _ (by norm_num))]
          · intro t x hx
            have hxL : x ∉ UL := by
              rintro ⟨p,hp,rfl⟩
              exact hx (T _).property
            have hxR : x ∉ UR := by
              rintro ⟨p,hp,rfl⟩
              exact hx (T _).property
            change HR.map (t,HL.map (t,x)) = x
            rw [hLout t x hxL,hRout t x hxR]
          · intro t x
            change JL (t,JR (t,HR.map (t,HL.map (t,x)))) = x
            rw [hJRleft,hJLleft]
          · intro t x
            change HR.map (t,HL.map (t,JL (t,JR (t,x)))) = x
            rw [hJLright,hJRright]
      obtain ⟨Q,hQ,hQ0,hQ1,hQold,hQopen⟩ := hExtension
      let q : Interval → Interval := fun u => ⟨1/4+(u:ℝ)/2,by constructor <;> linarith [u.property.1,u.property.2]⟩
      let B : Circle × Interval → E := fun p => Q (p.1,q p.2)
      have hBc : Continuous B := by dsimp [B,q]; fun_prop
      have hBi : Function.Injective B := by
        intro p w he
        have hh := hQ.injective he
        apply Prod.ext
        · have hz := congrArg (fun p : Circle × Interval => p.1) hh
          exact hz
        · apply Subtype.ext
          have hv := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
          change 1/4+(p.2:ℝ)/2 = 1/4+(w.2:ℝ)/2 at hv
          linarith
      letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
      have hBe : Topology.IsEmbedding B := (hBc.isClosedEmbedding hBi).isEmbedding
      let V := Set.range B
      let TB : Circle × Interval ≃ₜ V := hBe.toHomeomorph
      have hTB0 (z : Circle) : (TB (z,⟨1/6,by norm_num⟩)).val = (T (z,0)).val := by
        change Q (z,q ⟨1/6,by norm_num⟩) = _
        rw [show q ⟨1/6,by norm_num⟩ = ⟨1/3,by norm_num⟩ from Subtype.ext (by norm_num [q])]
        exact hQ0 z
      have hTB1 (z : Circle) : (TB (z,⟨5/6,by norm_num⟩)).val = (T (z,1)).val := by
        change Q (z,q ⟨5/6,by norm_num⟩) = _
        rw [show q ⟨5/6,by norm_num⟩ = ⟨2/3,by norm_num⟩ from Subtype.ext (by norm_num [q])]
        exact hQ1 z
      have hTB2 (z : Circle) : (TB (z,⟨1/3,by norm_num⟩)).val = (T (z,⟨1/4,by norm_num⟩)).val := by
        change Q (z,q ⟨1/3,by norm_num⟩) = _
        rw [show q ⟨1/3,by norm_num⟩ = ⟨5/12,by norm_num⟩ from Subtype.ext (by norm_num [q])]
        have hh := hQold z ⟨1/4,by norm_num⟩
        norm_num at hh
        exact hh
      have hTB3 (z : Circle) : (TB (z,⟨2/3,by norm_num⟩)).val = (T (z,⟨3/4,by norm_num⟩)).val := by
        change Q (z,q ⟨2/3,by norm_num⟩) = _
        rw [show q ⟨2/3,by norm_num⟩ = ⟨7/12,by norm_num⟩ from Subtype.ext (by norm_num [q])]
        have hh := hQold z ⟨3/4,by norm_num⟩
        norm_num at hh
        exact hh
      have hTBmid (z : Circle) : (TB (z,⟨1/2,by norm_num⟩)).val = (T (z,⟨1/2,by norm_num⟩)).val := by
        change Q (z,q ⟨1/2,by norm_num⟩) = _
        rw [show q ⟨1/2,by norm_num⟩ = ⟨1/2,by norm_num⟩ from Subtype.ext (by norm_num [q])]
        have hh := hQold z ⟨1/2,by norm_num⟩
        norm_num at hh
        exact hh
      obtain ⟨H,J,hPair,hCore,hOutside,hLeft,hRight⟩ := hMove V TB
      simp_rw [hTB0,hTB1,hTB2,hTB3] at hPair
      simp_rw [hTBmid] at hCore
      rw [hTb] at hPair
      exact ⟨H,J,hPair,hCore,hLeft,hRight⟩
  obtain ⟨HT,JT,hTpair,hTcore,hTleft,hTright⟩ := hCompression a Na h T hTb
  let BId := B.trans (Homeomorph.setCongr
    (show M.cover.projection ⁻¹' Nb.closedSet = (Homeomorph.refl E) '' (M.cover.projection ⁻¹' Nb.closedSet) by simp))
  have hBId (p : Circle × Interval) : (BId p).val = (B p).val := rfl
  have hBIdBoundary : Set.range (fun z : Circle => (BId (z,0)).val) ∪
      Set.range (fun z : Circle => (BId (z,1)).val) =
      (Homeomorph.refl E) '' (M.cover.projection ⁻¹' Nb.boundary.image) := by
    simp_rw [hBId]
    simpa using hBb
  obtain ⟨HB,JB,hBpair,hBcore,hBleft,hBright⟩ := hCompression b Nb (Homeomorph.refl E) BId hBIdBoundary
  simp_rw [hBId] at hBpair hBcore
  simp only [Homeomorph.refl_apply,Set.image_id] at hBpair
  have hRT : AmbientIsotopy.Rel (h '' (M.cover.projection ⁻¹' Na.boundary.image))
      (Set.range (fun z : Circle => (T (z,⟨1/4,by norm_num⟩)).val) ∪
        Set.range (fun z : Circle => (T (z,⟨3/4,by norm_num⟩)).val)) := ⟨HT,hTpair⟩
  have hRB : AmbientIsotopy.Rel (M.cover.projection ⁻¹' Nb.boundary.image)
      (Set.range (fun z : Circle => (B (z,⟨1/4,by norm_num⟩)).val) ∪
        Set.range (fun z : Circle => (B (z,⟨3/4,by norm_num⟩)).val)) := ⟨HB,hBpair⟩
  have hInnerPair : AmbientIsotopy.Rel
      (Set.range (fun z : Circle => (T (z,⟨1/4,by norm_num⟩)).val) ∪
        Set.range (fun z : Circle => (T (z,⟨3/4,by norm_num⟩)).val))
      (Set.range (fun z : Circle => (B (z,⟨1/4,by norm_num⟩)).val) ∪
        Set.range (fun z : Circle => (B (z,⟨3/4,by norm_num⟩)).val)) := by
    have hGivenConstructed (M : HyperellipticModel E S) (U W : Set E)
        (T : Circle × Interval ≃ₜ U) (A : Circle × Interval ≃ₜ W)
        (δ : ℝ) (hδ : 0 < δ) (hδquarter : δ ≤ 1/4)
        (hAcoordinates : ∀ z (u : Interval), ∃ v : Interval,
          (v:ℝ) = 1/2+δ*(2*(u:ℝ)-1) ∧ (A (z,u)).val = (T (z,v)).val) :
        AmbientIsotopy.Rel
          (Set.range (fun z : Circle => (T (z,⟨1/4,by norm_num⟩)).val) ∪
            Set.range (fun z : Circle => (T (z,⟨3/4,by norm_num⟩)).val))
          (Set.range (fun z : Circle => (A (z,0)).val) ∪
            Set.range (fun z : Circle => (A (z,1)).val)) := by
      all_goals
        have hWidth (M : HyperellipticModel E S) (U : Set E)
            (T : Circle × Interval ≃ₜ U) (δ : ℝ) (hδ : 0 < δ) (hδq : δ < 1/4) :
            ∃ H : AmbientIsotopy E, ∃ J : C(Interval × E,E),
              H.finalMap ''
                (Set.range (fun z : Circle => (T (z,⟨1/4,by norm_num⟩)).val) ∪
                  Set.range (fun z : Circle => (T (z,⟨3/4,by norm_num⟩)).val)) =
                Set.range (fun z : Circle => (T (z,⟨1/2-δ,by constructor <;> linarith⟩)).val) ∪
                  Set.range (fun z : Circle => (T (z,⟨1/2+δ,by constructor <;> linarith⟩)).val) ∧
              (∀ t z, H.map (t,(T (z,⟨1/2,by norm_num⟩)).val) =
                (T (z,⟨1/2,by norm_num⟩)).val) ∧
              (∀ t x, x ∉ U → H.map (t,x) = x) ∧
              (∀ t x, J (t,H.map (t,x)) = x) ∧
              (∀ t x, H.map (t,J (t,x)) = x) := by
          all_goals
            letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
            have actual_embedded_annulus_interior_isOpen
                (B : Circle × Interval → E) (hB : IsEmbedding B) :
                IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
              rw [isOpen_iff_forall_mem_open]
              rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
              have hu0 : (0:ℝ) < (u : ℝ) := hu.1
              have hu1 : (u : ℝ) < 1 := hu.2
              let lo : ℝ := (u : ℝ)/2
              let hi : ℝ := ((u : ℝ)+1)/2
              have hlu : lo < (u : ℝ) := by dsimp [lo]; exact half_lt_self (by exact hu.1)
              have huh : (u : ℝ) < hi := by dsimp [hi]; linarith [hu1]
              have hl0 : 0 < lo := by dsimp [lo]; exact half_pos (by exact hu.1)
              have hh1 : hi < 1 := by dsimp [hi]; linarith [hu1]
              have hlh : lo ≤ hi := (hlu.trans huh).le
              let width : ℝ → Interval := fun s =>
                ⟨(Set.projIcc lo hi hlh s : ℝ),
                  ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
                    le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
              have hwc : Continuous width :=
                (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
              let θ := Complex.arg (z : ℂ)
              let f : EuclideanSpace ℝ (Fin 2) → E := fun x => B (Circle.exp (x 1),width (x 0))
              have hfc : Continuous f := hB.continuous.comp
                ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
              let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
                {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
              have hΩ : IsOpen Ω :=
                (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
              have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
                  (width (x 0) : ℝ) = x 0 :=
                congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
              have hfi : Set.InjOn f Ω := by
                intro x hx w hw he
                have hp := hB.injective he
                have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
                  (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
                  ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
                have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
                change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
                rw [hclip x hx,hclip w hw] at hwidth
                ext i
                fin_cases i
                · exact hwidth
                · exact hangle
              have hopen : IsOpen (f '' Ω) :=
                CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
              have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) := by
                rintro q ⟨x,hx,rfl⟩
                refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
                · change 0 < (width (x 0) : ℝ)
                  rw [hclip x hx]
                  exact hl0.trans hx.1.1
                · change (width (x 0) : ℝ) < 1
                  rw [hclip x hx]
                  exact hx.1.2.trans hh1
              let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
              have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
              have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
              have hx : x ∈ Ω := by
                refine ⟨?_,?_⟩
                · rw [hx0]; exact ⟨hlu,huh⟩
                · rw [hx1]; constructor <;> linarith [Real.pi_pos]
              have hwu : width (u : ℝ) = u := by
                apply Subtype.ext
                change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
                exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
              have hpoint : f x = B (z,u) := by
                dsimp [f]
                rw [hx0,hx1,hwu,Circle.exp_arg]
              exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩
            have hCalibration (b : ℝ) (hb0 : 1/2 < b) (hb1 : b < 1) :
                ∃ h : Interval ≃ₜ Interval,
                  h 0 = 0 ∧ h 1 = 1 ∧
                  h ⟨1/3,by norm_num⟩ = ⟨1/2,by norm_num⟩ ∧
                  (h ⟨2/3,by norm_num⟩ : ℝ) = b := by
              all_goals
                let f : Interval → ℝ := fun u =>
                  if (u:ℝ) ≤ 1/3 then 3*(u:ℝ)/2
                  else if (u:ℝ) ≤ 2/3 then 1/2+3*(b-1/2)*((u:ℝ)-1/3)
                  else b+3*(1-b)*((u:ℝ)-2/3)
                have hfmem (u : Interval) : f u ∈ Set.Icc (0:ℝ) 1 := by
                  dsimp [f]
                  split_ifs <;> constructor <;> nlinarith [u.property.1,u.property.2]
                have hc2 : Continuous (fun u : Interval =>
                    if (u:ℝ) ≤ 2/3 then 1/2+3*(b-1/2)*((u:ℝ)-1/3)
                    else b+3*(1-b)*((u:ℝ)-2/3)) := by
                  apply continuous_if_le (by fun_prop) continuous_const (by fun_prop) (by fun_prop)
                  intro u hu
                  rw [hu]
                  ring
                have hfc : Continuous f := by
                  apply continuous_if_le (by fun_prop) continuous_const (by fun_prop) hc2.continuousOn
                  intro u hu
                  rw [hu,if_pos (by norm_num : (1/3:ℝ) ≤ 2/3)]
                  ring
                have hmono : StrictMono f := by
                  intro x y hxy
                  have hxyR : (x:ℝ) < (y:ℝ) := hxy
                  have hcentral : 0 < 3*(b-1/2)*((y:ℝ)-(x:ℝ)) :=
                    mul_pos (mul_pos (by norm_num) (sub_pos.mpr hb0)) (sub_pos.mpr hxyR)
                  have houter : 0 < 3*(1-b)*((y:ℝ)-(x:ℝ)) :=
                    mul_pos (mul_pos (by norm_num) (sub_pos.mpr hb1)) (sub_pos.mpr hxyR)
                  dsimp [f]
                  split_ifs <;> nlinarith [x.property.1,x.property.2,y.property.1,y.property.2]
                let F : Interval → Interval := fun u => ⟨f u,hfmem u⟩
                have hFc : Continuous F := hfc.subtype_mk _
                have hF0 : F 0 = 0 := Subtype.ext (by norm_num [F,f])
                have hF1 : F 1 = 1 := Subtype.ext (by norm_num [F,f]; ring)
                have hFs : Function.Surjective F := by
                  have hconn := (isConnected_range hFc).isPreconnected.ordConnected
                  intro u
                  exact hconn.out ⟨0,hF0⟩ ⟨1,hF1⟩ u.property
                have hFi : Function.Injective F := by
                  intro x y hxy
                  exact hmono.injective (congrArg Subtype.val hxy)
                let h : Interval ≃ₜ Interval :=
                  (Equiv.ofBijective F ⟨hFi,hFs⟩).toHomeomorphOfContinuousClosed hFc hFc.isClosedMap
                refine ⟨h,hF0,hF1,?_,?_⟩
                · apply Subtype.ext
                  change f ⟨1/3,by norm_num⟩ = 1/2
                  norm_num [f]
                · change f ⟨2/3,by norm_num⟩ = b
                  norm_num [f]
                  ring
            obtain ⟨k,hk0,hk1,hkthird,hktwo⟩ := hCalibration (1-2*δ) (by linarith) (by linarith)
            have hkInterior (u : Interval) (hu : u ∈ Set.Ioo (0:Interval) 1) : k u ∈ Set.Ioo (0:Interval) 1 := by
              constructor
              · apply lt_of_le_of_ne (k u).property.1
                intro he
                have heI : k u = 0 := Subtype.ext he.symm
                have hh := k.injective (heI.trans hk0.symm)
                subst u
                exact (lt_irrefl (0:Interval)) hu.1
              · apply lt_of_le_of_ne (k u).property.2
                intro he
                have heI : k u = 1 := Subtype.ext he
                have hh := k.injective (heI.trans hk1.symm)
                subst u
                exact (lt_irrefl (1:Interval)) hu.2
            let L : Circle × Interval → E := fun p =>
              (T (p.1,⟨(k p.2 : ℝ)/2,by constructor <;> linarith [(k p.2).property.1,(k p.2).property.2]⟩)).val
            let R : Circle × Interval → E := fun p =>
              (T (p.1,⟨1-(k p.2 : ℝ)/2,by constructor <;> linarith [(k p.2).property.1,(k p.2).property.2]⟩)).val
            have hLc : Continuous L := by dsimp [L]; fun_prop
            have hRc : Continuous R := by dsimp [R]; fun_prop
            have hLi : Function.Injective L := by
              intro p q he
              have hh := T.injective (Subtype.ext he)
              apply Prod.ext
              · have hx := congrArg (fun x : Circle × Interval => x.1) hh
                exact hx
              · apply Subtype.ext
                have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
                change (k p.2 : ℝ)/2 = (k q.2 : ℝ)/2 at hc
                exact congrArg Subtype.val (k.injective (Subtype.ext (by linarith)))
            have hRi : Function.Injective R := by
              intro p q he
              have hh := T.injective (Subtype.ext he)
              apply Prod.ext
              · have hx := congrArg (fun x : Circle × Interval => x.1) hh
                exact hx
              · apply Subtype.ext
                have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
                change 1-(k p.2 : ℝ)/2 = 1-(k q.2 : ℝ)/2 at hc
                exact congrArg Subtype.val (k.injective (Subtype.ext (by linarith)))
            have hL : Topology.IsEmbedding L := (hLc.isClosedEmbedding hLi).isEmbedding
            have hR : Topology.IsEmbedding R := (hRc.isClosedEmbedding hRi).isEmbedding
            let UL := L '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
            let UR := R '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
            have hUL : IsOpen UL := actual_embedded_annulus_interior_isOpen L hL
            have hUR : IsOpen UR := actual_embedded_annulus_interior_isOpen R hR
            obtain ⟨K,V,hleft,hright,hzero,hone,hfinal⟩ := CurveComplex.G3Review.actual_circle_band_ambient_motion
            have hfixL (t : Interval) (y : Circle × Interval) (hy : L y ∉ UL) : K.map (t,y) = y := by
              by_cases hy0 : y.2 = 0
              · rw [show y = (y.1,0) from Prod.ext rfl hy0]
                exact hzero t y.1
              by_cases hy1 : y.2 = 1
              · rw [show y = (y.1,1) from Prod.ext rfl hy1]
                exact hone t y.1
              have h0 : (0 : Interval) < y.2 := lt_of_le_of_ne (by exact y.2.property.1) (fun he => hy0 he.symm)
              have h1 : y.2 < (1 : Interval) := lt_of_le_of_ne (by exact y.2.property.2) hy1
              exact False.elim (hy ⟨y,⟨Set.mem_univ _,h0,h1⟩,rfl⟩)
            have hfixR (t : Interval) (y : Circle × Interval) (hy : R y ∉ UR) : K.map (t,y) = y := by
              by_cases hy0 : y.2 = 0
              · rw [show y = (y.1,0) from Prod.ext rfl hy0]
                exact hzero t y.1
              by_cases hy1 : y.2 = 1
              · rw [show y = (y.1,1) from Prod.ext rfl hy1]
                exact hone t y.1
              have h0 : (0 : Interval) < y.2 := lt_of_le_of_ne (by exact y.2.property.1) (fun he => hy0 he.symm)
              have h1 : y.2 < (1 : Interval) := lt_of_le_of_ne (by exact y.2.property.2) hy1
              exact False.elim (hy ⟨y,⟨Set.mem_univ _,h0,h1⟩,rfl⟩)
            obtain ⟨HL,JL,hHL,hLout,hJLleft,hJLright⟩ :=
              CurveComplex.G3Review.actual_compact_embedded_motion_extension L hL UL hUL
                (Set.image_subset_range _ _) K V hleft hright hfixL
            obtain ⟨HR,JR,hHR,hRout,hJRleft,hJRright⟩ :=
              CurveComplex.G3Review.actual_compact_embedded_motion_extension R hR UR hUR
                (Set.image_subset_range _ _) K V hleft hright hfixR
            have hLow (z : Circle) (u : Interval) (hu : (u : ℝ) ≤ 1/2) : (T (z,u)).val ∉ UR := by
              rintro ⟨p,⟨_,hp⟩,he⟩
              have hh := T.injective (Subtype.ext he)
              have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
              change 1-(k p.2 : ℝ)/2 = (u : ℝ) at hc
              have hp1 : (k p.2 : ℝ) < 1 := (hkInterior p.2 hp).2
              linarith
            have hHigh (z : Circle) (u : Interval) (hu : 1/2 ≤ (u : ℝ)) : (T (z,u)).val ∉ UL := by
              rintro ⟨p,⟨_,hp⟩,he⟩
              have hh := T.injective (Subtype.ext he)
              have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
              change (k p.2 : ℝ)/2 = (u : ℝ) at hc
              have hp1 : (k p.2 : ℝ) < 1 := (hkInterior p.2 hp).2
              linarith
            let H : AmbientIsotopy E := {
              map := ⟨fun p => HR.map (p.1,HL.map (p.1,p.2)),HR.map.continuous.comp
                (continuous_fst.prodMk (HL.map.continuous.comp (continuous_fst.prodMk continuous_snd)))⟩
              homeomorphism_at := by
                intro t
                obtain ⟨l,hl⟩ := HL.homeomorphism_at t
                obtain ⟨r,hr⟩ := HR.homeomorphism_at t
                exact ⟨l.trans r,fun x => by change r (l x) = HR.map (t,HL.map (t,x)); rw [hl,hr]⟩
              at_zero := by
                intro x
                change HR.map (⟨0,by norm_num⟩,HL.map (⟨0,by norm_num⟩,x)) = x
                rw [HL.at_zero,HR.at_zero] }
            let J : C(Interval × E,E) := ⟨fun p => JL (p.1,JR (p.1,p.2)),JL.continuous.comp
              (continuous_fst.prodMk (JR.continuous.comp (continuous_fst.prodMk continuous_snd)))⟩
            have hLf (z : Circle) : HL.finalMap (T (z,⟨1/4,by norm_num⟩)).val =
                (T (z,⟨1/2-δ,by constructor <;> linarith⟩)).val := by
              have h := hHL 1 (z,⟨1/3,by norm_num⟩)
              have hk := hfinal z
              change K.map (1,(z,⟨1/3,by norm_num⟩)) = (z,⟨2/3,by norm_num⟩) at hk
              rw [hk] at h
              norm_num [AmbientIsotopy.finalMap,L,hkthird,hktwo] at h ⊢
              have heq : (1-2*δ)/2 = 1/2-δ := by ring
              simpa only [heq] using h
            have hRf (z : Circle) : HR.finalMap (T (z,⟨3/4,by norm_num⟩)).val =
                (T (z,⟨1/2+δ,by constructor <;> linarith⟩)).val := by
              have h := hHR 1 (z,⟨1/3,by norm_num⟩)
              have hk := hfinal z
              change K.map (1,(z,⟨1/3,by norm_num⟩)) = (z,⟨2/3,by norm_num⟩) at hk
              rw [hk] at h
              norm_num [AmbientIsotopy.finalMap,R,hkthird,hktwo] at h ⊢
              have heq : 1-(1-2*δ)/2 = 1/2+δ := by ring
              simpa only [heq] using h
            have hHfL (z : Circle) : H.finalMap (T (z,⟨1/4,by norm_num⟩)).val =
                (T (z,⟨1/2-δ,by constructor <;> linarith⟩)).val := by
              change HR.finalMap (HL.finalMap _) = _
              rw [hLf]
              exact hRout 1 _ (hLow z _ (by change (1/2-δ:ℝ) ≤ 1/2; linarith))
            have hHfR (z : Circle) : H.finalMap (T (z,⟨3/4,by norm_num⟩)).val =
                (T (z,⟨1/2+δ,by constructor <;> linarith⟩)).val := by
              change HR.finalMap (HL.finalMap _) = _
              rw [show HL.finalMap (T (z,⟨3/4,by norm_num⟩)).val = (T (z,⟨3/4,by norm_num⟩)).val from
                hLout 1 _ (hHigh z _ (by change (1/2:ℝ) ≤ 3/4; norm_num))]
              exact hRf z
            refine ⟨H,J,?_,?_,?_,?_,?_⟩
            · rw [Set.image_union,← Set.range_comp,← Set.range_comp]
              exact congrArg₂ Set.union (congrArg Set.range (funext hHfL)) (congrArg Set.range (funext hHfR))
            · intro t z
              change HR.map (t,HL.map (t,_)) = _
              rw [hLout t _ (hHigh z _ (by norm_num)),hRout t _ (hLow z _ (by norm_num))]
            · intro t x hx
              have hxL : x ∉ UL := by
                rintro ⟨p,hp,rfl⟩
                exact hx (T _).property
              have hxR : x ∉ UR := by
                rintro ⟨p,hp,rfl⟩
                exact hx (T _).property
              change HR.map (t,HL.map (t,x)) = x
              rw [hLout t x hxL,hRout t x hxR]
            · intro t x
              change JL (t,JR (t,HR.map (t,HL.map (t,x)))) = x
              rw [hJRleft,hJLleft]
            · intro t x
              change HR.map (t,HL.map (t,JL (t,JR (t,x)))) = x
              rw [hJLright,hJRright]
        have hA0 (z : Circle) : (A (z,0)).val =
            (T (z,⟨1/2-δ,by constructor <;> linarith⟩)).val := by
          obtain ⟨v,hv,he⟩ := hAcoordinates z 0
          have hve : v = ⟨1/2-δ,by constructor <;> linarith⟩ := by
            apply Subtype.ext
            norm_num at hv
            linarith
          rw [hve] at he
          exact he
        have hA1 (z : Circle) : (A (z,1)).val =
            (T (z,⟨1/2+δ,by constructor <;> linarith⟩)).val := by
          obtain ⟨v,hv,he⟩ := hAcoordinates z 1
          have hve : v = ⟨1/2+δ,by constructor <;> linarith⟩ := by
            apply Subtype.ext
            norm_num at hv
            linarith
          rw [hve] at he
          exact he
        by_cases heq : δ = 1/4
        · have he0 : (⟨1/2-δ,by constructor <;> linarith⟩ : Interval) = ⟨1/4,by norm_num⟩ :=
            Subtype.ext (by change (1/2:ℝ)-δ = 1/4; linarith)
          have he1 : (⟨1/2+δ,by constructor <;> linarith⟩ : Interval) = ⟨3/4,by norm_num⟩ :=
            Subtype.ext (by change (1/2:ℝ)+δ = 3/4; linarith)
          simp_rw [hA0,hA1,he0,he1]
          exact ambientIsotopy_equivalence.refl _
        · obtain ⟨H,J,hpair,hcore,houtside,hleft,hright⟩ :=
            hWidth M U T δ hδ (lt_of_le_of_ne hδquarter heq)
          simp_rw [← hA0,← hA1] at hpair
          exact ⟨H,hpair⟩
    have hGivenToCommon := hGivenConstructed M
      (h '' (M.cover.projection ⁻¹' Na.closedSet)) W T A δ hδ hδquarter hAcoordinates
    have hCommonPairAmbient : AmbientIsotopy.Rel
        (Set.range (fun z : Circle => (A (z,0)).val) ∪
          Set.range (fun z : Circle => (A (z,1)).val))
        (Set.range (fun z : Circle => (B (z,⟨1/4,by norm_num⟩)).val) ∪
          Set.range (fun z : Circle => (B (z,⟨3/4,by norm_num⟩)).val)) := by
      have hactual := M.actual_raw_core_pair_supported_ambient_motion _ B G hGe
        rCommon hGcore hGrange hSides
      have hRange (u : Interval) :
          Set.range (fun z : Circle => (B (G (z,u))).val) =
            Set.range (fun z : Circle => (A (z,u)).val) := by
        exact congrArg Set.range (funext (fun z => hG (z,u)))
      rw [hRange 0, hRange 1] at hactual
      exact hactual
    exact ambientIsotopy_equivalence.trans hGivenToCommon hCommonPairAmbient
  exact ambientIsotopy_equivalence.trans (ambientIsotopy_equivalence.trans hmove hRT)
    (ambientIsotopy_equivalence.trans hInnerPair (ambientIsotopy_equivalence.symm hRB))

end CurveComplex.HyperellipticModel
