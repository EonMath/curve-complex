import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualRadialSupportTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualChartArcTools
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import RegionalSupportedCrosscutEnhanced
import OrdinaryMoviePreparation
import RegionalWeightedMovieDefinitions
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.GapMatchingTools
import CurveComplexGenusTwo.Topology.TopologicalArcJoin
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.UniformContactPatchTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.CornerGeometryTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.DiskExteriorHalfTools

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies
open CurveComplex.BranchedDoubleCover
open scoped BigOperators
set_option autoImplicit false
noncomputable local instance ordinarySupportedMovieLocalDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem regional_proper_interval_redraw_supported_movie
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (F : Set S) (V : Set ↥F) (E : OpenPartialHomeomorph S Plane)
    (hEtarget : E.target = Metric.ball 0 1)
    (hEclosure : closure E.source ⊆ Subtype.val '' V ∩ interior F)
    (a : C(Interval,↥F)) (ha : IsEmbedding a)
    (ha0 : (a 0).val ∈ frontier F) (ha1 : (a 1).val ∈ frontier F)
    (l r : Interval) (hl : 0 < l) (hlr : l < r) (hr : r < 1)
    (n : Path (a l) (a r)) (hn : IsEmbedding n)
    (hinside : a '' Icc l r ∪ range n ⊆ {y | y.val ∈ E.source})
    (hmeet : range n ∩ range a = {a l,a r}) :
    ∃ H : AmbientIsotopy ↥F,
      (∀ t y, y ∉ V → H.map (t,y) = y) ∧
      (∀ t y, y.val ∈ frontier F → H.map (t,y) = y) ∧
      (∀ t y, y ∈ a '' Iic l ∪ a '' Ici r → H.map (t,y) = y) ∧
      H.finalMap '' range a = (a '' Iic l ∪ a '' Ici r) ∪ range n ∧
      H.finalMap (a 0) = a 0 ∧ H.finalMap (a 1) = a 1 := by
  classical
  let av : C(Interval,S) := ⟨fun t => (a t).val, continuous_subtype_val.comp a.continuous⟩
  have hav : IsEmbedding av := IsEmbedding.subtypeVal.comp ha
  let old : Path (a l).val (a r).val :=
    ⟨⟨fun t => av (intervalAffine l r t),
      av.continuous.comp (intervalSegment l r).continuous⟩,
      by simp [av,intervalAffine], by simp [av,intervalAffine]⟩
  let new : Path (a l).val (a r).val :=
    ⟨⟨fun t => (n t).val, continuous_subtype_val.comp n.continuous⟩,
      congrArg Subtype.val n.source, congrArg Subtype.val n.target⟩
  have hold : IsEmbedding old := by
    apply (old.continuous.isClosedEmbedding ?_).isEmbedding
    intro t u he
    have hp := hav.injective he
    have hq := congrArg Subtype.val hp
    apply Subtype.ext
    dsimp [intervalAffine] at hq
    have hnz : (r:ℝ)-(l:ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlr)
    apply mul_left_cancel₀ hnz
    nlinarith only [hq]
  have hnew : IsEmbedding new := IsEmbedding.subtypeVal.comp hn
  have holdRange : range old = av '' Icc l r := by
    change range (av ∘ intervalAffine l r) = av '' Icc l r
    have hp : range (intervalAffine l r) = uIcc l r := by
      run_tac do
        let env ← Lean.getEnv
        let some (name,_) := env.constants.toList.find? (fun (name,_) =>
          name.toString == "_private.OrdinaryMoviePreparation.0.affine_parameter_range")
          | throwError "Paid affine preparation missing"
        Lean.Elab.Tactic.liftMetaTactic fun goal => goal.apply (Lean.mkConst name)
    rw [range_comp,hp,uIcc_of_le hlr.le]
  have hnewRange : range new = Subtype.val '' range n := by
    change range (Subtype.val ∘ n) = _
    rw [range_comp]
  have holdSource : range old ⊆ E.source := by
    rw [holdRange]
    rintro x ⟨t,ht,rfl⟩
    exact hinside (Or.inl ⟨t,ht,rfl⟩)
  have hnewSource : range new ⊆ E.source := by
    rw [hnewRange]
    rintro x ⟨y,hy,rfl⟩
    exact hinside (Or.inr hy)
  have holdnew : range old ∩ range new = {(a l).val,(a r).val} := by
    apply Subset.antisymm
    · rintro x ⟨hx,hy⟩
      rw [holdRange] at hx
      rw [hnewRange] at hy
      obtain ⟨t,ht,rfl⟩ := hx
      obtain ⟨y,hy,he⟩ := hy
      have he' : y = a t := Subtype.ext he
      have hm : a t ∈ range n ∩ range a := ⟨he' ▸ hy,⟨t,rfl⟩⟩
      rw [hmeet] at hm
      rcases hm with hm | hm
      · exact Or.inl (congrArg Subtype.val hm)
      · exact Or.inr (congrArg Subtype.val hm)
    · intro x hx
      rcases hx with rfl | rfl
      · exact ⟨⟨0,old.source⟩,⟨0,new.source⟩⟩
      · exact ⟨⟨1,old.target⟩,⟨1,new.target⟩⟩
  have hOldPlane := actual_chart_continuous_arc E
    (⟨old,old.continuous⟩ : C(Interval,S)) hold (fun t => holdSource ⟨t,rfl⟩)
  have hNewPlane := actual_chart_continuous_arc E
    (⟨new,new.continuous⟩ : C(Interval,S)) hnew (fun t => hnewSource ⟨t,rfl⟩)
  change IsArcBetween (E '' range old) (E (old 0)) (E (old 1)) at hOldPlane
  change IsArcBetween (E '' range new) (E (new 0)) (E (new 1)) at hNewPlane
  rw [old.source,old.target] at hOldPlane
  rw [new.source,new.target] at hNewPlane
  have hPlaneMeet : (E '' range old) ∩ (E '' range new) =
      {E (a l).val,E (a r).val} := by
    apply Subset.antisymm
    · rintro q ⟨⟨x,hx,rfl⟩,⟨y,hy,he⟩⟩
      have hxy : y = x := E.injOn (hnewSource hy) (holdSource hx) he
      have hm : x ∈ range old ∩ range new := ⟨hx,hxy ▸ hy⟩
      rw [holdnew] at hm
      rcases hm with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro q hq
      rcases hq with rfl | rfl
      · exact ⟨⟨_,⟨0,old.source⟩,rfl⟩,⟨_,⟨0,new.source⟩,rfl⟩⟩
      · exact ⟨⟨_,⟨1,old.target⟩,rfl⟩,⟨_,⟨1,new.target⟩,rfl⟩⟩
  let C := (E '' range old) ∪ (E '' range new)
  have hC : IsJordanCurve C := by
    apply IsJordanCurve.of_two_arcs hOldPlane hNewPlane.reverse
    intro q hqA hqB
    have hm : q ∈ (E '' range old) ∩ (E '' range new) := ⟨hqA,hqB⟩
    rw [hPlaneMeet] at hm
    simpa using hm
  have hCball : C ⊆ Metric.ball (0 : Plane) 1 := by
    intro q hq
    rw [←hEtarget]
    rcases hq with ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩
    · exact E.map_source (holdSource hx)
    · exact E.map_source (hnewSource hx)
  obtain ⟨dp,hdp,hdpB,hdpBall⟩ := actual_jordan_disc_in_open_unit_ball C hC hCball
  have hdpT (t : Metric.closedBall (0 : Plane) 1) : dp t ∈ E.target :=
    hEtarget.symm ▸ hdpBall ⟨t,rfl⟩
  let ds : C(Metric.closedBall (0 : Plane) 1,S) :=
    ⟨fun t => E.symm (dp t), E.symm.continuousOn.comp_continuous dp.continuous hdpT⟩
  have hds : IsEmbedding ds := by
    apply (ds.continuous.isClosedEmbedding ?_).isEmbedding
    intro t u he
    exact hdp.injective (E.symm.injOn (hdpT t) (hdpT u) he)
  have hdsB : ds '' {t | t.val ∈ Metric.sphere (0 : Plane) 1} = range old ∪ range new := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      have hq : dp t ∈ C := hdpB ▸ mem_image_of_mem dp ht
      rcases hq with ⟨y,hy,he⟩ | ⟨y,hy,he⟩
      · left
        change E.symm (dp t) ∈ range old
        rw [←he,E.left_inv (holdSource hy)]
        exact hy
      · right
        change E.symm (dp t) ∈ range new
        rw [←he,E.left_inv (hnewSource hy)]
        exact hy
    · intro hx
      have hxS : x ∈ E.source := hx.elim (fun h => holdSource h) (fun h => hnewSource h)
      have hq : E x ∈ C := by
        rcases hx with hx | hx
        · exact Or.inl ⟨x,hx,rfl⟩
        · exact Or.inr ⟨x,hx,rfl⟩
      rw [←hdpB] at hq
      obtain ⟨t,ht,he⟩ := hq
      refine ⟨t,ht,?_⟩
      change E.symm (dp t) = x
      rw [he,E.left_inv hxS]
  have hdsSource : range ds ⊆ E.source := by
    rintro x ⟨t,rfl⟩
    exact E.map_target (hdpT t)
  have hdsClosed : IsClosed (range ds) := (isCompact_range ds.continuous).isClosed
  have hdsFront : frontier (range ds) = range old ∪ range new := by
    rw [hdsClosed.frontier_eq,CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq ds hds,←hdsB]
    ext x
    constructor
    · rintro ⟨⟨t,rfl⟩,htnot⟩
      refine ⟨t,?_,rfl⟩
      have htge : 1 ≤ dist t.val (0 : Plane) := by
        by_contra hn
        exact htnot ⟨t,lt_of_not_ge hn,rfl⟩
      exact le_antisymm t.property htge
    · rintro ⟨t,ht,rfl⟩
      refine ⟨⟨t,rfl⟩,?_⟩
      rintro ⟨u,hu,he⟩
      have htu := hds.injective he
      subst u
      change dist t.val (0 : Plane) < 1 at hu
      change dist t.val (0 : Plane) = 1 at ht
      linarith only [hu,ht]
  let T : Set S := av '' Iic l ∪ av '' Ici r
  have hTclosed : IsClosed T :=
    (isClosed_Iic.isCompact.image av.continuous).isClosed.union
      (isClosed_Ici.isCompact.image av.continuous).isClosed
  have hOldTail : range old ∩ T = {(a l).val,(a r).val} := by
    rw [holdRange]
    ext x
    constructor
    · rintro ⟨⟨t,ht,rfl⟩,hx⟩
      rcases hx with ⟨u,hu,he⟩ | ⟨u,hu,he⟩
      · have he' := hav.injective he
        subst u
        have ht' : t = l := le_antisymm hu ht.1
        exact Or.inl (congrArg av ht')
      · have he' := hav.injective he
        subst u
        have ht' : t = r := le_antisymm ht.2 hu
        exact Or.inr (congrArg av ht')
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨⟨l,⟨le_rfl,hlr.le⟩,rfl⟩,Or.inl ⟨l,by simp,rfl⟩⟩
      · exact ⟨⟨r,⟨hlr.le,le_rfl⟩,rfl⟩,Or.inr ⟨r,by simp,rfl⟩⟩
  have hNewTail : range new ∩ T ⊆ {(a l).val,(a r).val} := by
    rintro x ⟨hx,hT⟩
    rw [hnewRange] at hx
    obtain ⟨y,hy,he⟩ := hx
    rcases hT with ⟨t,ht,hx⟩ | ⟨t,ht,hx⟩
    all_goals
      have hy' : y = a t := Subtype.ext (he.trans hx.symm)
      have hm : a t ∈ range n ∩ range a := ⟨hy' ▸ hy,⟨t,rfl⟩⟩
      rw [hmeet] at hm
      rcases hm with hm | hm
      · exact Or.inl (hx.symm.trans (congrArg Subtype.val hm))
      · exact Or.inr (hx.symm.trans (congrArg Subtype.val hm))
  have hTailOpenFront (t : Interval) (ht : t < l ∨ r < t) :
      av t ∉ frontier (range ds) := by
    intro hfront
    rw [hdsFront] at hfront
    have hT : av t ∈ T := by
      rcases ht with ht | ht
      · exact Or.inl ⟨t,ht.le,rfl⟩
      · exact Or.inr ⟨t,ht.le,rfl⟩
    have hm : av t ∈ ({(a l).val,(a r).val} : Set S) := by
      rcases hfront with ho | hn'
      · exact hOldTail ▸ (show av t ∈ range old ∩ T from ⟨ho,hT⟩)
      · exact hNewTail ⟨hn',hT⟩
    rcases hm with he | he
    · have he' : t = l := hav.injective he
      rcases ht with ht | ht <;> subst t <;> order
    · have he' : t = r := hav.injective he
      rcases ht with ht | ht <;> subst t <;> order
  have hTailSeparation (P : Set Interval) (hP : IsPreconnected P)
      (hoff : ∀ t ∈ P, av t ∉ frontier (range ds))
      (t0 : Interval) (ht0 : t0 ∈ P) (hzero : av t0 ∉ range ds) :
      av '' P ⊆ (range ds)ᶜ := by
    have hcover : av '' P ⊆ interior (range ds) ∪ (range ds)ᶜ := by
      rintro x ⟨t,ht,rfl⟩
      by_cases hd : av t ∈ range ds
      · left
        by_contra hi
        apply hoff t ht
        rw [hdsClosed.frontier_eq]
        exact ⟨hd,hi⟩
      · exact Or.inr hd
    have hdisjoint : Disjoint (interior (range ds)) (range ds)ᶜ := by
      apply disjoint_left.mpr
      intro x hx hn'
      exact hn' (interior_subset hx)
    rcases (hP.image av av.continuous.continuousOn).subset_or_subset
        isOpen_interior hdsClosed.isOpen_compl hdisjoint hcover with hin | hout
    · exact False.elim (hzero (interior_subset (hin ⟨t0,ht0,rfl⟩)))
    · exact hout
  have hSourceInterior : E.source ⊆ interior F :=
    fun x hx => (hEclosure (subset_closure hx)).2
  have hEndpointOutside (t : Interval) (ht : (a t).val ∈ frontier F) :
      av t ∉ range ds := by
    intro hd
    have hi := hSourceInterior (hdsSource hd)
    exact ht.2 hi
  have hLeftOut : av '' Iio l ⊆ (range ds)ᶜ :=
    hTailSeparation (Iio l) isPreconnected_Iio
      (fun t ht => hTailOpenFront t (Or.inl ht)) 0 hl (hEndpointOutside 0 ha0)
  have hRightOut : av '' Ioi r ⊆ (range ds)ᶜ :=
    hTailSeparation (Ioi r) isPreconnected_Ioi
      (fun t ht => hTailOpenFront t (Or.inr ht)) 1 hr (hEndpointOutside 1 ha1)
  have hEndNotInterior (x : S) (hx : x ∈ ({(a l).val,(a r).val} : Set S)) :
      x ∉ interior (range ds) := by
    have hf : x ∈ frontier (range ds) := by
      rw [hdsFront]
      rcases hx with rfl | rfl
      · exact Or.inl ⟨0,old.source⟩
      · exact Or.inl ⟨1,old.target⟩
    rw [hdsClosed.frontier_eq] at hf
    exact hf.2
  have hTailExterior : Disjoint T (interior (range ds)) := by
    apply disjoint_left.mpr
    intro x hx hi
    rcases hx with ⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩
    · change t ≤ l at ht
      rcases lt_or_eq_of_le ht with ht | ht
      · exact (hLeftOut ⟨t,ht,rfl⟩) (interior_subset hi)
      · subst t
        exact hEndNotInterior _ (Or.inl rfl) hi
    · change r ≤ t at ht
      rcases lt_or_eq_of_le ht with ht | ht
      · exact (hRightOut ⟨t,ht,rfl⟩) (interior_subset hi)
      · subst t
        exact hEndNotInterior _ (Or.inr rfl) hi
  obtain ⟨J,hJB⟩ := actual_jordan_global_unit_circle_chart C hC
  have hJclosed : J '' Metric.closedBall (0 : Plane) 1 = range dp := by
    rw [actual_global_jordan_closed_disk_range C hC J hJB]
    exact (embedded_disc_range_eq_closed_inside dp hdp C hC hdpB).symm
  let Q : Set Plane := J ⁻¹' E.target
  let O : Set Plane := J ⁻¹' (E '' (E.source \ T))
  have hO : IsOpen O := by
    apply J.continuous.isOpen_preimage
    apply E.isOpen_image_of_subset_source
    · exact E.open_source.inter hTclosed.isOpen_compl
    · exact sdiff_subset
  have hOQ : O ⊆ Q := by
    rintro x ⟨y,hy,he⟩
    change J x ∈ E.target
    rw [←he]
    exact E.map_source hy.1
  have hQclosed : Metric.closedBall (0 : Plane) 1 ⊆ Q := by
    intro x hx
    have hq : J x ∈ range dp := by
      rw [←hJclosed]
      exact mem_image_of_mem J hx
    change J x ∈ E.target
    exact hEtarget.symm ▸ hdpBall hq
  have hOball : Metric.ball (0 : Plane) 1 ⊆ O := by
    intro x hx
    have hq : J x ∈ range dp := by
      rw [←hJclosed]
      exact mem_image_of_mem J (Metric.ball_subset_closedBall hx)
    obtain ⟨t,ht⟩ := hq
    have htInt : t.val ∈ Metric.ball (0 : Plane) 1 := by
      by_contra hn'
      have htB : t.val ∈ Metric.sphere (0 : Plane) 1 :=
        le_antisymm t.property (le_of_not_gt hn')
      have hb : dp t ∈ C := hdpB ▸ mem_image_of_mem dp htB
      rw [ht,←hJB] at hb
      obtain ⟨q,hq,he⟩ := hb
      have he' : q = x := J.injective he
      rw [he'] at hq
      have hxn : dist x (0 : Plane) < 1 := hx
      have hqn : dist x (0 : Plane) = 1 := hq
      linarith only [hxn,hqn]
    have hxT : J x ∈ E.target := hQclosed (Metric.ball_subset_closedBall hx)
    refine ⟨E.symm (J x),⟨E.map_target hxT,?_⟩,E.right_inv hxT⟩
    intro hT
    have hi : E.symm (J x) ∈ interior (range ds) := by
      rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq ds hds]
      refine ⟨t,htInt,?_⟩
      change E.symm (dp t) = E.symm (J x)
      rw [ht]
    exact disjoint_left.mp hTailExterior hT hi
  obtain ⟨Rd,hRd,hRdFixed⟩ := actual_distance_radial_homeomorphism O
  have hRdOpen : Rd '' Metric.ball (0 : Plane) 1 ⊆ O := by
    have he : (Rd : Plane → Plane) =
        (fun x => (1 + min 1 (Metric.infDist (NormedSpace.normalize x) Oᶜ / 2)) • x) := funext hRd
    rw [he]
    exact actual_distance_radial_open_support O hOball
  have hRdClosed : Rd '' Metric.closedBall (0 : Plane) 1 ⊆ Q := by
    have he : (Rd : Plane → Plane) =
        (fun x => (1 + min 1 (Metric.infDist (NormedSpace.normalize x) Oᶜ / 2)) • x) := funext hRd
    rw [he]
    exact actual_distance_radial_closed_support O Q hOQ hOball
      (fun x hx => hQclosed (Metric.sphere_subset_closedBall hx))
  have hBoundarySource : range old ∪ range new ⊆ E.source :=
    union_subset holdSource hnewSource
  have hBoundarySphere (x : S) (hx : x ∈ range old ∪ range new) :
      J.symm (E x) ∈ Metric.sphere (0 : Plane) 1 := by
    have hm : E x ∈ C := by
      rcases hx with hx | hx
      · exact Or.inl ⟨x,hx,rfl⟩
      · exact Or.inr ⟨x,hx,rfl⟩
    rw [←hJB] at hm
    obtain ⟨q,hq,he⟩ := hm
    rw [←he,J.symm_apply_apply]
    exact hq
  have hTailForbidden (x : S) (hxS : x ∈ E.source) (hxT : x ∈ T) :
      J.symm (E x) ∉ O := by
    rintro ⟨y,hy,he⟩
    rw [J.apply_symm_apply] at he
    have hyx : y = x := E.injOn hy.1 hxS he
    exact hy.2 (hyx.symm ▸ hxT)
  have hEndL : (a l).val ∈ T := Or.inl ⟨l,by simp,rfl⟩
  have hEndR : (a r).val ∈ T := Or.inr ⟨r,by simp,rfl⟩
  have hOldL : (a l).val ∈ range old := ⟨0,old.source⟩
  have hOldR : (a r).val ∈ range old := ⟨1,old.target⟩
  have hOc : Oᶜ.Nonempty :=
    ⟨J.symm (E (a l).val),hTailForbidden _ (holdSource hOldL) hEndL⟩
  have hEndFixed (x : S) (hx : x ∈ range old ∪ range new) (hxT : x ∈ T) :
      Rd (J.symm (E x)) = J.symm (E x) := by
    apply hRdFixed
    · exact hTailForbidden x (hBoundarySource hx) hxT
    · simpa only [Metric.mem_sphere,dist_zero_right] using hBoundarySphere x hx
  have hBoundaryOffEnds (x : S) (hx : x ∈ range old ∪ range new)
      (hxe : x ∉ ({(a l).val,(a r).val} : Set S)) : x ∉ T := by
    intro hxT
    rcases hx with hx | hx
    · exact hxe (hOldTail ▸ (show x ∈ range old ∩ T from ⟨hx,hxT⟩))
    · exact hxe (hNewTail ⟨hx,hxT⟩)
  obtain ⟨G,hGi,hGc,hGf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (Plane.convex_closedSquare 0 1)
    (by rw [Plane.interior_closedSquare]; exact ⟨0,by simp [Plane.openSquare,Plane.supNorm]⟩)
    (Plane.isBounded_closedSquare 0 1)
  have hGopen : G '' Plane.openSquare 0 1 = Metric.ball (0 : Plane) 1 := by
    simpa only [Plane.interior_closedSquare] using hGi
  have hGclosed : G '' Plane.closedSquare 0 1 = Metric.closedBall (0 : Plane) 1 := by
    simpa only [(Plane.isClosed_closedSquare 0 1).closure_eq] using hGc
  have hGboundary : G '' modelCurve = Metric.sphere (0 : Plane) 1 := by
    simpa only [←modelCurve_eq_frontier] using hGf
  let coordinates := (G.trans Rd).trans J
  let Esq := E.trans coordinates.symm.toOpenPartialHomeomorph
  have hsqSource : Esq.source = E.source := by
    simp [Esq]
  have hsqTarget : Esq.target = coordinates ⁻¹' E.target := by
    simp [Esq]
  have hsqClosed : Plane.closedSquare 0 1 ⊆ Esq.target := by
    rw [hsqTarget]
    intro q hq
    have hb : G q ∈ Metric.closedBall (0 : Plane) 1 := by
      rw [←hGclosed]
      exact mem_image_of_mem G hq
    exact hRdClosed ⟨G q,hb,rfl⟩
  have hsqValue (x : S) : Esq x = G.symm (Rd.symm (J.symm (E x))) := rfl
  have hsqOffEnds (x : S) (hx : x ∈ range old ∪ range new)
      (hxe : x ∉ ({(a l).val,(a r).val} : Set S)) :
      Esq x ∈ Plane.openSquare 0 1 := by
    let q := J.symm (E x)
    have hqSphere : q ∈ Metric.sphere (0 : Plane) 1 := hBoundarySphere x hx
    have hqO : q ∈ O := ⟨x,⟨hBoundarySource hx,hBoundaryOffEnds x hx hxe⟩,
      (J.apply_symm_apply (E x)).symm⟩
    have hqInt := actual_distance_radial_boundary_inside O hO hOc Rd hRd q hqO
      (by simpa only [Metric.mem_sphere,dist_zero_right] using hqSphere)
    rw [←hGopen] at hqInt
    obtain ⟨z,hz,he⟩ := hqInt
    rw [hsqValue]
    change G.symm (Rd.symm q) ∈ Plane.openSquare 0 1
    rw [←he,G.symm_apply_apply]
    exact hz
  have hsqTail (x : S) (hxT : x ∈ T) (hxS : x ∈ Esq.source) :
      Esq x ∉ Plane.openSquare 0 1 := by
    intro hxO
    have hxES : x ∈ E.source := hsqSource ▸ hxS
    have hqBall : G (Esq x) ∈ Metric.ball (0 : Plane) 1 := by
      rw [←hGopen]
      exact mem_image_of_mem G hxO
    rw [hsqValue,G.apply_symm_apply] at hqBall
    have hfree := hRdOpen ⟨Rd.symm (J.symm (E x)),hqBall,rfl⟩
    rw [Rd.apply_symm_apply] at hfree
    exact hTailForbidden x hxES hxT hfree
  let Asq := Esq '' range old
  let Bsq := Esq '' range new
  let u := Esq (a l).val
  let v := Esq (a r).val
  have hAsq : IsArcBetween Asq u v := by
    have hh := actual_chart_continuous_arc Esq (⟨old,old.continuous⟩ : C(Interval,S)) hold
      (fun t => hsqSource.symm ▸ holdSource ⟨t,rfl⟩)
    change IsArcBetween (Esq '' range old) (Esq (old 0)) (Esq (old 1)) at hh
    rw [old.source,old.target] at hh
    exact hh
  have hBsq : IsArcBetween Bsq u v := by
    have hh := actual_chart_continuous_arc Esq (⟨new,new.continuous⟩ : C(Interval,S)) hnew
      (fun t => hsqSource.symm ▸ hnewSource ⟨t,rfl⟩)
    change IsArcBetween (Esq '' range new) (Esq (new 0)) (Esq (new 1)) at hh
    rw [new.source,new.target] at hh
    exact hh
  have hsqEndBoundary (x : S) (hx : x ∈ range old ∪ range new) (hxT : x ∈ T) :
      Esq x ∈ modelCurve := by
    have he' := congrArg Rd.symm (hEndFixed x hx hxT)
    simp only [Rd.symm_apply_apply] at he'
    rw [hsqValue,←he']
    have hs := hBoundarySphere x hx
    rw [←hGboundary] at hs
    obtain ⟨q,hq,heq⟩ := hs
    rw [←heq,G.symm_apply_apply]
    exact hq
  have hu : u ∈ modelCurve := hsqEndBoundary _ (Or.inl hOldL) hEndL
  have hv : v ∈ modelCurve := hsqEndBoundary _ (Or.inl hOldR) hEndR
  have hsqProper (A : Set S) (hA : A ⊆ range old ∪ range new) :
      Esq '' A \ {u,v} ⊆ Plane.openSquare 0 1 := by
    rintro y ⟨⟨x,hx,rfl⟩,hye⟩
    apply hsqOffEnds x (hA hx)
    intro hxe
    apply hye
    rcases hxe with hxe | hxe
    · left; rw [hxe]
    · right; rw [hxe]; rfl
  have hsqInterior : {y : S | y ∈ Esq.source ∧ Esq y ∈ Plane.openSquare 0 1} ⊆ interior F :=
    fun x hx => hSourceInterior (hsqSource ▸ hx.1)
  obtain ⟨H,hfix,hfront,Hs,hHs,hmove⟩ := regional_square_crosscut_supported_isotopy
    S F Esq hsqClosed Asq Bsq u v hAsq hBsq hu hv
    (hsqProper _ subset_union_left) (hsqProper _ subset_union_right) hsqInterior
  have hPull (P : Set S) (hP : P ⊆ Esq.source) :
      {z : S | z ∈ Esq.source ∧ Esq z ∈ Esq '' P} = P := by
    ext x
    constructor
    · rintro ⟨hxS,y,hy,he⟩
      exact Esq.injOn (hP hy) hxS he ▸ hy
    · intro hx
      exact ⟨hP hx,x,hx,rfl⟩
  change Hs.finalMap '' {z : S | z ∈ Esq.source ∧ Esq z ∈ Esq '' range old} =
    {z : S | z ∈ Esq.source ∧ Esq z ∈ Esq '' range new} at hmove
  rw [hPull (range old) (fun x hx => hsqSource.symm ▸ holdSource hx),
    hPull (range new) (fun x hx => hsqSource.symm ▸ hnewSource hx)] at hmove
  have hOldF : range old ⊆ F := by
    rw [holdRange]
    rintro x ⟨t,ht,rfl⟩
    exact (a t).property
  have hSubtypeOld : {y : ↥F | y.val ∈ range old} = a '' Icc l r := by
    ext y
    constructor
    · intro hy
      rw [holdRange] at hy
      obtain ⟨t,ht,he⟩ := hy
      exact ⟨t,ht,Subtype.ext he⟩
    · rintro ⟨t,ht,rfl⟩
      rw [holdRange]
      exact ⟨t,ht,rfl⟩
  have hSubtypeNew : {y : ↥F | y.val ∈ range new} = range n := by
    rw [hnewRange]
    ext y
    constructor
    · rintro ⟨z,hz,he⟩
      exact Subtype.ext he ▸ hz
    · intro hy
      exact ⟨y,hy,rfl⟩
  have hmoveSub : H.finalMap '' (a '' Icc l r) = range n := by
    have hm := regional_lifted_crosscut_trace_transport F (range old) (range new)
      hOldF Hs H hHs hmove
    rw [hSubtypeOld,hSubtypeNew] at hm
    exact hm
  have hTailVal (y : ↥F) (hy : y ∈ a '' Iic l ∪ a '' Ici r) : y.val ∈ T := by
    rcases hy with ⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩
    · exact Or.inl ⟨t,ht,rfl⟩
    · exact Or.inr ⟨t,ht,rfl⟩
  have hTailFix : ∀ t y, y ∈ a '' Iic l ∪ a '' Ici r → H.map (t,y) = y := by
    intro t y hy
    apply hfix t y
    intro hyS
    exact hsqTail y.val (hTailVal y hy) hyS.1 hyS.2
  have hOutside : ∀ t y, y ∉ V → H.map (t,y) = y := by
    intro t y hy
    apply hfix t y
    intro hyS
    have heS : y.val ∈ E.source := hsqSource ▸ hyS.1
    obtain ⟨z,hz,he⟩ := (hEclosure (subset_closure heS)).1
    exact hy (Subtype.ext he ▸ hz)
  have hRangeSplit : range a = (a '' Iic l ∪ a '' Ici r) ∪ a '' Icc l r := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      by_cases htl : t ≤ l
      · exact Or.inl (Or.inl ⟨t,htl,rfl⟩)
      by_cases hrt : r ≤ t
      · exact Or.inl (Or.inr ⟨t,hrt,rfl⟩)
      · exact Or.inr ⟨t,⟨le_of_not_ge htl,le_of_not_ge hrt⟩,rfl⟩
    · rintro ((⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩) | ⟨t,ht,rfl⟩)
      all_goals exact ⟨t,rfl⟩
  have hTailImage : H.finalMap '' (a '' Iic l ∪ a '' Ici r) = a '' Iic l ∪ a '' Ici r := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      change H.map (1,z) ∈ a '' Iic l ∪ a '' Ici r
      rw [hTailFix 1 z hz]
      exact hz
    · intro hy
      exact ⟨y,hy,hTailFix 1 y hy⟩
  refine ⟨H,hOutside,hfront,hTailFix,?_,hfront 1 (a 0) ha0,hfront 1 (a 1) ha1⟩
  rw [hRangeSplit,image_union,hTailImage,hmoveSub]
