import ActualChartTwoRayDiskSector
import Mathlib.Analysis.Convex.Join
import EmbeddedDiskSubintervalExteriorSign
import RegionalDiskArcLift
import CurveComplexGenusTwo.Topology.ActualHarerDiskGluing.CompactKernelTransport
import Schoenflies.JordanSchoenflies
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import HalfJointCollarCornerPacket
import RegionalWeightedHalfFanProof
import HalfStripLocalization
import Lean
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.CornerGeometryTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.UniformContactPatchTools
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalFiniteFaceTransport
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalRelativeSupportNeighborhood
import CurveComplexGenusTwo.Topology.FrontierCircle.PathGluingProbe

import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualInternalCollarCalibration
open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies RegionalChordNormalization
open scoped BigOperators
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 2000000

open Lean Elab Term
elab "paid_active_narrowing" : term => do
 let n := Name.str (Name.num (Name.str (Name.str .anonymous "_private") "HalfStripLocalization") 0) "half_strip_active_compact_narrowing"
 return ← mkConstWithLevelParams n


/-- Exact local existence obligation from the original M2 context. The chosen
collars and corner chart are joint outputs; no successful extension, rail,
profile, count, or movie premise is added. -/
theorem regional_half_joint_calibrated_collar_corner_exists
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
        (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ boundaryCircle) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
          {y | y.val ∈ boundaryCircle}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    let IntrinsicArcVertex := Quot (intrinsicArcRel)
    let intrinsicArcFaces : Set (Finset (IntrinsicArcVertex)) :=
      {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc,
        (∀ u, Quot.mk (intrinsicArcRel) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
    let intrinsicArcComplex : AbstractSimplicialComplex (IntrinsicArcVertex) := {
      faces := intrinsicArcFaces
      isRelLowerSet_faces := by
        intro τ hτ
        refine ⟨hτ.1,?_⟩
        intro μ hμτ hne
        obtain ⟨rep,hclass,hd⟩ := hτ.2
        refine ⟨hne,(fun u => rep ⟨u.val,hμτ u.property⟩),?_,?_⟩
        · intro u
          exact hclass ⟨u.val,hμτ u.property⟩
        · intro u w huw
          apply hd
          intro he
          exact huw (Subtype.ext (congrArg (fun z : ↥τ => z.val) he))
      singleton_mem := by
        intro u
        obtain ⟨a,ha⟩ := Quot.exists_rep u
        refine ⟨Finset.singleton_nonempty u,(fun _ => a),?_,?_⟩
        · intro z
          exact ha.trans (Finset.mem_singleton.mp z.property).symm
        · intro z w hzw
          exact False.elim (hzw (Subtype.ext
            ((Finset.mem_singleton.mp z.property).trans (Finset.mem_singleton.mp w.property).symm))) }
    ∀ (ι : Type) [Fintype ι] (r : ι → IntrinsicEssentialArc)
      (α : IntrinsicEssentialArc),
      FamilyInvariant (fun i => (r i).val.val) α.val.val →
      (∀ i j : Option ι, i ≠ j →
        RegionalEmbeddedFamily.RegionalAllInteriorContactsCross F
          (augmented (fun i => (r i).val.val) α.val.val i)
          (augmented (fun i => (r i).val.val) α.val.val j)) →
      ∀ v w : ι, v ≠ w →
      ∀ d : PairedHalfBigonDisk F {y | y.val ∈ boundaryCircle} {y | y.val ∈ frontier F} (r v).val.val (r w).val.val,
      ∀ V : Set ↥F, IsOpen V → range d.disk ⊆ V →
        Disjoint (closure V) ({y : ↥F | y.val ∈ frontier F} \ {y | y.val ∈ boundaryCircle}) →
        let C₀ : Set ↥F := {d.first 1}
        let removed := fun j : ι => ((range d.first \ C₀) ∩ range (r j).val.val).ncard
        let guiding := fun j : ι => ((range d.second \ C₀) ∩ range (r j).val.val).ncard
        let offset := fun j : ι =>
          ((range (r v).val.val \ range d.first) ∩ range (r j).val.val).ncard +
            (C₀ ∩ range (r j).val.val).ncard
        (∑ j : ι, if j ≠ v ∧ j ≠ w then guiding j else 0) ≤
          (∑ j : ι, if j ≠ v ∧ j ≠ w then removed j else 0) →
        ∀ fan : FiniteFanCarrier F
          (augmented (fun i => (r i).val.val) α.val.val) {some v,some w}
          (range d.first ∪ range d.second) V (range d.disk)
          (forbiddenEndpoints (fun i => (r i).val.val) α.val.val v),
        ∀ gap : BoundaryEndpointGap {y : ↥F | y.val ∈ boundaryCircle} V
          (forbiddenEndpoints (fun i => (r i).val.val) α.val.val v) d.boundarySide,
        Nonempty (RegionalHalfJointCollarCornerPacket F {y | y.val ∈ boundaryCircle}
          {y : ↥F | y.val ∈ frontier F}
          (fun i => (r i).val.val) α.val.val v w d V fan gap) := by
  classical
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    ι inst r α hinv hcross v w hvw d V hV hdV havoid
    C₀ removed guiding offset hcheap fan gap
  let : ClosedSurface S := Classical.choice hS.2.1
  let a := (r v).val.val
  let b := (r w).val.val
  let f := augmented (fun i => (r i).val.val) α.val.val
  have hBF : boundaryCircle ⊆ frontier F := by
    dsimp only [boundaryCircle]
    rw [hfrontier]
    exact subset_union_left
  have hfirst0 : d.first 0 = a d.aStart := by
    simpa [a,CurveComplex.BranchedDoubleCover.intervalAffine] using d.first_eq 0
  have hfirst1 : d.first 1 = a d.aFinish := by
    simpa [a,CurveComplex.BranchedDoubleCover.intervalAffine] using d.first_eq 1
  have hsecond0 : d.second 0 = b d.bStart := by
    simpa [b,CurveComplex.BranchedDoubleCover.intervalAffine] using d.second_eq 0
  have hsecond1 : d.second 1 = b d.bFinish := by
    simpa [b,CurveComplex.BranchedDoubleCover.intervalAffine] using d.second_eq 1
  have hfirstV : range d.first ⊆ V := by
    intro y hy
    apply hdV
    have hm : y ∈ range d.disk ∩ range a := by
      rw [d.whole_first]
      exact hy
    exact hm.1
  have hsecondV : range d.second ⊆ V := by
    intro y hy
    apply hdV
    have hm : y ∈ range d.disk ∩ range b := by
      rw [d.whole_second]
      exact hy
    exact hm.1
  have hstartEndpoint : d.aStart = 0 ∨ d.aStart = 1 := by
    by_cases h0 : d.aStart = 0
    · exact Or.inl h0
    by_cases h1 : d.aStart = 1
    · exact Or.inr h1
    exact False.elim ((r v).val.property.2.2.2 d.aStart
      ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩
      (hBF (show (a d.aStart).val ∈ boundaryCircle from hfirst0 ▸ d.first_zero)))
  have hbstartEndpoint : d.bStart = 0 ∨ d.bStart = 1 := by
    by_cases h0 : d.bStart = 0
    · exact Or.inl h0
    by_cases h1 : d.bStart = 1
    · exact Or.inr h1
    exact False.elim ((r w).val.property.2.2.2 d.bStart
      ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩
      (hBF (show (b d.bStart).val ∈ boundaryCircle from hsecond0 ▸ d.second_zero)))
  have hfinishInterior : d.aFinish ∈ Ioo (0 : Interval) 1 := by
    have h0 : d.aFinish ≠ 0 := by
      intro he
      apply d.corner_off_frontier
      change (d.first 1).val ∈ frontier F
      rw [hfirst1,he]
      exact hBF (r v).val.property.2.1
    have h1 : d.aFinish ≠ 1 := by
      intro he
      apply d.corner_off_frontier
      change (d.first 1).val ∈ frontier F
      rw [hfirst1,he]
      exact hBF (r v).val.property.2.2.1
    exact ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩
  let clock : Interval ≃ₜ Interval :=
    if d.aStart = 0 then Homeomorph.refl _ else unitInterval.symmHomeomorph
  have hclockStart : clock 0 = d.aStart := by
    rcases hstartEndpoint with h0 | h1
    · simp [clock,h0]
    · simp [clock,h1]
  let cornerTime : Interval := clock.symm d.aFinish
  have hcornerTime : cornerTime ∈ Ioo (0 : Interval) 1 := by
    by_cases h0 : d.aStart = 0
    · simpa [cornerTime,clock,h0] using hfinishInterior
    · constructor
      · simpa [cornerTime,clock,h0] using unitInterval.symm_lt_symm.mpr hfinishInterior.2
      · simpa [cornerTime,clock,h0] using unitInterval.symm_lt_symm.mpr hfinishInterior.1
  let aclock : C(Interval,↥F) := a.comp ⟨clock,clock.continuous⟩
  have haclock : IsEmbedding aclock := (r v).val.property.1.comp clock.isEmbedding
  have hclockCorner : aclock cornerTime = d.first 1 := by
    simpa [aclock,cornerTime] using hfirst1.symm
  have hpv : d.first 1 ∈ range (f (some v)) := by
    exact ⟨d.aFinish,hfirst1.symm⟩
  have hpw : d.first 1 ∈ range (f (some w)) := by
    exact ⟨d.bFinish,hsecond1.symm.trans d.corner_eq.symm⟩
  have hpEvent : d.first 1 ∈ fan.events := by
    rw [fan.events_exact]
    refine ⟨hfirstV (mem_range_self 1),Or.inl (mem_range_self 1),some v,by simp,
      some w,by simpa using hvw, hpv,hpw⟩
  obtain ⟨cornerFan,hcornerNested,hcornerLeftAxis,hcornerRightAxis,hcornerSigns⟩ :=
    fan.selected_axis_fans ⟨d.first 1,hpEvent⟩ (some v) (by simp) hpv
  have hselectedOpposite : ∀ h : d.first 1 ∈ range b,
      incidentPorts f (d.first 1) cornerFan.chart cornerFan.left cornerFan.right
        (⟨some w,h⟩,false) 1 *
      incidentPorts f (d.first 1) cornerFan.chart cornerFan.left cornerFan.right
        (⟨some w,h⟩,true) 1 < 0 := by
    intro h
    rcases hcornerSigns ⟨some w,h⟩ (by simpa using Ne.symm hvw) with hs | hs
    · exact mul_neg_of_pos_of_neg hs.1 hs.2
    · exact mul_neg_of_neg_of_pos hs.1 hs.2
  have haugFinite : ∀ k : Option ι, k ≠ some v →
      (range a ∩ range (f k)).Finite := by
    intro k hk
    cases k with
    | none => simpa [a,f,augmented,inter_comm] using hinv.2.2.2.2 v
    | some j =>
      have hj : v ≠ j := by intro he; apply hk; simp [he]
      simpa [a,f,augmented] using hinv.1 v j hj
  let K : Set ↥F := ⋃ k : {k : Option ι // k ≠ some v}, range (f k.val)
  have hfiniteK : (range aclock ∩ K).Finite := by
    rw [inter_iUnion]
    apply finite_iUnion
    intro k
    apply (haugFinite k.val k.property).subset
    rintro y ⟨⟨t,rfl⟩,hy⟩
    exact ⟨⟨clock t,rfl⟩,hy⟩
  have hcornerK : aclock cornerTime ∈ K := by
    rw [hclockCorner]
    exact mem_iUnion.mpr ⟨⟨some w,by simpa using Ne.symm hvw⟩,hpw⟩
  obtain ⟨l,u,hl,hcornerTimeu,hgap⟩ := regional_proper_arc_isolated_contact_gap
    aclock haclock K hfiniteK cornerTime hcornerTime hcornerK
  have hparam : range (CurveComplex.BranchedDoubleCover.intervalAffine
      (0 : Interval) cornerTime) = Icc (0 : Interval) cornerTime := by
    apply Subset.antisymm
    · rintro z ⟨t,rfl⟩
      exact CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hcornerTime.1.le t
    · have h0 : (0 : Interval) ∈ range
          (CurveComplex.BranchedDoubleCover.intervalAffine 0 cornerTime) :=
        ⟨0,by simp [CurveComplex.BranchedDoubleCover.intervalAffine]⟩
      have h1 : cornerTime ∈ range
          (CurveComplex.BranchedDoubleCover.intervalAffine 0 cornerTime) :=
        ⟨1,by simp [CurveComplex.BranchedDoubleCover.intervalAffine]⟩
      have hc : Continuous (CurveComplex.BranchedDoubleCover.intervalAffine
          (0 : Interval) cornerTime) :=
        (CurveComplex.BranchedDoubleCover.intervalSegment (0 : Interval) cornerTime).continuous
      simpa [uIcc_of_le hcornerTime.1.le] using
        (isPreconnected_range hc).ordConnected.uIcc_subset h0 h1
  have hfirstClock : ∀ t, d.first t = aclock
      (CurveComplex.BranchedDoubleCover.intervalAffine 0 cornerTime t) := by
    intro t
    rw [d.first_eq]
    apply congrArg a
    apply Subtype.ext
    by_cases h0 : d.aStart = 0
    · simp [aclock,cornerTime,clock,h0,CurveComplex.BranchedDoubleCover.intervalAffine]
    · have h1 := hstartEndpoint.resolve_left h0
      simp [aclock,cornerTime,clock,h0,h1,CurveComplex.BranchedDoubleCover.intervalAffine,
        unitInterval.coe_symm_eq]
      ring
  have hfirstRange : range d.first = aclock '' Icc (0 : Interval) cornerTime := by
    have he : (d.first : Interval → ↥F) = aclock ∘
        CurveComplex.BranchedDoubleCover.intervalAffine 0 cornerTime := funext hfirstClock
    rw [he,range_comp,hparam]
  let U : Set ↥F := V ∩ chartPull F cornerFan.chart (Metric.ball (0 : Plane) 1)
  have hU : IsOpen U := hV.inter
    ((cornerFan.chart.isOpen_inter_preimage Metric.isOpen_ball).preimage continuous_subtype_val)
  have hcornerU : aclock cornerTime ∈ U := by
    rw [hclockCorner]
    refine ⟨hfirstV (mem_range_self 1),cornerFan.contact_in_source,?_⟩
    rw [cornerFan.contact_zero]
    simp
  obtain ⟨ll,uu,hnbd,hUU⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨0,hcornerTime.1⟩ ⟨1,hcornerTime.2⟩).mp
      ((hU.preimage aclock.continuous).mem_nhds hcornerU)
  obtain ⟨cut,hcutLower,hcutUpper⟩ := exists_between (lt_min hcornerTimeu hnbd.2)
  have hcutu : cut < u := hcutUpper.trans_le (min_le_left _ _)
  have hcutuu : cut < uu := hcutUpper.trans_le (min_le_right _ _)
  have hcut : cut ∈ Ioo (0 : Interval) 1 :=
    ⟨hcornerTime.1.trans hcutLower,hcutu.trans_le u.property.2⟩
  have hprefix : aclock '' Icc (0 : Interval) cut ⊆ V := by
    rintro y ⟨t,ht,rfl⟩
    by_cases htc : t ≤ cornerTime
    · apply hfirstV
      rw [hfirstRange]
      exact ⟨t,⟨ht.1,htc⟩,rfl⟩
    · exact (hUU ⟨hnbd.1.trans (lt_of_not_ge htc),ht.2.trans_lt hcutuu⟩).1
  have hpadded : Disjoint (aclock '' Ioc cornerTime cut) K := by
    apply disjoint_left.mpr
    rintro y ⟨t,ht,rfl⟩ hy
    have he := (hgap t ⟨hl.trans ht.1,ht.2.trans_lt hcutu⟩).mp hy
    exact (ne_of_gt ht.1) he
  have htail : aclock '' Icc cut (1 : Interval) ⊆ range a \ range d.first := by
    rintro y ⟨t,ht,rfl⟩
    refine ⟨⟨clock t,rfl⟩,?_⟩
    rw [hfirstRange]
    rintro ⟨s,hs,he⟩
    have hst := haclock.injective he
    exact (not_le_of_gt (hcutLower.trans_le ht.1)) (hst ▸ hs.2)
  have hcutWindow : aclock cut ∈ chartPull F cornerFan.chart (Metric.ball (0 : Plane) 1) :=
    (hUU ⟨hnbd.1.trans hcutLower,hcutuu⟩).2
  obtain ⟨oldStrip₀,hOld₀,hOldCenter₀,hOldEnds₀,hOldInterior₀,hOldOpen₀⟩ :=
    regional_original_proper_arc_has_F_strip S g hg hS x R hR htarget
      F hFcompact hbase houtside J c hbaseDisjoint hfrontier
      a (r v).val.property.1 (r v).val.property.2.1
      (r v).val.property.2.2.1 (r v).val.property.2.2.2
  obtain ⟨guideStrip₀,hGuide₀,hGuideCenter₀,hGuideEnds₀,hGuideInterior₀,hGuideOpen₀⟩ :=
    regional_original_proper_arc_has_F_strip S g hg hS x R hR htarget
      F hFcompact hbase houtside J c hbaseDisjoint hfrontier
      b (r w).val.property.1 (r w).val.property.2.1
      (r w).val.property.2.2.1 (r w).val.property.2.2.2
  have hactiveCenter : ∀ t ∈ clock '' Icc (0 : Interval) cut,
      oldStrip₀ (t,⟨0,by norm_num⟩) ∈ V := by
    rintro t ⟨s,hs,rfl⟩
    rw [hOldCenter₀]
    exact hprefix ⟨s,hs,rfl⟩
  obtain ⟨oldStrip,activeWindow,hActiveOpen,hActivePrefix,hOld,hOldCenter,
    hOldActive,hOldEnds,hOldInterior,hOldOpen⟩ :=
    paid_active_narrowing F boundaryCircle oldStrip₀ hOld₀ hOldEnds₀ hOldInterior₀
      hOldOpen₀ (clock '' Icc (0 : Interval) cut)
      (isCompact_Icc.image clock.continuous) V hV hactiveCenter
  have hOldCenterActual : ∀ t, oldStrip (t,⟨0,by norm_num⟩) = a t := by
    intro t
    rw [hOldCenter,hOldCenter₀]
  have hsecondParam : range (CurveComplex.BranchedDoubleCover.intervalAffine
      d.bStart d.bFinish) = Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) := by
    apply Subset.antisymm
    · rintro z ⟨t,rfl⟩
      change min d.bStart d.bFinish ≤ _ ∧ _ ≤ max d.bStart d.bFinish
      have ht0 := t.property.1
      have ht1 := t.property.2
      dsimp [CurveComplex.BranchedDoubleCover.intervalAffine]
      constructor
      · change (min d.bStart d.bFinish : ℝ) ≤
          (1-(t : ℝ))*(d.bStart : ℝ)+(t : ℝ)*(d.bFinish : ℝ)
        have hm0 : (min d.bStart d.bFinish : ℝ) ≤ (d.bStart : ℝ) := min_le_left _ _
        have hm1 : (min d.bStart d.bFinish : ℝ) ≤ (d.bFinish : ℝ) := min_le_right _ _
        nlinarith
      · change (1-(t : ℝ))*(d.bStart : ℝ)+(t : ℝ)*(d.bFinish : ℝ) ≤
          (max d.bStart d.bFinish : ℝ)
        have hm0 : (d.bStart : ℝ) ≤ (max d.bStart d.bFinish : ℝ) := le_max_left _ _
        have hm1 : (d.bFinish : ℝ) ≤ (max d.bStart d.bFinish : ℝ) := le_max_right _ _
        nlinarith
    · have h0 : d.bStart ∈ range
          (CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish) :=
        ⟨0,by simp [CurveComplex.BranchedDoubleCover.intervalAffine]⟩
      have h1 : d.bFinish ∈ range
          (CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish) :=
        ⟨1,by simp [CurveComplex.BranchedDoubleCover.intervalAffine]⟩
      have hc : Continuous (CurveComplex.BranchedDoubleCover.intervalAffine
          d.bStart d.bFinish) :=
        (CurveComplex.BranchedDoubleCover.intervalSegment d.bStart d.bFinish).continuous
      exact (isPreconnected_range hc).ordConnected.uIcc_subset h0 h1
  have hsecondRange : range d.second =
      b '' Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) := by
    have he : (d.second : Interval → ↥F) = b ∘
        CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish :=
      funext d.second_eq
    rw [he,range_comp,hsecondParam]
  have hguideCenter : ∀ t ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish),
      guideStrip₀ (t,⟨0,by norm_num⟩) ∈ V := by
    intro t ht
    rw [hGuideCenter₀]
    apply hsecondV
    rw [hsecondRange]
    exact ⟨t,ht,rfl⟩
  obtain ⟨guideStrip,guideWindow,hGuideWindowOpen,hGuideSelected,hGuide,hGuideCenter,
    hGuideActive,hGuideEnds,hGuideInterior,hGuideOpen⟩ :=
    paid_active_narrowing F boundaryCircle guideStrip₀ hGuide₀ hGuideEnds₀ hGuideInterior₀
      hGuideOpen₀ (Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish))
      isCompact_Icc V hV hguideCenter
  have hGuideCenterActual : ∀ t, guideStrip (t,⟨0,by norm_num⟩) = b t := by
    intro t
    rw [hGuideCenter,hGuideCenter₀]
  let guideClock : Interval ≃ₜ Interval :=
    if d.bStart = 0 then Homeomorph.refl _ else unitInterval.symmHomeomorph
  have hguideClockStart : guideClock 0 = d.bStart := by
    rcases hbstartEndpoint with h0 | h1
    · simp [guideClock,h0]
    · simp [guideClock,h1]
  let boundaryLine : C(Icc (-1 : ℝ) 1,↥F) :=
    ⟨fun u => guideStrip (d.bStart,u),guideStrip.continuous.comp
      (continuous_const.prodMk continuous_id)⟩
  have hBoundaryLine : IsEmbedding boundaryLine := by
    exact hGuide.comp ((continuous_const.prodMk continuous_id).isClosedEmbedding
      (by intro u v he; exact congrArg Prod.snd he)).isEmbedding
  have hBoundaryZero : boundaryLine ⟨0,by norm_num⟩ = d.second 0 := by
    exact (hGuideCenterActual _).trans hsecond0.symm
  have hBoundaryBV : range boundaryLine ⊆ {y : ↥F | y.val ∈ boundaryCircle} ∩ V := by
    rintro y ⟨u,rfl⟩
    refine ⟨?_,hGuideActive _ (hGuideSelected ⟨min_le_left _ _,le_max_left _ _⟩) u⟩
    change (guideStrip (d.bStart,u)).val ∈ boundaryCircle
    rcases hbstartEndpoint with h0 | h1
    · rw [h0]
      exact (hGuideEnds u).1
    · rw [h1]
      exact (hGuideEnds u).2
  have hguideClockOrder : StrictMono guideClock ∨ StrictAnti guideClock := by
    by_cases h0 : d.bStart = 0
    · left
      simpa [guideClock,h0] using (strictMono_id : StrictMono (fun t : Interval => t))
    · right
      intro s t hst
      simpa [guideClock,h0] using unitInterval.symm_lt_symm.mpr hst
  have hproper (k : Option ι) : IsEmbedding (f k) ∧
      ((f k) 0).val ∈ boundaryCircle ∧ ((f k) 1).val ∈ boundaryCircle ∧
      ∀ t ∈ Ioo (0 : Interval) 1, ((f k) t).val ∉ frontier F := by
    cases k with
    | none => exact α.val.property
    | some k => exact (r k).val.property
  have hends (i j : Option ι) (hij : i ≠ j) :
      f i 0 ≠ f j 0 ∧ f i 0 ≠ f j 1 ∧ f i 1 ≠ f j 0 ∧ f i 1 ≠ f j 1 := by
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        exact ⟨(fun h => hinv.2.2.1 j ⟨0,h.symm⟩),
          (fun h => hinv.2.2.1 j ⟨1,h.symm⟩),
          (fun h => hinv.2.2.2.1 j ⟨0,h.symm⟩),
          (fun h => hinv.2.2.2.1 j ⟨1,h.symm⟩)⟩
    | some i =>
      cases j with
      | none =>
        exact ⟨(fun h => hinv.2.2.1 i ⟨0,h⟩),
          (fun h => hinv.2.2.2.1 i ⟨0,h⟩),
          (fun h => hinv.2.2.1 i ⟨1,h⟩),
          (fun h => hinv.2.2.2.1 i ⟨1,h⟩)⟩
      | some j => exact hinv.2.1 i j (fun h => hij (congrArg some h))
  have hboundaryOthers : ∀ k : Option ι, k ≠ some w → d.second 0 ∉ range (f k) := by
    intro k hk
    rintro ⟨t,ht⟩
    have htFrontier : ((f k) t).val ∈ frontier F := by
      rw [ht]
      exact hBF d.second_zero
    have htEndpoint : t = 0 ∨ t = 1 := by
      by_cases ht0 : t = 0
      · exact Or.inl ht0
      by_cases ht1 : t = 1
      · exact Or.inr ht1
      exact False.elim ((hproper k).2.2.2 t
        ⟨bot_lt_iff_ne_bot.mpr ht0,lt_top_iff_ne_top.mpr ht1⟩ htFrontier)
    have he : f (some w) d.bStart = f k t := hsecond0.symm.trans ht.symm
    have hfour := hends (some w) k (Ne.symm hk)
    rcases hbstartEndpoint with hb0 | hb1 <;> rcases htEndpoint with ht0 | ht1
    · exact hfour.1 (by simpa [hb0,ht0] using he)
    · exact hfour.2.1 (by simpa [hb0,ht1] using he)
    · exact hfour.2.2.1 (by simpa [hb1,ht0] using he)
    · exact hfour.2.2.2 (by simpa [hb1,ht1] using he)
  let outgoingObstacles : Set ↥F := ⋃ k : {k : Option ι // k ≠ some w}, range (f k.val)
  have houtCompact : IsCompact outgoingObstacles :=
    isCompact_iUnion (fun k => isCompact_range (f k.val).continuous)
  have houtAvoid : d.second 0 ∉ outgoingObstacles := by
    intro h
    obtain ⟨k,hk⟩ := mem_iUnion.mp h
    exact hboundaryOthers k.val k.property hk
  have hzeroOpen : (⟨0,by norm_num⟩ : Icc (-1 : ℝ) 1) ∈
      boundaryLine ⁻¹' outgoingObstaclesᶜ := by
    change boundaryLine ⟨0,by norm_num⟩ ∉ outgoingObstacles
    rwa [hBoundaryZero]
  obtain ⟨outRadius,houtRadius,houtBall⟩ := Metric.isOpen_iff.mp
    (houtCompact.isClosed.isOpen_compl.preimage boundaryLine.continuous)
    ⟨0,by norm_num⟩ hzeroOpen
  let bound : ℝ := min outRadius 1 / 2
  have hbound : 0 < bound := by dsimp [bound]; positivity
  have hboundRadius : bound < outRadius := by
    dsimp [bound]
    linarith [min_le_left outRadius 1]
  have hboundOne : bound < 1 := by
    dsimp [bound]
    linarith [min_le_right outRadius 1]
  have hboundaryLocal : boundaryLine '' {u | |u.val| < bound} ⊆
      {y : ↥F | y.val ∈ boundaryCircle} ∩ V := by
    rintro y ⟨u,hu,rfl⟩
    exact hBoundaryBV ⟨u,rfl⟩
  have houtgoingClear : ∀ k : Option ι, k ≠ some w →
      Disjoint (boundaryLine '' {u | |u.val| < bound}) (range (f k)) := by
    intro k hk
    apply disjoint_left.mpr
    rintro y ⟨u,hu,rfl⟩ hy
    have hball : u ∈ Metric.ball (⟨0,by norm_num⟩ : Icc (-1 : ℝ) 1) outRadius := by
      change dist (u.val : ℝ) 0 < outRadius
      simpa [Real.dist_eq] using hu.trans hboundRadius
    exact houtBall hball (mem_iUnion.mpr ⟨⟨k,hk⟩,hy⟩)
  let beta : Ioo (0 : ℝ) bound → ↥F := fun ρ =>
    boundaryLine ⟨ρ.val,⟨by linarith [ρ.property.1],ρ.property.2.le.trans hboundOne.le⟩⟩
  have hbetaEq : ∀ ρ, ∃ u : Icc (-1 : ℝ) 1,
      u.val = ρ.val ∧ beta ρ = boundaryLine u := by
    intro ρ
    exact ⟨⟨ρ.val,⟨by linarith [ρ.property.1],ρ.property.2.le.trans hboundOne.le⟩⟩,rfl,rfl⟩
  have hbetaBV : ∀ ρ, beta ρ ∈ {y : ↥F | y.val ∈ boundaryCircle} ∩ V := by
    intro ρ
    exact hboundaryLocal ⟨_,by simpa [abs_of_pos ρ.property.1] using ρ.property.2,rfl⟩
  have hbetaMissGuide : ∀ ρ, beta ρ ∉ range b := by
    intro ρ
    rintro ⟨t,ht⟩
    have he := hGuide.injective ((hGuideCenterActual t).trans ht)
    have hw := congrArg (fun z : Interval × Icc (-1 : ℝ) 1 => z.2.val) he
    change 0 = ρ.val at hw
    exact (ne_of_gt ρ.property.1) hw.symm
  have hbetaSafe : ∀ ρ, beta ρ ∉ forbiddenEndpoints (fun i => (r i).val.val) α.val.val v := by
    intro ρ hforbidden
    have hline : beta ρ ∈ boundaryLine '' {u | |u.val| < bound} :=
      ⟨_,by simpa [abs_of_pos ρ.property.1] using ρ.property.2,rfl⟩
    have hother : ∀ k : Option ι, k ≠ some w → beta ρ ∉ range (f k) :=
      fun k hk => disjoint_left.mp (houtgoingClear k hk) hline
    rcases hforbidden with ⟨j,hj,hj0 | hj1⟩ | hα0 | hα1
    · by_cases hjw : j = w
      · subst j
        exact hbetaMissGuide ρ ⟨0,hj0.symm⟩
      · exact hother (some j) (by simpa using hjw) ⟨0,hj0.symm⟩
    · by_cases hjw : j = w
      · subst j
        exact hbetaMissGuide ρ ⟨1,hj1.symm⟩
      · exact hother (some j) (by simpa using hjw) ⟨1,hj1.symm⟩
    · exact hother none (by simp) ⟨0,hα0.symm⟩
    · exact hother none (by simp) ⟨1,hα1.symm⟩
  obtain ⟨baseCurve,hbaseCurve⟩ := RegionalEmbeddedFamily.contact_chart_sphere_is_curve
    S (chartAt (EuclideanSpace ℝ (Fin 2)) x)
    ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R hR htarget
  have hbaseCurveActual : baseCurve.image = boundaryCircle := hbaseCurve
  have hlineOpen : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      IsOpen {y : ↥({y : ↥F | y.val ∈ boundaryCircle}) |
        y.val ∈ boundaryLine '' {u | |u.val| < δ}} := by
    intro δ hδ hδ1
    let lineArc : C(Interval,S) :=
      ⟨fun t => (boundaryLine ⟨-δ+2*δ*t.val,by
        constructor <;> nlinarith [t.property.1,t.property.2]⟩).val,by fun_prop⟩
    have hLineArc : IsEmbedding lineArc := by
      apply (lineArc.continuous.isClosedEmbedding ?_).isEmbedding
      intro t u he
      have hh := congrArg Subtype.val (hBoundaryLine.injective (Subtype.ext he))
      change -δ+2*δ*t.val = -δ+2*δ*u.val at hh
      apply Subtype.ext
      nlinarith
    have hLineArcRange : range lineArc ⊆ baseCurve.image := by
      rintro y ⟨t,rfl⟩
      rw [hbaseCurveActual]
      exact (hBoundaryBV ⟨_,rfl⟩).1
    have hLineArcOpen := CurveComplex.LocalSurgery.embedded_curve_subarc_interior_isOpen
      baseCurve lineArc hLineArc hLineArcRange
    have hLineArcImage : lineArc '' Ioo (0 : Interval) 1 =
        Subtype.val '' (boundaryLine '' {u | |u.val| < δ}) := by
      ext y
      constructor
      · rintro ⟨t,ht,rfl⟩
        refine ⟨_,⟨_,?_,rfl⟩,rfl⟩
        change |(-δ + 2*δ*t.val)| < δ
        exact abs_lt.mpr ⟨by nlinarith [show (0 : ℝ) < t.val from ht.1, hδ],
          by nlinarith [show t.val < (1 : ℝ) from ht.2, hδ]⟩
      · rintro ⟨z,⟨u,hu,rfl⟩,rfl⟩
        change |u.val| < δ at hu
        have huδ := abs_lt.mp hu
        let t : Interval := ⟨(u.val+δ)/(2*δ),by
          constructor
          · exact div_nonneg (by linarith) (by positivity)
          · apply (div_le_one (by positivity : 0 < 2*δ)).mpr
            linarith⟩
        have ht : t ∈ Ioo (0 : Interval) 1 := by
          constructor
          · change 0 < (u.val+δ)/(2*δ)
            exact div_pos (by linarith) (by positivity)
          · change (u.val+δ)/(2*δ) < 1
            apply (div_lt_one (by positivity : 0 < 2*δ)).mpr
            linarith
        refine ⟨t,ht,?_⟩
        change (boundaryLine _).val = (boundaryLine u).val
        congr 2
        apply Subtype.ext
        dsimp [t]
        field_simp
        ring
    let boundaryToCurve : ↥({y : ↥F | y.val ∈ boundaryCircle}) → baseCurve.image :=
      fun y => ⟨y.val.val,hbaseCurveActual.symm ▸ y.property⟩
    have hBoundaryToCurve : Continuous boundaryToCurve :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    convert hLineArcOpen.preimage hBoundaryToCurve using 1
    ext y
    change y.val ∈ boundaryLine '' {u | |u.val| < δ} ↔
      y.val.val ∈ lineArc '' Ioo (0 : Interval) 1
    rw [hLineArcImage]
    constructor
    · intro hy
      exact ⟨y.val,hy,rfl⟩
    · rintro ⟨z,hz,he⟩
      exact (Subtype.ext he : z = y.val) ▸ hz
  let boundaryPath : C(Interval,↥({y : ↥F | y.val ∈ boundaryCircle})) :=
    ⟨fun t => ⟨d.boundarySide t,d.boundary_in_B t⟩,
      d.boundarySide.continuous.subtype_mk _⟩
  have hboundaryOneLine : boundaryPath 1 ∈
      {y : ↥({y : ↥F | y.val ∈ boundaryCircle}) |
        y.val ∈ boundaryLine '' {u | |u.val| < bound}} := by
    refine ⟨⟨0,by norm_num⟩,by simpa using hbound,?_⟩
    exact hBoundaryZero.trans d.boundary_one.symm
  have hterminalNhd := ((hlineOpen bound hbound hboundOne.le).preimage
    boundaryPath.continuous).mem_nhds hboundaryOneLine
  obtain ⟨terminalLower,hterminalLower,hterminalSubset⟩ :=
    nhds_top_basis.mem_iff.mp hterminalNhd
  obtain ⟨terminalCut,hterminalCutLower,hterminalCutOne⟩ :=
    exists_between (show max terminalLower gap.cut < (1 : Interval) from
      max_lt hterminalLower gap.cut_lt_one)
  have hterminalLine : d.boundarySide '' Icc terminalCut (1 : Interval) ⊆
      boundaryLine '' {u | |u.val| < bound} := by
    rintro y ⟨t,ht,rfl⟩
    exact hterminalSubset ((le_max_left terminalLower gap.cut).trans_lt
      (hterminalCutLower.trans_le ht.1))
  have hterminalAfterGap : gap.cut < terminalCut :=
    (le_max_right terminalLower gap.cut).trans_lt hterminalCutLower
  obtain ⟨incomingMarker,hincomingMarkerLower,hincomingMarkerUpper⟩ :=
    exists_between (show max gap.cut terminalCut < (1 : Interval) from
      max_lt gap.cut_lt_one hterminalCutOne)
  have hincomingMarker : incomingMarker ∈ Ioo (max gap.cut terminalCut) (1 : Interval) :=
    ⟨hincomingMarkerLower,hincomingMarkerUpper⟩
  let incomingParam : C(Interval,Interval) :=
    CurveComplex.BranchedDoubleCover.intervalSegment 1 terminalCut
  have hincomingParam : ∀ t, incomingParam t ∈ Icc terminalCut (1 : Interval) := by
    intro t
    constructor
    · change (terminalCut : ℝ) ≤ (1-t.val)*1+t.val*(terminalCut : ℝ)
      nlinarith [t.property.2,show (terminalCut : ℝ) < 1 from hterminalCutOne]
    · change (1-t.val)*1+t.val*(terminalCut : ℝ) ≤ 1
      nlinarith [t.property.1,show (terminalCut : ℝ) < 1 from hterminalCutOne]
  have hincomingInRange : ∀ t, d.boundarySide (incomingParam t) ∈ range boundaryLine := by
    intro t
    obtain ⟨u,hu,he⟩ := hterminalLine ⟨incomingParam t,hincomingParam t,rfl⟩
    exact ⟨u,he⟩
  let incomingSuffix : C(Interval,range boundaryLine) :=
    ⟨fun t => ⟨d.boundarySide (incomingParam t),hincomingInRange t⟩,
      (d.boundarySide.continuous.comp incomingParam.continuous).subtype_mk hincomingInRange⟩
  let incomingCoord : C(Interval,ℝ) :=
    ⟨fun t => (hBoundaryLine.toHomeomorph.symm (incomingSuffix t)).val,
      continuous_subtype_val.comp (hBoundaryLine.toHomeomorph.symm.continuous.comp
        incomingSuffix.continuous)⟩
  have hincomingCoordEq : ∀ t,
      boundaryLine (hBoundaryLine.toHomeomorph.symm (incomingSuffix t)) =
        d.boundarySide (incomingParam t) := by
    intro t
    exact congrArg Subtype.val (hBoundaryLine.toHomeomorph.apply_symm_apply (incomingSuffix t))
  have hincomingCoordZero : incomingCoord 0 = 0 := by
    have he := hincomingCoordEq 0
    have hp0 : incomingParam 0 = 1 := by
      simp [incomingParam,CurveComplex.BranchedDoubleCover.intervalSegment,
        CurveComplex.BranchedDoubleCover.intervalAffine]
    rw [hp0,d.boundary_one,← hBoundaryZero] at he
    exact congrArg Subtype.val (hBoundaryLine.injective he)
  have hincomingCoordNonzero : ∀ t : Interval, 0 < t.val → incomingCoord t ≠ 0 := by
    intro t ht he
    have hc : hBoundaryLine.toHomeomorph.symm (incomingSuffix t) = ⟨0,by norm_num⟩ :=
      Subtype.ext he
    have hh := hincomingCoordEq t
    rw [hc,hBoundaryZero,← d.boundary_one] at hh
    have hp := congrArg Subtype.val (d.boundary_embedded.injective hh.symm)
    change (1-t.val)*1+t.val*(terminalCut : ℝ) = 1 at hp
    have hcut1 : (terminalCut : ℝ) < 1 := hterminalCutOne
    nlinarith
  obtain ⟨incomingSign,hincomingSignUnit,hincomingPositive⟩ :=
    actual_continuous_positive_parameter_sign incomingCoord hincomingCoordNonzero
  have hincomingSignTail : ∀ s ∈ Ioo terminalCut (1 : Interval),
      ∀ u : Icc (-1 : ℝ) 1, boundaryLine u = d.boundarySide s → 0 < incomingSign*u.val := by
    intro s hs u hu
    let t : Interval := ⟨(1-s.val)/(1-(terminalCut : ℝ)),by
      constructor
      · exact div_nonneg (sub_nonneg.mpr s.property.2)
          (sub_nonneg.mpr terminalCut.property.2)
      · apply (div_le_one (show 0 < 1-(terminalCut : ℝ) from
          sub_pos.mpr hterminalCutOne)).mpr
        linarith [show (terminalCut : ℝ) < s.val from hs.1]⟩
    have ht : 0 < t.val := div_pos (sub_pos.mpr hs.2) (sub_pos.mpr hterminalCutOne)
    have hp : incomingParam t = s := by
      apply Subtype.ext
      change (1-(1-s.val)/(1-(terminalCut : ℝ)))*1+
        ((1-s.val)/(1-(terminalCut : ℝ)))*(terminalCut : ℝ) = s.val
      field_simp [show 1-(terminalCut : ℝ) ≠ 0 from ne_of_gt (sub_pos.mpr hterminalCutOne)]
      ring
    have hcoord := hincomingCoordEq t
    rw [hp,← hu] at hcoord
    have hcu := congrArg Subtype.val (hBoundaryLine.injective hcoord)
    change incomingCoord t = u.val at hcu
    rw [← hcu]
    exact hincomingPositive t ht
  let boundaryPrefix : Set ↥F := d.boundarySide '' Icc (0 : Interval) terminalCut
  have hboundaryPrefixCompact : IsCompact boundaryPrefix :=
    isCompact_Icc.image d.boundarySide.continuous
  have hboundaryPrefixAvoid : d.second 0 ∉ boundaryPrefix := by
    rintro ⟨t,ht,he⟩
    have ht1 := d.boundary_embedded.injective (he.trans d.boundary_one.symm)
    exact (not_le_of_gt hterminalCutOne) (ht1 ▸ ht.2)
  have hprefixZeroOpen : (⟨0,by norm_num⟩ : Icc (-1 : ℝ) 1) ∈
      boundaryLine ⁻¹' boundaryPrefixᶜ := by
    change boundaryLine ⟨0,by norm_num⟩ ∉ boundaryPrefix
    rwa [hBoundaryZero]
  obtain ⟨boundaryRadius,hboundaryRadius,hboundaryBall⟩ := Metric.isOpen_iff.mp
    (hboundaryPrefixCompact.isClosed.isOpen_compl.preimage boundaryLine.continuous)
    ⟨0,by norm_num⟩ hprefixZeroOpen
  let signedBound : ℝ := min bound boundaryRadius / 2
  have hsignedBound : 0 < signedBound := by dsimp [signedBound]; positivity
  have hsignedBoundOld : signedBound < bound := by
    dsimp [signedBound]
    linarith [min_le_left bound boundaryRadius]
  have hsignedBoundRadius : signedBound < boundaryRadius := by
    dsimp [signedBound]
    linarith [min_le_right bound boundaryRadius]
  have hsignedBoundOne : signedBound < 1 := hsignedBoundOld.trans hboundOne
  let widthClock : Icc (-1 : ℝ) 1 ≃ₜ Icc (-1 : ℝ) 1 := {
    toFun := fun u => ⟨-incomingSign*u.val,by
      rcases hincomingSignUnit with he | he <;> rw [he]
      · simpa using u.property
      · constructor <;> nlinarith [u.property.1,u.property.2]⟩
    invFun := fun u => ⟨-incomingSign*u.val,by
      rcases hincomingSignUnit with he | he <;> rw [he]
      · simpa using u.property
      · constructor <;> nlinarith [u.property.1,u.property.2]⟩
    left_inv := by
      intro u
      apply Subtype.ext
      rcases hincomingSignUnit with he | he <;> simp [he]
    right_inv := by
      intro u
      apply Subtype.ext
      rcases hincomingSignUnit with he | he <;> simp [he]
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hwidthClockAbs : ∀ u, |(widthClock u).val| = |u.val| := by
    intro u
    change |-incomingSign*u.val| = |u.val|
    rcases hincomingSignUnit with he | he <;> simp [he]
  have hwidthClockZero : widthClock ⟨0,by norm_num⟩ = ⟨0,by norm_num⟩ := by
    apply Subtype.ext
    simp [widthClock]
  let signedGuideStrip : C(Interval × Icc (-1 : ℝ) 1,↥F) :=
    guideStrip.comp ⟨(Homeomorph.refl Interval).prodCongr widthClock,
      ((Homeomorph.refl Interval).prodCongr widthClock).continuous⟩
  have hSignedGuide : IsEmbedding signedGuideStrip :=
    hGuide.comp ((Homeomorph.refl Interval).prodCongr widthClock).isEmbedding
  have hSignedGuideCenter : ∀ t, signedGuideStrip (t,⟨0,by norm_num⟩) = b t := by
    intro t
    change guideStrip (t,widthClock ⟨0,by norm_num⟩) = b t
    rw [hwidthClockZero,hGuideCenterActual]
  have hSignedGuideActive : ∀ t ∈ guideWindow, ∀ u, signedGuideStrip (t,u) ∈ V := by
    intro t ht u
    exact hGuideActive t ht (widthClock u)
  have hSignedGuideEnds : ∀ u, (signedGuideStrip (0,u)).val ∈ boundaryCircle ∧
      (signedGuideStrip (1,u)).val ∈ boundaryCircle := by
    intro u
    exact hGuideEnds (widthClock u)
  have hSignedGuideInterior : ∀ t ∈ Ioo (0 : Interval) 1, ∀ u,
      (signedGuideStrip (t,u)).val ∈ interior F := by
    intro t ht u
    exact hGuideInterior t ht (widthClock u)
  let signedBoundaryLine : C(Icc (-1 : ℝ) 1,↥F) :=
    boundaryLine.comp ⟨widthClock,widthClock.continuous⟩
  have hSignedBoundary : IsEmbedding signedBoundaryLine := hBoundaryLine.comp widthClock.isEmbedding
  have hSignedBoundaryZero : signedBoundaryLine ⟨0,by norm_num⟩ = d.second 0 := by
    change boundaryLine (widthClock ⟨0,by norm_num⟩) = d.second 0
    rw [hwidthClockZero,hBoundaryZero]
  have hSignedBetaOutside : ∀ u : Icc (-1 : ℝ) 1, 0 < u.val → u.val < signedBound →
      signedBoundaryLine u ∉ range d.boundarySide := by
    intro u hu0 huBound
    have huAbs : |(widthClock u).val| < signedBound := by
      rw [hwidthClockAbs,abs_of_pos hu0]
      exact huBound
    have hnotPrefix : signedBoundaryLine u ∉ boundaryPrefix := by
      apply hboundaryBall
      change dist ((widthClock u).val : ℝ) 0 < boundaryRadius
      simpa [Real.dist_eq] using huAbs.trans hsignedBoundRadius
    rintro ⟨s,hs⟩
    by_cases hsCut : s ≤ terminalCut
    · exact hnotPrefix ⟨s,⟨bot_le,hsCut⟩,hs⟩
    by_cases hsOne : s = 1
    · have he : signedBoundaryLine u = signedBoundaryLine ⟨0,by norm_num⟩ := by
        rw [hSignedBoundaryZero]
        exact hs.symm.trans (hsOne ▸ d.boundary_one)
      have huZero := congrArg Subtype.val (hSignedBoundary.injective he)
      exact (ne_of_gt hu0) huZero
    have hsInterior : s ∈ Ioo terminalCut (1 : Interval) :=
      ⟨lt_of_not_ge hsCut,lt_top_iff_ne_top.mpr hsOne⟩
    have hp := hincomingSignTail s hsInterior (widthClock u) hs.symm
    change 0 < incomingSign * (-incomingSign*u.val) at hp
    rcases hincomingSignUnit with he | he <;> rw [he] at hp <;> nlinarith
  have hSignedGuideOpen : IsOpen (signedGuideStrip ''
      {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
    convert hGuideOpen using 1
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨(z.1,widthClock z.2),?_,rfl⟩
      exact abs_lt.mp ((hwidthClockAbs z.2).symm ▸ abs_lt.mpr hz)
    · rintro ⟨z,hz,rfl⟩
      refine ⟨(z.1,widthClock.symm z.2),?_,?_⟩
      · have ha := hwidthClockAbs (widthClock.symm z.2)
        rw [widthClock.apply_symm_apply] at ha
        exact abs_lt.mp (ha ▸ abs_lt.mpr hz)
      · change guideStrip (z.1,widthClock (widthClock.symm z.2)) = guideStrip z
        rw [widthClock.apply_symm_apply]
  have hSignedBoundaryEq : ∀ u,
      signedBoundaryLine u = signedGuideStrip (d.bStart,u) := fun _ => rfl
  have hSignedBoundaryLocal : signedBoundaryLine '' {u | |u.val| < signedBound} ⊆
      {y : ↥F | y.val ∈ boundaryCircle} ∩ V := by
    rintro y ⟨u,hu,rfl⟩
    exact hBoundaryBV ⟨widthClock u,rfl⟩
  have hSignedOutgoingClear : ∀ k : Option ι, k ≠ some w →
      Disjoint (signedBoundaryLine '' {u | |u.val| < signedBound}) (range (f k)) := by
    intro k hk
    apply disjoint_left.mpr
    rintro y ⟨u,hu,rfl⟩ hy
    exact disjoint_left.mp (houtgoingClear k hk)
      ⟨widthClock u,by
        change |(widthClock u).val| < bound
        rw [hwidthClockAbs]
        exact hu.trans hsignedBoundOld,rfl⟩ hy
  have hsmallTerminalNhd := ((hlineOpen signedBound hsignedBound hsignedBoundOne.le).preimage
    boundaryPath.continuous).mem_nhds (show boundaryPath 1 ∈
      {y : ↥({y : ↥F | y.val ∈ boundaryCircle}) |
        y.val ∈ boundaryLine '' {u | |u.val| < signedBound}} from
      ⟨⟨0,by norm_num⟩,by simpa using hsignedBound,hBoundaryZero.trans d.boundary_one.symm⟩)
  obtain ⟨smallTerminalLower,hsmallTerminalLower,hsmallTerminalSubset⟩ :=
    nhds_top_basis.mem_iff.mp hsmallTerminalNhd
  obtain ⟨signedTerminalCut,hsignedTerminalLower,hsignedTerminalOne⟩ :=
    exists_between (show max smallTerminalLower terminalCut < (1 : Interval) from
      max_lt hsmallTerminalLower hterminalCutOne)
  have hSignedIncomingTerminal : d.boundarySide '' Ioo signedTerminalCut (1 : Interval) ⊆
      signedBoundaryLine '' {u | -signedBound < u.val ∧ u.val < 0} := by
    rintro y ⟨s,hs,rfl⟩
    obtain ⟨u,hu,he⟩ := hsmallTerminalSubset
      (show s ∈ Ioi smallTerminalLower from
        (le_max_left _ _).trans_lt (hsignedTerminalLower.trans hs.1))
    refine ⟨widthClock.symm u,?_,?_⟩
    · have hraw : |u.val| < signedBound := hu
      have heq : (widthClock.symm u).val = -incomingSign*u.val := rfl
      have hsign := hincomingSignTail s
        ⟨(le_max_right _ _).trans_lt (hsignedTerminalLower.trans hs.1),hs.2⟩ u he
      have ha := hwidthClockAbs (widthClock.symm u)
      rw [widthClock.apply_symm_apply] at ha
      refine ⟨(abs_lt.mp (ha ▸ hraw)).1,?_⟩
      rw [heq]
      nlinarith only [hsign]
    · change boundaryLine (widthClock (widthClock.symm u)) = d.boundarySide s
      rwa [widthClock.apply_symm_apply]
  -- Calibrate the actual old F collar using an ambient homeomorphism supported
  -- in the interior part of V. This support is what preserves its B ends.
  let axisDomain : Set S := cornerFan.chart.source ∩
    cornerFan.chart ⁻¹' Metric.ball (0 : Plane) 1
  have hAxisDomain : IsOpen axisDomain :=
    cornerFan.chart.isOpen_inter_preimage Metric.isOpen_ball
  let oldAxisChart := cornerFan.chart.restr axisDomain
  have hOldAxisSource : oldAxisChart.source = cornerFan.chart.source ∩ axisDomain :=
    cornerFan.chart.restr_source' axisDomain hAxisDomain
  have hOldAxis : ∀ t, (a t).val ∈ oldAxisChart.source →
      oldAxisChart (a t).val 1 = 0 := by
    intro t ht
    rw [hOldAxisSource] at ht
    have hm : a t ∈ chartPull F cornerFan.chart (Metric.ball (0 : Plane) 1) ∩
        range (f (some v)) := ⟨ht.2,⟨t,rfl⟩⟩
    rw [cornerFan.whole_open ⟨some v,hpv⟩] at hm
    obtain ⟨s,hs,he⟩ := hm
    have hrad : cornerFan.chart (a t).val ∈
        segment ℝ (incidentPorts f (d.first 1) cornerFan.chart
          cornerFan.left cornerFan.right (⟨some v,hpv⟩,false)) 0 ∪
        segment ℝ 0 (incidentPorts f (d.first 1) cornerFan.chart
          cornerFan.left cornerFan.right (⟨some v,hpv⟩,true)) := by
      rw [← cornerFan.radial_trace ⟨some v,hpv⟩]
      exact ⟨s,⟨hs.1.le,hs.2.le⟩,congrArg (fun y : ↥F => cornerFan.chart y.val) he⟩
    change cornerFan.chart (a t).val 1 = 0
    rcases hrad with hrad | hrad
    · rw [segment_eq_image] at hrad
      obtain ⟨z,hz,hzval⟩ := hrad
      rw [← hzval]
      change (1-z) * (incidentPorts f (d.first 1) cornerFan.chart
        cornerFan.left cornerFan.right (⟨some v,hpv⟩,false)) 1 + z * 0 = 0
      rw [hcornerLeftAxis]
      ring
    · rw [segment_eq_image] at hrad
      obtain ⟨z,hz,hzval⟩ := hrad
      rw [← hzval]
      change (1-z) * 0 + z * (incidentPorts f (d.first 1) cornerFan.chart
        cornerFan.left cornerFan.right (⟨some v,hpv⟩,true)) 1 = 0
      rw [hcornerRightAxis]
      ring
  have hOldCornerSource : (a d.aFinish).val ∈ oldAxisChart.source := by
    rw [hOldAxisSource,← hfirst1]
    exact ⟨cornerFan.contact_in_source,cornerFan.contact_in_source,
      by change cornerFan.chart (d.first 1).val ∈ Metric.ball (0 : Plane) 1
         rw [cornerFan.contact_zero]; simp⟩
  have hOldCornerZero : oldAxisChart (a d.aFinish).val = 0 := by
    change cornerFan.chart (a d.aFinish).val = 0
    rw [← hfirst1,cornerFan.contact_zero]
  obtain ⟨ambientV,hAmbientV,hAmbientVeq⟩ :=
    (IsEmbedding.subtypeVal.isInducing.isOpen_iff).mp hV
  let calibrationSupport : Set S := interior F ∩ ambientV
  have hCalibrationSupport : IsOpen calibrationSupport := isOpen_interior.inter hAmbientV
  have hCornerSupport : (a d.aFinish).val ∈ calibrationSupport := by
    constructor
    · exact (mem_interior_iff_notMem_frontier (a d.aFinish).property).mpr
        ((r v).val.property.2.2.2 _ hfinishInterior)
    · change a d.aFinish ∈ Subtype.val ⁻¹' ambientV
      rw [hAmbientVeq,← hfirst1]
      exact hfirstV (mem_range_self 1)
  let ambientOld : C(Interval,S) := ⟨fun t => (a t).val,a.continuous.subtype_val⟩
  let ambientOldStrip : Interval × Icc (-1 : ℝ) 1 → S := fun z => (oldStrip z).val
  have hAmbientOld : IsEmbedding ambientOld := IsEmbedding.subtypeVal.comp (r v).val.property.1
  have hAmbientOldStrip : IsEmbedding ambientOldStrip := IsEmbedding.subtypeVal.comp hOld
  obtain ⟨oldFactor,hOldFactor,calibrationSign,calibrationScale,calibrationRadius,
      calibrationMap,hCalibrationSign,hCalibrationScale,hCalibrationRadius,
      hCalibrationCenter,hCalibrationFixed,hCalibrationCoords⟩ :=
    source_internal_collar_calibration ambientOld hAmbientOld ambientOldStrip
      hAmbientOldStrip (fun t => congrArg Subtype.val (hOldCenterActual t))
      d.aFinish hfinishInterior oldAxisChart hOldCornerSource hOldCornerZero
      hOldAxis univ calibrationSupport isOpen_univ hCalibrationSupport (subset_univ _)
      hCornerSupport (subset_univ _)
  have hCalibrationPreserves (A : Set S) (hA : calibrationSupport ⊆ A) :
      ∀ y, y ∈ A ↔ calibrationMap y ∈ A := by
    intro y
    constructor
    · intro hy
      by_contra hny
      have hfixed := hCalibrationFixed (calibrationMap y) (fun h => hny (hA h))
      have he : calibrationMap y = y := calibrationMap.injective hfixed
      exact hny (he.symm ▸ hy)
    · intro hy
      by_contra hny
      have hfixed := hCalibrationFixed y (fun h => hny (hA h))
      exact hny (hfixed ▸ hy)
  have hCalibrationF : ∀ y, y ∈ F ↔ calibrationMap y ∈ F :=
    hCalibrationPreserves F (fun _ h => interior_subset h.1)
  have hCalibrationInterior : ∀ y, y ∈ interior F ↔ calibrationMap y ∈ interior F :=
    hCalibrationPreserves (interior F) inter_subset_left
  have hCalibrationV : ∀ y, y ∈ ambientV ↔ calibrationMap y ∈ ambientV :=
    hCalibrationPreserves ambientV inter_subset_right
  let relativeCalibration : ↥F ≃ₜ ↥F := calibrationMap.subtype hCalibrationF
  have hCalibrationBoundary : ∀ y : ↥F, y.val ∈ boundaryCircle → relativeCalibration y = y := by
    intro y hy
    apply Subtype.ext
    apply hCalibrationFixed
    intro hySupport
    exact disjoint_left.mp disjoint_interior_frontier hySupport.1 (hBF hy)
  let oldWidthMap : C(Interval × Icc (-1 : ℝ) 1,Interval × Icc (-1 : ℝ) 1) :=
    ⟨fun z => (z.1,⟨oldFactor*z.2.val,by
      constructor <;> nlinarith [z.2.property.1,z.2.property.2,hOldFactor.1,hOldFactor.2]⟩),
      by fun_prop⟩
  have hOldWidthMap : IsEmbedding oldWidthMap := by
    apply (oldWidthMap.continuous.isClosedEmbedding _).isEmbedding
    intro z y he
    apply Prod.ext
    · change (oldWidthMap z).1 = (oldWidthMap y).1
      exact congrArg Prod.fst he
    · apply Subtype.ext
      have hc := congrArg (fun q : Interval × Icc (-1 : ℝ) 1 => q.2.val) he
      exact (mul_left_cancel₀ hOldFactor.1.ne') hc
  let calibratedOldStrip : C(Interval × Icc (-1 : ℝ) 1,↥F) :=
    (⟨relativeCalibration,relativeCalibration.continuous⟩ : C(↥F,↥F)).comp
      (oldStrip.comp oldWidthMap)
  have hCalibratedOld : IsEmbedding calibratedOldStrip :=
    relativeCalibration.isEmbedding.comp (hOld.comp hOldWidthMap)
  have hCalibratedOldCenter : ∀ t,
      calibratedOldStrip (t,⟨0,by norm_num⟩) = a t := by
    intro t
    have hz : oldWidthMap (t,⟨0,by norm_num⟩) = (t,⟨0,by norm_num⟩) := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext; change oldFactor*0 = 0; ring
    change relativeCalibration (oldStrip (oldWidthMap (t,⟨0,by norm_num⟩))) = a t
    rw [hz,hOldCenterActual]
    exact Subtype.ext (hCalibrationCenter t)
  have hCalibratedOldEnds : ∀ u,
      (calibratedOldStrip (0,u)).val ∈ boundaryCircle ∧
      (calibratedOldStrip (1,u)).val ∈ boundaryCircle := by
    intro u
    have h0 := (hOldEnds (oldWidthMap (0,u)).2).1
    have h1 := (hOldEnds (oldWidthMap (1,u)).2).2
    change (relativeCalibration (oldStrip (0,(oldWidthMap (0,u)).2))).val ∈ boundaryCircle ∧
      (relativeCalibration (oldStrip (1,(oldWidthMap (1,u)).2))).val ∈ boundaryCircle
    rw [hCalibrationBoundary _ h0,hCalibrationBoundary _ h1]
    exact ⟨h0,h1⟩
  have hCalibratedOldInterior : ∀ t ∈ Ioo (0 : Interval) 1, ∀ u,
      (calibratedOldStrip (t,u)).val ∈ interior F := by
    intro t ht u
    exact (hCalibrationInterior _).mp (hOldInterior t ht (oldWidthMap (t,u)).2)
  have hCalibratedOldActive : ∀ t ∈ activeWindow, ∀ u,
      calibratedOldStrip (t,u) ∈ V := by
    intro t ht u
    rw [← hAmbientVeq]
    apply (hCalibrationV _).mp
    have hv := hOldActive t ht (oldWidthMap (t,u)).2
    rw [← hAmbientVeq] at hv
    exact hv
  have hCalibratedOldCoordinates : ∀ t : Interval, ∀ u : Icc (-1 : ℝ) 1,
      |t.val-d.aFinish.val| < calibrationRadius →
      (calibratedOldStrip (t,u)).val ∈ cornerFan.chart.source ∧
      cornerFan.chart (calibratedOldStrip (t,u)).val =
        Plane.mk (cornerFan.chart (a t).val 0) (calibrationSign*calibrationScale*u.val) := by
    intro t u ht
    have hc := hCalibrationCoords t u ht
    refine ⟨?_,hc.2⟩
    have hs := hc.1
    rw [hOldAxisSource] at hs
    exact hs.1
  have hCalibratedOldUnit : ∀ t : Interval, ∀ u : Icc (-1 : ℝ) 1,
      |t.val-d.aFinish.val| < calibrationRadius →
      calibratedOldStrip (t,u) ∈ chartPull F cornerFan.chart (Metric.ball (0 : Plane) 1) := by
    intro t u ht
    have hs := (hCalibrationCoords t u ht).1
    rw [hOldAxisSource] at hs
    exact hs.2
  let oldNarrowCore : Set (Interval × Icc (-1 : ℝ) 1) :=
    {z | -oldFactor < z.2.val ∧ z.2.val < oldFactor}
  have hOldNarrowCore : IsOpen oldNarrowCore :=
    (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
  have hOldNarrowCoreSub : oldNarrowCore ⊆ {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
    intro z hz
    exact ⟨lt_of_le_of_lt (neg_le_neg hOldFactor.2) hz.1,hz.2.trans_le hOldFactor.2⟩
  obtain ⟨narrowOpen,hNarrowOpen,hNarrowImage⟩ :=
    hOld.isInducing.image_eq_isOpen_inter_range hOldNarrowCore
  have hNarrowOpenImage : IsOpen (oldStrip '' oldNarrowCore) := by
    have he : oldStrip '' oldNarrowCore = narrowOpen ∩
        oldStrip '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
      apply Subset.antisymm
      · intro y hy
        exact ⟨(hNarrowImage ▸ hy).1,image_mono hOldNarrowCoreSub hy⟩
      · rintro y ⟨hyO,hyCore⟩
        rw [hNarrowImage]
        exact ⟨hyO,image_subset_range oldStrip _ hyCore⟩
    rw [he]
    exact hNarrowOpen.inter hOldOpen
  have hOldWidthCore : oldWidthMap '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} = oldNarrowCore := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      change -oldFactor < oldFactor*y.2.val ∧ oldFactor*y.2.val < oldFactor
      constructor <;> nlinarith [hOldFactor.1,hy.1,hy.2]
    · intro hz
      have hu : -1 < z.2.val/oldFactor ∧ z.2.val/oldFactor < 1 := by
        constructor
        · apply (lt_div_iff₀ hOldFactor.1).mpr
          simpa using hz.1
        · exact (div_lt_one hOldFactor.1).mpr hz.2
      refine ⟨(z.1,⟨z.2.val/oldFactor,⟨hu.1.le,hu.2.le⟩⟩),hu,?_⟩
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact mul_div_cancel₀ z.2.val hOldFactor.1.ne'
  have hCalibratedOldOpen : IsOpen (calibratedOldStrip ''
      {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
    have he : calibratedOldStrip '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} =
        relativeCalibration '' (oldStrip '' oldNarrowCore) := by
      rw [← hOldWidthCore,image_image,image_image]
      rfl
    rw [he]
    exact relativeCalibration.isOpenMap _ hNarrowOpenImage
  let calibrationWindow : Set Interval :=
    {t | |(clock t).val-d.aFinish.val| < calibrationRadius} ∩ clock ⁻¹' activeWindow
  have hCalibrationWindow : IsOpen calibrationWindow := by
    apply IsOpen.inter
    · exact isOpen_lt (by fun_prop) continuous_const
    · exact hActiveOpen.preimage clock.continuous
  have hCornerCalibrationWindow : cornerTime ∈ calibrationWindow := by
    constructor
    · change |(clock cornerTime).val-d.aFinish.val| < calibrationRadius
      simp only [cornerTime,Homeomorph.apply_symm_apply,sub_self,abs_zero]
      exact hCalibrationRadius
    · exact hActivePrefix ⟨cornerTime,⟨bot_le,hcutLower.le⟩,rfl⟩
  obtain ⟨calibrationLeft,calibrationRight,hCalibrationInterval,hCalibrationIntervalSub⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨0,hcornerTime.1⟩ ⟨1,hcornerTime.2⟩).mp
      (hCalibrationWindow.mem_nhds hCornerCalibrationWindow)
  obtain ⟨calibratedCut,hCalibratedCutLower,hCalibratedCutUpper⟩ :=
    exists_between (lt_min hcutLower hCalibrationInterval.2)
  have hCalibratedCutOld : calibratedCut < cut :=
    hCalibratedCutUpper.trans_le (min_le_left _ _)
  have hCalibratedCutRight : calibratedCut < calibrationRight :=
    hCalibratedCutUpper.trans_le (min_le_right _ _)
  have hCalibratedCutInterior : calibratedCut ∈ Ioo (0 : Interval) 1 :=
    ⟨hcornerTime.1.trans hCalibratedCutLower,hCalibratedCutOld.trans hcut.2⟩
  have hCalibratedPrefix : aclock '' Icc (0 : Interval) calibratedCut ⊆ V :=
    (image_mono (Icc_subset_Icc_right hCalibratedCutOld.le)).trans hprefix
  have hCalibratedPadded : Disjoint (aclock '' Ioc cornerTime calibratedCut) K :=
    hpadded.mono_left (image_mono (Ioc_subset_Ioc_right hCalibratedCutOld.le))
  have hCalibratedTail : aclock '' Icc calibratedCut (1 : Interval) ⊆ range a \ range d.first := by
    rintro y ⟨t,ht,rfl⟩
    refine ⟨⟨clock t,rfl⟩,?_⟩
    rw [hfirstRange]
    rintro ⟨s,hs,he⟩
    have hst := haclock.injective he
    exact (not_le_of_gt (hCalibratedCutLower.trans_le ht.1)) (hst ▸ hs.2)
  obtain ⟨coordinateLeft,hCoordinateLeftLower,hCoordinateLeftUpper⟩ := exists_between hCalibrationInterval.1
  obtain ⟨coordinateRight,hCoordinateRightLower,hCoordinateRightUpper⟩ := exists_between hCalibratedCutRight
  have hCoordinateLR : coordinateLeft < coordinateRight :=
    hCoordinateLeftUpper.trans (hCalibratedCutLower.trans hCoordinateRightLower)
  have hCoordinateClosedSub : Icc coordinateLeft coordinateRight ⊆ calibrationWindow := by
    intro t ht
    exact hCalibrationIntervalSub
      ⟨hCoordinateLeftLower.trans_le ht.1,ht.2.trans_lt hCoordinateRightUpper⟩
  let oldCoordinateWindow : Set Interval := Ioo coordinateLeft coordinateRight
  have hOldCoordinatePadded : Icc cornerTime calibratedCut ⊆ oldCoordinateWindow := by
    intro t ht
    exact ⟨hCoordinateLeftUpper.trans_le ht.1,ht.2.trans_lt hCoordinateRightLower⟩
  have hOldCoordinateActive : oldCoordinateWindow ⊆ clock ⁻¹' activeWindow := by
    intro t ht
    exact (hCoordinateClosedSub ⟨ht.1.le,ht.2.le⟩).2
  let coordinateClamp : C(Interval,Interval) :=
    ⟨fun t => (projIcc coordinateLeft coordinateRight hCoordinateLR.le t).val,
      continuous_subtype_val.comp continuous_projIcc⟩
  have hCoordinateClampSource : ∀ t,
      (a (clock (coordinateClamp t))).val ∈ cornerFan.chart.source := by
    intro t
    have ht := (hCoordinateClosedSub (projIcc coordinateLeft coordinateRight hCoordinateLR.le t).property).1
    have hs := (hCalibratedOldCoordinates (clock (coordinateClamp t)) ⟨0,by norm_num⟩ ht).1
    rwa [hCalibratedOldCenter] at hs
  let oldCoordinateX : C(Interval,ℝ) :=
    ⟨fun t => cornerFan.chart (a (clock (coordinateClamp t))).val 0,
      (by fun_prop : Continuous (fun z : Plane => z 0)).comp
        (cornerFan.chart.continuousOn.comp_continuous
          (a.continuous.subtype_val.comp (clock.continuous.comp coordinateClamp.continuous))
          hCoordinateClampSource)⟩
  have hOldCoordinateXEq : ∀ t ∈ Icc coordinateLeft coordinateRight,
      oldCoordinateX t = cornerFan.chart (a (clock t)).val 0 := by
    intro t ht
    change cornerFan.chart (a (clock (projIcc coordinateLeft coordinateRight hCoordinateLR.le t).val)).val 0 = _
    rw [projIcc_of_mem hCoordinateLR.le ht]
  have hOldCoordinateXZero : oldCoordinateX cornerTime = 0 := by
    rw [hOldCoordinateXEq _ ⟨hCoordinateLeftUpper.le,
      (hCalibratedCutLower.trans hCoordinateRightLower).le⟩]
    change cornerFan.chart (aclock cornerTime).val 0 = 0
    rw [hclockCorner,cornerFan.contact_zero]
    rfl
  have hOldCoordinateXInjective : InjOn oldCoordinateX (Icc coordinateLeft coordinateRight) := by
    intro t ht s hs he
    rw [hOldCoordinateXEq t ht,hOldCoordinateXEq s hs] at he
    have htx := (hCalibrationCoords (clock t) ⟨0,by norm_num⟩ (hCoordinateClosedSub ht).1).1
    have hsx := (hCalibrationCoords (clock s) ⟨0,by norm_num⟩ (hCoordinateClosedSub hs).1).1
    change (calibratedOldStrip (clock t,⟨0,by norm_num⟩)).val ∈ oldAxisChart.source at htx
    change (calibratedOldStrip (clock s,⟨0,by norm_num⟩)).val ∈ oldAxisChart.source at hsx
    rw [hCalibratedOldCenter] at htx hsx
    have hey : oldAxisChart (a (clock t)).val = oldAxisChart (a (clock s)).val := by
      ext i
      fin_cases i
      · exact he
      · exact (hOldAxis _ htx).trans (hOldAxis _ hsx).symm
    exact clock.injective ((r v).val.property.1.injective (Subtype.ext (oldAxisChart.injOn htx hsx hey)))
  have hOldCoordinateOrder : StrictMonoOn oldCoordinateX (Icc coordinateLeft coordinateRight) ∨
      StrictAntiOn oldCoordinateX (Icc coordinateLeft coordinateRight) :=
    oldCoordinateX.continuous.continuousOn.strictMonoOn_of_injOn_Icc'
      hCoordinateLR.le hOldCoordinateXInjective
  -- The frontier equation below concerns this actual three-sided half disk.
  let ambientDisk : C(Metric.closedBall (0 : Plane) 1,S) :=
    ⟨fun z => (d.disk z).val,d.disk.continuous.subtype_val⟩
  have hAmbientDisk : IsEmbedding ambientDisk := IsEmbedding.subtypeVal.comp d.disk_embedded
  have hAmbientDiskClosed : IsClosed (range ambientDisk) :=
    (isCompact_range ambientDisk.continuous).isClosed
  have hAmbientDiskFrontier : frontier (range ambientDisk) =
      Subtype.val '' (range d.first ∪ range d.second ∪ range d.boundarySide) := by
    rw [← d.boundary_image,image_image]
    change frontier (range ambientDisk) =
      ambientDisk '' {z | z.val ∈ Metric.sphere (0 : Plane) 1}
    rw [hAmbientDiskClosed.frontier_eq,
      CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq ambientDisk hAmbientDisk]
    ext p
    constructor
    · rintro ⟨⟨z,rfl⟩,hnot⟩
      refine ⟨z,le_antisymm z.property ?_,rfl⟩
      by_contra hn
      exact hnot ⟨z,lt_of_not_ge hn,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      refine ⟨⟨z,rfl⟩,?_⟩
      rintro ⟨y,hy,he⟩
      have heq := hAmbientDisk.injective he
      subst y
      change dist z.val (0 : Plane) = 1 at hz
      change dist z.val (0 : Plane) < 1 at hy
      linarith
  have hAmbientDiskRegular : closure (interior (range ambientDisk)) = range ambientDisk := by
    let A : Set (Metric.closedBall (0 : Plane) 1) := {z | z.val ∈ Metric.ball (0 : Plane) 1}
    have hAimage : Subtype.val '' A = Metric.ball (0 : Plane) 1 := by
      ext z
      constructor
      · rintro ⟨y,hy,rfl⟩; exact hy
      · intro hz; exact ⟨⟨z,Metric.ball_subset_closedBall hz⟩,hz,rfl⟩
    have hAclosure : closure A = univ := by
      rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,hAimage,
        closure_ball (0 : Plane) (by norm_num : (1 : ℝ) ≠ 0)]
      ext z
      simp only [mem_preimage,mem_univ,iff_true]
      exact z.property
    have hdense : range ambientDisk ⊆ closure (ambientDisk '' A) := by
      rw [← image_univ,← hAclosure]
      exact image_closure_subset_closure_image ambientDisk.continuous
    rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq ambientDisk hAmbientDisk]
    exact Subset.antisymm (closure_minimal (image_subset_range _ _) hAmbientDiskClosed) hdense
  have hGuideNonzeroHeight : ∀ y ∈ range b,
      y ∈ chartPull F cornerFan.chart (Metric.ball (0 : Plane) 1) →
      y ≠ d.first 1 → cornerFan.chart y.val 1 ≠ 0 := by
    intro y hy hsource hne hzero
    have hm : y ∈ chartPull F cornerFan.chart (Metric.ball (0 : Plane) 1) ∩
        range (f (some w)) := ⟨hsource,hy⟩
    rw [cornerFan.whole_open ⟨some w,hpw⟩] at hm
    obtain ⟨t,ht,he⟩ := hm
    have hrad : cornerFan.chart y.val ∈
        segment ℝ (incidentPorts f (d.first 1) cornerFan.chart
          cornerFan.left cornerFan.right (⟨some w,hpw⟩,false)) 0 ∪
        segment ℝ 0 (incidentPorts f (d.first 1) cornerFan.chart
          cornerFan.left cornerFan.right (⟨some w,hpw⟩,true)) := by
      rw [← cornerFan.radial_trace ⟨some w,hpw⟩]
      exact ⟨t,⟨ht.1.le,ht.2.le⟩,congrArg (fun z : ↥F => cornerFan.chart z.val) he⟩
    have hsigns := hselectedOpposite hpw
    have hleft : incidentPorts f (d.first 1) cornerFan.chart
        cornerFan.left cornerFan.right (⟨some w,hpw⟩,false) 1 ≠ 0 := by
      intro hz
      rw [hz,zero_mul] at hsigns
      exact (lt_irrefl 0) hsigns
    have hright : incidentPorts f (d.first 1) cornerFan.chart
        cornerFan.left cornerFan.right (⟨some w,hpw⟩,true) 1 ≠ 0 := by
      intro hz
      rw [hz,mul_zero] at hsigns
      exact (lt_irrefl 0) hsigns
    have hChartZero : cornerFan.chart y.val = 0 := by
      rcases hrad with hrad | hrad
      · rw [segment_eq_image'] at hrad
        obtain ⟨s,hs,hsval⟩ := hrad
        have hyzero := congrArg (fun z : Plane => z 1) hsval
        change incidentPorts f (d.first 1) cornerFan.chart
          cornerFan.left cornerFan.right (⟨some w,hpw⟩,false) 1 +
          s * (0 - incidentPorts f (d.first 1) cornerFan.chart
            cornerFan.left cornerFan.right (⟨some w,hpw⟩,false) 1) =
          cornerFan.chart y.val 1 at hyzero
        rw [hzero] at hyzero
        have hsone : s = 1 := by
          have hf : (1-s) * incidentPorts f (d.first 1) cornerFan.chart
              cornerFan.left cornerFan.right (⟨some w,hpw⟩,false) 1 = 0 := by
            nlinarith only [hyzero]
          have := (mul_eq_zero.mp hf).resolve_right hleft
          linarith
        simpa [hsone] using hsval.symm
      · rw [segment_eq_image'] at hrad
        obtain ⟨s,hs,hsval⟩ := hrad
        have hyzero := congrArg (fun z : Plane => z 1) hsval
        change 0 + s * (_ - 0) = _ at hyzero
        rw [hzero] at hyzero
        have hszero : s = 0 := (mul_eq_zero.mp (by simpa using hyzero)).resolve_right hright
        simpa [hszero] using hsval.symm
    apply hne
    apply Subtype.ext
    exact cornerFan.chart.injOn hsource.1 cornerFan.contact_in_source
      (hChartZero.trans cornerFan.contact_zero.symm)
  have hGuideCornerNhd : d.second ⁻¹'
      chartPull F cornerFan.chart (Metric.ball (0 : Plane) 1) ∈ nhds (1 : Interval) := by
    apply ((cornerFan.chart.isOpen_inter_preimage Metric.isOpen_ball).preimage
      (continuous_subtype_val.comp d.second.continuous)).mem_nhds
    change (d.second 1).val ∈ cornerFan.chart.source ∧
      cornerFan.chart (d.second 1).val ∈ Metric.ball (0 : Plane) 1
    rw [← d.corner_eq]
    exact ⟨cornerFan.contact_in_source,by rw [cornerFan.contact_zero]; simp⟩
  obtain ⟨guideEntryLower,hGuideEntryLower,hGuideEntrySuffix⟩ :=
    nhds_top_basis.mem_iff.mp hGuideCornerNhd
  obtain ⟨guideEntryTime,hGuideEntryAfter,hGuideEntryBefore⟩ :=
    exists_between (show max (0 : Interval) guideEntryLower < 1 from max_lt zero_lt_one hGuideEntryLower)
  have hGuideEntryInterior : guideEntryTime ∈ Ioo (0 : Interval) 1 :=
    ⟨(le_max_left _ _).trans_lt hGuideEntryAfter,hGuideEntryBefore⟩
  have hGuideEntrySource : d.second guideEntryTime ∈
      chartPull F cornerFan.chart (Metric.ball (0 : Plane) 1) :=
    hGuideEntrySuffix ((le_max_right _ _).trans_lt hGuideEntryAfter)
  let cornerEntry : Plane := cornerFan.chart (d.second guideEntryTime).val
  have hCornerEntryNonzeroHeight : cornerEntry 1 ≠ 0 := by
    apply hGuideNonzeroHeight (d.second guideEntryTime)
    · exact ⟨CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish guideEntryTime,
        (d.second_eq guideEntryTime).symm⟩
    · exact hGuideEntrySource
    · intro he
      have heq := d.second_embedded.injective (he.trans d.corner_eq)
      exact hGuideEntryBefore.ne heq
  have hCornerEntryOpen : cornerEntry ∈ Metric.ball (0 : Plane) 1 := hGuideEntrySource.2
  -- The repaired strict hull margin follows from strict margins for its fixed
  -- vertices; epsilon only controls the moving entry vertex.
  have hCornerHullOpenMargin (δ : ℝ)
      (hδopen : Plane.mk (-δ) 0 ∈ Metric.ball (0 : Plane) 1) :
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        regionalHalfCornerHull δ cornerEntry ε ⊆ Metric.ball (0 : Plane) 1 := by
    let vertex : ℝ → Plane := fun ε => Plane.mk (cornerEntry 0-ε) (cornerEntry 1)
    have hVertex : Continuous vertex := by fun_prop
    have hVertexZero : vertex 0 = cornerEntry := by
      ext i
      fin_cases i <;> simp [vertex,Plane.mk]
    have hVertexNhd : vertex ⁻¹' Metric.ball (0 : Plane) 1 ∈ nhds (0 : ℝ) :=
      hVertex.continuousAt.preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds (hVertexZero.symm ▸ hCornerEntryOpen))
    obtain ⟨ε₀,hε₀,hεBall⟩ := Metric.mem_nhds_iff.mp hVertexNhd
    refine ⟨ε₀,hε₀,?_⟩
    intro ε hε hεsmall
    apply convexHull_min _ (convex_ball (0 : Plane) 1)
    intro z hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · simp
    · exact hδopen
    · exact hCornerEntryOpen
    · apply hεBall
      simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos hε] using hεsmall

  have hReflectedFan (p : ↥F) (W : IncidentFanWindow F f V p) :
      ∃ W' : IncidentFanWindow F f V p,
        W'.chart = W.chart.transHomeomorph (ContinuousLinearEquiv.neg ℝ : Plane ≃L[ℝ] Plane).toHomeomorph ∧
        W'.left = W.left ∧ W'.right = W.right := by
    let N : Plane ≃L[ℝ] Plane := ContinuousLinearEquiv.neg ℝ
    let Q := W.chart.transHomeomorph N.toHomeomorph
    have hPullClosed : RegionalChordNormalization.chartPull F Q (Metric.closedBall (0 : Plane) 1) =
        RegionalChordNormalization.chartPull F W.chart (Metric.closedBall (0 : Plane) 1) := by
      ext y
      change (y.val ∈ W.chart.source ∧ -W.chart y.val ∈ Metric.closedBall 0 1) ↔
        (y.val ∈ W.chart.source ∧ W.chart y.val ∈ Metric.closedBall 0 1)
      simp only [Metric.mem_closedBall,dist_zero_right,norm_neg]
    have hPullOpen : RegionalChordNormalization.chartPull F Q (Metric.ball (0 : Plane) 1) =
        RegionalChordNormalization.chartPull F W.chart (Metric.ball (0 : Plane) 1) := by
      ext y
      change (y.val ∈ W.chart.source ∧ -W.chart y.val ∈ Metric.ball 0 1) ↔
        (y.val ∈ W.chart.source ∧ W.chart y.val ∈ Metric.ball 0 1)
      simp only [Metric.mem_ball,dist_zero_right,norm_neg]
    have hImage (a b : Plane) : (fun z : Plane => -z) '' segment ℝ a b =
        segment ℝ (-a) (-b) :=
      image_segment ℝ N.toLinearMap.toAffineMap a b
    let W' : IncidentFanWindow F f V p := {
      chart := Q
      source_closure := W.source_closure
      contact_in_source := W.contact_in_source
      contact_zero := by change -W.chart p.val = 0; rw [W.contact_zero,neg_zero]
      disk_in_target := by
        intro z hz
        change -z ∈ W.chart.target
        apply W.disk_in_target
        simpa only [Metric.mem_closedBall,dist_zero_right,norm_neg] using hz
      left := W.left
      right := W.right
      center := W.center
      cuts := W.cuts
      at_center := W.at_center
      whole_closed := by intro i; rw [hPullClosed]; exact W.whole_closed i
      whole_open := by intro i; rw [hPullOpen]; exact W.whole_open i
      radial_trace := by
        intro i
        have he := congrArg (fun T : Set Plane => (fun z : Plane => -z) '' T) (W.radial_trace i)
        rw [image_union,hImage,hImage,neg_zero,image_image] at he
        exact he
      nonincident_clear := by intro i hi; rw [hPullClosed]; exact W.nonincident_clear i hi
      ports_on_sphere := by
        intro z
        change -incidentPorts f p W.chart W.left W.right z ∈ Metric.sphere (0 : Plane) 1
        simpa only [Metric.mem_sphere,dist_zero_right,norm_neg] using W.ports_on_sphere z
      ports_injective := by
        intro z y he
        apply W.ports_injective
        exact neg_injective he }
    exact ⟨W',rfl,rfl,rfl⟩
  obtain ⟨reflectedFan,hReflectedChart,hReflectedLeft,hReflectedRight⟩ :=
    hReflectedFan (d.first 1) cornerFan
  let keepChart : Prop := StrictAntiOn oldCoordinateX (Icc coordinateLeft coordinateRight)
  let finalFan : IncidentFanWindow F f V (d.first 1) := if keepChart then cornerFan else reflectedFan
  let finalX : C(Interval,ℝ) := if keepChart then oldCoordinateX else -oldCoordinateX
  let finalSign : ℝ := if keepChart then calibrationSign else -calibrationSign
  have hFinalXAnti : StrictAntiOn finalX (Icc coordinateLeft coordinateRight) := by
    by_cases hk : keepChart
    · simpa only [finalX,if_pos hk] using hk
    · have hm := hOldCoordinateOrder.resolve_right hk
      intro s hs t ht hst
      change (if keepChart then oldCoordinateX else -oldCoordinateX) t <
        (if keepChart then oldCoordinateX else -oldCoordinateX) s
      simp only [hk,ite_false,ContinuousMap.neg_apply,neg_lt_neg_iff]
      exact hm hs ht hst
  have hFinalXZero : finalX cornerTime = 0 := by
    by_cases hk : keepChart <;> simp [finalX,hk,hOldCoordinateXZero]
  have hFinalSignUnit : finalSign = -1 ∨ finalSign = 1 := by
    by_cases hk : keepChart
    · simpa [finalSign,hk] using hCalibrationSign
    · rcases hCalibrationSign with hs | hs <;> simp [finalSign,hk,hs]
  have hFinalFanSource : finalFan.chart.source = cornerFan.chart.source := by
    by_cases hk : keepChart
    · simp [finalFan,hk]
    · simp [finalFan,hk,hReflectedChart]
  have hFinalFanPull (A : Set Plane) (hA : ∀ z : Plane, -z ∈ A ↔ z ∈ A) :
      chartPull F finalFan.chart A = chartPull F cornerFan.chart A := by
    by_cases hk : keepChart
    · simp [finalFan,hk]
    · simp only [finalFan,hk,ite_false,hReflectedChart]
      ext y
      change (y.val ∈ cornerFan.chart.source ∧ -cornerFan.chart y.val ∈ A) ↔ _
      rw [hA]
      rfl
  have hFinalPullOpen : chartPull F finalFan.chart (Metric.ball (0 : Plane) 1) =
      chartPull F cornerFan.chart (Metric.ball (0 : Plane) 1) := by
    apply hFinalFanPull
    intro z
    simp only [Metric.mem_ball,dist_zero_right,norm_neg]
  have hFinalPullClosed : chartPull F finalFan.chart (Metric.closedBall (0 : Plane) 1) =
      chartPull F cornerFan.chart (Metric.closedBall (0 : Plane) 1) := by
    apply hFinalFanPull
    intro z
    simp only [Metric.mem_closedBall,dist_zero_right,norm_neg]
  have hFinalNested : ∀ h : d.first 1 ∈ fan.events,
      chartPull F finalFan.chart (Metric.closedBall (0 : Plane) 1) ⊆
        chartPull F (fan.window ⟨d.first 1,h⟩).chart (Metric.ball (0 : Plane) 1) := by
    intro h
    rw [hFinalPullClosed]
    exact hcornerNested
  have hFinalAxes : ∀ h : d.first 1 ∈ range a,
      incidentPorts f (d.first 1) finalFan.chart finalFan.left finalFan.right (⟨some v,h⟩,false) 1 = 0 ∧
      incidentPorts f (d.first 1) finalFan.chart finalFan.left finalFan.right (⟨some v,h⟩,true) 1 = 0 := by
    intro h
    by_cases hk : keepChart
    · simpa [finalFan,hk] using And.intro hcornerLeftAxis hcornerRightAxis
    · simp only [finalFan,hk,ite_false,hReflectedChart,hReflectedLeft,hReflectedRight]
      change -(incidentPorts f (d.first 1) cornerFan.chart cornerFan.left cornerFan.right (⟨some v,h⟩,false) 1) = 0 ∧
        -(incidentPorts f (d.first 1) cornerFan.chart cornerFan.left cornerFan.right (⟨some v,h⟩,true) 1) = 0
      rw [hcornerLeftAxis,hcornerRightAxis]
      norm_num
  have hFinalPortSigns : ∀ j : incidentIndex f (d.first 1), j.val ≠ some v →
      incidentPorts f (d.first 1) finalFan.chart finalFan.left finalFan.right (j,false) 1 *
        incidentPorts f (d.first 1) finalFan.chart finalFan.left finalFan.right (j,true) 1 < 0 := by
    intro j hj
    have hs : incidentPorts f (d.first 1) cornerFan.chart cornerFan.left cornerFan.right (j,false) 1 *
        incidentPorts f (d.first 1) cornerFan.chart cornerFan.left cornerFan.right (j,true) 1 < 0 := by
      rcases hcornerSigns j hj with hs | hs
      · exact mul_neg_of_pos_of_neg hs.1 hs.2
      · exact mul_neg_of_neg_of_pos hs.1 hs.2
    by_cases hk : keepChart
    · simpa [finalFan,hk] using hs
    · simp only [finalFan,hk,ite_false,hReflectedChart,hReflectedLeft,hReflectedRight]
      change (-incidentPorts f (d.first 1) cornerFan.chart cornerFan.left cornerFan.right (j,false) 1) *
        (-incidentPorts f (d.first 1) cornerFan.chart cornerFan.left cornerFan.right (j,true) 1) < 0
      simpa only [neg_mul_neg] using hs
  have hFinalCoordinates : ∀ t ∈ Icc coordinateLeft coordinateRight, ∀ u : Icc (-1 : ℝ) 1,
      (calibratedOldStrip (clock t,u)).val ∈ finalFan.chart.source ∧
      finalFan.chart (calibratedOldStrip (clock t,u)).val =
        Plane.mk (finalX t) (finalSign*calibrationScale*u.val) := by
    intro t ht u
    have hc := hCalibratedOldCoordinates (clock t) u (hCoordinateClosedSub ht).1
    refine ⟨hFinalFanSource.symm ▸ hc.1,?_⟩
    by_cases hk : keepChart
    · simpa only [finalFan,finalX,finalSign,hk,ite_true,hOldCoordinateXEq t ht] using hc.2
    · simp only [finalFan,finalX,finalSign,hk,ite_false,hReflectedChart,ContinuousMap.neg_apply]
      change -cornerFan.chart (calibratedOldStrip (clock t,u)).val = _
      rw [hc.2,hOldCoordinateXEq t ht]
      ext i
      fin_cases i <;> simp [Plane.mk] <;> ring
  have hFinalUnit : ∀ t ∈ Icc coordinateLeft coordinateRight, ∀ u : Icc (-1 : ℝ) 1,
      calibratedOldStrip (clock t,u) ∈ chartPull F finalFan.chart (Metric.ball (0 : Plane) 1) := by
    intro t ht u
    rw [hFinalPullOpen]
    exact hCalibratedOldUnit _ _ (hCoordinateClosedSub ht).1
  have hFinalCutMem : calibratedCut ∈ Icc coordinateLeft coordinateRight :=
    ⟨(hCoordinateLeftUpper.trans hCalibratedCutLower).le,hCoordinateRightLower.le⟩
  have hFinalCornerMem : cornerTime ∈ Icc coordinateLeft coordinateRight :=
    ⟨hCoordinateLeftUpper.le,(hCalibratedCutLower.trans hCoordinateRightLower).le⟩
  let finalDelta : ℝ := -finalX calibratedCut
  have hFinalDelta : 0 < finalDelta := by
    have hn := hFinalXAnti hFinalCornerMem hFinalCutMem hCalibratedCutLower
    rw [hFinalXZero] at hn
    exact neg_pos.mpr hn
  have hFinalCutX : finalX calibratedCut = -finalDelta := by simp [finalDelta]
  have hFinalVertexOpen : Plane.mk (-finalDelta) 0 ∈ Metric.ball (0 : Plane) 1 := by
    have hc := (hFinalCoordinates calibratedCut hFinalCutMem ⟨0,by norm_num⟩).2
    have hu := (hFinalUnit calibratedCut hFinalCutMem ⟨0,by norm_num⟩).2
    rw [hc] at hu
    simpa [hFinalCutX] using hu
  have hFinalXOpenAnti : StrictAntiOn finalX oldCoordinateWindow :=
    hFinalXAnti.mono (fun _ h => ⟨h.1.le,h.2.le⟩)
  have hFinalGuideNonzeroHeight : ∀ y ∈ range b,
      y ∈ chartPull F finalFan.chart (Metric.ball (0 : Plane) 1) →
      y ≠ d.first 1 → finalFan.chart y.val 1 ≠ 0 := by
    intro y hy hsource hne
    rw [hFinalPullOpen] at hsource
    have hn := hGuideNonzeroHeight y hy hsource hne
    by_cases hk : keepChart
    · simpa [finalFan,hk] using hn
    · simp only [finalFan,hk,ite_false,hReflectedChart]
      change -(cornerFan.chart y.val 1) ≠ 0
      exact neg_ne_zero.mpr hn
  have hFinalEntryNhd : d.second ⁻¹' chartPull F finalFan.chart
      (Metric.ball (0 : Plane) 1 ∩ {z | |z 0| < finalDelta/2}) ∈ nhds (1 : Interval) := by
    apply ((finalFan.chart.isOpen_inter_preimage
      (Metric.isOpen_ball.inter (isOpen_lt (by fun_prop) continuous_const))).preimage
        (continuous_subtype_val.comp d.second.continuous)).mem_nhds
    change (d.second 1).val ∈ finalFan.chart.source ∧
      finalFan.chart (d.second 1).val ∈ Metric.ball (0 : Plane) 1 ∩ {z | |z 0| < finalDelta/2}
    rw [← d.corner_eq]
    refine ⟨finalFan.contact_in_source,?_⟩
    rw [finalFan.contact_zero]
    exact ⟨by simp,by simpa using half_pos hFinalDelta⟩
  obtain ⟨finalEntryLower,hFinalEntryLower,hFinalEntrySuffix⟩ := nhds_top_basis.mem_iff.mp hFinalEntryNhd
  obtain ⟨finalEntryTime,hFinalEntryAfter,hFinalEntryBefore⟩ :=
    exists_between (show max (0 : Interval) finalEntryLower < 1 from max_lt zero_lt_one hFinalEntryLower)
  have hFinalEntryInterior : finalEntryTime ∈ Ioo (0 : Interval) 1 :=
    ⟨(le_max_left _ _).trans_lt hFinalEntryAfter,hFinalEntryBefore⟩
  have hFinalEntrySource : d.second finalEntryTime ∈ chartPull F finalFan.chart
      (Metric.ball (0 : Plane) 1 ∩ {z | |z 0| < finalDelta/2}) :=
    hFinalEntrySuffix ((le_max_right _ _).trans_lt hFinalEntryAfter)
  let finalEntry : Plane := finalFan.chart (d.second finalEntryTime).val
  have hFinalEntryHeight : finalEntry 1 ≠ 0 := by
    apply hFinalGuideNonzeroHeight (d.second finalEntryTime)
    · exact ⟨CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish finalEntryTime,
        (d.second_eq finalEntryTime).symm⟩
    · exact ⟨hFinalEntrySource.1,hFinalEntrySource.2.1⟩
    · intro he
      exact hFinalEntryBefore.ne (d.second_embedded.injective (he.trans d.corner_eq))
  have hFinalEntryOpen : finalEntry ∈ Metric.ball (0 : Plane) 1 := hFinalEntrySource.2.1
  have hFinalEntryHorizontal : |finalEntry 0| < finalDelta/2 := hFinalEntrySource.2.2
  have hFinalHorizontalProgress : ∀ ε : ℝ, 0 < ε → ε < finalDelta/2 →
      0 < finalEntry 0-ε+finalDelta := by
    intro ε hε hεsmall
    have hx := (abs_lt.mp hFinalEntryHorizontal).1
    linarith only [hx,hεsmall]
  have hFinalHullMargin : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < finalDelta/2 ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        regionalHalfCornerHull finalDelta finalEntry ε ⊆ Metric.ball (0 : Plane) 1 := by
    let vertex : ℝ → Plane := fun ε => Plane.mk (finalEntry 0-ε) (finalEntry 1)
    have hVertex : Continuous vertex := by fun_prop
    have hVertexZero : vertex 0 = finalEntry := by ext i; fin_cases i <;> simp [vertex]
    have hVertexNhd : vertex ⁻¹' Metric.ball (0 : Plane) 1 ∈ nhds (0 : ℝ) :=
      hVertex.continuousAt.preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds (hVertexZero.symm ▸ hFinalEntryOpen))
    obtain ⟨ε₁,hε₁,hεBall⟩ := Metric.mem_nhds_iff.mp hVertexNhd
    obtain ⟨ε₀,hε₀,hε₀small⟩ := exists_between (lt_min hε₁ (half_pos hFinalDelta))
    refine ⟨ε₀,hε₀,hε₀small.trans_le (min_le_right _ _),?_⟩
    intro ε hε hεsmall
    apply convexHull_min _ (convex_ball (0 : Plane) 1)
    intro z hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · simp
    · exact hFinalVertexOpen
    · exact hFinalEntryOpen
    · apply hεBall
      have hh := hεsmall.trans (hε₀small.trans_le (min_le_left _ _))
      simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos hε] using hh
  have hNegativeAxisSegment (z : Plane) :
      z ∈ segment ℝ (0 : Plane) (Plane.mk (-finalDelta) 0) ↔
        z 1 = 0 ∧ z 0 ∈ Icc (-finalDelta) 0 := by
    constructor
    · intro hz
      rw [segment_eq_image'] at hz
      obtain ⟨t,ht,rfl⟩ := hz
      change 0+t*(0-0) = 0 ∧ -finalDelta ≤ 0+t*(-finalDelta-0) ∧
        0+t*(-finalDelta-0) ≤ 0
      refine ⟨by ring,?_,?_⟩ <;> nlinarith only [ht.1,ht.2,hFinalDelta]
    · rintro ⟨hy,hx⟩
      rw [segment_eq_image']
      refine ⟨-z 0/finalDelta,⟨?_,?_⟩,?_⟩
      · exact div_nonneg (neg_nonneg.mpr hx.2) hFinalDelta.le
      · apply (div_le_one hFinalDelta).mpr
        linarith only [hx.1]
      · ext i
        fin_cases i
        · change 0+(-z 0/finalDelta)*(-finalDelta-0) = z 0
          field_simp
          <;> ring
        · change 0+(-z 0/finalDelta)*(0-0) = z 1
          simpa using hy.symm
  have hFinalXSegmentImage : finalX '' Icc cornerTime calibratedCut = Icc (-finalDelta) 0 := by
    have he := finalX.continuous.continuousOn.image_Icc_of_antitoneOn hCalibratedCutLower.le
      (hFinalXAnti.antitoneOn.mono (Icc_subset_Icc hFinalCornerMem.1 hFinalCutMem.2))
    simpa only [hFinalXZero,hFinalCutX] using he
  have hFinalOldCenterCoordinates : ∀ t ∈ Icc coordinateLeft coordinateRight,
      (a (clock t)).val ∈ finalFan.chart.source ∧
      finalFan.chart (a (clock t)).val = Plane.mk (finalX t) 0 := by
    intro t ht
    have hc := hFinalCoordinates t ht ⟨0,by norm_num⟩
    rw [hCalibratedOldCenter] at hc
    simpa only [mul_zero] using hc
  have hFinalOldSegment : chartPull F finalFan.chart
      (segment ℝ (0 : Plane) (Plane.mk (-finalDelta) 0)) =
      a '' (clock '' Icc cornerTime calibratedCut) := by
    ext y
    constructor
    · rintro ⟨hy,hseg⟩
      have hs := (hNegativeAxisSegment (finalFan.chart y.val)).mp hseg
      obtain ⟨t,ht,he⟩ := hFinalXSegmentImage.symm ▸ hs.2
      have htc : t ∈ Icc coordinateLeft coordinateRight :=
        Icc_subset_Icc hFinalCornerMem.1 hFinalCutMem.2 ht
      have hc := hFinalOldCenterCoordinates t htc
      refine ⟨clock t,⟨t,ht,rfl⟩,?_⟩
      apply Subtype.ext
      apply finalFan.chart.injOn hc.1 hy
      rw [hc.2]
      ext i
      fin_cases i
      · exact he
      · exact hs.1.symm
    · rintro ⟨s,⟨t,ht,rfl⟩,rfl⟩
      have hc := hFinalOldCenterCoordinates t (Icc_subset_Icc hFinalCornerMem.1 hFinalCutMem.2 ht)
      refine ⟨hc.1,?_⟩
      rw [hc.2,hNegativeAxisSegment]
      exact ⟨rfl,hFinalXSegmentImage ▸ mem_image_of_mem finalX ht⟩
  let firstPath : Path (d.first 0) (d.first 1) := {
    toContinuousMap := d.first
    source' := rfl
    target' := rfl }
  let secondPath : Path (d.second 0) (d.first 1) := {
    toContinuousMap := d.second
    source' := rfl
    target' := d.corner_eq.symm }
  let sidePath : Path (d.first 0) (d.second 0) := {
    toContinuousMap := d.boundarySide
    source' := d.boundary_zero
    target' := d.boundary_one }
  let guideComplementPath := sidePath.symm.trans firstPath
  have hSideReverse : IsEmbedding sidePath.symm :=
    d.boundary_embedded.comp unitInterval.symmHomeomorph.isEmbedding
  have hGuideComplement : IsEmbedding guideComplementPath := by
    apply isEmbedding_path_trans_of_inter_singleton_probe _ _ hSideReverse d.first_embedded
    rw [Path.symm_range]
    exact (inter_comm _ _).trans d.first_boundary_inter
  have hGuideComplementRange : range guideComplementPath = range d.boundarySide ∪ range d.first := by
    rw [Path.trans_range,Path.symm_range]
    rfl
  have hGuideComplementMeet : range d.second ∩ range guideComplementPath =
      {d.second 0,d.second 1} := by
    rw [hGuideComplementRange,inter_union_distrib_left,d.second_boundary_inter,
      inter_comm (range d.second) (range d.first),d.sides_inter,d.corner_eq]
    rfl
  have hGuideComplementCollision : ∀ s t : Interval,
      d.second s = guideComplementPath t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t he
    have hm : d.second s ∈ range d.second ∩ range guideComplementPath :=
      ⟨mem_range_self _,⟨t,he.symm⟩⟩
    rw [hGuideComplementMeet,mem_insert_iff,mem_singleton_iff] at hm
    rcases hm with h0 | h1
    · exact Or.inl ⟨d.second_embedded.injective h0,
        hGuideComplement.injective (he.symm.trans (h0.trans guideComplementPath.source.symm))⟩
    · exact Or.inr ⟨d.second_embedded.injective h1,
        hGuideComplement.injective (he.symm.trans (h1.trans (d.corner_eq.symm.trans guideComplementPath.target.symm)))⟩
  have hGuideDiskBoundary : d.disk '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      range d.second ∪ range guideComplementPath := by
    rw [d.boundary_image,hGuideComplementRange]
    rw [union_comm (range d.first) (range d.second),union_assoc,
      union_comm (range d.first) (range d.boundarySide)]
  let oldComplementPath := sidePath.trans secondPath
  have hOldComplement : IsEmbedding oldComplementPath := by
    apply isEmbedding_path_trans_of_inter_singleton_probe _ _ d.boundary_embedded d.second_embedded
    exact (inter_comm _ _).trans d.second_boundary_inter
  have hOldComplementRange : range oldComplementPath = range d.boundarySide ∪ range d.second := by
    rw [Path.trans_range]
    rfl
  have hOldComplementMeet : range d.first ∩ range oldComplementPath = {d.first 0,d.first 1} := by
    rw [hOldComplementRange,inter_union_distrib_left,d.first_boundary_inter,d.sides_inter]
    rfl
  have hOldComplementCollision : ∀ s t : Interval,
      d.first s = oldComplementPath t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t he
    have hm : d.first s ∈ range d.first ∩ range oldComplementPath :=
      ⟨mem_range_self _,⟨t,he.symm⟩⟩
    rw [hOldComplementMeet,mem_insert_iff,mem_singleton_iff] at hm
    rcases hm with h0 | h1
    · exact Or.inl ⟨d.first_embedded.injective h0,
        hOldComplement.injective (he.symm.trans (h0.trans oldComplementPath.source.symm))⟩
    · exact Or.inr ⟨d.first_embedded.injective h1,
        hOldComplement.injective (he.symm.trans (h1.trans oldComplementPath.target.symm))⟩
  have hOldDiskBoundary : d.disk '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      range d.first ∪ range oldComplementPath := by
    rw [d.boundary_image,hOldComplementRange]
    rw [union_assoc,union_comm (range d.second) (range d.boundarySide)]
  have hFanTrace (p : ↥F) (W : IncidentFanWindow F f V p)
      (i : incidentIndex f p) (y : ↥F) (hy : y.val ∈ W.chart.source)
      (hyball : W.chart y.val ∈ Metric.closedBall (0 : Plane) 1) :
      y ∈ range (f i.val) ↔ W.chart y.val ∈
        segment ℝ (incidentPorts f p W.chart W.left W.right (i,false)) 0 ∪
          segment ℝ 0 (incidentPorts f p W.chart W.left W.right (i,true)) := by
    constructor
    · intro hyf
      have hcut : y ∈ f i.val '' Icc (W.left i) (W.right i) :=
        W.whole_closed i ▸ ⟨⟨hy,hyball⟩,hyf⟩
      obtain ⟨t,ht,rfl⟩ := hcut
      exact W.radial_trace i ▸ ⟨t,ht,rfl⟩
    · intro hyf
      obtain ⟨t,ht,he⟩ := W.radial_trace i |>.symm ▸ hyf
      have hcut : f i.val t ∈ f i.val '' Icc (W.left i) (W.right i) := ⟨t,ht,rfl⟩
      have hs : (f i.val t).val ∈ W.chart.source := (W.whole_closed i |>.symm ▸ hcut).1.1
      exact ⟨t,Subtype.ext (W.chart.injOn hs hy he)⟩
  have hHorizontalPorts (u v z : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
      (huv : u ≠ v) (hu1 : u 1 = 0) (hv1 : v 1 = 0) (hz : ‖z‖ ≤ 1) :
      z ∈ segment ℝ u 0 ∪ segment ℝ 0 v ↔ z 1 = 0 := by
    have hun : u ≠ 0 := by intro he; simpa [he] using hu
    have hq : u 0 ^ 2 = v 0 ^ 2 := by
      have a := EuclideanSpace.real_norm_sq_eq u
      have b := EuclideanSpace.real_norm_sq_eq v
      simp [hu,hv,hu1,hv1,Fin.sum_univ_two] at a b
      linarith
    have hvu : v = -u := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hq with he | he
      · exact (huv (by ext i; fin_cases i; exact he; simpa [hu1,hv1])).elim
      · ext i
        fin_cases i
        · change v 0 = -u 0
          linarith
        · change v 1 = -u 1
          rw [hv1,hu1,neg_zero]
    rw [hvu,segment_symm ℝ u 0]
    constructor
    · rintro (⟨a,b,ha,hb,hab,he⟩ | ⟨a,b,ha,hb,hab,he⟩)
      · have := congrArg (fun z : Plane => z 1) he
        simpa [hu1] using this.symm
      · have := congrArg (fun z : Plane => z 1) he
        simpa [hu1] using this.symm
    · intro hz1
      have hd : Plane.det u z = 0 := by simp [Plane.det,hu1,hz1]
      obtain ⟨s,hs⟩ := (Plane.det_eq_zero_iff_smul u z hun).mp hd
      have hns : |s| ≤ 1 := by
        rw [hs,norm_smul,Real.norm_eq_abs,hu,mul_one] at hz
        exact hz
      rcases le_total 0 s with hp | hm
      · left
        rw [hs]
        exact ⟨1-s,s,sub_nonneg.mpr ((le_abs_self s).trans hns),hp,by ring,by simp⟩
      · right
        have he : z = (-s) • (-u) := by rw [hs]; module
        rw [he]
        exact ⟨1-(-s),-s,sub_nonneg.mpr ((neg_le_abs s).trans hns),
          neg_nonneg.mpr hm,by ring,by simp⟩
  have hFanAxis (p : ↥F) (W : IncidentFanWindow F f V p)
      (i : incidentIndex f p)
      (hi0 : incidentPorts f p W.chart W.left W.right (i,false) 1 = 0)
      (hi1 : incidentPorts f p W.chart W.left W.right (i,true) 1 = 0)
      (y : ↥F) (hy : y.val ∈ W.chart.source)
      (hyball : W.chart y.val ∈ Metric.closedBall (0 : Plane) 1) :
      y ∈ range (f i.val) ↔ W.chart y.val 1 = 0 := by
    apply (hFanTrace p W i y hy hyball).trans
    apply hHorizontalPorts
      (incidentPorts f p W.chart W.left W.right (i,false))
      (incidentPorts f p W.chart W.left W.right (i,true)) (W.chart y.val)
    · simpa only [Metric.mem_sphere,dist_zero_right] using W.ports_on_sphere (i,false)
    · simpa only [Metric.mem_sphere,dist_zero_right] using W.ports_on_sphere (i,true)
    · exact fun he => Bool.false_ne_true (congrArg Prod.snd (W.ports_injective he))
    · exact hi0
    · exact hi1
    · simpa only [Metric.mem_closedBall,dist_zero_right] using hyball
  have hRadialHeightInjective (p q : Plane) (hpq : p 1*q 1 < 0) :
      InjOn (fun z : Plane => z 1) (segment ℝ p 0 ∪ segment ℝ 0 q) := by
    have hp : p 1 ≠ 0 := by intro he; rw [he,zero_mul] at hpq; exact (lt_irrefl 0) hpq
    have hq : q 1 ≠ 0 := by intro he; rw [he,mul_zero] at hpq; exact (lt_irrefl 0) hpq
    have hOne (v : Plane) (hv : v 1 ≠ 0) :
        InjOn (fun z : Plane => z 1) (segment ℝ (0 : Plane) v) := by
      intro x hx y hy he
      rw [segment_eq_image'] at hx hy
      obtain ⟨s,hs,rfl⟩ := hx
      obtain ⟨t,ht,rfl⟩ := hy
      have hst : s = t := mul_right_cancel₀ hv (by simpa using he)
      rw [hst]
    have hMixed (x y : Plane) (hx : x ∈ segment ℝ (0 : Plane) p)
        (hy : y ∈ segment ℝ (0 : Plane) q) (he : x 1 = y 1) : x = y := by
      rw [segment_eq_image'] at hx hy
      obtain ⟨s,hs,rfl⟩ := hx
      obtain ⟨t,ht,rfl⟩ := hy
      change 0+s*(p 1-0) = 0+t*(q 1-0) at he
      have hz : s*p 1 = 0 := by
        rcases mul_neg_iff.mp hpq with hsign | hsign
        · nlinarith only [he,mul_nonneg hs.1 hsign.1.le,
            mul_nonpos_of_nonneg_of_nonpos ht.1 hsign.2.le]
        · nlinarith only [he,mul_nonpos_of_nonneg_of_nonpos hs.1 hsign.1.le,
            mul_nonneg ht.1 hsign.2.le]
      have hs0 := (mul_eq_zero.mp hz).resolve_right hp
      have ht0 : t = 0 := (mul_eq_zero.mp (by linarith only [he,hz] : t*q 1 = 0)).resolve_right hq
      simp [hs0,ht0]
    rw [segment_symm ℝ p 0]
    intro x hx y hy he
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hOne p hp hx hy he
    · exact hMixed x y hx hy he
    · exact (hMixed y x hy hx he.symm).symm
    · exact hOne q hq hx hy he
  let guideIndex : incidentIndex f (d.first 1) := ⟨some w,hpw⟩
  let guideHeight : Interval → ℝ := fun t => finalFan.chart (b t).val 1
  have hGuideFanSource : ∀ t ∈ Icc (finalFan.left guideIndex) (finalFan.right guideIndex),
      (b t).val ∈ finalFan.chart.source := by
    intro t ht
    exact ((finalFan.whole_closed guideIndex).symm ▸ mem_image_of_mem (f (some w)) ht).1.1
  have hGuideFanHeightContinuous : ContinuousOn guideHeight
      (Icc (finalFan.left guideIndex) (finalFan.right guideIndex)) :=
    (by fun_prop : Continuous (fun z : Plane => z 1)).continuousOn.comp
      (finalFan.chart.continuousOn.comp b.continuous.subtype_val.continuousOn hGuideFanSource)
      (fun _ _ => mem_univ _)
  have hGuideFanHeightInjective : InjOn guideHeight
      (Icc (finalFan.left guideIndex) (finalFan.right guideIndex)) := by
    intro s hs t ht he
    apply (r w).val.property.1.injective
    apply Subtype.ext
    apply finalFan.chart.injOn (hGuideFanSource s hs) (hGuideFanSource t ht)
    apply hRadialHeightInjective _ _ (hFinalPortSigns guideIndex (by simpa [guideIndex] using Ne.symm hvw))
    · exact finalFan.radial_trace guideIndex ▸ mem_image_of_mem (fun u => finalFan.chart (b u).val) hs
    · exact finalFan.radial_trace guideIndex ▸ mem_image_of_mem (fun u => finalFan.chart (b u).val) ht
    · exact he
  have hGuideFanHeightOrder : StrictMonoOn guideHeight
      (Icc (finalFan.left guideIndex) (finalFan.right guideIndex)) ∨
      StrictAntiOn guideHeight (Icc (finalFan.left guideIndex) (finalFan.right guideIndex)) :=
    hGuideFanHeightContinuous.strictMonoOn_of_injOn_Icc'
      ((finalFan.cuts guideIndex).2.1.trans (finalFan.cuts guideIndex).2.2.1).le
      hGuideFanHeightInjective
  let guideRays : Set Plane :=
    segment ℝ (incidentPorts f (d.first 1) finalFan.chart finalFan.left finalFan.right (guideIndex,false)) 0 ∪
      segment ℝ 0 (incidentPorts f (d.first 1) finalFan.chart finalFan.left finalFan.right (guideIndex,true))
  have hGuideRaysHeight : InjOn (fun z : Plane => z 1) guideRays :=
    hRadialHeightInjective _ _ (hFinalPortSigns guideIndex (by simpa [guideIndex] using Ne.symm hvw))
  have hFinalSuffixSource : ∀ t ∈ Icc finalEntryTime (1 : Interval),
      d.second t ∈ chartPull F finalFan.chart (Metric.ball (0 : Plane) 1) := by
    intro t ht
    have hh := hFinalEntrySuffix
      ((le_max_right _ _).trans_lt (hFinalEntryAfter.trans_le ht.1))
    exact ⟨hh.1,hh.2.1⟩
  have hFinalSuffixRays : ∀ t ∈ Icc finalEntryTime (1 : Interval),
      finalFan.chart (d.second t).val ∈ guideRays := by
    intro t ht
    have hh := hFinalSuffixSource t ht
    apply (hFanTrace (d.first 1) finalFan guideIndex (d.second t) hh.1
      (Metric.ball_subset_closedBall hh.2)).mp
    exact ⟨CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish t,(d.second_eq t).symm⟩
  have hEntryRay : finalEntry ∈ guideRays := hFinalSuffixRays finalEntryTime ⟨le_rfl,le_top⟩
  have hEntrySegmentRays : segment ℝ (0 : Plane) finalEntry ⊆ guideRays := by
    rcases hEntryRay with he | he
    · exact (convex_segment _ _).segment_subset (right_mem_segment ℝ _ _) he |>.trans subset_union_left
    · exact (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) he |>.trans subset_union_right
  let suffixHeight : Interval → ℝ := fun t => finalFan.chart (d.second t).val 1
  have hSuffixHeightContinuous : ContinuousOn suffixHeight (Icc finalEntryTime (1 : Interval)) :=
    (by fun_prop : Continuous (fun z : Plane => z 1)).continuousOn.comp
      (finalFan.chart.continuousOn.comp d.second.continuous.subtype_val.continuousOn
        (fun t ht => (hFinalSuffixSource t ht).1)) (fun _ _ => mem_univ _)
  have hSuffixHeightInjective : InjOn suffixHeight (Icc finalEntryTime (1 : Interval)) := by
    intro s hs t ht he
    apply d.second_embedded.injective
    apply Subtype.ext
    exact finalFan.chart.injOn (hFinalSuffixSource s hs).1 (hFinalSuffixSource t ht).1
      (hGuideRaysHeight (hFinalSuffixRays s hs) (hFinalSuffixRays t ht) he)
  have hSuffixHeightOne : suffixHeight 1 = 0 := by
    change finalFan.chart (d.second 1).val 1 = 0
    rw [←d.corner_eq,finalFan.contact_zero]
    rfl
  have hSuffixHeightImage : suffixHeight '' Icc finalEntryTime (1 : Interval) = uIcc (0 : ℝ) (finalEntry 1) := by
    rcases hSuffixHeightContinuous.strictMonoOn_of_injOn_Icc' hFinalEntryBefore.le hSuffixHeightInjective with hm | hm
    · have he := hSuffixHeightContinuous.image_Icc_of_monotoneOn hFinalEntryBefore.le hm.monotoneOn
      have hle : finalEntry 1 ≤ 0 := by
        have hh := hm.monotoneOn (left_mem_Icc.mpr hFinalEntryBefore.le)
          (right_mem_Icc.mpr hFinalEntryBefore.le) hFinalEntryBefore.le
        simpa only [hSuffixHeightOne] using hh
      simpa only [hSuffixHeightOne,uIcc_of_ge hle] using he
    · have he := hSuffixHeightContinuous.image_Icc_of_antitoneOn hFinalEntryBefore.le hm.antitoneOn
      have hle : 0 ≤ finalEntry 1 := by
        have hh := hm.antitoneOn (left_mem_Icc.mpr hFinalEntryBefore.le)
          (right_mem_Icc.mpr hFinalEntryBefore.le) hFinalEntryBefore.le
        simpa only [hSuffixHeightOne] using hh
      simpa only [hSuffixHeightOne,uIcc_of_le hle] using he
  let heightLinear : Plane →ₗ[ℝ] ℝ := {
    toFun := fun z => z 1
    map_add' := by intro x y; rfl
    map_smul' := by intro s x; rfl }
  have hEntrySegmentHeight : (fun z : Plane => z 1) '' segment ℝ (0 : Plane) finalEntry =
      uIcc (0 : ℝ) (finalEntry 1) := by
    have he := image_segment ℝ heightLinear.toAffineMap (0 : Plane) finalEntry
    change (fun z : Plane => z 1) '' segment ℝ (0 : Plane) finalEntry =
      segment ℝ (0 : ℝ) (finalEntry 1) at he
    simpa only [segment_eq_uIcc] using he
  have hFinalGuideSegment : chartPull F finalFan.chart (segment ℝ (0 : Plane) finalEntry) =
      d.second '' Icc finalEntryTime (1 : Interval) := by
    ext y
    constructor
    · rintro ⟨hy,hseg⟩
      have hh : finalFan.chart y.val 1 ∈ uIcc (0 : ℝ) (finalEntry 1) :=
        hEntrySegmentHeight ▸ mem_image_of_mem (fun z : Plane => z 1) hseg
      obtain ⟨t,ht,he⟩ := hSuffixHeightImage.symm ▸ hh
      refine ⟨t,ht,?_⟩
      apply Subtype.ext
      exact finalFan.chart.injOn (hFinalSuffixSource t ht).1 hy
        (hGuideRaysHeight (hFinalSuffixRays t ht) (hEntrySegmentRays hseg) he)
    · rintro ⟨t,ht,rfl⟩
      refine ⟨(hFinalSuffixSource t ht).1,?_⟩
      have hh : suffixHeight t ∈ uIcc (0 : ℝ) (finalEntry 1) :=
        hSuffixHeightImage ▸ mem_image_of_mem suffixHeight ht
      obtain ⟨z,hz,he⟩ := hEntrySegmentHeight.symm ▸ hh
      exact (hGuideRaysHeight (hEntrySegmentRays hz) (hFinalSuffixRays t ht) he) ▸ hz
  have hFinalSourceInterior : finalFan.chart.source ⊆ interior F :=
    fun _ h => (finalFan.source_closure (subset_closure h)).2
  have hFinalBoundaryClear : ∀ t, (d.boundarySide t).val ∉ finalFan.chart.source := by
    intro t ht
    exact disjoint_left.mp disjoint_interior_frontier (hFinalSourceInterior ht)
      (hBF (d.boundary_in_B t))
  have hFinalBoundaryRangeClear : Disjoint finalFan.chart.source (Subtype.val '' range d.boundarySide) := by
    apply disjoint_left.mpr
    rintro y hy ⟨z,⟨t,rfl⟩,rfl⟩
    exact hFinalBoundaryClear t hy
  have hFinalFrontierTwoSides : ∀ z ∈ Metric.ball (0 : Plane) 1,
      finalFan.chart.symm z ∈ frontier (range ambientDisk) ↔
        finalFan.chart.symm z ∈ Subtype.val '' range d.first ∪ Subtype.val '' range d.second := by
    intro z hz
    have hsource := finalFan.chart.map_target (finalFan.disk_in_target (Metric.ball_subset_closedBall hz))
    rw [hAmbientDiskFrontier,image_union,image_union]
    constructor
    · rintro (h | h)
      · exact h
      · exact False.elim (disjoint_left.mp hFinalBoundaryRangeClear hsource h)
    · exact Or.inl
  let finalChartPullback : Metric.closedBall (0 : Plane) 1 → ↥F := fun z =>
    ⟨finalFan.chart.symm z.val,
      interior_subset (hFinalSourceInterior (finalFan.chart.map_target (finalFan.disk_in_target z.property)))⟩
  have hFinalChartPullbackSource : ∀ z, (finalChartPullback z).val ∈ finalFan.chart.source :=
    fun z => finalFan.chart.map_target (finalFan.disk_in_target z.property)
  have hFinalChartPullbackCoord : ∀ z, finalFan.chart (finalChartPullback z).val = z.val :=
    fun z => finalFan.chart.right_inv (finalFan.disk_in_target z.property)
  have hFinalChartPullbackContinuous : Continuous finalChartPullback :=
    (finalFan.chart.symm.continuousOn.comp_continuous continuous_subtype_val
      (fun z => finalFan.disk_in_target z.property)).subtype_mk _
  have hFinalChartOldAxis : ∀ z : Metric.closedBall (0 : Plane) 1,
      finalChartPullback z ∈ range a ↔ z.val 1 = 0 := by
    intro z
    have hh := hFanAxis (d.first 1) finalFan ⟨some v,hpv⟩
      (hFinalAxes hpv).1 (hFinalAxes hpv).2 (finalChartPullback z)
      (hFinalChartPullbackSource z) (by rw [hFinalChartPullbackCoord]; exact z.property)
    change (finalChartPullback z ∈ range a ↔ finalFan.chart (finalChartPullback z).val 1 = 0) at hh
    rwa [hFinalChartPullbackCoord] at hh
  have hHorizontalNorm (u : ℝ) : ‖Plane.mk u 0‖ = |u| := by
    have he := EuclideanSpace.real_norm_sq_eq (Plane.mk u 0)
    simp only [Fin.sum_univ_two] at he
    change ‖Plane.mk u 0‖^2 = u^2+0^2 at he
    nlinarith only [he,norm_nonneg (Plane.mk u 0),abs_nonneg u,sq_abs u]
  have hFinalDeltaLtOne : finalDelta < 1 := by
    have hn : ‖Plane.mk (-finalDelta) 0‖ < 1 := by
      simpa only [Metric.mem_ball,dist_zero_right] using hFinalVertexOpen
    rw [hHorizontalNorm,abs_neg,abs_of_pos hFinalDelta] at hn
    exact hn
  let axisPoint : Icc (-1 : ℝ) 1 → Metric.closedBall (0 : Plane) 1 :=
    fun u => ⟨Plane.mk u.val 0,by
      simpa only [Metric.mem_closedBall,dist_zero_right,hHorizontalNorm] using abs_le.mpr u.property⟩
  have hAxisPointContinuous : Continuous axisPoint := by
    apply Continuous.subtype_mk
    fun_prop
  have hAxisPointOnOld : ∀ u, finalChartPullback (axisPoint u) ∈ range a :=
    fun u => (hFinalChartOldAxis (axisPoint u)).mpr rfl
  have hClockRange : range aclock = range a := clock.surjective.range_comp a
  let axisLift : Icc (-1 : ℝ) 1 → range aclock :=
    fun u => ⟨finalChartPullback (axisPoint u),hClockRange.symm ▸ hAxisPointOnOld u⟩
  have hAxisLiftContinuous : Continuous axisLift :=
    (hFinalChartPullbackContinuous.comp hAxisPointContinuous).subtype_mk _
  let axisParameter : Icc (-1 : ℝ) 1 → Interval := fun u => haclock.toHomeomorph.symm (axisLift u)
  have hAxisParameterContinuous : Continuous axisParameter :=
    haclock.toHomeomorph.symm.continuous.comp hAxisLiftContinuous
  have hAxisParameterValue : ∀ u, aclock (axisParameter u) = finalChartPullback (axisPoint u) :=
    fun u => congrArg Subtype.val (haclock.toHomeomorph.apply_symm_apply (axisLift u))
  have hAxisParameterCoord : ∀ u, finalFan.chart (aclock (axisParameter u)).val = Plane.mk u.val 0 := by
    intro u
    rw [hAxisParameterValue,hFinalChartPullbackCoord]
  have hAxisParameterInjective : Function.Injective axisParameter := by
    intro u z he
    apply Subtype.ext
    have hc := (hAxisParameterCoord u).symm.trans ((congrArg (fun t => finalFan.chart (aclock t).val) he).trans (hAxisParameterCoord z))
    exact congrArg (fun p : Plane => p 0) hc
  have hAxisParameterZero : axisParameter ⟨0,by norm_num⟩ = cornerTime := by
    apply haclock.injective
    apply Subtype.ext
    apply finalFan.chart.injOn
    · rw [hAxisParameterValue]
      exact hFinalChartPullbackSource _
    · rw [hclockCorner]
      exact finalFan.contact_in_source
    · rw [hAxisParameterCoord,hclockCorner,finalFan.contact_zero]
      ext i
      fin_cases i <;> rfl
  let negativeCut : Icc (-1 : ℝ) 1 := ⟨-finalDelta,⟨by linarith only [hFinalDeltaLtOne],by linarith only [hFinalDelta]⟩⟩
  have hAxisParameterCut : axisParameter negativeCut = calibratedCut := by
    apply haclock.injective
    apply Subtype.ext
    apply finalFan.chart.injOn
    · rw [hAxisParameterValue]
      exact hFinalChartPullbackSource _
    · exact (hFinalOldCenterCoordinates calibratedCut hFinalCutMem).1
    · rw [hAxisParameterCoord]
      change Plane.mk (-finalDelta) 0 = finalFan.chart (a (clock calibratedCut)).val
      rw [(hFinalOldCenterCoordinates calibratedCut hFinalCutMem).2,hFinalCutX]
  have hAxisParameterAnti : StrictAnti axisParameter := by
    letI : Fact ((-1 : ℝ) ≤ 1) := ⟨by norm_num⟩
    rcases hAxisParameterContinuous.strictMono_of_inj hAxisParameterInjective with hm | hm
    · have hh := hm (show negativeCut < ⟨0,by norm_num⟩ from neg_neg_of_pos hFinalDelta)
      rw [hAxisParameterCut,hAxisParameterZero] at hh
      exact False.elim ((not_lt_of_ge hCalibratedCutLower.le) hh)
    · exact hm
  have hAxisFirstCriterion : ∀ u : Icc (-1 : ℝ) 1,
      finalChartPullback (axisPoint u) ∈ range d.first ↔ 0 ≤ u.val := by
    intro u
    rw [hfirstRange,← hAxisParameterValue]
    constructor
    · rintro ⟨t,ht,he⟩
      have heq := haclock.injective he
      have hle : axisParameter u ≤ axisParameter ⟨0,by norm_num⟩ := by
        rw [hAxisParameterZero]
        exact heq ▸ ht.2
      exact hAxisParameterAnti.le_iff_ge.mp hle
    · intro hu
      refine ⟨axisParameter u,⟨bot_le,?_⟩,rfl⟩
      rw [← hAxisParameterZero]
      exact hAxisParameterAnti.antitone hu
  have hFinalRetainedTest : finalFan.chart.symm (Plane.mk (-1/2) 0) ∉ range ambientDisk := by
    let u : Icc (-1 : ℝ) 1 := ⟨-1/2,by norm_num⟩
    have ha : finalChartPullback (axisPoint u) ∈ range a := hAxisPointOnOld u
    intro hdisk
    have hd : finalChartPullback (axisPoint u) ∈ range d.disk := by
      obtain ⟨z,hz⟩ := hdisk
      exact ⟨z,Subtype.ext hz⟩
    have hf : finalChartPullback (axisPoint u) ∈ range d.first := d.whole_first ▸ And.intro hd ha
    have hu := (hAxisFirstCriterion u).mp hf
    norm_num [u] at hu
  have hGuideCenterEq : finalFan.center guideIndex = d.bFinish := by
    apply (r w).val.property.1.injective
    exact (finalFan.at_center guideIndex).trans (d.corner_eq.trans hsecond1)
  have hGuideCenterCoord : finalFan.chart (b (finalFan.center guideIndex)).val = 0 := by
    change finalFan.chart (f guideIndex.val (finalFan.center guideIndex)).val = 0
    rw [finalFan.at_center,finalFan.contact_zero]
  have hGuideIntervalSegment : ∀ s t : Interval, s ≤ t →
      Icc s t ⊆ Icc (finalFan.left guideIndex) (finalFan.right guideIndex) →
      segment ℝ (finalFan.chart (b s).val) (finalFan.chart (b t).val) ⊆ guideRays →
      (fun u => finalFan.chart (b u).val) '' Icc s t =
        segment ℝ (finalFan.chart (b s).val) (finalFan.chart (b t).val) := by
    intro s t hst hsub hseg
    have hc := hGuideFanHeightContinuous.mono hsub
    have hi := hGuideFanHeightInjective.mono hsub
    have himage : guideHeight '' Icc s t = uIcc (guideHeight s) (guideHeight t) := by
      rcases hc.strictMonoOn_of_injOn_Icc' hst hi with hm | hm
      · rw [uIcc_of_le (hm.monotoneOn (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst) hst)]
        exact hc.image_Icc_of_monotoneOn hst hm.monotoneOn
      · rw [uIcc_of_ge (hm.antitoneOn (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst) hst)]
        exact hc.image_Icc_of_antitoneOn hst hm.antitoneOn
    have hheight : (fun z : Plane => z 1) ''
        segment ℝ (finalFan.chart (b s).val) (finalFan.chart (b t).val) =
        uIcc (guideHeight s) (guideHeight t) := by
      have he := image_segment ℝ heightLinear.toAffineMap
        (finalFan.chart (b s).val) (finalFan.chart (b t).val)
      change (fun z : Plane => z 1) '' _ = segment ℝ (guideHeight s) (guideHeight t) at he
      simpa only [segment_eq_uIcc] using he
    ext z
    constructor
    · rintro ⟨u,hu,rfl⟩
      have hh : guideHeight u ∈ uIcc (guideHeight s) (guideHeight t) := himage ▸ mem_image_of_mem _ hu
      obtain ⟨z,hz,he⟩ := hheight.symm ▸ hh
      have hr : finalFan.chart (b u).val ∈ guideRays := by
        change finalFan.chart (f guideIndex.val u).val ∈ _
        change _ ∈ _ ∪ _
        rw [←finalFan.radial_trace]
        exact mem_image_of_mem _ (hsub hu)
      change finalFan.chart (b u).val ∈ _
      rw [←hGuideRaysHeight (hseg hz) hr he]
      exact hz
    · intro hz
      have hh : z 1 ∈ uIcc (guideHeight s) (guideHeight t) := hheight ▸ mem_image_of_mem _ hz
      obtain ⟨u,hu,he⟩ := himage.symm ▸ hh
      refine ⟨u,hu,?_⟩
      have hr : finalFan.chart (b u).val ∈ guideRays := by
        change finalFan.chart (f guideIndex.val u).val ∈ _
        change _ ∈ _ ∪ _
        rw [←finalFan.radial_trace]
        exact mem_image_of_mem _ (hsub hu)
      exact hGuideRaysHeight hr (hseg hz) he
  have hGuideLeftHalf : (fun u => finalFan.chart (b u).val) ''
      Icc (finalFan.left guideIndex) (finalFan.center guideIndex) =
      segment ℝ (incidentPorts f (d.first 1) finalFan.chart finalFan.left finalFan.right (guideIndex,false)) 0 := by
    have hc := finalFan.cuts guideIndex
    have hh := hGuideIntervalSegment (finalFan.left guideIndex) (finalFan.center guideIndex)
      hc.2.1.le (Icc_subset_Icc le_rfl hc.2.2.1.le)
    rw [hGuideCenterCoord] at hh
    exact hh subset_union_left
  have hGuideRightHalf : (fun u => finalFan.chart (b u).val) ''
      Icc (finalFan.center guideIndex) (finalFan.right guideIndex) =
      segment ℝ 0 (incidentPorts f (d.first 1) finalFan.chart finalFan.left finalFan.right (guideIndex,true)) := by
    have hc := finalFan.cuts guideIndex
    have hh := hGuideIntervalSegment (finalFan.center guideIndex) (finalFan.right guideIndex)
      hc.2.2.1.le (Icc_subset_Icc hc.2.1.le le_rfl)
    rw [hGuideCenterCoord] at hh
    exact hh subset_union_right
  let incomingPort : Plane := incidentPorts f (d.first 1) finalFan.chart finalFan.left finalFan.right
    (guideIndex,if d.bStart = 0 then false else true)
  have hIncomingPortNorm : ‖incomingPort‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using finalFan.ports_on_sphere
      (guideIndex,if d.bStart = 0 then false else true)
  have hFinalSecondRay : ∀ z : Metric.closedBall (0 : Plane) 1,
      finalChartPullback z ∈ range d.second ↔ z.val ∈ segment ℝ (0 : Plane) incomingPort := by
    intro z
    constructor
    · intro hz
      have hb : finalChartPullback z ∈ range b := by
        rw [hsecondRange] at hz
        exact image_subset_range _ _ hz
      have ht : finalChartPullback z ∈ chartPull F finalFan.chart (Metric.closedBall (0 : Plane) 1) ∩ range (f guideIndex.val) :=
        ⟨⟨hFinalChartPullbackSource z,by rw [hFinalChartPullbackCoord]; exact z.property⟩,hb⟩
      rw [finalFan.whole_closed] at ht
      obtain ⟨t,ht,he⟩ := ht
      change b t = finalChartPullback z at he
      have htsecond : t ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) := by
        rw [hsecondRange] at hz
        obtain ⟨u,hu,huq⟩ := hz
        have hut : u = t := (r w).val.property.1.injective (huq.trans he.symm)
        exact hut ▸ hu
      by_cases h0 : d.bStart = 0
      · have htc : t ≤ finalFan.center guideIndex := by
          simpa [h0,←hGuideCenterEq] using htsecond.2
        have hh : finalFan.chart (b t).val ∈ segment ℝ
            (incidentPorts f (d.first 1) finalFan.chart finalFan.left finalFan.right (guideIndex,false)) 0 :=
          hGuideLeftHalf ▸ mem_image_of_mem _ ⟨ht.1,htc⟩
        rw [he,hFinalChartPullbackCoord] at hh
        simpa only [incomingPort,h0,ite_true,segment_symm ℝ (0 : Plane)] using hh
      · have h1 := hbstartEndpoint.resolve_left h0
        have hct : finalFan.center guideIndex ≤ t := by
          rw [h1,min_eq_right (show d.bFinish ≤ 1 from le_top),←hGuideCenterEq] at htsecond
          exact htsecond.1
        have hh : finalFan.chart (b t).val ∈ segment ℝ 0
            (incidentPorts f (d.first 1) finalFan.chart finalFan.left finalFan.right (guideIndex,true)) :=
          hGuideRightHalf ▸ mem_image_of_mem _ ⟨hct,ht.2⟩
        rw [he,hFinalChartPullbackCoord] at hh
        simpa only [incomingPort,h0,ite_false] using hh
    · intro hz
      by_cases h0 : d.bStart = 0
      · have hh : z.val ∈ (fun u => finalFan.chart (b u).val) ''
            Icc (finalFan.left guideIndex) (finalFan.center guideIndex) := by
          rw [hGuideLeftHalf,segment_symm]
          simpa only [incomingPort,h0,ite_true] using hz
        obtain ⟨t,ht,he⟩ := hh
        have htcuts := Icc_subset_Icc le_rfl (finalFan.cuts guideIndex).2.2.1.le ht
        have heq : b t = finalChartPullback z := Subtype.ext
          (finalFan.chart.injOn (hGuideFanSource t htcuts) (hFinalChartPullbackSource z)
            (he.trans (hFinalChartPullbackCoord z).symm))
        rw [hsecondRange]
        refine ⟨t,?_,heq⟩
        simpa [h0,←hGuideCenterEq] using And.intro (bot_le : (0 : Interval) ≤ t) ht.2
      · have h1 := hbstartEndpoint.resolve_left h0
        have hh : z.val ∈ (fun u => finalFan.chart (b u).val) ''
            Icc (finalFan.center guideIndex) (finalFan.right guideIndex) := by
          rw [hGuideRightHalf]
          simpa only [incomingPort,h0,ite_false] using hz
        obtain ⟨t,ht,he⟩ := hh
        have htcuts := Icc_subset_Icc (finalFan.cuts guideIndex).2.1.le le_rfl ht
        have heq : b t = finalChartPullback z := Subtype.ext
          (finalFan.chart.injOn (hGuideFanSource t htcuts) (hFinalChartPullbackSource z)
            (he.trans (hFinalChartPullbackCoord z).symm))
        rw [hsecondRange]
        refine ⟨t,?_,heq⟩
        rw [h1,min_eq_right (show d.bFinish ≤ 1 from le_top),max_eq_left (show d.bFinish ≤ 1 from le_top),←hGuideCenterEq]
        exact ⟨ht.1,le_top⟩
  have hFinalFirstRay : ∀ z : Metric.closedBall (0 : Plane) 1,
      finalChartPullback z ∈ range d.first ↔ z.val 1 = 0 ∧ 0 ≤ z.val 0 := by
    intro z
    have hAxis (hz : z.val 1 = 0) :
        finalChartPullback z ∈ range d.first ↔ 0 ≤ z.val 0 := by
      have he : z.val = Plane.mk (z.val 0) 0 := by ext i; fin_cases i <;> simp [hz]
      have hn : |z.val 0| ≤ 1 := by
        have hh := z.property
        rw [Metric.mem_closedBall,dist_zero_right,he,hHorizontalNorm] at hh
        exact hh
      let u : Icc (-1 : ℝ) 1 := ⟨z.val 0,abs_le.mp hn⟩
      have hu : axisPoint u = z := Subtype.ext he.symm
      simpa only [hu] using hAxisFirstCriterion u
    constructor
    · intro hz
      have ha : finalChartPullback z ∈ range a := by
        rw [hfirstRange] at hz
        exact hClockRange ▸ image_subset_range _ _ hz
      have hzero := (hFinalChartOldAxis z).mp ha
      exact ⟨hzero,(hAxis hzero).mp hz⟩
    · rintro ⟨hzero,hpos⟩
      exact (hAxis hzero).mpr hpos
  have hFinalEntryPullback : finalChartPullback ⟨finalEntry,Metric.ball_subset_closedBall hFinalEntryOpen⟩ =
      d.second finalEntryTime := by
    apply Subtype.ext
    exact finalFan.chart.left_inv hFinalEntrySource.1
  have hEntryIncomingRay : finalEntry ∈ segment ℝ (0 : Plane) incomingPort := by
    apply (hFinalSecondRay ⟨finalEntry,Metric.ball_subset_closedBall hFinalEntryOpen⟩).mp
    rw [hFinalEntryPullback]
    exact mem_range_self _
  obtain ⟨entryCoefficient,hEntryCoefficient,hEntryCoefficientEq⟩ :=
    (by simpa only [segment_eq_image',zero_add,sub_zero,mem_image] using hEntryIncomingRay :
      ∃ c ∈ Icc (0 : ℝ) 1, c • incomingPort = finalEntry)
  have hEntryScale : finalEntry = entryCoefficient • incomingPort := hEntryCoefficientEq.symm
  have hEntryCoefficientPos : 0 < entryCoefficient := by
    apply lt_of_le_of_ne hEntryCoefficient.1
    intro he
    apply hFinalEntryHeight
    rw [hEntryScale,←he,zero_smul]
    rfl
  have hIncomingPortHeight : incomingPort 1 ≠ 0 := by
    intro he
    apply hFinalEntryHeight
    rw [hEntryScale]
    change entryCoefficient * incomingPort 1 = 0
    rw [he,mul_zero]
  have hIncomingRayEquation : ∀ z ∈ Metric.closedBall (0 : Plane) 1,
      z ∈ segment ℝ (0 : Plane) incomingPort ↔
        z 0-(finalEntry 0/finalEntry 1)*z 1 = 0 ∧ 0 ≤ z 1/finalEntry 1 := by
    intro z hz
    constructor
    · intro hseg
      obtain ⟨c,hc,rfl⟩ :=
        (by simpa only [segment_eq_image',zero_add,sub_zero,mem_image] using hseg :
          ∃ c ∈ Icc (0 : ℝ) 1, c • incomingPort = z)
      have hratio : (c • incomingPort) 1/finalEntry 1 = c/entryCoefficient := by
        rw [hEntryScale]
        change (c*incomingPort 1)/(entryCoefficient*incomingPort 1) = c/entryCoefficient
        field_simp [hEntryCoefficientPos.ne',hIncomingPortHeight]
      refine ⟨?_,hratio ▸ div_nonneg hc.1 hEntryCoefficientPos.le⟩
      rw [hEntryScale]
      change c*incomingPort 0-(entryCoefficient*incomingPort 0/(entryCoefficient*incomingPort 1))*(c*incomingPort 1)=0
      field_simp [hEntryCoefficientPos.ne',hIncomingPortHeight]
      <;> ring
    · rintro ⟨hell,htheta⟩
      have he : z = (z 1/finalEntry 1) • finalEntry := by
        ext i
        fin_cases i
        · change z 0 = (z 1/finalEntry 1)*finalEntry 0
          calc z 0 = (finalEntry 0/finalEntry 1)*z 1 := sub_eq_zero.mp hell
               _ = (z 1/finalEntry 1)*finalEntry 0 := by ring
        · exact (div_mul_cancel₀ (z 1) hFinalEntryHeight).symm
      have he' : z = ((z 1/finalEntry 1)*entryCoefficient) • incomingPort :=
        he.trans ((congrArg (fun p : Plane => (z 1/finalEntry 1) • p) hEntryScale).trans
          (smul_smul _ _ _))
      have hc : 0 ≤ (z 1/finalEntry 1)*entryCoefficient := mul_nonneg htheta hEntryCoefficientPos.le
      have hc1 : (z 1/finalEntry 1)*entryCoefficient ≤ 1 := by
        have hn : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
        rw [he',norm_smul,Real.norm_eq_abs,hIncomingPortNorm,mul_one,abs_of_nonneg hc] at hn
        exact hn
      rw [segment_eq_image']
      exact ⟨(z 1/finalEntry 1)*entryCoefficient,⟨hc,hc1⟩,by simpa only [zero_add,sub_zero] using he'.symm⟩
  have hFinalFrontier : ∀ z ∈ Metric.ball (0 : Plane) 1,
      finalFan.chart.symm z ∈ frontier (range ambientDisk) ↔
        (z 1 = 0 ∧ 0 ≤ z 0) ∨
        (z 0-(finalEntry 0/finalEntry 1)*z 1 = 0 ∧ 0 ≤ z 1/finalEntry 1) := by
    intro z hz
    let zz : Metric.closedBall (0 : Plane) 1 := ⟨z,Metric.ball_subset_closedBall hz⟩
    have hImage (T : Set ↥F) : finalFan.chart.symm z ∈ Subtype.val '' T ↔ finalChartPullback zz ∈ T := by
      constructor
      · rintro ⟨y,hy,he⟩
        exact (Subtype.ext he : y = finalChartPullback zz) ▸ hy
      · intro hy
        exact ⟨finalChartPullback zz,hy,rfl⟩
    rw [hFinalFrontierTwoSides z hz,mem_union,hImage,hImage,
      hFinalFirstRay zz,hFinalSecondRay zz,hIncomingRayEquation z zz.property]
  let matchedOldSign : ℝ := if 0 < finalEntry 1 then 1 else -1
  have hMatchedOldSignUnit : matchedOldSign = -1 ∨ matchedOldSign = 1 := by
    by_cases hp : 0 < finalEntry 1 <;> simp [matchedOldSign,hp]
  have hMatchedOldSign : 0 < matchedOldSign * finalEntry 1 := by
    by_cases hp : 0 < finalEntry 1
    · simpa [matchedOldSign,hp] using hp
    · have hn : finalEntry 1 < 0 := lt_of_le_of_ne (le_of_not_gt hp) hFinalEntryHeight
      simpa [matchedOldSign,hp] using neg_pos.mpr hn
  let oldWidthSign : ℝ := matchedOldSign * finalSign
  have hOldWidthSignUnit : oldWidthSign = -1 ∨ oldWidthSign = 1 := by
    rcases hMatchedOldSignUnit with he | he <;> rcases hFinalSignUnit with hf | hf <;>
      simp [oldWidthSign,he,hf]
  have hFinalOldSignFactor : finalSign * oldWidthSign = matchedOldSign := by
    rcases hFinalSignUnit with hf | hf <;> simp [oldWidthSign,hf]
  let oldWidthClock : Icc (-1 : ℝ) 1 ≃ₜ Icc (-1 : ℝ) 1 := {
    toFun := fun u => ⟨oldWidthSign*u.val,by
      rcases hOldWidthSignUnit with he | he <;> rw [he]
      · constructor <;> nlinarith only [u.property.1,u.property.2]
      · simpa using u.property⟩
    invFun := fun u => ⟨oldWidthSign*u.val,by
      rcases hOldWidthSignUnit with he | he <;> rw [he]
      · constructor <;> nlinarith only [u.property.1,u.property.2]
      · simpa using u.property⟩
    left_inv := by
      intro u
      apply Subtype.ext
      rcases hOldWidthSignUnit with he | he <;> simp [he]
    right_inv := by
      intro u
      apply Subtype.ext
      rcases hOldWidthSignUnit with he | he <;> simp [he]
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hOldWidthClockAbs : ∀ u, |(oldWidthClock u).val| = |u.val| := by
    intro u
    change |oldWidthSign*u.val| = |u.val|
    rcases hOldWidthSignUnit with he | he <;> simp [he]
  have hOldWidthClockZero : oldWidthClock ⟨0,by norm_num⟩ = ⟨0,by norm_num⟩ := by
    apply Subtype.ext
    simp [oldWidthClock]
  let matchedOldStrip : C(Interval × Icc (-1 : ℝ) 1,↥F) :=
    calibratedOldStrip.comp ⟨(Homeomorph.refl Interval).prodCongr oldWidthClock,
      ((Homeomorph.refl Interval).prodCongr oldWidthClock).continuous⟩
  have hMatchedOld : IsEmbedding matchedOldStrip :=
    hCalibratedOld.comp ((Homeomorph.refl Interval).prodCongr oldWidthClock).isEmbedding
  have hMatchedOldCenter : ∀ t, matchedOldStrip (t,⟨0,by norm_num⟩) = a t := by
    intro t
    change calibratedOldStrip (t,oldWidthClock ⟨0,by norm_num⟩) = a t
    rw [hOldWidthClockZero,hCalibratedOldCenter]
  have hMatchedOldActive : ∀ t ∈ activeWindow, ∀ u, matchedOldStrip (t,u) ∈ V :=
    fun t ht u => hCalibratedOldActive t ht (oldWidthClock u)
  have hMatchedOldEnds : ∀ u, (matchedOldStrip (0,u)).val ∈ boundaryCircle ∧
      (matchedOldStrip (1,u)).val ∈ boundaryCircle :=
    fun u => hCalibratedOldEnds (oldWidthClock u)
  have hMatchedOldInterior : ∀ t ∈ Ioo (0 : Interval) 1, ∀ u,
      (matchedOldStrip (t,u)).val ∈ interior F :=
    fun t ht u => hCalibratedOldInterior t ht (oldWidthClock u)
  have hMatchedOldOpen : IsOpen (matchedOldStrip ''
      {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
    convert hCalibratedOldOpen using 1
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨(z.1,oldWidthClock z.2),?_,rfl⟩
      exact abs_lt.mp ((hOldWidthClockAbs z.2).symm ▸ abs_lt.mpr hz)
    · rintro ⟨z,hz,rfl⟩
      refine ⟨(z.1,oldWidthClock.symm z.2),?_,?_⟩
      · have ha := hOldWidthClockAbs (oldWidthClock.symm z.2)
        rw [oldWidthClock.apply_symm_apply] at ha
        exact abs_lt.mp (ha ▸ abs_lt.mpr hz)
      · change calibratedOldStrip (z.1,oldWidthClock (oldWidthClock.symm z.2)) = calibratedOldStrip z
        rw [oldWidthClock.apply_symm_apply]
  have hMatchedOldCoordinates : ∀ t ∈ Icc coordinateLeft coordinateRight, ∀ u,
      (matchedOldStrip (clock t,u)).val ∈ finalFan.chart.source ∧
      finalFan.chart (matchedOldStrip (clock t,u)).val =
        Plane.mk (finalX t) (matchedOldSign*calibrationScale*u.val) := by
    intro t ht u
    have hc := hFinalCoordinates t ht (oldWidthClock u)
    refine ⟨hc.1,?_⟩
    change finalFan.chart (calibratedOldStrip (clock t,oldWidthClock u)).val = _
    rw [hc.2]
    congr 1
    change finalSign*calibrationScale*(oldWidthSign*u.val) = matchedOldSign*calibrationScale*u.val
    calc finalSign*calibrationScale*(oldWidthSign*u.val) =
          (finalSign*oldWidthSign)*calibrationScale*u.val := by ring
         _ = matchedOldSign*calibrationScale*u.val := by rw [hFinalOldSignFactor]
  have hMatchedOldUnit : ∀ t ∈ Icc coordinateLeft coordinateRight, ∀ u,
      matchedOldStrip (clock t,u) ∈ chartPull F finalFan.chart (Metric.ball (0 : Plane) 1) :=
    fun t ht u => hFinalUnit t ht (oldWidthClock u)
  have hOppositeRayHeight (p q : Plane) (hpq : p 1*q 1 < 0)
      (z : Plane) (hz : z ∈ segment ℝ (0 : Plane) q) : z 1*p 1 ≤ 0 := by
    rw [segment_eq_image'] at hz
    obtain ⟨c,hc,rfl⟩ := hz
    change (0+c*(q 1-0))*p 1 ≤ 0
    have hm := mul_nonpos_of_nonneg_of_nonpos hc.1 hpq.le
    nlinarith only [hm]
  have hPositiveGuideRay : ∀ y ∈ range b,
      y ∈ chartPull F finalFan.chart (Metric.ball (0 : Plane) 1) →
      0 < finalFan.chart y.val 1 * incomingPort 1 →
      finalFan.chart y.val ∈ segment ℝ (0 : Plane) incomingPort := by
    intro y hy hsource hpos
    have hr := (hFanTrace (d.first 1) finalFan guideIndex y hsource.1
      (Metric.ball_subset_closedBall hsource.2)).mp hy
    have hsign := hFinalPortSigns guideIndex (by simpa [guideIndex] using Ne.symm hvw)
    by_cases h0 : d.bStart = 0
    · simp only [incomingPort,h0,ite_true] at hpos ⊢
      rcases hr with hh | hh
      · rwa [segment_symm]
      · exact False.elim ((not_lt_of_ge (hOppositeRayHeight _ _ hsign _ hh)) hpos)
    · simp only [incomingPort,h0,ite_false] at hpos ⊢
      rcases hr with hh | hh
      · rw [segment_symm] at hh
        have hrev : incidentPorts f (d.first 1) finalFan.chart finalFan.left finalFan.right (guideIndex,true) 1 *
            incidentPorts f (d.first 1) finalFan.chart finalFan.left finalFan.right (guideIndex,false) 1 < 0 :=
          by rw [mul_comm]; exact hsign
        exact False.elim ((not_lt_of_ge (hOppositeRayHeight _ _ hrev _ hh)) hpos)
      · exact hh
  let guideCoordinates : Plane ≃ₜ Plane := {
    toFun := fun z => Plane.mk (z 1-finalEntry 1) (z 0-(finalEntry 0/finalEntry 1)*z 1)
    invFun := fun z => Plane.mk (z 1+(finalEntry 0/finalEntry 1)*(z 0+finalEntry 1))
      (z 0+finalEntry 1)
    left_inv := by
      intro z
      ext i
      fin_cases i
      · change z 0-(finalEntry 0/finalEntry 1)*z 1+
          (finalEntry 0/finalEntry 1)*(z 1-finalEntry 1+finalEntry 1)=z 0
        ring
      · change z 1-finalEntry 1+finalEntry 1=z 1
        ring
    right_inv := by
      intro z
      ext i
      fin_cases i
      · change z 0+finalEntry 1-finalEntry 1=z 0
        ring
      · change z 1+(finalEntry 0/finalEntry 1)*(z 0+finalEntry 1)-
          (finalEntry 0/finalEntry 1)*(z 0+finalEntry 1)=z 1
        ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let guideAxisDomain : Set S := finalFan.chart.source ∩ finalFan.chart ⁻¹'
    (Metric.ball (0 : Plane) 1 ∩ {z | 0 < z 1*incomingPort 1})
  have hGuideAxisDomain : IsOpen guideAxisDomain :=
    finalFan.chart.isOpen_inter_preimage (Metric.isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop)))
  let guideAxisChart := (finalFan.chart.restr guideAxisDomain).transHomeomorph guideCoordinates
  have hGuideAxisSource : guideAxisChart.source = finalFan.chart.source ∩ guideAxisDomain :=
    finalFan.chart.restr_source' guideAxisDomain hGuideAxisDomain
  have hGuideAxis : ∀ t, (b t).val ∈ guideAxisChart.source → guideAxisChart (b t).val 1 = 0 := by
    intro t ht
    rw [hGuideAxisSource] at ht
    have hr := hPositiveGuideRay (b t) (mem_range_self t) ⟨ht.1,ht.2.2.1⟩ ht.2.2.2
    exact ((hIncomingRayEquation _ (Metric.ball_subset_closedBall ht.2.2.1)).mp hr).1
  let rawEntry : Interval := CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish finalEntryTime
  have hRawEntryEq : b rawEntry = d.second finalEntryTime := (d.second_eq finalEntryTime).symm
  have hRawEntryInterior : rawEntry ∈ Ioo (0 : Interval) 1 := by
    have hi : (b rawEntry).val ∈ interior F := by
      rw [hRawEntryEq]
      exact hFinalSourceInterior hFinalEntrySource.1
    constructor
    · apply bot_lt_iff_ne_bot.mpr
      intro he
      rw [he] at hi
      exact disjoint_left.mp disjoint_interior_frontier hi (hBF (r w).val.property.2.1)
    · apply lt_top_iff_ne_top.mpr
      intro he
      rw [he] at hi
      exact disjoint_left.mp disjoint_interior_frontier hi (hBF (r w).val.property.2.2.1)
  have hEntryPortPositive : 0 < finalEntry 1 * incomingPort 1 := by
    rw [hEntryScale]
    change (entryCoefficient*incomingPort 1)*incomingPort 1 > 0
    have hh := mul_pos hEntryCoefficientPos (sq_pos_of_ne_zero hIncomingPortHeight)
    nlinarith only [hh]
  have hGuideEntrySource : (b rawEntry).val ∈ guideAxisChart.source := by
    rw [hGuideAxisSource,hRawEntryEq]
    exact ⟨hFinalEntrySource.1,hFinalEntrySource.1,hFinalEntryOpen,hEntryPortPositive⟩
  have hGuideEntryZero : guideAxisChart (b rawEntry).val = 0 := by
    change guideCoordinates (finalFan.chart (b rawEntry).val) = 0
    rw [hRawEntryEq]
    change guideCoordinates finalEntry = 0
    ext i
    fin_cases i
    · change finalEntry 1-finalEntry 1=0
      ring
    · change finalEntry 0-(finalEntry 0/finalEntry 1)*finalEntry 1=0
      rw [div_mul_cancel₀ _ hFinalEntryHeight,sub_self]
  have hGuideEntrySupport : (b rawEntry).val ∈ calibrationSupport := by
    rw [hRawEntryEq]
    refine ⟨hFinalSourceInterior hFinalEntrySource.1,?_⟩
    change d.second finalEntryTime ∈ Subtype.val ⁻¹' ambientV
    rw [hAmbientVeq]
    exact hsecondV (mem_range_self _)
  let ambientGuide : C(Interval,S) := ⟨fun t => (b t).val,b.continuous.subtype_val⟩
  let ambientGuideStrip : Interval × Icc (-1 : ℝ) 1 → S := fun z => (signedGuideStrip z).val
  have hAmbientGuideCenter : IsEmbedding ambientGuide := IsEmbedding.subtypeVal.comp (r w).val.property.1
  have hAmbientGuideStrip : IsEmbedding ambientGuideStrip := IsEmbedding.subtypeVal.comp hSignedGuide
  obtain ⟨guideFactor,hGuideFactor,guideCalibrationSign,guideCalibrationScale,guideCalibrationRadius,
      guideCalibrationMap,hGuideCalibrationSign,hGuideCalibrationScale,hGuideCalibrationRadius,
      hGuideCalibrationCenter,hGuideCalibrationFixed,hGuideCalibrationCoords⟩ :=
    source_internal_collar_calibration ambientGuide hAmbientGuideCenter ambientGuideStrip
      hAmbientGuideStrip (fun t => congrArg Subtype.val (hSignedGuideCenter t))
      rawEntry hRawEntryInterior guideAxisChart hGuideEntrySource hGuideEntryZero
      hGuideAxis univ calibrationSupport isOpen_univ hCalibrationSupport (subset_univ _)
      hGuideEntrySupport (subset_univ _)
  have hGuideCalibrationPreserves (A : Set S) (hA : calibrationSupport ⊆ A) :
      ∀ y, y ∈ A ↔ guideCalibrationMap y ∈ A := by
    intro y
    constructor
    · intro hy
      by_contra hny
      have hfixed := hGuideCalibrationFixed (guideCalibrationMap y) (fun h => hny (hA h))
      have he : guideCalibrationMap y = y := guideCalibrationMap.injective hfixed
      exact hny (he.symm ▸ hy)
    · intro hy
      by_contra hny
      have hfixed := hGuideCalibrationFixed y (fun h => hny (hA h))
      exact hny (hfixed ▸ hy)
  have hGuideCalibrationF : ∀ y, y ∈ F ↔ guideCalibrationMap y ∈ F :=
    hGuideCalibrationPreserves F (fun _ h => interior_subset h.1)
  have hGuideCalibrationInterior : ∀ y, y ∈ interior F ↔ guideCalibrationMap y ∈ interior F :=
    hGuideCalibrationPreserves (interior F) inter_subset_left
  have hGuideCalibrationV : ∀ y, y ∈ ambientV ↔ guideCalibrationMap y ∈ ambientV :=
    hGuideCalibrationPreserves ambientV inter_subset_right
  let relativeGuideCalibration : ↥F ≃ₜ ↥F := guideCalibrationMap.subtype hGuideCalibrationF
  have hGuideCalibrationBoundary : ∀ y : ↥F, y.val ∈ boundaryCircle → relativeGuideCalibration y = y := by
    intro y hy
    apply Subtype.ext
    apply hGuideCalibrationFixed
    intro hySupport
    exact disjoint_left.mp disjoint_interior_frontier hySupport.1 (hBF hy)
  let guideWidthMap : C(Interval × Icc (-1 : ℝ) 1,Interval × Icc (-1 : ℝ) 1) :=
    ⟨fun z => (z.1,⟨guideFactor*z.2.val,by
      constructor <;> nlinarith [z.2.property.1,z.2.property.2,hGuideFactor.1,hGuideFactor.2]⟩),
      by fun_prop⟩
  have hGuideWidthMap : IsEmbedding guideWidthMap := by
    apply (guideWidthMap.continuous.isClosedEmbedding _).isEmbedding
    intro z y he
    apply Prod.ext
    · change (guideWidthMap z).1 = (guideWidthMap y).1
      exact congrArg Prod.fst he
    · apply Subtype.ext
      have hc := congrArg (fun q : Interval × Icc (-1 : ℝ) 1 => q.2.val) he
      exact (mul_left_cancel₀ hGuideFactor.1.ne') hc
  let calibratedGuideStrip : C(Interval × Icc (-1 : ℝ) 1,↥F) :=
    (⟨relativeGuideCalibration,relativeGuideCalibration.continuous⟩ : C(↥F,↥F)).comp
      (signedGuideStrip.comp guideWidthMap)
  have hCalibratedGuide : IsEmbedding calibratedGuideStrip :=
    relativeGuideCalibration.isEmbedding.comp (hSignedGuide.comp hGuideWidthMap)
  have hCalibratedGuideCenter : ∀ t,
      calibratedGuideStrip (t,⟨0,by norm_num⟩) = b t := by
    intro t
    have hz : guideWidthMap (t,⟨0,by norm_num⟩) = (t,⟨0,by norm_num⟩) := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext; change guideFactor*0 = 0; ring
    change relativeGuideCalibration (signedGuideStrip (guideWidthMap (t,⟨0,by norm_num⟩))) = b t
    rw [hz,hSignedGuideCenter]
    exact Subtype.ext (hGuideCalibrationCenter t)
  have hCalibratedGuideEnds : ∀ u,
      (calibratedGuideStrip (0,u)).val ∈ boundaryCircle ∧
      (calibratedGuideStrip (1,u)).val ∈ boundaryCircle := by
    intro u
    have h0 := (hSignedGuideEnds (guideWidthMap (0,u)).2).1
    have h1 := (hSignedGuideEnds (guideWidthMap (1,u)).2).2
    change (relativeGuideCalibration (signedGuideStrip (0,(guideWidthMap (0,u)).2))).val ∈ boundaryCircle ∧
      (relativeGuideCalibration (signedGuideStrip (1,(guideWidthMap (1,u)).2))).val ∈ boundaryCircle
    rw [hGuideCalibrationBoundary _ h0,hGuideCalibrationBoundary _ h1]
    exact ⟨h0,h1⟩
  have hCalibratedGuideInterior : ∀ t ∈ Ioo (0 : Interval) 1, ∀ u,
      (calibratedGuideStrip (t,u)).val ∈ interior F := by
    intro t ht u
    exact (hGuideCalibrationInterior _).mp (hSignedGuideInterior t ht (guideWidthMap (t,u)).2)
  have hCalibratedGuideActive : ∀ t ∈ guideWindow, ∀ u,
      calibratedGuideStrip (t,u) ∈ V := by
    intro t ht u
    rw [← hAmbientVeq]
    apply (hGuideCalibrationV _).mp
    have hv := hSignedGuideActive t ht (guideWidthMap (t,u)).2
    rw [← hAmbientVeq] at hv
    exact hv
  let guideNarrowCore : Set (Interval × Icc (-1 : ℝ) 1) :=
    {z | -guideFactor < z.2.val ∧ z.2.val < guideFactor}
  have hGuideNarrowCore : IsOpen guideNarrowCore :=
    (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
  have hGuideNarrowCoreSub : guideNarrowCore ⊆ {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
    intro z hz
    exact ⟨lt_of_le_of_lt (neg_le_neg hGuideFactor.2) hz.1,hz.2.trans_le hGuideFactor.2⟩
  obtain ⟨guideNarrowOpen,hGuideNarrowOpen,hGuideNarrowImage⟩ :=
    hSignedGuide.isInducing.image_eq_isOpen_inter_range hGuideNarrowCore
  have hGuideNarrowOpenImage : IsOpen (signedGuideStrip '' guideNarrowCore) := by
    have he : signedGuideStrip '' guideNarrowCore = guideNarrowOpen ∩
        signedGuideStrip '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
      apply Subset.antisymm
      · intro y hy
        exact ⟨(hGuideNarrowImage ▸ hy).1,image_mono hGuideNarrowCoreSub hy⟩
      · rintro y ⟨hyO,hyCore⟩
        rw [hGuideNarrowImage]
        exact ⟨hyO,image_subset_range signedGuideStrip _ hyCore⟩
    rw [he]
    exact hGuideNarrowOpen.inter hSignedGuideOpen
  have hGuideWidthCore : guideWidthMap '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} = guideNarrowCore := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      change -guideFactor < guideFactor*y.2.val ∧ guideFactor*y.2.val < guideFactor
      constructor <;> nlinarith [hGuideFactor.1,hy.1,hy.2]
    · intro hz
      have hu : -1 < z.2.val/guideFactor ∧ z.2.val/guideFactor < 1 := by
        constructor
        · apply (lt_div_iff₀ hGuideFactor.1).mpr
          simpa using hz.1
        · exact (div_lt_one hGuideFactor.1).mpr hz.2
      refine ⟨(z.1,⟨z.2.val/guideFactor,⟨hu.1.le,hu.2.le⟩⟩),hu,?_⟩
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact mul_div_cancel₀ z.2.val hGuideFactor.1.ne'
  have hCalibratedGuideOpen : IsOpen (calibratedGuideStrip ''
      {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
    have he : calibratedGuideStrip '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} =
        relativeGuideCalibration '' (signedGuideStrip '' guideNarrowCore) := by
      rw [← hGuideWidthCore,image_image,image_image]
      rfl
    rw [he]
    exact relativeGuideCalibration.isOpenMap _ hGuideNarrowOpenImage
  have hCalibratedGuideCoordinates : ∀ t : Interval, ∀ u : Icc (-1 : ℝ) 1,
      |t.val-rawEntry.val| < guideCalibrationRadius →
      (calibratedGuideStrip (t,u)).val ∈ finalFan.chart.source ∧
      finalFan.chart (calibratedGuideStrip (t,u)).val =
        Plane.mk (finalFan.chart (b t).val 0+guideCalibrationSign*guideCalibrationScale*u.val)
          (finalFan.chart (b t).val 1) := by
    intro t u ht
    have hc := hGuideCalibrationCoords t u ht
    have hc0 := (hGuideCalibrationCoords t ⟨0,by norm_num⟩ ht).1
    change (calibratedGuideStrip (t,⟨0,by norm_num⟩)).val ∈ guideAxisChart.source at hc0
    rw [hCalibratedGuideCenter] at hc0
    have hbaxis := hGuideAxis t hc0
    have hs := hc.1
    rw [hGuideAxisSource] at hs
    refine ⟨hs.1,?_⟩
    have hheight := congrArg (fun z : Plane => z 0) hc.2
    have hnormal := congrArg (fun z : Plane => z 1) hc.2
    change finalFan.chart (calibratedGuideStrip (t,u)).val 1-finalEntry 1 =
      finalFan.chart (b t).val 1-finalEntry 1 at hheight
    change finalFan.chart (calibratedGuideStrip (t,u)).val 0-
      (finalEntry 0/finalEntry 1)*finalFan.chart (calibratedGuideStrip (t,u)).val 1 =
      guideCalibrationSign*guideCalibrationScale*u.val at hnormal
    change finalFan.chart (b t).val 0-(finalEntry 0/finalEntry 1)*finalFan.chart (b t).val 1=0 at hbaxis
    have hh : finalFan.chart (calibratedGuideStrip (t,u)).val 1 = finalFan.chart (b t).val 1 :=
      by linarith only [hheight]
    ext i
    fin_cases i
    · change finalFan.chart (calibratedGuideStrip (t,u)).val 0 =
        finalFan.chart (b t).val 0+guideCalibrationSign*guideCalibrationScale*u.val
      rw [hh] at hnormal
      linarith only [hnormal,hbaxis]
    · exact hh
  have hCalibratedGuideUnit : ∀ t : Interval, ∀ u : Icc (-1 : ℝ) 1,
      |t.val-rawEntry.val| < guideCalibrationRadius →
      calibratedGuideStrip (t,u) ∈ chartPull F finalFan.chart (Metric.ball (0 : Plane) 1) := by
    intro t u ht
    have hs := (hGuideCalibrationCoords t u ht).1
    rw [hGuideAxisSource] at hs
    exact ⟨hs.1,hs.2.2.1⟩
  have hCalibratedGuideEntry : ∀ u : Icc (-1 : ℝ) 1,
      (calibratedGuideStrip (rawEntry,u)).val ∈ finalFan.chart.source ∧
      finalFan.chart (calibratedGuideStrip (rawEntry,u)).val =
        Plane.mk (finalEntry 0+guideCalibrationSign*guideCalibrationScale*u.val) (finalEntry 1) := by
    intro u
    have hc := hCalibratedGuideCoordinates rawEntry u (by simpa using hGuideCalibrationRadius)
    rwa [hRawEntryEq] at hc
  let calibratedBoundaryLine : C(Icc (-1 : ℝ) 1,↥F) :=
    ⟨fun u => calibratedGuideStrip (d.bStart,u),calibratedGuideStrip.continuous.comp
      (continuous_const.prodMk continuous_id)⟩
  have hCalibratedBoundary : IsEmbedding calibratedBoundaryLine :=
    hCalibratedGuide.comp ((continuous_const.prodMk continuous_id).isClosedEmbedding
      (by intro u v he; exact congrArg Prod.snd he)).isEmbedding
  have hCalibratedBoundaryZero : calibratedBoundaryLine ⟨0,by norm_num⟩ = d.second 0 :=
    (hCalibratedGuideCenter d.bStart).trans hsecond0.symm
  have hCalibratedBoundaryScale : ∀ u,
      calibratedBoundaryLine u = signedBoundaryLine (guideWidthMap (d.bStart,u)).2 := by
    intro u
    have hb : (signedGuideStrip (d.bStart,(guideWidthMap (d.bStart,u)).2)).val ∈ boundaryCircle := by
      rcases hbstartEndpoint with h0 | h1
      · rw [h0]; exact (hSignedGuideEnds _).1
      · rw [h1]; exact (hSignedGuideEnds _).2
    change relativeGuideCalibration (signedGuideStrip (d.bStart,(guideWidthMap (d.bStart,u)).2)) = _
    rw [hGuideCalibrationBoundary _ hb]
    rfl
  let calibratedBoundaryBound : ℝ := signedBound/2
  have hCalibratedBoundaryBound : 0 < calibratedBoundaryBound := half_pos hsignedBound
  have hCalibratedBoundaryBoundSmall : calibratedBoundaryBound < signedBound :=
    half_lt_self hsignedBound
  have hCalibratedBoundaryBoundOne : calibratedBoundaryBound < 1 :=
    hCalibratedBoundaryBoundSmall.trans hsignedBoundOne
  have hCalibratedBoundaryLocal : range calibratedBoundaryLine ⊆
      {y : ↥F | y.val ∈ boundaryCircle} ∩ V := by
    rintro y ⟨u,rfl⟩
    refine ⟨?_,hCalibratedGuideActive d.bStart (hGuideSelected ⟨min_le_left _ _,le_max_left _ _⟩) u⟩
    rcases hbstartEndpoint with h0 | h1
    · change (calibratedGuideStrip (d.bStart,u)).val ∈ boundaryCircle
      rw [h0]
      exact (hCalibratedGuideEnds u).1
    · change (calibratedGuideStrip (d.bStart,u)).val ∈ boundaryCircle
      rw [h1]
      exact (hCalibratedGuideEnds u).2
  have hCalibratedBoundaryOutside : ∀ u : Icc (-1 : ℝ) 1,
      0 < u.val → u.val < calibratedBoundaryBound →
      calibratedBoundaryLine u ∉ range d.boundarySide := by
    intro u hu0 hu
    rw [hCalibratedBoundaryScale]
    apply hSignedBetaOutside
    · exact mul_pos hGuideFactor.1 hu0
    · change guideFactor*u.val < signedBound
      have hm := mul_le_mul_of_nonneg_right hGuideFactor.2 hu0.le
      linarith only [hm,hu,hCalibratedBoundaryBoundSmall]
  have hCalibratedIncomingTerminal : ∀ β : ℝ, 0 < β → β < 1 →
      ∃ terminal : Interval, terminal < 1 ∧
        d.boundarySide '' Ioo terminal (1 : Interval) ⊆
          calibratedBoundaryLine '' {u | -β < u.val ∧ u.val < 0} := by
    intro β hβ hβone
    have hr : 0 < guideFactor*β := mul_pos hGuideFactor.1 hβ
    have hrone : guideFactor*β < 1 := by
      have hm := mul_le_mul_of_nonneg_right hGuideFactor.2 hβ.le
      linarith only [hm,hβone]
    have hn := ((hlineOpen (guideFactor*β) hr hrone.le).preimage boundaryPath.continuous).mem_nhds
      (show boundaryPath 1 ∈ {y : ↥({y : ↥F | y.val ∈ boundaryCircle}) |
        y.val ∈ boundaryLine '' {u | |u.val| < guideFactor*β}} from
        ⟨⟨0,by norm_num⟩,by simpa using hr,hBoundaryZero.trans d.boundary_one.symm⟩)
    obtain ⟨lower,hlower,hsub⟩ := nhds_top_basis.mem_iff.mp hn
    obtain ⟨terminal,htlower,htone⟩ := exists_between
      (show max lower terminalCut < (1 : Interval) from max_lt hlower hterminalCutOne)
    refine ⟨terminal,htone,?_⟩
    rintro y ⟨s,hs,rfl⟩
    obtain ⟨u,hu,he⟩ := hsub ((le_max_left _ _).trans_lt (htlower.trans hs.1))
    let uu : Icc (-1 : ℝ) 1 := widthClock.symm u
    have huuAbs : |uu.val| < guideFactor*β := by
      have ha := hwidthClockAbs (widthClock.symm u)
      rw [widthClock.apply_symm_apply] at ha
      exact ha ▸ hu
    have huuNeg : uu.val < 0 := by
      have hp := hincomingSignTail s
        ⟨(le_max_right _ _).trans_lt (htlower.trans hs.1),hs.2⟩ u he
      change -incomingSign*u.val < 0
      linarith only [hp]
    have hvAbs : |uu.val/guideFactor| < β := by
      rw [abs_div,abs_of_pos hGuideFactor.1]
      apply (div_lt_iff₀ hGuideFactor.1).mpr
      simpa only [mul_comm] using huuAbs
    let vv : Icc (-1 : ℝ) 1 := ⟨uu.val/guideFactor,by
      have hb := abs_lt.mp (hvAbs.trans hβone)
      exact ⟨hb.1.le,hb.2.le⟩⟩
    have hvv : -β < vv.val ∧ vv.val < 0 :=
      ⟨(abs_lt.mp hvAbs).1,div_neg_of_neg_of_pos huuNeg hGuideFactor.1⟩
    refine ⟨vv,hvv,?_⟩
    rw [hCalibratedBoundaryScale]
    have hscale : (guideWidthMap (d.bStart,vv)).2 = uu := by
      apply Subtype.ext
      exact mul_div_cancel₀ uu.val hGuideFactor.1.ne'
    rw [hscale]
    change boundaryLine (widthClock (widthClock.symm u)) = d.boundarySide s
    rwa [widthClock.apply_symm_apply]
  have hPrescribedSquare
      {S : Type} [TopologicalSpace S] [T2Space S]
      (q g : C(Interval, S)) (d : C(Metric.closedBall (0 : Plane) 1, S))
      (hq : IsEmbedding q) (hg : IsEmbedding g) (hd : IsEmbedding d)
      (hzero : q 0 = g 0) (hone : q 1 = g 1)
      (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
        range q ∪ range g)
      (hcollision : ∀ s t : Interval, q s = g t →
        (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
      ∃ P : C(Interval × Interval, S),
        IsEmbedding P ∧ range P = range d ∧
        (∀ t : Interval, P (t, 1) = q t) ∧
        range (fun t : Interval => P (t, 0)) ∪
          range (fun u : Interval => P (0, u)) ∪
          range (fun u : Interval => P (1, u)) = range g := by
    clear * - q g d hq hg hd hzero hone hboundary hcollision
    classical
    obtain ⟨a,b,ha,hb,hab0,hab1,habSphere,habMeet,haLift,hbLift⟩ :=
      RegionalEmbeddedFamily.clean_disk_boundary_pair_planar_lifts d hd q g hq hg
        hzero.symm hone.symm hcollision hboundary
    let top : C(Interval,Plane) :=
      ⟨fun t => Plane.mk (2*(t:ℝ)-1) 1, by fun_prop⟩
    have htinj : Function.Injective top := by
      intro s t he
      apply Subtype.ext
      have hh := congrArg (fun z : Plane => z 0) he
      change 2*(s:ℝ)-1=2*(t:ℝ)-1 at hh
      linarith
    have ht0 : top 0 = cornerNW := by ext i; fin_cases i <;> norm_num [top,Plane.mk,cornerNW]
    have ht1 : top 1 = cornerNE := by ext i; fin_cases i <;> norm_num [top,Plane.mk,cornerNE]
    have htRange : range top = sideTop := by
      ext z
      constructor
      · rintro ⟨t,rfl⟩
        apply mem_sideTop.mpr
        refine ⟨rfl,abs_le.mpr ⟨?_,?_⟩⟩
        · change -1 ≤ 2*(t:ℝ)-1; linarith [t.property.1]
        · change 2*(t:ℝ)-1 ≤ 1; linarith [t.property.2]
      · intro hz
        obtain ⟨hy,hx⟩ := mem_sideTop.mp hz
        have hx' := abs_le.mp hx
        refine ⟨⟨(z 0+1)/2,⟨by linarith,by linarith⟩⟩,?_⟩
        ext i
        fin_cases i
        · change 2*((z 0+1)/2)-1=z 0
          ring
        · exact hy.symm
    have hThree : IsArcBetween (sideLeft ∪ (sideBottom ∪ sideRight)) cornerNW cornerNE := by
      apply isArcBetween_sideLeft.concatenate isArcBetween_lowerSides
      rintro z hz (hb | hr)
      · have hx := (mem_sideLeft.mp hz).1
        have hy := (mem_sideBottom.mp hb).1
        ext i
        fin_cases i
        · simpa [cornerSW] using hx
        · simpa [cornerSW] using hy
      · have hx := (mem_sideLeft.mp hz).1
        have hx' := (mem_sideRight.mp hr).1
        linarith
    obtain ⟨k,hkc,hki,hkr,hk0,hk1⟩ := hThree
    let other : C(Interval,Plane) := ⟨fun t => k t,hkc.restrict⟩
    have hoinj : Function.Injective other := by
      intro s t he
      apply Subtype.ext
      exact hki s.property t.property he
    have hoRange : range other = sideLeft ∪ (sideBottom ∪ sideRight) := by
      rw [← hkr]
      ext z
      exact ⟨fun ⟨t,ht⟩ => ⟨t,t.property,ht⟩,fun ⟨t,ht,he⟩ => ⟨⟨t,ht⟩,he⟩⟩
    have hm0 : top 0 = other 0 := ht0.trans hk0.symm
    have hm1 : top 1 = other 1 := ht1.trans hk1.symm
    have hmMeet (s t : Interval) (he : top s = other t) :
        (s=0 ∧ t=0) ∨ (s=1 ∧ t=1) := by
      have hzTop : top s ∈ sideTop := htRange ▸ mem_range_self s
      have hzOther : top s ∈ sideLeft ∪ (sideBottom ∪ sideRight) :=
        he.symm ▸ (hoRange ▸ mem_range_self t)
      have hend : top s = cornerNW ∨ top s = cornerNE := by
        rcases hzOther with hl | hbot | hr
        · exact Or.inl (sideTop_meet_sideLeft _ hzTop hl)
        · have hh := (mem_sideTop.mp hzTop).1
          have hh' := (mem_sideBottom.mp hbot).1
          linarith
        · right
          have hx := (mem_sideRight.mp hr).1
          have hy := (mem_sideTop.mp hzTop).1
          ext i
          fin_cases i
          · simpa [cornerNE] using hx
          · simpa [cornerNE] using hy
      rcases hend with he0 | he1
      · exact Or.inl ⟨htinj (he0.trans ht0.symm),hoinj (he.symm.trans (he0.trans hk0.symm))⟩
      · exact Or.inr ⟨htinj (he1.trans ht1.symm),hoinj (he.symm.trans (he1.trans hk1.symm))⟩
    have hmCover : range top ∪ range other = modelCurve := by
      rw [htRange,hoRange,modelCurve_eq_sides]
      ext z
      simp only [mem_union]
      tauto
    let m : C(Interval ⊕ Interval, modelCurve) :=
      ⟨fun x => ⟨Sum.elim top other x, by
        cases x with
        | inl t => exact hmCover ▸ Or.inl (mem_range_self t)
        | inr t => exact hmCover ▸ Or.inr (mem_range_self t)⟩,
        by fun_prop⟩
    let n : C(Interval ⊕ Interval, Metric.sphere (0 : Plane) 1) :=
      ⟨fun x => ⟨Sum.elim a b x, by
        cases x with
        | inl t => exact habSphere ▸ Or.inl (mem_range_self t)
        | inr t => exact habSphere ▸ Or.inr (mem_range_self t)⟩,
        by fun_prop⟩
    have hms : Function.Surjective m := by
      intro z
      have hz : z.val ∈ range top ∪ range other := hmCover.symm ▸ z.property
      rcases hz with ⟨t,ht⟩ | ⟨t,ht⟩
      · exact ⟨Sum.inl t,Subtype.ext ht⟩
      · exact ⟨Sum.inr t,Subtype.ext ht⟩
    have hns : Function.Surjective n := by
      intro z
      have hz : z.val ∈ range a ∪ range b := habSphere.symm ▸ z.property
      rcases hz with ⟨t,ht⟩ | ⟨t,ht⟩
      · exact ⟨Sum.inl t,Subtype.ext ht⟩
      · exact ⟨Sum.inr t,Subtype.ext ht⟩
    have hkernel (x y : Interval ⊕ Interval) : m x = m y ↔ n x = n y := by
      simpa only [m,n,ContinuousMap.coe_mk,Subtype.mk.injEq] using
        ActualHarerDiskGluing.clean_pair_sum_kernel top other a b htinj hoinj ha.injective hb.injective
          hm0 hm1 hab0 hab1 hmMeet habMeet x y
    obtain ⟨f,hf,hfr,hfe⟩ := ActualHarerDiskGluing.compact_kernel_transport m n hms hkernel
    have : CompactSpace modelCurve := isCompact_iff_compactSpace.mp isCompact_modelCurve
    let e : modelCurve ≃ₜ Metric.sphere (0 : Plane) 1 :=
      f.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f
        ⟨hf.injective, by
          intro z
          obtain ⟨x,hx⟩ := hns z
          exact ⟨m x,(hfe x).trans hx⟩⟩)
    obtain ⟨F,hF⟩ := jordan_schoenflies_of_homeomorph isJordanCurve_modelCurve
      RegionalEmbeddedFamily.unit_sphere_isJordanCurve e
    have hFt (t : Interval) : F (top t) = a t :=
      (hF (m (Sum.inl t))).trans (congrArg Subtype.val (hfe (Sum.inl t)))
    have hFo (t : Interval) : F (other t) = b t :=
      (hF (m (Sum.inr t))).trans (congrArg Subtype.val (hfe (Sum.inr t)))
    have hFsphere : F '' modelCurve = Metric.sphere (0 : Plane) 1 := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        rw [hF ⟨x,hx⟩]
        exact (e ⟨x,hx⟩).property
      · intro hz
        refine ⟨e.symm ⟨z,hz⟩,(e.symm ⟨z,hz⟩).property,?_⟩
        rw [hF (e.symm ⟨z,hz⟩)]
        exact congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)
    have hFclosed : F '' Plane.closedSquare 0 1 = Metric.closedBall (0 : Plane) 1 := by
      rw [← LocalSurgery.actualModelSquareClosedRegion, image_union,hFsphere,
        CurveComplex.jordan_inside_homeomorph_image,hFsphere,
        RegionalEmbeddedFamily.inside_unit_sphere,union_comm,Metric.ball_union_sphere]
    let sq : C(Interval × Interval, Plane) :=
      ⟨fun z => Plane.mk (2*(z.1:ℝ)-1) (2*(z.2:ℝ)-1),by fun_prop⟩
    have hsqi : Function.Injective sq := by
      intro x y he
      apply Prod.ext <;> apply Subtype.ext
      · have hh := congrArg (fun z : Plane => z 0) he
        change 2*(x.1:ℝ)-1=2*(y.1:ℝ)-1 at hh
        linarith
      · have hh := congrArg (fun z : Plane => z 1) he
        change 2*(x.2:ℝ)-1=2*(y.2:ℝ)-1 at hh
        linarith
    have hsqr : range sq = Plane.closedSquare 0 1 := by
      ext z
      rw [Plane.closedSquare_eq_inter]
      simp only [mem_inter_iff,mem_setOf_eq]
      norm_num only [PiLp.zero_apply, WithLp.ofLp_zero, Pi.zero_apply, zero_sub,zero_add]
      constructor
      · rintro ⟨t,rfl⟩
        change (-1 ≤ 2*(t.1:ℝ)-1 ∧ 2*(t.1:ℝ)-1 ≤ 1) ∧
          (-1 ≤ 2*(t.2:ℝ)-1 ∧ 2*(t.2:ℝ)-1 ≤ 1)
        constructor <;> constructor <;> linarith [t.1.property.1,t.1.property.2,t.2.property.1,t.2.property.2]
      · rintro ⟨⟨hx0,hx1⟩,hy0,hy1⟩
        change -1 ≤ z 0 at hx0
        change z 0 ≤ 1 at hx1
        change -1 ≤ z 1 at hy0
        change z 1 ≤ 1 at hy1
        refine ⟨(⟨(z 0+1)/2,⟨by linarith,by linarith⟩⟩,
          ⟨(z 1+1)/2,⟨by linarith,by linarith⟩⟩),?_⟩
        ext i
        fin_cases i <;> dsimp [sq,Plane.mk] <;> ring
    let L : C(Interval × Interval,Metric.closedBall (0 : Plane) 1) :=
      ⟨fun x => ⟨F (sq x),hFclosed ▸ mem_image_of_mem F (hsqr ▸ mem_range_self x)⟩,
        (F.continuous.comp sq.continuous).subtype_mk _⟩
    have hLi : Function.Injective L := fun x y h => hsqi (F.injective (congrArg Subtype.val h))
    have hLs : Function.Surjective L := by
      intro z
      obtain ⟨x,hx,he⟩ : z.val ∈ F '' Plane.closedSquare 0 1 := hFclosed.symm ▸ z.property
      obtain ⟨t,rfl⟩ := hsqr.symm ▸ hx
      exact ⟨t,Subtype.ext he⟩
    let P := d.comp L
    have hPt (t : Interval) : P (t,1) = q t := by
      obtain ⟨z,hz,hdz⟩ := haLift t
      apply Eq.trans _ hdz
      apply congrArg d
      apply Subtype.ext
      change F (sq (t,1))=z.val
      have he : sq (t,1)=top t := by ext i; fin_cases i <;> norm_num [sq,top,Plane.mk]
      rw [he,hFt,hz]
    have hOtherPre :
        range (fun t : Interval => sq (t,0)) ∪
        range (fun u : Interval => sq (0,u)) ∪
        range (fun u : Interval => sq (1,u)) = range other := by
      rw [hoRange]
      have heH (y : ℝ) : range (fun t : Interval => Plane.mk (2*(t:ℝ)-1) y) =
          {z : Plane | z 1=y ∧ |z 0|≤1} := by
        ext z
        constructor
        · rintro ⟨t,rfl⟩
          refine ⟨rfl,abs_le.mpr ⟨?_,?_⟩⟩
          · change -1 ≤ 2*(t:ℝ)-1; linarith [t.property.1]
          · change 2*(t:ℝ)-1 ≤ 1; linarith [t.property.2]
        · rintro ⟨hy,hx⟩
          have hx' := abs_le.mp hx
          refine ⟨⟨(z 0+1)/2,⟨by linarith,by linarith⟩⟩,?_⟩
          ext i; fin_cases i
          · change 2*((z 0+1)/2)-1=z 0; ring
          · exact hy.symm
      have heV (x : ℝ) : range (fun u : Interval => Plane.mk x (2*(u:ℝ)-1)) =
          {z : Plane | z 0=x ∧ |z 1|≤1} := by
        ext z
        constructor
        · rintro ⟨t,rfl⟩
          refine ⟨rfl,abs_le.mpr ⟨?_,?_⟩⟩
          · change -1 ≤ 2*(t:ℝ)-1; linarith [t.property.1]
          · change 2*(t:ℝ)-1 ≤ 1; linarith [t.property.2]
        · rintro ⟨hx,hy⟩
          have hy' := abs_le.mp hy
          refine ⟨⟨(z 1+1)/2,⟨by linarith,by linarith⟩⟩,?_⟩
          ext i; fin_cases i
          · exact hx.symm
          · change 2*((z 1+1)/2)-1=z 1; ring
      have h0 : (0 : Interval).val=0 := rfl
      have h1 : (1 : Interval).val=1 := rfl
      simp only [sq,ContinuousMap.coe_mk,h0,h1,mul_zero,mul_one,zero_sub]
      norm_num only [show (2:ℝ)-1=1 by norm_num]
      rw [heH,heV,heV]
      ext z
      simp only [mem_union,mem_setOf_eq,mem_sideBottom,mem_sideLeft,mem_sideRight]
      tauto
    refine ⟨P,hd.comp (L.continuous.isClosedEmbedding hLi).isEmbedding,?_,hPt,?_⟩
    · change range (d ∘ L)=range d
      exact hLs.range_comp d
    · have hRangeF : F '' range other = range b := by
        rw [← range_comp]
        congr 1
        funext t
        exact hFo t
      have hRangeEdges :
          range (fun t : Interval => F (sq (t,0))) ∪
          range (fun u : Interval => F (sq (0,u))) ∪
          range (fun u : Interval => F (sq (1,u))) = range b := by
        change range (F ∘ (fun t : Interval => sq (t,0))) ∪
          range (F ∘ (fun u : Interval => sq (0,u))) ∪
          range (F ∘ (fun u : Interval => sq (1,u))) = range b
        rw [range_comp,range_comp,range_comp,← image_union,← image_union,hOtherPre,hRangeF]
      have hPfrom (z : Interval × Interval) (hm : F (sq z) ∈ range b) :
          P z ∈ range g := by
        obtain ⟨v,hv⟩ := hm
        obtain ⟨w,hw,he⟩ := hbLift v
        exact ⟨v,he.symm.trans (congrArg d (Subtype.ext (hw.trans hv)))⟩
      ext x
      constructor
      · rintro ((⟨t,rfl⟩ | ⟨u,rfl⟩) | ⟨u,rfl⟩)
        · apply hPfrom
          rw [← hRangeEdges]
          exact Or.inl (Or.inl (mem_range_self t))
        · apply hPfrom
          rw [← hRangeEdges]
          exact Or.inl (Or.inr (mem_range_self u))
        · apply hPfrom
          rw [← hRangeEdges]
          exact Or.inr (mem_range_self u)
      · rintro ⟨v,rfl⟩
        have hm : b v ∈ range (fun t : Interval => F (sq (t,0))) ∪
            range (fun u : Interval => F (sq (0,u))) ∪
            range (fun u : Interval => F (sq (1,u))) := hRangeEdges.symm ▸ mem_range_self v
        obtain ⟨z,hz,he⟩ := hbLift v
        rcases hm with (⟨t,ht⟩ | ⟨u,hu⟩) | ⟨u,hu⟩
        · exact Or.inl (Or.inl ⟨t,(congrArg d (Subtype.ext (ht.trans hz.symm))).trans he⟩)
        · exact Or.inl (Or.inr ⟨u,(congrArg d (Subtype.ext (hu.trans hz.symm))).trans he⟩)
        · exact Or.inr ⟨u,(congrArg d (Subtype.ext (hu.trans hz.symm))).trans he⟩
  obtain ⟨guideSquareTop,hGuideSquareTop,hGuideSquareRange,hGuideSquareEdge,hGuideOtherEdges⟩ :=
    hPrescribedSquare
      d.second guideComplementPath.toContinuousMap d.disk d.second_embedded hGuideComplement
      d.disk_embedded guideComplementPath.source.symm
      (d.corner_eq.symm.trans guideComplementPath.target.symm)
      hGuideDiskBoundary hGuideComplementCollision
  let squareFlip := (Homeomorph.refl Interval).prodCongr unitInterval.symmHomeomorph
  let guideSquare : C(Interval × Interval,↥F) :=
    guideSquareTop.comp ⟨squareFlip,squareFlip.continuous⟩
  have hGuideSquare : IsEmbedding guideSquare := hGuideSquareTop.comp squareFlip.isEmbedding
  have hGuideSquareRangeExact : range guideSquare = range d.disk := by
    change range (guideSquareTop ∘ squareFlip) = range d.disk
    rw [squareFlip.surjective.range_comp,hGuideSquareRange]
  have hGuideSquareBottom : ∀ t, guideSquare (t,0) = d.second t := by
    intro t
    change guideSquareTop (t,unitInterval.symmHomeomorph 0) = d.second t
    simpa using hGuideSquareEdge t
  obtain ⟨oldSquareTop,hOldSquareTop,hOldSquareRange,hOldSquareEdge,hOldOtherEdges⟩ :=
    hPrescribedSquare
      d.first oldComplementPath.toContinuousMap d.disk d.first_embedded hOldComplement
      d.disk_embedded oldComplementPath.source.symm oldComplementPath.target.symm
      hOldDiskBoundary hOldComplementCollision
  let oldSquare : C(Interval × Interval,↥F) :=
    oldSquareTop.comp ⟨squareFlip,squareFlip.continuous⟩
  have hOldSquare : IsEmbedding oldSquare := hOldSquareTop.comp squareFlip.isEmbedding
  have hOldSquareRangeExact : range oldSquare = range d.disk := by
    change range (oldSquareTop ∘ squareFlip) = range d.disk
    rw [squareFlip.surjective.range_comp,hOldSquareRange]
  have hOldSquareBottom : ∀ t, oldSquare (t,0) = d.first t := by
    intro t
    change oldSquareTop (t,unitInterval.symmHomeomorph 0) = d.first t
    simpa using hOldSquareEdge t
  have hOldSquareWholeCenter : range oldSquare ∩ range (fun t => matchedOldStrip (t,⟨0,by norm_num⟩)) =
      range (fun t => oldSquare (t,0)) := by
    simp only [hOldSquareRangeExact,hMatchedOldCenter,hOldSquareBottom]
    exact d.whole_first
  have hGuideSquareWholeCenter : range guideSquare ∩ range (fun t => calibratedGuideStrip (t,⟨0,by norm_num⟩)) =
      range (fun t => guideSquare (t,0)) := by
    simp only [hGuideSquareRangeExact,hCalibratedGuideCenter,hGuideSquareBottom]
    exact d.whole_second
  let guideSeam : C(Interval,Interval) :=
    CurveComplex.BranchedDoubleCover.intervalSegment d.bStart d.bFinish
  have hGuideSquareSeam : ∀ s : Interval,
      guideSquare (s,0) = calibratedGuideStrip (guideSeam s,⟨0,by norm_num⟩) := by
    intro s
    rw [hGuideSquareBottom,hCalibratedGuideCenter]
    exact d.second_eq s
  obtain ⟨guideBankSign,guideBankRadius,hGuideBankSignUnit,hGuideBankRadius,hGuideBankRadiusOne,hGuideBank⟩ :=
    embedded_disk_subinterval_edge_has_uniform_exterior_sign
      guideSquare hGuideSquare calibratedGuideStrip hCalibratedGuide guideSeam
      hGuideSquareSeam hGuideSquareWholeCenter hCalibratedGuideOpen
  have hGuideBankPositive : guideBankSign = 1 := by
    rcases hGuideBankSignUnit with hs | hs
    · obtain ⟨terminal,htone,hincoming⟩ := hCalibratedIncomingTerminal
        (guideBankRadius/2) (half_pos hGuideBankRadius)
        ((half_lt_self hGuideBankRadius).trans hGuideBankRadiusOne)
      obtain ⟨s,hst,hsone⟩ := exists_between htone
      obtain ⟨u,hu,he⟩ := hincoming ⟨s,⟨hst,hsone⟩,rfl⟩
      have hstart : d.bStart ∈ range guideSeam :=
        ⟨0,by simp [guideSeam,CurveComplex.BranchedDoubleCover.intervalSegment,
          CurveComplex.BranchedDoubleCover.intervalAffine]⟩
      have hpos : 0 < guideBankSign*u.val := by rw [hs]; linarith only [hu.2]
      have hsmall : guideBankSign*u.val ≤ guideBankRadius := by
        rw [hs]
        linarith only [hu.1,hGuideBankRadius]
      have hnot := hGuideBank d.bStart hstart u hpos hsmall
      apply False.elim
      apply hnot
      rw [hGuideSquareRangeExact]
      have hboundary : d.boundarySide s ∈ range d.disk := by
        apply image_subset_range d.disk {z | z.val ∈ Metric.sphere (0 : Plane) 1}
        rw [d.boundary_image]
        exact Or.inr (mem_range_self s)
      exact he.symm ▸ hboundary
    · exact hs
  have hCalibratedGuideExterior : ∀ t ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish),
      ∀ u : Icc (-1 : ℝ) 1, 0 < u.val → u.val ≤ guideBankRadius →
        calibratedGuideStrip (t,u) ∉ range d.disk := by
    intro t ht u hu hsmall
    have hseam : t ∈ range guideSeam := hsecondParam.symm ▸ ht
    have hh := hGuideBank t hseam u
    rw [hGuideBankPositive,one_mul,hGuideSquareRangeExact] at hh
    exact hh hu hsmall
  let oldSeam : C(Interval,Interval) :=
    CurveComplex.BranchedDoubleCover.intervalSegment d.aStart d.aFinish
  have hOldSquareSeam : ∀ s : Interval,
      oldSquare (s,0) = matchedOldStrip (oldSeam s,⟨0,by norm_num⟩) := by
    intro s
    rw [hOldSquareBottom,hMatchedOldCenter]
    exact d.first_eq s
  obtain ⟨oldBankSign,oldBankRadius,hOldBankSignUnit,hOldBankRadius,hOldBankRadiusOne,hOldBank⟩ :=
    embedded_disk_subinterval_edge_has_uniform_exterior_sign
      oldSquare hOldSquare matchedOldStrip hMatchedOld oldSeam
      hOldSquareSeam hOldSquareWholeCenter hMatchedOldOpen
  have hFinalDiskSector := actual_chart_two_ray_disk_sector finalFan.chart (range ambientDisk)
    hAmbientDiskClosed (by rw [hAmbientDiskRegular]) finalEntry hFinalEntryHeight
    finalFan.disk_in_target hFinalFrontier hFinalRetainedTest
  have hFinalDiskCriterion : ∀ y : ↥F,
      y ∈ chartPull F finalFan.chart (Metric.ball (0 : Plane) 1) →
      (y ∈ range d.disk ↔
        0 ≤ finalFan.chart y.val 1/finalEntry 1 ∧
        0 ≤ finalFan.chart y.val 0-(finalEntry 0/finalEntry 1)*finalFan.chart y.val 1) := by
    intro y hy
    have hh := hFinalDiskSector (finalFan.chart y.val) hy.2
    rw [finalFan.chart.left_inv hy.1] at hh
    apply Iff.trans ?_ hh
    constructor
    · rintro ⟨z,rfl⟩
      exact mem_range_self _
    · rintro ⟨z,hz⟩
      exact ⟨z,Subtype.ext hz⟩
  have hGuideHorizontalSign : guideCalibrationSign = -1 := by
    rcases hGuideCalibrationSign with hs | hs
    · exact hs
    · let u : Icc (-1 : ℝ) 1 := ⟨guideBankRadius/2,by
        constructor <;> linarith only [hGuideBankRadius,hGuideBankRadiusOne]⟩
      have hu : 0 < u.val := half_pos hGuideBankRadius
      have ht : rawEntry ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) :=
        hsecondParam ▸ mem_range_self finalEntryTime
      have hnot := hCalibratedGuideExterior rawEntry ht u hu (half_le_self hGuideBankRadius.le)
      have hsource := hCalibratedGuideUnit rawEntry u (by simpa using hGuideCalibrationRadius)
      apply False.elim
      apply hnot
      apply (hFinalDiskCriterion _ hsource).mpr
      rw [(hCalibratedGuideEntry u).2]
      change 0 ≤ finalEntry 1/finalEntry 1 ∧
        0 ≤ finalEntry 0+guideCalibrationSign*guideCalibrationScale*u.val-
          (finalEntry 0/finalEntry 1)*finalEntry 1
      rw [hs,one_mul,div_self hFinalEntryHeight,div_mul_cancel₀ _ hFinalEntryHeight]
      constructor
      · norm_num
      · linarith only [mul_pos hGuideCalibrationScale hu]
  have hGuideEntrySection : ∀ u : Icc (-1 : ℝ) 1,
      (calibratedGuideStrip (rawEntry,u)).val ∈ finalFan.chart.source ∧
      finalFan.chart (calibratedGuideStrip (rawEntry,u)).val =
        Plane.mk (finalEntry 0-guideCalibrationScale*u.val) (finalEntry 1) := by
    intro u
    have hc := hCalibratedGuideEntry u
    rw [hGuideHorizontalSign] at hc
    convert hc using 1 <;> congr 1 <;> ring
  have hGuideFramed : ∀ t : Interval, ∀ u : Icc (-1 : ℝ) 1,
      |t.val-rawEntry.val| < guideCalibrationRadius →
      (calibratedGuideStrip (t,u)).val ∈ finalFan.chart.source ∧
      finalFan.chart (calibratedGuideStrip (t,u)).val =
        Plane.mk (finalFan.chart (b t).val 0-guideCalibrationScale*u.val)
          (finalFan.chart (b t).val 1) := by
    intro t u ht
    have hc := hCalibratedGuideCoordinates t u ht
    rw [hGuideHorizontalSign] at hc
    convert hc using 1 <;> congr 1 <;> ring
  have hHullParameters (δ ε : ℝ) (e z : Plane) :
      z ∈ regionalHalfCornerHull δ e ε ↔
        ∃ t ∈ Icc (0 : ℝ) 1, ∃ a ∈ Icc (0 : ℝ) 1, ∃ b ∈ Icc (0 : ℝ) 1,
          z = Plane.mk (t*e 0-(1-t)*a*δ-t*b*ε) (t*e 1) := by
    clear * - δ ε e z
    have hvertices : ({0,Plane.mk (-δ) 0,e,Plane.mk (e 0-ε) (e 1)} : Set Plane) =
        {0,Plane.mk (-δ) 0} ∪ {e,Plane.mk (e 0-ε) (e 1)} := by
      ext y
      simp only [mem_insert_iff,mem_singleton_iff,mem_union]
      tauto
    have hbottom : ({0,Plane.mk (-δ) 0} : Set Plane).Nonempty := ⟨0,by simp⟩
    have htop : ({e,Plane.mk (e 0-ε) (e 1)} : Set Plane).Nonempty := ⟨e,by simp⟩
    rw [regionalHalfCornerHull,hvertices,convexHull_union hbottom htop,
      convexHull_pair,convexHull_pair,mem_convexJoin]
    have hcoordinates (a b t : ℝ) :
        (0+a • (Plane.mk (-δ) 0-0))+
          t • ((e+b • (Plane.mk (e 0-ε) (e 1)-e))-(0+a • (Plane.mk (-δ) 0-0))) =
          Plane.mk (t*e 0-(1-t)*a*δ-t*b*ε) (t*e 1) := by
      ext i
      fin_cases i
      · change (0+a*(-δ-0))+t*((e 0+b*((e 0-ε)-e 0))-(0+a*(-δ-0))) = t*e 0-(1-t)*a*δ-t*b*ε
        ring
      · change (0+a*(0-0))+t*((e 1+b*(e 1-e 1))-(0+a*(0-0))) = t*e 1
        ring
    constructor
    · rintro ⟨x,hx,y,hy,hz⟩
      rw [segment_eq_image'] at hx hy hz
      obtain ⟨a,ha,rfl⟩ := hx
      obtain ⟨b,hb,rfl⟩ := hy
      obtain ⟨t,ht,he⟩ := hz
      exact ⟨t,ht,a,ha,b,hb,he.symm.trans (hcoordinates a b t)⟩
    · rintro ⟨t,ht,a,ha,b,hb,rfl⟩
      refine ⟨0+a • (Plane.mk (-δ) 0-0),?_,e+b • (Plane.mk (e 0-ε) (e 1)-e),?_,?_⟩
      · rw [segment_eq_image']
        exact mem_image_of_mem _ ha
      · rw [segment_eq_image']
        exact mem_image_of_mem _ hb
      · rw [segment_eq_image']
        exact ⟨t,ht,hcoordinates a b t⟩
  have hHullFaces (δ ε : ℝ) (e : Plane) (hδ : 0 < δ) (hε : 0 ≤ ε) (he : e 1 ≠ 0) :
      (regionalHalfCornerHull δ e ε ⊆ {z | 0 ≤ z 1/e 1 ∧ z 1/e 1 ≤ 1 ∧ z 0-(e 0/e 1)*z 1 ≤ 0}) ∧
      (regionalHalfCornerHull δ e ε ∩ {z | z 0-(e 0/e 1)*z 1 = 0} = segment ℝ (0 : Plane) e) ∧
      (regionalHalfCornerHull δ e ε ∩ {z | z 1 = 0} = segment ℝ (0 : Plane) (Plane.mk (-δ) 0)) ∧
      (regionalHalfCornerHull δ e ε ∩ {z | z 1 = e 1} = segment ℝ e (Plane.mk (e 0-ε) (e 1))) := by
    clear * - δ ε e hδ hε he hHullParameters
    have htheta (t a b : ℝ) : (Plane.mk (t*e 0-(1-t)*a*δ-t*b*ε) (t*e 1)) 1/e 1 = t := by
      change (t*e 1)/e 1=t
      exact mul_div_cancel_right₀ t he
    have hell (t a b : ℝ) :
        (Plane.mk (t*e 0-(1-t)*a*δ-t*b*ε) (t*e 1)) 0-
          (e 0/e 1)*(Plane.mk (t*e 0-(1-t)*a*δ-t*b*ε) (t*e 1)) 1 =
          -((1-t)*a*δ)-t*b*ε := by
      change (t*e 0-(1-t)*a*δ-t*b*ε)-(e 0/e 1)*(t*e 1)=_
      field_simp
      <;> ring
    have hnonneg (t a b : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc (0 : ℝ) 1)
        (hb : b ∈ Icc (0 : ℝ) 1) : 0 ≤ (1-t)*a*δ ∧ 0 ≤ t*b*ε :=
      ⟨mul_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) ha.1) hδ.le,
       mul_nonneg (mul_nonneg ht.1 hb.1) hε⟩
    have hvertex (x : Plane) (hx : x ∈ ({0,Plane.mk (-δ) 0,e,Plane.mk (e 0-ε) (e 1)} : Set Plane)) :
        x ∈ regionalHalfCornerHull δ e ε := subset_convexHull ℝ _ hx
    have hsegment (x y : Plane)
        (hx : x ∈ ({0,Plane.mk (-δ) 0,e,Plane.mk (e 0-ε) (e 1)} : Set Plane))
        (hy : y ∈ ({0,Plane.mk (-δ) 0,e,Plane.mk (e 0-ε) (e 1)} : Set Plane)) :
        segment ℝ x y ⊆ regionalHalfCornerHull δ e ε :=
      (convex_convexHull ℝ _).segment_subset (hvertex x hx) (hvertex y hy)
    refine ⟨?_,?_,?_,?_⟩
    · intro z hz
      obtain ⟨t,ht,a,ha,b,hb,rfl⟩ := (hHullParameters δ ε e z).mp hz
      rw [mem_setOf_eq,htheta,hell]
      have hn := hnonneg t a b ht ha hb
      exact ⟨ht.1,ht.2,by linarith only [hn.1,hn.2]⟩
    · ext z
      constructor
      · rintro ⟨hz,hline⟩
        obtain ⟨t,ht,a,ha,b,hb,rfl⟩ := (hHullParameters δ ε e z).mp hz
        change _ = 0 at hline
        rw [hell] at hline
        have hn := hnonneg t a b ht ha hb
        have hA : (1-t)*a*δ=0 := by linarith only [hline,hn.1,hn.2]
        have hB : t*b*ε=0 := by linarith only [hline,hn.1,hn.2]
        rw [segment_eq_image']
        refine ⟨t,ht,?_⟩
        ext i
        fin_cases i
        · change 0+t*(e 0-0)=t*e 0-(1-t)*a*δ-t*b*ε
          rw [hA,hB]
          ring
        · change 0+t*(e 1-0)=t*e 1
          ring
      · intro hz
        refine ⟨hsegment 0 e (by simp) (by simp) hz,?_⟩
        rw [segment_eq_image'] at hz
        obtain ⟨t,ht,rfl⟩ := hz
        change (0+t*(e 0-0))-(e 0/e 1)*(0+t*(e 1-0))=0
        field_simp
        <;> ring
    · ext z
      constructor
      · rintro ⟨hz,hzero⟩
        obtain ⟨t,ht,a,ha,b,hb,rfl⟩ := (hHullParameters δ ε e z).mp hz
        change t*e 1=0 at hzero
        have ht0 := (mul_eq_zero.mp hzero).resolve_right he
        subst t
        rw [segment_eq_image']
        refine ⟨a,ha,?_⟩
        ext i
        fin_cases i
        · change 0+a*(-δ-0)=0*e 0-(1-0)*a*δ-0*b*ε
          ring
        · change 0+a*(0-0)=0*e 1
          ring
      · intro hz
        refine ⟨hsegment 0 (Plane.mk (-δ) 0) (by simp) (by simp) hz,?_⟩
        rw [segment_eq_image'] at hz
        obtain ⟨t,ht,rfl⟩ := hz
        change 0+t*(0-0)=0
        ring
    · ext z
      constructor
      · rintro ⟨hz,hone⟩
        obtain ⟨t,ht,a,ha,b,hb,rfl⟩ := (hHullParameters δ ε e z).mp hz
        change t*e 1=e 1 at hone
        have ht1 : t=1 := mul_right_cancel₀ he (by simpa only [one_mul] using hone)
        subst t
        rw [segment_eq_image']
        refine ⟨b,hb,?_⟩
        ext i
        fin_cases i
        · change e 0+b*((e 0-ε)-e 0)=1*e 0-(1-1)*a*δ-1*b*ε
          ring
        · change e 1+b*(e 1-e 1)=1*e 1
          ring
      · intro hz
        refine ⟨hsegment e (Plane.mk (e 0-ε) (e 1)) (by simp) (by simp) hz,?_⟩
        rw [segment_eq_image'] at hz
        obtain ⟨t,ht,rfl⟩ := hz
        change e 1+t*(e 1-e 1)=e 1
        ring
  have hOldBankNegative : oldBankSign = -1 := by
    rcases hOldBankSignUnit with hs | hs
    · exact hs
    · have hx : 0 < finalX coordinateLeft := by
        have hh := hFinalXAnti ⟨le_rfl,hCoordinateLR.le⟩ hFinalCornerMem hCoordinateLeftUpper
        simpa only [hFinalXZero] using hh
      let q : ℝ := (finalEntry 0/finalEntry 1)*(matchedOldSign*calibrationScale)
      let width : ℝ := min (oldBankRadius/2) (finalX coordinateLeft/(2*(|q|+1)))
      have hw : 0 < width := lt_min (half_pos hOldBankRadius)
        (div_pos hx (by positivity))
      have hwbank : width ≤ oldBankRadius :=
        (min_le_left _ _).trans (half_le_self hOldBankRadius.le)
      have hwx : 2*(|q|+1)*width ≤ finalX coordinateLeft := by
        have hh : width ≤ finalX coordinateLeft/(2*(|q|+1)) := min_le_right _ _
        have hhx := (le_div_iff₀ (show 0 < 2*(|q|+1) by positivity)).mp hh
        nlinarith only [hhx]
      let u : Icc (-1 : ℝ) 1 := ⟨width,⟨by linarith only [hw],hwbank.trans hOldBankRadiusOne.le⟩⟩
      have hseam : clock coordinateLeft ∈ range oldSeam := by
        have hm : aclock coordinateLeft ∈ range d.first :=
          hfirstRange.symm ▸ mem_image_of_mem aclock ⟨bot_le,hCoordinateLeftUpper.le⟩
        obtain ⟨s,he⟩ := hm
        refine ⟨s,(r v).val.property.1.injective ?_⟩
        exact (d.first_eq s).symm.trans he
      have hnot := hOldBank (clock coordinateLeft) hseam u
      rw [hs,one_mul,hOldSquareRangeExact] at hnot
      apply False.elim
      apply hnot hw hwbank
      apply (hFinalDiskCriterion _ (hMatchedOldUnit coordinateLeft ⟨le_rfl,hCoordinateLR.le⟩ u)).mpr
      rw [(hMatchedOldCoordinates coordinateLeft ⟨le_rfl,hCoordinateLR.le⟩ u).2]
      change 0 ≤ (matchedOldSign*calibrationScale*width)/finalEntry 1 ∧
        0 ≤ finalX coordinateLeft-(finalEntry 0/finalEntry 1)*(matchedOldSign*calibrationScale*width)
      constructor
      · apply le_of_lt
        rw [div_pos_iff]
        apply mul_pos_iff.mp
        have hh := mul_pos (mul_pos hMatchedOldSign hCalibrationScale) hw
        convert hh using 1 <;> ring
      · have hq := mul_le_mul_of_nonneg_right (le_abs_self q) hw.le
        have hg : 0 ≤ finalX coordinateLeft-q*width := by
          nlinarith only [hwx,hq,hw,abs_nonneg q]
        simpa only [q,mul_assoc] using hg
  have hMatchedOldExterior : ∀ t ∈ range oldSeam, ∀ u : Icc (-1 : ℝ) 1,
      -oldBankRadius ≤ u.val → u.val < 0 → matchedOldStrip (t,u) ∉ range d.disk := by
    intro t ht u hl hu
    have hh := hOldBank t ht u
    rw [hOldBankNegative,hOldSquareRangeExact] at hh
    exact hh (by linarith only [hu]) (by linarith only [hl])
  have hAffinePrefix (s t u : Interval) :
      CurveComplex.BranchedDoubleCover.intervalAffine s t '' Icc (0 : Interval) u =
      Icc (min s (CurveComplex.BranchedDoubleCover.intervalAffine s t u))
        (max s (CurveComplex.BranchedDoubleCover.intervalAffine s t u)) := by
    clear * - s t u
    let f := CurveComplex.BranchedDoubleCover.intervalAffine s t
    have hc : Continuous f := (CurveComplex.BranchedDoubleCover.intervalSegment s t).continuous
    have hzero : f 0=s := by simp [f,CurveComplex.BranchedDoubleCover.intervalAffine]
    apply Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩
      rcases le_total s t with hst | hts
      · have hmono : Monotone f := by
          intro x y hxy
          change (1-x.val)*s.val+x.val*t.val ≤ (1-y.val)*s.val+y.val*t.val
          change s.val ≤ t.val at hst
          change x.val ≤ y.val at hxy
          nlinarith only [hst,hxy]
        have hs : s ≤ f u := hzero ▸ hmono (show (0 : Interval) ≤ u from bot_le)
        change f x ∈ Icc (min s (f u)) (max s (f u))
        simpa only [min_eq_left hs,max_eq_right hs,mem_Icc] using
          (show s ≤ f x ∧ f x ≤ f u from ⟨hzero ▸ hmono hx.1,hmono hx.2⟩)
      · have hanti : Antitone f := by
          intro x y hxy
          change (1-y.val)*s.val+y.val*t.val ≤ (1-x.val)*s.val+x.val*t.val
          change t.val ≤ s.val at hts
          change x.val ≤ y.val at hxy
          nlinarith only [hts,hxy]
        have hs : f u ≤ s := hzero ▸ hanti (show (0 : Interval) ≤ u from bot_le)
        change f x ∈ Icc (min s (f u)) (max s (f u))
        simpa only [min_eq_right hs,max_eq_left hs,mem_Icc] using
          (show f u ≤ f x ∧ f x ≤ s from ⟨hanti hx.2,hzero ▸ hanti hx.1⟩)
    · have hp : OrdConnected (f '' Icc (0 : Interval) u) :=
        ((isPreconnected_Icc : IsPreconnected (Icc (0 : Interval) u)).image f hc.continuousOn).ordConnected
      have h0 : s ∈ f '' Icc (0 : Interval) u := ⟨0,⟨le_rfl,bot_le⟩,hzero⟩
      have hu : f u ∈ f '' Icc (0 : Interval) u := mem_image_of_mem f ⟨bot_le,le_rfl⟩
      exact hp.uIcc_subset h0 hu
  have hGuidePrefixParameters :
      CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish ''
        Icc (0 : Interval) finalEntryTime = Icc (min d.bStart rawEntry) (max d.bStart rawEntry) :=
    hAffinePrefix d.bStart d.bFinish finalEntryTime
  have hGuidePrefixSelected : Icc (min d.bStart rawEntry) (max d.bStart rawEntry) ⊆
      Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) := by
    rw [←hGuidePrefixParameters,←hsecondParam]
    exact image_subset_range _ _
  have hGuidePrefixImage : b '' Icc (min d.bStart rawEntry) (max d.bStart rawEntry) =
      d.second '' Icc (0 : Interval) finalEntryTime := by
    rw [←hGuidePrefixParameters,image_image]
    congr 1
    funext t
    exact (d.second_eq t).symm
  have hGuideCarrierDisk : ∀ μ : ℝ, 0 ≤ μ → μ ≤ guideBankRadius →
      regionalHalfJointGuideCarrier F calibratedGuideStrip d.bStart rawEntry μ ∩ range d.disk =
        d.second '' Icc (0 : Interval) finalEntryTime := by
    intro μ hμ hμsmall
    ext y
    constructor
    · rintro ⟨⟨⟨t,u⟩,⟨ht,hu⟩,rfl⟩,hd⟩
      have hu0 : u.val=0 := by
        by_contra hn
        exact hCalibratedGuideExterior t (hGuidePrefixSelected ht) u
          (lt_of_le_of_ne hu.1 (Ne.symm hn)) (hu.2.trans hμsmall) hd
      have he : u=⟨0,by norm_num⟩ := Subtype.ext hu0
      rw [he,hCalibratedGuideCenter]
      exact hGuidePrefixImage ▸ mem_image_of_mem b ht
    · intro hy
      obtain ⟨t,ht,rfl⟩ := hGuidePrefixImage.symm ▸ hy
      refine ⟨⟨(t,⟨0,by norm_num⟩),⟨ht,le_rfl,hμ⟩,hCalibratedGuideCenter t⟩,?_⟩
      have hh : b t ∈ range d.second := image_subset_range _ _ (hGuidePrefixImage ▸ mem_image_of_mem b ht)
      exact (d.whole_second.symm ▸ hh).1
  have hCornerCarrierDisk : ∀ ε : ℝ, 0 ≤ ε →
      regionalHalfCornerHull finalDelta finalEntry ε ⊆ Metric.ball (0 : Plane) 1 →
      chartPull F finalFan.chart (regionalHalfCornerHull finalDelta finalEntry ε) ∩ range d.disk =
        d.second '' Icc finalEntryTime (1 : Interval) := by
    intro ε hε hball
    have hf := hHullFaces finalDelta ε finalEntry hFinalDelta hε hFinalEntryHeight
    rw [←hFinalGuideSegment]
    ext y
    constructor
    · rintro ⟨⟨hy,hH⟩,hD⟩
      have hsector := (hFinalDiskCriterion y ⟨hy,hball hH⟩).mp hD
      exact ⟨hy,hf.2.1 ▸ ⟨hH,le_antisymm (hf.1 hH).2.2 hsector.2⟩⟩
    · rintro ⟨hy,hseg⟩
      have hH : finalFan.chart y.val ∈ regionalHalfCornerHull finalDelta finalEntry ε ∩
          {z | z 0-(finalEntry 0/finalEntry 1)*z 1=0} := hf.2.1.symm ▸ hseg
      refine ⟨⟨hy,hH.1⟩,(hFinalDiskCriterion y ⟨hy,hball hH.1⟩).mpr ?_⟩
      exact ⟨(hf.1 hH.1).1,le_of_eq hH.2.symm⟩
  have hOldNegativeDisk : ∀ ν : ℝ, 0 ≤ ν → ν ≤ oldBankRadius →
      regionalHalfOldNegativeBand F matchedOldStrip clock calibratedCut ν ∩ range d.disk = range d.first := by
    intro ν hν hνsmall
    ext y
    constructor
    · rintro ⟨⟨⟨t,u⟩,⟨⟨s,hs,rfl⟩,hu⟩,rfl⟩,hd⟩
      have hu0 : u.val=0 := by
        by_contra hn
        have hun : u.val<0 := lt_of_le_of_ne hu.2 hn
        by_cases hsc : s ≤ cornerTime
        · have hseam : clock s ∈ range oldSeam := by
            have hm : aclock s ∈ range d.first := hfirstRange.symm ▸ mem_image_of_mem aclock ⟨hs.1,hsc⟩
            obtain ⟨z,he⟩ := hm
            exact ⟨z,(r v).val.property.1.injective ((d.first_eq z).symm.trans he)⟩
          exact hMatchedOldExterior _ hseam u (by linarith only [hu.1,hνsmall]) hun hd
        · have hcoord : s ∈ Icc coordinateLeft coordinateRight :=
            ⟨(hCoordinateLeftUpper.le.trans (le_of_not_ge hsc)),hs.2.trans hCoordinateRightLower.le⟩
          have hh := (hFinalDiskCriterion _ (hMatchedOldUnit s hcoord u)).mp hd
          rw [(hMatchedOldCoordinates s hcoord u).2] at hh
          have hneg : (matchedOldSign*calibrationScale*u.val)/finalEntry 1 < 0 := by
            rw [div_neg_iff]
            apply mul_neg_iff.mp
            have he := mul_neg_of_pos_of_neg (mul_pos hMatchedOldSign hCalibrationScale) hun
            convert he using 1 <;> ring
          exact (not_lt_of_ge hh.1) hneg
      have he : u=⟨0,by norm_num⟩ := Subtype.ext hu0
      rw [he,hMatchedOldCenter] at hd ⊢
      exact d.whole_first ▸ ⟨hd,mem_range_self _⟩
    · intro hy
      have hd : y ∈ range d.disk := (d.whole_first.symm ▸ hy).1
      obtain ⟨s,hs,rfl⟩ := hfirstRange ▸ hy
      refine ⟨⟨(clock s,⟨0,by norm_num⟩),⟨?_,by linarith only [hν],le_rfl⟩,hMatchedOldCenter _⟩,hd⟩
      exact ⟨s,⟨hs.1,hs.2.trans hCalibratedCutLower.le⟩,rfl⟩
  have hUniformOpen {X : Type} [TopologicalSpace X]
      (E : C(Interval × Icc (-1 : ℝ) 1,X)) (K : Set Interval) (hK : IsCompact K)
      (U : Set X) (hU : IsOpen U) (hcenter : ∀ t ∈ K, E (t,⟨0,by norm_num⟩) ∈ U) :
      ∃ η : ℝ, 0 < η ∧ ∀ t ∈ K, ∀ u : Icc (-1 : ℝ) 1, |u.val| < η → E (t,u) ∈ U := by
    clear * - X E K hK U hU hcenter
    have he : ∀ᶠ u : Icc (-1 : ℝ) 1 in nhds ⟨0,by norm_num⟩,
        ∀ t ∈ K, E (t,u) ∈ U := by
      apply hK.eventually_forall_of_forall_eventually
      intro t ht
      have hc : Continuous (fun z : Icc (-1 : ℝ) 1 × Interval => E (z.2,z.1)) :=
        E.continuous.comp continuous_swap
      exact (hU.preimage hc).mem_nhds (hcenter t ht)
    obtain ⟨η,hη,hsub⟩ := Metric.mem_nhds_iff.mp he
    refine ⟨η,hη,fun t ht u hu => hsub ?_ t ht⟩
    simpa only [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq,sub_zero] using hu
  obtain ⟨hullMargin,hHullMargin,hHullMarginDelta,hHullMarginBall⟩ := hFinalHullMargin
  let fixedCap : ℝ := hullMargin/2
  have hFixedCap : 0 < fixedCap := half_pos hHullMargin
  have hFixedCapSmall : fixedCap < hullMargin := half_lt_self hHullMargin
  let fixedHull : Set Plane := regionalHalfCornerHull finalDelta finalEntry fixedCap
  have hFixedHullBall : fixedHull ⊆ Metric.ball (0 : Plane) 1 :=
    hHullMarginBall fixedCap hFixedCap hFixedCapSmall
  have hFixedHullCompact : IsCompact fixedHull :=
    (show ({0,Plane.mk (-finalDelta) 0,finalEntry,
      Plane.mk (finalEntry 0-fixedCap) (finalEntry 1)} : Set Plane).Finite by simp).isCompact_convexHull ℝ
  let fixedCorner : Set ↥F := chartPull F finalFan.chart fixedHull
  have hFixedCornerCompact : IsCompact fixedCorner := by
    have hc : IsCompact {z : Metric.closedBall (0 : Plane) 1 | z.val ∈ fixedHull} :=
      (hFixedHullCompact.isClosed.preimage continuous_subtype_val).isCompact
    have himage : finalChartPullback '' {z : Metric.closedBall (0 : Plane) 1 | z.val ∈ fixedHull} = fixedCorner := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact ⟨hFinalChartPullbackSource z,(hFinalChartPullbackCoord z).symm ▸ hz⟩
      · rintro ⟨hy,hH⟩
        refine ⟨⟨finalFan.chart y.val,Metric.ball_subset_closedBall (hFixedHullBall hH)⟩,hH,?_⟩
        apply Subtype.ext
        exact finalFan.chart.left_inv hy
    rw [←himage]
    exact hc.image hFinalChartPullbackContinuous
  have hFixedCornerDisk : fixedCorner ∩ range d.disk =
      d.second '' Icc finalEntryTime (1 : Interval) :=
    hCornerCarrierDisk fixedCap hFixedCap.le hFixedHullBall
  have hFixedGuideCenter : ∀ t ∈ Icc (min d.bStart rawEntry) (max d.bStart rawEntry),
      b t ∈ fixedCorner → t=rawEntry := by
    intro t ht hH
    have hp := hGuidePrefixImage ▸ mem_image_of_mem b ht
    have hd : b t ∈ range d.disk :=
      (d.whole_second.symm ▸ image_subset_range _ _ hp).1
    have hboth : b t ∈ fixedCorner ∩ range d.disk := ⟨hH,hd⟩
    obtain ⟨u,hu,he⟩ := hFixedCornerDisk ▸ hboth
    obtain ⟨s,hs,hse⟩ := hp
    have hsu : s=u := d.second_embedded.injective (hse.trans he.symm)
    have hsentry : s=finalEntryTime := le_antisymm hs.2 (hsu.symm ▸ hu.1)
    apply (r w).val.property.1.injective
    exact (hse.symm.trans (congrArg d.second hsentry)).trans hRawEntryEq.symm
  have hFixedOldCenter : ∀ t : Interval, a (clock t) ∈ fixedCorner →
      t ∈ Icc cornerTime calibratedCut := by
    intro t hH
    have haxis := (hFanAxis (d.first 1) finalFan ⟨some v,hpv⟩
      (hFinalAxes hpv).1 (hFinalAxes hpv).2 (a (clock t)) hH.1
      (Metric.ball_subset_closedBall (hFixedHullBall hH.2))).mp (mem_range_self (clock t))
    have hf := hHullFaces finalDelta fixedCap finalEntry hFinalDelta hFixedCap.le hFinalEntryHeight
    have hseg : a (clock t) ∈ chartPull F finalFan.chart
        (segment ℝ (0 : Plane) (Plane.mk (-finalDelta) 0)) :=
      ⟨hH.1,hf.2.2.1 ▸ ⟨hH.2,haxis⟩⟩
    obtain ⟨raw,⟨s,hs,rfl⟩,he⟩ := hFinalOldSegment ▸ hseg
    exact (clock.injective ((r v).val.property.1.injective he)) ▸ hs
  let guideAway : Set Interval := Icc (min d.bStart rawEntry) (max d.bStart rawEntry) ∩
    {t | guideCalibrationRadius ≤ |t.val-rawEntry.val|}
  have hGuideAwayCompact : IsCompact guideAway :=
    isCompact_Icc.inter_right (isClosed_le continuous_const (by fun_prop))
  obtain ⟨guideHullWidth,hGuideHullWidth,hGuideHullClear⟩ := hUniformOpen calibratedGuideStrip
    guideAway hGuideAwayCompact fixedCornerᶜ hFixedCornerCompact.isClosed.isOpen_compl (by
      intro t ht
      rw [hCalibratedGuideCenter]
      intro hy
      have he := hFixedGuideCenter t ht.1 hy
      subst t
      exact (not_le_of_gt hGuideCalibrationRadius) (by simpa only [mem_setOf_eq,sub_self,abs_zero] using ht.2))
  let oldAway : Set Interval := (clock '' Icc (0 : Interval) calibratedCut) \ (clock '' oldCoordinateWindow)
  have hOldAwayCompact : IsCompact oldAway :=
    (isCompact_Icc.image clock.continuous).diff (clock.isOpenMap _ isOpen_Ioo)
  obtain ⟨oldHullWidth,hOldHullWidth,hOldHullClear⟩ := hUniformOpen matchedOldStrip
    oldAway hOldAwayCompact fixedCornerᶜ hFixedCornerCompact.isClosed.isOpen_compl (by
      intro t ht
      rw [hMatchedOldCenter]
      intro hy
      obtain ⟨s,hs,rfl⟩ := ht.1
      exact ht.2 ⟨s,hOldCoordinatePadded (hFixedOldCenter s hy),rfl⟩)
  have hHullMono (δ : ℝ) (e : Plane) (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 < η) (hεη : ε ≤ η) :
      regionalHalfCornerHull δ e ε ⊆ regionalHalfCornerHull δ e η := by
    clear * - δ e ε η hε hη hεη hHullParameters
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro z hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact subset_convexHull ℝ _ (by simp)
    · exact subset_convexHull ℝ _ (by simp)
    · exact subset_convexHull ℝ _ (by simp)
    · apply (hHullParameters δ η e _).mpr
      refine ⟨1,by norm_num,0,by norm_num,ε/η,⟨div_nonneg hε hη.le,(div_le_one hη).mpr hεη⟩,?_⟩
      ext i
      fin_cases i
      · change e 0-ε=1*e 0-(1-1)*0*δ-1*(ε/η)*η
        simp only [one_mul,sub_self,zero_mul,sub_zero,div_mul_cancel₀ _ hη.ne']
      · change e 1=1*e 1
        ring
  have hOldCornerInter : ∀ ν : ℝ, 0 ≤ ν → ν < oldHullWidth →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ fixedCap →
      regionalHalfOldNegativeBand F matchedOldStrip clock calibratedCut ν ∩
        chartPull F finalFan.chart (regionalHalfCornerHull finalDelta finalEntry ε) =
        a '' (clock '' Icc cornerTime calibratedCut) := by
    intro ν hν hνsmall ε hε hεsmall
    have hsub := hHullMono finalDelta finalEntry ε fixedCap hε hFixedCap hεsmall
    have hf := hHullFaces finalDelta ε finalEntry hFinalDelta hε hFinalEntryHeight
    ext y
    constructor
    · rintro ⟨⟨⟨t,u⟩,⟨⟨s,hs,rfl⟩,hu⟩,rfl⟩,hH⟩
      have hswindow : s ∈ oldCoordinateWindow := by
        by_contra hn
        have ht : clock s ∈ oldAway := ⟨⟨s,hs,rfl⟩,by
          rintro ⟨s',hs',he⟩
          exact hn ((clock.injective he) ▸ hs')⟩
        have hwidth : |u.val| < oldHullWidth := by
          rw [abs_of_nonpos hu.2]
          linarith only [hu.1,hνsmall]
        exact hOldHullClear _ ht u hwidth ⟨hH.1,hsub hH.2⟩
      have hcoord : s ∈ Icc coordinateLeft coordinateRight := ⟨hswindow.1.le,hswindow.2.le⟩
      have hc := (hMatchedOldCoordinates s hcoord u).2
      have hheight : (matchedOldSign*calibrationScale*u.val)/finalEntry 1 ≥ 0 := by
        have hh := (hf.1 hH.2).1
        rwa [hc] at hh
      have hu0 : u.val=0 := by
        by_contra hn
        have hneg : (matchedOldSign*calibrationScale*u.val)/finalEntry 1 < 0 := by
          rw [div_neg_iff]
          apply mul_neg_iff.mp
          have hh := mul_neg_of_pos_of_neg (mul_pos hMatchedOldSign hCalibrationScale)
            (lt_of_le_of_ne hu.2 hn)
          convert hh using 1 <;> ring
        exact (not_lt_of_ge hheight) hneg
      have he : u=⟨0,by norm_num⟩ := Subtype.ext hu0
      rw [he,hMatchedOldCenter] at hH ⊢
      apply hFinalOldSegment ▸ (show a (clock s) ∈ chartPull F finalFan.chart
          (segment ℝ (0 : Plane) (Plane.mk (-finalDelta) 0)) from ?_)
      refine ⟨hH.1,hf.2.2.1 ▸ ⟨hH.2,?_⟩⟩
      have hc0 := (hMatchedOldCoordinates s hcoord ⟨0,by norm_num⟩).2
      rw [hMatchedOldCenter] at hc0
      rw [hc0]
      change matchedOldSign*calibrationScale*0=0
      ring
    · intro hy
      have hseg := hFinalOldSegment.symm ▸ hy
      obtain ⟨t,⟨s,hs,rfl⟩,rfl⟩ := hy
      refine ⟨⟨(clock s,⟨0,by norm_num⟩),⟨?_,by linarith only [hν],le_rfl⟩,hMatchedOldCenter _⟩,
        hseg.1,(hf.2.2.1.symm ▸ hseg.2).1⟩
      exact ⟨s,⟨bot_le,hs.2⟩,rfl⟩
  have hGuideCornerInter : ∀ μ : ℝ, 0 ≤ μ → μ < guideHullWidth →
      ∀ ε : ℝ, 0 < ε → ε ≤ fixedCap → ε ≤ guideCalibrationScale*μ →
      regionalHalfJointGuideCarrier F calibratedGuideStrip d.bStart rawEntry μ ∩
        chartPull F finalFan.chart (regionalHalfCornerHull finalDelta finalEntry ε) =
      calibratedGuideStrip '' {z | z.1=rawEntry ∧ 0 ≤ z.2.val ∧ z.2.val ≤ ε/guideCalibrationScale} := by
    intro μ hμ hμsmall ε hε hεcap hεwidth
    have hsub := hHullMono finalDelta finalEntry ε fixedCap hε.le hFixedCap hεcap
    have hf := hHullFaces finalDelta ε finalEntry hFinalDelta hε.le hFinalEntryHeight
    ext y
    constructor
    · rintro ⟨⟨⟨t,u⟩,⟨ht,hu⟩,rfl⟩,hH⟩
      have htnear : |t.val-rawEntry.val| < guideCalibrationRadius := by
        by_contra hn
        exact hGuideHullClear t ⟨ht,le_of_not_gt hn⟩ u
          (by rw [abs_of_nonneg hu.1]; exact hu.2.trans_lt hμsmall) ⟨hH.1,hsub hH.2⟩
      have hc := hGuideFramed t u htnear
      have hbunit := hCalibratedGuideUnit t ⟨0,by norm_num⟩ htnear
      rw [hCalibratedGuideCenter] at hbunit
      have hbrays : finalFan.chart (b t).val ∈ guideRays :=
        (hFanTrace (d.first 1) finalFan guideIndex (b t) hbunit.1
          (Metric.ball_subset_closedBall hbunit.2)).mp (mem_range_self t)
      let θ : ℝ := finalFan.chart (b t).val 1/finalEntry 1
      have hθ : θ ∈ Icc (0 : ℝ) 1 := by
        have hh := hf.1 hH.2
        rw [hc.2] at hh
        exact ⟨hh.1,hh.2.1⟩
      have hz : θ • finalEntry ∈ segment ℝ (0 : Plane) finalEntry := by
        rw [segment_eq_image']
        exact ⟨θ,hθ,by simp⟩
      have heheight : (θ • finalEntry) 1=finalFan.chart (b t).val 1 := by
        change (finalFan.chart (b t).val 1/finalEntry 1)*finalEntry 1=_
        exact div_mul_cancel₀ _ hFinalEntryHeight
      have hecoord := hGuideRaysHeight (hEntrySegmentRays hz) hbrays heheight
      have hbseg : b t ∈ chartPull F finalFan.chart (segment ℝ (0 : Plane) finalEntry) :=
        ⟨hbunit.1,hecoord ▸ hz⟩
      have hbH : b t ∈ fixedCorner :=
        ⟨hbseg.1,((hHullFaces finalDelta fixedCap finalEntry hFinalDelta hFixedCap.le
          hFinalEntryHeight).2.1.symm ▸ hbseg.2).1⟩
      have htentry := hFixedGuideCenter t ht hbH
      subst t
      have htop : finalFan.chart (calibratedGuideStrip (rawEntry,u)).val ∈
          segment ℝ finalEntry (Plane.mk (finalEntry 0-ε) (finalEntry 1)) :=
        hf.2.2.2 ▸ ⟨hH.2,by rw [(hGuideEntrySection u).2]; rfl⟩
      rw [segment_eq_image'] at htop
      obtain ⟨weight,hweight,he⟩ := htop
      have he0 := congrArg (fun z : Plane => z 0) he
      rw [(hGuideEntrySection u).2] at he0
      change finalEntry 0+weight*((finalEntry 0-ε)-finalEntry 0)=finalEntry 0-guideCalibrationScale*u.val at he0
      have huwidth : u.val ≤ ε/guideCalibrationScale := by
        apply (le_div_iff₀ hGuideCalibrationScale).mpr
        nlinarith only [he0,hweight.2,hε]
      exact ⟨(rawEntry,u),⟨rfl,hu.1,huwidth⟩,rfl⟩
    · rintro ⟨⟨t,u⟩,⟨rfl,hu,huw⟩,rfl⟩
      have hum : u.val ≤ μ := by
        have hh := (le_div_iff₀ hGuideCalibrationScale).mp huw
        nlinarith only [hh,hεwidth,hGuideCalibrationScale]
      refine ⟨⟨(rawEntry,u),⟨⟨min_le_right _ _,le_max_right _ _⟩,hu,hum⟩,rfl⟩,
        (hGuideEntrySection u).1,?_⟩
      rw [(hGuideEntrySection u).2]
      apply (hHullParameters finalDelta ε finalEntry _).mpr
      let weight : ℝ := guideCalibrationScale*u.val/ε
      have hweight : weight ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (mul_nonneg hGuideCalibrationScale.le hu) hε.le,
         (div_le_one hε).mpr (by nlinarith only [(le_div_iff₀ hGuideCalibrationScale).mp huw])⟩
      refine ⟨1,by norm_num,0,by norm_num,weight,hweight,?_⟩
      ext i
      fin_cases i
      · change finalEntry 0-guideCalibrationScale*u.val=1*finalEntry 0-(1-1)*0*finalDelta-1*weight*ε
        simp only [one_mul,sub_self,zero_mul,sub_zero,weight,div_mul_cancel₀ _ hε.ne']
      · change finalEntry 1=1*finalEntry 1
        ring
  have hOldGuideCentersDisjoint : Disjoint (aclock '' Icc (0 : Interval) calibratedCut)
      (b '' Icc (min d.bStart rawEntry) (max d.bStart rawEntry)) := by
    apply disjoint_left.mpr
    rintro y ⟨s,hs,rfl⟩ hg
    have hg' := hGuidePrefixImage ▸ hg
    obtain ⟨t,ht,he⟩ := hg'
    by_cases hsc : s ≤ cornerTime
    · have hfirst : aclock s ∈ range d.first := hfirstRange.symm ▸ mem_image_of_mem aclock ⟨hs.1,hsc⟩
      have hboth : aclock s ∈ range d.first ∩ range d.second := ⟨hfirst,⟨t,he⟩⟩
      have hcorner : aclock s=d.first 1 := mem_singleton_iff.mp (d.sides_inter ▸ hboth)
      have htone : t=1 := d.second_embedded.injective (he.trans (hcorner.trans d.corner_eq))
      exact (not_le_of_gt hFinalEntryBefore) (htone ▸ ht.2)
    · have hK : aclock s ∈ K := by
        apply mem_iUnion_of_mem ⟨some w,by simpa using Ne.symm hvw⟩
        exact ⟨CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish t,
          (d.second_eq t).symm.trans he⟩
      exact disjoint_left.mp hCalibratedPadded ⟨s,⟨lt_of_not_ge hsc,hs.2⟩,rfl⟩ hK
  obtain ⟨oldNeighborhood,guideNeighborhood,hOldNeighborhood,hGuideNeighborhood,
    hOldCenterNeighborhood,hGuideCenterNeighborhood,hNeighborhoodsDisjoint⟩ :=
      SeparatedNhds.of_isCompact_isCompact (isCompact_Icc.image aclock.continuous)
        (isCompact_Icc.image b.continuous) hOldGuideCentersDisjoint
  obtain ⟨oldGuideWidth,hOldGuideWidth,hOldGuideClear⟩ := hUniformOpen matchedOldStrip
    (clock '' Icc (0 : Interval) calibratedCut) (isCompact_Icc.image clock.continuous)
    oldNeighborhood hOldNeighborhood (by
      intro t ht
      rw [hMatchedOldCenter]
      obtain ⟨s,hs,rfl⟩ := ht
      exact hOldCenterNeighborhood ⟨s,hs,rfl⟩)
  obtain ⟨guideOldWidth,hGuideOldWidth,hGuideOldClear⟩ := hUniformOpen calibratedGuideStrip
    (Icc (min d.bStart rawEntry) (max d.bStart rawEntry)) isCompact_Icc
    guideNeighborhood hGuideNeighborhood (by
      intro t ht
      rw [hCalibratedGuideCenter]
      exact hGuideCenterNeighborhood (mem_image_of_mem b ht))
  have hOldGuideDisjoint : ∀ ν μ : ℝ, ν < oldGuideWidth → μ < guideOldWidth →
      Disjoint (regionalHalfOldNegativeBand F matchedOldStrip clock calibratedCut ν)
        (regionalHalfJointGuideCarrier F calibratedGuideStrip d.bStart rawEntry μ) := by
    intro ν μ hν hμ
    apply disjoint_left.mpr
    rintro y ⟨⟨t,u⟩,⟨ht,hu⟩,rfl⟩ ⟨⟨s,z⟩,⟨hs,hz⟩,he⟩
    apply disjoint_left.mp hNeighborhoodsDisjoint (hOldGuideClear t ht u ?_) (he ▸ hGuideOldClear s hs z ?_)
    · rw [abs_of_nonpos hu.2]
      linarith only [hu.1,hν]
    · rw [abs_of_nonneg hz.1]
      exact hz.2.trans_lt hμ
  obtain ⟨jointBound,hJointBound,hJointBoundSmall⟩ := exists_between
    (lt_min hGuideBankRadius hCalibratedBoundaryBound)
  have hJointBoundGuide : jointBound < guideBankRadius := hJointBoundSmall.trans_le (min_le_left _ _)
  have hJointBoundBoundary : jointBound < calibratedBoundaryBound := hJointBoundSmall.trans_le (min_le_right _ _)
  have hJointBoundOne : jointBound < 1 := hJointBoundBoundary.trans hCalibratedBoundaryBoundOne
  obtain ⟨jointEntryMargin,hJointEntryMargin,hJointEntryMarginSmall⟩ := exists_between
    (lt_min hJointBound (lt_min hGuideHullWidth hGuideOldWidth))
  have hJointEntryBound : jointEntryMargin < jointBound := hJointEntryMarginSmall.trans_le (min_le_left _ _)
  have hJointEntryHull : jointEntryMargin < guideHullWidth :=
    (hJointEntryMarginSmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hJointEntryOld : jointEntryMargin < guideOldWidth :=
    (hJointEntryMarginSmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  obtain ⟨jointNegativeWidth,hJointNegativeWidth,hJointNegativeWidthSmall⟩ := exists_between
    (lt_min (show (0 : ℝ) < 1/2 by norm_num)
      (lt_min hOldBankRadius (lt_min hOldHullWidth hOldGuideWidth)))
  have hJointNegativeCorner : jointNegativeWidth < 1/2 :=
    hJointNegativeWidthSmall.trans_le (min_le_left _ _)
  have hJointNegativeBank : jointNegativeWidth < oldBankRadius :=
    (hJointNegativeWidthSmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hJointNegativeHull : jointNegativeWidth < oldHullWidth :=
    ((hJointNegativeWidthSmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hJointNegativeGuide : jointNegativeWidth < oldGuideWidth :=
    ((hJointNegativeWidthSmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  obtain ⟨jointCapBound,hJointCapBound,hJointCapBoundSmall⟩ := exists_between
    (lt_min hFixedCap (mul_pos hGuideCalibrationScale hJointEntryMargin))
  have hJointCapFixed : jointCapBound < fixedCap := hJointCapBoundSmall.trans_le (min_le_left _ _)
  have hJointCapScale : jointCapBound < guideCalibrationScale*jointEntryMargin :=
    hJointCapBoundSmall.trans_le (min_le_right _ _)
  obtain ⟨jointTerminal,hJointTerminal,hJointIncoming⟩ :=
    hCalibratedIncomingTerminal jointBound hJointBound hJointBoundOne
  refine ⟨{
    bound := jointBound
    bound_pos := hJointBound
    bound_lt_one := hJointBoundOne
    clock := clock
    clock_start := hclockStart
    cut := calibratedCut
    corner_before_cut := hCalibratedCutLower
    cut_interior := hCalibratedCutInterior
    active_prefix := ?_
    padded_clear := ?_
    retained_tail := ?_
    oldStrip := matchedOldStrip
    oldStrip_embedded := hMatchedOld
    oldStrip_center := hMatchedOldCenter
    oldStrip_ends := hMatchedOldEnds
    oldStrip_interior := hMatchedOldInterior
    oldStrip_open := hMatchedOldOpen
    activeWindow := activeWindow
    activeWindow_open := hActiveOpen
    activeWindow_prefix := ?_
    oldStrip_full_active_fibers := hMatchedOldActive
    guideStrip := calibratedGuideStrip
    guideStrip_embedded := hCalibratedGuide
    guideStrip_center := hCalibratedGuideCenter
    guideStrip_ends := hCalibratedGuideEnds
    guideStrip_interior := hCalibratedGuideInterior
    guideStrip_open := hCalibratedGuideOpen
    guiding_exterior := ?_
    guideWindow := guideWindow
    guideWindow_open := hGuideWindowOpen
    guideWindow_selected := hGuideSelected
    guide_full_window_fibers := hCalibratedGuideActive
    guideClock := guideClock
    guideClock_start := hguideClockStart
    guideClock_increasing := hguideClockOrder
    guideClock_identity_or_reverse := ?_
    guideEntryTime := finalEntryTime
    guideEntryTime_interior := hFinalEntryInterior
    boundaryLine := calibratedBoundaryLine
    boundaryLine_eq := fun _ => rfl
    boundaryLine_embedded := hCalibratedBoundary
    boundaryLine_zero := hCalibratedBoundaryZero
    boundaryLine_local := (image_subset_range _ _).trans hCalibratedBoundaryLocal
    terminalCut := jointTerminal
    terminalCut_lt := hJointTerminal
    incoming_terminal := hJointIncoming
    positive_boundary_branch_outside := ?_
    corner_event := hpEvent
    cornerFan := finalFan
    cornerFan_in_original := hFinalNested
    corner_a_axis := hFinalAxes
    corner_other_ports_opposite := hFinalPortSigns
    cornerDelta := finalDelta
    cornerDelta_pos := hFinalDelta
    cornerEntry := finalEntry
    cornerEntry_nonzero_height := hFinalEntryHeight
    corner_selected_ports_opposite := ?_
    cornerEntry_actual := ⟨hFinalEntrySource.1,rfl⟩
    corner_b_axis_segment := hFinalGuideSegment
    corner_a_axis_segment := hFinalOldSegment
    entryMargin := jointEntryMargin
    entryMargin_pos := hJointEntryMargin
    entryMargin_lt_bound := hJointEntryBound
    kappa := guideCalibrationScale
    kappa_pos := hGuideCalibrationScale
    guide_entry_section := fun u _ _ => hGuideEntrySection u
    capBound := jointCapBound
    capBound_pos := hJointCapBound
    capBound_lt_scale_margin := hJointCapScale
    corner_horizontal_progress := ?_
    corner_hull_in_unit := ?_
    oldCornerWindow := oldCoordinateWindow
    oldCornerWindow_open := isOpen_Ioo
    oldCornerWindow_padded := hOldCoordinatePadded
    oldCornerWindow_active := hOldCoordinateActive
    oldCornerWidth := 1/2
    oldCornerWidth_pos := by norm_num
    oldCornerWidth_lt_one := by norm_num
    oldCornerX := finalX
    oldCornerX_order := hFinalXOpenAnti
    oldCornerX_corner := hFinalXZero
    oldCornerX_cut := hFinalCutX
    oldCornerScale := calibrationScale
    oldCornerScale_pos := hCalibrationScale
    oldCornerSign := matchedOldSign
    oldCornerSign_unit := hMatchedOldSignUnit
    oldCornerSign_matches := hMatchedOldSign
    old_corner_transition := fun t ht u _ => hMatchedOldCoordinates t ⟨ht.1.le,ht.2.le⟩ u
    old_corner_transition_unit := fun t ht u _ => hMatchedOldUnit t ⟨ht.1.le,ht.2.le⟩ u
    oldNegativeWidth := jointNegativeWidth
    oldNegativeWidth_pos := hJointNegativeWidth
    oldNegativeWidth_lt_corner := hJointNegativeCorner
    guide_carrier_disk_inter := hGuideCarrierDisk jointEntryMargin hJointEntryMargin.le
      (hJointEntryBound.trans hJointBoundGuide).le
    corner_carrier_disk_inter := ?_
    old_negative_disk_inter := hOldNegativeDisk jointNegativeWidth hJointNegativeWidth.le hJointNegativeBank.le
    guide_corner_carrier_inter := ?_
    old_negative_guide_carrier_disjoint := hOldGuideDisjoint jointNegativeWidth jointEntryMargin
      hJointNegativeGuide hJointEntryOld
    old_negative_corner_carrier_inter := ?_
  }⟩
  · rw [image_image]
    exact hCalibratedPrefix
  · rw [image_image]
    exact hCalibratedPadded
  · rw [image_image]
    exact hCalibratedTail
  · exact (image_mono (Icc_subset_Icc_right hCalibratedCutOld.le)).trans hActivePrefix
  · apply disjoint_left.mpr
    rintro y ⟨⟨t,u⟩,⟨ht,hu⟩,rfl⟩ hd
    exact hCalibratedGuideExterior t ht u hu.1 (hu.2.trans hJointBoundGuide).le hd
  · by_cases h0 : d.bStart=0
    · exact Or.inl (if_pos h0)
    · exact Or.inr (if_neg h0)
  · apply disjoint_left.mpr
    rintro y ⟨u,hu,rfl⟩ hd
    exact hCalibratedBoundaryOutside u hu.1 (hu.2.trans hJointBoundBoundary) hd
  · intro h
    exact hFinalPortSigns ⟨some w,h⟩ (by simpa using Ne.symm hvw)
  · intro ε hε hεsmall
    exact hFinalHorizontalProgress ε hε
      (hεsmall.trans (hJointCapFixed.trans (hFixedCapSmall.trans hHullMarginDelta)))
  · intro ε hε hεsmall
    exact hHullMarginBall ε hε (hεsmall.trans (hJointCapFixed.trans hFixedCapSmall))
  · intro ε hε hεsmall
    exact hCornerCarrierDisk ε hε.le
      (hHullMarginBall ε hε (hεsmall.trans (hJointCapFixed.trans hFixedCapSmall)))
  · intro ε hε hεsmall
    exact hGuideCornerInter jointEntryMargin hJointEntryMargin.le hJointEntryHull ε hε
      (hεsmall.trans hJointCapFixed).le (hεsmall.trans hJointCapScale).le
  · intro ε hε hεsmall
    exact hOldCornerInter jointNegativeWidth hJointNegativeWidth.le hJointNegativeHull ε hε.le
      (hεsmall.trans hJointCapFixed).le
