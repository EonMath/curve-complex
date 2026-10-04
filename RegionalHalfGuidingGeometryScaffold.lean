import HalfSignedGuidingChainRecord
import FiniteSupportedInternalCollarCalibrationScaffold
import RegionalHalfJointCollarCornerScaffold
import CurveComplexGenusTwo.Topology.FrontierCircle.PathGluingProbe
import Lean

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies RegionalChordNormalization
open scoped BigOperators
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P
set_option maxHeartbeats 36000000
set_option maxRecDepth 6000

theorem regional_half_signed_guiding_chain
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
        Nonempty (RegionalHalfSignedGuidingChain F {y | y.val ∈ boundaryCircle}
          {y : ↥F | y.val ∈ frontier F}
          (fun i => (r i).val.val) α.val.val v w d V fan gap) := by
  classical
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    ι inst r α hinv hcross v w hvw d V hV hdV havoid
    C₀ removed guiding offset hcheap fan gap
  let : ClosedSurface S := Classical.choice hS.2.1
  obtain ⟨joint⟩ := regional_half_joint_calibrated_collar_corner_exists
    S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular
    J c hdisjoint hbaseDisjoint hfrontier
    ι r α hinv hcross v w hvw d V hV hdV havoid hcheap fan gap
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
  have hbstartEndpoint : d.bStart = 0 ∨ d.bStart = 1 := by
    by_cases h0 : d.bStart = 0
    · exact Or.inl h0
    by_cases h1 : d.bStart = 1
    · exact Or.inr h1
    exact False.elim ((r w).val.property.2.2.2 d.bStart
      ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩
      (hBF (show (b d.bStart).val ∈ boundaryCircle from hsecond0 ▸ d.second_zero)))
  let guideStrip := joint.guideStrip
  let boundaryLine := joint.boundaryLine
  have hGuide : IsEmbedding guideStrip := joint.guideStrip_embedded
  have hGuideCenterActual : ∀ t, guideStrip (t,⟨0,by norm_num⟩) = b t :=
    joint.guideStrip_center
  have hBoundaryLine : IsEmbedding boundaryLine := joint.boundaryLine_embedded
  have hBoundaryZero : boundaryLine ⟨0,by norm_num⟩ = d.second 0 := joint.boundaryLine_zero
  have hBoundaryBV : range boundaryLine ⊆ {y : ↥F | y.val ∈ boundaryCircle} ∩ V := by
    rintro y ⟨u,rfl⟩
    rw [joint.boundaryLine_eq]
    refine ⟨?_,joint.guide_full_window_fibers _
      (joint.guideWindow_selected ⟨min_le_left _ _,le_max_left _ _⟩) u⟩
    rcases hbstartEndpoint with h0 | h1
    · rw [h0]
      exact (joint.guideStrip_ends u).1
    · rw [h1]
      exact (joint.guideStrip_ends u).2
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
  let bound : ℝ := min outRadius (min joint.bound joint.entryMargin) / 2
  have hbound : 0 < bound := by dsimp [bound]; positivity [joint.bound_pos,joint.entryMargin_pos]
  have hboundRadius : bound < outRadius := by
    dsimp [bound]
    linarith only [min_le_left outRadius (min joint.bound joint.entryMargin),houtRadius]
  have hboundJoint : bound < joint.bound := by
    dsimp [bound]
    have hm := (min_le_right outRadius (min joint.bound joint.entryMargin)).trans
      (min_le_left joint.bound joint.entryMargin)
    linarith only [hm,joint.bound_pos]
  have hboundMargin : bound < joint.entryMargin := by
    dsimp [bound]
    have hm := (min_le_right outRadius (min joint.bound joint.entryMargin)).trans
      (min_le_right joint.bound joint.entryMargin)
    linarith only [hm,joint.entryMargin_pos]
  have hboundOne : bound < 1 := hboundJoint.trans joint.bound_lt_one
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
    obtain ⟨u,hu,hbu⟩ := hbetaEq ρ
    rw [hbu,joint.boundaryLine_eq] at ht
    have he := hGuide.injective ((hGuideCenterActual t).trans ht)
    have hw := congrArg (fun z : Interval × Icc (-1 : ℝ) 1 => z.2.val) he
    change 0 = u.val at hw
    exact (ne_of_gt ρ.property.1) (hu.symm.trans hw.symm)
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
  have hBetaPositiveOutside : ∀ u : Icc (-1 : ℝ) 1, 0 < u.val → u.val < bound →
      boundaryLine u ∉ range d.boundarySide := by
    intro u hu0 hu1
    exact disjoint_left.mp joint.positive_boundary_branch_outside
      ⟨u,⟨hu0,hu1.trans hboundJoint⟩,rfl⟩
  have hBetaOutside : ∀ ρ, beta ρ ∉ range d.boundarySide := by
    intro ρ
    obtain ⟨u,hu,he⟩ := hbetaEq ρ
    rw [he]
    exact hBetaPositiveOutside u (hu.symm ▸ ρ.property.1) (hu.symm ▸ ρ.property.2)
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
    exists_between (show max terminalLower joint.terminalCut < (1 : Interval) from
      max_lt hterminalLower joint.terminalCut_lt)
  have hIncomingTerminal : d.boundarySide '' Ioo terminalCut (1 : Interval) ⊆
      boundaryLine '' {u | -bound < u.val ∧ u.val < 0} := by
    rintro y ⟨s,hs,rfl⟩
    obtain ⟨u,hu,he⟩ := hterminalSubset (show s ∈ Ioi terminalLower from
      (le_max_left _ _).trans_lt (hterminalCutLower.trans hs.1))
    obtain ⟨q,hq,hqe⟩ := joint.incoming_terminal
      ⟨s,⟨(le_max_right _ _).trans_lt (hterminalCutLower.trans hs.1),hs.2⟩,rfl⟩
    have heu : q = u := hBoundaryLine.injective (hqe.trans he.symm)
    refine ⟨u,⟨(abs_lt.mp hu).1,heu ▸ hq.2⟩,he⟩
  obtain ⟨incomingMarker,hincomingMarkerLower,hincomingMarkerOne⟩ :=
    exists_between (show max gap.cut terminalCut < (1 : Interval) from
      max_lt gap.cut_lt_one hterminalCutOne)
  have hBoundaryExtensionSeam : ∀ (ρ : Ioo (0 : ℝ) bound),
      range d.boundarySide ∩ boundaryLine '' {u | 0 ≤ u.val ∧ u.val ≤ ρ.val} =
        {d.second 0} := by
    intro ρ
    apply subset_antisymm
    · rintro y ⟨hy,⟨u,hu,rfl⟩⟩
      have hu0 : u.val = 0 := by
        by_contra hzero
        exact hBetaPositiveOutside u (lt_of_le_of_ne hu.1 (Ne.symm hzero))
          (hu.2.trans_lt ρ.property.2) hy
      have he : u = (⟨0,by norm_num⟩ : Icc (-1 : ℝ) 1) := Subtype.ext hu0
      simpa only [mem_singleton_iff,he] using hBoundaryZero
    · intro y hy
      have he : y = d.second 0 := mem_singleton_iff.mp hy
      rw [he]
      exact ⟨⟨1,d.boundary_one⟩,⟨⟨0,by norm_num⟩,⟨le_rfl,ρ.property.1.le⟩,
        hBoundaryZero⟩⟩
  let oldBoundaryPath : Path (d.first 0) (d.second 0) := {
    toContinuousMap := d.boundarySide
    source' := d.boundary_zero
    target' := d.boundary_one }
  let outgoingParam : Ioo (0 : ℝ) bound → C(Interval,Icc (-1 : ℝ) 1) := fun ρ =>
    ⟨fun t => ⟨ρ.val*t.val,by
      have hnonneg := mul_nonneg ρ.property.1.le t.property.1
      have hle := mul_le_of_le_one_right ρ.property.1.le t.property.2
      exact ⟨by linarith only [hnonneg],hle.trans (ρ.property.2.le.trans hboundOne.le)⟩⟩,
      by fun_prop⟩
  have hOutgoingParam : ∀ ρ, IsEmbedding (outgoingParam ρ) := by
    intro ρ
    apply ((outgoingParam ρ).continuous.isClosedEmbedding ?_).isEmbedding
    intro t u he
    have hh := congrArg Subtype.val he
    change ρ.val*t.val = ρ.val*u.val at hh
    exact Subtype.ext (mul_left_cancel₀ (ne_of_gt ρ.property.1) hh)
  have hOutgoingParamRange : ∀ ρ, range (outgoingParam ρ) =
      {u | 0 ≤ u.val ∧ u.val ≤ ρ.val} := by
    intro ρ
    ext u
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨mul_nonneg ρ.property.1.le t.property.1,
        mul_le_of_le_one_right ρ.property.1.le t.property.2⟩
    · intro hu
      let t : Interval := ⟨u.val/ρ.val,⟨div_nonneg hu.1 ρ.property.1.le,
        (div_le_one ρ.property.1).mpr hu.2⟩⟩
      refine ⟨t,Subtype.ext ?_⟩
      change ρ.val*(u.val/ρ.val) = u.val
      field_simp [ne_of_gt ρ.property.1]
  let outgoingPath : ∀ ρ : Ioo (0 : ℝ) bound, Path (d.second 0) (beta ρ) :=
    fun ρ => {
      toContinuousMap := boundaryLine.comp (outgoingParam ρ)
      source' := by
        change boundaryLine ((outgoingParam ρ) 0) = d.second 0
        have he : (outgoingParam ρ) 0 = (⟨0,by norm_num⟩ : Icc (-1 : ℝ) 1) := by
          apply Subtype.ext
          change ρ.val*(0 : ℝ) = 0
          exact mul_zero _
        rw [he,hBoundaryZero]
      target' := by
        change boundaryLine ((outgoingParam ρ) 1) = beta ρ
        congr 1
        apply Subtype.ext
        change ρ.val*(1 : ℝ) = ρ.val
        exact mul_one _ }
  have hOutgoingPath : ∀ ρ, IsEmbedding (outgoingPath ρ) := by
    intro ρ
    exact hBoundaryLine.comp (hOutgoingParam ρ)
  have hOutgoingPathRange : ∀ ρ, range (outgoingPath ρ) =
      boundaryLine '' {u | 0 ≤ u.val ∧ u.val ≤ ρ.val} := by
    intro ρ
    change range (boundaryLine ∘ outgoingParam ρ) = _
    rw [range_comp,hOutgoingParamRange]
  let boundaryExtension : Ioo (0 : ℝ) bound → C(Interval,↥F) := fun ρ =>
    (oldBoundaryPath.trans (outgoingPath ρ)).toContinuousMap
  have hBoundaryExtension : ∀ ρ, IsEmbedding (boundaryExtension ρ) := by
    intro ρ
    apply CurveComplex.isEmbedding_path_trans_of_inter_singleton_probe
      oldBoundaryPath (outgoingPath ρ) d.boundary_embedded (hOutgoingPath ρ)
    rw [hOutgoingPathRange]
    exact hBoundaryExtensionSeam ρ
  have hBoundaryExtensionZero : ∀ ρ, boundaryExtension ρ 0 = d.first 0 := by
    intro ρ
    exact (oldBoundaryPath.trans (outgoingPath ρ)).source
  have hBoundaryExtensionOne : ∀ ρ, boundaryExtension ρ 1 = beta ρ := by
    intro ρ
    exact (oldBoundaryPath.trans (outgoingPath ρ)).target
  have hBoundaryExtensionRange : ∀ ρ, range (boundaryExtension ρ) =
      range d.boundarySide ∪ boundaryLine '' {u | 0 ≤ u.val ∧ u.val ≤ ρ.val} := by
    intro ρ
    change range (oldBoundaryPath.trans (outgoingPath ρ)) = _
    rw [Path.trans_range,hOutgoingPathRange]
    rfl
  have hboundaryDisk : range d.boundarySide ⊆ range d.disk := by
    apply subset_trans (show range d.boundarySide ⊆
      range d.first ∪ range d.second ∪ range d.boundarySide from subset_union_right)
    rw [← d.boundary_image]
    exact image_subset_range _ _
  have hBoundaryExtensionBV : ∀ ρ, range (boundaryExtension ρ) ⊆
      {y : ↥F | y.val ∈ boundaryCircle} ∩ V := by
    intro ρ y hy
    rw [hBoundaryExtensionRange] at hy
    rcases hy with hy | hy
    · obtain ⟨t,rfl⟩ := hy
      exact ⟨d.boundary_in_B t,hdV (hboundaryDisk ⟨t,rfl⟩)⟩
    · obtain ⟨u,hu,rfl⟩ := hy
      apply hboundaryLocal
      exact ⟨u,by
        change |u.val| < bound
        rw [abs_of_nonneg hu.1]
        exact hu.2.trans_lt ρ.property.2,rfl⟩
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
  have hRadialContactUnique (a b z : Plane) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
      (hab : a ≠ b) (hza : z ∈ segment ℝ (0 : Plane) a)
      (hzb : z ∈ segment ℝ (0 : Plane) b) : z = 0 := by
    rw [segment_eq_image'] at hza hzb
    obtain ⟨t,ht,he⟩ := hza
    obtain ⟨s,hs,hf⟩ := hzb
    have hte : t • a = z := by simpa using he
    have hse : s • b = z := by simpa using hf
    have hts : t = s := by
      have hn := congrArg norm (hte.trans hse.symm)
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1,
        abs_of_nonneg hs.1,ha,hb,mul_one] using hn
    by_cases ht0 : t = 0
    · simpa [ht0] using hte.symm
    · have hab' : a = b := by
        have heq : t • a = t • b := hte.trans (hts ▸ hse.symm)
        have heq' := congrArg (fun y : Plane => t⁻¹ • y) heq
        simpa [smul_smul,ht0] using heq'
      exact (hab hab').elim
  have hFanContactUnique (p : ↥F) (W : IncidentFanWindow F f V p)
      (i j : incidentIndex f p) (hij : i.val ≠ j.val)
      (y : ↥F) (hy : y.val ∈ W.chart.source)
      (hyball : W.chart y.val ∈ Metric.closedBall (0 : Plane) 1)
      (hyi : y ∈ range (f i.val)) (hyj : y ∈ range (f j.val)) : y = p := by
    have hArm (k : incidentIndex f p) (hyk : y ∈ range (f k.val)) :
        ∃ β : Bool, W.chart y.val ∈ segment ℝ (0 : Plane)
          (incidentPorts f p W.chart W.left W.right (k,β)) := by
      rcases (hFanTrace p W k y hy hyball).mp hyk with hh | hh
      · refine ⟨false,?_⟩
        rwa [segment_symm ℝ _ (0 : Plane)] at hh
      · exact ⟨true,hh⟩
    obtain ⟨β,hβ⟩ := hArm i hyi
    obtain ⟨γ,hγ⟩ := hArm j hyj
    have hz : W.chart y.val = 0 := hRadialContactUnique _ _ _
      (by simpa only [Metric.mem_sphere,dist_zero_right] using W.ports_on_sphere (i,β))
      (by simpa only [Metric.mem_sphere,dist_zero_right] using W.ports_on_sphere (j,γ))
      (fun he => hij (congrArg (fun z : incidentIndex f p × Bool => z.1.val)
        (W.ports_injective he))) hβ hγ
    exact Subtype.ext (W.chart.injOn hy W.contact_in_source (hz.trans W.contact_zero.symm))
  have hFanShrinking (p : ↥F) (W : IncidentFanWindow F f V p)
      (U : Set S) (hU : IsOpen U) (hpU : p.val ∈ U) :
      ∃ η : ℝ, 0 < η ∧ η < 1 ∧
        Metric.closedBall (0 : Plane) η ⊆ W.chart.target ∧
        W.chart.symm '' Metric.closedBall (0 : Plane) η ⊆ U := by
    let Q := W.chart '' (W.chart.source ∩ U)
    have hQ : IsOpen Q := W.chart.isOpen_image_source_inter hU
    have hzero : (0 : Plane) ∈ Q := ⟨p.val,⟨W.contact_in_source,hpU⟩,W.contact_zero⟩
    obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hQ 0 hzero
    let η := min ρ 1 / 2
    have hη : 0 < η := half_pos (lt_min hρ zero_lt_one)
    have hηρ : η < ρ := by dsimp [η]; have := min_le_left ρ 1; linarith
    have hη1 : η < 1 := by dsimp [η]; have := min_le_right ρ 1; linarith
    have hηQ : Metric.closedBall (0 : Plane) η ⊆ Q :=
      (Metric.closedBall_subset_ball hηρ).trans hball
    refine ⟨η,hη,hη1,?_,?_⟩
    · intro z hz
      obtain ⟨y,hy,he⟩ := hηQ hz
      exact he ▸ W.chart.map_source hy.1
    · rintro y ⟨z,hz,rfl⟩
      obtain ⟨u,hu,he⟩ := hηQ hz
      rw [← he,W.chart.left_inv hu.1]
      exact hu.2
  have hEntryUnit0 : joint.cornerEntry ∈ Metric.closedBall (0 : Plane) 1 := by
    apply Metric.ball_subset_closedBall
    apply joint.corner_hull_in_unit (joint.capBound/2) (half_pos joint.capBound_pos)
      (half_lt_self joint.capBound_pos)
    apply subset_convexHull ℝ
    simp
  have hCornerB0 : d.first 1 ∈ range b := ⟨d.bFinish,hsecond1.symm.trans d.corner_eq.symm⟩
  have hEntryOthers : ∀ k : Option ι, k ≠ some w →
      d.second joint.guideEntryTime ∉ range (f k) := by
    intro k hk hyk
    have hcore : d.second joint.guideEntryTime ∈
        chartPull F joint.cornerFan.chart (Metric.closedBall (0 : Plane) 1) :=
      ⟨joint.cornerEntry_actual.1,joint.cornerEntry_actual.2 ▸ hEntryUnit0⟩
    by_cases hinc : d.first 1 ∈ range (f k)
    · have he := hFanContactUnique (d.first 1) joint.cornerFan ⟨k,hinc⟩
        ⟨some w,hCornerB0⟩ hk _ hcore.1 hcore.2 hyk
        (by rw [d.second_eq]; exact mem_range_self _)
      apply joint.cornerEntry_nonzero_height
      rw [← joint.cornerEntry_actual.2,he,joint.cornerFan.contact_zero]
      rfl
    · exact Set.disjoint_left.mp (joint.cornerFan.nonincident_clear k hinc) hcore hyk
  let entryFiber : C(Icc (-1 : ℝ) 1,↥F) :=
    guideStrip.comp ⟨fun u =>
      (CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish joint.guideEntryTime,u),
      by fun_prop⟩
  have hEntryFiberZero : entryFiber ⟨0,by norm_num⟩ = d.second joint.guideEntryTime := by
    change guideStrip (_,⟨0,by norm_num⟩) = _
    rw [hGuideCenterActual,d.second_eq]
  have hEntryAvoid : d.second joint.guideEntryTime ∉ outgoingObstacles := by
    intro hy
    obtain ⟨k,hk⟩ := mem_iUnion.mp hy
    exact hEntryOthers k.val k.property hk
  have hEntryZeroOpen : (⟨0,by norm_num⟩ : Icc (-1 : ℝ) 1) ∈
      entryFiber ⁻¹' outgoingObstaclesᶜ := by
    change entryFiber ⟨0,by norm_num⟩ ∉ outgoingObstacles
    rwa [hEntryFiberZero]
  obtain ⟨entryRadius,hEntryRadius,hEntryBall⟩ := Metric.isOpen_iff.mp
    (houtCompact.isClosed.isOpen_compl.preimage entryFiber.continuous)
    ⟨0,by norm_num⟩ hEntryZeroOpen
  -- One producer-owned positive cap width works over the complete common domain.
  let cornerWidth : ℝ := min bound (min joint.entryMargin (min (joint.capBound / joint.kappa) entryRadius)) / 2
  have hcw : 0 < cornerWidth := by
    exact half_pos (lt_min hbound (lt_min joint.entryMargin_pos
      (lt_min (div_pos joint.capBound_pos joint.kappa_pos) hEntryRadius)))
  have hcwbound : cornerWidth < bound := by
    dsimp [cornerWidth]
    have := min_le_left bound (min joint.entryMargin (min (joint.capBound / joint.kappa) entryRadius))
    linarith
  have hcwentry : cornerWidth < joint.entryMargin := by
    dsimp [cornerWidth]
    have hmin := (min_le_right bound (min joint.entryMargin (min (joint.capBound / joint.kappa) entryRadius))).trans
      (min_le_left joint.entryMargin (min (joint.capBound / joint.kappa) entryRadius))
    have := joint.entryMargin_pos
    linarith
  have hcwcap : cornerWidth < joint.capBound / joint.kappa := by
    dsimp [cornerWidth]
    have hmin := (min_le_right bound (min joint.entryMargin (min (joint.capBound / joint.kappa) entryRadius))).trans
      (min_le_right joint.entryMargin (min (joint.capBound / joint.kappa) entryRadius)) |>.trans
      (min_le_left (joint.capBound / joint.kappa) entryRadius)
    have := div_pos joint.capBound_pos joint.kappa_pos
    linarith
  have hcwRadius : cornerWidth < entryRadius := by
    dsimp [cornerWidth]
    have hmin := (min_le_right bound (min joint.entryMargin (min (joint.capBound / joint.kappa) entryRadius))).trans
      ((min_le_right joint.entryMargin (min (joint.capBound / joint.kappa) entryRadius)).trans
        (min_le_right (joint.capBound / joint.kappa) entryRadius))
    linarith only [hmin,hEntryRadius]
  let cornerEpsilon : ℝ := joint.kappa * cornerWidth
  have hce : 0 < cornerEpsilon := mul_pos joint.kappa_pos hcw
  have hcecap : cornerEpsilon < joint.capBound := by
    dsimp [cornerEpsilon]
    simpa [mul_comm] using (lt_div_iff₀ joint.kappa_pos).mp hcwcap
  let capSegment : Set Plane := segment ℝ (Plane.mk (-joint.cornerDelta) 0)
    (Plane.mk (joint.cornerEntry 0-cornerEpsilon) (joint.cornerEntry 1))
  have hCapHull : capSegment ⊆ regionalHalfCornerHull joint.cornerDelta joint.cornerEntry cornerEpsilon := by
    apply (convex_convexHull ℝ _).segment_subset
    · apply subset_convexHull ℝ
      simp [regionalHalfCornerHull]
    · apply subset_convexHull ℝ
      simp [regionalHalfCornerHull]
  have hCapOpen : capSegment ⊆ Metric.ball (0 : Plane) 1 :=
    hCapHull.trans (joint.corner_hull_in_unit cornerEpsilon hce hcecap)
  have hCapClosed : capSegment ⊆ Metric.closedBall (0 : Plane) 1 :=
    hCapOpen.trans Metric.ball_subset_closedBall
  have hCapTarget : capSegment ⊆ joint.cornerFan.chart.target :=
    hCapClosed.trans joint.cornerFan.disk_in_target
  obtain ⟨capForward,hCapForward,hCapForwardRange,hCapForwardZero,hCapForwardOne,hCapForwardFormula⟩ :=
    CurveComplex.actual_signed_chart_connector_arc joint.cornerFan.chart joint.cornerDelta
      (joint.cornerEntry 0-cornerEpsilon) (joint.cornerEntry 1)
      joint.cornerEntry_nonzero_height hCapTarget
  have hCapInF (t : Interval) : capForward t ∈ F := by
    have ht := (hCapForwardFormula t).1
    obtain ⟨y,hy,he⟩ := (joint.cornerFan.source_closure (subset_closure ht)).1
    exact he ▸ y.property
  let cap : C(Interval,↥F) :=
    ⟨fun t => ⟨capForward (unitInterval.symmHomeomorph t), hCapInF _⟩,
      (capForward.continuous.comp unitInterval.symmHomeomorph.continuous).subtype_mk _⟩
  have hCap : IsEmbedding cap := by
    apply (cap.continuous.isClosedEmbedding ?_).isEmbedding
    intro t s he
    apply unitInterval.symmHomeomorph.injective
    exact hCapForward.injective (congrArg Subtype.val he)
  have hCapRange : range cap = chartPull F joint.cornerFan.chart capSegment := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      refine ⟨(hCapForwardFormula _).1,?_⟩
      have ht : capForward (unitInterval.symmHomeomorph t) ∈ range capForward := mem_range_self _
      rw [hCapForwardRange] at ht
      obtain ⟨z,hz,he⟩ := ht
      change joint.cornerFan.chart (capForward _) ∈ capSegment
      rw [← he,joint.cornerFan.chart.right_inv (hCapTarget hz)]
      exact hz
    · intro hy
      obtain ⟨t,ht⟩ : y.val ∈ range capForward := by
        rw [hCapForwardRange]
        exact ⟨joint.cornerFan.chart y.val,hy.2,joint.cornerFan.chart.left_inv hy.1⟩
      refine ⟨unitInterval.symmHomeomorph.symm t,?_⟩
      apply Subtype.ext
      change capForward (unitInterval.symmHomeomorph (unitInterval.symmHomeomorph.symm t)) = y.val
      simpa using ht
  have hCapFormula (t : Interval) :
      let z := Plane.mk (-joint.cornerDelta+(1-t.val)*(joint.cornerEntry 0-cornerEpsilon+joint.cornerDelta))
        (joint.cornerEntry 1*(1-t.val))
      z ∈ joint.cornerFan.chart.target ∧ (cap t).val = joint.cornerFan.chart.symm z := by
    have hf := hCapForwardFormula (unitInterval.symmHomeomorph t)
    have he : joint.cornerFan.chart (cap t).val =
        Plane.mk (-joint.cornerDelta+(1-t.val)*(joint.cornerEntry 0-cornerEpsilon+joint.cornerDelta))
          (joint.cornerEntry 1*(1-t.val)) := by
      simpa only [cap,ContinuousMap.coe_mk,unitInterval.symmHomeomorph_apply,unitInterval.coe_symm_eq] using hf.2
    refine ⟨he ▸ joint.cornerFan.chart.map_source hf.1,?_⟩
    rw [← he]
    exact (joint.cornerFan.chart.left_inv hf.1).symm
  have hCapUnit : range cap ⊆ chartPull F joint.cornerFan.chart (Metric.closedBall (0 : Plane) 1) := by
    rw [hCapRange]
    exact fun _ hy => ⟨hy.1,hCapClosed hy.2⟩
  have hCapV : range cap ⊆ V := by
    intro y hy
    obtain ⟨z,hz,he⟩ := (joint.cornerFan.source_closure (subset_closure (hCapUnit hy).1)).1
    exact (Subtype.ext he) ▸ hz
  have hCapInterior : ∀ t, (cap t).val ∈ interior F := by
    intro t
    exact (joint.cornerFan.source_closure (subset_closure (hCapUnit (mem_range_self t)).1)).2
  have hCutSource : (a (joint.clock joint.cut)).val ∈ joint.cornerFan.chart.source ∧
      joint.cornerFan.chart (a (joint.clock joint.cut)).val = Plane.mk (-joint.cornerDelta) 0 := by
    have hf := joint.old_corner_transition joint.cut
      (joint.oldCornerWindow_padded ⟨joint.corner_before_cut.le,le_rfl⟩)
      ⟨0,by norm_num⟩ (by simpa using joint.oldCornerWidth_pos.le)
    rw [joint.oldStrip_center,joint.oldCornerX_cut] at hf
    simpa [a] using hf
  have hCapOne : cap 1 = a (joint.clock joint.cut) := by
    apply Subtype.ext
    change capForward (unitInterval.symmHomeomorph 1) = _
    rw [unitInterval.symmHomeomorph_apply,unitInterval.symm_one,hCapForwardZero]
    rw [← hCutSource.2]
    exact joint.cornerFan.chart.left_inv hCutSource.1
  let capWidth : Icc (-1 : ℝ) 1 := ⟨cornerWidth,by constructor <;> linarith [hcwbound,hboundOne]⟩
  have hJoinSource := joint.guide_entry_section capWidth hcw.le hcwentry.le
  have hCapZero : cap 0 = guideStrip
      (CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish joint.guideEntryTime,capWidth) := by
    apply Subtype.ext
    change capForward (unitInterval.symmHomeomorph 0) = _
    rw [unitInterval.symmHomeomorph_apply,unitInterval.symm_zero,hCapForwardOne]
    change joint.cornerFan.chart.symm (Plane.mk (joint.cornerEntry 0-cornerEpsilon) (joint.cornerEntry 1)) = _
    rw [← hJoinSource.2]
    exact joint.cornerFan.chart.left_inv hJoinSource.1
  have hCapZeroClear (k : Option ι) (hk : k ≠ some w) : cap 0 ∉ range (f k) := by
    intro hy
    have hn := hEntryBall (show capWidth ∈ Metric.ball (⟨0,by norm_num⟩ : Icc (-1 : ℝ) 1) entryRadius by
      simpa [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq,capWidth,abs_of_pos hcw] using hcwRadius)
    apply hn
    apply mem_iUnion.mpr
    refine ⟨⟨k,hk⟩,?_⟩
    rw [hCapZero] at hy
    exact hy
  have hCapOneClear (k : Option ι) (hk : k ≠ some v) : cap 1 ∉ range (f k) := by
    intro hy
    apply Set.disjoint_left.mp joint.padded_clear
      (show cap 1 ∈ a '' (joint.clock '' Ioc (joint.clock.symm d.aFinish) joint.cut) by
        exact ⟨joint.clock joint.cut,⟨joint.cut,⟨joint.corner_before_cut,le_rfl⟩,rfl⟩,hCapOne.symm⟩)
    exact mem_iUnion.mpr ⟨⟨k,hk⟩,hy⟩
  have hCapMeetA : range cap ∩ range a = {a (joint.clock joint.cut)} := by
    ext y
    constructor
    · rintro ⟨⟨t,rfl⟩,hy⟩
      have hcore := hCapUnit (mem_range_self t)
      have hcora : d.first 1 ∈ range a := ⟨d.aFinish,hfirst1.symm⟩
      have haxis := joint.corner_a_axis hcora
      have hz := (hFanAxis (d.first 1) joint.cornerFan ⟨some v,hcora⟩
        haxis.1 haxis.2 (cap t) hcore.1 hcore.2).mp hy
      have hf := hCapFormula t
      have hheight : joint.cornerFan.chart (cap t).val 1 = joint.cornerEntry 1*(1-t.val) := by
        rw [hf.2,joint.cornerFan.chart.right_inv hf.1]
        rfl
      have ht : t = 1 := by
        apply Subtype.ext
        have hs := (mul_eq_zero.mp (hheight.symm.trans hz)).resolve_left joint.cornerEntry_nonzero_height
        change t.val = 1
        linarith
      rw [ht,hCapOne]
      rfl
    · intro hy
      rw [mem_singleton_iff] at hy
      rw [hy]
      exact ⟨⟨1,hCapOne⟩,mem_range_self _⟩
  have hCapNonincident (k : Option ι) (hk : d.first 1 ∉ range (f k)) :
      Disjoint (range cap) (range (f k)) := by
    apply Set.disjoint_left.mpr
    intro y hy hyk
    exact Set.disjoint_left.mp (joint.cornerFan.nonincident_clear k hk) (hCapUnit hy) hyk
  have hEntryUnit : joint.cornerEntry ∈ Metric.closedBall (0 : Plane) 1 := by
    apply Metric.ball_subset_closedBall
    apply joint.corner_hull_in_unit cornerEpsilon hce hcecap
    apply subset_convexHull ℝ
    simp
  have hCornerB : d.first 1 ∈ range b := ⟨d.bFinish,hsecond1.symm.trans d.corner_eq.symm⟩
  let bIncident : incidentIndex f (d.first 1) := ⟨some w,hCornerB⟩
  let bLeft := incidentPorts f (d.first 1) joint.cornerFan.chart
    joint.cornerFan.left joint.cornerFan.right (bIncident,false)
  let bRight := incidentPorts f (d.first 1) joint.cornerFan.chart
    joint.cornerFan.left joint.cornerFan.right (bIncident,true)
  have hEntryB : joint.cornerEntry ∈ segment ℝ (0 : Plane) bLeft ∪ segment ℝ (0 : Plane) bRight := by
    have ht := (hFanTrace (d.first 1) joint.cornerFan bIncident (d.second joint.guideEntryTime)
      joint.cornerEntry_actual.1 (joint.cornerEntry_actual.2 ▸ hEntryUnit)).mp
      (by rw [d.second_eq]; exact mem_range_self _)
    rw [joint.cornerEntry_actual.2] at ht
    simpa only [bLeft,bRight,segment_symm ℝ _ (0 : Plane)] using ht
  have hBports : bLeft 1 * bRight 1 < 0 := joint.corner_selected_ports_opposite hCornerB
  have hPlanarCapB : Disjoint capSegment (segment ℝ (0 : Plane) bLeft ∪ segment ℝ (0 : Plane) bRight) := by
    rcases hEntryB with hl | hr
    · exact CurveComplex.actual_near_entering_ray_corner_avoid joint.cornerDelta cornerEpsilon
        joint.cornerDelta_pos hce joint.cornerEntry bLeft bRight hl
        joint.cornerEntry_nonzero_height hBports
    · rw [union_comm]
      exact CurveComplex.actual_near_entering_ray_corner_avoid
        joint.cornerDelta cornerEpsilon joint.cornerDelta_pos hce joint.cornerEntry bRight bLeft hr
        joint.cornerEntry_nonzero_height (by rw [mul_comm]; exact hBports)
  have hCapMissB : Disjoint (range cap) (range b) := by
    apply Set.disjoint_left.mpr
    intro y hy hyb
    have hys : y ∈ chartPull F joint.cornerFan.chart capSegment := hCapRange ▸ hy
    have ht := (hFanTrace (d.first 1) joint.cornerFan bIncident y hys.1 (hCapClosed hys.2)).mp hyb
    exact Set.disjoint_left.mp hPlanarCapB hys.2
      (by simpa only [bLeft,bRight,segment_symm ℝ _ (0 : Plane)] using ht)
  have hCapSubsingleton (k : Option ι) (hk : k ≠ some v) (hw : k ≠ some w) :
      (range cap ∩ range (f k)).Subsingleton := by
    by_cases hinc : d.first 1 ∈ range (f k)
    · let ki : incidentIndex f (d.first 1) := ⟨k,hinc⟩
      let l := incidentPorts f (d.first 1) joint.cornerFan.chart
        joint.cornerFan.left joint.cornerFan.right (ki,false)
      let r := incidentPorts f (d.first 1) joint.cornerFan.chart
        joint.cornerFan.left joint.cornerFan.right (ki,true)
      have hprod : l 1*r 1 < 0 := joint.corner_other_ports_opposite ki hk
      have hPlanar : (capSegment ∩ (segment ℝ (0 : Plane) l ∪ segment ℝ (0 : Plane) r)).Subsingleton := by
        rcases (mul_neg_iff.mp hprod) with ⟨hl,hr⟩ | ⟨hl,hr⟩
        · have hn := CurveComplex.actual_signed_corner_segment_counts
            (fun _ : Unit => l) (fun _ : Unit => r) (fun _ => hl) (fun _ => hr)
            joint.cornerDelta (joint.cornerEntry 0-cornerEpsilon) (joint.cornerEntry 1)
            joint.cornerDelta_pos joint.cornerEntry_nonzero_height ()
          exact (Set.ncard_le_one hn.1).mp hn.2
        · have hn := CurveComplex.actual_signed_corner_segment_counts
            (fun _ : Unit => r) (fun _ : Unit => l) (fun _ => hr) (fun _ => hl)
            joint.cornerDelta (joint.cornerEntry 0-cornerEpsilon) (joint.cornerEntry 1)
            joint.cornerDelta_pos joint.cornerEntry_nonzero_height ()
          rw [union_comm]
          exact (Set.ncard_le_one hn.1).mp hn.2
      intro y hy z hz
      have hyc : y ∈ chartPull F joint.cornerFan.chart capSegment := hCapRange ▸ hy.1
      have hzc : z ∈ chartPull F joint.cornerFan.chart capSegment := hCapRange ▸ hz.1
      have hyf := (hFanTrace (d.first 1) joint.cornerFan ki y hyc.1 (hCapClosed hyc.2)).mp hy.2
      have hzf := (hFanTrace (d.first 1) joint.cornerFan ki z hzc.1 (hCapClosed hzc.2)).mp hz.2
      have he := hPlanar ⟨hyc.2,by simpa only [l,r,segment_symm ℝ _ (0 : Plane)] using hyf⟩
        ⟨hzc.2,by simpa only [l,r,segment_symm ℝ _ (0 : Plane)] using hzf⟩
      exact Subtype.ext (joint.cornerFan.chart.injOn hyc.1 hzc.1 he)
    · intro y hy z hz
      exact (Set.disjoint_left.mp (hCapNonincident k hinc) hy.1 hy.2).elim
  have hCapMissDisk : Disjoint (range cap) (range d.disk) := by
    apply Set.disjoint_left.mpr
    intro y hy hyd
    have hyh : y ∈ chartPull F joint.cornerFan.chart
        (regionalHalfCornerHull joint.cornerDelta joint.cornerEntry cornerEpsilon) := by
      have hyc : y ∈ chartPull F joint.cornerFan.chart capSegment := hCapRange ▸ hy
      exact ⟨hyc.1,hCapHull hyc.2⟩
    have hyb : y ∈ d.second '' Icc joint.guideEntryTime (1 : Interval) := by
      rw [← joint.corner_carrier_disk_inter cornerEpsilon hce hcecap]
      exact ⟨hyh,hyd⟩
    obtain ⟨t,ht,he⟩ := hyb
    exact Set.disjoint_left.mp hCapMissB hy (he ▸ (by rw [d.second_eq]; exact mem_range_self _))
  have hCapGuideCarrier : range cap ∩ regionalHalfJointGuideCarrier F guideStrip d.bStart
      (CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish joint.guideEntryTime)
      joint.entryMargin = {cap 0} := by
    ext y
    constructor
    · rintro ⟨⟨t,rfl⟩,hyg⟩
      have hyc : cap t ∈ chartPull F joint.cornerFan.chart capSegment := hCapRange ▸ mem_range_self t
      have hyh : cap t ∈ chartPull F joint.cornerFan.chart
          (regionalHalfCornerHull joint.cornerDelta joint.cornerEntry cornerEpsilon) := ⟨hyc.1,hCapHull hyc.2⟩
      have hSection : cap t ∈ guideStrip '' {z | z.1 =
          CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish joint.guideEntryTime ∧
          0 ≤ z.2.val ∧ z.2.val ≤ cornerEpsilon / joint.kappa} := by
        rw [← joint.guide_corner_carrier_inter cornerEpsilon hce hcecap]
        exact ⟨hyg,hyh⟩
      obtain ⟨z,hz,he⟩ := hSection
      have hzEntry : z.2.val ≤ joint.entryMargin := by
        have hc : cornerEpsilon / joint.kappa = cornerWidth := by
          simp [cornerEpsilon,ne_of_gt joint.kappa_pos]
        exact hz.2.2.trans (hc ▸ hcwentry.le)
      have hsection := joint.guide_entry_section z.2 hz.2.1 hzEntry
      have hheight : joint.cornerFan.chart (cap t).val 1 = joint.cornerEntry 1 := by
        rw [← he]
        change joint.cornerFan.chart (guideStrip (z.1,z.2)).val 1 = joint.cornerEntry 1
        rw [hz.1]
        have ht := congrArg (fun p : Plane => p 1) hsection.2
        exact ht
      have hf := hCapFormula t
      rw [hf.2,joint.cornerFan.chart.right_inv hf.1] at hheight
      change joint.cornerEntry 1*(1-t.val) = joint.cornerEntry 1 at hheight
      have ht : t = 0 := by
        apply Subtype.ext
        change t.val = 0
        have hs : 1-t.val = 1 := mul_left_cancel₀ joint.cornerEntry_nonzero_height
          (by simpa only [mul_one] using hheight)
        linarith only [hs]
      rw [ht]
      rfl
    · intro hy
      rw [mem_singleton_iff] at hy
      rw [hy]
      refine ⟨mem_range_self 0,?_⟩
      rw [hCapZero]
      refine ⟨(_,capWidth),⟨?_,hcw.le,hcwentry.le⟩,rfl⟩
      simp only [mem_Icc]
      exact ⟨min_le_right _ _,le_max_right _ _⟩
  -- All geometric sites on the original guiding side, with observer none retained.
  let P : Set ↥F := (range d.second \ {d.first 1}) ∩
    {p | ∃ k : Option ι, k ≠ some w ∧ p ∈ range (f k)}
  have hSecondDisk : range d.second ⊆ range d.disk := by
    intro y hy
    exact (d.whole_second.symm ▸ hy).1
  have hSecondWhole : range d.second ⊆ range b := by
    intro y hy
    exact (d.whole_second.symm ▸ hy).2
  have hPfan : P ⊆ fan.events := by
    intro y hy
    rw [fan.events_exact]
    refine ⟨hdV (hSecondDisk hy.1.1),Or.inr hy.1.1,some w,by simp,?_⟩
    obtain ⟨k,hk,hyk⟩ := hy.2
    exact ⟨k,Ne.symm hk,hSecondWhole hy.1.1,hyk⟩
  have hPfinite : P.Finite := fan.events_finite.subset hPfan
  have hPselectedClear : Disjoint P (range a) := by
    apply Set.disjoint_left.mpr
    intro y hy hya
    have hyfirst : y ∈ range d.first := d.whole_first ▸ ⟨hSecondDisk hy.1.1,hya⟩
    apply hy.1.2
    exact d.sides_inter ▸ ⟨hyfirst,hy.1.1⟩
  have hTailUnit : d.second '' Icc joint.guideEntryTime (1 : Interval) ⊆
      chartPull F joint.cornerFan.chart (Metric.closedBall (0 : Plane) 1) := by
    rw [← joint.corner_b_axis_segment]
    intro y hy
    exact ⟨hy.1,(convex_closedBall (0 : Plane) 1).segment_subset
      (by simp) hEntryUnit hy.2⟩
  have hPTailClear : Disjoint P (d.second '' Icc joint.guideEntryTime (1 : Interval)) := by
    apply Set.disjoint_left.mpr
    intro y hy hyt
    have hcore := hTailUnit hyt
    obtain ⟨k,hk,hyk⟩ := hy.2
    by_cases hinc : d.first 1 ∈ range (f k)
    · have he := hFanContactUnique (d.first 1) joint.cornerFan ⟨k,hinc⟩
        bIncident hk y hcore.1 hcore.2 hyk (hSecondWhole hy.1.1)
      apply hy.1.2
      rw [he]
      exact mem_singleton _
    · exact Set.disjoint_left.mp (joint.cornerFan.nonincident_clear k hinc) hcore hyk
  let pTime (p : ↥P) : Interval := Classical.choose p.property.1.1
  have hpTime (p : ↥P) : d.second (pTime p) = p.val := Classical.choose_spec p.property.1.1
  have hpTimeInjective : Function.Injective pTime := by
    intro p q he
    apply Subtype.ext
    exact (hpTime p).symm.trans (he ▸ hpTime q)
  have hpTimeBounds (p : ↥P) : pTime p ∈ Ioo (0 : Interval) joint.guideEntryTime := by
    constructor
    · apply lt_of_le_of_ne (unitInterval.nonneg _)
      intro he
      obtain ⟨k,hk,hpk⟩ := p.property.2
      apply hboundaryOthers k hk
      have ht : pTime p = 0 := Subtype.ext he.symm
      rw [← hpTime p,ht] at hpk
      exact hpk
    · by_contra hle
      have ht : p.val ∈ d.second '' Icc joint.guideEntryTime (1 : Interval) :=
        ⟨pTime p,⟨le_of_not_gt hle,unitInterval.le_one _⟩,hpTime p⟩
      exact Set.disjoint_left.mp hPTailClear p.property ht
  have hPThird (p : ↥P) : ∃ k : Option ι, k ≠ some v ∧ k ≠ some w ∧ p.val ∈ range (f k) := by
    obtain ⟨k,hk,hpk⟩ := p.property.2
    refine ⟨k,?_,hk,hpk⟩
    intro he
    rw [he] at hpk
    exact Set.disjoint_left.mp hPselectedClear p.property hpk
  letI : Fintype ↥P := hPfinite.fintype
  letI : LinearOrder ↥P := LinearOrder.lift' pTime hpTimeInjective
  let eventCount : ℕ := Fintype.card ↥P
  let eventLabel : Fin eventCount ≃ ↥P := (Fintype.orderIsoFinOfCardEq ↥P rfl).toEquiv
  have hEventLabelOrder (i j : Fin eventCount) (hij : i < j) :
      pTime (eventLabel i) < pTime (eventLabel j) :=
    (Fintype.orderIsoFinOfCardEq ↥P rfl).strictMono hij
  have hEventAxisFan (p : ↥P) :
      ∃ W : IncidentFanWindow F f V p.val,
        chartPull F W.chart (Metric.closedBall (0 : Plane) 1) ⊆
          chartPull F (fan.window ⟨p.val,hPfan p.property⟩).chart (Metric.ball (0 : Plane) 1) ∧
        (∀ h : p.val ∈ range b,
          incidentPorts f p.val W.chart W.left W.right (⟨some w,h⟩,false) 1 = 0 ∧
          incidentPorts f p.val W.chart W.left W.right (⟨some w,h⟩,true) 1 = 0) ∧
        ∀ j : incidentIndex f p.val, j.val ≠ some w →
          incidentPorts f p.val W.chart W.left W.right (j,false) 1 *
          incidentPorts f p.val W.chart W.left W.right (j,true) 1 < 0 := by
    obtain ⟨W,hW,haxis0,haxis1,hopp⟩ := fan.selected_axis_fans
      ⟨p.val,hPfan p.property⟩ (some w) (by simp) (hSecondWhole p.property.1.1)
    refine ⟨W,hW,fun _ => ⟨haxis0,haxis1⟩,?_⟩
    intro j hj
    rcases hopp j hj with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · exact mul_neg_of_pos_of_neg hl hr
    · exact mul_neg_of_neg_of_pos hl hr
  obtain ⟨tailParam,hTailParam,hTailParamZero,hTailParamOne,hTailParamRange,hTailParamValue⟩ :=
    CurveComplex.source_affine_subinterval joint.cut (1 : Interval) joint.cut_interior.2
  have hTailParamFormula (t : Interval) : tailParam t =
      CurveComplex.BranchedDoubleCover.intervalAffine joint.cut 1 t := by
    apply Subtype.ext
    rw [hTailParamValue]
    simp only [CurveComplex.BranchedDoubleCover.intervalAffine,Subtype.coe_mk]
    ring
  let retained : C(Interval,↥F) := a.comp
    (⟨joint.clock,joint.clock.continuous⟩ : C(Interval,Interval)) |>.comp tailParam
  have hRetained : IsEmbedding retained :=
    (r v).val.property.1.comp (joint.clock.isEmbedding.comp hTailParam)
  have hRetainedFormula (t : Interval) : retained t =
      a (joint.clock (CurveComplex.BranchedDoubleCover.intervalAffine joint.cut 1 t)) := by
    change a (joint.clock (tailParam t)) = _
    rw [hTailParamFormula]
  have hRetainedZero : retained 0 = cap 1 := by
    change a (joint.clock (tailParam 0)) = cap 1
    rw [hTailParamZero,hCapOne]
  have hRetainedOne : retained 1 = a (joint.clock 1) := by
    change a (joint.clock (tailParam 1)) = _
    rw [hTailParamOne]
  have hRetainedRange : range retained = a '' (joint.clock '' Icc joint.cut (1 : Interval)) := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨joint.clock (tailParam t),⟨tailParam t,hTailParamRange ▸ mem_range_self t,rfl⟩,rfl⟩
    · rintro ⟨s,⟨t,ht,rfl⟩,rfl⟩
      obtain ⟨u,hu⟩ := hTailParamRange.symm ▸ ht
      exact ⟨u,congrArg (fun t => a (joint.clock t)) hu⟩
  have hRetainedOld : range retained ⊆ range a \ range d.first :=
    hRetainedRange ▸ joint.retained_tail
  have hCapRetainedInter : range cap ∩ range retained = {cap 1} := by
    ext y
    constructor
    · rintro ⟨hy,hrt⟩
      have he : y = a (joint.clock joint.cut) := mem_singleton_iff.mp
        (hCapMeetA ▸ ⟨hy,(hRetainedOld hrt).1⟩)
      rw [he,hCapOne]
      rfl
    · intro hy
      rw [mem_singleton_iff] at hy
      rw [hy]
      exact ⟨mem_range_self 1,⟨0,hRetainedZero⟩⟩
  let capPath : Path (cap 0) (cap 1) := ⟨cap,rfl,rfl⟩
  let retainedPath : Path (cap 1) (a (joint.clock 1)) := ⟨retained,hRetainedZero,hRetainedOne⟩
  let suffix : C(Interval,↥F) := (capPath.trans retainedPath).toContinuousMap
  have hSuffix : IsEmbedding suffix :=
    CurveComplex.isEmbedding_path_trans_of_inter_singleton_probe capPath retainedPath
      hCap hRetained hCapRetainedInter
  have hSuffixZero : suffix 0 = cap 0 := (capPath.trans retainedPath).source
  have hSuffixOne : suffix 1 = a (joint.clock 1) := (capPath.trans retainedPath).target
  have hSuffixRange : range suffix = range cap ∪ range retained := Path.trans_range _ _
  have hSuffixCornerRemoved : d.first 1 ∉ range suffix := by
    rw [hSuffixRange]
    rintro (hc | ht)
    · have hca : d.first 1 ∈ range a := ⟨d.aFinish,hfirst1.symm⟩
      have he : d.first 1 = a (joint.clock joint.cut) :=
        mem_singleton_iff.mp (hCapMeetA ▸ ⟨hc,hca⟩)
      have haeq : joint.clock (joint.clock.symm d.aFinish) = joint.clock joint.cut :=
        (joint.clock.apply_symm_apply d.aFinish).trans
          ((r v).val.property.1.injective (hfirst1.symm.trans he))
      exact joint.corner_before_cut.ne (joint.clock.injective haeq)
    · exact (hRetainedOld ht).2 (mem_range_self 1)
  have hOldContactsFinite (k : Option ι) (hk : k ≠ some v) :
      (range a ∩ range (f k)).Finite := by
    cases k with
    | none =>
      change (range a ∩ range α.val.val).Finite
      rw [inter_comm]
      exact hinv.2.2.2.2 v
    | some j =>
      exact hinv.1 v j (fun he => hk (congrArg some he.symm))
  have hSuffixContactsFinite (k : Option ι) (hk : k ≠ some v) (hw : k ≠ some w) :
      (range suffix ∩ range (f k)).Finite := by
    rw [hSuffixRange,union_inter_distrib_right]
    exact (hCapSubsingleton k hk hw).finite.union
      ((hOldContactsFinite k hk).subset (fun _ hy => ⟨(hRetainedOld hy.1).1,hy.2⟩))
  have hCapChargeCount (k : Option ι) (hk : k ≠ some v) (hw : k ≠ some w) :
      (range cap ∩ range (f k)).ncard ≤ ({d.first 1} ∩ range (f k)).ncard := by
    by_cases hc : d.first 1 ∈ range (f k)
    · have he : ({d.first 1} ∩ range (f k)) = {d.first 1} := by
        exact singleton_inter_of_mem hc
      rw [he,ncard_singleton]
      exact (ncard_le_one (hCapSubsingleton k hk hw).finite).mpr (hCapSubsingleton k hk hw)
    · have he : range cap ∩ range (f k) = ∅ :=
        Set.disjoint_iff_inter_eq_empty.mp (hCapNonincident k hc)
      rw [he,ncard_empty]
      exact Nat.zero_le _
  have hSuffixChargeCount (k : Option ι) (hk : k ≠ some v) (hw : k ≠ some w) :
      (range suffix ∩ range (f k)).ncard ≤
        ((range a \ range d.first) ∩ range (f k)).ncard +
        ({d.first 1} ∩ range (f k)).ncard := by
    have htail : (range retained ∩ range (f k)).ncard ≤
        ((range a \ range d.first) ∩ range (f k)).ncard :=
      ncard_le_ncard (fun _ hy => ⟨hRetainedOld hy.1,hy.2⟩)
        ((hOldContactsFinite k hk).subset (fun _ hy => ⟨hy.1.1,hy.2⟩))
    rw [hSuffixRange,union_inter_distrib_right]
    calc
      _ ≤ (range cap ∩ range (f k)).ncard + (range retained ∩ range (f k)).ncard := ncard_union_le _ _
      _ ≤ ({d.first 1} ∩ range (f k)).ncard +
          ((range a \ range d.first) ∩ range (f k)).ncard := Nat.add_le_add (hCapChargeCount k hk hw) htail
      _ = _ := Nat.add_comm _ _
  have hSuffixSelectedSubset : range suffix ∩ range b ⊆
      (range a ∩ range b) \ {d.first 1} := by
    intro y hy
    have hys : y ∈ range cap ∪ range retained := hSuffixRange ▸ hy.1
    rcases hys with hc | ht
    · exact (Set.disjoint_left.mp hCapMissB hc hy.2).elim
    · refine ⟨⟨(hRetainedOld ht).1,hy.2⟩,?_⟩
      intro he
      exact (hRetainedOld ht).2 ((mem_singleton_iff.mp he) ▸ mem_range_self 1)
  have hSuffixSelectedCountDrop : (range suffix ∩ range b).ncard + 1 ≤
      (range a ∩ range b).ncard := by
    have hfin : (range a ∩ range b).Finite := hinv.1 v w hvw
    have hcorner : d.first 1 ∈ range a ∩ range b :=
      ⟨⟨d.aFinish,hfirst1.symm⟩,hCornerB⟩
    calc
      _ ≤ ((range a ∩ range b) \ {d.first 1}).ncard + 1 :=
        Nat.add_le_add_right (ncard_le_ncard hSuffixSelectedSubset hfin.sdiff) 1
      _ = _ := ncard_sdiff_singleton_add_one hcorner hfin
  have hCapObserverZero : α.val.val 0 ∉ range cap := by
    rintro ⟨t,ht⟩
    have hf := hCapInterior t
    have hfront := hBF α.val.property.2.1
    rw [ht] at hf
    exact hfront.2 hf
  have hCapObserverOne : α.val.val 1 ∉ range cap := by
    rintro ⟨t,ht⟩
    have hf := hCapInterior t
    have hfront := hBF α.val.property.2.2.1
    rw [ht] at hf
    exact hfront.2 hf
  have hSuffixObserverZero : α.val.val 0 ∉ range suffix := by
    rw [hSuffixRange]
    rintro (hc | ht)
    · exact hCapObserverZero hc
    · exact hinv.2.2.1 v (hRetainedOld ht).1
  have hSuffixObserverOne : α.val.val 1 ∉ range suffix := by
    rw [hSuffixRange]
    rintro (hc | ht)
    · exact hCapObserverOne hc
    · exact hinv.2.2.2.1 v (hRetainedOld ht).1
  have hCapContactIncident (k : Option ι) (y : ↥(range cap ∩ range (f k))) :
      d.first 1 ∈ range (f k) := by
    by_contra hk
    exact Set.disjoint_left.mp (hCapNonincident k hk) y.property.1 y.property.2
  let capCharge (k : Option ι) : ↥(range cap ∩ range (f k)) →
      ↥({d.first 1} ∩ range (f k)) := fun y =>
    ⟨d.first 1,mem_singleton _,hCapContactIncident k y⟩
  have hCapChargeInjective (k : Option ι) (hk : k ≠ some v) (hw : k ≠ some w) :
      Function.Injective (capCharge k) := by
    intro y z _
    exact Subtype.ext (hCapSubsingleton k hk hw y.property z.property)
  have hSuffixCapContact (k : Option ι) (y : ↥(range suffix ∩ range (f k)))
      (hy : y.val ∉ range retained) : y.val ∈ range cap := by
    have hh : y.val ∈ range cap ∪ range retained := by
      rw [← hSuffixRange]
      exact y.property.1
    exact hh.resolve_right hy
  let suffixCharge (k : Option ι) : ↥(range suffix ∩ range (f k)) →
      (↥((range d.second \ {d.first 1}) ∩ range (f k)) ⊕
        ↥((range a \ range d.first) ∩ range (f k))) ⊕
        ↥({d.first 1} ∩ range (f k)) := fun y =>
    if hy : y.val ∈ range retained then
      Sum.inl (Sum.inr ⟨y.val,hRetainedOld hy,y.property.2⟩)
    else Sum.inr (capCharge k ⟨y.val,hSuffixCapContact k y hy,y.property.2⟩)
  have hSuffixChargeInjective (k : Option ι) (hk : k ≠ some v) (hw : k ≠ some w) :
      Function.Injective (suffixCharge k) := by
    intro y z he
    dsimp only [suffixCharge] at he
    by_cases hy : y.val ∈ range retained
    · by_cases hz : z.val ∈ range retained
      · rw [dif_pos hy,dif_pos hz] at he
        have he1 := Sum.inl.inj he
        have he2 := Sum.inr.inj he1
        have hev := congrArg
          (fun u : ↥((range a \ range d.first) ∩ range (f k)) => u.val) he2
        exact Subtype.ext hev
      · rw [dif_pos hy,dif_neg hz] at he
        cases he
    · by_cases hz : z.val ∈ range retained
      · rw [dif_neg hy,dif_pos hz] at he
        cases he
      · exact Subtype.ext (hCapSubsingleton k hk hw
          ⟨hSuffixCapContact k y hy,y.property.2⟩
          ⟨hSuffixCapContact k z hz,z.property.2⟩)
  have hGuideContactsFinite (k : Option ι) (hw : k ≠ some w) :
      ((range d.second \ {d.first 1}) ∩ range (f k)).Finite := by
    have hwhole : (range b ∩ range (f k)).Finite := by
      cases k with
      | none =>
        change (range b ∩ range α.val.val).Finite
        rw [inter_comm]
        exact hinv.2.2.2.2 w
      | some j =>
        exact hinv.1 w j (fun he => hw (congrArg some he.symm))
    exact hwhole.subset (fun _ hy => ⟨hSecondWhole hy.1.1,hy.2⟩)
  -- This finite-set injection is independent of how the actual rails are built.
  -- Its geometric hypotheses are local conclusions to be paid by those rails.
  have hFiniteEventCharge
      (patch : ↥P → Set ↥F)
      (hsingle : ∀ p k, k ≠ some v → k ≠ some w →
        (patch p ∩ range (f k)).Subsingleton)
      (hclear : ∀ p k, p.val ∉ range (f k) → Disjoint (patch p) (range (f k)))
      (k : Option ι) (hk : k ≠ some v) (hw : k ≠ some w) :
      ∃ charge : ↥((⋃ p : ↥P, patch p) ∩ range (f k)) →
          ↥((range d.second \ {d.first 1}) ∩ range (f k)),
        Function.Injective charge ∧
        ((⋃ p : ↥P, patch p) ∩ range (f k)).Finite ∧
        ((⋃ p : ↥P, patch p) ∩ range (f k)).ncard ≤
          ((range d.second \ {d.first 1}) ∩ range (f k)).ncard := by
    let Y : Set ↥F := (⋃ p : ↥P, patch p) ∩ range (f k)
    let chosen (y : ↥Y) : ↥P := Classical.choose (mem_iUnion.mp y.property.1)
    have hchosen (y : ↥Y) : y.val ∈ patch (chosen y) :=
      Classical.choose_spec (mem_iUnion.mp y.property.1)
    have horigin (y : ↥Y) : (chosen y).val ∈ range (f k) := by
      by_contra hn
      exact Set.disjoint_left.mp (hclear (chosen y) k hn) (hchosen y) y.property.2
    let charge : ↥Y → ↥((range d.second \ {d.first 1}) ∩ range (f k)) :=
      fun y => ⟨(chosen y).val,(chosen y).property.1,horigin y⟩
    have hinj : Function.Injective charge := by
      intro y z he
      have hv := congrArg
        (fun q : ↥((range d.second \ {d.first 1}) ∩ range (f k)) => q.val) he
      have hp : chosen y = chosen z := Subtype.ext hv
      apply Subtype.ext
      apply hsingle (chosen y) k hk hw
      · exact ⟨hchosen y,y.property.2⟩
      · exact ⟨hp.symm ▸ hchosen z,z.property.2⟩
    letI : Finite ↥((range d.second \ {d.first 1}) ∩ range (f k)) :=
      (hGuideContactsFinite k hw).to_subtype
    letI : Finite ↥Y := Finite.of_injective charge hinj
    refine ⟨charge,hinj,Set.toFinite Y,?_⟩
    rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective charge hinj
  have hSuffixChargeNotGuiding (k : Option ι)
      (y : ↥(range suffix ∩ range (f k)))
      (z : ↥((range d.second \ {d.first 1}) ∩ range (f k))) :
      suffixCharge k y ≠ Sum.inl (Sum.inl z) := by
    dsimp only [suffixCharge]
    split_ifs <;> simp
  -- Generic finite-set assembly: its patch conclusions must still come from
  -- the actual geometric rails. No such conclusions are inputs to this theorem.
  have hContactAssembly
      (patch : ↥P → Set ↥F)
      (hsingle : ∀ p k, k ≠ some v → k ≠ some w →
        (patch p ∩ range (f k)).Subsingleton)
      (hclear : ∀ p k, p.val ∉ range (f k) → Disjoint (patch p) (range (f k)))
      (gaps : Set ↥F)
      (hgap : ∀ k, k ≠ some v → Disjoint gaps (range (f k)))
      (k : Option ι) (hk : k ≠ some v) (hw : k ≠ some w) :
      ∃ charge : ↥(((⋃ p : ↥P, patch p) ∪ gaps ∪ range suffix) ∩ range (f k)) →
          (↥((range d.second \ {d.first 1}) ∩ range (f k)) ⊕
            ↥((range a \ range d.first) ∩ range (f k))) ⊕
            ↥({d.first 1} ∩ range (f k)),
        Function.Injective charge ∧
        (((⋃ p : ↥P, patch p) ∪ gaps ∪ range suffix) ∩ range (f k)).Finite ∧
        (((⋃ p : ↥P, patch p) ∪ gaps ∪ range suffix) ∩ range (f k)).ncard ≤
          ((range d.second \ {d.first 1}) ∩ range (f k)).ncard +
          (((range a \ range d.first) ∩ range (f k)).ncard +
            ({d.first 1} ∩ range (f k)).ncard) := by
    obtain ⟨eventCharge,hEventCharge,hEventFinite,hEventBound⟩ :=
      hFiniteEventCharge patch hsingle hclear k hk hw
    let U : Set ↥F := ⋃ p : ↥P, patch p
    let Y : Set ↥F := (U ∪ gaps ∪ range suffix) ∩ range (f k)
    have houtside (y : ↥Y) (hy : y.val ∉ U) : y.val ∈ range suffix := by
      rcases y.property.1 with (hu | hg) | hs
      · exact (hy hu).elim
      · exact (Set.disjoint_left.mp (hgap k hk) hg y.property.2).elim
      · exact hs
    let charge : ↥Y →
        (↥((range d.second \ {d.first 1}) ∩ range (f k)) ⊕
          ↥((range a \ range d.first) ∩ range (f k))) ⊕
          ↥({d.first 1} ∩ range (f k)) := fun y =>
      if hy : y.val ∈ U then Sum.inl (Sum.inl (eventCharge ⟨y.val,hy,y.property.2⟩))
      else suffixCharge k ⟨y.val,houtside y hy,y.property.2⟩
    have hinj : Function.Injective charge := by
      intro y z he
      dsimp only [charge] at he
      by_cases hy : y.val ∈ U
      · by_cases hz : z.val ∈ U
        · rw [dite_eq_left hy,dite_eq_left hz] at he
          have he1 := Sum.inl.inj he
          have he2 := Sum.inl.inj he1
          have hh := hEventCharge he2
          have hv := congrArg (fun q : ↥(U ∩ range (f k)) => q.val) hh
          exact Subtype.ext hv
        · rw [dite_eq_left hy,dite_eq_right hz] at he
          exact (hSuffixChargeNotGuiding k ⟨z.val,houtside z hz,z.property.2⟩
            (eventCharge ⟨y.val,hy,y.property.2⟩) he.symm).elim
      · by_cases hz : z.val ∈ U
        · rw [dite_eq_right hy,dite_eq_left hz] at he
          exact (hSuffixChargeNotGuiding k ⟨y.val,houtside y hy,y.property.2⟩
            (eventCharge ⟨z.val,hz,z.property.2⟩) he).elim
        · rw [dite_eq_right hy,dite_eq_right hz] at he
          have hh := hSuffixChargeInjective k hk hw he
          have hv := congrArg (fun q : ↥(range suffix ∩ range (f k)) => q.val) hh
          exact Subtype.ext hv
    letI : Finite ↥((range d.second \ {d.first 1}) ∩ range (f k)) :=
      (hGuideContactsFinite k hw).to_subtype
    letI : Finite ↥((range a \ range d.first) ∩ range (f k)) :=
      ((hOldContactsFinite k hk).subset (fun _ hy => ⟨hy.1.1,hy.2⟩)).to_subtype
    letI : Finite ↥({d.first 1} ∩ range (f k)) :=
      ((finite_singleton (d.first 1)).subset inter_subset_left).to_subtype
    letI : Finite ↥Y := Finite.of_injective charge hinj
    refine ⟨charge,hinj,Set.toFinite Y,?_⟩
    have hle := Nat.card_le_card_of_injective charge hinj
    simpa only [Nat.card_sum,Nat.card_coe_set_eq,Nat.add_assoc] using hle
  have hSelectedContactAssembly (initialTrace : Set ↥F) (hp : Disjoint initialTrace (range b)) :
      ((initialTrace ∪ range suffix) ∩ range b).Finite ∧
      (initialTrace ∪ range suffix) ∩ range b ⊆ (range a ∩ range b) \ {d.first 1} ∧
      ((initialTrace ∪ range suffix) ∩ range b).ncard + 1 ≤ (range a ∩ range b).ncard := by
    have he : (initialTrace ∪ range suffix) ∩ range b = range suffix ∩ range b := by
      rw [union_inter_distrib_right,Set.disjoint_iff_inter_eq_empty.mp hp,empty_union]
    rw [he]
    exact ⟨(hinv.1 v w hvw).sdiff.subset hSuffixSelectedSubset,
      hSuffixSelectedSubset,hSuffixSelectedCountDrop⟩
  -- G0: actual times on b and on the original oriented guide clock.
  let actualEntry : Interval := CurveComplex.BranchedDoubleCover.intervalAffine
    d.bStart d.bFinish joint.guideEntryTime
  let eventRawTime (p : ↥P) : Interval :=
    CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish (pTime p)
  let orientedAffine (t : Interval) : Interval := joint.guideClock.symm
    (CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish t)
  let eventOrientedTime (p : ↥P) : Interval := orientedAffine (pTime p)
  let orientedEntry : Interval := orientedAffine joint.guideEntryTime
  have hRawCenter (p : ↥P) : b (eventRawTime p) = p.val :=
    (d.second_eq (pTime p)).symm.trans (hpTime p)
  have hRawInjective : Function.Injective eventRawTime := by
    intro p q he
    apply Subtype.ext
    exact (hRawCenter p).symm.trans ((congrArg b he).trans (hRawCenter q))
  have hOrientedAffine : StrictMono orientedAffine := by
    rcases joint.guideClock_identity_or_reverse with hc | hc
    · have hs : d.bStart = 0 := by simpa [hc] using joint.guideClock_start.symm
      have hfin : 0 < d.bFinish.val := by
        have hn : d.bFinish.val ≠ 0 := by
          intro he
          apply d.b_distinct
          rw [hs]
          exact Subtype.ext he.symm
        exact lt_of_le_of_ne d.bFinish.property.1 (Ne.symm hn)
      intro t u htu
      dsimp only [orientedAffine]
      rw [hc]
      change (1-t.val)*d.bStart.val+t.val*d.bFinish.val <
        (1-u.val)*d.bStart.val+u.val*d.bFinish.val
      have htuR : t.val < u.val := htu
      rw [hs]
      norm_num
      nlinarith [mul_pos (sub_pos.mpr htuR) hfin]
    · have hs : d.bStart = 1 := by simpa [hc] using joint.guideClock_start.symm
      have hfin : d.bFinish.val < 1 := by
        have hn : d.bFinish.val ≠ 1 := by
          intro he
          apply d.b_distinct
          rw [hs]
          exact Subtype.ext he.symm
        exact lt_of_le_of_ne d.bFinish.property.2 hn
      intro t u htu
      dsimp only [orientedAffine]
      rw [hc]
      change 1-((1-t.val)*d.bStart.val+t.val*d.bFinish.val) <
        1-((1-u.val)*d.bStart.val+u.val*d.bFinish.val)
      have htuR : t.val < u.val := htu
      rw [hs]
      norm_num
      nlinarith [mul_pos (sub_pos.mpr htuR) (sub_pos.mpr hfin)]
  have hOrientedZero : orientedAffine 0 = 0 := by
    dsimp only [orientedAffine]
    have hz : CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish 0 =
        d.bStart := by apply Subtype.ext; simp [CurveComplex.BranchedDoubleCover.intervalAffine]
    rw [hz,← joint.guideClock_start]
    exact joint.guideClock.symm_apply_apply 0
  have hOrientedBounds (p : ↥P) : eventOrientedTime p ∈ Ioo (0 : Interval) orientedEntry := by
    constructor
    · have hh := hOrientedAffine (hpTimeBounds p).1
      rw [hOrientedZero] at hh
      exact hh
    · exact hOrientedAffine (hpTimeBounds p).2
  have hOrientedLabels (i j : Fin eventCount) (hij : i < j) :
      eventOrientedTime (eventLabel i) < eventOrientedTime (eventLabel j) :=
    hOrientedAffine (hEventLabelOrder i j hij)
  have hRawOrder (p : ↥P) :
      (d.bStart < eventRawTime p ∧ eventRawTime p < actualEntry) ∨
      (actualEntry < eventRawTime p ∧ eventRawTime p < d.bStart) := by
    have ht0 : 0 < (pTime p).val := (hpTimeBounds p).1
    have hte : (pTime p).val < joint.guideEntryTime.val := (hpTimeBounds p).2
    rcases hbstartEndpoint with hs | hs
    · have hfin : 0 < d.bFinish.val := by
        have hn : d.bFinish.val ≠ 0 := by
          intro he; apply d.b_distinct; rw [hs]; exact Subtype.ext he.symm
        exact lt_of_le_of_ne d.bFinish.property.1 (Ne.symm hn)
      left
      change d.bStart.val < (1-(pTime p).val)*d.bStart.val+(pTime p).val*d.bFinish.val ∧
        (1-(pTime p).val)*d.bStart.val+(pTime p).val*d.bFinish.val <
          (1-joint.guideEntryTime.val)*d.bStart.val+joint.guideEntryTime.val*d.bFinish.val
      rw [hs]
      norm_num
      constructor <;> nlinarith [mul_pos ht0 hfin,mul_pos (sub_pos.mpr hte) hfin]
    · have hfin : d.bFinish.val < 1 := by
        have hn : d.bFinish.val ≠ 1 := by
          intro he; apply d.b_distinct; rw [hs]; exact Subtype.ext he.symm
        exact lt_of_le_of_ne d.bFinish.property.2 hn
      right
      change (1-joint.guideEntryTime.val)*d.bStart.val+joint.guideEntryTime.val*d.bFinish.val <
        (1-(pTime p).val)*d.bStart.val+(pTime p).val*d.bFinish.val ∧
        (1-(pTime p).val)*d.bStart.val+(pTime p).val*d.bFinish.val < d.bStart.val
      rw [hs]
      norm_num
      constructor <;> nlinarith [mul_pos ht0 (sub_pos.mpr hfin),
        mul_pos (sub_pos.mpr hte) (sub_pos.mpr hfin)]
  have hRawCore (p : ↥P) : eventRawTime p ∈
      Ioo (min d.bStart actualEntry) (max d.bStart actualEntry) := by
    rcases hRawOrder p with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · exact ⟨lt_of_le_of_lt (min_le_left _ _) h0,lt_of_lt_of_le h1 (le_max_right _ _)⟩
    · exact ⟨lt_of_le_of_lt (min_le_right _ _) h0,lt_of_lt_of_le h1 (le_max_left _ _)⟩
  have hRawInterior (p : ↥P) : eventRawTime p ∈ Ioo (0 : Interval) 1 :=
    ⟨lt_of_le_of_lt (unitInterval.nonneg _) (hRawCore p).1,
      lt_of_lt_of_le (hRawCore p).2 (unitInterval.le_one _)⟩
  have hEntryDifferent : d.bStart ≠ actualEntry := by
    intro he
    have hpos := hOrientedAffine joint.guideEntryTime_interior.1
    have hz : orientedEntry = 0 := by
      change joint.guideClock.symm actualEntry = 0
      rw [← he,← joint.guideClock_start]
      exact joint.guideClock.symm_apply_apply 0
    change orientedAffine 0 < orientedEntry at hpos
    rw [hOrientedZero,hz] at hpos
    exact (lt_irrefl _ hpos)
  have hCoreNontrivial : min d.bStart actualEntry < max d.bStart actualEntry := by
    rcases lt_or_gt_of_ne hEntryDifferent with hh | hh
    · simpa only [min_eq_left hh.le,max_eq_right hh.le] using hh
    · simpa only [min_eq_right hh.le,max_eq_left hh.le] using hh
  -- G1: literal restricted event charts and disjoint ambient supports.
  let ambientGuide : C(Interval × Icc (-1 : ℝ) 1,S) :=
    ⟨fun z => (guideStrip z).val,guideStrip.continuous.subtype_val⟩
  let ambientB : C(Interval,S) := ⟨fun t => (b t).val,b.continuous.subtype_val⟩
  have hAmbientGuide : IsEmbedding ambientGuide := IsEmbedding.subtypeVal.comp hGuide
  have hAmbientB : IsEmbedding ambientB := IsEmbedding.subtypeVal.comp (r w).val.property.1
  let smallCoordinates : Set (Interval × Icc (-1 : ℝ) 1) :=
    {z | min d.bStart actualEntry < z.1 ∧ z.1 < max d.bStart actualEntry ∧
      |z.2.val| < joint.entryMargin/4}
  let smallRelative : Set ↥F := guideStrip '' smallCoordinates
  let Rsmall : Set S := ambientGuide '' smallCoordinates
  have hMarginOne : joint.entryMargin < 1 :=
    joint.entryMargin_lt_bound.trans joint.bound_lt_one
  have hSmallCoordinatesOpen : IsOpen smallCoordinates :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt (continuous_abs.comp (continuous_subtype_val.comp continuous_snd))
          continuous_const))
  have hSmallInCore : smallCoordinates ⊆ {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
    intro z hz
    have hh := abs_lt.mp hz.2.2
    constructor <;> linarith [joint.entryMargin_pos]
  have hSmallRelativeOpen : IsOpen smallRelative := by
    obtain ⟨U,hU,hUeq⟩ := hGuide.isInducing.isOpen_iff.mp hSmallCoordinatesOpen
    have he : smallRelative =
        (guideStrip '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) ∩ U := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        refine ⟨⟨z,hSmallInCore hz,rfl⟩,?_⟩
        have hzU : z ∈ guideStrip ⁻¹' U := hUeq.symm ▸ hz
        exact hzU
      · rintro ⟨⟨z,hz,rfl⟩,hy⟩
        exact ⟨z,hUeq ▸ hy,rfl⟩
    rw [he]
    exact joint.guideStrip_open.inter hU
  have hEntrySelected : actualEntry ∈
      Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) := by
    have ht0 := joint.guideEntryTime.property.1
    have ht1 := joint.guideEntryTime.property.2
    rcases le_total d.bStart d.bFinish with hh | hh
    · rw [min_eq_left hh,max_eq_right hh]
      exact CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hh joint.guideEntryTime
    · rw [min_eq_right hh,max_eq_left hh]
      have hhR : d.bFinish.val ≤ d.bStart.val := hh
      change d.bFinish.val ≤ (1-joint.guideEntryTime.val)*d.bStart.val+
          joint.guideEntryTime.val*d.bFinish.val ∧
        (1-joint.guideEntryTime.val)*d.bStart.val+joint.guideEntryTime.val*d.bFinish.val ≤ d.bStart.val
      constructor <;> nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hhR),
        mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hhR)]
  have hSmallTimeSelected {z : Interval × Icc (-1 : ℝ) 1} (hz : z ∈ smallCoordinates) :
      z.1 ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) :=
    ⟨(le_min (min_le_left _ _) hEntrySelected.1).trans hz.1.le,
      hz.2.1.le.trans (max_le (le_max_left _ _) hEntrySelected.2)⟩
  have hSmallRelativeInterior : ∀ y ∈ smallRelative, y.val ∈ interior F := by
    rintro y ⟨z,hz,rfl⟩
    exact joint.guideStrip_interior z.1
      ⟨lt_of_le_of_lt (unitInterval.nonneg _) hz.1,
        lt_of_lt_of_le hz.2.1 (unitInterval.le_one _)⟩ z.2
  have hSmallRelativeV : smallRelative ⊆ V := by
    rintro y ⟨z,hz,rfl⟩
    exact joint.guide_full_window_fibers z.1
      (joint.guideWindow_selected (hSmallTimeSelected hz)) z.2
  obtain ⟨ambientV,hAmbientV,hAmbientVeq⟩ :=
    (IsEmbedding.subtypeVal.isInducing.isOpen_iff).mp hV
  have hSmallSupport : Rsmall ⊆ interior F ∩ ambientV := by
    rintro y ⟨z,hz,rfl⟩
    refine ⟨hSmallRelativeInterior _ ⟨z,hz,rfl⟩,?_⟩
    have hv := hSmallRelativeV ⟨z,hz,rfl⟩
    rw [← hAmbientVeq] at hv
    exact hv
  have hRsmallOpen : IsOpen Rsmall := by
    obtain ⟨U,hU,hUeq⟩ :=
      IsEmbedding.subtypeVal.isInducing.isOpen_iff.mp hSmallRelativeOpen
    have he : Rsmall = U ∩ interior F := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        refine ⟨?_,hSmallRelativeInterior _ ⟨z,hz,rfl⟩⟩
        have hyU : guideStrip z ∈ Subtype.val ⁻¹' U := hUeq.symm ▸ ⟨z,hz,rfl⟩
        exact hyU
      · intro hy
        let yf : ↥F := ⟨y,interior_subset hy.2⟩
        have hyf : yf ∈ smallRelative := hUeq ▸ hy.1
        obtain ⟨z,hz,he⟩ := hyf
        exact ⟨z,hz,congrArg Subtype.val he⟩
    rw [he]
    exact hU.inter isOpen_interior
  have hEventSmall (p : ↥P) : p.val.val ∈ Rsmall := by
    refine ⟨(eventRawTime p,⟨0,by norm_num⟩),?_,?_⟩
    · exact ⟨(hRawCore p).1,(hRawCore p).2,by simpa using div_pos joint.entryMargin_pos (by norm_num : (0:ℝ)<4)⟩
    · change (guideStrip (eventRawTime p,⟨0,by norm_num⟩)).val = p.val.val
      rw [hGuideCenterActual,hRawCenter]
  let eventFan (p : ↥P) : IncidentFanWindow F f V p.val := Classical.choose (hEventAxisFan p)
  have hEventFanProperties (p : ↥P) := Classical.choose_spec (hEventAxisFan p)
  let eventUnitDomain (p : ↥P) : Set S :=
    (eventFan p).chart.source ∩ (eventFan p).chart ⁻¹' Metric.ball (0 : Plane) 1
  have hEventUnitOpen (p : ↥P) : IsOpen (eventUnitDomain p) :=
    (eventFan p).chart.isOpen_inter_preimage Metric.isOpen_ball
  let eventAxisChart (p : ↥P) : OpenPartialHomeomorph S Plane :=
    (eventFan p).chart.restr (eventUnitDomain p)
  have hEventAxisSource (p : ↥P) : (eventAxisChart p).source =
      (eventFan p).chart.source ∩ eventUnitDomain p :=
    (eventFan p).chart.restr_source' _ (hEventUnitOpen p)
  have hEventAxisPoint (p : ↥P) : ambientB (eventRawTime p) ∈ (eventAxisChart p).source := by
    change (b (eventRawTime p)).val ∈ (eventAxisChart p).source
    rw [hRawCenter,hEventAxisSource]
    refine ⟨(eventFan p).contact_in_source,(eventFan p).contact_in_source,?_⟩
    change (eventFan p).chart p.val.val ∈ Metric.ball (0 : Plane) 1
    rw [(eventFan p).contact_zero]
    simp
  have hEventAxisZero (p : ↥P) : eventAxisChart p (ambientB (eventRawTime p)) = 0 := by
    change (eventFan p).chart (b (eventRawTime p)).val = 0
    rw [hRawCenter,(eventFan p).contact_zero]
  have hEventWholeAxis (p : ↥P) (t : Interval)
      (ht : ambientB t ∈ (eventAxisChart p).source) :
      eventAxisChart p (ambientB t) 1 = 0 := by
    rw [hEventAxisSource] at ht
    obtain ⟨hleft,hright⟩ := (hEventFanProperties p).2.1 (hSecondWhole p.property.1.1)
    apply (hFanAxis p.val (eventFan p) ⟨some w,hSecondWhole p.property.1.1⟩
      hleft hright (b t) ht.2.1 (Metric.ball_subset_closedBall ht.2.2)).mp
    exact ⟨t,rfl⟩
  obtain ⟨eventOpen,hEventOpen,hEventOpenDisjoint⟩ :=
    CurveComplex.source_finite_compact_open_separation
      (fun p : ↥P => ({p.val.val} : Set S)) (fun _ => isCompact_singleton)
  let eventSupport (p : ↥P) : Set S :=
    eventOpen p ∩ Rsmall ∩ eventUnitDomain p
  have hEventSupportOpen (p : ↥P) : IsOpen (eventSupport p) :=
    ((hEventOpen p).1.inter hRsmallOpen).inter (hEventUnitOpen p)
  have hEventSupportPoint (p : ↥P) : p.val.val ∈ eventSupport p := by
    refine ⟨⟨(hEventOpen p).2 (mem_singleton _),hEventSmall p⟩,?_⟩
    refine ⟨(eventFan p).contact_in_source,?_⟩
    change (eventFan p).chart p.val.val ∈ Metric.ball (0 : Plane) 1
    rw [(eventFan p).contact_zero]
    simp
  have hEventSupportSmall (p : ↥P) : eventSupport p ⊆ Rsmall := fun _ hy => hy.1.2
  have hEventSupportDisjoint (p q : ↥P) (hpq : p ≠ q) :
      Disjoint (eventSupport p) (eventSupport q) := by
    apply (hEventOpenDisjoint p q ?_).mono (fun _ hy => hy.1.1) (fun _ hy => hy.1.1)
    apply disjoint_singleton.mpr
    intro he
    exact hpq (Subtype.ext (Subtype.ext he))
  -- G2: ambient corrections supported in this literal core retain all signs.
  have hSmallMembership (z : Interval × Icc (-1 : ℝ) 1) :
      ambientGuide z ∈ Rsmall ↔ z ∈ smallCoordinates := by
    constructor
    · rintro ⟨q,hq,he⟩
      exact hAmbientGuide.injective he ▸ hq
    · exact fun hz => ⟨z,hz,rfl⟩
  have hSupportedRegionPreserves (H : S ≃ₜ S)
      (hfix : ∀ y, y ∉ Rsmall → H y = y)
      (A : Set S) (hA : Rsmall ⊆ A) (y : S) : y ∈ A ↔ H y ∈ A := by
    constructor
    · intro hy
      by_contra hn
      have hf := hfix (H y) (fun h => hn (hA h))
      have he : H y = y := H.injective hf
      exact hn (he.symm ▸ hy)
    · intro hy
      by_contra hn
      have hf := hfix y (fun h => hn (hA h))
      exact hn (hf ▸ hy)
  have hCorrectionCoordinates (H : S ≃ₜ S)
      (hcenter : ∀ t, H (ambientB t) = ambientB t)
      (hfix : ∀ y, y ∉ Rsmall → H y = y) :
      ∃ K : (Interval × Icc (-1 : ℝ) 1) ≃ₜ (Interval × Icc (-1 : ℝ) 1),
        (∀ z, ambientGuide (K z) = H (ambientGuide z)) ∧
        (∀ t, K (t,⟨0,by norm_num⟩) = (t,⟨0,by norm_num⟩)) ∧
        (∀ z, z ∉ smallCoordinates → K z = z) ∧
        (∀ z, 0 < (K z).2.val ↔ 0 < z.2.val) ∧
        (∀ z, (K z).2.val = 0 ↔ z.2.val = 0) ∧
        (∀ z, (K z).2.val < 0 ↔ z.2.val < 0) := by
    have hRange : ∀ y, y ∈ range ambientGuide ↔ H y ∈ range ambientGuide :=
      hSupportedRegionPreserves H hfix (range ambientGuide)
        (fun _ ⟨z,hz,he⟩ => ⟨z,he⟩)
    let K : (Interval × Icc (-1 : ℝ) 1) ≃ₜ (Interval × Icc (-1 : ℝ) 1) :=
      hAmbientGuide.toHomeomorph.trans (H.subtype hRange) |>.trans hAmbientGuide.toHomeomorph.symm
    have hK (z : Interval × Icc (-1 : ℝ) 1) :
        ambientGuide (K z) = H (ambientGuide z) := by
      exact congrArg Subtype.val (hAmbientGuide.toHomeomorph.apply_symm_apply
        ((H.subtype hRange) (hAmbientGuide.toHomeomorph z)))
    have hKCenter (t : Interval) : K (t,⟨0,by norm_num⟩) = (t,⟨0,by norm_num⟩) := by
      apply hAmbientGuide.injective
      rw [hK]
      have hz : ambientGuide (t,⟨0,by norm_num⟩) = ambientB t :=
        congrArg Subtype.val (hGuideCenterActual t)
      rw [hz,hcenter]
    have hKFixed (z : Interval × Icc (-1 : ℝ) 1) (hz : z ∉ smallCoordinates) : K z = z := by
      apply hAmbientGuide.injective
      rw [hK]
      exact hfix _ (fun hy => hz ((hSmallMembership z).mp hy))
    have hKZero (z : Interval × Icc (-1 : ℝ) 1) : (K z).2.val = 0 ↔ z.2.val = 0 := by
      constructor
      · intro hz
        have he : K z = ((K z).1,⟨0,by norm_num⟩) :=
          Prod.ext rfl (Subtype.ext hz)
        have hh : z = ((K z).1,⟨0,by norm_num⟩) := K.injective (he.trans (hKCenter _).symm)
        exact congrArg (fun q : Interval × Icc (-1 : ℝ) 1 => q.2.val) hh
      · intro hz
        have he : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl (Subtype.ext hz)
        rw [he,hKCenter]
    have hKPositive (z : Interval × Icc (-1 : ℝ) 1) (hz : 0 < z.2.val) : 0 < (K z).2.val := by
      let y : C(Interval,ℝ) :=
        ⟨fun s => (K (z.1,⟨s.val,⟨by linarith [s.property.1],s.property.2⟩⟩)).2.val,
          by fun_prop⟩
      have hyzero (s : Interval) (hs : 0 < s.val) : y s ≠ 0 := by
        intro he
        have hh := (hKZero (z.1,⟨s.val,⟨by linarith [s.property.1],s.property.2⟩⟩)).mp he
        exact (ne_of_gt hs) hh
      have hyone : y 1 = 1 := by
        change (K (z.1,⟨1,by norm_num⟩)).2.val = 1
        rw [hKFixed]
        intro hh
        have hl := hh.2.2
        norm_num at hl
        linarith
      obtain ⟨σ,hσ,hpositive⟩ := CurveComplex.actual_continuous_positive_parameter_sign y hyzero
      have hσone : σ = 1 := by
        rcases hσ with he | he
        · have hp := hpositive 1 (by norm_num)
          rw [he,hyone] at hp
          norm_num at hp
        · exact he
      let s : Interval := ⟨z.2.val,⟨hz.le,z.2.property.2⟩⟩
      have hp := hpositive s hz
      rw [hσone,one_mul] at hp
      exact hp
    have hKNegative (z : Interval × Icc (-1 : ℝ) 1) (hz : z.2.val < 0) : (K z).2.val < 0 := by
      let y : C(Interval,ℝ) :=
        ⟨fun s => (K (z.1,⟨-s.val,⟨by linarith [s.property.2],by linarith [s.property.1]⟩⟩)).2.val,
          by fun_prop⟩
      have hyzero (s : Interval) (hs : 0 < s.val) : y s ≠ 0 := by
        intro he
        have hh := (hKZero (z.1,⟨-s.val,⟨by linarith [s.property.2],by linarith [s.property.1]⟩⟩)).mp he
        have hh' : s.val = 0 := neg_eq_zero.mp hh
        exact (ne_of_gt hs) hh'
      have hyone : y 1 = -1 := by
        change (K (z.1,⟨-1,by norm_num⟩)).2.val = -1
        rw [hKFixed]
        intro hh
        have hl := hh.2.2
        norm_num at hl
        linarith
      obtain ⟨σ,hσ,hpositive⟩ := CurveComplex.actual_continuous_positive_parameter_sign y hyzero
      have hσminus : σ = -1 := by
        rcases hσ with he | he
        · exact he
        · have hp := hpositive 1 (by norm_num)
          rw [he,hyone] at hp
          norm_num at hp
      let s : Interval := ⟨-z.2.val,⟨neg_nonneg.mpr hz.le,by linarith [z.2.property.1]⟩⟩
      have hp := hpositive s (neg_pos.mpr hz)
      rw [hσminus] at hp
      have hzval : (⟨-s.val,⟨by linarith [s.property.2],by linarith [s.property.1]⟩⟩ : Icc (-1 : ℝ) 1) = z.2 := by
        apply Subtype.ext
        change -(-z.2.val) = z.2.val
        ring
      change 0 < -1*(K (z.1,⟨-s.val,⟨by linarith [s.property.2],by linarith [s.property.1]⟩⟩)).2.val at hp
      rw [hzval] at hp
      linarith
    have hKPositiveIff (z : Interval × Icc (-1 : ℝ) 1) : 0 < (K z).2.val ↔ 0 < z.2.val := by
      constructor
      · intro hz
        rcases lt_trichotomy z.2.val 0 with hn | he | hp
        · exact (not_lt_of_gt hz (hKNegative z hn)).elim
        · rw [(hKZero z).mpr he] at hz
          exact (lt_irrefl _ hz).elim
        · exact hp
      · exact hKPositive z
    have hKNegativeIff (z : Interval × Icc (-1 : ℝ) 1) : (K z).2.val < 0 ↔ z.2.val < 0 := by
      constructor
      · intro hz
        rcases lt_trichotomy z.2.val 0 with hn | he | hp
        · exact hn
        · rw [(hKZero z).mpr he] at hz
          exact (lt_irrefl _ hz).elim
        · exact (not_lt_of_gt hz (hKPositive z hp)).elim
      · exact hKNegative z
    exact ⟨K,hK,hKCenter,hKFixed,hKPositiveIff,hKZero,hKNegativeIff⟩
  let positiveCarrierCoordinates : Set (Interval × Icc (-1 : ℝ) 1) :=
    {z | z.1 ∈ Icc (min d.bStart actualEntry) (max d.bStart actualEntry) ∧
      0 ≤ z.2.val ∧ z.2.val ≤ joint.entryMargin}
  let selectedPositiveCoordinates : Set (Interval × Icc (-1 : ℝ) 1) :=
    {z | z.1 ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) ∧
      0 < z.2.val ∧ z.2.val < joint.bound}
  have hSmallPositiveCarrier {z : Interval × Icc (-1 : ℝ) 1} (hz : z ∈ smallCoordinates) :
      z ∈ positiveCarrierCoordinates ↔ 0 ≤ z.2.val := by
    constructor
    · exact fun h => h.2.1
    · intro h
      refine ⟨⟨hz.1.le,hz.2.1.le⟩,h,?_⟩
      exact (le_abs_self _).trans ((hz.2.2.trans (by linarith [joint.entryMargin_pos])).le)
  have hSmallSelectedPositive {z : Interval × Icc (-1 : ℝ) 1} (hz : z ∈ smallCoordinates) :
      z ∈ selectedPositiveCoordinates ↔ 0 < z.2.val := by
    constructor
    · exact fun h => h.2.1
    · intro h
      refine ⟨hSmallTimeSelected hz,h,?_⟩
      exact (le_abs_self _).trans_lt (hz.2.2.trans
        ((by linarith [joint.entryMargin_pos] : joint.entryMargin/4 < joint.entryMargin).trans
          joint.entryMargin_lt_bound))
  have hCorrectionCarriers (H : S ≃ₜ S)
      (hcenter : ∀ t, H (ambientB t) = ambientB t)
      (hfix : ∀ y, y ∉ Rsmall → H y = y) :
      H '' (ambientGuide '' positiveCarrierCoordinates) =
          ambientGuide '' positiveCarrierCoordinates ∧
      H '' (ambientGuide '' selectedPositiveCoordinates) =
          ambientGuide '' selectedPositiveCoordinates := by
    obtain ⟨K,hK,hKCenter,hKFixed,hKPositive,hKZero,hKNegative⟩ :=
      hCorrectionCoordinates H hcenter hfix
    have hKSmall (z : Interval × Icc (-1 : ℝ) 1) : K z ∈ smallCoordinates ↔ z ∈ smallCoordinates := by
      rw [← hSmallMembership (K z),hK]
      exact (hSupportedRegionPreserves H hfix Rsmall subset_rfl (ambientGuide z)).symm.trans
        (hSmallMembership z)
    have hCarrier (z : Interval × Icc (-1 : ℝ) 1) :
        K z ∈ positiveCarrierCoordinates ↔ z ∈ positiveCarrierCoordinates := by
      by_cases hz : z ∈ smallCoordinates
      · rw [hSmallPositiveCarrier ((hKSmall z).mpr hz),hSmallPositiveCarrier hz]
        simpa only [not_lt] using not_congr (hKNegative z)
      · rw [hKFixed z hz]
    have hSelected (z : Interval × Icc (-1 : ℝ) 1) :
        K z ∈ selectedPositiveCoordinates ↔ z ∈ selectedPositiveCoordinates := by
      by_cases hz : z ∈ smallCoordinates
      · rw [hSmallSelectedPositive ((hKSmall z).mpr hz),hSmallSelectedPositive hz]
        exact hKPositive z
      · rw [hKFixed z hz]
    have hImage (A : Set (Interval × Icc (-1 : ℝ) 1))
        (hA : ∀ z, K z ∈ A ↔ z ∈ A) : H '' (ambientGuide '' A) = ambientGuide '' A := by
      ext y
      constructor
      · rintro ⟨q,⟨z,hz,rfl⟩,rfl⟩
        exact ⟨K z,(hA z).mpr hz,hK z⟩
      · rintro ⟨z,hz,rfl⟩
        refine ⟨ambientGuide (K.symm z),⟨K.symm z,?_,rfl⟩,?_⟩
        · apply (hA (K.symm z)).mp
          rwa [K.apply_symm_apply]
        · exact (hK (K.symm z)).symm.trans (congrArg ambientGuide (K.apply_symm_apply z))
    exact ⟨hImage _ hCarrier,hImage _ hSelected⟩
  have hRelativeCorrectionCarriers (H : S ≃ₜ S)
      (hcenter : ∀ t, H (ambientB t) = ambientB t)
      (hfix : ∀ y, y ∉ Rsmall → H y = y) :
      ∃ HF : ↥F ≃ₜ ↥F,
        (∀ y, (HF y).val = H y.val) ∧
        (∀ z, z ∉ smallCoordinates → HF (guideStrip z) = guideStrip z) ∧
        regionalHalfJointGuideCarrier F
            ((⟨HF,HF.continuous⟩ : C(↥F,↥F)).comp guideStrip)
            d.bStart actualEntry joint.entryMargin =
          regionalHalfJointGuideCarrier F guideStrip d.bStart actualEntry joint.entryMargin ∧
        ((⟨HF,HF.continuous⟩ : C(↥F,↥F)).comp guideStrip) '' selectedPositiveCoordinates =
          guideStrip '' selectedPositiveCoordinates := by
    have hF : ∀ y, y ∈ F ↔ H y ∈ F :=
      hSupportedRegionPreserves H hfix F (fun _ hy => interior_subset (hSmallSupport hy).1)
    let HF : ↥F ≃ₜ ↥F := H.subtype hF
    have hvalImage (A : Set (Interval × Icc (-1 : ℝ) 1)) :
        Subtype.val '' (HF '' (guideStrip '' A)) = H '' (ambientGuide '' A) := by
      simp only [image_image]
      rfl
    have hOriginalValImage (A : Set (Interval × Icc (-1 : ℝ) 1)) :
        Subtype.val '' (guideStrip '' A) = ambientGuide '' A := by
      rw [image_image]
      rfl
    have hRelativeImage (A : Set (Interval × Icc (-1 : ℝ) 1))
        (hA : H '' (ambientGuide '' A) = ambientGuide '' A) :
        HF '' (guideStrip '' A) = guideStrip '' A := by
      apply (Set.image_injective.mpr Subtype.val_injective)
      rw [hvalImage,hOriginalValImage]
      exact hA
    obtain ⟨hCarrier,hSelected⟩ := hCorrectionCarriers H hcenter hfix
    refine ⟨HF,fun _ => rfl,?_,?_,?_⟩
    · intro z hz
      apply Subtype.ext
      exact hfix _ (fun hh => hz ((hSmallMembership z).mp hh))
    · change (fun z => HF (guideStrip z)) '' positiveCarrierCoordinates = guideStrip '' positiveCarrierCoordinates
      simpa only [image_image] using hRelativeImage positiveCarrierCoordinates hCarrier
    · change (fun z => HF (guideStrip z)) '' selectedPositiveCoordinates = guideStrip '' selectedPositiveCoordinates
      simpa only [image_image] using hRelativeImage selectedPositiveCoordinates hSelected
  have hEventUnionSmall : (⋃ p : ↥P, eventSupport p) ⊆ Rsmall := by
    intro y hy
    obtain ⟨p,hp⟩ := mem_iUnion.mp hy
    exact hEventSupportSmall p hp
  have hEventSupportAmbientPoint (p : ↥P) :
      ambientB (eventRawTime p) ∈ eventSupport p := by
    change (b (eventRawTime p)).val ∈ eventSupport p
    rw [hRawCenter]
    exact hEventSupportPoint p
  have hBoundaryFibersOutside (u : Icc (-1 : ℝ) 1) :
      (0,u) ∉ smallCoordinates ∧ (1,u) ∉ smallCoordinates := by
    constructor
    · intro hh
      exact (not_lt_of_ge (unitInterval.nonneg _)) hh.1
    · intro hh
      exact (not_lt_of_ge (unitInterval.le_one _)) hh.2.1
  have hStartEntryFibersOutside (u : Icc (-1 : ℝ) 1) :
      (d.bStart,u) ∉ smallCoordinates ∧ (actualEntry,u) ∉ smallCoordinates := by
    constructor
    · rcases hbstartEndpoint with hh | hh
      · rw [hh]
        exact (hBoundaryFibersOutside u).1
      · rw [hh]
        exact (hBoundaryFibersOutside u).2
    · intro hh
      rcases le_total d.bStart actualEntry with he | he
      · have hn := hh.2.1
        rw [max_eq_right he] at hn
        exact lt_irrefl _ hn
      · have hn := hh.1
        rw [min_eq_right he] at hn
        exact lt_irrefl _ hn
  have hCorrectionFullFaces (H : S ≃ₜ S)
      (hfix : ∀ y, y ∉ Rsmall → H y = y) :
      (∀ u, H (ambientGuide (0,u)) = ambientGuide (0,u) ∧
        H (ambientGuide (1,u)) = ambientGuide (1,u)) ∧
      (∀ u, H (ambientGuide (d.bStart,u)) = ambientGuide (d.bStart,u)) ∧
      (∀ u, H (ambientGuide (actualEntry,u)) = ambientGuide (actualEntry,u)) := by
    refine ⟨?_,?_,?_⟩
    · intro u
      exact ⟨hfix _ (fun hh => (hBoundaryFibersOutside u).1 ((hSmallMembership _).mp hh)),
        hfix _ (fun hh => (hBoundaryFibersOutside u).2 ((hSmallMembership _).mp hh))⟩
    · intro u
      exact hfix _ (fun hh => (hStartEntryFibersOutside u).1 ((hSmallMembership _).mp hh))
    · intro u
      exact hfix _ (fun hh => (hStartEntryFibersOutside u).2 ((hSmallMembership _).mp hh))
  -- G4: a conditional same-data joint reconstruction, internal to this caller.
  -- G3 must later supply H; this clause does not assert that such H exists.
  have hCompatibleJointFromCorrection (H : S ≃ₜ S)
      (hcenter : ∀ t, H (ambientB t) = ambientB t)
      (hfix : ∀ y, y ∉ Rsmall → H y = y) :
      ∃ J1 : RegionalHalfJointCollarCornerPacket F
          {y : ↥F | y.val ∈ boundaryCircle} {y : ↥F | y.val ∈ frontier F}
          (fun i => (r i).val.val) α.val.val v w d V fan gap,
        (∀ z, (J1.guideStrip z).val = H (guideStrip z).val) ∧
        J1.bound = joint.bound ∧ J1.clock = joint.clock ∧ J1.cut = joint.cut ∧
        J1.oldStrip = joint.oldStrip ∧ J1.activeWindow = joint.activeWindow ∧
        J1.guideWindow = joint.guideWindow ∧ J1.guideClock = joint.guideClock ∧
        J1.guideEntryTime = joint.guideEntryTime ∧ J1.boundaryLine = joint.boundaryLine ∧
        J1.terminalCut = joint.terminalCut ∧ J1.cornerFan = joint.cornerFan ∧
        J1.cornerDelta = joint.cornerDelta ∧ J1.cornerEntry = joint.cornerEntry ∧
        J1.entryMargin = joint.entryMargin ∧ J1.kappa = joint.kappa ∧
        J1.capBound = joint.capBound ∧ J1.oldCornerWindow = joint.oldCornerWindow ∧
        J1.oldCornerWidth = joint.oldCornerWidth ∧ J1.oldCornerX = joint.oldCornerX ∧
        J1.oldCornerScale = joint.oldCornerScale ∧ J1.oldCornerSign = joint.oldCornerSign ∧
        J1.oldNegativeWidth = joint.oldNegativeWidth := by
    obtain ⟨HF,hval,hfixed,hCarrier,hSelected⟩ := hRelativeCorrectionCarriers H hcenter hfix
    let E1 : C(Interval × Icc (-1 : ℝ) 1,↥F) :=
      (⟨HF,HF.continuous⟩ : C(↥F,↥F)).comp guideStrip
    have hE1Val (z : Interval × Icc (-1 : ℝ) 1) :
        (E1 z).val = H (guideStrip z).val := hval _
    have hE1Fixed (z : Interval × Icc (-1 : ℝ) 1) (hz : z ∉ smallCoordinates) :
        E1 z = guideStrip z := hfixed z hz
    have hE1Ends (u : Icc (-1 : ℝ) 1) : E1 (0,u) = guideStrip (0,u) ∧
        E1 (1,u) = guideStrip (1,u) :=
      ⟨hE1Fixed _ (hBoundaryFibersOutside u).1,hE1Fixed _ (hBoundaryFibersOutside u).2⟩
    have hE1Start (u : Icc (-1 : ℝ) 1) : E1 (d.bStart,u) = guideStrip (d.bStart,u) :=
      hE1Fixed _ (hStartEntryFibersOutside u).1
    have hE1Entry (u : Icc (-1 : ℝ) 1) : E1 (actualEntry,u) = guideStrip (actualEntry,u) :=
      hE1Fixed _ (hStartEntryFibersOutside u).2
    have hE1Embedded : IsEmbedding E1 := HF.isEmbedding.comp hGuide
    have hE1Center (t : Interval) : E1 (t,⟨0,by norm_num⟩) = b t := by
      apply Subtype.ext
      rw [hE1Val,hGuideCenterActual]
      exact hcenter t
    have hInteriorPreserved (y : S) : y ∈ interior F ↔ H y ∈ interior F :=
      hSupportedRegionPreserves H hfix (interior F) (fun _ hy => (hSmallSupport hy).1) y
    have hVPreserved (y : S) : y ∈ ambientV ↔ H y ∈ ambientV :=
      hSupportedRegionPreserves H hfix ambientV (fun _ hy => (hSmallSupport hy).2) y
    have hE1Interior (t : Interval) (ht : t ∈ Ioo (0 : Interval) 1) (u : Icc (-1 : ℝ) 1) :
        (E1 (t,u)).val ∈ interior F := by
      rw [hE1Val]
      exact (hInteriorPreserved _).mp (joint.guideStrip_interior t ht u)
    have hE1Window (t : Interval) (ht : t ∈ joint.guideWindow) (u : Icc (-1 : ℝ) 1) :
        E1 (t,u) ∈ V := by
      rw [← hAmbientVeq]
      change (E1 (t,u)).val ∈ ambientV
      rw [hE1Val]
      apply (hVPreserved _).mp
      have hv : guideStrip (t,u) ∈ V := joint.guide_full_window_fibers t ht u
      rw [← hAmbientVeq] at hv
      exact hv
    have hE1Open : IsOpen (E1 '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
      have he : E1 '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} =
          HF '' (guideStrip '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
        ext y
        constructor
        · rintro ⟨z,hz,rfl⟩
          exact ⟨guideStrip z,⟨z,hz,rfl⟩,rfl⟩
        · rintro ⟨q,⟨z,hz,rfl⟩,rfl⟩
          exact ⟨z,hz,rfl⟩
      rw [he]
      exact HF.isOpenMap _ joint.guideStrip_open
    have hE1Carrier : regionalHalfJointGuideCarrier F E1 d.bStart actualEntry joint.entryMargin =
        regionalHalfJointGuideCarrier F guideStrip d.bStart actualEntry joint.entryMargin := hCarrier
    have hE1Selected : E1 '' selectedPositiveCoordinates = guideStrip '' selectedPositiveCoordinates := hSelected
    have hE1Exterior : Disjoint (E1 '' selectedPositiveCoordinates) (range d.disk) := by
      rw [hE1Selected]
      exact joint.guiding_exterior
    have hE1Disk : regionalHalfJointGuideCarrier F E1 d.bStart actualEntry joint.entryMargin ∩
        range d.disk = d.second '' Icc (0 : Interval) joint.guideEntryTime := by
      rw [hE1Carrier]
      exact joint.guide_carrier_disk_inter
    have hE1EntryImage (ε : ℝ) :
        E1 '' {z | z.1 = actualEntry ∧ 0 ≤ z.2.val ∧ z.2.val ≤ ε/joint.kappa} =
          guideStrip '' {z | z.1 = actualEntry ∧ 0 ≤ z.2.val ∧ z.2.val ≤ ε/joint.kappa} := by
      apply Set.image_congr
      intro z hz
      rw [show z = (actualEntry,z.2) from Prod.ext hz.1 rfl]
      exact hE1Entry z.2
    have hE1Corner (ε : ℝ) (hε : 0 < ε) (hεcap : ε < joint.capBound) :
        regionalHalfJointGuideCarrier F E1 d.bStart actualEntry joint.entryMargin ∩
          chartPull F joint.cornerFan.chart (regionalHalfCornerHull joint.cornerDelta joint.cornerEntry ε) =
        E1 '' {z | z.1 = actualEntry ∧ 0 ≤ z.2.val ∧ z.2.val ≤ ε/joint.kappa} := by
      rw [hE1Carrier,hE1EntryImage]
      exact joint.guide_corner_carrier_inter ε hε hεcap
    have hE1NegativeClear : Disjoint
        (regionalHalfOldNegativeBand F joint.oldStrip joint.clock joint.cut joint.oldNegativeWidth)
        (regionalHalfJointGuideCarrier F E1 d.bStart actualEntry joint.entryMargin) := by
      rw [hE1Carrier]
      exact joint.old_negative_guide_carrier_disjoint
    let J1 : RegionalHalfJointCollarCornerPacket F
        {y : ↥F | y.val ∈ boundaryCircle} {y : ↥F | y.val ∈ frontier F}
        (fun i => (r i).val.val) α.val.val v w d V fan gap := {
      joint with
      guideStrip := E1
      guideStrip_embedded := hE1Embedded
      guideStrip_center := hE1Center
      guideStrip_ends := by
        intro u
        rw [(hE1Ends u).1,(hE1Ends u).2]
        exact joint.guideStrip_ends u
      guideStrip_interior := hE1Interior
      guideStrip_open := hE1Open
      guiding_exterior := hE1Exterior
      guide_full_window_fibers := hE1Window
      boundaryLine_eq := by
        intro u
        rw [hE1Start]
        exact joint.boundaryLine_eq u
      guide_entry_section := by
        intro u hu hμ
        change (E1 (actualEntry,u)).val ∈ joint.cornerFan.chart.source ∧
          joint.cornerFan.chart (E1 (actualEntry,u)).val =
            Plane.mk (joint.cornerEntry 0-joint.kappa*u.val) (joint.cornerEntry 1)
        rw [hE1Entry]
        exact joint.guide_entry_section u hu hμ
      guide_carrier_disk_inter := hE1Disk
      guide_corner_carrier_inter := hE1Corner
      old_negative_guide_carrier_disjoint := hE1NegativeClear }
    exact ⟨J1,hE1Val,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  -- G5 consumer: actual oriented windows inside a supplied positive raw germ radius.
  have hEventClock (p : ↥P) : joint.guideClock (eventOrientedTime p) = eventRawTime p :=
    joint.guideClock.apply_symm_apply _
  have hGuideClockDistances (t u : Interval) :
      |(joint.guideClock t).val-(joint.guideClock u).val| = |t.val-u.val| := by
    rcases joint.guideClock_identity_or_reverse with hc | hc
    · simp only [hc,Homeomorph.refl_apply,id_eq]
    · rw [hc]
      change |(1-t.val)-(1-u.val)| = |t.val-u.val|
      rw [show (1-t.val)-(1-u.val) = -(t.val-u.val) by ring,abs_neg]
  have hIndividualEventWindow (η : ↥P → ℝ) (hη : ∀ p, 0 < η p) (p : ↥P) :
      ∃ ell right : Interval,
        0 < ell ∧ ell < eventOrientedTime p ∧ eventOrientedTime p < right ∧ right < orientedEntry ∧
        ∀ t : Interval, t ∈ Icc ell right →
          ambientB (joint.guideClock t) ∈ eventSupport p ∧
          |(joint.guideClock t).val-(eventRawTime p).val| < η p := by
    let center : C(Interval,S) := ambientB.comp ⟨joint.guideClock,joint.guideClock.continuous⟩
    have hp : center (eventOrientedTime p) ∈ eventSupport p := by
      change ambientB (joint.guideClock (eventOrientedTime p)) ∈ eventSupport p
      rw [hEventClock]
      exact hEventSupportAmbientPoint p
    have ho : IsOpen (center ⁻¹' eventSupport p) :=
      (hEventSupportOpen p).preimage center.continuous
    obtain ⟨n,hn,hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hp)
    let m : ℝ := min (min n (η p))
      (min (eventOrientedTime p).val (orientedEntry.val-(eventOrientedTime p).val))
    have hm : 0 < m := lt_min (lt_min hn (hη p))
      (lt_min (hOrientedBounds p).1 (sub_pos.mpr (hOrientedBounds p).2))
    let δ : ℝ := m/2
    have hδ : 0 < δ := div_pos hm (by norm_num)
    have hδm : δ < m := half_lt_self hm
    have hδn : δ < n := lt_of_lt_of_le hδm ((min_le_left _ _).trans (min_le_left _ _))
    have hδη : δ < η p := lt_of_lt_of_le hδm ((min_le_left _ _).trans (min_le_right _ _))
    have hδleft : δ < (eventOrientedTime p).val :=
      lt_of_lt_of_le hδm ((min_le_right _ _).trans (min_le_left _ _))
    have hδright : δ < orientedEntry.val-(eventOrientedTime p).val :=
      lt_of_lt_of_le hδm ((min_le_right _ _).trans (min_le_right _ _))
    let ell : Interval := ⟨(eventOrientedTime p).val-δ,
      ⟨by linarith,by linarith [(eventOrientedTime p).property.2]⟩⟩
    let right : Interval := ⟨(eventOrientedTime p).val+δ,
      ⟨by linarith [(eventOrientedTime p).property.1],by linarith [orientedEntry.property.2]⟩⟩
    refine ⟨ell,right,?_,?_,?_,?_,?_⟩
    · change 0 < (eventOrientedTime p).val-δ
      linarith
    · change (eventOrientedTime p).val-δ < (eventOrientedTime p).val
      linarith
    · change (eventOrientedTime p).val < (eventOrientedTime p).val+δ
      linarith
    · change (eventOrientedTime p).val+δ < orientedEntry.val
      linarith
    · intro t ht
      have hl : (eventOrientedTime p).val-δ ≤ t.val := ht.1
      have hr : t.val ≤ (eventOrientedTime p).val+δ := ht.2
      have hd : |t.val-(eventOrientedTime p).val| ≤ δ := abs_le.mpr ⟨by linarith,by linarith⟩
      refine ⟨hball ?_,?_⟩
      · simpa only [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq] using lt_of_le_of_lt hd hδn
      · rw [← hEventClock p,hGuideClockDistances]
        exact lt_of_le_of_lt hd hδη
  have hActualEventWindows (η : ↥P → ℝ) (hη : ∀ p, 0 < η p) :
      ∃ ell right : ↥P → Interval,
        (∀ p, 0 < ell p ∧ ell p < eventOrientedTime p ∧ eventOrientedTime p < right p ∧
          right p < orientedEntry) ∧
        (∀ p t, t ∈ Icc (ell p) (right p) →
          ambientB (joint.guideClock t) ∈ eventSupport p ∧
          |(joint.guideClock t).val-(eventRawTime p).val| < η p) ∧
        (∀ p q, p ≠ q → Disjoint (Icc (ell p) (right p)) (Icc (ell q) (right q))) ∧
        (∀ i j : Fin eventCount, i < j → right (eventLabel i) < ell (eventLabel j)) := by
    choose ell right hw using hIndividualEventWindow η hη
    have hb (p : ↥P) := (hw p).2.2.2.2
    have hd (p q : ↥P) (hpq : p ≠ q) :
        Disjoint (Icc (ell p) (right p)) (Icc (ell q) (right q)) := by
      apply Set.disjoint_left.mpr
      intro t htp htq
      exact Set.disjoint_left.mp (hEventSupportDisjoint p q hpq) (hb p t htp).1 (hb q t htq).1
    refine ⟨ell,right,fun p => ⟨(hw p).1,(hw p).2.1,(hw p).2.2.1,(hw p).2.2.2.1⟩,hb,hd,?_⟩
    intro i j hij
    have hpq : eventLabel i ≠ eventLabel j := eventLabel.injective.ne hij.ne
    have hc := hOrientedLabels i j hij
    by_contra! hn
    have hil : ell (eventLabel i) < eventOrientedTime (eventLabel i) := (hw _).2.1
    have hjr : eventOrientedTime (eventLabel j) < right (eventLabel j) := (hw _).2.2.1
    have hir : ell (eventLabel i) ≤ right (eventLabel i) := (hw _).2.1.le.trans (hw _).2.2.1.le
    have hjl : ell (eventLabel j) ≤ right (eventLabel j) := (hw _).2.1.le.trans (hw _).2.2.1.le
    apply Set.disjoint_left.mp (hd _ _ hpq)
    · show max (ell (eventLabel i)) (ell (eventLabel j)) ∈ Icc (ell (eventLabel i)) (right (eventLabel i))
      exact ⟨le_max_left _ _,max_le hir hn⟩
    · show max (ell (eventLabel i)) (ell (eventLabel j)) ∈ Icc (ell (eventLabel j)) (right (eventLabel j))
      exact ⟨le_max_right _ _,max_le (hil.le.trans (hc.le.trans hjr.le)) hjl⟩
  have hEventLongitudinalCoordinate (p : ↥P) (ell right : Interval)
      (hwin : 0 < ell ∧ ell < eventOrientedTime p ∧ eventOrientedTime p < right ∧ right < orientedEntry)
      (hsrc : ∀ t : Interval, t ∈ Icc ell right → ambientB (joint.guideClock t) ∈ eventSupport p) :
      ∃ X : C(Icc ell right,ℝ),
        (∀ t, X t = (eventFan p).chart (ambientB (joint.guideClock t.val)) 0) ∧
        (∀ t, (eventFan p).chart (ambientB (joint.guideClock t.val)) = Plane.mk (X t) 0) ∧
        (StrictMono X ∨ StrictAnti X) ∧
        X ⟨eventOrientedTime p,⟨hwin.2.1.le,hwin.2.2.1.le⟩⟩ = 0 := by
    letI : Fact (ell ≤ right) := ⟨hwin.2.1.le.trans hwin.2.2.1.le⟩
    let trace : C(Icc ell right,S) :=
      ⟨fun t => ambientB (joint.guideClock t.val),by fun_prop⟩
    have htrace (t : Icc ell right) : trace t ∈ (eventFan p).chart.source :=
      (hsrc t.val t.property).2.1
    have haxis (t : Icc ell right) : (eventFan p).chart (trace t) 1 = 0 := by
      apply hEventWholeAxis p (joint.guideClock t.val)
      rw [hEventAxisSource]
      exact ⟨(hsrc t.val t.property).2.1,(hsrc t.val t.property).2⟩
    have hc : Continuous ((eventFan p).chart ∘ trace) :=
      (eventFan p).chart.continuousOn.comp_continuous trace.continuous htrace
    let X : C(Icc ell right,ℝ) :=
      ⟨fun t => (eventFan p).chart (trace t) 0,
        (by fun_prop : Continuous (fun z : Plane => z 0)).comp hc⟩
    have hxi : Function.Injective X := by
      intro t u he
      apply Subtype.ext
      apply joint.guideClock.injective
      apply hAmbientB.injective
      apply (eventFan p).chart.injOn (htrace t) (htrace u)
      apply PiLp.ext
      intro i
      fin_cases i
      · exact he
      · change (eventFan p).chart (trace t) 1 = (eventFan p).chart (trace u) 1
        rw [haxis,haxis]
    refine ⟨X,fun _ => rfl,?_,X.continuous.strictMono_of_inj_boundedOrder' hxi,?_⟩
    · intro t
      apply PiLp.ext
      intro i
      fin_cases i
      · rfl
      · change (eventFan p).chart (trace t) 1 = 0
        exact haxis t
    · change (eventFan p).chart (b (joint.guideClock (eventOrientedTime p))).val 0 = 0
      rw [hEventClock,hRawCenter,(eventFan p).contact_zero]
      rfl
  -- Reuse the paid full fan reflection construction locally for event-axis order.
  have hReflectedEventFan (p : ↥F) (W : IncidentFanWindow F f V p) :
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
  have hIncreasingEventCoordinates (p : ↥P) (ell right : Interval)
      (hwin : 0 < ell ∧ ell < eventOrientedTime p ∧ eventOrientedTime p < right ∧ right < orientedEntry)
      (hsrc : ∀ t : Interval, t ∈ Icc ell right → ambientB (joint.guideClock t) ∈ eventSupport p) :
      ∃ W : IncidentFanWindow F f V p.val, ∃ X : C(Icc ell right,ℝ), ∃ τ : ℝ,
        (τ = -1 ∨ τ = 1) ∧ StrictMono X ∧
        X ⟨eventOrientedTime p,⟨hwin.2.1.le,hwin.2.2.1.le⟩⟩ = 0 ∧
        W.chart.source = (eventFan p).chart.source ∧
        (∀ y : S, W.chart y = τ • (eventFan p).chart y) ∧
        chartPull F W.chart (Metric.closedBall (0 : Plane) 1) =
          chartPull F (eventFan p).chart (Metric.closedBall (0 : Plane) 1) ∧
        chartPull F W.chart (Metric.ball (0 : Plane) 1) =
          chartPull F (eventFan p).chart (Metric.ball (0 : Plane) 1) ∧
        (chartPull F W.chart (Metric.closedBall (0 : Plane) 1) ⊆
          chartPull F (fan.window ⟨p.val,hPfan p.property⟩).chart (Metric.ball (0 : Plane) 1)) ∧
        (∀ h : p.val ∈ range b,
          incidentPorts f p.val W.chart W.left W.right (⟨some w,h⟩,false) 1 = 0 ∧
          incidentPorts f p.val W.chart W.left W.right (⟨some w,h⟩,true) 1 = 0) ∧
        (∀ j : incidentIndex f p.val, j.val ≠ some w →
          incidentPorts f p.val W.chart W.left W.right (j,false) 1 *
            incidentPorts f p.val W.chart W.left W.right (j,true) 1 < 0) ∧
        (∀ t : Icc ell right, W.chart (ambientB (joint.guideClock t.val)) = Plane.mk (X t) 0) := by
    obtain ⟨X,hX,hAxis,hOrder,hZero⟩ := hEventLongitudinalCoordinate p ell right hwin hsrc
    rcases hOrder with hm | ha
    · refine ⟨eventFan p,X,1,Or.inr rfl,hm,hZero,rfl,?_,rfl,rfl,
        (hEventFanProperties p).1,(hEventFanProperties p).2.1,(hEventFanProperties p).2.2,hAxis⟩
      intro y
      exact (one_smul ℝ _).symm
    · obtain ⟨W,hChart,hLeft,hRight⟩ := hReflectedEventFan p.val (eventFan p)
      have hMono : StrictMono (-X) := by
        intro t u htu
        change -X t < -X u
        exact neg_lt_neg (ha htu)
      have hSource : W.chart.source = (eventFan p).chart.source := by rw [hChart]; rfl
      have hCoordinates (y : S) : W.chart y = (-1 : ℝ) • (eventFan p).chart y := by
        rw [hChart]
        change -(eventFan p).chart y = (-1 : ℝ) • (eventFan p).chart y
        rw [neg_one_smul]
      have hClosed : chartPull F W.chart (Metric.closedBall (0 : Plane) 1) =
          chartPull F (eventFan p).chart (Metric.closedBall (0 : Plane) 1) := by
        ext y
        rw [hChart]
        change (y.val ∈ (eventFan p).chart.source ∧ -(eventFan p).chart y.val ∈ Metric.closedBall 0 1) ↔
          (y.val ∈ (eventFan p).chart.source ∧ (eventFan p).chart y.val ∈ Metric.closedBall 0 1)
        simp only [Metric.mem_closedBall,dist_zero_right,norm_neg]
      have hOpen : chartPull F W.chart (Metric.ball (0 : Plane) 1) =
          chartPull F (eventFan p).chart (Metric.ball (0 : Plane) 1) := by
        ext y
        rw [hChart]
        change (y.val ∈ (eventFan p).chart.source ∧ -(eventFan p).chart y.val ∈ Metric.ball 0 1) ↔
          (y.val ∈ (eventFan p).chart.source ∧ (eventFan p).chart y.val ∈ Metric.ball 0 1)
        simp only [Metric.mem_ball,dist_zero_right,norm_neg]
      refine ⟨W,-X,-1,Or.inl rfl,hMono,?_,hSource,hCoordinates,hClosed,hOpen,?_,?_,?_,?_⟩
      · simpa only [ContinuousMap.neg_apply,hZero,neg_zero]
      · rw [hClosed]
        exact (hEventFanProperties p).1
      · intro h
        rw [hChart,hLeft,hRight]
        change -(incidentPorts f p.val (eventFan p).chart (eventFan p).left (eventFan p).right (⟨some w,h⟩,false) 1) = 0 ∧
          -(incidentPorts f p.val (eventFan p).chart (eventFan p).left (eventFan p).right (⟨some w,h⟩,true) 1) = 0
        rw [(hEventFanProperties p).2.1 h |>.1,(hEventFanProperties p).2.1 h |>.2]
        norm_num
      · intro j hj
        rw [hChart,hLeft,hRight]
        change (-incidentPorts f p.val (eventFan p).chart (eventFan p).left (eventFan p).right (j,false) 1) *
          (-incidentPorts f p.val (eventFan p).chart (eventFan p).left (eventFan p).right (j,true) 1) < 0
        simpa only [neg_mul_neg] using (hEventFanProperties p).2.2 j hj
      · intro t
        rw [hChart]
        change -(eventFan p).chart (ambientB (joint.guideClock t.val)) = Plane.mk (-X t) 0
        rw [hAxis]
        ext i
        fin_cases i <;> simp [Plane.mk]
  -- Conditional consumer of the exact G3 formula, without asserting G3 existence.
  have hEventFormulaConsumer (H : S ≃ₜ S)
      (E : C(Interval × Icc (-1 : ℝ) 1,↥F))
      (hE : ∀ z, (E z).val = H (ambientGuide z))
      (ω scale η σ : ↥P → ℝ)
      (hBudgets : ∀ p, 0 < ω p ∧ ω p ≤ 1 ∧ 0 < scale p ∧ 0 < η p ∧ (σ p = -1 ∨ σ p = 1))
      (hFormula : ∀ p (t : Interval) (u : Icc (-1 : ℝ) 1),
        |t.val-(eventRawTime p).val| < η p → |u.val| ≤ ω p →
        H (ambientGuide (t,u)) ∈ (eventAxisChart p).source ∩ eventSupport p ∧
        eventAxisChart p (H (ambientGuide (t,u))) =
          Plane.mk (eventAxisChart p (ambientB t) 0) (σ p*scale p*u.val)) :
      ∃ ell right : ↥P → Interval,
        (∀ p, 0 < ell p ∧ ell p < eventOrientedTime p ∧ eventOrientedTime p < right p ∧
          right p < orientedEntry) ∧
        (∀ i j : Fin eventCount, i < j → right (eventLabel i) < ell (eventLabel j)) ∧
        ∀ p, ∃ W : IncidentFanWindow F f V p.val, ∃ X : C(Icc (ell p) (right p),ℝ), ∃ τ : ℝ,
          (τ = -1 ∨ τ = 1) ∧ (τ*σ p = -1 ∨ τ*σ p = 1) ∧ StrictMono X ∧
          (∀ hcenter : eventOrientedTime p ∈ Icc (ell p) (right p), X ⟨eventOrientedTime p,hcenter⟩ = 0) ∧
          chartPull F W.chart (Metric.closedBall (0 : Plane) 1) ⊆
            chartPull F (fan.window ⟨p.val,hPfan p.property⟩).chart (Metric.ball (0 : Plane) 1) ∧
          (∀ h : p.val ∈ range b,
            incidentPorts f p.val W.chart W.left W.right (⟨some w,h⟩,false) 1 = 0 ∧
            incidentPorts f p.val W.chart W.left W.right (⟨some w,h⟩,true) 1 = 0) ∧
          (∀ j : incidentIndex f p.val, j.val ≠ some w →
            incidentPorts f p.val W.chart W.left W.right (j,false) 1 *
              incidentPorts f p.val W.chart W.left W.right (j,true) 1 < 0) ∧
          ∀ (t : Interval) (ht : t ∈ Icc (ell p) (right p)) (u : Icc (-1 : ℝ) 1), |u.val| ≤ ω p →
            E (joint.guideClock t,u) ∈ chartPull F W.chart (Metric.ball (0 : Plane) 1) ∧
            W.chart (E (joint.guideClock t,u)).val = Plane.mk (X ⟨t,ht⟩) (τ*σ p*scale p*u.val) := by
    obtain ⟨ell,right,hw,hSupport,hDisjoint,hOrder⟩ :=
      hActualEventWindows η (fun p => (hBudgets p).2.2.2.1)
    refine ⟨ell,right,hw,hOrder,?_⟩
    intro p
    obtain ⟨W,X,τ,hτ,hMono,hZero,hSource,hCoordinates,hClosed,hOpen,hNested,hAxis,hThird,hActual⟩ :=
      hIncreasingEventCoordinates p (ell p) (right p) (hw p) (fun t ht => (hSupport p t ht).1)
    have hSign : τ*σ p = -1 ∨ τ*σ p = 1 := by
      rcases hτ with hτ | hτ <;> rcases (hBudgets p).2.2.2.2 with hσ | hσ <;> simp [hτ,hσ]
    refine ⟨W,X,τ,hτ,hSign,hMono,fun _ => hZero,hNested,hAxis,hThird,?_⟩
    intro t ht u hu
    have hc := hFormula p (joint.guideClock t) u (hSupport p t ht).2 hu
    have hUnit : E (joint.guideClock t,u) ∈
        chartPull F (eventFan p).chart (Metric.ball (0 : Plane) 1) := by
      change (E (joint.guideClock t,u)).val ∈ (eventFan p).chart.source ∧
        (eventFan p).chart (E (joint.guideClock t,u)).val ∈ Metric.ball (0 : Plane) 1
      rw [hE]
      exact hc.1.2.2
    have hOldFormula : (eventFan p).chart (E (joint.guideClock t,u)).val =
        Plane.mk ((eventFan p).chart (ambientB (joint.guideClock t)) 0) (σ p*scale p*u.val) := by
      rw [hE]
      exact hc.2
    have hXIdentity : τ*((eventFan p).chart (ambientB (joint.guideClock t)) 0) = X ⟨t,ht⟩ := by
      have he := congrArg (fun z : Plane => z 0) (hActual ⟨t,ht⟩)
      rw [hCoordinates] at he
      exact he
    refine ⟨hOpen.symm ▸ hUnit,?_⟩
    rw [hCoordinates,hOldFormula]
    apply PiLp.ext
    intro i
    fin_cases i
    · exact hXIdentity
    · change τ*(σ p*scale p*u.val) = τ*σ p*scale p*u.val
      ring
  have hCommonEventFormulaRadius (ω : ↥P → ℝ) (hω : ∀ p, 0 < ω p) :
      ∃ ζ : ℝ, 0 < ζ ∧ ζ < joint.entryMargin/4 ∧ ζ < joint.bound/2 ∧ ∀ p, ζ < ω p := by
    let sizes : Finset ℝ := insert (joint.entryMargin/4)
      (insert (joint.bound/2) (Finset.univ.image ω))
    have hs : sizes.Nonempty := Finset.insert_nonempty _ _
    have hPositive (z : ℝ) (hz : z ∈ sizes) : 0 < z := by
      simp only [sizes,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hz
      rcases hz with rfl | rfl | ⟨p,rfl⟩
      · exact div_pos joint.entryMargin_pos (by norm_num)
      · exact div_pos joint.bound_pos (by norm_num)
      · exact hω p
    let m : ℝ := sizes.min' hs
    have hm : 0 < m := hPositive _ (sizes.min'_mem hs)
    have hμ : m ≤ joint.entryMargin/4 := sizes.min'_le _ (by simp [sizes])
    have hB : m ≤ joint.bound/2 := sizes.min'_le _ (by simp [sizes])
    have hp (p : ↥P) : m ≤ ω p := sizes.min'_le _ (by simp [sizes])
    refine ⟨m/2,div_pos hm (by norm_num),lt_of_lt_of_le (half_lt_self hm) hμ,
      lt_of_lt_of_le (half_lt_self hm) hB,fun p => lt_of_lt_of_le (half_lt_self hm) (hp p)⟩
  -- Actual G3 candidate call; final admission remains pending reader/provider acceptance.
  obtain ⟨calibrationH,calibrationWidth,calibrationScale,calibrationRadius,calibrationSign,
      hCalibrationBudgets,hCalibrationCenter,hCalibrationSupport,hCalibrationFormula⟩ :=
    CurveComplex.source_finite_supported_internal_collar_calibration ambientB hAmbientB
      ambientGuide hAmbientGuide (fun t => congrArg Subtype.val (hGuideCenterActual t))
      eventRawTime hRawInjective hRawInterior eventAxisChart hEventAxisPoint hEventAxisZero
      hEventWholeAxis eventSupport hEventSupportOpen hEventSupportAmbientPoint hEventSupportDisjoint
  have hCalibrationSmallFix (y : S) (hy : y ∉ Rsmall) : calibrationH y = y := by
    apply hCalibrationSupport
    exact fun h => hy (hEventUnionSmall h)
  obtain ⟨correctedJoint,hCorrectedGuideEq,hCorrectedBound,hCorrectedClock,hCorrectedCut,
      hCorrectedOldStrip,hCorrectedActiveWindow,hCorrectedGuideWindow,hCorrectedGuideClock,
      hCorrectedEntryTime,hCorrectedBoundaryLine,hCorrectedTerminalCut,hCorrectedCornerFan,
      hCorrectedCornerDelta,hCorrectedCornerEntry,hCorrectedEntryMargin,hCorrectedKappa,
      hCorrectedCapBound,hCorrectedOldCornerWindow,hCorrectedOldCornerWidth,hCorrectedOldCornerX,
      hCorrectedOldCornerScale,hCorrectedOldCornerSign,hCorrectedOldNegativeWidth⟩ :=
    hCompatibleJointFromCorrection calibrationH hCalibrationCenter hCalibrationSmallFix
  obtain ⟨eventWindowLeft,eventWindowRight,hEventWindows,hEventWindowsOrder,hCalibratedEvents⟩ :=
    hEventFormulaConsumer calibrationH correctedJoint.guideStrip hCorrectedGuideEq
      calibrationWidth calibrationScale calibrationRadius calibrationSign hCalibrationBudgets hCalibrationFormula
  obtain ⟨commonFormulaRadius,hCommonFormulaRadius,hCommonFormulaMargin,hCommonFormulaBound,hCommonFormulaEvents⟩ :=
    hCommonEventFormulaRadius calibrationWidth (fun p => (hCalibrationBudgets p).1)
  have hOrderedAxisTimeRoute (ell right : Interval) (hlr : ell < right)
      (X : C(Icc ell right,ℝ)) (hX : StrictMono X) :
      ∃ T : C(Interval,Interval),
        StrictMono T ∧ T 0 = ell ∧ T 1 = right ∧
        (∀ t, T t ∈ Icc ell right) ∧
        ∀ t (h : T t ∈ Icc ell right),
          X ⟨T t,h⟩ = (1-t.val)*X ⟨ell,⟨le_rfl,hlr.le⟩⟩ +
            t.val*X ⟨right,⟨hlr.le,le_rfl⟩⟩ := by
    letI : Fact (ell ≤ right) := ⟨hlr.le⟩
    have hBotTop : (⊥ : Icc ell right) < ⊤ := hlr
    have hXGap : X ⊥ < X ⊤ := hX hBotTop
    have hEmbedding : IsEmbedding X := (X.continuous.isClosedEmbedding hX.injective).isEmbedding
    let Q := hEmbedding.toHomeomorph
    have hRange : range X = Icc (X ⊥) (X ⊤) := by
      simpa only [Icc_bot_top,image_univ] using X.continuous.image_Icc_of_strictMono hX (a := ⊥) (b := ⊤)
    let line : C(Interval,ℝ) := ⟨fun t => (1-t.val)*X ⊥+t.val*X ⊤,by fun_prop⟩
    have hLineRange (t : Interval) : line t ∈ range X := by
      rw [hRange]
      change X ⊥ ≤ (1-t.val)*X ⊥+t.val*X ⊤ ∧ (1-t.val)*X ⊥+t.val*X ⊤ ≤ X ⊤
      constructor <;> nlinarith only [t.property.1,t.property.2,
        mul_nonneg t.property.1 (sub_nonneg.mpr hXGap.le),
        mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hXGap.le)]
    let lineInRange : C(Interval,range X) :=
      ⟨fun t => ⟨line t,hLineRange t⟩,line.continuous.subtype_mk _⟩
    let T : C(Interval,Interval) :=
      ⟨fun t => (Q.symm (lineInRange t)).val,by fun_prop⟩
    have hApply (t : Interval) : X (Q.symm (lineInRange t)) = line t :=
      congrArg Subtype.val (Q.apply_symm_apply (lineInRange t))
    have hLineOrder : StrictMono line := by
      intro t u htu
      change (1-t.val)*X ⊥+t.val*X ⊤ < (1-u.val)*X ⊥+u.val*X ⊤
      have hh : t.val < u.val := htu
      nlinarith only [mul_pos (sub_pos.mpr hh) (sub_pos.mpr hXGap)]
    have hTOrder : StrictMono T := by
      intro t u htu
      change (Q.symm (lineInRange t)).val < (Q.symm (lineInRange u)).val
      apply hX.lt_iff_lt.mp
      rw [hApply,hApply]
      exact hLineOrder htu
    have hZero : Q.symm (lineInRange 0) = (⊥ : Icc ell right) := by
      apply hX.injective
      rw [hApply]
      simp [line]
    have hOne : Q.symm (lineInRange 1) = (⊤ : Icc ell right) := by
      apply hX.injective
      rw [hApply]
      simp [line]
    refine ⟨T,hTOrder,?_,?_,fun t => (Q.symm (lineInRange t)).property,?_⟩
    · change (Q.symm (lineInRange 0)).val = ell
      rw [hZero]
      rfl
    · change (Q.symm (lineInRange 1)).val = right
      rw [hOne]
      rfl
    · intro t h
      exact hApply t
  have hOrientedCoreSelected (t : Interval) (ht : t ∈ Ioo (0 : Interval) orientedEntry) :
      joint.guideClock t ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) := by
    have he : joint.guideClock orientedEntry = actualEntry := joint.guideClock.apply_symm_apply _
    apply hSmallTimeSelected (z := (joint.guideClock t,⟨0,by norm_num⟩))
    refine ⟨?_,?_,by simpa using div_pos joint.entryMargin_pos (by norm_num : (0:ℝ)<4)⟩
    · rcases joint.guideClock_increasing with hm | ha
      · have h := hm ht.1
        rw [joint.guideClock_start] at h
        exact lt_of_le_of_lt (min_le_left _ _) h
      · have h := ha ht.2
        rw [he] at h
        exact lt_of_le_of_lt (min_le_right _ _) h
    · rcases joint.guideClock_increasing with hm | ha
      · have h := hm ht.2
        rw [he] at h
        exact lt_of_lt_of_le h (le_max_right _ _)
      · have h := ha ht.1
        rw [joint.guideClock_start] at h
        exact lt_of_lt_of_le h (le_max_left _ _)
  have hHorizontalRadialContacts (l r : Plane) (hopp : l 1*r 1 < 0) (height : ℝ) (hheight : height ≠ 0) :
      ({z : Plane | z 1 = height} ∩ (segment ℝ l 0 ∪ segment ℝ 0 r)).Subsingleton := by
    have hParam (v z : Plane) (hz : z ∈ segment ℝ (0 : Plane) v) :
        ∃ q : ℝ, 0 ≤ q ∧ z = q • v := by
      rw [segment_eq_image'] at hz
      obtain ⟨q,hq,he⟩ := hz
      exact ⟨q,hq.1,by simpa [AffineMap.lineMap_apply] using he.symm⟩
    have hSame (v y z : Plane) (hy : y 1 = height) (hz : z 1 = height)
        (hyp : y ∈ segment ℝ (0 : Plane) v) (hzp : z ∈ segment ℝ (0 : Plane) v) : y = z := by
      obtain ⟨a,ha,hya⟩ := hParam v y hyp
      obtain ⟨b,hb,hzb⟩ := hParam v z hzp
      have hv : v 1 ≠ 0 := by
        intro he
        rw [hya] at hy
        change a*v 1 = height at hy
        exact hheight (by simpa [he] using hy.symm)
      have hab : a = b := mul_right_cancel₀ hv (by
        have hyh := congrArg (fun p : Plane => p 1) hya
        have hzh := congrArg (fun p : Plane => p 1) hzb
        change y 1 = a*v 1 at hyh
        change z 1 = b*v 1 at hzh
        exact hyh.symm.trans ((hy.trans hz.symm).trans hzh))
      rw [hya,hzb,hab]
    have hDifferent (v w y z : Plane) (hvw : v 1*w 1 < 0) (hy : y 1 = height) (hz : z 1 = height)
        (hyp : y ∈ segment ℝ (0 : Plane) v) (hzp : z ∈ segment ℝ (0 : Plane) w) : False := by
      obtain ⟨a,ha,hya⟩ := hParam v y hyp
      obtain ⟨b,hb,hzb⟩ := hParam w z hzp
      have hay : a*v 1 = height := by rw [hya] at hy; exact hy
      have hbz : b*w 1 = height := by rw [hzb] at hz; exact hz
      have hap : 0 < a := lt_of_le_of_ne ha (by intro he; exact hheight (by simpa [← he] using hay.symm))
      have hbp : 0 < b := lt_of_le_of_ne hb (by intro he; exact hheight (by simpa [← he] using hbz.symm))
      have hn : a*b*(v 1*w 1) < 0 := mul_neg_of_pos_of_neg (mul_pos hap hbp) hvw
      have he : a*b*(v 1*w 1) = height*height := by
        calc
          a*b*(v 1*w 1) = (a*v 1)*(b*w 1) := by ring
          _ = height*height := by rw [hay,hbz]
      rw [he] at hn
      exact (mul_self_nonneg height).not_gt hn
    intro y hy z hz
    rcases hy.2 with hyl | hyr <;> rcases hz.2 with hzl | hzr
    · exact hSame l y z hy.1 hz.1 (segment_symm ℝ l 0 ▸ hyl) (segment_symm ℝ l 0 ▸ hzl)
    · exact (hDifferent l r y z hopp hy.1 hz.1 (segment_symm ℝ l 0 ▸ hyl) hzr).elim
    · exact (hDifferent r l y z (by simpa only [mul_comm] using hopp) hy.1 hz.1 hyr
        (segment_symm ℝ l 0 ▸ hzl)).elim
    · exact hSame r y z hy.1 hz.1 hyr hzr
  have hHorizontalRailContacts (p : ↥P) (W : IncidentFanWindow F f V p.val)
      (rail : C(Interval,↥F)) (height : ℝ) (hheight : height ≠ 0)
      (hUnit : ∀ t, rail t ∈ chartPull F W.chart (Metric.ball (0 : Plane) 1))
      (hHeight : ∀ t, W.chart (rail t).val 1 = height)
      (hThird : ∀ j : incidentIndex f p.val, j.val ≠ some w →
        incidentPorts f p.val W.chart W.left W.right (j,false) 1 *
          incidentPorts f p.val W.chart W.left W.right (j,true) 1 < 0) :
      (∀ k : Option ι, k ≠ some v → k ≠ some w → (range rail ∩ range (f k)).Subsingleton) ∧
      (∀ k : Option ι, p.val ∉ range (f k) → Disjoint (range rail) (range (f k))) := by
    refine ⟨?_,?_⟩
    · intro k hkv hkw
      by_cases hinc : p.val ∈ range (f k)
      · let j : incidentIndex f p.val := ⟨k,hinc⟩
        intro y hy z hz
        obtain ⟨t,rfl⟩ := hy.1
        obtain ⟨s,rfl⟩ := hz.1
        apply Subtype.ext
        apply W.chart.injOn (hUnit t).1 (hUnit s).1
        apply hHorizontalRadialContacts _ _ (hThird j hkw) height hheight
        · exact ⟨hHeight t,(hFanTrace p.val W j (rail t) (hUnit t).1
            (Metric.ball_subset_closedBall (hUnit t).2)).mp hy.2⟩
        · exact ⟨hHeight s,(hFanTrace p.val W j (rail s) (hUnit s).1
            (Metric.ball_subset_closedBall (hUnit s).2)).mp hz.2⟩
      · have hd : Disjoint (range rail) (range (f k)) := (W.nonincident_clear k hinc).mono (by
          rintro y ⟨t,rfl⟩; exact ⟨(hUnit t).1,Metric.ball_subset_closedBall (hUnit t).2⟩) Subset.rfl
        rw [Set.disjoint_iff_inter_eq_empty.mp hd]
        exact Set.subsingleton_empty
    · intro k hk
      apply (W.nonincident_clear k hk).mono _ Subset.rfl
      rintro y ⟨t,rfl⟩
      exact ⟨(hUnit t).1,Metric.ball_subset_closedBall (hUnit t).2⟩
  -- Literal chart coordinates on an actual rectangle of the unchanged guide.
  have hGuideRectangleChart (ell right : Interval) (hlr : ell < right)
      (a : ℝ) (ha : 0 < a) (haOne : a ≤ 1)
      (c : OpenPartialHomeomorph S Plane)
      (hbox : ∀ t ∈ Icc ell right, ∀ u : Icc (-1 : ℝ) 1, |u.val| ≤ a →
        (correctedJoint.guideStrip (joint.guideClock t,u)).val ∈ c.source) :
      ∃ Q : OpenPartialHomeomorph S Plane, Q.source = c.source ∧
        ∀ t ∈ Icc ell right, ∀ u : Icc (-1 : ℝ) 1, |u.val| ≤ a →
          Q (correctedJoint.guideStrip (joint.guideClock t,u)).val =
            Plane.mk (2*(t.val-ell.val)/(right.val-ell.val)-1) (u.val/a) := by
    have hd : 0 < right.val-ell.val := sub_pos.mpr hlr
    have hx (z : ↥(Plane.closedSquare 0 1)) : -1 ≤ (z:Plane) 0 ∧ (z:Plane) 0 ≤ 1 :=
      abs_le.mp ((Plane.abs_zero_le_supNorm z).trans (mem_closedSquare_zero_one.mp z.property))
    have hy (z : ↥(Plane.closedSquare 0 1)) : -1 ≤ (z:Plane) 1 ∧ (z:Plane) 1 ≤ 1 :=
      abs_le.mp ((Plane.abs_one_le_supNorm z).trans (mem_closedSquare_zero_one.mp z.property))
    let k : ↥(Plane.closedSquare 0 1) → Interval × Icc (-1 : ℝ) 1 := fun z =>
      (joint.guideClock ⟨ell.val+(right.val-ell.val)*((z:Plane) 0+1)/2,by
        constructor <;> nlinarith only [(hx z).1,(hx z).2,ell.property.1,right.property.2,hd]⟩,
       ⟨a*(z:Plane) 1,by constructor <;> nlinarith only [(hy z).1,(hy z).2,ha,haOne]⟩)
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have hki : Function.Injective k := by
      intro z w he
      have h0 := congrArg (fun q : Interval × Icc (-1 : ℝ) 1 => joint.guideClock.symm q.1) he
      have h1 := congrArg (fun q : Interval × Icc (-1 : ℝ) 1 => q.2.val) he
      simp only [k,joint.guideClock.symm_apply_apply] at h0
      have h0r := congrArg Subtype.val h0
      apply Subtype.ext
      ext i
      fin_cases i
      · change ell.val+(right.val-ell.val)*((z:Plane) 0+1)/2 =
          ell.val+(right.val-ell.val)*((w:Plane) 0+1)/2 at h0r
        change (z:Plane) 0 = (w:Plane) 0
        nlinarith only [h0r,hd]
      · change a*(z:Plane) 1 = a*(w:Plane) 1 at h1
        exact mul_left_cancel₀ ha.ne' h1
    let T : ↥(Plane.closedSquare 0 1) → S := fun z => (correctedJoint.guideStrip (k z)).val
    letI : CompactSpace ↥(Plane.closedSquare 0 1) :=
      isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
    have hT : IsEmbedding T :=
      IsEmbedding.subtypeVal.comp (correctedJoint.guideStrip_embedded.comp
        ((hkc.isClosedEmbedding hki).isEmbedding))
    have hTc (z : ↥(Plane.closedSquare 0 1)) : T z ∈ c.source := by
      apply hbox
      · constructor
        · change ell.val ≤ ell.val+(right.val-ell.val)*((z:Plane) 0+1)/2
          nlinarith only [(hx z).1,hd]
        · change ell.val+(right.val-ell.val)*((z:Plane) 0+1)/2 ≤ right.val
          nlinarith only [(hx z).2,hd]
      · change |a*(z:Plane) 1| ≤ a
        rw [abs_mul,abs_of_pos ha]
        exact (mul_le_mul_of_nonneg_left (abs_le.mpr (hy z)) ha.le).trans_eq (mul_one a)
    have hCc : Continuous (c ∘ T) := c.continuousOn.comp_continuous hT.continuous hTc
    have hCi : Function.Injective (c ∘ T) := by
      intro z w he
      exact hT.injective (c.injOn (hTc z) (hTc w) he)
    obtain ⟨H,hH⟩ := exists_ambient_extension_of_embedded_closed_square (c ∘ T)
      ((hCc.isClosedEmbedding hCi).isEmbedding)
    let Q : OpenPartialHomeomorph S Plane := c.transHomeomorph H.symm
    refine ⟨Q,by simp [Q],?_⟩
    intro t ht u hu
    let x : ℝ := 2*(t.val-ell.val)/(right.val-ell.val)-1
    let y : ℝ := u.val/a
    have hx' : -1 ≤ x ∧ x ≤ 1 := by
      dsimp [x]
      have hlow : 0 ≤ (t.val-ell.val)/(right.val-ell.val) := div_nonneg (sub_nonneg.mpr ht.1) hd.le
      have hhigh : (t.val-ell.val)/(right.val-ell.val) ≤ 1 :=
        (div_le_one hd).mpr (sub_le_sub_right (show t.val ≤ right.val from ht.2) ell.val)
      rw [mul_div_assoc]
      constructor <;> linarith only [hlow,hhigh]
    have hy' : |y| ≤ 1 := by
      dsimp [y]
      rw [abs_div,abs_of_pos ha]
      exact (div_le_one ha).mpr hu
    let z : ↥(Plane.closedSquare 0 1) := ⟨Plane.mk x y,by
      rw [mem_closedSquare_zero_one]
      exact max_le (abs_le.mpr hx') hy'⟩
    have hk : k z = (joint.guideClock t,u) := by
      apply Prod.ext
      · apply congrArg joint.guideClock
        apply Subtype.ext
        change ell.val+(right.val-ell.val)*(x+1)/2 = t.val
        dsimp [x]
        field_simp [hd.ne']
        <;> ring
      · apply Subtype.ext
        change a*y = u.val
        dsimp [y]
        field_simp [ha.ne']
    have hh := hH z
    change H z.val = c (T z) at hh
    have hz : T z = (correctedJoint.guideStrip (joint.guideClock t,u)).val :=
      congrArg (fun v => (correctedJoint.guideStrip v).val) hk
    rw [hz] at hh
    change H.symm (c (correctedJoint.guideStrip (joint.guideClock t,u)).val) = _
    rw [← hh,H.symm_apply_apply]
  -- Actual old contact times are the only center obstructions on the guide prefix.
  have hOrientedSecond (t : Interval) (ht : t ≤ orientedEntry) :
      ∃ s ∈ Icc (0 : Interval) joint.guideEntryTime,
        orientedAffine s = t ∧ b (joint.guideClock t) = d.second s := by
    have hc : Continuous orientedAffine := joint.guideClock.symm.continuous.comp
      (CurveComplex.BranchedDoubleCover.intervalSegment d.bStart d.bFinish).continuous
    have hi := hc.image_Icc_of_strictMono hOrientedAffine (a := 0) (b := joint.guideEntryTime)
    have hm : t ∈ orientedAffine '' Icc (0 : Interval) joint.guideEntryTime := by
      rw [hi,hOrientedZero]
      exact ⟨unitInterval.nonneg _,ht⟩
    obtain ⟨s,hs,he⟩ := hm
    refine ⟨s,hs,he,?_⟩
    rw [← he]
    dsimp only [orientedAffine]
    rw [joint.guideClock.apply_symm_apply]
    exact (d.second_eq s).symm
  have hGuideCenterClear (t : Interval) (ht : t ≤ orientedEntry)
      (havoid : ∀ p : ↥P, t ≠ eventOrientedTime p) :
      b (joint.guideClock t) ∉ outgoingObstacles := by
    obtain ⟨s,hs,he,hcenter⟩ := hOrientedSecond t ht
    rw [hcenter]
    intro hout
    obtain ⟨k,hk⟩ := mem_iUnion.mp hout
    have hn : d.second s ≠ d.first 1 := by
      intro hh
      have hs1 : s = 1 := d.second_embedded.injective (hh.trans d.corner_eq)
      rw [hs1] at hs
      exact (not_le_of_gt joint.guideEntryTime_interior.2) hs.2
    let p : ↥P := ⟨d.second s,⟨⟨⟨s,rfl⟩,by simpa using hn⟩,k.val,k.property,hk⟩⟩
    have hst : pTime p = s := d.second_embedded.injective (hpTime p)
    apply havoid p
    change t = orientedAffine (pTime p)
    rw [hst]
    exact he.symm
  let clearGuideTimes : Set Interval := Icc (0 : Interval) orientedEntry \
    ⋃ p : ↥P, Ioo (eventWindowLeft p) (eventWindowRight p)
  have hClearGuideTimesCompact : IsCompact clearGuideTimes :=
    isCompact_Icc.diff (isOpen_iUnion (fun _ => isOpen_Ioo))
  have hClearGuideTimesCenter (t : Interval) (ht : t ∈ clearGuideTimes) :
      b (joint.guideClock t) ∉ outgoingObstacles := by
    apply hGuideCenterClear t ht.1.2
    intro p he
    apply ht.2
    apply mem_iUnion.mpr
    refine ⟨p,?_⟩
    rw [he]
    exact ⟨(hEventWindows p).2.1,(hEventWindows p).2.2.1⟩
  let orientedCorrectedGuide : C(Interval × Icc (-1 : ℝ) 1,↥F) :=
    ⟨fun z => correctedJoint.guideStrip (joint.guideClock z.1,z.2),by fun_prop⟩
  have hClearGuideUniformWidth : ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
      ∀ t ∈ clearGuideTimes, ∀ u : Icc (-1 : ℝ) 1, |u.val| ≤ a →
        orientedCorrectedGuide (t,u) ∉ outgoingObstacles := by
    let O : Set (Interval × Icc (-1 : ℝ) 1) := orientedCorrectedGuide ⁻¹' outgoingObstaclesᶜ
    have hO : IsOpen O := houtCompact.isClosed.isOpen_compl.preimage orientedCorrectedGuide.continuous
    have hbase : clearGuideTimes ×ˢ ({⟨0,by norm_num⟩} : Set (Icc (-1 : ℝ) 1)) ⊆ O := by
      rintro ⟨t,u⟩ ⟨ht,hu⟩
      have he : u = ⟨0,by norm_num⟩ := hu
      subst u
      change correctedJoint.guideStrip (joint.guideClock t,⟨0,by norm_num⟩) ∉ outgoingObstacles
      rw [correctedJoint.guideStrip_center]
      exact hClearGuideTimesCenter t ht
    obtain ⟨A,W,hA,hW,hTA,h0W,hAW⟩ := generalized_tube_lemma
      hClearGuideTimesCompact isCompact_singleton hO hbase
    let clip : ℝ → Icc (-1 : ℝ) 1 := projIcc (-1) 1 (by norm_num)
    have h0 : (0 : ℝ) ∈ clip ⁻¹' W := by
      simpa [clip,projIcc_of_mem] using h0W (mem_singleton (⟨0,by norm_num⟩ : Icc (-1 : ℝ) 1))
    obtain ⟨d,hd,hdW⟩ := Metric.mem_nhds_iff.mp ((hW.preimage continuous_projIcc).mem_nhds h0)
    let a : ℝ := min (d/2) (1/2)
    have ha : 0 < a := by dsimp [a]; positivity
    have ha1 : a ≤ 1 := (min_le_right (d/2) (1/2 : ℝ)).trans (by norm_num)
    have had : a < d := by
      have h := min_le_left (d/2) (1/2 : ℝ)
      dsimp only [a]
      linarith
    refine ⟨a,ha,ha1,?_⟩
    intro t ht u hu
    apply hAW
    refine ⟨hTA ht,?_⟩
    have hb : u.val ∈ Metric.ball (0 : ℝ) d := by
      simpa [Metric.mem_ball,Real.dist_eq] using hu.trans_lt had
    have hw := hdW hb
    change clip u.val ∈ W at hw
    simpa only [clip,projIcc_of_mem _ u.property] using hw
  obtain ⟨clearGuideWidth,hClearGuideWidth,hClearGuideWidthOne,hClearGuideWidthClear⟩ :=
    hClearGuideUniformWidth
  let clearGapLeft (i : Fin (eventCount+1)) : Interval :=
    if h : i.val = 0 then 0 else eventWindowRight (eventLabel ⟨i.val-1,by omega⟩)
  let clearGapRight (i : Fin (eventCount+1)) : Interval :=
    if h : i.val = eventCount then orientedEntry else eventWindowLeft (eventLabel ⟨i.val,by omega⟩)
  have hOrientedEntryPositive : 0 < orientedEntry := by
    simpa only [hOrientedZero] using hOrientedAffine joint.guideEntryTime_interior.1
  have hClearGapOrder (i : Fin (eventCount+1)) : clearGapLeft i < clearGapRight i := by
    by_cases hi0 : i.val = 0
    · by_cases him : i.val = eventCount
      · simpa only [clearGapLeft,clearGapRight,dif_pos hi0,dif_pos him] using hOrientedEntryPositive
      · simpa only [clearGapLeft,clearGapRight,dif_pos hi0,dif_neg him] using
          (hEventWindows (eventLabel ⟨i.val,by omega⟩)).1
    · by_cases him : i.val = eventCount
      · simpa only [clearGapLeft,clearGapRight,dif_neg hi0,dif_pos him] using
          (hEventWindows (eventLabel ⟨i.val-1,by omega⟩)).2.2.2
      · simpa only [clearGapLeft,clearGapRight,dif_neg hi0,dif_neg him] using
          hEventWindowsOrder ⟨i.val-1,by omega⟩ ⟨i.val,by omega⟩ (by change i.val-1 < i.val; omega)
  have hClearGapCore (i : Fin (eventCount+1)) :
      Icc (clearGapLeft i) (clearGapRight i) ⊆ Icc (0 : Interval) orientedEntry := by
    intro t ht
    have hl : 0 ≤ clearGapLeft i := unitInterval.nonneg _
    have hr : clearGapRight i ≤ orientedEntry := by
      dsimp only [clearGapRight]
      split
      · exact le_rfl
      · exact ((hEventWindows _).2.1.trans ((hEventWindows _).2.2.1.trans (hEventWindows _).2.2.2)).le
    exact ⟨hl.trans ht.1,ht.2.trans hr⟩
  have hClearGapTimes (i : Fin (eventCount+1)) :
      Icc (clearGapLeft i) (clearGapRight i) ⊆ clearGuideTimes := by
    intro t ht
    refine ⟨hClearGapCore i ht,?_⟩
    intro hwindow
    obtain ⟨p,hp⟩ := mem_iUnion.mp hwindow
    let j : Fin eventCount := eventLabel.symm p
    have hjp : eventLabel j = p := eventLabel.apply_symm_apply p
    by_cases hji : j.val < i.val
    · have hi0 : i.val ≠ 0 := by omega
      let prev : Fin eventCount := ⟨i.val-1,by omega⟩
      have hprev : eventWindowRight p ≤ eventWindowRight (eventLabel prev) := by
        by_cases he : j = prev
        · rw [← hjp,he]
        · have hlt : j < prev := by
            change j.val < i.val-1
            have hn : j.val ≠ prev.val := fun h => he (Fin.ext h)
            dsimp [prev] at hn
            omega
          exact (hjp ▸ (hEventWindowsOrder j prev hlt)).le.trans
            ((hEventWindows _).2.1.trans (hEventWindows _).2.2.1).le
      have htl : eventWindowRight (eventLabel prev) ≤ t := by
        simpa only [clearGapLeft,dif_neg hi0,prev] using ht.1
      exact (not_lt_of_ge (hprev.trans htl)) hp.2
    · have him : i.val ≠ eventCount := by omega
      let next : Fin eventCount := ⟨i.val,by omega⟩
      have hnext : eventWindowLeft (eventLabel next) ≤ eventWindowLeft p := by
        by_cases he : next = j
        · rw [he,hjp]
        · have hlt : next < j := by
            change i.val < j.val
            have hn : next.val ≠ j.val := fun h => he (Fin.ext h)
            dsimp [next] at hn
            omega
          exact ((hEventWindows _).2.1.trans (hEventWindows _).2.2.1).le.trans
            (hjp ▸ (hEventWindowsOrder next j hlt)).le
      have htr : t ≤ eventWindowLeft (eventLabel next) := by
        simpa only [clearGapRight,dif_neg him,next] using ht.2
      exact (not_lt_of_ge (htr.trans hnext)) hp.1
  have hActualClearGapBox (i : Fin (eventCount+1)) (t : Interval)
      (ht : t ∈ Icc (clearGapLeft i) (clearGapRight i))
      (u : Icc (-1 : ℝ) 1) (hu : |u.val| ≤ clearGuideWidth) :
      correctedJoint.guideStrip (joint.guideClock t,u) ∉ outgoingObstacles :=
    hClearGuideWidthClear t (hClearGapTimes i ht) u hu
  have hOrientedSelectedClosed (t : Interval) (ht : t ≤ orientedEntry) :
      joint.guideClock t ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) := by
    obtain ⟨s,hs,he,_⟩ := hOrientedSecond t ht
    have hclock := congrArg joint.guideClock he
    dsimp only [orientedAffine] at hclock
    rw [joint.guideClock.apply_symm_apply] at hclock
    rw [← hclock]
    have hlo0 : (min d.bStart d.bFinish).val ≤ d.bStart.val := min_le_left _ _
    have hlo1 : (min d.bStart d.bFinish).val ≤ d.bFinish.val := min_le_right _ _
    have hhi0 : d.bStart.val ≤ (max d.bStart d.bFinish).val := le_max_left _ _
    have hhi1 : d.bFinish.val ≤ (max d.bStart d.bFinish).val := le_max_right _ _
    change (min d.bStart d.bFinish).val ≤ (1-s.val)*d.bStart.val+s.val*d.bFinish.val ∧
      (1-s.val)*d.bStart.val+s.val*d.bFinish.val ≤ (max d.bStart d.bFinish).val
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr hlo0),
        mul_nonneg s.property.1 (sub_nonneg.mpr hlo1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr hhi0),
        mul_nonneg s.property.1 (sub_nonneg.mpr hhi1)]
  have hRectangleRailFactory (ell right : Interval) (hlr : ell < right)
      (hentry : right ≤ orientedEntry) (a : ℝ) (ha : 0 < a) (haOne : a ≤ 1)
      (c : OpenPartialHomeomorph S Plane)
      (hbox : ∀ t ∈ Icc ell right, ∀ u : Icc (-1 : ℝ) 1, |u.val| ≤ a →
        (correctedJoint.guideStrip (joint.guideClock t,u)).val ∈ c.source)
      (hclear : ∀ t ∈ Icc ell right, ∀ u : Icc (-1 : ℝ) 1, |u.val| ≤ a →
        correctedJoint.guideStrip (joint.guideClock t,u) ∉ outgoingObstacles) :
      ∃ Q : OpenPartialHomeomorph S Plane, Q.source = c.source ∧
        ∀ u0 u1 : Icc (-1 : ℝ) 1,
        0 < u0.val → u0.val < bound → u0.val ≤ a →
        0 < u1.val → u1.val < bound → u1.val ≤ a →
        ∃ G : C(Interval,Interval × Icc (-1 : ℝ) 1), ∃ rail : C(Interval,↥F), ∃ L R : Plane,
          IsEmbedding rail ∧
          (∀ t, rail t = correctedJoint.guideStrip (G t)) ∧
          (G 0).1 = joint.guideClock ell ∧ (G 1).1 = joint.guideClock right ∧
          (G 0).2 = u0 ∧ (G 1).2 = u1 ∧
          StrictMono (fun t => joint.guideClock.symm (G t).1) ∧
          (∀ t, (G t).1 ∈ correctedJoint.guideWindow) ∧
          (∀ t, 0 < (G t).2.val ∧ (G t).2.val < bound) ∧
          (∀ t, let z := (1-t.val) • L+t.val • R
            z ∈ Q.target ∧ (rail t).val = Q.symm z) ∧
          (∀ k : Option ι, Disjoint (range rail) (range (f k))) := by
    obtain ⟨Q,hQSource,hQ⟩ := hGuideRectangleChart ell right hlr a ha haOne c hbox
    refine ⟨Q,hQSource,?_⟩
    intro u0 u1 hu0 hb0 ha0 hu1 hb1 ha1
    let T : C(Interval,Interval) :=
      ⟨CurveComplex.BranchedDoubleCover.intervalAffine ell right,
        (CurveComplex.BranchedDoubleCover.intervalSegment ell right).continuous⟩
    have hT : StrictMono T := by
      intro t s hts
      change (1-t.val)*ell.val+t.val*right.val < (1-s.val)*ell.val+s.val*right.val
      have hh : t.val < s.val := hts
      nlinarith only [mul_pos (sub_pos.mpr hh) (sub_pos.mpr (show ell.val < right.val from hlr))]
    have hTZero : T 0 = ell := by
      apply Subtype.ext
      change (1-(0:ℝ))*ell.val+0*right.val = ell.val
      ring
    have hTOne : T 1 = right := by
      apply Subtype.ext
      change (1-(1:ℝ))*ell.val+1*right.val = right.val
      ring
    have hTWindow (t : Interval) : T t ∈ Icc ell right :=
      ⟨hTZero ▸ hT.monotone (unitInterval.nonneg t),hTOne ▸ hT.monotone (unitInterval.le_one t)⟩
    let U : C(Interval,Icc (-1 : ℝ) 1) := ⟨fun t =>
      ⟨(1-t.val)*u0.val+t.val*u1.val,by
        constructor <;> nlinarith only [t.property.1,t.property.2,u0.property.1,u0.property.2,u1.property.1,u1.property.2,
          mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr u0.property.1),
          mul_nonneg t.property.1 (sub_nonneg.mpr u1.property.1),
          mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr u0.property.2),
          mul_nonneg t.property.1 (sub_nonneg.mpr u1.property.2)]⟩,by fun_prop⟩
    have hU (t : Interval) : 0 < (U t).val ∧ (U t).val < bound ∧ |(U t).val| ≤ a := by
      have hlow : min u0.val u1.val ≤ (U t).val := by
        change min u0.val u1.val ≤ (1-t.val)*u0.val+t.val*u1.val
        nlinarith only [mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr (min_le_left u0.val u1.val)),
          mul_nonneg t.property.1 (sub_nonneg.mpr (min_le_right u0.val u1.val))]
      have hhigh : (U t).val ≤ max u0.val u1.val := by
        change (1-t.val)*u0.val+t.val*u1.val ≤ max u0.val u1.val
        nlinarith only [mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr (le_max_left u0.val u1.val)),
          mul_nonneg t.property.1 (sub_nonneg.mpr (le_max_right u0.val u1.val))]
      have hp : 0 < (U t).val := (lt_min hu0 hu1).trans_le hlow
      exact ⟨hp,hhigh.trans_lt (max_lt hb0 hb1),by rw [abs_of_pos hp]; exact hhigh.trans (max_le ha0 ha1)⟩
    let G : C(Interval,Interval × Icc (-1 : ℝ) 1) := ⟨fun t => (joint.guideClock (T t),U t),by fun_prop⟩
    let rail : C(Interval,↥F) := correctedJoint.guideStrip.comp G
    let L : Plane := Plane.mk (-1) (u0.val/a)
    let R : Plane := Plane.mk 1 (u1.val/a)
    have hChart (t : Interval) : Q (rail t).val = (1-t.val) • L+t.val • R := by
      change Q (correctedJoint.guideStrip (joint.guideClock (T t),U t)).val = _
      rw [hQ (T t) (hTWindow t) (U t) (hU t).2.2]
      ext i
      fin_cases i
      · change 2*((1-t.val)*ell.val+t.val*right.val-ell.val)/(right.val-ell.val)-1 = (1-t.val)*(-1)+t.val*1
        field_simp [ne_of_gt (sub_pos.mpr (show ell.val < right.val from hlr))]
        <;> ring
      · change ((1-t.val)*u0.val+t.val*u1.val)/a = (1-t.val)*(u0.val/a)+t.val*(u1.val/a)
        ring
    have hG : IsEmbedding G := (G.continuous.isClosedEmbedding (by
      intro t s he
      apply hT.injective
      exact joint.guideClock.injective (congrArg Prod.fst he))).isEmbedding
    refine ⟨G,rail,L,R,correctedJoint.guideStrip_embedded.comp hG,fun _ => rfl,?_,?_,?_,?_,?_,?_,
      fun t => ⟨(hU t).1,(hU t).2.1⟩,?_,?_⟩
    · change joint.guideClock (T 0) = _
      rw [hTZero]
    · change joint.guideClock (T 1) = _
      rw [hTOne]
    · apply Subtype.ext
      simp [G,U]
    · apply Subtype.ext
      simp [G,U]
    · simpa only [G,ContinuousMap.coe_mk,joint.guideClock.symm_apply_apply] using hT
    · intro t
      rw [hCorrectedGuideWindow]
      exact joint.guideWindow_selected (hOrientedSelectedClosed (T t) ((hTWindow t).2.trans hentry))
    · intro t
      have hsrc : (rail t).val ∈ Q.source := hQSource ▸ hbox (T t) (hTWindow t) (U t) (hU t).2.2
      refine ⟨(hChart t) ▸ Q.map_source hsrc,?_⟩
      rw [← hChart]
      exact (Q.left_inv hsrc).symm
    · intro k
      apply Set.disjoint_left.mpr
      rintro y ⟨t,rfl⟩ hk
      by_cases hkw : k = some w
      · have hb : rail t ∈ range b := by rw [hkw] at hk; exact hk
        obtain ⟨s,hs⟩ := hb
        have he := correctedJoint.guideStrip_embedded.injective
          (hs.symm.trans (correctedJoint.guideStrip_center s).symm)
        have hw := congrArg (fun z : Interval × Icc (-1 : ℝ) 1 => z.2.val) he
        exact (ne_of_gt (hU t).1) hw
      · exact hclear (T t) (hTWindow t) (U t) (hU t).2.2 (mem_iUnion.mpr ⟨⟨k,hkw⟩,hk⟩)
  have hGuideChartUniformWidth (ell right : Interval) (c : OpenPartialHomeomorph S Plane)
      (hcenter : ∀ t ∈ Icc ell right, (b (joint.guideClock t)).val ∈ c.source) :
      ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
        ∀ t ∈ Icc ell right, ∀ u : Icc (-1 : ℝ) 1, |u.val| ≤ a →
          (correctedJoint.guideStrip (joint.guideClock t,u)).val ∈ c.source := by
    let M : C(Interval × Icc (-1 : ℝ) 1,S) :=
      ⟨fun z => (orientedCorrectedGuide z).val,orientedCorrectedGuide.continuous.subtype_val⟩
    let O : Set (Interval × Icc (-1 : ℝ) 1) := M ⁻¹' c.source
    have hO : IsOpen O := c.open_source.preimage M.continuous
    have hbase : (Icc ell right) ×ˢ ({⟨0,by norm_num⟩} : Set (Icc (-1 : ℝ) 1)) ⊆ O := by
      rintro ⟨t,u⟩ ⟨ht,hu⟩
      have he : u = ⟨0,by norm_num⟩ := hu
      subst u
      change (correctedJoint.guideStrip (joint.guideClock t,⟨0,by norm_num⟩)).val ∈ c.source
      rw [correctedJoint.guideStrip_center]
      exact hcenter t ht
    obtain ⟨A,W,hA,hW,hTA,h0W,hAW⟩ := generalized_tube_lemma
      isCompact_Icc isCompact_singleton hO hbase
    let clip : ℝ → Icc (-1 : ℝ) 1 := projIcc (-1) 1 (by norm_num)
    have h0 : (0 : ℝ) ∈ clip ⁻¹' W := by
      simpa [clip,projIcc_of_mem] using h0W (mem_singleton (⟨0,by norm_num⟩ : Icc (-1 : ℝ) 1))
    obtain ⟨d,hd,hdW⟩ := Metric.mem_nhds_iff.mp ((hW.preimage continuous_projIcc).mem_nhds h0)
    let a : ℝ := min (d/2) (1/2)
    have ha : 0 < a := by dsimp [a]; positivity
    have ha1 : a ≤ 1 := (min_le_right (d/2) (1/2 : ℝ)).trans (by norm_num)
    have had : a < d := by
      have h := min_le_left (d/2) (1/2 : ℝ)
      dsimp only [a]
      linarith
    refine ⟨a,ha,ha1,?_⟩
    intro t ht u hu
    change (t,u) ∈ O
    apply hAW
    refine ⟨hTA ht,?_⟩
    have hb : u.val ∈ Metric.ball (0 : ℝ) d := by
      simpa [Metric.mem_ball,Real.dist_eq] using hu.trans_lt had
    have hw := hdW hb
    change clip u.val ∈ W at hw
    simpa only [clip,projIcc_of_mem _ u.property] using hw
  have hActualClearGapChartMesh (i : Fin (eventCount+1)) (ell right : Interval)
      (hlr : ell < right)
      (hcore : Icc ell right ⊆ Icc (clearGapLeft i) (clearGapRight i)) :
      ∃ n : ℕ, ∃ hn : 0 < n, ∃ times : Fin (n+1) → Interval,
        StrictMono times ∧ times 0 = ell ∧ times (Fin.last n) = right ∧
        (∀ j, times j ∈ Icc (ell) (right)) ∧
        ∃ C : Fin n → OpenPartialHomeomorph S Plane, ∃ widths : Fin n → ℝ,
          (∀ k, 0 < widths k ∧ widths k ≤ 1 ∧ widths k ≤ clearGuideWidth) ∧
          (∀ k t, t ∈ Icc (times k.castSucc) (times k.succ) →
            ∀ u : Icc (-1 : ℝ) 1, |u.val| ≤ widths k →
              (correctedJoint.guideStrip (joint.guideClock t,u)).val ∈ (C k).source) ∧
          (∀ k t, t ∈ Icc (times k.castSucc) (times k.succ) →
            ∀ u : Icc (-1 : ℝ) 1, |u.val| ≤ widths k →
              correctedJoint.guideStrip (joint.guideClock t,u) ∉ outgoingObstacles) := by
    obtain ⟨q,hq,hq0,hq1,hqRange,hqVal⟩ := source_affine_subinterval
      (ell) (right) (hlr)
    have hqMono : StrictMono q := by
      intro t s hts
      rw [show q t < q s ↔ (q t).val < (q s).val from Iff.rfl]
      rw [hqVal,hqVal]
      have hh : t.val < s.val := hts
      nlinarith [mul_pos (sub_pos.mpr (show (ell).val < (right).val from hlr)) (sub_pos.mpr hh)]
    let fgap : C(Interval,S) := ambientB.comp ⟨fun t => joint.guideClock (q t),by fun_prop⟩
    obtain ⟨n,hn,chart,hcharts⟩ := position_interval_subdivision fgap
      (fun y : S => (chartAt (EuclideanSpace ℝ (Fin 2)) y).source)
      (fun y => (chartAt (EuclideanSpace ℝ (Fin 2)) y).open_source)
      (fun t => ⟨fgap t,mem_chart_source _ (fgap t)⟩)
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    let mesh (j : Fin (n+1)) : Interval := ⟨j.val/n,by
      constructor
      · positivity
      · apply (div_le_one hnR).mpr
        exact_mod_cast Nat.le_of_lt_succ j.isLt⟩
    let times (j : Fin (n+1)) : Interval := q (mesh j)
    have htimes : StrictMono times := by
      intro j k hjk
      apply hqMono
      change (j.val : ℝ)/n < (k.val : ℝ)/n
      apply (div_lt_div_iff_of_pos_right hnR).mpr
      exact_mod_cast hjk
    have htimeRange (j : Fin (n+1)) : times j ∈ Icc (ell) (right) :=
      hqRange ▸ mem_range_self (mesh j)
    let C (k : Fin n) : OpenPartialHomeomorph S Plane := chartAt (EuclideanSpace ℝ (Fin 2)) (chart k)
    have hcenters (k : Fin n) (t : Interval) (ht : t ∈ Icc (times k.castSucc) (times k.succ)) :
        (b (joint.guideClock t)).val ∈ (C k).source := by
      have htr : t ∈ Icc (ell) (right) :=
        ⟨(htimeRange k.castSucc).1.trans ht.1,ht.2.trans (htimeRange k.succ).2⟩
      obtain ⟨s,hs⟩ := hqRange.symm ▸ htr
      have hlo : mesh k.castSucc ≤ s := hqMono.le_iff_le.mp (by rw [hs]; exact ht.1)
      have hhi : s ≤ mesh k.succ := hqMono.le_iff_le.mp (by rw [hs]; exact ht.2)
      have hloR : (k.val : ℝ)/n ≤ s.val := by
        change (k.val : ℝ)/n ≤ s.val at hlo
        exact hlo
      have hhiR : s.val ≤ ((k.val : ℝ)+1)/n := by
        change s.val ≤ (mesh k.succ).val at hhi
        simpa only [mesh,Fin.val_succ,Nat.cast_add,Nat.cast_one] using hhi
      have hh := hcharts k s hloR hhiR
      change (b (joint.guideClock (q s))).val ∈ (C k).source at hh
      rw [hs] at hh
      exact hh
    have hboxes (k : Fin n) := hGuideChartUniformWidth (times k.castSucc) (times k.succ) (C k) (hcenters k)
    choose rawWidth hRawWidth hRawWidthOne hRawWidthBox using hboxes
    let widths (k : Fin n) : ℝ := min (rawWidth k) clearGuideWidth
    refine ⟨n,hn,times,htimes,?_,?_,htimeRange,C,widths,?_,?_,?_⟩
    · have hz : mesh 0 = 0 := by apply Subtype.ext; simp [mesh]
      change q (mesh 0) = ell
      rw [hz,hq0]
    · have hz : mesh (Fin.last n) = 1 := by
        apply Subtype.ext
        change (n : ℝ)/n = 1
        exact div_self hnR.ne'
      change q (mesh (Fin.last n)) = right
      rw [hz,hq1]
    · intro k
      exact ⟨lt_min (hRawWidth k) hClearGuideWidth,
        (min_le_left _ _).trans (hRawWidthOne k),min_le_right _ _⟩
    · intro k t ht u hu
      exact hRawWidthBox k t ht u (hu.trans (min_le_left _ _))
    · intro k t ht u hu
      apply hActualClearGapBox i t _ u (hu.trans (min_le_right _ _))
      exact hcore ⟨(htimeRange k.castSucc).1.trans ht.1,ht.2.trans (htimeRange k.succ).2⟩
  -- Literal chart coordinates on an actual rectangle of the unchanged guide.
  have hGuidePositiveRectangleChart (ell right : Interval) (hlr : ell < right)
      (a : ℝ) (ha : 0 < a) (haOne : a ≤ 1)
      (c : OpenPartialHomeomorph S Plane)
      (hbox : ∀ t ∈ Icc ell right, ∀ u : Icc (-1 : ℝ) 1, 0 ≤ u.val → u.val ≤ a →
        (correctedJoint.guideStrip (joint.guideClock t,u)).val ∈ c.source) :
      ∃ Q : OpenPartialHomeomorph S Plane, Q.source = c.source ∧
        ∀ t ∈ Icc ell right, ∀ u : Icc (-1 : ℝ) 1, 0 ≤ u.val → u.val ≤ a →
          Q (correctedJoint.guideStrip (joint.guideClock t,u)).val =
            Plane.mk (2*(t.val-ell.val)/(right.val-ell.val)-1) (2*u.val/a-1) := by
    have hd : 0 < right.val-ell.val := sub_pos.mpr hlr
    have hx (z : ↥(Plane.closedSquare 0 1)) : -1 ≤ (z:Plane) 0 ∧ (z:Plane) 0 ≤ 1 :=
      abs_le.mp ((Plane.abs_zero_le_supNorm z).trans (mem_closedSquare_zero_one.mp z.property))
    have hy (z : ↥(Plane.closedSquare 0 1)) : -1 ≤ (z:Plane) 1 ∧ (z:Plane) 1 ≤ 1 :=
      abs_le.mp ((Plane.abs_one_le_supNorm z).trans (mem_closedSquare_zero_one.mp z.property))
    let k : ↥(Plane.closedSquare 0 1) → Interval × Icc (-1 : ℝ) 1 := fun z =>
      (joint.guideClock ⟨ell.val+(right.val-ell.val)*((z:Plane) 0+1)/2,by
        constructor <;> nlinarith only [(hx z).1,(hx z).2,ell.property.1,right.property.2,hd]⟩,
       ⟨a*((z:Plane) 1+1)/2,by constructor <;> nlinarith only [(hy z).1,(hy z).2,ha,haOne]⟩)
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have hki : Function.Injective k := by
      intro z w he
      have h0 := congrArg (fun q : Interval × Icc (-1 : ℝ) 1 => joint.guideClock.symm q.1) he
      have h1 := congrArg (fun q : Interval × Icc (-1 : ℝ) 1 => q.2.val) he
      simp only [k,joint.guideClock.symm_apply_apply] at h0
      have h0r := congrArg Subtype.val h0
      apply Subtype.ext
      ext i
      fin_cases i
      · change ell.val+(right.val-ell.val)*((z:Plane) 0+1)/2 =
          ell.val+(right.val-ell.val)*((w:Plane) 0+1)/2 at h0r
        change (z:Plane) 0 = (w:Plane) 0
        nlinarith only [h0r,hd]
      · change a*((z:Plane) 1+1)/2 = a*((w:Plane) 1+1)/2 at h1
        change (z:Plane) 1 = (w:Plane) 1
        nlinarith only [h1,ha]
    let T : ↥(Plane.closedSquare 0 1) → S := fun z => (correctedJoint.guideStrip (k z)).val
    letI : CompactSpace ↥(Plane.closedSquare 0 1) :=
      isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
    have hT : IsEmbedding T :=
      IsEmbedding.subtypeVal.comp (correctedJoint.guideStrip_embedded.comp
        ((hkc.isClosedEmbedding hki).isEmbedding))
    have hTc (z : ↥(Plane.closedSquare 0 1)) : T z ∈ c.source := by
      apply hbox
      · constructor
        · change ell.val ≤ ell.val+(right.val-ell.val)*((z:Plane) 0+1)/2
          nlinarith only [(hx z).1,hd]
        · change ell.val+(right.val-ell.val)*((z:Plane) 0+1)/2 ≤ right.val
          nlinarith only [(hx z).2,hd]
      · change 0 ≤ a*((z:Plane) 1+1)/2
        nlinarith only [(hy z).1,ha]
      · change a*((z:Plane) 1+1)/2 ≤ a
        nlinarith only [(hy z).2,ha]
    have hCc : Continuous (c ∘ T) := c.continuousOn.comp_continuous hT.continuous hTc
    have hCi : Function.Injective (c ∘ T) := by
      intro z w he
      exact hT.injective (c.injOn (hTc z) (hTc w) he)
    obtain ⟨H,hH⟩ := exists_ambient_extension_of_embedded_closed_square (c ∘ T)
      ((hCc.isClosedEmbedding hCi).isEmbedding)
    let Q : OpenPartialHomeomorph S Plane := c.transHomeomorph H.symm
    refine ⟨Q,by simp [Q],?_⟩
    intro t ht u hu0 hu
    let x : ℝ := 2*(t.val-ell.val)/(right.val-ell.val)-1
    let y : ℝ := 2*u.val/a-1
    have hx' : -1 ≤ x ∧ x ≤ 1 := by
      dsimp [x]
      have hlow : 0 ≤ (t.val-ell.val)/(right.val-ell.val) := div_nonneg (sub_nonneg.mpr ht.1) hd.le
      have hhigh : (t.val-ell.val)/(right.val-ell.val) ≤ 1 :=
        (div_le_one hd).mpr (sub_le_sub_right (show t.val ≤ right.val from ht.2) ell.val)
      rw [mul_div_assoc]
      constructor <;> linarith only [hlow,hhigh]
    have hy' : |y| ≤ 1 := by
      have hlo : 0 ≤ u.val/a := div_nonneg hu0 ha.le
      have hhi : u.val/a ≤ 1 := (div_le_one ha).mpr hu
      dsimp [y]
      rw [mul_div_assoc]
      exact abs_le.mpr ⟨by linarith only [hlo],by linarith only [hhi]⟩
    let z : ↥(Plane.closedSquare 0 1) := ⟨Plane.mk x y,by
      rw [mem_closedSquare_zero_one]
      exact max_le (abs_le.mpr hx') hy'⟩
    have hk : k z = (joint.guideClock t,u) := by
      apply Prod.ext
      · apply congrArg joint.guideClock
        apply Subtype.ext
        change ell.val+(right.val-ell.val)*(x+1)/2 = t.val
        dsimp [x]
        field_simp [hd.ne']
        <;> ring
      · apply Subtype.ext
        change a*(y+1)/2 = u.val
        dsimp [y]
        field_simp [ha.ne']
        <;> ring
    have hh := hH z
    change H z.val = c (T z) at hh
    have hz : T z = (correctedJoint.guideStrip (joint.guideClock t,u)).val :=
      congrArg (fun v => (correctedJoint.guideStrip v).val) hk
    rw [hz] at hh
    change H.symm (c (correctedJoint.guideStrip (joint.guideClock t,u)).val) = _
    rw [← hh,H.symm_apply_apply]
  have hPositiveRectangleRailFactory (ell right : Interval) (hlr : ell < right)
      (hentry : right ≤ orientedEntry) (a : ℝ) (ha : 0 < a) (haOne : a ≤ 1)
      (c : OpenPartialHomeomorph S Plane)
      (hbox : ∀ t ∈ Icc ell right, ∀ u : Icc (-1 : ℝ) 1, 0 ≤ u.val → u.val ≤ a →
        (correctedJoint.guideStrip (joint.guideClock t,u)).val ∈ c.source)
      (hclear : ∀ t ∈ Icc ell right, ∀ u : Icc (-1 : ℝ) 1, 0 ≤ u.val → u.val ≤ a →
        correctedJoint.guideStrip (joint.guideClock t,u) ∉ outgoingObstacles) :
      ∃ Q : OpenPartialHomeomorph S Plane, Q.source = c.source ∧
        ∀ u0 u1 : Icc (-1 : ℝ) 1,
        0 < u0.val → u0.val < bound → u0.val ≤ a →
        0 < u1.val → u1.val < bound → u1.val ≤ a →
        ∃ G : C(Interval,Interval × Icc (-1 : ℝ) 1), ∃ rail : C(Interval,↥F), ∃ L R : Plane,
          IsEmbedding rail ∧
          (∀ t, rail t = correctedJoint.guideStrip (G t)) ∧
          (G 0).1 = joint.guideClock ell ∧ (G 1).1 = joint.guideClock right ∧
          (G 0).2 = u0 ∧ (G 1).2 = u1 ∧
          StrictMono (fun t => joint.guideClock.symm (G t).1) ∧
          (∀ t, (G t).1 ∈ correctedJoint.guideWindow) ∧
          (∀ t, 0 < (G t).2.val ∧ (G t).2.val < bound) ∧
          (∀ t, let z := (1-t.val) • L+t.val • R
            z ∈ Q.target ∧ (rail t).val = Q.symm z) ∧
          (∀ k : Option ι, Disjoint (range rail) (range (f k))) := by
    obtain ⟨Q,hQSource,hQ⟩ := hGuidePositiveRectangleChart ell right hlr a ha haOne c hbox
    refine ⟨Q,hQSource,?_⟩
    intro u0 u1 hu0 hb0 ha0 hu1 hb1 ha1
    let T : C(Interval,Interval) :=
      ⟨CurveComplex.BranchedDoubleCover.intervalAffine ell right,
        (CurveComplex.BranchedDoubleCover.intervalSegment ell right).continuous⟩
    have hT : StrictMono T := by
      intro t s hts
      change (1-t.val)*ell.val+t.val*right.val < (1-s.val)*ell.val+s.val*right.val
      have hh : t.val < s.val := hts
      nlinarith only [mul_pos (sub_pos.mpr hh) (sub_pos.mpr (show ell.val < right.val from hlr))]
    have hTZero : T 0 = ell := by
      apply Subtype.ext
      change (1-(0:ℝ))*ell.val+0*right.val = ell.val
      ring
    have hTOne : T 1 = right := by
      apply Subtype.ext
      change (1-(1:ℝ))*ell.val+1*right.val = right.val
      ring
    have hTWindow (t : Interval) : T t ∈ Icc ell right :=
      ⟨hTZero ▸ hT.monotone (unitInterval.nonneg t),hTOne ▸ hT.monotone (unitInterval.le_one t)⟩
    let U : C(Interval,Icc (-1 : ℝ) 1) := ⟨fun t =>
      ⟨(1-t.val)*u0.val+t.val*u1.val,by
        constructor <;> nlinarith only [t.property.1,t.property.2,u0.property.1,u0.property.2,u1.property.1,u1.property.2,
          mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr u0.property.1),
          mul_nonneg t.property.1 (sub_nonneg.mpr u1.property.1),
          mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr u0.property.2),
          mul_nonneg t.property.1 (sub_nonneg.mpr u1.property.2)]⟩,by fun_prop⟩
    have hU (t : Interval) : 0 < (U t).val ∧ (U t).val < bound ∧ |(U t).val| ≤ a := by
      have hlow : min u0.val u1.val ≤ (U t).val := by
        change min u0.val u1.val ≤ (1-t.val)*u0.val+t.val*u1.val
        nlinarith only [mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr (min_le_left u0.val u1.val)),
          mul_nonneg t.property.1 (sub_nonneg.mpr (min_le_right u0.val u1.val))]
      have hhigh : (U t).val ≤ max u0.val u1.val := by
        change (1-t.val)*u0.val+t.val*u1.val ≤ max u0.val u1.val
        nlinarith only [mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr (le_max_left u0.val u1.val)),
          mul_nonneg t.property.1 (sub_nonneg.mpr (le_max_right u0.val u1.val))]
      have hp : 0 < (U t).val := (lt_min hu0 hu1).trans_le hlow
      exact ⟨hp,hhigh.trans_lt (max_lt hb0 hb1),by rw [abs_of_pos hp]; exact hhigh.trans (max_le ha0 ha1)⟩
    let G : C(Interval,Interval × Icc (-1 : ℝ) 1) := ⟨fun t => (joint.guideClock (T t),U t),by fun_prop⟩
    let rail : C(Interval,↥F) := correctedJoint.guideStrip.comp G
    let L : Plane := Plane.mk (-1) (2*u0.val/a-1)
    let R : Plane := Plane.mk 1 (2*u1.val/a-1)
    have hChart (t : Interval) : Q (rail t).val = (1-t.val) • L+t.val • R := by
      change Q (correctedJoint.guideStrip (joint.guideClock (T t),U t)).val = _
      rw [hQ (T t) (hTWindow t) (U t) (hU t).1.le ((le_abs_self _).trans (hU t).2.2)]
      ext i
      fin_cases i
      · change 2*((1-t.val)*ell.val+t.val*right.val-ell.val)/(right.val-ell.val)-1 = (1-t.val)*(-1)+t.val*1
        field_simp [ne_of_gt (sub_pos.mpr (show ell.val < right.val from hlr))]
        <;> ring
      · change 2*((1-t.val)*u0.val+t.val*u1.val)/a-1 = (1-t.val)*(2*u0.val/a-1)+t.val*(2*u1.val/a-1)
        ring
    have hG : IsEmbedding G := (G.continuous.isClosedEmbedding (by
      intro t s he
      apply hT.injective
      exact joint.guideClock.injective (congrArg Prod.fst he))).isEmbedding
    refine ⟨G,rail,L,R,correctedJoint.guideStrip_embedded.comp hG,fun _ => rfl,?_,?_,?_,?_,?_,?_,
      fun t => ⟨(hU t).1,(hU t).2.1⟩,?_,?_⟩
    · change joint.guideClock (T 0) = _
      rw [hTZero]
    · change joint.guideClock (T 1) = _
      rw [hTOne]
    · apply Subtype.ext
      simp [G,U]
    · apply Subtype.ext
      simp [G,U]
    · simpa only [G,ContinuousMap.coe_mk,joint.guideClock.symm_apply_apply] using hT
    · intro t
      rw [hCorrectedGuideWindow]
      exact joint.guideWindow_selected (hOrientedSelectedClosed (T t) ((hTWindow t).2.trans hentry))
    · intro t
      have hsrc : (rail t).val ∈ Q.source := hQSource ▸ hbox (T t) (hTWindow t) (U t) (hU t).1.le ((le_abs_self _).trans (hU t).2.2)
      refine ⟨(hChart t) ▸ Q.map_source hsrc,?_⟩
      rw [← hChart]
      exact (Q.left_inv hsrc).symm
    · intro k
      apply Set.disjoint_left.mpr
      rintro y ⟨t,rfl⟩ hk
      by_cases hkw : k = some w
      · have hb : rail t ∈ range b := by rw [hkw] at hk; exact hk
        obtain ⟨s,hs⟩ := hb
        have he := correctedJoint.guideStrip_embedded.injective
          (hs.symm.trans (correctedJoint.guideStrip_center s).symm)
        have hw := congrArg (fun z : Interval × Icc (-1 : ℝ) 1 => z.2.val) he
        exact (ne_of_gt (hU t).1) hw
      · exact hclear (T t) (hTWindow t) (U t) (hU t).1.le ((le_abs_self _).trans (hU t).2.2) (mem_iUnion.mpr ⟨⟨k,hkw⟩,hk⟩)
  have hActualGuideStartFace (u : Icc (-1 : ℝ) 1) :
      orientedCorrectedGuide (0,u) = boundaryLine u := by
    change correctedJoint.guideStrip (joint.guideClock 0,u) = boundaryLine u
    rw [joint.guideClock_start,← correctedJoint.boundaryLine_eq,hCorrectedBoundaryLine]
  have hActualGuideEntryFace (u : Icc (-1 : ℝ) 1) :
      orientedCorrectedGuide (orientedEntry,u) = entryFiber u := by
    apply Subtype.ext
    change (correctedJoint.guideStrip (joint.guideClock orientedEntry,u)).val = (entryFiber u).val
    have he : joint.guideClock orientedEntry = actualEntry := joint.guideClock.apply_symm_apply _
    rw [he,hCorrectedGuideEq]
    exact (hCorrectionFullFaces calibrationH hCalibrationSmallFix).2.2 u
  have hOutgoingClosedFace (u : Icc (-1 : ℝ) 1) (hu0 : 0 ≤ u.val) (hu : u.val ≤ bound) :
      orientedCorrectedGuide (0,u) ∉ outgoingObstacles ∧
      (orientedCorrectedGuide (0,u)).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source := by
    rw [hActualGuideStartFace]
    refine ⟨?_,?_⟩
    · apply houtBall
      change |u.val-0| < outRadius
      simpa only [sub_zero,abs_of_nonneg hu0] using hu.trans_lt hboundRadius
    · have hb := (hBoundaryBV ⟨u,rfl⟩).1
      obtain ⟨z,hz,hze⟩ := hb
      rw [← hze]
      exact (chartAt (EuclideanSpace ℝ (Fin 2)) x).map_target
        (htarget (Metric.sphere_subset_closedBall hz))
  have hCornerEntryClosedFace (u : Icc (-1 : ℝ) 1) (hu0 : 0 ≤ u.val) (hu : u.val ≤ cornerWidth) :
      orientedCorrectedGuide (orientedEntry,u) ∉ outgoingObstacles ∧
      (orientedCorrectedGuide (orientedEntry,u)).val ∈ joint.cornerFan.chart.source := by
    rw [hActualGuideEntryFace]
    refine ⟨?_,?_⟩
    · apply hEntryBall
      change |u.val-0| < entryRadius
      simpa only [sub_zero,abs_of_nonneg hu0] using hu.trans_lt hcwRadius
    · exact (joint.guide_entry_section u hu0 (hu.trans hcwentry.le)).1
  have hClosedFaceBox (e : Interval) (width : ℝ) (hwidth : 0 < width) (hwidthOne : width ≤ 1)
      (c : OpenPartialHomeomorph S Plane)
      (hface : ∀ u : Icc (-1 : ℝ) 1, 0 ≤ u.val → u.val ≤ width →
        orientedCorrectedGuide (e,u) ∉ outgoingObstacles ∧
        (orientedCorrectedGuide (e,u)).val ∈ c.source) :
      ∃ A : Set Interval, IsOpen A ∧ e ∈ A ∧
        ∀ t ∈ A, ∀ u : Icc (-1 : ℝ) 1, 0 ≤ u.val → u.val ≤ width →
          orientedCorrectedGuide (t,u) ∉ outgoingObstacles ∧
          (orientedCorrectedGuide (t,u)).val ∈ c.source := by
    let topWidth : Icc (-1 : ℝ) 1 := ⟨width,⟨by linarith,hwidthOne⟩⟩
    let K : Set (Icc (-1 : ℝ) 1) := Icc ⟨0,by norm_num⟩ topWidth
    let M : C(Interval × Icc (-1 : ℝ) 1,S) :=
      ⟨fun z => (orientedCorrectedGuide z).val,orientedCorrectedGuide.continuous.subtype_val⟩
    let O : Set (Interval × Icc (-1 : ℝ) 1) :=
      orientedCorrectedGuide ⁻¹' outgoingObstaclesᶜ ∩ M ⁻¹' c.source
    have hO : IsOpen O :=
      (houtCompact.isClosed.isOpen_compl.preimage orientedCorrectedGuide.continuous).inter
        (c.open_source.preimage M.continuous)
    have hbase : ({e} : Set Interval) ×ˢ K ⊆ O := by
      rintro ⟨t,u⟩ ⟨ht,hu⟩
      have he : t = e := ht
      subst t
      exact hface u hu.1 hu.2
    obtain ⟨A,W,hA,hW,hEA,hKW,hAW⟩ := generalized_tube_lemma
      isCompact_singleton isClosed_Icc.isCompact hO hbase
    refine ⟨A,hA,hEA (mem_singleton e),?_⟩
    intro t ht u hu0 hu
    exact hAW ⟨ht,hKW ⟨hu0,hu⟩⟩
  obtain ⟨outgoingTimeBox,hOutgoingTimeBox,hOutgoingTimeZero,hOutgoingTimeFibers⟩ :=
    hClosedFaceBox 0 bound hbound hboundOne.le
      (chartAt (EuclideanSpace ℝ (Fin 2)) x) hOutgoingClosedFace
  obtain ⟨entryTimeBox,hEntryTimeBox,hEntryTimePoint,hEntryTimeFibers⟩ :=
    hClosedFaceBox orientedEntry cornerWidth hcw (hcwbound.le.trans hboundOne.le)
      joint.cornerFan.chart hCornerEntryClosedFace
  have hFirstClearGapPositive : 0 < clearGapRight 0 := by
    simpa [clearGapLeft] using hClearGapOrder 0
  obtain ⟨outTimeRadius,hOutTimeRadius,hOutTimeBall⟩ := Metric.mem_nhds_iff.mp
    (hOutgoingTimeBox.mem_nhds hOutgoingTimeZero)
  let firstBoxLength : ℝ := min outTimeRadius (clearGapRight 0).val/4
  have hFirstBoxLength : 0 < firstBoxLength := by
    exact div_pos (lt_min hOutTimeRadius hFirstClearGapPositive) (by norm_num)
  have hFirstBoxRadius : firstBoxLength < outTimeRadius := by
    have hm := min_le_left outTimeRadius (clearGapRight 0).val
    dsimp [firstBoxLength]
    linarith
  have hFirstBoxGap : firstBoxLength < (clearGapRight 0).val := by
    have hm := min_le_right outTimeRadius (clearGapRight 0).val
    have hp : 0 < (clearGapRight 0).val := hFirstClearGapPositive
    dsimp [firstBoxLength]
    linarith only [hm,hp]
  let firstBoxEnd : Interval := ⟨firstBoxLength,⟨hFirstBoxLength.le,hFirstBoxGap.le.trans (clearGapRight 0).property.2⟩⟩
  have hFirstBoxOrder : 0 < firstBoxEnd ∧ firstBoxEnd < clearGapRight 0 := ⟨hFirstBoxLength,hFirstBoxGap⟩
  have hActualFirstBox (t : Interval) (ht : t ∈ Icc (0 : Interval) firstBoxEnd)
      (u : Icc (-1 : ℝ) 1) (hu0 : 0 ≤ u.val) (hu : u.val ≤ bound) :
      orientedCorrectedGuide (t,u) ∉ outgoingObstacles ∧
      (orientedCorrectedGuide (t,u)).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source := by
    apply hOutgoingTimeFibers t _ u hu0 hu
    apply hOutTimeBall
    have hh : t.val < outTimeRadius := (show t.val ≤ firstBoxLength from ht.2).trans_lt hFirstBoxRadius
    simpa [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq,abs_of_nonneg t.property.1] using hh
  let lastGap : Fin (eventCount+1) := Fin.last eventCount
  have hLastGapEnd : clearGapRight lastGap = orientedEntry := by simp [clearGapRight,lastGap]
  have hLastGapBefore : clearGapLeft lastGap < orientedEntry :=
    hLastGapEnd ▸ hClearGapOrder lastGap
  obtain ⟨entryTimeRadius,hEntryTimeRadius,hEntryTimeBall⟩ := Metric.mem_nhds_iff.mp
    (hEntryTimeBox.mem_nhds hEntryTimePoint)
  let lastBoxLength : ℝ := min entryTimeRadius (orientedEntry.val-(clearGapLeft lastGap).val)/4
  have hLastBoxLength : 0 < lastBoxLength := by
    exact div_pos (lt_min hEntryTimeRadius (sub_pos.mpr (show (clearGapLeft lastGap).val < orientedEntry.val from hLastGapBefore))) (by norm_num)
  have hLastBoxRadius : lastBoxLength < entryTimeRadius := by
    have hm := min_le_left entryTimeRadius (orientedEntry.val-(clearGapLeft lastGap).val)
    dsimp [lastBoxLength]
    linarith
  have hLastBoxGap : lastBoxLength < orientedEntry.val-(clearGapLeft lastGap).val := by
    have hm := min_le_right entryTimeRadius (orientedEntry.val-(clearGapLeft lastGap).val)
    have hp : 0 < orientedEntry.val-(clearGapLeft lastGap).val := sub_pos.mpr (show (clearGapLeft lastGap).val < orientedEntry.val from hLastGapBefore)
    dsimp [lastBoxLength]
    linarith
  let lastBoxStart : Interval := ⟨orientedEntry.val-lastBoxLength,⟨by
    have hn := (clearGapLeft lastGap).property.1
    linarith,by linarith [orientedEntry.property.2,hLastBoxLength]⟩⟩
  have hLastBoxOrder : clearGapLeft lastGap < lastBoxStart ∧ lastBoxStart < orientedEntry := by
    constructor
    · change (clearGapLeft lastGap).val < orientedEntry.val-lastBoxLength
      linarith [hLastBoxGap]
    · exact sub_lt_self _ hLastBoxLength
  have hActualLastBox (t : Interval) (ht : t ∈ Icc lastBoxStart orientedEntry)
      (u : Icc (-1 : ℝ) 1) (hu0 : 0 ≤ u.val) (hu : u.val ≤ cornerWidth) :
      orientedCorrectedGuide (t,u) ∉ outgoingObstacles ∧
      (orientedCorrectedGuide (t,u)).val ∈ joint.cornerFan.chart.source := by
    apply hEntryTimeFibers t _ u hu0 hu
    apply hEntryTimeBall
    have hlo : orientedEntry.val-lastBoxLength ≤ t.val := ht.1
    have hhi : t.val ≤ orientedEntry.val := ht.2
    have hd : orientedEntry.val-t.val < entryTimeRadius := by linarith [hLastBoxRadius]
    simpa [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hhi)] using hd
  have hFirstBoxSelected : firstBoxEnd ≤ orientedEntry := by
    have hr : clearGapRight 0 ≤ orientedEntry :=
      (hClearGapCore 0 ⟨(hClearGapOrder 0).le,le_rfl⟩).2
    exact hFirstBoxOrder.2.le.trans hr
  obtain ⟨firstGapChart,hFirstGapChartSource,hFirstGapRailFactory⟩ :=
    hPositiveRectangleRailFactory 0 firstBoxEnd hFirstBoxOrder.1 hFirstBoxSelected
      bound hbound hboundOne.le (chartAt (EuclideanSpace ℝ (Fin 2)) x)
      (fun t ht u hu0 hu => (hActualFirstBox t ht u hu0 hu).2)
      (fun t ht u hu0 hu => (hActualFirstBox t ht u hu0 hu).1)
  obtain ⟨lastGapChart,hLastGapChartSource,hLastGapRailFactory⟩ :=
    hPositiveRectangleRailFactory lastBoxStart orientedEntry hLastBoxOrder.2 le_rfl
      cornerWidth hcw (hcwbound.le.trans hboundOne.le) joint.cornerFan.chart
      (fun t ht u hu0 hu => (hActualLastBox t ht u hu0 hu).2)
      (fun t ht u hu0 hu => (hActualLastBox t ht u hu0 hu).1)
  have hOrientedEntryClosed (t : Interval) (ht : t ≤ orientedEntry) :
      joint.guideClock t ∈ Icc (min d.bStart actualEntry) (max d.bStart actualEntry) := by
    have he : joint.guideClock orientedEntry = actualEntry := joint.guideClock.apply_symm_apply _
    rcases joint.guideClock_increasing with hm | ha
    · have h0 := hm.monotone (show (0 : Interval) ≤ t from unitInterval.nonneg t)
      have h1 := hm.monotone ht
      rw [joint.guideClock_start] at h0
      rw [he] at h1
      exact ⟨(min_le_left _ _).trans h0,h1.trans (le_max_right _ _)⟩
    · have h0 := ha.antitone (show (0 : Interval) ≤ t from unitInterval.nonneg t)
      have h1 := ha.antitone ht
      rw [joint.guideClock_start] at h0
      rw [he] at h1
      exact ⟨(min_le_right _ _).trans h1,h0.trans (le_max_left _ _)⟩
  let fullCorrectedGuideCarrier : Set ↥F := regionalHalfJointGuideCarrier F correctedJoint.guideStrip
    d.bStart actualEntry joint.entryMargin
  have hGuideSlabFullCarrier (G : C(Interval,Interval × Icc (-1 : ℝ) 1))
      (hTimes : ∀ t, joint.guideClock.symm (G t).1 ≤ orientedEntry)
      (hWidths : ∀ t, (G t).2.val < bound) :
      regionalHalfGuideSlab F correctedJoint.guideStrip G ⊆ fullCorrectedGuideCarrier := by
    rintro y ⟨z,⟨t,hzt,hzu0,hzu1⟩,rfl⟩
    refine ⟨z,⟨?_,hzu0,?_⟩,rfl⟩
    · rw [hzt]
      have h := hOrientedEntryClosed (joint.guideClock.symm (G t).1) (hTimes t)
      simpa only [joint.guideClock.apply_symm_apply] using h
    · exact hzu1.trans ((hWidths t).trans hboundMargin).le
  have hFullCorrectedGuideCorner :
      fullCorrectedGuideCarrier ∩ chartPull F joint.cornerFan.chart
          (regionalHalfCornerHull joint.cornerDelta joint.cornerEntry cornerEpsilon) =
        correctedJoint.guideStrip '' {z | z.1 = actualEntry ∧ 0 ≤ z.2.val ∧ z.2.val ≤ cornerWidth} := by
    have he := correctedJoint.guide_corner_carrier_inter cornerEpsilon hce (by
      rw [hCorrectedCapBound]
      exact hcecap)
    rw [hCorrectedEntryTime,hCorrectedEntryMargin,hCorrectedCornerFan,hCorrectedCornerDelta,
      hCorrectedCornerEntry,hCorrectedKappa] at he
    have hr : cornerEpsilon/joint.kappa = cornerWidth := by
      simp [cornerEpsilon,ne_of_gt joint.kappa_pos]
    rw [hr] at he
    exact he
  have hFullCorrectedOldNegativeClear : Disjoint
      (regionalHalfOldNegativeBand F joint.oldStrip joint.clock joint.cut joint.oldNegativeWidth)
      fullCorrectedGuideCarrier := by
    have hd := correctedJoint.old_negative_guide_carrier_disjoint
    rw [hCorrectedOldStrip,hCorrectedClock,hCorrectedCut,hCorrectedOldNegativeWidth,
      hCorrectedEntryTime,hCorrectedEntryMargin] at hd
    exact hd
  have hGuideSlabOldNegativeClear (G : C(Interval,Interval × Icc (-1 : ℝ) 1))
      (hTimes : ∀ t, joint.guideClock.symm (G t).1 ≤ orientedEntry)
      (hWidths : ∀ t, (G t).2.val < bound) : Disjoint
      (regionalHalfOldNegativeBand F joint.oldStrip joint.clock joint.cut joint.oldNegativeWidth)
      (regionalHalfGuideSlab F correctedJoint.guideStrip G) :=
    hFullCorrectedOldNegativeClear.mono_right (hGuideSlabFullCarrier G hTimes hWidths)
  have hGuideSlabInV (G : C(Interval,Interval × Icc (-1 : ℝ) 1))
      (hWindow : ∀ t, (G t).1 ∈ correctedJoint.guideWindow) :
      regionalHalfGuideSlab F correctedJoint.guideStrip G ⊆ V := by
    rintro y ⟨z,⟨t,hzt,hzu0,hzu1⟩,rfl⟩
    apply correctedJoint.guide_full_window_fibers z.1 _ z.2
    rw [hzt]
    exact hWindow t
  have hGuideSlabBeforeCorner (G : C(Interval,Interval × Icc (-1 : ℝ) 1))
      (hTimes : ∀ t, joint.guideClock.symm (G t).1 < orientedEntry)
      (hWidths : ∀ t, (G t).2.val < bound) :
      regionalHalfGuideSlab F correctedJoint.guideStrip G ∩ chartPull F joint.cornerFan.chart
        (regionalHalfCornerHull joint.cornerDelta joint.cornerEntry cornerEpsilon) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hys,hyc⟩
    have hy : y ∈ correctedJoint.guideStrip ''
        {z | z.1 = actualEntry ∧ 0 ≤ z.2.val ∧ z.2.val ≤ cornerWidth} := by
      rw [← hFullCorrectedGuideCorner]
      exact ⟨hGuideSlabFullCarrier G (fun t => (hTimes t).le) hWidths hys,hyc⟩
    obtain ⟨z,hz,hzy⟩ := hy
    obtain ⟨u,⟨t,hut,hu0,hu1⟩,huy⟩ := hys
    have he := correctedJoint.guideStrip_embedded.injective (huy.trans hzy.symm)
    have htime : (G t).1 = actualEntry := hut.symm.trans ((congrArg Prod.fst he).trans hz.1)
    have hclock : joint.guideClock.symm (G t).1 = orientedEntry := congrArg joint.guideClock.symm htime
    exact (hTimes t).ne hclock
  have hGuideSlabAtCorner (G : C(Interval,Interval × Icc (-1 : ℝ) 1))
      (hTimes : ∀ t, joint.guideClock.symm (G t).1 ≤ orientedEntry)
      (hWidths : ∀ t, (G t).2.val < bound)
      (hLastTime : (G 1).1 = actualEntry) (hLastWidth : (G 1).2.val = cornerWidth) :
      regionalHalfGuideSlab F correctedJoint.guideStrip G ∩ chartPull F joint.cornerFan.chart
        (regionalHalfCornerHull joint.cornerDelta joint.cornerEntry cornerEpsilon) =
      correctedJoint.guideStrip '' {z | z.1 = (G 1).1 ∧ 0 ≤ z.2.val ∧ z.2.val ≤ (G 1).2.val} := by
    ext y
    constructor
    · intro hy
      have hh : y ∈ correctedJoint.guideStrip ''
          {z | z.1 = actualEntry ∧ 0 ≤ z.2.val ∧ z.2.val ≤ cornerWidth} := by
        rw [← hFullCorrectedGuideCorner]
        exact ⟨hGuideSlabFullCarrier G hTimes hWidths hy.1,hy.2⟩
      simpa only [hLastTime,hLastWidth] using hh
    · rintro ⟨z,hz,rfl⟩
      refine ⟨⟨z,⟨1,hz.1,hz.2.1,hz.2.2⟩,rfl⟩,?_⟩
      have hh : correctedJoint.guideStrip z ∈ correctedJoint.guideStrip ''
          {z | z.1 = actualEntry ∧ 0 ≤ z.2.val ∧ z.2.val ≤ cornerWidth} :=
        ⟨z,by simpa only [hLastTime,hLastWidth] using hz,rfl⟩
      rw [← hFullCorrectedGuideCorner] at hh
      exact hh.2
  have hFirstLastBoxOrder : firstBoxEnd < lastBoxStart := by
    by_cases hm : eventCount = 0
    · have hfirst : clearGapRight 0 = orientedEntry := by simp [clearGapRight,hm]
      have hlast : clearGapLeft lastGap = 0 := by simp [clearGapLeft,lastGap,hm]
      have hfp : firstBoxLength ≤ orientedEntry.val/4 := by
        rw [← hfirst]
        exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      have hlp : lastBoxLength ≤ orientedEntry.val/4 := by
        have hh := div_le_div_of_nonneg_right
          (min_le_right entryTimeRadius (orientedEntry.val-(clearGapLeft lastGap).val))
          (by norm_num : (0:ℝ) ≤ 4)
        change lastBoxLength ≤ (orientedEntry.val-(clearGapLeft lastGap).val)/4 at hh
        simpa [hlast] using hh
      change firstBoxLength < orientedEntry.val-lastBoxLength
      have he : 0 < orientedEntry.val := hOrientedEntryPositive
      linarith
    · let i0 : Fin eventCount := ⟨0,by omega⟩
      let iLast : Fin eventCount := ⟨eventCount-1,by omega⟩
      have hfr : clearGapRight 0 = eventWindowLeft (eventLabel i0) := by
        simp [clearGapRight,hm,Ne.symm hm,i0]
      have hll : clearGapLeft lastGap = eventWindowRight (eventLabel iLast) := by
        simp [clearGapLeft,lastGap,hm,iLast]
      have hmiddle : eventWindowLeft (eventLabel i0) < eventWindowRight (eventLabel iLast) := by
        by_cases hi : i0 = iLast
        · rw [hi]
          exact (hEventWindows _).2.1.trans (hEventWindows _).2.2.1
        · have hij : i0 < iLast := by
            have hn : iLast.val ≠ 0 := fun h => hi (Fin.ext h.symm)
            change 0 < iLast.val
            omega
          exact ((hEventWindows _).2.1.trans (hEventWindows _).2.2.1).trans
            ((hEventWindowsOrder i0 iLast hij).trans
              ((hEventWindows _).2.1.trans (hEventWindows _).2.2.1))
      have hmid : clearGapRight 0 < clearGapLeft lastGap := by
        rw [hfr,hll]
        exact hmiddle
      exact hFirstBoxOrder.2.trans (hmid.trans hLastBoxOrder.1)
  let middleGapLeft (i : Fin (eventCount+1)) : Interval :=
    if i.val = 0 then firstBoxEnd else clearGapLeft i
  let middleGapRight (i : Fin (eventCount+1)) : Interval :=
    if i.val = eventCount then lastBoxStart else clearGapRight i
  have hMiddleGapOrder (i : Fin (eventCount+1)) : middleGapLeft i < middleGapRight i := by
    by_cases hi0 : i.val = 0
    · have he : i = 0 := Fin.ext hi0
      subst i
      by_cases hm : eventCount = 0
      · simpa [middleGapLeft,middleGapRight,hm] using hFirstLastBoxOrder
      · simpa [middleGapLeft,middleGapRight,hm,Ne.symm hm] using hFirstBoxOrder.2
    · by_cases him : i.val = eventCount
      · have he : i = lastGap := Fin.ext him
        subst i
        have hm : eventCount ≠ 0 := by simpa [lastGap] using hi0
        simpa only [middleGapLeft,middleGapRight,lastGap,Fin.val_last,if_neg hm,if_pos rfl,ite_true] using hLastBoxOrder.1
      · simpa only [middleGapLeft,middleGapRight,if_neg hi0,if_neg him] using hClearGapOrder i
  have hMiddleGapCore (i : Fin (eventCount+1)) :
      Icc (middleGapLeft i) (middleGapRight i) ⊆ Icc (clearGapLeft i) (clearGapRight i) := by
    intro t ht
    have hl : clearGapLeft i ≤ middleGapLeft i := by
      by_cases hi0 : i.val = 0
      · simp only [middleGapLeft,if_pos hi0,clearGapLeft,dif_pos hi0]
        exact hFirstBoxOrder.1.le
      · simp only [middleGapLeft,if_neg hi0,le_refl]
    have hr : middleGapRight i ≤ clearGapRight i := by
      by_cases him : i.val = eventCount
      · have he : i = lastGap := Fin.ext him
        subst i
        simp only [middleGapRight,lastGap,Fin.val_last,if_pos rfl,hLastGapEnd]
        exact hLastBoxOrder.2.le
      · simp [middleGapRight,him]
    exact ⟨hl.trans ht.1,ht.2.trans hr⟩
  have hMiddleMeshes (i : Fin (eventCount+1)) :=
    hActualClearGapChartMesh i (middleGapLeft i) (middleGapRight i)
      (hMiddleGapOrder i) (hMiddleGapCore i)
  choose middleCount hMiddleCount middleTimes hMiddleTimesOrder hMiddleTimesZero hMiddleTimesOne
    hMiddleTimesRange middleCharts middleWidths hMiddleWidths hMiddleBoxes hMiddleClear using hMiddleMeshes
  let MeshPiece := Σ i : Fin (eventCount+1), Fin (middleCount i)
  let railSizes : Finset ℝ := {commonFormulaRadius,bound,cornerWidth} ∪
    Finset.univ.image (fun j : MeshPiece => middleWidths j.1 j.2)
  have hRailSizes : railSizes.Nonempty := ⟨bound,by simp [railSizes]⟩
  have hRailSizesPositive : ∀ z ∈ railSizes, 0 < z := by
    intro z hz
    simp only [railSizes,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_image,Finset.mem_univ,true_and] at hz
    rcases hz with (rfl | rfl | rfl) | ⟨j,rfl⟩
    · exact hCommonFormulaRadius
    · exact hbound
    · exact hcw
    · exact (hMiddleWidths j.1 j.2).1
  let eventWidthBase : ℝ := railSizes.min' hRailSizes/2
  have hEventWidthBase : 0 < eventWidthBase :=
    div_pos (hRailSizesPositive _ (railSizes.min'_mem hRailSizes)) (by norm_num)
  have hEventWidthBaseSize (z : ℝ) (hz : z ∈ railSizes) : eventWidthBase < z := by
    have hp := hRailSizesPositive _ (railSizes.min'_mem hRailSizes)
    exact (half_lt_self hp).trans_le (railSizes.min'_le z hz)
  have hEventWidthBaseFormula : eventWidthBase < commonFormulaRadius :=
    hEventWidthBaseSize _ (by simp [railSizes])
  have hEventWidthBaseBound : eventWidthBase < bound :=
    hEventWidthBaseSize _ (by simp [railSizes])
  have hEventWidthBaseCorner : eventWidthBase < cornerWidth :=
    hEventWidthBaseSize _ (by simp [railSizes])
  have hEventWidthBaseMesh (i : Fin (eventCount+1)) (k : Fin (middleCount i)) :
      eventWidthBase < middleWidths i k :=
    hEventWidthBaseSize _ (by simp only [railSizes,Finset.mem_union,Finset.mem_image,
      Finset.mem_univ,true_and]; exact Or.inr ⟨⟨i,k⟩,rfl⟩)
  let railWidth (ρ : Ioo (0 : ℝ) bound) : Icc (-1 : ℝ) 1 :=
    ⟨eventWidthBase*(ρ.val/bound),⟨by
      have hpos := mul_pos hEventWidthBase (div_pos ρ.property.1 hbound)
      linarith,by
      have hratio : ρ.val/bound < 1 := (div_lt_one hbound).mpr ρ.property.2
      have hless : eventWidthBase*(ρ.val/bound) < eventWidthBase := by
        nlinarith [mul_pos hEventWidthBase (sub_pos.mpr hratio)]
      exact hless.le.trans (hEventWidthBaseBound.le.trans hboundOne.le)⟩⟩
  have hRailWidth (ρ : Ioo (0 : ℝ) bound) :
      0 < (railWidth ρ).val ∧ (railWidth ρ).val < bound ∧
      (railWidth ρ).val < commonFormulaRadius ∧ ∀ p, |(railWidth ρ).val| ≤ calibrationWidth p := by
    have hp : 0 < (railWidth ρ).val := mul_pos hEventWidthBase (div_pos ρ.property.1 hbound)
    have hl : (railWidth ρ).val < eventWidthBase := by
      change eventWidthBase*(ρ.val/bound) < eventWidthBase
      have hratio : ρ.val/bound < 1 := (div_lt_one hbound).mpr ρ.property.2
      nlinarith [mul_pos hEventWidthBase (sub_pos.mpr hratio)]
    refine ⟨hp,hl.trans hEventWidthBaseBound,hl.trans hEventWidthBaseFormula,?_⟩
    intro p
    rw [abs_of_pos hp]
    exact (hl.trans (hEventWidthBaseFormula.trans (hCommonFormulaEvents p))).le
  have hRailWidthMesh (ρ : Ioo (0 : ℝ) bound) (i : Fin (eventCount+1)) (k : Fin (middleCount i)) :
      (railWidth ρ).val ≤ middleWidths i k := by
    have hratio : ρ.val/bound < 1 := (div_lt_one hbound).mpr ρ.property.2
    have hless : (railWidth ρ).val < eventWidthBase := by
      change eventWidthBase*(ρ.val/bound) < eventWidthBase
      nlinarith [mul_pos hEventWidthBase (sub_pos.mpr hratio)]
    exact (hless.trans (hEventWidthBaseMesh i k)).le
  have hRailWidthCorner (ρ : Ioo (0 : ℝ) bound) : (railWidth ρ).val ≤ cornerWidth := by
    have hratio : ρ.val/bound < 1 := (div_lt_one hbound).mpr ρ.property.2
    have hless : (railWidth ρ).val < eventWidthBase := by
      change eventWidthBase*(ρ.val/bound) < eventWidthBase
      nlinarith [mul_pos hEventWidthBase (sub_pos.mpr hratio)]
    exact (hless.trans hEventWidthBaseCorner).le
  have hActualHorizontalEventRail (p : ↥P) (ρ : Ioo (0 : ℝ) bound) :
      ∃ W : IncidentFanWindow F f V p.val,
      ∃ G : C(Interval,Interval × Icc (-1 : ℝ) 1), ∃ rail : C(Interval,↥F), ∃ L R : Plane,
        W = Classical.choose (hCalibratedEvents p) ∧ IsEmbedding rail ∧
        (∀ t, rail t = correctedJoint.guideStrip (G t)) ∧
        (G 0).1 = joint.guideClock (eventWindowLeft p) ∧
        (G 1).1 = joint.guideClock (eventWindowRight p) ∧
        StrictMono (fun t => joint.guideClock.symm (G t).1) ∧
        (∀ t, (G t).1 ∈ correctedJoint.guideWindow) ∧
        (∀ t, (G t).2 = railWidth ρ) ∧
        L 1 = R 1 ∧ L 1 ≠ 0 ∧ L 0 ≠ R 0 ∧
        (∀ t, rail t ∈ chartPull F W.chart (Metric.ball (0 : Plane) 1)) ∧
        (∀ t, let z := (1-t.val) • L+t.val • R
          z ∈ W.chart.target ∧ (rail t).val = W.chart.symm z) ∧
        (chartPull F W.chart (Metric.closedBall (0 : Plane) 1) ⊆
          chartPull F (fan.window ⟨p.val,hPfan p.property⟩).chart (Metric.ball (0 : Plane) 1)) ∧
        (∀ h : p.val ∈ range b,
          incidentPorts f p.val W.chart W.left W.right (⟨some w,h⟩,false) 1 = 0 ∧
          incidentPorts f p.val W.chart W.left W.right (⟨some w,h⟩,true) 1 = 0) ∧
        (∀ j : incidentIndex f p.val, j.val ≠ some w →
          incidentPorts f p.val W.chart W.left W.right (j,false) 1 *
            incidentPorts f p.val W.chart W.left W.right (j,true) 1 < 0) ∧
        (∀ k : Option ι, k ≠ some v → k ≠ some w → (range rail ∩ range (f k)).Subsingleton) ∧
        (∀ k : Option ι, p.val ∉ range (f k) → Disjoint (range rail) (range (f k))) := by
    let W := Classical.choose (hCalibratedEvents p)
    obtain ⟨X,τ,hτ,hSign,hX,hXZero,hNested,hAxis,hThird,hFormula⟩ :=
      Classical.choose_spec (hCalibratedEvents p)
    have hlr : eventWindowLeft p < eventWindowRight p :=
      (hEventWindows p).2.1.trans (hEventWindows p).2.2.1
    obtain ⟨T,hT,hTZero,hTOne,hTWindow,hLine⟩ := hOrderedAxisTimeRoute _ _ hlr X hX
    let G : C(Interval,Interval × Icc (-1 : ℝ) 1) :=
      ⟨fun t => (joint.guideClock (T t),railWidth ρ),by fun_prop⟩
    let rail : C(Interval,↥F) := correctedJoint.guideStrip.comp G
    let leftTime : Icc (eventWindowLeft p) (eventWindowRight p) := ⟨eventWindowLeft p,⟨le_rfl,hlr.le⟩⟩
    let rightTime : Icc (eventWindowLeft p) (eventWindowRight p) := ⟨eventWindowRight p,⟨hlr.le,le_rfl⟩⟩
    let height : ℝ := τ*calibrationSign p*calibrationScale p*(railWidth ρ).val
    let L : Plane := Plane.mk (X leftTime) height
    let R : Plane := Plane.mk (X rightTime) height
    have hG : IsEmbedding G := G.continuous.isClosedEmbedding (by
      intro t u he
      apply hT.injective
      exact joint.guideClock.injective (congrArg Prod.fst he)) |>.isEmbedding
    have hUnit (t : Interval) : rail t ∈ chartPull F W.chart (Metric.ball (0 : Plane) 1) :=
      (hFormula (T t) (hTWindow t) (railWidth ρ) ((hRailWidth ρ).2.2.2 p)).1
    have hChart (t : Interval) : W.chart (rail t).val = (1-t.val) • L+t.val • R := by
      have he := (hFormula (T t) (hTWindow t) (railWidth ρ) ((hRailWidth ρ).2.2.2 p)).2
      change W.chart (rail t).val = Plane.mk (X ⟨T t,hTWindow t⟩) height at he
      rw [he,hLine t]
      ext i
      fin_cases i
      · rfl
      · change height = (1-t.val)*height+t.val*height
        ring
    have hHeight : height ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by rcases hSign with hh | hh <;> rw [hh] <;> norm_num)
        (ne_of_gt (hCalibrationBudgets p).2.2.1)) (ne_of_gt (hRailWidth ρ).1)
    have hHeightAll (t : Interval) : W.chart (rail t).val 1 = height := by
      exact congrArg (fun z : Plane => z 1)
        ((hFormula (T t) (hTWindow t) (railWidth ρ) ((hRailWidth ρ).2.2.2 p)).2)
    have hContacts := hHorizontalRailContacts p W rail height hHeight hUnit hHeightAll hThird
    refine ⟨W,G,rail,L,R,rfl,correctedJoint.guideStrip_embedded.comp hG,fun _ => rfl,?_,?_,?_,?_,
      fun _ => rfl,rfl,hHeight,?_,hUnit,?_,hNested,hAxis,hThird,hContacts.1,hContacts.2⟩
    · change joint.guideClock (T 0) = _
      rw [hTZero]
    · change joint.guideClock (T 1) = _
      rw [hTOne]
    · simpa only [G,ContinuousMap.coe_mk,joint.guideClock.symm_apply_apply] using hT
    · intro t
      rw [hCorrectedGuideWindow]
      apply joint.guideWindow_selected
      apply hOrientedCoreSelected
      exact ⟨(hEventWindows p).1.trans_le (hTWindow t).1,
        (hTWindow t).2.trans_lt (hEventWindows p).2.2.2⟩
    · change X leftTime ≠ X rightTime
      exact (hX (show leftTime < rightTime from hlr)).ne
    · intro t
      refine ⟨(hChart t) ▸ W.chart.map_source (hUnit t).1,?_⟩
      rw [← hChart]
      exact (W.chart.left_inv (hUnit t).1).symm
  let chosenEventWindow (p : ↥P) (ρ : Ioo (0 : ℝ) bound) :=
    Classical.choose (hActualHorizontalEventRail p ρ)
  let chosenEventCoordinates (p : ↥P) (ρ : Ioo (0 : ℝ) bound) :=
    Classical.choose (Classical.choose_spec (hActualHorizontalEventRail p ρ))
  let chosenEventRail (p : ↥P) (ρ : Ioo (0 : ℝ) bound) :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hActualHorizontalEventRail p ρ)))
  let chosenEventLeft (p : ↥P) (ρ : Ioo (0 : ℝ) bound) :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hActualHorizontalEventRail p ρ))))
  let chosenEventRight (p : ↥P) (ρ : Ioo (0 : ℝ) bound) :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (hActualHorizontalEventRail p ρ)))))
  have hChosenEventData (p : ↥P) (ρ : Ioo (0 : ℝ) bound) :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (hActualHorizontalEventRail p ρ)))))
  have hChosenEventFixedWindow (p : ↥P) (ρ : Ioo (0 : ℝ) bound) :
      chosenEventWindow p ρ = Classical.choose (hCalibratedEvents p) := (hChosenEventData p ρ).1
  have hChosenEventContacts (p : ↥P) (ρ : Ioo (0 : ℝ) bound) (k : Option ι)
      (hv : k ≠ some v) (hw : k ≠ some w) :
      (range (chosenEventRail p ρ) ∩ range (f k)).Subsingleton := by
    obtain ⟨hW,hEmbedded,hFactor,hZero,hOne,hOrder,hWindow,hWidth,hHeightSame,hHeightNonzero,
      hLongDistinct,hUnit,hFormula,hNested,hAxis,hThird,hContacts,hNonincident⟩ := hChosenEventData p ρ
    exact hContacts k hv hw
  have hChosenEventNonincident (p : ↥P) (ρ : Ioo (0 : ℝ) bound) (k : Option ι)
      (hk : p.val ∉ range (f k)) : Disjoint (range (chosenEventRail p ρ)) (range (f k)) := by
    obtain ⟨hW,hEmbedded,hFactor,hZero,hOne,hOrder,hWindow,hWidth,hHeightSame,hHeightNonzero,
      hLongDistinct,hUnit,hFormula,hNested,hAxis,hThird,hContacts,hNonincident⟩ := hChosenEventData p ρ
    exact hNonincident k hk
  have hChosenEventSlabs (p : ↥P) (ρ : Ioo (0 : ℝ) bound) :
      regionalHalfGuideSlab F correctedJoint.guideStrip (chosenEventCoordinates p ρ) ⊆ fullCorrectedGuideCarrier ∧
      regionalHalfGuideSlab F correctedJoint.guideStrip (chosenEventCoordinates p ρ) ⊆ V ∧
      Disjoint (regionalHalfOldNegativeBand F joint.oldStrip joint.clock joint.cut joint.oldNegativeWidth)
        (regionalHalfGuideSlab F correctedJoint.guideStrip (chosenEventCoordinates p ρ)) ∧
      regionalHalfGuideSlab F correctedJoint.guideStrip (chosenEventCoordinates p ρ) ∩
        chartPull F joint.cornerFan.chart (regionalHalfCornerHull joint.cornerDelta joint.cornerEntry cornerEpsilon) = ∅ := by
    obtain ⟨hW,hEmbedded,hFactor,hZero,hOne,hOrder,hWindow,hWidth,hHeightSame,hHeightNonzero,
      hLongDistinct,hUnit,hFormula,hNested,hAxis,hThird,hContacts,hNonincident⟩ := hChosenEventData p ρ
    have hTimes (t : Interval) : joint.guideClock.symm (chosenEventCoordinates p ρ t).1 < orientedEntry := by
      have h := hOrder.monotone (show t ≤ (1 : Interval) from unitInterval.le_one t)
      rw [hOne,joint.guideClock.symm_apply_apply] at h
      exact h.trans_lt (hEventWindows p).2.2.2
    have hWidths (t : Interval) : (chosenEventCoordinates p ρ t).2.val < bound := by
      rw [hWidth]
      exact (hRailWidth ρ).2.1
    exact ⟨hGuideSlabFullCarrier _ (fun t => (hTimes t).le) hWidths,
      hGuideSlabInV _ hWindow,hGuideSlabOldNegativeClear _ (fun t => (hTimes t).le) hWidths,
      hGuideSlabBeforeCorner _ hTimes hWidths⟩
  have hActualEventUnionCharge (ρ : Ioo (0 : ℝ) bound) (k : Option ι)
      (hv : k ≠ some v) (hw : k ≠ some w) :=
    hFiniteEventCharge (fun p => range (chosenEventRail p ρ))
      (fun p k hv hw => hChosenEventContacts p ρ k hv hw)
      (fun p k hk => hChosenEventNonincident p ρ k hk) k hv hw
  have hMiddleRailFactories (i : Fin (eventCount+1)) (k : Fin (middleCount i)) :=
    hRectangleRailFactory (middleTimes i k.castSucc) (middleTimes i k.succ)
      (hMiddleTimesOrder i k.castSucc_lt_succ)
      (((hClearGapCore i (hMiddleGapCore i (hMiddleTimesRange i k.succ))).2))
      (middleWidths i k) (hMiddleWidths i k).1 (hMiddleWidths i k).2.1
      (middleCharts i k) (hMiddleBoxes i k) (hMiddleClear i k)
  let middleRailChart (i : Fin (eventCount+1)) (k : Fin (middleCount i)) :=
    Classical.choose (hMiddleRailFactories i k)
  have hMiddleRailFactory (i : Fin (eventCount+1)) (k : Fin (middleCount i)) :=
    (Classical.choose_spec (hMiddleRailFactories i k)).2
  let rhoWidth (ρ : Ioo (0 : ℝ) bound) : Icc (-1 : ℝ) 1 :=
    ⟨ρ.val,⟨by linarith [ρ.property.1],ρ.property.2.le.trans hboundOne.le⟩⟩
  have hFirstActual (ρ : Ioo (0 : ℝ) bound) :=
    hFirstGapRailFactory (rhoWidth ρ) (railWidth ρ)
      ρ.property.1 ρ.property.2 ρ.property.2.le
      (hRailWidth ρ).1 (hRailWidth ρ).2.1 (hRailWidth ρ).2.1.le
  let firstCoordinates (ρ : Ioo (0 : ℝ) bound) := Classical.choose (hFirstActual ρ)
  let firstRail (ρ : Ioo (0 : ℝ) bound) :=
    Classical.choose (Classical.choose_spec (hFirstActual ρ))
  let firstLeft (ρ : Ioo (0 : ℝ) bound) :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hFirstActual ρ)))
  let firstRight (ρ : Ioo (0 : ℝ) bound) :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hFirstActual ρ))))
  have hFirstData (ρ : Ioo (0 : ℝ) bound) :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hFirstActual ρ))))
  have hMiddleActual (ρ : Ioo (0 : ℝ) bound) (i : Fin (eventCount+1)) (k : Fin (middleCount i)) :=
    hMiddleRailFactory i k (railWidth ρ) (railWidth ρ)
      (hRailWidth ρ).1 (hRailWidth ρ).2.1 (hRailWidthMesh ρ i k)
      (hRailWidth ρ).1 (hRailWidth ρ).2.1 (hRailWidthMesh ρ i k)
  let middleCoordinates (ρ : Ioo (0 : ℝ) bound) (i : Fin (eventCount+1)) (k : Fin (middleCount i)) :=
    Classical.choose (hMiddleActual ρ i k)
  let middleRail (ρ : Ioo (0 : ℝ) bound) (i : Fin (eventCount+1)) (k : Fin (middleCount i)) :=
    Classical.choose (Classical.choose_spec (hMiddleActual ρ i k))
  let middleLeft (ρ : Ioo (0 : ℝ) bound) (i : Fin (eventCount+1)) (k : Fin (middleCount i)) :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hMiddleActual ρ i k)))
  let middleRight (ρ : Ioo (0 : ℝ) bound) (i : Fin (eventCount+1)) (k : Fin (middleCount i)) :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hMiddleActual ρ i k))))
  have hMiddleData (ρ : Ioo (0 : ℝ) bound) (i : Fin (eventCount+1)) (k : Fin (middleCount i)) :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hMiddleActual ρ i k))))
  have hLastActual (ρ : Ioo (0 : ℝ) bound) :=
    hLastGapRailFactory (railWidth ρ) capWidth
      (hRailWidth ρ).1 (hRailWidth ρ).2.1 (hRailWidthCorner ρ)
      hcw hcwbound le_rfl
  let lastCoordinates (ρ : Ioo (0 : ℝ) bound) := Classical.choose (hLastActual ρ)
  let lastRail (ρ : Ioo (0 : ℝ) bound) :=
    Classical.choose (Classical.choose_spec (hLastActual ρ))
  let lastLeft (ρ : Ioo (0 : ℝ) bound) :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hLastActual ρ)))
  let lastRight (ρ : Ioo (0 : ℝ) bound) :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hLastActual ρ))))
  have hLastData (ρ : Ioo (0 : ℝ) bound) :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hLastActual ρ))))
  have hMiddleBeforeEntry (i : Fin (eventCount+1)) (k : Fin (middleCount i)) :
      middleTimes i k.succ < orientedEntry := by
    apply (hMiddleTimesRange i k.succ).2.trans_lt
    by_cases him : i.val = eventCount
    · simpa only [middleGapRight,if_pos him] using hLastBoxOrder.2
    · simpa only [middleGapRight,if_neg him,clearGapRight,dif_neg him] using
        ((hEventWindows (eventLabel ⟨i.val,by omega⟩)).2.1.trans
          ((hEventWindows _).2.2.1.trans (hEventWindows _).2.2.2))
  have hFirstSlabs (ρ : Ioo (0 : ℝ) bound) :
      regionalHalfGuideSlab F correctedJoint.guideStrip (firstCoordinates ρ) ⊆ V ∧
      Disjoint (regionalHalfOldNegativeBand F joint.oldStrip joint.clock joint.cut joint.oldNegativeWidth)
        (regionalHalfGuideSlab F correctedJoint.guideStrip (firstCoordinates ρ)) ∧
      regionalHalfGuideSlab F correctedJoint.guideStrip (firstCoordinates ρ) ∩
        chartPull F joint.cornerFan.chart
          (regionalHalfCornerHull joint.cornerDelta joint.cornerEntry cornerEpsilon) = ∅ := by
    obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hFirstData ρ
    have ht (t : Interval) : joint.guideClock.symm (firstCoordinates ρ t).1 < orientedEntry := by
      have hl := ho.monotone (show t ≤ (1:Interval) from unitInterval.le_one t)
      have hend : joint.guideClock.symm (firstCoordinates ρ 1).1 = firstBoxEnd := by
        rw [h1,joint.guideClock.symm_apply_apply]
      rw [hend] at hl
      exact hl.trans_lt (hFirstBoxOrder.2.trans_le (hClearGapCore 0
        (show clearGapRight 0 ∈ Icc (clearGapLeft 0) (clearGapRight 0) from ⟨(hClearGapOrder 0).le,le_rfl⟩)).2)
    exact ⟨hGuideSlabInV _ hw,hGuideSlabOldNegativeClear _ (fun t => (ht t).le)
      (fun t => (hwidth t).2),hGuideSlabBeforeCorner _ ht (fun t => (hwidth t).2)⟩
  have hMiddleSlabs (ρ : Ioo (0 : ℝ) bound) (i : Fin (eventCount+1)) (k : Fin (middleCount i)) :
      regionalHalfGuideSlab F correctedJoint.guideStrip (middleCoordinates ρ i k) ⊆ V ∧
      Disjoint (regionalHalfOldNegativeBand F joint.oldStrip joint.clock joint.cut joint.oldNegativeWidth)
        (regionalHalfGuideSlab F correctedJoint.guideStrip (middleCoordinates ρ i k)) ∧
      regionalHalfGuideSlab F correctedJoint.guideStrip (middleCoordinates ρ i k) ∩
        chartPull F joint.cornerFan.chart
          (regionalHalfCornerHull joint.cornerDelta joint.cornerEntry cornerEpsilon) = ∅ := by
    obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hMiddleData ρ i k
    have ht (t : Interval) : joint.guideClock.symm (middleCoordinates ρ i k t).1 < orientedEntry := by
      have hl := ho.monotone (show t ≤ (1:Interval) from unitInterval.le_one t)
      have hend : joint.guideClock.symm (middleCoordinates ρ i k 1).1 = middleTimes i k.succ := by
        rw [h1,joint.guideClock.symm_apply_apply]
      rw [hend] at hl
      exact hl.trans_lt (hMiddleBeforeEntry i k)
    exact ⟨hGuideSlabInV _ hw,hGuideSlabOldNegativeClear _ (fun t => (ht t).le)
      (fun t => (hwidth t).2),hGuideSlabBeforeCorner _ ht (fun t => (hwidth t).2)⟩
  have hLastSlabs (ρ : Ioo (0 : ℝ) bound) :
      regionalHalfGuideSlab F correctedJoint.guideStrip (lastCoordinates ρ) ⊆ V ∧
      Disjoint (regionalHalfOldNegativeBand F joint.oldStrip joint.clock joint.cut joint.oldNegativeWidth)
        (regionalHalfGuideSlab F correctedJoint.guideStrip (lastCoordinates ρ)) ∧
      regionalHalfGuideSlab F correctedJoint.guideStrip (lastCoordinates ρ) ∩
        chartPull F joint.cornerFan.chart
          (regionalHalfCornerHull joint.cornerDelta joint.cornerEntry cornerEpsilon) =
        correctedJoint.guideStrip '' {z | z.1 = (lastCoordinates ρ 1).1 ∧
          0 ≤ z.2.val ∧ z.2.val ≤ (lastCoordinates ρ 1).2.val} := by
    obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hLastData ρ
    have ht (t : Interval) : joint.guideClock.symm (lastCoordinates ρ t).1 ≤ orientedEntry := by
      have hl := ho.monotone (show t ≤ (1:Interval) from unitInterval.le_one t)
      have hend : joint.guideClock.symm (lastCoordinates ρ 1).1 = orientedEntry := by
        rw [h1,joint.guideClock.symm_apply_apply]
      exact hend ▸ hl
    exact ⟨hGuideSlabInV _ hw,hGuideSlabOldNegativeClear _ ht (fun t => (hwidth t).2),
      hGuideSlabAtCorner _ ht (fun t => (hwidth t).2)
        (h1.trans (joint.guideClock.apply_symm_apply actualEntry)) (congrArg Subtype.val hu1)⟩
  have hActualFullGuideCarrier : fullCorrectedGuideCarrier =
      regionalHalfJointGuideCarrier F guideStrip d.bStart actualEntry joint.entryMargin := by
    obtain ⟨HF,hval,hfix,hcarrier,hselected⟩ :=
      hRelativeCorrectionCarriers calibrationH hCalibrationCenter hCalibrationSmallFix
    have heq : correctedJoint.guideStrip = (⟨HF,HF.continuous⟩ : C(↥F,↥F)).comp guideStrip := by
      ext z
      exact (hCorrectedGuideEq z).trans (hval (guideStrip z)).symm
    change regionalHalfJointGuideCarrier F correctedJoint.guideStrip d.bStart actualEntry joint.entryMargin = _
    rw [heq]
    exact hcarrier
  have hActualFullGuideCap : fullCorrectedGuideCarrier ∩ range cap = {cap 0} := by
    rw [hActualFullGuideCarrier,inter_comm]
    exact hCapGuideCarrier
  have hRailInsideSlab (G : C(Interval,Interval × Icc (-1 : ℝ) 1))
      (rail : C(Interval,↥F)) (hfactor : ∀ t, rail t = correctedJoint.guideStrip (G t))
      (hwidth : ∀ t, 0 ≤ (G t).2.val) :
      range rail ⊆ regionalHalfGuideSlab F correctedJoint.guideStrip G := by
    rintro y ⟨t,rfl⟩
    exact ⟨G t,⟨t,rfl,hwidth t,le_rfl⟩,(hfactor t).symm⟩
  have hGuideRailMissB (G : C(Interval,Interval × Icc (-1 : ℝ) 1))
      (rail : C(Interval,↥F)) (hfactor : ∀ t, rail t = correctedJoint.guideStrip (G t))
      (hwidth : ∀ t, 0 < (G t).2.val) : Disjoint (range rail) (range b) := by
    apply disjoint_left.mpr
    rintro y ⟨t,rfl⟩ ⟨s,hs⟩
    have he := correctedJoint.guideStrip_embedded.injective
      ((hfactor t).symm.trans (hs.symm.trans (correctedJoint.guideStrip_center s).symm))
    have hu := congrArg (fun z : Interval × Icc (-1 : ℝ) 1 => z.2.val) he
    exact (ne_of_gt (hwidth t)) hu
  have hGuideOrderedIntersection
      (G H : C(Interval,Interval × Icc (-1 : ℝ) 1))
      (q r : C(Interval,↥F))
      (hq : ∀ t, q t = correctedJoint.guideStrip (G t))
      (hr : ∀ t, r t = correctedJoint.guideStrip (H t))
      (hG : StrictMono (fun t => joint.guideClock.symm (G t).1))
      (hH : StrictMono (fun t => joint.guideClock.symm (H t).1))
      (horder : joint.guideClock.symm (G 1).1 ≤ joint.guideClock.symm (H 0).1) :
      ∀ s t, q s = r t → s = 1 ∧ t = 0 := by
    intro s t he
    have hc := correctedJoint.guideStrip_embedded.injective ((hq s).symm.trans (he.trans (hr t)))
    have htime := congrArg (fun z : Interval × Icc (-1 : ℝ) 1 => joint.guideClock.symm z.1) hc
    have hs : s = 1 := by
      apply le_antisymm (show s ≤ (1:Interval) from unitInterval.le_one s)
      apply hG.le_iff_le.mp
      exact horder.trans ((hH.monotone (show (0:Interval) ≤ t from unitInterval.nonneg t)).trans htime.symm.le)
    have ht : t = 0 := by
      apply le_antisymm _ (show (0:Interval) ≤ t from unitInterval.nonneg t)
      apply hH.le_iff_le.mp
      exact htime.symm.le.trans ((hG.monotone (show s ≤ (1:Interval) from unitInterval.le_one s)).trans horder)
    exact ⟨hs,ht⟩
  have hFirstRailZero (ρ : Ioo (0 : ℝ) bound) : firstRail ρ 0 = beta ρ := by
    obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hFirstData ρ
    calc
      firstRail ρ 0 = correctedJoint.guideStrip (firstCoordinates ρ 0) := hf 0
      _ = correctedJoint.guideStrip (joint.guideClock 0,rhoWidth ρ) :=
        congrArg correctedJoint.guideStrip (Prod.ext h0 hu0)
      _ = boundaryLine (rhoWidth ρ) := by
        rw [joint.guideClock_start,← correctedJoint.boundaryLine_eq,hCorrectedBoundaryLine]
      _ = beta ρ := rfl
  have hLastRailOne (ρ : Ioo (0 : ℝ) bound) : lastRail ρ 1 = cap 0 := by
    obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hLastData ρ
    calc
      lastRail ρ 1 = correctedJoint.guideStrip (lastCoordinates ρ 1) := hf 1
      _ = correctedJoint.guideStrip (joint.guideClock orientedEntry,capWidth) :=
        congrArg correctedJoint.guideStrip (Prod.ext h1 hu1)
      _ = entryFiber capWidth := hActualGuideEntryFace capWidth
      _ = cap 0 := hCapZero.symm
  have hMiddleAdjacentSeam (ρ : Ioo (0 : ℝ) bound) (i : Fin (eventCount+1))
      (k l : Fin (middleCount i)) (hkl : k.val+1 = l.val) :
      middleRail ρ i k 1 = middleRail ρ i l 0 := by
    obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hMiddleData ρ i k
    obtain ⟨ee,ef,e0,e1,eu0,eu1,eo,ew,ewidth,eformula,eclear⟩ := hMiddleData ρ i l
    have htime : k.succ = l.castSucc := Fin.ext hkl
    rw [hf,ef]
    apply congrArg correctedJoint.guideStrip
    apply Prod.ext
    · rw [h1,e0,htime]
    · rw [hu1,eu0]
  have hFirstMiddleSeam (ρ : Ioo (0 : ℝ) bound) :
      firstRail ρ 1 = middleRail ρ 0 ⟨0,hMiddleCount 0⟩ 0 := by
    obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hFirstData ρ
    obtain ⟨ee,ef,e0,e1,eu0,eu1,eo,ew,ewidth,eformula,eclear⟩ := hMiddleData ρ 0 ⟨0,hMiddleCount 0⟩
    rw [hf,ef]
    apply congrArg correctedJoint.guideStrip
    apply Prod.ext
    · rw [h1,e0,show (⟨0,hMiddleCount 0⟩ : Fin (middleCount 0)).castSucc = 0 from rfl,
        hMiddleTimesZero]
      simp [middleGapLeft]
    · rw [hu1,eu0]
  have hMiddleLastSeam (ρ : Ioo (0 : ℝ) bound) :
      middleRail ρ lastGap ⟨middleCount lastGap-1,by have := hMiddleCount lastGap; omega⟩ 1 =
        lastRail ρ 0 := by
    let k : Fin (middleCount lastGap) := ⟨middleCount lastGap-1,by have := hMiddleCount lastGap; omega⟩
    obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hMiddleData ρ lastGap k
    obtain ⟨ee,ef,e0,e1,eu0,eu1,eo,ew,ewidth,eformula,eclear⟩ := hLastData ρ
    have hk : k.succ = Fin.last (middleCount lastGap) := by
      apply Fin.ext
      simp only [Fin.val_succ,Fin.val_last]
      dsimp [k]
      have := hMiddleCount lastGap
      omega
    change middleRail ρ lastGap k 1 = lastRail ρ 0
    rw [hf,ef]
    apply congrArg correctedJoint.guideStrip
    apply Prod.ext
    · rw [h1,e0,hk,hMiddleTimesOne]
      simp [middleGapRight,lastGap]
    · rw [hu1,eu0]
  have hMiddleEventSeam (ρ : Ioo (0 : ℝ) bound) (j : Fin eventCount) :
      let i : Fin (eventCount+1) := j.castSucc
      middleRail ρ i ⟨middleCount i-1,by have := hMiddleCount i; omega⟩ 1 =
        chosenEventRail (eventLabel j) ρ 0 := by
    let i : Fin (eventCount+1) := j.castSucc
    let k : Fin (middleCount i) := ⟨middleCount i-1,by have := hMiddleCount i; omega⟩
    obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hMiddleData ρ i k
    obtain ⟨hW,hEmbedded,hFactor,hZero,hOne,hOrder,hWindow,hWidth,hHeightSame,hHeightNonzero,
      hLongDistinct,hUnit,hFormula,hNested,hAxis,hThird,hContacts,hNonincident⟩ := hChosenEventData (eventLabel j) ρ
    have hk : k.succ = Fin.last (middleCount i) := by
      apply Fin.ext
      simp only [Fin.val_succ,Fin.val_last]
      dsimp [k]
      have := hMiddleCount i
      omega
    have hi : i.val ≠ eventCount := Nat.ne_of_lt j.isLt
    have hright : middleGapRight i = eventWindowLeft (eventLabel j) := by
      simp only [middleGapRight,if_neg hi,clearGapRight,dif_neg hi]
      rfl
    change middleRail ρ i k 1 = chosenEventRail (eventLabel j) ρ 0
    rw [hf,hFactor]
    apply congrArg correctedJoint.guideStrip
    apply Prod.ext
    · rw [h1,hZero,hk,hMiddleTimesOne,hright]
    · rw [hu1,hWidth]
  have hEventMiddleSeam (ρ : Ioo (0 : ℝ) bound) (j : Fin eventCount) :
      chosenEventRail (eventLabel j) ρ 1 = middleRail ρ j.succ ⟨0,hMiddleCount j.succ⟩ 0 := by
    obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hMiddleData ρ j.succ ⟨0,hMiddleCount j.succ⟩
    obtain ⟨hW,hEmbedded,hFactor,hZero,hOne,hOrder,hWindow,hWidth,hHeightSame,hHeightNonzero,
      hLongDistinct,hUnit,hFormula,hNested,hAxis,hThird,hContacts,hNonincident⟩ := hChosenEventData (eventLabel j) ρ
    have hi : j.succ.val ≠ 0 := by simp
    have hleft : middleGapLeft j.succ = eventWindowRight (eventLabel j) := by
      simp only [middleGapLeft,if_neg hi,clearGapLeft,dif_neg hi]
      congr 2
    rw [hFactor,hf]
    apply congrArg correctedJoint.guideStrip
    apply Prod.ext
    · rw [hOne,h0,show (⟨0,hMiddleCount j.succ⟩ : Fin (middleCount j.succ)).castSucc = 0 from rfl,
        hMiddleTimesZero,hleft]
    · rw [hWidth,hu0]
  have hFiniteOrderedSegments : ∀ (K : Type) [Fintype K],
      ∀ ell right : K → Interval, ∀ e : Interval,
      (∀ k, ell k < right k) →
      (∀ i j, i ≠ j → right i ≤ ell j ∨ right j ≤ ell i) →
      (∃ k, ell k = 0) → (∀ k, right k ≤ e) →
      (∀ k, right k < e → ∃ j, ell j = right k) →
      ∃ N : ℕ, ∃ hN : 0 < N, ∃ label : Fin N ≃ K,
        ∃ times : Fin (N+1) → Interval,
          StrictMono times ∧ times 0 = 0 ∧ times (Fin.last N) = e ∧
          ∀ i : Fin N, ell (label i) = times i.castSucc ∧ right (label i) = times i.succ := by
    intro K inst ell right e hlt hsep hzero he hnext
    have hEll : Function.Injective ell := by
      intro i j hij
      by_contra hn
      rcases hsep i j hn with h | h
      · exact (not_le_of_gt (hlt i)) (h.trans hij.symm.le)
      · exact (not_le_of_gt (hlt j)) (h.trans hij.le)
    letI : LinearOrder K := LinearOrder.lift' ell hEll
    let N := Fintype.card K
    obtain ⟨k0,hk0⟩ := hzero
    letI : Nonempty K := ⟨k0⟩
    have hN : 0 < N := Fintype.card_pos
    let label : Fin N ≃ K := (Fintype.orderIsoFinOfCardEq K rfl).toEquiv
    have hLabel : StrictMono (fun i => ell (label i)) :=
      (Fintype.orderIsoFinOfCardEq K rfl).strictMono
    have hEllEnd (k : K) : ell k < e := (hlt k).trans_le (he k)
    have hSepForward (i j : Fin N) (hij : i < j) : right (label i) ≤ ell (label j) := by
      rcases hsep (label i) (label j) (label.injective.ne hij.ne) with h | h
      · exact h
      · exact False.elim ((not_le_of_gt ((hLabel hij).trans (hlt (label j)))) h)
    have hLastRight : right (label ⟨N-1,by omega⟩) = e := by
      apply le_antisymm (he _)
      by_contra hn
      have hr : right (label ⟨N-1,by omega⟩) < e := lt_of_not_ge hn
      obtain ⟨j,hj⟩ := hnext _ hr
      let l := label.symm j
      have hl : label l = j := label.apply_symm_apply j
      have hltl : (⟨N-1,by omega⟩ : Fin N) < l := hLabel.lt_iff_lt.mp (by
        rw [hl,hj]
        exact hlt _)
      have hb := l.isLt
      change N-1 < l.val at hltl
      omega
    have hNextRight (i : Fin N) (hi : i.val+1 < N) :
        right (label i) = ell (label ⟨i.val+1,hi⟩) := by
      let next : Fin N := ⟨i.val+1,hi⟩
      have hin : i < next := by change i.val < i.val+1; omega
      have hr : right (label i) < e := (hSepForward i next hin).trans_lt (hEllEnd _)
      obtain ⟨j,hj⟩ := hnext (label i) hr
      let l := label.symm j
      have hl : label l = j := label.apply_symm_apply j
      have hil : i < l := hLabel.lt_iff_lt.mp (by rw [hl,hj]; exact hlt _)
      have hln : l ≤ next := hLabel.le_iff_le.mp (by rw [hl,hj]; exact hSepForward i next hin)
      have hEq : l = next := by
        apply Fin.ext
        change i.val < l.val at hil
        change l.val ≤ i.val+1 at hln
        dsimp [next]
        omega
      simpa only [← hl,hEq] using hj.symm
    have hLabelZero : ell (label ⟨0,hN⟩) = 0 := by
      apply le_antisymm _ (show (0:Interval) ≤ ell (label ⟨0,hN⟩) from unitInterval.nonneg _)
      have hle := hLabel.monotone (show (⟨0,hN⟩ : Fin N) ≤ label.symm k0 from Fin.zero_le _)
      simpa [label.apply_symm_apply,hk0] using hle
    let times : Fin (N+1) → Interval := Fin.lastCases e (fun j => ell (label j))
    have hTimesCast (j : Fin N) : times j.castSucc = ell (label j) := by simp [times]
    have hTimesLast : times (Fin.last N) = e := by simp [times]
    have hTimesOrder : StrictMono times := by
      intro j k
      revert j
      refine Fin.lastCases ?_ (fun k' => ?_) k
      · intro j
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · intro hjk
          exact (Fin.lt_irrefl _ hjk).elim
        · intro hjk
          rw [hTimesCast,hTimesLast]
          exact hEllEnd _
      · intro j
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · intro hjk
          have hk := k'.isLt
          have hh : N < k'.val := hjk
          omega
        · intro hjk
          rw [hTimesCast,hTimesCast]
          exact hLabel hjk
    refine ⟨N,hN,label,times,hTimesOrder,?_,hTimesLast,?_⟩
    · rw [show (0 : Fin (N+1)) = (⟨0,hN⟩ : Fin N).castSucc from rfl,hTimesCast,hLabelZero]
    · intro i
      refine ⟨(hTimesCast i).symm,?_⟩
      by_cases hi : i.val+1 < N
      · have his : i.succ = (⟨i.val+1,hi⟩ : Fin N).castSucc := rfl
        rw [his,hTimesCast]
        exact hNextRight i hi
      · have hil : i = ⟨N-1,by omega⟩ := by
          apply Fin.ext
          change i.val = N-1
          have := i.isLt
          omega
        have his : i.succ = Fin.last N := by apply Fin.ext; simp; have := i.isLt; omega
        rw [his,hTimesLast,hil,hLastRight]
  have hEventLeftMono : Monotone (fun j : Fin eventCount => eventWindowLeft (eventLabel j)) := by
    intro i j hij
    by_cases he : i = j
    · rw [he]
    · have hlt : i < j := lt_of_le_of_ne hij he
      exact (((hEventWindows _).2.1.trans (hEventWindows _).2.2.1).trans
        (hEventWindowsOrder i j hlt)).le
  have hEventRightMono : Monotone (fun j : Fin eventCount => eventWindowRight (eventLabel j)) := by
    intro i j hij
    by_cases he : i = j
    · rw [he]
    · have hlt : i < j := lt_of_le_of_ne hij he
      exact ((hEventWindowsOrder i j hlt).trans
        ((hEventWindows _).2.1.trans (hEventWindows _).2.2.1)).le
  have hClearGapSeparated (i j : Fin (eventCount+1)) (hij : i < j) :
      clearGapRight i < clearGapLeft j := by
    have hi : i.val ≠ eventCount := by have := j.isLt; change i.val < j.val at hij; omega
    have hj : j.val ≠ 0 := by change i.val < j.val at hij; omega
    let leftEvent : Fin eventCount := ⟨i.val,by omega⟩
    let rightEvent : Fin eventCount := ⟨j.val-1,by have := j.isLt; omega⟩
    have hle : leftEvent ≤ rightEvent := by change i.val ≤ j.val-1; change i.val < j.val at hij; omega
    have hlt : eventWindowLeft (eventLabel leftEvent) < eventWindowRight (eventLabel leftEvent) :=
      (hEventWindows _).2.1.trans (hEventWindows _).2.2.1
    simpa only [clearGapRight,dif_neg hi,clearGapLeft,dif_neg hj,leftEvent,rightEvent] using
      hlt.trans_le (hEventRightMono hle)
  have hMiddleGapBounds (i : Fin (eventCount+1)) :
      firstBoxEnd ≤ middleGapLeft i ∧ middleGapRight i ≤ lastBoxStart := by
    constructor
    · by_cases hi : i.val = 0
      · simp only [middleGapLeft,if_pos hi,le_refl]
      · have hiz : (0 : Fin (eventCount+1)) < i := by change 0 < i.val; omega
        simp only [middleGapLeft,if_neg hi]
        exact (hFirstBoxOrder.2.trans (hClearGapSeparated 0 i hiz)).le
    · by_cases hi : i.val = eventCount
      · simp only [middleGapRight,if_pos hi,le_refl]
      · have hil : i < lastGap := by change i.val < eventCount; have := i.isLt; omega
        simp only [middleGapRight,if_neg hi]
        exact ((hClearGapSeparated i lastGap hil).trans hLastBoxOrder.1).le
  have hEventBoxBounds (j : Fin eventCount) :
      firstBoxEnd < eventWindowLeft (eventLabel j) ∧
      eventWindowRight (eventLabel j) < lastBoxStart := by
    let firstEvent : Fin eventCount := ⟨0,by have := j.isLt; omega⟩
    let lastEvent : Fin eventCount := ⟨eventCount-1,by have := j.isLt; omega⟩
    have hm : eventCount ≠ 0 := by have := j.isLt; omega
    have hfirst : clearGapRight 0 = eventWindowLeft (eventLabel firstEvent) := by
      simp [clearGapRight,Ne.symm hm,firstEvent]
    have hlast : clearGapLeft lastGap = eventWindowRight (eventLabel lastEvent) := by
      simp [clearGapLeft,lastGap,hm,lastEvent]
    constructor
    · exact (hfirst ▸ hFirstBoxOrder.2).trans_le (hEventLeftMono (show firstEvent ≤ j from by change 0 ≤ j.val; exact Nat.zero_le _))
    · have hjl : j ≤ lastEvent := by change j.val ≤ eventCount-1; have := j.isLt; omega
      have hend : eventWindowRight (eventLabel lastEvent) < lastBoxStart := by
        rw [← hlast]
        exact hLastBoxOrder.1
      exact (hEventRightMono hjl).trans_lt hend
  let RawGuideIndex := Unit ⊕ (MeshPiece ⊕ (Fin eventCount ⊕ Unit))
  let rawGuideLeft : RawGuideIndex → Interval := Sum.elim (fun _ => 0)
    (Sum.elim (fun j => middleTimes j.1 j.2.castSucc)
      (Sum.elim (fun j => eventWindowLeft (eventLabel j)) (fun _ => lastBoxStart)))
  let rawGuideRight : RawGuideIndex → Interval := Sum.elim (fun _ => firstBoxEnd)
    (Sum.elim (fun j => middleTimes j.1 j.2.succ)
      (Sum.elim (fun j => eventWindowRight (eventLabel j)) (fun _ => orientedEntry)))
  have hRawGuidePositive (i : RawGuideIndex) : rawGuideLeft i < rawGuideRight i := by
    rcases i with u | (j | (j | u))
    · exact hFirstBoxOrder.1
    · exact hMiddleTimesOrder j.1 j.2.castSucc_lt_succ
    · exact (hEventWindows _).2.1.trans (hEventWindows _).2.2.1
    · exact hLastBoxOrder.2
  have hRawGuideFirstBounds (i : RawGuideIndex) (hi : i ≠ Sum.inl ()) :
      firstBoxEnd ≤ rawGuideLeft i := by
    rcases i with u | (j | (j | u))
    · cases u
      exact (hi rfl).elim
    · exact (hMiddleGapBounds j.1).1.trans (hMiddleTimesRange j.1 j.2.castSucc).1
    · exact (hEventBoxBounds j).1.le
    · exact hFirstLastBoxOrder.le
  have hRawGuideLastBounds (i : RawGuideIndex) (hi : i ≠ Sum.inr (Sum.inr (Sum.inr ()))) :
      rawGuideRight i ≤ lastBoxStart := by
    rcases i with u | (j | (j | u))
    · exact hFirstLastBoxOrder.le
    · exact (hMiddleTimesRange j.1 j.2.succ).2.trans (hMiddleGapBounds j.1).2
    · exact (hEventBoxBounds j).2.le
    · cases u
      exact (hi rfl).elim
  have hRawGuideEntryBounds (i : RawGuideIndex) : rawGuideRight i ≤ orientedEntry := by
    by_cases hi : i = Sum.inr (Sum.inr (Sum.inr ()))
    · subst i
      exact le_rfl
    · exact (hRawGuideLastBounds i hi).trans hLastBoxOrder.2.le
  have hMiddleEventSeparated (i : Fin (eventCount+1)) (k : Fin (middleCount i)) (j : Fin eventCount) :
      middleTimes i k.succ ≤ eventWindowLeft (eventLabel j) ∨
      eventWindowRight (eventLabel j) ≤ middleTimes i k.castSucc := by
    by_cases hij : i.val ≤ j.val
    · have hi : i.val ≠ eventCount := by have := j.isLt; omega
      let ei : Fin eventCount := ⟨i.val,by have := j.isLt; omega⟩
      have hel : ei ≤ j := hij
      apply Or.inl
      apply (hMiddleTimesRange i k.succ).2.trans
      apply ((hMiddleGapCore i (show middleGapRight i ∈ Icc (middleGapLeft i) (middleGapRight i)
        from ⟨(hMiddleGapOrder i).le,le_rfl⟩)).2).trans
      have heq : clearGapRight i = eventWindowLeft (eventLabel ei) := by
        simp only [clearGapRight,dif_neg hi]
        rfl
      rw [heq]
      exact hEventLeftMono hel
    · have hi : i.val ≠ 0 := by omega
      let ei : Fin eventCount := ⟨i.val-1,by have := i.isLt; omega⟩
      have hel : j ≤ ei := by change j.val ≤ i.val-1; omega
      apply Or.inr
      have heq : clearGapLeft i = eventWindowRight (eventLabel ei) := by
        simp only [clearGapLeft,dif_neg hi]
        rfl
      have hh : clearGapLeft i ≤ middleGapLeft i :=
        (hMiddleGapCore i (show middleGapLeft i ∈ Icc (middleGapLeft i) (middleGapRight i)
          from ⟨le_rfl,(hMiddleGapOrder i).le⟩)).1
      exact (hEventRightMono hel).trans ((heq ▸ hh).trans (hMiddleTimesRange i k.castSucc).1)
  have hMiddleSeparated (j k : MeshPiece) (hjk : j ≠ k) :
      middleTimes j.1 j.2.succ ≤ middleTimes k.1 k.2.castSucc ∨
      middleTimes k.1 k.2.succ ≤ middleTimes j.1 j.2.castSucc := by
    by_cases hi : j.1 = k.1
    · rcases j with ⟨i,j⟩
      rcases k with ⟨i',k⟩
      change i = i' at hi
      subst i'
      have hneq : j ≠ k := by intro h; subst k; exact hjk rfl
      rcases lt_or_gt_of_ne hneq with h | h
      · apply Or.inl
        apply (hMiddleTimesOrder i).monotone
        change j.val+1 ≤ k.val
        change j.val < k.val at h
        omega
      · apply Or.inr
        apply (hMiddleTimesOrder i).monotone
        change k.val+1 ≤ j.val
        change k.val < j.val at h
        omega
    · rcases lt_or_gt_of_ne hi with h | h
      · apply Or.inl
        have hr := (hMiddleGapCore j.1 (hMiddleTimesRange j.1 j.2.succ)).2
        have hl := (hMiddleGapCore k.1 (hMiddleTimesRange k.1 k.2.castSucc)).1
        exact hr.trans ((hClearGapSeparated j.1 k.1 h).le.trans hl)
      · apply Or.inr
        have hr := (hMiddleGapCore k.1 (hMiddleTimesRange k.1 k.2.succ)).2
        have hl := (hMiddleGapCore j.1 (hMiddleTimesRange j.1 j.2.castSucc)).1
        exact hr.trans ((hClearGapSeparated k.1 j.1 h).le.trans hl)
  have hRawGuideSeparated (i j : RawGuideIndex) (hij : i ≠ j) :
      rawGuideRight i ≤ rawGuideLeft j ∨ rawGuideRight j ≤ rawGuideLeft i := by
    rcases i with u | (i | (i | u))
    · cases u
      exact Or.inl (hRawGuideFirstBounds j hij.symm)
    · rcases j with u | (j | (j | u))
      · exact Or.inr (hRawGuideFirstBounds (Sum.inr (Sum.inl i)) (by simp))
      · exact hMiddleSeparated i j (fun h => hij (congrArg (fun z => Sum.inr (Sum.inl z)) h))
      · exact hMiddleEventSeparated i.1 i.2 j
      · exact Or.inl (hRawGuideLastBounds (Sum.inr (Sum.inl i)) (by intro h; cases h))
    · rcases j with u | (j | (j | u))
      · exact Or.inr (hRawGuideFirstBounds (Sum.inr (Sum.inr (Sum.inl i))) (by simp))
      · exact (hMiddleEventSeparated j.1 j.2 i).symm
      · have hn : i ≠ j := fun h => hij (congrArg (fun z => Sum.inr (Sum.inr (Sum.inl z))) h)
        rcases lt_or_gt_of_ne hn with h | h
        · exact Or.inl (hEventWindowsOrder i j h).le
        · exact Or.inr (hEventWindowsOrder j i h).le
      · exact Or.inl (hRawGuideLastBounds (Sum.inr (Sum.inr (Sum.inl i))) (by intro h; cases h))
    · cases u
      exact Or.inr (hRawGuideLastBounds j hij.symm)
  have hRawGuideNext (i : RawGuideIndex) (hi : rawGuideRight i < orientedEntry) :
      ∃ j : RawGuideIndex, rawGuideLeft j = rawGuideRight i := by
    rcases i with u | (j | (j | u))
    · refine ⟨Sum.inr (Sum.inl ⟨0,⟨0,hMiddleCount 0⟩⟩),?_⟩
      change middleTimes 0 (⟨0,hMiddleCount 0⟩ : Fin (middleCount 0)).castSucc = firstBoxEnd
      rw [show (⟨0,hMiddleCount 0⟩ : Fin (middleCount 0)).castSucc = 0 from rfl,hMiddleTimesZero]
      simp [middleGapLeft]
    · rcases j with ⟨i,k⟩
      by_cases hk : k.val+1 < middleCount i
      · refine ⟨Sum.inr (Sum.inl ⟨i,⟨k.val+1,hk⟩⟩),?_⟩
        rfl
      · have hkLast : k.succ = Fin.last (middleCount i) := by
          apply Fin.ext
          simp only [Fin.val_succ,Fin.val_last]
          have := k.isLt
          omega
        by_cases him : i.val < eventCount
        · refine ⟨Sum.inr (Sum.inr (Sum.inl ⟨i.val,him⟩)),?_⟩
          change eventWindowLeft (eventLabel ⟨i.val,him⟩) = middleTimes i k.succ
          rw [hkLast,hMiddleTimesOne]
          have hn : i.val ≠ eventCount := Nat.ne_of_lt him
          simp only [middleGapRight,if_neg hn,clearGapRight,dif_neg hn]
        · refine ⟨Sum.inr (Sum.inr (Sum.inr ())),?_⟩
          change lastBoxStart = middleTimes i k.succ
          rw [hkLast,hMiddleTimesOne]
          have hn : i.val = eventCount := by have := i.isLt; omega
          simp only [middleGapRight,if_pos hn]
    · refine ⟨Sum.inr (Sum.inl ⟨j.succ,⟨0,hMiddleCount j.succ⟩⟩),?_⟩
      change middleTimes j.succ (⟨0,hMiddleCount j.succ⟩ : Fin (middleCount j.succ)).castSucc =
        eventWindowRight (eventLabel j)
      rw [show (⟨0,hMiddleCount j.succ⟩ : Fin (middleCount j.succ)).castSucc = 0 from rfl,hMiddleTimesZero]
      have hn : j.succ.val ≠ 0 := by simp
      simp only [middleGapLeft,if_neg hn,clearGapLeft,dif_neg hn]
      congr 2
    · exact (lt_irrefl orientedEntry hi).elim
  obtain ⟨guideCount,hGuideCount,guideLabel,guideTimes,hGuideTimesOrder,hGuideTimesZero,
      hGuideTimesOne,hGuideTimesFaces⟩ :=
    hFiniteOrderedSegments RawGuideIndex rawGuideLeft rawGuideRight orientedEntry hRawGuidePositive
      hRawGuideSeparated ⟨Sum.inl (),rfl⟩ hRawGuideEntryBounds hRawGuideNext
  have hRawLeftInjective : Function.Injective rawGuideLeft := by
    intro i j he
    by_contra hn
    rcases hRawGuideSeparated i j hn with h | h
    · exact (not_le_of_gt (hRawGuidePositive i)) (h.trans he.symm.le)
    · exact (not_le_of_gt (hRawGuidePositive j)) (h.trans he.le)
  have hRawRightInjective : Function.Injective rawGuideRight := by
    intro i j he
    by_contra hn
    rcases hRawGuideSeparated i j hn with h | h
    · exact (not_le_of_gt (hRawGuidePositive j)) (he.symm.le.trans h)
    · exact (not_le_of_gt (hRawGuidePositive i)) (he.le.trans h)
  have hGuideLabelFirst : guideLabel ⟨0,hGuideCount⟩ = Sum.inl () := by
    apply hRawLeftInjective
    exact (hGuideTimesFaces ⟨0,hGuideCount⟩).1.trans hGuideTimesZero
  have hGuideLabelLast : guideLabel ⟨guideCount-1,by omega⟩ = Sum.inr (Sum.inr (Sum.inr ())) := by
    apply hRawRightInjective
    change rawGuideRight (guideLabel ⟨guideCount-1,by omega⟩) = orientedEntry
    have hh : (⟨guideCount-1,by omega⟩ : Fin guideCount).succ = Fin.last guideCount := by
      apply Fin.ext
      simp only [Fin.val_succ,Fin.val_last]
      omega
    exact (hGuideTimesFaces ⟨guideCount-1,by omega⟩).2.trans (by rw [hh,hGuideTimesOne])
  have hFinitePathClocks : ∀ n : ℕ, ∀ z : Fin (n+2) → ↥F,
      ∀ E : (k : Fin (n+1)) → Path (z k.castSucc) (z k.succ),
      ∃ cuts : Fin (n+2) → Interval, StrictMono cuts ∧ cuts 0 = 0 ∧
        cuts (Fin.last (n+1)) = 1 ∧ ∀ k t,
          E k t = CurveComplexGenusTwo.SourceTopology.nonemptyGraphPath n z E
            (CurveComplex.BranchedDoubleCover.intervalAffine (cuts k.castSucc) (cuts k.succ) t) := by
    intro n
    induction n with
    | zero =>
      intro z E
      let cuts (j : Fin 2) : Interval := ⟨j.val,by
        constructor
        · exact_mod_cast Nat.zero_le j.val
        · exact_mod_cast (show j.val ≤ 1 from Nat.le_of_lt_succ j.isLt)⟩
      refine ⟨cuts,?_,?_,?_,?_⟩
      · intro j k hjk
        change (j.val : ℝ) < k.val
        exact_mod_cast hjk
      · apply Subtype.ext
        norm_num [cuts]
      · apply Subtype.ext
        norm_num [cuts,Fin.last]
      · intro k t
        have hk : k = 0 := by apply Fin.ext; omega
        subst k
        have h0 : cuts (Fin.castSucc (0 : Fin 1)) = 0 := by
          apply Subtype.ext
          norm_num [cuts]
        have h1 : cuts (Fin.succ (0 : Fin 1)) = 1 := by
          apply Subtype.ext
          norm_num [cuts]
        simp only [CurveComplexGenusTwo.SourceTopology.nonemptyGraphPath]
        rw [h0,h1]
        congr 1
        apply Subtype.ext
        simp [CurveComplex.BranchedDoubleCover.intervalAffine]
    | succ n ih =>
      intro z E
      obtain ⟨oldCuts,hOldOrder,hOldZero,hOldOne,hOldFormula⟩ :=
        ih (z ∘ Fin.castSucc) (fun k => E k.castSucc)
      let half (t : Interval) : Interval := ⟨t.val/2,by constructor <;> linarith [t.property.1,t.property.2]⟩
      let cuts : Fin (n+3) → Interval := Fin.lastCases 1 (fun j => half (oldCuts j))
      have hHalfOrder : StrictMono half := by
        intro t s hts
        change t.val/2 < s.val/2
        exact (div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)).mpr hts
      have hCutsCast (j : Fin (n+2)) : cuts j.castSucc = half (oldCuts j) := by simp [cuts]
      have hCutsLast : cuts (Fin.last (n+2)) = 1 := by simp [cuts]
      have hCutOrder : StrictMono cuts := by
        intro j k
        revert j
        refine Fin.lastCases ?_ (fun k' => ?_) k
        · intro j
          refine Fin.lastCases ?_ (fun j' => ?_) j
          · intro hjk
            exact (Fin.lt_irrefl _ hjk).elim
          · intro hjk
            rw [hCutsCast,hCutsLast]
            change (oldCuts j').val/2 < 1
            linarith [(oldCuts j').property.2]
        · intro j
          refine Fin.lastCases ?_ (fun j' => ?_) j
          · intro hjk
            have hk := k'.isLt
            have hh : n+2 < k'.val := hjk
            omega
          · intro hjk
            rw [hCutsCast,hCutsCast]
            exact hHalfOrder (hOldOrder (show j' < k' from hjk))
      let prev := CurveComplexGenusTwo.SourceTopology.nonemptyGraphPath n (z ∘ Fin.castSucc) (fun k => E k.castSucc)
      let last := E (Fin.last (n+1))
      have hLeft (u : Interval) : (prev.trans last) (half u) = prev u := by
        rw [Path.trans_apply,dif_pos (by change u.val/2 ≤ (1:ℝ)/2; linarith [u.property.2])]
        congr 1
        apply Subtype.ext
        change 2*(u.val/2) = u.val
        ring
      have hRight (t : Interval) : (prev.trans last)
          (CurveComplex.BranchedDoubleCover.intervalAffine (half 1) 1 t) = last t := by
        rw [Path.trans_apply]
        split_ifs with h
        · have ht : t = 0 := by
            apply Subtype.ext
            change (1-t.val)*((1:ℝ)/2)+t.val*1 ≤ (1:ℝ)/2 at h
            change t.val = 0
            linarith [t.property.1]
          subst t
          have hu : (⟨2*(CurveComplex.BranchedDoubleCover.intervalAffine (half 1) 1 0).val,by constructor <;> norm_num [CurveComplex.BranchedDoubleCover.intervalAffine,half]⟩ : Interval) = 1 := by
            apply Subtype.ext
            change 2*((1-(0:ℝ))*((1:ℝ)/2)+0*1) = 1
            norm_num
          rw [hu,Path.target,Path.source]
          rfl
        · congr 1
          apply Subtype.ext
          change 2*((1-t.val)*((1:ℝ)/2)+t.val*1)-1 = t.val
          ring
      refine ⟨cuts,hCutOrder,?_,hCutsLast,?_⟩
      · rw [show (0 : Fin (n+3)) = (0 : Fin (n+2)).castSucc from rfl,hCutsCast,hOldZero]
        apply Subtype.ext
        norm_num [half]
      · intro k t
        refine Fin.lastCases ?_ (fun k' => ?_) k
        · change last t = (prev.trans last)
            (CurveComplex.BranchedDoubleCover.intervalAffine
              (cuts (Fin.last (n+1)).castSucc) (cuts (Fin.last (n+2))) t)
          rw [hCutsLast,hCutsCast,hOldOne]
          exact (hRight t).symm
        · change E k'.castSucc t = (prev.trans last) _
          have hs : cuts k'.castSucc.succ = half (oldCuts k'.succ) := hCutsCast k'.succ
          rw [hCutsCast,hs]
          have ha : CurveComplex.BranchedDoubleCover.intervalAffine (half (oldCuts k'.castSucc))
              (half (oldCuts k'.succ)) t =
              half (CurveComplex.BranchedDoubleCover.intervalAffine (oldCuts k'.castSucc) (oldCuts k'.succ) t) := by
            apply Subtype.ext
            change (1-t.val)*((oldCuts k'.castSucc).val/2)+t.val*((oldCuts k'.succ).val/2) =
              ((1-t.val)*(oldCuts k'.castSucc).val+t.val*(oldCuts k'.succ).val)/2
            ring
          rw [ha,hLeft]
          exact hOldFormula k' t
  let rawGuideCoordinates (ρ : Ioo (0 : ℝ) bound) : RawGuideIndex →
      C(Interval,Interval × Icc (-1 : ℝ) 1) :=
    Sum.elim (fun _ => firstCoordinates ρ)
      (Sum.elim (fun j => middleCoordinates ρ j.1 j.2)
        (Sum.elim (fun j => chosenEventCoordinates (eventLabel j) ρ) (fun _ => lastCoordinates ρ)))
  let rawGuideRail (ρ : Ioo (0 : ℝ) bound) : RawGuideIndex → C(Interval,↥F) :=
    Sum.elim (fun _ => firstRail ρ)
      (Sum.elim (fun j => middleRail ρ j.1 j.2)
        (Sum.elim (fun j => chosenEventRail (eventLabel j) ρ) (fun _ => lastRail ρ)))
  let rawGuideKind : RawGuideIndex → Fin 4 := Sum.elim (fun _ => 3)
    (Sum.elim (fun _ => 3) (Sum.elim (fun _ => 2) (fun _ => 3)))
  have hRawGuideData (ρ : Ioo (0 : ℝ) bound) (i : RawGuideIndex) :
      IsEmbedding (rawGuideRail ρ i) ∧
      (∀ t, rawGuideRail ρ i t = correctedJoint.guideStrip (rawGuideCoordinates ρ i t)) ∧
      (rawGuideCoordinates ρ i 0).1 = joint.guideClock (rawGuideLeft i) ∧
      (rawGuideCoordinates ρ i 1).1 = joint.guideClock (rawGuideRight i) ∧
      StrictMono (fun t => joint.guideClock.symm (rawGuideCoordinates ρ i t).1) ∧
      (∀ t, (rawGuideCoordinates ρ i t).1 ∈ correctedJoint.guideWindow) ∧
      (∀ t, 0 < (rawGuideCoordinates ρ i t).2.val ∧ (rawGuideCoordinates ρ i t).2.val < bound) := by
    rcases i with u | (j | (j | u))
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hFirstData ρ
      exact ⟨he,hf,h0,h1,ho,hw,hwidth⟩
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hMiddleData ρ j.1 j.2
      exact ⟨he,hf,h0,h1,ho,hw,hwidth⟩
    · obtain ⟨hW,hEmbedded,hFactor,hZero,hOne,hOrder,hWindow,hWidth,hHeightSame,hHeightNonzero,
        hLongDistinct,hUnit,hFormula,hNested,hAxis,hThird,hContacts,hNonincident⟩ := hChosenEventData (eventLabel j) ρ
      refine ⟨hEmbedded,hFactor,hZero,hOne,hOrder,hWindow,?_⟩
      intro t
      change 0 < (chosenEventCoordinates (eventLabel j) ρ t).2.val ∧
        (chosenEventCoordinates (eventLabel j) ρ t).2.val < bound
      rw [hWidth]
      exact ⟨(hRailWidth ρ).1,(hRailWidth ρ).2.1⟩
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hLastData ρ
      exact ⟨he,hf,h0,h1,ho,hw,hwidth⟩
  have hRawStartCommon (ρ : Ioo (0 : ℝ) bound) (i : RawGuideIndex) (hi : i ≠ Sum.inl ()) :
      (rawGuideCoordinates ρ i 0).2 = railWidth ρ := by
    rcases i with u | (j | (j | u))
    · cases u
      exact (hi rfl).elim
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hMiddleData ρ j.1 j.2
      exact hu0
    · obtain ⟨hW,hEmbedded,hFactor,hZero,hOne,hOrder,hWindow,hWidth,hHeightSame,hHeightNonzero,
        hLongDistinct,hUnit,hFormula,hNested,hAxis,hThird,hContacts,hNonincident⟩ := hChosenEventData (eventLabel j) ρ
      exact hWidth 0
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hLastData ρ
      exact hu0
  have hRawEndCommon (ρ : Ioo (0 : ℝ) bound) (i : RawGuideIndex)
      (hi : i ≠ Sum.inr (Sum.inr (Sum.inr ()))) :
      (rawGuideCoordinates ρ i 1).2 = railWidth ρ := by
    rcases i with u | (j | (j | u))
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hFirstData ρ
      exact hu1
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hMiddleData ρ j.1 j.2
      exact hu1
    · obtain ⟨hW,hEmbedded,hFactor,hZero,hOne,hOrder,hWindow,hWidth,hHeightSame,hHeightNonzero,
        hLongDistinct,hUnit,hFormula,hNested,hAxis,hThird,hContacts,hNonincident⟩ := hChosenEventData (eventLabel j) ρ
      exact hWidth 1
    · cases u
      exact (hi rfl).elim
  have hRawRailSeam (ρ : Ioo (0 : ℝ) bound) (i j : RawGuideIndex)
      (he : rawGuideRight i = rawGuideLeft j) : rawGuideRail ρ i 1 = rawGuideRail ρ j 0 := by
    obtain ⟨hiE,hiF,hi0,hi1,hiO,hiW,hiWidth⟩ := hRawGuideData ρ i
    obtain ⟨hjE,hjF,hj0,hj1,hjO,hjW,hjWidth⟩ := hRawGuideData ρ j
    have hi : i ≠ Sum.inr (Sum.inr (Sum.inr ())) := by
      intro h
      subst i
      have hlt : rawGuideLeft j < orientedEntry :=
        (hRawGuidePositive j).trans_le (hRawGuideEntryBounds j)
      exact (ne_of_lt hlt) he.symm
    have hj : j ≠ Sum.inl () := by
      intro h
      subst j
      have hlt : (0:Interval) < rawGuideRight i :=
        (show (0:Interval) ≤ rawGuideLeft i from unitInterval.nonneg _).trans_lt (hRawGuidePositive i)
      exact (ne_of_gt hlt) he
    rw [hiF,hjF]
    apply congrArg correctedJoint.guideStrip
    apply Prod.ext
    · rw [hi1,hj0,he]
    · rw [hRawEndCommon ρ i hi,hRawStartCommon ρ j hj]
  have hRawGuidesMissB (ρ : Ioo (0 : ℝ) bound) (i : RawGuideIndex) :
      Disjoint (range (rawGuideRail ρ i)) (range b) := by
    obtain ⟨he,hf,h0,h1,ho,hw,hwidth⟩ := hRawGuideData ρ i
    exact hGuideRailMissB _ _ hf (fun t => (hwidth t).1)
  have hRawGuidesMissA (ρ : Ioo (0 : ℝ) bound) (i : RawGuideIndex) :
      Disjoint (range (rawGuideRail ρ i)) (range a) := by
    rcases i with u | (j | (j | u))
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hFirstData ρ
      exact hclear (some v)
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hMiddleData ρ j.1 j.2
      exact hclear (some v)
    · apply hChosenEventNonincident (eventLabel j) ρ (some v)
      exact fun h => Set.disjoint_left.mp hPselectedClear (eventLabel j).property h
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hLastData ρ
      exact hclear (some v)
  have hRawGuideSlabCarrier (ρ : Ioo (0 : ℝ) bound) (i : RawGuideIndex) :
      regionalHalfGuideSlab F correctedJoint.guideStrip (rawGuideCoordinates ρ i) ⊆ fullCorrectedGuideCarrier := by
    obtain ⟨he,hf,h0,h1,ho,hw,hwidth⟩ := hRawGuideData ρ i
    have ht (t : Interval) : joint.guideClock.symm (rawGuideCoordinates ρ i t).1 ≤ orientedEntry := by
      have hh := ho.monotone (show t ≤ (1:Interval) from unitInterval.le_one t)
      rw [h1,joint.guideClock.symm_apply_apply] at hh
      exact hh.trans (hRawGuideEntryBounds i)
    exact hGuideSlabFullCarrier _ ht (fun t => (hwidth t).2)
  have hRawGuideRailCarrier (ρ : Ioo (0 : ℝ) bound) (i : RawGuideIndex) :
      range (rawGuideRail ρ i) ⊆ fullCorrectedGuideCarrier := by
    obtain ⟨he,hf,h0,h1,ho,hw,hwidth⟩ := hRawGuideData ρ i
    exact (hRailInsideSlab _ _ hf (fun t => (hwidth t).1.le)).trans (hRawGuideSlabCarrier ρ i)
  obtain ⟨guideN,rfl⟩ : ∃ k, guideCount = k+1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hGuideCount)
  have hGuideLastLabel : guideLabel (Fin.last guideN) = Sum.inr (Sum.inr (Sum.inr ())) := by
    convert hGuideLabelLast using 1
    congr 1
  have hGuideFirstLabel : guideLabel (0 : Fin (guideN+1)) = Sum.inl () := by
    simpa only [Fin.zero_eta] using hGuideLabelFirst
  let guideRail (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+1)) := rawGuideRail ρ (guideLabel i)
  let guideCoordinates (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+1)) := rawGuideCoordinates ρ (guideLabel i)
  let guidePort (ρ : Ioo (0 : ℝ) bound) : Fin (guideN+2) → ↥F :=
    Fin.lastCases (cap 0) (fun i => guideRail ρ i 0)
  let guidePortCoordinates (ρ : Ioo (0 : ℝ) bound) : Fin (guideN+2) → Interval × Icc (-1 : ℝ) 1 :=
    Fin.lastCases (guideCoordinates ρ (Fin.last guideN) 1) (fun i => guideCoordinates ρ i 0)
  have hGuideLastOne (ρ : Ioo (0 : ℝ) bound) : guideRail ρ (Fin.last guideN) 1 = cap 0 := by
    change rawGuideRail ρ (guideLabel (Fin.last guideN)) 1 = cap 0
    rw [hGuideLastLabel]
    exact hLastRailOne ρ
  have hGuidePortFactor (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+2)) :
      guidePort ρ i = correctedJoint.guideStrip (guidePortCoordinates ρ i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [guidePort,guidePortCoordinates,Fin.lastCases_last] using
        (hGuideLastOne ρ).symm.trans ((hRawGuideData ρ (guideLabel (Fin.last guideN))).2.1 1)
    · simpa only [guidePort,guidePortCoordinates,Fin.lastCases_castSucc] using
        (hRawGuideData ρ (guideLabel j)).2.1 0
  have hGuidePortTimes (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+2)) :
      (guidePortCoordinates ρ i).1 = joint.guideClock (guideTimes i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [guidePortCoordinates,Fin.lastCases_last]
      exact (hRawGuideData ρ (guideLabel (Fin.last guideN))).2.2.2.1.trans
        (congrArg joint.guideClock (hGuideTimesFaces (Fin.last guideN)).2)
    · simp only [guidePortCoordinates,Fin.lastCases_castSucc]
      exact (hRawGuideData ρ (guideLabel j)).2.2.1.trans
        (congrArg joint.guideClock (hGuideTimesFaces j).1)
  have hGuidePortInjective (ρ : Ioo (0 : ℝ) bound) : Function.Injective (guidePort ρ) := by
    intro i j he
    have hc := correctedJoint.guideStrip_embedded.injective
      ((hGuidePortFactor ρ i).symm.trans (he.trans (hGuidePortFactor ρ j)))
    have ht := congrArg Prod.fst hc
    rw [hGuidePortTimes,hGuidePortTimes] at ht
    exact hGuideTimesOrder.injective (joint.guideClock.injective ht)
  have hGuideZero (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+1)) :
      guideRail ρ i 0 = guidePort ρ i.castSucc := by simp [guidePort]
  have hGuideOne (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+1)) :
      guideRail ρ i 1 = guidePort ρ i.succ := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [guidePort] using hGuideLastOne ρ
    · rw [Fin.succ_castSucc]
      simp only [guidePort,Fin.lastCases_castSucc]
      exact hRawRailSeam ρ (guideLabel j.castSucc) (guideLabel j.succ)
        ((hGuideTimesFaces j.castSucc).2.trans (hGuideTimesFaces j.succ).1.symm)
  have hGuidePortsMissA (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+2)) :
      guidePort ρ i ∉ range a := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [guidePort,Fin.lastCases_last]
      exact fun ha => disjoint_left.mp (hRawGuidesMissA ρ (guideLabel (Fin.last guideN)))
        ⟨1,hGuideLastOne ρ⟩ ha
    · simp only [guidePort,Fin.lastCases_castSucc]
      exact fun ha => disjoint_left.mp (hRawGuidesMissA ρ (guideLabel j)) ⟨0,rfl⟩ ha
  have hGuideOrdered (ρ : Ioo (0 : ℝ) bound) (i j : Fin (guideN+1)) (hij : i < j) :
      ∀ s t, guideRail ρ i s = guideRail ρ j t → s = 1 ∧ t = 0 := by
    obtain ⟨hiE,hiF,hi0,hi1,hiO,hiW,hiWidth⟩ := hRawGuideData ρ (guideLabel i)
    obtain ⟨hjE,hjF,hj0,hj1,hjO,hjW,hjWidth⟩ := hRawGuideData ρ (guideLabel j)
    apply hGuideOrderedIntersection _ _ _ _ hiF hjF hiO hjO
    rw [hi1,hj0,joint.guideClock.symm_apply_apply,joint.guideClock.symm_apply_apply,
      (hGuideTimesFaces i).2,(hGuideTimesFaces j).1]
    exact hGuideTimesOrder.monotone (show i.succ ≤ j.castSucc from by
      change i.val+1 ≤ j.val
      exact Nat.succ_le_of_lt hij)
  have hGuideCapOrdered (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+1)) (s t : Interval)
      (he : guideRail ρ i s = cap t) : s = 1 ∧ t = 0 := by
    have hc : cap t = cap 0 := by
      have hh : cap t ∈ fullCorrectedGuideCarrier ∩ range cap :=
        ⟨hRawGuideRailCarrier ρ (guideLabel i) ⟨s,he⟩,⟨t,rfl⟩⟩
      rw [hActualFullGuideCap] at hh
      exact hh
    have ht : t = 0 := hCap.injective hc
    obtain ⟨hiE,hiF,hi0,hi1,hiO,hiW,hiWidth⟩ := hRawGuideData ρ (guideLabel i)
    have hCapFactor : cap 0 = correctedJoint.guideStrip (guidePortCoordinates ρ (Fin.last (guideN+1))) := by
      simpa only [guidePort,Fin.lastCases_last] using hGuidePortFactor ρ (Fin.last (guideN+1))
    have hh := correctedJoint.guideStrip_embedded.injective
      ((hiF s).symm.trans ((he.trans hc).trans hCapFactor))
    have hhTime := congrArg (fun z : Interval × Icc (-1 : ℝ) 1 => joint.guideClock.symm z.1) hh
    rw [hGuidePortTimes,joint.guideClock.symm_apply_apply,hGuideTimesOne] at hhTime
    have hs : s = 1 := by
      apply le_antisymm (show s ≤ (1:Interval) from unitInterval.le_one s)
      apply hiO.le_iff_le.mp
      have hend : joint.guideClock.symm (rawGuideCoordinates ρ (guideLabel i) 1).1 ≤ orientedEntry := by
        rw [hi1,joint.guideClock.symm_apply_apply]
        exact hRawGuideEntryBounds (guideLabel i)
      exact hend.trans hhTime.symm.le
    exact ⟨hs,ht⟩
  have hGuideRetainedClear (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+1)) :
      Disjoint (range (guideRail ρ i)) (range retained) :=
    (hRawGuidesMissA ρ (guideLabel i)).mono_right (fun _ h => (hRetainedOld h).1)
  have hCapRetainedOrdered (s t : Interval) (he : cap s = retained t) : s = 1 ∧ t = 0 := by
    have hs : cap s = cap 1 := by
      have hh : cap s ∈ range cap ∩ range retained := ⟨⟨s,rfl⟩,⟨t,he.symm⟩⟩
      rw [hCapRetainedInter] at hh
      exact hh
    exact ⟨hCap.injective hs,hRetained.injective (he.symm.trans (hs.trans hRetainedZero.symm))⟩
  have hCapRetainedEndDistinct : cap 1 ≠ retained 1 := by
    intro h
    have hh : (0:Interval) = 1 := hRetained.injective (hRetainedZero.trans h)
    exact (zero_ne_one hh)
  have hCapOneInA : cap 1 ∈ range a := ⟨joint.clock joint.cut,hCapOne.symm⟩
  have hRetainedOneInA : retained 1 ∈ range a := ⟨joint.clock 1,hRetainedOne.symm⟩
  have hCapZeroPort (ρ : Ioo (0 : ℝ) bound) : cap 0 = guidePort ρ (Fin.last (guideN+1)) := by simp [guidePort]
  have hGuideEmbedded (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+1)) : IsEmbedding (guideRail ρ i) :=
    (hRawGuideData ρ (guideLabel i)).1
  let fullPort (ρ : Ioo (0 : ℝ) bound) : Fin (guideN+4) → ↥F :=
    Fin.lastCases (retained 1) (Fin.lastCases (cap 1) (guidePort ρ))
  let fullPiece (ρ : Ioo (0 : ℝ) bound) : Fin (guideN+3) → C(Interval,↥F) :=
    Fin.lastCases retained (Fin.lastCases cap (guideRail ρ))
  have hFullPortInjective (ρ : Ioo (0 : ℝ) bound) : Function.Injective (fullPort ρ) := by
    intro i j
    revert i
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · intro h; rfl
      · refine Fin.lastCases ?_ (fun i'' => ?_) i'
        · intro h
          exact (hCapRetainedEndDistinct (by simpa [fullPort] using h)).elim
        · intro h
          have hh : (guidePort ρ) i'' = retained 1 := by simpa [fullPort] using h
          exact ((hGuidePortsMissA ρ) i'' (hh.symm ▸ hRetainedOneInA)).elim
    · intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · revert j'
        intro j'
        refine Fin.lastCases ?_ (fun j'' => ?_) j'
        · intro h
          exact (hCapRetainedEndDistinct (by simpa [fullPort] using h.symm)).elim
        · intro h
          have hh : (guidePort ρ) j'' = retained 1 := by simpa [fullPort] using h.symm
          exact ((hGuidePortsMissA ρ) j'' (hh.symm ▸ hRetainedOneInA)).elim
      · revert i'
        refine Fin.lastCases ?_ (fun j'' => ?_) j'
        · intro i'
          refine Fin.lastCases ?_ (fun i'' => ?_) i'
          · intro h; rfl
          · intro h
            have hh : (guidePort ρ) i'' = cap 1 := by simpa [fullPort] using h
            exact ((hGuidePortsMissA ρ) i'' (hh.symm ▸ hCapOneInA)).elim
        · intro i'
          refine Fin.lastCases ?_ (fun i'' => ?_) i'
          · intro h
            have hh : (guidePort ρ) j'' = cap 1 := by simpa [fullPort] using h.symm
            exact ((hGuidePortsMissA ρ) j'' (hh.symm ▸ hCapOneInA)).elim
          · intro h
            have hh : i'' = j'' := (hGuidePortInjective ρ) (by simpa [fullPort] using h)
            subst i''
            rfl
  have hFullZero (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+3)) : (fullPiece ρ) i 0 = (fullPort ρ) i.castSucc := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [fullPiece,fullPort] using hRetainedZero
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa [fullPiece,fullPort] using (hCapZeroPort ρ)
      · simpa [fullPiece,fullPort] using (hGuideZero ρ) j
  have hFullOne (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+3)) : (fullPiece ρ) i 1 = (fullPort ρ) i.succ := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [fullPiece,fullPort]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.succ_castSucc,Fin.succ_last,fullPiece,fullPort,Fin.lastCases_castSucc,Fin.lastCases_last]
      · simpa only [fullPiece,fullPort,Fin.succ_castSucc,Fin.lastCases_castSucc] using (hGuideOne ρ) j
  have hFullEmbed (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+3)) : IsEmbedding ((fullPiece ρ) i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [fullPiece] using hRetained
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa [fullPiece] using hCap
      · simpa [fullPiece] using (hGuideEmbedded ρ) j
  have hFullOrdered (ρ : Ioo (0 : ℝ) bound) (i j : Fin (guideN+3)) (hij : i < j) (s t : Interval)
      (he : (fullPiece ρ) i s = (fullPiece ρ) j t) : s = 1 ∧ t = 0 := by
    revert i
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · refine Fin.lastCases ?_ (fun i' => ?_)
      · intro hij he
        exact (lt_irrefl _ hij).elim
      · refine Fin.lastCases ?_ (fun i'' => ?_) i'
        · intro hij he
          exact hCapRetainedOrdered s t (by simpa [fullPiece] using he)
        · intro hij he
          have hh : (guideRail ρ) i'' s = retained t := by simpa [fullPiece] using he
          exact (disjoint_left.mp ((hGuideRetainedClear ρ) i'') ⟨s,rfl⟩ ⟨t,hh.symm⟩).elim
    · refine Fin.lastCases ?_ (fun i' => ?_)
      · intro hij he
        have hh : guideN+2 < j'.val := hij
        have := j'.isLt
        omega
      · revert i'
        refine Fin.lastCases ?_ (fun j'' => ?_) j'
        · refine Fin.lastCases ?_ (fun i'' => ?_)
          · intro hij he
            have hh : guideN+1 < guideN+1 := hij
            omega
          · intro hij he
            exact (hGuideCapOrdered ρ) i'' s t (by simpa [fullPiece] using he)
        · refine Fin.lastCases ?_ (fun i'' => ?_)
          · intro hij he
            have hh : guideN+1 < j''.val := hij
            have := j''.isLt
            omega
          · intro hij he
            exact (hGuideOrdered ρ) i'' j'' (show i'' < j'' from hij) s t (by simpa [fullPiece] using he)
  let fullPaths (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+3)) : Path (fullPort ρ i.castSucc) (fullPort ρ i.succ) :=
    ⟨(fullPiece ρ) i,(hFullZero ρ) i,(hFullOne ρ) i⟩
  let qPath (ρ : Ioo (0 : ℝ) bound) :=
    CurveComplexGenusTwo.SourceTopology.nonemptyGraphPath (guideN+2) (fullPort ρ) (fullPaths ρ)
  let q (ρ : Ioo (0 : ℝ) bound) : C(Interval,↥F) := (qPath ρ).toContinuousMap
  have hq (ρ : Ioo (0 : ℝ) bound) : Function.Injective (q ρ) := by
    apply CurveComplexGenusTwo.SourceTopology.nonemptyGraphPath_injective
    · exact (hFullPortInjective ρ)
    · exact fun i => ((hFullEmbed ρ) i).injective
    · intro i j hij s t he
      rcases lt_or_gt_of_ne hij with h | h
      · obtain ⟨hs,ht⟩ := (hFullOrdered ρ) i j h s t he
        exact ⟨Or.inr hs,Or.inl ht⟩
      · obtain ⟨ht,hs⟩ := (hFullOrdered ρ) j i h t s he.symm
        exact ⟨Or.inl hs,Or.inr ht⟩
  have hqRange (ρ : Ioo (0 : ℝ) bound) : range (q ρ) = ⋃ i, range ((fullPiece ρ) i) := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      obtain ⟨i,u,he⟩ := CurveComplexGenusTwo.SourceTopology.nonemptyGraphPath_point_on_arc
        (guideN+2) (fullPort ρ) (fullPaths ρ) t
      exact mem_iUnion.mpr ⟨i,u,he.symm⟩
    · intro hx
      obtain ⟨i,u,rfl⟩ := mem_iUnion.mp hx
      exact CurveComplexGenusTwo.SourceTopology.nonemptyGraphPath_arc_in_range
        (guideN+2) (fullPort ρ) (fullPaths ρ) i u
  have hAdjacent (ρ : Ioo (0 : ℝ) bound) (i j : Fin (guideN+3)) (hij : i.val+1=j.val) :
      range ((fullPiece ρ) i) ∩ range ((fullPiece ρ) j) = {(fullPort ρ) i.succ} := by
    ext x
    constructor
    · rintro ⟨⟨s,hs⟩,⟨t,ht⟩⟩
      obtain ⟨hs1,ht0⟩ := (hFullOrdered ρ) i j (show i<j from by change i.val<j.val; omega)
        s t (hs.trans ht.symm)
      rw [←hs,hs1,(hFullOne ρ)]
      rfl
    · intro hx
      have hh : i.succ = j.castSucc := Fin.ext hij
      have hx' : x = (fullPort ρ) i.succ := hx
      rw [hx']
      exact ⟨⟨1,(hFullOne ρ) i⟩,⟨0,((hFullZero ρ) j).trans (congrArg (fullPort ρ) hh.symm)⟩⟩
  have hNonadjacent (ρ : Ioo (0 : ℝ) bound) (i j : Fin (guideN+3)) (hij : i.val+1<j.val) :
      Disjoint (range ((fullPiece ρ) i)) (range ((fullPiece ρ) j)) := by
    apply disjoint_left.mpr
    rintro x ⟨s,hs⟩ ⟨t,ht⟩
    obtain ⟨hs1,ht0⟩ := (hFullOrdered ρ) i j (show i<j from by change i.val<j.val; omega)
      s t (hs.trans ht.symm)
    have hh := (hFullPortInjective ρ) (((hFullOne ρ) i).symm.trans (by simpa [hs1,ht0] using hs.trans ht.symm) |>.trans ((hFullZero ρ) j))
    have hv := congrArg Fin.val hh
    simp only [Fin.val_succ,Fin.val_castSucc] at hv
    omega
  have hQEmbedded (ρ : Ioo (0 : ℝ) bound) : IsEmbedding (q ρ) :=
    ((q ρ).continuous.isClosedEmbedding (hq ρ)).isEmbedding
  have hQZero (ρ : Ioo (0 : ℝ) bound) : q ρ 0 = beta ρ := by
    have hh : q ρ 0 = fullPort ρ 0 := (qPath ρ).source
    rw [hh]
    change fullPort ρ (0 : Fin (guideN+1)).castSucc.castSucc.castSucc = beta ρ
    simp only [fullPort,guidePort,Fin.lastCases_castSucc]
    change rawGuideRail ρ (guideLabel 0) 0 = beta ρ
    rw [hGuideFirstLabel]
    exact hFirstRailZero ρ
  have hQOne (ρ : Ioo (0 : ℝ) bound) : q ρ 1 = a (joint.clock 1) := by
    have hh : q ρ 1 = fullPort ρ (Fin.last (guideN+3)) := (qPath ρ).target
    simpa [fullPort,hRetainedOne] using hh
  have hActualCuts (ρ : Ioo (0 : ℝ) bound) :=
    hFinitePathClocks (guideN+2) (fullPort ρ) (fullPaths ρ)
  let cuts (ρ : Ioo (0 : ℝ) bound) := Classical.choose (hActualCuts ρ)
  have hCuts (ρ : Ioo (0 : ℝ) bound) := Classical.choose_spec (hActualCuts ρ)
  let clearTrace (ρ : Ioo (0 : ℝ) bound) : Set ↥F :=
    range (firstRail ρ) ∪ (⋃ j : MeshPiece, range (middleRail ρ j.1 j.2)) ∪ range (lastRail ρ)
  let guidingTrace (ρ : Ioo (0 : ℝ) bound) : Set ↥F := ⋃ i, range (guideRail ρ i)
  have hClearTrace (ρ : Ioo (0 : ℝ) bound) (k : Option ι) : Disjoint (clearTrace ρ) (range (f k)) := by
    apply disjoint_left.mpr
    intro y hy hk
    rcases hy with (hfirst | hmiddle) | hlast
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hFirstData ρ
      exact disjoint_left.mp (hclear k) hfirst hk
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hmiddle
      obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hMiddleData ρ j.1 j.2
      exact disjoint_left.mp (hclear k) hj hk
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hLastData ρ
      exact disjoint_left.mp (hclear k) hlast hk
  have hGuideRawTrace (ρ : Ioo (0 : ℝ) bound) :
      guidingTrace ρ = ⋃ i : RawGuideIndex, range (rawGuideRail ρ i) := by
    ext y
    constructor
    · intro hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨guideLabel i,hi⟩
    · intro hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨guideLabel.symm i,by simpa only [guideRail,guideLabel.apply_symm_apply] using hi⟩
  have hGuidingEventClearTrace (ρ : Ioo (0 : ℝ) bound) :
      guidingTrace ρ = (⋃ p : ↥P, range (chosenEventRail p ρ)) ∪ clearTrace ρ := by
    rw [hGuideRawTrace]
    ext y
    constructor
    · intro hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      rcases i with u | (j | (j | u))
      · exact Or.inr (Or.inl (Or.inl hi))
      · exact Or.inr (Or.inl (Or.inr (mem_iUnion.mpr ⟨j,hi⟩)))
      · exact Or.inl (mem_iUnion.mpr ⟨eventLabel j,hi⟩)
      · exact Or.inr (Or.inr hi)
    · rintro (hevent | (hfirst | hmiddle) | hlast)
      · obtain ⟨p,hp⟩ := mem_iUnion.mp hevent
        refine mem_iUnion.mpr ⟨Sum.inr (Sum.inr (Sum.inl (eventLabel.symm p))),?_⟩
        simpa only [rawGuideRail,Sum.elim_inr,Sum.elim_inl,eventLabel.apply_symm_apply] using hp
      · exact mem_iUnion.mpr ⟨Sum.inl (),hfirst⟩
      · obtain ⟨j,hj⟩ := mem_iUnion.mp hmiddle
        exact mem_iUnion.mpr ⟨Sum.inr (Sum.inl j),hj⟩
      · exact mem_iUnion.mpr ⟨Sum.inr (Sum.inr (Sum.inr ())),hlast⟩
  have hFullPieceTrace (ρ : Ioo (0 : ℝ) bound) :
      (⋃ i, range (fullPiece ρ i)) = guidingTrace ρ ∪ range cap ∪ range retained := by
    ext y
    constructor
    · intro hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      revert hi
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro hi
        exact Or.inr (by simpa only [fullPiece,Fin.lastCases_last] using hi)
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · intro hi
          exact Or.inl (Or.inr (by simpa only [fullPiece,Fin.lastCases_castSucc,Fin.lastCases_last] using hi))
        · intro hi
          exact Or.inl (Or.inl (mem_iUnion.mpr ⟨j,by simpa only [fullPiece,Fin.lastCases_castSucc] using hi⟩))
    · rintro ((hguide | hcap) | hret)
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hguide
        exact mem_iUnion.mpr ⟨i.castSucc.castSucc,by simpa only [fullPiece,Fin.lastCases_castSucc] using hi⟩
      · exact mem_iUnion.mpr ⟨(Fin.last (guideN+1)).castSucc,by simpa only [fullPiece,Fin.lastCases_castSucc,Fin.lastCases_last] using hcap⟩
      · exact mem_iUnion.mpr ⟨Fin.last (guideN+2),by simpa only [fullPiece,Fin.lastCases_last] using hret⟩
  have hQGuidingSuffixTrace (ρ : Ioo (0 : ℝ) bound) : range (q ρ) = guidingTrace ρ ∪ range suffix := by
    rw [hqRange,hFullPieceTrace,hSuffixRange,union_assoc]
  have hQContactTrace (ρ : Ioo (0 : ℝ) bound) :
      range (q ρ) = (⋃ p : ↥P, range (chosenEventRail p ρ)) ∪ clearTrace ρ ∪ range suffix := by
    rw [hQGuidingSuffixTrace,hGuidingEventClearTrace]
  have hGuidingMissB (ρ : Ioo (0 : ℝ) bound) : Disjoint (guidingTrace ρ) (range b) := by
    apply disjoint_left.mpr
    intro y hy hb
    obtain ⟨i,hi⟩ := mem_iUnion.mp hy
    exact disjoint_left.mp (hRawGuidesMissB ρ (guideLabel i)) hi hb
  have hActualContactCounts (ρ : Ioo (0 : ℝ) bound) (k : Option ι)
      (hv : k ≠ some v) (hw : k ≠ some w) :
      ∃ charge : ↥(range (q ρ) ∩ range (f k)) →
          (↥((range d.second \ {d.first 1}) ∩ range (f k)) ⊕
            ↥((range a \ range d.first) ∩ range (f k))) ⊕
            ↥({d.first 1} ∩ range (f k)),
        Function.Injective charge ∧
        (range (q ρ) ∩ range (f k)).Finite ∧
        (range (q ρ) ∩ range (f k)).ncard ≤
          ((range d.second \ {d.first 1}) ∩ range (f k)).ncard +
          (((range a \ range d.first) ∩ range (f k)).ncard +
            ({d.first 1} ∩ range (f k)).ncard) := by
    rw [hQContactTrace]
    exact hContactAssembly (fun p => range (chosenEventRail p ρ))
      (fun p k hv hw => hChosenEventContacts p ρ k hv hw)
      (fun p k hk => hChosenEventNonincident p ρ k hk)
      (clearTrace ρ) (fun k _ => hClearTrace ρ k) k hv hw
  let charge (ρ : Ioo (0 : ℝ) bound) (k : Option ι) (hv : k ≠ some v) (hw : k ≠ some w) :=
    Classical.choose (hActualContactCounts ρ k hv hw)
  have hChargeData (ρ : Ioo (0 : ℝ) bound) (k : Option ι) (hv : k ≠ some v) (hw : k ≠ some w) :=
    Classical.choose_spec (hActualContactCounts ρ k hv hw)
  have hActualSelectedCounts (ρ : Ioo (0 : ℝ) bound) :
      (range (q ρ) ∩ range b).Finite ∧
      range (q ρ) ∩ range b ⊆ (range a ∩ range b) \ {d.first 1} ∧
      (range (q ρ) ∩ range b).ncard + 1 ≤ (range a ∩ range b).ncard := by
    rw [hQGuidingSuffixTrace]
    exact hSelectedContactAssembly (guidingTrace ρ) (hGuidingMissB ρ)
  have hQCornerRemoved (ρ : Ioo (0 : ℝ) bound) : d.first 1 ∉ range (q ρ) := by
    rw [hQGuidingSuffixTrace]
    rintro (hguide | hsuffix)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hguide
      exact disjoint_left.mp (hRawGuidesMissA ρ (guideLabel i)) hi ⟨d.aFinish,hfirst1.symm⟩
    · exact hSuffixCornerRemoved hsuffix
  let kind : Fin (guideN+3) → Fin 4 := Fin.lastCases 0 (Fin.lastCases 1 (fun i => rawGuideKind (guideLabel i)))
  let cornerIndex : Fin (guideN+3) := (Fin.last (guideN+1)).castSucc
  have hRawKind (i : RawGuideIndex) : rawGuideKind i = 2 ∨ rawGuideKind i = 3 := by
    rcases i with u | (j | (j | u)) <;> simp [rawGuideKind]
  have hRetainedKind (i : Fin (guideN+3)) : kind i = 0 ↔ i.val = guideN+2 := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [kind]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [kind]
      · have hh := hRawKind (guideLabel j)
        have hn : j.val ≠ guideN+2 := by have := j.isLt; omega
        rcases hh with hh | hh <;> simp [kind,hh,hn]
  have hCornerKind (i : Fin (guideN+3)) : kind i = 1 ↔ i = cornerIndex := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hn : Fin.last (guideN+2) ≠ cornerIndex := by intro h; have := congrArg Fin.val h; simp [cornerIndex] at this
      simp [kind,hn]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [kind,cornerIndex]
      · have hn : j.castSucc.castSucc ≠ cornerIndex := by
          intro h
          have hh := congrArg Fin.val h
          simp only [Fin.val_castSucc,cornerIndex,Fin.val_last] at hh
          have := j.isLt
          omega
        rcases hRawKind (guideLabel j) with hh | hh <;> simp [kind,hh,hn]
  have hEventGuide (i : Fin (guideN+3)) (hi : kind i = 2) : i.val < guideN+1 := by
    revert hi
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro h; norm_num [kind] at h
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro h; norm_num [kind] at h
      · intro h
        exact j.isLt
  let eventGuide (i : {i : Fin (guideN+3) // kind i = 2}) : Fin (guideN+1) := ⟨i.val.val,hEventGuide i.val i.property⟩
  have hEventGuideKind (i : {i : Fin (guideN+3) // kind i = 2}) : rawGuideKind (guideLabel (eventGuide i)) = 2 := by
    have he : i.val = (eventGuide i).castSucc.castSucc := Fin.ext rfl
    have hi := i.property
    rw [he] at hi
    simpa only [kind,Fin.lastCases_castSucc] using hi
  let rawEventDecode (i : {i : RawGuideIndex // rawGuideKind i = 2}) : Fin eventCount := by
    rcases i with ⟨i,hi⟩
    rcases i with u | (j | (j | u))
    · norm_num [rawGuideKind] at hi
    · norm_num [rawGuideKind] at hi
    · exact j
    · norm_num [rawGuideKind] at hi
  have hRawEventDecode (i : {i : RawGuideIndex // rawGuideKind i = 2}) :
      i.val = Sum.inr (Sum.inr (Sum.inl (rawEventDecode i))) := by
    rcases i with ⟨i,hi⟩
    rcases i with u | (j | (j | u))
    · norm_num [rawGuideKind] at hi
    · norm_num [rawGuideKind] at hi
    · rfl
    · norm_num [rawGuideKind] at hi
  let eventIndex (i : {i : Fin (guideN+3) // kind i = 2}) : Fin eventCount :=
    rawEventDecode ⟨guideLabel (eventGuide i),hEventGuideKind i⟩
  have hEventInverse (i : {i : Fin (guideN+3) // kind i = 2}) :
      guideLabel (eventGuide i) = Sum.inr (Sum.inr (Sum.inl (eventIndex i))) := hRawEventDecode ⟨guideLabel (eventGuide i),hEventGuideKind i⟩
  have hEventInjective : Function.Injective eventIndex := by
    intro i j he
    apply Subtype.ext
    apply Fin.ext
    have hh : eventGuide i = eventGuide j := guideLabel.injective
      ((hEventInverse i).trans ((congrArg (fun k => Sum.inr (Sum.inr (Sum.inl k))) he).trans (hEventInverse j).symm))
    exact congrArg (fun k : Fin (guideN+1) => k.val) hh
  let RawGapIndex := Unit ⊕ (MeshPiece ⊕ Unit)
  let gapEncode : RawGapIndex → RawGuideIndex := Sum.elim Sum.inl
    (Sum.elim (fun j => Sum.inr (Sum.inl j)) (fun u => Sum.inr (Sum.inr (Sum.inr u))))
  let rawGapDecode (i : {i : RawGuideIndex // rawGuideKind i = 3}) : RawGapIndex := by
    rcases i with ⟨i,hi⟩
    rcases i with u | (j | (j | u))
    · exact Sum.inl u
    · exact Sum.inr (Sum.inl j)
    · norm_num [rawGuideKind] at hi
    · exact Sum.inr (Sum.inr u)
  have hRawGapDecode (i : {i : RawGuideIndex // rawGuideKind i = 3}) : i.val = gapEncode (rawGapDecode i) := by
    rcases i with ⟨i,hi⟩
    rcases i with u | (j | (j | u))
    · rfl
    · rfl
    · norm_num [rawGuideKind] at hi
    · rfl
  have hGapGuide (i : Fin (guideN+3)) (hi : kind i = 3) : i.val < guideN+1 := by
    revert hi
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro h; norm_num [kind] at h
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro h; norm_num [kind] at h
      · intro h
        exact j.isLt
  let gapGuide (i : {i : Fin (guideN+3) // kind i = 3}) : Fin (guideN+1) := ⟨i.val.val,hGapGuide i.val i.property⟩
  have hGapGuideKind (i : {i : Fin (guideN+3) // kind i = 3}) : rawGuideKind (guideLabel (gapGuide i)) = 3 := by
    have he : i.val = (gapGuide i).castSucc.castSucc := Fin.ext rfl
    have hi := i.property
    rw [he] at hi
    simpa only [kind,Fin.lastCases_castSucc] using hi
  let gapIndex (i : {i : Fin (guideN+3) // kind i = 3}) := rawGapDecode ⟨guideLabel (gapGuide i),hGapGuideKind i⟩
  have hGapInverse (i : {i : Fin (guideN+3) // kind i = 3}) : guideLabel (gapGuide i) = gapEncode (gapIndex i) := hRawGapDecode ⟨guideLabel (gapGuide i),hGapGuideKind i⟩
  have hIntervalHomeoInterior (H : Interval ≃ₜ Interval) (t : Interval)
      (ht : t ∈ Ioo (0:Interval) 1) : H t ∈ Ioo (0:Interval) 1 := by
    rcases H.continuous.strictMono_of_inj_boundedOrder' H.injective with hm | ha
    · exact ⟨(unitInterval.nonneg (H 0)).trans_lt (hm ht.1),
        (hm ht.2).trans_le (unitInterval.le_one (H 1))⟩
    · exact ⟨(unitInterval.nonneg (H 1)).trans_lt (ha ht.2),
        (ha ht.1).trans_le (unitInterval.le_one (H 0))⟩
  have hIntervalHomeoOne (H : Interval ≃ₜ Interval) : H 1 = 0 ∨ H 1 = 1 := by
    rcases H.continuous.strictMono_of_inj_boundedOrder' H.injective with hm | ha
    · right
      apply le_antisymm (show H 1 ≤ (1:Interval) from unitInterval.le_one _)
      have hh := hm.monotone (show H.symm 1 ≤ (1:Interval) from unitInterval.le_one _)
      rwa [H.apply_symm_apply] at hh
    · left
      apply le_antisymm _ (show (0:Interval) ≤ H 1 from unitInterval.nonneg _)
      have hh := ha.antitone (show H.symm 0 ≤ (1:Interval) from unitInterval.le_one _)
      rwa [H.apply_symm_apply] at hh
  have hOrientedEntryLtOne : orientedEntry < (1:Interval) :=
    (hOrientedAffine joint.guideEntryTime_interior.2).trans_le (unitInterval.le_one _)
  have hGuideFrontierStart (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+1)) (s : Interval)
      (hs : (guideRail ρ i s).val ∈ frontier F) : guideRail ρ i s = beta ρ := by
    obtain ⟨hiE,hiF,hi0,hi1,hiO,hiW,hiWidth⟩ := hRawGuideData ρ (guideLabel i)
    let θ := joint.guideClock.symm (rawGuideCoordinates ρ (guideLabel i) s).1
    have hθentry : θ ≤ orientedEntry := by
      have hh := hiO.monotone (show s ≤ (1:Interval) from unitInterval.le_one s)
      rw [hi1,joint.guideClock.symm_apply_apply] at hh
      exact hh.trans (hRawGuideEntryBounds (guideLabel i))
    by_cases hθpos : (0:Interval) < θ
    · have ht := hIntervalHomeoInterior joint.guideClock θ ⟨hθpos,hθentry.trans_lt hOrientedEntryLtOne⟩
      have ht' : (rawGuideCoordinates ρ (guideLabel i) s).1 ∈ Ioo (0:Interval) 1 := by
        simpa only [θ,joint.guideClock.apply_symm_apply] using ht
      have hInterior := correctedJoint.guideStrip_interior _ ht' (rawGuideCoordinates ρ (guideLabel i) s).2
      have hFrontier : (correctedJoint.guideStrip (rawGuideCoordinates ρ (guideLabel i) s)).val ∈ frontier F := by
        rwa [←hiF s]
      exact (hFrontier.2 hInterior).elim
    · have hθzero : θ = 0 := le_antisymm (le_of_not_gt hθpos) (show (0:Interval) ≤ θ from unitInterval.nonneg θ)
      have hleft : rawGuideLeft (guideLabel i) = 0 := by
        apply le_antisymm _ (show (0:Interval) ≤ rawGuideLeft (guideLabel i) from unitInterval.nonneg _)
        have hh := hiO.monotone (show (0:Interval) ≤ s from unitInterval.nonneg s)
        rw [hi0,joint.guideClock.symm_apply_apply] at hh
        exact hh.trans hθzero.le
      have hstart : joint.guideClock.symm (rawGuideCoordinates ρ (guideLabel i) 0).1 = 0 := by
        rw [hi0,joint.guideClock.symm_apply_apply,hleft]
      have hs0 : s = 0 := hiO.injective (hθzero.trans hstart.symm)
      have hlab : guideLabel i = Sum.inl () := hRawLeftInjective hleft
      subst s
      change rawGuideRail ρ (guideLabel i) 0 = beta ρ
      rw [hlab]
      exact hFirstRailZero ρ
  have hRetainedFrontierEnd (s : Interval) (hs : (retained s).val ∈ frontier F) : s = 1 := by
    by_contra hn
    have hlt : s < (1:Interval) := lt_top_iff_ne_top.mpr hn
    have hcut : 0 < joint.cut.val ∧ joint.cut.val < 1 := joint.cut_interior
    have htime : CurveComplex.BranchedDoubleCover.intervalAffine joint.cut 1 s ∈ Ioo (0:Interval) 1 := by
      constructor
      · change 0 < (1-s.val)*joint.cut.val+s.val*1
        have hnon := mul_nonneg s.property.1 (sub_nonneg.mpr hcut.2.le)
        nlinarith only [hnon,hcut.1]
      · change (1-s.val)*joint.cut.val+s.val*1 < 1
        have hprod := mul_pos (sub_pos.mpr (show s.val<1 from hlt)) (sub_pos.mpr hcut.2)
        nlinarith only [hprod]
    have ht := hIntervalHomeoInterior joint.clock _ htime
    apply (hproper (some v)).2.2.2 _ ht
    simpa only [hRetainedFormula,a,f,augmented,Option.elim_some] using hs
  have hQProper (ρ : Ioo (0 : ℝ) bound) (t : Interval) (ht : t ∈ Ioo (0:Interval) 1) :
      (q ρ t).val ∉ frontier F := by
    intro hfront
    obtain ⟨i,u,he⟩ := CurveComplexGenusTwo.SourceTopology.nonemptyGraphPath_point_on_arc
      (guideN+2) (fullPort ρ) (fullPaths ρ) t
    change q ρ t = fullPiece ρ i u at he
    revert he
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro he
      have hh : q ρ t = retained u := by simpa only [fullPiece,Fin.lastCases_last] using he
      have hu : u = 1 := hRetainedFrontierEnd u (by rwa [←hh])
      have htt : t = 1 := hq ρ (hh.trans (by rw [hu,hRetainedOne]) |>.trans (hQOne ρ).symm)
      exact (ne_of_lt ht.2) htt
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro he
        have hh : q ρ t = cap u := by simpa only [fullPiece,Fin.lastCases_castSucc,Fin.lastCases_last] using he
        exact hfront.2 (by rw [hh]; exact hCapInterior u)
      · intro he
        have hh : q ρ t = guideRail ρ j u := by simpa only [fullPiece,Fin.lastCases_castSucc] using he
        have hu := hGuideFrontierStart ρ j u (by rwa [←hh])
        have htt : t = 0 := hq ρ (hh.trans hu |>.trans (hQZero ρ).symm)
        exact (ne_of_gt ht.1) htt
  have hPieceClock (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+3)) (t : Interval) :
      fullPiece ρ i t = q ρ
        (CurveComplex.BranchedDoubleCover.intervalAffine (cuts ρ i.castSucc) (cuts ρ i.succ) t) :=
    (hCuts ρ).2.2.2 i t
  let prefixEnd (ρ : Ioo (0 : ℝ) bound) := cuts ρ (Fin.last (guideN+2)).castSucc
  have hPrefixEndLtOne (ρ : Ioo (0 : ℝ) bound) : prefixEnd ρ < (1:Interval) := by
    have hh := (hCuts ρ).1 (Fin.castSucc_lt_last (Fin.last (guideN+2)))
    rwa [(hCuts ρ).2.2.1] at hh
  have hIntervalAffineBounds (l r : Interval) (hlr : l ≤ r) (t : Interval) :
      CurveComplex.BranchedDoubleCover.intervalAffine l r t ∈ Icc l r := by
    constructor
    · change l.val ≤ (1-t.val)*l.val+t.val*r.val
      have hh := mul_nonneg t.property.1 (sub_nonneg.mpr (show l.val ≤ r.val from hlr))
      nlinarith only [hh]
    · change (1-t.val)*l.val+t.val*r.val ≤ r.val
      have hh := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr (show l.val ≤ r.val from hlr))
      nlinarith only [hh]
  have hPieceBeforePrefix (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+3))
      (hi : i.val < guideN+2) (u : Interval) :
      fullPiece ρ i u ∈ q ρ '' Icc (0:Interval) (prefixEnd ρ) := by
    refine ⟨CurveComplex.BranchedDoubleCover.intervalAffine (cuts ρ i.castSucc) (cuts ρ i.succ) u,
      ⟨unitInterval.nonneg _,?_⟩,(hPieceClock ρ i u).symm⟩
    exact (hIntervalAffineBounds _ _ ((hCuts ρ).1.monotone i.castSucc_lt_succ.le) u).2.trans
      ((hCuts ρ).1.monotone (show i.succ ≤ (Fin.last (guideN+2)).castSucc from by
        change i.val+1 ≤ guideN+2
        omega))
  have hQChangedRange (ρ : Ioo (0 : ℝ) bound) :
      q ρ '' Icc (0:Interval) (prefixEnd ρ) = guidingTrace ρ ∪ range cap := by
    ext y
    constructor
    · rintro ⟨t,ht,rfl⟩
      obtain ⟨i,u,he⟩ := CurveComplexGenusTwo.SourceTopology.nonemptyGraphPath_point_on_arc
        (guideN+2) (fullPort ρ) (fullPaths ρ) t
      change q ρ t = fullPiece ρ i u at he
      revert he
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro he
        have htime : t = CurveComplex.BranchedDoubleCover.intervalAffine
            (prefixEnd ρ) (cuts ρ (Fin.last (guideN+3))) u :=
          hq ρ (he.trans (hPieceClock ρ (Fin.last (guideN+2)) u))
        have hu : u = 0 := by
          apply Subtype.ext
          have hh : t.val ≤ (prefixEnd ρ).val := ht.2
          have hCutsOne : cuts ρ (Fin.last (guideN+3)) = 1 := (hCuts ρ).2.2.1
          rw [htime,hCutsOne] at hh
          change (1-u.val)*(prefixEnd ρ).val+u.val*1 ≤ (prefixEnd ρ).val at hh
          have hcut : (prefixEnd ρ).val < 1 := hPrefixEndLtOne ρ
          have hnon : 0 ≤ u.val := u.property.1
          have hprod : 0 ≤ u.val*(1-(prefixEnd ρ).val) := mul_nonneg hnon (sub_nonneg.mpr hcut.le)
          have hzero : u.val*(1-(prefixEnd ρ).val) = 0 := by nlinarith only [hh,hprod]
          exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (sub_pos.mpr hcut))
        have hh : q ρ t = retained u := by simpa only [fullPiece,Fin.lastCases_last] using he
        have hy : q ρ t = cap 1 := hh.trans (by rw [hu,hRetainedZero])
        exact Or.inr ⟨1,hy.symm⟩
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · intro he
          exact Or.inr ⟨u,by simpa only [fullPiece,Fin.lastCases_castSucc,Fin.lastCases_last] using he.symm⟩
        · intro he
          exact Or.inl (mem_iUnion.mpr ⟨j,u,by simpa only [fullPiece,Fin.lastCases_castSucc] using he.symm⟩)
    · rintro (hguide | hcap)
      · obtain ⟨i,u,rfl⟩ := mem_iUnion.mp hguide
        have hh := hPieceBeforePrefix ρ i.castSucc.castSucc (by
          simp only [Fin.val_castSucc]
          exact i.isLt.trans_le (Nat.le_succ _)) u
        simpa only [fullPiece,Fin.lastCases_castSucc] using hh
      · obtain ⟨u,rfl⟩ := hcap
        have hh := hPieceBeforePrefix ρ (Fin.last (guideN+1)).castSucc (by simp) u
        simpa only [fullPiece,Fin.lastCases_castSucc,Fin.lastCases_last] using hh
  have hGuidingTraceV (ρ : Ioo (0 : ℝ) bound) : guidingTrace ρ ⊆ V := by
    intro y hy
    obtain ⟨i,u,rfl⟩ := mem_iUnion.mp hy
    obtain ⟨he,hf,h0,h1,ho,hw,hwidth⟩ := hRawGuideData ρ (guideLabel i)
    rw [hf]
    exact correctedJoint.guide_full_window_fibers _ (hw u) _
  have hGuidingTraceMissA (ρ : Ioo (0 : ℝ) bound) : Disjoint (guidingTrace ρ) (range a) := by
    apply disjoint_left.mpr
    intro y hy ha
    obtain ⟨i,hi⟩ := mem_iUnion.mp hy
    exact disjoint_left.mp (hRawGuidesMissA ρ (guideLabel i)) hi ha
  have hChangedInV (ρ : Ioo (0 : ℝ) bound) : q ρ '' Icc (0:Interval) (prefixEnd ρ) ⊆ V := by
    rw [hQChangedRange]
    exact union_subset (hGuidingTraceV ρ) hCapV
  have hChangedMeetsA (ρ : Ioo (0 : ℝ) bound) :
      (q ρ '' Icc (0:Interval) (prefixEnd ρ)) ∩ range a = {a (joint.clock joint.cut)} := by
    rw [hQChangedRange,union_inter_distrib_right,
      disjoint_iff_inter_eq_empty.mp (hGuidingTraceMissA ρ),empty_union,hCapMeetA]
  let GuidePiece := {i : Fin (guideN+3) // i.val < cornerIndex.val}
  let guidePieceIndex (i : GuidePiece) : Fin (guideN+1) := ⟨i.val.val,by
    simpa only [cornerIndex,Fin.val_castSucc,Fin.val_last] using i.property⟩
  let chainGuideCoordinates (ρ : Ioo (0 : ℝ) bound) (i : GuidePiece) := guideCoordinates ρ (guidePieceIndex i)
  let chainGuidePortTime (i : Fin (guideN+4)) : Interval :=
    if hi : i.val < guideN+2 then guideTimes ⟨i.val,hi⟩ else 1
  have hGuidePieceIndex (i : GuidePiece) : i.val = (guidePieceIndex i).castSucc.castSucc := Fin.ext rfl
  have hGuidePieceFormula (ρ : Ioo (0 : ℝ) bound) (i : GuidePiece) :
      fullPiece ρ i.val = guideRail ρ (guidePieceIndex i) := by
    rw [hGuidePieceIndex]
    simp only [fullPiece,Fin.lastCases_castSucc]
  have hChainGuideTime (j : Fin (guideN+2)) : chainGuidePortTime j.castSucc.castSucc = guideTimes j := by
    dsimp only [chainGuidePortTime]
    rw [dif_pos (show j.castSucc.castSucc.val < guideN+2 from j.isLt)]
    rfl
  have hChainGuideTimeBound (i : Fin (guideN+4)) (hi : i.val ≤ cornerIndex.val) :
      chainGuidePortTime i ≤ orientedEntry := by
    have hb : i.val < guideN+2 := by
      have hh : i.val ≤ guideN+1 := hi
      omega
    let j : Fin (guideN+2) := ⟨i.val,hb⟩
    have htime : chainGuidePortTime i = guideTimes j := by
      simp only [chainGuidePortTime,dif_pos hb]
      rfl
    rw [htime]
    exact ((hGuideTimesOrder.monotone (Fin.le_last j))).trans_eq hGuideTimesOne
  have hChainGuideFactor (ρ : Ioo (0 : ℝ) bound) (i : GuidePiece) (t : Interval) :
      fullPiece ρ i.val t = correctedJoint.guideStrip (chainGuideCoordinates ρ i t) := by
    rw [hGuidePieceFormula]
    exact (hRawGuideData ρ (guideLabel (guidePieceIndex i))).2.1 t
  have hChainGuideZero (ρ : Ioo (0 : ℝ) bound) (i : GuidePiece) :
      (chainGuideCoordinates ρ i 0).1 = joint.guideClock (chainGuidePortTime i.val.castSucc) := by
    have hi : i.val.castSucc = (guidePieceIndex i).castSucc.castSucc.castSucc := congrArg Fin.castSucc (hGuidePieceIndex i)
    rw [hi,hChainGuideTime]
    exact (hRawGuideData ρ (guideLabel (guidePieceIndex i))).2.2.1.trans
      (congrArg joint.guideClock (hGuideTimesFaces (guidePieceIndex i)).1)
  have hChainGuideOne (ρ : Ioo (0 : ℝ) bound) (i : GuidePiece) :
      (chainGuideCoordinates ρ i 1).1 = joint.guideClock (chainGuidePortTime i.val.succ) := by
    have hi : i.val.succ = (guidePieceIndex i).succ.castSucc.castSucc := by
      rw [hGuidePieceIndex]
      simp only [Fin.succ_castSucc]
    rw [hi,hChainGuideTime]
    exact (hRawGuideData ρ (guideLabel (guidePieceIndex i))).2.2.2.1.trans
      (congrArg joint.guideClock (hGuideTimesFaces (guidePieceIndex i)).2)
  have hChainGuideOrder (ρ : Ioo (0 : ℝ) bound) (i : GuidePiece) :
      StrictMono (fun t => joint.guideClock.symm (chainGuideCoordinates ρ i t).1) :=
    (hRawGuideData ρ (guideLabel (guidePieceIndex i))).2.2.2.2.1
  have hChainGuideWindow (ρ : Ioo (0 : ℝ) bound) (i : GuidePiece) (t : Interval) :
      (chainGuideCoordinates ρ i t).1 ∈ joint.guideWindow := by
    rw [←hCorrectedGuideWindow]
    exact (hRawGuideData ρ (guideLabel (guidePieceIndex i))).2.2.2.2.2.1 t
  have hChainGuideWidth (ρ : Ioo (0 : ℝ) bound) (i : GuidePiece) (t : Interval) :
      0 < (chainGuideCoordinates ρ i t).2.val ∧ (chainGuideCoordinates ρ i t).2.val < bound :=
    (hRawGuideData ρ (guideLabel (guidePieceIndex i))).2.2.2.2.2.2 t
  have hChainFirstWidth (ρ : Ioo (0 : ℝ) bound) (i : GuidePiece) (hi : i.val.val = 0) :
      (chainGuideCoordinates ρ i 0).2.val = ρ.val := by
    have hj : guidePieceIndex i = 0 := Fin.ext hi
    change (rawGuideCoordinates ρ (guideLabel (guidePieceIndex i)) 0).2.val = ρ.val
    rw [hj,hGuideFirstLabel]
    obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hFirstData ρ
    exact congrArg Subtype.val hu0
  have hChainGuideTimeZero : chainGuidePortTime 0 = 0 := by
    rw [show (0 : Fin (guideN+4)) = (0 : Fin (guideN+2)).castSucc.castSucc from rfl,hChainGuideTime]
    exact hGuideTimesZero
  have hChainGuideTimeOrder (i j : Fin (guideN+4)) (hij : i.val < j.val) (hj : j.val ≤ cornerIndex.val) :
      chainGuidePortTime i < chainGuidePortTime j := by
    have hjb : j.val < guideN+2 := by have hh : j.val ≤ guideN+1 := hj; omega
    have hib : i.val < guideN+2 := hij.trans hjb
    simp only [chainGuidePortTime,dif_pos hib,dif_pos hjb]
    exact hGuideTimesOrder hij
  have hChainGuideTimeLast : joint.guideClock (chainGuidePortTime cornerIndex.castSucc) = actualEntry := by
    have hi : cornerIndex.castSucc = (Fin.last (guideN+1)).castSucc.castSucc := rfl
    rw [hi,hChainGuideTime,hGuideTimesOne]
    exact joint.guideClock.apply_symm_apply actualEntry
  have hChainGuideTimeSelected (i : Fin (guideN+4)) (hi : i.val ≤ cornerIndex.val) :
      joint.guideClock (chainGuidePortTime i) ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) :=
    hOrientedSelectedClosed _ (hChainGuideTimeBound i hi)
  have hChainLastGuide (i : GuidePiece) (hi : i.val.val+1=cornerIndex.val) :
      guidePieceIndex i = Fin.last guideN := by
    apply Fin.ext
    have hh : i.val.val+1 = guideN+1 := hi
    change i.val.val = guideN
    omega
  have hChainGuideOldNegativeClear (ρ : Ioo (0 : ℝ) bound) (i : GuidePiece) :
      Disjoint (regionalHalfOldNegativeBand F joint.oldStrip joint.clock joint.cut joint.oldNegativeWidth)
        (regionalHalfGuideSlab F correctedJoint.guideStrip (chainGuideCoordinates ρ i)) := by
    obtain ⟨he,hf,h0,h1,ho,hw,hwidth⟩ := hRawGuideData ρ (guideLabel (guidePieceIndex i))
    apply hGuideSlabOldNegativeClear _ _ (fun t => (hwidth t).2)
    intro t
    have hh := ho.monotone (show t ≤ (1:Interval) from unitInterval.le_one t)
    rw [h1,joint.guideClock.symm_apply_apply] at hh
    exact hh.trans (hRawGuideEntryBounds _)
  have hChainGuideCornerInter (ρ : Ioo (0 : ℝ) bound) (i : GuidePiece) :
      regionalHalfGuideSlab F correctedJoint.guideStrip (chainGuideCoordinates ρ i) ∩
        chartPull F joint.cornerFan.chart (regionalHalfCornerHull joint.cornerDelta joint.cornerEntry cornerEpsilon) =
      if i.val.val+1=cornerIndex.val then
        correctedJoint.guideStrip '' {z | z.1=(chainGuideCoordinates ρ i 1).1 ∧
          0≤z.2.val ∧ z.2.val≤(chainGuideCoordinates ρ i 1).2.val}
      else ∅ := by
    by_cases hi : i.val.val+1=cornerIndex.val
    · rw [if_pos hi]
      have hj := hChainLastGuide i hi
      have hh : chainGuideCoordinates ρ i = lastCoordinates ρ := by
        change rawGuideCoordinates ρ (guideLabel (guidePieceIndex i)) = lastCoordinates ρ
        rw [hj,hGuideLastLabel]
        rfl
      rw [hh]
      exact (hLastSlabs ρ).2.2
    · rw [if_neg hi]
      obtain ⟨he,hf,h0,h1,ho,hw,hwidth⟩ := hRawGuideData ρ (guideLabel (guidePieceIndex i))
      have hj : (guidePieceIndex i).val+1 < guideN+1 := by
        change i.val.val+1 < guideN+1
        have hh : i.val.val < guideN+1 := (guidePieceIndex i).isLt
        have hn : i.val.val+1≠guideN+1 := hi
        omega
      apply hGuideSlabBeforeCorner _ _ (fun t => (hwidth t).2)
      intro t
      have hh := ho.monotone (show t ≤ (1:Interval) from unitInterval.le_one t)
      rw [h1,joint.guideClock.symm_apply_apply,(hGuideTimesFaces (guidePieceIndex i)).2] at hh
      exact hh.trans_lt (hGuideTimesOrder (show (guidePieceIndex i).succ < Fin.last (guideN+1) from hj) |>.trans_eq hGuideTimesOne)
  let chainEventP (i : {i : Fin (guideN+3) // kind i = 2}) : ↥P := eventLabel (eventIndex i)
  let chainEventSite (i : {i : Fin (guideN+3) // kind i = 2}) : ↥F := (chainEventP i).val
  have hChainEventSiteInjective : Function.Injective chainEventSite :=
    Subtype.val_injective.comp (eventLabel.injective.comp hEventInjective)
  let chainEventFan (i : {i : Fin (guideN+3) // kind i = 2}) := Classical.choose (hCalibratedEvents (chainEventP i))
  let chainEventLeft (ρ : Ioo (0 : ℝ) bound) (i : {i : Fin (guideN+3) // kind i = 2}) := chosenEventLeft (chainEventP i) ρ
  let chainEventRight (ρ : Ioo (0 : ℝ) bound) (i : {i : Fin (guideN+3) // kind i = 2}) := chosenEventRight (chainEventP i) ρ
  have hChainEventPiece (ρ : Ioo (0 : ℝ) bound) (i : {i : Fin (guideN+3) // kind i = 2}) :
      fullPiece ρ i.val = chosenEventRail (chainEventP i) ρ := by
    have hi : i.val = (eventGuide i).castSucc.castSucc := Fin.ext rfl
    rw [hi]
    simp only [fullPiece,Fin.lastCases_castSucc,guideRail,hEventInverse,rawGuideRail,Sum.elim_inr,Sum.elim_inl]
    rfl
  have hChainEventMetadata (i : {i : Fin (guideN+3) // kind i = 2}) :
      (chartPull F (chainEventFan i).chart (Metric.closedBall (0 : Plane) 1) ⊆
        chartPull F (fan.window ⟨chainEventSite i,hPfan (chainEventP i).property⟩).chart (Metric.ball (0 : Plane) 1)) ∧
      (∀ h : chainEventSite i ∈ range b,
        incidentPorts f (chainEventSite i) (chainEventFan i).chart (chainEventFan i).left (chainEventFan i).right (⟨some w,h⟩,false) 1 = 0 ∧
        incidentPorts f (chainEventSite i) (chainEventFan i).chart (chainEventFan i).left (chainEventFan i).right (⟨some w,h⟩,true) 1 = 0) ∧
      (∀ j : incidentIndex f (chainEventSite i), j.val ≠ some w →
        incidentPorts f (chainEventSite i) (chainEventFan i).chart (chainEventFan i).left (chainEventFan i).right (j,false) 1 *
        incidentPorts f (chainEventSite i) (chainEventFan i).chart (chainEventFan i).left (chainEventFan i).right (j,true) 1 < 0) := by
    obtain ⟨X,τ,hτ,hSign,hX,hXZero,hNested,hAxis,hThird,hFormula⟩ :=
      Classical.choose_spec (hCalibratedEvents (chainEventP i))
    exact ⟨hNested,hAxis,hThird⟩
  have hChainEventHorizontal (ρ : Ioo (0 : ℝ) bound) (i : {i : Fin (guideN+3) // kind i = 2}) :
      chainEventLeft ρ i 1 = chainEventRight ρ i 1 ∧ chainEventLeft ρ i 1 ≠ 0 ∧
      chainEventLeft ρ i 0 ≠ chainEventRight ρ i 0 := by
    obtain ⟨hW,hEmbedded,hFactor,hZero,hOne,hOrder,hWindow,hWidth,hHeightSame,hHeightNonzero,
      hLongDistinct,hUnit,hFormula,hNested,hAxis,hThird,hContacts,hNonincident⟩ := hChosenEventData (chainEventP i) ρ
    exact ⟨hHeightSame,hHeightNonzero,hLongDistinct⟩
  have hChainEventFormula (ρ : Ioo (0 : ℝ) bound) (i : {i : Fin (guideN+3) // kind i = 2}) (t : Interval) :
      let z := (1-t.val) • chainEventLeft ρ i+t.val • chainEventRight ρ i
      z ∈ (chainEventFan i).chart.target ∧ (fullPiece ρ i.val t).val = (chainEventFan i).chart.symm z := by
    obtain ⟨hW,hEmbedded,hFactor,hZero,hOne,hOrder,hWindow,hWidth,hHeightSame,hHeightNonzero,
      hLongDistinct,hUnit,hFormula,hNested,hAxis,hThird,hContacts,hNonincident⟩ := hChosenEventData (chainEventP i) ρ
    have hh : let z := (1-t.val) • chosenEventLeft (chainEventP i) ρ+t.val • chosenEventRight (chainEventP i) ρ
      z ∈ (chosenEventWindow (chainEventP i) ρ).chart.target ∧
        (chosenEventRail (chainEventP i) ρ t).val = (chosenEventWindow (chainEventP i) ρ).chart.symm z := hFormula t
    have hw : chosenEventWindow (chainEventP i) ρ = chainEventFan i := hChosenEventFixedWindow (chainEventP i) ρ
    have hh' : let z := (1-t.val) • chosenEventLeft (chainEventP i) ρ+t.val • chosenEventRight (chainEventP i) ρ
      z ∈ (chainEventFan i).chart.target ∧
        (chosenEventRail (chainEventP i) ρ t).val = (chainEventFan i).chart.symm z := hw ▸ hh
    exact ⟨hh'.1,(congrArg (fun c : C(Interval,↥F) => (c t).val) (hChainEventPiece ρ i)).trans hh'.2⟩
  let rawGapChart : RawGapIndex → OpenPartialHomeomorph S Plane := Sum.elim (fun _ => firstGapChart)
    (Sum.elim (fun j => middleRailChart j.1 j.2) (fun _ => lastGapChart))
  let rawGapLeft (ρ : Ioo (0 : ℝ) bound) : RawGapIndex → Plane := Sum.elim (fun _ => firstLeft ρ)
    (Sum.elim (fun j => middleLeft ρ j.1 j.2) (fun _ => lastLeft ρ))
  let rawGapRight (ρ : Ioo (0 : ℝ) bound) : RawGapIndex → Plane := Sum.elim (fun _ => firstRight ρ)
    (Sum.elim (fun j => middleRight ρ j.1 j.2) (fun _ => lastRight ρ))
  let chainGapChart (i : {i : Fin (guideN+3) // kind i = 3}) := rawGapChart (gapIndex i)
  let chainGapLeft (ρ : Ioo (0 : ℝ) bound) (i : {i : Fin (guideN+3) // kind i = 3}) := rawGapLeft ρ (gapIndex i)
  let chainGapRight (ρ : Ioo (0 : ℝ) bound) (i : {i : Fin (guideN+3) // kind i = 3}) := rawGapRight ρ (gapIndex i)
  have hChainGapPiece (ρ : Ioo (0 : ℝ) bound) (i : {i : Fin (guideN+3) // kind i = 3}) :
      fullPiece ρ i.val = rawGuideRail ρ (gapEncode (gapIndex i)) := by
    have hi : i.val = (gapGuide i).castSucc.castSucc := Fin.ext rfl
    rw [hi]
    simp only [fullPiece,Fin.lastCases_castSucc,guideRail,hGapInverse]
  have hRawGapFormula (ρ : Ioo (0 : ℝ) bound) (i : RawGapIndex) (t : Interval) :
      let z := (1-t.val) • rawGapLeft ρ i+t.val • rawGapRight ρ i
      z ∈ (rawGapChart i).target ∧ (rawGuideRail ρ (gapEncode i) t).val = (rawGapChart i).symm z := by
    rcases i with u | (j | u)
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hFirstData ρ
      exact hformula t
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hMiddleData ρ j.1 j.2
      exact hformula t
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hLastData ρ
      exact hformula t
  have hChainGapFormula (ρ : Ioo (0 : ℝ) bound) (i : {i : Fin (guideN+3) // kind i = 3}) (t : Interval) :
      let z := (1-t.val) • chainGapLeft ρ i+t.val • chainGapRight ρ i
      z ∈ (chainGapChart i).target ∧ (fullPiece ρ i.val t).val = (chainGapChart i).symm z := by
    rw [hChainGapPiece]
    exact hRawGapFormula ρ (gapIndex i) t
  have hRawGapClear (ρ : Ioo (0 : ℝ) bound) (i : RawGapIndex) (k : Option ι) :
      Disjoint (range (rawGuideRail ρ (gapEncode i))) (range (f k)) := by
    rcases i with u | (j | u)
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hFirstData ρ
      exact hclear k
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hMiddleData ρ j.1 j.2
      exact hclear k
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hLastData ρ
      exact hclear k
  have hChainGapClear (ρ : Ioo (0 : ℝ) bound) (i : {i : Fin (guideN+3) // kind i = 3}) (k : Option ι) :
      Disjoint (range (fullPiece ρ i.val)) (range (f k)) := by
    rw [hChainGapPiece]
    exact hRawGapClear ρ (gapIndex i) k
  have hFullGuideExterior (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+1)) :
      range (guideRail ρ i) ⊆ correctedJoint.guideStrip '' {z | 0 < z.2.val ∧ z.2.val < bound} := by
    rintro y ⟨t,rfl⟩
    obtain ⟨he,hf,h0,h1,ho,hw,hwidth⟩ := hRawGuideData ρ (guideLabel i)
    exact ⟨rawGuideCoordinates ρ (guideLabel i) t,hwidth t,(hf t).symm⟩
  have hChainEventExterior (ρ : Ioo (0 : ℝ) bound) (i : {i : Fin (guideN+3) // kind i = 2}) :
      range (fullPiece ρ i.val) ⊆ correctedJoint.guideStrip '' {z | 0 < z.2.val ∧ z.2.val < bound} := by
    have hi : i.val = (eventGuide i).castSucc.castSucc := Fin.ext rfl
    rw [hi]
    simpa only [fullPiece,Fin.lastCases_castSucc] using hFullGuideExterior ρ (eventGuide i)
  have hChainGapExterior (ρ : Ioo (0 : ℝ) bound) (i : {i : Fin (guideN+3) // kind i = 3}) :
      range (fullPiece ρ i.val) ⊆ correctedJoint.guideStrip '' {z | 0 < z.2.val ∧ z.2.val < bound} := by
    have hi : i.val = (gapGuide i).castSucc.castSucc := Fin.ext rfl
    rw [hi]
    simpa only [fullPiece,Fin.lastCases_castSucc] using hFullGuideExterior ρ (gapGuide i)
  have hRawStartClear (ρ : Ioo (0 : ℝ) bound) (i : RawGuideIndex) (k : Option ι) :
      rawGuideRail ρ i 0 ∉ range (f k) := by
    rcases i with u | (j | (j | u))
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hFirstData ρ
      exact fun hk => disjoint_left.mp (hclear k) ⟨0,rfl⟩ hk
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hMiddleData ρ j.1 j.2
      exact fun hk => disjoint_left.mp (hclear k) ⟨0,rfl⟩ hk
    · let i : Fin (eventCount+1) := j.castSucc
      let q : Fin (middleCount i) := ⟨middleCount i-1,by have := hMiddleCount i; omega⟩
      obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hMiddleData ρ i q
      intro hk
      exact disjoint_left.mp (hclear k) ⟨1,hMiddleEventSeam ρ j⟩ hk
    · obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hw,hwidth,hformula,hclear⟩ := hLastData ρ
      exact fun hk => disjoint_left.mp (hclear k) ⟨0,rfl⟩ hk
  have hGuidePortsSafe (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+2)) (k : Option ι)
      (hk : k ≠ some w) : guidePort ρ i ∉ range (f k) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [guidePort,Fin.lastCases_last] using hCapZeroClear k hk
    · simpa only [guidePort,Fin.lastCases_castSucc,guideRail] using hRawStartClear ρ (guideLabel j) k
  have hRetainedOneSafe (k : Option ι) (hk : k ≠ some v) : retained 1 ∉ range (f k) := by
    rintro ⟨t,ht⟩
    have hEnd := hIntervalHomeoOne joint.clock
    have hBoundary : (retained 1).val ∈ boundaryCircle := by
      rw [hRetainedOne]
      rcases hEnd with h0 | h1
      · rw [h0]
        exact (r v).val.property.2.1
      · rw [h1]
        exact (r v).val.property.2.2.1
    have hFrontier : ((f k) t).val ∈ frontier F := by
      rw [ht]
      exact hBF hBoundary
    have htEnd : t = 0 ∨ t = 1 := by
      by_cases h0 : t = 0
      · exact Or.inl h0
      by_cases h1 : t = 1
      · exact Or.inr h1
      exact ((hproper k).2.2.2 t ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩ hFrontier).elim
    have he : f (some v) (joint.clock 1) = f k t := hRetainedOne.symm.trans ht.symm
    have hfour := hends (some v) k (Ne.symm hk)
    rcases hEnd with h0 | h1 <;> rcases htEnd with ht0 | ht1
    · exact hfour.1 (by simpa only [h0,ht0] using he)
    · exact hfour.2.1 (by simpa only [h0,ht1] using he)
    · exact hfour.2.2.1 (by simpa only [h1,ht0] using he)
    · exact hfour.2.2.2 (by simpa only [h1,ht1] using he)
  have hFullPortsSafe (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+4)) (k : Option ι)
      (hv : k ≠ some v) (hw : k ≠ some w) : fullPort ρ i ∉ range (f k) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [fullPort,Fin.lastCases_last] using hRetainedOneSafe k hv
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [fullPort,Fin.lastCases_castSucc,Fin.lastCases_last] using hCapOneClear k hv
      · simpa only [fullPort,Fin.lastCases_castSucc] using hGuidePortsSafe ρ j k hw
  have hQEndpointSafe (ρ : Ioo (0 : ℝ) bound) (j : ι) (hj : j ≠ v) :
      q ρ 0 ≠ f (some j) 0 ∧ q ρ 0 ≠ f (some j) 1 ∧ q ρ 1 ≠ f (some j) 0 ∧ q ρ 1 ≠ f (some j) 1 := by
    rw [hQZero,hQOne]
    refine ⟨?_,?_,?_,?_⟩
    · intro he
      exact hbetaSafe ρ (Or.inl ⟨j,hj,Or.inl he⟩)
    · intro he
      exact hbetaSafe ρ (Or.inl ⟨j,hj,Or.inr he⟩)
    · intro he
      exact hRetainedOneSafe (some j) (by simpa only [ne_eq,Option.some.injEq] using hj) ⟨0,he.symm.trans hRetainedOne.symm⟩
    · intro he
      exact hRetainedOneSafe (some j) (by simpa only [ne_eq,Option.some.injEq] using hj) ⟨1,he.symm.trans hRetainedOne.symm⟩
  have hQObserverZero : ∀ ρ, α.val.val 0 ∉ range (q ρ) := by
    intro ρ
    rintro ⟨t,ht⟩
    by_cases ht0 : t = 0
    · rw [ht0,hQZero] at ht
      exact hbetaSafe ρ (Or.inr (Or.inl ht))
    by_cases ht1 : t = 1
    · rw [ht1,hQOne] at ht
      exact hinv.2.2.1 v ⟨joint.clock 1,ht⟩
    have hf : ((q ρ) t).val ∈ frontier F := by
      rw [ht]
      exact hBF α.val.property.2.1
    exact hQProper ρ t ⟨bot_lt_iff_ne_bot.mpr ht0,lt_top_iff_ne_top.mpr ht1⟩ hf
  have hQObserverOne : ∀ ρ, α.val.val 1 ∉ range (q ρ) := by
    intro ρ
    rintro ⟨t,ht⟩
    by_cases ht0 : t = 0
    · rw [ht0,hQZero] at ht
      exact hbetaSafe ρ (Or.inr (Or.inr ht))
    by_cases ht1 : t = 1
    · rw [ht1,hQOne] at ht
      exact hinv.2.2.2.1 v ⟨joint.clock 1,ht⟩
    have hf : ((q ρ) t).val ∈ frontier F := by
      rw [ht]
      exact hBF α.val.property.2.2.1
    exact hQProper ρ t ⟨bot_lt_iff_ne_bot.mpr ht0,lt_top_iff_ne_top.mpr ht1⟩ hf
  have hChainGuidingKind (i : Fin (guideN+3)) (hi : i.val < cornerIndex.val) : kind i = 2 ∨ kind i = 3 := by
    let j : Fin (guideN+1) := ⟨i.val,hi⟩
    have he : i = j.castSucc.castSucc := Fin.ext rfl
    rw [he]
    simp only [kind,Fin.lastCases_castSucc]
    exact hRawKind (guideLabel j)
  have hChainFirstKind : kind 0 = 3 := by
    change kind (0 : Fin (guideN+1)).castSucc.castSucc = 3
    simp only [kind,Fin.lastCases_castSucc,hGuideFirstLabel]
    rfl
  have hChainLastKind (i : Fin (guideN+3)) (hi : i.val+1=cornerIndex.val) : kind i = 3 := by
    have hn : i.val = guideN := by have hh : i.val+1=guideN+1 := hi; omega
    have he : i = (Fin.last guideN).castSucc.castSucc := Fin.ext hn
    rw [he]
    simp only [kind,Fin.lastCases_castSucc,hGuideLastLabel]
    rfl
  have hCornerPiece (ρ : Ioo (0 : ℝ) bound) : fullPiece ρ cornerIndex = cap := by
    simp only [cornerIndex,fullPiece,Fin.lastCases_castSucc,Fin.lastCases_last]
  have hRetainedPiece (ρ : Ioo (0 : ℝ) bound) : fullPiece ρ (Fin.last (guideN+2)) = retained := by
    simp only [fullPiece,Fin.lastCases_last]
  have hFullChangedMissB (ρ : Ioo (0 : ℝ) bound) (i : Fin (guideN+3)) (hi : kind i ≠ 0) :
      Disjoint (range (fullPiece ρ i)) (range b) := by
    have hn : i.val ≠ guideN+2 := fun h => hi ((hRetainedKind i).mpr h)
    revert hi hn
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hi hn
      exact (hn rfl).elim
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro hi hn
        simpa only [fullPiece,Fin.lastCases_castSucc,Fin.lastCases_last] using hCapMissB
      · intro hi hn
        simpa only [fullPiece,Fin.lastCases_castSucc,guideRail] using hRawGuidesMissB ρ (guideLabel j)
  have hChainCornerWidthTransition (ρ : Ioo (0 : ℝ) bound) (i : GuidePiece)
      (hi : i.val.val+1=cornerIndex.val) (u : Icc (-1 : ℝ) 1)
      (hu : 0≤u.val) (hw : u.val≤(chainGuideCoordinates ρ i 1).2.val) :
      let y := correctedJoint.guideStrip ((chainGuideCoordinates ρ i 1).1,u)
      y.val ∈ joint.cornerFan.chart.source ∧ joint.cornerFan.chart y.val =
        Plane.mk (joint.cornerEntry 0-u.val/(chainGuideCoordinates ρ i 1).2.val*cornerEpsilon) (joint.cornerEntry 1) := by
    have hj := hChainLastGuide i hi
    have hcoord : chainGuideCoordinates ρ i = lastCoordinates ρ := by
      change rawGuideCoordinates ρ (guideLabel (guidePieceIndex i)) = lastCoordinates ρ
      rw [hj,hGuideLastLabel]
      rfl
    rw [hcoord] at hw ⊢
    obtain ⟨he,hf,h0,h1,hu0,hu1,ho,hwindow,hwidth,hformula,hclear⟩ := hLastData ρ
    rw [h1,hu1]
    have hface : correctedJoint.guideStrip (joint.guideClock orientedEntry,u) = entryFiber u :=
      hActualGuideEntryFace u
    rw [hface]
    have hwidthEnd : (lastCoordinates ρ 1).2 = capWidth := hu1
    have hu' : u.val≤cornerWidth := by
      have hcapBound : u.val≤capWidth.val := hwidthEnd ▸ hw
      exact hcapBound
    have hh := joint.guide_entry_section u hu (hu'.trans hcwentry.le)
    have hsection : (entryFiber u).val ∈ joint.cornerFan.chart.source ∧
      joint.cornerFan.chart (entryFiber u).val = Plane.mk
        (joint.cornerEntry 0-joint.kappa*u.val) (joint.cornerEntry 1) := hh
    have hratio : u.val/capWidth.val*cornerEpsilon = joint.kappa*u.val := by
      change u.val/cornerWidth*(joint.kappa*cornerWidth) = joint.kappa*u.val
      field_simp [ne_of_gt hcw]
    simpa only [hratio] using hsection
  exact ⟨{
    bound := bound
    bound_pos := hbound
    bound_lt_one := hboundOne
    clock := joint.clock
    clock_start := joint.clock_start
    cut := joint.cut
    corner_before_cut := joint.corner_before_cut
    cut_interior := joint.cut_interior
    active_prefix := joint.active_prefix
    padded_clear := joint.padded_clear
    retained_tail := joint.retained_tail
    oldStrip := joint.oldStrip
    oldStrip_embedded := joint.oldStrip_embedded
    oldStrip_center := joint.oldStrip_center
    oldStrip_ends := joint.oldStrip_ends
    oldStrip_interior := joint.oldStrip_interior
    oldStrip_open := joint.oldStrip_open
    activeWindow := joint.activeWindow
    activeWindow_open := joint.activeWindow_open
    activeWindow_prefix := joint.activeWindow_prefix
    oldStrip_full_active_fibers := joint.oldStrip_full_active_fibers
    guideStrip := correctedJoint.guideStrip
    guideStrip_embedded := correctedJoint.guideStrip_embedded
    guideStrip_center := correctedJoint.guideStrip_center
    guideStrip_ends := correctedJoint.guideStrip_ends
    guideStrip_interior := correctedJoint.guideStrip_interior
    guideStrip_open := correctedJoint.guideStrip_open
    guiding_exterior := by
      apply correctedJoint.guiding_exterior.mono_left
      rintro y ⟨z,hz,rfl⟩
      refine ⟨z,⟨hz.1,hz.2.1,?_⟩,rfl⟩
      exact hz.2.2.trans (by rw [hCorrectedBound]; exact hboundJoint)
    guideWindow := joint.guideWindow
    guideWindow_open := joint.guideWindow_open
    guideWindow_selected := joint.guideWindow_selected
    guide_full_window_fibers := by
      simpa only [hCorrectedGuideWindow] using correctedJoint.guide_full_window_fibers
    guideClock := joint.guideClock
    guideClock_start := joint.guideClock_start
    guideClock_increasing := joint.guideClock_increasing
    guideEntryTime := joint.guideEntryTime
    guideEntryTime_interior := joint.guideEntryTime_interior
    boundaryLine := boundaryLine
    boundaryLine_eq := by
      intro u
      simpa only [hCorrectedBoundaryLine] using correctedJoint.boundaryLine_eq u
    boundaryLine_embedded := hBoundaryLine
    boundaryLine_zero := hBoundaryZero
    boundaryLine_local := hboundaryLocal
    terminalCut := terminalCut
    terminalCut_lt := hterminalCutOne
    incoming_terminal := hIncomingTerminal
    incomingMarker := incomingMarker
    incomingMarker_in := ⟨hincomingMarkerLower,hincomingMarkerOne⟩
    outgoing_clear := houtgoingClear
    beta := beta
    beta_eq := hbetaEq
    beta_outside_old_boundary := hBetaOutside
    beta_safe := hbetaSafe
    boundaryExtension := boundaryExtension
    boundaryExtension_embedded := hBoundaryExtension
    boundaryExtension_zero := hBoundaryExtensionZero
    boundaryExtension_one := hBoundaryExtensionOne
    boundaryExtension_range := hBoundaryExtensionRange
    boundaryExtension_in_BV := hBoundaryExtensionBV
    boundaryExtension_seam := hBoundaryExtensionSeam
    n := guideN+2
    n_pos := by omega
    piece := fullPiece
    piece_embedded := hFullEmbed
    port := fullPort
    piece_zero := hFullZero
    piece_one := hFullOne
    adjacent_inter := hAdjacent
    nonadjacent_disjoint := hNonadjacent
    kind := kind
    retained_kind := hRetainedKind
    cornerIndex := cornerIndex
    corner_kind := hCornerKind
    corner_position := by simp only [cornerIndex,Fin.val_castSucc,Fin.val_last]
    guiding_piece_exists := by omega
    guiding_kind := hChainGuidingKind
    guiding_first_kind := hChainFirstKind
    guiding_last_kind := hChainLastKind
    guidePortTime := chainGuidePortTime
    guidePortTime_zero := hChainGuideTimeZero
    guidePortTime_order := hChainGuideTimeOrder
    guidePortTime_last := hChainGuideTimeLast
    guidePortTime_selected := hChainGuideTimeSelected
    guideCoordinates := chainGuideCoordinates
    guideCoordinates_factor := hChainGuideFactor
    guideCoordinates_zero := hChainGuideZero
    guideCoordinates_one := hChainGuideOne
    guideCoordinates_order := hChainGuideOrder
    guideCoordinates_window := hChainGuideWindow
    guideCoordinates_width := hChainGuideWidth
    guideCoordinates_first_width := hChainFirstWidth
    q := q
    q_embedded := hQEmbedded
    q_zero := hQZero
    q_one := hQOne
    q_proper := hQProper
    q_range := hqRange
    cuts := cuts
    cuts_strict := fun ρ => (hCuts ρ).1
    cuts_zero := fun ρ => (hCuts ρ).2.1
    cuts_one := fun ρ => (hCuts ρ).2.2.1
    piece_clock := hPieceClock
    retained_formula := by
      intro ρ t
      rw [hRetainedPiece]
      exact hRetainedFormula t
    changed_prefix_in_V := hChangedInV
    changed_prefix_meets_a := hChangedMeetsA
    changed_misses_b := hFullChangedMissB
    corner_removed := hQCornerRemoved
    safe_ports := hFullPortsSafe
    eventSite := chainEventSite
    eventSite_injective := hChainEventSiteInjective
    eventSite_old := fun i => (chainEventP i).property.1
    eventSite_incident := fun i => hPThird (chainEventP i)
    eventSite_in_fan := fun i => hPfan (chainEventP i).property
    eventFan := chainEventFan
    eventFan_nested := fun i => (hChainEventMetadata i).1
    event_axis := fun i => (hChainEventMetadata i).2.1
    event_third_ports_opposite := fun i => (hChainEventMetadata i).2.2
    eventLeft := chainEventLeft
    eventRight := chainEventRight
    event_horizontal := hChainEventHorizontal
    event_formula := hChainEventFormula
    event_exterior := hChainEventExterior
    event_subsingleton := by
      intro ρ i k hv hw
      rw [hChainEventPiece]
      exact hChosenEventContacts (chainEventP i) ρ k hv hw
    event_nonincident_clear := by
      intro ρ i k hk
      rw [hChainEventPiece]
      exact hChosenEventNonincident (chainEventP i) ρ k hk
    gapChart := chainGapChart
    gapLeft := chainGapLeft
    gapRight := chainGapRight
    gap_formula := hChainGapFormula
    gap_clear := fun ρ i k _ => hChainGapClear ρ i k
    gap_exterior := hChainGapExterior
    cornerFan := joint.cornerFan
    cornerFan_in_original := joint.cornerFan_in_original
    cornerDelta := joint.cornerDelta
    cornerDelta_pos := joint.cornerDelta_pos
    cornerEntry := joint.cornerEntry
    cornerEntry_nonzero_height := joint.cornerEntry_nonzero_height
    corner_entry_on_selected_side := ⟨joint.guideEntryTime,joint.guideEntryTime_interior,joint.cornerEntry_actual⟩
    corner_selected_ports_opposite := joint.corner_selected_ports_opposite
    cornerEpsilon := fun _ => cornerEpsilon
    cornerEpsilon_pos := fun _ => hce
    corner_formula := by
      intro ρ t
      rw [hCornerPiece]
      exact hCapFormula t
    corner_in_unit_window := by
      intro ρ
      rw [hCornerPiece]
      exact hCapUnit
    corner_meets_a := by
      intro ρ
      rw [hCornerPiece]
      exact hCapMeetA
    corner_subsingleton := by
      intro ρ k hv hw
      rw [hCornerPiece]
      exact hCapSubsingleton k hv hw
    corner_nonincident_clear := by
      intro ρ k hk
      rw [hCornerPiece]
      exact hCapNonincident k hk
    charge := charge
    charge_injective := fun ρ k hv hw => (hChargeData ρ k hv hw).1
    endpoint_safe := hQEndpointSafe
    observer_zero_excluded := hQObserverZero
    observer_one_excluded := hQObserverOne
    family_contacts_finite := by
      intro ρ j hj
      by_cases hw : j = w
      · subst j
        exact (hActualSelectedCounts ρ).1
      · exact (hChargeData ρ (some j) (by simpa using hj) (by simpa using hw)).2.1
    observer_contacts_finite := fun ρ => (hChargeData ρ none (by simp) (by simp)).2.1
    third_count := fun ρ j hv hw => (hChargeData ρ (some j) (by simpa using hv) (by simpa using hw)).2.2
    selected_contacts_subset := fun ρ => (hActualSelectedCounts ρ).2.1
    selected_count_drop := fun ρ => (hActualSelectedCounts ρ).2.2
    guide_entry_in_corner := joint.cornerEntry_actual.1
    guide_entry_eq := joint.cornerEntry_actual.2
    cornerHull_open_unit := fun _ => joint.corner_hull_in_unit cornerEpsilon hce hcecap
    corner_horizontal_progress := by
      intro ρ
      have hh := joint.corner_horizontal_progress cornerEpsilon hce hcecap
      linarith only [hh]
    corner_b_axis_segment := joint.corner_b_axis_segment
    corner_a_axis_segment := joint.corner_a_axis_segment
    guide_corner_width_transition := hChainCornerWidthTransition
    corner_disk_inter := fun _ => joint.corner_carrier_disk_inter cornerEpsilon hce hcecap
    guide_corner_inter := hChainGuideCornerInter
    oldCornerWindow := joint.oldCornerWindow
    oldCornerWindow_open := joint.oldCornerWindow_open
    oldCornerWindow_padded := joint.oldCornerWindow_padded
    oldCornerWindow_active := joint.oldCornerWindow_active
    oldCornerWidth := joint.oldCornerWidth
    oldCornerWidth_pos := joint.oldCornerWidth_pos
    oldCornerWidth_lt_one := joint.oldCornerWidth_lt_one
    oldCornerX := joint.oldCornerX
    oldCornerX_order := joint.oldCornerX_order
    oldCornerX_corner := joint.oldCornerX_corner
    oldCornerX_cut := joint.oldCornerX_cut
    oldCornerScale := joint.oldCornerScale
    oldCornerScale_pos := joint.oldCornerScale_pos
    oldCornerSign := joint.oldCornerSign
    oldCornerSign_unit := joint.oldCornerSign_unit
    oldCornerSign_matches := joint.oldCornerSign_matches
    old_corner_transition := joint.old_corner_transition
    old_corner_transition_unit := joint.old_corner_transition_unit
    oldNegativeWidth := joint.oldNegativeWidth
    oldNegativeWidth_pos := joint.oldNegativeWidth_pos
    oldNegativeWidth_lt_corner := joint.oldNegativeWidth_lt_corner
    old_negative_disk_inter := joint.old_negative_disk_inter
    old_negative_guide_clear := hChainGuideOldNegativeClear
    old_negative_corner_inter := fun _ => joint.old_negative_corner_carrier_inter cornerEpsilon hce hcecap
  }⟩
