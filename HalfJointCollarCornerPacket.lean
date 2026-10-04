import CorridorGeometryDefinitions
import RegionalHalfEndpointGapScaffold

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies RegionalChordNormalization
open scoped BigOperators
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Literal guide carrier, truncated at the actual interior entry before the corner. -/
def regionalHalfJointGuideCarrier
    {S : Type} [TopologicalSpace S] (F : Set S)
    (E : C(Interval × Icc (-1 : ℝ) 1,↥F))
    (bStart tEntry : Interval) (μ : ℝ) : Set ↥F :=
  E '' {z | z.1 ∈ Icc (min bStart tEntry) (max bStart tEntry) ∧
    0 ≤ z.2.val ∧ z.2.val ≤ μ}

/-- Joint producer-owned proper collars, a common nested fan, and six local
carrier equations.  The packet precedes the choice of any finite rails.
The original incoming gap is a parameter, not an outgoing endpoint. -/
structure RegionalHalfJointCollarCornerPacket
    {S ι : Type} [TopologicalSpace S] (F : Set S) (B T : Set ↥F)
    (r : ι → C(Interval,↥F)) (α : C(Interval,↥F)) (v w : ι)
    (d : PairedHalfBigonDisk F B T (r v) (r w)) (V : Set ↥F)
    (fan : FiniteFanCarrier F (augmented r α) {some v,some w}
      (range d.first ∪ range d.second) V (range d.disk) (forbiddenEndpoints r α v))
    (gap : BoundaryEndpointGap B V (forbiddenEndpoints r α v) d.boundarySide) where
  bound : ℝ
  bound_pos : 0 < bound
  bound_lt_one : bound < 1
  clock : Interval ≃ₜ Interval
  clock_start : clock 0 = d.aStart
  cut : Interval
  corner_before_cut : clock.symm d.aFinish < cut
  cut_interior : cut ∈ Ioo (0 : Interval) 1
  active_prefix : r v '' (clock '' Icc (0 : Interval) cut) ⊆ V
  padded_clear : Disjoint (r v '' (clock '' Ioc (clock.symm d.aFinish) cut))
    (⋃ k : {k : Option ι // k ≠ some v}, range (augmented r α k.val))
  retained_tail : r v '' (clock '' Icc cut (1 : Interval)) ⊆ range (r v) \ range d.first
  oldStrip : C(Interval × Icc (-1 : ℝ) 1,↥F)
  oldStrip_embedded : IsEmbedding oldStrip
  oldStrip_center : ∀ t, oldStrip (t,⟨0,by norm_num⟩) = r v t
  oldStrip_ends : ∀ u, oldStrip (0,u) ∈ B ∧ oldStrip (1,u) ∈ B
  oldStrip_interior : ∀ t ∈ Ioo (0 : Interval) 1, ∀ u, (oldStrip (t,u)).val ∈ interior F
  oldStrip_open : IsOpen (oldStrip '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1})
  activeWindow : Set Interval
  activeWindow_open : IsOpen activeWindow
  activeWindow_prefix : clock '' Icc (0 : Interval) cut ⊆ activeWindow
  oldStrip_full_active_fibers : ∀ t ∈ activeWindow, ∀ u, oldStrip (t,u) ∈ V
  -- Orient this actual b collar once: incoming boundary is negative, guide positive.
  guideStrip : C(Interval × Icc (-1 : ℝ) 1,↥F)
  guideStrip_embedded : IsEmbedding guideStrip
  guideStrip_center : ∀ t, guideStrip (t,⟨0,by norm_num⟩) = r w t
  guideStrip_ends : ∀ u, guideStrip (0,u) ∈ B ∧ guideStrip (1,u) ∈ B
  guideStrip_interior : ∀ t ∈ Ioo (0 : Interval) 1, ∀ u, (guideStrip (t,u)).val ∈ interior F
  guideStrip_open : IsOpen (guideStrip '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1})
  guiding_exterior : Disjoint
    (guideStrip '' {z | z.1 ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) ∧
      0 < z.2.val ∧ z.2.val < bound}) (range d.disk)
  -- This one corridor is narrowed in V before the adjustable rails and q are chosen.
  guideWindow : Set Interval
  guideWindow_open : IsOpen guideWindow
  guideWindow_selected : Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) ⊆ guideWindow
  guide_full_window_fibers : ∀ t ∈ guideWindow, ∀ u, guideStrip (t,u) ∈ V
  guideClock : Interval ≃ₜ Interval
  guideClock_start : guideClock 0 = d.bStart
  guideClock_increasing : StrictMono guideClock ∨ StrictAnti guideClock
  guideClock_identity_or_reverse : guideClock = Homeomorph.refl Interval ∨
    guideClock = unitInterval.symmHomeomorph
  guideEntryTime : Interval
  guideEntryTime_interior : guideEntryTime ∈ Ioo (0 : Interval) 1
  boundaryLine : C(Icc (-1 : ℝ) 1,↥F)
  boundaryLine_eq : ∀ u, boundaryLine u = guideStrip (d.bStart,u)
  boundaryLine_embedded : IsEmbedding boundaryLine
  boundaryLine_zero : boundaryLine ⟨0,by norm_num⟩ = d.second 0
  boundaryLine_local : boundaryLine '' {u | |u.val| < bound} ⊆ B ∩ V
  terminalCut : Interval
  terminalCut_lt : terminalCut < 1
  incoming_terminal : d.boundarySide '' Ioo terminalCut (1 : Interval) ⊆
    boundaryLine '' {u | -bound < u.val ∧ u.val < 0}
  positive_boundary_branch_outside : Disjoint
    (boundaryLine '' {u | 0 < u.val ∧ u.val < bound}) (range d.boundarySide)
  corner_event : d.first 1 ∈ fan.events
  cornerFan : IncidentFanWindow F (augmented r α) V (d.first 1)
  cornerFan_in_original : ∀ h : d.first 1 ∈ fan.events,
    chartPull F cornerFan.chart (Metric.closedBall (0 : Plane) 1) ⊆
      chartPull F (fan.window ⟨d.first 1,h⟩).chart (Metric.ball (0 : Plane) 1)
  corner_a_axis : ∀ h : d.first 1 ∈ range (r v),
    incidentPorts (augmented r α) (d.first 1) cornerFan.chart
      cornerFan.left cornerFan.right (⟨some v,h⟩,false) 1 = 0 ∧
    incidentPorts (augmented r α) (d.first 1) cornerFan.chart
      cornerFan.left cornerFan.right (⟨some v,h⟩,true) 1 = 0
  corner_other_ports_opposite : ∀ j : incidentIndex (augmented r α) (d.first 1),
    j.val ≠ some v →
    (incidentPorts (augmented r α) (d.first 1) cornerFan.chart
      cornerFan.left cornerFan.right (j,false) 1) *
    (incidentPorts (augmented r α) (d.first 1) cornerFan.chart
      cornerFan.left cornerFan.right (j,true) 1) < 0
  cornerDelta : ℝ
  cornerDelta_pos : 0 < cornerDelta
  cornerEntry : Plane
  cornerEntry_nonzero_height : cornerEntry 1 ≠ 0
  corner_selected_ports_opposite : ∀ h : d.first 1 ∈ range (r w),
    (incidentPorts (augmented r α) (d.first 1) cornerFan.chart cornerFan.left cornerFan.right
      (⟨some w,h⟩,false) 1) *
    (incidentPorts (augmented r α) (d.first 1) cornerFan.chart cornerFan.left cornerFan.right
      (⟨some w,h⟩,true) 1) < 0
  cornerEntry_actual : (d.second guideEntryTime).val ∈ cornerFan.chart.source ∧
    cornerFan.chart (d.second guideEntryTime).val = cornerEntry
  corner_b_axis_segment : chartPull F cornerFan.chart (segment ℝ (0 : Plane) cornerEntry) =
    d.second '' Icc guideEntryTime (1 : Interval)
  corner_a_axis_segment : chartPull F cornerFan.chart (segment ℝ (0 : Plane) (Plane.mk (-cornerDelta) 0)) =
    r v '' (clock '' Icc (clock.symm d.aFinish) cut)
  entryMargin : ℝ
  entryMargin_pos : 0 < entryMargin
  entryMargin_lt_bound : entryMargin < bound
  kappa : ℝ
  kappa_pos : 0 < kappa
  guide_entry_section : ∀ u : Icc (-1 : ℝ) 1,
    0 ≤ u.val → u.val ≤ entryMargin →
    let y := guideStrip
      (CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish guideEntryTime,u)
    y.val ∈ cornerFan.chart.source ∧
      cornerFan.chart y.val = Plane.mk (cornerEntry 0 - kappa*u.val) (cornerEntry 1)
  capBound : ℝ
  capBound_pos : 0 < capBound
  capBound_lt_scale_margin : capBound < kappa * entryMargin
  corner_horizontal_progress : ∀ ε : ℝ, 0 < ε → ε < capBound →
    0 < cornerEntry 0 - ε + cornerDelta
  corner_hull_in_unit : ∀ ε : ℝ, 0 < ε → ε < capBound →
    regionalHalfCornerHull cornerDelta cornerEntry ε ⊆ Metric.ball (0 : Plane) 1
  oldCornerWindow : Set Interval
  oldCornerWindow_open : IsOpen oldCornerWindow
  oldCornerWindow_padded : Icc (clock.symm d.aFinish) cut ⊆ oldCornerWindow
  oldCornerWindow_active : oldCornerWindow ⊆ clock ⁻¹' activeWindow
  oldCornerWidth : ℝ
  oldCornerWidth_pos : 0 < oldCornerWidth
  oldCornerWidth_lt_one : oldCornerWidth < 1
  oldCornerX : C(Interval,ℝ)
  oldCornerX_order : StrictAntiOn oldCornerX oldCornerWindow
  oldCornerX_corner : oldCornerX (clock.symm d.aFinish) = 0
  oldCornerX_cut : oldCornerX cut = -cornerDelta
  oldCornerScale : ℝ
  oldCornerScale_pos : 0 < oldCornerScale
  oldCornerSign : ℝ
  oldCornerSign_unit : oldCornerSign = -1 ∨ oldCornerSign = 1
  oldCornerSign_matches : 0 < oldCornerSign * cornerEntry 1
  old_corner_transition : ∀ t ∈ oldCornerWindow, ∀ u : Icc (-1 : ℝ) 1,
    |u.val| ≤ oldCornerWidth →
    let y := oldStrip (clock t,u)
    y.val ∈ cornerFan.chart.source ∧
      cornerFan.chart y.val = Plane.mk (oldCornerX t) (oldCornerSign*oldCornerScale*u.val)
  old_corner_transition_unit : ∀ t ∈ oldCornerWindow, ∀ u : Icc (-1 : ℝ) 1,
    |u.val| ≤ oldCornerWidth →
    oldStrip (clock t,u) ∈ chartPull F cornerFan.chart (Metric.ball (0 : Plane) 1)
  oldNegativeWidth : ℝ
  oldNegativeWidth_pos : 0 < oldNegativeWidth
  oldNegativeWidth_lt_corner : oldNegativeWidth < oldCornerWidth
  guide_carrier_disk_inter :
    regionalHalfJointGuideCarrier F guideStrip d.bStart
      (CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish guideEntryTime) entryMargin ∩ range d.disk = d.second '' Icc (0 : Interval) guideEntryTime
  corner_carrier_disk_inter : ∀ ε : ℝ, 0 < ε → ε < capBound →
    chartPull F cornerFan.chart (regionalHalfCornerHull cornerDelta cornerEntry ε) ∩ range d.disk = d.second '' Icc guideEntryTime (1 : Interval)
  old_negative_disk_inter :
    regionalHalfOldNegativeBand F oldStrip clock cut oldNegativeWidth ∩ range d.disk = range d.first
  guide_corner_carrier_inter : ∀ ε : ℝ, 0 < ε → ε < capBound →
    regionalHalfJointGuideCarrier F guideStrip d.bStart
      (CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish guideEntryTime) entryMargin ∩
      chartPull F cornerFan.chart (regionalHalfCornerHull cornerDelta cornerEntry ε) =
    guideStrip '' {z | z.1 =
      CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish guideEntryTime ∧
      0 ≤ z.2.val ∧ z.2.val ≤ ε / kappa}
  old_negative_guide_carrier_disjoint : Disjoint
    (regionalHalfOldNegativeBand F oldStrip clock cut oldNegativeWidth)
    (regionalHalfJointGuideCarrier F guideStrip d.bStart
      (CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish guideEntryTime) entryMargin)
  old_negative_corner_carrier_inter : ∀ ε : ℝ, 0 < ε → ε < capBound →
    regionalHalfOldNegativeBand F oldStrip clock cut oldNegativeWidth ∩
      chartPull F cornerFan.chart (regionalHalfCornerHull cornerDelta cornerEntry ε) =
    r v '' (clock '' Icc (clock.symm d.aFinish) cut)
