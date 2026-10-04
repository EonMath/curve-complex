import CorridorGeometryDefinitions
import RegionalHalfEndpointGapScaffold

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies RegionalChordNormalization
open scoped BigOperators
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Actual finite signed geometry tied to the given half disk and its paid fan/gap.
Tags are 0 retained, 1 corner, 2 old guiding event, 3 clear gap. No movie,
homotopy, swept disk, profile or square is part of this record. -/
structure RegionalHalfSignedGuidingChain
    {S ι : Type} [TopologicalSpace S] (F : Set S) (B T : Set ↥F)
    (r : ι → C(Interval,↥F)) (α : C(Interval,↥F)) (v w : ι)
    (d : PairedHalfBigonDisk F B T (r v) (r w)) (V : Set ↥F)
    (fan : FiniteFanCarrier F (augmented r α) {some v,some w}
      (range d.first ∪ range d.second) V (range d.disk) (forbiddenEndpoints r α v))
    (gap : BoundaryEndpointGap B V (forbiddenEndpoints r α v) d.boundarySide) where
  -- One common small-parameter interval; every geometric/count field is uniform.
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
  incomingMarker : Interval
  incomingMarker_in : incomingMarker ∈ Ioo (max gap.cut terminalCut) (1 : Interval)
  outgoing_clear : ∀ k : Option ι, k ≠ some w →
    Disjoint (boundaryLine '' {u | |u.val| < bound}) (range (augmented r α k))
  beta : Ioo (0 : ℝ) bound → ↥F
  beta_eq : ∀ ρ, ∃ u : Icc (-1 : ℝ) 1, u.val = ρ.val ∧ beta ρ = boundaryLine u
  beta_outside_old_boundary : ∀ ρ, beta ρ ∉ range d.boundarySide
  beta_safe : ∀ ρ, beta ρ ∉ forbiddenEndpoints r α v
  boundaryExtension : Ioo (0 : ℝ) bound → C(Interval,↥F)
  boundaryExtension_embedded : ∀ ρ, IsEmbedding (boundaryExtension ρ)
  boundaryExtension_zero : ∀ ρ, boundaryExtension ρ 0 = d.first 0
  boundaryExtension_one : ∀ ρ, boundaryExtension ρ 1 = beta ρ
  boundaryExtension_range : ∀ ρ, range (boundaryExtension ρ) =
    range d.boundarySide ∪ boundaryLine '' {u | 0 ≤ u.val ∧ u.val ≤ ρ.val}
  boundaryExtension_in_BV : ∀ ρ, range (boundaryExtension ρ) ⊆ B ∩ V
  boundaryExtension_seam : ∀ (ρ : Ioo (0 : ℝ) bound), range d.boundarySide ∩
    boundaryLine '' {u | 0 ≤ u.val ∧ u.val ≤ ρ.val} = {d.second 0}
  n : ℕ
  n_pos : 0 < n
  piece : Ioo (0 : ℝ) bound → Fin (n+1) → C(Interval,↥F)
  piece_embedded : ∀ ρ i, IsEmbedding (piece ρ i)
  port : Ioo (0 : ℝ) bound → Fin (n+2) → ↥F
  piece_zero : ∀ ρ i, piece ρ i 0 = port ρ i.castSucc
  piece_one : ∀ ρ i, piece ρ i 1 = port ρ i.succ
  adjacent_inter : ∀ ρ (i j : Fin (n+1)), i.val + 1 = j.val →
    range (piece ρ i) ∩ range (piece ρ j) = {port ρ i.succ}
  nonadjacent_disjoint : ∀ ρ (i j : Fin (n+1)), i.val + 1 < j.val →
    Disjoint (range (piece ρ i)) (range (piece ρ j))
  kind : Fin (n+1) → Fin 4
  retained_kind : ∀ i, kind i = 0 ↔ i.val = n
  cornerIndex : Fin (n+1)
  corner_kind : ∀ i, kind i = 1 ↔ i = cornerIndex
  corner_position : cornerIndex.val + 1 = n
  -- Finite rails have literal coordinates in that same prechosen filled corridor.
  guiding_piece_exists : 1 < n
  guiding_kind : ∀ i : Fin (n+1), i.val < cornerIndex.val → kind i = 2 ∨ kind i = 3
  guiding_first_kind : kind 0 = 3
  guiding_last_kind : ∀ i : Fin (n+1), i.val + 1 = cornerIndex.val → kind i = 3
  guidePortTime : Fin (n+2) → Interval
  guidePortTime_zero : guidePortTime 0 = 0
  guidePortTime_order : ∀ i j, i.val < j.val → j.val ≤ cornerIndex.val →
    guidePortTime i < guidePortTime j
  guidePortTime_last : guideClock (guidePortTime cornerIndex.castSucc) =
    CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish guideEntryTime
  guidePortTime_selected : ∀ i, i.val ≤ cornerIndex.val →
    guideClock (guidePortTime i) ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish)
  guideCoordinates : Ioo (0 : ℝ) bound →
    {i : Fin (n+1) // i.val < cornerIndex.val} → C(Interval,Interval × Icc (-1 : ℝ) 1)
  guideCoordinates_factor : ∀ ρ i t, piece ρ i.val t = guideStrip (guideCoordinates ρ i t)
  guideCoordinates_zero : ∀ ρ i, (guideCoordinates ρ i 0).1 =
    guideClock (guidePortTime i.val.castSucc)
  guideCoordinates_one : ∀ ρ i, (guideCoordinates ρ i 1).1 =
    guideClock (guidePortTime i.val.succ)
  guideCoordinates_order : ∀ ρ i,
    StrictMono (fun t => guideClock.symm (guideCoordinates ρ i t).1)
  guideCoordinates_window : ∀ ρ i t, (guideCoordinates ρ i t).1 ∈ guideWindow
  guideCoordinates_width : ∀ ρ i t,
    0 < (guideCoordinates ρ i t).2.val ∧ (guideCoordinates ρ i t).2.val < bound
  guideCoordinates_first_width : ∀ ρ (i : {i : Fin (n+1) // i.val < cornerIndex.val}),
    i.val.val = 0 → (guideCoordinates ρ i 0).2.val = ρ.val
  q : Ioo (0 : ℝ) bound → C(Interval,↥F)
  q_embedded : ∀ ρ, IsEmbedding (q ρ)
  q_zero : ∀ ρ, q ρ 0 = beta ρ
  q_one : ∀ ρ, q ρ 1 = r v (clock 1)
  q_proper : ∀ ρ t, t ∈ Ioo (0 : Interval) 1 → q ρ t ∉ T
  q_range : ∀ ρ, range (q ρ) = ⋃ i, range (piece ρ i)
  cuts : Ioo (0 : ℝ) bound → Fin (n+2) → Interval
  cuts_strict : ∀ ρ, StrictMono (cuts ρ)
  cuts_zero : ∀ ρ, cuts ρ 0 = 0
  cuts_one : ∀ ρ, cuts ρ (Fin.last (n+1)) = 1
  piece_clock : ∀ ρ i t, piece ρ i t = q ρ
    (CurveComplex.BranchedDoubleCover.intervalAffine (cuts ρ i.castSucc) (cuts ρ i.succ) t)
  retained_formula : ∀ ρ t, piece ρ (Fin.last n) t = r v
    (clock (CurveComplex.BranchedDoubleCover.intervalAffine cut 1 t))
  changed_prefix_in_V : ∀ ρ,
    q ρ '' Icc (0 : Interval) (cuts ρ ⟨n,by omega⟩) ⊆ V
  changed_prefix_meets_a : ∀ ρ,
    (q ρ '' Icc (0 : Interval) (cuts ρ ⟨n,by omega⟩)) ∩ range (r v) = {r v (clock cut)}
  changed_misses_b : ∀ ρ i, kind i ≠ 0 → Disjoint (range (piece ρ i)) (range (r w))
  corner_removed : ∀ ρ, d.first 1 ∉ range (q ρ)
  safe_ports : ∀ ρ i k, k ≠ some v → k ≠ some w →
    port ρ i ∉ range (augmented r α k)
  -- Distinct old geometric sites, including simultaneous multiple incidences.
  eventSite : {i : Fin (n+1) // kind i = 2} → ↥F
  eventSite_injective : Function.Injective eventSite
  eventSite_old : ∀ i, eventSite i ∈ range d.second \ {d.first 1}
  eventSite_incident : ∀ i, ∃ k : Option ι, k ≠ some v ∧ k ≠ some w ∧
    eventSite i ∈ range (augmented r α k)
  eventSite_in_fan : ∀ i, eventSite i ∈ fan.events
  eventFan : ∀ i : {i : Fin (n+1) // kind i = 2}, IncidentFanWindow F (augmented r α) V (eventSite i)
  eventFan_nested : ∀ i, chartPull F (eventFan i).chart (Metric.closedBall (0 : Plane) 1) ⊆
    chartPull F (fan.window ⟨eventSite i,eventSite_in_fan i⟩).chart (Metric.ball (0 : Plane) 1)
  event_axis : ∀ i (h : eventSite i ∈ range (r w)),
    incidentPorts (augmented r α) (eventSite i) (eventFan i).chart
      (eventFan i).left (eventFan i).right (⟨some w,h⟩,false) 1 = 0 ∧
    incidentPorts (augmented r α) (eventSite i) (eventFan i).chart
      (eventFan i).left (eventFan i).right (⟨some w,h⟩,true) 1 = 0
  event_third_ports_opposite : ∀ i (j : incidentIndex (augmented r α) (eventSite i)),
    j.val ≠ some w →
    (incidentPorts (augmented r α) (eventSite i) (eventFan i).chart
      (eventFan i).left (eventFan i).right (j,false) 1) *
    (incidentPorts (augmented r α) (eventSite i) (eventFan i).chart
      (eventFan i).left (eventFan i).right (j,true) 1) < 0
  eventLeft : Ioo (0 : ℝ) bound → {i : Fin (n+1) // kind i = 2} → Plane
  eventRight : Ioo (0 : ℝ) bound → {i : Fin (n+1) // kind i = 2} → Plane
  event_horizontal : ∀ ρ i, eventLeft ρ i 1 = eventRight ρ i 1 ∧ eventLeft ρ i 1 ≠ 0 ∧
    eventLeft ρ i 0 ≠ eventRight ρ i 0
  event_formula : ∀ ρ i t,
    let z := (1-t.val) • eventLeft ρ i + t.val • eventRight ρ i
    z ∈ (eventFan i).chart.target ∧
      (piece ρ i.val t).val = (eventFan i).chart.symm z
  event_exterior : ∀ ρ (i : {i : Fin (n+1) // kind i = 2}), range (piece ρ i.val) ⊆
    guideStrip '' {z | 0 < z.2.val ∧ z.2.val < bound}
  event_subsingleton : ∀ ρ (i : {i : Fin (n+1) // kind i = 2}) k, k ≠ some v → k ≠ some w →
    (range (piece ρ i.val) ∩ range (augmented r α k)).Subsingleton
  event_nonincident_clear : ∀ ρ i k, eventSite i ∉ range (augmented r α k) →
    Disjoint (range (piece ρ i.val)) (range (augmented r α k))
  gapChart : {i : Fin (n+1) // kind i = 3} → OpenPartialHomeomorph S Plane
  gapLeft : Ioo (0 : ℝ) bound → {i : Fin (n+1) // kind i = 3} → Plane
  gapRight : Ioo (0 : ℝ) bound → {i : Fin (n+1) // kind i = 3} → Plane
  gap_formula : ∀ ρ i t,
    let z := (1-t.val) • gapLeft ρ i + t.val • gapRight ρ i
    z ∈ (gapChart i).target ∧ (piece ρ i.val t).val = (gapChart i).symm z
  gap_clear : ∀ ρ (i : {i : Fin (n+1) // kind i = 3}) k, k ≠ some v → Disjoint (range (piece ρ i.val)) (range (augmented r α k))
  gap_exterior : ∀ ρ (i : {i : Fin (n+1) // kind i = 3}), range (piece ρ i.val) ⊆
    guideStrip '' {z | 0 < z.2.val ∧ z.2.val < bound}
  cornerFan : IncidentFanWindow F (augmented r α) V (d.first 1)
  cornerFan_in_original : ∀ h : d.first 1 ∈ fan.events,
    chartPull F cornerFan.chart (Metric.closedBall (0 : Plane) 1) ⊆
      chartPull F (fan.window ⟨d.first 1,h⟩).chart (Metric.ball (0 : Plane) 1)
  cornerDelta : ℝ
  cornerDelta_pos : 0 < cornerDelta
  cornerEntry : Plane
  cornerEntry_nonzero_height : cornerEntry 1 ≠ 0
  corner_entry_on_selected_side : ∃ t ∈ Ioo (0 : Interval) 1,
    (d.second t).val ∈ cornerFan.chart.source ∧ cornerFan.chart (d.second t).val = cornerEntry
  corner_selected_ports_opposite : ∀ h : d.first 1 ∈ range (r w),
    (incidentPorts (augmented r α) (d.first 1) cornerFan.chart cornerFan.left cornerFan.right
      (⟨some w,h⟩,false) 1) *
    (incidentPorts (augmented r α) (d.first 1) cornerFan.chart cornerFan.left cornerFan.right
      (⟨some w,h⟩,true) 1) < 0
  cornerEpsilon : Ioo (0 : ℝ) bound → ℝ
  cornerEpsilon_pos : ∀ ρ, 0 < cornerEpsilon ρ
  corner_formula : ∀ ρ t,
    let z := Plane.mk (-cornerDelta + (1-t.val)*(cornerEntry 0-cornerEpsilon ρ+cornerDelta))
      (cornerEntry 1*(1-t.val))
    z ∈ cornerFan.chart.target ∧ (piece ρ cornerIndex t).val = cornerFan.chart.symm z
  /-- The actual cap remains inside the chosen fan carrier for every common
  small parameter; this is produced with the cap, not assumed of the movie. -/
  corner_in_unit_window : ∀ ρ, range (piece ρ cornerIndex) ⊆
    chartPull F cornerFan.chart (Metric.closedBall (0 : Plane) 1)
  corner_meets_a : ∀ ρ, range (piece ρ cornerIndex) ∩ range (r v) = {r v (clock cut)}
  corner_subsingleton : ∀ ρ k, k ≠ some v → k ≠ some w →
    (range (piece ρ cornerIndex) ∩ range (augmented r α k)).Subsingleton
  corner_nonincident_clear : ∀ ρ k, d.first 1 ∉ range (augmented r α k) →
    Disjoint (range (piece ρ cornerIndex)) (range (augmented r α k))
  -- Full unchanged comparison traces, including observer none; actual injections.
  charge : ∀ ρ k, k ≠ some v → k ≠ some w →
    ↥(range (q ρ) ∩ range (augmented r α k)) →
      (↥((range d.second \ {d.first 1}) ∩ range (augmented r α k)) ⊕
       ↥((range (r v) \ range d.first) ∩ range (augmented r α k))) ⊕
      ↥({d.first 1} ∩ range (augmented r α k))
  charge_injective : ∀ ρ k (hv : k ≠ some v) (hw : k ≠ some w),
    Function.Injective (charge ρ k hv hw)
  endpoint_safe : ∀ ρ j, j ≠ v →
    q ρ 0 ≠ r j 0 ∧ q ρ 0 ≠ r j 1 ∧ q ρ 1 ≠ r j 0 ∧ q ρ 1 ≠ r j 1
  observer_zero_excluded : ∀ ρ, α 0 ∉ range (q ρ)
  observer_one_excluded : ∀ ρ, α 1 ∉ range (q ρ)
  family_contacts_finite : ∀ ρ j, j ≠ v → (range (q ρ) ∩ range (r j)).Finite
  observer_contacts_finite : ∀ ρ, (range (q ρ) ∩ range α).Finite
  third_count : ∀ ρ j, j ≠ v → j ≠ w →
    (range (q ρ) ∩ range (r j)).ncard ≤
      ((range d.second \ {d.first 1}) ∩ range (r j)).ncard +
      (((range (r v) \ range d.first) ∩ range (r j)).ncard +
        ({d.first 1} ∩ range (r j)).ncard)
  selected_contacts_subset : ∀ ρ,
    range (q ρ) ∩ range (r w) ⊆ (range (r v) ∩ range (r w)) \ {d.first 1}
  selected_count_drop : ∀ ρ,
    (range (q ρ) ∩ range (r w)).ncard + 1 ≤ (range (r v) ∩ range (r w)).ncard
  -- Exact corner/corridor attachment; these are local coordinate carriers, not a swept disk.
  guide_entry_in_corner : (d.second guideEntryTime).val ∈ cornerFan.chart.source
  guide_entry_eq : cornerFan.chart (d.second guideEntryTime).val = cornerEntry
  cornerHull_open_unit : ∀ ρ,
    regionalHalfCornerHull cornerDelta cornerEntry (cornerEpsilon ρ) ⊆ Metric.ball (0 : Plane) 1
  corner_horizontal_progress : ∀ ρ, -cornerDelta < cornerEntry 0-cornerEpsilon ρ
  corner_b_axis_segment : chartPull F cornerFan.chart (segment ℝ (0 : Plane) cornerEntry) =
    d.second '' Icc guideEntryTime (1 : Interval)
  corner_a_axis_segment : chartPull F cornerFan.chart (segment ℝ (0 : Plane) (Plane.mk (-cornerDelta) 0)) =
    r v '' (clock '' Icc (clock.symm d.aFinish) cut)
  guide_corner_width_transition : ∀ ρ (i : {i : Fin (n+1) // i.val < cornerIndex.val}),
    i.val.val + 1 = cornerIndex.val → ∀ u : Icc (-1 : ℝ) 1,
    0 ≤ u.val → u.val ≤ (guideCoordinates ρ i 1).2.val →
    let y := guideStrip ((guideCoordinates ρ i 1).1,u)
    y.val ∈ cornerFan.chart.source ∧
      cornerFan.chart y.val = Plane.mk
        (cornerEntry 0-u.val/(guideCoordinates ρ i 1).2.val*cornerEpsilon ρ) (cornerEntry 1)
  corner_disk_inter : ∀ ρ,
    chartPull F cornerFan.chart (regionalHalfCornerHull cornerDelta cornerEntry (cornerEpsilon ρ)) ∩
      range d.disk = d.second '' Icc guideEntryTime (1 : Interval)
  guide_corner_inter : ∀ ρ (i : {i : Fin (n+1) // i.val < cornerIndex.val}),
    regionalHalfGuideSlab F guideStrip (guideCoordinates ρ i) ∩
      chartPull F cornerFan.chart (regionalHalfCornerHull cornerDelta cornerEntry (cornerEpsilon ρ)) =
    if i.val.val + 1 = cornerIndex.val then
      guideStrip '' {z | z.1 = (guideCoordinates ρ i 1).1 ∧
        0 ≤ z.2.val ∧ z.2.val ≤ (guideCoordinates ρ i 1).2.val}
    else ∅
  -- A common old-strip/chart transition gives local tapering and the retained seam margin.
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
  old_negative_disk_inter :
    regionalHalfOldNegativeBand F oldStrip clock cut oldNegativeWidth ∩ range d.disk = range d.first
  old_negative_guide_clear : ∀ ρ i,
    Disjoint (regionalHalfOldNegativeBand F oldStrip clock cut oldNegativeWidth)
      (regionalHalfGuideSlab F guideStrip (guideCoordinates ρ i))
  old_negative_corner_inter : ∀ ρ,
    regionalHalfOldNegativeBand F oldStrip clock cut oldNegativeWidth ∩
      chartPull F cornerFan.chart (regionalHalfCornerHull cornerDelta cornerEntry (cornerEpsilon ρ)) =
    r v '' (clock '' Icc (clock.symm d.aFinish) cut)
