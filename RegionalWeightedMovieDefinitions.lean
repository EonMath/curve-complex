import RegionalDecreaseSupport
import RegionalChordDefinitions

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalChordNormalization
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

namespace RegionalWeightedMovies

/-- Geometric contact sites in V, rather than a finite enumeration of continuous traces. -/
def contactSites {S κ : Type} [TopologicalSpace S] (F : Set S)
    (a : κ → C(Interval,↥F)) (selected : Set κ) (sides V : Set ↥F) : Set ↥F :=
  {p | p ∈ V ∧ p ∈ sides ∧
    ∃ i ∈ selected, ∃ j, i ≠ j ∧ p ∈ range (a i) ∩ range (a j)}

/-- All other family endpoints and BOTH observer endpoints. -/
def forbiddenEndpoints {X ι : Type} [TopologicalSpace X]
    (r : ι → C(Interval,X)) (α : C(Interval,X)) (v : ι) : Set X :=
  {p | (∃ j, j ≠ v ∧ (p = r j 0 ∨ p = r j 1)) ∨ p = α 0 ∨ p = α 1}

def incidentIndex {X κ : Type} [TopologicalSpace X]
    (a : κ → C(Interval,X)) (p : X) := {i : κ // p ∈ range (a i)}

def incidentPorts {S κ : Type} [TopologicalSpace S] {F : Set S}
    (a : κ → C(Interval,↥F)) (p : ↥F)
    (e : OpenPartialHomeomorph S Plane)
    (l r : incidentIndex a p → Interval) : incidentIndex a p × Bool → Plane :=
  fun z => e ((a z.1.val) (if z.2 then r z.1 else l z.1)).val

/-- One finite-star window at an actual old contact. All incident whole traces
and all nonincident compact traces remain explicit. -/
structure IncidentFanWindow {S κ : Type} [TopologicalSpace S]
    (F : Set S) (a : κ → C(Interval,↥F)) (V : Set ↥F) (p : ↥F) where
  chart : OpenPartialHomeomorph S Plane
  source_closure : closure chart.source ⊆ Subtype.val '' V ∩ interior F
  contact_in_source : p.val ∈ chart.source
  contact_zero : chart p.val = 0
  disk_in_target : Metric.closedBall (0 : Plane) 1 ⊆ chart.target
  left : incidentIndex a p → Interval
  right : incidentIndex a p → Interval
  center : incidentIndex a p → Interval
  cuts : ∀ i, 0 < left i ∧ left i < center i ∧ center i < right i ∧ right i < 1
  at_center : ∀ i, a i.val (center i) = p
  whole_closed : ∀ i,
    chartPull F chart (Metric.closedBall (0 : Plane) 1) ∩ range (a i.val) =
      a i.val '' Icc (left i) (right i)
  whole_open : ∀ i,
    chartPull F chart (Metric.ball (0 : Plane) 1) ∩ range (a i.val) =
      a i.val '' Ioo (left i) (right i)
  radial_trace : ∀ i, (fun t => chart ((a i.val) t).val) '' Icc (left i) (right i) =
    segment ℝ (incidentPorts a p chart left right (i,false)) 0 ∪
      segment ℝ 0 (incidentPorts a p chart left right (i,true))
  nonincident_clear : ∀ i, p ∉ range (a i) →
    Disjoint (chartPull F chart (Metric.closedBall (0 : Plane) 1)) (range (a i))
  ports_on_sphere : ∀ z, incidentPorts a p chart left right z ∈ Metric.sphere (0 : Plane) 1
  ports_injective : Function.Injective (incidentPorts a p chart left right)

/-- Events are finite contacts. Continuous pieces, not events, cover the full
traces inside the closed disk carrier K. The observer is an ordinary index
of a, and sign witnesses are literal existing regional crossing charts. -/
structure FiniteFanCarrier {S κ : Type} [TopologicalSpace S]
    (F : Set S) (a : κ → C(Interval,↥F)) (selected : Set κ)
    (sides V K forbidden : Set ↥F) where
  events : Set ↥F
  events_finite : events.Finite
  events_exact : events = contactSites F a selected sides V
  pieces : κ → Finset (Interval × Interval)
  piece_order : ∀ i, ∀ lr ∈ pieces i, lr.1 ≤ lr.2
  whole_trace_pieces : ∀ i,
    K ∩ range (a i) = ⋃ lr ∈ pieces i, a i '' Icc lr.1 lr.2
  carrier_in_V : K ⊆ V
  forbidden_finite : forbidden.Finite
  window : ∀ p : ↥events, IncidentFanWindow F a V p.val
  windows_disjoint : ∀ p q : ↥events, p ≠ q →
    Disjoint (chartPull F (window p).chart (Metric.closedBall (0 : Plane) 1))
      (chartPull F (window q).chart (Metric.closedBall (0 : Plane) 1))
  selected_axis_fans : ∀ p : ↥events, ∀ i, i ∈ selected →
    ∀ hip : p.val ∈ range (a i),
      ∃ A : IncidentFanWindow F a V p.val,
        chartPull F A.chart (Metric.closedBall (0 : Plane) 1) ⊆
          chartPull F (window p).chart (Metric.ball (0 : Plane) 1) ∧
        incidentPorts a p.val A.chart A.left A.right (⟨i,hip⟩,false) 1 = 0 ∧
        incidentPorts a p.val A.chart A.left A.right (⟨i,hip⟩,true) 1 = 0 ∧
        ∀ j : incidentIndex a p.val, j.val ≠ i →
          ((0 < incidentPorts a p.val A.chart A.left A.right (j,false) 1 ∧
            incidentPorts a p.val A.chart A.left A.right (j,true) 1 < 0) ∨
          (incidentPorts a p.val A.chart A.left A.right (j,false) 1 < 0 ∧
            0 < incidentPorts a p.val A.chart A.left A.right (j,true) 1))
  opposite_side_charts : ∀ p : ↥events, ∀ i j, i ≠ j →
    (i ∈ selected ∨ j ∈ selected) →
    ∀ u t : Interval, u ∈ Ioo (0 : Interval) 1 → t ∈ Ioo (0 : Interval) 1 →
      a i u = p.val → a j t = p.val →
      ∃ C : RegionalEmbeddedFamily.RegionalIsolatedContactChart F (a i) (a j) u t,
        C.OppositeSides ∧
        {y : ↥F | y.val ∈ C.chart.source ∧ C.chart y.val ∈ Plane.closedSquare 0 1} ⊆ V

/-- A genuine relative-open B gap along the supplied embedded boundary side,
adjacent to its guiding endpoint. That endpoint may itself be forbidden. -/
structure BoundaryEndpointGap {X : Type} [TopologicalSpace X]
    (B V forbidden : Set X) (boundarySide : C(Interval,X)) where
  cut : Interval
  cut_lt_one : cut < 1
  gap_open_in_B : IsOpen {y : ↥B | y.val ∈ boundarySide '' Ioo cut 1}
  gap_in_V : boundarySide '' Ioo cut 1 ⊆ V
  gap_avoids : Disjoint (boundarySide '' Ioo cut 1) forbidden
  chosen : Interval
  chosen_in_gap : chosen ∈ Ioo cut 1

end RegionalWeightedMovies
