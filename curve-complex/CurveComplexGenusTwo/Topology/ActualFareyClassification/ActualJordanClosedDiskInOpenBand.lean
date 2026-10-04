import CurveComplexGenusTwo.Topology.TorusStrip.JordanBoxNarrow

open Set Topology Schoenflies

/-- Strict physical-band bounds on the actual compact Jordan boundary extend
strictly to the ENTIRE closed bounded disk. -/
theorem actual_jordan_closed_disk_in_open_horizontal_band
    (C : Set Plane) (hC : IsJordanCurve C) (d e : ℝ)
    (hBand : ∀ z∈C, d<z 1 ∧ z 1<e) :
    closure (inside C)⊆{z : Plane | d<z 1 ∧ z 1<e} := by
  obtain ⟨a,ha,hmin⟩ := hC.isCompact.exists_isMinOn hC.nonempty
    (EuclideanSpace.proj 1).continuous.continuousOn
  obtain ⟨b,hb,hmax⟩ := hC.isCompact.exists_isMaxOn hC.nonempty
    (EuclideanSpace.proj 1).continuous.continuousOn
  have hlo := jordan_coordinate_lower_bound hC 1 (a 1) (fun z hz => hmin hz)
  have hhi := jordan_coordinate_upper_bound hC 1 (b 1) (fun z hz => hmax hz)
  intro z hz
  exact ⟨lt_of_lt_of_le (hBand a ha).1 (hlo z hz),lt_of_le_of_lt (hhi z hz) (hBand b hb).2⟩

/-- An ACTUAL source bigon inherits the source horizontal band. There is no
additional subdisk-containment certificate. -/
theorem actual_source_bigon_closed_disk_in_open_horizontal_band
    (G : C(ℝ,Plane)) (r s d e : ℝ)
    (hJ : IsJordanCurve ((G '' Icc r s)∪segment ℝ (G r) (G s)))
    (hBand : ∀ x, d<G x 1 ∧ G x 1<e) :
    closure (inside ((G '' Icc r s)∪segment ℝ (G r) (G s)))⊆
      {z : Plane | d<z 1 ∧ z 1<e} := by
  apply actual_jordan_closed_disk_in_open_horizontal_band _ hJ d e
  intro z hz
  rcases hz with hz | hz
  · obtain ⟨x,hx,rfl⟩ := hz
    exact hBand x
  · have hConvex : Convex ℝ {z : Plane | d<z 1 ∧ z 1<e} :=
      (convex_Ioo d e).is_linear_preimage (EuclideanSpace.proj 1).isLinear
    exact hConvex.segment_subset (hBand r) (hBand s) hz

#print axioms actual_jordan_closed_disk_in_open_horizontal_band
#print axioms actual_source_bigon_closed_disk_in_open_horizontal_band
