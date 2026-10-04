import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualPrescribedTargetEndpointMargins

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology Schoenflies CurveComplex.ActualCrossingSlide
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- An actual prescribed-target crossing chart, with its source geometry and
stationary anchor axis. No surgery, homotopy or target-reaching move is stored. -/
structure ActualTargetCrossingChart (M : HyperellipticModel E S)
    (anchor a : EssentialMarkedArc M) (p : S) where
  source : Set S
  target : Set Plane
  open_source : IsOpen source
  coordinate : source ≃ₜ target
  square_target : Plane.closedSquare 0 1 ⊆ target
  marked_free : Disjoint source (M.cover.branch : Set S)
  anchor_axis : ∀ q : source, q.val ∈ anchor.val.image ↔ (coordinate q).val 1 = 0
  point : p ∈ source
  point_zero : planeCoordinates (coordinate ⟨p,point⟩).val = (0,0)

/-- Every actual prescribed-target transverse contact produces its chart. -/
theorem actual_target_crossing_chart_producer
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (Q : FinitePosition M anchor F)
    (v : {v // v ∈ F}) (p : S) (hp : p ∈ crossings M anchor (Q.rep v)) :
    Nonempty (ActualTargetCrossingChart M anchor (Q.rep v) p) := by
  obtain ⟨U,V,hU,e,hCV,hm,ha,hpU,hp0⟩ := actual_crossing_disk_slide_chart
    M anchor (Q.rep v) p (Q.transverse v p hp)
  exact ⟨⟨U,V,hU,e,hCV,hm,ha,hpU,hp0⟩⟩

/-- PRODUCE finite whole-target geometric preparation from the actual
prescribed Q alone: selected endpoint margins, actual anchor crossing charts,
and actual complementary embedded core strips covering its entire compact
middle. Endpoint collars have no interior anchor contacts, including when
marked endpoints are shared. No chart, strip, margin, finite cover, move,
reaching script or homotopy is an input. -/
theorem actual_prescribed_target_finite_geometry
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (hF : IsArcSimplex M F)
    (Q : FinitePosition M anchor F) (v : {v // v ∈ F}) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
      (∀ r : Interval, 0 < r.val → r.val < δ → (Q.rep v).val.map r ∉ anchor.val.image) ∧
      (∀ r : Interval, 1-δ < r.val → r.val < 1 → (Q.rep v).val.map r ∉ anchor.val.image) ∧
      ∃ charts : (p : crossings M anchor (Q.rep v)) →
        ActualTargetCrossingChart M anchor (Q.rep v) p.val,
      ∃ strips : Finset (ActualTargetCoreStrip M anchor F Q v),
        ((Q.rep v).val.map '' {r : Interval | δ ≤ r.val ∧ r.val ≤ 1-δ}) ⊆
          (⋃ p, (charts p).source) ∪ (⋃ B ∈ strips, range B.map) ∧
        (crossings M anchor (Q.rep v)).Finite := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨δ,hδ,hhalf,hcontacts,hleft,hright⟩ :=
    actual_prescribed_target_endpoint_contact_margin M anchor F Q v
  have hex (p : crossings M anchor (Q.rep v)) :
      Nonempty (ActualTargetCrossingChart M anchor (Q.rep v) p.val) :=
    actual_target_crossing_chart_producer M anchor F Q v p.val p.property
  let charts := fun p => Classical.choice (hex p)
  let W : Set S := ⋃ p, (charts p).source
  have hW : IsOpen W := isOpen_iUnion (fun p => (charts p).open_source)
  let middle : Set Interval := {r : Interval | δ ≤ r.val ∧ r.val ≤ 1-δ}
  let K : Set Interval := middle \ (Q.rep v).val.map ⁻¹' W
  have hmiddle : IsClosed middle :=
    (isClosed_Icc.preimage continuous_subtype_val)
  have hKclosed : IsClosed K := hmiddle.sdiff (hW.preimage (Q.rep v).val.continuous)
  have hK : IsCompact K := hKclosed.isCompact
  have hKi : ∀ r ∈ K, 0 < r.val ∧ r.val < 1 := by
    intro r hr
    exact ⟨hδ.trans_le hr.1.1,by linarith [hr.1.2]⟩
  have hKa : ∀ r ∈ K, (Q.rep v).val.map r ∉ anchor.val.image := by
    intro r hr hra
    have hri := hKi r hr
    have hm : (Q.rep v).val.map r ∉ M.cover.branch := by
      intro hm
      rcases (Q.rep v).val.marked_only_at_ends r hm with hh | hh
      · have he := congrArg Subtype.val hh; change r.val=0 at he; linarith [hri.1]
      · have he := congrArg Subtype.val hh; change r.val=1 at he; linarith [hri.2]
    have hp : (Q.rep v).val.map r ∈ crossings M anchor (Q.rep v) :=
      ⟨⟨hra,hm⟩,mem_range_self r,hm⟩
    exact hr.2 (mem_iUnion.mpr ⟨⟨_,hp⟩,(charts ⟨_,hp⟩).point⟩)
  obtain ⟨strips,hstripParameters,hstripImages⟩ := actual_compact_prescribed_target_finite_strips
    M anchor F hF Q v K hK hKi hKa
  refine ⟨δ,hδ,hhalf,hleft,hright,charts,strips,?_,Q.finite v⟩
  rintro z ⟨r,hr,rfl⟩
  by_cases hzW : (Q.rep v).val.map r ∈ W
  · exact Or.inl hzW
  · exact Or.inr (hstripImages ⟨r,⟨hr,hzW⟩,rfl⟩)

end
end CurveComplex.HyperellipticModel.ArcSurgery
