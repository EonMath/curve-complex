import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualMarkFreeBigonLocalization

noncomputable section
open Set Topology Schoenflies CurveComplex

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A genuine essential marked loop cannot lie in a closed square whose
open interior contains no marks. This includes a loop based on the boundary. -/
theorem actual_essential_arc_in_mark_free_square_nonloop
    (M : HyperellipticModel E S) (c : EssentialMarkedArc M)
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (hc : c.val.image ⊆ f '' Plane.closedSquare 0 1)
    (hfree : ∀ z ∈ Plane.openSquare 0 1, f z ∉ M.cover.branch) :
    c.val.map (0 : Interval) ≠ c.val.map (1 : Interval) := by
  letI : T2Space S := M.sphere.symm.t2Space
  intro hloop
  let e := hf.toOpenPartialHomeomorph f
  let g : Interval → Plane := e.symm ∘ c.val.map
  have hcrange (t : Interval) : c.val.map t ∈ Set.range f := by
    obtain ⟨z, hz, he⟩ := hc (Set.mem_range_self t)
    exact ⟨z, he⟩
  have hsource (t : Interval) : c.val.map t ∈ e.symm.source := by
    change c.val.map t ∈ e.target
    simpa only [e, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using hcrange t
  have hfg (t : Interval) : f (g t) = c.val.map t :=
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv f hf (hcrange t)
  have hg : Continuous g := e.symm.continuousOn.comp_continuous c.val.continuous hsource
  let C := Set.range g
  have hC : IsJordanCurve C := by
    let k : ℝ → Plane := g ∘ Set.projIcc 0 1 zero_le_one
    have hk : Continuous k := hg.comp continuous_projIcc
    refine ⟨k, ⟨hk.continuousOn, ?_, ?_⟩, ?_⟩
    · simpa [k, g, Set.projIcc_of_mem] using congrArg e.symm hloop
    · intro t ht u hu h
      let ti : Interval := ⟨t, ht.1, ht.2.le⟩
      let ui : Interval := ⟨u, hu.1, hu.2.le⟩
      have he : g ti = g ui := by
        simpa only [k, Function.comp_apply,
          Set.projIcc_of_mem zero_le_one ⟨ht.1, ht.2.le⟩,
          Set.projIcc_of_mem zero_le_one ⟨hu.1, hu.2.le⟩, ti, ui] using h
      have hcmap : c.val.map ti = c.val.map ui :=
        (hfg ti).symm.trans ((congrArg f he).trans (hfg ui))
      rcases c.val.injective_except_loop_closure ti ui hcmap with h | h | h
      · exact congrArg Subtype.val h
      · exact (hu.2.ne (congrArg Subtype.val h.2)).elim
      · exact (ht.2.ne (congrArg Subtype.val h.1)).elim
    · ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨t, rfl⟩
        refine ⟨t, t.property, ?_⟩
        simp [k, Set.projIcc_of_mem]
  have hCsub : C ⊆ Plane.closedSquare 0 1 := by
    rintro z ⟨t, rfl⟩
    obtain ⟨w, hw, he⟩ := hc (Set.mem_range_self t)
    have hgw : g t = w := hf.injective ((hfg t).trans he.symm)
    exact hgw.symm ▸ hw
  have himage : f '' C = c.val.image := by
    ext y
    constructor
    · rintro ⟨z, ⟨t, rfl⟩, rfl⟩
      exact hfg t ▸ Set.mem_range_self t
    · rintro ⟨t, rfl⟩
      exact ⟨g t, Set.mem_range_self t, hfg t⟩
  have hs := jordan_curve_theorem hC
  have hk : IsCompact (closure (inside C)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.isBounded_inside.closure
  have hU := open_embedding_bounded_face_transport f hf C (inside C)
    (jordan_inside_complement_component hC) hs.isOpen_inside hk
    (by rw [hs.frontier_inside])
  rw [himage] at hU
  have hess := c.property
  change c.val.map (0 : Interval) ≠ c.val.map (1 : Interval) ∨
    ∀ U, IsComplementComponent c.val.image U → ∃ b, b ∈ M.cover.branch ∧ b ∈ U at hess
  rcases hess with hn | he
  · exact hn hloop
  · obtain ⟨b, hb, z, hz, hzb⟩ := he (f '' inside C) hU
    exact hfree z (actual_jordan_inside_closed_square hC hCsub hz) (hzb.symm ▸ hb)

/-- In a mark-free actual bigon, an intruding essential protected arc must
be a non-loop. Boundary-based loops are excluded by the actual essentiality
predicate rather than silently discarded from the family. -/
theorem actual_mark_free_bigon_intruding_arc_nonloop
    (M : HyperellipticModel E S) (a b c : EssentialMarkedArc M)
    (hca : Disjoint (arcInterior M c) (arcInterior M a))
    (hcb : Disjoint (arcInterior M c) (arcInterior M b))
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (hboundary : a.val.image ∪ b.val.image = f '' modelCurve)
    (hentry : (arcInterior M c ∩ f '' Plane.openSquare 0 1).Nonempty)
    (hfree : ∀ z ∈ Plane.openSquare 0 1, f z ∉ M.cover.branch) :
    c.val.map (0 : Interval) ≠ c.val.map (1 : Interval) := by
  have hc := (actual_endpoint_bigon_intruding_arc_localization M a b c hca hcb
    f hf hboundary hentry).2
  exact actual_essential_arc_in_mark_free_square_nonloop M c f hf hc hfree

#print axioms actual_essential_arc_in_mark_free_square_nonloop
#print axioms actual_mark_free_bigon_intruding_arc_nonloop
end CurveComplex.HyperellipticModel
