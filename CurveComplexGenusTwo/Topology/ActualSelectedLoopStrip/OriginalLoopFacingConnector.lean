import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.OriginalLoopPuncturedLine
import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.ProperLineConnector
import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.ZeroContactLoopIntersection

open Set Topology

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem originalLoopRealParameter_neg (t : ℝ) :
    (originalLoopRealParameter (-t) : Interval) =
      unitInterval.symm (originalLoopRealParameter t) := by
  apply Subtype.ext
  simp [originalLoopRealParameter, orderIsoIooNegOneOne, unitInterval.symm, Set.codRestrict]
  ring

theorem originalLoopPlanarLineAt_range_inverse
    (M : HyperellipticModel E S) (p : S) (a : MarkedArc M)
    (ha : a.map 0 = a.map 1) (hp : a.map 0 = p) (z : Schoenflies.Plane) :
    z ∈ range (originalLoopPlanarLineAt M p a ha hp) ↔
      ((M.puncturedPlane p).symm z).val ∈ a.image := by
  constructor
  · rintro ⟨t, rfl⟩
    simp only [originalLoopPlanarLineAt, ContinuousMap.coe_mk,
      Homeomorph.symm_apply_apply]
    exact mem_range_self _
  · rintro ⟨t, ht⟩
    have hn : a.map t ≠ p := ht ▸ ((M.puncturedPlane p).symm z).property
    have ht0 : t ≠ 0 := by intro he; exact hn (he ▸ hp)
    have ht1 : t ≠ 1 := by intro he; exact hn (he ▸ ha.symm.trans hp)
    have hti : t ∈ Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
        lt_of_le_of_ne t.property.2 ht1⟩
    refine ⟨originalLoopRealParameter.symm ⟨t, hti⟩, ?_⟩
    simp only [originalLoopPlanarLineAt, ContinuousMap.coe_mk,
      Homeomorph.apply_symm_apply]
    have he : (⟨a.map t, hn⟩ : {x : S // x ≠ p}) = (M.puncturedPlane p).symm z :=
      Subtype.ext ht
    simp only [he, Homeomorph.apply_symm_apply]

theorem continuous_interval_connector_in_facing_sides
    (K L U Uout V Vout : Set S)
    (hU : IsOpen U) (hUout : IsOpen Uout)
    (hV : IsOpen V) (hVout : IsOpen Vout)
    (hUUout : Disjoint U Uout) (hVVout : Disjoint V Vout)
    (hUpart : U ∪ Uout = Kᶜ) (hVpart : V ∪ Vout = Lᶜ)
    (P : C(Interval, S)) (hP0V : P 0 ∈ V) (hP1U : P 1 ∈ U)
    (hfree : ∀ t ∈ Ioo (0 : Interval) 1, P t ∉ K ∪ L) :
    ∀ t ∈ Ioo (0 : Interval) 1, P t ∈ U ∩ V := by
  have hsubU : P '' Ioc (0 : Interval) 1 ⊆ U := by
    have hcover : P '' Ioc (0 : Interval) 1 ⊆ U ∪ Uout := by
      rw [hUpart]
      rintro z ⟨t, ht, rfl⟩ hz
      by_cases he : t = 1
      · have hn : P 1 ∈ Kᶜ := hUpart ▸ Or.inl hP1U
        exact hn (he ▸ hz)
      · exact hfree t ⟨ht.1, lt_of_le_of_ne ht.2 he⟩ (Or.inl hz)
    rcases (isPreconnected_Ioc.image P P.continuous.continuousOn).subset_or_subset
        hU hUout hUUout hcover with h | h
    · exact h
    · exact False.elim (disjoint_left.mp hUUout hP1U (h ⟨1, by norm_num, rfl⟩))
  have hsubV : P '' Ico (0 : Interval) 1 ⊆ V := by
    have hcover : P '' Ico (0 : Interval) 1 ⊆ V ∪ Vout := by
      rw [hVpart]
      rintro z ⟨t, ht, rfl⟩ hz
      by_cases he : t = 0
      · have hn : P 0 ∈ Lᶜ := hVpart ▸ Or.inl hP0V
        exact hn (he ▸ hz)
      · exact hfree t ⟨lt_of_le_of_ne ht.1 (Ne.symm he), ht.2⟩ (Or.inr hz)
    rcases (isPreconnected_Ico.image P P.continuous.continuousOn).subset_or_subset
        hV hVout hVVout hcover with h | h
    · exact h
    · exact False.elim (disjoint_left.mp hVVout hP0V (h ⟨0, by norm_num, rfl⟩))
  intro t ht
  exact ⟨hsubU ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩,
    hsubV ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩⟩

/-- The original source hypotheses produce a genuine embedded transverse
connector inside the mark-free face, with endpoints on the literal loop maps. -/
theorem actual_zero_contact_original_loop_facing_connector
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) b)
    (hzero : ArcSurgery.crossings M a b = ∅) :
    ∃ U : Set S,
      IsComplementComponent (a.val.image ∪ b.val.image) U ∧
      Disjoint U (M.cover.branch : Set S) ∧
      frontier U = a.val.image ∪ b.val.image ∧
      ∃ s t : Ioo (0 : Interval) 1, ∃ P : C(Interval, S),
        P 0 = a.val.map s ∧ P 1 = b.val.map t ∧
        Function.Injective P ∧
        (∀ u ∈ Ioo (0 : Interval) 1, P u ∈ U) ∧
        (∀ u, P u ∉ M.cover.branch) := by
  have hb := (actual_same_class_loop_closure_invariant M a b hclass).mp ha
  have hbase := actual_same_class_loop_literal_base M a b ha hclass
  have hmeet := actual_zero_contact_same_class_loop_intersection M a b ha hclass hzero
  let F := originalLoopPlanarLineAt M (a.val.map 0) a.val ha rfl
  let G := originalLoopPlanarLineAt M (a.val.map 0) b.val hb hbase.symm
  have hF : IsClosedEmbedding F := originalLoopPlanarLineAt_closedEmbedding M _ a.val ha rfl
  have hG : IsClosedEmbedding G := originalLoopPlanarLineAt_closedEmbedding M _ b.val hb hbase.symm
  have hdis : Disjoint (range F) (range G) :=
    originalLoopPlanarLinesAt_disjoint M _ a.val b.val ha hb rfl hbase.symm hmeet
  obtain ⟨s, t, hne, hcross⟩ :=
    CurveComplexGenusTwo.Topology.PuncturedTorusCandidate.proper_disjoint_lines_have_straight_connector
      F G hF hG hdis
  let P : C(Interval, S) :=
    ⟨fun u => ((M.puncturedPlane (a.val.map 0)).symm
        (AffineMap.lineMap (F s) (G t) (u : ℝ))).val,
      continuous_subtype_val.comp ((M.puncturedPlane (a.val.map 0)).symm.continuous.comp
        (by fun_prop))⟩
  have hP0 : P 0 = a.val.map (originalLoopRealParameter s) := by
    simp [P, F, originalLoopPlanarLineAt]
  have hP1 : P 1 = b.val.map (originalLoopRealParameter t) := by
    simp [P, G, originalLoopPlanarLineAt]
  have hPinj : Function.Injective P := by
    intro u v huv
    apply Subtype.ext
    apply AffineMap.lineMap_injective ℝ hne
    apply (M.puncturedPlane (a.val.map 0)).symm.injective
    exact Subtype.ext huv
  have hPfree : ∀ u ∈ Ioo (0 : Interval) 1, P u ∉ a.val.image ∪ b.val.image := by
    intro u hu hmem
    apply hcross (u : ℝ) ⟨hu.1, hu.2⟩
    rcases hmem with hmem | hmem
    · exact Or.inl ((originalLoopPlanarLineAt_range_inverse M _ a.val ha rfl _).mpr hmem)
    · exact Or.inr ((originalLoopPlanarLineAt_range_inverse M _ b.val hb hbase.symm _).mpr hmem)
  obtain ⟨A⟩ := markedLoop_disc_decomposition_exists M a.val ha
  obtain ⟨B⟩ := markedLoop_disc_decomposition_exists M b.val hb
  obtain ⟨i, hbi⟩ := actual_common_base_loop_other_trace_one_side M a b hb hbase hmeet A
  let j : Fin 2 := if i = 0 then 1 else 0
  have hij : i ≠ j := by fin_cases i <;> simp [j]
  obtain ⟨k, hAjB, hak, hfree⟩ :=
    actual_same_class_common_base_between_region_mark_free M a b ha hclass hmeet
      A B i j hij hbi
  let m : Fin 2 := if k = 0 then 1 else 0
  have hkm : k ≠ m := by fin_cases k <;> simp [m]
  have hAdis : Disjoint (A.side i) (A.side j) := by
    fin_cases i
    · simpa [j] using A.disjoint
    · simpa [j] using A.disjoint.symm
  have hBdis : Disjoint (B.side k) (B.side m) := by
    fin_cases k
    · simpa [m] using B.disjoint
    · simpa [m] using B.disjoint.symm
  have hApart : A.side i ∪ A.side j = a.val.imageᶜ := by
    fin_cases i
    · simpa [j] using A.complement
    · simpa [j, union_comm] using A.complement
  have hBpart : B.side k ∪ B.side m = b.val.imageᶜ := by
    fin_cases k
    · simpa [m] using B.complement
    · simpa [m, union_comm] using B.complement
  have hP0V : P 0 ∈ B.side k := by
    rw [hP0]
    exact hak ⟨mem_range_self _, (originalLoopPuncturedLine M a.val ha
      (originalLoopRealParameter s)).property⟩
  have hP1U : P 1 ∈ A.side i := by
    rw [hP1]
    refine hbi ⟨mem_range_self _, ?_⟩
    intro he
    exact (originalLoopPuncturedLine M b.val hb (originalLoopRealParameter t)).property
      (he.trans hbase)
  have hPin := continuous_interval_connector_in_facing_sides a.val.image b.val.image
    (A.side i) (A.side j) (B.side k) (B.side m)
    (A.discs i).open_side (A.discs j).open_side
    (B.discs k).open_side (B.discs m).open_side
    hAdis hBdis hApart hBpart P hP0V hP1U hPfree
  let U := A.side i ∩ B.side k
  have hUopen : IsOpen U := (A.discs i).open_side.inter (B.discs k).open_side
  have hUconn : IsConnected U := actual_common_base_between_region_connected
    M a b hb hbase A B i j k hij hbi hAjB hak
  have hUsub : U ⊆ (a.val.image ∪ b.val.image)ᶜ := by
    intro x hx hxab
    rcases hxab with hxa | hxb
    · exact (A.discs i).component.2.2.1 hx.1 hxa
    · exact (B.discs k).component.2.2.1 hx.2 hxb
  have hfront := actual_common_base_between_frontier_eq M a b A B i k hbi hak
  have hUcomp : IsComplementComponent (a.val.image ∪ b.val.image) U := by
    apply actual_open_connected_region_is_complement_component
      (a.val.image ∪ b.val.image) U hUopen hUconn hUsub
    rw [hfront]
  refine ⟨U, hUcomp, hfree, hfront, originalLoopRealParameter s,
    originalLoopRealParameter t, P, hP0, hP1, hPinj, hPin, ?_⟩
  intro u hu
  by_cases h0 : u = 0
  · rw [h0, hP0] at hu
    rcases a.val.marked_only_at_ends _ hu with he | he
    · exact (ne_of_gt (originalLoopRealParameter s).property.1) he
    · exact (ne_of_lt (originalLoopRealParameter s).property.2) he
  by_cases h1 : u = 1
  · rw [h1, hP1] at hu
    rcases b.val.marked_only_at_ends _ hu with he | he
    · exact (ne_of_gt (originalLoopRealParameter t).property.1) he
    · exact (ne_of_lt (originalLoopRealParameter t).property.2) he
  · exact disjoint_left.mp hfree (hPin u
      ⟨lt_of_le_of_ne u.property.1 (Ne.symm h0), lt_of_le_of_ne u.property.2 h1⟩) hu

end CurveComplex.HyperellipticModel
