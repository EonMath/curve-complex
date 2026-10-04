import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.ProperStripBoundaryParameters
import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.OriginalLoopFacingConnector
import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.ProperStripCompactification
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/- Private geometric leaf for the exact selected-loop zero-contact caller.
   The proof must construct the strip and its compactification from these
   source hypotheses; U, a chart, a collar, and graph clearance are outputs. -/
private theorem actual_selected_loop_zero_contact_prescribed_pinched_strip_leaf
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) b)
    (hzero : ArcSurgery.crossings M a b = ∅) :
    ∃ U : Set S,
      IsComplementComponent (a.val.image ∪ b.val.image) U ∧
      Disjoint U (M.cover.branch : Set S) ∧
      frontier U = a.val.image ∪ b.val.image ∧
      ∃ e : Interval ≃ₜ Interval,
        ((e 0 = 0 ∧ e 1 = 1) ∨ (e 0 = 1 ∧ e 1 = 0)) ∧
        ∃ G : C(Interval × Interval, S),
          (∀ s, G (s, 0) = a.val.map s) ∧
          (∀ s, G (s, 1) = b.val.map (e s)) ∧
          (∀ t, G (0, t) = a.val.map 0 ∧ G (1, t) = a.val.map 0) ∧
          (∀ s t s' t', G (s, t) = G (s', t') →
            (s = s' ∧ t = t') ∨
            ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1))) ∧
          (∀ s t, s ∈ Set.Ioo (0 : Interval) 1 →
            t ∈ Set.Ioo (0 : Interval) 1 → G (s, t) ∈ U) ∧
          (∀ s t, s ∈ Set.Ioo (0 : Interval) 1 →
            G (s, t) ∉ M.cover.branch) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let : CompactSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let : CompactSpace S := M.sphere.symm.compactSpace
  -- The relative pair-strip is constructed from the two actual proper lines.
  have pairStrip : ∀ (F G : C(ℝ, Schoenflies.Plane)),
      Topology.IsClosedEmbedding F → Topology.IsClosedEmbedding G →
      Disjoint (Set.range F) (Set.range G) →
      ∃ flip : Bool, ∃ H : C(ℝ × Interval, Schoenflies.Plane),
        Topology.IsClosedEmbedding H ∧
        (∀ s, H (s, 0) = F s) ∧
        (∀ s, H (s, 1) = G (if flip then -s else s)) := by
    exact proper_disjoint_lines_prescribed_strip
  have hb := (actual_same_class_loop_closure_invariant M a b hclass).mp ha
  have hbase := actual_same_class_loop_literal_base M a b ha hclass
  have hmeet := actual_zero_contact_same_class_loop_intersection M a b ha hclass hzero
  let F := originalLoopPlanarLineAt M (a.val.map 0) a.val ha rfl
  let L := originalLoopPlanarLineAt M (a.val.map 0) b.val hb hbase.symm
  have hF : Topology.IsClosedEmbedding F := originalLoopPlanarLineAt_closedEmbedding M _ a.val ha rfl
  have hL : Topology.IsClosedEmbedding L := originalLoopPlanarLineAt_closedEmbedding M _ b.val hb hbase.symm
  have hdis : Disjoint (Set.range F) (Set.range L) :=
    originalLoopPlanarLinesAt_disjoint M _ a.val b.val ha hb rfl hbase.symm hmeet
  obtain ⟨flip, H, hH, hH0, hH1⟩ := pairStrip F L hF hL hdis
  let Hp : C(ℝ × Interval, {x : S // x ≠ a.val.map 0}) :=
    ⟨(M.puncturedPlane (a.val.map 0)).symm ∘ H,
      (M.puncturedPlane (a.val.map 0)).symm.continuous.comp H.continuous⟩
  have hHp : Topology.IsClosedEmbedding Hp :=
    (M.puncturedPlane (a.val.map 0)).symm.isClosedEmbedding.comp hH
  let r := originalLoopRealParameter
  let Q := properStripCompactification (a.val.map 0) Hp hHp.isProperMap r
  let e : Interval ≃ₜ Interval := if flip then unitInterval.symmHomeomorph else Homeomorph.refl _
  have heends : (e 0 = 0 ∧ e 1 = 1) ∨ (e 0 = 1 ∧ e 1 = 0) := by
    cases flip <;> simp [e]
  have heparam (u : ℝ) : (r (if flip then -u else u) : Interval) = e (r u) := by
    cases flip
    · rfl
    · exact originalLoopRealParameter_neg u
  have hHp0 (u : ℝ) : (Hp (u, 0)).val = a.val.map (r u) := by
    change ((M.puncturedPlane (a.val.map 0)).symm (H (u, 0))).val = _
    rw [hH0]
    simp [F, originalLoopPlanarLineAt, r]
  have hHp1 (u : ℝ) : (Hp (u, 1)).val = b.val.map (e (r u)) := by
    change ((M.puncturedPlane (a.val.map 0)).symm (H (u, 1))).val = _
    rw [hH1]
    simp only [L, originalLoopPlanarLineAt, ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]
    exact congrArg b.val.map (heparam u)
  have hQends (w : Interval) : Q (0, w) = a.val.map 0 ∧ Q (1, w) = a.val.map 0 :=
    properStripCompactification_ends _ Hp hHp.isProperMap r w
  have hedge (u : Interval) (hu : u ∉ Set.Ioo (0 : Interval) 1) : u = 0 ∨ u = 1 := by
    by_cases h0 : u = 0
    · exact Or.inl h0
    by_cases h1 : u = 1
    · exact Or.inr h1
    exact False.elim (hu ⟨lt_of_le_of_ne u.property.1 (Ne.symm h0),
      lt_of_le_of_ne u.property.2 h1⟩)
  have hQ0 (u : Interval) : Q (u, 0) = a.val.map u := by
    by_cases hu : u ∈ Set.Ioo (0 : Interval) 1
    · rw [show Q (u, 0) = (Hp (r.symm ⟨u, hu⟩, 0)).val from
        properStripCompactification_interior _ Hp hHp.isProperMap r u 0 hu]
      rw [hHp0]
      simp
    · rcases hedge u hu with rfl | rfl
      · exact (hQends 0).1
      · exact (hQends 0).2.trans ha
  have hQ1 (u : Interval) : Q (u, 1) = b.val.map (e u) := by
    by_cases hu : u ∈ Set.Ioo (0 : Interval) 1
    · rw [show Q (u, 1) = (Hp (r.symm ⟨u, hu⟩, 1)).val from
        properStripCompactification_interior _ Hp hHp.isProperMap r u 1 hu]
      rw [hHp1]
      simp
    · rcases hedge u hu with rfl | rfl
      · rw [(hQends 1).1]
        cases flip <;> simp [e, hbase, hb]
      · rw [(hQends 1).2]
        cases flip <;> simp [e, hbase, hb]
  obtain ⟨A⟩ := markedLoop_disc_decomposition_exists M a.val ha
  obtain ⟨B⟩ := markedLoop_disc_decomposition_exists M b.val hb
  obtain ⟨i, hbi⟩ := actual_common_base_loop_other_trace_one_side M a b hb hbase hmeet A
  let j : Fin 2 := if i = 0 then 1 else 0
  have hij : i ≠ j := by fin_cases i <;> simp [j]
  obtain ⟨k, hAjB, hak, hfree⟩ :=
    actual_same_class_common_base_between_region_mark_free M a b ha hclass hmeet
      A B i j hij hbi
  let m : Fin 2 := if k = 0 then 1 else 0
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
    · simpa [j, Set.union_comm] using A.complement
  have hBpart : B.side k ∪ B.side m = b.val.imageᶜ := by
    fin_cases k
    · simpa [m] using B.complement
    · simpa [m, Set.union_comm] using B.complement
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
  have hHpin (u : ℝ) : ∀ w ∈ Set.Ioo (0 : Interval) 1, (Hp (u, w)).val ∈ U := by
    let P : C(Interval, S) := ⟨fun w => (Hp (u, w)).val,
      continuous_subtype_val.comp (Hp.continuous.comp (continuous_const.prodMk continuous_id))⟩
    have hP0V : P 0 ∈ B.side k := by
      change (Hp (u, 0)).val ∈ _
      rw [hHp0]
      exact hak ⟨Set.mem_range_self _, (originalLoopPuncturedLine M a.val ha (r u)).property⟩
    have hP1U : P 1 ∈ A.side i := by
      change (Hp (u, 1)).val ∈ _
      rw [hHp1, ← heparam]
      refine hbi ⟨Set.mem_range_self _, ?_⟩
      intro he
      exact (originalLoopPuncturedLine M b.val hb (r (if flip then -u else u))).property
        (he.trans hbase)
    have hPfree : ∀ w ∈ Set.Ioo (0 : Interval) 1, P w ∉ a.val.image ∪ b.val.image := by
      intro w hw hmem
      rcases hmem with hmem | hmem
      · obtain ⟨v, hv⟩ := (originalLoopPlanarLineAt_range_inverse M _ a.val ha rfl _).mpr hmem
        have he : H (v, 0) = H (u, w) := (hH0 v).trans hv
        have hw0 : (0 : Interval) = w := congrArg Prod.snd (hH.injective he)
        exact (ne_of_gt hw.1) hw0.symm
      · obtain ⟨v, hv⟩ := (originalLoopPlanarLineAt_range_inverse M _ b.val hb hbase.symm _).mpr hmem
        let v' : ℝ := if flip then -v else v
        have hv' : (if flip then -v' else v') = v := by cases flip <;> simp [v']
        have he : H (v', 1) = H (u, w) := by rw [hH1, hv']; exact hv
        have hw1 : (1 : Interval) = w := congrArg Prod.snd (hH.injective he)
        exact (ne_of_lt hw.2) hw1.symm
    exact continuous_interval_connector_in_facing_sides a.val.image b.val.image
      (A.side i) (A.side j) (B.side k) (B.side m)
      (A.discs i).open_side (A.discs j).open_side
      (B.discs k).open_side (B.discs m).open_side
      hAdis hBdis hApart hBpart P hP0V hP1U hPfree
  have hQin (u w : Interval) (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (hw : w ∈ Set.Ioo (0 : Interval) 1) : Q (u, w) ∈ U := by
    rw [show Q (u, w) = (Hp (r.symm ⟨u, hu⟩, w)).val from
      properStripCompactification_interior _ Hp hHp.isProperMap r u w hu]
    exact hHpin _ w hw
  refine ⟨U, hUcomp, hfree, hfront, e, heends, Q, hQ0, hQ1, hQends, ?_, hQin, ?_⟩
  · intro s t s' t' he
    exact properStripCompactification_injective_except_ends _ Hp hHp.isProperMap hHp.injective
      r s s' t t' he
  · intro s t hs hmark
    by_cases ht : t ∈ Set.Ioo (0 : Interval) 1
    · exact Set.disjoint_left.mp hfree (hQin s t hs ht) hmark
    · rcases hedge t ht with rfl | rfl
      · rw [hQ0] at hmark
        rcases a.val.marked_only_at_ends _ hmark with he | he
        · exact (ne_of_gt hs.1) he
        · exact (ne_of_lt hs.2) he
      · rw [hQ1] at hmark
        have hse : e s ∈ Set.Ioo (0 : Interval) 1 := by
          cases flip
          · exact hs
          · exact ⟨by change 0 < 1 - (s : ℝ); have h := hs.2; change (s : ℝ) < 1 at h; linarith,
              by change 1 - (s : ℝ) < 1; have h := hs.1; change 0 < (s : ℝ) at h; linarith⟩
        rcases b.val.marked_only_at_ends _ hmark with he | he
        · exact (ne_of_gt hse.1) he
        · exact (ne_of_lt hse.2) he

end CurveComplex.HyperellipticModel
