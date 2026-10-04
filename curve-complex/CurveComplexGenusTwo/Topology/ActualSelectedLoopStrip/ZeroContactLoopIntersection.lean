import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopOriginalFirstContactBoundary
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopClosureInvariant
import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects
import CurveComplexGenusTwo.Dictionary.JordanEssentiality
import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport
import CurveComplexGenusTwo.Topology.ArcCounts.ActualNumericDegree
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import CurveComplexGenusTwo.Filtration.Geometry.ActualCommonBasepointLoopIsotopy

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_zero_contact_same_class_loop_intersection
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) b)
    (hzero : ArcSurgery.crossings M a b = ∅) :
    a.val.image ∩ b.val.image = {a.val.map 0} := by
  have hbase : a.val.map 0 = b.val.map 0 :=
    actual_same_class_loop_literal_base M a b ha hclass
  ext x
  constructor
  · rintro ⟨hxa, hxb⟩
    by_contra hx
    have hmark : x ∈ (M.cover.branch : Set S) := by
      by_contra hnot
      have hcross : x ∈ ArcSurgery.crossings M a b :=
        ⟨⟨hxa, hnot⟩, ⟨hxb, hnot⟩⟩
      rw [hzero] at hcross
      exact hcross
    obtain ⟨t, ht⟩ := hxa
    rcases a.val.marked_only_at_ends t (ht ▸ hmark) with ht0 | ht1
    · exact hx (ht.symm.trans (congrArg a.val.map ht0))
    · exact hx ((ht.symm.trans (congrArg a.val.map ht1)).trans ha.symm)
  · intro hx
    have hxe : x = a.val.map 0 := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨⟨0, rfl⟩, ⟨0, hbase.symm⟩⟩

theorem actual_loop_family_trace_avoids_other_object_trace
    (M : HyperellipticModel E S)
    {F : Finset (EssentialArcClass M)}
    (r : {w // w ∈ F} → EssentialMarkedArc M)
    (hd : ∀ w z, w ≠ z →
      Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
    (J : Finset (EssentialArcClass M))
    (u : {w // w ∈ F}) (hu : u.val ∉ J)
    (hloop : (r u).val.map 0 = (r u).val.map 1)
    (x : S) (hx : x ∈ (r u).val.image)
    (hbase : x ≠ (r u).val.map 0) :
    x ∉ actualObjectTrace M r J := by
  have hxnotmark : x ∉ (M.cover.branch : Set S) := by
    intro hm
    obtain ⟨t, ht⟩ := hx
    rcases (r u).val.marked_only_at_ends t (ht ▸ hm) with ht0 | ht1
    · exact hbase (ht.symm.trans (congrArg (r u).val.map ht0))
    · exact hbase ((ht.symm.trans (congrArg (r u).val.map ht1)).trans hloop.symm)
  intro hxgraph
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hxgraph
  obtain ⟨hvJ, hvx⟩ := Set.mem_iUnion.mp hv
  have huv : u ≠ v := by
    intro he
    exact hu (he ▸ hvJ)
  have hdis := hd u v huv
  exact Set.disjoint_left.mp hdis ⟨hx, hxnotmark⟩ ⟨hvx, hxnotmark⟩

theorem actual_selected_loop_boundaries_avoid_original_graph
    (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
    (rT : {w // w ∈ T.val} → EssentialMarkedArc M)
    (hdT : ∀ w z, w ≠ z → Disjoint (arcInterior M (rT w)) (arcInterior M (rT z)))
    (F J : Finset (EssentialArcClass M)) (hTF : T.val ⊆ F) (hJT : J ⊆ T.val)
    (r0 : {w // w ∈ F} → EssentialMarkedArc M)
    (hd0 : ∀ w z, w ≠ z → Disjoint (arcInterior M (r0 w)) (arcInterior M (r0 z)))
    (haligned0 : ∀ w : {w // w ∈ T.val}, w.val ∈ J →
      r0 ⟨w.val, hTF w.property⟩ = rT w)
    (r : {w // w ∈ F} → EssentialMarkedArc M)
    (hgraph : actualObjectTrace M r0 J = actualObjectTrace M r J)
    (u : {w // w ∈ T.val}) (hu : u.val ∉ J)
    (hloop : (r0 ⟨u.val, hTF u.property⟩).val.map 0 =
      (r0 ⟨u.val, hTF u.property⟩).val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) (r0 ⟨u.val, hTF u.property⟩) =
      Quotient.mk (essentialArcSetoid M) (rT u))
    (x : S)
    (hx : x ∈ (r0 ⟨u.val, hTF u.property⟩).val.image ∪ (rT u).val.image)
    (hbase : x ≠ (r0 ⟨u.val, hTF u.property⟩).val.map 0) :
    x ∉ actualObjectTrace M r J := by
  let uF : {w // w ∈ F} := ⟨u.val, hTF u.property⟩
  rw [← hgraph]
  rcases hx with hxa | hxb
  · exact actual_loop_family_trace_avoids_other_object_trace M r0 hd0 J uF hu
      hloop x hxa hbase
  · have hbaseEq : (r0 uF).val.map 0 = (rT u).val.map 0 :=
      actual_same_class_loop_literal_base M (r0 uF) (rT u) hloop hclass
    have hbloop : (rT u).val.map 0 = (rT u).val.map 1 :=
      (actual_same_class_loop_closure_invariant M (r0 uF) (rT u) hclass).mp hloop
    have hxnotmark : x ∉ (M.cover.branch : Set S) := by
      intro hm
      obtain ⟨t, ht⟩ := hxb
      rcases (rT u).val.marked_only_at_ends t (ht ▸ hm) with ht0 | ht1
      · exact hbase ((ht.symm.trans (congrArg (rT u).val.map ht0)).trans hbaseEq.symm)
      · exact hbase (((ht.symm.trans (congrArg (rT u).val.map ht1)).trans
          hbloop.symm).trans hbaseEq.symm)
    intro hxgraph
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hxgraph
    obtain ⟨hvJ, hvx⟩ := Set.mem_iUnion.mp hv
    let vT : {w // w ∈ T.val} := ⟨v.val, hJT hvJ⟩
    have hvEq : r0 v = rT vT := by
      simpa [vT] using haligned0 vT hvJ
    have huv : u ≠ vT := by
      intro he
      exact hu (he ▸ hvJ)
    have hxv : x ∈ (rT vT).val.image := by simpa [← hvEq] using hvx
    exact Set.disjoint_left.mp (hdT u vT huv) ⟨hxb, hxnotmark⟩
      ⟨hxv, hxnotmark⟩

theorem actual_common_base_loop_other_trace_one_side
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hb : b.val.map 0 = b.val.map 1)
    (hbase : a.val.map 0 = b.val.map 0)
    (hmeet : a.val.image ∩ b.val.image = {a.val.map 0})
    (D : MarkedLoopDiscDecomposition a.val) :
    ∃ i : Fin 2, b.val.image \ {a.val.map 0} ⊆ D.side i := by
  have hbconn : IsConnected (b.val.image \ {a.val.map 0}) := by
    rw [hbase]
    exact loop_image_remove_base_connected M b.val hb
  have hbsub : b.val.image \ {a.val.map 0} ⊆ a.val.imageᶜ := by
    intro x hx hxa
    have hxbase : x ∈ ({a.val.map 0} : Set S) := hmeet ▸ ⟨hxa, hx.1⟩
    exact hx.2 hxbase
  obtain ⟨x, hx⟩ := hbconn.nonempty
  let C := connectedComponentIn a.val.imageᶜ x
  have hC : IsComplementComponent a.val.image C :=
    complementComponent_iff_componentIn.mpr ⟨x, hbsub hx, rfl⟩
  obtain ⟨i, hi⟩ := (D.all_components C).mp hC
  refine ⟨i, ?_⟩
  rw [← hi]
  exact hbconn.isPreconnected.subset_connectedComponentIn hx hbsub

theorem actual_same_class_complement_side_mark_pattern
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hclass : Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) b)
    (U : Set S) (hU : IsComplementComponent a.val.image U) :
    ∃ V : Set S, IsComplementComponent b.val.image V ∧
      ∀ z ∈ M.cover.branch, (z ∈ U ↔ z ∈ V) := by
  obtain ⟨H, hfix, himage⟩ := Quotient.exact hclass
  obtain ⟨e, he⟩ := H.homeomorphism_at (1 : Interval)
  have hefix (z : S) (hz : z ∈ M.cover.branch) : e z = z := by
    rw [he z]
    exact hfix 1 z hz
  have hefinal : e = H.finalMap := by
    funext x
    exact he x
  have himage : e '' a.val.image = b.val.image := by
    rw [hefinal]
    exact himage
  refine ⟨e '' U, ?_, ?_⟩
  · rw [← himage]
    exact complementComponent_image e hU
  · intro z hz
    constructor
    · intro hzU
      exact ⟨z, hzU, hefix z hz⟩
    · rintro ⟨x, hxU, hxz⟩
      have hx : x = z := e.injective (hxz.trans (hefix z hz).symm)
      exact hx ▸ hxU

theorem actual_common_base_loop_opposite_side_nested
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hmeet : a.val.image ∩ b.val.image = {a.val.map 0})
    (A : MarkedLoopDiscDecomposition a.val)
    (B : MarkedLoopDiscDecomposition b.val)
    (i j : Fin 2) (hij : i ≠ j)
    (hbi : b.val.image \ {a.val.map 0} ⊆ A.side i) :
    ∃ k : Fin 2, A.side j ⊆ B.side k ∧
      a.val.image \ {a.val.map 0} ⊆ B.side k := by
  have hAij : Disjoint (A.side i) (A.side j) := by
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact A.disjoint
    · exact A.disjoint.symm
    · exact False.elim (hij rfl)
  have hAjavoid : A.side j ⊆ b.val.imageᶜ := by
    intro x hxj hxb
    by_cases he : x = a.val.map 0
    · exact (A.discs j).component.2.2.1 hxj
        (he ▸ Set.mem_range_self (0 : Interval))
    · exact Set.disjoint_left.mp hAij (hbi ⟨hxb, by simpa using he⟩) hxj
  obtain ⟨x, hxj⟩ := (A.discs j).component.1
  let C := connectedComponentIn b.val.imageᶜ x
  have hC : IsComplementComponent b.val.image C :=
    complementComponent_iff_componentIn.mpr ⟨x, hAjavoid hxj, rfl⟩
  obtain ⟨k, hk⟩ := (B.all_components C).mp hC
  have hAjB : A.side j ⊆ B.side k := by
    rw [← hk]
    exact (A.discs j).component.2.1.isPreconnected.subset_connectedComponentIn hxj hAjavoid
  refine ⟨k, hAjB, ?_⟩
  intro y hy
  have hyclA : y ∈ closure (A.side j) := by
    apply frontier_subset_closure
    rw [(A.discs j).boundary]
    exact hy.1
  have hyclB : y ∈ closure (B.side k) := closure_mono hAjB hyclA
  rw [(B.discs k).closure_eq] at hyclB
  rcases hyclB with hyB | hyb
  · exact hyB
  · have hybase : y ∈ ({a.val.map 0} : Set S) := hmeet ▸ ⟨hy.1, hyb⟩
    exact False.elim (hy.2 hybase)

theorem actual_same_class_common_base_between_region_mark_free
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) b)
    (hmeet : a.val.image ∩ b.val.image = {a.val.map 0})
    (A : MarkedLoopDiscDecomposition a.val)
    (B : MarkedLoopDiscDecomposition b.val)
    (i j : Fin 2) (hij : i ≠ j)
    (hbi : b.val.image \ {a.val.map 0} ⊆ A.side i) :
    ∃ k : Fin 2, A.side j ⊆ B.side k ∧
      a.val.image \ {a.val.map 0} ⊆ B.side k ∧
      Disjoint (A.side i ∩ B.side k) (M.cover.branch : Set S) := by
  obtain ⟨k, hAjB, hak⟩ :=
    actual_common_base_loop_opposite_side_nested M a b hmeet A B i j hij hbi
  obtain ⟨V, hV, hpattern⟩ :=
    actual_same_class_complement_side_mark_pattern M a b hclass
      (A.side i) (A.discs i).component
  obtain ⟨m, hm⟩ := (B.all_components V).mp hV
  have hmink : m ≠ k := by
    intro he
    have hess : ∃ z, z ∈ M.cover.branch ∧ z ∈ A.side j := by
      rcases a.property with hn | hregions
      · exact False.elim (hn ha)
      · exact hregions _ (A.discs j).component
    obtain ⟨z, hz, hzj⟩ := hess
    have hzk : z ∈ B.side k := hAjB hzj
    have hzV : z ∈ V := hm.symm ▸ (he.symm ▸ hzk)
    have hzi : z ∈ A.side i := (hpattern z hz).mpr hzV
    have hdis : Disjoint (A.side i) (A.side j) := by
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · exact A.disjoint
      · exact A.disjoint.symm
      · exact False.elim (hij rfl)
    exact Set.disjoint_left.mp hdis hzi hzj
  have hBmk : Disjoint (B.side m) (B.side k) := by
    fin_cases m <;> fin_cases k
    · exact False.elim (hmink rfl)
    · exact B.disjoint
    · exact B.disjoint.symm
    · exact False.elim (hmink rfl)
  refine ⟨k, hAjB, hak, ?_⟩
  apply Set.disjoint_left.mpr
  intro z hzU hzmark
  have hzm : z ∈ B.side m := hm ▸ (hpattern z hzmark).mp hzU.1
  exact Set.disjoint_left.mp hBmk hzm hzU.2

theorem actual_jordan_opposite_side_eq_compl_closure
    (M : HyperellipticModel E S) (b : EssentialMarkedArc M)
    (B : MarkedLoopDiscDecomposition b.val)
    (k m : Fin 2) (hkm : k ≠ m) :
    B.side k = (closure (B.side m))ᶜ := by
  rw [(B.discs m).closure_eq]
  have hdis : Disjoint (B.side k) (B.side m) := by
    fin_cases k <;> fin_cases m
    · exact False.elim (hkm rfl)
    · exact B.disjoint
    · exact B.disjoint.symm
    · exact False.elim (hkm rfl)
  ext x
  constructor
  · intro hx hxother
    rcases hxother with hxside | hximage
    · exact Set.disjoint_left.mp hdis hx hxside
    · exact (B.discs k).component.2.2.1 hx hximage
  · intro hx
    have hcomp : x ∈ b.val.imageᶜ := by
      intro hxb
      exact hx (Or.inr hxb)
    have hsides : x ∈ B.side 0 ∪ B.side 1 := B.complement ▸ hcomp
    fin_cases k <;> fin_cases m
    · exact False.elim (hkm rfl)
    · exact hsides.resolve_right (fun hm => hx (Or.inl hm))
    · exact hsides.resolve_left (fun hm => hx (Or.inl hm))
    · exact False.elim (hkm rfl)

theorem actual_common_base_between_frontier_subset
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (A : MarkedLoopDiscDecomposition a.val)
    (B : MarkedLoopDiscDecomposition b.val)
    (i k : Fin 2) :
    frontier (A.side i ∩ B.side k) ⊆ a.val.image ∪ b.val.image := by
  intro x hx
  rcases frontier_inter_subset (A.side i) (B.side k) hx with hxa | hxb
  · exact Or.inl ((A.discs i).boundary ▸ hxa.1)
  · exact Or.inr ((B.discs k).boundary ▸ hxb.2)

theorem actual_common_base_between_nonempty
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hb : b.val.map 0 = b.val.map 1)
    (hbase : a.val.map 0 = b.val.map 0)
    (A : MarkedLoopDiscDecomposition a.val)
    (B : MarkedLoopDiscDecomposition b.val)
    (i k : Fin 2)
    (hbi : b.val.image \ {a.val.map 0} ⊆ A.side i) :
    (A.side i ∩ B.side k).Nonempty := by
  obtain ⟨x, hx⟩ := (loop_image_remove_base_connected M b.val hb).nonempty
  have hxAi : x ∈ A.side i := hbi (by simpa only [hbase] using hx)
  have hxfront : x ∈ frontier (B.side k) := by
    rw [(B.discs k).boundary]
    exact hx.1
  obtain ⟨y, hyAi, hyBk⟩ := Set.Nonempty.of_closure
    ⟨x, (A.discs i).open_side.inter_closure ⟨hxAi, frontier_subset_closure hxfront⟩⟩
  exact ⟨y, hyAi, hyBk⟩

theorem actual_common_base_between_frontier_eq
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (A : MarkedLoopDiscDecomposition a.val)
    (B : MarkedLoopDiscDecomposition b.val)
    (i k : Fin 2)
    (hbi : b.val.image \ {a.val.map 0} ⊆ A.side i)
    (hak : a.val.image \ {a.val.map 0} ⊆ B.side k) :
    frontier (A.side i ∩ B.side k) = a.val.image ∪ b.val.image := by
  let U := A.side i ∩ B.side k
  have hcl_inter_left {P Q : Set S} (hQ : IsOpen Q)
      {x : S} (hxP : x ∈ closure P) (hxQ : x ∈ Q) :
      x ∈ closure (P ∩ Q) := by
    apply mem_closure_iff.mpr
    intro O hO hxO
    obtain ⟨y, ⟨hyO, hyQ⟩, hyP⟩ :=
      mem_closure_iff.mp hxP (O ∩ Q) (hO.inter hQ) ⟨hxO,hxQ⟩
    exact ⟨y, hyO, ⟨hyP,hyQ⟩⟩
  have ha_closure (x : S) (hx : x ∈ a.val.image \ {a.val.map 0}) : x ∈ closure U := by
    have hxAi : x ∈ closure (A.side i) := by
      apply frontier_subset_closure
      rw [(A.discs i).boundary]
      exact hx.1
    exact hcl_inter_left (B.discs k).open_side hxAi (hak hx)
  have hb_closure (x : S) (hx : x ∈ b.val.image \ {a.val.map 0}) : x ∈ closure U := by
    have hxBk : x ∈ closure (B.side k) := by
      apply frontier_subset_closure
      rw [(B.discs k).boundary]
      exact hx.1
    change x ∈ closure (A.side i ∩ B.side k)
    rw [Set.inter_comm]
    exact hcl_inter_left (A.discs i).open_side hxBk (hbi hx)
  have hbase_closure : a.val.map 0 ∈ closure U := by
    have h0 : (0 : Interval) ∈ closure (Set.Ioo (0 : Interval) 1) := by
      rw [closure_Ioo (by norm_num : (0 : Interval) ≠ 1)]
      exact ⟨le_rfl,zero_le_one⟩
    have hmapcl : a.val.map 0 ∈ closure (a.val.map '' Set.Ioo (0 : Interval) 1) :=
      image_closure_subset_closure_image a.val.continuous ⟨0,h0,rfl⟩
    have hsub : a.val.map '' Set.Ioo (0 : Interval) 1 ⊆ closure U := by
      rintro x ⟨t, ht, rfl⟩
      have hnotbase : a.val.map t ≠ a.val.map 0 := by
        intro he
        rcases a.val.injective_except_loop_closure t 0 he with hh | hh | hh
        · exact (ne_of_gt ht.1) hh
        · exact (ne_of_gt ht.1) hh.1
        · exact (ne_of_lt ht.2) hh.1
      exact ha_closure _ ⟨⟨t,rfl⟩, by simpa using hnotbase⟩
    have hc : closure (closure U) = closure U :=
      (isClosed_closure : IsClosed (closure U)).closure_eq
    exact hc ▸ closure_mono hsub hmapcl
  apply Set.Subset.antisymm
  · exact actual_common_base_between_frontier_subset M a b A B i k
  · intro x hx
    have hUopen : IsOpen U := (A.discs i).open_side.inter (B.discs k).open_side
    have hxnotU : x ∉ U := by
      rcases hx with hxa | hxb
      · exact fun h => (A.discs i).component.2.2.1 h.1 hxa
      · exact fun h => (B.discs k).component.2.2.1 h.2 hxb
    rw [hUopen.frontier_eq]
    refine ⟨?_, hxnotU⟩
    rcases hx with hxa | hxb
    · by_cases he : x = a.val.map 0
      · exact he ▸ hbase_closure
      · exact ha_closure x ⟨hxa, by simpa using he⟩
    · by_cases he : x = a.val.map 0
      · exact he ▸ hbase_closure
      · exact hb_closure x ⟨hxb, by simpa using he⟩

theorem actual_same_class_zero_contact_markfree_between_region
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) b)
    (hzero : ArcSurgery.crossings M a b = ∅) :
    ∃ U : Set S, IsOpen U ∧ U.Nonempty ∧
      Disjoint U (M.cover.branch : Set S) ∧
      frontier U = a.val.image ∪ b.val.image := by
  have hb : b.val.map 0 = b.val.map 1 :=
    (actual_same_class_loop_closure_invariant M a b hclass).mp ha
  have hbase : a.val.map 0 = b.val.map 0 :=
    actual_same_class_loop_literal_base M a b ha hclass
  have hmeet := actual_zero_contact_same_class_loop_intersection M a b ha hclass hzero
  obtain ⟨A⟩ := markedLoop_disc_decomposition_exists M a.val ha
  obtain ⟨B⟩ := markedLoop_disc_decomposition_exists M b.val hb
  obtain ⟨i, hbi⟩ := actual_common_base_loop_other_trace_one_side M a b hb hbase hmeet A
  let j : Fin 2 := if i = 0 then 1 else 0
  have hij : i ≠ j := by fin_cases i <;> simp [j]
  obtain ⟨k, _hAjB, hak, hfree⟩ :=
    actual_same_class_common_base_between_region_mark_free M a b ha hclass hmeet
      A B i j hij hbi
  let U := A.side i ∩ B.side k
  refine ⟨U, (A.discs i).open_side.inter (B.discs k).open_side, ?_, hfree, ?_⟩
  · exact actual_common_base_between_nonempty M a b hb hbase A B i k hbi
  · exact actual_common_base_between_frontier_eq M a b A B i k hbi hak

theorem actual_connected_trace_avoids_open_region
    (C U : Set S) (hC : IsConnected C) (hU : IsOpen U)
    (hfront : Disjoint C (frontier U))
    (hout : ∃ x ∈ C, x ∉ U) : Disjoint C U := by
  have hcover : C ⊆ U ∪ (closure U)ᶜ := by
    intro x hx
    by_cases hxu : x ∈ U
    · exact Or.inl hxu
    · exact Or.inr (by
        intro hxc
        exact Set.disjoint_left.mp hfront hx ((hU.frontier_eq).symm ▸ ⟨hxc,hxu⟩))
  have hdis : Disjoint U (closure U)ᶜ :=
    Set.disjoint_left.mpr (fun x hxU hxC => hxC (subset_closure hxU))
  rcases hC.isPreconnected.subset_or_subset hU isClosed_closure.isOpen_compl
      hdis hcover with hin | houtside
  · obtain ⟨x,hxC,hxU⟩ := hout
    exact False.elim (hxU (hin hxC))
  · exact Set.disjoint_left.mpr (fun x hxC hxU => houtside hxC (subset_closure hxU))

theorem actual_marked_arc_avoids_markfree_region_of_second_mark
    (M : HyperellipticModel E S) (c : MarkedArc M) (base : S)
    (hbase : base ∈ M.cover.branch) (U : Set S) (hU : IsOpen U)
    (hfree : Disjoint U (M.cover.branch : Set S))
    (hfront : Disjoint (c.image \ {base}) (frontier U))
    (hsecond : ∃ z ∈ c.image \ {base}, z ∈ M.cover.branch) :
    Disjoint (c.image \ {base}) U := by
  apply actual_connected_trace_avoids_open_region
    (c.image \ {base}) U (markedArc_image_remove_mark_connected M c base hbase)
    hU hfront
  obtain ⟨z,hzc,hzm⟩ := hsecond
  exact ⟨z,hzc,fun hzU => Set.disjoint_left.mp hfree hzU hzm⟩

theorem actual_tangent_nested_jordan_between_connected
    (C : Set Schoenflies.Plane) (hC : Schoenflies.IsJordanCurve C)
    (f : ℝ → Schoenflies.Plane) (hf : Schoenflies.IsLoop f)
    (hbaseC : f 0 ∈ C)
    (hinner : (f '' Set.Icc (0 : ℝ) 1) \ {f 0} ⊆ Schoenflies.inside C)
    (hother : (C \ {f 0}).Nonempty) :
    IsConnected (Schoenflies.inside C ∩
      Schoenflies.outside (f '' Set.Icc (0 : ℝ) 1)) := by
  let K := f '' Set.Icc (0 : ℝ) 1
  have hK : Schoenflies.IsJordanCurve K := ⟨f,hf,rfl⟩
  have hCs := Schoenflies.jordan_curve_theorem hC
  have hKs := Schoenflies.jordan_curve_theorem hK
  have hbaseK : f 0 ∈ K := ⟨0,Schoenflies.zero_mem_I,rfl⟩
  have hKcl : K ⊆ Schoenflies.inside C ∪ C := by
    intro z hz
    by_cases he : z = f 0
    · exact Or.inr (he ▸ hbaseC)
    · exact Or.inl (hinner ⟨hz,by simpa using he⟩)
  have hinside : Schoenflies.inside K ⊆ Schoenflies.inside C :=
    CurveComplex.jordan_inside_mono_of_boundary_subset_closed_inside hCs hKs hKcl
  have hmiddle : f '' Set.Ioo (0 : ℝ) 1 ⊆ Schoenflies.inside C := by
    rintro z ⟨t,ht,rfl⟩
    apply hinner
    refine ⟨⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩,?_⟩
    intro he
    have ht0 : t = 0 := hf.injOn ⟨ht.1.le,ht.2⟩ ⟨le_rfl,zero_lt_one⟩
      (Set.mem_singleton_iff.mp he)
    exact (ne_of_gt ht.1) ht0
  have hbaseout : f 0 ∉ Schoenflies.inside C :=
    fun he => Schoenflies.inside_subset_compl he hbaseC
  obtain ⟨_x0,_hx0,_y0,_hy0,_hne0,hcov⟩ :=
    Schoenflies.actual_loop_domain_exact_two hf hCs.isOpen_inside
      hCs.isConnected_inside hbaseout hmiddle
  let A : Set Schoenflies.Plane := Schoenflies.inside C \ K
  obtain ⟨x,hxI⟩ := hKs.isConnected_inside.nonempty
  have hxA : x ∈ A := ⟨hinside hxI,Schoenflies.inside_subset_compl hxI⟩
  obtain ⟨q,hqC,hqne⟩ := hother
  have hqnotK : q ∉ K := by
    intro hqK
    by_cases he : q = f 0
    · exact hqne (by simpa using he)
    · exact Schoenflies.inside_subset_compl (hinner ⟨hqK,by simpa using he⟩) hqC
  have hqnotI : q ∉ Schoenflies.inside K :=
    fun he => Schoenflies.inside_subset_compl (hinside he) hqC
  have hqO : q ∈ Schoenflies.outside K := by
    have hcover : q ∈ Schoenflies.inside K ∪ Schoenflies.outside K := by
      rw [Schoenflies.inside_union_outside]
      exact hqnotK
    exact hcover.resolve_left hqnotI
  have hqcl : q ∈ closure (Schoenflies.inside C) := by
    apply frontier_subset_closure
    rw [hCs.frontier_inside]
    exact hqC
  obtain ⟨y,hyO,hyI⟩ := mem_closure_iff.mp hqcl (Schoenflies.outside K)
    hKs.isOpen_outside hqO
  have hyA : y ∈ A := ⟨hyI,Schoenflies.outside_subset_compl hyO⟩
  have hxi : connectedComponentIn A x ⊆ Schoenflies.inside K := by
    have hs : connectedComponentIn A x ⊆ connectedComponentIn Kᶜ x :=
      (isConnected_connectedComponentIn_iff.mpr hxA).isPreconnected.subset_connectedComponentIn
        (mem_connectedComponentIn hxA) (fun z hz => (connectedComponentIn_subset _ _ hz).2)
    rwa [hKs.connectedComponentIn_eq_inside hxI] at hs
  have hyo : connectedComponentIn A y ⊆ Schoenflies.outside K := by
    have hs : connectedComponentIn A y ⊆ connectedComponentIn Kᶜ y :=
      (isConnected_connectedComponentIn_iff.mpr hyA).isPreconnected.subset_connectedComponentIn
        (mem_connectedComponentIn hyA) (fun z hz => (connectedComponentIn_subset _ _ hz).2)
    rwa [hKs.connectedComponentIn_eq_outside hyO] at hs
  have hne : connectedComponentIn A x ≠ connectedComponentIn A y := by
    intro he
    exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside
      (hxi (he.symm ▸ mem_connectedComponentIn hyA)) hyO
  have hcover := Schoenflies.covered_by_two_components_of_ne hcov hxA hyA hne
  have heq : Schoenflies.inside C ∩ Schoenflies.outside K = connectedComponentIn A y := by
    apply Set.Subset.antisymm
    · intro z hz
      have hzA : z ∈ A := ⟨hz.1,Schoenflies.outside_subset_compl hz.2⟩
      rcases hcover z hzA with hzX | hzY
      · exact False.elim (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside
          (hxi hzX) hz.2)
      · exact hzY
    · intro z hz
      exact ⟨(connectedComponentIn_subset _ _ hz).1,hyo hz⟩
  rw [heq]
  exact isConnected_connectedComponentIn_iff.mpr hyA

theorem actual_component_subset_open_of_frontier_disjoint
    (D V : Set S) (hV : IsOpen V) (hVD : V ⊆ D)
    (hfront : Disjoint (frontier V) D) {x : S} (hx : x ∈ V) :
    connectedComponentIn D x ⊆ V := by
  have hxD : x ∈ D := hVD hx
  have hC : IsConnected (connectedComponentIn D x) :=
    isConnected_connectedComponentIn_iff.mpr hxD
  apply hC.isPreconnected.subset_of_closure_inter_subset hV
    ⟨x,mem_connectedComponentIn hxD,hx⟩
  rintro y ⟨hycl,hyC⟩
  by_contra hyV
  have hyfront : y ∈ frontier V := by
    rw [hV.frontier_eq]
    exact ⟨hycl,hyV⟩
  exact Set.disjoint_left.mp hfront hyfront (connectedComponentIn_subset _ _ hyC)

theorem actual_two_component_open_partition_connected
    (D V W : Set S) (F : Finset (Set S))
    (hD : D = V ∪ W) (hV : IsOpen V) (hW : IsOpen W)
    (hdis : Disjoint V W) (hVconn : IsConnected V) (hWnonempty : W.Nonempty)
    (hFcard : F.card = 2)
    (hF : ∀ C : Set S, IsComplementComponent Dᶜ C ↔ C ∈ F) :
    IsConnected W := by
  have hVsub : V ⊆ D := fun x hx => hD.symm ▸ Or.inl hx
  have hWsub : W ⊆ D := fun x hx => hD.symm ▸ Or.inr hx
  have hVcl : closure V ⊆ Wᶜ :=
    closure_minimal (fun x hxV hxW => Set.disjoint_left.mp hdis hxV hxW)
      hW.isClosed_compl
  have hWcl : closure W ⊆ Vᶜ :=
    closure_minimal (fun x hxW hxV => Set.disjoint_left.mp hdis hxV hxW)
      hV.isClosed_compl
  have hVfront : Disjoint (frontier V) D := by
    apply Set.disjoint_left.mpr
    intro x hxfront hxD
    rcases hD ▸ hxD with hxV | hxW
    · rw [hV.frontier_eq] at hxfront
      exact hxfront.2 hxV
    · exact hVcl (frontier_subset_closure hxfront) hxW
  have hWfront : Disjoint (frontier W) D := by
    apply Set.disjoint_left.mpr
    intro x hxfront hxD
    rcases hD ▸ hxD with hxV | hxW
    · exact hWcl (frontier_subset_closure hxfront) hxV
    · rw [hW.frontier_eq] at hxfront
      exact hxfront.2 hxW
  obtain ⟨x,hx⟩ := hVconn.nonempty
  obtain ⟨y,hy⟩ := hWnonempty
  have hxD : x ∈ D := hVsub hx
  have hyD : y ∈ D := hWsub hy
  let CX := connectedComponentIn D x
  let CY := connectedComponentIn D y
  have hCXsub : CX ⊆ V := actual_component_subset_open_of_frontier_disjoint
    D V hV hVsub hVfront hx
  have hCYsub : CY ⊆ W := actual_component_subset_open_of_frontier_disjoint
    D W hW hWsub hWfront hy
  have hCXcomp : IsComplementComponent Dᶜ CX := by
    apply complementComponent_iff_componentIn.mpr
    refine ⟨x,by simpa using hxD,?_⟩
    simp [CX]
  have hCYcomp : IsComplementComponent Dᶜ CY := by
    apply complementComponent_iff_componentIn.mpr
    refine ⟨y,by simpa using hyD,?_⟩
    simp [CY]
  have hCXmem : CX ∈ F := (hF CX).mp hCXcomp
  have hCYmem : CY ∈ F := (hF CY).mp hCYcomp
  have hne : CX ≠ CY := by
    intro he
    exact Set.disjoint_left.mp hdis
      (hCXsub (he ▸ mem_connectedComponentIn hyD)) hy
  have hFpair : F = {CX,CY} := by
    have hsub : ({CX,CY} : Finset (Set S)) ⊆ F := by
      intro Z hZ
      simp only [Finset.mem_insert,Finset.mem_singleton] at hZ
      rcases hZ with he | he
      · exact he ▸ hCXmem
      · exact he ▸ hCYmem
    have hpaircard : ({CX,CY} : Finset (Set S)).card = 2 := by simp [hne]
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hWsubCY : W ⊆ CY := by
    intro z hz
    have hzD : z ∈ D := hWsub hz
    let CZ := connectedComponentIn D z
    have hCZcomp : IsComplementComponent Dᶜ CZ := by
      apply complementComponent_iff_componentIn.mpr
      refine ⟨z,by simpa using hzD,?_⟩
      simp [CZ]
    have hCZmem : CZ ∈ F := (hF CZ).mp hCZcomp
    have hCZne : CZ ≠ CX := by
      intro he
      exact Set.disjoint_left.mp hdis (hCXsub (he.symm ▸ mem_connectedComponentIn hzD)) hz
    have hCZeq : CZ = CY := by
      have hh : CZ = CX ∨ CZ = CY := by
        simpa only [hFpair,Finset.mem_insert,Finset.mem_singleton] using hCZmem
      exact hh.resolve_left hCZne
    exact hCZeq ▸ mem_connectedComponentIn hzD
  have hWeq : W = CY := Set.Subset.antisymm hWsubCY hCYsub
  rw [hWeq]
  exact isConnected_connectedComponentIn_iff.mpr hyD

theorem actual_common_base_between_region_connected
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hb : b.val.map 0 = b.val.map 1)
    (hbase : a.val.map 0 = b.val.map 0)
    (A : MarkedLoopDiscDecomposition a.val)
    (B : MarkedLoopDiscDecomposition b.val)
    (i j k : Fin 2) (hij : i ≠ j)
    (hbi : b.val.image \ {a.val.map 0} ⊆ A.side i)
    (hAjB : A.side j ⊆ B.side k)
    (hak : a.val.image \ {a.val.map 0} ⊆ B.side k) :
    IsConnected (A.side i ∩ B.side k) := by
  let m : Fin 2 := if k = 0 then 1 else 0
  have hmk : m ≠ k := by fin_cases k <;> simp [m]
  have hBdis : Disjoint (B.side m) (B.side k) := by
    fin_cases k
    · simpa [m] using B.disjoint.symm
    · simpa [m] using B.disjoint
  have hAdis : Disjoint (A.side i) (A.side j) := by
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact A.disjoint
    · exact A.disjoint.symm
    · exact False.elim (hij rfl)
  have hBmavoida : B.side m ⊆ a.val.imageᶜ := by
    intro x hxm hxa
    by_cases he : x = a.val.map 0
    · have hxb : x ∈ b.val.image := he ▸ hbase ▸ Set.mem_range_self (0 : Interval)
      exact (B.discs m).component.2.2.1 hxm hxb
    · exact Set.disjoint_left.mp hBdis hxm (hak ⟨hxa,by simpa using he⟩)
  have hBmcover : B.side m ⊆ A.side i ∪ A.side j := by
    intro x hx
    have hh : x ∈ A.side 0 ∪ A.side 1 := A.complement ▸ hBmavoida hx
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hh
    · exact hh.symm
    · exact False.elim (hij rfl)
  have hBmAi : B.side m ⊆ A.side i := by
    rcases (B.discs m).component.2.1.isPreconnected.subset_or_subset
        (A.discs i).open_side (A.discs j).open_side hAdis hBmcover with hh | hh
    · exact hh
    · obtain ⟨x,hxm⟩ := (B.discs m).component.1
      exact False.elim (Set.disjoint_left.mp hBdis hxm (hAjB (hh hxm)))
  let D := A.side i \ b.val.image
  let V := B.side m
  let W := A.side i ∩ B.side k
  have hDpartition : D = V ∪ W := by
    have hBsides : b.val.imageᶜ = B.side m ∪ B.side k := by
      rw [← B.complement]
      fin_cases k
      · simp [m,Set.union_comm]
      · simp [m]
    ext x
    constructor
    · intro hx
      have hxside : x ∈ B.side m ∪ B.side k := hBsides ▸ hx.2
      rcases hxside with hxm | hxk
      · exact Or.inl hxm
      · exact Or.inr ⟨hx.1,hxk⟩
    · intro hx
      rcases hx with hxm | hxW
      · exact ⟨hBmAi hxm,(B.discs m).component.2.2.1 hxm⟩
      · exact ⟨hxW.1,(B.discs k).component.2.2.1 hxW.2⟩
  have hbaseout : b.val.map 0 ∉ A.side i := by
    rw [← hbase]
    exact fun hh => (A.discs i).component.2.2.1 hh (Set.mem_range_self (0 : Interval))
  have hinter : arcInterior M b ⊆ A.side i := by
    intro x hx
    apply hbi
    refine ⟨hx.1,?_⟩
    intro he
    exact hx.2 ((Set.mem_singleton_iff.mp he) ▸ a.val.start_marked)
  obtain ⟨F,hFcard,hF⟩ := actual_loop_domain_split_faces M b hb
    (A.discs i).open_side (A.discs i).component.2.1 hbaseout hinter
  have hF' : ∀ C : Set S, IsComplementComponent Dᶜ C ↔ C ∈ F := by
    intro C
    have heq : Dᶜ = (A.side i)ᶜ ∪ b.val.image := by
      ext x
      by_cases hxAi : x ∈ A.side i <;>
        by_cases hxb : x ∈ b.val.image <;> simp [D,hxAi,hxb]
    rw [heq]
    exact hF C
  have hWnonempty : W.Nonempty := by
    change (A.side i ∩ B.side k).Nonempty
    exact actual_common_base_between_nonempty M a b hb hbase A B i k hbi
  exact actual_two_component_open_partition_connected D V W F hDpartition
    (B.discs m).open_side ((A.discs i).open_side.inter (B.discs k).open_side)
    (Set.disjoint_left.mpr (fun x hxm hxW => Set.disjoint_left.mp hBdis hxm hxW.2))
    (B.discs m).component.2.1 hWnonempty hFcard hF'

theorem actual_same_class_zero_contact_markfree_between_face
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) b)
    (hzero : ArcSurgery.crossings M a b = ∅) :
    ∃ U : Set S, IsOpen U ∧ IsConnected U ∧
      Disjoint U (M.cover.branch : Set S) ∧
      frontier U = a.val.image ∪ b.val.image := by
  have hb : b.val.map 0 = b.val.map 1 :=
    (actual_same_class_loop_closure_invariant M a b hclass).mp ha
  have hbase : a.val.map 0 = b.val.map 0 :=
    actual_same_class_loop_literal_base M a b ha hclass
  have hmeet := actual_zero_contact_same_class_loop_intersection M a b ha hclass hzero
  obtain ⟨A⟩ := markedLoop_disc_decomposition_exists M a.val ha
  obtain ⟨B⟩ := markedLoop_disc_decomposition_exists M b.val hb
  obtain ⟨i,hbi⟩ := actual_common_base_loop_other_trace_one_side M a b hb hbase hmeet A
  let j : Fin 2 := if i = 0 then 1 else 0
  have hij : i ≠ j := by fin_cases i <;> simp [j]
  obtain ⟨k,hAjB,hak,hfree⟩ :=
    actual_same_class_common_base_between_region_mark_free M a b ha hclass hmeet
      A B i j hij hbi
  refine ⟨A.side i ∩ B.side k,
    (A.discs i).open_side.inter (B.discs k).open_side, ?_,hfree,?_⟩
  · exact actual_common_base_between_region_connected M a b hb hbase A B
      i j k hij hbi hAjB hak
  · exact actual_common_base_between_frontier_eq M a b A B i k hbi hak

theorem actual_open_connected_region_is_complement_component
    (G U : Set S) (hU : IsOpen U) (hconn : IsConnected U)
    (hsub : U ⊆ Gᶜ) (hfront : frontier U ⊆ G) :
    IsComplementComponent G U := by
  refine ⟨hconn.nonempty,hconn,hsub,?_⟩
  intro V hV hUV hVG
  have hcl : closure U ∩ V ⊆ U := by
    intro x hx
    by_contra hn
    have hxf : x ∈ frontier U := by
      rw [hU.frontier_eq]
      exact ⟨hx.1,hn⟩
    exact hVG hx.2 (hfront hxf)
  have hVU : V ⊆ U := hV.isPreconnected.subset_of_closure_inter_subset hU
    (by obtain ⟨x,hx⟩ := hconn.nonempty; exact ⟨x,hUV hx,hx⟩) hcl
  exact Set.Subset.antisymm hVU hUV

theorem actual_same_class_zero_contact_markfree_between_component
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) b)
    (hzero : ArcSurgery.crossings M a b = ∅) :
    ∃ U : Set S, IsComplementComponent (a.val.image ∪ b.val.image) U ∧
      Disjoint U (M.cover.branch : Set S) ∧
      frontier U = a.val.image ∪ b.val.image := by
  have hb : b.val.map 0 = b.val.map 1 :=
    (actual_same_class_loop_closure_invariant M a b hclass).mp ha
  have hbase : a.val.map 0 = b.val.map 0 :=
    actual_same_class_loop_literal_base M a b ha hclass
  have hmeet := actual_zero_contact_same_class_loop_intersection M a b ha hclass hzero
  obtain ⟨A⟩ := markedLoop_disc_decomposition_exists M a.val ha
  obtain ⟨B⟩ := markedLoop_disc_decomposition_exists M b.val hb
  obtain ⟨i,hbi⟩ := actual_common_base_loop_other_trace_one_side M a b hb hbase hmeet A
  let j : Fin 2 := if i = 0 then 1 else 0
  have hij : i ≠ j := by fin_cases i <;> simp [j]
  obtain ⟨k,hAjB,hak,hfree⟩ :=
    actual_same_class_common_base_between_region_mark_free M a b ha hclass hmeet
      A B i j hij hbi
  let U := A.side i ∩ B.side k
  have hUopen : IsOpen U := (A.discs i).open_side.inter (B.discs k).open_side
  have hUconn : IsConnected U :=
    actual_common_base_between_region_connected M a b hb hbase A B
      i j k hij hbi hAjB hak
  have hUsub : U ⊆ (a.val.image ∪ b.val.image)ᶜ := by
    intro x hx hxab
    rcases hxab with hxa | hxb
    · exact (A.discs i).component.2.2.1 hx.1 hxa
    · exact (B.discs k).component.2.2.1 hx.2 hxb
  have hfront := actual_common_base_between_frontier_eq M a b A B i k hbi hak
  refine ⟨U,actual_open_connected_region_is_complement_component
    (a.val.image ∪ b.val.image) U hUopen hUconn hUsub ?_,hfree,hfront⟩
  rw [hfront]

theorem actual_nonloop_marked_arc_avoids_markfree_face
    (M : HyperellipticModel E S) (c : MarkedArc M) (base : S)
    (hbase : base ∈ M.cover.branch)
    (hnonloop : c.map 0 ≠ c.map 1)
    (U : Set S) (hU : IsOpen U)
    (hfree : Disjoint U (M.cover.branch : Set S))
    (hfront : Disjoint (c.image \ {base}) (frontier U)) :
    Disjoint c.image U := by
  have hsecond : ∃ z ∈ c.image \ {base}, z ∈ M.cover.branch := by
    by_cases hstart : c.map 0 = base
    · refine ⟨c.map 1,⟨Set.mem_range_self 1,?_⟩,c.end_marked⟩
      intro he
      exact hnonloop (hstart.trans (Set.mem_singleton_iff.mp he).symm)
    · refine ⟨c.map 0,⟨Set.mem_range_self 0,?_⟩,c.start_marked⟩
      intro he
      exact hstart (Set.mem_singleton_iff.mp he)
  have havoid := actual_marked_arc_avoids_markfree_region_of_second_mark
    M c base hbase U hU hfree hfront hsecond
  apply Set.disjoint_left.mpr
  intro x hxc hxU
  by_cases he : x = base
  · exact Set.disjoint_left.mp hfree hxU (he ▸ hbase)
  · exact Set.disjoint_left.mp havoid ⟨hxc,by simpa using he⟩ hxU

theorem actual_selected_nonloop_graph_object_avoids_between_face
    (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
    (rT : {w // w ∈ T.val} → EssentialMarkedArc M)
    (hdT : ∀ w z, w ≠ z → Disjoint (arcInterior M (rT w)) (arcInterior M (rT z)))
    (F J : Finset (EssentialArcClass M)) (hTF : T.val ⊆ F) (hJT : J ⊆ T.val)
    (r0 : {w // w ∈ F} → EssentialMarkedArc M)
    (hd0 : ∀ w z, w ≠ z → Disjoint (arcInterior M (r0 w)) (arcInterior M (r0 z)))
    (haligned0 : ∀ w : {w // w ∈ T.val}, w.val ∈ J →
      r0 ⟨w.val, hTF w.property⟩ = rT w)
    (r : {w // w ∈ F} → EssentialMarkedArc M)
    (hgraph : actualObjectTrace M r0 J = actualObjectTrace M r J)
    (u : {w // w ∈ T.val}) (hu : u.val ∉ J)
    (hloop : (r0 ⟨u.val, hTF u.property⟩).val.map 0 =
      (r0 ⟨u.val, hTF u.property⟩).val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M)
      (r0 ⟨u.val, hTF u.property⟩) =
      Quotient.mk (essentialArcSetoid M) (rT u))
    (U : Set S) (hU : IsOpen U)
    (hfree : Disjoint U (M.cover.branch : Set S))
    (hfront : frontier U =
      (r0 ⟨u.val, hTF u.property⟩).val.image ∪ (rT u).val.image)
    (v : {w // w ∈ F}) (hv : v.val ∈ J)
    (hnonloop : (r0 v).val.map 0 ≠ (r0 v).val.map 1) :
    Disjoint (r0 v).val.image U := by
  let base := (r0 ⟨u.val,hTF u.property⟩).val.map 0
  have hbase : base ∈ M.cover.branch :=
    (r0 ⟨u.val,hTF u.property⟩).val.start_marked
  have hfrontdis : Disjoint ((r0 v).val.image \ {base}) (frontier U) := by
    apply Set.disjoint_left.mpr
    intro x hxv hxf
    have hxbound : x ∈ (r0 ⟨u.val,hTF u.property⟩).val.image ∪
        (rT u).val.image := hfront ▸ hxf
    have hxn : x ∉ actualObjectTrace M r J :=
      actual_selected_loop_boundaries_avoid_original_graph M p T rT hdT F J
        hTF hJT r0 hd0 haligned0 r hgraph u hu hloop hclass x hxbound
        (by intro he; exact hxv.2 (by simpa [base] using he))
    have hxg : x ∈ actualObjectTrace M r J := by
      rw [← hgraph]
      exact Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨hv,hxv.1⟩⟩
    exact hxn hxg
  exact actual_nonloop_marked_arc_avoids_markfree_face M (r0 v).val base
    hbase hnonloop U hU hfree hfrontdis

theorem actual_connected_trace_face_dichotomy
    (C U : Set S) (hC : IsConnected C) (hU : IsOpen U)
    (hfront : Disjoint C (frontier U)) :
    C ⊆ U ∨ Disjoint C U := by
  by_cases hsub : C ⊆ U
  · exact Or.inl hsub
  · obtain ⟨x,hxC,hxU⟩ := Set.not_subset.mp hsub
    exact Or.inr (actual_connected_trace_avoids_open_region C U hC hU hfront
      ⟨x,hxC,hxU⟩)

omit [TopologicalSpace S] in
theorem actual_loop_inside_face_meets_boundary_only_at_base
    (C K U : Set S) (base : S)
    (hbaseC : base ∈ C) (hbaseK : base ∈ K)
    (hU : U ⊆ Cᶜ) (hK : K \ {base} ⊆ U) :
    C ∩ K = {base} := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hn
    exact hU (hK ⟨hx.2,hn⟩) hx.1
  · intro x hx
    have he : x = base := Set.mem_singleton_iff.mp hx
    exact he ▸ ⟨hbaseC,hbaseK⟩

theorem actual_loop_inside_two_loop_face_meets_both_at_base
    (M : HyperellipticModel E S) (a b c : EssentialMarkedArc M)
    (hbasea : a.val.map 0 = c.val.map 0)
    (hbaseb : b.val.map 0 = c.val.map 0)
    (U : Set S) (hU : U ⊆ (a.val.image ∪ b.val.image)ᶜ)
    (hc : c.val.image \ {c.val.map 0} ⊆ U) :
    a.val.image ∩ c.val.image = {c.val.map 0} ∧
      b.val.image ∩ c.val.image = {c.val.map 0} := by
  constructor
  · exact actual_loop_inside_face_meets_boundary_only_at_base
      a.val.image c.val.image U (c.val.map 0)
      (hbasea ▸ Set.mem_range_self (0 : Interval))
      (Set.mem_range_self (0 : Interval))
      (fun x hx hxa => hU hx (Or.inl hxa)) hc
  · exact actual_loop_inside_face_meets_boundary_only_at_base
      b.val.image c.val.image U (c.val.map 0)
      (hbaseb ▸ Set.mem_range_self (0 : Interval))
      (Set.mem_range_self (0 : Interval))
      (fun x hx hxb => hU hx (Or.inr hxb)) hc

theorem actual_third_essential_loop_cannot_enclose_markfree_side
    (M : HyperellipticModel E S) (a b c : EssentialMarkedArc M)
    (hc : c.val.map 0 = c.val.map 1)
    (hbaseac : a.val.map 0 = c.val.map 0)
    (A : MarkedLoopDiscDecomposition a.val)
    (B : MarkedLoopDiscDecomposition b.val)
    (C : MarkedLoopDiscDecomposition c.val)
    (i j k m l q : Fin 2) (hij : i ≠ j) (hkm : k ≠ m) (hlq : l ≠ q)
    (hAjC : A.side j ⊆ C.side l)
    (haC : a.val.image \ {a.val.map 0} ⊆ C.side l)
    (hBmC : B.side m ⊆ C.side l)
    (hbC : b.val.image \ {a.val.map 0} ⊆ C.side l)
    (hfree : Disjoint (A.side i ∩ B.side k) (M.cover.branch : Set S)) :
    False := by
  have hCdis : Disjoint (C.side q) (C.side l) := by
    fin_cases q <;> fin_cases l
    · exact False.elim (hlq rfl)
    · exact C.disjoint
    · exact C.disjoint.symm
    · exact False.elim (hlq rfl)
  have hCqAi : C.side q ⊆ A.side i := by
    intro x hxq
    have hxnotAj : x ∉ A.side j :=
      fun hxj => Set.disjoint_left.mp hCdis hxq (hAjC hxj)
    have hxnota : x ∉ a.val.image := by
      intro hxa
      by_cases he : x = a.val.map 0
      · exact (C.discs q).component.2.2.1 hxq
          (he ▸ hbaseac ▸ Set.mem_range_self (0 : Interval))
      · exact Set.disjoint_left.mp hCdis hxq
          (haC ⟨hxa,by simpa using he⟩)
    have hsides : x ∈ A.side 0 ∪ A.side 1 := A.complement ▸ hxnota
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hsides.resolve_right hxnotAj
    · exact hsides.resolve_left hxnotAj
    · exact False.elim (hij rfl)
  have hCqBk : C.side q ⊆ B.side k := by
    intro x hxq
    have hxnotBm : x ∉ B.side m :=
      fun hxm => Set.disjoint_left.mp hCdis hxq (hBmC hxm)
    have hxnotb : x ∉ b.val.image := by
      intro hxb
      by_cases he : x = a.val.map 0
      · exact (C.discs q).component.2.2.1 hxq
          (he ▸ hbaseac ▸ Set.mem_range_self (0 : Interval))
      · exact Set.disjoint_left.mp hCdis hxq
          (hbC ⟨hxb,by simpa using he⟩)
    have hsides : x ∈ B.side 0 ∪ B.side 1 := B.complement ▸ hxnotb
    fin_cases k <;> fin_cases m
    · exact False.elim (hkm rfl)
    · exact hsides.resolve_right hxnotBm
    · exact hsides.resolve_left hxnotBm
    · exact False.elim (hkm rfl)
  have hmark : ∃ z, z ∈ M.cover.branch ∧ z ∈ C.side q := by
    rcases c.property with hn | hregions
    · exact False.elim (hn hc)
    · exact hregions _ (C.discs q).component
  obtain ⟨z,hzm,hzq⟩ := hmark
  exact Set.disjoint_left.mp hfree ⟨hCqAi hzq,hCqBk hzq⟩ hzm

theorem actual_essential_loop_inside_markfree_between_region_same_class
    (M : HyperellipticModel E S) (a b c : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hc : c.val.map 0 = c.val.map 1)
    (hbaseab : a.val.map 0 = b.val.map 0)
    (hbaseac : a.val.map 0 = c.val.map 0)
    (A : MarkedLoopDiscDecomposition a.val)
    (B : MarkedLoopDiscDecomposition b.val)
    (i j k m : Fin 2) (hij : i ≠ j) (hkm : k ≠ m)
    (hfree : Disjoint (A.side i ∩ B.side k) (M.cover.branch : Set S))
    (hcinside : c.val.image \ {a.val.map 0} ⊆ A.side i ∩ B.side k) :
    Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) c := by
  let : T2Space S := M.sphere.symm.t2Space
  let U := A.side i ∩ B.side k
  have hUsub : U ⊆ (a.val.image ∪ b.val.image)ᶜ := by
    intro x hx hxab
    rcases hxab with hxa | hxb
    · exact (A.discs i).component.2.2.1 hx.1 hxa
    · exact (B.discs k).component.2.2.1 hx.2 hxb
  have hmeet := actual_loop_inside_two_loop_face_meets_both_at_base M a b c
    hbaseac (hbaseab.symm.trans hbaseac) U hUsub
    (by simpa only [← hbaseac] using hcinside)
  have hmeetac : a.val.image ∩ c.val.image = {a.val.map 0} := by
    simpa only [← hbaseac] using hmeet.1
  have hmeetbc : b.val.image ∩ c.val.image = {b.val.map 0} := by
    simpa only [← hbaseab,← hbaseac] using hmeet.2
  obtain ⟨C⟩ := markedLoop_disc_decomposition_exists M c.val hc
  have hcAi : c.val.image \ {a.val.map 0} ⊆ A.side i :=
    fun x hx => (hcinside hx).1
  have hcBk : c.val.image \ {b.val.map 0} ⊆ B.side k := by
    intro x hx
    exact (hcinside (by simpa only [← hbaseab] using hx)).2
  obtain ⟨l,hAjC,haC⟩ := actual_common_base_loop_opposite_side_nested
    M a c hmeetac A C i j hij hcAi
  obtain ⟨n,hBmC,hbC'⟩ := actual_common_base_loop_opposite_side_nested
    M b c hmeetbc B C k m hkm hcBk
  have hbC : b.val.image \ {a.val.map 0} ⊆ C.side n := by
    intro x hx
    exact hbC' (by simpa only [hbaseab] using hx)
  have hln : l ≠ n := by
    intro he
    let q : Fin 2 := if l = 0 then 1 else 0
    have hlq : l ≠ q := by fin_cases l <;> simp [q]
    exact actual_third_essential_loop_cannot_enclose_markfree_side M a b c hc
      hbaseac A B C i j k m l q hij hkm hlq hAjC haC
      (he ▸ hBmC) (he ▸ hbC) hfree
  have hCdis : Disjoint (C.side l) (C.side n) := by
    fin_cases l <;> fin_cases n
    · exact False.elim (hln rfl)
    · exact C.disjoint
    · exact C.disjoint.symm
    · exact False.elim (hln rfl)
  let V := A.side i ∩ C.side l
  have hVBk : V ⊆ B.side k := by
    intro x hx
    have hxnotBm : x ∉ B.side m :=
      fun hxm => Set.disjoint_left.mp hCdis hx.2 (hBmC hxm)
    have hxnotb : x ∉ b.val.image := by
      intro hxb
      by_cases he : x = a.val.map 0
      · exact (A.discs i).component.2.2.1 hx.1
          (he ▸ Set.mem_range_self (0 : Interval))
      · exact Set.disjoint_left.mp hCdis hx.2
          (hbC ⟨hxb,by simpa using he⟩)
    have hsides : x ∈ B.side 0 ∪ B.side 1 := B.complement ▸ hxnotb
    fin_cases k <;> fin_cases m
    · exact False.elim (hkm rfl)
    · exact hsides.resolve_right hxnotBm
    · exact hsides.resolve_left hxnotBm
    · exact False.elim (hkm rfl)
  have hVfree : Disjoint V (M.cover.branch : Set S) :=
    Set.disjoint_left.mpr (fun x hxV hxm =>
      Set.disjoint_left.mp hfree ⟨hxV.1,hVBk hxV⟩ hxm)
  have hVopen : IsOpen V := (A.discs i).open_side.inter (C.discs l).open_side
  have hVconn : IsConnected V :=
    actual_common_base_between_region_connected M a c hc hbaseac A C
      i j l hij hcAi hAjC haC
  have hVsub : V ⊆ (a.val.image ∪ c.val.image)ᶜ := by
    intro x hx hxac
    rcases hxac with hxa | hxc
    · exact (A.discs i).component.2.2.1 hx.1 hxa
    · exact (C.discs l).component.2.2.1 hx.2 hxc
  have hVfront : frontier V = a.val.image ∪ c.val.image :=
    actual_common_base_between_frontier_eq M a c A C i l hcAi haC
  have hVcomp : IsComplementComponent (a.val.image ∪ c.val.image) V :=
    actual_open_connected_region_is_complement_component
      (a.val.image ∪ c.val.image) V hVopen hVconn hVsub hVfront.subset
  exact actual_common_basepoint_loops_empty_face_class_equality M a c ha hc
    hbaseac hmeetac (a.val.image ∪ c.val.image) V
    ((markedArc_image_compact a.val).isClosed.union
      (markedArc_image_compact c.val).isClosed)
    Set.subset_union_left Set.subset_union_right hVcomp hVfront.subset
    (fun z hz hzV => Set.disjoint_left.mp hVfree hzV hz)

theorem actual_distinct_class_based_loop_avoids_markfree_between_region
    (M : HyperellipticModel E S) (a b c : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hc : c.val.map 0 = c.val.map 1)
    (hbaseab : a.val.map 0 = b.val.map 0)
    (hbaseac : a.val.map 0 = c.val.map 0)
    (hclassne : Quotient.mk (essentialArcSetoid M) a ≠
      Quotient.mk (essentialArcSetoid M) c)
    (A : MarkedLoopDiscDecomposition a.val)
    (B : MarkedLoopDiscDecomposition b.val)
    (i j k m : Fin 2) (hij : i ≠ j) (hkm : k ≠ m)
    (hfree : Disjoint (A.side i ∩ B.side k) (M.cover.branch : Set S))
    (hfront : Disjoint (c.val.image \ {a.val.map 0})
      (frontier (A.side i ∩ B.side k))) :
    Disjoint c.val.image (A.side i ∩ B.side k) := by
  let U := A.side i ∩ B.side k
  have hUopen : IsOpen U := (A.discs i).open_side.inter (B.discs k).open_side
  have hconn : IsConnected (c.val.image \ {a.val.map 0}) := by
    rw [hbaseac]
    exact loop_image_remove_base_connected M c.val hc
  rcases actual_connected_trace_face_dichotomy
      (c.val.image \ {a.val.map 0}) U hconn hUopen hfront with hinside | havoid
  · exact False.elim (hclassne
      (actual_essential_loop_inside_markfree_between_region_same_class M a b c
        ha hc hbaseab hbaseac A B i j k m hij hkm hfree hinside))
  · apply Set.disjoint_left.mpr
    intro x hxc hxU
    by_cases he : x = a.val.map 0
    · exact Set.disjoint_left.mp hfree hxU (he ▸ a.val.start_marked)
    · exact Set.disjoint_left.mp havoid ⟨hxc,by simpa using he⟩ hxU

theorem actual_selected_loop_zero_contact_graph_free_between_component
    (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
    (rT : {w // w ∈ T.val} → EssentialMarkedArc M)
    (hrT : ∀ w, Quotient.mk (essentialArcSetoid M) (rT w) = w.val)
    (hdT : ∀ w z, w ≠ z → Disjoint (arcInterior M (rT w)) (arcInterior M (rT z)))
    (F J : Finset (EssentialArcClass M)) (hTF : T.val ⊆ F) (hJT : J ⊆ T.val)
    (r0 : {w // w ∈ F} → EssentialMarkedArc M)
    (hr0 : ∀ w, Quotient.mk (essentialArcSetoid M) (r0 w) = w.val)
    (hd0 : ∀ w z, w ≠ z → Disjoint (arcInterior M (r0 w)) (arcInterior M (r0 z)))
    (haligned0 : ∀ w : {w // w ∈ T.val}, w.val ∈ J →
      r0 ⟨w.val, hTF w.property⟩ = rT w)
    (r : {w // w ∈ F} → EssentialMarkedArc M)
    (hgraph : actualObjectTrace M r0 J = actualObjectTrace M r J)
    (u : {w // w ∈ T.val}) (hu : u.val ∉ J)
    (hloop : (r0 ⟨u.val,hTF u.property⟩).val.map 0 =
      (r0 ⟨u.val,hTF u.property⟩).val.map 1)
    (hzero : ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u) = ∅) :
    ∃ U : Set S,
      IsComplementComponent
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image) U ∧
      Disjoint U (M.cover.branch : Set S) ∧
      frontier U =
        (r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image ∧
      Disjoint U (actualObjectTrace M r J) := by
  let uF : {w // w ∈ F} := ⟨u.val,hTF u.property⟩
  let a := r0 uF
  let b := rT u
  have hclass : Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) b :=
    (hr0 uF).trans (hrT u).symm
  have hb : b.val.map 0 = b.val.map 1 :=
    (actual_same_class_loop_closure_invariant M a b hclass).mp hloop
  have hbase : a.val.map 0 = b.val.map 0 :=
    actual_same_class_loop_literal_base M a b hloop hclass
  have hmeet := actual_zero_contact_same_class_loop_intersection M a b
    hloop hclass hzero
  obtain ⟨A⟩ := markedLoop_disc_decomposition_exists M a.val hloop
  obtain ⟨B⟩ := markedLoop_disc_decomposition_exists M b.val hb
  obtain ⟨i,hbi⟩ := actual_common_base_loop_other_trace_one_side M a b hb hbase hmeet A
  let j : Fin 2 := if i = 0 then 1 else 0
  have hij : i ≠ j := by fin_cases i <;> simp [j]
  obtain ⟨k,hAjB,hak,hfree⟩ :=
    actual_same_class_common_base_between_region_mark_free M a b hloop hclass hmeet
      A B i j hij hbi
  let m : Fin 2 := if k = 0 then 1 else 0
  have hkm : k ≠ m := by fin_cases k <;> simp [m]
  let U := A.side i ∩ B.side k
  have hUopen : IsOpen U := (A.discs i).open_side.inter (B.discs k).open_side
  have hUconn : IsConnected U :=
    actual_common_base_between_region_connected M a b hb hbase A B
      i j k hij hbi hAjB hak
  have hUsub : U ⊆ (a.val.image ∪ b.val.image)ᶜ := by
    intro x hx hxab
    rcases hxab with hxa | hxb
    · exact (A.discs i).component.2.2.1 hx.1 hxa
    · exact (B.discs k).component.2.2.1 hx.2 hxb
  have hfront : frontier U = a.val.image ∪ b.val.image :=
    actual_common_base_between_frontier_eq M a b A B i k hbi hak
  have hUcomp : IsComplementComponent (a.val.image ∪ b.val.image) U :=
    actual_open_connected_region_is_complement_component
      (a.val.image ∪ b.val.image) U hUopen hUconn hUsub hfront.subset
  refine ⟨U,hUcomp,hfree,hfront,?_⟩
  apply Set.disjoint_left.mpr
  intro x hxU hxgraph
  rw [← hgraph] at hxgraph
  obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hxgraph
  obtain ⟨hvJ,hxv⟩ := Set.mem_iUnion.mp hv
  let c := r0 v
  have hfrontdis : Disjoint (c.val.image \ {a.val.map 0}) (frontier U) := by
    apply Set.disjoint_left.mpr
    intro y hyc hyfront
    have hybound : y ∈ a.val.image ∪ b.val.image := hfront ▸ hyfront
    have hyn : y ∉ actualObjectTrace M r J :=
      actual_selected_loop_boundaries_avoid_original_graph M p T rT hdT F J
        hTF hJT r0 hd0 haligned0 r hgraph u hu hloop hclass y hybound hyc.2
    have hyg : y ∈ actualObjectTrace M r J := by
      rw [← hgraph]
      exact Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨hvJ,hyc.1⟩⟩
    exact hyn hyg
  by_cases hstart : c.val.map 0 = a.val.map 0
  · by_cases hc : c.val.map 0 = c.val.map 1
    · have hclassne : Quotient.mk (essentialArcSetoid M) a ≠
          Quotient.mk (essentialArcSetoid M) c := by
        intro he
        have huv : u.val = v.val := by
          calc u.val = Quotient.mk (essentialArcSetoid M) a := (hr0 uF).symm
            _ = Quotient.mk (essentialArcSetoid M) c := he
            _ = v.val := hr0 v
        exact hu (huv ▸ hvJ)
      have havoid := actual_distinct_class_based_loop_avoids_markfree_between_region
        M a b c hloop hc hbase hstart.symm hclassne A B i j k m hij hkm
        hfree hfrontdis
      exact Set.disjoint_left.mp havoid hxv hxU
    · have havoid := actual_nonloop_marked_arc_avoids_markfree_face
        M c.val (a.val.map 0) a.val.start_marked hc U hUopen hfree hfrontdis
      exact Set.disjoint_left.mp havoid hxv hxU
  · have hsecond : ∃ z ∈ c.val.image \ {a.val.map 0},
        z ∈ M.cover.branch := by
      refine ⟨c.val.map 0,⟨Set.mem_range_self 0,?_⟩,c.val.start_marked⟩
      intro he
      exact hstart (Set.mem_singleton_iff.mp he)
    have havoid := actual_marked_arc_avoids_markfree_region_of_second_mark
      M c.val (a.val.map 0) a.val.start_marked U hUopen hfree hfrontdis hsecond
    by_cases he : x = a.val.map 0
    · exact Set.disjoint_left.mp hfree hxU (he ▸ a.val.start_marked)
    · exact Set.disjoint_left.mp havoid ⟨hxv,by simpa using he⟩ hxU

theorem actual_common_base_two_loop_markfree_component_unique
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hb : b.val.map 0 = b.val.map 1)
    (hbaseab : a.val.map 0 = b.val.map 0)
    (A : MarkedLoopDiscDecomposition a.val)
    (B : MarkedLoopDiscDecomposition b.val)
    (i j k m : Fin 2) (hij : i ≠ j) (hkm : k ≠ m)
    (hbi : b.val.image \ {a.val.map 0} ⊆ A.side i)
    (hak : a.val.image \ {a.val.map 0} ⊆ B.side k)
    (hUcomp : IsComplementComponent (a.val.image ∪ b.val.image)
      (A.side i ∩ B.side k))
    (V : Set S) (hV : IsComplementComponent (a.val.image ∪ b.val.image) V)
    (hVfree : Disjoint V (M.cover.branch : Set S)) :
    V = A.side i ∩ B.side k := by
  let G := a.val.image ∪ b.val.image
  have hAdis : Disjoint (A.side i) (A.side j) := by
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact A.disjoint
    · exact A.disjoint.symm
    · exact False.elim (hij rfl)
  have hBdis : Disjoint (B.side k) (B.side m) := by
    fin_cases k <;> fin_cases m
    · exact False.elim (hkm rfl)
    · exact B.disjoint
    · exact B.disjoint.symm
    · exact False.elim (hkm rfl)
  have hAjavoidsb : A.side j ⊆ b.val.imageᶜ := by
    intro x hxj hxb
    by_cases he : x = a.val.map 0
    · exact (A.discs j).component.2.2.1 hxj
        (he ▸ Set.mem_range_self (0 : Interval))
    · exact Set.disjoint_left.mp hAdis
        (hbi ⟨hxb,by simpa using he⟩) hxj
  have hBmavoidsa : B.side m ⊆ a.val.imageᶜ := by
    intro x hxm hxa
    by_cases he : x = a.val.map 0
    · exact (B.discs m).component.2.2.1 hxm
        (he ▸ hbaseab ▸ Set.mem_range_self (0 : Interval))
    · exact Set.disjoint_left.mp hBdis
        (hak ⟨hxa,by simpa using he⟩) hxm
  have hAjcomp : IsComplementComponent G (A.side j) := by
    apply actual_open_connected_region_is_complement_component G (A.side j)
      (A.discs j).open_side (A.discs j).component.2.1
    · intro x hx hxab
      rcases hxab with hxa | hxb
      · exact (A.discs j).component.2.2.1 hx hxa
      · exact hAjavoidsb hx hxb
    · rw [(A.discs j).boundary]
      exact Set.subset_union_left
  have hBmcomp : IsComplementComponent G (B.side m) := by
    apply actual_open_connected_region_is_complement_component G (B.side m)
      (B.discs m).open_side (B.discs m).component.2.1
    · intro x hx hxab
      rcases hxab with hxa | hxb
      · exact hBmavoidsa hx hxa
      · exact (B.discs m).component.2.2.1 hx hxb
    · rw [(B.discs m).boundary]
      exact Set.subset_union_right
  have hVsubAi : V ⊆ A.side i := by
    have hVcover : V ⊆ A.side i ∪ A.side j := by
      intro x hx
      have hxnota : x ∉ a.val.image := fun hxa => hV.2.2.1 hx (Or.inl hxa)
      have hh : x ∈ A.side 0 ∪ A.side 1 := A.complement ▸ hxnota
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · exact hh
      · exact hh.symm
      · exact False.elim (hij rfl)
    rcases hV.2.1.isPreconnected.subset_or_subset (A.discs i).open_side
        (A.discs j).open_side hAdis hVcover with hi | hj
    · exact hi
    · obtain ⟨x,hxV⟩ := hV.1
      have heq : V = A.side j := by
        by_contra hn
        exact Set.disjoint_left.mp (complementComponents_disjoint hV hAjcomp hn)
          hxV (hj hxV)
      have hmark : ∃ z, z ∈ M.cover.branch ∧ z ∈ A.side j := by
        rcases a.property with hn | hregions
        · exact False.elim (hn ha)
        · exact hregions _ (A.discs j).component
      obtain ⟨z,hzm,hzj⟩ := hmark
      exact False.elim (Set.disjoint_left.mp hVfree (heq.symm ▸ hzj) hzm)
  have hVsubBk : V ⊆ B.side k := by
    have hVcover : V ⊆ B.side k ∪ B.side m := by
      intro x hx
      have hxnotb : x ∉ b.val.image := fun hxb => hV.2.2.1 hx (Or.inr hxb)
      have hh : x ∈ B.side 0 ∪ B.side 1 := B.complement ▸ hxnotb
      fin_cases k <;> fin_cases m
      · exact False.elim (hkm rfl)
      · exact hh
      · exact hh.symm
      · exact False.elim (hkm rfl)
    rcases hV.2.1.isPreconnected.subset_or_subset (B.discs k).open_side
        (B.discs m).open_side hBdis hVcover with hk | hm
    · exact hk
    · obtain ⟨x,hxV⟩ := hV.1
      have heq : V = B.side m := by
        by_contra hn
        exact Set.disjoint_left.mp (complementComponents_disjoint hV hBmcomp hn)
          hxV (hm hxV)
      have hmark : ∃ z, z ∈ M.cover.branch ∧ z ∈ B.side m := by
        rcases b.property with hn | hregions
        · exact False.elim (hn hb)
        · exact hregions _ (B.discs m).component
      obtain ⟨z,hzm,hzj⟩ := hmark
      exact False.elim (Set.disjoint_left.mp hVfree (heq.symm ▸ hzj) hzm)
  have hVsub : V ⊆ A.side i ∩ B.side k := fun x hx => ⟨hVsubAi hx,hVsubBk hx⟩
  obtain ⟨x,hxV⟩ := hV.1
  by_contra hn
  exact Set.disjoint_left.mp (complementComponents_disjoint hV hUcomp hn)
    hxV (hVsub hxV)

theorem actual_same_class_zero_contact_markfree_component_unique
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a =
      Quotient.mk (essentialArcSetoid M) b)
    (hzero : ArcSurgery.crossings M a b = ∅)
    (V W : Set S)
    (hV : IsComplementComponent (a.val.image ∪ b.val.image) V)
    (hW : IsComplementComponent (a.val.image ∪ b.val.image) W)
    (hVfree : Disjoint V (M.cover.branch : Set S))
    (hWfree : Disjoint W (M.cover.branch : Set S)) :
    V = W := by
  have hb : b.val.map 0 = b.val.map 1 :=
    (actual_same_class_loop_closure_invariant M a b hclass).mp ha
  have hbase : a.val.map 0 = b.val.map 0 :=
    actual_same_class_loop_literal_base M a b ha hclass
  have hmeet := actual_zero_contact_same_class_loop_intersection M a b ha hclass hzero
  obtain ⟨A⟩ := markedLoop_disc_decomposition_exists M a.val ha
  obtain ⟨B⟩ := markedLoop_disc_decomposition_exists M b.val hb
  obtain ⟨i,hbi⟩ := actual_common_base_loop_other_trace_one_side M a b hb hbase hmeet A
  let j : Fin 2 := if i = 0 then 1 else 0
  have hij : i ≠ j := by fin_cases i <;> simp [j]
  obtain ⟨k,hAjB,hak,_hfree⟩ :=
    actual_same_class_common_base_between_region_mark_free M a b ha hclass hmeet
      A B i j hij hbi
  let m : Fin 2 := if k = 0 then 1 else 0
  have hkm : k ≠ m := by fin_cases k <;> simp [m]
  let U := A.side i ∩ B.side k
  have hUopen : IsOpen U := (A.discs i).open_side.inter (B.discs k).open_side
  have hUconn : IsConnected U :=
    actual_common_base_between_region_connected M a b hb hbase A B
      i j k hij hbi hAjB hak
  have hUsub : U ⊆ (a.val.image ∪ b.val.image)ᶜ := by
    intro x hx hxab
    rcases hxab with hxa | hxb
    · exact (A.discs i).component.2.2.1 hx.1 hxa
    · exact (B.discs k).component.2.2.1 hx.2 hxb
  have hUfront : frontier U ⊆ a.val.image ∪ b.val.image :=
    actual_common_base_between_frontier_subset M a b A B i k
  have hUcomp : IsComplementComponent (a.val.image ∪ b.val.image) U :=
    actual_open_connected_region_is_complement_component
      (a.val.image ∪ b.val.image) U hUopen hUconn hUsub hUfront
  have hVU := actual_common_base_two_loop_markfree_component_unique
    M a b ha hb hbase A B i j k m hij hkm hbi hak hUcomp V hV hVfree
  have hWU := actual_common_base_two_loop_markfree_component_unique
    M a b ha hb hbase A B i j k m hij hkm hbi hak hUcomp W hW hWfree
  exact hVU.trans hWU.symm

theorem actual_pinched_strip_avoids_graph_of_graphfree_face
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (U H graph : Set S) (hUH : U = H)
    (hgraphfree : Disjoint H graph)
    (base : S)
    (e : Interval ≃ₜ Interval) (G : C(Interval × Interval,S))
    (hG0 : ∀ s, G (s,0) = a.val.map s)
    (hG1 : ∀ s, G (s,1) = b.val.map (e s))
    (hGends : ∀ t, G (0,t) = base ∧ G (1,t) = base)
    (hGinner : ∀ s t, s ∈ Set.Ioo (0 : Interval) 1 →
      t ∈ Set.Ioo (0 : Interval) 1 → G (s,t) ∈ U)
    (hboundary : ∀ x ∈ a.val.image ∪ b.val.image,
      x ≠ base → x ∉ graph) :
    ∀ s t, G (s,t) ≠ base → G (s,t) ∉ graph := by
  intro s t hne
  by_cases hs0 : s = 0
  · exact False.elim (hne (hs0 ▸ (hGends t).1))
  by_cases hs1 : s = 1
  · exact False.elim (hne (hs1 ▸ (hGends t).2))
  have hs : s ∈ Set.Ioo (0 : Interval) 1 := by
    exact ⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),
      lt_of_le_of_ne s.property.2 hs1⟩
  by_cases ht0 : t = 0
  · rw [ht0,hG0] at hne ⊢
    exact hboundary _ (Or.inl (Set.mem_range_self s)) hne
  by_cases ht1 : t = 1
  · rw [ht1,hG1] at hne ⊢
    exact hboundary _ (Or.inr (Set.mem_range_self (e s))) hne
  have ht : t ∈ Set.Ioo (0 : Interval) 1 := by
    exact ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
      lt_of_le_of_ne t.property.2 ht1⟩
  exact Set.disjoint_left.mp hgraphfree (hUH ▸ hGinner s t hs ht)

end CurveComplex.HyperellipticModel
