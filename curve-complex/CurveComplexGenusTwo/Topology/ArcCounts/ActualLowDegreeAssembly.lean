import CurveComplexGenusTwo.Filtration.Geometry.ActualBigonMarkNamedHeader
import CurveComplexGenusTwo.Filtration.Geometry.ActualFaceMarksHeader
import CurveComplexGenusTwo.Dictionary.JordanEssentiality
import CurveComplexGenusTwo.Topology.ArcCounts.ActualObjectFaceCountNamedHeader
import CurveComplexGenusTwo.Topology.ArcStraightening
import Schoenflies.TwoArcs
import CurveComplexGenusTwo.Topology.ArcCounts.ActualNumericDegree
set_option maxHeartbeats 2800000
namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Every actual representative trace is the closure of its unmarked interior. -/
theorem actual_arc_image_subset_closure_interior
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M) :
    a.val.image ⊆ closure (arcInterior M a) := by
  have hi : a.val.map '' Set.Ioo (0 : Interval) 1 = arcInterior M a := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      refine ⟨⟨t,rfl⟩,?_⟩
      intro hb
      rcases a.val.marked_only_at_ends t hb with h | h
      · simpa [h] using ht.1
      · simpa [h] using ht.2
    · rintro ⟨⟨t,rfl⟩,hn⟩
      have ht0 : (t : ℝ) ≠ 0 := by
        intro h
        have he : t = (0 : Interval) := Subtype.ext h
        exact hn (he ▸ a.val.start_marked)
      have ht1 : (t : ℝ) ≠ 1 := by
        intro h
        have he : t = (1 : Interval) := Subtype.ext h
        exact hn (he ▸ a.val.end_marked)
      refine ⟨t,?_,rfl⟩
      change (0 : ℝ) < t.val ∧ t.val < 1
      exact ⟨lt_of_le_of_ne' t.property.1 ht0, lt_of_le_of_ne t.property.2 ht1⟩
  rintro y ⟨t,ht⟩
  have htcl : t ∈ closure (Set.Ioo (0 : Interval) 1) := by
    rw [closure_Ioo (by norm_num : (0 : Interval) ≠ 1)]
    constructor
    · change (0 : ℝ) ≤ t.val; exact t.property.1
    · change t.val ≤ (1 : ℝ); exact t.property.2
  have hm : a.val.map t ∈ closure (a.val.map '' Set.Ioo (0 : Interval) 1) :=
    image_closure_subset_closure_image a.val.continuous ⟨t,htcl,rfl⟩
  rw [hi] at hm
  exact ht ▸ hm

/-- Actual face boundary support follows from literal frontier contacts.
Finite marked endpoints cannot form isolated residual boundary points. -/
theorem actual_face_frontier_subset_incident_traces
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M) (U : Set S)
    (hU : IsComplementComponent (⋃ i, (r i).val.image) U) :
    frontier U ⊆ ⋃ i ∈ {i | (frontier U ∩ arcInterior M (r i)).Nonempty}, (r i).val.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  let A := ⋃ i ∈ {i | (frontier U ∩ arcInterior M (r i)).Nonempty}, (r i).val.image
  have hA : IsClosed A := isClosed_iUnion_of_finite (fun i =>
    isClosed_iUnion_of_finite (fun _ => (markedArc_image_compact (r i).val).isClosed))
  have hG : IsClosed (⋃ i, (r i).val.image) :=
    (markedFamily_graph_compact (fun i => (r i).val)).isClosed
  have hopen : IsOpen U := complementComponent_open hG hU
  have hfront : frontier U ⊆ A ∪ (M.cover.branch : Set S) := by
    intro z hz
    by_cases hb : z ∈ M.cover.branch
    · exact Or.inr hb
    · left
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (complementComponent_frontier_subset hG hU hz)
      exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨⟨z,hz,hi,hb⟩,hi⟩⟩
  intro z hz
  by_contra hzA
  have hzb : z ∈ M.cover.branch := (hfront hz).resolve_left hzA
  let O := Aᶜ ∩ ((M.cover.branch.erase z : Finset S) : Set S)ᶜ
  have hO : IsOpen O := hA.isOpen_compl.inter
    (M.cover.branch.erase z).finite_toSet.isClosed.isOpen_compl
  have hzO : z ∈ O := ⟨hzA,by simp⟩
  obtain ⟨D,hDO,hD,hzD,hDc⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
      (inferInstance : LocallyConnectedSpace S) z O (hO.mem_nhds hzO)
  have hL : IsConnected (D \ {z}) := actual_open_puncture_connected M hD hDc z
  have hcl : closure U ∩ (D \ {z}) ⊆ U := by
    intro x hx
    by_contra hxU
    have hxfr : x ∈ frontier U := by rw [hopen.frontier_eq]; exact ⟨hx.1,hxU⟩
    have hxb : x ∈ M.cover.branch := (hfront hxfr).resolve_left (hDO hx.2.1).1
    exact (hDO hx.2.1).2 (by simp only [Finset.mem_coe,Finset.mem_erase]; exact ⟨by simpa using hx.2.2,hxb⟩)
  have hmeet : ((D \ {z}) ∩ U).Nonempty := by
    obtain ⟨x,hxD,hxU⟩ := Set.Nonempty.of_closure
      ⟨z,hD.inter_closure ⟨hzD,frontier_subset_closure hz⟩⟩
    refine ⟨x,⟨hxD,?_⟩,hxU⟩
    intro hxz
    have he : x = z := Set.mem_singleton_iff.mp hxz
    exact hU.2.2.1 (he ▸ hxU) (complementComponent_frontier_subset hG hU hz)
  have hLU : D \ {z} ⊆ U := hL.isPreconnected.subset_of_closure_inter_subset hopen hmeet hcl
  obtain ⟨i,hzi⟩ := Set.mem_iUnion.mp (complementComponent_frontier_subset hG hU hz)
  obtain ⟨w,hwD,hwi⟩ := Set.Nonempty.of_closure
    ⟨z,hD.inter_closure ⟨hzD,actual_arc_image_subset_closure_interior M (r i) hzi⟩⟩
  have hwne : w ∉ ({z} : Set S) := by
    intro h
    exact hwi.2 ((Set.mem_singleton_iff.mp h).symm ▸ hzb)
  exact hU.2.2.1 (hLU ⟨hwD,hwne⟩) (Set.mem_iUnion.mpr ⟨i,hwi.1⟩)
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_face_frontier_subset_incident_traces

namespace CurveComplex.HyperellipticModel
open Set
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The actual full-graph face bounded only by an essential loop is marked;
no face-degree or desired mark-budget certificate is assumed. -/
theorem actual_loop_frontier_face_contains_branch
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (hloop : a.val.map 0 = a.val.map 1)
    (G U : Set S) (hG : IsClosed G) (haG : a.val.image ⊆ G)
    (hU : IsComplementComponent G U)
    (hboundary : frontier U ⊆ a.val.image) :
    ∃ b, b ∈ M.cover.branch ∧ b ∈ U := by
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  have hopen : IsOpen U := complementComponent_open hG hU
  have hUA : U ⊆ a.val.imageᶜ := fun x hx hxa => hU.2.2.1 hx (haG hxa)
  have hcomp : IsComplementComponent a.val.image U := by
    refine ⟨hU.1, hU.2.1, hUA, ?_⟩
    intro V hV hUV hVA
    have hcl : closure U ∩ V ⊆ U := by
      intro x hx
      by_contra hn
      have hxf : x ∈ frontier U := by
        rw [hopen.frontier_eq]
        exact ⟨hx.1, hn⟩
      exact hVA hx.2 (hboundary hxf)
    have hVU : V ⊆ U := hV.isPreconnected.subset_of_closure_inter_subset hopen
      (by obtain ⟨x, hx⟩ := hU.1; exact ⟨x, hUV hx, hx⟩) hcl
    exact Set.Subset.antisymm hVU hUV
  rcases a.property with hnonloop | hregions
  · exact False.elim (hnonloop hloop)
  · exact hregions U hcomp

/-- Marked actual faces consume disjoint unused branch marks, without an
assumed injection or numerical budget. A covering face family is unnecessary. -/
theorem actual_marked_faces_card_le_unused_branch
    (M : HyperellipticModel E S) {ι : Type*} [Fintype ι]
    (r : ι → MarkedArc M) (F : Finset (Set S))
    (hF : ∀ U ∈ F, IsComplementComponent (⋃ i, (r i).image) U)
    (hmarked : ∀ U ∈ F, ∃ b, b ∈ M.cover.branch ∧ b ∈ U) :
    F.card ≤ 6 - (markedFamilyVertices r).card := by
  classical
  let marks : Set S → Finset S := fun U => M.cover.branch.filter (· ∈ U)
  have hp : (F : Set (Set S)).PairwiseDisjoint marks := by
    intro U hU V hV hne
    apply Finset.disjoint_left.mpr
    intro x hxU hxV
    exact Set.disjoint_left.mp (complementComponents_disjoint (hF U hU) (hF V hV) hne)
      (Finset.mem_filter.mp hxU).2 (Finset.mem_filter.mp hxV).2
  have hsub : F.biUnion marks ⊆ M.cover.branch \ markedFamilyVertices r := by
    intro x hx
    obtain ⟨U, hU, hxU⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hb, hxU⟩ := Finset.mem_filter.mp hxU
    refine Finset.mem_sdiff.mpr ⟨hb, ?_⟩
    intro hxv
    have hxg : x ∈ ⋃ i, (r i).image := by
      have h : x ∈ (⋃ i, (r i).image) ∩ (M.cover.branch : Set S) := by
        rw [markedFamily_graph_inter_branch]
        exact hxv
      exact h.1
    exact (hF U hU).2.2.1 hxU hxg
  have hpos : ∀ U ∈ F, 1 ≤ (marks U).card := by
    intro U hU
    obtain ⟨b, hb, hbU⟩ := hmarked U hU
    exact Finset.one_le_card.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hbU⟩⟩
  have hsum : F.card ≤ ∑ U ∈ F, (marks U).card := by
    simpa using Finset.sum_le_sum hpos
  have hcard : F.card ≤ (M.cover.branch \ markedFamilyVertices r).card := by
    rw [← Finset.card_biUnion hp] at hsum
    exact hsum.trans (Finset.card_le_card hsub)
  rw [Finset.card_sdiff_of_subset (markedFamilyVertices_subset_branch r), M.cover.branch_card] at hcard
  exact hcard
end CurveComplex.HyperellipticModel
namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A one-trace nonloop face is the nonloop's connected complement and hence
contains branch marks. This handles both occurrences of a repeated bridge. -/
theorem actual_nonloop_frontier_face_contains_branch
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (hnonloop : a.val.map 0 ≠ a.val.map 1)
    (G U : Set S) (hG : IsClosed G) (haG : a.val.image ⊆ G)
    (hU : IsComplementComponent G U)
    (hboundary : frontier U ⊆ a.val.image) :
    ∃ b, b ∈ M.cover.branch ∧ b ∈ U := by
  classical
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  have hopen : IsOpen U := complementComponent_open hG hU
  have hUA : U ⊆ a.val.imageᶜ := fun x hx hxa => hU.2.2.1 hx (haG hxa)
  have hcomp : IsComplementComponent a.val.image U := by
    refine ⟨hU.1, hU.2.1, hUA, ?_⟩
    intro V hV hUV hVA
    have hcl : closure U ∩ V ⊆ U := by
      intro x hx
      by_contra hn
      have hxf : x ∈ frontier U := by
        rw [hopen.frontier_eq]
        exact ⟨hx.1, hn⟩
      exact hVA hx.2 (hboundary hxf)
    have hVU : V ⊆ U := hV.isPreconnected.subset_of_closure_inter_subset hopen
      (by obtain ⟨x, hx⟩ := hU.1; exact ⟨x, hUV hx, hx⟩) hcl
    exact Set.Subset.antisymm hVU hUV
  have hconn : IsConnected a.val.imageᶜ := markedNonLoop_complement_connected M a.val hnonloop
  have hUeq : a.val.imageᶜ = U := hcomp.2.2.2 _ hconn hUA (Subset.refl _)
  have hc : (markedArcEndset a.val).card ≤ 2 := by
    exact (Finset.card_insert_le _ _).trans (by simp)
  have hlt : (markedArcEndset a.val).card < M.cover.branch.card := by
    rw [M.cover.branch_card]
    omega
  obtain ⟨b, hb, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨b, hb, ?_⟩
  rw [← hUeq]
  intro hbi
  have he : b ∈ markedArcEndset a.val := by
    change b ∈ (markedArcEndset a.val : Set S)
    rw [← markedArc_image_inter_branch]
    exact ⟨hbi, hb⟩
  exact hnot he

end CurveComplex.HyperellipticModel
namespace CurveComplex.HyperellipticModel
open Set
open scoped Classical
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A real face of a nonempty graph contacts at least one actual edge. -/
theorem actual_face_incident_edges_nonempty
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι] [Nonempty ι]
    (r : ι → EssentialMarkedArc M) (U : Set S)
    (hU : IsComplementComponent (⋃ i, (r i).val.image) U) :
    (Finset.univ.filter (fun i => (frontier U ∩ arcInterior M (r i)).Nonempty)).Nonempty := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  letI : ConnectedSpace S := M.cover.projection_surjective.connectedSpace M.cover.projection_continuous
  have hne : U ≠ Set.univ := by
    intro he
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact hU.2.2.1 (he.symm ▸ Set.mem_univ ((r i).val.map 0))
      (Set.mem_iUnion.mpr ⟨i,Set.mem_range_self 0⟩)
  obtain ⟨z,hz⟩ := nonempty_frontier_iff.mpr ⟨hU.1,hne⟩
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (actual_face_frontier_subset_incident_traces M r U hU hz)
  obtain ⟨hcontact,_⟩ := Set.mem_iUnion.mp hi
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcontact⟩⟩

/-- Every actual degree-at-most-one face contains an actual unused branch mark. -/
theorem actual_face_degree_le_one_contains_branch
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι] [Nonempty ι]
    (r : ι → EssentialMarkedArc M) (U : Set S)
    (hU : IsComplementComponent (⋃ i, (r i).val.image) U)
    (hdegree : (Finset.univ.filter (fun i =>
      (frontier U ∩ arcInterior M (r i)).Nonempty)).card ≤ 1) :
    ∃ b, b ∈ M.cover.branch ∧ b ∈ U := by
  classical
  let T := Finset.univ.filter (fun i => (frontier U ∩ arcInterior M (r i)).Nonempty)
  letI : T2Space S := M.sphere.symm.t2Space
  change T.card ≤ 1 at hdegree
  have hpos : 0 < T.card := Finset.card_pos.mpr (actual_face_incident_edges_nonempty M r U hU)
  have hcard : T.card = 1 := by omega
  obtain ⟨i,he⟩ := Finset.card_eq_one.mp hcard
  have hboundary : frontier U ⊆ (r i).val.image := by
    intro z hz
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (actual_face_frontier_subset_incident_traces M r U hU hz)
    obtain ⟨hcontact,hzj⟩ := Set.mem_iUnion.mp hj
    have hjT : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcontact⟩
    have hji : j = i := by simpa [he] using hjT
    exact hji ▸ hzj
  have hG : IsClosed (⋃ i, (r i).val.image) :=
    (markedFamily_graph_compact (fun i => (r i).val)).isClosed
  have hiG : (r i).val.image ⊆ ⋃ j, (r j).val.image := fun x hx => Set.mem_iUnion.mpr ⟨i,hx⟩
  by_cases hl : (r i).val.map 0 = (r i).val.map 1
  · exact actual_loop_frontier_face_contains_branch M (r i) hl _ U hG hiG hU hboundary
  · exact actual_nonloop_frontier_face_contains_branch M (r i) hl _ U hG hiG hU hboundary

/-- An actual unmarked low-degree face has exactly two distinct incident edges,
and its WHOLE frontier is supported on those two traces. -/
theorem actual_unmarked_low_degree_two_traces
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι] [Nonempty ι]
    (r : ι → EssentialMarkedArc M) (U : Set S)
    (hU : IsComplementComponent (⋃ i, (r i).val.image) U)
    (hdegree : (Finset.univ.filter (fun i =>
      (frontier U ∩ arcInterior M (r i)).Nonempty)).card < 3)
    (hfree : ∀ b ∈ M.cover.branch, b ∉ U) :
    ∃ i j : ι, i ≠ j ∧
      (frontier U ∩ arcInterior M (r i)).Nonempty ∧
      (frontier U ∩ arcInterior M (r j)).Nonempty ∧
      frontier U ⊆ (r i).val.image ∪ (r j).val.image := by
  classical
  let T := Finset.univ.filter (fun i => (frontier U ∩ arcInterior M (r i)).Nonempty)
  change T.card < 3 at hdegree
  have hnot : ¬ T.card ≤ 1 := by
    intro h
    obtain ⟨b,hb,hbU⟩ := actual_face_degree_le_one_contains_branch M r U hU h
    exact hfree b hb hbU
  have hcard : T.card = 2 := by omega
  obtain ⟨i,j,hij,he⟩ := Finset.card_eq_two.mp hcard
  have hi : i ∈ T := by simp [he]
  have hj : j ∈ T := by simp [he]
  refine ⟨i,j,hij,(Finset.mem_filter.mp hi).2,(Finset.mem_filter.mp hj).2,?_⟩
  intro z hz
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (actual_face_frontier_subset_incident_traces M r U hU hz)
  obtain ⟨hcontact,hzk⟩ := Set.mem_iUnion.mp hk
  have hkT : k ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcontact⟩
  have hki : k = i ∨ k = j := by simpa [he] using hkT
  rcases hki with h | h
  · exact Or.inl (h ▸ hzk)
  · exact Or.inr (h ▸ hzk)
/-- The actually marked low-degree faces inject into disjoint unused branch
sets via the existing concrete marking theorem. No charge certificate is input. -/
theorem actual_marked_low_degree_faces_card_le_unused_branch
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M) (F : Finset (Set S))
    (hF : ∀ U ∈ F, IsComplementComponent (⋃ i, (r i).val.image) U) :
    ((F.filter (fun U => (Finset.univ.filter (fun i =>
      (frontier U ∩ arcInterior M (r i)).Nonempty)).card < 3)).filter
      (fun U => ∃ b, b ∈ M.cover.branch ∧ b ∈ U)).card ≤
        6 - (markedFamilyVertices (fun i => (r i).val)).card := by
  classical
  apply actual_marked_faces_card_le_unused_branch M (fun i => (r i).val)
  · intro U hU
    exact hF U (Finset.mem_filter.mp (Finset.mem_filter.mp hU).1).1
  · intro U hU
    exact (Finset.mem_filter.mp hU).2

/-- Concrete low-degree faces split into marked and genuinely unmarked faces.
Only the latter still require the two-trace component classification. -/
theorem actual_low_degree_faces_card_le_unused_plus_unmarked
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M) (F : Finset (Set S))
    (hF : ∀ U ∈ F, IsComplementComponent (⋃ i, (r i).val.image) U) :
    (F.filter (fun U => (Finset.univ.filter (fun i =>
      (frontier U ∩ arcInterior M (r i)).Nonempty)).card < 3)).card ≤
      (6 - (markedFamilyVertices (fun i => (r i).val)).card) +
      ((F.filter (fun U => (Finset.univ.filter (fun i =>
        (frontier U ∩ arcInterior M (r i)).Nonempty)).card < 3)).filter
        (fun U => ∀ b ∈ M.cover.branch, b ∉ U)).card := by
  classical
  let B := F.filter (fun U => (Finset.univ.filter (fun i =>
    (frontier U ∩ arcInterior M (r i)).Nonempty)).card < 3)
  have hsplit := Finset.card_filter_add_card_filter_not (s := B)
    (fun U => ∃ b, b ∈ M.cover.branch ∧ b ∈ U)
  have hnot : B.filter (fun U => ¬ ∃ b, b ∈ M.cover.branch ∧ b ∈ U) =
      B.filter (fun U => ∀ b ∈ M.cover.branch, b ∉ U) := by
    ext U
    simp only [Finset.mem_filter, not_exists, not_and]
  rw [hnot] at hsplit
  have hm := actual_marked_low_degree_faces_card_le_unused_branch M r F hF
  change (B.filter _).card ≤ _ at hm
  dsimp [B] at hsplit hm ⊢
  omega
/-- A closed actual graph face whose boundary is supported in a subgraph is
itself a component of that subgraph's complement. -/
theorem actual_face_reduce_to_boundary_subgraph
    (M : HyperellipticModel E S) (G K U : Set S)
    (hG : IsClosed G) (hKG : K ⊆ G) (hU : IsComplementComponent G U)
    (hboundary : frontier U ⊆ K) : IsComplementComponent K U := by
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  have hopen : IsOpen U := complementComponent_open hG hU
  have hUK : U ⊆ Kᶜ := fun x hx hxK => hU.2.2.1 hx (hKG hxK)
  refine ⟨hU.1,hU.2.1,hUK,?_⟩
  intro V hV hUV hVK
  have hcl : closure U ∩ V ⊆ U := by
    intro x hx
    by_contra hxU
    have hxfr : x ∈ frontier U := by rw [hopen.frontier_eq]; exact ⟨hx.1,hxU⟩
    exact hVK hx.2 (hboundary hxfr)
  have hVU : V ⊆ U := hV.isPreconnected.subset_of_closure_inter_subset hopen
    (by obtain ⟨x,hx⟩ := hU.1; exact ⟨x,hUV hx,hx⟩) hcl
  exact Set.Subset.antisymm hVU hUV

/-- The two actual traces of an unmarked low-degree face cannot form a
nonloop parallel bigon of distinct source classes. -/
theorem actual_unmarked_low_degree_two_nonparallel_traces
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (hsigma : sigma.Nonempty)
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (U : Set S) (hU : IsComplementComponent (⋃ i, (r i).val.image) U)
    (hdegree : (Finset.univ.filter (fun i =>
      (frontier U ∩ arcInterior M (r i)).Nonempty)).card < 3)
    (hfree : ∀ b ∈ M.cover.branch, b ∉ U) :
    ∃ i j : {v // v ∈ sigma}, i ≠ j ∧
      (frontier U ∩ arcInterior M (r i)).Nonempty ∧
      (frontier U ∩ arcInterior M (r j)).Nonempty ∧
      frontier U ⊆ (r i).val.image ∪ (r j).val.image ∧
      IsComplementComponent ((r i).val.image ∪ (r j).val.image) U ∧
      ((r i).val.map 0 ≠ (r i).val.map 1 →
        (r j).val.map 0 ≠ (r j).val.map 1 →
        markedArcEndset (r i).val ≠ markedArcEndset (r j).val) := by
  classical
  letI : Nonempty {v // v ∈ sigma} := hsigma.to_subtype
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨i,j,hij,hi,hj,hboundary⟩ := actual_unmarked_low_degree_two_traces M r U hU hdegree hfree
  have hG : IsClosed (⋃ i, (r i).val.image) :=
    (markedFamily_graph_compact (fun i => (r i).val)).isClosed
  have hiG : (r i).val.image ⊆ ⋃ k, (r k).val.image := fun x hx => Set.mem_iUnion.mpr ⟨i,hx⟩
  have hjG : (r j).val.image ⊆ ⋃ k, (r k).val.image := fun x hx => Set.mem_iUnion.mpr ⟨j,hx⟩
  refine ⟨i,j,hij,hi,hj,hboundary,
    actual_face_reduce_to_boundary_subgraph M _ _ U hG (Set.union_subset hiG hjG) hU hboundary,?_⟩
  intro hin hjn hends
  have hne : Quotient.mk (essentialArcSetoid M) (r i) ≠
      Quotient.mk (essentialArcSetoid M) (r j) := by
    rw [hr,hr]
    exact fun he => hij (Subtype.ext he)
  obtain ⟨b,hb,hbU⟩ := actual_bigon_face_contains_mark M (r i) (r j)
    hin hjn hends (hd i j hij) hne _ U hG hiG hjG hU hboundary
  exact hfree b hb hbU
end CurveComplex.HyperellipticModel


#print axioms CurveComplex.HyperellipticModel.actual_unmarked_low_degree_two_traces

#print axioms CurveComplex.HyperellipticModel.actual_low_degree_faces_card_le_unused_plus_unmarked

#print axioms CurveComplex.HyperellipticModel.actual_unmarked_low_degree_two_nonparallel_traces

namespace CurveComplex.HyperellipticModel
open Set
open scoped Classical BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance assemblyClassDecEq (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

/-- All numerical and actual-mark charging work is discharged. The only
remaining positive term counts genuinely unmarked actual low-degree faces. -/
theorem actual_bad_weighted_face_bound_before_cross_classification
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (F : Finset (Set S))
    (hF : ∀ U ∈ F, IsComplementComponent (⋃ i, (r i).val.image) U) :
    3 * F.card ≤ 2 * sigma.card +
      3 * (6 - (markedFamilyVertices (fun i => (r i).val)).card) +
      3 * ((F.filter (fun U => actualIncidentEdgeDegree M r U < 3)).filter
        (fun U => ∀ b ∈ M.cover.branch, b ∉ U)).card := by
  classical
  have hd := actual_bad_low_degree_deficit_bound M r hr hd hbad F hF
  have hm : (F.filter (fun U => actualIncidentEdgeDegree M r U < 3)).card ≤
      (6 - (markedFamilyVertices (fun i => (r i).val)).card) +
      ((F.filter (fun U => actualIncidentEdgeDegree M r U < 3)).filter
        (fun U => ∀ b ∈ M.cover.branch, b ∉ U)).card :=
    actual_low_degree_faces_card_le_unused_plus_unmarked M r F hF
  omega
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_bad_weighted_face_bound_before_cross_classification
