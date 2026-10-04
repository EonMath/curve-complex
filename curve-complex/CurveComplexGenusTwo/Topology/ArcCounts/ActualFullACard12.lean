import CurveComplexGenusTwo.Topology.ArcCounts.Card12FinalAssembly
import CurveComplexGenusTwo.Topology.ArcCounts.NonloopCard12Assembly
namespace CurveComplex.HyperellipticModel
open Set
open scoped Classical BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actualA_card_le_twelve (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) (hσ : σ ∈ actualA M) :
    σ.card ≤ 12 := by
  classical
  by_cases hσne : σ.Nonempty
  swap
  · have hσempty := Finset.not_nonempty_iff_eq_empty.mp hσne
    simp [hσempty]
  obtain ⟨r,hr,hd⟩ := hσ
  by_cases hnonloop : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1
  · exact actual_nonloop_class_family_card_le_twelve M σ hσne r hr hd hnonloop
  by_cases hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) σ = σ
  · have hbad' : @CurveGenusTwo.Filtration.badVertices (EssentialArcClass M) S
        M.finalClassDecEq (actualArcLabels M) σ = σ := by
      convert hbad using 1 <;> congr 1
      exact Subsingleton.elim _ _
    exact actual_bad_simplex_card_le_twelve M σ hσne r hr hd hbad'
  let I := {v // v ∈ σ}
  let G : Set S := ⋃ i : I, (r i).val.image
  let touch : Set S → I → Prop := fun U i => (frontier U ∩ arcInterior M (r i)).Nonempty
  have hfacecount : ∀ (F : Finset (Set S)),
      (∀ U ∈ F, IsComplementComponent G U) →
      ∀ i : I, actualEdgeIncidentFaceCount M r F i ≤ 2 := by
    intro F hF i
    by_cases hl : (r i).val.map 0 = (r i).val.map 1
    swap
    · exact actual_nonloop_family_edge_incident_face_count_le_two M r hd i hl F hF
    let rr : {v : I // v ≠ i} → EssentialMarkedArc M := fun v => r v.val
    have hgraph : G = (⋃ v, (rr v).val.image) ∪ (r i).val.image := by
      ext x
      constructor
      · intro hx
        obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hx
        by_cases hvu : v = i
        · exact Or.inr (hvu ▸ hv)
        · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨v,hvu⟩,hv⟩)
      · rintro (hx | hx)
        · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_iUnion.mpr ⟨v.val,hv⟩
        · exact Set.mem_iUnion.mpr ⟨i,hx⟩
    obtain ⟨T,hTcard,hT⟩ := actual_loop_edge_incident_faces_atMostTwo M rr (r i) hl
      (fun v => hd i v.val v.property.symm)
    calc
      actualEdgeIncidentFaceCount M r F i ≤ T.card := Finset.card_le_card (by
        intro U hU
        obtain ⟨hUF,hUi⟩ := Finset.mem_filter.mp hU
        exact hT U (hgraph ▸ hF U hUF) hUi)
      _ = 2 := hTcard
  let separated : I → Prop := fun i => ∃ U V : Set S,
    IsComplementComponent G U ∧ touch U i ∧ IsComplementComponent G V ∧
      touch V i ∧ U ≠ V
  let degree : Set S → ℕ := fun U => ∑ i : I,
    if touch U i then (if separated i then 1 else 2) else 0
  have hsum : ∀ (F : Finset (Set S)),
      (∀ U ∈ F, IsComplementComponent G U) →
      (∑ U ∈ F, degree U) ≤ 2 * σ.card := by
    intro F hF
    change (∑ U ∈ F, ∑ i : I, if touch U i then (if separated i then 1 else 2) else 0) ≤ _
    rw [Finset.sum_comm]
    have hi : ∀ i : I, (∑ U ∈ F,
        if touch U i then (if separated i then 1 else 2) else 0) ≤ 2 := by
      intro i
      by_cases hs : separated i
      · simpa only [hs,ite_true,Finset.sum_boole,Nat.cast_id,actualEdgeIncidentFaceCount,touch] using hfacecount F hF i
      · have hcard : (F.filter (fun U => touch U i)).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro U hU V hV
          by_contra hne
          obtain ⟨hUF,hUi⟩ := Finset.mem_filter.mp hU
          obtain ⟨hVF,hVi⟩ := Finset.mem_filter.mp hV
          exact hs ⟨U,V,hF U hUF,hUi,hF V hVF,hVi,hne⟩
        have he : (∑ U ∈ F, if touch U i then (if separated i then 1 else 2) else 0) =
            2 * (F.filter (fun U => touch U i)).card := by
          simp only [hs,ite_false]
          rw [← Finset.sum_filter]
          simp [Nat.mul_comm]
        rw [he]
        omega
    calc
      _ ≤ ∑ _i : I, (2 : ℕ) := Finset.sum_le_sum (fun i _ => hi i)
      _ = 2 * σ.card := by simp [I,Nat.mul_comm]
  have hcontactBound : ∀ U : Set S, actualIncidentEdgeDegree M r U ≤ degree U := by
    intro U
    rw [actualIncidentEdgeDegree,Finset.card_eq_sum_ones,Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i hi
    by_cases ht : touch U i <;> by_cases hs : separated i <;>
      simp [degree,touch,ht,hs] at *
  have hseparatedLow : ∀ (U : Set S) (i j : I), i ≠ j → touch U i → touch U j →
      degree U < 3 → separated i := by
    intro U i j hij hi hj hdeg
    by_contra hs
    have ht : (∑ k ∈ ({i,j} : Finset I),
        if touch U k then (if separated k then 1 else 2) else 0) ≤ degree U := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro k hk hkn
      exact Nat.zero_le _
    have he : (∑ k ∈ ({i,j} : Finset I),
        if touch U k then (if separated k then 1 else 2) else 0) =
        2 + (if separated j then 1 else 2) := by
      simp [hij,hi,hj,hs]
    rw [he] at ht
    split_ifs at ht <;> omega
  have hsecond : ∀ (K U : Set S), IsClosed K → K ⊆ G →
      IsComplementComponent G U → IsComplementComponent K U →
      ∀ u : I, (r u).val.image ⊆ K → touch U u → separated u →
      ∃ W, IsComplementComponent K W ∧ W ≠ U ∧ touch W u := by
    intro K U hK hKG hU hUK u huK htouch hs
    letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
    obtain ⟨A,B,hA,htA,hB,htB,hAB⟩ := hs
    have hv : ∃ V, IsComplementComponent G V ∧ touch V u ∧ V ≠ U := by
      by_cases he : A = U
      · exact ⟨B,hB,htB,by intro heB; exact hAB (he.trans heB.symm)⟩
      · exact ⟨A,hA,htA,he⟩
    obtain ⟨V,hV,hcontact,hVU⟩ := hv
    obtain ⟨x,hxV⟩ := hV.1
    have hxK : x ∈ Kᶜ := fun h => hV.2.2.1 hxV (hKG h)
    let W := connectedComponentIn Kᶜ x
    have hW : IsComplementComponent K W :=
      complementComponent_iff_componentIn.mpr ⟨x,hxK,rfl⟩
    have hVW : V ⊆ W := hV.2.1.isPreconnected.subset_connectedComponentIn hxV
      (fun y hy h => hV.2.2.1 hy (hKG h))
    have hWU : W ≠ U := by
      intro he
      exact Set.disjoint_left.mp (complementComponents_disjoint hV hU hVU) hxV (he ▸ hVW hxV)
    obtain ⟨z,hzV,hzu⟩ := hcontact
    have hzcl : z ∈ closure W := closure_mono hVW (frontier_subset_closure hzV)
    have hznot : z ∉ W := fun h => hW.2.2.1 h (huK hzu.1)
    have hWopen : IsOpen W := by
      obtain ⟨y,hy,he⟩ := complementComponent_iff_componentIn.mp hW
      rw [he]
      exact hK.isOpen_compl.connectedComponentIn
    refine ⟨W,hW,hWU,z,?_,hzu⟩
    rw [frontier, hWopen.interior_eq]
    exact ⟨hzcl,hznot⟩
  have hrejectUnique : ∀ (U : Set S), IsComplementComponent G U →
      ∀ i j : I, IsComplementComponent ((r i).val.image ∪ (r j).val.image) U →
      touch U j → separated j →
      (∃ W, IsComplementComponent ((r i).val.image ∪ (r j).val.image) W ∧
        ∀ V, IsComplementComponent ((r i).val.image ∪ (r j).val.image) V →
          touch V j → V = W) → False := by
    intro U hU i j hUK hj hs huniq
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨W,hWK,hunique⟩ := huniq
    have hUeq := hunique U hUK hj
    obtain ⟨V,hVK,hVU,hVcontact⟩ := hsecond ((r i).val.image ∪ (r j).val.image) U
      ((markedArc_image_compact (r i).val).isClosed.union (markedArc_image_compact (r j).val).isClosed)
      (Set.union_subset (Set.subset_iUnion (fun v => (r v).val.image) i)
        (Set.subset_iUnion (fun v => (r v).val.image) j)) hU hUK j Set.subset_union_right hj hs
    exact hVU ((hunique V hVK hVcontact).trans hUeq.symm)
  have hnotMixed : ∀ (U : Set S), IsComplementComponent G U →
      ∀ i j : I, i ≠ j → IsComplementComponent ((r i).val.image ∪ (r j).val.image) U →
      touch U j → separated j → (r i).val.map 0 = (r i).val.map 1 →
      (r j).val.map 0 ≠ (r j).val.map 1 → False := by
    intro U hU i j hij hUK hj hs hiLoop hjNonloop
    have he : (r i).val.image ∩ (r j).val.image =
        ((markedArcEndset (r i).val : Set S) ∩ (markedArcEndset (r j).val : Set S)) :=
      markedArc_disjoint_interiors_inter_image _ _ (hd i j hij)
    have hemem : ∀ x, x ∈ (r i).val.image ∩ (r j).val.image ↔
        x = (r i).val.map 0 ∧ (x = (r j).val.map 0 ∨ x = (r j).val.map 1) := by
      intro x
      rw [he]
      simp [markedArcEndset,hiLoop]
    by_cases h0 : (r i).val.map 0 = (r j).val.map 0
    · have hmeet : (r i).val.image ∩ (r j).val.image = {(r j).val.map 0} := by
        ext x
        rw [hemem]
        simp only [h0,Set.mem_singleton_iff]
        tauto
      exact hrejectUnique U hU i j hUK hj hs
        (actual_loop_single_slit_unique_incident_face M (r i) (r j) hiLoop hjNonloop hmeet)
    · by_cases h1 : (r i).val.map 0 = (r j).val.map 1
      · have hmeet : (r i).val.image ∩ (r j).val.image = {(r j).val.map 1} := by
          ext x
          rw [hemem]
          simp only [h1,Set.mem_singleton_iff]
          tauto
        exact hrejectUnique U hU i j hUK hj hs
          (actual_loop_finish_slit_unique_incident_face M (r i) (r j) hiLoop hjNonloop hmeet)
      · have hdis : Disjoint (r i).val.image (r j).val.image := by
          apply Set.disjoint_left.mpr
          intro x hxi hxj
          obtain ⟨hxi,hxj⟩ := (hemem x).mp ⟨hxi,hxj⟩
          rcases hxj with hxj | hxj
          · exact h0 (hxi.symm.trans hxj)
          · exact h1 (hxi.symm.trans hxj)
        exact hrejectUnique U hU i j hUK hj hs
          (actual_loop_disjoint_nonloop_unique_incident_face M (r i) (r j) hiLoop hjNonloop hdis)
  letI : Nonempty I := hσne.to_subtype
  have hcross : ∀ (U : Set S), IsComplementComponent G U → degree U < 3 →
      (∀ b ∈ M.cover.branch, b ∉ U) → ∃ i j : I,
      connectedComponentIn G ((r i).val.map 0) ≠ connectedComponentIn G ((r j).val.map 0) ∧
      (frontier U ∩ (r i).val.image).Nonempty ∧ (frontier U ∩ (r j).val.image).Nonempty := by
    intro U hU hdegree hfree
    letI : T2Space S := M.sphere.symm.t2Space
    have hdcontact : actualIncidentEdgeDegree M r U < 3 :=
      lt_of_le_of_lt (hcontactBound U) hdegree
    obtain ⟨i,j,hij,hi,hj,hboundary,hpair,hparallel⟩ :=
      actual_unmarked_low_degree_two_nonparallel_traces M hσne r hr hd U hU hdcontact hfree
    have hsi : separated i := hseparatedLow U i j hij hi hj hdegree
    have hsj : separated j := hseparatedLow U j i hij.symm hj hi hdegree
    refine ⟨i,j,?_,?_,?_⟩
    · intro hsame
      by_cases ha : (r i).val.map 0 = (r i).val.map 1
      · by_cases hb : (r j).val.map 0 = (r j).val.map 1
        · by_cases hbase : (r i).val.map 0 = (r j).val.map 0
          · have hmeet : (r i).val.image ∩ (r j).val.image = {(r i).val.map 0} := by
              rw [markedArc_disjoint_interiors_inter_image _ _ (hd i j hij)]
              change (({(r i).val.map 0, (r i).val.map 1} : Finset S) : Set S) ∩
                (({(r j).val.map 0, (r j).val.map 1} : Finset S) : Set S) = {(r i).val.map 0}
              simp [← ha,← hb,← hbase]
            have he := actual_common_basepoint_loops_empty_face_class_equality M (r i) (r j)
              ha hb hbase hmeet G U (markedFamily_graph_compact (fun k => (r k).val)).isClosed
              (Set.subset_iUnion (fun k => (r k).val.image) i)
              (Set.subset_iUnion (fun k => (r k).val.image) j) hU hboundary hfree
            rw [hr,hr] at he
            exact hij (Subtype.ext he)
          · have hdis : Disjoint (r i).val.image (r j).val.image := by
              apply Set.disjoint_left.mpr
              intro x hxi hxj
              have hh := markedArc_disjoint_interiors_inter_image (r i).val (r j).val (hd i j hij)
              have hx := hh ▸ (show x ∈ (r i).val.image ∩ (r j).val.image from ⟨hxi,hxj⟩)
              have hxi : x = (r i).val.map 0 := by simpa [markedArcEndset,ha] using hx.1
              have hxj : x = (r j).val.map 0 := by simpa [markedArcEndset,hb] using hx.2
              exact hbase (hxi.symm.trans hxj)
            exact actual_disjoint_loops_face_separates_graph_components M r i j ha hb hdis U
              hU hpair hi hj hsame
        · exact hnotMixed U hU i j hij hpair hj hsj ha hb
      · by_cases hb : (r j).val.map 0 = (r j).val.map 1
        · exact hnotMixed U hU j i hij.symm (by simpa [Set.union_comm] using hpair) hi hsi hb ha
        ·
          obtain ⟨p,hp⟩ := hpair.1
          have hc := actual_nonparallel_nonloop_pair_complement_connected M (r i) (r j)
            ha hb (hd i j hij)
            (hparallel ha hb) p (hpair.2.2.1 hp)
          have hwhole : U = ((r i).val.image ∪ (r j).val.image)ᶜ :=
            (hpair.2.2.2 _ hc hpair.2.2.1 (fun x hx => hx)).symm
          have hsubset : M.cover.branch ⊆ markedArcEndset (r i).val ∪ markedArcEndset (r j).val := by
            intro b hb
            have hnot := hfree b hb
            rw [hwhole] at hnot
            have hbimg : b ∈ (r i).val.image ∪ (r j).val.image := by
              by_contra h
              exact hnot h
            rcases hbimg with hbi | hbj
            · apply Finset.mem_union_left
              change b ∈ (markedArcEndset (r i).val : Set S)
              rw [← markedArc_image_inter_branch]
              exact ⟨hbi,hb⟩
            · apply Finset.mem_union_right
              change b ∈ (markedArcEndset (r j).val : Set S)
              rw [← markedArc_image_inter_branch]
              exact ⟨hbj,hb⟩
          have hcard := Finset.card_le_card hsubset
          have hu := Finset.card_union_le (markedArcEndset (r i).val) (markedArcEndset (r j).val)
          have hi : (markedArcEndset (r i).val).card = 2 := by simp [markedArcEndset,ha]
          have hj : (markedArcEndset (r j).val).card = 2 := by simp [markedArcEndset,hb]
          rw [M.cover.branch_card] at hcard
          omega
    · obtain ⟨x,hx,hxi⟩ := hi
      exact ⟨x,hx,hxi.1⟩
    · obtain ⟨x,hx,hxj⟩ := hj
      exact ⟨x,hx,hxj.1⟩
  obtain ⟨F,hEuler,hF⟩ := actual_strong_quantitative_euler_lower_bound M r hd
  apply card12_of_one_weighted_face_family M σ hσne r hr hd F hF hEuler
  intro hF
  let B := F.filter (fun U => degree U < 3)
  let L := B.filter (fun U => ∀ b ∈ M.cover.branch, b ∉ U)
  have hLF : ∀ U ∈ L, IsComplementComponent G U := by
    intro U hU
    exact hF U (Finset.mem_filter.mp (Finset.mem_filter.mp hU).1).1
  have hLCross : ∀ U ∈ L, ∃ i j : I,
      connectedComponentIn G ((r i).val.map 0) ≠ connectedComponentIn G ((r j).val.map 0) ∧
      (frontier U ∩ (r i).val.image).Nonempty ∧ (frontier U ∩ (r j).val.image).Nonempty := by
    intro U hU
    obtain ⟨hUB,hfree⟩ := Finset.mem_filter.mp hU
    obtain ⟨hUF,hdeg⟩ := Finset.mem_filter.mp hUB
    exact hcross U (hF U hUF) hdeg hfree
  have hforest := actual_cross_component_faces_card_le_components_sub_one M σ hσne r hr hd
    L hLF hLCross
  have hmarked : (B.filter (fun U => ∃ b, b ∈ M.cover.branch ∧ b ∈ U)).card ≤
      6 - (markedFamilyVertices (fun i => (r i).val)).card := by
    apply actual_marked_faces_card_le_unused_branch M (fun i => (r i).val)
    · intro U hU
      exact hF U (Finset.mem_filter.mp (Finset.mem_filter.mp hU).1).1
    · intro U hU
      exact (Finset.mem_filter.mp hU).2
  have hsplit := Finset.card_filter_add_card_filter_not (s := B)
    (fun U => ∃ b, b ∈ M.cover.branch ∧ b ∈ U)
  have hnot : B.filter (fun U => ¬ ∃ b, b ∈ M.cover.branch ∧ b ∈ U) = L := by
    ext U
    simp only [L,Finset.mem_filter,not_exists,not_and]
  rw [hnot] at hsplit
  have hp : ∀ U ∈ F, (3 : ℕ) ≤ degree U +
      3 * (if degree U < 3 then 1 else 0) := by
    intro U hUF
    by_cases h : degree U < 3
    · simp [h]
    · simp only [h,ite_false,mul_zero,add_zero]
      omega
  have hpre := Finset.sum_le_sum hp
  have hcount : (∑ U ∈ F, 3 * (if degree U < 3 then 1 else 0)) = 3 * B.card := by
    rw [← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_boole,Nat.cast_id]
    rfl
  simp only [Finset.sum_add_distrib] at hpre
  rw [hcount] at hpre
  have htotal := hsum F hF
  have h3 : 3 * F.card ≤ (∑ U ∈ F, degree U) + 3 * B.card := by
    simpa [Nat.mul_comm] using hpre
  omega
end CurveComplex.HyperellipticModel
