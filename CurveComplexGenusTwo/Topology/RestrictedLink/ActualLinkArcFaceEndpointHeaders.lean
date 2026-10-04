import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects
import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
namespace CurveComplex.HyperellipticModel
open Set CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance integrationLocalInstance_ActualLinkArcFaceEndpointHeaders_1 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
set_option maxHeartbeats 2000000
theorem actual_link_arc_face_has_interior_endpoint (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
    (τ : Finset (EssentialArcClass M)) (hτ : τ ∈ actualRestrictedLink M T)
    (r : {v // v ∈ T.val} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (O : Finset (EssentialArcClass M)) (hO : O ∈ actualObjectFamily M T.val)
    (U : Set S) (hOU : IsComplementComponent (actualObjectTrace M r O) U)
    (hUG : IsComplementComponent (⋃ v, (r v).val.image) U)
    (a : EssentialMarkedArc M) (w : EssentialArcClass M) (hw : w ∈ τ)
    (haw : Quotient.mk (essentialArcSetoid M) a = w)
    (hd : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v)))
    (hHit : (arcInterior M a ∩ U).Nonempty) :
    arcInterior M a ⊆ U ∧ a.val.image ⊆ closure U ∧
      (a.val.map 0 ∈ U ∨ a.val.map 1 ∈ U) := by
  classical
  have localize (M : HyperellipticModel E S) {I : Type} [Finite I]
      (r : I → EssentialMarkedArc M) (a : EssentialMarkedArc M)
      (hd : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v))) :
      ∃ U : Set S, IsComplementComponent (⋃ v, (r v).val.image) U ∧
        arcInterior M a ⊆ U ∧ a.val.image ⊆ closure U := by
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
    have hci : IsConnected (arcInterior M a) := by
      rw [← hi]
      have hc : IsConnected (Set.Ioo (0 : Interval) 1) :=
        ⟨⟨⟨(1:ℝ)/2, by constructor <;> norm_num⟩, by
            constructor
            · change (0 : ℝ) < 1/2; norm_num
            · change (1 : ℝ)/2 < 1; norm_num⟩,
          isPreconnected_Ioo⟩
      exact hc.image a.val.map a.val.continuous.continuousOn
    have hdense : a.val.image ⊆ closure (arcInterior M a) := by
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
    let G := ⋃ v, (r v).val.image
    have havoid : arcInterior M a ⊆ Gᶜ := by
      intro x hx hxG
      obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hxG
      exact Set.disjoint_left.mp (hd v) hx ⟨hv,hx.2⟩
    obtain ⟨x,hx⟩ := hci.nonempty
    let U := connectedComponentIn Gᶜ x
    have hU : IsComplementComponent G U :=
      complementComponent_iff_componentIn.mpr ⟨x,havoid hx,rfl⟩
    have hsub : arcInterior M a ⊆ U := hci.isPreconnected.subset_connectedComponentIn hx havoid
    have hclU : a.val.image ⊆ closure U := hdense.trans (closure_mono hsub)
    exact ⟨U,hU,hsub,hclU⟩
  have uniform (M : HyperellipticModel E S) (σ : Finset (EssentialArcClass M))
      (O : Finset (EssentialArcClass M)) (hO : O ∈ actualObjectFamily M σ) :
      ∃ v ∈ σ, ∀ w ∈ O, classEndpoints M w = classEndpoints M v := by
    classical
    simp only [actualObjectFamily,Finset.mem_union,Finset.mem_image,Finset.mem_filter] at hO
    rcases hO with ⟨v,⟨hv,hloop⟩,rfl⟩ | ⟨v,⟨hv,hn,hcard⟩,rfl⟩
    · refine ⟨v,hv,?_⟩
      intro w hw
      exact congrArg (classEndpoints M) (Finset.mem_singleton.mp hw)
    · refine ⟨v,hv,?_⟩
      intro w hw
      exact (Finset.mem_filter.mp hw).2.2
  have labels (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
      (τ : Finset (EssentialArcClass M)) (hτ : τ ∈ actualRestrictedLink M T) :
      (∀ w ∈ τ, ¬ (actualArcLabels M).isLoop w) ∧
      (∀ w ∈ τ, ∀ z ∈ T.val ∪ τ, z ≠ w →
        ¬ (actualArcLabels M).isLoop z → classEndpoints M z ≠ classEndpoints M w) := by
    classical
    change Disjoint T.val τ ∧ T.val ∪ τ ∈ actualA M ∧
      badVertices (actualArcLabels M) (T.val ∪ τ) = T.val at hτ
    have good : ∀ w ∈ τ, w ∉ badVertices (actualArcLabels M) (T.val ∪ τ) := by
      intro w hw
      rw [hτ.2.2]
      exact fun hwT => Finset.disjoint_left.mp hτ.1 hwT hw
    have nonloop : ∀ w ∈ τ, ¬ (actualArcLabels M).isLoop w := by
      intro w hw hl
      exact good w hw (Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hw, Or.inl hl⟩)
    refine ⟨nonloop, ?_⟩
    intro w hw z hz hzw hzl he
    exact good w hw (Finset.mem_filter.mpr
      ⟨Finset.mem_union_right _ hw, Or.inr ⟨z, hz, hzw, nonloop w hw, hzl, he⟩⟩)
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  obtain ⟨W,hW,hint,hcl⟩ := localize M r a hd
  have heW : W = U := by
    by_contra hn
    obtain ⟨x,hx,hxU⟩ := hHit
    exact Set.disjoint_left.mp (complementComponents_disjoint hW hUG hn) (hint hx) hxU
  rw [heW] at hint hcl
  refine ⟨hint,hcl,?_⟩
  obtain ⟨v,hv,huniform⟩ := uniform M T.val O hO
  have hopen := complementComponent_open (actualObjectTrace_compact M r O).isClosed hOU
  have hfront := complementComponent_frontier_subset (actualObjectTrace_compact M r O).isClosed hOU
  have boundaryMark (x : S) (hx : x ∈ frontier U) (hb : x ∈ M.cover.branch) :
      x ∈ classEndpoints M v := by
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hfront hx)
    obtain ⟨hjO,hxj⟩ := Set.mem_iUnion.mp hj
    have hend : x ∈ (markedArcEndset (r j).val : Set S) := by
      rw [← markedArc_image_inter_branch]
      exact ⟨hxj,hb⟩
    have hlabel : markedArcEndset (r j).val = classEndpoints M j.val :=
      (markedArcEndset_eq_classEndpoints M (r j)).trans (congrArg (classEndpoints M) (hr j))
    rw [hlabel,huniform j.val hjO] at hend
    exact hend
  by_contra hn
  push_neg at hn
  have hfront0 : a.val.map 0 ∈ frontier U := by
    rw [hopen.frontier_eq]
    exact ⟨hcl ⟨0,rfl⟩,hn.1⟩
  have hfront1 : a.val.map 1 ∈ frontier U := by
    rw [hopen.frontier_eq]
    exact ⟨hcl ⟨1,rfl⟩,hn.2⟩
  have hlabel : markedArcEndset a.val = classEndpoints M w :=
    (markedArcEndset_eq_classEndpoints M a).trans (congrArg (classEndpoints M) haw)
  have hsub : classEndpoints M w ⊆ classEndpoints M v := by
    rw [← hlabel]
    intro x hx
    simp only [markedArcEndset,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact boundaryMark _ hfront0 a.val.start_marked
    · exact boundaryMark _ hfront1 a.val.end_marked
  obtain ⟨hnonloop,hfresh⟩ := labels M p T τ hτ
  have hwcard := (actualArcLabels M).nonloop_endpoint_card w (hnonloop w hw)
  change (classEndpoints M w).card = 2 at hwcard
  have hvcard : (classEndpoints M v).card = 2 := by
    have hle := Finset.card_le_card hsub
    rcases classEndpoints_card M v with hvcard | hvcard
    · omega
    · exact hvcard
  have hvnonloop : ¬ (actualArcLabels M).isLoop v := by
    change (classEndpoints M v).card ≠ 1
    omega
  have hneq : v ≠ w := by
    intro he
    change Disjoint T.val τ ∧ _ at hτ
    exact Finset.disjoint_left.mp hτ.1 hv (he.symm ▸ hw)
  have heq : classEndpoints M w = classEndpoints M v :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  exact hfresh w hw v (Finset.mem_union_left _ hv) hneq hvnonloop heq.symm
end CurveComplex.HyperellipticModel
