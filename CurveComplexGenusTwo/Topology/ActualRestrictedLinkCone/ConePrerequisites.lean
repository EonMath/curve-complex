import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualWholeInteriorAxisChart
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualGoodFreeGapHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualObjectGapChartHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualGoodGapArcHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualGapArcLinkHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualLinkArcFaceEndpointHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.RestrictedLinkLabelsHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualObjectEndpointUniformHeaders
import CurveComplexGenusTwo.Filtration.Geometry.MarkedArcPrimitives
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualOneMarkPlanarArcHeaders
import Schoenflies.JordanClosed
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualArcFaceLocalizationHeaders


namespace CurveComplex.HyperellipticModel
open Set Schoenflies CurveGenusTwo.Filtration
open scoped Classical
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

/-- A positive bad stratum produces a genuine complementary free face,
its marked Jordan chart, and an essential nonloop arc in the restricted link.
All representatives and geometric witnesses are outputs. -/
theorem actual_positive_stratum_good_face_apex (M : HyperellipticModel E S)
    (p : ℕ) (hp : 1 ≤ p) (T : ActualStratum M p) :
    ∃ r : {w // w ∈ T.val} → EssentialMarkedArc M,
      (∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val) ∧
      (∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z))) ∧
    ∃ O : Finset (EssentialArcClass M), ∃ U : Set S,
      O ∈ actualObjectFamily M T.val ∧
      IsComplementComponent (actualObjectTrace M r O) U ∧
      IsComplementComponent (⋃ w, (r w).val.image) U ∧
      (∀ Q ∈ actualObjectFamily M T.val, Q ≠ O →
        ¬ actualObjectTrace M r Q ⊆ closure U) ∧
      1 ≤ (M.cover.branch.filter (fun x => x ∈ U)).card ∧
      (M.cover.branch.filter (fun x => x ∈ U)).card ≤ 2 ∧
    ∃ C : Set Plane, ∃ f : Plane → S, ∃ z : Plane,
      IsJordanCurve C ∧ Topology.IsOpenEmbedding f ∧
      U = f '' inside C ∧ z ∈ C ∧ f z ∈ M.cover.branch ∧
    ∃ a : EssentialMarkedArc M,
      a.val.map 0 ≠ a.val.map 1 ∧ arcInterior M a ⊆ U ∧
      (a.val.map 0 ∈ U ∨ a.val.map 1 ∈ U) ∧
      ({Quotient.mk (essentialArcSetoid M) a} : Finset (EssentialArcClass M)) ∈
        actualRestrictedLink M T := by
  classical
  obtain ⟨r, hr, hd⟩ := (show IsArcSimplex M T.val from T.property.1)
  have hbad := T.property.2.2
  have hne : T.val.Nonempty := Finset.card_pos.mp (by rw [T.property.2.1]; omega)
  obtain ⟨O, U, hO, hOU, hUG, hfree, hlo, hhi⟩ :=
    actual_good_free_gap M r hr hd hbad hne
  obtain ⟨C, hC, f, hf, heU, z, hz, hzB⟩ :=
    actual_object_gap_marked_inside_chart M r hr hd hbad O hO U hOU
  obtain ⟨a, haneq, haint, haend⟩ :=
    actual_good_gap_arc M U C hC f hf heU z hz hzB hlo hhi
  exact ⟨r, hr, hd, O, U, hO, hOU, hUG, hfree, hlo, hhi,
    C, f, z, hC, hf, heU, hz, hzB, a, haneq, haint, haend,
    actual_gap_arc_link_vertex M T.val r hr hd hbad U hUG.2.2.1 a haneq haint haend⟩

/-- Restricted-link classes with the apex's endpoint pair are necessarily
that apex: a second such class would become bad in the original filtration. -/
theorem actual_link_endpoint_pair_unique (M : HyperellipticModel E S)
    (p : ℕ) (T : ActualStratum M p) (τ : Finset (EssentialArcClass M))
    (hτ : τ ∈ actualRestrictedLink M T)
    {v w : EssentialArcClass M} (hv : v ∈ τ) (hw : w ∈ τ)
    (he : classEndpoints M v = classEndpoints M w) : v = w := by
  classical
  obtain ⟨hn, hf⟩ := actualRestrictedLink_fresh_labels M p T τ hτ
  by_contra hne
  exact hf w hw v (Finset.mem_union_right _ hv) hne (hn v hv) he

/-- Each interior mark of a good one-mark face forces the same endpoint
for every restricted-link representative that enters that face. -/
theorem actual_one_mark_face_entering_endpoint (M : HyperellipticModel E S)
    (p : ℕ) (T : ActualStratum M p) (τ : Finset (EssentialArcClass M))
    (hτ : τ ∈ actualRestrictedLink M T)
    (r : {v // v ∈ T.val} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (O : Finset (EssentialArcClass M)) (hO : O ∈ actualObjectFamily M T.val)
    (U : Set S) (hOU : IsComplementComponent (actualObjectTrace M r O) U)
    (hUG : IsComplementComponent (⋃ v, (r v).val.image) U)
    (q : S) (hmarks : ∀ x ∈ U, x ∈ M.cover.branch → x = q)
    (a : EssentialMarkedArc M) (w : EssentialArcClass M) (hw : w ∈ τ)
    (haw : Quotient.mk (essentialArcSetoid M) a = w)
    (hd : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v)))
    (hHit : (arcInterior M a ∩ U).Nonempty) :
    arcInterior M a ⊆ U ∧ a.val.image ⊆ closure U ∧ q ∈ classEndpoints M w := by
  classical
  obtain ⟨hi, hc, he⟩ := actual_link_arc_face_has_interior_endpoint
    M p T τ hτ r hr O hO U hOU hUG a w hw haw hd hHit
  refine ⟨hi, hc, ?_⟩
  rw [← haw, ← markedArcEndset_eq_classEndpoints]
  rcases he with he | he
  · have hq := hmarks _ he a.val.start_marked
    simp [markedArcEndset, ← hq]
  · have hq := hmarks _ he a.val.end_marked
    simp [markedArcEndset, ← hq]
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set CurveGenusTwo.Filtration
open scoped Classical
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

/-- A one-mark free face has all boundary labels from one actual bad object;
any link arc meeting it joins its unique interior mark to those labels. -/
theorem actual_one_mark_link_face_boundary_labels (M : HyperellipticModel E S)
    (p : ℕ) (T : ActualStratum M p)
    (τ : Finset (EssentialArcClass M)) (hτ : τ ∈ actualRestrictedLink M T)
    (r : {v // v ∈ T.val} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (O : Finset (EssentialArcClass M)) (hO : O ∈ actualObjectFamily M T.val)
    (U : Set S) (hOU : IsComplementComponent (actualObjectTrace M r O) U)
    (hUG : IsComplementComponent (⋃ v, (r v).val.image) U)
    (q : S) (hmarks : ∀ z ∈ U, z ∈ M.cover.branch → z = q) :
    ∃ v ∈ T.val, (∀ z ∈ frontier U, z ∈ M.cover.branch → z ∈ classEndpoints M v) ∧
      ∀ (a : EssentialMarkedArc M) (w : EssentialArcClass M),
      w ∈ τ → Quotient.mk (essentialArcSetoid M) a = w →
      (∀ v, Disjoint (arcInterior M a) (arcInterior M (r v))) →
      (arcInterior M a ∩ U).Nonempty →
      q ∈ classEndpoints M w ∧ classEndpoints M w ⊆ insert q (classEndpoints M v) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  obtain ⟨v, hv, huniform⟩ := actual_object_endpoint_labels_uniform M T.val O hO
  have hopen := complementComponent_open (actualObjectTrace_compact M r O).isClosed hOU
  have hfront := complementComponent_frontier_subset (actualObjectTrace_compact M r O).isClosed hOU
  have boundaryMark (x : S) (hx : x ∈ frontier U) (hb : x ∈ M.cover.branch) :
      x ∈ classEndpoints M v := by
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hfront hx)
    obtain ⟨hjO, hxj⟩ := Set.mem_iUnion.mp hj
    have hend : x ∈ (markedArcEndset (r j).val : Set S) := by
      rw [← markedArc_image_inter_branch]
      exact ⟨hxj, hb⟩
    have hlabel : markedArcEndset (r j).val = classEndpoints M j.val :=
      (markedArcEndset_eq_classEndpoints M (r j)).trans
        (congrArg (classEndpoints M) (hr j))
    rw [hlabel, huniform j.val hjO] at hend
    exact hend
  refine ⟨v, hv, boundaryMark, ?_⟩
  intro a w hw haw hd hHit
  obtain ⟨hi, hc, he⟩ := actual_link_arc_face_has_interior_endpoint
    M p T τ hτ r hr O hO U hOU hUG a w hw haw hd hHit
  have endpoint (t : Interval) (hb : a.val.map t ∈ M.cover.branch) :
      a.val.map t ∈ insert q (classEndpoints M v) := by
    by_cases hin : a.val.map t ∈ U
    · exact Finset.mem_insert.mpr (Or.inl (hmarks _ hin hb))
    · have hf : a.val.map t ∈ frontier U := by
        rw [hopen.frontier_eq]
        exact ⟨hc ⟨t, rfl⟩, hin⟩
      exact Finset.mem_insert.mpr (Or.inr (boundaryMark _ hf hb))
  constructor
  · rw [← haw, ← markedArcEndset_eq_classEndpoints]
    rcases he with he | he
    · have hq := hmarks _ he a.val.start_marked
      simp [markedArcEndset, ← hq]
    · have hq := hmarks _ he a.val.end_marked
      simp [markedArcEndset, ← hq]
  · rw [← haw, ← markedArcEndset_eq_classEndpoints]
    intro x hx
    simp only [markedArcEndset, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact endpoint 0 a.val.start_marked
    · exact endpoint 1 a.val.end_marked

/-- Distinct good classes in an endpoint star inject into its other endpoints.
This is the finite bound used to handle one-mark-face spokes. -/
theorem actual_link_endpoint_star_card (M : HyperellipticModel E S)
    (p : ℕ) (T : ActualStratum M p) (τ : Finset (EssentialArcClass M))
    (hτ : τ ∈ actualRestrictedLink M T) (F : Finset (EssentialArcClass M))
    (hF : F ⊆ τ) (q : S) (e : Finset S)
    (hq : ∀ w ∈ F, q ∈ classEndpoints M w)
    (hends : ∀ w ∈ F, classEndpoints M w ⊆ insert q e) : F.card ≤ e.card := by
  classical
  obtain ⟨hn, hf⟩ := actualRestrictedLink_fresh_labels M p T τ hτ
  have other (w : {w // w ∈ F}) : ∃ x ∈ e, x ≠ q ∧ x ∈ classEndpoints M w.val := by
    have hcard := (actualArcLabels M).nonloop_endpoint_card w.val (hn _ (hF w.property))
    change (classEndpoints M w.val).card = 2 at hcard
    obtain ⟨x, hx, hxq⟩ := Finset.exists_mem_ne (by omega : 1 < (classEndpoints M w.val).card) q
    refine ⟨x, ?_, hxq, hx⟩
    exact (Finset.mem_insert.mp (hends _ w.property hx)).resolve_left hxq
  let g : {w // w ∈ F} → {x // x ∈ e} := fun w =>
    ⟨(other w).choose, (other w).choose_spec.1⟩
  apply Finset.card_le_card_of_injective (f := g)
  intro u w hgw
  have hu := (other u).choose_spec.2
  have hw := (other w).choose_spec.2
  have gx : (other u).choose = (other w).choose := congrArg Subtype.val hgw
  have pair (v : {v // v ∈ F}) :
      classEndpoints M v.val = {q, (other v).choose} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hq _ v.property
      · have hx := Finset.mem_singleton.mp hx
        exact hx ▸ (other v).choose_spec.2.2
    · have hc := (actualArcLabels M).nonloop_endpoint_card v.val (hn _ (hF v.property))
      change (classEndpoints M v.val).card = 2 at hc
      simp [hc, (other v).choose_spec.2.1.symm]
  apply Subtype.ext
  by_contra hne
  apply hf w.val (hF w.property) u.val (Finset.mem_union_right _ (hF u.property)) hne
    (hn _ (hF u.property))
  rw [pair u, pair w, gx]
/-- At most two actual restricted-link classes enter a one-mark good face,
including the loop-object case where the boundary has only one label. -/
theorem actual_one_mark_face_entering_card_le_two (M : HyperellipticModel E S)
    (p : ℕ) (T : ActualStratum M p)
    (τ : Finset (EssentialArcClass M)) (hτ : τ ∈ actualRestrictedLink M T)
    (r : {v // v ∈ T.val} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (O : Finset (EssentialArcClass M)) (hO : O ∈ actualObjectFamily M T.val)
    (U : Set S) (hOU : IsComplementComponent (actualObjectTrace M r O) U)
    (hUG : IsComplementComponent (⋃ v, (r v).val.image) U)
    (q : S) (hmarks : ∀ z ∈ U, z ∈ M.cover.branch → z = q)
    (F : Finset (EssentialArcClass M)) (hF : F ⊆ τ)
    (s : {w // w ∈ F} → EssentialMarkedArc M)
    (hs : ∀ w, Quotient.mk (essentialArcSetoid M) (s w) = w.val)
    (hd : ∀ w v, Disjoint (arcInterior M (s w)) (arcInterior M (r v)))
    (hHit : ∀ w, (arcInterior M (s w) ∩ U).Nonempty) : F.card ≤ 2 := by
  classical
  obtain ⟨v, hv, hboundary, hlabel⟩ :=
    actual_one_mark_link_face_boundary_labels M p T τ hτ r hr O hO U hOU hUG q hmarks
  have each (w : {w // w ∈ F}) :=
    hlabel (s w) w.val (hF w.property) (hs w) (hd w) (hHit w)
  have hcard := actual_link_endpoint_star_card M p T τ hτ F hF q
    (classEndpoints M v) (fun w hw => (each ⟨w, hw⟩).1)
    (fun w hw => (each ⟨w, hw⟩).2)
  rcases classEndpoints_card M v with h | h <;> omega
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Schoenflies unitInterval
open scoped Classical
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 2000000
/-- A literal actual arc entering a one-mark Jordan face is a planar spoke;
this constructs its coordinates rather than assuming a spoke certificate. -/
theorem actual_one_mark_face_spoke_coordinates (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (hne : a.val.map 0 ≠ a.val.map 1)
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (C : Set Plane) (q : Plane) (hC : IsJordanCurve C) (hq : q ∈ inside C)
    (hint : arcInterior M a ⊆ f '' inside C)
    (hwhole : a.val.image ⊆ closure (f '' inside C))
    (hend : a.val.map 0 ∈ f '' inside C ∨ a.val.map 1 ∈ f '' inside C)
    (hmarks : ∀ z ∈ inside C, f z ∈ M.cover.branch → z = q) :
    ∃ (P : Set Plane) (u : Plane), IsArcBetween P u q ∧ u ∈ C ∧
      a.val.image = f '' P ∧ P \ {u} ⊆ inside C ∧
      markedArcEndset a.val = {f u,f q} ∧ f u ∈ M.cover.branch := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have hj := jordan_curve_theorem hC
  have hk : IsCompact (closure (inside C)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hj.isBounded_inside.closure
  have hcl : closure (f '' inside C) ⊆ f '' closure (inside C) :=
    closure_minimal (image_mono subset_closure) (hk.image hf.continuous).isClosed
  have him : ∀ t : Interval, a.val.map t ∈ range f := by
    intro t
    obtain ⟨x, _, hx⟩ := hcl (hwhole ⟨t, rfl⟩)
    exact ⟨x, hx⟩
  let H : Plane ≃ₜ range f := hf.isEmbedding.toHomeomorph
  let g : Interval → Plane := fun t => H.symm ⟨a.val.map t, him t⟩
  have hg : Continuous g := H.symm.continuous.comp (a.val.continuous.subtype_mk _)
  have hfg (t : Interval) : f (g t) = a.val.map t := by
    exact congrArg Subtype.val (H.apply_symm_apply ⟨a.val.map t, him t⟩)
  have hai : Function.Injective a.val.map := by
    intro t u he
    rcases a.val.injective_except_loop_closure t u he with ht | ht | ht
    · exact ht
    · obtain ⟨rfl, rfl⟩ := ht
      exact False.elim (hne he)
    · obtain ⟨rfl, rfl⟩ := ht
      exact False.elim (hne he.symm)
  have hgi : Function.Injective g := by
    intro t u he
    apply hai
    rw [← hfg t, ← hfg u, he]
  have hgin (t : Interval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) : g t ∈ inside C := by
    have htB : a.val.map t ∉ M.cover.branch := by
      intro ht
      rcases a.val.marked_only_at_ends t ht with ht | ht
      · exact ht0 ht
      · exact ht1 ht
    obtain ⟨x, hx, he⟩ := hint ⟨⟨t, rfl⟩, htB⟩
    have hxg : x = g t := hf.injective (he.trans (hfg t).symm)
    exact hxg ▸ hx
  have hclosure (t : Interval) : g t ∈ closure (inside C) := by
    obtain ⟨x, hx, he⟩ := hcl (hwhole ⟨t, rfl⟩)
    exact hf.injective (he.trans (hfg t).symm) ▸ hx
  have mark (t : Interval) (ht : a.val.map t ∈ M.cover.branch)
      (hin : a.val.map t ∈ f '' inside C) : g t = q := by
    obtain ⟨x, hx, he⟩ := hin
    have hxg : x = g t := hf.injective (he.trans (hfg t).symm)
    apply hmarks _ (hxg ▸ hx)
    rwa [hfg]
  have endCases : (g 0 ∈ C ∧ g 1 = q) ∨ (g 1 ∈ C ∧ g 0 = q) := by
    have boundary (t u : Interval) (htu : t ≠ u) (hu : g u = q)
        (htB : a.val.map t ∈ M.cover.branch) : g t ∈ C := by
      have hn : g t ∉ inside C := by
        intro ht
        have he : g t = q := hmarks _ ht (by rwa [hfg])
        exact htu (hgi (he.trans hu.symm))
      have hs : g t ∈ inside C ∪ C := by
        have hc := hclosure t
        rwa [(IsRegionOf.inside C).closure_eq hj] at hc
      exact hs.resolve_left hn
    rcases hend with he | he
    · have he0 := mark 0 a.val.start_marked he
      right
      exact ⟨boundary 1 0 (by norm_num) he0 a.val.end_marked, he0⟩
    · have he1 := mark 1 a.val.end_marked he
      left
      exact ⟨boundary 0 1 (by norm_num) he1 a.val.start_marked, he1⟩
  let P := range g
  have hP : IsArcBetween P (g 0) (g 1) := by
    let k : ℝ → Plane := fun t => g (projIcc 0 1 zero_le_one t)
    refine ⟨k, (hg.comp continuous_projIcc).continuousOn, ?_, ?_, ?_, ?_⟩
    · intro t ht u hu he
      have hh := hgi he
      rw [projIcc_of_mem zero_le_one ht, projIcc_of_mem zero_le_one hu] at hh
      exact congrArg Subtype.val hh
    · ext x
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨projIcc 0 1 zero_le_one t, rfl⟩
      · rintro ⟨t, rfl⟩
        refine ⟨t.val, t.property, ?_⟩
        dsimp [k]
        rw [projIcc_of_mem zero_le_one t.property]
    · dsimp [k]
      rw [projIcc_of_mem zero_le_one (by norm_num : (0 : ℝ) ∈ Icc 0 1)]
      rfl
    · dsimp [k]
      rw [projIcc_of_mem zero_le_one (by norm_num : (1 : ℝ) ∈ Icc 0 1)]
      rfl
  have himage : a.val.image = f '' P := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨g t, ⟨t, rfl⟩, hfg t⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, (hfg t).symm⟩
  rcases endCases with he | he
  · refine ⟨P, g 0, he.2 ▸ hP, he.1, himage, ?_, ?_, ?_⟩
    · rintro x ⟨⟨t, rfl⟩, ht⟩
      by_cases ht1 : t = 1
      · simpa [ht1, he.2] using hq
      · exact hgin t (fun ht0 => ht (ht0 ▸ rfl)) ht1
    · change ({a.val.map (0 : Interval), a.val.map (1 : Interval)} : Finset S) = _
      rw [← hfg 0, ← hfg 1, he.2]
    · rw [hfg]
      exact a.val.start_marked
  · refine ⟨P, g 1, he.2 ▸ hP.reverse, he.1, himage, ?_, ?_, ?_⟩
    · rintro x ⟨⟨t, rfl⟩, ht⟩
      by_cases ht0 : t = 0
      · simpa [ht0, he.2] using hq
      · exact hgin t ht0 (fun ht1 => ht (ht1 ▸ rfl))
    · change ({a.val.map (0 : Interval), a.val.map (1 : Interval)} : Finset S) = _
      rw [← hfg 0, ← hfg 1, he.2]
      exact Finset.pair_comm _ _
    · rw [hfg]
      exact a.val.end_marked
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- An actual arc whose marked endpoint lies in an open complementary face
really enters that face; incidence at the endpoint is not a supplied hit. -/
theorem actual_face_marked_endpoint_entry (M : HyperellipticModel E S) {I : Type} [Finite I]
    (r : I → EssentialMarkedArc M) (a : EssentialMarkedArc M)
    (hd : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v)))
    (U : Set S) (hU : IsComplementComponent (⋃ v, (r v).val.image) U)
    (hopen : IsOpen U) (q : S) (hq : q ∈ U) (hqa : q ∈ a.val.image) :
    (arcInterior M a ∩ U).Nonempty := by
  obtain ⟨V, hV, hi, hc⟩ := actual_arc_face_localization M r a hd
  obtain ⟨z, hzU, hzV⟩ := (mem_closure_iff.mp (hc hqa)) U hopen hq
  have he : V = U := by
    by_contra hne
    exact Set.disjoint_left.mp (complementComponents_disjoint hV hU hne) hzV hzU
  let t : Interval := ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩
  have ht : a.val.map t ∈ arcInterior M a := by
    refine ⟨⟨t, rfl⟩, ?_⟩
    intro hb
    rcases a.val.marked_only_at_ends t hb with h | h
    · have hh := congrArg Subtype.val h
      norm_num [t] at hh
    · have hh := congrArg Subtype.val h
      norm_num [t] at hh
  exact ⟨a.val.map t, ht, he ▸ hi ht⟩
end CurveComplex.HyperellipticModel
