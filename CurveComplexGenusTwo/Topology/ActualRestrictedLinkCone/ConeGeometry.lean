import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ConePrerequisites
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualOneMarkDiscClassHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualOneMarkSpokeAvoidanceHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualSimplexInsertHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.RestrictedLinkHeaders
import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Topology.Extraction
import Schoenflies.JordanClosed


namespace CurveComplex.HyperellipticModel
open Set Schoenflies CurveGenusTwo.Filtration unitInterval
open scoped Classical
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
set_option maxHeartbeats 6000000
/-- Actual simultaneous one-mark insertion, using the original family on the
whole simplex and its literal restriction to the fixed bad support. -/
theorem actual_one_mark_aligned_restricted_link (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
    (τ : Finset (EssentialArcClass M)) (hτ : τ ∈ actualRestrictedLink M T)
    (r : {w // w ∈ T.val ∪ τ} → EssentialMarkedArc M)
    (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
    (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
    (rT : {w // w ∈ T.val} → EssentialMarkedArc M)
    (hrestrict : ∀ w, r ⟨w.val,Finset.mem_union_left _ w.property⟩ = rT w)
    (O : Finset (EssentialArcClass M)) (hO : O ∈ actualObjectFamily M T.val)
    (U : Set S) (hOU : IsComplementComponent (actualObjectTrace M rT O) U)
    (hUG : IsComplementComponent (⋃ w, (rT w).val.image) U)
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (C : Set Plane) (x q : Plane) (hC : IsJordanCurve C)
    (hU : U = f '' inside C) (hx : x ∈ C) (hq : q ∈ inside C)
    (a : EssentialMarkedArc M) (ha0 : a.val.map 0 = f x) (ha1 : a.val.map 1 = f q)
    (haIn : arcInterior M a ⊆ U)
    (hmarks : ∀ z ∈ inside C, f z ∈ M.cover.branch → z = q) :
    insert (Quotient.mk (essentialArcSetoid M) a) τ ∈ actualRestrictedLink M T := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  let v := Quotient.mk (essentialArcSetoid M) a
  change insert v τ ∈ actualRestrictedLink M T
  by_cases hvτ : v ∈ τ
  · simpa only [Finset.insert_eq_of_mem hvτ] using hτ
  have hqU : f q ∈ U := hU.symm ▸ mem_image_of_mem f hq
  have hxq : x ≠ q := fun he => inside_subset_compl hq (he ▸ hx)
  have hane : a.val.map 0 ≠ a.val.map 1 := by
    rw [ha0, ha1]
    exact hf.injective.ne hxq
  have hqB : f q ∈ M.cover.branch := ha1 ▸ a.val.end_marked
  have hxB : f x ∈ M.cover.branch := ha0 ▸ a.val.start_marked
  have hrdT : ∀ w z, w ≠ z → Disjoint (arcInterior M (rT w)) (arcInterior M (rT z)) := by
    intro w z hne
    rw [← hrestrict w, ← hrestrict z]
    exact hd _ _ (fun h => hne (Subtype.ext (congrArg (fun w : {w // w ∈ T.val ∪ τ} => w.val) h)))
  have hrT : ∀ w, Quotient.mk (essentialArcSetoid M) (rT w) = w.val := by
    intro w
    rw [← hrestrict w]
    exact hr _
  have hvertex : ({v} : Finset (EssentialArcClass M)) ∈ actualRestrictedLink M T :=
    actual_gap_arc_link_vertex M T.val rT hrT hrdT T.property.2.2
      U hUG.2.2.1 a hane haIn (Or.inr (ha1.symm ▸ hqU))
  have vnotT : v ∉ T.val := by
    change Disjoint T.val {v} ∧ _ at hvertex
    exact Finset.disjoint_singleton_right.mp hvertex.1
  have hopen : IsOpen U := complementComponent_open (actualObjectTrace_compact M rT O).isClosed hOU
  have amissT (w : {w // w ∈ T.val}) : Disjoint (arcInterior M a) (arcInterior M (rT w)) := by
    apply Set.disjoint_left.mpr
    intro z hz hzT
    exact hUG.2.2.1 (haIn hz) (mem_iUnion.mpr ⟨w, hzT.1⟩)
  have ahit := actual_face_marked_endpoint_entry M rT a amissT U hUG hopen (f q) hqU
    ⟨1, ha1⟩
  obtain ⟨W, hW, haWi, haWcl⟩ := actual_arc_face_localization M rT a amissT
  have hWU : W = U := by
    by_contra he
    obtain ⟨z, hz, hzU⟩ := ahit
    exact Set.disjoint_left.mp (complementComponents_disjoint hW hUG he) (haWi hz) hzU
  have haWhole : a.val.image ⊆ closure U := hWU ▸ haWcl
  obtain ⟨A, xa, hA, hxa, haImage, hAi, haEnds, _⟩ :=
    actual_one_mark_face_spoke_coordinates M a hane f hf C q hC hq
      (hU ▸ haIn) (hU ▸ haWhole) (Or.inr (ha1.symm ▸ mem_image_of_mem f hq)) hmarks
  have hxaEq : xa = x := by
    have he : ({f x, f q} : Finset S) = {f xa, f q} := by
      change ({a.val.map (0 : Interval), a.val.map (1 : Interval)} : Finset S) = _ at haEnds
      simpa only [ha0, ha1] using haEnds
    have hmem : f x ∈ ({f xa, f q} : Finset S) := he ▸ Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hmem with h | h
    · exact (hf.injective h).symm
    · exact False.elim (hxq (hf.injective (Finset.mem_singleton.mp h)))
  subst xa
  let k : {w // w ∈ τ} → {w // w ∈ T.val ∪ τ} :=
    fun w => ⟨w.val, Finset.mem_union_right _ w.property⟩
  have missT (w : {w // w ∈ τ}) :
      ∀ z, Disjoint (arcInterior M (r (k w))) (arcInterior M (rT z)) := by
    intro z
    rw [← hrestrict z]
    apply hd
    intro he
    change Disjoint T.val τ ∧ _ at hτ
    exact Finset.disjoint_left.mp hτ.1 z.property
      ((congrArg Subtype.val he).symm ▸ w.property)
  have hmarksU : ∀ z ∈ U, z ∈ M.cover.branch → z = f q := by
    intro z hz hb
    obtain ⟨u, hu, rfl⟩ := hU ▸ hz
    exact congrArg f (hmarks u hu hb)
  obtain ⟨b0, hb0T, hbnd, henter⟩ :=
    actual_one_mark_link_face_boundary_labels M p T τ hτ rT hrT O hO U hOU hUG (f q) hmarksU
  have hxEnds : f x ∈ classEndpoints M b0 := hbnd _ (by
    have hj := jordan_curve_theorem hC
    have hclU : f x ∈ closure U := by
      rw [hU]
      apply mem_closure_image hf.continuous.continuousAt
      exact frontier_subset_closure (hj.frontier_inside.symm ▸ hx)
    rw [hopen.frontier_eq]
    refine ⟨hclU, ?_⟩
    intro hin
    obtain ⟨y, hy, he⟩ := hU ▸ hin
    exact inside_subset_compl hy (hf.injective he ▸ hx)) hxB
  have otherCard : ((classEndpoints M b0).erase (f x)).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hxEnds]
    rcases classEndpoints_card M b0 with h | h <;> omega
  have coords (w : {w // w ∈ τ}) (hit : (arcInterior M (r (k w)) ∩ U).Nonempty) :
      ∃ B : Set Plane, ∃ y : Plane,
        IsArcBetween B y q ∧ y ∈ C ∧ (r (k w)).val.image = f '' B ∧
        B \ {y} ⊆ inside C ∧ f y ∈ (classEndpoints M b0).erase (f x) ∧
        markedArcEndset (r (k w)).val = {f y, f q} := by
    obtain ⟨hi, hc, he⟩ := actual_link_arc_face_has_interior_endpoint M p T τ hτ rT hrT
      O hO U hOU hUG (r (k w)) w.val w.property (hr (k w)) (missT w) hit
    have hn := (actualRestrictedLink_fresh_labels M p T τ hτ).1 w.val w.property
    have hne := actualRepresentative_nonloop M (r (k w)) (by rwa [hr])
    obtain ⟨B, y, hB, hy, hbImage, hBi, hbEnds, hyB⟩ :=
      actual_one_mark_face_spoke_coordinates M (r (k w)) hne f hf C q hC hq
        (hU ▸ hi) (hU ▸ hc) (hU ▸ he) hmarks
    have hyEnds : f y ∈ classEndpoints M b0 := hbnd _ (by
      have hclU : f y ∈ closure U := by
        rw [hU]
        apply mem_closure_image hf.continuous.continuousAt
        exact frontier_subset_closure ((jordan_curve_theorem hC).frontier_inside.symm ▸ hy)
      rw [hopen.frontier_eq]
      refine ⟨hclU, ?_⟩
      intro hin
      obtain ⟨z, hz, he⟩ := hU ▸ hin
      exact inside_subset_compl hz (hf.injective he ▸ hy)) hyB
    have hyx : y ≠ x := by
      intro he
      subst y
      have hclass := actual_one_mark_disc_class M a (r (k w)) f hf C A B x q
        hC hA hB hx hq hAi hBi haImage hbImage hmarks
      have hvw : v = w.val := hclass.trans (hr (k w))
      exact hvτ (hvw.symm ▸ w.property)
    exact ⟨B, y, hB, hy, hbImage, hBi,
      Finset.mem_erase.mpr ⟨hf.injective.ne hyx, hyEnds⟩, hbEnds⟩
  have entering_unique (w z : {w // w ∈ τ})
      (hw : (arcInterior M (r (k w)) ∩ U).Nonempty)
      (hz : (arcInterior M (r (k z)) ∩ U).Nonempty) : w = z := by
    obtain ⟨B, y, _, _, _, _, hy, hew⟩ := coords w hw
    obtain ⟨D, z0, _, _, _, _, hz0, hez⟩ := coords z hz
    have hyz : f y = f z0 := (Finset.card_le_one.mp otherCard) _ hy _ hz0
    apply Subtype.ext
    apply actual_link_endpoint_pair_unique M p T τ hτ w.property z.property
    rw [← hr (k w), ← hr (k z), ← markedArcEndset_eq_classEndpoints,
      ← markedArcEndset_eq_classEndpoints, hew, hez, hyz]
  obtain ⟨c, hcclass, hcIn, hcdis⟩ : ∃ c : EssentialMarkedArc M,
      Quotient.mk (essentialArcSetoid M) c = v ∧ arcInterior M c ⊆ U ∧
      ∀ w : {w // w ∈ τ}, Disjoint (arcInterior M c) (arcInterior M (r (k w))) := by
    by_cases hhit : ∃ w : {w // w ∈ τ}, (arcInterior M (r (k w)) ∩ U).Nonempty
    · obtain ⟨w, hw⟩ := hhit
      obtain ⟨B, y, hB, hy, hbImage, hBi, hyErase, _⟩ := coords w hw
      have hxy : x ≠ y := fun he => (Finset.mem_erase.mp hyErase).1 (congrArg f he.symm)
      obtain ⟨c, hc, hc0, hc1, hcI, hcB⟩ := actual_one_mark_spoke_avoidance M a (r (k w))
        f hf C A B x y q hC hA hB hx hy hxy hq hAi hBi haImage hbImage hxB hqB hmarks
      refine ⟨c, hc, hU.symm ▸ hcI, ?_⟩
      intro z
      by_cases hz : (arcInterior M (r (k z)) ∩ U).Nonempty
      · have he := entering_unique z w hz hw
        subst z
        exact hcB
      · apply Set.disjoint_left.mpr
        intro t htc htz
        exact hz ⟨t, htz, hU.symm ▸ hcI htc⟩
    · refine ⟨a, rfl, haIn, ?_⟩
      intro w
      apply Set.disjoint_left.mpr
      intro t hta htw
      exact hhit ⟨w, t, htw, haIn hta⟩
  have hcAll (w : {w // w ∈ T.val ∪ τ}) : Disjoint (arcInterior M c) (arcInterior M (r w)) := by
    rcases Finset.mem_union.mp w.property with hw | hw
    · have he : (⟨w.val, Finset.mem_union_left _ hw⟩ : {w // w ∈ T.val ∪ τ}) = w := Subtype.ext rfl
      have hrw := hrestrict ⟨w.val, hw⟩
      rw [he] at hrw
      rw [hrw]
      apply Set.disjoint_left.mpr
      intro t htc htr
      exact hUG.2.2.1 (hcIn htc) (mem_iUnion.mpr ⟨⟨w.val, hw⟩, htr.1⟩)
    · have he : k ⟨w.val, hw⟩ = w := Subtype.ext rfl
      simpa only [he] using hcdis ⟨w.val, hw⟩
  have hs := actual_simplex_insert_disjoint_representative M (T.val ∪ τ) r hr hd c hcAll
  rw [hcclass] at hs
  have hfresh : ∀ w ∈ T.val ∪ τ, w ≠ v → ¬ (actualArcLabels M).isLoop w →
      (actualArcLabels M).endpointPair w ≠ (actualArcLabels M).endpointPair v := by
    intro w hw hwv hwl he
    rcases Finset.mem_union.mp hw with hwT | hwτ
    · have hlabels := (actualRestrictedLink_fresh_labels M p T {v} hvertex).2 v
        (Finset.mem_singleton_self v) w (Finset.mem_union_left _ hwT) hwv hwl
      exact hlabels he
    · let z : {w // w ∈ τ} := ⟨w, hwτ⟩
      have hqend : f q ∈ classEndpoints M w := by
        have he : classEndpoints M w = classEndpoints M v := he
        rw [he, ← markedArcEndset_eq_classEndpoints]
        simp [markedArcEndset, ha1]
      have hqim : f q ∈ (r (k z)).val.image := by
        have he : markedArcEndset (r (k z)).val = classEndpoints M w := by rw [markedArcEndset_eq_classEndpoints, hr]
        rw [← he] at hqend
        simp only [markedArcEndset, Finset.mem_insert, Finset.mem_singleton] at hqend
        rcases hqend with h | h
        · exact ⟨0, h.symm⟩
        · exact ⟨1, h.symm⟩
      have hhit := actual_face_marked_endpoint_entry M rT (r (k z)) (missT z)
        U hUG hopen (f q) hqU hqim
      obtain ⟨B, y, hB, hy, hbImage, hBi, hyEr, hbEnds⟩ := coords z hhit
      have heEnds : ({f y, f q} : Finset S) = {f x, f q} := by
        have he : classEndpoints M w = classEndpoints M v := he
        calc
          {f y, f q} = markedArcEndset (r (k z)).val := hbEnds.symm
          _ = classEndpoints M w := by rw [markedArcEndset_eq_classEndpoints, hr]
          _ = classEndpoints M v := he
          _ = {f x, f q} := haEnds
      have hmem : f y ∈ ({f x, f q} : Finset S) := heEnds ▸ Finset.mem_insert_self _ _
      rcases Finset.mem_insert.mp hmem with hyx | hyq
      · exact (Finset.mem_erase.mp hyEr).1 hyx
      · exact inside_subset_compl hq (hf.injective (Finset.mem_singleton.mp hyq) ▸ hy)
  have hn := (actualRestrictedLink_fresh_labels M p T {v} hvertex).1 v (Finset.mem_singleton_self v)
  have hb := badVertices_insert_fresh_endpoint (actualArcLabels M) (T.val ∪ τ) v hn hfresh
  change Disjoint T.val τ ∧ T.val ∪ τ ∈ actualA M ∧ _ at hτ
  change Disjoint T.val (insert v τ) ∧ T.val ∪ insert v τ ∈ actualA M ∧ _
  refine ⟨Finset.disjoint_insert_right.mpr ⟨vnotT, hτ.1⟩, ?_, ?_⟩
  · change IsArcSimplex M (T.val ∪ insert v τ)
    simpa only [Finset.union_insert] using hs
  · simpa only [Finset.union_insert, hτ.2.2] using hb
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Schoenflies unitInterval
open scoped Classical
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- The actual two-mark complementary face produces an essential arc with
both ends and its entire image in the prescribed face chart. -/
theorem actual_two_mark_planar_apex (M : HyperellipticModel E S)
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (C : Set Plane) (hC : IsJordanCurve C) (p q : Plane)
    (hp : p ∈ inside C) (hq : q ∈ inside C) (hpq : p ≠ q)
    (hpB : f p ∈ M.cover.branch) (hqB : f q ∈ M.cover.branch)
    (hmarks : ∀ z ∈ inside C, f z ∈ M.cover.branch → z = p ∨ z = q) :
    ∃ a : EssentialMarkedArc M,
      a.val.map 0 = f p ∧ a.val.map 1 = f q ∧ a.val.image ⊆ f '' inside C := by
  have hj := jordan_curve_theorem hC
  obtain ⟨A, hAi, _, g, hgc, hgi, hgim, hg0, hg1⟩ :=
    exists_simple_arc_of_isPreconnected hj.isOpen_inside hj.isConnected_inside.isPreconnected hp hq hpq
  let k : Interval → S := fun t => f (g t.val)
  have hk : Continuous k := hf.continuous.comp (continuousOn_iff_continuous_restrict.mp hgc)
  have hki : Function.Injective k := by
    intro t u he
    apply Subtype.ext
    exact hgi t.property u.property (hf.injective he)
  have hk0 : k 0 = f p := congrArg f hg0
  have hk1 : k 1 = f q := congrArg f hg1
  have hkIn (t : Interval) : g t.val ∈ inside C :=
    hAi (hgim ▸ mem_image_of_mem g t.property)
  let a : MarkedArc M := {
    map := k
    continuous := hk
    injective_except_loop_closure := fun t u he => Or.inl (hki he)
    start_marked := hk0 ▸ hpB
    end_marked := hk1 ▸ hqB
    marked_only_at_ends := by
      intro t hb
      rcases hmarks _ (hkIn t) hb with he | he
      · exact Or.inl (hki ((congrArg f he).trans hk0.symm))
      · exact Or.inr (hki ((congrArg f he).trans hk1.symm)) }
  have hae : IsEssentialMarkedArc M a := Or.inl (by
    change k 0 ≠ k 1
    rw [hk0, hk1]
    exact hf.injective.ne hpq)
  refine ⟨⟨a, hae⟩, hk0, hk1, ?_⟩
  rintro z ⟨t, rfl⟩
  exact mem_image_of_mem f (hkIn t)
end CurveComplex.HyperellipticModel
