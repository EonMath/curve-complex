import CurveComplexGenusTwo.Topology.CompletedJordan
import CurveComplexGenusTwo.Topology.ArcCounts.ActualNumericDegree
namespace Schoenflies
open Set

theorem actual_planar_arc_two_local_sides
    (G P : Set Plane) (hG : IsClosed G) {a b : Plane}
    (hP : IsArcBetween P a b) (hinter : P \ {a,b} ⊆ Gᶜ)
    : ∃ zL ∈ Gᶜ \ P, ∃ zR ∈ Gᶜ \ P,
      ∀ w ∈ P \ {a,b}, ∃ N : Set Plane,
        IsOpen N ∧ w ∈ N ∧ N ⊆ Gᶜ ∧
        N \ P ⊆ connectedComponentIn (Gᶜ \ P) zL ∪
          connectedComponentIn (Gᶜ \ P) zR := by
  classical
  let D := Gᶜ \ ({a,b} : Set Plane)
  have hD : IsOpen D := hG.isOpen_compl.sdiff (isClosed_singleton.union isClosed_singleton)
  have ha : a ∉ D := fun h => h.2 (by simp)
  have hb : b ∉ D := fun h => h.2 (by simp)
  have hPD : P \ {a,b} ⊆ D := fun x hx => ⟨hinter hx,hx.2⟩
  obtain ⟨A,hA,hmeet,hJ⟩ := exists_jordan_completion_of_isArcBetween hP
  have hcollars := hasArcCollars_of_jordan_arc_split hD hA hP hmeet hJ ha hb hPD
  obtain ⟨f,hc,hi,himg,h0,h1⟩ := hP
  have hdiff : P \ {a,b} = f '' Ioo 0 1 := by
    rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi]
    rfl
  have hsubarc : ∀ s t : ℝ, 0 < s → s < t → t < 1 →
      Nonempty (ArcCollar D P (f '' Icc s t)) := by
    intro s t hs hst ht
    have hsubI : Icc s t ⊆ Icc (0:ℝ) 1 := fun u hu => ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have hsubIoo : Icc s t ⊆ Ioo 0 1 := fun u hu => ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have hsI : s ∈ Icc s t := left_mem_Icc.mpr hst.le
    have htI : t ∈ Icc s t := right_mem_Icc.mpr hst.le
    refine hcollars _ ?_ (isCompact_image_of_subset_I hc hsubI isClosed_Icc)
      (isPreconnected_Icc.image f (hc.mono hsubI))
      ⟨f s,mem_image_of_mem f hsI,f t,mem_image_of_mem f htI,?_⟩
    · intro x hx
      have hxopen : x ∈ P \ {a,b} := hdiff ▸ image_mono hsubIoo hx
      exact ⟨hPD hxopen,hxopen.1⟩
    · intro he
      exact (ne_of_lt hst) (hi (hsubI hsI) (hsubI htI) he)
  obtain ⟨C₀⟩ := hsubarc (1/4) (3/4) (by norm_num) (by norm_num) (by norm_num)
  have hz₀ : f (1/2) ∈ f '' Icc (1/4 : ℝ) (3/4) :=
    ⟨1/2,⟨by norm_num,by norm_num⟩,rfl⟩
  have hmon : D \ P ⊆ Gᶜ \ P := fun x hx => ⟨hx.1.1,hx.2⟩
  refine ⟨C₀.ptL,hmon C₀.ptL_mem_diff,C₀.ptR,hmon C₀.ptR_mem_diff,?_⟩
  intro w hw
  rw [hdiff] at hw
  obtain ⟨u,hu,rfl⟩ := hw
  obtain ⟨C⟩ := hsubarc (min u (1/4)) (max u (3/4))
    (lt_min hu.1 (by norm_num))
    (by have := min_le_right u (1/4 : ℝ); have := le_max_right u (3/4 : ℝ); linarith)
    (max_lt hu.2 (by norm_num))
  refine ⟨C.nbhd,C.isOpen_nbhd,
    C.subset_nbhd ⟨u,⟨min_le_left _ _,le_max_left _ _⟩,rfl⟩,
    fun x hx => (C.nbhd_subset hx).1,?_⟩
  intro x hx
  have hh := C₀.nbhd_diff_subset_components C hz₀
    (show f (1/2) ∈ f '' Icc (min u (1/4)) (max u (3/4)) from
      ⟨1/2,⟨(min_le_right _ _).trans (by norm_num),
        (by norm_num : (1/2:ℝ) ≤ 3/4).trans (le_max_right _ _)⟩,rfl⟩) hx
  exact hh.elim (fun h => Or.inl (connectedComponentIn_mono _ hmon h))
    (fun h => Or.inr (connectedComponentIn_mono _ hmon h))

theorem actual_planar_arc_incident_faces_at_most_two
    (G P : Set Plane) (hG : IsClosed G) {a b : Plane}
    (hP : IsArcBetween P a b) (hinter : P \ {a,b} ⊆ Gᶜ)
    (F : Finset (Set Plane))
    (hF : ∀ V ∈ F, CurveComplex.HyperellipticModel.IsComplementComponent (G ∪ P) V)
    (htouch : ∀ V ∈ F, (frontier V ∩ (P \ {a,b})).Nonempty) : F.card ≤ 2 := by
  classical
  let D := Gᶜ \ ({a,b} : Set Plane)
  have hD : IsOpen D := hG.isOpen_compl.sdiff (isClosed_singleton.union isClosed_singleton)
  have ha : a ∉ D := fun h => h.2 (by simp)
  have hb : b ∉ D := fun h => h.2 (by simp)
  have hPD : P \ {a,b} ⊆ D := fun x hx => ⟨hinter hx,hx.2⟩
  obtain ⟨A,hA,hmeet,hJ⟩ := exists_jordan_completion_of_isArcBetween hP
  have hcollars := hasArcCollars_of_jordan_arc_split hD hA hP hmeet hJ ha hb hPD
  obtain ⟨f,hc,hi,himg,h0,h1⟩ := hP
  have hdiff : P \ {a,b} = f '' Ioo 0 1 := by
    rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi]
    rfl
  have hsubarc : ∀ s t : ℝ, 0 < s → s < t → t < 1 →
      Nonempty (ArcCollar D P (f '' Icc s t)) := by
    intro s t hs hst ht
    have hsubI : Icc s t ⊆ Icc (0:ℝ) 1 := fun u hu => ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have hsubIoo : Icc s t ⊆ Ioo 0 1 := fun u hu => ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have hsI : s ∈ Icc s t := left_mem_Icc.mpr hst.le
    have htI : t ∈ Icc s t := right_mem_Icc.mpr hst.le
    refine hcollars _ ?_ (isCompact_image_of_subset_I hc hsubI isClosed_Icc)
      (isPreconnected_Icc.image f (hc.mono hsubI))
      ⟨f s,mem_image_of_mem f hsI,f t,mem_image_of_mem f htI,?_⟩
    · intro x hx
      have hxopen : x ∈ P \ {a,b} := hdiff ▸ image_mono hsubIoo hx
      exact ⟨hPD hxopen,hxopen.1⟩
    · intro he
      exact (ne_of_lt hst) (hi (hsubI hsI) (hsubI htI) he)
  obtain ⟨C₀⟩ := hsubarc (1/4) (3/4) (by norm_num) (by norm_num) (by norm_num)
  have hz₀ : f (1/2) ∈ f '' Icc (1/4 : ℝ) (3/4) :=
    ⟨1/2,⟨by norm_num,by norm_num⟩,rfl⟩
  have hmon : D \ P ⊆ (G ∪ P)ᶜ := by
    rintro x ⟨hx,hxp⟩ (hxG | hxP)
    · exact hx.1 hxG
    · exact hxp hxP
  let L := connectedComponentIn (G ∪ P)ᶜ C₀.ptL
  let R := connectedComponentIn (G ∪ P)ᶜ C₀.ptR
  have hsub : F ⊆ ({L,R} : Finset (Set Plane)) := by
    intro V hVF
    have hV := hF V hVF
    obtain ⟨w,hwfr,hwP⟩ := htouch V hVF
    rw [hdiff] at hwP
    obtain ⟨u,hu,rfl⟩ := hwP
    obtain ⟨C⟩ := hsubarc (min u (1/4)) (max u (3/4))
      (lt_min hu.1 (by norm_num))
      (by have := min_le_right u (1/4 : ℝ); have := le_max_right u (3/4 : ℝ); linarith)
      (max_lt hu.2 (by norm_num))
    have hwu : f u ∈ C.nbhd := C.subset_nbhd ⟨u,⟨min_le_left _ _,le_max_left _ _⟩,rfl⟩
    obtain ⟨x,hxN,hxV⟩ := mem_closure_iff.mp (frontier_subset_closure hwfr)
      C.nbhd C.isOpen_nbhd hwu
    have hxP : x ∉ P := fun hx => hV.2.2.1 hxV (Or.inr hx)
    have hcover := C₀.nbhd_diff_subset_components C hz₀
      (show f (1/2) ∈ f '' Icc (min u (1/4)) (max u (3/4)) from
        ⟨1/2,⟨(min_le_right _ _).trans (by norm_num),
          (by norm_num : (1/2:ℝ) ≤ 3/4).trans (le_max_right _ _)⟩,rfl⟩)
      ⟨hxN,hxP⟩
    have heq (z : Plane) (hz : x ∈ connectedComponentIn (G ∪ P)ᶜ z) :
        V = connectedComponentIn (G ∪ P)ᶜ z := by
      obtain ⟨p,hp,hVp⟩ := CurveComplex.HyperellipticModel.complementComponent_iff_componentIn.mp hV
      rw [hVp]
      exact (connectedComponentIn_eq (hVp ▸ hxV)).trans (connectedComponentIn_eq hz).symm
    rcases hcover with hxL | hxR
    · exact Finset.mem_insert.mpr (Or.inl (heq _ (connectedComponentIn_mono _ hmon hxL)))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
        (heq _ (connectedComponentIn_mono _ hmon hxR))))
  exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))
end Schoenflies

namespace CurveComplex.HyperellipticModel
open Set Schoenflies Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_general_nonloop_edge_face_count_le_two
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M)
    (hNL : a.val.map 0 ≠ a.val.map 1)
    (ha : ∀ i, Disjoint (arcInterior M a) (arcInterior M (r i)))
    (F : Finset (Set S))
    (hF : ∀ V ∈ F, IsComplementComponent ((⋃ i, (r i).val.image) ∪ a.val.image) V)
    (htouch : ∀ V ∈ F, (frontier V ∩ arcInterior M a).Nonempty) : F.card ≤ 2 := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let n : NonLoopArc M := ⟨a.val,hNL⟩
  obtain ⟨p,hpb,hp⟩ := n.exists_marked_puncture
  let e : Schoenflies.Plane → S := fun x => ((M.puncturedPlane p).symm x).val
  have hec : Continuous e := continuous_subtype_val.comp (M.puncturedPlane p).symm.continuous
  have hei : Function.Injective e := Subtype.val_injective.comp (M.puncturedPlane p).symm.injective
  have heopen : IsOpenEmbedding e :=
    (isClosed_singleton.isOpen_compl.isOpenEmbedding_subtypeVal).comp
      (M.puncturedPlane p).symm.isOpenEmbedding
  let g : Interval → Schoenflies.Plane := fun t =>
    M.puncturedPlane p ⟨a.val.map t,fun he => hp (he ▸ Set.mem_range_self t)⟩
  have heg (t : Interval) : e (g t) = a.val.map t := by
    exact congrArg Subtype.val ((M.puncturedPlane p).symm_apply_apply _)
  have hgP : IsArcBetween (Set.range g) (g 0) (g 1) := n.plane_isArcBetween p hp
  let G : Set S := ⋃ i, (r i).val.image
  let P := Set.range g
  let H := G ∪ a.val.image
  have hG : IsClosed G := (markedFamily_graph_compact (fun i => (r i).val)).isClosed
  have himage : e '' P = a.val.image := by
    ext x
    constructor
    · rintro ⟨y,⟨t,rfl⟩,rfl⟩
      rw [heg]
      exact Set.mem_range_self t
    · rintro ⟨t,rfl⟩
      exact ⟨g t,Set.mem_range_self t,heg t⟩
  have hPiff (x : Schoenflies.Plane) : e x ∈ a.val.image ↔ x ∈ P := by
    rw [← himage]
    exact hei.mem_set_image
  have hinter : P \ {g 0,g 1} ⊆ (e ⁻¹' G)ᶜ := by
    rintro x ⟨⟨t,rfl⟩,hends⟩ hxG
    have hxarc : a.val.map t ∈ arcInterior M a := by
      refine ⟨Set.mem_range_self t,?_⟩
      intro hb
      rcases a.val.marked_only_at_ends t hb with ht | ht
      · exact hends (by simp [ht])
      · exact hends (by simp [ht])
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (show a.val.map t ∈ G by simpa [heg] using hxG)
    exact Set.disjoint_left.mp (ha i) hxarc ⟨hi,hxarc.2⟩
  obtain ⟨zL,hzL,zR,hzR,hlocal⟩ := actual_planar_arc_two_local_sides
    (e ⁻¹' G) P (hG.preimage hec) hgP hinter
  have hmon : e '' ((e ⁻¹' G)ᶜ \ P) ⊆ Hᶜ := by
    rintro x ⟨y,⟨hyG,hyP⟩,rfl⟩ (hxG | hxP)
    · exact hyG hxG
    · exact hyP ((hPiff y).mp hxP)
  have hcomponent (z : Schoenflies.Plane) (hz : z ∈ (e ⁻¹' G)ᶜ \ P) :
      e '' connectedComponentIn ((e ⁻¹' G)ᶜ \ P) z ⊆ connectedComponentIn Hᶜ (e z) := by
    have hc : IsConnected (e '' connectedComponentIn ((e ⁻¹' G)ᶜ \ P) z) :=
      (isConnected_connectedComponentIn_iff.mpr hz).image e hec.continuousOn
    exact hc.isPreconnected.subset_connectedComponentIn
      (Set.mem_image_of_mem e (mem_connectedComponentIn hz))
      ((Set.image_mono (connectedComponentIn_subset _ _)).trans hmon)
  let L := connectedComponentIn Hᶜ (e zL)
  let R := connectedComponentIn Hᶜ (e zR)
  have hsub : F ⊆ ({L,R} : Finset (Set S)) := by
    intro V hVF
    have hV := hF V hVF
    obtain ⟨w,hwfr,⟨⟨t,htw⟩,hwmark⟩⟩ := htouch V hVF
    have htends : g t ∈ P \ {g 0,g 1} := by
      refine ⟨Set.mem_range_self t,?_⟩
      rintro (ht0 | ht1)
      · have he := congrArg e ht0
        rw [heg,heg] at he
        exact hwmark (htw ▸ he.symm ▸ a.val.start_marked)
      · have he := congrArg e ht1
        rw [heg,heg] at he
        exact hwmark (htw ▸ he.symm ▸ a.val.end_marked)
    obtain ⟨N,hN,hgtN,hNG,hNcover⟩ := hlocal _ htends
    have hwN : w ∈ e '' N := ⟨g t,hgtN,(heg t).trans htw⟩
    obtain ⟨x,hxN,hxV⟩ := mem_closure_iff.mp (frontier_subset_closure hwfr)
      (e '' N) (heopen.isOpenMap N hN) hwN
    obtain ⟨y,hyN,rfl⟩ := hxN
    have hyP : y ∉ P := fun hy => hV.2.2.1 hxV (Or.inr ((hPiff y).mpr hy))
    have heq (z : S) (hz : e y ∈ connectedComponentIn Hᶜ z) :
        V = connectedComponentIn Hᶜ z := by
      obtain ⟨v,hv,hVv⟩ := complementComponent_iff_componentIn.mp hV
      rw [hVv]
      exact (connectedComponentIn_eq (hVv ▸ hxV)).trans (connectedComponentIn_eq hz).symm
    rcases hNcover ⟨hyN,hyP⟩ with hyL | hyR
    · exact Finset.mem_insert.mpr (Or.inl (heq _ (hcomponent zL hzL ⟨y,hyL,rfl⟩)))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
        (heq _ (hcomponent zR hzR ⟨y,hyR,rfl⟩))))
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_insert_le _ _).trans (by simp))

open scoped BigOperators

theorem actual_nonloop_family_edge_incident_face_count_le_two
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (u : ι) (hNL : (r u).val.map 0 ≠ (r u).val.map 1)
    (F : Finset (Set S))
    (hF : ∀ V ∈ F, IsComplementComponent (⋃ i, (r i).val.image) V) :
    actualEdgeIncidentFaceCount M r F u ≤ 2 := by
  classical
  let rr : {v : ι // v ≠ u} → EssentialMarkedArc M := fun v => r v.val
  have hgraph : (⋃ v, (r v).val.image) = (⋃ v, (rr v).val.image) ∪ (r u).val.image := by
    ext x
    constructor
    · intro hx
      obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hx
      by_cases hvu : v = u
      · exact Or.inr (hvu ▸ hv)
      · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨v,hvu⟩,hv⟩)
    · rintro (hx | hx)
      · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨v.val,hv⟩
      · exact Set.mem_iUnion.mpr ⟨u,hx⟩
  apply actual_general_nonloop_edge_face_count_le_two M rr (r u) hNL
    (fun v => hd u v.val v.property.symm)
  · intro V hV
    rw [← hgraph]
    exact hF V (Finset.mem_filter.mp hV).1
  · intro V hV
    exact (Finset.mem_filter.mp hV).2

theorem actual_nonloop_incident_degree_sum_le
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (hnonloop : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1)
    (F : Finset (Set S))
    (hF : ∀ V ∈ F, IsComplementComponent (⋃ i, (r i).val.image) V) :
    (∑ V ∈ F, actualIncidentEdgeDegree M r V) ≤ 2 * Fintype.card ι := by
  classical
  rw [actual_incident_degree_double_count]
  calc
    _ ≤ ∑ _i : ι, (2:ℕ) := Finset.sum_le_sum
      (fun i _ => actual_nonloop_family_edge_incident_face_count_le_two M r hd i (hnonloop i) F hF)
    _ = 2 * Fintype.card ι := by simp [Nat.mul_comm]

end CurveComplex.HyperellipticModel
