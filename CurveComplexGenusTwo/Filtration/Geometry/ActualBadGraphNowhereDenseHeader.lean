import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects
import CurveComplexGenusTwo.Filtration.Geometry.CurveJordanBridge
import CurveComplexGenusTwo.Intersection.SphereChart
namespace CurveComplex.HyperellipticModel
open Set CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance integrationLocalInstance_ActualBadGraphNowhereDenseHeader_1 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

theorem actual_bad_graph_nowhereDense (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : badVertices (actualArcLabels M) σ = σ) :
    IsNowhereDense (⋃ v, (r v).val.image) := by
  classical
  have hpair : ∀ a b : NonLoopArc M,
      markedArcEndset a.val = markedArcEndset b.val →
      Disjoint (a.val.image \ (M.cover.branch : Set S))
        (b.val.image \ (M.cover.branch : Set S)) →
      IsNowhereDense (a.val.image ∪ b.val.image) := by
    intro a b hends hd
    classical
    have hjnd : ∀ J : CurveComplex.SpherePort.JordanCurve,
        CurveComplex.SpherePort.Chart J → IsNowhereDense J.image := by
      intro J P
      let f : Schoenflies.Plane → CurveComplex.SpherePort.Sphere := fun z => (P.plane.symm z).val
      have hf : Topology.IsOpenEmbedding f :=
        isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp P.plane.symm.isOpenEmbedding
      have hC := CurveComplex.SpherePort.chart_image_jordan J P
      have hsep := Schoenflies.jordan_curve_theorem hC
      have hnd : IsNowhereDense (P.planeImage J) := by
        rw [← hsep.frontier_inside]
        change interior (closure (frontier (Schoenflies.inside (P.planeImage J)))) = ∅
        rw [isClosed_frontier.closure_eq, ← frontier_compl]
        exact interior_frontier hsep.isOpen_inside.isClosed_compl
      have he : f '' P.planeImage J = J.image := by
        ext x
        constructor
        · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
          simpa [f] using hy
        · intro hx
          have hxp : x ≠ P.puncture := fun h => P.avoids (h ▸ hx)
          refine ⟨P.plane ⟨x, hxp⟩, ?_, ?_⟩
          · exact ⟨⟨x, hxp⟩, hx, rfl⟩
          · simp [f]
      rw [← he]
      exact hf.isEmbedding.isInducing.isNowhereDense_image hnd
    obtain ⟨p, hpmark, hpa⟩ := a.exists_marked_puncture
    have hpb : p ∉ b.val.image := by
      intro hp
      have hpends : p ∈ markedArcEndset b.val := by
        change p ∈ (markedArcEndset b.val : Set S)
        rw [← markedArc_image_inter_branch]
        exact ⟨hp, hpmark⟩
      rw [← hends] at hpends
      have hpim : p ∈ a.val.image ∩ (M.cover.branch : Set S) := by
        rw [markedArc_image_inter_branch]; exact hpends
      exact hpa hpim.1
    obtain ⟨c, hci⟩ := actual_parallel_pair_curve_unordered M a b hends hd
    obtain ⟨J, hJ⟩ := actualCurve_sphereJordan M c
    have hpJ : M.sphere p ∉ J.image := by
      rw [hJ]
      rintro ⟨x, hx, he⟩
      have hxp : x = p := M.sphere.injective he
      rw [hxp, hci] at hx
      exact hx.elim hpa hpb
    let P : CurveComplex.SpherePort.Chart J := {
      puncture := M.sphere p
      avoids := hpJ
      plane := puncturedSpherePlane (M.sphere p) }
    have hnd := hjnd J P
    have he : M.sphere.symm '' J.image = a.val.image ∪ b.val.image := by
      rw [hJ, ← image_comp, M.sphere.symm_comp_self, image_id, hci]
    rw [← he]
    exact M.sphere.symm.isEmbedding.isInducing.isNowhereDense_image hnd
  have hloop : ∀ a : MarkedArc M, a.map 0 = a.map 1 → IsNowhereDense a.image := by
    intro a hloop
    classical
    have hjnd : ∀ J : CurveComplex.SpherePort.JordanCurve,
        CurveComplex.SpherePort.Chart J → IsNowhereDense J.image := by
      intro J P
      let f : Schoenflies.Plane → CurveComplex.SpherePort.Sphere := fun z => (P.plane.symm z).val
      have hf : Topology.IsOpenEmbedding f :=
        isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp P.plane.symm.isOpenEmbedding
      have hC := CurveComplex.SpherePort.chart_image_jordan J P
      have hsep := Schoenflies.jordan_curve_theorem hC
      have hnd : IsNowhereDense (P.planeImage J) := by
        rw [← hsep.frontier_inside]
        change interior (closure (frontier (Schoenflies.inside (P.planeImage J)))) = ∅
        rw [isClosed_frontier.closure_eq, ← frontier_compl]
        exact interior_frontier hsep.isOpen_inside.isClosed_compl
      have he : f '' P.planeImage J = J.image := by
        ext x
        constructor
        · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
          simpa [f] using hy
        · intro hx
          have hxp : x ≠ P.puncture := fun h => P.avoids (h ▸ hx)
          refine ⟨P.plane ⟨x, hxp⟩, ?_, ?_⟩
          · exact ⟨⟨x, hxp⟩, hx, rfl⟩
          · simp [f]
      rw [← he]
      exact hf.isEmbedding.isInducing.isNowhereDense_image hnd
    obtain ⟨p, hpmark, hpne⟩ := Finset.exists_mem_ne
      (by rw [M.cover.branch_card]; norm_num : 1 < M.cover.branch.card) (a.map 0)
    have hpa : p ∉ a.image := by
      rintro ⟨t, rfl⟩
      rcases a.marked_only_at_ends t hpmark with ht | ht
      · exact hpne (congrArg a.map ht)
      · exact hpne ((congrArg a.map ht).trans hloop.symm)
    let J : CurveComplex.SpherePort.JordanCurve := {
      map := M.sphere ∘ a.map
      continuous := M.sphere.continuous.comp a.continuous
      injective_except_ends := fun t u h =>
        a.injective_except_loop_closure t u (M.sphere.injective h)
      closed := congrArg M.sphere hloop }
    have hJ : J.image = M.sphere '' a.image := by
      exact Set.range_comp M.sphere a.map
    have hpJ : M.sphere p ∉ J.image := by
      rw [hJ]
      rintro ⟨x, hx, he⟩
      exact hpa (M.sphere.injective he ▸ hx)
    let P : CurveComplex.SpherePort.Chart J := {
      puncture := M.sphere p
      avoids := hpJ
      plane := puncturedSpherePlane (M.sphere p) }
    have he : M.sphere.symm '' J.image = a.image := by
      rw [hJ, ← image_comp, M.sphere.symm_comp_self, image_id]
    rw [← he]
    exact M.sphere.symm.isEmbedding.isInducing.isNowhereDense_image (hjnd J P)
  apply IsNowhereDense.iUnion
  intro u
  have hu : u.val ∈ badVertices (actualArcLabels M) σ := hbad.symm ▸ u.property
  simp only [badVertices, Finset.mem_filter] at hu
  rcases hu.2 with hl | ⟨w, hw, hwu, hul, hwl, he⟩
  · apply hloop
    have hc : (markedArcEndset (r u).val).card = 1 := by
      rw [markedArcEndset_eq_classEndpoints, hr]
      exact hl
    by_contra hn
    have hc2 : (markedArcEndset (r u).val).card = 2 := Finset.card_pair hn
    omega
  · let z : {v // v ∈ σ} := ⟨w, hw⟩
    have hUn : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) (r u)) := by
      rw [hr]; exact hul
    have hWn : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) (r z)) := by
      rw [hr]; exact hwl
    let a : NonLoopArc M := ⟨(r u).val, actualRepresentative_nonloop M (r u) hUn⟩
    let b : NonLoopArc M := ⟨(r z).val, actualRepresentative_nonloop M (r z) hWn⟩
    have hends : markedArcEndset a.val = markedArcEndset b.val := by
      change markedArcEndset (r u).val = markedArcEndset (r z).val
      rw [markedArcEndset_eq_classEndpoints, markedArcEndset_eq_classEndpoints, hr, hr]
      exact he.symm
    have huz : u ≠ z := fun h => hwu (congrArg Subtype.val h).symm
    exact (hpair a b hends (hd u z huz)).mono Set.subset_union_left

end CurveComplex.HyperellipticModel
