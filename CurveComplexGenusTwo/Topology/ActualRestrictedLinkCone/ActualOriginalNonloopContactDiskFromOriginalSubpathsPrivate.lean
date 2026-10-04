import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalContactDiskCleanupEntirePairGraphPrivate
open Lean Elab Term in
elab "checkedRLOriginalContactDiskPairGraphCleanup" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalContactDiskCleanupEntirePairGraphPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_original_contact_disk_cleanup_entire_pair_and_graph_private
  discard <| getConstInfo n
  return mkConst n

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies Metric
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 1600000
private theorem actual_original_nonloop_entire_pair_graph_clear_disk_of_original_subpaths_private
    (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
    (F J : Finset (EssentialArcClass M)) (hTF : T.val ⊆ F) (hJT : J ⊆ T.val)
    (r r0 : {w // w ∈ F} → EssentialMarkedArc M)
    (rT : {w // w ∈ T.val} → EssentialMarkedArc M)
    (hd0 : ∀ w z,w≠z → Disjoint (arcInterior M (r0 w)) (arcInterior M (r0 z)))
    (u : {w // w ∈ T.val}) (hu : u.val ∉ J)
    (hdT : ∀ w : {w // w ∈ T.val},w.val ∈ J → Disjoint (arcInterior M (rT w)) (arcInterior M (rT u)))
    (haligned0 : ∀ w : {w // w ∈ T.val},w.val ∈ J → r0 ⟨w.val,hTF w.property⟩=rT w)
    (hgraph : actualObjectTrace M r0 J=actualObjectTrace M r J)
    (hab : Quotient.mk (essentialArcSetoid M) (r0 ⟨u.val,hTF u.property⟩)=
      Quotient.mk (essentialArcSetoid M) (rT u))
    (ha : (r0 ⟨u.val,hTF u.property⟩).val.map 0≠(r0 ⟨u.val,hTF u.property⟩).val.map 1)
    (hfinite : (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).Finite)
    (hcross : ∀ q ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
      ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) q)
    (hSubpaths :
∃ (f g : C(Interval,S)) (u₀ v₀ : S),
      IsEmbedding f ∧ IsEmbedding g ∧
      range f ⊆ (r0 ⟨u.val,hTF u.property⟩).val.image ∧ range g ⊆ (rT u).val.image ∧
      f 0 = u₀ ∧ g 0 = u₀ ∧ f 1 = v₀ ∧ g 1 = v₀ ∧ u₀ ≠ v₀ ∧
      range f ∩ range g = {u₀,v₀} ∧
      v₀ ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u) ∧
      (u₀ ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u) ∨
        (u₀ ∈ (r0 ⟨u.val,hTF u.property⟩).val.image ∩ (rT u).val.image ∧ u₀ ∈ (M.cover.branch : Set S))) ∧
      ∃ (hu : u₀ ∈ ((M.cover.branch : Set S) \ {u₀})ᶜ)
        (hv : v₀ ∈ ((M.cover.branch : Set S) \ {u₀})ᶜ)
        (α β : Path (⟨u₀,hu⟩ : ↑((M.cover.branch : Set S) \ {u₀})ᶜ) ⟨v₀,hv⟩),
        (∀ t : Interval, (α t : S) = f t) ∧
        (∀ t : Interval, (β t : S) = g t) ∧ α.Homotopic β) :
    ∃ D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u),
      Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image ∪
          (M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
      (D.firstCorner∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u) ∨
        D.secondCorner∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)) := by
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨f,g,u₀,v₀,hf,hg,hfa,hgb,hf0,hg0,hf1,hg1,hne,hinter,
    hvcontact,hucontact,hu₀,hv₀,α,β,hα,hβ,hhom⟩ :=
    hSubpaths
  obtain ⟨Ω,hn,hconn,hsub,hmax,hfrontier,hfree⟩ :=
    actual_punctured_homotopic_jordan_sides_have_empty_region
      M f g u₀ v₀ hf hg hf0 hg0 hf1 hg1 hne hinter
      hu₀ hv₀ α β hα hβ hhom
  have hboundaryMarks : ∀ z ∈ range f ∪ range g,
      z ∈ M.cover.branch → z=u₀ := by
    intro z hz hzm
    rcases hz with ⟨t,rfl⟩ | ⟨t,rfl⟩
    · have ht := (α t).property
      rw [hα] at ht
      by_contra he
      exact ht ⟨hzm,by simpa using he⟩
    · have ht := (β t).property
      rw [hβ] at ht
      by_contra he
      exact ht ⟨hzm,by simpa using he⟩
  have hcollision : ∀ s t : Interval,f s=g t →
      (s=0 ∧ t=0) ∨ (s=1 ∧ t=1) := by
    intro s t he
    have hx : f s ∈ ({u₀,v₀} : Set S) := by
      rw [←hinter]; exact ⟨mem_range_self s,⟨t,he.symm⟩⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨hf.injective (hx.trans hf0.symm),
        hg.injective (he.symm.trans (hx.trans hg0.symm))⟩
    · rw [mem_singleton_iff] at hx
      exact Or.inr ⟨hf.injective (hx.trans hf1.symm),
        hg.injective (he.symm.trans (hx.trans hg1.symm))⟩
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs f g hf.injective hg.injective
    (hf0.trans hg0.symm) (hf1.trans hg1.symm) hcollision
  obtain ⟨Jc,hJc⟩ := actualCurve_sphereJordan M c
  let Lc : C(Interval,S) :=
    ⟨M.sphere.symm ∘ Jc.map,M.sphere.symm.continuous.comp Jc.continuous⟩
  have hLc : range Lc=range f ∪ range g := by
    change range (M.sphere.symm ∘ Jc.map)=_
    rw [range_comp]
    change M.sphere.symm '' Jc.image=_
    rw [hJc,hc,←image_comp,M.sphere.symm_comp_self,image_id]
  have hcard : ({u₀} : Finset S).card<M.cover.branch.card := by
    rw [M.cover.branch_card]; simp
  obtain ⟨q,hqm,hqnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hq : q ∉ range Lc := by
    intro hq
    have he := hboundaryMarks q (hLc ▸ hq) hqm
    exact hqnot (by simp [he])
  have hΩ : IsComplementComponent (range Lc) Ω :=
    hLc.symm ▸ ⟨hn,hconn,hsub,hmax⟩
  obtain ⟨d,hd,hi,hbdy⟩ := actual_selected_jordan_component_embedded_disk M Lc
    (congrArg M.sphere.symm Jc.closed)
    (fun s t he => Jc.injective_except_ends s t (M.sphere.symm.injective he))
    q hq Ω hΩ (hLc.symm ▸ hfrontier)
  have hdfree : Disjoint (d '' {x | x.val ∈ Metric.ball
      (0 : EuclideanSpace ℝ (Fin 2)) 1}) (M.cover.branch : Set S) :=
    hi.symm ▸ hfree
  have hdboundary : d '' {x | x.val ∈ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 2)) 1}=range f ∪ range g := hbdy.trans hLc
  have hdcorner : ∀ z ∈ range d,z ∈ M.cover.branch → z=u₀ := by
    rintro z ⟨x,rfl⟩ hzm
    have hxnorm : ‖x.val‖≤1 := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using x.property
    rcases hxnorm.lt_or_eq with hx | hx
    · exact False.elim (disjoint_left.mp hdfree
        ⟨x,by simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hx,rfl⟩ hzm)
    · apply hboundaryMarks _ _ hzm
      rw [←hdboundary]
      exact ⟨x,by simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using hx,rfl⟩
  let B : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) := {
    firstCorner := u₀,secondCorner := v₀,firstSide := f,secondSide := g,
    first_embedded := hf,second_embedded := hg,
    first_zero := hf0,first_one := hf1,second_zero := hg0,second_one := hg1,
    first_on_curve := hfa,second_on_curve := hgb,
    sides_inter := hinter,disk := d,disk_embedded := hd,boundary_eq := hdboundary,
    marks_are_corners := by
      intro z hz hzm
      exact Or.inl (hdcorner z hz hzm) }
  exact checkedRLOriginalContactDiskPairGraphCleanup M p T F J hTF hJT r r0 rT
    hd0 u hu hdT haligned0 hgraph hab ha hfinite hcross ⟨B,Or.inr hvcontact⟩

#print axioms actual_original_nonloop_entire_pair_graph_clear_disk_of_original_subpaths_private
end CurveComplex.HyperellipticModel
