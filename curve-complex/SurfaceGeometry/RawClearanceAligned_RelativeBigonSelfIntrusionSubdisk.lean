import RawClearanceAligned_RelativeBigonSelfIntrusionCrosscut
import CurveComplexGenusTwo.Topology.IntersectionParity.Subdisk
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEmbeddedSideEndpointMarks
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem relative_marked_bigon_first_self_intrusion_smaller_disk
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (B : ActualMarkedTwoSideDisk M a.toEssential b.toEssential)
    (hin : (a.image ∩ B.openInterior).Nonempty) :
    ∃ D : ActualMarkedTwoSideDisk M a.toEssential b.toEssential,
      range D.disk ⊆ range B.disk ∧
      (∃ x ∈ ({B.firstCorner,B.secondCorner}:Set S), x ∉ range D.disk) ∧
      (D.firstCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential ∨
        D.secondCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let : CompactSpace S := M.sphere.symm.compactSpace
  let : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere
      (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
      0 (by norm_num))
  let : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  let := (actualSphereSmoothAtlas M).charts
  let := (actualSphereSmoothAtlas M).manifold
  let : ClosedSurface S := {}
  obtain ⟨q,hq,hqa,hq0,hq1,hqin,hnotboth⟩ :=
    relative_marked_bigon_first_arc_self_intrusion_crosscut M a b B hin
  have hfree : Disjoint B.openInterior (range B.firstSide ∪ range B.secondSide) := by
    rw [← B.boundary_eq]
    apply Set.disjoint_left.mpr
    rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
    have huv := B.disk_embedded.injective (hux.trans hvx.symm)
    subst v
    have hu' : ‖u.val‖ < 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hu
    have hv' : ‖u.val‖ = 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hv
    linarith
  obtain ⟨r,hr⟩ := hq0
  obtain ⟨s,hs⟩ := hq1
  have hrs : r ≠ s := by
    intro he
    have h01 : (0:Interval) = 1 := hq.injective (hr.symm.trans ((congrArg B.secondSide he).trans hs))
    exact zero_ne_one h01
  let affine : Interval → Interval := fun t =>
    ⟨(1-t.val)*r.val+t.val*s.val,by
      constructor <;> nlinarith [t.property.1,t.property.2,r.property.1,r.property.2,
        s.property.1,s.property.2]⟩
  let g : C(Interval,S) := ⟨B.secondSide ∘ affine,B.secondSide.continuous.comp (by fun_prop)⟩
  have hg0 : g 0 = q 0 := by simpa [g,affine] using hr
  have hg1 : g 1 = q 1 := by simpa [g,affine] using hs
  have hgi : Function.Injective g := by
    intro t u he
    have hv := congrArg Subtype.val (B.second_embedded.injective he)
    apply Subtype.ext
    have hne : r.val ≠ s.val := fun he => hrs (Subtype.ext he)
    dsimp [affine] at hv
    have hz : (t.val-u.val)*(s.val-r.val)=0 := by nlinarith only [hv]
    rcases mul_eq_zero.mp hz with hz | hz
    · exact sub_eq_zero.mp hz
    · exact False.elim (hne (sub_eq_zero.mp hz).symm)
  have hg : IsEmbedding g := (g.continuous.isClosedEmbedding hgi).isEmbedding
  have hgg : range g ⊆ range B.secondSide := by
    rintro x ⟨t,rfl⟩
    exact mem_range_self (affine t)
  have hcross (t u : Interval) (he : q t = g u) :
      (t=0 ∧ u=0) ∨ (t=1 ∧ u=1) := by
    by_cases ht0 : t=0
    · exact Or.inl ⟨ht0,hgi (by rw [hg0,← he,ht0])⟩
    by_cases ht1 : t=1
    · exact Or.inr ⟨ht1,hgi (by rw [hg1,← he,ht1])⟩
    have htI : t ∈ Ioo (0:Interval) 1 :=
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
    exact False.elim (Set.disjoint_left.mp hfree (hqin ⟨t,htI,rfl⟩)
      (Or.inr (he.symm ▸ hgg (mem_range_self u))))
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs q g hq.injective hgi hg0.symm hg1.symm hcross
  have hcB : c.image ⊆ range B.disk := by
    rw [hc]
    apply union_subset
    · rintro x ⟨t,rfl⟩
      by_cases ht0 : t=0
      · subst t
        exact image_subset_range _ _ (B.boundary_eq.symm ▸
          (show q 0 ∈ range B.firstSide ∪ range B.secondSide from Or.inr ⟨r,hr⟩))
      by_cases ht1 : t=1
      · subst t
        exact image_subset_range _ _ (B.boundary_eq.symm ▸
          (show q 1 ∈ range B.firstSide ∪ range B.secondSide from Or.inr ⟨s,hs⟩))
      exact image_subset_range _ _ (hqin ⟨t,
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩)
    · exact fun x hx => image_subset_range _ _ (B.boundary_eq.symm ▸
        (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inr (hgg hx)))
  obtain ⟨d,hd,hdb,hdB⟩ := CurveComplex.LocalSurgery.curve_in_embedded_disk_bounds_subdisk
    c B.disk B.disk_embedded hcB
  have hdin : d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆ B.openInterior := by
    change d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆
      B.disk '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
    rw [← CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq B.disk B.disk_embedded]
    exact (CurveComplex.LocalSurgery.embedded_surface_disk_interior_isOpen d hd).subset_interior_iff.mpr
      ((image_subset_range _ _).trans hdB)
  have hmarks : ∀ x ∈ range d, x ∈ M.cover.branch → x ∈ ({q 0,q 1}:Set S) := by
    intro x hx hxmark
    obtain ⟨u,hu⟩ := hx
    have hnorm : ‖u.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
    have hne : ¬ ‖u.val‖ < 1 := by
      intro h
      have hxU := hdin ⟨u,by simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using h,hu⟩
      exact Set.disjoint_left.mp (relative_selected_bigon_open_interior_mark_free M _ _ B) hxU hxmark
    have hxc : x ∈ c.image := hdb ▸ (show x ∈ d ''
        {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} from
      ⟨u,by simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right]
        using le_antisymm hnorm (not_lt.mp hne),hu⟩)
    rw [hc] at hxc
    let A : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
    let F : C(Interval,S) := ⟨b.val.map,b.val.continuous⟩
    rcases hxc with ⟨t,ht⟩ | ⟨t,ht⟩
    · obtain ⟨v,hv⟩ := hqa (mem_range_self t)
      have hvmark : a.val.map v ∈ M.cover.branch := hv.trans ht ▸ hxmark
      have he : q t = A 0 ∨ q t = A 1 := by
        rcases a.val.marked_only_at_ends v hvmark with hv0 | hv1
        · exact Or.inl (hv.symm.trans (congrArg a.val.map hv0))
        · exact Or.inr (hv.symm.trans (congrArg a.val.map hv1))
      rcases actual_embedded_side_source_endpoint A q
        (A.continuous.isClosedEmbedding a.injective).isEmbedding hq hqa t he with ht0 | ht1
      · exact Or.inl ((congrArg q ht0).symm.trans ht).symm
      · exact Or.inr ((congrArg q ht1).symm.trans ht).symm
    · have hgb : range g ⊆ b.image := hgg.trans B.second_on_curve
      obtain ⟨v,hv⟩ := hgb (mem_range_self t)
      have hvmark : b.val.map v ∈ M.cover.branch := hv.trans ht ▸ hxmark
      have he : g t = F 0 ∨ g t = F 1 := by
        rcases b.val.marked_only_at_ends v hvmark with hv0 | hv1
        · exact Or.inl (hv.symm.trans (congrArg b.val.map hv0))
        · exact Or.inr (hv.symm.trans (congrArg b.val.map hv1))
      rcases actual_embedded_side_source_endpoint F g
        (F.continuous.isClosedEmbedding b.injective).isEmbedding hg hgb t he with ht0 | ht1
      · exact Or.inl ((hg0.symm.trans ((congrArg g ht0).symm.trans ht))).symm
      · exact Or.inr ((hg1.symm.trans ((congrArg g ht1).symm.trans ht))).symm
  have hsides : range q ∩ range g = {q 0,q 1} := by
    ext x
    constructor
    · rintro ⟨⟨t,ht⟩,⟨u,hu⟩⟩
      rcases hcross t u (ht.trans hu.symm) with ⟨ht0,_⟩ | ⟨ht1,_⟩
      · exact Or.inl ((congrArg q ht0).symm.trans ht).symm
      · exact Or.inr ((congrArg q ht1).symm.trans ht).symm
    · intro hx
      rcases mem_insert_iff.mp hx with hx | hx
      · exact hx ▸ ⟨⟨0,rfl⟩,⟨0,hg0⟩⟩
      · exact mem_singleton_iff.mp hx ▸ ⟨⟨1,rfl⟩,⟨1,hg1⟩⟩
  let D : ActualMarkedTwoSideDisk M a.toEssential b.toEssential := {
    firstCorner := q 0, secondCorner := q 1,
    firstSide := q, secondSide := g, first_embedded := hq, second_embedded := hg,
    first_zero := rfl,first_one := rfl,second_zero := hg0,second_one := hg1,
    first_on_curve := hqa, second_on_curve := hgg.trans B.second_on_curve,
    sides_inter := hsides,disk := d,disk_embedded := hd,boundary_eq := hdb.trans hc,
    marks_are_corners := hmarks }
  have hmissing : ∃ x ∈ ({B.firstCorner,B.secondCorner}:Set S), x ∉ range D.disk := by
    have hn01 : ¬ (r=0 ∧ s=1) := by
      rintro ⟨rfl,rfl⟩
      apply hnotboth
      rw [← hr,← hs,B.second_zero,B.second_one]
      exact ⟨Or.inl rfl,Or.inr rfl⟩
    have hn10 : ¬ (r=1 ∧ s=0) := by
      rintro ⟨rfl,rfl⟩
      apply hnotboth
      rw [← hr,← hs,B.second_one,B.second_zero]
      exact ⟨Or.inr rfl,Or.inl rfl⟩
    have hend : ∃ v : Interval, (v=0 ∨ v=1) ∧ r≠v ∧ s≠v := by
      by_cases hr0 : r=0
      · refine ⟨1,Or.inr rfl,?_,fun hs1 => hn01 ⟨hr0,hs1⟩⟩
        rw [hr0]
        exact zero_ne_one
      by_cases hs0 : s=0
      · refine ⟨1,Or.inr rfl,fun hr1 => hn10 ⟨hr1,hs0⟩,?_⟩
        rw [hs0]
        exact zero_ne_one
      exact ⟨0,Or.inl rfl,hr0,hs0⟩
    obtain ⟨v,hv,hrv,hsv⟩ := hend
    let x : S := B.secondSide v
    have hxcorner : x ∈ ({B.firstCorner,B.secondCorner}:Set S) := by
      rcases hv with hv | hv
      · exact Or.inl ((congrArg B.secondSide hv).trans B.second_zero)
      · exact Or.inr ((congrArg B.secondSide hv).trans B.second_one)
    have hxB : x ∈ range B.firstSide ∪ range B.secondSide := Or.inr (mem_range_self v)
    have hxnotq : x ∉ range q := by
      rintro ⟨t,ht⟩
      by_cases ht0 : t=0
      · apply hrv
        apply B.second_embedded.injective
        exact hr.trans ((congrArg q ht0).symm.trans ht)
      by_cases ht1 : t=1
      · apply hsv
        apply B.second_embedded.injective
        exact hs.trans ((congrArg q ht1).symm.trans ht)
      exact Set.disjoint_left.mp hfree (ht ▸ hqin ⟨t,
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩) hxB
    have hxnotg : x ∉ range g := by
      rintro ⟨t,ht⟩
      have he : g t = B.secondSide 0 ∨ g t = B.secondSide 1 := by
        rcases hv with hv | hv
        · exact Or.inl (ht.trans (congrArg B.secondSide hv))
        · exact Or.inr (ht.trans (congrArg B.secondSide hv))
      rcases actual_embedded_side_source_endpoint B.secondSide g B.second_embedded hg hgg t he
        with ht0 | ht1
      · exact hxnotq ⟨0,hg0.symm.trans ((congrArg g ht0).symm.trans ht)⟩
      · exact hxnotq ⟨1,hg1.symm.trans ((congrArg g ht1).symm.trans ht)⟩
    have hxnotc : x ∉ c.image := by
      rw [hc]
      exact fun h => h.elim hxnotq hxnotg
    refine ⟨x,hxcorner,?_⟩
    rintro ⟨u,hu⟩
    have hnorm : ‖u.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
    have hne : ‖u.val‖ ≠ 1 := by
      intro he
      apply hxnotc
      rw [← hdb]
      exact ⟨u,by simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using he,hu⟩
    have hxinside : x ∈ B.openInterior := hdin ⟨u,
      by simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right]
        using lt_of_le_of_ne hnorm hne,hu⟩
    exact Set.disjoint_left.mp hfree hxinside hxB
  have hcontact : D.firstCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential ∨
      D.secondCorner ∈ ArcSurgery.crossings M a.toEssential b.toEssential := by
    by_cases h0mark : q 0 ∈ M.cover.branch
    · right
      have h1not : q 1 ∉ M.cover.branch := by
        intro h1mark
        exact hnotboth ⟨B.marks_are_corners _ (hcB (hc.symm ▸ Or.inl (mem_range_self 0))) h0mark,
          B.marks_are_corners _ (hcB (hc.symm ▸ Or.inl (mem_range_self 1))) h1mark⟩
      exact ⟨⟨hqa (mem_range_self 1),h1not⟩,B.second_on_curve ⟨s,hs⟩,h1not⟩
    · left
      exact ⟨⟨hqa (mem_range_self 0),h0mark⟩,B.second_on_curve ⟨r,hr⟩,h0mark⟩
  exact ⟨D,hdB,hmissing,hcontact⟩

end CurveComplex.HyperellipticModel
