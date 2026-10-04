import CurveComplexGenusTwo.Topology.IntersectionParity.BigonDiskData

namespace CurveComplex.LocalSurgery
open Set Topology

theorem other_component_intrusion_crosscut
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (a b c : EssentialCurve E) (B : TwoCurveDisk a.val b.val)
    (hca : Disjoint c.val.image a.val.image)
    (hin : (c.val.image ∩ B.openInterior).Nonempty) :
    ∃ q : C(Interval, E), IsEmbedding q ∧ range q ⊆ c.val.image ∧
      q 0 ∈ range B.secondSide ∧ q 1 ∈ range B.secondSide ∧
      q '' Ioo (0 : Interval) 1 ⊆ B.openInterior ∧
      q 0 ≠ q 1 ∧
      q 0 ∉ ({B.firstCorner, B.secondCorner} : Set E) ∧
      q 1 ∉ ({B.firstCorner, B.secondCorner} : Set E) := by
  have hout : ¬ c.val.image ⊆ range B.disk := by
    intro hc
    obtain ⟨e, he, hb, _⟩ := curve_in_embedded_disk_bounds_subdisk
      c.val B.disk B.disk_embedded hc
    exact c.property ⟨e, he, hb⟩
  obtain ⟨q, hq, hqc, hq0, hq1, hqin⟩ :=
    curve_entering_disk_has_crosscut c.val B.disk B.disk_embedded hout hin
  have hside (t : Interval)
      (ht : q t ∈ range B.firstSide ∪ range B.secondSide) :
      q t ∈ range B.secondSide := by
    rcases ht with ht | ht
    · exact False.elim (Set.disjoint_left.mp hca (hqc (mem_range_self t))
        (B.first_on_curve ht))
    · exact ht
  have hcorner (x : E) (hx : x ∈ ({B.firstCorner, B.secondCorner} : Set E)) :
      x ∈ a.val.image := by
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · exact hx ▸ B.first_on_curve ⟨0, B.first_zero⟩
    · exact (Set.mem_singleton_iff.mp hx) ▸ B.first_on_curve ⟨1, B.first_one⟩
  refine ⟨q, hq, hqc, hside 0 (B.boundary_eq ▸ hq0),
    hside 1 (B.boundary_eq ▸ hq1), hqin, ?_, ?_, ?_⟩
  · intro heq
    exact zero_ne_one (hq.injective heq)
  · exact fun hx => Set.disjoint_left.mp hca (hqc (mem_range_self 0)) (hcorner _ hx)
  · exact fun hx => Set.disjoint_left.mp hca (hqc (mem_range_self 1)) (hcorner _ hx)

theorem other_component_intrusion_produces_subdisk
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (a b c : EssentialCurve E) (B : TwoCurveDisk a.val b.val)
    (hca : Disjoint c.val.image a.val.image)
    (hin : (c.val.image ∩ B.openInterior).Nonempty) :
    ∃ B' : TwoCurveDisk c.val b.val,
      range B'.disk ⊆ range B.disk ∧
      B.firstCorner ∉ range B'.disk ∧
      B.secondCorner ∉ range B'.disk := by
  obtain ⟨q, hq, hqc, hq0, hq1, hqin, hqne, hq0corner, hq1corner⟩ :=
    other_component_intrusion_crosscut a b c B hca hin
  have hdisjoint : Disjoint B.openInterior (range B.firstSide ∪ range B.secondSide) := by
    rw [← B.boundary_eq]
    apply Set.disjoint_left.mpr
    rintro x ⟨u, hu, hux⟩ ⟨v, hv, hvx⟩
    have huv : u = v := B.disk_embedded.injective (hux.trans hvx.symm)
    subst v
    have hu' : ‖u.val‖ < 1 := by
      simpa only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right] using hu
    have hv' : ‖u.val‖ = 1 := by
      simpa only [Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right] using hv
    linarith
  obtain ⟨r, hr⟩ := hq0
  obtain ⟨s, hs⟩ := hq1
  have hrs : r ≠ s := by intro h; apply hqne; rw [← hr, ← hs, h]
  have hr0 : r ≠ 0 := by
    intro h
    exact hq0corner (Set.mem_insert_iff.mpr (Or.inl (hr.symm.trans (h ▸ B.second_zero))))
  have hr1 : r ≠ 1 := by
    intro h
    exact hq0corner (Set.mem_insert_iff.mpr
      (Or.inr (Set.mem_singleton_iff.mpr (hr.symm.trans (h ▸ B.second_one)))))
  have hs0 : s ≠ 0 := by
    intro h
    exact hq1corner (Set.mem_insert_iff.mpr (Or.inl (hs.symm.trans (h ▸ B.second_zero))))
  have hs1 : s ≠ 1 := by
    intro h
    exact hq1corner (Set.mem_insert_iff.mpr
      (Or.inr (Set.mem_singleton_iff.mpr (hs.symm.trans (h ▸ B.second_one)))))
  let affine : Interval → Interval := fun t =>
    ⟨(1 - t.val) * r.val + t.val * s.val, by
      constructor <;> nlinarith [t.property.1, t.property.2, r.property.1,
        r.property.2, s.property.1, s.property.2]⟩
  let g : C(Interval, E) := ⟨B.secondSide ∘ affine,
    B.secondSide.continuous.comp (by fun_prop)⟩
  have hg0 : g 0 = q 0 := by simpa [g, affine] using hr
  have hg1 : g 1 = q 1 := by simpa [g, affine] using hs
  have hginj : Function.Injective g := by
    intro t u he
    have hv := congrArg Subtype.val (B.second_embedded.injective he)
    apply Subtype.ext
    have hne : r.val ≠ s.val := fun h => hrs (Subtype.ext h)
    dsimp [affine] at hv
    have hz : (t.val - u.val) * (s.val - r.val) = 0 := by nlinarith only [hv]
    rcases mul_eq_zero.mp hz with hz | hz
    · exact sub_eq_zero.mp hz
    · exact False.elim (hne (sub_eq_zero.mp hz).symm)
  have hg : Topology.IsEmbedding g := (g.continuous.isClosedEmbedding hginj).isEmbedding
  have hgg : range g ⊆ range B.secondSide := by
    rintro y ⟨t, rfl⟩; exact ⟨affine t, rfl⟩
  have hcross (t u : Interval) (he : q t = g u) :
      (t = 0 ∧ u = 0) ∨ (t = 1 ∧ u = 1) := by
    by_cases ht0 : t = 0
    · left
      refine ⟨ht0, hginj ?_⟩
      rw [hg0, ← he, ht0]
    by_cases ht1 : t = 1
    · right
      refine ⟨ht1, hginj ?_⟩
      rw [hg1, ← he, ht1]
    have htI : t ∈ Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩
    exact False.elim (Set.disjoint_left.mp hdisjoint
      (hqin ⟨t, htI, rfl⟩) (he.symm ▸ Or.inr (hgg ⟨u, rfl⟩)))
  obtain ⟨j, hj⟩ := CurveComplex.exists_curve_of_two_arcs q g hq.injective hg.injective
    hg0.symm hg1.symm hcross
  have hjDisk : j.image ⊆ range B.disk := by
    rw [hj]
    rintro y (⟨t, rfl⟩ | hgy)
    · by_cases ht0 : t = 0
      · subst t
        have hb : q 0 ∈ range B.firstSide ∪ range B.secondSide :=
          Or.inr ⟨r, hr⟩
        obtain ⟨v, hv, heq⟩ := B.boundary_eq.symm ▸ hb
        exact ⟨v, heq⟩
      by_cases ht1 : t = 1
      · subst t
        have hb : q 1 ∈ range B.firstSide ∪ range B.secondSide :=
          Or.inr ⟨s, hs⟩
        obtain ⟨v, hv, heq⟩ := B.boundary_eq.symm ▸ hb
        exact ⟨v, heq⟩
      obtain ⟨v, hv, heq⟩ := hqin ⟨t,
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩, rfl⟩
      exact ⟨v, heq⟩
    · have hb : y ∈ range B.firstSide ∪ range B.secondSide :=
        Or.inr (hgg hgy)
      obtain ⟨v, hv, heq⟩ := B.boundary_eq.symm ▸ hb
      exact ⟨v, heq⟩
  obtain ⟨e, he, heb, hesub⟩ :=
    curve_in_embedded_disk_bounds_subdisk j B.disk B.disk_embedded hjDisk
  have hsides : range q ∩ range g = {q 0, q 1} := by
    ext y
    constructor
    · rintro ⟨⟨t, ht⟩, ⟨u, hu⟩⟩
      rcases hcross t u (ht.trans hu.symm) with ⟨ht0, _⟩ | ⟨ht1, _⟩
      · simp [← ht, ht0]
      · simp [← ht, ht1]
    · intro hy
      rcases Set.mem_insert_iff.mp hy with hy | hy
      · subst y; exact ⟨⟨0, rfl⟩, ⟨0, hg0⟩⟩
      · have hy' : y = q 1 := Set.mem_singleton_iff.mp hy
        subst y; exact ⟨⟨1, rfl⟩, ⟨1, hg1⟩⟩
  let B' : TwoCurveDisk c.val b.val := {
    firstCorner := q 0, secondCorner := q 1, corners_ne := hqne,
    firstSide := q, secondSide := g, first_embedded := hq, second_embedded := hg,
    first_zero := rfl, first_one := rfl, second_zero := hg0, second_one := hg1,
    first_on_curve := hqc, second_on_curve := hgg.trans B.second_on_curve,
    sides_inter := hsides, disk := e, disk_embedded := he,
    boundary_eq := heb.trans hj }
  have hrpos : 0 < r.val := lt_of_le_of_ne r.property.1
    (fun h => hr0 (Subtype.ext h.symm))
  have hspos : 0 < s.val := lt_of_le_of_ne s.property.1
    (fun h => hs0 (Subtype.ext h.symm))
  have hrlt : r.val < 1 := lt_of_le_of_ne r.property.2
    (fun h => hr1 (Subtype.ext h))
  have hslt : s.val < 1 := lt_of_le_of_ne s.property.2
    (fun h => hs1 (Subtype.ext h))
  have ha0 (t : Interval) : 0 < (affine t).val := by
    by_cases ht1 : t.val = 1
    · simp [affine, ht1]; exact hspos
    have hp := mul_pos (sub_pos.mpr (lt_of_le_of_ne t.property.2 ht1)) hrpos
    have hn := mul_nonneg t.property.1 hspos.le
    dsimp [affine]
    nlinarith
  have ha1 (t : Interval) : (affine t).val < 1 := by
    by_cases ht1 : t.val = 1
    · simp [affine, ht1]; exact hslt
    have hp := mul_pos (sub_pos.mpr (lt_of_le_of_ne t.property.2 ht1))
      (sub_pos.mpr hrlt)
    have hn := mul_nonneg t.property.1 (sub_nonneg.mpr hslt.le)
    dsimp [affine]
    nlinarith
  have cornerNotJ (v : Interval) (hv : v = 0 ∨ v = 1) :
      B.secondSide v ∉ j.image := by
    have hvA : B.secondSide v ∈ a.val.image := by
      rcases hv with hv | hv
      · rw [hv, B.second_zero]
        exact B.first_on_curve ⟨0, B.first_zero⟩
      · rw [hv, B.second_one]
        exact B.first_on_curve ⟨1, B.first_one⟩
    rw [hj]
    rintro (⟨t, ht⟩ | ⟨t, ht⟩)
    · exact Set.disjoint_left.mp hca (hqc ⟨t, ht⟩) hvA
    · have ha : affine t = v := B.second_embedded.injective ht
      rcases hv with hv | hv
      · have heq := congrArg Subtype.val ha
        rw [hv] at heq
        exact (not_lt_of_ge (le_of_eq heq)) (ha0 t)
      · have heq := congrArg Subtype.val ha
        rw [hv] at heq
        exact (not_lt_of_ge (le_of_eq heq.symm)) (ha1 t)
  have missingFromDisk (x : E)
      (hx : x ∈ range B.firstSide ∪ range B.secondSide)
      (hxc : x ∉ j.image) : x ∉ range e := by
    rintro ⟨v, hv⟩
    have hn : ‖v.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using v.property
    have hne : ‖v.val‖ ≠ 1 := by
      intro heq
      apply hxc
      rw [← heb]
      refine ⟨v, ?_, hv⟩
      simpa only [Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right] using heq
    have hvopen : e v ∈ e '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      refine ⟨v, ?_, rfl⟩
      simpa only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right] using lt_of_le_of_ne hn hne
    have hsubset : e '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆
        interior (range B.disk) :=
      (embedded_surface_disk_interior_isOpen e he).subset_interior_iff.mpr
        (fun z hz => hesub (Set.image_subset_range _ _ hz))
    have hxinside := hsubset hvopen
    rw [embedded_surface_disk_interior_eq B.disk B.disk_embedded, hv] at hxinside
    exact Set.disjoint_left.mp hdisjoint hxinside hx
  refine ⟨B', hesub, ?_, ?_⟩
  · rw [← B.second_zero]
    exact missingFromDisk _ (Or.inr ⟨0, rfl⟩) (cornerNotJ 0 (Or.inl rfl))
  · rw [← B.second_one]
    exact missingFromDisk _ (Or.inr ⟨1, rfl⟩) (cornerNotJ 1 (Or.inr rfl))

theorem other_component_intrusion_strict_finite_count
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (a b c : EssentialCurve E) (B : TwoCurveDisk a.val b.val)
    (hca : Disjoint c.val.image a.val.image)
    (hin : (c.val.image ∩ B.openInterior).Nonempty)
    (X : Set E) (hX : X.Finite) (hcorner : B.firstCorner ∈ X) :
    ∃ B' : TwoCurveDisk c.val b.val,
      range B'.disk ⊆ range B.disk ∧
      B.firstCorner ∉ range B'.disk ∧
      B.secondCorner ∉ range B'.disk ∧
      (X ∩ range B'.disk).ncard < (X ∩ range B.disk).ncard := by
  obtain ⟨B', hsub, hmiss0, hmiss1⟩ :=
    other_component_intrusion_produces_subdisk a b c B hca hin
  have hcornerDisk : B.firstCorner ∈ range B.disk := by
    have hb : B.firstCorner ∈ range B.firstSide ∪ range B.secondSide :=
      Or.inl ⟨0, B.first_zero⟩
    obtain ⟨v, hv, heq⟩ := B.boundary_eq.symm ▸ hb
    exact ⟨v, heq⟩
  have hstrict : (X ∩ range B'.disk).ncard < (X ∩ range B.disk).ncard := by
    apply Set.ncard_lt_ncard
    · apply Set.ssubset_iff_subset_ne.mpr
      refine ⟨Set.inter_subset_inter_right _ hsub, ?_⟩
      intro heq
      have hx : B.firstCorner ∈ X ∩ range B'.disk :=
        heq.symm ▸ ⟨hcorner, hcornerDisk⟩
      exact hmiss0 hx.2
    · exact hX.subset Set.inter_subset_left
  exact ⟨B', hsub, hmiss0, hmiss1, hstrict⟩

end CurveComplex.LocalSurgery
