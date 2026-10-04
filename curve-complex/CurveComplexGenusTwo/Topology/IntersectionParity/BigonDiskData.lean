import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import CurveComplexGenusTwo.Topology.IntersectionParity.Subdisk
import CurveComplexGenusTwo.Topology.IntersectionParity.ArcInterior
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskCrosscut
import CurveComplexGenusTwo.Topology.IntersectionParity.CurveImageInclusion
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed

namespace CurveComplex.LocalSurgery

/-- A genuine disk candidate with two original curve sides. Interior emptiness
is deliberately the producer's conclusion, not a field of this data. -/
structure TwoCurveDisk {S : Type} [TopologicalSpace S] (a b : Curve S) where
  firstCorner : S
  secondCorner : S
  corners_ne : firstCorner ≠ secondCorner
  firstSide : C(Interval, S)
  secondSide : C(Interval, S)
  first_embedded : Topology.IsEmbedding firstSide
  second_embedded : Topology.IsEmbedding secondSide
  first_zero : firstSide 0 = firstCorner
  second_zero : secondSide 0 = firstCorner
  first_one : firstSide 1 = secondCorner
  second_one : secondSide 1 = secondCorner
  first_on_curve : Set.range firstSide ⊆ a.image
  second_on_curve : Set.range secondSide ⊆ b.image
  sides_inter : Set.range firstSide ∩ Set.range secondSide = {firstCorner, secondCorner}
  disk : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S)
  disk_embedded : Topology.IsEmbedding disk
  boundary_eq : disk '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
    Set.range firstSide ∪ Set.range secondSide

noncomputable def TwoCurveDisk.crossingCount
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    (B : TwoCurveDisk a b) (ht : Transverse a b) : ℕ := by
  classical
  exact (ht.1.toFinset.filter fun x => x ∈ Set.range B.disk).card

def TwoCurveDisk.openInterior
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    (B : TwoCurveDisk a b) : Set S :=
  B.disk '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}

/-- The source innermostness descent is an actual crosscut/subdisk construction
with a strict finite crossing decrease, not an assumed minimum disk. -/
theorem nonempty_two_curve_disk_has_smaller_disk
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (a b : EssentialCurve S) (ht : Transverse a.val b.val)
    (B : TwoCurveDisk a.val b.val)
    (hinterior : (B.openInterior ∩ (a.val.image ∪ b.val.image)).Nonempty) :
    ∃ B' : TwoCurveDisk a.val b.val,
      B'.crossingCount ht < B.crossingCount ht := by
  classical
  have firstSideDescent (a b : EssentialCurve S) (ht : Transverse a.val b.val)
      (B : TwoCurveDisk a.val b.val)
      (hin : (a.val.image ∩ B.openInterior).Nonempty) :
      ∃ B' : TwoCurveDisk a.val b.val, B'.crossingCount ht < B.crossingCount ht := by
    have hout (c : EssentialCurve S) : ¬ c.val.image ⊆ Set.range B.disk := by
      intro hc
      obtain ⟨e, he, hb, _⟩ := curve_in_embedded_disk_bounds_subdisk c.val B.disk B.disk_embedded hc
      exact c.property ⟨e, he, hb⟩
    have hdisjoint : Disjoint B.openInterior (Set.range B.firstSide ∪ Set.range B.secondSide) := by
      rw [← B.boundary_eq]
      apply Set.disjoint_left.mpr
      rintro x ⟨u, hu, hux⟩ ⟨v, hv, hvx⟩
      have huv : u = v := B.disk_embedded.injective (hux.trans hvx.symm)
      subst v
      have hu' : ‖u.val‖ < 1 := by simpa only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right] using hu
      have hv' : ‖u.val‖ = 1 := by simpa only [Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right] using hv
      linarith
    have endpointOnOther (q : C(Interval, S)) (hqa : Set.range q ⊆ a.val.image)
        (hqinside : q '' Set.Ioo (0 : Interval) 1 ⊆ B.openInterior)
        (e : Interval) (hqe : q e ∈ Set.range B.firstSide ∪ Set.range B.secondSide) :
        q e ∈ Set.range B.secondSide := by
      by_contra hnot
      have hefirst : q e ∈ Set.range B.firstSide := hqe.resolve_right hnot
      obtain ⟨v, hv⟩ := hefirst
      have hv0 : v ≠ 0 := by
        intro heq
        subst v
        rw [B.first_zero] at hv
        exact hnot ⟨0, B.second_zero.trans hv⟩
      have hv1 : v ≠ 1 := by
        intro heq
        subst v
        rw [B.first_one] at hv
        exact hnot ⟨1, B.second_one.trans hv⟩
      have hvI : v ∈ Set.Ioo (0 : Interval) 1 := by
        constructor
        · exact lt_of_le_of_ne (show (0 : Interval) ≤ v from v.property.1) (Ne.symm hv0)
        · exact lt_of_le_of_ne (show v ≤ (1 : Interval) from v.property.2) hv1
      let qA : C(Interval, a.val.image) :=
        ⟨fun t => ⟨q t, hqa ⟨t, rfl⟩⟩, q.continuous.subtype_mk _⟩
      let N := qA ⁻¹' {x : a.val.image | (x : S) ∈ B.firstSide '' Set.Ioo (0 : Interval) 1}
      have hNopen : IsOpen N := (embedded_curve_subarc_interior_isOpen a.val B.firstSide
        B.first_embedded B.first_on_curve).preimage qA.continuous
      have heN : e ∈ N := ⟨v, hvI, hv⟩
      have hecl : e ∈ closure (Set.Ioo (0 : Interval) 1) := by
        rw [closure_Ioo (by norm_num : (0 : Interval) ≠ 1)]
        exact ⟨e.property.1, e.property.2⟩
      obtain ⟨t, htN, htI⟩ := mem_closure_iff_nhds.mp hecl N (hNopen.mem_nhds heN)
      have htU := hqinside (Set.mem_image_of_mem q htI)
      have htB : q t ∈ Set.range B.firstSide ∪ Set.range B.secondSide := by
        obtain ⟨v, hvI, hv⟩ := htN
        exact Or.inl ⟨v, hv⟩
      exact Set.disjoint_left.mp hdisjoint htU htB
    have hcorner : B.firstCorner ∈ a.val.image ∩ b.val.image := by
      exact ⟨B.first_on_curve ⟨0, B.first_zero⟩, B.second_on_curve ⟨0, B.second_zero⟩⟩
    have hcornerDisk : B.firstCorner ∈ Set.range B.disk := by
      have hb : B.firstCorner ∈ Set.range B.firstSide ∪ Set.range B.secondSide :=
        Or.inl ⟨0, B.first_zero⟩
      obtain ⟨x, hx, heq⟩ := B.boundary_eq.symm ▸ hb
      exact ⟨x, heq⟩
    have smallerCard (B' : TwoCurveDisk a.val b.val)
        (hsub : Set.range B'.disk ⊆ Set.range B.disk)
        (x : S) (hx : x ∈ a.val.image ∩ b.val.image) (hxB : x ∈ Set.range B.disk)
        (hmissing : x ∉ Set.range B'.disk) :
        B'.crossingCount ht < B.crossingCount ht := by
      unfold TwoCurveDisk.crossingCount
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, hsub hx.2⟩
      · intro heq
        have hm : x ∈ ht.1.toFinset.filter (fun x => x ∈ Set.range B.disk) := by
          simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
          exact ⟨hx, hxB⟩
        rw [← heq] at hm
        exact hmissing (Finset.mem_filter.mp hm).2
    obtain ⟨q, hq, hqa, hq0, hq1, hqinside⟩ := curve_entering_disk_has_crosscut
      a.val B.disk B.disk_embedded (hout a) hin
    have hqe0 : q 0 ∈ Set.range B.secondSide :=
      endpointOnOther q hqa hqinside 0 (B.boundary_eq ▸ hq0)
    have hqe1 : q 1 ∈ Set.range B.secondSide :=
      endpointOnOther q hqa hqinside 1 (B.boundary_eq ▸ hq1)
    have hqneq : q 0 ≠ q 1 := by
      intro heq
      have he := hq.injective heq
      norm_num at he
    have noBothCorners (f : C(Interval, S)) (hf : Function.Injective f)
        (hfB : Set.range f ⊆ Set.range B.firstSide)
        (hf0 : f 0 = q 0) (hf1 : f 1 = q 1) : False := by
      have hcrossFirst (t u : Interval) (he : q t = f u) :
          (t = 0 ∧ u = 0) ∨ (t = 1 ∧ u = 1) := by
        by_cases ht0 : t = 0
        · exact Or.inl ⟨ht0, hf (by rw [hf0, ← he, ht0])⟩
        by_cases ht1 : t = 1
        · exact Or.inr ⟨ht1, hf (by rw [hf1, ← he, ht1])⟩
        have htI : t ∈ Set.Ioo (0 : Interval) 1 :=
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩
        exact False.elim (Set.disjoint_left.mp hdisjoint (hqinside ⟨t, htI, rfl⟩)
          (Or.inl (he.symm ▸ hfB ⟨u, rfl⟩)))
      obtain ⟨cA, hcA⟩ := CurveComplex.exists_curve_of_two_arcs q f hq.injective hf
        hf0.symm hf1.symm hcrossFirst
      have hcAa : cA.image ⊆ a.val.image := by
        rw [hcA]; exact Set.union_subset hqa (hfB.trans B.first_on_curve)
      have hcEq := curve_image_eq_of_subset a.val cA hcAa
      apply hout a
      rw [← hcEq, hcA]
      rintro y (⟨t, rfl⟩ | hfy)
      · by_cases ht0 : t = 0
        · subst t; obtain ⟨v, hv, he⟩ := hq0; exact ⟨v, he⟩
        by_cases ht1 : t = 1
        · subst t; obtain ⟨v, hv, he⟩ := hq1; exact ⟨v, he⟩
        obtain ⟨v, hv, he⟩ := hqinside ⟨t,
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩, rfl⟩
        exact ⟨v, he⟩
      · have hb : y ∈ Set.range B.firstSide ∪ Set.range B.secondSide := Or.inl (hfB hfy)
        rw [← B.boundary_eq] at hb
        obtain ⟨v, hv, he⟩ := hb
        exact ⟨v, he⟩
    obtain ⟨r, hr⟩ := hqe0
    obtain ⟨s, hs⟩ := hqe1
    have hrs : r ≠ s := by intro h; apply hqneq; rw [← hr, ← hs, h]
    have hn01 : ¬ (r = 0 ∧ s = 1) := by
      rintro ⟨hr0, hs1⟩
      apply noBothCorners B.firstSide B.first_embedded.injective (Set.Subset.refl _)
      · rw [B.first_zero]; simpa [hr0, B.second_zero] using hr
      · rw [B.first_one]; simpa [hs1, B.second_one] using hs
    have hn10 : ¬ (r = 1 ∧ s = 0) := by
      rintro ⟨hr1, hs0⟩
      let rev : C(Interval, Interval) := ⟨fun t => ⟨1 - t.val, by
        constructor <;> linarith [t.property.1, t.property.2]⟩, by fun_prop⟩
      let f : C(Interval, S) := B.firstSide.comp rev
      apply noBothCorners f
      · intro t u he
        have he' := congrArg Subtype.val (B.first_embedded.injective he)
        apply Subtype.ext
        change 1 - t.val = 1 - u.val at he'
        linarith
      · rintro y ⟨t, rfl⟩; exact ⟨rev t, rfl⟩
      · change B.firstSide (rev 0) = q 0
        have hrev : rev 0 = 1 := by apply Subtype.ext; norm_num [rev]
        rw [hrev, B.first_one]
        simpa [hr1, B.second_one] using hr
      · change B.firstSide (rev 1) = q 1
        have hrev : rev 1 = 0 := by apply Subtype.ext; norm_num [rev]
        rw [hrev, B.first_zero]
        simpa [hs0, B.second_zero] using hs
    let affine : Interval → Interval := fun t =>
      ⟨(1 - t.val) * r.val + t.val * s.val, by
        constructor <;> nlinarith [t.property.1, t.property.2, r.property.1,
          r.property.2, s.property.1, s.property.2]⟩
    let g : C(Interval, S) := ⟨B.secondSide ∘ affine,
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
    have hgg : Set.range g ⊆ Set.range B.secondSide := by
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
      have htI : t ∈ Set.Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩
      have huB : q t ∈ Set.range B.firstSide ∪ Set.range B.secondSide := by
        rw [he]; exact Or.inr (hgg ⟨u, rfl⟩)
      exact False.elim (Set.disjoint_left.mp hdisjoint (hqinside ⟨t, htI, rfl⟩) huB)
    obtain ⟨c, hc⟩ := CurveComplex.exists_curve_of_two_arcs q g hq.injective hg.injective
      (hg0.symm) (hg1.symm) hcross
    have hcDisk : c.image ⊆ Set.range B.disk := by
      rw [hc]
      rintro y (⟨t, rfl⟩ | hgy)
      · by_cases ht0 : t = 0
        · subst t; obtain ⟨v, hv, he⟩ := hq0; exact ⟨v, he⟩
        by_cases ht1 : t = 1
        · subst t; obtain ⟨v, hv, he⟩ := hq1; exact ⟨v, he⟩
        obtain ⟨v, hv, he⟩ := hqinside ⟨t,
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩, rfl⟩
        exact ⟨v, he⟩
      · have hb : y ∈ Set.range B.firstSide ∪ Set.range B.secondSide := Or.inr (hgg hgy)
        obtain ⟨v, hv, he⟩ := B.boundary_eq.symm ▸ hb
        exact ⟨v, he⟩
    obtain ⟨e, he, heb, hesub⟩ := curve_in_embedded_disk_bounds_subdisk c B.disk B.disk_embedded hcDisk
    have missingFromDisk (x : S)
        (hx : x ∈ Set.range B.firstSide ∪ Set.range B.secondSide)
        (hxc : x ∉ c.image) : x ∉ Set.range e := by
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
          interior (Set.range B.disk) :=
        (embedded_surface_disk_interior_isOpen e he).subset_interior_iff.mpr
          (fun z hz => hesub (Set.image_subset_range _ _ hz))
      have hxinside := hsubset hvopen
      rw [embedded_surface_disk_interior_eq B.disk B.disk_embedded, hv] at hxinside
      exact Set.disjoint_left.mp hdisjoint hxinside hx
    have hendpoint : ∃ v : Interval, (v = 0 ∨ v = 1) ∧ r ≠ v ∧ s ≠ v := by
      by_cases hr0 : r = 0
      · refine ⟨1, Or.inr rfl, ?_, ?_⟩
        · rw [hr0]; norm_num
        · intro hs1; exact hn01 ⟨hr0, hs1⟩
      by_cases hs0 : s = 0
      · refine ⟨1, Or.inr rfl, ?_, ?_⟩
        · intro hr1; exact hn10 ⟨hr1, hs0⟩
        · rw [hs0]; norm_num
      exact ⟨0, Or.inl rfl, hr0, hs0⟩
    obtain ⟨v, hv, hrv, hsv⟩ := hendpoint
    let x := B.secondSide v
    have hxB : x ∈ Set.range B.firstSide ∪ Set.range B.secondSide := Or.inr ⟨v, rfl⟩
    have hxCurve : x ∈ a.val.image ∩ b.val.image := by
      refine ⟨?_, B.second_on_curve ⟨v, rfl⟩⟩
      rcases hv with hv | hv
      · change B.secondSide v ∈ a.val.image
        rw [hv, B.second_zero]
        exact B.first_on_curve ⟨0, B.first_zero⟩
      · change B.secondSide v ∈ a.val.image
        rw [hv, B.second_one]
        exact B.first_on_curve ⟨1, B.first_one⟩
    have hxNotQ : x ∉ Set.range q := by
      rintro ⟨t, ht⟩
      by_cases ht0 : t = 0
      · apply hrv
        apply B.second_embedded.injective
        exact hr.trans (ht0 ▸ ht)
      by_cases ht1 : t = 1
      · apply hsv
        apply B.second_embedded.injective
        exact hs.trans (ht1 ▸ ht)
      exact Set.disjoint_left.mp hdisjoint
        (ht ▸ hqinside ⟨t,
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩, rfl⟩) hxB
    have hxNotG : x ∉ Set.range g := by
      rintro ⟨t, ht⟩
      have ha : affine t = v := B.second_embedded.injective ht
      have hav := congrArg Subtype.val ha
      rcases hv with hv | hv
      · have hrpos : 0 < r.val := lt_of_le_of_ne r.property.1 (by intro h; exact hrv (hv ▸ Subtype.ext h.symm))
        have hspos : 0 < s.val := lt_of_le_of_ne s.property.1 (by intro h; exact hsv (hv ▸ Subtype.ext h.symm))
        rw [hv] at hav
        dsimp [affine] at hav
        by_cases ht1 : t.val = 1
        · simp [ht1] at hav; exact hsv (hav.trans hv.symm)
        have hp := mul_pos (sub_pos.mpr (lt_of_le_of_ne t.property.2 ht1)) hrpos
        have hn := mul_nonneg t.property.1 s.property.1
        norm_num at hav
        nlinarith
      · have hrlt : r.val < 1 := lt_of_le_of_ne r.property.2 (by intro h; exact hrv (hv ▸ Subtype.ext h))
        have hslt : s.val < 1 := lt_of_le_of_ne s.property.2 (by intro h; exact hsv (hv ▸ Subtype.ext h))
        rw [hv] at hav
        dsimp [affine] at hav
        by_cases ht1 : t.val = 1
        · simp [ht1] at hav; exact hsv (hav.trans hv.symm)
        have hp := mul_pos (sub_pos.mpr (lt_of_le_of_ne t.property.2 ht1)) (sub_pos.mpr hrlt)
        have hn := mul_nonneg t.property.1 (sub_nonneg.mpr s.property.2)
        norm_num at hav
        nlinarith
    have hxNotC : x ∉ c.image := by rw [hc]; exact fun h => h.elim hxNotQ hxNotG
    have hsides : Set.range q ∩ Set.range g = {q 0, q 1} := by
      ext y
      constructor
      · rintro ⟨⟨t, ht⟩, ⟨u, hu⟩⟩
        rcases hcross t u (ht.trans hu.symm) with ⟨ht0, hu0⟩ | ⟨ht1, hu1⟩
        · simp [← ht, ht0]
        · simp [← ht, ht1]
      · intro hy
        rcases Set.mem_insert_iff.mp hy with hy | hy
        · subst y; exact ⟨⟨0, rfl⟩, ⟨0, hg0⟩⟩
        · have hy' : y = q 1 := Set.mem_singleton_iff.mp hy
          subst y; exact ⟨⟨1, rfl⟩, ⟨1, hg1⟩⟩
    let B' : TwoCurveDisk a.val b.val := {
      firstCorner := q 0, secondCorner := q 1, corners_ne := hqneq,
      firstSide := q, secondSide := g, first_embedded := hq, second_embedded := hg,
      first_zero := rfl, first_one := rfl, second_zero := hg0, second_one := hg1,
      first_on_curve := hqa, second_on_curve := hgg.trans B.second_on_curve,
      sides_inter := hsides, disk := e, disk_embedded := he,
      boundary_eq := heb.trans hc }
    refine ⟨B', smallerCard B' hesub x hxCurve ?_ (missingFromDisk x hxB hxNotC)⟩
    obtain ⟨w, hw, heq⟩ := B.boundary_eq.symm ▸ hxB
    exact ⟨w, heq⟩
  let swapDisk {c d : Curve S} (B : TwoCurveDisk c d) : TwoCurveDisk d c := {
    firstCorner := B.firstCorner
    secondCorner := B.secondCorner
    corners_ne := B.corners_ne
    firstSide := B.secondSide
    secondSide := B.firstSide
    first_embedded := B.second_embedded
    second_embedded := B.first_embedded
    first_zero := B.second_zero
    second_zero := B.first_zero
    first_one := B.second_one
    second_one := B.first_one
    first_on_curve := B.second_on_curve
    second_on_curve := B.first_on_curve
    sides_inter := by rw [Set.inter_comm]; exact B.sides_inter
    disk := B.disk
    disk_embedded := B.disk_embedded
    boundary_eq := by rw [B.boundary_eq, Set.union_comm] }
  rcases hinterior with ⟨p, hpB, hpa | hpb⟩
  · exact firstSideDescent a b ht B ⟨p, hpa, hpB⟩
  · let ht' := transverse_symm_of_chart ht
    obtain ⟨B', hcount⟩ := firstSideDescent b a ht' (swapDisk B) ⟨p, hpb, hpB⟩
    refine ⟨swapDisk B', ?_⟩
    have hsets : ht'.1.toFinset = ht.1.toFinset := by
      ext x
      simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, and_comm]
    change (ht.1.toFinset.filter fun x => x ∈ Set.range B'.disk).card <
      (ht.1.toFinset.filter fun x => x ∈ Set.range B.disk).card
    change (ht'.1.toFinset.filter fun x => x ∈ Set.range B'.disk).card <
      (ht'.1.toFinset.filter fun x => x ∈ Set.range B.disk).card at hcount
    rw [hsets] at hcount
    exact hcount

end CurveComplex.LocalSurgery
