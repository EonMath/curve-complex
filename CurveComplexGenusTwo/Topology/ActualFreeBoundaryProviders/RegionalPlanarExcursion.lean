import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.RegionalPlanarFiniteLift
import Mathlib.Order.Interval.Set.Infinite
import CurveComplexGenusTwo.Topology.LocalSurgery.ActualReturningSubarc
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalDiskArcLift

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

/-- A finite-contact pair of embedded planar arcs with common endpoints has
    an actual excursion of the second arc away from the first. The excursion
    endpoints are consecutive contacts, so tangencies cause no problem. -/
theorem planar_finite_pair_has_clean_excursion
    (A B : C(Interval,Plane))
    (_hA : Topology.IsEmbedding A) (hB : Topology.IsEmbedding B)
    (h0 : A 0 = B 0) (h1 : A 1 = B 1)
    (hfinite : (Set.range A ∩ Set.range B).Finite) :
    ∃ l r : Interval,
      l < r ∧ B l ∈ Set.range A ∧ B r ∈ Set.range A ∧
      (∀ t : Interval, l < t → t < r → B t ∉ Set.range A) ∧
      ∃ w : Interval, l < w ∧ w < r ∧ B w ∉ Set.range A := by
  classical
  have : Infinite Interval := by
    change Infinite (Set.Icc (0 : ℝ) 1)
    exact Set.Icc.infinite (by norm_num)
  have hBout : ∃ w : Interval, B w ∉ Set.range A := by
    by_contra h
    push Not at h
    have hsub : Set.range B ⊆ Set.range A ∩ Set.range B := by
      rintro z ⟨t,rfl⟩
      exact ⟨h t,Set.mem_range_self t⟩
    have hBfinite : (Set.range B).Finite := hfinite.subset hsub
    exact (Set.infinite_range_of_injective hB.injective) hBfinite
  obtain ⟨w,hw⟩ := hBout
  let T : Set Interval := {t | B t ∈ Set.range A}
  have hT : T.Finite := by
    apply hfinite.of_injOn (show Set.MapsTo B T
      (Set.range A ∩ Set.range B) from fun t ht => ⟨ht,Set.mem_range_self t⟩)
    intro s _ t _ he
    exact hB.injective he
  have hT0 : (0 : Interval) ∈ T := by
    change B 0 ∈ Set.range A
    exact ⟨0,h0⟩
  have hT1 : (1 : Interval) ∈ T := by
    change B 1 ∈ Set.range A
    exact ⟨1,h1⟩
  let L : Set Interval := T ∩ Set.Iic w
  let R : Set Interval := T ∩ Set.Ici w
  have hLf : L.Finite := hT.inter_of_left _
  have hRf : R.Finite := hT.inter_of_left _
  have hLn : L.Nonempty := ⟨0,hT0,w.property.1⟩
  have hRn : R.Nonempty := ⟨1,hT1,w.property.2⟩
  obtain ⟨l,hl,hlmax⟩ := Set.exists_max_image L id hLf hLn
  obtain ⟨r,hr,hrmin⟩ := Set.exists_min_image R id hRf hRn
  have hlw : l < w := lt_of_le_of_ne hl.2 (fun he => hw (he ▸ hl.1))
  have hwr : w < r := lt_of_le_of_ne hr.2 (fun he => hw (he.symm ▸ hr.1))
  refine ⟨l,r,hlw.trans hwr,hl.1,hr.1,?_,w,hlw,hwr,hw⟩
  intro t hlt htr ht
  by_cases htw : t ≤ w
  · exact (not_lt_of_ge (hlmax t ⟨ht,htw⟩)) hlt
  · have hwt : w ≤ t := le_of_not_ge htw
    exact (not_lt_of_ge (hrmin t ⟨ht,hwt⟩)) htr

/-- A consecutive-contact excursion and its matching first-arc subarc
    produce a genuine planar Jordan curve. This disk candidate can still meet
    other deck translates after projection. -/
theorem planar_finite_pair_has_jordan_excursion
    (A B : C(Interval,Plane))
    (hA : Topology.IsEmbedding A) (hB : Topology.IsEmbedding B)
    (h0 : A 0 = B 0) (h1 : A 1 = B 1)
    (hfinite : (Set.range A ∩ Set.range B).Finite) :
    ∃ (P Q : Set Plane) (u v : Plane),
      u ≠ v ∧
      IsArcBetween P u v ∧ IsArcBetween Q u v ∧
      P ⊆ Set.range A ∧ Q ⊆ Set.range B ∧
      P ∩ Q = {u,v} ∧ IsJordanCurve (P ∪ Q) ∧
      ∃ l r : Interval, l < r ∧
        Q \ {u,v} ⊆ B '' Set.Ioo l r ∧
        ∀ t : Interval, l < t → t < r → B t ∉ Set.range A := by
  obtain ⟨l,r,hlr,hBl,hBr,hgap,w,hlw,hwr,hw⟩ :=
    planar_finite_pair_has_clean_excursion A B hA hB h0 h1 hfinite
  obtain ⟨s,hs⟩ := hBl
  obtain ⟨t,ht⟩ := hBr
  have hst : s ≠ t := by
    intro he
    have hBlr : B l = B r := hs.symm.trans (by rw [he]; exact ht)
    exact (ne_of_lt hlr) (hB.injective hBlr)
  obtain ⟨q,hqemb,hqrange,hqint⟩ :=
    CurveComplex.LocalSurgery.actual_embedded_affine_subarc B hB l r hlr
  have hqR : Set.range q ⊆ Set.range B :=
    hqrange.trans (Set.image_subset_range B _)
  have hq0 : q 0 = B l := q.source
  have hq1 : q 1 = B r := q.target
  have hqA : ∀ z ∈ Set.range q, z ∈ Set.range A →
      z = B l ∨ z = B r := by
    rintro z ⟨x,hxz⟩ hzA
    by_cases hx0 : x = 0
    · left
      calc z = q x := hxz.symm
        _ = q 0 := by rw [hx0]
        _ = B l := hq0
    by_cases hx1 : x = 1
    · right
      calc z = q x := hxz.symm
        _ = q 1 := by rw [hx1]
        _ = B r := hq1
    have hxI : x ∈ Set.Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne x.property.1 (Ne.symm hx0),
       lt_of_le_of_ne x.property.2 hx1⟩
    obtain ⟨y,hy,hxy⟩ := hqint ⟨x,hxI,hxz⟩
    exact False.elim (hgap y hy.1 hy.2 (hxy ▸ hzA))
  have hqArc : IsArcBetween (Set.range q) (B l) (B r) := by
    have hh := planar_embedded_path_isArcBetween (q : C(Interval,Plane)) hqemb
    change IsArcBetween (Set.range q) (q 0) (q 1) at hh
    simpa only [hq0,hq1] using hh
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · obtain ⟨p,hpemb,hprange,hpint⟩ :=
      CurveComplex.LocalSurgery.actual_embedded_affine_subarc A hA s t hlt
    have hpR : Set.range p ⊆ Set.range A :=
      hprange.trans (Set.image_subset_range A _)
    have hpArc : IsArcBetween (Set.range p) (B l) (B r) := by
      have hh := planar_embedded_path_isArcBetween (p : C(Interval,Plane)) hpemb
      change IsArcBetween (Set.range p) (p 0) (p 1) at hh
      simpa only [p.source,p.target,hs,ht] using hh
    have hmeet : Set.range p ∩ Set.range q = {B l,B r} := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzP,hzQ⟩
        rcases hqA z hzQ (hpR hzP) with h | h <;> simp [h]
      · rintro z (rfl | rfl)
        · exact ⟨hpArc.left_mem,hqArc.left_mem⟩
        · exact ⟨hpArc.right_mem,hqArc.right_mem⟩
    refine ⟨Set.range p,Set.range q,B l,B r,
      (fun he => (ne_of_lt hlr) (hB.injective he)),
      hpArc,hqArc,hpR,hqR,hmeet,?_,l,r,hlr,?_,hgap⟩
    · exact isJordanCurve_union hpArc hqArc (fun z hzP hzQ => by
        have hz := hmeet ▸ (show z ∈ Set.range p ∩ Set.range q from ⟨hzP,hzQ⟩)
        simpa using hz)
    · rintro z ⟨hzQ,hznot⟩
      obtain ⟨x,hxz⟩ := hzQ
      have hx0 : x ≠ 0 := by
        intro he
        exact hznot (Or.inl (by simpa [he,hq0] using hxz.symm))
      have hx1 : x ≠ 1 := by
        intro he
        exact hznot (Or.inr (by simpa [he,hq1] using hxz.symm))
      exact hqint ⟨x,⟨lt_of_le_of_ne x.property.1 (Ne.symm hx0),
        lt_of_le_of_ne x.property.2 hx1⟩,hxz⟩
  · obtain ⟨p,hpemb,hprange,hpint⟩ :=
      CurveComplex.LocalSurgery.actual_embedded_affine_subarc A hA t s hgt
    have hpR : Set.range p ⊆ Set.range A :=
      hprange.trans (Set.image_subset_range A _)
    have hpArc : IsArcBetween (Set.range p) (B l) (B r) := by
      have hh : IsArcBetween (Set.range p) (B r) (B l) := by
        have hh' := planar_embedded_path_isArcBetween (p : C(Interval,Plane)) hpemb
        change IsArcBetween (Set.range p) (p 0) (p 1) at hh'
        simpa only [p.source,p.target,hs,ht] using hh'
      exact hh.reverse
    have hmeet : Set.range p ∩ Set.range q = {B l,B r} := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzP,hzQ⟩
        rcases hqA z hzQ (hpR hzP) with h | h <;> simp [h]
      · rintro z (rfl | rfl)
        · exact ⟨hpArc.left_mem,hqArc.left_mem⟩
        · exact ⟨hpArc.right_mem,hqArc.right_mem⟩
    refine ⟨Set.range p,Set.range q,B l,B r,?_,hpArc,hqArc,hpR,hqR,
      hmeet,?_,l,r,hlr,?_,hgap⟩
    · exact fun he => (ne_of_lt hlr) (hB.injective he)
    · exact isJordanCurve_union hpArc hqArc (fun z hzP hzQ => by
        have hz := hmeet ▸ (show z ∈ Set.range p ∩ Set.range q from ⟨hzP,hzQ⟩)
        simpa using hz)
    · rintro z ⟨hzQ,hznot⟩
      obtain ⟨x,hxz⟩ := hzQ
      have hx0 : x ≠ 0 := by
        intro he
        exact hznot (Or.inl (by simpa [he,hq0] using hxz.symm))
      have hx1 : x ≠ 1 := by
        intro he
        exact hznot (Or.inr (by simpa [he,hq1] using hxz.symm))
      exact hqint ⟨x,⟨lt_of_le_of_ne x.property.1 (Ne.symm hx0),
        lt_of_le_of_ne x.property.2 hx1⟩,hxz⟩

end RegionalEmbeddedFamily
