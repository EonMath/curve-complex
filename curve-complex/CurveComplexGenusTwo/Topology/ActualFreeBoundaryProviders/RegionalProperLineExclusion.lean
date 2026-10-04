import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.RegionalPlanarJordanSquare

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

/-- A proper planar line that misses a Jordan boundary cannot enter its
    bounded interior. This is the reusable frontier/deck-line exclusion step. -/
theorem proper_line_disjoint_jordan_avoids_inside
    (C : Set Plane) (hC : IsJordanCurve C)
    (L : C(ℝ,Plane)) (hproper : IsProperMap L)
    (havoid : ∀ t : ℝ, L t ∉ C) :
    Set.range L ⊆ (Schoenflies.inside C)ᶜ := by
  have hsep := jordan_curve_theorem hC
  let K := closure (Schoenflies.inside C)
  have hK : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      hsep.isBounded_inside.closure
  have hsub : Set.range L ⊆
      Schoenflies.inside C ∪ Schoenflies.outside C := by
    rintro _ ⟨t,rfl⟩
    rw [inside_union_outside C]
    exact havoid t
  rcases (isPreconnected_range L.continuous).subset_or_subset
      hsep.isOpen_inside hsep.isOpen_outside
      disjoint_inside_outside hsub with hin | hout
  · have hpre : L ⁻¹' K = Set.univ := by
      apply Set.eq_univ_of_forall
      intro t
      exact subset_closure (hin ⟨t,rfl⟩)
    have hc := hproper.isCompact_preimage hK
    rw [hpre] at hc
    exact False.elim (noncompact_univ ℝ hc)
  · exact fun z hz hzInside =>
      Set.disjoint_left.mp disjoint_inside_outside hzInside (hout hz)

theorem proper_line_upper_tail_avoids_jordan_inside
    (C : Set Plane) (hC : IsJordanCurve C)
    (L : C(ℝ,Plane)) (hproper : IsProperMap L)
    (a : ℝ) (havoid : ∀ t : ℝ, a < t → L t ∉ C) :
    L '' Set.Ioi a ⊆ (Schoenflies.inside C)ᶜ := by
  have hsep := jordan_curve_theorem hC
  let K := closure (Schoenflies.inside C)
  have hK : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      hsep.isBounded_inside.closure
  have hsub : L '' Set.Ioi a ⊆
      Schoenflies.inside C ∪ Schoenflies.outside C := by
    rintro _ ⟨t,ht,rfl⟩
    rw [inside_union_outside C]
    exact havoid t ht
  have hconn := (isPreconnected_Ioi (a := a)).image L
    L.continuous.continuousOn
  rcases hconn.subset_or_subset hsep.isOpen_inside
      hsep.isOpen_outside disjoint_inside_outside hsub with hin | hout
  · obtain ⟨B,hB⟩ := (hproper.isCompact_preimage hK).bddAbove
    have ha : a < max a B + 1 := by linarith [le_max_left a B]
    have hp : L (max a B + 1) ∈ K := subset_closure (hin ⟨_,ha,rfl⟩)
    exact False.elim (by linarith [hB hp,le_max_right a B])
  · exact fun z hz hzInside =>
      Set.disjoint_left.mp disjoint_inside_outside hzInside (hout hz)

theorem proper_line_lower_tail_avoids_jordan_inside
    (C : Set Plane) (hC : IsJordanCurve C)
    (L : C(ℝ,Plane)) (hproper : IsProperMap L)
    (a : ℝ) (havoid : ∀ t : ℝ, t < a → L t ∉ C) :
    L '' Set.Iio a ⊆ (Schoenflies.inside C)ᶜ := by
  have hsep := jordan_curve_theorem hC
  let K := closure (Schoenflies.inside C)
  have hK : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      hsep.isBounded_inside.closure
  have hsub : L '' Set.Iio a ⊆
      Schoenflies.inside C ∪ Schoenflies.outside C := by
    rintro _ ⟨t,ht,rfl⟩
    rw [inside_union_outside C]
    exact havoid t ht
  have hconn := (isPreconnected_Iio (a := a)).image L
    L.continuous.continuousOn
  rcases hconn.subset_or_subset hsep.isOpen_inside
      hsep.isOpen_outside disjoint_inside_outside hsub with hin | hout
  · obtain ⟨B,hB⟩ := (hproper.isCompact_preimage hK).bddBelow
    have ha : min a B - 1 < a := by linarith [min_le_left a B]
    have hp : L (min a B - 1) ∈ K := subset_closure (hin ⟨_,ha,rfl⟩)
    exact False.elim (by linarith [hB hp,min_le_right a B])
  · exact fun z hz hzInside =>
      Set.disjoint_left.mp disjoint_inside_outside hzInside (hout hz)

theorem proper_line_single_jordan_contact_avoids_inside
    (C : Set Plane) (hC : IsJordanCurve C)
    (L : C(ℝ,Plane)) (hproper : IsProperMap L)
    (a : ℝ) (ha : L a ∈ C)
    (honly : ∀ t : ℝ, L t ∈ C → t = a) :
    Set.range L ⊆ (Schoenflies.inside C)ᶜ := by
  have hupper := proper_line_upper_tail_avoids_jordan_inside
    C hC L hproper a (fun t ht hc => (ne_of_gt ht) (honly t hc))
  have hlower := proper_line_lower_tail_avoids_jordan_inside
    C hC L hproper a (fun t ht hc => (ne_of_lt ht) (honly t hc))
  rintro z ⟨t,rfl⟩ hz
  rcases lt_trichotomy t a with hlt | he | hgt
  · exact hlower ⟨t,hlt,rfl⟩ hz
  · subst t
    exact (inside_subset_compl hz) ha
  · exact hupper ⟨t,hgt,rfl⟩ hz

end RegionalEmbeddedFamily
