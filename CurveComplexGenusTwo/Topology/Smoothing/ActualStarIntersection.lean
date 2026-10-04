import CurveComplexGenusTwo.Topology.Smoothing.ActualGermArcs

open Set
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

lemma normalized_endpoint_germ_subset (M : HyperellipticModel E S)
    (a : EssentialMarkedArc M) (b : Bool) (r : ℝ) (hr : 0 < r) (hrhalf : r < 1 / 2) :
    (a.val.map ∘ endpointGermParameter b r hr (by linarith)) ''
      {t : Interval | 0 < t.val} ⊆ a.val.map '' endpointGermParameters b r := by
  rintro x ⟨t, ht, rfl⟩
  change 0 < t.val at ht
  refine ⟨endpointGermParameter b r hr (by linarith) t, ?_, rfl⟩
  cases b <;> change _ ∧ _
  · change 0 < r * t.val ∧ r * t.val ≤ r
    constructor
    · exact mul_pos hr ht
    · nlinarith [t.property.2]
  · change 1 - r ≤ 1 - r * t.val ∧ 1 - r * t.val < 1
    constructor
    · nlinarith [t.property.2]
    · nlinarith

/-- The actual normalized closed endpoint star meets exactly at its marked
vertex. Loop halves are distinct arms; full-family interior disjointness gives
the same conclusion between different arcs. -/
theorem actual_normalized_star_intersection
    (M : HyperellipticModel E S) {ι : Type} (a : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (a i)) (arcInterior M (a j)))
    (p : S) (r : ℝ) (hr : 0 < r) (hrhalf : r < 1 / 2)
    (v w : ι × Bool) (hvw : v ≠ w)
    (hv : (a v.1).val.map (endpointGermParameter v.2 r hr (by linarith) ⟨0, by norm_num⟩) = p)
    (hw : (a w.1).val.map (endpointGermParameter w.2 r hr (by linarith) ⟨0, by norm_num⟩) = p) :
    Set.range ((a v.1).val.map ∘ endpointGermParameter v.2 r hr (by linarith)) ∩
      Set.range ((a w.1).val.map ∘ endpointGermParameter w.2 r hr (by linarith)) = {p} := by
  have hdis := actual_endpoint_germs_disjoint M a hd r hrhalf v w hvw
  have hdis' := hdis.mono
    (normalized_endpoint_germ_subset M (a v.1) v.2 r hr hrhalf)
    (normalized_endpoint_germ_subset M (a w.1) w.2 r hr hrhalf)
  ext x
  constructor
  · rintro ⟨⟨t, ht⟩, ⟨u, hu⟩⟩
    by_cases ht0 : t.val = 0
    · have ht' : t = (⟨0, by norm_num⟩ : Interval) := Subtype.ext ht0
      subst t
      exact mem_singleton_iff.mpr (ht.symm.trans hv)
    · by_cases hu0 : u.val = 0
      · have hu' : u = (⟨0, by norm_num⟩ : Interval) := Subtype.ext hu0
        subst u
        exact mem_singleton_iff.mpr (hu.symm.trans hw)
      · exact False.elim (Set.disjoint_left.mp hdis'
          ⟨t, lt_of_le_of_ne t.property.1 (Ne.symm ht0), ht⟩
          ⟨u, lt_of_le_of_ne u.property.1 (Ne.symm hu0), hu⟩)
  · intro hx
    have hx' : x = p := mem_singleton_iff.mp hx
    subst x
    exact ⟨⟨⟨0, by norm_num⟩, hv⟩, ⟨⟨0, by norm_num⟩, hw⟩⟩

#print axioms actual_normalized_star_intersection
end CurveComplex.HyperellipticModel
