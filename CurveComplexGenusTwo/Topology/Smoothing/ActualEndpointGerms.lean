import CurveComplexGenusTwo.Topology.Smoothing.ActualEndpointIsolation

open Set
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Endpoint-germ parameters exclude their marked vertex. True selects the
terminal germ; false the initial germ. Both incidences of a loop are retained. -/
def endpointGermParameters (terminal : Bool) (r : ℝ) : Set Interval :=
  if terminal then {t | 1 - r ≤ t.val ∧ t.val < 1}
  else {t | 0 < t.val ∧ t.val ≤ r}

lemma endpointGermParameters_interior (b : Bool) (r : ℝ) (hr : r < 1 / 2)
    {t : Interval} (ht : t ∈ endpointGermParameters b r) : 0 < t.val ∧ t.val < 1 := by
  cases b <;> simp only [endpointGermParameters, Bool.false_eq_true, if_false, if_true,
    Set.mem_setOf_eq] at ht
  · exact ⟨ht.1, by linarith [ht.2]⟩
  · exact ⟨by linarith [ht.1], ht.2⟩

lemma endpointGermParameters_disjoint (r : ℝ) (hr : r < 1 / 2)
    (b c : Bool) (hbc : b ≠ c) :
    Disjoint (endpointGermParameters b r) (endpointGermParameters c r) := by
  apply Set.disjoint_left.mpr
  intro t ht hc
  cases b <;> cases c <;> simp_all [endpointGermParameters] <;> linarith

/-- The actual finite family induces pairwise disjoint endpoint germs, with
two distinct incidences for each loop. No target-ray normalization is assumed. -/
theorem actual_endpoint_germs_disjoint
    (M : HyperellipticModel E S) {ι : Type} (a : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (a i)) (arcInterior M (a j)))
    (r : ℝ) (hr : r < 1 / 2) :
    ∀ v w : ι × Bool, v ≠ w →
      Disjoint ((a v.1).val.map '' endpointGermParameters v.2 r)
        ((a w.1).val.map '' endpointGermParameters w.2 r) := by
  intro v w hvw
  apply Set.disjoint_left.mpr
  rintro z ⟨t, ht, rfl⟩ ⟨u, hu, heq⟩
  have hti := endpointGermParameters_interior v.2 r hr ht
  have hui := endpointGermParameters_interior w.2 r hr hu
  have ht0 : t ≠ (⟨0, by norm_num⟩ : Interval) := by
    intro hh; have hx := congrArg Subtype.val hh; dsimp at hx; linarith [hti.1]
  have ht1 : t ≠ (⟨1, by norm_num⟩ : Interval) := by
    intro hh; have hx := congrArg Subtype.val hh; dsimp at hx; linarith [hti.2]
  have hnotmarked : (a v.1).val.map t ∉ M.cover.branch := by
    intro hb
    rcases (a v.1).val.marked_only_at_ends t hb with hh | hh
    · exact ht0 hh
    · exact ht1 hh
  by_cases hij : v.1 = w.1
  · have hbc : v.2 ≠ w.2 := by
      intro hbc; apply hvw; exact Prod.ext hij hbc
    rw [← hij] at heq
    rcases (a v.1).val.injective_except_loop_closure t u heq.symm with hequal | hclose | hclose
    · subst u
      exact Set.disjoint_left.mp (endpointGermParameters_disjoint r hr v.2 w.2 hbc) ht hu
    · exact ht0 hclose.1
    · exact ht1 hclose.1
  · exact Set.disjoint_left.mp (hd v.1 w.1 hij)
      ⟨⟨t, rfl⟩, hnotmarked⟩ ⟨⟨u, heq⟩, hnotmarked⟩

#print axioms actual_endpoint_germs_disjoint
end CurveComplex.HyperellipticModel
