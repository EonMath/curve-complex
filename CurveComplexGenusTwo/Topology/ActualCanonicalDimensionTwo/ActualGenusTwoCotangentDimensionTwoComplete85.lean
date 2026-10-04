import CurveComplexGenusTwo.Topology.ActualCanonicalDimensionTwo.ActualDimensionDependencies85

open scoped Manifold ContDiff Bundle TensorProduct
set_option backward.isDefEq.respectTransparency false

theorem actual_genus_two_holomorphic_cotangent_dimension_two
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A
    letI : IsManifold 𝓘(ℂ) ∞ E := hA
    Nonempty (Module.Basis (Fin 2) ℂ (ActualCanonicalSection E)) := by
  classical
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  have hDetection := CanonicalDimensionTwo.actualPointMittagLefflerDetection E hg A hA
  have hZeros : ∀ s : CanonicalDimensionTwo.ActualCanonicalSection E,
      s ≠ 0 → ∃ p : E, s p = 0 := by
    intro s hs
    obtain ⟨Z, hZ, hsum⟩ := actual_genus_two_canonical_section_zero_order_sum E hg A hA s hs
    have hnonempty : Z.Nonempty := by
      by_contra hn
      have he : Z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [he] at hsum
    obtain ⟨p, hp⟩ := hnonempty
    refine ⟨p, ?_⟩
    have hm : p ∈ (Z : Set E) := hp
    rw [hZ] at hm
    exact hm
  letI : Module.Finite ℂ
      (Module.Dual ℂ (ℂ ⊗[ℤ] CurveComplex.integralHomology E 1)) :=
    Module.Finite.of_basis (CanonicalDimensionTwo.genus_two_complex_h1_dual_basis E hg)
  letI : Module.Finite ℂ (CanonicalDimensionTwo.ActualCanonicalSection E) :=
    Module.Finite.of_injective CanonicalDimensionTwo.actualSectionPeriodDual
      (CanonicalDimensionTwo.actualSectionPeriodDual_injective E hg A hA)
  have hLower := CanonicalDimensionTwo.actualCanonicalSection_finrank_ge_two_of_detection_and_zeros
    E hg A hA hDetection hZeros inferInstance
  exact CanonicalDimensionTwo.actualCanonicalSection_basis_of_hodge_injective_and_lower_bound
    E hg A hA (CanonicalDimensionTwo.actualHodgePeriod_injective E hg A hA) hLower

#print axioms actual_genus_two_holomorphic_cotangent_dimension_two
