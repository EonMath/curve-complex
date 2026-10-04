import CurveComplexGenusTwo.Topology.Smoothing.ActualEndpointGerms

open Set Filter
open scoped Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- One positive cut works simultaneously for every actual incident germ,
including both ends of loops, inside any given neighborhood of the vertex. -/
theorem uniform_actual_endpoint_germs
    (M : HyperellipticModel E S) (ι : Type) [Fintype ι]
    (a : ι → EssentialMarkedArc M) (p : S)
    (U : Set S) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      (∀ i, (a i).val.map ⟨0, by norm_num⟩ = p →
        ∀ t : Interval, t.val ≤ r → (a i).val.map t ∈ U) ∧
      (∀ i, (a i).val.map ⟨1, by norm_num⟩ = p →
        ∀ t : Interval, 1 - r ≤ t.val → (a i).val.map t ∈ U) := by
  have hs : ∀ᶠ t : Interval in 𝓝 ⟨0, by norm_num⟩,
      ∀ i, (a i).val.map ⟨0, by norm_num⟩ = p → (a i).val.map t ∈ U := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : (a i).val.map ⟨0, by norm_num⟩ = p
    · have hmem : U ∈ 𝓝 ((a i).val.map ⟨0, by norm_num⟩) := by
        rw [hi]; exact hU.mem_nhds hpU
      exact ((a i).val.continuous.continuousAt.eventually hmem).mono (fun t ht _ => ht)
    · exact Eventually.of_forall (fun t h => False.elim (hi h))
  have he : ∀ᶠ t : Interval in 𝓝 ⟨1, by norm_num⟩,
      ∀ i, (a i).val.map ⟨1, by norm_num⟩ = p → (a i).val.map t ∈ U := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : (a i).val.map ⟨1, by norm_num⟩ = p
    · have hmem : U ∈ 𝓝 ((a i).val.map ⟨1, by norm_num⟩) := by
        rw [hi]; exact hU.mem_nhds hpU
      exact ((a i).val.continuous.continuousAt.eventually hmem).mono (fun t ht _ => ht)
    · exact Eventually.of_forall (fun t h => False.elim (hi h))
  obtain ⟨δ0, hδ0, hsδ⟩ := Metric.eventually_nhds_iff.mp hs
  obtain ⟨δ1, hδ1, heδ⟩ := Metric.eventually_nhds_iff.mp he
  let r : ℝ := min (min (δ0 / 2) (δ1 / 2)) (1 / 4)
  have hr0 : 0 < r := lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have hrδ0 : r < δ0 := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  have hrδ1 : r < δ1 := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  refine ⟨r, hr0, lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_, ?_⟩
  · intro i hi t ht
    apply hsδ _ i hi
    rw [Subtype.dist_eq, Real.dist_eq]
    change |t.val - 0| < δ0
    rw [sub_zero, abs_of_nonneg t.property.1]
    exact lt_of_le_of_lt ht hrδ0
  · intro i hi t ht
    apply heδ _ i hi
    rw [Subtype.dist_eq, Real.dist_eq]
    change |t.val - 1| < δ1
    rw [abs_of_nonpos (by linarith [t.property.2])]
    linarith

#print axioms uniform_actual_endpoint_germs
end CurveComplex.HyperellipticModel
