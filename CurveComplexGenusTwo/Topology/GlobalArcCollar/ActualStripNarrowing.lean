import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualArcChartSelection
namespace CurveComplex
open Set Topology Metric

/-- Uniformly narrow an actual compact strip into any ambient open set
containing its entire center. No metric or normality on the surface is needed.
The center parametrization remains exact, and one width factor is used at every
longitudinal parameter, so all existing seam equations survive. -/
theorem source_shrink_embedded_strip_in_open
    {S : Type} [TopologicalSpace S] [T2Space S]
    (B : Interval × Icc (-1:ℝ) 1 → S) (hB : IsEmbedding B)
    (U : Set S) (hU : IsOpen U)
    (hcenter : ∀ t, B (t,⟨0,by norm_num⟩) ∈ U) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ ∧ ρ ≤ 1,
      ∃ N : Interval × Icc (-1:ℝ) 1 → S,
        IsEmbedding N ∧ range N ⊆ U ∧
        (∀ z, N z = B (z.1,⟨ρ*(z.2:ℝ),by
          constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]⟩)) ∧
        (∀ t, N (t,⟨0,by norm_num⟩) = B (t,⟨0,by norm_num⟩)) := by
  let O : Set (Interval × Icc (-1:ℝ) 1) := B ⁻¹' U
  have hO : IsOpen O := hU.preimage hB.continuous
  have hbase : univ ×ˢ ({⟨0,by norm_num⟩} : Set (Icc (-1:ℝ) 1)) ⊆ O := by
    rintro ⟨t,w⟩ ⟨_,hw⟩
    have he : w = ⟨0,by norm_num⟩ := hw
    subst w
    exact hcenter t
  obtain ⟨A,W,hA,hW,hUA,h0W,hAW⟩ := generalized_tube_lemma
    isCompact_univ isCompact_singleton hO hbase
  let clip : ℝ → Icc (-1:ℝ) 1 := projIcc (-1) 1 (by norm_num)
  have h0pre : (0:ℝ) ∈ clip ⁻¹' W := by
    simpa [clip,projIcc_of_mem] using
      h0W (mem_singleton (⟨0,by norm_num⟩ : Icc (-1:ℝ) 1))
  obtain ⟨d,hd,hdW⟩ := Metric.mem_nhds_iff.mp
    ((hW.preimage continuous_projIcc).mem_nhds h0pre)
  let ρ : ℝ := min (d/2) (1/2)
  have hρ : 0 < ρ ∧ ρ ≤ 1 := by
    constructor
    · dsimp [ρ]; positivity
    · have hh := min_le_right (d/2) (1/2:ℝ); dsimp [ρ]; linarith
  have hρd : ρ < d := by
    have hh := min_le_left (d/2) (1/2:ℝ); dsimp [ρ]; linarith
  let k : Interval × Icc (-1:ℝ) 1 → Interval × Icc (-1:ℝ) 1 :=
    fun z => (z.1,⟨ρ*(z.2:ℝ),by
      constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]⟩)
  have hkc : Continuous k := by dsimp [k]; fun_prop
  have hki : Function.Injective k := by
    intro z w he
    apply Prod.ext
    · simpa [k] using congrArg Prod.fst he
    · apply Subtype.ext
      exact mul_left_cancel₀ hρ.1.ne' (congrArg (fun z => (z.2:ℝ)) he)
  have hkO (z) : k z ∈ O := by
    apply hAW ⟨hUA trivial,?_⟩
    have hw : ρ*(z.2:ℝ) ∈ Icc (-1:ℝ) 1 := by
      constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]
    have habs : |ρ*(z.2:ℝ)| < d := by
      rw [abs_mul,abs_of_pos hρ.1]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr z.2.property) hρ.1.le).trans_lt
        (by simpa using hρd)
    have hh := hdW (show ρ*(z.2:ℝ) ∈ ball (0:ℝ) d by
      simpa [mem_ball,Real.dist_eq] using habs)
    simpa [clip,projIcc_of_mem _ hw] using hh
  refine ⟨ρ,hρ,B ∘ k,((hB.continuous.comp hkc).isClosedEmbedding
    (hB.injective.comp hki)).isEmbedding,?_,fun _ => rfl,?_⟩
  · rintro x ⟨z,rfl⟩
    exact hkO z
  · intro t
    apply congrArg B
    exact Prod.ext rfl (Subtype.ext (mul_zero _))
end CurveComplex
#print axioms CurveComplex.source_shrink_embedded_strip_in_open
