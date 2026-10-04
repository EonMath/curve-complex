import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualStripNarrowing
namespace CurveComplex
open Set Topology Metric
/-- Actual uniform transverse shrinking for any continuous compact strip. -/
theorem source_continuous_strip_uniform_width
    {S : Type} [TopologicalSpace S]
    (B : Interval × Icc (-1:ℝ) 1 → S) (hB : Continuous B)
    (U : Set S) (hU : IsOpen U)
    (hcenter : ∀ t, B (t,⟨0,by norm_num⟩) ∈ U) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ ∧ ρ ≤ 1,
      ∀ t (w : Icc (-1:ℝ) 1),
        B (t,⟨ρ*(w:ℝ),by constructor <;>
          nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩) ∈ U := by
  let O : Set (Interval × Icc (-1:ℝ) 1) := B ⁻¹' U
  have hO : IsOpen O := hU.preimage hB
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
  refine ⟨ρ,hρ,?_⟩
  intro t w
  apply hAW ⟨hUA trivial,?_⟩
  have hw : ρ*(w:ℝ) ∈ Icc (-1:ℝ) 1 := by
    constructor <;> nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]
  have habs : |ρ*(w:ℝ)| < d := by
    rw [abs_mul,abs_of_pos hρ.1]
    exact (mul_le_mul_of_nonneg_left (abs_le.mpr w.property) hρ.1.le).trans_lt
      (by simpa using hρd)
  have hh := hdW (show ρ*(w:ℝ) ∈ ball (0:ℝ) d by
    simpa [mem_ball,Real.dist_eq] using habs)
  simpa [clip,projIcc_of_mem _ hw] using hh
end CurveComplex
#print axioms CurveComplex.source_continuous_strip_uniform_width
