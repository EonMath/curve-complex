import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenSphereAnnulusExteriorPartitionLocal
import Mathlib.Topology.MetricSpace.Thickening
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies Metric
-- Shrink the actual supplied exterior extension into any genuine open source
-- neighborhood of its WHOLE central cylinder; the central trace is unchanged.
example {X : Type} [TopologicalSpace X]
    (g : C(Circle × Set.Icc (-2:ℝ) 3,X)) (U : Set X) (hU : IsOpen U)
    (hcentral : ∀ z (t : Set.Icc (-2:ℝ) 3), 0 ≤ (t:ℝ) → (t:ℝ) ≤ 1 → g (z,t)∈U) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ z (t : Set.Icc (-2:ℝ) 3), -δ ≤ (t:ℝ) → (t:ℝ)≤1+δ → g (z,t)∈U := by
  audit_main14_base3
    let O := g ⁻¹' U
    have hO : IsOpen O := hU.preimage g.continuous
    let K : Set (Set.Icc (-2:ℝ) 3) := {t | 0 ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1}
    have hK : IsCompact K := by
      have he : K=(Subtype.val : Set.Icc (-2:ℝ) 3 → ℝ) ⁻¹' Set.Icc 0 1 := rfl
      rw [he]
      exact (isClosed_Icc.preimage continuous_subtype_val).isCompact
    have hcontain : (Set.univ : Set Circle) ×ˢ K ⊆ O := by
      rintro ⟨z,t⟩ ⟨hz,ht⟩
      exact hcentral z t ht.1 ht.2
    obtain ⟨D,V,hD,hV,hall,hKV,hDV⟩ := generalized_tube_lemma
      (isCompact_univ : IsCompact (Set.univ : Set Circle)) hK hO hcontain
    let clip : ℝ → Set.Icc (-2:ℝ) 3 := Set.projIcc (-2) 3 (by norm_num)
    have hclip : Continuous clip := continuous_projIcc
    have ho : IsOpen (clip ⁻¹' V) := hV.preimage hclip
    have hi : Set.Icc (0:ℝ) 1 ⊆ clip ⁻¹' V := by
      intro t ht
      let t' : Set.Icc (-2:ℝ) 3 := ⟨t,by constructor <;> linarith [ht.1,ht.2]⟩
      have hc : clip t=t' := Set.projIcc_of_mem (by norm_num) t'.property
      change clip t∈V
      rw [hc]
      exact hKV ht
    obtain ⟨η,hη,hηV⟩ := isCompact_Icc.exists_cthickening_subset_open ho hi
    let δ : ℝ := min (η/2) (1/2)
    have hd : 0 < δ := lt_min (half_pos hη) (by norm_num)
    have hdη : δ ≤ η := (min_le_left _ _).trans (by linarith)
    refine ⟨δ,hd,lt_of_le_of_lt (min_le_right _ _) (by norm_num),?_⟩
    intro z t ht0 ht1
    have hthick : (t:ℝ) ∈ cthickening η (Set.Icc (0:ℝ) 1) := by
      by_cases hlo : (t:ℝ)<0
      · apply mem_cthickening_of_dist_le (t:ℝ) 0 η (Set.Icc 0 1) (by norm_num)
        rw [Real.dist_eq,sub_zero,abs_of_neg hlo]
        linarith
      · by_cases hup : 1<(t:ℝ)
        · apply mem_cthickening_of_dist_le (t:ℝ) 1 η (Set.Icc 0 1) (by norm_num)
          rw [Real.dist_eq,abs_of_pos (by linarith : 0<(t:ℝ)-1)]
          linarith
        · exact self_subset_cthickening (Set.Icc (0:ℝ) 1) ⟨le_of_not_gt hlo,le_of_not_gt hup⟩
    have hv : t∈V := by
      have hh := hηV hthick
      change clip (t:ℝ)∈V at hh
      have hc : clip (t:ℝ)=t := Set.projIcc_of_mem (by norm_num) t.property
      rwa [hc] at hh
    exact hDV ⟨hall (Set.mem_univ z),hv⟩
end CurveComplex.HyperellipticModel
