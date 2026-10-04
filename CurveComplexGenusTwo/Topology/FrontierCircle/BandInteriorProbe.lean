import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe
import CurveComplexGenusTwo.Topology.FrontierCircle.GlobalBandScaffold

open Set Topology unitInterval
namespace CurveComplex

theorem embedded_rectangle_center_interior_probe
    {S : Type*} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (B : I × BandWidth → S) (hB : IsEmbedding B)
    (t : I) (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) :
    B (t,⟨0,by norm_num⟩) ∈ interior (Set.range B) := by
  let f : EuclideanSpace ℝ (Fin 2) → S := fun z =>
    B (projIcc 0 1 zero_le_one (z 0),projIcc (-1) 1 (by norm_num) (z 1))
  let U : Set (EuclideanSpace ℝ (Fin 2)) := {z | z 0 ∈ Ioo 0 1 ∧ z 1 ∈ Ioo (-1) 1}
  have hU : IsOpen U := (isOpen_Ioo.preimage (by fun_prop)).inter
    (isOpen_Ioo.preimage (by fun_prop))
  have hf : Continuous f := hB.continuous.comp
    ((continuous_projIcc.comp (by fun_prop)).prodMk (continuous_projIcc.comp (by fun_prop)))
  have hi : InjOn f U := by
    intro z hz w hw he
    have hh := hB.injective he
    have h0 := congrArg (fun q : I × BandWidth => (q.1:ℝ)) hh
    have h1 := congrArg (fun q : I × BandWidth => (q.2:ℝ)) hh
    simp only [projIcc_of_mem zero_le_one ⟨hz.1.1.le,hz.1.2.le⟩,
      projIcc_of_mem zero_le_one ⟨hw.1.1.le,hw.1.2.le⟩] at h0
    simp only [projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) ⟨hz.2.1.le,hz.2.2.le⟩,
      projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) ⟨hw.2.1.le,hw.2.2.le⟩] at h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hopen : IsOpen (f '' U) := surface_invariance_of_domain_probe f U hU hf.continuousOn hi
  have hsub : f '' U ⊆ Set.range B := by
    rintro z ⟨w,hw,rfl⟩
    exact Set.mem_range_self _
  apply (hopen.subset_interior_iff.mpr hsub)
  refine ⟨Schoenflies.Plane.mk t 0,⟨⟨ht0,ht1⟩,by norm_num⟩,?_⟩
  simp [f,projIcc_of_mem zero_le_one t.property,
    projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ∈ Icc (-1) 1 by norm_num)]

#print axioms embedded_rectangle_center_interior_probe
end CurveComplex
