import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe
import CurveComplexGenusTwo.Topology.FrontierCircle.GlobalBandScaffold

open Set Topology unitInterval
namespace CurveComplex

/-- Two actual half rectangles glued exactly along their bottom edges form
an ambient neighborhood at every interior point of the common seam. -/
theorem glued_half_rectangles_seam_interior_probe
    {S : Type*} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (L R : BandWidth × I → S) (hL : IsEmbedding L) (hR : IsEmbedding R)
    (hseam : ∀ t, L (t,0) = R (t,0))
    (hmeet : Set.range L ∩ Set.range R = Set.range (fun t => L (t,0)))
    (t : BandWidth) (ht0 : (-1:ℝ) < t) (ht1 : (t:ℝ) < 1) :
    L (t,0) ∈ interior (Set.range L ∪ Set.range R) := by
  classical
  let l : EuclideanSpace ℝ (Fin 2) → S := fun z =>
    L (projIcc (-1) 1 (by norm_num) (z 0),projIcc 0 1 zero_le_one (-z 1))
  let r : EuclideanSpace ℝ (Fin 2) → S := fun z =>
    R (projIcc (-1) 1 (by norm_num) (z 0),projIcc 0 1 zero_le_one (z 1))
  let F : EuclideanSpace ℝ (Fin 2) → S := fun z => if z 1 ≤ 0 then l z else r z
  have hl : Continuous l := hL.continuous.comp
    ((continuous_projIcc.comp (by fun_prop)).prodMk (continuous_projIcc.comp (by fun_prop)))
  have hr : Continuous r := hR.continuous.comp
    ((continuous_projIcc.comp (by fun_prop)).prodMk (continuous_projIcc.comp (by fun_prop)))
  have hc : Continuous F := by
    apply continuous_if_le (by fun_prop) continuous_const hl.continuousOn hr.continuousOn
    intro z hz
    simp only [l,r,hz,neg_zero,projIcc_of_mem zero_le_one (show (0:ℝ) ∈ Icc (0:ℝ) 1 by simp)]
    exact hseam _
  let U : Set (EuclideanSpace ℝ (Fin 2)) := {z | z 0 ∈ Ioo (-1) 1 ∧ z 1 ∈ Ioo (-1) 1}
  have hU : IsOpen U := (isOpen_Ioo.preimage (by fun_prop)).inter
    (isOpen_Ioo.preimage (by fun_prop))
  have hX (z) (hz : z ∈ U) :
      (projIcc (-1) 1 (by norm_num) (z 0) : ℝ) = z 0 := by
    rw [projIcc_of_mem (by norm_num) ⟨hz.1.1.le,hz.1.2.le⟩]
  have hLeft (z) (hz : z ∈ U) (hn : z 1 ≤ 0) :
      (projIcc 0 1 zero_le_one (-z 1) : ℝ) = -z 1 := by
    rw [projIcc_of_mem zero_le_one (show -z 1 ∈ Icc (0:ℝ) 1 by constructor <;> linarith [hz.2.1])]
  have hRight (z) (hz : z ∈ U) (hn : 0 ≤ z 1) :
      (projIcc 0 1 zero_le_one (z 1) : ℝ) = z 1 := by
    rw [projIcc_of_mem zero_le_one ⟨hn,hz.2.2.le⟩]
  have hi : InjOn F U := by
    intro z hz w hw he
    dsimp only [F] at he
    split_ifs at he with hz0 hw0 hw0
    · have hh := hL.injective he
      have h0 := congrArg (fun q : BandWidth × I => (q.1:ℝ)) hh
      have h1 := congrArg (fun q : BandWidth × I => (q.2:ℝ)) hh
      dsimp only at h0 h1
      rw [hX z hz,hX w hw] at h0
      rw [hLeft z hz hz0,hLeft w hw hw0] at h1
      ext i
      fin_cases i
      · exact h0
      · exact neg_injective h1
    · have hm : l z ∈ Set.range L ∩ Set.range R := ⟨Set.mem_range_self _,⟨_,he.symm⟩⟩
      rw [hmeet] at hm
      obtain ⟨v,hv⟩ := hm
      have hh := hR.injective (he.symm.trans (hv.symm.trans (hseam v)))
      have h1 := congrArg (fun q : BandWidth × I => (q.2:ℝ)) hh
      dsimp only at h1
      rw [hRight w hw (by linarith)] at h1
      norm_num at h1
      exfalso; linarith
    · have hm : l w ∈ Set.range L ∩ Set.range R := ⟨Set.mem_range_self _,⟨_,he⟩⟩
      rw [hmeet] at hm
      obtain ⟨v,hv⟩ := hm
      have hh := hR.injective (he.trans (hv.symm.trans (hseam v)))
      have h1 := congrArg (fun q : BandWidth × I => (q.2:ℝ)) hh
      dsimp only at h1
      rw [hRight z hz (by linarith)] at h1
      norm_num at h1
      exfalso; linarith
    · have hh := hR.injective he
      have h0 := congrArg (fun q : BandWidth × I => (q.1:ℝ)) hh
      have h1 := congrArg (fun q : BandWidth × I => (q.2:ℝ)) hh
      dsimp only at h0 h1
      rw [hX z hz,hX w hw] at h0
      rw [hRight z hz (by linarith),hRight w hw (by linarith)] at h1
      ext i
      fin_cases i
      · exact h0
      · exact h1
  have hopen : IsOpen (F '' U) := surface_invariance_of_domain_probe F U hU hc.continuousOn hi
  have hsub : F '' U ⊆ Set.range L ∪ Set.range R := by
    rintro z ⟨w,hw,rfl⟩
    dsimp only [F]
    split_ifs
    · exact Or.inl (Set.mem_range_self _)
    · exact Or.inr (Set.mem_range_self _)
  apply (hopen.subset_interior_iff.mpr hsub)
  refine ⟨Schoenflies.Plane.mk t 0,⟨⟨ht0,ht1⟩,by norm_num⟩,?_⟩
  simp [F,l,projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) t.property]

#print axioms glued_half_rectangles_seam_interior_probe
end CurveComplex
