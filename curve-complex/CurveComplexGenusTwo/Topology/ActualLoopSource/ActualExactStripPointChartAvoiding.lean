import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEmbeddedAnchorPointChart
namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology Schoenflies CurveComplex.ActualCrossingSlide
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- An actual exact fixed-anchor strip PRODUCES a mark-free open chart at its
central point. No transverse second arc or pre-existing chart is assumed. -/
theorem actual_exact_strip_point_chart_avoiding
    (M : HyperellipticModel E S) (A Q : Set S)
    (B : Interval × Icc (-1:ℝ) 1 → S) (hB : IsEmbedding B)
    (hmarks : ∀ z, B z ∉ Q)
    (haxis : ∀ z, B z ∈ A ↔ z.2.val = 0) :
    ∃ U : Set S, ∃ V : Set Plane, ∃ _hU : IsOpen U, ∃ e : U ≃ₜ V,
      Plane.closedSquare 0 1 ⊆ V ∧ Disjoint U (Q : Set S) ∧
      (∀ q : U, q.val ∈ A ↔ (e q).val 1 = 0) ∧
      ∃ hp : B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩) ∈ U,
        (e ⟨B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩),hp⟩).val = 0 := by
  let := (actualSphereSmoothAtlas M).charts
  let q : UnitBox → Interval × Icc (-1:ℝ) 1 := fun z =>
    (⟨(z.val.1+1)/2,by have h := abs_lt.mp z.property.1; constructor <;> linarith⟩,
      ⟨z.val.2,(abs_lt.mp z.property.2).1.le,(abs_lt.mp z.property.2).2.le⟩)
  have hqc : Continuous q := by unfold q; fun_prop
  let inv : Interval × Icc (-1:ℝ) 1 → ℝ × ℝ := fun z => (2*z.1.val-1,z.2.val)
  have hinv : Continuous inv := by unfold inv; fun_prop
  have hqi : IsEmbedding q := by
    apply IsEmbedding.of_comp hqc hinv
    have he : inv ∘ q = (Subtype.val : UnitBox → ℝ × ℝ) := by
      funext z; apply Prod.ext
      · dsimp [inv,q]; ring
      · rfl
    rw [he]
    exact IsEmbedding.subtypeVal
  let f : UnitBox → S := B ∘ q
  have hf : IsEmbedding f := hB.comp hqi
  let U : Set S := range f
  let F : Plane → S := fun z => B (projIcc 0 1 zero_le_one ((z 0+1)/2),
    projIcc (-1) 1 (by norm_num) (z 1))
  have hFc : Continuous F := by
    apply hB.continuous.comp
    exact (continuous_projIcc.comp (by fun_prop)).prodMk (continuous_projIcc.comp (by fun_prop))
  have hFU : F '' Plane.openSquare 0 1 = U := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hz' : |z 0| < 1 ∧ |z 1| < 1 :=
        max_lt_iff.mp (mem_openSquare_zero_one.mp hz)
      refine ⟨⟨(z 0,z 1),hz'⟩,?_⟩
      apply congrArg B
      apply Prod.ext <;> apply Subtype.ext
      · have h := abs_lt.mp hz'.1
        rw [projIcc_of_mem zero_le_one
          (show (z 0+1)/2 ∈ Icc (0:ℝ) 1 by constructor <;> linarith)]
      · rw [projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1)
          ⟨(abs_lt.mp hz'.2).1.le,(abs_lt.mp hz'.2).2.le⟩]
    · rintro ⟨z,rfl⟩
      refine ⟨Plane.mk z.val.1 z.val.2,?_,?_⟩
      · apply mem_openSquare_zero_one.mpr
        exact max_lt_iff.mpr z.property
      · apply congrArg B
        apply Prod.ext <;> apply Subtype.ext
        · have h := abs_lt.mp z.property.1
          change (projIcc 0 1 zero_le_one ((z.val.1+1)/2)).val = (z.val.1+1)/2
          rw [projIcc_of_mem zero_le_one (show (z.val.1+1)/2 ∈ Icc (0:ℝ) 1 by constructor <;> linarith)]
        · change (projIcc (-1) 1 (by norm_num) z.val.2).val = z.val.2
          rw [projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1)
              ⟨(abs_lt.mp z.property.2).1.le,(abs_lt.mp z.property.2).2.le⟩]
  have hFi : InjOn F (Plane.openSquare 0 1) := by
    intro z hz w hw he
    have hz' := max_lt_iff.mp (mem_openSquare_zero_one.mp hz)
    have hw' := max_lt_iff.mp (mem_openSquare_zero_one.mp hw)
    have hqcoord (z : Plane) (hz : |z 0| < 1 ∧ |z 1| < 1) :
        F z = f ⟨(z 0,z 1),hz⟩ := by
      apply congrArg B
      apply Prod.ext <;> apply Subtype.ext
      · have h := abs_lt.mp hz.1
        rw [projIcc_of_mem zero_le_one
          (show (z 0+1)/2 ∈ Icc (0:ℝ) 1 by constructor <;> linarith)]
      · rw [projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1)
          ⟨(abs_lt.mp hz.2).1.le,(abs_lt.mp hz.2).2.le⟩]
    rw [hqcoord z hz',hqcoord w hw'] at he
    have h := congrArg Subtype.val (hf.injective he)
    ext i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hU : IsOpen U := hFU ▸ surface_invariance_of_domain_probe F _
    (Plane.isOpen_openSquare 0 1) hFc.continuousOn hFi
  let j : UnitBox ≃ₜ U := hf.toHomeomorph
  let V : Set Plane := doublePlaneCoordinates '' {z : ℝ × ℝ | |z.1|<1 ∧ |z.2|<1}
  let e : U ≃ₜ V := j.symm.trans (doublePlaneCoordinates.image _)
  have hCV : Plane.closedSquare 0 1 ⊆ V := by
    intro z hz
    have h := max_le_iff.mp (mem_closedSquare_zero_one.mp hz)
    refine ⟨(z 0/2,z 1/2),?_,?_⟩
    · change |z 0/2| < 1 ∧ |z 1/2| < 1
      rw [abs_div,abs_div]; norm_num
      constructor <;> linarith [h.1,h.2]
    · apply planeCoordinates.injective
      apply Prod.ext
      · change 2*(z 0/2) = z 0; ring
      · change 2*(z 1/2) = z 1; ring
  have hj (z : U) : B (q (j.symm z)) = z.val := congrArg Subtype.val (j.apply_symm_apply z)
  let z0 : UnitBox := ⟨(0,0),by norm_num⟩
  have hz0 : f z0 = B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩) := by
    apply congrArg B
    apply Prod.ext <;> apply Subtype.ext <;> norm_num [q,z0]
  have hpU : B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩) ∈ U := ⟨z0,hz0⟩
  refine ⟨U,V,hU,e,hCV,?_,?_,hpU,?_⟩
  · apply Set.disjoint_left.mpr
    rintro z ⟨w,rfl⟩ hz
    exact hmarks (q w) hz
  · intro z
    rw [← hj z,haxis]
    change (j.symm z).val.2 = 0 ↔ 2*(j.symm z).val.2 = 0
    constructor <;> intro h <;> linarith
  · have he : j.symm ⟨B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩),hpU⟩ = z0 := by
      apply j.injective
      rw [j.apply_symm_apply]
      apply Subtype.ext
      exact hz0.symm
    change doublePlaneCoordinates (j.symm _).val = 0
    rw [he]
    apply planeCoordinates.injective
    apply Prod.ext
    · change 2*(0:ℝ) = 0; ring
    · change 2*(0:ℝ) = 0; ring
end
end CurveComplex.HyperellipticModel.ArcSurgery
