import CurveComplexGenusTwo.Topology.FareyFanStage
import CurveComplexGenusTwo.Foundations.FullSubcomplex
import CurveComplexGenusTwo.Foundations.VertexEquiv
import CurveComplexGenusTwo.Topology.FareyFan

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

noncomputable def fareyFanVertexEquiv : Option ℤ ≃ {v : FareySlope //
    fareyDenominator v ≤ 1} := by
  classical
  let f : Option ℤ → {v : FareySlope // fareyDenominator v ≤ 1} :=
    fun i => ⟨fareyFanSlope i, (fareyDenominator_one_iff_fan _).2 ⟨i, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro i j h
    apply fareyFanSlope_injective
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨i, hi⟩ := (fareyDenominator_one_iff_fan v.1).1 v.2
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hi
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩

theorem fareyFanVertexEquiv_val (i : Option ℤ) :
    (fareyFanVertexEquiv i).1 = fareyFanSlope i := rfl

theorem fareyFan_face_iff_ambient (σ : Finset (Option ℤ)) :
    σ ∈ fareyFanComplex.faces ↔
      (σ.image fareyFanSlope) ∈ fareyComplex.faces := by
  constructor
  · intro hσ
    refine ⟨Finset.image_nonempty.mpr hσ.1, ?_⟩
    intro a ha b hb hab
    rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨j, hj, rfl⟩
    apply hσ.2 hi hj
    intro hij
    exact hab (congrArg fareyFanSlope hij)
  · intro hσ
    refine ⟨Finset.image_nonempty.mp hσ.1, ?_⟩
    intro i hi j hj hij
    have hdiff : fareyFanSlope i ≠ fareyFanSlope j := by
      intro h
      exact hij (fareyFanSlope_injective h)
    exact hσ.2 (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      (Finset.mem_image.mpr ⟨j, hj, rfl⟩) hdiff

theorem fareyFan_face_vertexEquiv_iff (σ : Finset (Option ℤ)) :
    σ ∈ fareyFanComplex.faces ↔
      (σ.image fareyFanVertexEquiv) ∈
        (fullSubcomplex fareyComplex
          (fun v => fareyDenominator v ≤ 1)).faces := by
  rw [mem_fullSubcomplex_iff]
  have heq : (Subtype.val ∘ fareyFanVertexEquiv) = fareyFanSlope := by
    funext i
    exact fareyFanVertexEquiv_val i
  have himage :
      (Finset.image Subtype.val (Finset.image fareyFanVertexEquiv σ)) =
        Finset.image fareyFanSlope σ := by
    rw [Finset.image_image]
    simp only [heq]
  rw [himage]
  exact fareyFan_face_iff_ambient σ

noncomputable def fareyFanRealizationHomeomorphStageOne :
    RealizationPoint fareyFanComplex ≃ₜ
      RealizationPoint (fullSubcomplex fareyComplex
        (fun v => fareyDenominator v ≤ 1)) :=
  realizationHomeomorphOfVertexEquiv fareyFanComplex
    (fullSubcomplex fareyComplex (fun v => fareyDenominator v ≤ 1))
    fareyFanVertexEquiv fareyFan_face_vertexEquiv_iff

noncomputable def fareyStageOneHomeomorph :
    RealizationPoint fareyFanComplex ≃ₜ fareyStage 1 := by
  let h₁ := fareyFanRealizationHomeomorphStageOne
  let h₂ := fullSubcomplexHomeomorphSupported fareyComplex
    (fun v => fareyDenominator v ≤ 1)
  exact h₁.trans h₂

theorem fareyStageOneHomeomorph_weight (x : RealizationPoint fareyFanComplex)
    (v : FareySlope) :
    (fareyStageOneHomeomorph x).1.weight v =
      if hv : fareyDenominator v ≤ 1 then
        x.weight (fareyFanVertexEquiv.symm ⟨v, hv⟩)
      else 0 := by
  by_cases hv : fareyDenominator v ≤ 1
  · change (fullToAmbient fareyComplex (fun v => fareyDenominator v ≤ 1)
        (fareyFanRealizationHomeomorphStageOne x)).weight v = _
    rw [fullToAmbient_weight_of_property fareyComplex _ _ v hv]
    rw [fareyFanRealizationHomeomorphStageOne,
      realizationHomeomorphOfVertexEquiv_weight]
    simp [hv]
  · change (fullToAmbient fareyComplex (fun v => fareyDenominator v ≤ 1)
        (fareyFanRealizationHomeomorphStageOne x)).weight v = _
    rw [fullToAmbient_weight_of_not_property fareyComplex _ _ v hv]
    simp [hv]

theorem fareyStageOneHomeomorph_fanSlope_weight
    (x : RealizationPoint fareyFanComplex) (i : Option ℤ) :
    (fareyStageOneHomeomorph x).1.weight (fareyFanSlope i) =
      x.weight i := by
  rw [fareyStageOneHomeomorph_weight]
  have hden : fareyDenominator (fareyFanSlope i) ≤ 1 :=
    (fareyDenominator_one_iff_fan _).2 ⟨i, rfl⟩
  simp only [hden, dite_true]
  have heq : fareyFanVertexEquiv i = ⟨fareyFanSlope i, hden⟩ := by
    apply Subtype.ext
    rfl
  rw [← heq]
  simp

theorem fareyStageOne_contractible :
    ContractibleSpace (fareyStage 1) := by
  exact (Homeomorph.contractibleSpace_iff fareyStageOneHomeomorph).mp
    fareyFan_contractible

noncomputable def fareyStageOneInterpolate :
    ConeTime × fareyStage 1 → fareyStage 1 := fun p =>
  fareyStageOneHomeomorph
    (coneInterpolateJoint fareyFanComplex none fareyFan_hasConeApex
      (p.1, fareyStageOneHomeomorph.symm p.2))

theorem fareyStageOneInterpolate_continuous :
    Continuous fareyStageOneInterpolate := by
  apply fareyStageOneHomeomorph.continuous.comp
  exact (coneInterpolateJoint_continuous fareyFanComplex none fareyFan_hasConeApex).comp
    (continuous_fst.prodMk
      (fareyStageOneHomeomorph.symm.continuous.comp continuous_snd))

theorem fareyStageOneInterpolate_zero (x : fareyStage 1) :
    fareyStageOneInterpolate (⟨0, by norm_num⟩, x) = x := by
  rw [fareyStageOneInterpolate, coneInterpolateJoint,
    coneInterpolate_zero]
  exact fareyStageOneHomeomorph.apply_symm_apply x

noncomputable def fareyStageOneApex : fareyStage 1 :=
  fareyStageOneHomeomorph (coneVertex fareyFanComplex none)

theorem fareyStageOneInterpolate_one (x : fareyStage 1) :
    fareyStageOneInterpolate (⟨1, by norm_num⟩, x) =
      fareyStageOneApex := by
  rw [fareyStageOneInterpolate, fareyStageOneApex,
    coneInterpolateJoint, coneInterpolate_one]

noncomputable def fareyStageOneHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id (fareyStage 1))
      (ContinuousMap.const (fareyStage 1) fareyStageOneApex) where
  toFun p := fareyStageOneInterpolate p
  continuous_toFun := fareyStageOneInterpolate_continuous
  map_zero_left := fareyStageOneInterpolate_zero
  map_one_left := fareyStageOneInterpolate_one

end CurveComplexGenusTwo.Topology
