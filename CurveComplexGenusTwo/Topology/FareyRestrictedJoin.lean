import CurveComplexGenusTwo.Topology.FareyJoinFirstStage

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set unitInterval

private noncomputable def fareyJoinFirstEndpoint
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base)) :
    ContinuousMap (RealizationPoint fareyJoinComplex)
      (RealizationPoint fareyJoinComplex) where
  toFun := fun x => fareyJoinReplaceLeft base H 1 x
  continuous_toFun := by
    have hc : Continuous (fun x : RealizationPoint fareyJoinComplex =>
        ((1 : I), x)) := continuous_const.prodMk continuous_id
    exact (fareyJoinReplaceLeft_continuous base H).comp hc

private noncomputable def fareyJoinFirstMap
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base)) :
    ContinuousMap (I × RealizationPoint fareyJoinComplex)
      (RealizationPoint fareyJoinComplex) where
  toFun := fun z => fareyJoinReplaceLeft base H z.1 z.2
  continuous_toFun := fareyJoinReplaceLeft_continuous base H

private theorem fareyJoinFirstMap_zero
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base))
    (x : RealizationPoint fareyJoinComplex) :
    fareyJoinFirstMap base H (0, x) = x :=
  fareyJoinReplaceLeft_zero base H x

private theorem fareyJoinFirstMap_one
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base))
    (x : RealizationPoint fareyJoinComplex) :
    fareyJoinFirstMap base H (1, x) = fareyJoinFirstEndpoint base H x := rfl

private noncomputable def fareyJoinFirstHomotopy
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base)) :
    ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyJoinComplex))
      (fareyJoinFirstEndpoint base H) where
  toContinuousMap := fareyJoinFirstMap base H
  map_zero_left := fareyJoinFirstMap_zero base H
  map_one_left := fareyJoinFirstMap_one base H

private noncomputable def fareyJoinCollapseMap
    (base : RealizationPoint fareyFlagComplex) :
    ContinuousMap (I × RealizationPoint fareyJoinComplex)
      (RealizationPoint fareyJoinComplex) where
  toFun := fun z => fareyJoinCollapseRight base z.1 z.2
  continuous_toFun := fareyJoinCollapseRight_continuous base

private noncomputable def fareyJoinSecondInput
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base)) :
    ContinuousMap (I × RealizationPoint fareyJoinComplex)
      (I × RealizationPoint fareyJoinComplex) where
  toFun := fun z => (z.1, fareyJoinFirstEndpoint base H z.2)
  continuous_toFun := by
    exact continuous_fst.prodMk
      ((fareyJoinFirstEndpoint base H).continuous.comp continuous_snd)

private noncomputable def fareyJoinSecondMap
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base)) :
    ContinuousMap (I × RealizationPoint fareyJoinComplex)
      (RealizationPoint fareyJoinComplex) :=
  (fareyJoinCollapseMap base).comp (fareyJoinSecondInput base H)

private theorem fareyJoinReplaceLeft_one_mass
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base))
    (x : RealizationPoint fareyJoinComplex) :
    fareyJoinLeftMass (fareyJoinReplaceLeft base H 1 x) =
      fareyJoinLeftMass x := by
  classical
  have hsupp : fareyJoinRight
      (supportFinset fareyJoinComplex (fareyJoinReplaceLeft base H 1 x)) =
      fareyJoinRight (supportFinset fareyJoinComplex x) := by
    ext b
    simp only [mem_fareyJoinRight_iff, mem_supportFinset_iff]
    by_cases hm : 0 < fareyJoinLeftMass x
    · rw [fareyJoinReplaceLeft_weight_inr_of_pos base H 1 x hm b]
    · simp [fareyJoinReplaceLeft, hm]
  have hright : fareyJoinRightMass (fareyJoinReplaceLeft base H 1 x) =
      fareyJoinRightMass x := by
    unfold fareyJoinRightMass
    rw [hsupp]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hm : 0 < fareyJoinLeftMass x
    · exact fareyJoinReplaceLeft_weight_inr_of_pos base H 1 x hm b
    · simp [fareyJoinReplaceLeft, hm]
  have hsum1 := fareyJoinMass_sum_one (fareyJoinReplaceLeft base H 1 x)
  have hsum2 := fareyJoinMass_sum_one x
  linarith

private theorem fareyJoinSecondMap_zero
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base))
    (x : RealizationPoint fareyJoinComplex) :
    fareyJoinSecondMap base H (0, x) = fareyJoinFirstEndpoint base H x := by
  exact fareyJoinCollapseRight_zero_of_leftBase base
    (fareyJoinFirstEndpoint base H x) (by
      intro a
      change (fareyJoinReplaceLeft base H 1 x).weight (.inl a) =
        fareyJoinLeftMass (fareyJoinReplaceLeft base H 1 x) * base.weight a
      rw [fareyJoinReplaceLeft_one_mass base H x]
      exact fareyJoinReplaceLeft_one_leftBase base H x a)

private theorem fareyJoinSecondMap_one
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base))
    (x : RealizationPoint fareyJoinComplex) :
    fareyJoinSecondMap base H (1, x) =
      fareyJoinBlend 0 base base := by
  change fareyJoinCollapseRight base 1 (fareyJoinFirstEndpoint base H x) = _
  exact fareyJoinCollapseRight_one base (fareyJoinFirstEndpoint base H x)

private noncomputable def fareyJoinSecondHomotopy
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base)) :
    ContinuousMap.Homotopy
      (fareyJoinFirstEndpoint base H)
      (ContinuousMap.const (RealizationPoint fareyJoinComplex)
        (fareyJoinBlend 0 base base)) where
  toContinuousMap := fareyJoinSecondMap base H
  map_zero_left := fareyJoinSecondMap_zero base H
  map_one_left := fareyJoinSecondMap_one base H

/-- A genuine contraction of the Farey factor contracts the weak realization
of the join via left-factor replacement and right-mass collapse. -/
theorem fareyJoin_contractible_of_left_factor_contraction
    (base : RealizationPoint fareyFlagComplex)
    (H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex) base)) :
    ContractibleSpace (RealizationPoint fareyJoinComplex) := by
  apply (contractible_iff_id_nullhomotopic
    (RealizationPoint fareyJoinComplex)).2
  refine ⟨fareyJoinBlend 0 base base, ?_⟩
  exact ⟨(fareyJoinFirstHomotopy base H).trans
    (fareyJoinSecondHomotopy base H)⟩

end CurveComplexGenusTwo.Topology

#print axioms CurveComplexGenusTwo.Topology.fareyJoin_contractible_of_left_factor_contraction
