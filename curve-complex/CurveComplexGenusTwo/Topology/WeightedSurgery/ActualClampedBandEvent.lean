import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualFiniteEventContinuation
import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.WeightedBandClockHeaders

namespace CurveComplex.WeightedFlowScratch
open scoped BigOperators
variable {V B : Type*} [DecidableEq V] [DecidableEq B]

noncomputable def clampedBandMass (m depth : ℝ) : ℝ := min m (max 0 depth)

noncomputable def actualBandTime (m : ℝ) (hm : 0 ≤ m) (depth : ℝ) : EdgeTime :=
  if h : m = 0 then 0 else
    ⟨clampedBandMass m depth / m,
      div_nonneg (le_min hm (le_max_left _ _)) hm,
      (div_le_one (lt_of_le_of_ne hm (Ne.symm h))).mpr (min_le_left _ _)⟩

theorem actualBandTime_mul_mass (m : ℝ) (hm : 0 ≤ m) (depth : ℝ) :
    (actualBandTime m hm depth).val * m = clampedBandMass m depth := by
  by_cases h : m = 0
  · subst m
    simp [actualBandTime, clampedBandMass]
  · simp [actualBandTime, h]

noncomputable def clampedBranchingSurgeryPoint (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (branches : Finset B) (hne : branches.Nonempty) (f : B → V)
    (hnew : σ ∪ branches.image f ∈ K.faces) (z : ℝ × FiniteSimplex σ) :
    RealizationPoint K :=
  branchingSurgeryPoint K σ hσ selected branches hne f hnew
    (actualBandTime (z.2.val selected) (z.2.property.1 selected) z.1, z.2)

theorem clampedBranchingSurgeryPoint_weight (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (branches : Finset B) (hne : branches.Nonempty) (f : B → V)
    (hnew : σ ∪ branches.image f ∈ K.faces) (z : ℝ × FiniteSimplex σ) (v : V) :
    (clampedBranchingSurgeryPoint K σ hσ selected branches hne f hnew z).weight v =
    ((faceInclusion K σ hσ z.2).weight v -
      (if v = selected.val then clampedBandMass (z.2.val selected) z.1 else 0) +
      ∑ b ∈ branches, if f b = v then clampedBandMass (z.2.val selected) z.1 else 0) /
      (1 + ((branches.card : ℝ)-1) * clampedBandMass (z.2.val selected) z.1) := by
  simp only [clampedBranchingSurgeryPoint, branchingSurgeryPoint,
    surgeryUnnormalizedWeight, surgeryNormalization, surgeryCutMass,
    actualBandTime_mul_mass]

theorem clampedBranchingSurgeryPoint_continuous (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (branches : Finset B) (hne : branches.Nonempty) (f : B → V)
    (hnew : σ ∪ branches.image f ∈ K.faces) :
    Continuous (clampedBranchingSurgeryPoint K σ hσ selected branches hne f hnew) := by
  apply continuous_of_face_coordinates K (σ ∪ branches.image f) hnew
  · intro z v hv
    change surgeryUnnormalizedWeight K σ hσ selected branches f _ v / _ = 0
    rw [surgeryUnnormalizedWeight_zero_outside _ _ _ _ _ _ _ v hv]
    exact zero_div _
  · intro v
    have hm : Continuous (fun z : ℝ × FiniteSimplex σ => z.2.val selected) :=
      (continuous_apply selected).comp (continuous_subtype_val.comp continuous_snd)
    have hr : Continuous (fun z : ℝ × FiniteSimplex σ =>
        clampedBandMass (z.2.val selected) z.1) := hm.min
      (continuous_const.max continuous_fst)
    have hc : Continuous (fun z : ℝ × FiniteSimplex σ =>
        (faceInclusion K σ hσ z.2).weight v) :=
      ((continuous_weight K v).comp (continuous_faceInclusion K σ hσ)).comp continuous_snd
    have hcut : Continuous (fun z : ℝ × FiniteSimplex σ =>
        if v = selected.val then clampedBandMass (z.2.val selected) z.1 else 0) := by
      split_ifs
      · exact hr
      · exact continuous_const
    have hnewmass : Continuous (fun z : ℝ × FiniteSimplex σ =>
        ∑ b ∈ branches, if f b = v then clampedBandMass (z.2.val selected) z.1 else 0) := by
      apply continuous_finsetSum
      intro b _
      split_ifs
      · exact hr
      · exact continuous_const
    have hden : Continuous (fun z : ℝ × FiniteSimplex σ =>
        1 + ((branches.card : ℝ)-1) * clampedBandMass (z.2.val selected) z.1) :=
      continuous_const.add (continuous_const.mul hr)
    have hpositive (z : ℝ × FiniteSimplex σ) :
        0 < 1 + ((branches.card : ℝ)-1) * clampedBandMass (z.2.val selected) z.1 := by
      have hn : (1 : ℝ) ≤ branches.card := by exact_mod_cast Finset.card_pos.mpr hne
      have hr0 : 0 ≤ clampedBandMass (z.2.val selected) z.1 :=
        le_min (z.2.property.1 selected) (le_max_left _ _)
      have hprod := mul_nonneg (sub_nonneg.mpr hn) hr0
      linarith
    have heq : (fun z : ℝ × FiniteSimplex σ =>
        (clampedBranchingSurgeryPoint K σ hσ selected branches hne f hnew z).weight v) =
        fun z => ((faceInclusion K σ hσ z.2).weight v -
          (if v = selected.val then clampedBandMass (z.2.val selected) z.1 else 0) +
          ∑ b ∈ branches, if f b = v then clampedBandMass (z.2.val selected) z.1 else 0) /
          (1 + ((branches.card : ℝ)-1) * clampedBandMass (z.2.val selected) z.1) := by
      funext z
      exact clampedBranchingSurgeryPoint_weight _ _ _ _ _ _ _ _ _ _
    rw [heq]
    exact ((hc.sub hcut).add hnewmass).div hden (fun z => ne_of_gt (hpositive z))

theorem clampedBranchingSurgeryPoint_before (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (branches : Finset B) (hne : branches.Nonempty) (f : B → V)
    (hnew : σ ∪ branches.image f ∈ K.faces) (p : FiniteSimplex σ)
    (depth : ℝ) (hd : depth ≤ 0) :
    clampedBranchingSurgeryPoint K σ hσ selected branches hne f hnew (depth,p) =
      faceInclusion K σ hσ p := by
  apply RealizationPoint.ext
  funext v
  rw [clampedBranchingSurgeryPoint_weight]
  have hz : clampedBandMass (p.val selected) depth = 0 := by
    unfold clampedBandMass
    rw [max_eq_left hd, min_eq_right (p.property.1 selected)]
  simp [hz]

theorem clampedBranchingSurgeryPoint_after (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (branches : Finset B) (hne : branches.Nonempty) (f : B → V)
    (hnew : σ ∪ branches.image f ∈ K.faces) (p : FiniteSimplex σ)
    (depth : ℝ) (hd : p.val selected ≤ depth) :
    clampedBranchingSurgeryPoint K σ hσ selected branches hne f hnew (depth,p) =
      branchingSurgeryPoint K σ hσ selected branches hne f hnew (1,p) := by
  apply RealizationPoint.ext
  funext v
  rw [clampedBranchingSurgeryPoint_weight]
  have hz : clampedBandMass (p.val selected) depth = p.val selected := by
    exact min_eq_left (hd.trans (le_max_right _ _))
  simp [hz, branchingSurgeryPoint, surgeryUnnormalizedWeight, surgeryNormalization,
    surgeryCutMass]

end CurveComplex.WeightedFlowScratch
