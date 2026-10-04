import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers

namespace CurveComplex.HyperellipticModel.ArcSurgery

set_option maxHeartbeats 1000000
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem surgeryPair_rawEssential_iff (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
    (R R' : SurgeryPair M anchor F P x) (side : Bool) :
    IsEssentialMarkedArc M (R.raw side) ↔ IsEssentialMarkedArc M (R'.raw side) := by
  have hi : (R.raw side).image = (R'.raw side).image :=
    (R.raw_trace side).trans (R'.raw_trace side).symm
  have hzero : (R.raw side).map ⟨0, by norm_num⟩ =
      (R'.raw side).map ⟨0, by norm_num⟩ :=
    (R.raw_start side).trans (R'.raw_start side).symm
  have hone : (R.raw side).map ⟨1, by norm_num⟩ =
      (R'.raw side).map ⟨1, by norm_num⟩ :=
    (R.raw_end side).trans (R'.raw_end side).symm
  change ((R.raw side).map ⟨0, by norm_num⟩ ≠ (R.raw side).map ⟨1, by norm_num⟩ ∨
    ∀ U, IsComplementComponent (R.raw side).image U →
      ∃ b, b ∈ M.cover.branch ∧ b ∈ U) ↔
    ((R'.raw side).map ⟨0, by norm_num⟩ ≠ (R'.raw side).map ⟨1, by norm_num⟩ ∨
    ∀ U, IsComplementComponent (R'.raw side).image U →
      ∃ b, b ∈ M.cover.branch ∧ b ∈ U)
  rw [hi, hzero, hone]

theorem surgeryPair_retained_independent (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
    (R R' : SurgeryPair M anchor F P x) : R.retained = R'.retained := by
  ext side
  rw [R.retained_iff, R'.retained_iff]
  exact surgeryPair_rawEssential_iff M anchor F P x R R' side

theorem surgeryPair_pushOff_independent (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
    (R R' : SurgeryPair M anchor F P x) (side : Bool)
    (hs : side ∈ R.retained) (hs' : side ∈ R'.retained) :
    vertex M (R.pushed ⟨side, hs⟩) = vertex M (R'.pushed ⟨side, hs'⟩) := by
  apply Quotient.sound
  change MarkedIsotopyRel M (R.pushed ⟨side, hs⟩).val.image
    (R'.pushed ⟨side, hs'⟩).val.image
  have hi : (R.raw side).image = (R'.raw side).image :=
    (R.raw_trace side).trans (R'.raw_trace side).symm
  have hleft := (markedIsotopy_equivalence M).symm (R.push_isotopy ⟨side, hs⟩)
  have hright := R'.push_isotopy ⟨side, hs'⟩
  rw [← hi] at hright
  exact (markedIsotopy_equivalence M).trans hleft hright

theorem replacementClasses_independent (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
    (R R' : SurgeryPair M anchor F P x) :
    replacementClasses M anchor F P x R = replacementClasses M anchor F P x R' := by
  classical
  letI : DecidableEq (EssentialArcClass M) := instDecidableEqEssentialArcClass_arcSurgeryProducers M
  have hret := surgeryPair_retained_independent M anchor F P x R R'
  have hsub (A B : SurgeryPair M anchor F P x) (hAB : A.retained = B.retained) :
      replacementClasses M anchor F P x A ⊆ replacementClasses M anchor F P x B := by
    intro v hv
    obtain ⟨side, hside, heq⟩ := Finset.mem_image.mp hv
    have hs : side.val ∈ B.retained := hAB ▸ side.property
    apply Finset.mem_image.mpr
    refine ⟨⟨side.val, hs⟩, Finset.mem_attach _ _, ?_⟩
    exact (surgeryPair_pushOff_independent M anchor F P x A B side.val side.property hs).symm.trans heq
  exact Finset.Subset.antisymm (hsub R R' hret) (hsub R' R hret.symm)

end CurveComplex.HyperellipticModel.ArcSurgery
