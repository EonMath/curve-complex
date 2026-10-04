import CurveComplexGenusTwo.Topology.FareyStageCollapse
import CurveComplexGenusTwo.Foundations.JoinFiniteSupport

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

/-- Compact subsets of the weak Farey realization have bounded denominator. -/
theorem compact_farey_has_stage_bound
    (C : Set (RealizationPoint fareyComplex)) (hC : IsCompact C) :
    ∃ n : ℕ, C ⊆ fareyStage n := by
  obtain ⟨F, hF⟩ := compact_realization_has_finite_support fareyComplex C hC
  let n : ℕ := F.sup fareyDenominator
  refine ⟨n, ?_⟩
  intro x hx w hw
  by_contra hne
  have hsupport : w ∈ supportFinset fareyComplex x :=
    (mem_supportFinset_iff fareyComplex x w).2 hne
  exact hw (Finset.le_sup (f := fareyDenominator) (hF x hx hsupport))

/-- The denominator stages cover the entire realization. -/
theorem fareyStage_iUnion :
    (⋃ n : ℕ, fareyStage n) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact fareyStage_exhaustive x

def FareyFaceIndex := {σ : Finset FareySlope // σ ∈ fareyComplex.faces}

noncomputable def fareyFaceCoverMap :
    (Σ σ : FareyFaceIndex, FiniteSimplex σ.1) →
      RealizationPoint fareyComplex :=
  fun p => faceInclusion fareyComplex p.1.1 p.1.2 p.2

theorem fareyFaceCoverMap_isQuotientMap :
    Topology.IsQuotientMap fareyFaceCoverMap := by
  refine ⟨⟨?_⟩, ?_⟩
  · apply TopologicalSpace.ext
    funext U
    apply propext
    change IsOpen U ↔ IsOpen (fareyFaceCoverMap ⁻¹' U)
    constructor
    · intro hU
      exact isOpen_sigma_iff.mpr (fun i => hU i.1 i.2)
    · intro hU σ hσ
      exact isOpen_sigma_iff.mp hU ⟨σ, hσ⟩
  · intro x
    obtain ⟨σ, hσ, y, hy⟩ := exists_faceInclusion_eq fareyComplex x
    exact ⟨⟨⟨σ, hσ⟩, y⟩, hy⟩

theorem continuous_fareyHomotopy_of_faces
    {Y : Type*} [TopologicalSpace Y]
    (f : RealizationPoint fareyComplex × ConeTime → Y)
    (hfaces : Continuous (fun p :
      (Σ σ : FareyFaceIndex, FiniteSimplex σ.1) × ConeTime =>
      f (fareyFaceCoverMap p.1, p.2))) :
    Continuous f :=
  fareyFaceCoverMap_isQuotientMap.continuous_lift_prod_left hfaces

/-- Continuity on every denominator stage suffices for joint continuity on
the actual weak realization times a compact interval. -/
theorem continuous_fareyHomotopy_of_stages
    {Y : Type*} [TopologicalSpace Y]
    (f : RealizationPoint fareyComplex × ConeTime → Y)
    (hstage : ∀ n : ℕ,
      Continuous (fun p : fareyStage n × ConeTime =>
        f ((p.1 : RealizationPoint fareyComplex), p.2))) :
    Continuous f := by
  apply continuous_fareyHomotopy_of_faces f
  let h : (Σ σ : FareyFaceIndex, FiniteSimplex σ.1 × ConeTime) → Y :=
    fun p => f (faceInclusion fareyComplex p.1.1 p.1.2 p.2.1, p.2.2)
  have hh : Continuous h := by
    apply continuous_sigma_iff.mpr
    intro σ
    let n : ℕ := σ.1.sup fareyDenominator
    have hbound : ∀ w ∈ σ.1, fareyDenominator w ≤ n := by
      intro w hw
      exact Finset.le_sup (f := fareyDenominator) hw
    let i : fareyStageFaceIndex n := ⟨σ.1, σ.2, hbound⟩
    let g : FiniteSimplex σ.1 → fareyStage n :=
      fullFaceInclusion fareyComplex
        (fun v => fareyDenominator v ≤ n) i
    have hg : Continuous g :=
      fullFaceInclusion_continuous fareyComplex _ i
    have hp : Continuous (fun p : FiniteSimplex σ.1 × ConeTime =>
        (g p.1, p.2)) :=
      (hg.comp continuous_fst).prodMk continuous_snd
    have hf := (hstage n).comp hp
    convert hf using 1
    funext p
    rfl
  have hd : Continuous (fun p :
      (Σ σ : FareyFaceIndex, FiniteSimplex σ.1) × ConeTime =>
      h (Homeomorph.sigmaProdDistrib p)) :=
    hh.comp (Homeomorph.sigmaProdDistrib).continuous
  simpa only [h, fareyFaceCoverMap, Homeomorph.sigmaProdDistrib_apply] using hd

end CurveComplexGenusTwo.Topology
