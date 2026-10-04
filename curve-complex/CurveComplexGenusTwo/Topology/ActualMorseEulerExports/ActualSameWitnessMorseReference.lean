import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseWeightedLinearizationInternal
import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualSameAtlasMorseCoordinatesComplete
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseReferenceZeroSet

open scoped Manifold ContDiff Bundle
open Bundle Set

/-! REVIEW-ONLY same-witness producer. Source: Milnor, Morse Theory, §2
and §6; original compact bump/weighted-gradient construction. F,Z,X and the
literal original tangent-chart derivatives are produced together. -/

theorem actual_same_atlas_genus_two_morse_reference_with_literal_signs
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A;
    letI : IsManifold 𝓘(ℂ) ∞ E := hA;
    letI : IsManifold 𝓘(ℝ,ℂ) ∞ E := actual_same_atlas_complex_is_real_smooth E hA;
    ∃ (F : E → ℝ) (Z : Finset E)
      (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
      (k : Z → Fin 3) (c : Z → OpenPartialHomeomorph E ℂ)
      (D : Z → (ℂ ≃L[ℝ] ℂ)),
      ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F ∧
      ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (X x)) ∧
      (Z : Set E) = {x | X x = 0} ∧
      (Z : Set E) = {x | mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x = 0} ∧
      (∀ x : E, x ∉ Z →
        0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
          ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x))) ∧
      (∀ q : Z, q.val ∈ (c q).source ∧ c q q.val = 0 ∧
        c q ∈ IsManifold.maximalAtlas 𝓘(ℝ,ℂ) ∞ E ∧
        ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q) (c q).source ∧
        ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q).symm (c q).target ∧
        ∀ x ∈ (c q).source, F x = F q.val + actualComplexMorseQuadratic (k q) (c q x)) ∧
      (∀ q : Z, HasFDerivAt
        (fun w : ℂ =>
          let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val + w)
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
            (TotalSpace.mk' ℂ x (X x))).2)
        (D q).toContinuousLinearMap 0) ∧
      ∀ q : Z,
        (if 0 < (D q 1).re * (D q Complex.I).im - (D q Complex.I).re * (D q 1).im
          then (1 : ℤ) else -1) = (-1 : ℤ) ^ (k q).val := by
  run_tac do
    let n := Lean.Name.str (Lean.Name.num
      (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualMorseWeightedLinearizationInternal") 0) "actual_same_witness_morse_reference_internal"
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
      $(Lean.mkIdent `E) $(Lean.mkIdent `hg) $(Lean.mkIdent `A) $(Lean.mkIdent `hA)))

