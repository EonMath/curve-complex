import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualTwoSuppliedFieldSignComparisonInternal
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseReferenceZeroSet

open scoped Manifold ContDiff Bundle
open Bundle

/-! REVIEW-ONLY source leaf: comparison of two SUPPLIED nondegenerate fields
on the SAME original atlas. Source: Milnor, Topology from the Differentiable
Viewpoint, §6 (sum of local indices independent of the field). The proof route
is the already checked actual complex-ratio/uniform-relative-cap cancellation,
with union-zero discs and finite point detection. No index equality or cap
certificate is a hypothesis. This leaf alone has no numerical Euler claim. -/

theorem actual_same_atlas_two_supplied_fields_literal_sign_sum_eq
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A;
    letI : IsManifold 𝓘(ℂ) ∞ E := hA;
    ∀ hR : IsManifold 𝓘(ℝ,ℂ) ∞ E,
    letI : IsManifold 𝓘(ℝ,ℂ) ∞ E := hR;
    ∀ V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x,
      ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (V x)) →
    ∀ Z : Finset E, (Z : Set E) = {x | V x = 0} →
    ∀ D : Z → (ℂ ≃L[ℝ] ℂ),
      (∀ q : Z, HasFDerivAt
        (fun w : ℂ =>
          let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val + w)
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
            (TotalSpace.mk' ℂ x (V x))).2)
        (D q).toContinuousLinearMap 0) →
    ∀ W : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x,
      ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (W x)) →
    ∀ Q : Finset E, (Q : Set E) = {x | W x = 0} →
    ∀ L : Q → (ℂ ≃L[ℝ] ℂ),
      (∀ q : Q, HasFDerivAt
        (fun w : ℂ =>
          let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val + w)
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
            (TotalSpace.mk' ℂ x (W x))).2)
        (L q).toContinuousLinearMap 0) →
      (∑ q : Z,
        if 0 < (D q 1).re * (D q Complex.I).im - (D q Complex.I).re * (D q 1).im
          then (1 : ℤ) else -1) =
      ∑ q : Q,
        if 0 < (L q 1).re * (L q Complex.I).im - (L q Complex.I).re * (L q 1).im
          then (1 : ℤ) else -1 := by
  run_tac do
    let n := Lean.Name.str (Lean.Name.num
      (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualTwoSuppliedFieldSignComparisonInternal") 0) "actual_same_atlas_two_supplied_fields_literal_sign_sum_eq"
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
      $(Lean.mkIdent `E) $(Lean.mkIdent `hg) $(Lean.mkIdent `A) $(Lean.mkIdent `hA)))

