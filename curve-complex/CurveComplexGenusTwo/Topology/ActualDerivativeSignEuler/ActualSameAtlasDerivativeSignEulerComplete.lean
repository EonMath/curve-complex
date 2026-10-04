import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualMorseEulerCountComplete
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualSameWitnessMorseReference
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualGivenVReferenceSignComparison
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Octagon.GraphMV.UnconditionalGraphAssembly
import CurveComplexGenusTwo.Octagon.OctagonRepresentativeScaffold
import CurveComplexGenusTwo.Topology.ActualGenusTwoRecognition.OriginalClosedOrientableRecognitionNamedProofV1
import CurveComplexGenusTwo.Topology.ActualClosedOrientableHomology.OriginalClosedOrientableParameterExclusionProof
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Algebra.Homology.EulerCharacteristic

open scoped Manifold ContDiff Bundle
open Bundle
open CategoryTheory CategoryTheory.Limits Set
open CurveComplex CurveComplex.Octagon CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false

private theorem actual_octagon_higher_singular_homology_zero (n : ℕ) (hn : 3 ≤ n) :
    IsZero (H Surface n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hk : 2 ≤ k := by omega
  have hface := surfaceFace_positive_homology (k+1) (by omega)
  have hband := (actualBoundaryGraphHigherZero (k+1) (by omega)).of_iso
    (bandBoundaryHomologyIso (k+1))
  have hover := surfaceOverlap_higher_homology k hk
  letI : Subsingleton (H faceSet (k+1)) := ModuleCat.subsingleton_of_isZero hface
  letI : Subsingleton (H bandSet (k+1)) := ModuleCat.subsingleton_of_isZero hband
  letI : Subsingleton (H overlapSet k) := ModuleCat.subsingleton_of_isZero hover
  have hz (z : H Surface (k+1)) : z = 0 := by
    have hcz : surfaceActualConnecting k z = 0 := Subsingleton.elim _ _
    obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff _).mp (surfaceActual_exact_surface k) z hcz
    have hvzero : v = 0 := Subsingleton.elim _ _
    rw [← hv, hvzero, map_zero]
  letI : Subsingleton (H Surface (k+1)) := ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

private theorem actual_genus_two_higher_integral_homology_zero
    (E : Type) [TopologicalSpace E] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : IsGenus E 2) (n : ℕ) (hn : 3 ≤ n) : IsZero (integralHomology E n) := by
  obtain ⟨p, hp, ⟨e⟩⟩ := actual_original_genus_two_closed_orientable_recognition E hg
  have hp2 := actual_original_genus_two_closed_orientable_parameter_exclusion E hg p hp ⟨e⟩
  subst p
  let h := e.trans octagonOrientableGenusTwoHomeomorph.symm
  exact (actual_octagon_higher_singular_homology_zero n hn).of_iso
    (CircleHomologyComputation.homotopyHomologyIso h.toHomotopyEquiv n)

private theorem actual_genus_two_full_singular_euler
    (E : Type) [TopologicalSpace E] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : IsGenus E 2) :
    (∑ᶠ n : ℕ, (-1 : ℤ)^n * (Module.finrank ℤ (integralHomology E n) : ℤ)) = -2 := by
  classical
  letI : ClosedSurface E := Classical.choice hg.2.1
  letI : LocallyPathConnectedSpace E := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
  letI : PathConnectedSpace E := PathConnectedSpace.of_locallyPathConnectedSpace
  have hr0 : Module.finrank ℤ (integralHomology E 0) = 1 := by
    let i := CategoryTheory.asIso ((TopCat.of E).singularHomology₀ε (ModuleCat.of ℤ ℤ))
    calc
      Module.finrank ℤ (integralHomology E 0) = Module.finrank ℤ ℤ := i.toLinearEquiv.finrank_eq
      _ = 1 := by simp
  have hr1 : Module.finrank ℤ (integralHomology E 1) = 4 := by
    let i := Classical.choice hg.2.2.2
    calc
      Module.finrank ℤ (integralHomology E 1) = Module.finrank ℤ (Fin (2*2) → ℤ) := i.toLinearEquiv.finrank_eq
      _ = 4 := Module.finrank_fin_fun ℤ
  have hr2 : Module.finrank ℤ (integralHomology E 2) = 1 := by
    let i := Classical.choice hg.2.2.1
    calc
      Module.finrank ℤ (integralHomology E 2) = Module.finrank ℤ ℤ := i.toLinearEquiv.finrank_eq
      _ = 1 := by simp
  have hrHigher (n : ℕ) (hn : 3 ≤ n) : Module.finrank ℤ (integralHomology E n) = 0 := by
    letI := ModuleCat.subsingleton_of_isZero (actual_genus_two_higher_integral_homology_zero E hg n hn)
    exact Module.finrank_zero_of_subsingleton
  have hsupport : Function.support (fun n : ℕ =>
      (-1 : ℤ)^n * (Module.finrank ℤ (integralHomology E n) : ℤ)) ⊆ (Finset.range 3 : Set ℕ) := by
    intro n hn
    by_contra hnot
    have hlarge : 3 ≤ n := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hnot
    exact hn (by dsimp only; rw [hrHigher n hlarge]; simp)
  rw [finsum_eq_sum_of_support_subset _ hsupport]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hr0, hr1, hr2]
  norm_num

private theorem actual_real_derivative_sign_unique
    (f : ℂ → ℂ) (D₁ D₂ : ℂ ≃L[ℝ] ℂ)
    (h₁ : HasFDerivAt f D₁.toContinuousLinearMap 0)
    (h₂ : HasFDerivAt f D₂.toContinuousLinearMap 0) :
    (if 0 < (D₁ 1).re * (D₁ Complex.I).im -
      (D₁ Complex.I).re * (D₁ 1).im then (1:ℤ) else -1) =
    (if 0 < (D₂ 1).re * (D₂ Complex.I).im -
      (D₂ Complex.I).re * (D₂ 1).im then (1:ℤ) else -1) := by
  have h := h₁.unique h₂
  have hOne : D₁ 1 = D₂ 1 := congrArg (fun F : ℂ →L[ℝ] ℂ => F 1) h
  have hI : D₁ Complex.I = D₂ Complex.I :=
    congrArg (fun F : ℂ →L[ℝ] ℂ => F Complex.I) h
  rw [hOne, hI]

private theorem actual_literal_derivative_sign_sum_unique
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (Z : Finset E) (D₁ D₂ : Z → (ℂ ≃L[ℝ] ℂ))
    (h₁ : ∀ q : Z, HasFDerivAt
      (fun w : ℂ =>
        let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+w);
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
          (TotalSpace.mk' ℂ x (V x))).2)
      (D₁ q).toContinuousLinearMap 0)
    (h₂ : ∀ q : Z, HasFDerivAt
      (fun w : ℂ =>
        let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+w);
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
          (TotalSpace.mk' ℂ x (V x))).2)
      (D₂ q).toContinuousLinearMap 0) :
    (∑ q : Z, if 0 < (D₁ q 1).re * (D₁ q Complex.I).im -
      (D₁ q Complex.I).re * (D₁ q 1).im then (1:ℤ) else -1) =
    (∑ q : Z, if 0 < (D₂ q 1).re * (D₂ q Complex.I).im -
      (D₂ q Complex.I).re * (D₂ q 1).im then (1:ℤ) else -1) := by
  apply Finset.sum_congr rfl
  intro q _
  exact actual_real_derivative_sign_unique _ (D₁ q) (D₂ q) (h₁ q) (h₂ q)

private theorem actual_same_atlas_derivative_sign_sum_eq_full_singular_euler
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
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
            let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+w);
            (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
              (TotalSpace.mk' ℂ x (V x))).2)
          (D q).toContinuousLinearMap 0) →
        (∑ q : Z,
          if 0 < (D q 1).re * (D q Complex.I).im -
            (D q Complex.I).re * (D q 1).im then (1:ℤ) else -1) =
          (∑ᶠ n : ℕ, (-1 : ℤ)^n *
            (Module.finrank ℤ (CurveComplex.integralHomology E n) : ℤ)) ∧
        (∑ q : Z,
          if 0 < (D q 1).re * (D q Complex.I).im -
            (D q Complex.I).re * (D q 1).im then (1:ℤ) else -1) = -2 := by
  classical
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  intro hR
  letI : IsManifold 𝓘(ℝ,ℂ) ∞ E := hR
  letI : ClosedSurface E := Classical.choice hg.2.1
  intro V hV Z hZ D hD
  have hreference :
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
    exact actual_same_atlas_genus_two_morse_reference_with_literal_signs E hg A hA
  obtain ⟨F,Q,X,k,c,L,hF,hX,hQ,hcritical,hup,hcharts,hL,hparity⟩ := hreference
  have hcomparison :
      (∑ q : Z, if 0 < (D q 1).re * (D q Complex.I).im -
        (D q Complex.I).re * (D q 1).im then (1:ℤ) else -1) =
      ∑ q : Q, if 0 < (L q 1).re * (L q Complex.I).im -
        (L q Complex.I).re * (L q 1).im then (1:ℤ) else -1 := by
    exact actual_same_atlas_two_supplied_fields_literal_sign_sum_eq
      E hg A hA hR V hV Z hZ D hD X hX Q hQ L hL
  have hreferenceSigns :
      (∑ q : Q, if 0 < (L q 1).re * (L q Complex.I).im -
        (L q Complex.I).re * (L q 1).im then (1:ℤ) else -1) =
      ∑ q : Q, (-1 : ℤ) ^ (k q : ℕ) := by
    exact Finset.sum_congr rfl (fun q _ => hparity q)
  -- Apply the complete integral Euler count to the same retained reference witness.
  have hMorseEulerCount :
      (∑ q : Q, (-1 : ℤ) ^ (k q : ℕ)) =
      ∑ᶠ n : ℕ, (-1 : ℤ)^n *
        (Module.finrank ℤ (CurveComplex.integralHomology E n) : ℤ) := by
    exact actual_smooth_morse_function_full_integral_euler_count
      F hF Q hcritical X hX hup k c
      (fun q => ⟨(hcharts q).1, (hcharts q).2.1⟩)
      (fun q => ⟨(hcharts q).2.2.2.1, (hcharts q).2.2.2.2.1⟩)
      (fun q => (hcharts q).2.2.2.2.2)
  have hfull := hcomparison.trans (hreferenceSigns.trans hMorseEulerCount)
  exact ⟨hfull,hfull.trans (actual_genus_two_full_singular_euler E hg)⟩

#print axioms actual_genus_two_full_singular_euler
#print axioms actual_literal_derivative_sign_sum_unique
#print axioms actual_same_atlas_derivative_sign_sum_eq_full_singular_euler
