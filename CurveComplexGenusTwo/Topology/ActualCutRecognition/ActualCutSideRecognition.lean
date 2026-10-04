import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.ActualCutRecognition.ActualCutPositiveNormalForms
import CurveComplexGenusTwo.CWHurewicz.CircleHomologyComputation
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryModelHomologyComplete

namespace CurveComplex.Hyperbolic
open Set Topology CategoryTheory
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The one-boundary orientable compact-surface recognition step of the same
source cut. The rank-two singular homology is the preceding DERIVED helper's
output. The original theorem gains no additional premise. The ambient
compactness and actual whole-circle collar must produce the compact cut-side
model before normal-form recognition; no supplied surface classification or
preselected punctured-torus model is accepted. -/
theorem actual_rank_two_cut_side_punctured_torus_recognition
    (M : HyperellipticModel E S) (c : Curve E) (hc : Essential c)
    (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
    (hUconn : IsConnected U) (hVconn : IsConnected V)
    (hUV : Disjoint U V) (hcover : U ∪ V = c.imageᶜ)
    (hfrontU : frontier U = c.image) (hfrontV : frontier V = c.image)
    (hUone : Nonempty (integralHomology U 1 ≅ ModuleCat.of ℤ (Fin 2 → ℤ))) :
    Nonempty (U ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) := by
  classical
  obtain ⟨p, q, hp, hq, ⟨eU⟩, hmodelV⟩ :=
    actual_essential_cut_positive_orientable_normal_forms M c hc U V
      hU hV hUconn hVconn hUV hcover hfrontU hfrontV
  let eHU := CircleHomologyComputation.homotopyHomologyIso eU.toHomotopyEquiv 1
  obtain ⟨eModelH1⟩ := actual_one_boundary_orientable_model_homology_one p
  obtain ⟨eUone⟩ := hUone
  let eRank : ModuleCat.of ℤ (Fin (2 * p) → ℤ) ≅ ModuleCat.of ℤ (Fin 2 → ℤ) :=
    eModelH1.symm ≪≫ eHU.symm ≪≫ eUone
  have hRank : 2 * p = 2 := by
    simpa using eRank.toLinearEquiv.finrank_eq
  have hpone : p = 1 := by omega
  subst p
  obtain ⟨eTorus⟩ := actual_one_handle_one_boundary_model_punctured_product_torus
  exact ⟨eU.trans eTorus⟩

end CurveComplex.Hyperbolic
