import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Separation.Regular
import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualLocalTangentPerturbation
import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualSameAtlasRealSmooth

open scoped Manifold ContDiff
open Set Topology

theorem actual_same_atlas_plateau_bump_on_compact_core
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ChartedSpace ℂ E]
    [CurveComplex.ClosedSurface E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (p : E) (K : Set E) (hK : IsCompact K)
    (hchart : K ⊆ (chartAt ℂ p).source) :
    ∃ (V : Set E) (b : E → ℝ),
      IsOpen V ∧ K ⊆ V ∧ closure V ⊆ (chartAt ℂ p).source ∧
      ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ b ∧
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧
      tsupport b ⊆ (chartAt ℂ p).source ∧
      ∀ x ∈ V, b x = 1 := by
  obtain ⟨V, hVopen, hKV, hVchart⟩ :=
    normal_exists_closure_subset hK.isClosed (chartAt ℂ p).open_source hchart
  obtain ⟨W, hWopen, hVW, hWchart⟩ :=
    normal_exists_closure_subset isClosed_closure (chartAt ℂ p).open_source hVchart
  obtain ⟨b, hb, hrange, hs, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := 𝓘(ℝ,ℂ)) hWopen isClosed_closure hVW
  refine ⟨V, b, hVopen, hKV, hVchart, hb, ?_, ?_, ?_⟩
  · intro x
    exact hrange ⟨x, rfl⟩
  · change closure (Function.support b) ⊆ (chartAt ℂ p).source
    rw [hs]
    exact hWchart
  intro x hx
  exact (hone x).mp (subset_closure hx)

#print axioms actual_same_atlas_plateau_bump_on_compact_core

theorem actual_same_atlas_finite_plateau_cover
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A;
    letI : IsManifold 𝓘(ℝ,ℂ) ∞ E := actual_same_atlas_complex_is_real_smooth E hA;
    ∃ (ι : Type) (f : SmoothBumpCovering ι 𝓘(ℝ,ℂ) E Set.univ),
      Finite ι ∧
      ∃ (U : ι → Set E) (b : ι → E → ℝ),
        (∀ i, IsOpen (U i)) ∧
        (∀ i, {x : E | f i x = 1} ⊆ U i) ∧
        (∀ i, closure (U i) ⊆ (chartAt ℂ (f.c i)).source) ∧
        (∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ (b i)) ∧
        (∀ i x, 0 ≤ b i x ∧ b i x ≤ 1) ∧
        (∀ i, tsupport (b i) ⊆ (chartAt ℂ (f.c i)).source) ∧
        (∀ i, ∀ x ∈ U i, b i x = 1) ∧
        (∀ x : E, ∃ i, x ∈ U i) := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℝ,ℂ) ∞ E := actual_same_atlas_complex_is_real_smooth E hA
  letI : CurveComplex.ClosedSurface E := Classical.choice hg.2.1
  obtain ⟨ι, f, hfinite, hcompact, hsource, hcover⟩ :=
    actual_same_atlas_finite_compact_bump_cores E hg A hA
  have hplateau : ∀ i : ι, ∃ (U : Set E) (b : E → ℝ),
      IsOpen U ∧ {x : E | f i x = 1} ⊆ U ∧
      closure U ⊆ (chartAt ℂ (f.c i)).source ∧
      ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ b ∧
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧
      tsupport b ⊆ (chartAt ℂ (f.c i)).source ∧
      ∀ x ∈ U, b x = 1 := by
    intro i
    exact actual_same_atlas_plateau_bump_on_compact_core E (f.c i)
      {x : E | f i x = 1} (hcompact i) (hsource i)
  choose U b hUopen hcore hclosure hb hbounds hsupport hone using hplateau
  refine ⟨ι, f, hfinite, U, b, hUopen, hcore, hclosure, hb, hbounds,
    hsupport, hone, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact ⟨i, hcore i hi⟩

#print axioms actual_same_atlas_finite_plateau_cover
