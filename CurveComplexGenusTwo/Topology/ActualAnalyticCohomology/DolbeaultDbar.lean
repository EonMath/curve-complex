import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.ChartFrameTransition
import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.SmoothJetTopology
import Mathlib.Analysis.Calculus.ContDiff.Operations
open TopologicalSpace
open scoped Manifold ContDiff Bundle Topology
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000
namespace SameAtlasAnalyticCohomology
universe u v
variable {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]

noncomputable def dolbeaultDbar : SmoothZero E →ₗ[ℂ] SmoothZeroOne E where
  toFun f := by
    classical
    exact ⟨fun a x => if x ∈ (extChartAt 𝓘(ℂ) a).source
      then chartDbar a f.1 x else 0, by
      refine ⟨?_, ?_, ?_⟩
      · intro a x hx
        simp only [ite_eq_right hx]
      · intro a
        let F : ℂ → ℂ := fun z => f.1 ((extChartAt 𝓘(ℂ) a).symm z)
        have hd : ContDiffOn ℝ ∞ (fderiv ℝ F) (extChartAt 𝓘(ℂ) a).target :=
          (f.property a).fderiv_of_isOpen (isOpen_extChartAt_target a) (by simp)
        have h1 := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
        have hI := hd.clm_apply (contDiffOn_const (c := Complex.I))
        have hs : ContDiffOn ℝ ∞
            (fun z => ((fderiv ℝ F z) 1 + Complex.I * (fderiv ℝ F z) Complex.I) / 2)
            (extChartAt 𝓘(ℂ) a).target := by
          simpa [smul_eq_mul] using (h1.add (hI.const_smul Complex.I)).div_const (2 : ℂ)
        apply hs.congr
        intro z hz
        simp only [ite_eq_left ((extChartAt 𝓘(ℂ) a).map_target hz), chartDbar,
          (extChartAt 𝓘(ℂ) a).right_inv hz, F]
      · intro a b x ha hb
        simp only [ite_eq_left ha, ite_eq_left hb]
        apply chartDbar_transition a b x f.1 ha hb
        exact ((f.property a).contDiffAt (extChartAt_target_mem_nhds' ((extChartAt 𝓘(ℂ) a).map_source ha))).of_le
          (by simp)⟩
  map_add' := by
    classical
    intro f g
    apply Subtype.ext
    funext a x
    by_cases hx : x ∈ (extChartAt 𝓘(ℂ) a).source
    · have hf := ((f.property a).contDiffAt (extChartAt_target_mem_nhds' ((extChartAt 𝓘(ℂ) a).map_source hx))).differentiableAt
        (by simp)
      have hg := ((g.property a).contDiffAt (extChartAt_target_mem_nhds' ((extChartAt 𝓘(ℂ) a).map_source hx))).differentiableAt
        (by simp)
      simp only [ite_eq_left hx, Submodule.coe_add, Pi.add_apply, chartDbar,
        fderiv_fun_add hf hg, add_apply]
      ring
    · simp only [ite_eq_right hx, Submodule.coe_add, Pi.add_apply, zero_add]
  map_smul' := by
    classical
    intro c f
    apply Subtype.ext
    funext a x
    by_cases hx : x ∈ (extChartAt 𝓘(ℂ) a).source
    · have hf := ((f.property a).contDiffAt (extChartAt_target_mem_nhds' ((extChartAt 𝓘(ℂ) a).map_source hx))).differentiableAt
        (by simp)
      simp only [ite_eq_left hx, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
      change chartDbar a (fun y => c • f.1 y) x = c • chartDbar a f.1 x
      unfold chartDbar
      dsimp only
      rw [fderiv_fun_const_smul (c := c) hf]
      simp only [smul_apply, smul_eq_mul]
      ring
    · simp only [ite_eq_right hx, Submodule.coe_smul, Pi.smul_apply, smul_zero]


theorem dolbeaultDbar_continuous : Continuous (dolbeaultDbar (E := E)) := by
  let L : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
    (2⁻¹ : ℂ) • (ContinuousLinearMap.apply ℝ ℂ 1 +
      Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I)
  have hL (A : ℂ →L[ℝ] ℂ) : L A = (A 1 + Complex.I * A Complex.I) / 2 := by
    simp only [L, smul_apply, add_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
    ring
  let Q (n : ℕ) : RealJet (n + 1) →L[ℝ] RealJet n :=
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => ℂ)
      (ℂ →L[ℝ] ℂ) ℂ L).comp
      (continuousMultilinearCurryRightEquiv' ℝ n ℂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  have hjet (a : E) (n : ℕ) (f : SmoothZero E) :
      smoothZeroOneJet a n (dolbeaultDbar f) =
        (⟨Q n, (Q n).continuous⟩ : C(RealJet (n + 1), RealJet n)).comp
          (smoothZeroJet a (n + 1) f) := by
    apply ContinuousMap.ext
    intro z
    let F : ℂ → ℂ := fun w => f.1 ((extChartAt 𝓘(ℂ) a).symm w)
    have hd : ContDiffAt ℝ ∞ (fderiv ℝ F) z.1 :=
      ((f.property a).fderiv_of_isOpen (isOpen_extChartAt_target a) (by simp)).contDiffAt
        ((isOpen_extChartAt_target a).mem_nhds z.property)
    have heq : (fun w : ℂ => (dolbeaultDbar f).1 a ((extChartAt 𝓘(ℂ) a).symm w)) =ᶠ[𝓝 z.1]
        (L ∘ fderiv ℝ F) := by
      filter_upwards [(isOpen_extChartAt_target a).mem_nhds z.property] with w hw
      simp only [dolbeaultDbar, LinearMap.coe_mk, AddHom.coe_mk,
        ite_eq_left ((extChartAt 𝓘(ℂ) a).map_target hw), chartDbar,
        (extChartAt 𝓘(ℂ) a).right_inv hw, Function.comp_apply, hL, F]
    change iteratedFDeriv ℝ n
      (fun w : ℂ => (dolbeaultDbar f).1 a ((extChartAt 𝓘(ℂ) a).symm w)) z.1 =
      Q n (iteratedFDeriv ℝ (n + 1) F z.1)
    rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds, L.iteratedFDeriv_comp_left hd (by simp)]
    simp only [Q, ContinuousLinearMap.comp_apply, iteratedFDeriv_succ_eq_comp_right,
      Function.comp_apply, ContinuousLinearMap.compContinuousMultilinearMapL_apply]
    change L.compContinuousMultilinearMap (iteratedFDeriv ℝ n (fderiv ℝ F) z.1) =
      L.compContinuousMultilinearMap
        ((continuousMultilinearCurryRightEquiv' ℝ n ℂ ℂ)
          ((continuousMultilinearCurryRightEquiv' ℝ n ℂ ℂ).symm
            (iteratedFDeriv ℝ n (fderiv ℝ F) z.1)))
    rw [LinearIsometryEquiv.apply_symm_apply]
  change @Continuous (SmoothZero E) (SmoothZeroOne E) _
    (TopologicalSpace.induced
      (fun α => fun (a : E) (n : ℕ) => smoothZeroOneJet a n α) inferInstance)
    (dolbeaultDbar (E := E))
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  apply continuous_pi
  intro n
  have ht : Continuous (fun f : SmoothZero E => fun (a : E) (n : ℕ) => smoothZeroJet a n f) := by
    change @Continuous _ _ (TopologicalSpace.induced
      (fun f : SmoothZero E => fun (a : E) (n : ℕ) => smoothZeroJet a n f) inferInstance) _ _
    exact continuous_induced_dom
  have hi : Continuous (fun f : SmoothZero E => smoothZeroJet a (n + 1) f) :=
    (continuous_apply (n + 1)).comp ((continuous_apply a).comp ht)
  have hc := (ContinuousMap.continuous_postcomp
    (⟨Q n, (Q n).continuous⟩ : C(RealJet (n + 1), RealJet n))).comp hi
  simpa only [Function.comp_def, ← hjet a n] using hc


end SameAtlasAnalyticCohomology
