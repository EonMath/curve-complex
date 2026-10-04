import CurveComplexGenusTwo.Topology.ActualPointMittagLeffler.ActualChartTestScalarExtensionV2
open TopologicalSpace SameAtlasAnalyticCohomology
open scoped Manifold ContDiff Bundle Distributions Topology
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace CanonicalDimensionTwo
universe u
/-- Literal extension of phi d(bar z_a), expressed in every preferred chart
by the fixed barred inverse-derivative formula, with explicit Hausdorffness. -/
noncomputable def actualChartTestFormExtension
    {E : Type u} [TopologicalSpace E] [T2Space E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] (a : E) :
    TestFunction (actualChartTestOpen a) ℂ ⊤ →ₗ[ℂ] SmoothZeroOne E where
  toFun φ := by
    classical
    exact ⟨fun b x => if x ∈ (extChartAt 𝓘(ℂ) a).source ∧
      x ∈ (extChartAt 𝓘(ℂ) b).source
      then φ ((extChartAt 𝓘(ℂ) a) x) / star (chartTransitionDerivative a b x)
      else 0, by
      refine ⟨?_, ?_, ?_⟩
      · intro b x hx
        dsimp only
        split_ifs with h
        · exact (hx h.2).elim
        · rfl
      · intro b z hz
        let ca := extChartAt 𝓘(ℂ) a
        let cb := extChartAt 𝓘(ℂ) b
        have hcont := continuousAt_extChartAt_symm'' (I := 𝓘(ℂ)) hz
        have hbt : cb.target ∈ 𝓝 z := (isOpen_extChartAt_target b).mem_nhds hz
        by_cases ha : cb.symm z ∈ ca.source
        · have ht : ContDiffAt ℂ ∞ (ca ∘ cb.symm) z := by
            have ht := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) (n := ∞) a b
              (show z ∈ (cb.symm ≫ ca).source from ⟨hz, ha⟩)
            simpa [ca, cb, contDiffWithinAt_univ] using ht
          have hrev : ContDiffAt ℂ ∞ (cb ∘ ca.symm) (ca (cb.symm z)) := by
            have hb : cb.symm z ∈ cb.source := cb.map_target hz
            have hh : ca.symm (ca (cb.symm z)) ∈ cb.source := by
              simpa only [ca.left_inv ha] using hb
            have ht := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) (n := ∞) b a
              (show ca (cb.symm z) ∈ (ca.symm ≫ cb).source from ⟨ca.map_source ha, hh⟩)
            simpa [ca, cb, contDiffWithinAt_univ] using ht
          have hq : ContDiffAt ℂ ∞
              (fun w => chartTransitionDerivative a b (cb.symm w)) z := by
            have hd : ContDiffAt ℂ ∞ (fun w => (fderiv ℂ (cb ∘ ca.symm) w) (1 : ℂ))
                (ca (cb.symm z)) :=
              (hrev.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
            exact hd.comp z ht
          have hstar : ContDiffAt ℝ ∞
              (fun w => star (chartTransitionDerivative a b (cb.symm w))) z := by
            exact Complex.conjCLE.contDiff.contDiffAt.comp z (hq.restrict_scalars ℝ)
          have hφ : ContDiffAt ℝ ∞ (fun w => φ (ca (cb.symm w))) z :=
            φ.contDiff.contDiffAt.comp z (ht.restrict_scalars ℝ)
          have hf : ContDiffAt ℝ ∞
              (fun w => φ (ca (cb.symm w)) / star (chartTransitionDerivative a b (cb.symm w))) z := by
            simpa only [div_eq_mul_inv] using! hφ.mul (hstar.fun_inv
              (star_ne_zero.mpr (chartTransitionDerivative_ne_zero a b _ ha (cb.map_target hz))))
          have he : (fun w => if cb.symm w ∈ ca.source ∧ cb.symm w ∈ cb.source
                then φ (ca (cb.symm w)) / star (chartTransitionDerivative a b (cb.symm w))
                else 0) =ᶠ[𝓝 z]
              (fun w => φ (ca (cb.symm w)) / star (chartTransitionDerivative a b (cb.symm w))) := by
            filter_upwards [hbt, hcont.preimage_mem_nhds (extChartAt_source_mem_nhds' ha)] with w hw hwa
            exact ite_eq_left ⟨hwa, cb.map_target hw⟩
          exact (hf.congr_of_eventuallyEq he).contDiffWithinAt
        · have hK : IsCompact (ca.symm '' tsupport (φ : ℂ → ℂ)) :=
            φ.hasCompactSupport.image_of_continuousOn
              ((continuousOn_extChartAt_symm a).mono φ.tsupport_subset)
          have hk : cb.symm z ∉ ca.symm '' tsupport (φ : ℂ → ℂ) := by
            rintro ⟨w, hw, he⟩
            apply ha
            rw [← he]
            exact ca.map_target (φ.tsupport_subset hw)
          have hn := hcont.preimage_mem_nhds (hK.isClosed.isOpen_compl.mem_nhds hk)
          have he : (fun w => if cb.symm w ∈ ca.source ∧ cb.symm w ∈ cb.source
                then φ (ca (cb.symm w)) / star (chartTransitionDerivative a b (cb.symm w))
                else 0) =ᶠ[𝓝 z] fun _ => 0 := by
            filter_upwards [hn] with w hw
            split_ifs with hh
            · have hv : φ (ca (cb.symm w)) = 0 := by
                by_contra hv
                exact hw ⟨ca (cb.symm w), subset_tsupport (φ : ℂ → ℂ) hv, ca.left_inv hh.1⟩
              rw [hv, zero_div]
            · rfl
          exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt
      · intro b c x hb hc
        by_cases ha : x ∈ (extChartAt 𝓘(ℂ) a).source
        · simp only [ha, hb, hc, and_self, ite_true]
          have hq (d e : E) : tangentCoordChange 𝓘(ℂ) d e x 1 =
              chartTransitionDerivative d e x := by
            simp only [tangentCoordChange_def, chartTransitionDerivative, mfld_simps,
              fderivWithin_univ]
          have hcomp := tangentCoordChange_comp (I := 𝓘(ℂ))
            (w := a) (x := b) (y := c) (z := x) (v := (1 : ℂ)) ⟨⟨ha, hb⟩, hc⟩
          rw [hq, hq] at hcomp
          have hlin : tangentCoordChange 𝓘(ℂ) b c x (chartTransitionDerivative a b x) =
              chartTransitionDerivative a b x * chartTransitionDerivative b c x := by
            calc
              _ = tangentCoordChange 𝓘(ℂ) b c x (chartTransitionDerivative a b x • (1 : ℂ)) := by
                rw [smul_eq_mul, mul_one]
              _ = chartTransitionDerivative a b x • tangentCoordChange 𝓘(ℂ) b c x 1 :=
                (tangentCoordChange 𝓘(ℂ) b c x).map_smul _ _
              _ = _ := by rw [hq, smul_eq_mul]
          rw [hlin] at hcomp
          rw [← hcomp, star_mul]
          simp only [div_div, mul_comm]
        · simp only [ha, false_and, ite_false, zero_div]⟩
  map_add' := by
    classical
    intro φ ψ
    apply Subtype.ext
    funext b x
    dsimp only
    change (if _ then (φ + ψ) _ / _ else 0) =
      (if _ then φ _ / _ else 0) + (if _ then ψ _ / _ else 0)
    split_ifs
    · change (φ _ + ψ _) / _ = φ _ / _ + ψ _ / _
      exact add_div _ _ _
    · exact (add_zero 0).symm
  map_smul' := by
    classical
    intro r φ
    apply Subtype.ext
    funext b x
    dsimp only
    change (if _ then (r • φ) _ / _ else 0) = r • (if _ then φ _ / _ else 0)
    split_ifs
    · change (r * φ _) / _ = r * (φ _ / _)
      exact mul_div_assoc _ _ _
    · exact (smul_zero r).symm

end CanonicalDimensionTwo
