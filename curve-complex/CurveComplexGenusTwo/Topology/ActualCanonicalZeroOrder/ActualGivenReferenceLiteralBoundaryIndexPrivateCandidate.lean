import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualSameAtlasGenusTwoReferenceVZD
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualLiteralTangentCoefficientSmooth
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.VerifiedRealNondegenerateIndex
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCircleSourceWindingTransport
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualCircleMapWindingHomotopySourceReviewRequest
open Set Metric Topology
open scoped ContDiff
private theorem actual_complex_closed_disc_coefficient_continuous_extension
    (b : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hb : ContinuousOn b (closedBall (0:ℂ) r)) :
    ∃ g : C(ℂ,ℂ), ∀ x ∈ closedBall (0:ℂ) r, g x = b x := by
  let u : C(closedBall (0:ℂ) r,ℝ) :=
    ⟨fun x => (b x.val).re, Complex.continuous_re.comp hb.restrict⟩
  let v : C(closedBall (0:ℂ) r,ℝ) :=
    ⟨fun x => (b x.val).im, Complex.continuous_im.comp hb.restrict⟩
  obtain ⟨U,hU⟩ := u.exists_restrict_eq isClosed_closedBall
  obtain ⟨V,hV⟩ := v.exists_restrict_eq isClosed_closedBall
  let g : C(ℂ,ℂ) := ⟨fun x => (U x:ℂ)+(V x:ℂ)*Complex.I,by fun_prop⟩
  refine ⟨g,?_⟩
  intro x hx
  have hu := congrArg (fun f : C(closedBall (0:ℂ) r,ℝ) => f ⟨x,hx⟩) hU
  have hv := congrArg (fun f : C(closedBall (0:ℂ) r,ℝ) => f ⟨x,hx⟩) hV
  change U x = (b x).re at hu
  change V x = (b x).im at hv
  change (U x:ℂ)+(V x:ℂ)*Complex.I = b x
  rw [hu,hv]
  exact Complex.re_add_im (b x)

private theorem actual_real_smooth_germ_has_global_continuous_literal_extension
    (b : ℂ → ℂ) (hb : ContDiffAt ℝ 1 b 0) :
    ∃ (r : ℝ) (g : C(ℂ,ℂ)), 0 < r ∧
      (∀ x ∈ closedBall (0:ℂ) r, g x = b x) ∧
      (g : ℂ → ℂ) =ᶠ[𝓝 0] b := by
  have hwithin : ContDiffWithinAt ℝ 1 b Set.univ 0 := hb.contDiffWithinAt
  obtain ⟨U,hU,hbU⟩ := (contDiffWithinAt_iff_contDiffOn_nhds (by norm_num : (1:WithTop ℕ∞) ≠ ∞)).mp hwithin
  have hUn : U ∈ 𝓝 (0:ℂ) := by simpa using hU
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp hUn
  let r := ε/2
  have hr : 0 < r := half_pos hε
  have hsub : closedBall (0:ℂ) r ⊆ U := by
    intro x hx
    exact hεU (lt_of_le_of_lt (mem_closedBall.mp hx) (half_lt_self hε))
  obtain ⟨g,hg⟩ := actual_complex_closed_disc_coefficient_continuous_extension b r hr
    (hbU.continuousOn.mono hsub)
  refine ⟨r,g,hr,hg,?_⟩
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr] with x hx
  exact hg x (ball_subset_closedBall hx)

open scoped unitInterval
open Set Topology
set_option backward.isDefEq.respectTransparency false
private noncomputable def actualCircleMapDegree (f : C(Circle,Circle)) : ℤ :=
  Classical.choose (actual_circle_map_winding_homotopy_source f)

open scoped Manifold Bundle
open Bundle
private theorem actual_given_same_atlas_nondegenerate_field_has_literal_boundary_indices
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hV : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (V x)))
    (Z : Finset E) (hZ : (Z : Set E) = {x | V x = 0})
    (D : Z → (ℂ ≃L[ℝ] ℂ))
    (hD : ∀ q : Z, HasFDerivAt
      (fun w : ℂ =>
        let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+w);
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
          (TotalSpace.mk' ℂ x (V x))).2)
      (D q).toContinuousLinearMap 0) :
    ∃ r : Z → ℝ, (∀ q, 0 < r q) ∧
      ∀ q : Z, ∀ ρ : ℝ, 0 < ρ → ρ < r q →
        let b : ℂ → ℂ := fun w =>
          let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+w);
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
            (TotalSpace.mk' ℂ x (V x))).2;
        (∀ z : Circle, b ((ρ:ℂ)*z) ≠ 0) ∧
        ∀ f : C(Circle,Circle),
          (∀ z, (f z:ℂ) = b ((ρ:ℂ)*z)/(‖b ((ρ:ℂ)*z)‖:ℂ)) →
          actualCircleMapDegree f =
            if 0 < (D q 1).re*(D q Complex.I).im -
              (D q Complex.I).re*(D q 1).im then 1 else -1 := by
  classical
  let b (q : Z) : ℂ → ℂ := fun w =>
    let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val+w)
    (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
      (TotalSpace.mk' ℂ x (V x))).2
  have hb0 (q : Z) : b q 0 = 0 := by
    have hz : V q.val = 0 := by
      have hm : q.val ∈ ({x | V x = 0} : Set E) := hZ ▸ q.property
      exact hm
    dsimp only [b]
    rw [add_zero,(chartAt ℂ q.val).left_inv (mem_chart_source ℂ q.val),hz]
    have he := (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val).zeroSection
      ℝ (mem_baseSet_trivializationAt ℂ _ q.val)
    exact congrArg Prod.snd he
  have hmodels (q : Z) : ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      (∀ z : Circle, b q ((ρ:ℂ)*z) ≠ 0) ∧
      ∀ f : C(Circle,Circle),
        (∀ z, (f z:ℂ) = b q ((ρ:ℂ)*z)/(‖b q ((ρ:ℂ)*z)‖:ℂ)) →
        actualCircleMapDegree f =
          if 0 < (D q 1).re*(D q Complex.I).im -
            (D q Complex.I).re*(D q 1).im then 1 else -1 := by
    have hs := actual_literal_tangent_coefficient_smooth V hV q.val
    obtain ⟨ε,g,hε,hg,hge⟩ :=
      actual_real_smooth_germ_has_global_continuous_literal_extension (b q) hs
    have hg0 : g 0 = 0 := (hg 0 (mem_closedBall_self hε.le)).trans (hb0 q)
    have hgd : HasFDerivAt g (D q).toContinuousLinearMap 0 :=
      (hD q).congr_of_eventuallyEq hge
    have hlocal : ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
        (∀ z : Circle, g ((ρ:ℂ)*z) ≠ 0) ∧
        ∀ f : C(Circle,Circle),
          (∀ z, (f z:ℂ) = g ((ρ:ℂ)*z)/(‖g ((ρ:ℂ)*z)‖:ℂ)) →
          actualCircleMapDegree f =
            if 0 < (D q 1).re*(D q Complex.I).im -
              (D q Complex.I).re*(D q 1).im then 1 else -1 := by
      run_tac do
        let n := Lean.Name.str (Lean.Name.num
          (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "VerifiedRealNondegenerateIndex") 0)
          "actual_real_nondegenerate_zero_literal_circle_index"
        Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) _ _ (by assumption) (by assumption)))
    obtain ⟨δ,hδ,hδmodel⟩ := hlocal
    refine ⟨min ε δ,lt_min hε hδ,?_⟩
    intro ρ hρ hρmin
    have heq (z : Circle) : g ((ρ:ℂ)*z) = b q ((ρ:ℂ)*z) := by
      apply hg
      rw [mem_closedBall,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hρ,Circle.norm_coe,mul_one]
      exact (lt_of_lt_of_le hρmin (min_le_left ε δ)).le
    have hm := hδmodel ρ hρ (lt_of_lt_of_le hρmin (min_le_right ε δ))
    simpa only [heq] using hm
  choose r hr hmodel using hmodels
  exact ⟨r,hr,hmodel⟩
