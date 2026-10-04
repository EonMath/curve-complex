import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseReferenceZeroSet
import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualComplexSmoothMorseParity
import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualSameAtlasMorseCoordinatesComplete
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualRealTangentTransitionCoefficient
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualRealTangentTransitionDifferentiable
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.Module.Equiv.Basic
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualRealTangentTransitionEventually
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

open scoped Manifold ContDiff Bundle
open Bundle Set Filter Topology InnerProductSpace

/-! Internal proof search for the literal finite weighted gradient field.
The source-facing field/sign head will remain review-only until approved.
All charts and trivializations use the installed, original ChartedSpace. -/

private theorem chart_gradient_adjoint_transport
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (p q x : E) (hp : x ∈ (chartAt ℂ p).source)
    (hq : x ∈ (chartAt ℂ q).source)
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F) :
    gradient (fun z => F ((chartAt ℂ p).symm z)) ((chartAt ℂ p) x) =
      ContinuousLinearMap.adjoint
        (((trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) p).coordChangeL ℝ
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q) x) : ℂ →L[ℝ] ℂ)
        (gradient (fun z => F ((chartAt ℂ q).symm z)) ((chartAt ℂ q) x)) := by
  let ep := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) p
  let eq := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  have hpb : x ∈ ep.baseSet := by simpa [ep] using hp
  have hqb : x ∈ eq.baseSet := by simpa [eq] using hq
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  change ⟪gradient (fun z => F ((chartAt ℂ p).symm z)) ((chartAt ℂ p) x), v⟫_ℝ =
    ⟪gradient (fun z => F ((chartAt ℂ q).symm z)) ((chartAt ℂ q) x),
      (ep.coordChangeL ℝ eq x) v⟫_ℝ
  change ((toDual ℝ ℂ)
    (gradient (fun z => F ((chartAt ℂ p).symm z)) ((chartAt ℂ p) x))) v =
    ((toDual ℝ ℂ)
      (gradient (fun z => F ((chartAt ℂ q).symm z)) ((chartAt ℂ q) x)))
      ((ep.coordChangeL ℝ eq x) v)
  rw [toDual_gradient, toDual_gradient]
  have hi := actual_chart_tangent_scalar_derivative_identity p x hp F hF v
  have hj := actual_chart_tangent_scalar_derivative_identity q x hq F hF
    ((ep.coordChangeL ℝ eq x) v)
  have ht : eq.symmL ℝ x ((ep.coordChangeL ℝ eq x) v) = ep.symmL ℝ x v := by
    rw [ep.coordChangeL_apply eq ⟨hpb, hqb⟩]
    rw [← ep.symmL_apply (R := ℝ) hpb]
    rw [← eq.continuousLinearMapAt_apply_of_mem (R := ℝ) hqb,
      eq.symmL_continuousLinearMapAt hqb]
  rw [ht] at hj
  exact hi.symm.trans hj

private theorem literal_clm_det (T : ℂ →L[ℝ] ℂ) :
    T.det = (T 1).re * (T Complex.I).im - (T Complex.I).re * (T 1).im := by
  have hm : T.toLinearMap.toMatrix Complex.basisOneI Complex.basisOneI =
      !![(T 1).re, (T Complex.I).re; (T 1).im, (T Complex.I).im] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]
  change T.toLinearMap.det = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, hm, Matrix.det_fin_two_of]

private theorem positive_symmetric_complex_operator_det_pos
    (M : ℂ →L[ℝ] ℂ) (hs : M.toLinearMap.IsSymmetric)
    (hp : ∀ v : ℂ, v ≠ 0 → 0 < ⟪M v, v⟫_ℝ) : 0 < M.det := by
  have ha := hp 1 one_ne_zero
  have hsym := hs (1 : ℂ) Complex.I
  have hab : (M 1).im = (M Complex.I).re := by
    simpa [Complex.inner] using hsym
  have ha' : 0 < (M 1).re := by simpa [Complex.inner] using ha
  let v : ℂ := -(M 1).im • (1 : ℂ) + (M 1).re • Complex.I
  have hv : v ≠ 0 := by
    intro hz
    have hi := congrArg Complex.im hz
    simp [v] at hi
    linarith
  have ht := hp v hv
  have hm : M v = -(M 1).im • M 1 + (M 1).re • M Complex.I := by
    simp only [v, map_add, map_smul]
  have hh : ⟪M v, v⟫_ℝ =
      (M 1).re * ((M 1).re * (M Complex.I).im - (M Complex.I).re * (M 1).im) := by
    rw [hm]
    simp only [v, Complex.inner, Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      smul_eq_mul, Complex.conj_re, Complex.conj_im, mul_one, mul_zero, zero_add,
      add_zero, Complex.mul_re]
    rw [hab]
    ring
  rw [hh] at ht
  rw [literal_clm_det]
  exact (mul_pos_iff_of_pos_left ha').mp ht

private theorem weighted_gram_operator_det_pos
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (L : ι → ℂ ≃L[ℝ] ℂ)
    (hb : ∀ i, 0 ≤ b i) (hpositive : ∃ i, 0 < b i) :
    0 < (∑ i, b i • (L i).toContinuousLinearMap.comp
      (ContinuousLinearMap.adjoint (L i).toContinuousLinearMap)).det := by
  let M : ℂ →L[ℝ] ℂ := ∑ i, b i • (L i).toContinuousLinearMap.comp
    (ContinuousLinearMap.adjoint (L i).toContinuousLinearMap)
  have hm (v w : ℂ) : ⟪M v, w⟫_ℝ =
      ∑ i, b i * ⟪ContinuousLinearMap.adjoint (L i).toContinuousLinearMap v,
        ContinuousLinearMap.adjoint (L i).toContinuousLinearMap w⟫_ℝ := by
    simp only [M, ContinuousLinearMap.sum_apply, sum_inner, ContinuousLinearMap.smul_apply,
      inner_smul_left, starRingEnd_apply, star_trivial, ContinuousLinearMap.comp_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [← ContinuousLinearMap.adjoint_inner_right]
  apply positive_symmetric_complex_operator_det_pos M
  · intro v w
    change ⟪M v, w⟫_ℝ = ⟪v, M w⟫_ℝ
    calc
      _ = ∑ i, b i * ⟪ContinuousLinearMap.adjoint (L i).toContinuousLinearMap v,
        ContinuousLinearMap.adjoint (L i).toContinuousLinearMap w⟫_ℝ := hm v w
      _ = ∑ i, b i * ⟪ContinuousLinearMap.adjoint (L i).toContinuousLinearMap w,
        ContinuousLinearMap.adjoint (L i).toContinuousLinearMap v⟫_ℝ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [real_inner_comm]
      _ = ⟪M w, v⟫_ℝ := (hm w v).symm
      _ = _ := real_inner_comm _ _
  · intro v hv
    rw [hm]
    obtain ⟨i, hi⟩ := hpositive
    have hn : ContinuousLinearMap.adjoint (L i).toContinuousLinearMap v ≠ 0 := by
      intro hz
      have hh := ContinuousLinearMap.adjoint_inner_left
        (L i).toContinuousLinearMap ((L i).symm v) v
      rw [hz, inner_zero_left] at hh
      have hnorm : ‖v‖ ^ 2 = 0 := by simpa only [ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply, real_inner_self_eq_norm_sq] using hh.symm
      exact hv (norm_eq_zero.mp (by nlinarith [norm_nonneg v]))
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hb j) (real_inner_self_nonneg)
    · exact ⟨i, Finset.mem_univ i, mul_pos hi (real_inner_self_pos.mpr hn)⟩


private theorem actual_weighted_gradient_coefficient_gram
    {E ι : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [Fintype ι]
    (p : ι → E) (b : ι → E → ℝ)
    (hs : ∀ i, tsupport (b i) ⊆ (chartAt ℂ (p i)).source)
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (r x : E) (hx : x ∈ (chartAt ℂ r).source) :
    let er := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r;
    let L := fun i =>
      ((trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (p i)).coordChangeL
        ℝ er x).toContinuousLinearMap;
    (er (TotalSpace.mk' ℂ x
      (∑ i, b i x •
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (p i)).symmL ℝ x
          (gradient (fun z => F ((chartAt ℂ (p i)).symm z))
            ((chartAt ℂ (p i)) x))))).2 =
      (∑ i, b i x • (L i).comp (ContinuousLinearMap.adjoint (L i)))
        (gradient (fun z => F ((chartAt ℂ r).symm z)) ((chartAt ℂ r) x)) := by
  dsimp only
  let er := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r
  have hr : x ∈ er.baseSet := by simpa [er] using hx
  rw [← er.continuousLinearMapAt_apply_of_mem (R := ℝ) hr]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hbi : b i x = 0
  · simp only [hbi, zero_smul]
  have hi : x ∈ (chartAt ℂ (p i)).source := hs i (subset_tsupport (b i) hbi)
  let ei := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (p i)
  have hib : x ∈ ei.baseSet := by simpa [ei] using hi
  have hchange (v : ℂ) : er.continuousLinearMapAt ℝ x (ei.symmL ℝ x v) =
      (ei.coordChangeL ℝ er x) v := by
    rw [ei.coordChangeL_apply er ⟨hib, hr⟩, ← ei.symmL_apply (R := ℝ) hib,
      ← er.continuousLinearMapAt_apply_of_mem (R := ℝ) hr]
  rw [hchange]
  rw [chart_gradient_adjoint_transport (p i) r x hi hx F hF]
  rfl


private theorem chart_pullback_contDiffAt
    {E H : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (r x : E) (hx : x ∈ (chartAt ℂ r).source)
    (f : E → H) (hf : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,H) ∞ f x) :
    ContDiffAt ℝ ∞ (fun z => f ((chartAt ℂ r).symm z)) ((chartAt ℂ r) x) := by
  let c := chartAt ℂ r
  have hct := c.map_source hx
  have hsymm : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c.symm (c x) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ,ℂ)) (x := r) (n := ∞)
      (c x) hct).contMDiffAt (c.open_target.mem_nhds hct)
  have hf' : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,H) ∞ f (c.symm (c x)) := by
    simpa only [c.left_inv hx] using hf
  exact (hf'.comp (c x) hsymm).contDiffAt

private theorem chart_weighted_gram_term_differentiable
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (r p q : E) (hq : q ∈ (chartAt ℂ r).source)
    (b : E → ℝ) (hb : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ b)
    (hs : tsupport b ⊆ (chartAt ℂ p).source) :
    let er := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r;
    let ep := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) p;
    let L := fun z => (ep.coordChangeL ℝ er ((chartAt ℂ r).symm z)).toContinuousLinearMap;
    DifferentiableAt ℝ (fun z => b ((chartAt ℂ r).symm z) •
      (L z).comp (ContinuousLinearMap.adjoint (L z))) ((chartAt ℂ r) q) := by
  dsimp only
  let c := chartAt ℂ r
  let er := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r
  let ep := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) p
  let L : ℂ → ℂ →L[ℝ] ℂ := fun z => ep.coordChangeL ℝ er (c.symm z)
  by_cases hp : q ∈ (chartAt ℂ p).source
  · have hqb : q ∈ er.baseSet := by simpa [er] using hq
    have hpb : q ∈ ep.baseSet := by simpa [ep] using hp
    have hLAt : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ →L[ℝ] ℂ) ∞
        (fun x => (ep.coordChangeL ℝ er x : ℂ →L[ℝ] ℂ)) q :=
      contMDiffAt_coordChangeL hpb hqb
    have hL : DifferentiableAt ℝ L (c q) :=
      (chart_pullback_contDiffAt r q hq _ hLAt).differentiableAt (by simp)
    let ad : (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
      { toFun := ContinuousLinearMap.adjoint
        map_add' := by intro T S; exact map_add ContinuousLinearMap.adjoint T S
        map_smul' := by intro a T; simpa using map_smulₛₗ ContinuousLinearMap.adjoint a T
        cont := ContinuousLinearMap.adjoint.continuous }
    have hAdj : DifferentiableAt ℝ (fun z => ContinuousLinearMap.adjoint (L z)) (c q) :=
      ad.differentiableAt.comp (c q) hL
    have hbAt : DifferentiableAt ℝ (fun z => b (c.symm z)) (c q) :=
      (chart_pullback_contDiffAt r q hq b hb.contMDiffAt).differentiableAt (by simp)
    exact hbAt.smul (hL.clm_comp hAdj)
  · have hqt : c q ∈ c.target := c.map_source hq
    have hc : ContinuousAt c.symm (c q) := c.symm.continuousAt hqt
    have hqs : q ∉ tsupport b := fun h => hp (hs h)
    have hn : (tsupport b)ᶜ ∈ 𝓝 q := (isClosed_tsupport b).isOpen_compl.mem_nhds hqs
    have hraw : ∀ᶠ z in 𝓝 (c q), c.symm z ∉ tsupport b := by
      have hn' : (tsupport b)ᶜ ∈ 𝓝 (c.symm (c q)) := by
        simpa only [c.left_inv hq] using hn
      exact hc.preimage_mem_nhds hn'
    have heq : (fun z => b (c.symm z) •
        (L z).comp (ContinuousLinearMap.adjoint (L z))) =ᶠ[𝓝 (c q)] fun _ => 0 := by
      filter_upwards [hraw] with z hz
      have hbz : b (c.symm z) = 0 := by
        by_contra h
        exact hz (subset_tsupport b h)
      simp only [hbz, zero_smul]
    exact (differentiableAt_const 0).congr_of_eventuallyEq heq


private theorem actual_weighted_gradient_raw_has_derivative
    {E ι : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [Fintype ι]
    (p : ι → E) (b : ι → E → ℝ)
    (hb : ∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ (b i))
    (hs : ∀ i, tsupport (b i) ⊆ (chartAt ℂ (p i)).source)
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (r q : E) (hq : q ∈ (chartAt ℂ r).source)
    (hcritical : gradient (fun z => F ((chartAt ℂ r).symm z)) ((chartAt ℂ r) q) = 0) :
    let W : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x := fun x =>
      ∑ i, b i x •
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (p i)).symmL ℝ x
          (gradient (fun z => F ((chartAt ℂ (p i)).symm z)) ((chartAt ℂ (p i)) x));
    let er := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r;
    let L := fun i =>
      ((trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (p i)).coordChangeL
        ℝ er q).toContinuousLinearMap;
    HasFDerivAt
      (fun z => (er (TotalSpace.mk' ℂ ((chartAt ℂ r).symm z)
        (W ((chartAt ℂ r).symm z)))).2)
      ((∑ i, b i q • (L i).comp (ContinuousLinearMap.adjoint (L i))).comp
        (fderiv ℝ (gradient (fun z => F ((chartAt ℂ r).symm z))) ((chartAt ℂ r) q)))
      ((chartAt ℂ r) q) := by
  classical
  dsimp only
  let c := chartAt ℂ r
  let er := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r
  let L : ι → ℂ → ℂ →L[ℝ] ℂ := fun i z =>
    (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (p i)).coordChangeL ℝ er
      (c.symm z)
  let M : ℂ → ℂ →L[ℝ] ℂ := fun z =>
    ∑ i, b i (c.symm z) • (L i z).comp (ContinuousLinearMap.adjoint (L i z))
  let G : ℂ → ℂ := gradient (fun z => F (c.symm z))
  have hct := c.map_source hq
  have hM : DifferentiableAt ℝ M (c q) := DifferentiableAt.fun_sum
    (fun i _ => chart_weighted_gram_term_differentiable r (p i) q hq (b i) (hb i) (hs i))
  have hG : DifferentiableAt ℝ G (c q) :=
    (((actual_smooth_scalar_chart_gradient_contDiffOn_infty r F hF)
      (c q) hct).contDiffAt (c.open_target.mem_nhds hct)).differentiableAt (by simp)
  have hd := hM.hasFDerivAt.clm_apply hG.hasFDerivAt
  have hG0 : G (c q) = 0 := hcritical
  have hflip : (fderiv ℝ M (c q)).flip (G (c q)) = 0 := by
    rw [hG0]
    ext w
    simp
  rw [hflip, add_zero] at hd
  have heq : (fun z =>
      (er (TotalSpace.mk' ℂ (c.symm z)
        (∑ i, b i (c.symm z) •
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (p i)).symmL ℝ (c.symm z)
            (gradient (fun w => F ((chartAt ℂ (p i)).symm w))
              ((chartAt ℂ (p i)) (c.symm z)))))).2) =ᶠ[𝓝 (c q)]
      fun z => M z (G z) := by
    filter_upwards [c.open_target.mem_nhds hct] with z hz
    have hcxs := c.map_target hz
    have hg := actual_weighted_gradient_coefficient_gram p b hs F hF r (c.symm z) hcxs
    simpa only [c.right_inv hz, M, G, L, c, er] using hg
  have hresult := hd.congr_of_eventuallyEq heq
  simpa only [M, G, L, c, er, (chartAt ℂ r).left_inv hq] using hresult


private theorem actual_tangent_transition_is_centered_chart_derivative
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q r : E) (hqr : q ∈ (chartAt ℂ r).source) :
    let eq := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q;
    let er := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r;
    HasFDerivAt
      (fun w : ℂ => (chartAt ℂ r) ((chartAt ℂ q).symm ((chartAt ℂ q) q + w)) -
        (chartAt ℂ r) q)
      (eq.coordChangeL ℝ er q).toContinuousLinearMap 0 := by
  dsimp only
  let cq := chartAt ℂ q
  let cr := chartAt ℂ r
  let eq := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  let er := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r
  have hchart : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ cr q :=
    (contMDiffOn_chart (I := 𝓘(ℝ,ℂ)) (x := r) (n := ∞) q hqr).contMDiffAt
      (cr.open_source.mem_nhds hqr)
  have hraw : DifferentiableAt ℝ (fun z => cr (cq.symm z)) (cq q) :=
    (chart_pullback_contDiffAt q q (mem_chart_source ℂ q) cr hchart).differentiableAt
      (by simp)
  have hEq : (eq.coordChangeL ℝ er q).toContinuousLinearMap =
      fderiv ℝ (fun z => cr (cq.symm z)) (cq q) := by
    ext v
    change ((tangentBundleCore 𝓘(ℝ,ℂ) E).localTriv (achart ℂ q)).coordChangeL ℝ
      ((tangentBundleCore 𝓘(ℝ,ℂ) E).localTriv (achart ℂ r)) q v = _
    rw [VectorBundleCore.localTriv_coordChange_eq]
    · simp only [tangentBundleCore_coordChange_achart, extChartAt,
        OpenPartialHomeomorph.extend, mfld_simps, Function.comp_def, cq, cr,
        fderivWithin_univ]
    · exact ⟨mem_chart_source ℂ q, hqr⟩
  have hshift : HasFDerivAt (fun w : ℂ => cq q + w) (ContinuousLinearMap.id ℝ ℂ) 0 := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) (0 : ℂ)).const_add (cq q)
  have hraw' : HasFDerivAt (fun z => cr (cq.symm z))
      (eq.coordChangeL ℝ er q).toContinuousLinearMap (cq q + (0 : ℂ)) := by
    rw [hEq, add_zero]
    exact hraw.hasFDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
    (hraw'.comp 0 hshift).sub_const (cr q)


private theorem actual_constructed_reference_literal_sign
    {E ι : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [Fintype ι]
    (p : ι → E) (b : ι → E → ℝ)
    (hb : ∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ (b i))
    (hs : ∀ i, tsupport (b i) ⊆ (chartAt ℂ (p i)).source)
    (hnonneg : ∀ i x, 0 ≤ b i x) (hpositive : ∀ x, ∃ i, 0 < b i x)
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (q r : E) (hqr : q ∈ (chartAt ℂ r).source)
    (hcritical : gradient (fun z => F ((chartAt ℂ r).symm z)) ((chartAt ℂ r) q) = 0)
    (k : Fin 3) (e : OpenPartialHomeomorph ℂ ℂ)
    (hform : IsActualComplexSmoothMorseNormalForm
      (fun z => F ((chartAt ℂ r).symm z)) (chartAt ℂ r).target
      ((chartAt ℂ r) q) k e) :
    let W : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x := fun x =>
      ∑ i, b i x •
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (p i)).symmL ℝ x
          (gradient (fun z => F ((chartAt ℂ (p i)).symm z)) ((chartAt ℂ (p i)) x));
    ∃ D : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt
        (fun w : ℂ =>
          let x := (chartAt ℂ q).symm ((chartAt ℂ q) q + w)
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
            (TotalSpace.mk' ℂ x (W x))).2)
        D.toContinuousLinearMap 0 ∧
      (if 0 < (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im
        then (1 : ℤ) else -1) = (-1 : ℤ) ^ k.val := by
  classical
  dsimp only
  let W : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x := fun x =>
    ∑ i, b i x •
      (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (p i)).symmL ℝ x
        (gradient (fun z => F ((chartAt ℂ (p i)).symm z)) ((chartAt ℂ (p i)) x))
  let cq := chartAt ℂ q
  let cr := chartAt ℂ r
  let eq := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  let er := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) r
  let L : ι → ℂ ≃L[ℝ] ℂ := fun i =>
    (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (p i)).coordChangeL ℝ er q
  let M : ℂ →L[ℝ] ℂ := ∑ i, b i q • (L i).toContinuousLinearMap.comp
    (ContinuousLinearMap.adjoint (L i).toContinuousLinearMap)
  let Hess : ℂ →L[ℝ] ℂ := fderiv ℝ (gradient (fun z => F (cr.symm z))) (cr q)
  have hM : 0 < M.det := weighted_gram_operator_det_pos (fun i => b i q) L
    (fun i => hnonneg i q) (hpositive q)
  obtain ⟨he, hh, hparity⟩ := actual_complex_smooth_morse_normal_form_det_parity
    (fun z => F (cr.symm z)) cr.target (cr q) k e hform
  have hHess : Hess.det ≠ 0 := by
    change (fderiv ℝ (gradient (fun z => F (cr.symm z))) (cr q)).det ≠ 0
    rw [hh]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))
      (pow_ne_zero _ he)
  have hMH : (M.comp Hess).det ≠ 0 := by
    change (M.toLinearMap.comp Hess.toLinearMap).det ≠ 0
    rw [LinearMap.det_comp]
    exact mul_ne_zero hM.ne' hHess
  let Dr : ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfDetNeZero (M.comp Hess).toLinearMap hMH).toContinuousLinearEquiv
  have hDr : Dr.toContinuousLinearMap = M.comp Hess := by ext v; simp [Dr]
  let raw : ℂ → ℂ := fun z => (er (TotalSpace.mk' ℂ (cr.symm z) (W (cr.symm z)))).2
  have hraw : HasFDerivAt raw Dr.toContinuousLinearMap (cr q) := by
    rw [hDr]
    exact actual_weighted_gradient_raw_has_derivative p b hb hs F hF r q hqr hcritical
  let Fr : ℂ → ℂ := fun w => raw (cr q + w)
  have hshift : HasFDerivAt (fun w : ℂ => cr q + w) (ContinuousLinearMap.id ℝ ℂ) 0 := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) (0 : ℂ)).const_add (cr q)
  have hFr : HasFDerivAt Fr Dr.toContinuousLinearMap 0 := by
    have hraw' : HasFDerivAt raw Dr.toContinuousLinearMap (cr q + (0 : ℂ)) := by
      simpa only [add_zero] using hraw
    simpa only [Fr, Function.comp_def, ContinuousLinearMap.comp_id] using hraw'.comp 0 hshift
  have hWq : W q = 0 := actual_finite_supported_chart_gradient_field_zero_at_critical
    p b hs F hF r q hqr hcritical
  have hFr0 : Fr 0 = 0 := by
    have hbase : q ∈ er.baseSet := by simpa [er] using hqr
    change (er (TotalSpace.mk' ℂ (cr.symm (cr q + 0))
      (W (cr.symm (cr q + 0))))).2 = 0
    rw [add_zero, cr.left_inv hqr, hWq,
      ← er.continuousLinearMapAt_apply_of_mem (R := ℝ) hbase]
    exact map_zero _
  let H : ℂ ≃L[ℝ] ℂ := eq.coordChangeL ℝ er q
  let A : ℂ → ℂ →L[ℝ] ℂ := fun w =>
    er.coordChangeL ℝ eq (cq.symm (cq q + w))
  let h : ℂ → ℂ := fun w => cr (cq.symm (cq q + w)) - cr q
  have hh : HasFDerivAt h H.toContinuousLinearMap 0 :=
    actual_tangent_transition_is_centered_chart_derivative q r hqr
  have h0 : h 0 = 0 := by simp only [h, add_zero, cq.left_inv (mem_chart_source ℂ q), sub_self]
  have hA : DifferentiableAt ℝ A 0 := actual_real_tangent_transition_differentiable q r hqr
  have hA0 : A 0 = H.symm.toContinuousLinearMap := by
    simp only [A, add_zero, cq.left_inv (mem_chart_source ℂ q)]
    have hbq : q ∈ eq.baseSet := by simpa [eq] using mem_chart_source ℂ q
    have hbr : q ∈ er.baseSet := by simpa [er] using hqr
    rw [← eq.symm_coordChangeL er ⟨hbr, hbq⟩]
  let D : ℂ ≃L[ℝ] ℂ := H.trans (Dr.trans H.symm)
  have hFr' : HasFDerivAt Fr Dr.toContinuousLinearMap (h 0) := by
    rw [h0]
    exact hFr
  have hcomp := hFr'.comp 0 hh
  have hder := hA.hasFDerivAt.clm_apply hcomp
  simp only [Function.comp_apply] at hder
  have hflip : (fderiv ℝ A 0).flip (Fr (h 0)) = 0 := by
    rw [h0, hFr0]
    ext v
    simp
  rw [hflip, add_zero, hA0] at hder
  have heq : (fun w : ℂ =>
      let x := cq.symm (cq q + w)
      (eq (TotalSpace.mk' ℂ x (W x))).2) =ᶠ[𝓝 (0 : ℂ)] fun w => A w (Fr (h w)) :=
    actual_real_tangent_transition_eventually q r hqr W
  have hDder : HasFDerivAt
      (fun w : ℂ => let x := cq.symm (cq q + w)
        (eq (TotalSpace.mk' ℂ x (W x))).2) D.toContinuousLinearMap 0 := by
    convert hder.congr_of_eventuallyEq heq using 1
    ext v
    rfl
  have hdetD : D.toLinearMap.det = Dr.toLinearMap.det := by
    have heqD : D.toLinearMap = H.symm.toLinearMap.comp (Dr.toLinearMap.comp H.toLinearMap) := by
      ext v
      rfl
    rw [heqD]
    exact LinearMap.det_conj Dr.toLinearMap H.symm.toLinearEquiv
  have hdetDr : Dr.toLinearMap.det = M.det * Hess.det := by
    have heqDr : Dr.toLinearMap = M.toLinearMap.comp Hess.toLinearMap := by ext v; simp [Dr]
    rw [heqDr, LinearMap.det_comp]
  refine ⟨D, hDder, ?_⟩
  have hpos : (0 < (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im) ↔
      0 < Hess.det := by
    have hliteral : (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im =
        D.toLinearMap.det := by
      have hdMap : D.toContinuousLinearMap.toLinearMap = D.toLinearMap := by ext v; rfl
      exact (show (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im =
        D.toContinuousLinearMap.det from (literal_clm_det D.toContinuousLinearMap).symm).trans
        (congrArg LinearMap.det hdMap)
    rw [hliteral]
    rw [hdetD, hdetDr]
    exact mul_pos_iff_of_pos_left hM
  simpa only [hpos] using hparity


private theorem actual_same_witness_morse_reference_internal
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
  classical
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  letI : IsManifold 𝓘(ℝ,ℂ) ∞ E := actual_same_atlas_complex_is_real_smooth E hA
  letI : CurveComplex.ClosedSurface E := Classical.choice hg.2.1
  obtain ⟨ι, f, _, U, b, hUopen, hcore, _, hb, hbounds, hsupport, hone, _⟩ :=
    actual_same_atlas_finite_plateau_cover E hg A hA
  letI : Fintype ι := f.fintype
  let K : ι → Set E := fun i => {x : E | f i x = 1}
  have hcompact : ∀ i, IsCompact (K i) :=
    fun i => (isClosed_eq (f i).continuous continuous_const).isCompact
  have hsource : ∀ i, K i ⊆ (chartAt ℂ (f.c i)).source :=
    fun i x hx => f.mem_chartAt_source_of_eq_one hx
  have hcover : ∀ x : E, ∃ i, x ∈ K i :=
    fun x => ⟨f.ind x (Set.mem_univ x), f.apply_ind x (Set.mem_univ x)⟩
  obtain ⟨F, hF, hreg, _⟩ := actual_same_atlas_morse_function_from_plateau_cover
    (fun i => f.c i) K U b hcompact hsource hUopen hcore hb hsupport hone hcover
  let C : Set E := {x | ∃ i, x ∈ K i ∧
    gradient (fun z => F ((chartAt ℂ (f.c i)).symm z))
      ((chartAt ℂ (f.c i)) x) = 0}
  have hC : C.Finite := actual_morse_finite_chart_core_critical_set
    (fun i => f.c i) K hcompact hsource F hF hreg
  let Z : Finset E := hC.toFinset
  let X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x := fun x =>
    ∑ i, b i x •
      (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (f.c i)).symmL ℝ x
        (gradient (fun z => F ((chartAt ℂ (f.c i)).symm z))
          ((chartAt ℂ (f.c i)) x))
  have hpos : ∀ x : E, x ∉ Z →
      0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x)) := by
    intro x hx
    rw [show X x = ∑ i, b i x •
      (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (f.c i)).symmL ℝ x
        (gradient (fun z => F ((chartAt ℂ (f.c i)).symm z))
          ((chartAt ℂ (f.c i)) x)) from rfl]
    rw [actual_finite_chart_gradient_field_energy (fun i => f.c i) b hsupport F hF x]
    obtain ⟨i, hi⟩ := hcover x
    have hbi : b i x = 1 := hone i x (hcore i hi)
    have hgi : gradient (fun z => F ((chartAt ℂ (f.c i)).symm z))
        ((chartAt ℂ (f.c i)) x) ≠ 0 := by
      intro hgzero
      apply hx
      exact hC.mem_toFinset.mpr ⟨i, hi, hgzero⟩
    exact actual_finite_weighted_gradient_energy_positive
      (fun j => b j x)
      (fun j => gradient (fun z => F ((chartAt ℂ (f.c j)).symm z))
        ((chartAt ℂ (f.c j)) x))
      (fun j => (hbounds j x).1) i hbi hgi

  have hX := actual_finite_supported_chart_gradient_field_smooth
    (fun i => f.c i) b hb hsupport F hF
  have hcrit : ∀ x : E, x ∈ Z → ∃ p : E,
      x ∈ (chartAt ℂ p).source ∧
      gradient (fun z => F ((chartAt ℂ p).symm z)) ((chartAt ℂ p) x) = 0 ∧
      (fderiv ℝ (gradient (fun z => F ((chartAt ℂ p).symm z))) ((chartAt ℂ p) x)).det ≠ 0 := by
    intro x hx
    obtain ⟨i, hi, hzero⟩ := hC.mem_toFinset.mp hx
    exact ⟨f.c i, hsource i hi, hzero, hreg i x hi hzero⟩
  have hzero : (Z : Set E) = {x | X x = 0} := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hzero⟩ := hC.mem_toFinset.mp hx
      exact actual_finite_supported_chart_gradient_field_zero_at_critical
        (fun i => f.c i) b hsupport F hF (f.c i) x (hsource i hi) hzero
    · intro hx
      by_contra hnot
      have hp := hpos x hnot
      change X x = 0 at hx
      rw [hx, map_zero, map_zero] at hp
      exact (lt_irrefl (0 : ℝ)) hp
  have hscalar : (Z : Set E) = {x | mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x = 0} :=
    actual_retained_morse_set_eq_scalar_mfderiv_zero F hF Z X
      (fun x hx => by obtain ⟨p, hp, hg, _⟩ := hcrit x hx; exact ⟨p, hp, hg⟩) hpos
  have hpositive : ∀ x : E, ∃ i, 0 < b i x := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨i, by rw [hone i x (hcore i hi)]; norm_num⟩
  have localData (q : Z) : ∃ (k : Fin 3) (c : OpenPartialHomeomorph E ℂ)
      (D : ℂ ≃L[ℝ] ℂ),
      (q.val ∈ c.source ∧ c q.val = 0 ∧
        c ∈ IsManifold.maximalAtlas 𝓘(ℝ,ℂ) ∞ E ∧
        ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c c.source ∧
        ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c.symm c.target ∧
        ∀ x ∈ c.source, F x = F q.val + actualComplexMorseQuadratic k (c x)) ∧
      HasFDerivAt
        (fun w : ℂ =>
          let x := (chartAt ℂ q.val).symm ((chartAt ℂ q.val) q.val + w)
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q.val
            (TotalSpace.mk' ℂ x (X x))).2)
        D.toContinuousLinearMap 0 ∧
      (if 0 < (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im
        then (1 : ℤ) else -1) = (-1 : ℤ) ^ k.val := by
    obtain ⟨r, hqr, hg, hdet⟩ := hcrit q.val q.property
    obtain ⟨k, e, hform, hchart⟩ := actual_same_atlas_smooth_morse_coordinates E A hA
      F hF r q.val hqr hg hdet
    obtain ⟨D, hD, hsign⟩ := actual_constructed_reference_literal_sign
      (fun i => f.c i) b hb hsupport (fun i x => (hbounds i x).1) hpositive
      F hF q.val r hqr hg k e hform
    exact ⟨k, (chartAt ℂ r).trans e, D, hchart, hD, hsign⟩
  choose k c D hchart hD hsign using localData
  exact ⟨F, Z, X, k, c, D, hF, hX, hzero, hscalar, hpos, hchart, hD, hsign⟩

