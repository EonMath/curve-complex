import CurveComplexGenusTwo.Topology.ActualLocalWeyl.ActualHarmonicDistributionRegularityContract
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.CompactlySupported

open scoped ContDiff Distributions BoundedContinuousFunction Topology
open TopologicalSpace MeasureTheory Filter

namespace CanonicalDimensionTwo.LocalDbar.HarmonicProof

private theorem distribution_compact_stage_bound (Ω : Opens ℂ)
    (D : Distribution Ω ℂ ⊤) (K : Compacts ℂ) (hK : (K : Set ℂ) ⊆ Ω) :
    ∃ (s : Finset ℕ) (C : ℝ), 0 < C ∧
      ∀ φ : ContDiffMapSupportedIn ℂ ℝ ⊤ K,
        ‖D (TestFunction.ofSupportedIn hK φ)‖ ≤
          C * s.sup (ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K) φ := by
  let A : ContDiffMapSupportedIn ℂ ℝ ⊤ K →L[ℝ] ℂ :=
    (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℝ) ℂ _).symm D |>.comp
      (TestFunction.ofSupportedInCLM ℝ hK)
  let q : Seminorm ℝ (ContDiffMapSupportedIn ℂ ℝ ⊤ K) :=
    (normSeminorm ℝ ℂ).comp A.toLinearMap
  obtain ⟨s, C, hC, hbound⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ ℂ ℝ ⊤ K) q
    (continuous_norm.comp A.continuous)
  refine ⟨s, C, ?_, ?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC)
  intro φ
  exact hbound φ

#print axioms distribution_compact_stage_bound

private abbrev FiniteJets (N : ℕ) :=
  (i : Fin (N + 1)) → ℂ →ᵇ (ℂ [×(i : ℕ)]→L[ℝ] ℝ)

private noncomputable def finiteJetMap (K : Compacts ℂ) (N : ℕ) :
    ContDiffMapSupportedIn ℂ ℝ ⊤ K →L[ℝ] FiniteJets N :=
  ContinuousLinearMap.pi fun i => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i : ℕ)

private theorem finiteJetMap_injective (K : Compacts ℂ) (N : ℕ) :
    Function.Injective (finiteJetMap K N) := by
  intro φ ψ h
  apply ContDiffMapSupportedIn.structureMapCLM_zero_injective ℝ
  exact congrFun h (0 : Fin (N + 1))

private theorem distribution_finite_jet_bound (Ω : Opens ℂ)
    (D : Distribution Ω ℂ ⊤) (K : Compacts ℂ) (hK : (K : Set ℂ) ⊆ Ω) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ φ : ContDiffMapSupportedIn ℂ ℝ ⊤ K,
        ‖D (TestFunction.ofSupportedIn hK φ)‖ ≤ C * ‖finiteJetMap K N φ‖ := by
  obtain ⟨s, C, hC, hb⟩ := distribution_compact_stage_bound Ω D K hK
  refine ⟨s.sup id, C, hC, ?_⟩
  intro φ
  apply (hb φ).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Seminorm.finset_sup_apply_le (norm_nonneg _)
  intro i hi
  change ‖ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i φ‖ ≤ _
  have hiN : i < s.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  exact norm_le_pi_norm (finiteJetMap K (s.sup id) φ) ⟨i, hiN⟩

private theorem extend_complex_functional {V E : Type*}
    [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : V →ₗ[ℝ] ℂ) (J : V →ₗ[ℝ] E) (hJ : Function.Injective J)
    (C : ℝ) (hb : ∀ v, ‖A v‖ ≤ C * ‖J v‖) :
    ∃ L : E →L[ℝ] ℂ, ∀ v, L (J v) = A v := by
  let e : V ≃ₗ[ℝ] LinearMap.range J := LinearEquiv.ofInjective J hJ
  let A' : LinearMap.range J →ₗ[ℝ] ℂ := A.comp e.symm.toLinearMap
  have hbound (v : LinearMap.range J) : ‖A' v‖ ≤ C * ‖v‖ := by
    have he : J (e.symm v) = (v : E) := congrArg Subtype.val (e.apply_symm_apply v)
    simpa [A', he] using hb (e.symm v)
  let B : LinearMap.range J →L[ℝ] ℂ := A'.mkContinuous C hbound
  obtain ⟨Br, hBr, _⟩ := exists_extension_norm_eq (LinearMap.range J) (Complex.reCLM.comp B)
  obtain ⟨Bi, hBi, _⟩ := exists_extension_norm_eq (LinearMap.range J) (Complex.imCLM.comp B)
  refine ⟨Complex.ofRealCLM.comp Br + Complex.I • Complex.ofRealCLM.comp Bi, ?_⟩
  intro v
  have hr := hBr (e v)
  have hi := hBi (e v)
  have hAv : B (e v) = A v := by simp [B, A']
  have hJv : (e v : E) = J v := rfl
  rw [hJv, ContinuousLinearMap.comp_apply, hAv] at hr hi
  simp only [add_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    smul_apply, smul_eq_mul, hr, hi]
  simpa [mul_comm] using Complex.re_add_im (A v)

#print axioms distribution_finite_jet_bound
#print axioms extend_complex_functional

private theorem distribution_finite_jet_representation (Ω : Opens ℂ)
    (D : Distribution Ω ℂ ⊤) (K : Compacts ℂ) (hK : (K : Set ℂ) ⊆ Ω) :
    ∃ (N : ℕ) (L : FiniteJets N →L[ℝ] ℂ),
      ∀ φ : ContDiffMapSupportedIn ℂ ℝ ⊤ K,
        D (TestFunction.ofSupportedIn hK φ) = L (finiteJetMap K N φ) := by
  obtain ⟨N, C, _, hb⟩ := distribution_finite_jet_bound Ω D K hK
  let A : ContDiffMapSupportedIn ℂ ℝ ⊤ K →L[ℝ] ℂ :=
    (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℝ) ℂ _).symm D |>.comp
      (TestFunction.ofSupportedInCLM ℝ hK)
  have hA (φ : ContDiffMapSupportedIn ℂ ℝ ⊤ K) :
      ‖A φ‖ ≤ C * ‖finiteJetMap K N φ‖ := hb φ
  obtain ⟨L, hL⟩ := extend_complex_functional (E := FiniteJets N) A.toLinearMap
    (finiteJetMap K N).toLinearMap (finiteJetMap_injective K N) C hA
  exact ⟨N, L, fun φ => (hL φ).symm⟩

#print axioms distribution_finite_jet_representation


universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private noncomputable def boundedFlip (g : E →ᵇ (E →L[ℝ] F)) :
    E →L[ℝ] (E →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := fun v => (ContinuousLinearMap.apply ℝ F v).compLeftContinuousBounded E g
      map_add' := by intro v w; ext y; simp
      map_smul' := by intro c v; ext y; simp }
    ‖g‖ (by
      intro v
      change ‖(ContinuousLinearMap.apply ℝ F v).compLeftContinuousBounded E g‖ ≤ ‖g‖ * ‖v‖
      apply BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg g) (norm_nonneg v)) |>.2
      intro y
      exact (g y).le_opNorm_of_le (le_refl ‖v‖) |>.trans
        (mul_le_mul_of_nonneg_right (g.norm_coe_le_norm y) (norm_nonneg v)))

private theorem boundedFlip_apply (g : E →ᵇ (E →L[ℝ] F)) (v y : E) :
    boundedFlip g v y = g y v := rfl

private noncomputable def boundedFlipCLM :
    (E →ᵇ (E →L[ℝ] F)) →L[ℝ] (E →L[ℝ] (E →ᵇ F)) :=
  LinearMap.mkContinuous
    { toFun := boundedFlip
      map_add' := by intro g h; ext v y; simp only [boundedFlip_apply]; rfl
      map_smul' := by intro c g; ext v y; simp only [boundedFlip_apply]; rfl }
    1 (by
      intro g
      rw [one_mul]
      change ‖boundedFlip g‖ ≤ ‖g‖
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
      intro v
      apply BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2
      intro y
      exact (g y).le_opNorm_of_le (le_refl ‖v‖) |>.trans
        (mul_le_mul_of_nonneg_right (g.norm_coe_le_norm y) (norm_nonneg v)))

private noncomputable def boundedTranslate (g : E →ᵇ F) (x : E) : E →ᵇ F :=
  g.compContinuous ⟨fun y => x - y, continuous_const.sub continuous_id⟩



private theorem hasFDerivAt_boundedTranslate
    (g : E →ᵇ F) (g' : E →ᵇ (E →L[ℝ] F))
    (hg : ∀ y, HasFDerivAt g (g' y) y) (huc : UniformContinuous g') (x : E) :
    HasFDerivAt (boundedTranslate g) (boundedFlip (boundedTranslate g' x)) x := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  filter_upwards [Metric.ball_mem_nhds x hδ] with z hz
  apply BoundedContinuousFunction.norm_le (mul_nonneg hε.le (norm_nonneg _)) |>.2
  intro y
  change ‖g (z - y) - g (x - y) - g' (x - y) (z - x)‖ ≤ ε * ‖z - x‖
  have hd (w : E) :
      HasFDerivAt (fun u => g (u - y) - g (x - y) - g' (x - y) (u - x))
        (g' (w - y) - g' (x - y)) w := by
    convert (((hg (w - y)).comp w ((hasFDerivAt_id w).sub_const y)).sub_const
      (g (x - y))).sub ((g' (x - y)).hasFDerivAt.comp w
        ((hasFDerivAt_id w).sub_const x)) using 1 <;> simp [Function.comp_def, Pi.sub_def]
  have hb (w : E) (hw : w ∈ Metric.ball x δ) : ‖g' (w - y) - g' (x - y)‖ ≤ ε := by
    apply le_of_lt
    rw [← dist_eq_norm]
    apply hclose
    simpa [Metric.mem_ball, dist_eq_norm, sub_sub_sub_cancel_right] using hw
  have hm := (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w _ => (hd w).hasFDerivWithinAt) hb (Metric.mem_ball_self hδ) hz
  simpa using hm

#print axioms boundedFlipCLM
#print axioms hasFDerivAt_boundedTranslate

private theorem contDiff_nat_boundedTranslate (n : ℕ) (g : E →ᵇ F)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ContDiff ℝ n (boundedTranslate g) := by
  induction n generalizing F with
  | zero =>
    have hg' : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
    let g' : E →ᵇ (E →L[ℝ] F) :=
      (⟨⟨fderiv ℝ g, hg'.continuous⟩, hc.fderiv (𝕜 := ℝ)⟩ :
        CompactlySupportedContinuousMap E (E →L[ℝ] F)).toBoundedContinuousFunction
    apply contDiff_zero.mpr
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hasFDerivAt_boundedTranslate g g'
      (fun y => (hg.differentiable (by simp) y).hasFDerivAt)
      (hg'.continuous.uniformContinuous_of_tendsto_cocompact
        (hc.fderiv (𝕜 := ℝ)).is_zero_at_infty)
      x).continuousAt
  | succ n ih =>
    have hg' : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
    let g' : E →ᵇ (E →L[ℝ] F) :=
      (⟨⟨fderiv ℝ g, hg'.continuous⟩, hc.fderiv (𝕜 := ℝ)⟩ :
        CompactlySupportedContinuousMap E (E →L[ℝ] F)).toBoundedContinuousFunction
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => boundedFlip (boundedTranslate g' x), ?_, ?_⟩
    · exact (boundedFlipCLM (E := E) (F := F)).contDiff.comp
        (ih g' hg' (hc.fderiv (𝕜 := ℝ)))
    · exact hasFDerivAt_boundedTranslate g g'
        (fun y => (hg.differentiable (by simp) y).hasFDerivAt)
        (hg'.continuous.uniformContinuous_of_tendsto_cocompact
          (hc.fderiv (𝕜 := ℝ)).is_zero_at_infty)

private theorem contDiff_boundedTranslate (g : E →ᵇ F)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ContDiff ℝ ∞ (boundedTranslate g) :=
  contDiff_infty.mpr fun n => contDiff_nat_boundedTranslate n g hg hc

#print axioms contDiff_boundedTranslate

private noncomputable def boundedShift (g : E →ᵇ F) (x : E) : E →ᵇ F :=
  g.compContinuous ⟨fun y => y - x, continuous_id.sub continuous_const⟩



private theorem contDiff_boundedShift (g : E →ᵇ F)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ContDiff ℝ ∞ (boundedShift g) := by
  let L := BoundedContinuousFunction.compContinuousCLM F ℝ
    (⟨fun y : E => -y, continuous_neg⟩ : ContinuousMap E E)
  have h := L.contDiff.comp ((contDiff_boundedTranslate g hg hc).comp contDiff_neg)
  convert h using 1
  funext x
  ext y
  simp [L, boundedShift, boundedTranslate, sub_eq_add_neg, add_comm]

#print axioms contDiff_boundedShift

private noncomputable def boundedKernelDeriv (g : ℂ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (i : ℕ) :
    ℂ →ᵇ (ℂ [×i]→L[ℝ] ℝ) :=
  (⟨⟨iteratedFDeriv ℝ i g, (hg.iteratedFDeriv_right (m := ∞) (by simp)).continuous⟩,
    hc.iteratedFDeriv (𝕜 := ℝ) i⟩ :
      CompactlySupportedContinuousMap ℂ (ℂ [×i]→L[ℝ] ℝ)).toBoundedContinuousFunction

private noncomputable def shiftedKernelJets (g : ℂ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (N : ℕ) (x : ℂ) :
    FiniteJets N :=
  fun i => boundedShift (boundedKernelDeriv g hg hc i) x

private theorem contDiff_shiftedKernelJets (g : ℂ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (N : ℕ) :
    ContDiff ℝ ∞ (shiftedKernelJets g hg hc N) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_boundedShift (boundedKernelDeriv g hg hc i)
    (hg.iteratedFDeriv_right (m := ∞) (by simp)) (hc.iteratedFDeriv (𝕜 := ℝ) i)

private noncomputable def shiftedKernelTest (g : ℂ → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Compacts ℂ) (x : ℂ)
    (hx : ∀ y ∉ K, g (y - x) = 0) : ContDiffMapSupportedIn ℂ ℝ ⊤ K where
  toFun := fun y => g (y - x)
  contDiff' := hg.comp (contDiff_id.sub contDiff_const)
  zero_on_compl' := hx

private theorem finiteJetMap_shiftedKernelTest (g : ℂ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (K : Compacts ℂ) (N : ℕ)
    (x : ℂ) (hx : ∀ y ∉ K, g (y - x) = 0) :
    finiteJetMap K N (shiftedKernelTest g hg K x hx) = shiftedKernelJets g hg hc N x := by
  funext i
  apply BoundedContinuousFunction.ext
  intro y
  change ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i : ℕ)
    (shiftedKernelTest g hg K x hx) y = iteratedFDeriv ℝ (i : ℕ) g (y - x)
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  exact iteratedFDeriv_comp_sub (i : ℕ) x y




#print axioms FiniteJets
#print axioms finiteJetMap
#print axioms finiteJetMap_injective
#print axioms boundedFlip
#print axioms boundedFlip_apply
#print axioms boundedTranslate

#print axioms contDiff_nat_boundedTranslate
#print axioms boundedShift

#print axioms boundedKernelDeriv
#print axioms shiftedKernelJets
#print axioms contDiff_shiftedKernelJets
#print axioms shiftedKernelTest
#print axioms finiteJetMap_shiftedKernelTest

end CanonicalDimensionTwo.LocalDbar.HarmonicProof

namespace CanonicalDimensionTwo.LocalDbar.HarmonicProof

private theorem iteratedFDeriv_directional_commute {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℂ → F} (hg : ContDiff ℝ ∞ g) (n : ℕ) (v z : ℂ) :
    fderiv ℝ (iteratedFDeriv ℝ n g) z v =
      iteratedFDeriv ℝ n (fun y => fderiv ℝ g y v) z := by
  induction n generalizing z with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.comp_fderiv]
    rfl
  | succ n ih =>
    have hi : (fun y => fderiv ℝ (iteratedFDeriv ℝ n g) y v) =
        iteratedFDeriv ℝ n (fun y => fderiv ℝ g y v) := by
      funext y
      exact ih y
    have hs : ContDiff ℝ ∞ (iteratedFDeriv ℝ n g) :=
      hg.iteratedFDeriv_right (m := ∞) (by simp)
    rw [iteratedFDeriv_succ_eq_comp_left,
      LinearIsometryEquiv.comp_fderiv (𝕜 := ℝ) (G := ℂ)
        (E := ℂ →L[ℝ] (ℂ [×n]→L[ℝ] F)) (F := ℂ [×(n + 1)]→L[ℝ] F),
      iteratedFDeriv_succ_eq_comp_left,
      ← hi]
    ext m
    change fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ n g)) z v (m 0) (Fin.tail m) =
      fderiv ℝ (fun y => fderiv ℝ (iteratedFDeriv ℝ n g) y v) z (m 0) (Fin.tail m)
    rw [fderiv_clm_apply
      ((hs.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z)
      (differentiableAt_const v)]
    simpa using congrArg (fun A => A (Fin.tail m))
      (hs.contDiffAt.isSymmSndFDerivAt (x := z) (by simp) v (m 0))

#print axioms iteratedFDeriv_directional_commute

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

private noncomputable abbrev finiteJetsModule (N : ℕ) : Module ℝ (FiniteJets N) :=
  (inferInstance : NormedSpace ℝ (FiniteJets N)).toModule

attribute [local instance] finiteJetsModule

private theorem fderiv_shiftedKernelJets (g : ℂ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (N : ℕ) (x v : ℂ) :
    fderiv ℝ (F := FiniteJets N) (shiftedKernelJets g hg hc N) x v =
      -shiftedKernelJets (fun y => fderiv ℝ g y v)
        ((hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
        (hc.fderiv_apply ℝ v) N x := by
  funext i
  apply BoundedContinuousFunction.ext
  intro y
  let ev : FiniteJets N →L[ℝ] (ℂ [×(i : ℕ)]→L[ℝ] ℝ) :=
    { toFun := fun q => q i y
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      cont := (BoundedContinuousFunction.evalCLM ℝ y).continuous.comp (continuous_apply i) }
  have hs : HasFDerivAt (shiftedKernelJets g hg hc N)
      (fderiv ℝ (F := FiniteJets N) (shiftedKernelJets g hg hc N) x) x :=
    ((contDiff_shiftedKernelJets g hg hc N).differentiable (by simp) x).hasFDerivAt
  have he := HasFDerivAt.comp (𝕜 := ℝ) (E := ℂ) (F := FiniteJets N)
    (G := ℂ [×(i : ℕ)]→L[ℝ] ℝ) x
    (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := FiniteJets N)
      (F := ℂ [×(i : ℕ)]→L[ℝ] ℝ) ev) hs
  have hd := ((hg.iteratedFDeriv_right (m := ∞) (i := (i : ℕ)) (by simp)).differentiable
    (by simp) (y - x)).hasFDerivAt.comp x
      ((hasFDerivAt_const (𝕜 := ℝ) y x).sub (hasFDerivAt_id x))
  have hd' : HasFDerivAt (fun a => ev (shiftedKernelJets g hg hc N a))
      (-(fderiv ℝ (iteratedFDeriv ℝ (i : ℕ) g) (y - x))) x := by
    convert hd using 1
    · rfl
    · ext w
      simp
  have h := congrArg (fun A => A v) (he.unique hd')
  change (fderiv ℝ (shiftedKernelJets g hg hc N) x v i) y =
    -(fderiv ℝ (iteratedFDeriv ℝ (i : ℕ) g) (y - x) v) at h
  rw [iteratedFDeriv_directional_commute hg] at h
  exact h

#print axioms fderiv_shiftedKernelJets

private theorem fderiv_regularizedKernel (g : ℂ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (N : ℕ)
    (L : FiniteJets N →L[ℝ] ℂ) (x v : ℂ) :
    fderiv ℝ (fun a => L (shiftedKernelJets g hg hc N a)) x v =
      -L (shiftedKernelJets (fun y => fderiv ℝ g y v)
        ((hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
        (hc.fderiv_apply ℝ v) N x) := by
  have hs := ((contDiff_shiftedKernelJets g hg hc N).differentiable (by simp) x).hasFDerivAt
  have he := HasFDerivAt.comp (𝕜 := ℝ) (E := ℂ) (F := FiniteJets N) (G := ℂ) x
    (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := FiniteJets N) (F := ℂ) L) hs
  have h := congrArg (fun A => A v) he.fderiv
  change fderiv ℝ (fun a => L (shiftedKernelJets g hg hc N a)) x v =
    L (fderiv ℝ (shiftedKernelJets g hg hc N) x v) at h
  erw [fderiv_shiftedKernelJets] at h
  exact h.trans (L.map_neg _)

private theorem second_fderiv_regularizedKernel (g : ℂ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (N : ℕ)
    (L : FiniteJets N →L[ℝ] ℂ) (x v : ℂ) :
    fderiv ℝ (fun a => fderiv ℝ (fun b => L (shiftedKernelJets g hg hc N b)) a v) x v =
      L (shiftedKernelJets (fun y => fderiv ℝ (fun z => fderiv ℝ g z v) y v)
        ((((hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).fderiv_right
          (m := ∞) (by simp)).clm_apply contDiff_const)
        ((hc.fderiv_apply ℝ v).fderiv_apply ℝ v) N x) := by
  have hfun := funext fun a => fderiv_regularizedKernel g hg hc N L a v
  erw [hfun, fderiv_fun_neg, neg_apply, fderiv_regularizedKernel, neg_neg]

private theorem shiftedKernelTest_fderiv (g : ℂ → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Compacts ℂ) (x : ℂ)
    (hx : ∀ y ∉ K, g (y - x) = 0) (y v : ℂ) :
    fderiv ℝ (shiftedKernelTest g hg K x hx) y v = fderiv ℝ g (y - x) v := by
  have h := ((hg.differentiable (by simp) (y - x)).hasFDerivAt).comp y
    ((hasFDerivAt_id y).sub_const x)
  change fderiv ℝ (g ∘ fun a : ℂ => a - x) y v = _
  simpa using congrArg (fun A => A v) h.fderiv

private theorem shiftedKernel_derivative_support (g : ℂ → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Compacts ℂ) (x : ℂ)
    (hx : ∀ y ∉ K, g (y - x) = 0) (v : ℂ) :
    ∀ y ∉ K, fderiv ℝ g (y - x) v = 0 := by
  intro y hy
  rw [← shiftedKernelTest_fderiv g hg K x hx y v]
  have hz : fderiv ℝ (shiftedKernelTest g hg K x hx) y = 0 :=
    (hasFDerivAt_zero_of_eventually_const 0 (Filter.eventually_of_mem
      (K.isCompact.isClosed.isOpen_compl.mem_nhds hy) (fun z hz => hx z hz))).fderiv
  rw [hz, zero_apply]

private theorem derivative_shiftedKernelTest (Ω : Opens ℂ) (g : ℂ → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Compacts ℂ) (hK : (K : Set ℂ) ⊆ Ω) (x : ℂ)
    (hx : ∀ y ∉ K, g (y - x) = 0) (v : ℂ) :
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v
      (TestFunction.ofSupportedIn hK (shiftedKernelTest g hg K x hx)) =
    TestFunction.ofSupportedIn hK (shiftedKernelTest (fun y => fderiv ℝ g y v)
      ((hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const) K x
      (shiftedKernel_derivative_support g hg K x hx v)) := by
  ext y
  simp only [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply,
    le_top, ↓reduceIte]
  exact shiftedKernelTest_fderiv g hg K x hx y v

#print axioms fderiv_regularizedKernel
#print axioms second_fderiv_regularizedKernel
#print axioms shiftedKernelTest_fderiv
#print axioms shiftedKernel_derivative_support
#print axioms derivative_shiftedKernelTest




private theorem smooth_laplacian_coordinate_formula {H : ℂ → ℂ}
    (hH : ContDiff ℝ ∞ H) (x : ℂ) :
    Laplacian.laplacian H x =
      fderiv ℝ (fun a => fderiv ℝ H a 1) x 1 +
        fderiv ℝ (fun a => fderiv ℝ H a Complex.I) x Complex.I := by
  have hd := ((hH.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp



#print axioms smooth_laplacian_coordinate_formula

private theorem finiteJets_mollifier_limit {ι : Type*} {l : Filter ι}
    {k : ι → ℂ → ℝ}
    (hn : ∀ᶠ i in l, ∀ x, 0 ≤ k i x)
    (hi : ∀ᶠ i in l, ∫ x : ℂ, k i x = 1)
    (hs : Tendsto (fun i => Function.support (k i)) l (𝓝 (0 : ℂ)).smallSets)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (N : ℕ) :
    Tendsto (fun i => ∫ x : ℂ, k i x • shiftedKernelJets φ hφ hcφ N x) l
      (𝓝 (shiftedKernelJets φ hφ hcφ N 0)) := by
  have hf : Continuous (fun x : ℂ => shiftedKernelJets φ hφ hcφ N (-x)) :=
    (contDiff_shiftedKernelJets φ hφ hcφ N).continuous.comp continuous_neg
  have hf0 : Tendsto (fun x : ℂ => shiftedKernelJets φ hφ hcφ N (-x))
      (𝓝 (0 : ℂ)) (𝓝 (shiftedKernelJets φ hφ hcφ N 0)) := by
    simpa only [neg_zero] using hf.tendsto 0
  have ht := MeasureTheory.convolution_tendsto_right (μ := volume)
    (g := fun _ : ι => fun x : ℂ => shiftedKernelJets φ hφ hcφ N (-x))
    (k := fun _ : ι => (0 : ℂ)) (x₀ := (0 : ℂ))
    (z₀ := shiftedKernelJets φ hφ hcφ N 0) hn hi hs
    (Eventually.of_forall fun _ => hf.aestronglyMeasurable)
    (hf0.comp tendsto_snd) tendsto_const_nhds
  simpa only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply,
    zero_sub, neg_neg] using ht

#print axioms finiteJets_mollifier_limit

open ContinuousLinearMap

set_option maxHeartbeats 400000
attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

private theorem fderiv_scalar_convolution {k f : ℂ → ℝ}
    (hk : LocallyIntegrable k volume) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (x v : ℂ) :
    fderiv ℝ (fun y => ∫ t : ℂ, k t * f (y - t)) x v =
      ∫ t : ℂ, k t * fderiv ℝ f (x - t) v := by
  let M : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := lsmul ℝ ℝ
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hd := hc.hasFDerivAt_convolution_right M hk hf1 x
  have hint : Integrable (fun t : ℂ =>
      M.precompR ℂ (k t) (fderiv ℝ f (x - t))) volume :=
    (hc.fderiv ℝ).convolutionExists_right (M.precompR ℂ)
      hk ((hf.fderiv_right (m := ∞) (by simp)).continuous) x
  have he := congrArg (fun A : ℂ →L[ℝ] ℝ => A v) hd.fderiv
  change fderiv ℝ (fun y => ∫ t : ℂ, k t * f (y - t)) x v =
      (∫ t : ℂ, M.precompR ℂ (k t) (fderiv ℝ f (x - t))) v at he
  rw [ContinuousLinearMap.integral_apply hint] at he
  exact he

private theorem integral_iteratedFDeriv_convolution {k φ : ℂ → ℝ}
    (hk : LocallyIntegrable k volume) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (n : ℕ) (x : ℂ) :
    iteratedFDeriv ℝ n (fun y => ∫ t : ℂ, k t * φ (y - t)) x =
      ∫ t : ℂ, k t • iteratedFDeriv ℝ n φ (x - t) := by
  have hs : ContDiff ℝ ∞ (fun y => ∫ t : ℂ, k t * φ (y - t)) := by
    exact hc.contDiff_convolution_right (lsmul ℝ ℝ) hk hφ
  have hint (j : ℕ) (y : ℂ) :
      Integrable (fun t : ℂ => k t • iteratedFDeriv ℝ j φ (y - t)) volume :=
    (hc.iteratedFDeriv (𝕜 := ℝ) j).convolutionExists_right (lsmul ℝ ℝ)
      hk (hφ.iteratedFDeriv_right (m := ∞) (by simp)).continuous y
  induction n generalizing x with
  | zero =>
      ext m
      rw [ContinuousMultilinearMap.integral_apply (hint 0 x)]
      simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
      ext m
      rw [((hs.iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp) x).iteratedFDeriv_succ_apply_left']
      have heq : (fun y => iteratedFDeriv ℝ n (fun z => ∫ t : ℂ, k t * φ (z - t)) y
          (Fin.tail m)) = (fun y => ∫ t : ℂ, k t * iteratedFDeriv ℝ n φ (y - t) (Fin.tail m)) := by
        funext y
        rw [ih, ContinuousMultilinearMap.integral_apply (hint n y)]
        rfl
      rw [heq]
      let A : (ℂ [×n]→L[ℝ] ℝ) →L[ℝ] ℝ :=
        ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℂ) ℝ (Fin.tail m)
      have hsf : ContDiff ℝ ∞ (fun y => iteratedFDeriv ℝ n φ y (Fin.tail m)) :=
        A.contDiff.comp (hφ.iteratedFDeriv_right (m := ∞) (by simp))
      have hcf : HasCompactSupport (fun y => iteratedFDeriv ℝ n φ y (Fin.tail m)) :=
        (hc.iteratedFDeriv (𝕜 := ℝ) n).comp_left A.map_zero
      rw [fderiv_scalar_convolution hk hsf hcf,
        ContinuousMultilinearMap.integral_apply (hint (n + 1) x)]
      apply integral_congr_ae
      filter_upwards with t
      simp only [smul_apply, smul_eq_mul]
      congr 1
      exact (((hφ.iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp) (x - t)).iteratedFDeriv_succ_apply_left' (m := m)).symm

#print axioms fderiv_scalar_convolution
#print axioms integral_iteratedFDeriv_convolution


private noncomputable abbrev finiteJetsContinuousENorm (N : ℕ) : ContinuousENorm (FiniteJets N) :=
  @SeminormedAddGroup.toContinuousENorm (FiniteJets N) (inferInstance : SeminormedAddGroup (FiniteJets N))

attribute [local instance] finiteJetsContinuousENorm

private theorem integrable_weighted_shiftedJets {k : ℂ → ℝ}
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (N : ℕ) :
    Integrable (fun x : ℂ => k x • shiftedKernelJets φ hφ hcφ N x) volume := by
  have hc : HasCompactSupport (fun x : ℂ => k x • shiftedKernelJets φ hφ hcφ N x) := by
    apply HasCompactSupport.of_support_subset_isCompact hkc
    intro x hx
    by_contra h
    exact hx (by
      change k x • shiftedKernelJets φ hφ hcφ N x = 0
      rw [image_eq_zero_of_notMem_tsupport h]
      funext i
      apply BoundedContinuousFunction.ext
      intro y
      exact zero_smul ℝ (iteratedFDeriv ℝ (i : ℕ) φ (y - x)))
  exact (hk.smul (contDiff_shiftedKernelJets φ hφ hcφ N).continuous).integrable_of_hasCompactSupport hc

private noncomputable def finiteJetsEval (N : ℕ) (i : Fin (N + 1)) (y : ℂ) :
    FiniteJets N →L[ℝ] (ℂ [×(i : ℕ)]→L[ℝ] ℝ) where
  toFun := fun q => q i y
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  cont := (BoundedContinuousFunction.evalCLM ℝ y).continuous.comp (continuous_apply i)

private theorem integral_shiftedKernelJets_apply {k : ℂ → ℝ}
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (N : ℕ) (i : Fin (N + 1)) (y : ℂ) :
    (∫ x : ℂ, k x • shiftedKernelJets φ hφ hcφ N x) i y =
      ∫ x : ℂ, k x • iteratedFDeriv ℝ (i : ℕ) φ (y - x) := by
  exact (ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (E := FiniteJets N)
    (Fₗ := ℂ [×(i : ℕ)]→L[ℝ] ℝ) (finiteJetsEval N i y)
    (integrable_weighted_shiftedJets hk hkc φ hφ hcφ N)).symm

private theorem integral_shiftedKernelJets_comm {k φ : ℂ → ℝ}
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (N : ℕ) :
    (∫ x : ℂ, k x • shiftedKernelJets φ hφ hcφ N x) =
      ∫ x : ℂ, φ x • shiftedKernelJets k hk hkc N x := by
  have he : (fun y => ∫ t : ℂ, k t * φ (y - t)) =
      (fun y => ∫ t : ℂ, φ t * k (y - t)) := by
    funext y
    rw [← integral_sub_left_eq_self (fun t : ℂ => φ t * k (y - t)) volume y]
    simp only [sub_sub_self, mul_comm]
  funext i
  apply BoundedContinuousFunction.ext
  intro y
  rw [integral_shiftedKernelJets_apply hk.continuous hkc,
    integral_shiftedKernelJets_apply hφ.continuous hcφ,
    ← integral_iteratedFDeriv_convolution hk.continuous.locallyIntegrable hφ hcφ,
    ← integral_iteratedFDeriv_convolution hφ.continuous.locallyIntegrable hk hkc, he]

private theorem regularized_pairing_comm {k φ : ℂ → ℝ}
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (N : ℕ)
    (L : FiniteJets N →L[ℝ] ℂ) :
    (∫ x : ℂ, φ x • L (shiftedKernelJets k hk hkc N x)) =
      L (∫ x : ℂ, k x • shiftedKernelJets φ hφ hcφ N x) := by
  rw [integral_shiftedKernelJets_comm hk hkc hφ hcφ]
  simpa only [map_smul] using ContinuousLinearMap.integral_comp_comm
    (𝕜 := ℝ) (E := FiniteJets N) (Fₗ := ℂ) L
    (integrable_weighted_shiftedJets hφ.continuous hcφ k hk hkc N)

#print axioms integrable_weighted_shiftedJets
#print axioms finiteJetsEval
#print axioms integral_shiftedKernelJets_apply
#print axioms integral_shiftedKernelJets_comm
#print axioms regularized_pairing_comm

private theorem shiftedKernelJets_zero_stage (K : Compacts ℂ)
    (φ : ContDiffMapSupportedIn ℂ ℝ ⊤ K) (N : ℕ) :
    shiftedKernelJets φ φ.contDiff φ.hasCompactSupport N 0 = finiteJetMap K N φ := by
  funext i
  apply BoundedContinuousFunction.ext
  intro y
  change iteratedFDeriv ℝ (i : ℕ) φ (y - 0) =
    ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i : ℕ) φ y
  rw [sub_zero, ContDiffMapSupportedIn.structureMapCLM_top_apply]

private theorem distribution_smoothing_recovers (Ω : Opens ℂ)
    (D : Distribution Ω ℂ ⊤) (K : Compacts ℂ) (hK : (K : Set ℂ) ⊆ Ω) :
    ∃ (N : ℕ) (L : FiniteJets N →L[ℝ] ℂ),
      (∀ φ : ContDiffMapSupportedIn ℂ ℝ ⊤ K,
        D (TestFunction.ofSupportedIn hK φ) = L (finiteJetMap K N φ)) ∧
      ∀ (k : ℕ → ℂ → ℝ) (hk : ∀ n, ContDiff ℝ ∞ (k n))
        (hkc : ∀ n, HasCompactSupport (k n)),
        (∀ n x, 0 ≤ k n x) → (∀ n, ∫ x : ℂ, k n x = 1) →
        Tendsto (fun n => Function.support (k n)) atTop (𝓝 (0 : ℂ)).smallSets →
        ∀ φ : ContDiffMapSupportedIn ℂ ℝ ⊤ K,
          Tendsto (fun n => ∫ x : ℂ, φ x • L (shiftedKernelJets (k n) (hk n) (hkc n) N x))
            atTop (𝓝 (D (TestFunction.ofSupportedIn hK φ))) := by
  obtain ⟨N, L, hL⟩ := distribution_finite_jet_representation Ω D K hK
  refine ⟨N, L, hL, ?_⟩
  intro k hk hkc hn hi hs φ
  have ht := finiteJets_mollifier_limit (Eventually.of_forall hn) (Eventually.of_forall hi)
    hs φ φ.contDiff φ.hasCompactSupport N
  have htL := L.continuous.continuousAt.tendsto.comp ht
  rw [shiftedKernelJets_zero_stage, ← hL φ] at htL
  convert htL using 1
  funext n
  exact regularized_pairing_comm (hk n) (hkc n) φ.contDiff φ.hasCompactSupport N L

#print axioms shiftedKernelJets_zero_stage
#print axioms distribution_smoothing_recovers


open Set Complex Real Metric

private theorem polarCoord_symm_circle (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  apply Complex.ext <;> simp [Complex.polarCoord_symm_apply, circleMap_zero_re,
    circleMap_zero_im, -Complex.ofReal_cos, -Complex.ofReal_sin]

private theorem compact_polar_integral {f : ℂ → ℂ} (hf : Continuous f)
    {R : ℝ} (hR : 0 < R) (hzero : ∀ w, R ≤ ‖w‖ → f w = 0) :
    (∫ w : ℂ, f w) = ∫ r in 0..R, ∫ θ in -Real.pi..Real.pi,
      r • f (circleMap 0 r θ) := by
  let P : ℝ × ℝ → ℂ := fun p => p.1 • f (circleMap 0 p.1 p.2)
  have hP : Continuous P := continuous_fst.smul (hf.comp (by fun_prop [circleMap]))
  have hPint : IntegrableOn P (Ioc 0 R ×ˢ Ioo (-Real.pi) Real.pi) :=
    (hP.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)
  calc
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, P p := by
      simpa only [polarCoord_target, polarCoord_symm_circle] using
        (Complex.integral_comp_polarCoord_symm f).symm
    _ = ∫ p in Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi, P p := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (measurableSet_Ioi.prod measurableSet_Ioo) (Set.prod_mono Ioc_subset_Ioi_self Subset.rfl)
      intro p hp
      have hpr : R < p.1 := by
        by_contra h
        exact hp.2 ⟨⟨hp.1.1, not_lt.mp h⟩, hp.1.2⟩
      have hn : R ≤ ‖circleMap 0 p.1 p.2‖ := by
        simpa only [norm_circleMap_zero, abs_of_pos (show 0 < p.1 from hp.1.1)] using hpr.le
      simp [P, hzero _ hn]
    _ = ∫ r in Ioc (0 : ℝ) R, ∫ θ in Ioo (-Real.pi) Real.pi, P (r, θ) := by
      rw [Measure.volume_eq_prod] at hPint ⊢
      exact setIntegral_prod P hPint
    _ = _ := by
      simp_rw [intervalIntegral.integral_of_le hR.le,
        intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le), integral_Ioc_eq_integral_Ioo]
      rfl

private theorem harmonic_angular_integral {H : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hH : InnerProductSpace.HarmonicOnNhd H (Metric.closedBall c |r|)) :
    (∫ θ in -Real.pi..Real.pi, H (circleMap c r θ)) = (2 * Real.pi) • H c := by
  have he := circleAverage_eq_integral_add (f := H) (c := c) (R := r) (-Real.pi)
  rw [intervalIntegral.integral_comp_add_right (fun θ => H (circleMap c r θ))] at he
  have hbounds : (0 : ℝ) + -Real.pi = -Real.pi := by ring
  have hbounds' : 2 * Real.pi + -Real.pi = Real.pi := by ring
  rw [hbounds, hbounds', hH.circleAverage_eq] at he
  have hm := congrArg (fun z : ℂ => (2 * Real.pi) • z) he
  simpa only [smul_smul, mul_inv_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero),
    one_smul] using hm.symm

private theorem harmonic_radial_averaging {H : ℂ → ℂ} (hH : Continuous H)
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hhar : InnerProductSpace.HarmonicOnNhd H (Metric.closedBall c R))
    {k : ℂ → ℝ} (hk : Continuous k)
    (hradial : ∀ z w : ℂ, ‖z‖ = ‖w‖ → k z = k w)
    (hzero : ∀ w : ℂ, R ≤ ‖w‖ → k w = 0) :
    (∫ w : ℂ, k w • H (c + w)) = (∫ w : ℂ, k w) • H c := by
  have h1 := compact_polar_integral (f := fun w : ℂ => k w • H (c + w)) (hk.smul (hH.comp (continuous_const.add continuous_id)))
    hR (fun w hw => by simp only [hzero w hw, zero_smul])
  have h2 := compact_polar_integral (f := fun w : ℂ => k w • H c) (hk.smul continuous_const)
    hR (fun w hw => by simp only [hzero w hw, zero_smul])
  rw [← integral_smul_const] 
  rw [h1, h2]
  apply intervalIntegral.integral_congr
  intro r hr
  have hr0 : 0 ≤ r := (uIcc_of_le hR.le ▸ hr).1
  have hrR : r ≤ R := (uIcc_of_le hR.le ▸ hr).2
  have hrad (θ : ℝ) : k (circleMap 0 r θ) = k (r : ℂ) :=
    hradial _ _ (by simp [norm_circleMap_zero])
  simp_rw [hrad, smul_smul, intervalIntegral.integral_smul]
  have hcirc (θ : ℝ) : c + circleMap 0 r θ = circleMap c r θ := by simp [circleMap]
  simp_rw [hcirc]
  rw [harmonic_angular_integral (hhar.mono (by
    rw [abs_of_nonneg hr0]
    exact Metric.closedBall_subset_closedBall hrR)), intervalIntegral.integral_const]
  congr 1
  congr 1
  ring

#print axioms compact_polar_integral
#print axioms harmonic_angular_integral
#print axioms harmonic_radial_averaging


open Set Complex Real Metric

private theorem exists_normalized_radial_kernel (r : ℝ) (hr : 0 < r) :
    ∃ k : ℂ → ℝ, ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧
      (∀ z, 0 ≤ k z) ∧ (∫ z : ℂ, k z) = 1 ∧
      (∀ z w : ℂ, ‖z‖ = ‖w‖ → k z = k w) ∧
      (∀ z : ℂ, r ≤ ‖z‖ → k z = 0) := by
  let B := ContDiffBumpBase.ofInnerProductSpace ℂ
  let q : ℂ → ℝ := fun z => B.toFun 2 ((2 / r) • z)
  have hq : ContDiff ℝ ∞ q := by
    let A : ℂ → ℝ × ℂ := fun z => (2, (2 / r) • z)
    have hA : ContDiff ℝ ∞ A := by
      dsimp only [A]
      fun_prop
    rw [contDiff_iff_contDiffAt]
    intro z
    have hb := B.smooth.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
      (show A z ∈ Ioi (1 : ℝ) ×ˢ (univ : Set ℂ) from ⟨by norm_num [A], mem_univ _⟩))
    exact hb.comp z hA.contDiffAt
  have hrad (z w : ℂ) (h : ‖z‖ = ‖w‖) : q z = q w := by
    simp only [q, B, ContDiffBumpBase.ofInnerProductSpace, norm_smul, h]
  have hsupp : Function.support q = Metric.ball (0 : ℂ) r := by
    ext z
    change B.toFun 2 ((2 / r) • z) ≠ 0 ↔ _
    rw [← Function.mem_support, B.support 2 (by norm_num)]
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos (show (0 : ℝ) < 2 by norm_num) hr)]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hr]
    constructor <;> intro h <;> nlinarith
  have hqc : HasCompactSupport q := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) r)
    rw [hsupp]
    exact Metric.ball_subset_closedBall
  have hqn (z : ℂ) : 0 ≤ q z := (B.mem_Icc 2 ((2 / r) • z)).1
  have hqi : Integrable q volume := hq.continuous.integrable_of_hasCompactSupport hqc
  have hqp : 0 < ∫ z : ℂ, q z := by
    rw [integral_pos_iff_support_of_nonneg hqn hqi, hsupp]
    exact measure_ball_pos volume (0 : ℂ) hr
  refine ⟨fun z => q z / ∫ w : ℂ, q w, hq.div_const _, ?_, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) r)
    intro z hz
    have hzq : q z ≠ 0 := by
      intro hzq
      exact hz (by simp only [hzq, zero_div])
    exact ball_subset_closedBall (hsupp ▸ hzq)
  · intro z
    exact div_nonneg (hqn z) hqp.le
  · rw [integral_div, div_self hqp.ne']
  · intro z w h
    simp only [hrad z w h]
  · intro z hz
    have hzq : q z = 0 := by
      by_contra h
      have hm : z ∈ Metric.ball (0 : ℂ) r := hsupp ▸ h
      exact (not_lt_of_ge hz) (by simpa using hm)
    simp only [hzq, zero_div]

#print axioms exists_normalized_radial_kernel

private theorem exists_radial_approximate_identity :
    ∃ k : ℕ → ℂ → ℝ,
      (∀ n, ContDiff ℝ ∞ (k n) ∧ HasCompactSupport (k n) ∧
        (∀ z, 0 ≤ k n z) ∧ (∫ z : ℂ, k n z) = 1 ∧
        (∀ z w : ℂ, ‖z‖ = ‖w‖ → k n z = k n w) ∧
        (∀ z : ℂ, 1 / ((n : ℝ) + 1) ≤ ‖z‖ → k n z = 0)) ∧
      Tendsto (fun n => Function.support (k n)) atTop (𝓝 (0 : ℂ)).smallSets := by
  have hex (n : ℕ) := exists_normalized_radial_kernel (1 / ((n : ℝ) + 1)) (by positivity)
  choose k hk using hex
  refine ⟨k, hk, ?_⟩
  rw [nhds_basis_ball.smallSets.tendsto_right_iff]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  intro z hz
  have hnz : ‖z‖ < 1 / ((n : ℝ) + 1) := by
    by_contra h
    exact hz ((hk n).2.2.2.2.2 z (not_lt.mp h))
  exact mem_ball_zero_iff.mpr (hnz.trans hn)

#print axioms exists_radial_approximate_identity

private noncomputable def finiteJetsShift (N : ℕ) (z : ℂ) :
    FiniteJets N →L[ℝ] FiniteJets N where
  toFun := fun q i => boundedShift (q i) z
  map_add' := by
    intro q q'
    funext i
    apply BoundedContinuousFunction.ext
    intro y
    rfl
  map_smul' := by
    intro a q
    funext i
    apply BoundedContinuousFunction.ext
    intro y
    rfl
  cont := continuous_pi fun i =>
    (BoundedContinuousFunction.compContinuousCLM (ℂ [×(i : ℕ)]→L[ℝ] ℝ) ℝ
      (⟨fun y : ℂ => y - z, continuous_id.sub continuous_const⟩ : ContinuousMap ℂ ℂ)).continuous.comp
        (continuous_apply i)

private theorem finiteJetsShift_shiftedKernelJets (N : ℕ) (z x : ℂ)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    finiteJetsShift N z (shiftedKernelJets φ hφ hcφ N x) =
      shiftedKernelJets φ hφ hcφ N (z + x) := by
  funext i
  apply BoundedContinuousFunction.ext
  intro y
  change iteratedFDeriv ℝ (i : ℕ) φ ((y - z) - x) =
    iteratedFDeriv ℝ (i : ℕ) φ (y - (z + x))
  rw [sub_add_eq_sub_sub]

private theorem centered_regularized_pairing_comm {k φ : ℂ → ℝ}
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (N : ℕ) (L : FiniteJets N →L[ℝ] ℂ) (z : ℂ) :
    (∫ x : ℂ, φ x • L (shiftedKernelJets k hk hkc N (z + x))) =
      ∫ x : ℂ, k x • L (shiftedKernelJets φ hφ hcφ N (z + x)) := by
  let A : FiniteJets N →L[ℝ] ℂ := L.comp (finiteJetsShift N z)
  have h₁ := regularized_pairing_comm hk hkc hφ hcφ N A
  have h₂ := regularized_pairing_comm hφ hcφ hk hkc N A
  rw [integral_shiftedKernelJets_comm hk hkc hφ hcφ] at h₁
  have he := h₁.trans h₂.symm
  simpa only [A, ContinuousLinearMap.comp_apply, finiteJetsShift_shiftedKernelJets] using he

private theorem regularizations_agree_by_radial_mean_value {k φ : ℂ → ℝ}
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (N : ℕ) (L : FiniteJets N →L[ℝ] ℂ) (z : ℂ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s)
    (hki : (∫ w : ℂ, k w) = 1) (hφi : (∫ w : ℂ, φ w) = 1)
    (hkrad : ∀ u v : ℂ, ‖u‖ = ‖v‖ → k u = k v)
    (hφrad : ∀ u v : ℂ, ‖u‖ = ‖v‖ → φ u = φ v)
    (hk0 : ∀ w : ℂ, r ≤ ‖w‖ → k w = 0)
    (hφ0 : ∀ w : ℂ, s ≤ ‖w‖ → φ w = 0)
    (hkh : InnerProductSpace.HarmonicOnNhd
      (fun x => L (shiftedKernelJets k hk hkc N x)) (Metric.closedBall z s))
    (hφh : InnerProductSpace.HarmonicOnNhd
      (fun x => L (shiftedKernelJets φ hφ hcφ N x)) (Metric.closedBall z r)) :
    L (shiftedKernelJets k hk hkc N z) = L (shiftedKernelJets φ hφ hcφ N z) := by
  have hLc : Continuous (fun q : FiniteJets N => L q) := L.continuous
  have he₁ := harmonic_radial_averaging
    (hLc.comp (contDiff_shiftedKernelJets k hk hkc N).continuous)
    hs hkh hφ.continuous hφrad hφ0
  have he₂ := harmonic_radial_averaging
    (hLc.comp (contDiff_shiftedKernelJets φ hφ hcφ N).continuous)
    hr hφh hk.continuous hkrad hk0
  rw [hφi, one_smul] at he₁
  rw [hki, one_smul] at he₂
  exact he₁.symm.trans ((centered_regularized_pairing_comm hk hkc hφ hcφ N L z).trans he₂)

#print axioms finiteJetsShift
#print axioms finiteJetsShift_shiftedKernelJets
#print axioms centered_regularized_pairing_comm
#print axioms regularizations_agree_by_radial_mean_value

private theorem regularized_laplacian_zero (Ω : Opens ℂ)
    (D : Distribution Ω ℂ ⊤)
    (hD : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℂ)
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℂ) D) +
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) Complex.I
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) Complex.I D) = 0)
    (K : Compacts ℂ) (hK : (K : Set ℂ) ⊆ Ω)
    (N : ℕ) (L : FiniteJets N →L[ℝ] ℂ)
    (hL : ∀ φ : ContDiffMapSupportedIn ℂ ℝ ⊤ K,
      D (TestFunction.ofSupportedIn hK φ) = L (finiteJetMap K N φ))
    (g : ℂ → ℝ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (x : ℂ) (hx : ∀ y ∉ K, g (y - x) = 0) :
    Laplacian.laplacian (fun a => L (shiftedKernelJets g hg hc N a)) x = 0 := by
  have heq (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
      (a : ℂ) (ha : ∀ y ∉ K, f (y - a) = 0) :
      L (shiftedKernelJets f hf hfc N a) =
        D (TestFunction.ofSupportedIn hK (shiftedKernelTest f hf K a ha)) := by
    rw [hL, finiteJetMap_shiftedKernelTest]
  have hLs : ContDiff ℝ ∞ (fun q : FiniteJets N => L q) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := FiniteJets N) (F := ℂ) (n := ∞) L
  have hs : ContDiff ℝ ∞ (fun a => L (shiftedKernelJets g hg hc N a)) :=
    hLs.comp (contDiff_shiftedKernelJets g hg hc N)
  rw [smooth_laplacian_coordinate_formula hs]
  have hgs (v : ℂ) : ContDiff ℝ ∞ (fun y => fderiv ℝ g y v) :=
    (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hp := congrArg
    (fun A : Distribution Ω ℂ ⊤ => A (TestFunction.ofSupportedIn hK
      (shiftedKernelTest g hg K x hx))) hD
  simp only [add_apply, Distribution.lineDerivCLM_apply, neg_neg, zero_apply] at hp
  simp only [derivative_shiftedKernelTest] at hp
  erw [second_fderiv_regularizedKernel, second_fderiv_regularizedKernel]
  erw [heq _ _ _ x (shiftedKernel_derivative_support _ (hgs 1) K x
    (shiftedKernel_derivative_support g hg K x hx 1) 1)]
  erw [heq _ _ _ x (shiftedKernel_derivative_support _ (hgs Complex.I) K x
    (shiftedKernel_derivative_support g hg K x hx Complex.I) Complex.I)]
  exact hp

private theorem regularized_harmonic_inner_ball (Ω : Opens ℂ)
    (D : Distribution Ω ℂ ⊤)
    (hD : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℂ)
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℂ) D) +
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) Complex.I
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) Complex.I D) = 0)
    (c : ℂ) (S : ℝ) (hK : Metric.closedBall c S ⊆ Ω)
    (N : ℕ) (L : FiniteJets N →L[ℝ] ℂ)
    (hL : ∀ φ : ContDiffMapSupportedIn ℂ ℝ ⊤ ⟨Metric.closedBall c S, isCompact_closedBall c S⟩,
      D (TestFunction.ofSupportedIn hK φ) = L (finiteJetMap _ N φ))
    (g : ℂ → ℝ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (r : ℝ) (hzero : ∀ w : ℂ, r ≤ ‖w‖ → g w = 0) :
    InnerProductSpace.HarmonicOnNhd (fun a => L (shiftedKernelJets g hg hc N a))
      (Metric.ball c (S - r)) := by
  have hLs : ContDiff ℝ ∞ (fun q : FiniteJets N => L q) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := FiniteJets N) (F := ℂ) (n := ∞) L
  intro x hx
  refine ⟨(hLs.comp (contDiff_shiftedKernelJets g hg hc N)).contDiffAt.of_le (by simp), ?_⟩
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with a ha
  apply regularized_laplacian_zero Ω D hD ⟨Metric.closedBall c S, isCompact_closedBall c S⟩
    hK N L hL g hg hc a
  intro y hy
  apply hzero
  have hy' : S < dist y c := lt_of_not_ge hy
  have ha' : dist a c < S - r := ha
  have ht := dist_triangle y a c
  simp only [dist_eq_norm] at ht hy' ha'
  linarith

#print axioms regularized_laplacian_zero
#print axioms regularized_harmonic_inner_ball

private theorem harmonic_distribution_inner_representation (Ω : Opens ℂ)
    (D : Distribution Ω ℂ ⊤)
    (hD : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℂ)
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℂ) D) +
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) Complex.I
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) Complex.I D) = 0)
    (c : ℂ) (S r : ℝ) (hrS : r < S) (hK : Metric.closedBall c S ⊆ Ω) :
    ∃ H : ℂ → ℂ, ContDiff ℝ ∞ H ∧
      ∀ φ : TestFunction Ω ℝ ⊤, tsupport φ ⊆ Metric.ball c r →
        D φ = ∫ x : ℂ, φ x • H x := by
  let K : Compacts ℂ := ⟨Metric.closedBall c S, isCompact_closedBall c S⟩
  obtain ⟨N, L, hL, hrec⟩ := distribution_smoothing_recovers Ω D K hK
  let δ := (S - r) / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hgap : r + 2 * δ < S := by dsimp [δ]; linarith
  obtain ⟨j, hj, hjc, hjn, hji, hjrad, hj0⟩ := exists_normalized_radial_kernel δ hδ
  obtain ⟨k, hk, hks⟩ := exists_radial_approximate_identity
  let H : ℂ → ℂ := fun x => L (shiftedKernelJets j hj hjc N x)
  have hLs : ContDiff ℝ ∞ (fun q : FiniteJets N => L q) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := FiniteJets N) (F := ℂ) (n := ∞) L
  have hH : ContDiff ℝ ∞ H := hLs.comp (contDiff_shiftedKernelJets j hj hjc N)
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hevent : ∀ᶠ n : ℕ in atTop, ∀ x ∈ Metric.ball c r,
      L (shiftedKernelJets (k n) (hk n).1 (hk n).2.1 N x) = H x := by
    filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn x hx
    have hnk0 : ∀ w : ℂ, δ ≤ ‖w‖ → k n w = 0 :=
      fun w hw => (hk n).2.2.2.2.2 w (hn.le.trans hw)
    have hsub : Metric.closedBall x δ ⊆ Metric.ball c (S - δ) :=
      Metric.closedBall_subset_ball' (by have hx' : dist x c < r := hx; linarith)
    exact regularizations_agree_by_radial_mean_value
      (hk n).1 (hk n).2.1 hj hjc N L x δ δ hδ hδ (hk n).2.2.2.1 hji
      (hk n).2.2.2.2.1 hjrad hnk0 hj0
      ((regularized_harmonic_inner_ball Ω D hD c S hK N L hL
        (k n) (hk n).1 (hk n).2.1 δ hnk0).mono hsub)
      ((regularized_harmonic_inner_ball Ω D hD c S hK N L hL j hj hjc δ hj0).mono hsub)
  refine ⟨H, hH, ?_⟩
  intro φ hφ
  let ψ : ContDiffMapSupportedIn ℂ ℝ ⊤ K :=
    ⟨φ, φ.contDiff, fun x hx => image_eq_zero_of_notMem_tsupport (fun hm =>
      hx ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hrS.le)) (hφ hm)))⟩
  have hψ : TestFunction.ofSupportedIn hK ψ = φ := by ext x; rfl
  have ht := hrec k (fun n => (hk n).1) (fun n => (hk n).2.1)
    (fun n => (hk n).2.2.1) (fun n => (hk n).2.2.2.1) hks ψ
  rw [hψ] at ht
  have heq : (fun n => ∫ x : ℂ, ψ x • L (shiftedKernelJets (k n) (hk n).1 (hk n).2.1 N x))
      =ᶠ[atTop] (fun _ => ∫ x : ℂ, φ x • H x) := by
    filter_upwards [hevent] with n hn
    apply integral_congr_ae
    filter_upwards with x
    change φ x • L (shiftedKernelJets (k n) (hk n).1 (hk n).2.1 N x) = φ x • H x
    by_cases hx : φ x = 0
    · simp only [hx, zero_smul]
    · rw [hn x (hφ (subset_tsupport φ hx))]
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' heq.symm)

#print axioms harmonic_distribution_inner_representation

private theorem continuous_representatives_agree (Ω U : Opens ℂ)
    (hU : (U : Set ℂ) ⊆ Ω) (D : Distribution Ω ℂ ⊤)
    (H G : ℂ → ℂ) (hH : Continuous H) (hG : Continuous G)
    (hHr : ∀ φ : TestFunction Ω ℝ ⊤, tsupport φ ⊆ U → D φ = ∫ x : ℂ, φ x • H x)
    (hGr : ∀ φ : TestFunction Ω ℝ ⊤, tsupport φ ⊆ U → D φ = ∫ x : ℂ, φ x • G x) :
    Set.EqOn H G U := by
  have hHi : LocallyIntegrableOn H U volume := hH.continuousOn.locallyIntegrableOn U.isOpen.measurableSet
  have hGi : LocallyIntegrableOn G U volume := hG.continuousOn.locallyIntegrableOn U.isOpen.measurableSet
  have he : Distribution.ofFun U H volume ⊤ = Distribution.ofFun U G volume ⊤ := by
    ext φ
    rw [Distribution.ofFun_apply hHi, Distribution.ofFun_apply hGi]
    let ψ : TestFunction Ω ℝ ⊤ :=
      ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hU⟩
    exact (hHr ψ φ.tsupport_subset).symm.trans (hGr ψ φ.tsupport_subset)
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq (Distribution.ofFun_injective hHi hGi he)
    U.isOpen hH.continuousOn hG.continuousOn

private theorem compact_support_inside_smaller_disk (c : ℂ) (R : ℝ) (hR : 0 < R)
    {φ : ℂ → ℝ} (hc : HasCompactSupport φ) (hφ : tsupport φ ⊆ Metric.ball c R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ tsupport φ ⊆ Metric.ball c r := by
  rcases (tsupport φ).eq_empty_or_nonempty with he | hn
  · refine ⟨R / 2, by linarith, by linarith, ?_⟩
    rw [he]
    exact Set.empty_subset _
  obtain ⟨x, hx, hmax⟩ := hc.exists_isMaxOn hn (continuous_id.dist continuous_const).continuousOn
  have hxR : dist x c < R := hφ hx
  refine ⟨(dist x c + R) / 2, by linarith [dist_nonneg (x := x) (y := c)], by linarith, ?_⟩
  intro y hy
  have hm : dist y c ≤ dist x c := hmax hy
  change dist y c < (dist x c + R) / 2
  linarith

private theorem disk_smooth_representative_from_inner_disks (c : ℂ) (R : ℝ) (hR : 0 < R)
    (D : Distribution (⟨Metric.ball c R, Metric.isOpen_ball⟩ : Opens ℂ) ℂ ⊤)
    (hinner : ∀ r : ℝ, 0 < r → r < R →
      ∃ H : ℂ → ℂ, ContDiff ℝ ∞ H ∧
        ∀ φ : TestFunction (⟨Metric.ball c R, Metric.isOpen_ball⟩ : Opens ℂ) ℝ ⊤,
          tsupport φ ⊆ Metric.ball c r → D φ = ∫ x : ℂ, φ x • H x) :
    ∃ g : ℂ → ℂ, ContDiffOn ℝ ∞ g (Metric.ball c R) ∧
      D = Distribution.ofFun (⟨Metric.ball c R, Metric.isOpen_ball⟩ : Opens ℂ) g volume ⊤ := by
  classical
  let Ω : Opens ℂ := ⟨Metric.ball c R, Metric.isOpen_ball⟩
  let J := {r : ℝ // 0 < r ∧ r < R}
  have hfamily (r : J) := hinner r r.property.1 r.property.2
  choose H hHs hHr using hfamily
  have hagree (r s : J) : Set.EqOn (H r) (H s) (Metric.ball c (min r.val s.val)) := by
    apply continuous_representatives_agree Ω
      ⟨Metric.ball c (min r.val s.val), Metric.isOpen_ball⟩
      (Metric.ball_subset_ball ((min_le_left r.val s.val).trans r.property.2.le)) D
      (H r) (H s) (hHs r).continuous (hHs s).continuous
    · intro φ hφ
      exact hHr r φ (hφ.trans (Metric.ball_subset_ball (min_le_left _ _)))
    · intro φ hφ
      exact hHr s φ (hφ.trans (Metric.ball_subset_ball (min_le_right _ _)))
  have hpoint (x : ℂ) (hx : x ∈ Metric.ball c R) :
      ∃ r : J, x ∈ Metric.ball c r.val := by
    have hxR : dist x c < R := hx
    refine ⟨⟨(dist x c + R) / 2, ?_, ?_⟩, ?_⟩
    · linarith [dist_nonneg (x := x) (y := c)]
    · linarith
    · change dist x c < _
      linarith
  let g : ℂ → ℂ := fun x => if hx : x ∈ Metric.ball c R then H (hpoint x hx).choose x else 0
  have hgH (r : J) : Set.EqOn g (H r) (Metric.ball c r.val) := by
    intro x hx
    have hxR : x ∈ Metric.ball c R := Metric.ball_subset_ball r.property.2.le hx
    simp only [g, dite_eq_left hxR]
    apply hagree (hpoint x hxR).choose r
    exact lt_min (show dist x c < (hpoint x hxR).choose.val from (hpoint x hxR).choose_spec)
      (show dist x c < r.val from hx)
  have hgs : ContDiffOn ℝ ∞ g (Metric.ball c R) := by
    intro x hx
    obtain ⟨r, hr⟩ := hpoint x hx
    apply ContDiffAt.contDiffWithinAt
    apply (hHs r).contDiffAt.congr_of_eventuallyEq
    filter_upwards [Metric.isOpen_ball.mem_nhds hr] with y hy
    exact hgH r hy
  refine ⟨g, hgs, ?_⟩
  ext φ
  rw [Distribution.ofFun_apply (hgs.continuousOn.locallyIntegrableOn Metric.isOpen_ball.measurableSet)]
  obtain ⟨r, hr, hrR, hφr⟩ := compact_support_inside_smaller_disk c R hR φ.hasCompactSupport φ.tsupport_subset
  let j : J := ⟨r, hr, hrR⟩
  rw [hHr j φ hφr]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : φ x = 0
  · simp only [hx, zero_smul]
  · rw [hgH j (hφr (subset_tsupport φ hx))]

#print axioms continuous_representatives_agree
#print axioms compact_support_inside_smaller_disk
#print axioms disk_smooth_representative_from_inner_disks

end CanonicalDimensionTwo.LocalDbar.HarmonicProof

namespace CanonicalDimensionTwo.LocalDbar

/-- Harmonic distributions on a positive-radius disk admit a smooth density on
that entire disk, with the original real-test distribution normalization. -/
theorem actualDiskHarmonicDistributionSmoothRepresentative :
    ActualDiskHarmonicDistributionSmoothRepresentativeStatement := by
  intro c R hR D hD
  apply HarmonicProof.disk_smooth_representative_from_inner_disks c R hR D
  intro r hr hrR
  exact HarmonicProof.harmonic_distribution_inner_representation
    ⟨Metric.ball c R, Metric.isOpen_ball⟩ D hD c ((r + R) / 2) r
    (by linarith) (Metric.closedBall_subset_ball (by linarith))

#print axioms actualDiskHarmonicDistributionSmoothRepresentative

end CanonicalDimensionTwo.LocalDbar
