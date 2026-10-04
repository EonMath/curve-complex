import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.FiniteChartTopology
import CurveComplexGenusTwo.Topology.ActualDbarClosedImage.NormalFamilyActualDbarReview
import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.DolbeaultDbar
import CurveComplexGenusTwo.Topology.ActualDbarClosedImage.CompactHolomorphicFunctionConstant
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Group.Bounded
import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.CompactCauchyProof
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.KernelCalculus
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

-- Preserved private proof component from ClosedImageTopology.lean

open scoped Manifold ContDiff
open Set Filter Topology
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SameAtlasAnalyticCohomology
universe u
variable {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]

private theorem continuous_smoothZeroJet (a : E) (n : ℕ) :
    Continuous (smoothZeroJet a n : SmoothZero E → C(ChartTarget a, RealJet n)) := by
  have h : Continuous (fun f : SmoothZero E => fun (a : E) (n : ℕ) =>
      smoothZeroJet a n f) := continuous_induced_dom
  exact (continuous_apply n).comp ((continuous_apply a).comp h)

private noncomputable def targetLocalMap (a : E) (x : E) : ChartTarget a := by
  classical
  exact if h : x ∈ (extChartAt 𝓘(ℂ) a).source then
    ⟨(extChartAt 𝓘(ℂ) a) x, (extChartAt 𝓘(ℂ) a).map_source h⟩
  else ⟨(extChartAt 𝓘(ℂ) a) a,
    (extChartAt 𝓘(ℂ) a).map_source (mem_extChartAt_source a)⟩

private theorem targetLocalMap_val {a x : E}
    (hx : x ∈ (extChartAt 𝓘(ℂ) a).source) :
    (targetLocalMap a x).val = (extChartAt 𝓘(ℂ) a) x := by
  simp only [targetLocalMap, dite_eq_left hx]

private theorem targetLocalMap_continuousAt {a x : E}
    (hx : x ∈ (extChartAt 𝓘(ℂ) a).source) :
    ContinuousAt (targetLocalMap a) x := by
  apply (Topology.IsInducing.subtypeVal.continuousAt_iff).mpr
  apply (continuousAt_extChartAt' hx).congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source a).mem_nhds hx] with y hy
  exact targetLocalMap_val hy

private theorem smoothZero_evaluation_continuous :
    Continuous (fun p : SmoothZero E × E => p.1.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨f, x⟩
  letI : LocallyCompactSpace (ChartTarget x) :=
    (isOpen_extChartAt_target x).locallyCompactSpace
  have hjet : ContinuousAt
      (fun p : SmoothZero E × E => smoothZeroJet x 0 p.1) (f, x) :=
    ((continuous_smoothZeroJet x 0).comp continuous_fst).continuousAt
  have hpoint := (targetLocalMap_continuousAt (mem_extChartAt_source x)).comp
    (continuous_snd.continuousAt : ContinuousAt (Prod.snd : SmoothZero E × E → E) (f, x))
  have heval := hjet.eval hpoint
  have hzero : ContinuousAt
      (fun p : SmoothZero E × E =>
        (continuousMultilinearCurryFin0 ℝ ℂ ℂ)
          ((smoothZeroJet x 0 p.1) (targetLocalMap x p.2))) (f, x) :=
    (continuousMultilinearCurryFin0 ℝ ℂ ℂ).continuous.continuousAt.comp heval
  apply hzero.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := 𝓘(ℂ)) x)] with p hp
  change p.1.1 p.2 = (iteratedFDeriv ℝ 0
    (fun z => p.1.1 ((extChartAt 𝓘(ℂ) x).symm z))
    (targetLocalMap x p.2).val) 0
  rw [iteratedFDeriv_zero_apply, targetLocalMap_val hp,
    (extChartAt 𝓘(ℂ) x).left_inv hp]

private noncomputable def smoothZeroToContinuous : SmoothZero E →ₗ[ℂ] C(E, ℂ) where
  toFun f := ⟨f.1, smoothZero_evaluation_continuous.comp (continuous_const.prodMk continuous_id)⟩
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

private theorem smoothZeroToContinuous_continuous :
    Continuous (smoothZeroToContinuous (E := E)) :=
  ContinuousMap.continuous_of_continuous_uncurry _ smoothZero_evaluation_continuous

private theorem smoothZeroToContinuous_injective :
    Function.Injective (smoothZeroToContinuous (E := E)) := by
  intro f g h
  apply Subtype.ext
  exact congrArg DFunLike.coe h

private theorem smoothZero_t2 : T2Space (SmoothZero E) :=
  T2Space.of_injective_continuous smoothZeroToContinuous_injective
    smoothZeroToContinuous_continuous

private theorem compact_smoothZero_norm_continuous [CompactSpace E] :
    Continuous (fun f : SmoothZero E => ‖smoothZeroToContinuous f‖) :=
  continuous_norm.comp smoothZeroToContinuous_continuous

private theorem compact_smoothZero_norm_eq_zero_iff [CompactSpace E] (f : SmoothZero E) :
    ‖smoothZeroToContinuous f‖ = 0 ↔ f = 0 := by
  rw [norm_eq_zero, ← map_zero smoothZeroToContinuous,
    smoothZeroToContinuous_injective.eq_iff]

private theorem compact_smoothZero_norm_bounds [CompactSpace E] (f : SmoothZero E) (x : E) :
    ‖f.1 x‖ ≤ ‖smoothZeroToContinuous f‖ :=
  ContinuousMap.norm_coe_le_norm (smoothZeroToContinuous f) x

private noncomputable def smoothZeroConst (c : ℂ) : SmoothZero E :=
  ⟨fun _ => c, fun _ => contDiffOn_const⟩

private theorem smoothZeroConst_continuous :
    Continuous (smoothZeroConst (E := E)) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  apply continuous_pi
  intro n
  apply ContinuousMap.continuous_of_continuous_uncurry
  by_cases hn : n = 0
  · subst n
    change Continuous (fun p : ℂ × ChartTarget a =>
      iteratedFDeriv ℝ 0 (fun _ : ℂ => p.1) p.2.1)
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 ℝ ℂ ℂ).symm.continuous.comp continuous_fst
  · change Continuous (fun p : ℂ × ChartTarget a =>
      iteratedFDeriv ℝ n (fun _ : ℂ => p.1) p.2.1)
    simp only [iteratedFDeriv_const_of_ne hn]
    exact continuous_const

private noncomputable def normalizeAt (p : E) (f : SmoothZero E) : SmoothZero E :=
  f - smoothZeroConst (f.1 p)

private theorem normalizeAt_apply (p : E) (f : SmoothZero E) (x : E) :
    (normalizeAt p f).1 x = f.1 x - f.1 p := rfl

private theorem normalizeAt_basepoint (p : E) (f : SmoothZero E) :
    (normalizeAt p f).1 p = 0 := sub_self _

private theorem normalizeAt_continuous (p : E) :
    Continuous (normalizeAt p : SmoothZero E → SmoothZero E) := by
  apply continuous_id.sub
  exact smoothZeroConst_continuous.comp
    (smoothZero_evaluation_continuous.comp (continuous_id.prodMk continuous_const))

private theorem normalizeAt_idempotent (p : E) (f : SmoothZero E) :
    normalizeAt p (normalizeAt p f) = normalizeAt p f := by
  apply Subtype.ext
  funext x
  simp only [normalizeAt_apply, sub_self, sub_zero]

private theorem normalized_functions_isClosed (p : E) :
    IsClosed {f : SmoothZero E | f.1 p = 0} := by
  exact isClosed_eq
    (smoothZero_evaluation_continuous.comp (continuous_id.prodMk continuous_const))
    continuous_const

private theorem chartDbar_normalizeAt (p : E) (f : SmoothZero E) (a x : E) :
    chartDbar a (normalizeAt p f).1 x = chartDbar a f.1 x := by
  simp only [chartDbar, normalizeAt_apply, fderiv_sub_const]

private theorem normalized_sup_norm_convergence [CompactSpace E]
    {ι : Type*} {l : Filter ι} {f : ι → SmoothZero E} {F : SmoothZero E}
    (hf : Tendsto f l (𝓝 F)) :
    Tendsto (fun n => ‖smoothZeroToContinuous (f n)‖) l
      (𝓝 ‖smoothZeroToContinuous F‖) :=
  compact_smoothZero_norm_continuous.continuousAt.tendsto.comp hf

private theorem normalized_limit_preserves_basepoint
    {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → SmoothZero E} {F : SmoothZero E}
    (p : E) (hf : Tendsto f l (𝓝 F)) (hzero : ∀ᶠ n in l, (f n).1 p = 0) :
    F.1 p = 0 := by
  exact (normalized_functions_isClosed p).mem_of_tendsto hf hzero

private theorem zero_chartDbar_analytic (f : SmoothZero E)
    (hz : ∀ a x, x ∈ (extChartAt 𝓘(ℂ) a).source → chartDbar a f.1 x = 0)
    (a : E) :
    AnalyticOnNhd ℂ (fun z => f.1 ((extChartAt 𝓘(ℂ) a).symm z))
      (extChartAt 𝓘(ℂ) a).target := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_extChartAt_target a)
  intro z hz'
  have hd := ((f.property a).differentiableOn (by simp)).differentiableAt
    ((isOpen_extChartAt_target a).mem_nhds hz')
  have he := hz a ((extChartAt 𝓘(ℂ) a).symm z)
    ((extChartAt 𝓘(ℂ) a).map_target hz')
  simp only [chartDbar, (extChartAt 𝓘(ℂ) a).right_inv hz'] at he
  have he' : (fderiv ℝ (fun w => f.1 ((extChartAt 𝓘(ℂ) a).symm w)) z) 1 +
      Complex.I * (fderiv ℝ (fun w => f.1 ((extChartAt 𝓘(ℂ) a).symm w)) z)
        Complex.I = 0 := by
    exact (div_eq_zero_iff.mp he).resolve_right (by norm_num)
  have hcr : (fderiv ℝ (fun w => f.1 ((extChartAt 𝓘(ℂ) a).symm w)) z)
      Complex.I = Complex.I *
        (fderiv ℝ (fun w => f.1 ((extChartAt 𝓘(ℂ) a).symm w)) z) 1 := by
    have hmul := congrArg (fun v : ℂ => Complex.I * v) he'
    simpa only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul, mul_zero,
      ← sub_eq_add_neg, sub_eq_zero] using (sub_eq_zero.mp (by
        simpa only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul, mul_zero,
          ← sub_eq_add_neg] using hmul)).symm
  exact (differentiableAt_complex_iff_differentiableAt_real.mpr ⟨hd, hcr⟩).differentiableWithinAt

private theorem zero_chartDbar_constant
    [T2Space E] [CompactSpace E] [Nonempty E] [PreconnectedSpace E]
    (f : SmoothZero E)
    (hz : ∀ a x, x ∈ (extChartAt 𝓘(ℂ) a).source → chartDbar a f.1 x = 0) :
    ∀ x y : E, f.1 x = f.1 y := by
  apply CanonicalBasepointFree.compact_surface_global_analytic_map_constant f.1
  intro x
  refine ⟨fun z => f.1 ((extChartAt 𝓘(ℂ) x).symm z), ?_, ?_, ?_⟩
  · have ha := zero_chartDbar_analytic f hz x ((extChartAt 𝓘(ℂ) x) x)
      ((extChartAt 𝓘(ℂ) x).map_source (mem_extChartAt_source x))
    exact ha
  · filter_upwards [(extChartAt_source_mem_nhds (I := 𝓘(ℂ)) x)] with y hy
    change f.1 y = f.1 ((extChartAt 𝓘(ℂ) x).symm ((extChartAt 𝓘(ℂ) x) y))
    rw [(extChartAt 𝓘(ℂ) x).left_inv hy]
  · change f.1 x = f.1 ((extChartAt 𝓘(ℂ) x).symm ((extChartAt 𝓘(ℂ) x) x))
    rw [extChartAt_to_inv]

private theorem normalized_zero_chartDbar_eq_zero
    [T2Space E] [CompactSpace E] [Nonempty E] [PreconnectedSpace E]
    (p : E) (f : SmoothZero E) (hp : f.1 p = 0)
    (hz : ∀ a x, x ∈ (extChartAt 𝓘(ℂ) a).source → chartDbar a f.1 x = 0) :
    f = 0 := by
  apply Subtype.ext
  funext x
  exact (zero_chartDbar_constant f hz x p).trans hp

private theorem chartDbar_evaluation_continuous (a x : E)
    (hx : x ∈ (extChartAt 𝓘(ℂ) a).source) :
    Continuous (fun f : SmoothZero E => chartDbar a f.1 x) := by
  let z : ChartTarget a :=
    ⟨(extChartAt 𝓘(ℂ) a) x, (extChartAt 𝓘(ℂ) a).map_source hx⟩
  have hj := (continuous_smoothZeroJet a 1).eval_const z
  have h1 := hj.eval_const (fun _ : Fin 1 => (1 : ℂ))
  have hI := hj.eval_const (fun _ : Fin 1 => Complex.I)
  have h := (h1.add (hI.const_mul Complex.I)).div_const (2 : ℂ)
  convert h using 1
  funext f
  change ((fderiv ℝ (fun w => f.1 ((extChartAt 𝓘(ℂ) a).symm w))
      ((extChartAt 𝓘(ℂ) a) x)) 1 + Complex.I *
      (fderiv ℝ (fun w => f.1 ((extChartAt 𝓘(ℂ) a).symm w))
        ((extChartAt 𝓘(ℂ) a) x)) Complex.I) / 2 =
    ((iteratedFDeriv ℝ 1 (fun w => f.1 ((extChartAt 𝓘(ℂ) a).symm w))
      ((extChartAt 𝓘(ℂ) a) x)) (fun _ => 1) + Complex.I *
      (iteratedFDeriv ℝ 1 (fun w => f.1 ((extChartAt 𝓘(ℂ) a).symm w))
        ((extChartAt 𝓘(ℂ) a) x)) (fun _ => Complex.I)) / 2
  rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply]

private theorem normalized_unit_limit_impossible
    [T2Space E] [CompactSpace E] [Nonempty E] [PreconnectedSpace E]
    {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → SmoothZero E} {F : SmoothZero E}
    (p : E) (hf : Tendsto f l (𝓝 F))
    (hp : ∀ᶠ n in l, (f n).1 p = 0)
    (hnorm : ∀ᶠ n in l, ‖smoothZeroToContinuous (f n)‖ = 1)
    (hd : ∀ a x, x ∈ (extChartAt 𝓘(ℂ) a).source →
      Tendsto (fun n => chartDbar a (f n).1 x) l (𝓝 0)) : False := by
  have hFp : F.1 p = 0 := normalized_limit_preserves_basepoint p hf hp
  have hFd : ∀ a x, x ∈ (extChartAt 𝓘(ℂ) a).source → chartDbar a F.1 x = 0 := by
    intro a x hx
    exact tendsto_nhds_unique
      ((chartDbar_evaluation_continuous a x hx).continuousAt.tendsto.comp hf) (hd a x hx)
  have hF : F = 0 := normalized_zero_chartDbar_eq_zero p F hFp hFd
  have hFnorm : ‖smoothZeroToContinuous F‖ = 1 :=
    tendsto_nhds_unique (normalized_sup_norm_convergence hf)
      (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hnorm))
  have hFzero : ‖smoothZeroToContinuous F‖ = 0 :=
    (compact_smoothZero_norm_eq_zero_iff F).mpr hF
  exact zero_ne_one (hFzero.symm.trans hFnorm)

private theorem exists_finite_nested_chart_disks [CompactSpace E] :
    ∃ (r : E → ℝ) (s : Finset E),
      (∀ a, 0 < r a ∧
        Metric.closedBall ((extChartAt 𝓘(ℂ) a) a) (2 * r a) ⊆
          (extChartAt 𝓘(ℂ) a).target) ∧
      ∀ x : E, ∃ a ∈ s, x ∈ (extChartAt 𝓘(ℂ) a).source ∧
        (extChartAt 𝓘(ℂ) a) x ∈ Metric.ball ((extChartAt 𝓘(ℂ) a) a) (r a) := by
  classical
  have hrad : ∀ a : E, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall ((extChartAt 𝓘(ℂ) a) a) (2 * r) ⊆
        (extChartAt 𝓘(ℂ) a).target := by
    intro a
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      ((isOpen_extChartAt_target a).mem_nhds
        ((extChartAt 𝓘(ℂ) a).map_source (mem_extChartAt_source a)))
    refine ⟨ε / 4, by positivity, ?_⟩
    exact (Metric.closedBall_subset_ball (by linarith)).trans hεsub
  choose r hr using hrad
  let U : E → Set E := fun a => (extChartAt 𝓘(ℂ) a).source ∩
    (extChartAt 𝓘(ℂ) a) ⁻¹' Metric.ball ((extChartAt 𝓘(ℂ) a) a) (r a)
  have hUopen : ∀ a, IsOpen (U a) :=
    fun a => isOpen_extChartAt_preimage' a Metric.isOpen_ball
  have hcover : (Set.univ : Set E) ⊆ ⋃ a, U a := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_extChartAt_source x, Metric.mem_ball_self (hr x).1⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen hcover
  refine ⟨r, s, hr, ?_⟩
  intro x
  rcases Set.mem_iUnion.mp (hs (Set.mem_univ x)) with ⟨a, ha⟩
  rcases Set.mem_iUnion.mp ha with ⟨has, hx⟩
  exact ⟨a, has, hx⟩

private theorem compact_chartJet_norm_continuous (a : E) (n : ℕ)
    (K : Set (ChartTarget a)) [CompactSpace K] :
    Continuous (fun f : SmoothZero E => ‖(smoothZeroJet a n f).restrict K‖) :=
  (continuous_norm (E := C(K, RealJet n))).comp ((ContinuousMap.continuous_restrict K).comp
    (continuous_smoothZeroJet a n))

private theorem compact_chartJet_norm_nonneg (a : E) (n : ℕ)
    (K : Set (ChartTarget a)) [CompactSpace K] (f : SmoothZero E) :
    0 ≤ ‖(smoothZeroJet a n f).restrict K‖ := norm_nonneg ((smoothZeroJet a n f).restrict K)

private theorem compact_chartJet_point_bound (a : E) (n : ℕ)
    (K : Set (ChartTarget a)) [CompactSpace K] (f : SmoothZero E)
    (z : ChartTarget a) (hz : z ∈ K) :
    ‖smoothZeroJet a n f z‖ ≤ ‖(smoothZeroJet a n f).restrict K‖ :=
  ContinuousMap.norm_coe_le_norm ((smoothZeroJet a n f).restrict K) ⟨z, hz⟩

private theorem compact_chartJet_norm_smul (a : E) (n : ℕ)
    (K : Set (ChartTarget a)) [CompactSpace K] (c : ℂ) (f : SmoothZero E) :
    ‖(smoothZeroJet a n (c • f)).restrict K‖ =
      ‖c‖ * ‖(smoothZeroJet a n f).restrict K‖ := by
  have he : (smoothZeroJet a n (c • f)).restrict K =
      c • (smoothZeroJet a n f).restrict K := by
    apply ContinuousMap.ext
    intro z
    exact iteratedFDeriv_const_smul_apply
      ((f.property a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.1.property)
        |>.of_le (by simp))
  rw [he]
  letI : NormSMulClass ℂ C(K, RealJet n) :=
    NormedSpace.toNormSMulClass (𝕜 := ℂ) (E := C(K, RealJet n))
  exact norm_smul c ((smoothZeroJet a n f).restrict K)

private theorem compact_chartJet_norm_add_le (a : E) (n : ℕ)
    (K : Set (ChartTarget a)) [CompactSpace K] (f g : SmoothZero E) :
    ‖(smoothZeroJet a n (f + g)).restrict K‖ ≤
      ‖(smoothZeroJet a n f).restrict K‖ + ‖(smoothZeroJet a n g).restrict K‖ := by
  have he : (smoothZeroJet a n (f + g)).restrict K =
      (smoothZeroJet a n f).restrict K + (smoothZeroJet a n g).restrict K := by
    apply ContinuousMap.ext
    intro z
    exact iteratedFDeriv_add_apply
      ((f.property a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.1.property)
        |>.of_le (by simp))
      ((g.property a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.1.property)
        |>.of_le (by simp))
  rw [he]
  exact norm_add_le ((smoothZeroJet a n f).restrict K) ((smoothZeroJet a n g).restrict K)

private theorem isCompact_closedBall_in_chartTarget (a : E) (r : ℝ)
    (hsub : Metric.closedBall ((extChartAt 𝓘(ℂ) a) a) r ⊆
      (extChartAt 𝓘(ℂ) a).target) :
    IsCompact {z : ChartTarget a | z.1 ∈ Metric.closedBall ((extChartAt 𝓘(ℂ) a) a) r} := by
  exact Topology.IsInducing.subtypeVal.isCompact_preimage'
    (isCompact_closedBall _ _) (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hsub)

private theorem global_sup_norm_le_finite_chart_norms [CompactSpace E]
    (s : Finset E) (K : ∀ a : E, Set (ChartTarget a)) [∀ a, CompactSpace (K a)]
    (hcover : ∀ x : E, ∃ a ∈ s, ∃ hx : x ∈ (extChartAt 𝓘(ℂ) a).source,
      (⟨(extChartAt 𝓘(ℂ) a) x, (extChartAt 𝓘(ℂ) a).map_source hx⟩ : ChartTarget a) ∈ K a)
    (f : SmoothZero E) :
    ‖smoothZeroToContinuous f‖ ≤ ∑ a ∈ s, ‖(smoothZeroJet a 0 f).restrict (K a)‖ := by
  classical
  apply (ContinuousMap.norm_le _ (Finset.sum_nonneg (fun a _ => norm_nonneg
    ((smoothZeroJet a 0 f).restrict (K a))))).mpr
  intro x
  obtain ⟨a, has, hax, hK⟩ := hcover x
  have hpoint := compact_chartJet_point_bound a 0 (K a) f
    ⟨(extChartAt 𝓘(ℂ) a) x, (extChartAt 𝓘(ℂ) a).map_source hax⟩ hK
  have hval : ‖f.1 x‖ ≤ ‖(smoothZeroJet a 0 f).restrict (K a)‖ := by
    change ‖iteratedFDeriv ℝ 0 (fun w => f.1 ((extChartAt 𝓘(ℂ) a).symm w))
      ((extChartAt 𝓘(ℂ) a) x)‖ ≤ _ at hpoint
    simpa only [norm_iteratedFDeriv_zero, (extChartAt 𝓘(ℂ) a).left_inv hax] using hpoint
  exact hval.trans (Finset.single_le_sum
    (fun b _ => norm_nonneg ((smoothZeroJet b 0 f).restrict (K b))) has)

private theorem dolbeaultDbar_normalizeAt (p : E) (f : SmoothZero E) :
    dolbeaultDbar (normalizeAt p f) = dolbeaultDbar f := by
  classical
  apply Subtype.ext
  funext a x
  change (if x ∈ (extChartAt 𝓘(ℂ) a).source then
    chartDbar a (normalizeAt p f).1 x else 0) =
    (if x ∈ (extChartAt 𝓘(ℂ) a).source then chartDbar a f.1 x else 0)
  rw [chartDbar_normalizeAt]

private theorem dolbeaultDbar_eq_zero_iff_chartDbar_eq_zero (f : SmoothZero E) :
    dolbeaultDbar f = 0 ↔
      ∀ a x, x ∈ (extChartAt 𝓘(ℂ) a).source → chartDbar a f.1 x = 0 := by
  classical
  constructor
  · intro h a x hx
    have hax := congrArg (fun α : SmoothZeroOne E => α.1 a x) h
    simpa only [dolbeaultDbar, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hx,
      Submodule.coe_zero, Pi.zero_apply] using hax
  · intro h
    apply Subtype.ext
    funext a x
    change (if x ∈ (extChartAt 𝓘(ℂ) a).source then chartDbar a f.1 x else 0) = 0
    split_ifs with hx
    · exact h a x hx
    · rfl

private theorem normalized_dolbeaultDbar_injective
    [T2Space E] [CompactSpace E] [Nonempty E] [PreconnectedSpace E]
    (p : E) (f g : SmoothZero E) (hf : f.1 p = 0) (hg : g.1 p = 0)
    (hd : dolbeaultDbar f = dolbeaultDbar g) : f = g := by
  apply sub_eq_zero.mp
  apply normalized_zero_chartDbar_eq_zero p (f - g)
  · change f.1 p - g.1 p = 0
    rw [hf, hg, sub_self]
  · apply (dolbeaultDbar_eq_zero_iff_chartDbar_eq_zero _).mp
    rw [map_sub, hd, sub_self]

private theorem range_eq_normalized_image (p : E) :
    ((dolbeaultDbar (E := E)).range : Set (SmoothZeroOne E)) =
      dolbeaultDbar '' {f : SmoothZero E | f.1 p = 0} := by
  ext α
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨normalizeAt p f, normalizeAt_basepoint p f, dolbeaultDbar_normalizeAt p f⟩
  · rintro ⟨f, _, rfl⟩
    exact ⟨f, rfl⟩

private theorem smoothZeroOne_t2 : T2Space (SmoothZeroOne E) := by
  let J := fun α : SmoothZeroOne E => fun (a : E) (n : ℕ) => smoothZeroOneJet a n α
  have hJ : Topology.IsInducing J := ⟨rfl⟩
  apply (Topology.IsEmbedding.mk hJ ?_).t2Space
  intro α β h
  apply Subtype.ext
  funext a x
  by_cases hx : x ∈ (extChartAt 𝓘(ℂ) a).source
  · let z : ChartTarget a :=
      ⟨(extChartAt 𝓘(ℂ) a) x, (extChartAt 𝓘(ℂ) a).map_source hx⟩
    have he := congrArg (fun j => (j a 0 z) (0 : Fin 0 → ℂ)) h
    change (iteratedFDeriv ℝ 0 (fun w => α.1 a ((extChartAt 𝓘(ℂ) a).symm w))
      ((extChartAt 𝓘(ℂ) a) x)) 0 =
      (iteratedFDeriv ℝ 0 (fun w => β.1 a ((extChartAt 𝓘(ℂ) a).symm w))
        ((extChartAt 𝓘(ℂ) a) x)) 0 at he
    simpa only [iteratedFDeriv_zero_apply, (extChartAt 𝓘(ℂ) a).left_inv hx] using he
  · exact (α.property.1 a x hx).trans (β.property.1 a x hx).symm

private theorem range_mem_of_primitive_limit
    {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → SmoothZero E} {F : SmoothZero E}
    {α : SmoothZeroOne E} (hf : Tendsto f l (𝓝 F))
    (hd : Tendsto (fun n => dolbeaultDbar (f n)) l (𝓝 α)) :
    α ∈ (dolbeaultDbar (E := E)).range := by
  letI := smoothZeroOne_t2 (E := E)
  exact ⟨F, tendsto_nhds_unique (dolbeaultDbar_continuous.continuousAt.tendsto.comp hf) hd⟩

end SameAtlasAnalyticCohomology

-- Preserved private proof component from NormalFamilyLocalTools.lean

-- Private technical component preserved from CauchyCompactEstimates.lean

open scoped ContDiff Topology Convolution
open MeasureTheory Set Filter Metric

namespace SameAtlasAnalyticCohomology.NormalFamilyTechnical

private theorem inv_convolution_compact_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    (g : ℂ → F) {R Z B : ℝ} (_hB : 0 ≤ B)
    (hg : ∀ w, ‖g w‖ ≤ B)
    (hs : Function.support g ⊆ closedBall (0 : ℂ) R)
    {z : ℂ} (hz : ‖z‖ ≤ Z) :
    ‖∫ w : ℂ, w⁻¹ • g (z - w)‖ ≤
      (∫ w : ℂ in closedBall 0 (R + Z), ‖w⁻¹‖) * B := by
  let K : Set ℂ := closedBall 0 (R + Z)
  have hi : IntegrableOn (fun w : ℂ => ‖w⁻¹‖ * B) K :=
    ((CanonicalDimensionTwo.LocalDbar.locallyIntegrable_complex_inv.integrableOn_isCompact
      (isCompact_closedBall 0 (R + Z))).norm).mul_const B
  have hdom : ∀ w : ℂ, ‖w⁻¹ • g (z - w)‖ ≤
      K.indicator (fun w : ℂ => ‖w⁻¹‖ * B) w := by
    intro w
    by_cases hw : w ∈ K
    · rw [Set.indicator_of_mem hw, norm_smul]
      exact mul_le_mul_of_nonneg_left (hg (z - w)) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hw]
      have hgw : g (z - w) = 0 := by
        by_contra hne
        have hn : ‖z - w‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hs hne
        have hsum : ‖w‖ ≤ R + Z := calc
          ‖w‖ = ‖z - (z - w)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖z‖ + ‖z - w‖ := norm_sub_le _ _
          _ ≤ R + Z := by linarith
        exact hw (by simpa only [K, mem_closedBall, dist_zero_right] using hsum)
      simp only [hgw, smul_zero, norm_zero, le_refl]
  calc
    ‖∫ w : ℂ, w⁻¹ • g (z - w)‖ ≤
        ∫ w : ℂ, K.indicator (fun w : ℂ => ‖w⁻¹‖ * B) w :=
      norm_integral_le_of_norm_le (hi.integrable_indicator measurableSet_closedBall)
        (Filter.Eventually.of_forall hdom)
    _ = (∫ w : ℂ in closedBall 0 (R + Z), ‖w⁻¹‖) * B := by
      rw [integral_indicator measurableSet_closedBall, integral_mul_const]

private theorem inv_convolution_uniformly_zero_of_uniformly_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    {g : ℕ → ℂ → F} {R Z : ℝ}
    (hs : ∀ n, Function.support (g n) ⊆ closedBall (0 : ℂ) R)
    (hg : TendstoUniformly (g) (fun _ => 0) atTop) :
    TendstoUniformlyOn (fun n z => ∫ w : ℂ, w⁻¹ • g n (z - w))
      (fun _ => 0) atTop (closedBall (0 : ℂ) Z) := by
  let C : ℝ := ∫ w : ℂ in closedBall 0 (R + Z), ‖w⁻¹‖
  have hC : 0 ≤ C := integral_nonneg (fun _ => norm_nonneg _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε' : 0 < ε / (C + 1) := div_pos hε (by linarith)
  have hg' := Metric.tendstoUniformly_iff.mp hg (ε / (C + 1)) hε'
  filter_upwards [hg'] with n hn
  intro z hz
  have hbound : ∀ w, ‖g n w‖ ≤ ε / (C + 1) := by
    intro w
    exact (show ‖g n w‖ < ε / (C + 1) by simpa only [dist_zero_left] using hn w).le
  have h := inv_convolution_compact_bound (g n) hε'.le hbound (hs n)
    (show ‖z‖ ≤ Z by simpa only [mem_closedBall, dist_zero_right] using hz)
  rw [dist_zero_left]
  apply h.trans_lt
  change C * (ε / (C + 1)) < ε
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by linarith : 0 < C + 1)).mpr
  nlinarith

private theorem fderiv_inv_smul_integral
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] {g : ℂ → F}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    fderiv ℝ (fun z : ℂ => ∫ w : ℂ, w⁻¹ • g (z - w)) =
      fun z => ∫ w : ℂ, w⁻¹ • fderiv ℝ g (z - w) := by
  funext z
  have h := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    CanonicalDimensionTwo.LocalDbar.locallyIntegrable_complex_inv
    (hg.of_le (by simp)) z
  change fderiv ℝ ((fun w : ℂ => w⁻¹) ⋆[ContinuousLinearMap.lsmul ℝ ℂ] g) z = _
  rw [h.fderiv]
  rfl

private theorem iteratedFDeriv_inv_convolution_compact_bound
    (n : ℕ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] {g : ℂ → F}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {R Z B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ w, ‖iteratedFDeriv ℝ n g w‖ ≤ B)
    (hs : Function.support g ⊆ closedBall (0 : ℂ) R)
    {z : ℂ} (hz : ‖z‖ ≤ Z) :
    ‖iteratedFDeriv ℝ n (fun z : ℂ => ∫ w : ℂ, w⁻¹ • g (z - w)) z‖ ≤
      (∫ w : ℂ in closedBall 0 (R + Z), ‖w⁻¹‖) * B := by
  induction n generalizing F with
  | zero =>
    simp only [norm_iteratedFDeriv_zero] at hbound ⊢
    exact inv_convolution_compact_bound g hB hbound hs hz
  | succ n ih =>
    rw [← norm_iteratedFDeriv_fderiv, fderiv_inv_smul_integral hg hc]
    apply ih (hg.fderiv_right (by simp)) (hc.fderiv ℝ)
    · intro w
      simpa only [norm_iteratedFDeriv_fderiv] using hbound w
    · exact (support_fderiv_subset ℝ).trans (closure_minimal hs isClosed_closedBall)

private theorem inv_convolution_real_jets_uniformly_zero
    {g : ℕ → ℂ → ℂ} {R Z : ℝ}
    (hg : ∀ n, ContDiff ℝ ∞ (g n)) (hc : ∀ n, HasCompactSupport (g n))
    (hs : ∀ n, Function.support (g n) ⊆ closedBall (0 : ℂ) R)
    (k : ℕ)
    (ht : TendstoUniformly (fun n => iteratedFDeriv ℝ k (g n)) (fun _ => 0) atTop) :
    TendstoUniformlyOn
      (fun n => iteratedFDeriv ℝ k (fun z : ℂ => ∫ w : ℂ, w⁻¹ • g n (z - w)))
      (fun _ => 0) atTop (closedBall (0 : ℂ) Z) := by
  let C : ℝ := ∫ w : ℂ in closedBall 0 (R + Z), ‖w⁻¹‖
  have hC : 0 ≤ C := integral_nonneg (fun _ => norm_nonneg _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε' : 0 < ε / (C + 1) := div_pos hε (by linarith)
  have ht' := Metric.tendstoUniformly_iff.mp ht (ε / (C + 1)) hε'
  filter_upwards [ht'] with n hn
  have hbound : ∀ w, ‖iteratedFDeriv ℝ k (g n) w‖ ≤ ε / (C + 1) := by
    intro w
    exact (show ‖iteratedFDeriv ℝ k (g n) w‖ < ε / (C + 1) by
      simpa only [dist_zero_left] using hn w).le
  intro z hz
  have h := iteratedFDeriv_inv_convolution_compact_bound k (hg n) (hc n)
    hε'.le hbound (hs n)
    (show ‖z‖ ≤ Z by simpa only [mem_closedBall, dist_zero_right] using hz)
  rw [dist_zero_left]
  apply h.trans_lt
  change C * (ε / (C + 1)) < ε
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by linarith : 0 < C + 1)).mpr
  nlinarith

end SameAtlasAnalyticCohomology.NormalFamilyTechnical

namespace SameAtlasAnalyticCohomology.NormalFamilyTechnical

private theorem normalized_cauchy_real_jets_uniformly_zero
    {g : ℕ → ℂ → ℂ} {R Z : ℝ}
    (hg : ∀ n, ContDiff ℝ ∞ (g n)) (hc : ∀ n, HasCompactSupport (g n))
    (hs : ∀ n, Function.support (g n) ⊆ closedBall (0 : ℂ) R)
    (k : ℕ)
    (ht : TendstoUniformly (fun n => iteratedFDeriv ℝ k (g n)) (fun _ => 0) atTop) :
    TendstoUniformlyOn
      (fun n => iteratedFDeriv ℝ k
        (fun z : ℂ => (Real.pi : ℂ)⁻¹ * ∫ w : ℂ, w⁻¹ * g n (z - w)))
      (fun _ => 0) atTop (closedBall (0 : ℂ) Z) := by
  let a : ℂ := (Real.pi : ℂ)⁻¹
  let L : (ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) ℂ) →L[ℂ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) ℂ := a • 1
  have ht' := L.uniformContinuous.comp_tendstoUniformlyOn
    (inv_convolution_real_jets_uniformly_zero hg hc hs k ht (Z := Z))
  have hi (n : ℕ) : ContDiff ℝ ∞ (fun z : ℂ => ∫ w : ℂ, w⁻¹ • g n (z - w)) :=
    (hc n).contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
      CanonicalDimensionTwo.LocalDbar.locallyIntegrable_complex_inv (hg n)
  convert ht' using 1
  · funext n z
    rw [show (fun z : ℂ => (Real.pi : ℂ)⁻¹ * ∫ w : ℂ, w⁻¹ * g n (z - w)) =
      (fun z : ℂ => a • ∫ w : ℂ, w⁻¹ • g n (z - w)) from rfl]
    exact iteratedFDeriv_const_smul_apply' ((hi n).contDiffAt.of_le (by simp))
  · funext z
    exact (map_zero L).symm

end SameAtlasAnalyticCohomology.NormalFamilyTechnical

-- Private technical component preserved from CutoffJetConvergence.lean

open scoped ContDiff Topology
open Set Filter Metric

namespace SameAtlasAnalyticCohomology.NormalFamilyTechnical

private theorem cutoff_mul_contDiff
    {χ g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) : ContDiff ℝ ∞ (fun z => χ z * g z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport χ
  · exact hχ.contDiffAt.mul ((hg z (hs hz)).contDiffAt (hU.mem_nhds (hs hz)))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    simp only [Pi.zero_apply] at hw
    simp only [hw, zero_mul]

private theorem cutoff_mul_real_jets_uniformly_zero
    {χ : ℂ → ℂ} {g : ℕ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U)
    (hg : ∀ n, ContDiffOn ℝ ∞ (g n) U)
    (ht : ∀ k : ℕ, TendstoUniformlyOn (fun n => iteratedFDeriv ℝ k (g n))
      (fun _ => 0) atTop (tsupport χ)) (k : ℕ) :
    TendstoUniformly (fun n => iteratedFDeriv ℝ k (fun z => χ z * g n z))
      (fun _ => 0) atTop := by
  classical
  have hb : ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖iteratedFDeriv ℝ i χ z‖ ≤ B := by
    intro i
    obtain ⟨B, hB⟩ := (hc.iteratedFDeriv i).exists_bound_of_continuous
      ((hχ.iteratedFDeriv_right (m := 0) (by simp)).continuous)
    exact ⟨max 0 B, le_max_left _ _, fun z => (hB z).trans (le_max_right _ _)⟩
  choose B hB hbound using hb
  let C : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B i
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hB i)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  let δ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have he : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k + 1),
      ∀ z ∈ tsupport χ, ‖iteratedFDeriv ℝ (k - i) (g n) z‖ < δ := by
    apply (eventually_all_finset _).mpr
    intro i _
    simpa only [dist_zero_left] using (Metric.tendstoUniformlyOn_iff.mp (ht (k - i))) δ hδ
  filter_upwards [he] with n hn
  intro z
  rw [dist_zero_left]
  by_cases hz : z ∈ tsupport χ
  · have hp := norm_iteratedFDerivWithin_mul_le hχ.contDiffOn (hg n)
      (hU.uniqueDiffOn) (hs hz) (n := k) (by simp)
    simp only [iteratedFDerivWithin_of_isOpen _ hU (hs hz)] at hp
    have hb' : ‖iteratedFDeriv ℝ k (fun z => χ z * g n z) z‖ ≤ C * δ := by
      apply hp.trans
      dsimp only [C]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hbound i z) (Nat.cast_nonneg _)
      · exact (hn i hi z hz).le
      · exact norm_nonneg _
      · exact mul_nonneg (Nat.cast_nonneg _) (hB i)
    apply hb'.trans_lt
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < C + 1)).mpr
    nlinarith
  · have hp : z ∉ tsupport (fun w => χ w * g n w) :=
      fun hm => hz (tsupport_mul_subset_left hm)
    have hd : iteratedFDeriv ℝ k (fun w => χ w * g n w) z = 0 := by
      by_contra hm
      exact hp (support_iteratedFDeriv_subset k hm)
    simpa only [hd, norm_zero] using hε

end SameAtlasAnalyticCohomology.NormalFamilyTechnical

-- Private technical component preserved from HolomorphicCompactness.lean

open scoped Topology NNReal
open MeasureTheory Set Filter Metric
set_option linter.style.haveILetI false

namespace SameAtlasAnalyticCohomology.NormalFamilyTechnical

private theorem holomorphic_nested_disk_deriv_bound
    {f : ℂ → ℂ} {c : ℂ} {r R B : ℝ} (hgap : r < R)
    (hf : DifferentiableOn ℂ f (ball c R))
    (hbound : ∀ z ∈ ball c R, ‖f z‖ ≤ B)
    {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖deriv f z‖ ≤ B / ((R - r) / 2) := by
  have hδ : 0 < (R - r) / 2 := by linarith
  have hsub : closedBall z ((R - r) / 2) ⊆ ball c R := by
    intro w hw
    have hw' := (mem_closedBall.mp hw)
    have hz' := (mem_closedBall.mp hz)
    apply mem_ball.mpr
    exact (dist_triangle w z c).trans_lt (by linarith)
  rw [← Complex.cderiv_eq_deriv isOpen_ball hf hδ hsub]
  exact Complex.norm_cderiv_le hδ (fun w hw => hbound w (hsub (sphere_subset_closedBall hw)))

private theorem holomorphic_nested_disk_lipschitz
    {c : ℂ} {r R B : ℝ} (hgap : r < R) (hB : 0 ≤ B) :
    ∃ L : ℝ≥0, ∀ f : ℂ → ℂ,
      DifferentiableOn ℂ f (ball c R) →
      (∀ z ∈ ball c R, ‖f z‖ ≤ B) →
      LipschitzOnWith L f (closedBall c r) := by
  let L : ℝ≥0 := ⟨B / ((R - r) / 2), div_nonneg hB (by linarith)⟩
  refine ⟨L, ?_⟩
  intro f hf hb
  apply (convex_closedBall c r).lipschitzOnWith_of_nnnorm_deriv_le
  · intro z hz
    exact hf.differentiableAt (isOpen_ball.mem_nhds (closedBall_subset_ball hgap hz))
  · intro z hz
    exact holomorphic_nested_disk_deriv_bound hgap hf hb hz

private theorem compact_equicontinuous_subsequence
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : ℕ → C(X, ℂ)) {B : ℝ}
    (hb : ∀ n x, ‖f n x‖ ≤ B)
    (he : Equicontinuous (fun n x => f n x)) :
    ∃ F : C(X, ℂ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (f ∘ φ) atTop (𝓝 F) := by
  classical
  let g : ℕ → BoundedContinuousFunction X ℂ := fun n => BoundedContinuousFunction.mkOfCompact (f n)
  have hge : Equicontinuous ((↑) : Set.range g → X → ℂ) := by
    have h := he.comp (fun u : Set.range g => Classical.choose u.property)
    convert h using 1
    funext u x
    exact (congrArg (fun k : BoundedContinuousFunction X ℂ => k x) (Classical.choose_spec u.property)).symm
  have hcomp : IsCompact (closure (Set.range g)) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) B)
      (isCompact_closedBall _ _) (Set.range g)
      (by rintro h x ⟨n, rfl⟩; simpa only [mem_closedBall, dist_zero_right, g, BoundedContinuousFunction.mkOfCompact_apply] using hb n x)
      hge
  obtain ⟨G, _, φ, hφ, ht⟩ := hcomp.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨G.toContinuousMap, φ, hφ, ?_⟩
  apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp ht

private theorem holomorphic_nested_disk_subsequence
    {f : ℕ → ℂ → ℂ} {c : ℂ} {r R B : ℝ} (hgap : r < R) (hB : 0 ≤ B)
    (hf : ∀ n, DifferentiableOn ℂ (f n) (ball c R))
    (hb : ∀ n z, z ∈ ball c R → ‖f n z‖ ≤ B) :
    ∃ F : C(closedBall c r, ℂ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun n (z : closedBall c r) => f (φ n) z) F atTop := by
  letI : CompactSpace (closedBall c r) := isCompact_iff_compactSpace.mp (isCompact_closedBall c r)
  let g : ℕ → C(closedBall c r, ℂ) := fun n =>
    ⟨fun z => f n z,
      ((hf n).continuousOn.mono (closedBall_subset_ball hgap)).domRestrict⟩
  obtain ⟨L, hL⟩ := holomorphic_nested_disk_lipschitz (c := c) hgap hB
  have he : Equicontinuous (fun n (z : closedBall c r) => g n z) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ L
    intro n x y
    exact hL (f n) (hf n) (hb n) x.property y.property
  obtain ⟨F, φ, hφ, ht⟩ := compact_equicontinuous_subsequence g
    (fun n z => hb n z (closedBall_subset_ball hgap z.property)) he
  exact ⟨F, φ, hφ, ContinuousMap.tendsto_iff_tendstoUniformly.mp ht⟩

end SameAtlasAnalyticCohomology.NormalFamilyTechnical

-- Private technical component preserved from HolomorphicJetConvergence.lean

open scoped ContDiff Topology
open Set Filter

namespace SameAtlasAnalyticCohomology.NormalFamilyTechnical

private theorem holomorphic_iteratedDeriv_differentiableOn
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (k : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv k f) U := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv hU

private theorem holomorphic_locally_uniform_iteratedDeriv
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (ht : TendstoLocallyUniformlyOn f F atTop U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (f n))
      (iteratedDeriv k F) atTop U := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using ht
  | succ k ih =>
    simpa only [iteratedDeriv_succ, Function.comp_def] using
      ih.deriv (Eventually.of_forall fun n =>
        holomorphic_iteratedDeriv_differentiableOn hU (hf n) k) hU

private theorem holomorphic_locally_uniform_real_jets
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (ht : TendstoLocallyUniformlyOn f F atTop U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (f n))
      (iteratedFDeriv ℝ k F) atTop U := by
  let A : ℂ → ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) ℂ :=
    fun c => (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin k) ℂ c).restrictScalars ℝ
  let L : ContinuousMultilinearMap ℂ (fun _ : Fin k => ℂ) ℂ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) ℂ :=
    ContinuousMultilinearMap.restrictScalarsLinear ℝ
  have hA : UniformContinuous A :=
    L.uniformContinuous.comp
      (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin k) ℂ).isometry.uniformContinuous
  have hreal (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U) :
      EqOn (A ∘ iteratedDeriv k g) (iteratedFDeriv ℝ k g) U := by
    intro z hz
    have hs : ContDiffAt ℂ k g z := (hg.analyticAt (hU.mem_nhds hz)).contDiffAt
    have h := hs.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
    simpa only [iteratedFDeriv_eq_equiv_comp, Function.comp_apply, A] using h
  have h := hA.comp_tendstoLocallyUniformlyOn
    (holomorphic_locally_uniform_iteratedDeriv hU hf ht k)
  exact (h.congr (fun n => hreal (f n) (hf n))).congr_right
    (hreal F (ht.differentiableOn (Eventually.of_forall hf) hU))

private theorem local_small_dbar_correction
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {g : ℕ → ℂ → ℂ} (hg : ∀ n, ContDiffOn ℝ ∞ (g n) (ball c R))
    (ht : ∀ k : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (g n))
      (fun _ => 0) atTop (ball c R)) :
    ∃ u : ℕ → ℂ → ℂ, (∀ n, ContDiff ℝ ∞ (u n)) ∧
      (∀ n z, z ∈ closedBall c r → CanonicalDimensionTwo.LocalDbar.dbar (u n) z = g n z) ∧
      ∀ k : ℕ, ∀ Z : ℝ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (u n)) (fun _ => 0) atTop (closedBall (0 : ℂ) Z) := by
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  let b : ContDiffBump c := ⟨r, s, hr, hrs⟩
  let χ : ℂ → ℂ := fun z => (b z : ℂ)
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hcχ : HasCompactSupport χ := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hsχ : tsupport χ ⊆ ball c R := by
    apply (tsupport_comp_subset Complex.ofReal_zero b).trans
    rw [b.tsupport_eq]
    exact closedBall_subset_ball hsR
  let G : ℕ → ℂ → ℂ := fun n z => χ z * g n z
  have hG (n : ℕ) : ContDiff ℝ ∞ (G n) :=
    cutoff_mul_contDiff isOpen_ball hχ hsχ (hg n)
  have hcG (n : ℕ) : HasCompactSupport (G n) := hcχ.mul_right
  have hGt (k : ℕ) : TendstoUniformly (fun n => iteratedFDeriv ℝ k (G n))
      (fun _ => 0) atTop := by
    apply cutoff_mul_real_jets_uniformly_zero isOpen_ball hχ hcχ hsχ hg
    intro j
    exact (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp
      (ht j) (tsupport χ) hsχ hcχ
  obtain ⟨T, hT⟩ := hcχ.isBounded.exists_norm_le
  have hGs (n : ℕ) : Function.support (G n) ⊆ closedBall (0 : ℂ) T := by
    intro z hz
    apply mem_closedBall.mpr
    rw [dist_zero_right]
    apply hT z
    exact subset_closure (Function.support_mul_subset_left χ (g n) hz)
  let u : ℕ → ℂ → ℂ := fun n z =>
    (Real.pi : ℂ)⁻¹ * ∫ w : ℂ, w⁻¹ * G n (z - w)
  refine ⟨u, fun n => (CanonicalDimensionTwo.LocalDbar.compactCauchyTransform
    (G n) (hG n) (hcG n)).1, ?_, ?_⟩
  · intro n z hz
    rw [(CanonicalDimensionTwo.LocalDbar.compactCauchyTransform (G n) (hG n) (hcG n)).2]
    change (b z : ℂ) * g n z = g n z
    rw [b.one_of_mem_closedBall hz, Complex.ofReal_one, one_mul]
  · intro k Z
    exact normalized_cauchy_real_jets_uniformly_zero hG hcG hGs k (hGt k)

private theorem uniformly_zero_on_compact_bound
    {V : Type*} [NormedAddCommGroup V] {v : ℕ → ℂ → V}
    {K : Set ℂ} (hK : IsCompact K) (hv : ∀ n, ContinuousOn (v n) K)
    (ht : TendstoUniformlyOn v (fun _ => 0) atTop K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n z, z ∈ K → ‖v n z‖ ≤ B := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Vn : ℕ → C(K, V) := fun n => ⟨fun z => v n z, (hv n).domRestrict⟩
  have hVn : Tendsto Vn atTop (𝓝 0) :=
    ContinuousMap.tendsto_iff_tendstoUniformly.mpr
      (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp ht)
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto Vn hVn).exists_norm_le
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro n z hz
  exact ((Vn n).norm_coe_le_norm ⟨z, hz⟩).trans
    ((hB (Vn n) (Set.mem_range_self n)).trans (le_max_right _ _))

private theorem local_dbar_zero_complex_differentiable
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hz : CanonicalDimensionTwo.LocalDbar.dbar f z = 0) : DifferentiableAt ℂ f z := by
  rw [differentiableAt_complex_iff_differentiableAt_real]
  refine ⟨hf, ?_⟩
  have hz' : fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I = 0 := by
    simpa only [CanonicalDimensionTwo.LocalDbar.dbar, div_eq_zero_iff,
      OfNat.ofNat_ne_zero, or_false] using hz
  have he : Complex.I * fderiv ℝ f z 1 - fderiv ℝ f z Complex.I = 0 := by
    calc
      _ = Complex.I * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) := by
        rw [mul_add, ← mul_assoc, Complex.I_mul_I]
        ring
      _ = 0 := by rw [hz', mul_zero]
  exact (sub_eq_zero.mp he).symm

private theorem local_small_dbar_lipschitz
    {c : ℂ} {r R B : ℝ} (hr : 0 < r) (hrR : r < R) (hB : 0 ≤ B)
    {f g : ℕ → ℂ → ℂ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (ball c R))
    (hb : ∀ n z, z ∈ ball c R → ‖f n z‖ ≤ B)
    (hg : ∀ n, ContDiffOn ℝ ∞ (g n) (ball c R))
    (heq : ∀ n z, z ∈ ball c R → CanonicalDimensionTwo.LocalDbar.dbar (f n) z = g n z)
    (ht : ∀ k : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (g n))
      (fun _ => 0) atTop (ball c R)) :
    ∃ L : ℝ≥0, ∀ n, LipschitzOnWith L (f n) (closedBall c r) := by
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  obtain ⟨u, hu, hud, hut⟩ := local_small_dbar_correction (hr.trans hrs) hsR hg ht
  let Z : ℝ := ‖c‖ + s
  have hsub : closedBall c s ⊆ closedBall (0 : ℂ) Z := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    have hdist := mem_closedBall.mp hz
    calc
      ‖z‖ = ‖z - c + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ Z := by rw [← dist_eq_norm] at *; dsimp [Z]; linarith
  obtain ⟨C₀, hC₀, hbound₀⟩ := uniformly_zero_on_compact_bound
    (isCompact_closedBall (0 : ℂ) Z)
    (fun n => ((hu n).iteratedFDeriv_right (m := 0) (i := 0) (by simp)).continuous.continuousOn)
    (hut 0 Z)
  obtain ⟨C₁, hC₁, hbound₁⟩ := uniformly_zero_on_compact_bound
    (isCompact_closedBall (0 : ℂ) Z)
    (fun n => ((hu n).iteratedFDeriv_right (m := 0) (i := 1) (by simp)).continuous.continuousOn)
    (hut 1 Z)
  let h : ℕ → ℂ → ℂ := fun n z => f n z - u n z
  have hhol (n : ℕ) : DifferentiableOn ℂ (h n) (ball c s) := by
    intro z hz
    have hfz := ((hf n).contDiffAt (isOpen_ball.mem_nhds (ball_subset_ball hsR.le hz))).differentiableAt (by simp)
    have huz := (hu n).differentiable (by simp) z
    apply (local_dbar_zero_complex_differentiable (hfz.sub huz) ?_).differentiableWithinAt
    have hsubd : CanonicalDimensionTwo.LocalDbar.dbar (h n) z =
        CanonicalDimensionTwo.LocalDbar.dbar (f n) z - CanonicalDimensionTwo.LocalDbar.dbar (u n) z := by
      simp only [h, CanonicalDimensionTwo.LocalDbar.dbar, fderiv_fun_sub hfz huz,
        sub_apply]
      ring
    change CanonicalDimensionTwo.LocalDbar.dbar (h n) z = 0
    rw [hsubd, heq n z (ball_subset_ball hsR.le hz), hud n z (ball_subset_closedBall hz), sub_self]
  obtain ⟨L, hL⟩ := holomorphic_nested_disk_lipschitz (c := c) hrs (add_nonneg hB hC₀)
  refine ⟨L + ⟨C₁, hC₁⟩, fun n => ?_⟩
  have hLh : LipschitzOnWith L (h n) (closedBall c r) := hL (h n) (hhol n) (by
    intro z hz
    exact (norm_sub_le _ _).trans (add_le_add (hb n z (ball_subset_ball hsR.le hz))
      (by simpa only [norm_iteratedFDeriv_zero] using hbound₀ n z (hsub (ball_subset_closedBall hz)))))
  have hLu : LipschitzOnWith ⟨C₁, hC₁⟩ (u n) (closedBall c r) := by
    apply (convex_closedBall c r).lipschitzOnWith_of_nnnorm_fderiv_le
      (𝕜 := ℝ) (fun z _ => (hu n).differentiable (by simp) z)
    intro z hz
    exact (show ‖fderiv ℝ (u n) z‖ ≤ C₁ by
      simpa only [norm_iteratedFDeriv_one] using
        hbound₁ n z (hsub (closedBall_subset_closedBall hrs.le hz)))
  convert hLh.add hLu using 1
  ext z
  exact (sub_add_cancel (f n z) (u n z)).symm

private theorem local_small_dbar_uniform_limit_real_jets
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {f g : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (ball c R))
    (hg : ∀ n, ContDiffOn ℝ ∞ (g n) (ball c R))
    (heq : ∀ n z, z ∈ ball c R → CanonicalDimensionTwo.LocalDbar.dbar (f n) z = g n z)
    (ht : ∀ k : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (g n))
      (fun _ => 0) atTop (ball c R))
    (hft : TendstoLocallyUniformlyOn f F atTop (ball c R)) :
    DifferentiableOn ℂ F (ball c r) ∧
      ∀ k : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (f n))
        (iteratedFDeriv ℝ k F) atTop (ball c r) := by
  obtain ⟨u, hu, hud, hut⟩ := local_small_dbar_correction hr hrR hg ht
  have hsub : ball c r ⊆ closedBall (0 : ℂ) (‖c‖ + r) := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖z‖ = ‖z - c + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ‖c‖ + r := by have := mem_ball.mp hz; rw [dist_eq_norm] at this; linarith
  have hut' (k : ℕ) : TendstoLocallyUniformlyOn
      (fun n => iteratedFDeriv ℝ k (u n)) (fun _ => 0) atTop (ball c r) :=
    ((hut k (‖c‖ + r)).mono hsub).tendstoLocallyUniformlyOn
  have hut₀ : TendstoUniformlyOn u (fun _ => 0) atTop (ball c r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h := Metric.tendstoUniformlyOn_iff.mp ((hut 0 (‖c‖ + r)).mono hsub) ε hε
    simpa only [dist_zero_left, norm_iteratedFDeriv_zero] using h
  let h : ℕ → ℂ → ℂ := fun n z => f n z - u n z
  have hhol (n : ℕ) : DifferentiableOn ℂ (h n) (ball c r) := by
    intro z hz
    have hfz := ((hf n).contDiffAt (isOpen_ball.mem_nhds (ball_subset_ball hrR.le hz))).differentiableAt (by simp)
    have huz := (hu n).differentiable (by simp) z
    apply (local_dbar_zero_complex_differentiable (hfz.sub huz) ?_).differentiableWithinAt
    have hsubd : CanonicalDimensionTwo.LocalDbar.dbar (f n - u n) z =
        CanonicalDimensionTwo.LocalDbar.dbar (f n) z - CanonicalDimensionTwo.LocalDbar.dbar (u n) z := by
      simp only [CanonicalDimensionTwo.LocalDbar.dbar, fderiv_sub hfz huz, sub_apply]
      ring
    rw [hsubd, heq n z (ball_subset_ball hrR.le hz), hud n z (ball_subset_closedBall hz), sub_self]
  have hht : TendstoLocallyUniformlyOn h F atTop (ball c r) := by
    simpa only [Pi.sub_def, sub_zero, h] using
      (hft.mono (ball_subset_ball hrR.le)).sub hut₀.tendstoLocallyUniformlyOn
  refine ⟨hht.differentiableOn (Eventually.of_forall hhol) isOpen_ball, ?_⟩
  intro k
  have hj := holomorphic_locally_uniform_real_jets isOpen_ball hhol hht k
  have hj' := hj.add (hut' k)
  have hc := hj'.congr (fun n z hz => show
      iteratedFDeriv ℝ k (h n) z + iteratedFDeriv ℝ k (u n) z =
        iteratedFDeriv ℝ k (f n) z from by
    rw [show h n = f n - u n from rfl,
      iteratedFDeriv_sub_apply
        (((hf n).contDiffAt (isOpen_ball.mem_nhds (ball_subset_ball hrR.le hz))).of_le (by simp))
        ((hu n).contDiffAt.of_le (by simp)), sub_add_cancel])
  simpa only [Pi.add_def, add_zero] using hc

end SameAtlasAnalyticCohomology.NormalFamilyTechnical

namespace SameAtlasAnalyticCohomology
open NormalFamilyTechnical
universe w
variable {X : Type w} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ∞ X]

private theorem form_tendsto_zero_chart_jets
    {α : ℕ → SmoothZeroOne X} (ht : Tendsto α atTop (𝓝 0)) (a : X) (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun n => iteratedFDeriv ℝ k (fun z : ℂ => (α n).1 a ((extChartAt 𝓘(ℂ) a).symm z)))
      (fun _ => 0) atTop (extChartAt 𝓘(ℂ) a).target := by
  letI : LocallyCompactSpace (ChartTarget a) := (isOpen_extChartAt_target a).locallyCompactSpace
  have hc : Continuous (smoothZeroOneJet a k : SmoothZeroOne X → C(ChartTarget a, RealJet k)) := by
    have h : Continuous (fun α : SmoothZeroOne X => fun (a : X) (k : ℕ) =>
        smoothZeroOneJet a k α) := continuous_induced_dom
    exact (continuous_apply k).comp ((continuous_apply a).comp h)
  have hj := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
    ((hc.tendsto 0).comp ht)
  apply tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr
  have hzero : (smoothZeroOneJet a k (0 : SmoothZeroOne X)) = 0 := by
    apply ContinuousMap.ext
    intro z
    change iteratedFDeriv ℝ k (fun _ : ℂ => (0 : ℂ)) z.1 = 0
    simp
  rw [hzero] at hj
  exact hj

private theorem dbar_chart_coefficient
    (f : SmoothZero X) (a : X) {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ) a).target) :
    CanonicalDimensionTwo.LocalDbar.dbar (fun w : ℂ => f.1 ((extChartAt 𝓘(ℂ) a).symm w)) z =
      (dolbeaultDbar f).1 a ((extChartAt 𝓘(ℂ) a).symm z) := by
  simp only [dolbeaultDbar, LinearMap.coe_mk, AddHom.coe_mk,
    ite_eq_left ((extChartAt 𝓘(ℂ) a).map_target hz), chartDbar,
    (extChartAt 𝓘(ℂ) a).right_inv hz, CanonicalDimensionTwo.LocalDbar.dbar]

private theorem small_dbar_chart_lipschitz
    {f : ℕ → SmoothZero X} (hb : ∀ n x, ‖(f n).1 x‖ ≤ 1)
    (ht : Tendsto (fun n => dolbeaultDbar (f n)) atTop (𝓝 0))
    (a : X) {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hR : ball c R ⊆ (extChartAt 𝓘(ℂ) a).target) :
    ∃ L : ℝ≥0, ∀ n, LipschitzOnWith L
      (fun z : ℂ => (f n).1 ((extChartAt 𝓘(ℂ) a).symm z)) (closedBall c r) := by
  apply local_small_dbar_lipschitz hr hrR zero_le_one
    (fun n => ((f n).property a).mono hR) (fun n z _ => hb n _)
    (fun n => ((dolbeaultDbar (f n)).property.2.1 a).mono hR)
    (fun n z hz => dbar_chart_coefficient (f n) a (hR hz))
  intro k
  exact (form_tendsto_zero_chart_jets ht a k).mono hR

private theorem small_dbar_equicontinuous
    {f : ℕ → SmoothZero X} (hb : ∀ n x, ‖(f n).1 x‖ ≤ 1)
    (ht : Tendsto (fun n => dolbeaultDbar (f n)) atTop (𝓝 0)) :
    Equicontinuous (fun n x => (f n).1 x) := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  let c := (extChartAt 𝓘(ℂ) x) x
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target x).mem_nhds
      ((extChartAt 𝓘(ℂ) x).map_source (mem_extChartAt_source x)))
  obtain ⟨L, hL⟩ := small_dbar_chart_lipschitz hb ht x
    (half_pos hR) (by linarith : R / 2 < R) hsub
  let δ := min (R / 2) (ε / ((L : ℝ) + 1))
  have hδ : 0 < δ := lt_min (half_pos hR) (div_pos hε (by positivity))
  have hnear : ∀ᶠ y in 𝓝 x, (extChartAt 𝓘(ℂ) x) y ∈ ball c δ :=
    (continuousAt_extChartAt' (I := 𝓘(ℂ)) (mem_extChartAt_source x))
      (Metric.ball_mem_nhds c hδ)
  filter_upwards [hnear, (isOpen_extChartAt_source (I := 𝓘(ℂ)) x).mem_nhds
    (mem_extChartAt_source x)] with y hy hys
  intro n
  have hy' : dist ((extChartAt 𝓘(ℂ) x) y) c < δ := mem_ball.mp hy
  have hc : c ∈ closedBall c (R / 2) := mem_closedBall_self (half_pos hR).le
  have hyball : (extChartAt 𝓘(ℂ) x) y ∈ closedBall c (R / 2) :=
    mem_closedBall.mpr (hy'.le.trans (min_le_left _ _))
  have hh := (hL n).dist_le_mul c hc ((extChartAt 𝓘(ℂ) x) y) hyball
  simp only [c, (extChartAt 𝓘(ℂ) x).left_inv (mem_extChartAt_source x),
    (extChartAt 𝓘(ℂ) x).left_inv hys] at hh
  apply hh.trans_lt
  have hdist : dist ((extChartAt 𝓘(ℂ) x) x) ((extChartAt 𝓘(ℂ) x) y) <
      ε / ((L : ℝ) + 1) := by
    rw [dist_comm]
    exact hy'.trans_le (min_le_right _ _)
  have hLnon : 0 ≤ (L : ℝ) := L.property
  have hdiv : (L : ℝ) * (ε / ((L : ℝ) + 1)) < ε := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < (L : ℝ) + 1)).mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_left hdist.le hLnon).trans_lt hdiv

end SameAtlasAnalyticCohomology

namespace SameAtlasAnalyticCohomology.NormalFamilyTechnical

private theorem small_dbar_uniform_limit_on_open
    {U : Set ℂ} (hU : IsOpen U) {f g : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (hg : ∀ n, ContDiffOn ℝ ∞ (g n) U)
    (heq : ∀ n z, z ∈ U → CanonicalDimensionTwo.LocalDbar.dbar (f n) z = g n z)
    (ht : ∀ k : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (g n))
      (fun _ => 0) atTop U)
    (hft : TendstoLocallyUniformlyOn f F atTop U) :
    DifferentiableOn ℂ F U ∧
      ∀ k : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (f n))
        (iteratedFDeriv ℝ k F) atTop U := by
  have hlocal (z : ℂ) (hz : z ∈ U) : ∃ r : ℝ, 0 < r ∧
      DifferentiableOn ℂ F (ball z r) ∧
      ∀ k : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (f n))
        (iteratedFDeriv ℝ k F) atTop (ball z r) := by
    obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
    refine ⟨R / 2, half_pos hR, ?_⟩
    exact local_small_dbar_uniform_limit_real_jets (half_pos hR) (by linarith)
      (fun n => (hf n).mono hsub) (fun n => (hg n).mono hsub)
      (fun n w hw => heq n w (hsub hw)) (fun k => (ht k).mono hsub) (hft.mono hsub)
  constructor
  · intro z hz
    obtain ⟨r, hr, hd, _⟩ := hlocal z hz
    exact (hd.differentiableAt (ball_mem_nhds z hr)).differentiableWithinAt
  · intro k
    apply hU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
    intro z hz
    obtain ⟨r, hr, _, ht'⟩ := hlocal z hz
    exact isOpen_ball.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp
      (ht' k) z (mem_ball_self hr)

end SameAtlasAnalyticCohomology.NormalFamilyTechnical

namespace SameAtlasAnalyticCohomology
open NormalFamilyTechnical
universe w
variable {X : Type w} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ∞ X]

private theorem actual_small_dbar_uniform_limit
    {f : ℕ → SmoothZero X} {F : X → ℂ}
    (ht : Tendsto (fun n => dolbeaultDbar (f n)) atTop (𝓝 0))
    (hft : TendstoUniformly (fun n x => (f n).1 x) F atTop) :
    ∃ G : SmoothZero X, G.1 = F ∧ Tendsto f atTop (𝓝 G) := by
  have hcharts (a : X) :
      DifferentiableOn ℂ (fun z : ℂ => F ((extChartAt 𝓘(ℂ) a).symm z))
        (extChartAt 𝓘(ℂ) a).target ∧
      ∀ k : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z : ℂ => (f n).1 ((extChartAt 𝓘(ℂ) a).symm z)))
        (iteratedFDeriv ℝ k (fun z : ℂ => F ((extChartAt 𝓘(ℂ) a).symm z)))
        atTop (extChartAt 𝓘(ℂ) a).target := by
    apply small_dbar_uniform_limit_on_open (isOpen_extChartAt_target a)
      (fun n => (f n).property a)
      (fun n => (dolbeaultDbar (f n)).property.2.1 a)
      (fun n z hz => dbar_chart_coefficient (f n) a hz)
      (form_tendsto_zero_chart_jets ht a)
    exact (hft.comp ((extChartAt 𝓘(ℂ) a).symm)).tendstoLocallyUniformly.tendstoLocallyUniformlyOn
  let G : SmoothZero X := ⟨F, fun a =>
    ((hcharts a).1.contDiffOn (isOpen_extChartAt_target a)).restrict_scalars ℝ⟩
  refine ⟨G, rfl, ?_⟩
  apply (Topology.IsInducing.induced
    (fun G : SmoothZero X => fun (a : X) (k : ℕ) => smoothZeroJet a k G)).tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro k
  letI : LocallyCompactSpace (ChartTarget a) := (isOpen_extChartAt_target a).locallyCompactSpace
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp ((hcharts a).2 k)

private theorem actualDbarSmallNormalFamily : ClosedImageReview.ActualDbarSmallNormalFamilyStatement := by
  intro X _ _ _ _ _ _ _ f hb ht
  have he : Equicontinuous (fun n x => (f n).1 x) := small_dbar_equicontinuous hb ht
  obtain ⟨F, φ, hφ, hft⟩ := compact_equicontinuous_subsequence
    (fun n => smoothZeroToContinuous (f n)) hb he
  have hft' : TendstoUniformly (fun n x => (f (φ n)).1 x) F atTop :=
    ContinuousMap.tendsto_iff_tendstoUniformly.mp hft
  obtain ⟨G, _, hG⟩ := actual_small_dbar_uniform_limit (ht.comp hφ.tendsto_atTop) hft'
  exact ⟨G, φ, hφ, hG⟩

end SameAtlasAnalyticCohomology

namespace SameAtlasAnalyticCohomology
open NormalFamilyTechnical
universe w
variable {X : Type w} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ∞ X] [T2Space X] [CompactSpace X] [Nonempty X]
  [PreconnectedSpace X]

private theorem normalized_bounded_small_dbar_tendsto_zero
    (p : X) {f : ℕ → SmoothZero X}
    (hp : ∀ n, (f n).1 p = 0) (hb : ∀ n x, ‖(f n).1 x‖ ≤ 1)
    (hd : Tendsto (fun n => dolbeaultDbar (f n)) atTop (𝓝 0)) :
    Tendsto (fun n => smoothZeroToContinuous (f n)) atTop (𝓝 0) := by
  letI : T2Space (SmoothZeroOne X) := smoothZeroOne_t2
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨F, φ, hφ, hF⟩ := actualDbarSmallNormalFamily X
    (fun n => f (ns n)) (fun n x => hb (ns n) x) (hd.comp hns)
  have hFp : F.1 p = 0 := normalized_limit_preserves_basepoint p hF
    (Eventually.of_forall fun n => hp (ns (φ n)))
  have hFd : dolbeaultDbar F = 0 := tendsto_nhds_unique
    (dolbeaultDbar_continuous.continuousAt.tendsto.comp hF)
    ((hd.comp hns).comp hφ.tendsto_atTop)
  have hFzero : F = 0 := normalized_zero_chartDbar_eq_zero p F hFp
    ((dolbeaultDbar_eq_zero_iff_chartDbar_eq_zero F).mp hFd)
  refine ⟨φ, ?_⟩
  have hh := smoothZeroToContinuous_continuous.continuousAt.tendsto.comp hF
  simpa only [hFzero, map_zero, Function.comp_def] using hh

end SameAtlasAnalyticCohomology

namespace SameAtlasAnalyticCohomology
open NormalFamilyTechnical
universe w
variable {X : Type w} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ∞ X] [T2Space X] [CompactSpace X] [Nonempty X]
  [PreconnectedSpace X]

private theorem unit_interval_smul_tendsto_zero
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y]
    [ContinuousSMul ℂ Y] {r : ℕ → ℝ} {v : ℕ → Y}
    (hr : ∀ n, r n ∈ Icc (0 : ℝ) 1) (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun n => (r n : ℂ) • v n) atTop (𝓝 0) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨c, _, φ, hφ, hc⟩ := isCompact_Icc.tendsto_subseq (fun n => hr (ns n))
  refine ⟨φ, ?_⟩
  have ht := (Complex.continuous_ofReal.continuousAt.tendsto.comp hc).smul
    ((hv.comp hns).comp hφ.tendsto_atTop)
  simpa only [smul_zero, Function.comp_def] using ht

private theorem normalized_small_dbar_tendsto_zero
    (p : X) {f : ℕ → SmoothZero X} (hp : ∀ n, (f n).1 p = 0)
    (hd : Tendsto (fun n => dolbeaultDbar (f n)) atTop (𝓝 0)) :
    Tendsto (fun n => smoothZeroToContinuous (f n)) atTop (𝓝 0) := by
  let M : ℕ → ℝ := fun n => max ‖smoothZeroToContinuous (f n)‖ 1
  have hM (n : ℕ) : 1 ≤ M n := le_max_right _ _
  have hMpos (n : ℕ) : 0 < M n := lt_of_lt_of_le zero_lt_one (hM n)
  let r : ℕ → ℝ := fun n => (M n)⁻¹
  have hr (n : ℕ) : r n ∈ Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr (hMpos n).le, inv_le_one_of_one_le₀ (hM n)⟩
  let g : ℕ → SmoothZero X := fun n => (r n : ℂ) • f n
  have hgp (n : ℕ) : (g n).1 p = 0 := by simp [g, hp n]
  have hgb (n : ℕ) (x : X) : ‖(g n).1 x‖ ≤ 1 := by
    change ‖(r n : ℂ) • (f n).1 x‖ ≤ 1
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr n).1]
    calc
      r n * ‖(f n).1 x‖ ≤ r n * M n :=
        mul_le_mul_of_nonneg_left ((compact_smoothZero_norm_bounds (f n) x).trans (le_max_left _ _)) (hr n).1
      _ = 1 := inv_mul_cancel₀ (hMpos n).ne'
  have hgd : Tendsto (fun n => dolbeaultDbar (g n)) atTop (𝓝 0) := by
    simpa only [g, map_smul] using unit_interval_smul_tendsto_zero hr hd
  have hgt := normalized_bounded_small_dbar_tendsto_zero p hgp hgb hgd
  have hgnorm (n : ℕ) : ‖smoothZeroToContinuous (g n)‖ = r n * ‖smoothZeroToContinuous (f n)‖ := by
    change ‖smoothZeroToContinuous ((r n : ℂ) • f n)‖ = _
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr n).1]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall := Metric.tendsto_nhds.mp hgt (min ε (1 / 2)) (lt_min hε (by norm_num))
  filter_upwards [hsmall] with n hn
  rw [dist_zero_right] at hn ⊢
  rw [hgnorm n] at hn
  have hnorm : ‖smoothZeroToContinuous (f n)‖ < 1 := by
    by_contra h
    have hm : M n = ‖smoothZeroToContinuous (f n)‖ := max_eq_left (not_lt.mp h)
    have hv : r n * ‖smoothZeroToContinuous (f n)‖ = 1 := by
      rw [← hm]
      exact inv_mul_cancel₀ (hMpos n).ne'
    rw [hv] at hn
    have := hn.trans_le (min_le_right ε (1 / 2))
    norm_num at this
  have hm : M n = 1 := max_eq_right hnorm.le
  have hrone : r n = 1 := by simp only [r, hm, inv_one]
  rw [hrone, one_mul] at hn
  exact hn.trans_le (min_le_left _ _)

end SameAtlasAnalyticCohomology

namespace SameAtlasAnalyticCohomology
open NormalFamilyTechnical
universe w
variable {X : Type w} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ∞ X] [T2Space X] [CompactSpace X] [Nonempty X]
  [PreconnectedSpace X]

private theorem normalized_convergent_dbar_cauchy
    (p : X) {f : ℕ → SmoothZero X} {α : SmoothZeroOne X}
    (hp : ∀ n, (f n).1 p = 0)
    (hd : Tendsto (fun n => dolbeaultDbar (f n)) atTop (𝓝 α)) :
    CauchySeq (fun n => smoothZeroToContinuous (f n)) := by
  by_contra hnot
  rw [Metric.cauchySeq_iff] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hbad⟩ := hnot
  choose m hm n hn hdist using hbad
  have hmt : Tendsto m atTop atTop := tendsto_atTop_mono hm tendsto_id
  have hnt : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  let g : ℕ → SmoothZero X := fun j => f (m j) - f (n j)
  have hgp (j : ℕ) : (g j).1 p = 0 := by simp [g, hp]
  have hgd : Tendsto (fun j => dolbeaultDbar (g j)) atTop (𝓝 0) := by
    simpa only [g, map_sub, sub_self, Function.comp_def] using
      (hd.comp hmt).sub (hd.comp hnt)
  have ht := normalized_small_dbar_tendsto_zero p hgp hgd
  have hsmall := Metric.tendsto_nhds.mp ht ε hε
  obtain ⟨j, hj⟩ := hsmall.exists
  have hc : ‖smoothZeroToContinuous (g j)‖ < ε := by simpa only [dist_zero_right] using hj
  have hdist' : ε ≤ ‖smoothZeroToContinuous (g j)‖ := by
    simpa only [g, map_sub, dist_eq_norm] using hdist j
  exact (not_lt_of_ge hdist') hc

end SameAtlasAnalyticCohomology

namespace SameAtlasAnalyticCohomology.NormalFamilyTechnical

private theorem compact_inner_dbar_solution
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) {g : ℂ → ℂ}
    (hg : ContDiffOn ℝ ∞ g (ball c R)) :
    ∃ v : ℂ → ℂ, ContDiff ℝ ∞ v ∧
      ∀ z ∈ closedBall c r, CanonicalDimensionTwo.LocalDbar.dbar v z = g z := by
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  let b : ContDiffBump c := ⟨r, s, hr, hrs⟩
  let χ : ℂ → ℂ := fun z => (b z : ℂ)
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hcχ : HasCompactSupport χ := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hsχ : tsupport χ ⊆ ball c R := by
    apply (tsupport_comp_subset Complex.ofReal_zero b).trans
    rw [b.tsupport_eq]
    exact closedBall_subset_ball hsR
  let G : ℂ → ℂ := fun z => χ z * g z
  have hG : ContDiff ℝ ∞ G := cutoff_mul_contDiff isOpen_ball hχ hsχ hg
  obtain ⟨hvs, hvd⟩ := CanonicalDimensionTwo.LocalDbar.compactCauchyTransform G hG hcχ.mul_right
  refine ⟨_, hvs, ?_⟩
  intro z hz
  rw [hvd]
  change (b z : ℂ) * g z = g z
  rw [b.one_of_mem_closedBall hz, Complex.ofReal_one, one_mul]

private theorem smooth_local_dbar_limit
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {f g : ℕ → ℂ → ℂ} {F g₀ : ℂ → ℂ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (ball c R))
    (hg : ∀ n, ContDiffOn ℝ ∞ (g n) (ball c R))
    (hg₀ : ContDiffOn ℝ ∞ g₀ (ball c R))
    (heq : ∀ n z, z ∈ ball c R → CanonicalDimensionTwo.LocalDbar.dbar (f n) z = g n z)
    (ht : ∀ k : ℕ, TendstoLocallyUniformlyOn
      (fun n => iteratedFDeriv ℝ k (fun z => g n z - g₀ z))
      (fun _ => 0) atTop (ball c R))
    (hft : TendstoLocallyUniformlyOn f F atTop (ball c R)) :
    ContDiffOn ℝ ∞ F (ball c r) ∧
      ∀ k : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (f n))
        (iteratedFDeriv ℝ k F) atTop (ball c r) := by
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  obtain ⟨v, hvs, hvd⟩ := compact_inner_dbar_solution (hr.trans hrs) hsR hg₀
  let H : ℕ → ℂ → ℂ := fun n z => f n z - v z
  let G : ℕ → ℂ → ℂ := fun n z => g n z - g₀ z
  have hH (n : ℕ) : ContDiffOn ℝ ∞ (H n) (ball c s) :=
    ((hf n).mono (ball_subset_ball hsR.le)).sub hvs.contDiffOn
  have hG (n : ℕ) : ContDiffOn ℝ ∞ (G n) (ball c s) :=
    ((hg n).sub hg₀).mono (ball_subset_ball hsR.le)
  have hHd (n : ℕ) (z : ℂ) (hz : z ∈ ball c s) :
      CanonicalDimensionTwo.LocalDbar.dbar (H n) z = G n z := by
    have hfz := ((hf n).contDiffAt (isOpen_ball.mem_nhds
      (ball_subset_ball hsR.le hz))).differentiableAt (by simp)
    have hvz := hvs.differentiable (by simp) z
    have hd : CanonicalDimensionTwo.LocalDbar.dbar (H n) z =
        CanonicalDimensionTwo.LocalDbar.dbar (f n) z - CanonicalDimensionTwo.LocalDbar.dbar v z := by
      simp only [H, CanonicalDimensionTwo.LocalDbar.dbar, fderiv_fun_sub hfz hvz, sub_apply]
      ring
    rw [hd, heq n z (ball_subset_ball hsR.le hz), hvd z (ball_subset_closedBall hz)]
  have hvconst : TendstoLocallyUniformlyOn (fun _ : ℕ => v) v atTop (ball c s) := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun n z _ => by simpa only [dist_self] using hε
  have hHt : TendstoLocallyUniformlyOn H (fun z => F z - v z) atTop (ball c s) :=
    (hft.mono (ball_subset_ball hsR.le)).sub hvconst
  obtain ⟨hFH, htH⟩ := local_small_dbar_uniform_limit_real_jets hr hrs hH hG hHd
    (fun k => (ht k).mono (ball_subset_ball hsR.le)) hHt
  have hFs : ContDiffOn ℝ ∞ (fun z => F z - v z) (ball c r) :=
    (hFH.contDiffOn isOpen_ball).restrict_scalars ℝ
  have hF : ContDiffOn ℝ ∞ F (ball c r) :=
    (hFs.add hvs.contDiffOn).congr (fun z _ => (sub_add_cancel (F z) (v z)).symm)
  refine ⟨hF, ?_⟩
  intro k
  have hvk : TendstoLocallyUniformlyOn (fun _ : ℕ => iteratedFDeriv ℝ k v)
      (iteratedFDeriv ℝ k v) atTop (ball c r) := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun n z _ => by simpa only [dist_self] using hε
  have hsum := (htH k).add hvk
  have hsubjet (a b : ℂ → ℂ) {z : ℂ} (ha : ContDiffAt ℝ ∞ a z)
      (hb : ContDiffAt ℝ ∞ b z) :
      iteratedFDeriv ℝ k (fun w => a w - b w) z + iteratedFDeriv ℝ k b z =
        iteratedFDeriv ℝ k a z := by
    change iteratedFDeriv ℝ k (a - b) z + iteratedFDeriv ℝ k b z = _
    rw [iteratedFDeriv_sub_apply (ha.of_le (by simp)) (hb.of_le (by simp)), sub_add_cancel]
  exact (hsum.congr (fun n z hz => hsubjet (f n) v
    ((hf n).contDiffAt (isOpen_ball.mem_nhds (ball_subset_ball hrR.le hz))) hvs.contDiffAt)).congr_right
      (fun z hz => hsubjet F v (hF.contDiffAt (isOpen_ball.mem_nhds hz)) hvs.contDiffAt)

end SameAtlasAnalyticCohomology.NormalFamilyTechnical

namespace SameAtlasAnalyticCohomology
open NormalFamilyTechnical
universe w
variable {X : Type w} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ∞ X]

private theorem actual_convergent_dbar_uniform_limit
    {f : ℕ → SmoothZero X} {F : X → ℂ} {α : SmoothZeroOne X}
    (ht : Tendsto (fun n => dolbeaultDbar (f n)) atTop (𝓝 α))
    (hft : TendstoUniformly (fun n x => (f n).1 x) F atTop) :
    ∃ G : SmoothZero X, G.1 = F ∧ Tendsto f atTop (𝓝 G) := by
  have hd : Tendsto (fun n => dolbeaultDbar (f n) - α) atTop (𝓝 0) := by
    simpa only [sub_self] using ht.sub_const α
  have hlocal (a : X) (z : ℂ) (hz : z ∈ (extChartAt 𝓘(ℂ) a).target) :
      ∃ r : ℝ, 0 < r ∧
        ContDiffOn ℝ ∞ (fun w : ℂ => F ((extChartAt 𝓘(ℂ) a).symm w)) (ball z r) ∧
        ∀ k : ℕ, TendstoLocallyUniformlyOn
          (fun n => iteratedFDeriv ℝ k (fun w : ℂ => (f n).1 ((extChartAt 𝓘(ℂ) a).symm w)))
          (iteratedFDeriv ℝ k (fun w : ℂ => F ((extChartAt 𝓘(ℂ) a).symm w)))
          atTop (ball z r) := by
    obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_extChartAt_target a).mem_nhds hz)
    refine ⟨R / 2, half_pos hR, ?_⟩
    apply smooth_local_dbar_limit (half_pos hR) (by linarith : R / 2 < R)
      (fun n => ((f n).property a).mono hsub)
      (fun n => ((dolbeaultDbar (f n)).property.2.1 a).mono hsub)
      ((α.property.2.1 a).mono hsub)
      (fun n w hw => dbar_chart_coefficient (f n) a (hsub hw))
    · intro k
      exact (form_tendsto_zero_chart_jets hd a k).mono hsub
    · exact (hft.comp ((extChartAt 𝓘(ℂ) a).symm)).tendstoLocallyUniformly.tendstoLocallyUniformlyOn
  have hFs (a : X) : ContDiffOn ℝ ∞
      (fun w : ℂ => F ((extChartAt 𝓘(ℂ) a).symm w)) (extChartAt 𝓘(ℂ) a).target := by
    intro z hz
    obtain ⟨r, hr, hs, _⟩ := hlocal a z hz
    exact (hs.contDiffAt (ball_mem_nhds z hr)).contDiffWithinAt
  let G : SmoothZero X := ⟨F, hFs⟩
  refine ⟨G, rfl, ?_⟩
  apply (Topology.IsInducing.induced
    (fun G : SmoothZero X => fun (a : X) (k : ℕ) => smoothZeroJet a k G)).tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro k
  letI : LocallyCompactSpace (ChartTarget a) := (isOpen_extChartAt_target a).locallyCompactSpace
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  apply tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp
  apply (isOpen_extChartAt_target a).tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro z hz
  obtain ⟨r, hr, _, ht'⟩ := hlocal a z hz
  exact isOpen_ball.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp (ht' k) z (mem_ball_self hr)

private theorem actual_dbar_range_seqClosed
    [T2Space X] [CompactSpace X] [Nonempty X] [PreconnectedSpace X] :
    IsSeqClosed ((dolbeaultDbar (E := X)).range : Set (SmoothZeroOne X)) := by
  intro α β hα hβ
  choose f hf using hα
  let p : X := Classical.choice inferInstance
  let g : ℕ → SmoothZero X := fun n => normalizeAt p (f n)
  have hgp (n : ℕ) : (g n).1 p = 0 := normalizeAt_basepoint p (f n)
  have hgd : Tendsto (fun n => dolbeaultDbar (g n)) atTop (𝓝 β) := by
    simpa only [g, dolbeaultDbar_normalizeAt, hf] using hβ
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete (normalized_convergent_dbar_cauchy p hgp hgd)
  obtain ⟨G, _, hG⟩ := actual_convergent_dbar_uniform_limit hgd
    (ContinuousMap.tendsto_iff_tendstoUniformly.mp hF)
  exact range_mem_of_primitive_limit hG hgd

end SameAtlasAnalyticCohomology

namespace SameAtlasAnalyticCohomology
universe w
variable {X : Type w} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ∞ X]

private theorem actual_dbar_range_isClosed_of_firstCountable
    [T2Space X] [CompactSpace X] [Nonempty X] [PreconnectedSpace X]
    [FirstCountableTopology (SmoothZeroOne X)] :
    IsClosed ((dolbeaultDbar (E := X)).range : Set (SmoothZeroOne X)) :=
  actual_dbar_range_seqClosed.isClosed

end SameAtlasAnalyticCohomology

open TopologicalSpace
open scoped Manifold ContDiff Bundle

namespace SameAtlasAnalyticCohomology
universe u v
variable {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]

/-- McMullen 8.10's closed-image argument, in the actual jet topology. -/
theorem dolbeaultDbar_range_isClosed
    [T2Space E] [CompactSpace E] [Nonempty E] [PreconnectedSpace E] :
    IsClosed ((dolbeaultDbar (E := E)).range : Set (SmoothZeroOne E)) := by
  letI : FirstCountableTopology (SmoothZeroOne E) :=
    smoothZeroOne_firstCountableTopology (E := E)
  exact actual_dbar_range_isClosed_of_firstCountable

end SameAtlasAnalyticCohomology
