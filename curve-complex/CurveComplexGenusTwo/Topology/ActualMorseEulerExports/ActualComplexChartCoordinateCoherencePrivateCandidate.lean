import CurveComplexGenusTwo.Topology.LocalOrientation.LocalReflectionGerm
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseCircleFundamentalCycle
import CurveComplexGenusTwo.CWHurewicz.ConnectingNaturality
import CurveComplexGenusTwo.Topology.Orientation.SurfaceTopHomologyDetection
import CurveComplexGenusTwo.Topology.Orientation.SurfaceLocalization
import Mathlib.Topology.Connected.Clopen
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCircleSourceWindingTransport
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualCircleMapWindingHomotopySourceReviewRequest
import CurveComplexGenusTwo.Octagon.GraphMV.UnconditionalGraphAssembly
import CurveComplexGenusTwo.Octagon.OctagonRepresentativeScaffold
import CurveComplexGenusTwo.Topology.ActualGenusTwoRecognition.OriginalClosedOrientableRecognitionNamedProofV1
import CurveComplexGenusTwo.Topology.ActualClosedOrientableHomology.OriginalClosedOrientableParameterExclusionProof
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Analysis.Analytic.Order
import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.IsolatedInvolutionStrictDerivativeNegative
import Mathlib.Topology.Separation.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
open scoped Manifold ContDiff Bundle
open Bundle Filter Topology Set Metric CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
private theorem actual_chart_transition_analytic_derivative {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (q r : E) (hr : q ∈ (chartAt ℂ r).source) :
    AnalyticAt ℂ (fun z => (chartAt ℂ r) ((chartAt ℂ q).symm z)) ((chartAt ℂ q) q) ∧
      deriv (fun z => (chartAt ℂ r) ((chartAt ℂ q).symm z)) ((chartAt ℂ q) q) ≠ 0 := by
  let c := chartAt ℂ q
  let d := chartAt ℂ r
  let G : ℂ → ℂ := fun z => d (c.symm z)
  let H : ℂ → ℂ := fun z => c (d.symm z)
  have hq : q ∈ c.source := mem_chart_source ℂ q
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ c q :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hq
  have hd : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ d q :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas r) hr
  have hci : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ c.symm (c q) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) (c.map_source hq)
  have hdi : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ d.symm (d q) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas r) (d.map_source hr)
  have hG : ContDiffAt ℂ 1 G (c q) :=
    ((hd.comp_of_eq hci (c.left_inv hq)).contDiffAt).of_le (by simp)
  have hH : ContDiffAt ℂ 1 H (d q) :=
    ((hc.comp_of_eq hdi (d.left_inv hr)).contDiffAt).of_le (by simp)
  have hGa : AnalyticAt ℂ G (c q) := by
    obtain ⟨U, hU, hqU, hcont⟩ := hG.contDiffOn' le_rfl (by simp)
    have hdiff : DifferentiableOn ℂ G U := by
      apply ContDiffOn.differentiableOn _ one_ne_zero
      simpa only [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] using hcont
    exact hdiff.analyticAt (hU.mem_nhds hqU)
  have hG0 : G (c q) = d q := by simp only [G, c.left_inv hq]
  have ht : Tendsto c.symm (𝓝 (c q)) (𝓝 q) := by
    simpa only [c.left_inv hq] using (c.symm.continuousAt (c.map_source hq)).tendsto
  have hcomp : (fun z => H (G z)) =ᶠ[𝓝 (c q)] id := by
    filter_upwards [ht.eventually (d.open_source.mem_nhds hr),
      c.open_target.mem_nhds (c.map_source hq)] with z hz hzt
    dsimp only [H, G, id]
    rw [d.left_inv hz, c.right_inv hzt]
  have hdH : HasDerivAt H (deriv H (d q)) (G (c q)) := by
    rw [hG0]
    exact (hH.differentiableAt one_ne_zero).hasDerivAt
  have hder : HasDerivAt (fun z => H (G z))
      (deriv H (d q) * deriv G (c q)) (c q) :=
    hdH.comp (c q) (hG.differentiableAt one_ne_zero).hasDerivAt
  have hone : deriv H (d q) * deriv G (c q) = 1 := by
    exact hder.deriv.symm.trans (hcomp.deriv_eq.trans (by simp))
  refine ⟨hGa, ?_⟩
  intro hzero
  rw [hzero, mul_zero] at hone
  exact zero_ne_one hone

private theorem radial_unit_homotopy (g : ℂ → ℂ) (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (hg : ∀ z ∈ closedBall z₀ ρ, ContinuousAt g z ∧ g z ≠ 0) :
    ∃ H : C(unitInterval × Circle, ℂ),
      (∀ p, H p ≠ 0) ∧
      (∀ z : Circle, H (0, z) = (z : ℂ) ^ n * g (z₀ + (ρ : ℂ) * z)) ∧
      (∀ z : Circle, H (1, z) = (z : ℂ) ^ n * g z₀) := by
  let R : unitInterval × Circle → ℂ :=
    fun p => z₀ + (((1 - (p.1 : ℝ)) * ρ : ℝ) : ℂ) * (p.2 : ℂ)
  have hR : Continuous R := by dsimp [R]; fun_prop
  have hRmem (p : unitInterval × Circle) : R p ∈ closedBall z₀ ρ := by
    rw [mem_closedBall, dist_eq_norm]
    dsimp [R]
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr p.1.2.2) hρ.le)]
    nlinarith [p.1.2.1, p.1.2.2]
  have hgR : Continuous (fun p => g (R p)) :=
    continuous_iff_continuousAt.mpr (fun p => (hg (R p) (hRmem p)).1.comp hR.continuousAt)
  let H : C(unitInterval × Circle, ℂ) :=
    ⟨fun p => (p.2 : ℂ) ^ n * g (R p),
      (show Continuous (fun p : unitInterval × Circle => (p.2 : ℂ) ^ n) from by fun_prop).mul hgR⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro p
    exact mul_ne_zero (pow_ne_zero n p.2.coe_ne_zero) (hg (R p) (hRmem p)).2
  · intro z
    simp [H, R]
  · intro z
    simp [H, R]

private theorem normalized_radial_homotopy (g : ℂ → ℂ) (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (hg : ∀ z ∈ closedBall z₀ ρ, ContinuousAt g z ∧ g z ≠ 0) :
    ∃ H : C(unitInterval × Circle, Circle),
      (∀ z : Circle, (H (0, z) : ℂ) =
        ((z : ℂ) ^ n * g (z₀ + (ρ : ℂ) * z)) /
          (‖(z : ℂ) ^ n * g (z₀ + (ρ : ℂ) * z)‖ : ℂ)) ∧
      (∀ z : Circle, (H (1, z) : ℂ) =
        (z : ℂ) ^ n * (g z₀ / (‖g z₀‖ : ℂ))) := by
  obtain ⟨F, hFne, hF0, hF1⟩ := radial_unit_homotopy g z₀ ρ hρ n hg
  have hnorm (p : unitInterval × Circle) : (‖F p‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (hFne p)
  have hunit (p : unitInterval × Circle) :
      F p / (‖F p‖ : ℂ) ∈ Submonoid.unitSphere ℂ := by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact div_self (norm_ne_zero_iff.mpr (hFne p))
  let H : C(unitInterval × Circle, Circle) :=
    ⟨fun p => ⟨F p / (‖F p‖ : ℂ), hunit p⟩,
      Continuous.subtype_mk (F.continuous.div
        (Complex.continuous_ofReal.comp F.continuous.norm) hnorm) hunit⟩
  refine ⟨H, ?_, ?_⟩
  · intro z
    change F (0, z) / (‖F (0, z)‖ : ℂ) = _
    rw [hF0]
  · intro z
    change F (1, z) / (‖F (1, z)‖ : ℂ) = _
    rw [hF1, norm_mul, norm_pow, Circle.norm_coe, one_pow, one_mul]
    exact mul_div_assoc _ _ _

private theorem power_loop_homotopy (g : ℂ → ℂ) (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (hg : ∀ z ∈ closedBall z₀ ρ, ContinuousAt g z ∧ g z ≠ 0) :
    ∃ H : C(unitInterval × Circle, Circle),
      (∀ z : Circle, (H (0, z) : ℂ) =
        ((z : ℂ) ^ n * g (z₀ + (ρ : ℂ) * z)) /
          (‖(z : ℂ) ^ n * g (z₀ + (ρ : ℂ) * z)‖ : ℂ)) ∧
      (∀ z : Circle, H (1, z) = z ^ n) := by
  obtain ⟨H, hH0, hH1⟩ := normalized_radial_homotopy g z₀ ρ hρ n hg
  have hg0 : g z₀ ≠ 0 := (hg z₀ (mem_closedBall_self hρ.le)).2
  let u : Circle := ⟨g z₀ / (‖g z₀‖ : ℂ), (by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact div_self (norm_ne_zero_iff.mpr hg0))⟩
  let f₀ : C(Circle, Circle) := ⟨fun z => H (0, z),
    H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let f₁ : C(Circle, Circle) := ⟨fun z => z ^ n * u, by fun_prop⟩
  let f₂ : C(Circle, Circle) := ⟨fun z => z ^ n, by fun_prop⟩
  let HH : ContinuousMap.Homotopy f₀ f₁ :=
    { toContinuousMap := H
      map_zero_left := by intro z; rfl
      map_one_left := by
        intro z
        apply Circle.ext
        exact hH1 z }
  let K : ContinuousMap.Homotopy f₁ f₂ :=
    { toFun := fun p => p.2 ^ n * Circle.exp ((1 - (p.1 : ℝ)) * Complex.arg (u : ℂ))
      continuous_toFun := by fun_prop
      map_zero_left := by intro z; simp [f₁, Circle.exp_arg]
      map_one_left := by intro z; simp [f₂] }
  refine ⟨(HH.trans K).toContinuousMap, ?_, ?_⟩
  · intro z
    change ((HH.trans K) (0, z) : ℂ) = _
    rw [ContinuousMap.Homotopy.apply_zero]
    exact hH0 z
  · intro z
    exact ContinuousMap.Homotopy.apply_one (HH.trans K) z

private theorem normalize_positive_scale (c : ℝ) (hc : 0 < c) (w : ℂ) :
    ((c : ℂ) * w) / (‖(c : ℂ) * w‖ : ℂ) = w / (‖w‖ : ℂ) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, Complex.ofReal_mul]
  apply mul_div_mul_left
  exact_mod_cast hc.ne'


private theorem actual_literal_complex_chart_transition_positive_boundary_model
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (q r : E)
    (hr : q ∈ (chartAt ℂ r).source) (R : ℝ) (hR : 0 < R) :
    let c := chartAt ℂ q;
    let d := chartAt ℂ r;
    let G : ℂ → ℂ := fun z => d (c.symm z);
    ∃ (ρ : ℝ) (H : C(unitInterval × Circle,Circle)),
      0 < ρ ∧ ρ < R ∧
      closedBall (c q) ρ ⊆ c.target ∧
      (∀ z ∈ closedBall (c q) ρ, c.symm z ∈ d.source) ∧
      (∀ z : Circle, G (c q+(ρ:ℂ)*z) ≠ d q) ∧
      (∀ z : Circle, (H (0,z):ℂ) =
        (G (c q+(ρ:ℂ)*z)-d q)/(‖G (c q+(ρ:ℂ)*z)-d q‖:ℂ)) ∧
      (∀ z : Circle, H (1,z) = z) := by
  dsimp only
  let c := chartAt ℂ q
  let d := chartAt ℂ r
  let G : ℂ → ℂ := fun z => d (c.symm z)
  let z₀ := c q
  obtain ⟨hGa,hGder⟩ := actual_chart_transition_analytic_derivative q r hr
  have hG0 : G z₀ = d q := by
    dsimp [G,z₀];rw [c.left_inv (mem_chart_source ℂ q)]
  have ha : AnalyticAt ℂ (fun z => G z-G z₀) z₀ := hGa.sub analyticAt_const
  have horder : analyticOrderAt (fun z => G z-G z₀) z₀ = (1:ℕ) :=
    hGa.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hGder
  obtain ⟨u,hu,hune,hfactor⟩ := ha.analyticOrderAt_eq_natCast.mp horder
  have ht : Tendsto c.symm (𝓝 z₀) (𝓝 q) := by
    simpa only [z₀,c.left_inv (mem_chart_source ℂ q)] using
      (c.symm.continuousAt (c.map_source (mem_chart_source ℂ q))).tendsto
  have hev : ∀ᶠ z in 𝓝 z₀, ContinuousAt u z ∧ u z ≠ 0 ∧
      G z-d q = (z-z₀)*u z ∧ z ∈ c.target ∧ c.symm z ∈ d.source := by
    filter_upwards [hu.eventually_continuousAt,hu.continuousAt.eventually_ne hune,
      hfactor,c.open_target.mem_nhds (c.map_source (mem_chart_source ℂ q)),
      ht.eventually (d.open_source.mem_nhds hr)] with z hc hn hf hzt hzd
    refine ⟨hc,hn,?_,hzt,hzd⟩
    simpa only [hG0,pow_one,smul_eq_mul] using hf
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  let ρ := min ε R / 2
  have hρ : 0 < ρ := half_pos (lt_min hε hR)
  have hρε : ρ < ε := by
    have hm := min_le_left ε R
    dsimp [ρ];linarith [lt_min hε hR]
  have hρR : ρ < R := by
    have hm := min_le_right ε R
    dsimp [ρ];linarith [lt_min hε hR]
  have hdata : ∀ z ∈ closedBall z₀ ρ,
      ContinuousAt u z ∧ u z ≠ 0 ∧ G z-d q = (z-z₀)*u z ∧
      z ∈ c.target ∧ c.symm z ∈ d.source := by
    intro z hz
    exact hball z (closedBall_subset_ball hρε hz)
  obtain ⟨H,hH0,hH1⟩ := power_loop_homotopy u z₀ ρ hρ 1
    (fun z hz => ⟨(hdata z hz).1,(hdata z hz).2.1⟩)
  have hcircle (z : Circle) : z₀+(ρ:ℂ)*z ∈ closedBall z₀ ρ := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ,Circle.norm_coe,mul_one]
  have hvalue (z : Circle) : G (z₀+(ρ:ℂ)*z)-d q =
      (ρ:ℂ)*((z:ℂ)*u (z₀+(ρ:ℂ)*z)) := by
    rw [(hdata _ (hcircle z)).2.2.1,add_sub_cancel_left,mul_assoc]
  refine ⟨ρ,H,hρ,hρR,fun z hz => (hdata z hz).2.2.2.1,
    fun z hz => (hdata z hz).2.2.2.2,?_,?_,?_⟩
  · intro z
    apply sub_ne_zero.mp
    rw [hvalue]
    exact mul_ne_zero (by exact_mod_cast hρ.ne')
      (mul_ne_zero (by exact Circle.coe_ne_zero z) (hdata _ (hcircle z)).2.1)
  · intro z
    rw [hvalue,normalize_positive_scale ρ hρ]
    simpa only [pow_one] using hH0 z
  · intro z
    simpa only [pow_one] using hH1 z

private theorem actual_literal_complex_chart_transition_boundary_h1_identity
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (q r : E)
    (hr : q ∈ (chartAt ℂ r).source) (R : ℝ) (hR : 0 < R) :
    let c := chartAt ℂ q;
    let d := chartAt ℂ r;
    ∃ (ρ : ℝ) (f : C(Circle,Circle)), 0 < ρ ∧ ρ < R ∧
      closedBall (c q) ρ ⊆ c.target ∧
      (∀ z ∈ closedBall (c q) ρ, c.symm z ∈ d.source) ∧
      (∀ z : Circle, d (c.symm (c q+(ρ:ℂ)*z)) ≠ d q) ∧
      (∀ z : Circle, (f z:ℂ) =
        (d (c.symm (c q+(ρ:ℂ)*z))-d q)/
          (‖d (c.symm (c q+(ρ:ℂ)*z))-d q‖:ℂ)) ∧
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f))
          CircleFundamentalCycle.fundamentalClass = CircleFundamentalCycle.fundamentalClass := by
  dsimp only
  obtain ⟨ρ,H,hρ,hρR,hct,hds,hne,hH0,hH1⟩ :=
    actual_literal_complex_chart_transition_positive_boundary_model q r hr R hR
  let f : C(Circle,Circle) := ⟨fun z => H (0,z),
    H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let HH : ContinuousMap.Homotopy f (ContinuousMap.id Circle) := {
    toContinuousMap := H
    map_zero_left := fun z => rfl
    map_one_left := hH1 }
  refine ⟨ρ,f,hρ,hρR,hct,hds,hne,hH0,?_⟩
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  have HT : TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom (ContinuousMap.id Circle)) := HH
  have he := HT.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) 1
  change F.map (TopCat.ofHom f) = F.map (TopCat.ofHom (ContinuousMap.id Circle)) at he
  have hid : TopCat.ofHom (ContinuousMap.id Circle) = 𝟙 (TopCat.of Circle) := rfl
  rw [hid,F.map_id] at he
  rw [he]
  rfl

private theorem actual_centered_complex_puncture_circle_coordinate
    (z₀ : ℂ) :
    ∃ N : C(({z₀}ᶜ : Set ℂ),Circle),
      (∀ x, (N x:ℂ) = (x.val-z₀)/(‖x.val-z₀‖:ℂ)) ∧
      IsIso ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom N))) := by
  let P : Set ℂ := {z₀}ᶜ
  have hi (y : ReflectionRadial.Punctured ℂ) : y.val+z₀ ∈ P := by
    intro heq
    change y.val+z₀=z₀ at heq
    have hz : y.val=0 := by linear_combination heq
    exact y.property hz
  let e : P ≃ₜ ReflectionRadial.Punctured ℂ := {
    toFun := fun x => ⟨x.val-z₀,sub_ne_zero.mpr x.property⟩
    invFun := fun y => ⟨y.val+z₀,hi y⟩
    left_inv := by intro x; apply Subtype.ext; simp
    right_inv := by intro x; apply Subtype.ext; simp
    continuous_toFun := (continuous_subtype_val.sub continuous_const).subtype_mk _
    continuous_invFun := (continuous_subtype_val.add continuous_const).subtype_mk hi }
  let N := ReflectionRadial.circleRetraction.comp (⟨e,e.continuous⟩ : C(P,ReflectionRadial.Punctured ℂ))
  refine ⟨N,?_,?_⟩
  · intro x
    change NormedSpace.normalize (x.val-z₀) = (x.val-z₀)/(‖x.val-z₀‖:ℂ)
    simp only [NormedSpace.normalize,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]
  · let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)
    haveI : IsIso (F.map (TopCat.ofHom ReflectionRadial.circleRetraction)) :=
      (ReflectionRadial.circlePuncturedIso 1).isIso_hom
    have heq : TopCat.ofHom (⟨e,e.continuous⟩ : C(P,ReflectionRadial.Punctured ℂ)) =
        (TopCat.isoOfHomeo e).hom := rfl
    haveI : IsIso (F.map (TopCat.ofHom (⟨e,e.continuous⟩ : C(P,ReflectionRadial.Punctured ℂ)))) := by
      rw [heq];infer_instance
    change IsIso (F.map (TopCat.ofHom N))
    change IsIso (F.map (TopCat.ofHom (⟨e,e.continuous⟩ : C(P,ReflectionRadial.Punctured ℂ)) ≫
      TopCat.ofHom ReflectionRadial.circleRetraction))
    rw [F.map_comp]
    infer_instance

private theorem actual_complex_plane_point_connecting_isIso (z₀ : ℂ) :
    IsIso (CurveComplexGenusTwo.CWHurewicz.relativeConnecting ℂ ({z₀}ᶜ) 1) := by
  open CurveComplexGenusTwo.CWHurewicz in
  have hz₁ : IsZero (H ℂ 1) :=
    CircleHomologyComputation.contractible_positive_homology ℂ 1 (by omega)
  open CurveComplexGenusTwo.CWHurewicz in
  have hz₂ : IsZero (H ℂ 2) :=
    CircleHomologyComputation.contractible_positive_homology ℂ 2 (by omega)
  open CurveComplexGenusTwo.CWHurewicz in
  obtain ⟨_,hex₂⟩ := pairHomology_exact_at_relative ℂ ({z₀}ᶜ) 1
  open CurveComplexGenusTwo.CWHurewicz in
  obtain ⟨_,hex₁⟩ := pairHomology_exact_at_subspace ℂ ({z₀}ᶜ) 1
  haveI : Mono (CurveComplexGenusTwo.CWHurewicz.relativeConnecting ℂ ({z₀}ᶜ) 1) :=
    hex₂.mono_g (hz₂.eq_of_src _ _)
  haveI : Epi (CurveComplexGenusTwo.CWHurewicz.relativeConnecting ℂ ({z₀}ᶜ) 1) :=
    hex₁.epi_f (hz₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

private theorem actual_literal_complex_closed_disc_relative_cap_class
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    let D := closedBall z₀ ρ;
    let B : Set D := {x | dist x.val z₀ = ρ};
    ∃ γ : C(Circle,B),
      (∀ z, ((γ z).val.val : ℂ) = z₀+(ρ:ℂ)*z) ∧
      ∃ r : relativeHomology D B 2,
        relativeConnecting D B 1 r =
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ)) CircleFundamentalCycle.fundamentalClass := by
  let D := closedBall z₀ ρ
  let B : Set D := {x | dist x.val z₀ = ρ}
  have hnorm (z : Circle) : dist (z₀+(ρ:ℂ)*z) z₀ = ρ := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hρ,Circle.norm_coe,mul_one]
  have hD (z : Circle) : z₀+(ρ:ℂ)*z ∈ D := by rw [mem_closedBall,hnorm]
  let γ₀ : C(Circle,D) :=
    ⟨fun z => ⟨z₀+(ρ:ℂ)*z,hD z⟩,
      (show Continuous (fun z : Circle => z₀+(ρ:ℂ)*z) from by fun_prop).subtype_mk hD⟩
  let γ : C(Circle,B) :=
    ⟨fun z => ⟨γ₀ z,hnorm z⟩, γ₀.continuous.subtype_mk (fun z => hnorm z)⟩
  refine ⟨γ,fun z => rfl,?_⟩
  letI : Nonempty D := ⟨⟨z₀,mem_closedBall_self hρ.le⟩⟩
  letI : ContractibleSpace D := (convex_closedBall z₀ ρ).contractibleSpace ⟨z₀,mem_closedBall_self hρ.le⟩
  have hz : IsZero (H D 1) := CircleHomologyComputation.contractible_positive_homology D 1 (by omega)
  let c : H B 1 :=
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ)) CircleFundamentalCycle.fundamentalClass
  have hcz : homologyInclusion D B 1 c = 0 := by
    letI : Subsingleton (H D 1) := ModuleCat.subsingleton_of_isZero hz
    exact Subsingleton.elim _ _
  obtain ⟨_,hexact⟩ := pairHomology_exact_at_subspace D B 1
  exact (ShortComplex.moduleCat_exact_iff _).mp hexact c hcz


private theorem actual_literal_scaled_circle_boundary_surjective
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (γ : C(Circle, {x : closedBall z₀ ρ | dist x.val z₀ = ρ}))
    (hγ : ∀ z, (γ z).val.val = z₀+(ρ:ℂ)*z) : Function.Surjective γ := by
  intro d
  have hnorm : ‖d.val.val-z₀‖ = ρ := by
    have hd : dist d.val.val z₀ = ρ := d.property
    simpa only [dist_eq_norm] using hd
  have hρc : (ρ:ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hunit : (d.val.val-z₀)/(ρ:ℂ) ∈ Submonoid.unitSphere ℂ := by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,hnorm,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ,div_self hρ.ne']
  let z : Circle := ⟨(d.val.val-z₀)/(ρ:ℂ),hunit⟩
  refine ⟨z,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rw [hγ]
  change z₀+(ρ:ℂ)*((d.val.val-z₀)/(ρ:ℂ))=d.val.val
  field_simp
  <;> ring


private theorem actual_literal_complex_chart_transition_normalized_cap_orientation
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (q r : E)
    (hr : q ∈ (chartAt ℂ r).source) (R : ℝ) (hR : 0 < R) :
    let c := chartAt ℂ q;
    let d := chartAt ℂ r;
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧
      closedBall (c q) ρ ⊆ c.target ∧
      (∀ z ∈ closedBall (c q) ρ, c.symm z ∈ d.source) ∧
      let D := closedBall (c q) ρ;
      let B : Set D := {x | dist x.val (c q) = ρ};
      ∃ (G : C(D,ℂ)) (hpair : ∀ x ∈ B, G x ∈ ({d q}ᶜ : Set ℂ))
        (γ : C(Circle,B)) (rD : relativeHomology D B 2)
        (N : C(({d q}ᶜ : Set ℂ),Circle)),
        (∀ z, G z = d (c.symm z.val)) ∧
        (∀ z, (γ z).val.val = c q+(ρ:ℂ)*z) ∧
        relativeConnecting D B 1 rD =
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ)) CircleFundamentalCycle.fundamentalClass ∧
        (∀ x, (N x:ℂ) = (x.val-d q)/(‖x.val-d q‖:ℂ)) ∧
        IsIso (relativeConnecting ℂ ({d q}ᶜ) 1 ≫
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom N))) ∧
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom N))
            (relativeConnecting ℂ ({d q}ᶜ) 1
              (pairRelativeHomologyMap B ({d q}ᶜ) G hpair 2 rD)) =
                CircleFundamentalCycle.fundamentalClass := by
  dsimp only
  let c := chartAt ℂ q
  let d := chartAt ℂ r
  obtain ⟨ρ,f,hρ,hρR,hct,hds,hne,hf,hfH1⟩ :=
    actual_literal_complex_chart_transition_boundary_h1_identity q r hr R hR
  refine ⟨ρ,hρ,hρR,hct,hds,?_⟩
  let D := closedBall (c q) ρ
  let B : Set D := {x | dist x.val (c q) = ρ}
  let Cq : C(D,E) := ⟨fun x => c.symm x.val,
    c.symm.continuousOn.comp_continuous continuous_subtype_val (fun x => hct x.property)⟩
  let G : C(D,ℂ) := ⟨fun x => d (Cq x),
    d.continuousOn.comp_continuous Cq.continuous (fun x => hds x.val x.property)⟩
  obtain ⟨γ,hγ,rD,hδD⟩ := actual_literal_complex_closed_disc_relative_cap_class (c q) ρ hρ
  have hpair : ∀ x ∈ B, G x ∈ ({d q}ᶜ : Set ℂ) := by
    intro x hx
    obtain ⟨z,hz⟩ := actual_literal_scaled_circle_boundary_surjective (c q) ρ hρ γ hγ ⟨x,hx⟩
    have he := congrArg (fun x => x.val.val) hz
    rw [hγ] at he
    change d (c.symm x.val) ≠ d q
    rw [← he]
    exact hne z
  obtain ⟨N,hN,hNiso⟩ := actual_centered_complex_puncture_circle_coordinate (d q)
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  haveI : IsIso (F.map (TopCat.ofHom N)) := hNiso
  haveI : IsIso (relativeConnecting ℂ ({d q}ᶜ) 1) :=
    actual_complex_plane_point_connecting_isIso (d q)
  refine ⟨G,hpair,γ,rD,N,fun z => rfl,hγ,hδD,hN,inferInstance,?_⟩
  have hcomp : TopCat.ofHom γ ≫ pairMapOnSubspace B ({d q}ᶜ) G hpair ≫
      TopCat.ofHom N = TopCat.ofHom f := by
    ext z
    change (N ⟨G (γ z).val,hpair (γ z).val (γ z).property⟩ : ℂ) = (f z:ℂ)
    rw [hN]
    change (d (c.symm (γ z).val.val)-d q)/
      (‖d (c.symm (γ z).val.val)-d q‖:ℂ) = (f z:ℂ)
    rw [hγ]
    exact (hf z).symm
  have hmaps : F.map (TopCat.ofHom N)
      (F.map (pairMapOnSubspace B ({d q}ᶜ) G hpair)
        (F.map (TopCat.ofHom γ) CircleFundamentalCycle.fundamentalClass)) =
      CircleFundamentalCycle.fundamentalClass := by
    change (F.map (TopCat.ofHom γ) ≫
      F.map (pairMapOnSubspace B ({d q}ᶜ) G hpair) ≫ F.map (TopCat.ofHom N))
        CircleFundamentalCycle.fundamentalClass = _
    rw [← F.map_comp,← F.map_comp,hcomp]
    exact hfH1
  have hn := congrArg (fun m => m rD) (relativeConnecting_natural B ({d q}ᶜ) G hpair 1)
  change F.map (pairMapOnSubspace B ({d q}ᶜ) G hpair) (relativeConnecting D B 1 rD) =
    relativeConnecting ℂ ({d q}ᶜ) 1 (pairRelativeHomologyMap B ({d q}ᶜ) G hpair 2 rD) at hn
  rw [hδD] at hn
  rw [← hn]
  exact hmaps

private theorem actual_literal_disc_boundary_moving_interior_point_positive_homotopy
    (c w : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hw : dist w c < ρ) :
    ∃ H : C(unitInterval × Circle,Circle),
      (∀ z : Circle, (H (0,z):ℂ) =
        (c+(ρ:ℂ)*z-w)/(‖c+(ρ:ℂ)*z-w‖:ℂ)) ∧
      (∀ z : Circle, H (1,z) = z) := by
  have hcw : ‖c-w‖ < ρ := by simpa only [dist_eq_norm,norm_sub_rev] using hw
  let F : C(unitInterval × Circle,ℂ) :=
    ⟨fun p => (1-(p.1:ℝ)) • (c-w)+(ρ:ℂ)*p.2,by fun_prop⟩
  have hne (p : unitInterval × Circle) : F p ≠ 0 := by
    intro hz
    have heq : (ρ:ℂ)*(p.2:ℂ) = -((1-(p.1:ℝ)) • (c-w)) := by
      exact eq_neg_of_add_eq_zero_right hz
    have he := congrArg norm heq
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ,
      Circle.norm_coe,mul_one,norm_neg,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (by linarith [p.1.property.2])] at he
    have ht₀ := p.1.property.1
    have hmul : (1-(p.1:ℝ))*‖c-w‖ ≤ ‖c-w‖ := by
      nlinarith [norm_nonneg (c-w)]
    linarith
  have hunit (p : unitInterval × Circle) : F p/(‖F p‖:ℂ) ∈ Submonoid.unitSphere ℂ := by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm,
      div_self (norm_ne_zero_iff.mpr (hne p))]
  let H : C(unitInterval × Circle,Circle) :=
    ⟨fun p => ⟨F p/(‖F p‖:ℂ),hunit p⟩,
      (F.continuous.div (Complex.continuous_ofReal.comp F.continuous.norm)
        (fun p => by
          change (‖F p‖:ℂ) ≠ 0
          exact_mod_cast norm_ne_zero_iff.mpr (hne p))).subtype_mk hunit⟩
  refine ⟨H,?_,?_⟩
  · intro z
    change F (0,z)/(‖F (0,z)‖:ℂ) = _
    have hF0 : F (0,z) = c+(ρ:ℂ)*z-w := by
      change (1-(0:ℝ)) • (c-w)+(ρ:ℂ)*z = c+(ρ:ℂ)*z-w
      simp only [sub_zero,one_smul]
      ring
    rw [hF0]
  · intro z
    apply Subtype.ext
    change F (1,z)/(‖F (1,z)‖:ℂ) = (z:ℂ)
    have hF1 : F (1,z) = (ρ:ℂ)*z := by simp [F]
    rw [hF1,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ,
      Circle.norm_coe,mul_one]
    have hρc : (ρ:ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    field_simp [hρc]

private theorem actual_literal_disc_boundary_moving_interior_point_h1_identity
    (c w : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hw : dist w c < ρ) :
    ∃ f : C(Circle,Circle),
      (∀ z : Circle, (f z:ℂ) = (c+(ρ:ℂ)*z-w)/(‖c+(ρ:ℂ)*z-w‖:ℂ)) ∧
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f))
          CircleFundamentalCycle.fundamentalClass = CircleFundamentalCycle.fundamentalClass := by
  obtain ⟨H,hH0,hH1⟩ := actual_literal_disc_boundary_moving_interior_point_positive_homotopy c w ρ hρ hw
  let f : C(Circle,Circle) := ⟨fun z => H (0,z),
    H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let HH : ContinuousMap.Homotopy f (ContinuousMap.id Circle) := {
    toContinuousMap := H
    map_zero_left := fun z => rfl
    map_one_left := hH1 }
  have HT : TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom (ContinuousMap.id Circle)) := HH
  refine ⟨f,hH0,?_⟩
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)
  have he := HT.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) 1
  change F.map (TopCat.ofHom f) = F.map (TopCat.ofHom (ContinuousMap.id Circle)) at he
  have hid : TopCat.ofHom (ContinuousMap.id Circle) = 𝟙 (TopCat.of Circle) := rfl
  rw [hid,F.map_id] at he
  rw [he]
  rfl

private theorem actual_literal_normalized_disc_cap_all_interior_points_positive
    (c w : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hw : dist w c < ρ) :
    let D := closedBall c ρ;
    let B : Set D := {x | dist x.val c = ρ};
    ∀ (γ : C(Circle,B)) (hγ : ∀ z, (γ z).val.val = c+(ρ:ℂ)*z)
      (rD : relativeHomology D B 2)
      (hr : relativeConnecting D B 1 rD =
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ)) CircleFundamentalCycle.fundamentalClass),
      ∃ (hpair : ∀ x ∈ B, (⟨Subtype.val,continuous_subtype_val⟩ : C(D,ℂ)) x ∈ ({w}ᶜ : Set ℂ))
        (N : C(({w}ᶜ : Set ℂ),Circle)),
        (∀ x, (N x:ℂ) = (x.val-w)/(‖x.val-w‖:ℂ)) ∧
        IsIso (relativeConnecting ℂ ({w}ᶜ) 1 ≫
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom N))) ∧
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom N))
            (relativeConnecting ℂ ({w}ᶜ) 1
              (pairRelativeHomologyMap B ({w}ᶜ) ⟨Subtype.val,continuous_subtype_val⟩ hpair 2 rD)) =
                CircleFundamentalCycle.fundamentalClass := by
  dsimp only
  let D := closedBall c ρ
  let B : Set D := {x | dist x.val c = ρ}
  intro γ hγ rD hr
  let G : C(D,ℂ) := ⟨Subtype.val,continuous_subtype_val⟩
  have hpair : ∀ x ∈ B, G x ∈ ({w}ᶜ : Set ℂ) := by
    intro x hx heq
    change x.val = w at heq
    have hd : dist x.val c = ρ := hx
    rw [heq] at hd
    exact (ne_of_lt hw) hd
  obtain ⟨N,hN,hNiso⟩ := actual_centered_complex_puncture_circle_coordinate w
  obtain ⟨f,hf,hfH1⟩ := actual_literal_disc_boundary_moving_interior_point_h1_identity c w ρ hρ hw
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)
  haveI : IsIso (F.map (TopCat.ofHom N)) := hNiso
  haveI : IsIso (relativeConnecting ℂ ({w}ᶜ) 1) := actual_complex_plane_point_connecting_isIso w
  refine ⟨hpair,N,hN,inferInstance,?_⟩
  have hcomp : TopCat.ofHom γ ≫ pairMapOnSubspace B ({w}ᶜ) G hpair ≫ TopCat.ofHom N =
      TopCat.ofHom f := by
    ext z
    change (N ⟨(γ z).val.val,hpair (γ z).val (γ z).property⟩ : ℂ) = (f z:ℂ)
    rw [hN,hγ]
    exact (hf z).symm
  have hmaps : F.map (TopCat.ofHom N)
      (F.map (pairMapOnSubspace B ({w}ᶜ) G hpair)
        (F.map (TopCat.ofHom γ) CircleFundamentalCycle.fundamentalClass)) =
      CircleFundamentalCycle.fundamentalClass := by
    change (F.map (TopCat.ofHom γ) ≫ F.map (pairMapOnSubspace B ({w}ᶜ) G hpair) ≫
      F.map (TopCat.ofHom N)) CircleFundamentalCycle.fundamentalClass = _
    rw [← F.map_comp,← F.map_comp,hcomp]
    exact hfH1
  have hn := congrArg (fun m => m rD) (relativeConnecting_natural B ({w}ᶜ) G hpair 1)
  change F.map (pairMapOnSubspace B ({w}ᶜ) G hpair) (relativeConnecting D B 1 rD) =
    relativeConnecting ℂ ({w}ᶜ) 1 (pairRelativeHomologyMap B ({w}ᶜ) G hpair 2 rD) at hn
  rw [hr] at hn
  rw [← hn]
  exact hmaps

private theorem actual_complex_chart_source_to_plane_point_relative_isIso
    {E : Type} [TopologicalSpace E] [T1Space E]
    (e : OpenPartialHomeomorph E ℂ) (q : E) (hq : q ∈ e.source) :
    let A : Set e.source := {x | x.val ≠ q};
    ∃ (f : C(e.source,ℂ)) (h : ∀ x ∈ A, f x ∈ ({e q}ᶜ : Set ℂ)),
      (∀ x, f x = e x.val) ∧ IsIso (pairRelativeHomologyMap A ({e q}ᶜ) f h 2) := by
  dsimp only
  let A : Set e.source := {x | x.val ≠ q}
  let B : Set e.target := {y | y.val ≠ e q}
  let eh := e.toHomeomorphSourceTarget
  let k : C(e.source,e.target) := ⟨eh,eh.continuous⟩
  have hk : ∀ x ∈ A, eh x ∈ B := by
    intro x hx heq
    apply hx
    exact e.injOn x.property hq heq
  have hki : ∀ y ∈ B, eh.symm y ∈ A := by
    intro y hy heq
    apply hy
    have hh := congrArg e heq
    change e (e.symm y.val) = e q at hh
    rw [e.right_inv y.property] at hh
    exact hh
  let j : C(e.target,ℂ) := ReflectionGermProof.inclusion e.target
  have hj : ∀ y ∈ B, j y ∈ ({e q}ᶜ : Set ℂ) := fun y hy => hy
  haveI : IsIso (pairRelativeHomologyMap A B k hk 2) :=
    ReflectionGermProof.pairHomeo_isIso A B eh hk hki 2
  haveI : IsIso (pairRelativeHomologyMap B ({e q}ᶜ) j hj 2) :=
    ReflectionGermProof.inclusion_isIso ({e q}ᶜ) e.target
      (ReflectionGermProof.puncture_excision (e q) e.target e.open_target (e.map_source hq))
  let f := j.comp k
  let h : ∀ x ∈ A, f x ∈ ({e q}ᶜ : Set ℂ) := fun x hx => hj (k x) (hk x hx)
  refine ⟨f,h,fun x => rfl,?_⟩
  rw [pairRelativeHomologyMap_comp A B ({e q}ᶜ) k j hk hj 2]
  infer_instance

private theorem actual_complex_chart_surface_point_orientation_coordinate
    {E : Type} [TopologicalSpace E] [T1Space E]
    (e : OpenPartialHomeomorph E ℂ) (q : E) (hq : q ∈ e.source) :
    let A : Set e.source := {x | x.val ≠ q};
    ∃ (f : C(e.source,ℂ)) (hf : ∀ x ∈ A, f x ∈ ({e q}ᶜ : Set ℂ))
      (N : C(({e q}ᶜ : Set ℂ),Circle))
      (Φ : relativeHomology E ({q}ᶜ) 2 ⟶ H Circle 1),
      (∀ x, f x = e x.val) ∧
      (∀ x, (N x:ℂ) = (x.val-e q)/(‖x.val-e q‖:ℂ)) ∧
      IsIso Φ ∧
      pairRelativeHomologyMap A ({q}ᶜ) (ReflectionGermProof.inclusion e.source)
        (fun x hx => hx) 2 ≫ Φ =
      pairRelativeHomologyMap A ({e q}ᶜ) f hf 2 ≫ relativeConnecting ℂ ({e q}ᶜ) 1 ≫
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom N)) := by
  dsimp only
  let A : Set e.source := {x | x.val ≠ q}
  obtain ⟨f,hf,hflit,hfiso⟩ := actual_complex_chart_source_to_plane_point_relative_isIso e q hq
  obtain ⟨N,hN,hNiso⟩ := actual_centered_complex_puncture_circle_coordinate (e q)
  let j := pairRelativeHomologyMap A ({q}ᶜ) (ReflectionGermProof.inclusion e.source)
    (fun x hx => hx) 2
  haveI : IsIso j := ReflectionGermProof.inclusion_isIso ({q}ᶜ) e.source
    (ReflectionGermProof.puncture_excision q e.source e.open_source hq)
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)
  haveI : IsIso (F.map (TopCat.ofHom N)) := hNiso
  haveI : IsIso (relativeConnecting ℂ ({e q}ᶜ) 1) := actual_complex_plane_point_connecting_isIso (e q)
  haveI : IsIso (pairRelativeHomologyMap A ({e q}ᶜ) f hf 2) := hfiso
  let Φ := inv j ≫ pairRelativeHomologyMap A ({e q}ᶜ) f hf 2 ≫
    relativeConnecting ℂ ({e q}ᶜ) 1 ≫ F.map (TopCat.ofHom N)
  refine ⟨f,hf,N,Φ,hflit,hN,inferInstance,?_⟩
  change j ≫ (inv j ≫ _) = _
  rw [← Category.assoc,IsIso.hom_inv_id,Category.id_comp]

private theorem actual_chart_orientation_coordinate_on_actual_disc
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (e : OpenPartialHomeomorph E ℂ) (q : E)
    (B : Set X) (m : C(X,E)) (hm : ∀ x, m x ∈ e.source)
    (hB : ∀ x ∈ B, m x ∈ ({q}ᶜ : Set E))
    (f : C(e.source,ℂ)) (hf : ∀ x ∈ {y : e.source | y.val ≠ q}, f x ∈ ({e q}ᶜ : Set ℂ))
    (N : C(({e q}ᶜ : Set ℂ),Circle))
    (Φ : relativeHomology E ({q}ᶜ) 2 ⟶ H Circle 1)
    (hcompat : pairRelativeHomologyMap {y : e.source | y.val ≠ q} ({q}ᶜ)
      (ReflectionGermProof.inclusion e.source) (fun x hx => hx) 2 ≫ Φ =
      pairRelativeHomologyMap {y : e.source | y.val ≠ q} ({e q}ᶜ) f hf 2 ≫
        relativeConnecting ℂ ({e q}ᶜ) 1 ≫
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom N)))
    (hflit : ∀ x, f x = e x.val)
    (G : C(X,ℂ)) (hG : ∀ x, G x = e (m x))
    (hGB : ∀ x ∈ B, G x ∈ ({e q}ᶜ : Set ℂ)) (r : relativeHomology X B 2) :
    Φ (pairRelativeHomologyMap B ({q}ᶜ) m hB 2 r) =
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom N))
      (relativeConnecting ℂ ({e q}ᶜ) 1 (pairRelativeHomologyMap B ({e q}ᶜ) G hGB 2 r)) := by
  let A : Set e.source := {y | y.val ≠ q}
  let k : C(X,e.source) := ⟨fun x => ⟨m x,hm x⟩,m.continuous.subtype_mk hm⟩
  have hk : ∀ x ∈ B, k x ∈ A := hB
  let j := ReflectionGermProof.inclusion e.source
  have heq : j.comp k = m := by ext x; rfl
  have hcomp := pairRelativeHomologyMap_comp B A ({q}ᶜ) k j hk (fun x hx => hx) 2
  have hcomp' : pairRelativeHomologyMap B ({q}ᶜ) m hB 2 =
      pairRelativeHomologyMap B A k hk 2 ≫
      pairRelativeHomologyMap A ({q}ᶜ) j (fun x hx => hx) 2 := by
    have he := ReflectionGermProof.pairMap_congr B ({q}ᶜ) (j.comp k) m
      (fun x hx => hk x hx) hB heq 2
    exact he.symm.trans hcomp
  have heqG : f.comp k = G := by
    ext x
    exact (hflit (k x)).trans (hG x).symm
  have hcompG := pairRelativeHomologyMap_comp B A ({e q}ᶜ) k f hk hf 2
  have hcompG' : pairRelativeHomologyMap B ({e q}ᶜ) G hGB 2 =
      pairRelativeHomologyMap B A k hk 2 ≫ pairRelativeHomologyMap A ({e q}ᶜ) f hf 2 := by
    have he := ReflectionGermProof.pairMap_congr B ({e q}ᶜ) (f.comp k) G
      (fun x hx => hf (k x) (hk x hx)) hGB heqG 2
    exact he.symm.trans hcompG
  have h := congrArg (fun g => g (pairRelativeHomologyMap B A k hk 2 r)) hcompat
  rw [hcomp',hcompG']
  exact h

private theorem actual_supplied_complex_chart_point_orientation_coordinates_agree
    {E : Type} [TopologicalSpace E] [T1Space E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (q p : E) (hqp : q ∈ (chartAt ℂ p).source) :
    let c := chartAt ℂ q;
    let d := chartAt ℂ p;
    ∀ (fc : C(c.source,ℂ))
      (hfc : ∀ x ∈ {y : c.source | y.val ≠ q}, fc x ∈ ({c q}ᶜ : Set ℂ))
      (Nc : C(({c q}ᶜ : Set ℂ),Circle))
      (Φc : relativeHomology E ({q}ᶜ) 2 ⟶ H Circle 1)
      (hcflit : ∀ x, fc x = c x.val)
      (hcNlit : ∀ x, (Nc x:ℂ) = (x.val-c q)/(‖x.val-c q‖:ℂ))
      (hciso : IsIso Φc)
      (hccompat : pairRelativeHomologyMap {y : c.source | y.val ≠ q} ({q}ᶜ)
        (ReflectionGermProof.inclusion c.source) (fun x hx => hx) 2 ≫ Φc =
        pairRelativeHomologyMap {y : c.source | y.val ≠ q} ({c q}ᶜ) fc hfc 2 ≫
          relativeConnecting ℂ ({c q}ᶜ) 1 ≫
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom Nc)))
      (fd : C(d.source,ℂ))
      (hfd : ∀ x ∈ {y : d.source | y.val ≠ q}, fd x ∈ ({d q}ᶜ : Set ℂ))
      (Nd : C(({d q}ᶜ : Set ℂ),Circle))
      (Φd : relativeHomology E ({q}ᶜ) 2 ⟶ H Circle 1)
      (hdflit : ∀ x, fd x = d x.val)
      (hdNlit : ∀ x, (Nd x:ℂ) = (x.val-d q)/(‖x.val-d q‖:ℂ))
      (hdcompat : pairRelativeHomologyMap {y : d.source | y.val ≠ q} ({q}ᶜ)
        (ReflectionGermProof.inclusion d.source) (fun x hx => hx) 2 ≫ Φd =
        pairRelativeHomologyMap {y : d.source | y.val ≠ q} ({d q}ᶜ) fd hfd 2 ≫
          relativeConnecting ℂ ({d q}ᶜ) 1 ≫
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom Nd))), Φc = Φd := by
  dsimp only
  let c := chartAt ℂ q
  let d := chartAt ℂ p
  intro fc hfc Nc Φc hcflit hcNlit hciso hccompat fd hfd Nd Φd hdflit hdNlit hdcompat
  haveI : IsIso Φc := hciso
  obtain ⟨ρ,hρ,hρR,hct,hds,G,hGB,γ,rD,N,hGlit,hγ,hδD,hN,hNiso,hpositive⟩ :=
    actual_literal_complex_chart_transition_normalized_cap_orientation q p hqp 1 (by norm_num)
  let D := closedBall (c q) ρ
  let B : Set D := {x | dist x.val (c q) = ρ}
  let m : C(D,E) := ⟨fun x => c.symm x.val,
    c.symm.continuousOn.comp_continuous continuous_subtype_val (fun x => hct x.property)⟩
  have hmc : ∀ x, m x ∈ c.source := fun x => c.map_target (hct x.property)
  have hmd : ∀ x, m x ∈ d.source := fun x => hds x.val x.property
  have hB : ∀ x ∈ B, m x ∈ ({q}ᶜ : Set E) := by
    intro x hx heq
    change m x = q at heq
    have hh := congrArg c heq
    change c (c.symm x.val) = c q at hh
    rw [c.right_inv (hct x.property)] at hh
    have hd : dist x.val (c q) = ρ := hx
    rw [hh,dist_self] at hd
    exact hρ.ne' hd.symm
  let t := pairRelativeHomologyMap B ({q}ᶜ) m hB 2 rD
  have hNd : N = Nd := by
    ext x
    exact (hN x).trans (hdNlit x).symm
  have hdvalue : Φd t = CircleFundamentalCycle.fundamentalClass := by
    have he := actual_chart_orientation_coordinate_on_actual_disc d q B m hmd hB
      fd hfd Nd Φd hdcompat hdflit G (fun x => hGlit x) hGB rD
    change Φd t = _ at he
    rw [← hNd] at he
    exact he.trans hpositive
  obtain ⟨hBc,N₀,hN₀,hiso₀,hpositive₀⟩ :=
    actual_literal_normalized_disc_cap_all_interior_points_positive (c q) (c q) ρ hρ
      (by simpa only [dist_self] using hρ) γ hγ rD hδD
  have hNc : N₀ = Nc := by
    ext x
    exact (hN₀ x).trans (hcNlit x).symm
  let Gc : C(D,ℂ) := ⟨Subtype.val,continuous_subtype_val⟩
  have hGclit : ∀ x, Gc x = c (m x) := fun x => (c.right_inv (hct x.property)).symm
  have hcvalue : Φc t = CircleFundamentalCycle.fundamentalClass := by
    have he := actual_chart_orientation_coordinate_on_actual_disc c q B m hmc hB
      fc hfc Nc Φc hccompat hcflit Gc hGclit hBc rD
    change Φc t = _ at he
    rw [← hNc] at he
    exact he.trans hpositive₀
  have hgenerates : ∀ u : relativeHomology E ({q}ᶜ) 2, ∃ n : ℤ, n • t = u := by
    intro u
    obtain ⟨n,hn⟩ := CircleFundamentalCycle.fundamentalClass_generates (Φc u)
    refine ⟨n,?_⟩
    apply (ModuleCat.mono_iff_injective Φc).mp inferInstance
    rw [map_zsmul,hcvalue]
    exact hn
  ext u
  obtain ⟨n,hn⟩ := hgenerates u
  change Φc u = Φd u
  rw [← hn,map_zsmul,map_zsmul,hcvalue,hdvalue]

private theorem actual_supplied_complex_atlas_coherent_point_orientation_coordinate
    {E : Type} [TopologicalSpace E] [T1Space E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (q : E) :
    ∃ Φ : relativeHomology E ({q}ᶜ) 2 ⟶ H Circle 1,
      IsIso Φ ∧ ∀ p : E, q ∈ (chartAt ℂ p).source →
        let d := chartAt ℂ p;
        let A : Set d.source := {x | x.val ≠ q};
        ∃ (f : C(d.source,ℂ)) (hf : ∀ x ∈ A, f x ∈ ({d q}ᶜ : Set ℂ))
          (N : C(({d q}ᶜ : Set ℂ),Circle)),
          (∀ x, f x = d x.val) ∧
          (∀ x, (N x:ℂ) = (x.val-d q)/(‖x.val-d q‖:ℂ)) ∧
          pairRelativeHomologyMap A ({q}ᶜ) (ReflectionGermProof.inclusion d.source)
            (fun x hx => hx) 2 ≫ Φ =
          pairRelativeHomologyMap A ({d q}ᶜ) f hf 2 ≫ relativeConnecting ℂ ({d q}ᶜ) 1 ≫
            (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
              (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom N)) := by
  obtain ⟨fc,hfc,Nc,Φc,hcflit,hcNlit,hciso,hccompat⟩ :=
    actual_complex_chart_surface_point_orientation_coordinate (chartAt ℂ q) q
      (mem_chart_source ℂ q)
  refine ⟨Φc,hciso,?_⟩
  intro p hqp
  dsimp only
  obtain ⟨fd,hfd,Nd,Φd,hdflit,hdNlit,hdiso,hdcompat⟩ :=
    actual_complex_chart_surface_point_orientation_coordinate (chartAt ℂ p) q hqp
  have heq := actual_supplied_complex_chart_point_orientation_coordinates_agree q p hqp
    fc hfc Nc Φc hcflit hcNlit hciso hccompat fd hfd Nd Φd hdflit hdNlit hdcompat
  exact ⟨fd,hfd,Nd,hdflit,hdNlit,by rw [heq];exact hdcompat⟩

private theorem actual_supplied_atlas_coherent_orientation_normalizes_all_literal_caps
    {E : Type} [TopologicalSpace E] [T1Space E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] :
    ∃ Φ : ∀ q : E, relativeHomology E ({q}ᶜ) 2 ⟶ H Circle 1,
      (∀ q, IsIso (Φ q)) ∧
      ∀ (p : E) (ρ : ℝ) (hρ : 0 < ρ)
        (htarget : closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target),
        let c := chartAt ℂ p;
        let D := closedBall (c p) ρ;
        let B : Set D := {x | dist x.val (c p) = ρ};
        ∀ (γ : C(Circle,B)) (hγ : ∀ z, (γ z).val.val = c p+(ρ:ℂ)*z)
          (rD : relativeHomology D B 2)
          (hrD : relativeConnecting D B 1 rD =
            (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
              (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ)) CircleFundamentalCycle.fundamentalClass)
          (m : C(D,E)) (hmlit : ∀ x, m x = c.symm x.val)
          (q : E) (hqp : q ∈ c.source) (hqdisc : dist (c q) (c p) < ρ),
          ∃ hB : ∀ x ∈ B, m x ∈ ({q}ᶜ : Set E),
            Φ q (pairRelativeHomologyMap B ({q}ᶜ) m hB 2 rD) =
              CircleFundamentalCycle.fundamentalClass := by
  choose Φ hΦiso hΦcharts using
    (fun q : E => actual_supplied_complex_atlas_coherent_point_orientation_coordinate q)
  refine ⟨Φ,hΦiso,?_⟩
  intro p ρ hρ htarget
  dsimp only
  let c := chartAt ℂ p
  let D := closedBall (c p) ρ
  let B : Set D := {x | dist x.val (c p) = ρ}
  intro γ hγ rD hrD m hmlit q hqp hqdisc
  have hm : ∀ x, m x ∈ c.source := by
    intro x
    rw [hmlit]
    exact c.map_target (htarget x.property)
  have hB : ∀ x ∈ B, m x ∈ ({q}ᶜ : Set E) := by
    intro x hx heq
    change m x = q at heq
    have hh := congrArg c heq
    rw [hmlit,c.right_inv (htarget x.property)] at hh
    have hd : dist x.val (c p) = ρ := hx
    rw [hh] at hd
    exact (ne_of_lt hqdisc) hd
  obtain ⟨f,hf,N,hflit,hNlit,hcompat⟩ := hΦcharts q p hqp
  obtain ⟨hGB,N₀,hN₀,hiso₀,hpositive₀⟩ :=
    actual_literal_normalized_disc_cap_all_interior_points_positive (c p) (c q) ρ hρ
      hqdisc γ hγ rD hrD
  have hN : N₀ = N := by
    ext x
    exact (hN₀ x).trans (hNlit x).symm
  let G : C(D,ℂ) := ⟨Subtype.val,continuous_subtype_val⟩
  have hG : ∀ x, G x = c (m x) := by
    intro x
    rw [hmlit,c.right_inv (htarget x.property)]
    rfl
  refine ⟨hB,?_⟩
  have he := actual_chart_orientation_coordinate_on_actual_disc c q B m hm hB
    f hf N (Φ q) hcompat hflit G hG hGB rD
  rw [← hN] at he
  exact he.trans hpositive₀
