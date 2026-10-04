import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import CurveComplexGenusTwo.CWHurewicz.AffineCarrier
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseStatements
import CurveComplexGenusTwo.CWHurewicz.SmallSingularChainsLocal
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.ZMod.Basic

open scoped Manifold ContDiff Bundle Simplicial
open Bundle
open Convexity
open Filter Topology
open CategoryTheory CategoryTheory.Limits CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false

namespace CanonicalDimensionTwo

noncomputable abbrev ActualCanonicalSection (E : Type*) [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :=
  ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ∞
    (fun x : E => TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial E ℂ x)

def actualOneForm {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (v : TangentBundle 𝓘(ℂ) E) : ℂ :=
  s v.proj v.2

theorem actualOneForm_fiber_linear {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (x : E) (v w : TangentSpace 𝓘(ℂ) x)
    (c : ℂ) :
    actualOneForm s ⟨x, v + c • w⟩ =
      actualOneForm s ⟨x, v⟩ + c * actualOneForm s ⟨x, w⟩ := by
  change s x (v + c • w) = s x v + c * s x w
  rw [map_add, map_smul]
  rfl

theorem actualOneForm_contMDiff {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) 𝓘(ℂ) ∞ (actualOneForm s) := by
  change ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) 𝓘(ℂ) ∞
    (fun v : TangentBundle 𝓘(ℂ) E => s v.proj v.2)
  have hs : ContMDiff (𝓘(ℂ).prod 𝓘(ℂ))
      (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ∞
      (fun v : TangentBundle 𝓘(ℂ) E =>
        TotalSpace.mk' (ℂ →L[ℂ] ℂ)
          (E := fun x : E => TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial E ℂ x)
          v.proj (s v.proj)) :=
    s.contMDiff.comp (contMDiff_proj (F := ℂ) (IB := 𝓘(ℂ)) (n := ∞)
      (fun x : E => TangentSpace 𝓘(ℂ) x))
  have hv : ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ∞
      (fun v : TangentBundle 𝓘(ℂ) E =>
        TotalSpace.mk' ℂ (E := fun x : E => TangentSpace 𝓘(ℂ) x) v.proj v.2) :=
    contMDiff_id
  have happ := hs.clm_bundle_apply hv
  intro v
  have hcoord := (contMDiffAt_totalSpace.mp (happ v)).2
  simpa [Bundle.Trivial.fiberBundle_trivializationAt'] using hcoord

def actualOneFormLinear {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualCanonicalSection E →ₗ[ℂ] (TangentBundle 𝓘(ℂ) E → ℂ) where
  toFun := actualOneForm
  map_add' := by
    intro s t
    funext v
    simp [actualOneForm]
  map_smul' := by
    intro c s
    funext v
    simp [actualOneForm]

theorem actualOneFormLinear_injective {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    Function.Injective (actualOneFormLinear (E := E)) := by
  intro s t h
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrFun h (⟨x, v⟩ : TangentBundle 𝓘(ℂ) E)
  exact hv

noncomputable def actualLocalOneForm {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q : E) (z : ℂ) :
    ℂ [⋀^Fin 1]→L[ℂ] ℂ :=
  (ContinuousAlternatingMap.ofSubsingleton ℂ ℂ ℂ (0 : Fin 1))
    (ContinuousLinearMap.inCoordinates
      ℂ (fun x : E => TangentSpace 𝓘(ℂ) x) ℂ (Bundle.Trivial E ℂ)
      q ((chartAt ℂ q).symm z) q ((chartAt ℂ q).symm z)
      (s ((chartAt ℂ q).symm z)))

theorem actualLocalOneForm_apply {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q : E) (z v : ℂ) :
    actualLocalOneForm s q z (fun _ : Fin 1 => v) =
      (ContinuousLinearMap.inCoordinates
        ℂ (fun x : E => TangentSpace 𝓘(ℂ) x) ℂ (Bundle.Trivial E ℂ)
        q ((chartAt ℂ q).symm z) q ((chartAt ℂ q).symm z)
        (s ((chartAt ℂ q).symm z))) v := by
  simp [actualLocalOneForm]

theorem actualLocalOneForm_apply_eq_mul_coefficient {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q : E) (z v : ℂ) :
    actualLocalOneForm s q z (fun _ : Fin 1 => v) =
      v * actualLocalOneForm s q z (fun _ : Fin 1 => (1 : ℂ)) := by
  rw [actualLocalOneForm_apply, actualLocalOneForm_apply]
  let L := ContinuousLinearMap.inCoordinates
    ℂ (fun x : E => TangentSpace 𝓘(ℂ) x) ℂ (Bundle.Trivial E ℂ)
    q ((chartAt ℂ q).symm z) q ((chartAt ℂ q).symm z)
    (s ((chartAt ℂ q).symm z))
  change L v = v * L 1
  simpa only [smul_eq_mul, smul_eq_mul, mul_one] using (L.map_smul v (1 : ℂ))

theorem actualLocalOneForm_eq_global_in_chart {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q x : E) (v : ℂ)
    (hx : x ∈ (chartAt ℂ q).source) :
    actualLocalOneForm s q ((chartAt ℂ q) x) (fun _ : Fin 1 => v) =
      actualOneForm s ⟨x,
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q).symmL ℂ x v⟩ := by
  rw [actualLocalOneForm_apply, (chartAt ℂ q).left_inv hx]
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_apply]
  rfl

theorem actualLocalOneForm_eq_global_on_tangent {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q x : E) (v : TangentSpace 𝓘(ℂ) x)
    (hx : x ∈ (chartAt ℂ q).source) :
    actualLocalOneForm s q ((chartAt ℂ q) x)
      (fun _ : Fin 1 =>
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q).continuousLinearMapAt ℂ x v) =
      actualOneForm s ⟨x, v⟩ := by
  rw [actualLocalOneForm_eq_global_in_chart s q x _ hx]
  rw [Trivialization.symmL_continuousLinearMapAt (R := ℂ)
    (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q)
    (by simpa using hx) v]

theorem actualLocalOneForm_change_chart {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q r x : E) (v : TangentSpace 𝓘(ℂ) x)
    (hq : x ∈ (chartAt ℂ q).source) (hr : x ∈ (chartAt ℂ r).source) :
    actualLocalOneForm s q ((chartAt ℂ q) x)
      (fun _ : Fin 1 =>
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q).continuousLinearMapAt ℂ x v) =
    actualLocalOneForm s r ((chartAt ℂ r) x)
      (fun _ : Fin 1 =>
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) r).continuousLinearMapAt ℂ x v) := by
  rw [actualLocalOneForm_eq_global_on_tangent s q x v hq,
    actualLocalOneForm_eq_global_on_tangent s r x v hr]

theorem actualLocalOneForm_coefficient_analytic {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q : E) :
    AnalyticAt ℂ
      (fun z => actualLocalOneForm s q z (fun _ : Fin 1 => (1 : ℂ)))
      ((chartAt ℂ q) q) := by
  let L : E → ℂ →L[ℂ] ℂ := fun x => ContinuousLinearMap.inCoordinates
    ℂ (fun x : E => TangentSpace 𝓘(ℂ) x) ℂ (Bundle.Trivial E ℂ)
    q x q x (s x)
  have hL : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞ L q :=
    ((contMDiffAt_hom_bundle _).mp (s.contMDiff q)).2
  have hcoeff : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 (fun x => L x 1) q :=
    (hL.clm_apply contMDiffAt_const).of_le (by simp)
  have hchart := (contMDiffAt_iff_of_mem_source
    (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (n := 1)
    (x := q) (y := L q 1) (mem_chart_source ℂ q)
    (mem_chart_source ℂ (L q 1))).mp hcoeff
  have hc : ContDiffAt ℂ 1 (fun z => L ((chartAt ℂ q).symm z) 1)
      ((chartAt ℂ q) q) := by
    simpa [extChartAt, OpenPartialHomeomorph.extend, contDiffWithinAt_univ,
      Function.comp_def] using hchart.2
  obtain ⟨U, hU, hqU, hcont⟩ := hc.contDiffOn' le_rfl (by simp)
  have hd : DifferentiableOn ℂ (fun z => L ((chartAt ℂ q).symm z) 1) U := by
    apply ContDiffOn.differentiableOn _ one_ne_zero
    simpa only [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] using hcont
  have ha := hd.analyticAt (hU.mem_nhds hqU)
  simpa only [actualLocalOneForm_apply] using ha

theorem actualLocalOneForm_coefficient_analytic_on_chart {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q x : E)
    (hx : x ∈ (chartAt ℂ q).source) :
    AnalyticAt ℂ
      (fun z => actualLocalOneForm s q z (fun _ : Fin 1 => (1 : ℂ)))
      ((chartAt ℂ q) x) := by
  let e := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q
  have he := e.contMDiffAt_symmL (IB := 𝓘(ℂ)) (n := ∞)
    (by simpa [e] using hx)
  have hconst : ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ∞
      (fun y : E => (⟨y, (1 : ℂ)⟩ : TotalSpace ℂ (Bundle.Trivial E ℂ))) x := by
    exact contMDiffAt_totalSpace.mpr ⟨contMDiffAt_id, contMDiffAt_const⟩
  have hv := he.clm_bundle_apply hconst
  have hcoeff : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1
      (fun y : E => actualOneForm s ⟨y, e.symmL ℂ y 1⟩) x := by
    exact ((actualOneForm_contMDiff s) _).comp x hv |>.of_le (by simp)
  have hchart := (contMDiffAt_iff_of_mem_source
    (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (n := 1)
    (x := q) (x' := x) (y := actualOneForm s ⟨x, e.symmL ℂ x 1⟩) hx
    (mem_chart_source ℂ (actualOneForm s ⟨x, e.symmL ℂ x 1⟩))).mp hcoeff
  have hc : ContDiffAt ℂ 1
      (fun z => actualOneForm s ⟨(chartAt ℂ q).symm z,
        e.symmL ℂ ((chartAt ℂ q).symm z) 1⟩)
      ((chartAt ℂ q) x) := by
    simpa [extChartAt, OpenPartialHomeomorph.extend, contDiffWithinAt_univ,
      Function.comp_def] using hchart.2
  obtain ⟨U, hU, hqU, hcont⟩ := hc.contDiffOn' le_rfl (by simp)
  have hd : DifferentiableOn ℂ
      (fun z => actualOneForm s ⟨(chartAt ℂ q).symm z,
        e.symmL ℂ ((chartAt ℂ q).symm z) 1⟩) U := by
    apply ContDiffOn.differentiableOn _ one_ne_zero
    simpa only [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] using hcont
  have ha := hd.analyticAt (hU.mem_nhds hqU)
  have hnear : (chartAt ℂ q).target ∈ 𝓝 ((chartAt ℂ q) x) :=
    (chartAt ℂ q).open_target.mem_nhds ((chartAt ℂ q).map_source hx)
  apply ha.congr
  filter_upwards [hnear] with z hz
  have hsrc : (chartAt ℂ q).symm z ∈ (chartAt ℂ q).source :=
    (chartAt ℂ q).map_target hz
  simpa [e, (chartAt ℂ q).right_inv hz] using
    (actualLocalOneForm_eq_global_in_chart s q
      ((chartAt ℂ q).symm z) 1 hsrc).symm

theorem actualLocalOneForm_extDeriv_eq_zero {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q : E) (z : ℂ) :
    extDeriv (actualLocalOneForm s q) z = 0 := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact Subsingleton.elim _ _

theorem actualLocalOneForm_has_primitive_on_ball {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q : E) (c : ℂ) (r : ℝ)
    (hball : Metric.ball c r ⊆ (chartAt ℂ q).target) :
    ∃ F : ℂ → ℂ, ∀ z ∈ Metric.ball c r,
      HasDerivWithinAt F
        (actualLocalOneForm s q z (fun _ : Fin 1 => (1 : ℂ)))
        (Metric.ball c r) z := by
  apply (convex_ball c r).exists_forall_hasDerivWithinAt
  intro z hz
  have htarget : z ∈ (chartAt ℂ q).target := hball hz
  have hx : (chartAt ℂ q).symm z ∈ (chartAt ℂ q).source :=
    (chartAt ℂ q).map_target htarget
  have ha := actualLocalOneForm_coefficient_analytic_on_chart s q
    ((chartAt ℂ q).symm z) hx
  rw [(chartAt ℂ q).right_inv htarget] at ha
  exact ha.differentiableAt.differentiableWithinAt

noncomputable def actualLocalCurveIntegral {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q : E)
    {a b : ℂ} (γ : Path a b) : ℂ :=
  curveIntegral
    (fun z => (ContinuousAlternatingMap.ofSubsingleton ℂ ℂ ℂ (0 : Fin 1)).symm
      (actualLocalOneForm s q z)) γ

theorem actualLocalCurveIntegral_refl {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q : E) (a : ℂ) :
    actualLocalCurveIntegral s q (Path.refl a) = 0 := by
  simp [actualLocalCurveIntegral]

noncomputable def actualPathVelocity {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ℝ → E) (t : ℝ) : TangentSpace 𝓘(ℂ) (γ t) :=
  (tangentSpaceCastModel 𝓘(ℂ) (γ t)).symm
    ((fderiv ℝ (fun u : ℝ => (chartAt ℂ (γ t)) (γ u)) t) 1)

noncomputable def actualPathIntegrand {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ℝ → E) (t : ℝ) : ℂ :=
  actualOneForm s ⟨γ t, actualPathVelocity γ t⟩

theorem actualPathIntegrand_eq_local_form {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ℝ → E) (t : ℝ) :
    actualPathIntegrand s γ t =
      actualLocalOneForm s (γ t) ((chartAt ℂ (γ t)) (γ t))
        (fun _ : Fin 1 =>
          (fderiv ℝ (fun u : ℝ => (chartAt ℂ (γ t)) (γ u)) t) 1) := by
  rw [actualLocalOneForm_eq_global_in_chart s (γ t) (γ t)
    ((fderiv ℝ (fun u : ℝ => (chartAt ℂ (γ t)) (γ u)) t) 1)
    (mem_chart_source ℂ (γ t))]
  simp only [actualPathIntegrand, actualPathVelocity]
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source ℂ (γ t))]
  have hcore :
      (tangentBundleCore 𝓘(ℂ) E).coordChange
        (achart ℂ (γ t)) (achart ℂ (γ t)) (γ t) =
        ContinuousLinearMap.id ℂ ℂ := by
    apply ContinuousLinearMap.ext
    intro v
    exact tangentCoordChange_self (I := 𝓘(ℂ))
      (show γ t ∈ (extChartAt 𝓘(ℂ) (γ t)).source from by simp)
  rw [hcore]
  rfl

theorem actualPathIntegrand_eq_arbitrary_chart {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ℝ → E) (t : ℝ) (q : E)
    (hq : γ t ∈ (chartAt ℂ q).source) :
    actualPathIntegrand s γ t =
      actualLocalOneForm s q ((chartAt ℂ q) (γ t))
        (fun _ : Fin 1 =>
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q).continuousLinearMapAt
            ℂ (γ t) (actualPathVelocity γ t)) := by
  exact (actualLocalOneForm_eq_global_on_tangent s q (γ t)
    (actualPathVelocity γ t) hq).symm

theorem actualPathVelocity_fixed_chart {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ℝ → E) (t : ℝ) (q : E)
    (hγc : ContinuousAt γ t)
    (hγd : DifferentiableAt ℝ
      (fun u : ℝ => (chartAt ℂ (γ t)) (γ u)) t)
    (hq : γ t ∈ (chartAt ℂ q).source) :
    (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℂ) y) q).continuousLinearMapAt
        ℂ (γ t) (actualPathVelocity γ t) =
      (fderiv ℝ (fun u : ℝ => (chartAt ℂ q) (γ u)) t) 1 := by
  let x := γ t
  let f : ℝ → ℂ := fun u => (chartAt ℂ x) (γ u)
  let g : ℂ → ℂ := (chartAt ℂ q) ∘ (chartAt ℂ x).symm
  have hx : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hevent : (fun u : ℝ => (chartAt ℂ q) (γ u)) =ᶠ[𝓝 t] g ∘ f := by
    filter_upwards [hγc.eventually ((chartAt ℂ x).open_source.mem_nhds hx)] with u hu
    simp only [g, f, Function.comp_apply, (chartAt ℂ x).left_inv hu]
  have hsource : (chartAt ℂ x) x ∈
      (((extChartAt 𝓘(ℂ) x).symm ≫ extChartAt 𝓘(ℂ) q).source) := by
    rw [PartialEquiv.trans_source'', PartialEquiv.symm_symm,
      PartialEquiv.symm_target]
    exact Set.mem_image_of_mem _ ⟨by simp [extChartAt],
      by simpa [extChartAt] using hq⟩
  have hg : DifferentiableAt ℂ g ((chartAt ℂ x) x) := by
    have h := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) (n := ∞) q x hsource
    simpa [extChartAt, OpenPartialHomeomorph.extend, g, differentiableWithinAt_univ,
      Function.comp_def] using h.differentiableWithinAt (by simp)
  have hdf : fderiv ℝ (fun u : ℝ => (chartAt ℂ q) (γ u)) t =
      ((fderiv ℂ g ((chartAt ℂ x) x)).restrictScalars ℝ).comp (fderiv ℝ f t) := by
    rw [hevent.fderiv_eq, fderiv_comp t (hg.restrictScalars ℝ) hγd]
    rw [hg.fderiv_restrictScalars ℝ]
  have htransition : fderiv ℂ g ((chartAt ℂ x) x) =
      tangentCoordChange 𝓘(ℂ) x q x := by
    simp [g, OpenPartialHomeomorph.extend, fderivWithin_univ]
  rw [hdf, htransition]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hq]
  rfl

theorem actualPathDifferentiable_fixed_chart {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ℝ → E) (t : ℝ) (q : E)
    (hγc : ContinuousAt γ t)
    (hγd : DifferentiableAt ℝ
      (fun u : ℝ => (chartAt ℂ (γ t)) (γ u)) t)
    (hq : γ t ∈ (chartAt ℂ q).source) :
    DifferentiableAt ℝ (fun u : ℝ => (chartAt ℂ q) (γ u)) t := by
  let x := γ t
  let f : ℝ → ℂ := fun u => (chartAt ℂ x) (γ u)
  let g : ℂ → ℂ := (chartAt ℂ q) ∘ (chartAt ℂ x).symm
  have hx : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hevent : (fun u : ℝ => (chartAt ℂ q) (γ u)) =ᶠ[𝓝 t] g ∘ f := by
    filter_upwards [hγc.eventually ((chartAt ℂ x).open_source.mem_nhds hx)] with u hu
    simp only [g, f, Function.comp_apply, (chartAt ℂ x).left_inv hu]
  have hsource : (chartAt ℂ x) x ∈
      (((extChartAt 𝓘(ℂ) x).symm ≫ extChartAt 𝓘(ℂ) q).source) := by
    rw [PartialEquiv.trans_source'', PartialEquiv.symm_symm,
      PartialEquiv.symm_target]
    exact Set.mem_image_of_mem _ ⟨by simp [extChartAt],
      by simpa [extChartAt] using hq⟩
  have hg : DifferentiableAt ℂ g ((chartAt ℂ x) x) := by
    have h := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) (n := ∞) q x hsource
    simpa [extChartAt, OpenPartialHomeomorph.extend, g, differentiableWithinAt_univ,
      Function.comp_def] using h.differentiableWithinAt (by simp)
  exact ((hg.restrictScalars ℝ).comp t hγd).congr_of_eventuallyEq hevent

theorem actualPathIntegrand_fixed_chart {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ℝ → E) (t : ℝ) (q : E)
    (hγc : ContinuousAt γ t)
    (hγd : DifferentiableAt ℝ
      (fun u : ℝ => (chartAt ℂ (γ t)) (γ u)) t)
    (hq : γ t ∈ (chartAt ℂ q).source) :
    actualPathIntegrand s γ t =
      actualLocalOneForm s q ((chartAt ℂ q) (γ t))
        (fun _ : Fin 1 =>
          (fderiv ℝ (fun u : ℝ => (chartAt ℂ q) (γ u)) t) 1) := by
  rw [actualPathIntegrand_eq_arbitrary_chart s γ t q hq,
    actualPathVelocity_fixed_chart γ t q hγc hγd hq]

theorem actualPathIntegrand_reverse {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ℝ → E) (t : ℝ)
    (hγ : DifferentiableAt ℝ
      (fun u : ℝ => (chartAt ℂ (γ (1 - t))) (γ u)) (1 - t)) :
    actualPathIntegrand s (fun u => γ (1 - u)) t =
      -actualPathIntegrand s γ (1 - t) := by
  let f : ℝ → ℂ := fun u => (chartAt ℂ (γ (1 - t))) (γ u)
  have hcomp : fderiv ℝ (fun u => f (1 - u)) t =
      (fderiv ℝ f (1 - t)).comp (fderiv ℝ (fun u : ℝ => 1 - u) t) := by
    simpa only [Function.comp_def] using
      (fderiv_comp (x := t) hγ (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => 1 - u) t))
  have hderiv : (fderiv ℝ (fun u => f (1 - u)) t) 1 =
      -((fderiv ℝ f (1 - t)) 1) := by
    rw [hcomp]
    simp
  have hvel : actualPathVelocity (fun u => γ (1 - u)) t =
      -actualPathVelocity γ (1 - t) := by
    simp only [actualPathVelocity]
    change (tangentSpaceCastModel 𝓘(ℂ) (γ (1 - t))).symm
      ((fderiv ℝ (fun u => f (1 - u)) t) 1) =
      -((tangentSpaceCastModel 𝓘(ℂ) (γ (1 - t))).symm
      ((fderiv ℝ f (1 - t)) 1))
    rw [hderiv, map_neg]
  simp [actualPathIntegrand, actualOneForm, hvel]

theorem actualPathIntegrand_affine {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ℝ → E)
    (hγ : ∀ t : ℝ, DifferentiableAt ℝ
      (fun u : ℝ => (chartAt ℂ (γ t)) (γ u)) t)
    (a b t : ℝ) :
    actualPathIntegrand s (fun u => γ (a * u + b)) t =
      a • actualPathIntegrand s γ (a * t + b) := by
  let f : ℝ → ℂ := fun u =>
    (chartAt ℂ (γ (a * t + b))) (γ u)
  have hcomp : fderiv ℝ (fun u => f (a * u + b)) t =
      (fderiv ℝ f (a * t + b)).comp
        (fderiv ℝ (fun u : ℝ => a * u + b) t) := by
    simpa only [Function.comp_def] using
      (fderiv_comp (x := t) (hγ (a * t + b))
        (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => a * u + b) t))
  have hderiv : (fderiv ℝ (fun u => f (a * u + b)) t) 1 =
      a • ((fderiv ℝ f (a * t + b)) 1) := by
    rw [hcomp]
    simp [smul_eq_mul]
  have hvel : actualPathVelocity (fun u => γ (a * u + b)) t =
      a • actualPathVelocity γ (a * t + b) := by
    simp only [actualPathVelocity]
    change (tangentSpaceCastModel 𝓘(ℂ) (γ (a * t + b))).symm
      ((fderiv ℝ (fun u => f (a * u + b)) t) 1) =
      a • (tangentSpaceCastModel 𝓘(ℂ) (γ (a * t + b))).symm
        ((fderiv ℝ f (a * t + b)) 1)
    rw [hderiv]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
  simp [actualPathIntegrand, actualOneForm, hvel, smul_eq_mul]

noncomputable def actualPathIntegral {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ℝ → E) : ℂ :=
  ∫ t in (0 : ℝ)..1, actualPathIntegrand s γ t

def ActualPathIntegrable {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ℝ → E) : Prop :=
  IntervalIntegrable (actualPathIntegrand s γ) MeasureTheory.volume 0 1

theorem actualPathIntegrand_add {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s t : ActualCanonicalSection E) (γ : ℝ → E) (u : ℝ) :
    actualPathIntegrand (s + t) γ u =
      actualPathIntegrand s γ u + actualPathIntegrand t γ u := by
  simp [actualPathIntegrand, actualOneForm]

theorem actualPathIntegrand_smul {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (c : ℂ) (s : ActualCanonicalSection E) (γ : ℝ → E) (u : ℝ) :
    actualPathIntegrand (c • s) γ u = c * actualPathIntegrand s γ u := by
  simp [actualPathIntegrand, actualOneForm]

theorem actualPathIntegral_add {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s t : ActualCanonicalSection E) (γ : ℝ → E)
    (hs : ActualPathIntegrable s γ) (ht : ActualPathIntegrable t γ) :
    actualPathIntegral (s + t) γ =
      actualPathIntegral s γ + actualPathIntegral t γ := by
  simp only [actualPathIntegral]
  conv_lhs => arg 1; ext u; rw [actualPathIntegrand_add]
  exact intervalIntegral.integral_add hs ht

theorem actualPathIntegral_smul {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (c : ℂ) (s : ActualCanonicalSection E) (γ : ℝ → E) :
    actualPathIntegral (c • s) γ = c * actualPathIntegral s γ := by
  simp only [actualPathIntegral]
  conv_lhs => arg 1; ext u; rw [actualPathIntegrand_smul]
  exact intervalIntegral.integral_const_mul c (actualPathIntegrand s γ)

theorem actualPathIntegral_split {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ℝ → E)
    (hγ : ActualPathIntegrable s γ) (u : ℝ) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) :
    actualPathIntegral s γ =
      (∫ t in (0 : ℝ)..u, actualPathIntegrand s γ t) +
      (∫ t in u..1, actualPathIntegrand s γ t) := by
  have h₀u : IntervalIntegrable (actualPathIntegrand s γ)
      MeasureTheory.volume 0 u :=
    hγ.mono_set (by
      rw [Set.uIcc_of_le hu₀, Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact Set.Icc_subset_Icc le_rfl hu₁)
  have hu₁' : IntervalIntegrable (actualPathIntegrand s γ)
      MeasureTheory.volume u 1 :=
    hγ.mono_set (by
      rw [Set.uIcc_of_le hu₁, Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact Set.Icc_subset_Icc hu₀ le_rfl)
  exact (intervalIntegral.integral_add_adjacent_intervals h₀u hu₁').symm

theorem actualPathIntegral_finite_subdivision {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ℝ → E)
    (hγ : ActualPathIntegrable s γ) (a : ℕ → ℝ) (n : ℕ)
    (hfirst : a 0 = 0) (hlast : a n = 1)
    (hbound : ∀ k ≤ n, 0 ≤ a k ∧ a k ≤ 1)
    (hmono : ∀ k < n, a k ≤ a (k + 1)) :
    actualPathIntegral s γ =
      ∑ k ∈ Finset.range n,
        ∫ t in a k..a (k + 1), actualPathIntegrand s γ t := by
  have hint : ∀ k < n, IntervalIntegrable (actualPathIntegrand s γ)
      MeasureTheory.volume (a k) (a (k + 1)) := by
    intro k hk
    apply hγ.mono_set
    rw [Set.uIcc_of_le (hmono k hk),
      Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact Set.Icc_subset_Icc (hbound k (Nat.le_of_lt hk)).1
      (hbound (k + 1) (Nat.succ_le_of_lt hk)).2
  simpa only [hfirst, hlast, actualPathIntegral] using
    (intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := n) hint).symm

theorem actualPathVelocity_const {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (x : E) (t : ℝ) : actualPathVelocity (fun _ => x) t = 0 := by
  simp [actualPathVelocity]

theorem actualPathIntegral_const {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (x : E) :
    actualPathIntegral s (fun _ => x) = 0 := by
  simp [actualPathIntegral, actualPathIntegrand, actualOneForm,
    actualPathVelocity_const]

theorem actualPathIntegral_reverse {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ℝ → E)
    (hγ : ∀ t : ℝ, DifferentiableAt ℝ
      (fun u : ℝ => (chartAt ℂ (γ t)) (γ u)) t) :
    actualPathIntegral s (fun u => γ (1 - u)) =
      -actualPathIntegral s γ := by
  simp only [actualPathIntegral]
  calc
    (∫ t in (0 : ℝ)..1, actualPathIntegrand s (fun u => γ (1 - u)) t) =
        ∫ t in (0 : ℝ)..1, -(actualPathIntegrand s γ (1 - t)) := by
          apply intervalIntegral.integral_congr
          intro t _
          exact actualPathIntegrand_reverse s γ t (hγ (1 - t))
    _ = -(∫ t in (0 : ℝ)..1, actualPathIntegrand s γ t) := by
      rw [intervalIntegral.integral_neg,
        intervalIntegral.integral_comp_sub_left (actualPathIntegrand s γ) (1 : ℝ)]
      norm_num

structure ActualRegularPath (E : Type*) [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] where
  toFun : ℝ → E
  continuous : Continuous toFun
  chartDifferentiable : ∀ t : ℝ, DifferentiableAt ℝ
    (fun u : ℝ => (chartAt ℂ (toFun t)) (toFun u)) t
  integrable : ∀ s : ActualCanonicalSection E, ActualPathIntegrable s toFun

noncomputable def ActualRegularPath.const {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] (x : E) :
    ActualRegularPath E where
  toFun := fun _ => x
  continuous := continuous_const
  chartDifferentiable := by
    intro t
    exact differentiableAt_const (c := (chartAt ℂ x) x)
  integrable := by
    intro s
    have hzero : actualPathIntegrand s (fun _ => x) = fun _ => 0 := by
      funext t
      simp [actualPathIntegrand, actualOneForm, actualPathVelocity_const]
    simp only [ActualPathIntegrable, hzero]
    exact intervalIntegrable_const

noncomputable def ActualRegularPath.reverse {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) : ActualRegularPath E where
  toFun := fun t => γ.toFun (1 - t)
  continuous := γ.continuous.comp (by fun_prop)
  chartDifferentiable := by
    intro t
    have h := γ.chartDifferentiable (1 - t)
    simpa only [Function.comp_def] using
      h.comp t (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => 1 - u) t)
  integrable := by
    intro s
    have hfun : actualPathIntegrand s (fun t => γ.toFun (1 - t)) =
        fun t => -actualPathIntegrand s γ.toFun (1 - t) := by
      funext t
      exact actualPathIntegrand_reverse s γ.toFun t (γ.chartDifferentiable (1 - t))
    change IntervalIntegrable (actualPathIntegrand s (fun t => γ.toFun (1 - t)))
      MeasureTheory.volume 0 1
    rw [hfun]
    have h := ((γ.integrable s).comp_sub_left 1 (by simp)).neg.symm
    convert h using 1 <;> norm_num

noncomputable def ActualRegularPath.leftHalf {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) : ActualRegularPath E where
  toFun := fun t => γ.toFun (t / 2)
  continuous := γ.continuous.comp (by fun_prop)
  chartDifferentiable := by
    intro t
    simpa only [Function.comp_def] using
      (γ.chartDifferentiable (t / 2)).comp t
        (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => u / 2) t)
  integrable := by
    intro s
    have hhalf : IntervalIntegrable (actualPathIntegrand s γ.toFun)
        MeasureTheory.volume 0 (1 / 2 : ℝ) :=
      (γ.integrable s).mono_set (by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
          Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact Set.Icc_subset_Icc le_rfl (by norm_num))
    have h := hhalf.comp_mul_left (c := (1 / 2 : ℝ))
    have heq : actualPathIntegrand s (fun t => γ.toFun (t / 2)) =
        fun t => (1 / 2 : ℝ) • actualPathIntegrand s γ.toFun (t / 2) := by
      funext t
      simpa [div_eq_mul_inv, mul_comm] using
        actualPathIntegrand_affine s γ.toFun γ.chartDifferentiable
          (1 / 2 : ℝ) 0 t
    change IntervalIntegrable (actualPathIntegrand s (fun t => γ.toFun (t / 2)))
      MeasureTheory.volume 0 1
    rw [heq]
    convert h.smul (1 / 2 : ℝ) using 1 <;> norm_num
    funext t
    simp [Pi.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_eq_mul, div_eq_mul_inv, mul_comm]

abbrev ActualRegularOneChains (E : Type*) [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :=
  ActualRegularPath E →₀ ℤ

noncomputable def actualRegularChainIntegral {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) : ActualRegularOneChains E →ₗ[ℤ] ℂ :=
  Finsupp.linearCombination ℤ
    (fun γ : ActualRegularPath E => actualPathIntegral s γ.toFun)

noncomputable def actualRegularChainBoundary {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualRegularOneChains E →ₗ[ℤ] (E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun γ : ActualRegularPath E =>
    Finsupp.single (γ.toFun 1) 1 - Finsupp.single (γ.toFun 0) 1)

noncomputable def actualRegularPathAsSingular {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).symm
    ⟨fun u => γ.toFun ((TopCat.stdSimplexHomeomorphI.{0} u).down : ℝ),
      by
        apply γ.continuous.comp
        fun_prop⟩

noncomputable def actualRegularChainsToSingular {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualRegularOneChains E →ₗ[ℤ]
      ((TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌ →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (actualRegularPathAsSingular (E := E))

noncomputable def actualRegularPointsToSingular {E : Type*}
    [TopologicalSpace E] : (E →₀ ℤ) →ₗ[ℤ]
      ((TopCat.toSSet.obj (TopCat.of E)) _⦋0⦌ →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ
    (fun x : E => TopCat.toSSetObj₀Equiv.symm x)

theorem actualRegularPathAsSingular_face_zero {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    (TopCat.toSSet.obj (TopCat.of E)).δ (0 : Fin 2)
      (actualRegularPathAsSingular γ) =
      TopCat.toSSetObj₀Equiv.symm (γ.toFun 1) := by
  apply TopCat.toSSetObj₀Equiv.injective
  change (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋0⦌))
    ((TopCat.toSSet.obj (TopCat.of E)).δ (0 : Fin 2)
      (actualRegularPathAsSingular γ)) default = γ.toFun 1
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rw [Subsingleton.elim (default : StdSimplex ℝ (Fin 1)) (StdSimplex.single 0),
    StdSimplex.map_single]
  simp [actualRegularPathAsSingular]

theorem actualRegularPathAsSingular_face_one {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    (TopCat.toSSet.obj (TopCat.of E)).δ (1 : Fin 2)
      (actualRegularPathAsSingular γ) =
      TopCat.toSSetObj₀Equiv.symm (γ.toFun 0) := by
  apply TopCat.toSSetObj₀Equiv.injective
  change (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋0⦌))
    ((TopCat.toSSet.obj (TopCat.of E)).δ (1 : Fin 2)
      (actualRegularPathAsSingular γ)) default = γ.toFun 0
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rw [Subsingleton.elim (default : StdSimplex ℝ (Fin 1)) (StdSimplex.single 0),
    StdSimplex.map_single]
  simp [actualRegularPathAsSingular]

theorem actualRegularChainsToSingular_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    (CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp (TopCat.of E) 0).comp
        (actualRegularChainsToSingular (E := E)) =
      (actualRegularPointsToSingular (E := E)).comp
        (actualRegularChainBoundary (E := E)) := by
  apply Finsupp.lhom_ext
  intro γ n
  simp [actualRegularChainsToSingular, actualRegularPointsToSingular,
    actualRegularChainBoundary]
  rw [show Finsupp.single (actualRegularPathAsSingular γ) n =
    n • Finsupp.single (actualRegularPathAsSingular γ) 1 by simp,
    map_smul,
    CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_two, actualRegularPathAsSingular_face_zero,
    actualRegularPathAsSingular_face_one]
  simp [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, smul_sub]
  abel

theorem actualRegularChainIntegral_single {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ActualRegularPath E) :
    actualRegularChainIntegral s (Finsupp.single γ 1) =
      actualPathIntegral s γ.toFun := by
  simp [actualRegularChainIntegral]

theorem actualRegularChainBoundary_single {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    actualRegularChainBoundary (Finsupp.single γ 1) =
      Finsupp.single (γ.toFun 1) 1 - Finsupp.single (γ.toFun 0) 1 := by
  simp [actualRegularChainBoundary]

theorem actualRegularChainIntegral_reverse {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ActualRegularPath E) :
    actualRegularChainIntegral s
      (Finsupp.single γ 1 + Finsupp.single γ.reverse 1) = 0 := by
  rw [map_add, actualRegularChainIntegral_single, actualRegularChainIntegral_single]
  change actualPathIntegral s γ.toFun +
    actualPathIntegral s (fun t => γ.toFun (1 - t)) = 0
  rw [actualPathIntegral_reverse s γ.toFun γ.chartDifferentiable]
  abel

theorem actualRegularChainBoundary_reverse {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    actualRegularChainBoundary
      (Finsupp.single γ 1 + Finsupp.single γ.reverse 1) = 0 := by
  rw [map_add, actualRegularChainBoundary_single, actualRegularChainBoundary_single]
  change (Finsupp.single (γ.toFun 1) 1 - Finsupp.single (γ.toFun 0) 1) +
    (Finsupp.single (γ.toFun (1 - 1)) 1 -
      Finsupp.single (γ.toFun (1 - 0)) 1) = 0
  norm_num

theorem actualRegularChainIntegral_add {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s t : ActualCanonicalSection E) :
    actualRegularChainIntegral (s + t) =
      actualRegularChainIntegral s + actualRegularChainIntegral t := by
  apply Finsupp.lhom_ext
  intro γ n
  simp [actualRegularChainIntegral, actualPathIntegral_add s t γ.toFun
    (γ.integrable s) (γ.integrable t), smul_add]

theorem actualRegularChainIntegral_smul {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (c : ℂ) (s : ActualCanonicalSection E) :
    actualRegularChainIntegral (c • s) =
      c • actualRegularChainIntegral s := by
  apply Finsupp.lhom_ext
  intro γ n
  simp [actualRegularChainIntegral, actualPathIntegral_smul,
    smul_eq_mul, mul_left_comm]

noncomputable def actualRegularPeriod {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualCanonicalSection E →ₗ[ℂ] (ActualRegularOneChains E →ₗ[ℤ] ℂ) where
  toFun := actualRegularChainIntegral
  map_add' := actualRegularChainIntegral_add
  map_smul' := actualRegularChainIntegral_smul

theorem actualRegularPathIntegral_fixed_chart {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ActualRegularPath E) (q : E)
    (hq : ∀ t : ℝ, γ.toFun t ∈ (chartAt ℂ q).source) :
    actualPathIntegral s γ.toFun =
      ∫ t in (0 : ℝ)..1,
        actualLocalOneForm s q ((chartAt ℂ q) (γ.toFun t))
          (fun _ : Fin 1 =>
            (fderiv ℝ (fun u : ℝ => (chartAt ℂ q) (γ.toFun u)) t) 1) := by
  apply intervalIntegral.integral_congr
  intro t _
  exact actualPathIntegrand_fixed_chart s γ.toFun t q
    γ.continuous.continuousAt (γ.chartDifferentiable t) (hq t)

theorem actualRegularPathIntegral_primitive_sub {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ActualRegularPath E)
    (q : E) (c : ℂ) (r : ℝ) (F : ℂ → ℂ)
    (hq : ∀ t : ℝ, γ.toFun t ∈ (chartAt ℂ q).source)
    (hball : ∀ t : ℝ, (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r)
    (hF : ∀ z ∈ Metric.ball c r,
      HasDerivWithinAt F
        (actualLocalOneForm s q z (fun _ : Fin 1 => (1 : ℂ)))
        (Metric.ball c r) z) :
    actualPathIntegral s γ.toFun =
      F ((chartAt ℂ q) (γ.toFun 1)) - F ((chartAt ℂ q) (γ.toFun 0)) := by
  let z : ℝ → ℂ := fun t => (chartAt ℂ q) (γ.toFun t)
  have hderiv (t : ℝ) : HasDerivAt (F ∘ z)
      (actualPathIntegrand s γ.toFun t) t := by
    have hz : HasDerivAt z ((fderiv ℝ z t) 1) t :=
      (actualPathDifferentiable_fixed_chart γ.toFun t q
        γ.continuous.continuousAt (γ.chartDifferentiable t) (hq t)).hasFDerivAt.hasDerivAt
    have hFa : HasDerivAt F
        (actualLocalOneForm s q (z t) (fun _ : Fin 1 => (1 : ℂ))) (z t) :=
      (hF (z t) (hball t)).hasDerivAt
        (Metric.isOpen_ball.mem_nhds (hball t))
    have hcomp := (hFa.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hz
    convert hcomp using 1
    rw [actualPathIntegrand_fixed_chart s γ.toFun t q
      γ.continuous.continuousAt (γ.chartDifferentiable t) (hq t),
      actualLocalOneForm_apply_eq_mul_coefficient]
    simp [z, ContinuousLinearMap.toSpanSingleton_apply]
  have hint : IntervalIntegrable (deriv (F ∘ z)) MeasureTheory.volume 0 1 := by
    have hfun : deriv (F ∘ z) = actualPathIntegrand s γ.toFun := by
      funext t
      exact (hderiv t).deriv
    rw [hfun]
    exact γ.integrable s
  calc
    actualPathIntegral s γ.toFun = ∫ t in (0 : ℝ)..1, deriv (F ∘ z) t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact (hderiv t).deriv.symm
    _ = F (z 1) - F (z 0) := intervalIntegral.integral_deriv_eq_sub
      (fun t _ => (hderiv t).differentiableAt) hint

theorem actualRegularPathIntegral_closed_in_chart_ball {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (γ : ActualRegularPath E)
    (q : E) (c : ℂ) (r : ℝ)
    (hq : ∀ t : ℝ, γ.toFun t ∈ (chartAt ℂ q).source)
    (hball : ∀ t : ℝ, (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r)
    (hballTarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (hloop : γ.toFun 1 = γ.toFun 0) :
    actualPathIntegral s γ.toFun = 0 := by
  obtain ⟨F, hF⟩ := actualLocalOneForm_has_primitive_on_ball s q c r hballTarget
  rw [actualRegularPathIntegral_primitive_sub s γ q c r F hq hball hF, hloop]
  simp

theorem actualRegularTriangleBoundary_integral_zero {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E)
    (γ01 γ12 γ20 : ActualRegularPath E)
    (q : E) (c : ℂ) (r : ℝ)
    (hq : ∀ γ ∈ ({γ01, γ12, γ20} : Set (ActualRegularPath E)),
      ∀ t : ℝ, γ.toFun t ∈ (chartAt ℂ q).source)
    (hball : ∀ γ ∈ ({γ01, γ12, γ20} : Set (ActualRegularPath E)),
      ∀ t : ℝ, (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r)
    (hballTarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (h01 : γ01.toFun 1 = γ12.toFun 0)
    (h12 : γ12.toFun 1 = γ20.toFun 0)
    (h20 : γ20.toFun 1 = γ01.toFun 0) :
    actualPathIntegral s γ01.toFun + actualPathIntegral s γ12.toFun +
      actualPathIntegral s γ20.toFun = 0 := by
  obtain ⟨F, hF⟩ := actualLocalOneForm_has_primitive_on_ball s q c r hballTarget
  rw [actualRegularPathIntegral_primitive_sub s γ01 q c r F
    (hq γ01 (by simp)) (hball γ01 (by simp)) hF,
    actualRegularPathIntegral_primitive_sub s γ12 q c r F
    (hq γ12 (by simp)) (hball γ12 (by simp)) hF,
    actualRegularPathIntegral_primitive_sub s γ20 q c r F
    (hq γ20 (by simp)) (hball γ20 (by simp)) hF,
    h01, h12, h20]
  abel

structure ActualRegularChartTriangle (E : Type*) [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] where
  edge01 : ActualRegularPath E
  edge12 : ActualRegularPath E
  edge20 : ActualRegularPath E
  chartCenter : E
  ballCenter : ℂ
  radius : ℝ
  edge_source : ∀ γ ∈ ({edge01, edge12, edge20} : Set (ActualRegularPath E)),
    ∀ t : ℝ, γ.toFun t ∈ (chartAt ℂ chartCenter).source
  edge_ball : ∀ γ ∈ ({edge01, edge12, edge20} : Set (ActualRegularPath E)),
    ∀ t : ℝ, (chartAt ℂ chartCenter) (γ.toFun t) ∈ Metric.ball ballCenter radius
  ball_target : Metric.ball ballCenter radius ⊆ (chartAt ℂ chartCenter).target
  endpoint01 : edge01.toFun 1 = edge12.toFun 0
  endpoint12 : edge12.toFun 1 = edge20.toFun 0
  endpoint20 : edge20.toFun 1 = edge01.toFun 0

abbrev ActualRegularChartTwoChains (E : Type*) [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :=
  ActualRegularChartTriangle E →₀ ℤ

noncomputable def actualRegularChartTwoBoundary {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualRegularChartTwoChains E →ₗ[ℤ] ActualRegularOneChains E :=
  Finsupp.linearCombination ℤ (fun Δ : ActualRegularChartTriangle E =>
    Finsupp.single Δ.edge01 1 + Finsupp.single Δ.edge12 1 +
      Finsupp.single Δ.edge20 1)

theorem actualRegularChartTriangle_boundary_cycle {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : ActualRegularChartTriangle E) :
    actualRegularChainBoundary
      (Finsupp.single Δ.edge01 1 + Finsupp.single Δ.edge12 1 +
        Finsupp.single Δ.edge20 1) = 0 := by
  simp only [map_add, actualRegularChainBoundary_single]
  rw [Δ.endpoint01, Δ.endpoint12, Δ.endpoint20]
  abel

theorem actualRegularChartTwoBoundary_boundary_zero {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    (actualRegularChainBoundary (E := E)).comp
      (actualRegularChartTwoBoundary (E := E)) = 0 := by
  apply Finsupp.lhom_ext
  intro Δ n
  simp only [LinearMap.comp_apply, LinearMap.zero_apply,
    actualRegularChartTwoBoundary, Finsupp.linearCombination_single,
    map_smul]
  rw [actualRegularChartTriangle_boundary_cycle, smul_zero]

theorem actualRegularPeriod_vanishes_on_chart_two_boundary {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) :
    (actualRegularChainIntegral s).comp actualRegularChartTwoBoundary = 0 := by
  apply Finsupp.lhom_ext
  intro Δ n
  simp only [LinearMap.comp_apply, LinearMap.zero_apply,
    actualRegularChartTwoBoundary, Finsupp.linearCombination_single,
    map_smul]
  have hΔ := actualRegularTriangleBoundary_integral_zero s
    Δ.edge01 Δ.edge12 Δ.edge20 Δ.chartCenter Δ.ballCenter Δ.radius
    Δ.edge_source Δ.edge_ball Δ.ball_target Δ.endpoint01 Δ.endpoint12 Δ.endpoint20
  simp only [actualRegularChainIntegral, map_add, Finsupp.linearCombination_single,
    one_smul]
  linear_combination (n : ℂ) * hΔ

noncomputable abbrev ActualRegularOneCycles (E : Type*) [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :=
  (actualRegularChainBoundary (E := E)).ker

noncomputable def actualRegularChartTwoBoundaryToCycles {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualRegularChartTwoChains E →ₗ[ℤ] ActualRegularOneCycles E :=
  LinearMap.codRestrict (ActualRegularOneCycles E)
    (actualRegularChartTwoBoundary (E := E)) (fun c => by
      have h := LinearMap.congr_fun
        (actualRegularChartTwoBoundary_boundary_zero (E := E)) c
      simpa [ActualRegularOneCycles] using h)

abbrev ActualRegularChartHomology (E : Type*) [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :=
  ActualRegularOneCycles E ⧸ (actualRegularChartTwoBoundaryToCycles (E := E)).range

noncomputable def actualRegularCyclePeriod {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) : ActualRegularOneCycles E →ₗ[ℤ] ℂ :=
  (actualRegularChainIntegral s).comp (ActualRegularOneCycles E).subtype

theorem actualRegularCyclePeriod_vanishes_on_chart_boundaries {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) :
    (actualRegularChartTwoBoundaryToCycles (E := E)).range ≤
      (actualRegularCyclePeriod s).ker := by
  intro z hz
  obtain ⟨c, rfl⟩ := hz
  have h := LinearMap.congr_fun
    (actualRegularPeriod_vanishes_on_chart_two_boundary s) c
  simpa [actualRegularCyclePeriod, actualRegularChartTwoBoundaryToCycles] using h

noncomputable def actualRegularChartHomologyPeriod {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) : ActualRegularChartHomology E →ₗ[ℤ] ℂ :=
  (actualRegularChartTwoBoundaryToCycles (E := E)).range.liftQ
    (actualRegularCyclePeriod s)
    (actualRegularCyclePeriod_vanishes_on_chart_boundaries s)

theorem actualSingularCycle_fill_contractible (X : Type)
    [TopologicalSpace X] [ContractibleSpace X]
    (c : (TopCat.toSSet.obj (TopCat.of X)) _⦋1⦌ →₀ ℤ)
    (hc : CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp (TopCat.of X) 0 c = 0) :
    ∃ b : (TopCat.toSSet.obj (TopCat.of X)) _⦋2⦌ →₀ ℤ,
      CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp (TopCat.of X) 1 b = c := by
  let K := CurveComplexGenusTwo.CWHurewicz.singularChains X
  let e₁ := CurveComplexGenusTwo.CWHurewicz.singularChainsFinsuppIso (TopCat.of X) 1
  let e₂ := CurveComplexGenusTwo.CWHurewicz.singularChainsFinsuppIso (TopCat.of X) 2
  have hz := CircleHomologyComputation.contractible_positive_homology X 1 (by omega)
  have he : K.ExactAt 1 := (HomologicalComplex.exactAt_iff_isZero_homology _ 1).mpr hz
  have hs := (ShortComplex.moduleCat_exact_iff _).mp he
  change ∀ (x : K.X 1), K.d 1 ((ComplexShape.down ℕ).next 1) x = 0 →
    ∃ b, K.d ((ComplexShape.down ℕ).prev 1) 1 b = x at hs
  rw [ChainComplex.next_nat_succ 0, ChainComplex.prev] at hs
  have hc' : K.d 1 0 (e₁.inv c) = 0 := by
    apply (CurveComplexGenusTwo.CWHurewicz.singularChainsFinsuppIso
      (TopCat.of X) 0).toLinearEquiv.injective
    change CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp
      (TopCat.of X) 0 c = _
    simpa using hc
  obtain ⟨b, hb⟩ := hs (e₁.inv c) hc'
  refine ⟨e₂.hom b, ?_⟩
  change e₁.hom (K.d 2 1 (e₂.inv (e₂.hom b))) = c
  have hc₂ : e₂.inv (e₂.hom b) = b := e₂.toLinearEquiv.left_inv b
  have hc₁ : e₁.hom (e₁.inv c) = c := e₁.toLinearEquiv.right_inv c
  dsimp [K, CurveComplexGenusTwo.CWHurewicz.singularChains] at hb ⊢
  rw [hc₂, hb]
  exact hc₁

abbrev ActualChartBall (E : Type*) [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ) :=
  {x : E // x ∈ (chartAt ℂ q).source ∧ (chartAt ℂ q) x ∈ Metric.ball c r}

noncomputable def actualChartBallHomeomorph {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target) :
    ActualChartBall E q c r ≃ₜ Metric.ball c r where
  toFun x := ⟨(chartAt ℂ q) x.1, x.2.2⟩
  invFun z := ⟨(chartAt ℂ q).symm z.1,
    ⟨(chartAt ℂ q).map_target (htarget z.2), by
      rw [(chartAt ℂ q).right_inv (htarget z.2)]
      exact z.2⟩⟩
  left_inv x := Subtype.ext ((chartAt ℂ q).left_inv x.2.1)
  right_inv z := Subtype.ext ((chartAt ℂ q).right_inv (htarget z.2))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (chartAt ℂ q).continuousOn.comp_continuous
      continuous_subtype_val (fun x => x.2.1)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (chartAt ℂ q).symm.continuousOn.comp_continuous
      continuous_subtype_val (fun z => htarget z.2)

theorem actualChartBall_contractible {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (hne : (Metric.ball c r).Nonempty) :
    ContractibleSpace (ActualChartBall E q c r) := by
  letI : ContractibleSpace (Metric.ball c r) :=
    (convex_ball c r).contractibleSpace hne
  exact (actualChartBallHomeomorph q c r htarget).contractibleSpace

noncomputable def actualChartBallEdge {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ) (γ : ActualRegularPath E)
    (hs : ∀ t, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t, (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    (TopCat.toSSet.obj (TopCat.of (ActualChartBall E q c r))) _⦋1⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of (ActualChartBall E q c r)) (.op ⦋1⦌)).symm
    ⟨fun u => ⟨γ.toFun ((TopCat.stdSimplexHomeomorphI.{0} u).down : ℝ),
      hs _, hb _⟩, by
      apply Continuous.subtype_mk
      exact γ.continuous.comp (by fun_prop)⟩

theorem actualChartBallEdge_face_zero {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ) (γ : ActualRegularPath E)
    (hs : ∀ t, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t, (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    (TopCat.toSSet.obj (TopCat.of (ActualChartBall E q c r))).δ (0 : Fin 2)
      (actualChartBallEdge q c r γ hs hb) =
      TopCat.toSSetObj₀Equiv.symm
        (⟨γ.toFun 1, hs 1, hb 1⟩ : ActualChartBall E q c r) := by
  apply TopCat.toSSetObj₀Equiv.injective
  change (TopCat.toSSetObjEquiv (TopCat.of (ActualChartBall E q c r)) (.op ⦋0⦌))
    ((TopCat.toSSet.obj (TopCat.of (ActualChartBall E q c r))).δ (0 : Fin 2)
      (actualChartBallEdge q c r γ hs hb)) default = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rw [Subsingleton.elim (default : StdSimplex ℝ (Fin 1)) (StdSimplex.single 0),
    StdSimplex.map_single]
  apply Subtype.ext
  simp [actualChartBallEdge]

theorem actualChartBallEdge_face_one {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ) (γ : ActualRegularPath E)
    (hs : ∀ t, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t, (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    (TopCat.toSSet.obj (TopCat.of (ActualChartBall E q c r))).δ (1 : Fin 2)
      (actualChartBallEdge q c r γ hs hb) =
      TopCat.toSSetObj₀Equiv.symm
        (⟨γ.toFun 0, hs 0, hb 0⟩ : ActualChartBall E q c r) := by
  apply TopCat.toSSetObj₀Equiv.injective
  change (TopCat.toSSetObjEquiv (TopCat.of (ActualChartBall E q c r)) (.op ⦋0⦌))
    ((TopCat.toSSet.obj (TopCat.of (ActualChartBall E q c r))).δ (1 : Fin 2)
      (actualChartBallEdge q c r γ hs hb)) default = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rw [Subsingleton.elim (default : StdSimplex ℝ (Fin 1)) (StdSimplex.single 0),
    StdSimplex.map_single]
  apply Subtype.ext
  simp [actualChartBallEdge]

theorem actualChartBallEdge_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ) (γ : ActualRegularPath E)
    (hs : ∀ t, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t, (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    singularBoundaryFinsupp (TopCat.of (ActualChartBall E q c r)) 0
      (Finsupp.single (actualChartBallEdge q c r γ hs hb) 1) =
      Finsupp.single (TopCat.toSSetObj₀Equiv.symm
        (⟨γ.toFun 1, hs 1, hb 1⟩ : ActualChartBall E q c r)) 1 -
      Finsupp.single (TopCat.toSSetObj₀Equiv.symm
        (⟨γ.toFun 0, hs 0, hb 0⟩ : ActualChartBall E q c r)) 1 := by
  rw [singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_two, actualChartBallEdge_face_zero,
    actualChartBallEdge_face_one, sub_eq_add_neg]

noncomputable def actualChartTriangleBallCycle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : ActualRegularChartTriangle E) :
    (TopCat.toSSet.obj (TopCat.of
      (ActualChartBall E Δ.chartCenter Δ.ballCenter Δ.radius))) _⦋1⦌ →₀ ℤ :=
  let hs (γ : ActualRegularPath E)
      (hγ : γ ∈ ({Δ.edge01, Δ.edge12, Δ.edge20} : Set (ActualRegularPath E))) :=
    Δ.edge_source γ hγ
  let hb (γ : ActualRegularPath E)
      (hγ : γ ∈ ({Δ.edge01, Δ.edge12, Δ.edge20} : Set (ActualRegularPath E))) :=
    Δ.edge_ball γ hγ
  Finsupp.single (actualChartBallEdge Δ.chartCenter Δ.ballCenter Δ.radius
      Δ.edge01 (hs Δ.edge01 (by simp)) (hb Δ.edge01 (by simp))) 1 +
    Finsupp.single (actualChartBallEdge Δ.chartCenter Δ.ballCenter Δ.radius
      Δ.edge12 (hs Δ.edge12 (by simp)) (hb Δ.edge12 (by simp))) 1 +
    Finsupp.single (actualChartBallEdge Δ.chartCenter Δ.ballCenter Δ.radius
      Δ.edge20 (hs Δ.edge20 (by simp)) (hb Δ.edge20 (by simp))) 1

theorem actualChartTriangleBallCycle_closed {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : ActualRegularChartTriangle E) :
    singularBoundaryFinsupp (TopCat.of
      (ActualChartBall E Δ.chartCenter Δ.ballCenter Δ.radius)) 0
      (actualChartTriangleBallCycle Δ) = 0 := by
  unfold actualChartTriangleBallCycle
  simp only [map_add]
  rw [actualChartBallEdge_boundary, actualChartBallEdge_boundary,
    actualChartBallEdge_boundary]
  simp only [Δ.endpoint01, Δ.endpoint12, Δ.endpoint20]
  abel

def actualChartBallInclusion {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ) :
    TopCat.of (ActualChartBall E q c r) ⟶ TopCat.of E :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem actualChartBallEdge_push {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ) (γ : ActualRegularPath E)
    (hs : ∀ t, γ.toFun t ∈ (chartAt ℂ q).source)
    (hb : ∀ t, (chartAt ℂ q) (γ.toFun t) ∈ Metric.ball c r) :
    (TopCat.toSSet.map (actualChartBallInclusion q c r)).app (.op ⦋1⦌)
      (actualChartBallEdge q c r γ hs hb) = actualRegularPathAsSingular γ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro u
  rfl

theorem actualChartTriangleBallCycle_push {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : ActualRegularChartTriangle E) :
    singularFinsuppPush
      (actualChartBallInclusion Δ.chartCenter Δ.ballCenter Δ.radius) 1
      (actualChartTriangleBallCycle Δ) =
      actualRegularChainsToSingular
        (actualRegularChartTwoBoundary (Finsupp.single Δ 1)) := by
  unfold actualChartTriangleBallCycle
  simp only [map_add, actualRegularChartTwoBoundary,
    Finsupp.linearCombination_single, one_smul]
  simp [singularFinsuppPush, actualRegularChainsToSingular,
    actualChartBallEdge_push, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

theorem actualChartTriangle_singular_fill {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : ActualRegularChartTriangle E) :
    ∃ b : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ,
      singularBoundaryFinsupp (TopCat.of E) 1 b =
        actualRegularChainsToSingular
          (actualRegularChartTwoBoundary (Finsupp.single Δ 1)) := by
  let X := ActualChartBall E Δ.chartCenter Δ.ballCenter Δ.radius
  have hne : (Metric.ball Δ.ballCenter Δ.radius).Nonempty :=
    ⟨(chartAt ℂ Δ.chartCenter) (Δ.edge01.toFun 0),
      Δ.edge_ball Δ.edge01 (by simp) 0⟩
  letI : ContractibleSpace X :=
    actualChartBall_contractible Δ.chartCenter Δ.ballCenter Δ.radius
      Δ.ball_target hne
  obtain ⟨b, hb⟩ := actualSingularCycle_fill_contractible X
    (actualChartTriangleBallCycle Δ) (actualChartTriangleBallCycle_closed Δ)
  refine ⟨singularFinsuppPush
    (actualChartBallInclusion Δ.chartCenter Δ.ballCenter Δ.radius) 2 b, ?_⟩
  rw [singularFinsuppPush_boundary, hb, actualChartTriangleBallCycle_push]

noncomputable def actualChartTriangleSingularFill {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : ActualRegularChartTriangle E) :
    (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ :=
  Classical.choose (actualChartTriangle_singular_fill Δ)

theorem actualChartTriangleSingularFill_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (Δ : ActualRegularChartTriangle E) :
    singularBoundaryFinsupp (TopCat.of E) 1
      (actualChartTriangleSingularFill Δ) =
        actualRegularChainsToSingular
          (actualRegularChartTwoBoundary (Finsupp.single Δ 1)) :=
  Classical.choose_spec (actualChartTriangle_singular_fill Δ)

noncomputable def actualChartTwoChainsToSingular {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualRegularChartTwoChains E →ₗ[ℤ]
      ((TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ) :=
  Finsupp.linearCombination ℤ (actualChartTriangleSingularFill (E := E))

theorem actualChartTwoChainsToSingular_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    (singularBoundaryFinsupp (TopCat.of E) 1).comp
        (actualChartTwoChainsToSingular (E := E)) =
      (actualRegularChainsToSingular (E := E)).comp
        actualRegularChartTwoBoundary := by
  apply Finsupp.lhom_ext
  intro Δ n
  simp only [LinearMap.comp_apply, actualChartTwoChainsToSingular,
    Finsupp.linearCombination_single, map_smul]
  rw [actualChartTriangleSingularFill_boundary]
  simp [actualRegularChartTwoBoundary, actualRegularChainsToSingular,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Finsupp.mapDomain_add, smul_add]

noncomputable abbrev ActualSingularOneCycles (E : Type) [TopologicalSpace E] :=
  (singularBoundaryFinsupp (TopCat.of E) 0).ker

noncomputable def actualRegularCyclesToSingular {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualRegularOneCycles E →ₗ[ℤ] ActualSingularOneCycles E :=
  (actualRegularChainsToSingular (E := E)).comp
    (ActualRegularOneCycles E).subtype |>.codRestrict _ (by
      intro c
      have hc := c.2
      change actualRegularChainBoundary c.1 = 0 at hc
      have h := LinearMap.congr_fun
        (actualRegularChainsToSingular_boundary (E := E)) c.1
      change singularBoundaryFinsupp (TopCat.of E) 0
          (actualRegularChainsToSingular c.1) =
        actualRegularPointsToSingular (actualRegularChainBoundary c.1) at h
      simpa [hc] using h)

noncomputable def actualSingularTwoBoundaries (E : Type) [TopologicalSpace E] :
    Submodule ℤ (ActualSingularOneCycles E) :=
  LinearMap.range <| LinearMap.codRestrict (ActualSingularOneCycles E)
    (singularBoundaryFinsupp (TopCat.of E) 1) (fun c => by
      exact singularBoundaryFinsupp_comp_zero (TopCat.of E) 0 c)

abbrev ActualSingularHOne (E : Type) [TopologicalSpace E] :=
  ActualSingularOneCycles E ⧸ actualSingularTwoBoundaries E

theorem actualRegularCyclesToSingular_chart_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    (actualRegularChartTwoBoundaryToCycles (E := E)).range ≤
      (actualSingularTwoBoundaries E).comap
        (actualRegularCyclesToSingular (E := E)) := by
  intro z hz
  obtain ⟨c, rfl⟩ := hz
  change actualRegularCyclesToSingular
    (actualRegularChartTwoBoundaryToCycles c) ∈ actualSingularTwoBoundaries E
  refine ⟨actualChartTwoChainsToSingular c, ?_⟩
  apply Subtype.ext
  change singularBoundaryFinsupp (TopCat.of E) 1
      (actualChartTwoChainsToSingular c) =
    actualRegularChainsToSingular (actualRegularChartTwoBoundary c)
  exact LinearMap.congr_fun
    (actualChartTwoChainsToSingular_boundary (E := E)) c

noncomputable def actualRegularChartHomologyToSingular {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualRegularChartHomology E →ₗ[ℤ] ActualSingularHOne E :=
  (actualRegularChartTwoBoundaryToCycles (E := E)).range.liftQ
    ((actualSingularTwoBoundaries E).mkQ.comp
      (actualRegularCyclesToSingular (E := E))) (by
        intro z hz
        exact Submodule.Quotient.mk_eq_zero _ |>.mpr
          (actualRegularCyclesToSingular_chart_boundary (E := E) hz))

theorem actualRegularChartHomologyToSingular_mk {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (z : ActualRegularOneCycles E) :
    actualRegularChartHomologyToSingular
      ((actualRegularChartTwoBoundaryToCycles (E := E)).range.mkQ z) =
      (actualSingularTwoBoundaries E).mkQ (actualRegularCyclesToSingular z) := by
  rfl

set_option maxHeartbeats 1600000 in
noncomputable def actualSingularHOneIsoProject (E : Type)
    [TopologicalSpace E] :
    ModuleCat.of ℤ (ActualSingularHOne E) ≅ CurveComplex.integralHomology E 1 := by
  let K := mvAmbientComplex (TopCat.of E)
  let S := K.sc' 2 1 0
  have htype : S.moduleCatLeftHomologyData.H =
      ModuleCat.of ℤ (ActualSingularHOne E) := rfl
  exact (CategoryTheory.Iso.refl _ ≪≫
    (K.homologyIsoSc' 2 1 0
      ((ComplexShape.down ℕ).prev_eq' (by rfl))
      ((ComplexShape.down ℕ).next_eq' (by rfl)) ≪≫
      S.moduleCatHomologyIso).symm ≪≫
    singularHomologyRepresentation (TopCat.of E) 1)

noncomputable def actualRegularChartHomologyToProject {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualRegularChartHomology E →ₗ[ℤ] CurveComplex.integralHomology E 1 :=
  (actualSingularHOneIsoProject E).hom.hom.comp
    (actualRegularChartHomologyToSingular (E := E))

theorem actualRegularChartHomologyToProject_mk {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (z : ActualRegularOneCycles E) :
    actualRegularChartHomologyToProject
      ((actualRegularChartTwoBoundaryToCycles (E := E)).range.mkQ z) =
    (actualSingularHOneIsoProject E).hom.hom
      ((actualSingularTwoBoundaries E).mkQ (actualRegularCyclesToSingular z)) := by
  exact congrArg (actualSingularHOneIsoProject E).hom.hom
    (actualRegularChartHomologyToSingular_mk z)

noncomputable def actualChartSmoothArc {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z w : Metric.ball c r) : ℝ → E :=
  fun t => (chartAt ℂ q).symm
    (AffineMap.lineMap z.1 w.1 (Real.smoothTransition t))

theorem actualChartSmoothArc_chart_ball {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z w : Metric.ball c r) (t : ℝ) :
    (chartAt ℂ q) (actualChartSmoothArc q c r htarget z w t) ∈
      Metric.ball c r := by
  have hzw : AffineMap.lineMap z.1 w.1 (Real.smoothTransition t) ∈
      Metric.ball c r :=
    (convex_ball c r).mapsTo_lineMap z.2 w.2
      ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  simpa [actualChartSmoothArc, (chartAt ℂ q).right_inv (htarget hzw)] using hzw

theorem actualChartSmoothArc_source {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z w : Metric.ball c r) (t : ℝ) :
    actualChartSmoothArc q c r htarget z w t ∈ (chartAt ℂ q).source := by
  apply (chartAt ℂ q).map_target
  exact htarget ((convex_ball c r).mapsTo_lineMap z.2 w.2
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩)

theorem actualChartSmoothArc_zero {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z w : Metric.ball c r) :
    actualChartSmoothArc q c r htarget z w 0 = (chartAt ℂ q).symm z := by
  simp [actualChartSmoothArc]

theorem actualChartSmoothArc_one {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z w : Metric.ball c r) :
    actualChartSmoothArc q c r htarget z w 1 = (chartAt ℂ q).symm w := by
  simp [actualChartSmoothArc]

theorem actualChartSmoothArc_continuous {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z w : Metric.ball c r) :
    Continuous (actualChartSmoothArc q c r htarget z w) := by
  apply (chartAt ℂ q).symm.continuousOn.comp_continuous
  · exact AffineMap.lineMap_continuous.comp
      Real.smoothTransition.continuous
  · intro t
    exact htarget ((convex_ball c r).mapsTo_lineMap z.2 w.2
      ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩)

theorem actualChartSmoothArc_fixed_chart_contDiff {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z w : Metric.ball c r) :
    ContDiff ℝ ∞ (fun t : ℝ =>
      (chartAt ℂ q) (actualChartSmoothArc q c r htarget z w t)) := by
  have hcoord : (fun t : ℝ =>
      (chartAt ℂ q) (actualChartSmoothArc q c r htarget z w t)) =
      fun t => AffineMap.lineMap z.1 w.1 (Real.smoothTransition t) := by
    funext t
    exact (chartAt ℂ q).right_inv
      (htarget ((convex_ball c r).mapsTo_lineMap z.2 w.2
        ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩))
  rw [hcoord]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  fun_prop

theorem actualChartSmoothArc_chartDifferentiable {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z w : Metric.ball c r) (t : ℝ) :
    DifferentiableAt ℝ (fun u : ℝ =>
      (chartAt ℂ (actualChartSmoothArc q c r htarget z w t))
        (actualChartSmoothArc q c r htarget z w u)) t := by
  let γ := actualChartSmoothArc q c r htarget z w
  let x := γ t
  let f : ℝ → ℂ := fun u => (chartAt ℂ q) (γ u)
  let g : ℂ → ℂ := (chartAt ℂ x) ∘ (chartAt ℂ q).symm
  have hf : DifferentiableAt ℝ f t :=
    (actualChartSmoothArc_fixed_chart_contDiff q c r htarget z w).differentiable
      (by simp) t
  have hx : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hq : x ∈ (chartAt ℂ q).source :=
    actualChartSmoothArc_source q c r htarget z w t
  have hsource : (chartAt ℂ q) x ∈
      (((extChartAt 𝓘(ℂ) q).symm ≫ extChartAt 𝓘(ℂ) x).source) := by
    rw [PartialEquiv.trans_source'', PartialEquiv.symm_symm,
      PartialEquiv.symm_target]
    exact Set.mem_image_of_mem _ ⟨by simpa [extChartAt] using hq,
      by simpa [extChartAt] using hx⟩
  have hg : DifferentiableAt ℂ g ((chartAt ℂ q) x) := by
    have h := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ))
      (n := ∞) x q hsource
    simpa [extChartAt, OpenPartialHomeomorph.extend, g,
      differentiableWithinAt_univ, Function.comp_def] using
      h.differentiableWithinAt (by simp)
  have heq : (fun u : ℝ => (chartAt ℂ x) (γ u)) = g ∘ f := by
    funext u
    simp only [g, f, Function.comp_apply]
    rw [(chartAt ℂ q).left_inv
      (actualChartSmoothArc_source q c r htarget z w u)]
  rw [heq]
  exact (hg.restrictScalars ℝ).comp t hf

theorem actualChartSmoothArc_integrable {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z w : Metric.ball c r) (s : ActualCanonicalSection E) :
    ActualPathIntegrable s (actualChartSmoothArc q c r htarget z w) := by
  let γ := actualChartSmoothArc q c r htarget z w
  let f : ℝ → ℂ := fun t => (chartAt ℂ q) (γ t)
  let a : ℂ → ℂ := fun u => actualLocalOneForm s q u
    (fun _ : Fin 1 => (1 : ℂ))
  have hf : ContDiff ℝ ∞ f :=
    actualChartSmoothArc_fixed_chart_contDiff q c r htarget z w
  have ha : Continuous (fun t : ℝ => a (f t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hat : AnalyticAt ℂ a (f t) :=
      actualLocalOneForm_coefficient_analytic_on_chart s q (γ t)
        (actualChartSmoothArc_source q c r htarget z w t)
    exact hat.continuousAt.comp (hf.continuous.continuousAt)
  have hd : Continuous (fun t : ℝ => (fderiv ℝ f t) 1) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hformula : actualPathIntegrand s γ =
      fun t => ((fderiv ℝ f t) 1) * a (f t) := by
    funext t
    rw [actualPathIntegrand_fixed_chart s γ t q
      ((actualChartSmoothArc_continuous q c r htarget z w).continuousAt)
      (actualChartSmoothArc_chartDifferentiable q c r htarget z w t)
      (actualChartSmoothArc_source q c r htarget z w t),
      actualLocalOneForm_apply_eq_mul_coefficient]
  change IntervalIntegrable (actualPathIntegrand s γ) MeasureTheory.volume 0 1
  rw [hformula]
  exact (hd.mul ha).intervalIntegrable _ _

noncomputable def actualChartBallRegularArc {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z w : Metric.ball c r) : ActualRegularPath E where
  toFun := actualChartSmoothArc q c r htarget z w
  continuous := actualChartSmoothArc_continuous q c r htarget z w
  chartDifferentiable := actualChartSmoothArc_chartDifferentiable q c r htarget z w
  integrable := actualChartSmoothArc_integrable q c r htarget z w

noncomputable def actualContinuousPathAsSingular {E : Type*}
    [TopologicalSpace E] (γ : ℝ → E) (hγ : Continuous γ) :
    (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).symm
    ⟨fun u => γ ((TopCat.stdSimplexHomeomorphI.{0} u).down : ℝ),
      hγ.comp (by fun_prop)⟩

theorem actualContinuousPathAsSingular_face_zero {E : Type*}
    [TopologicalSpace E] (γ : ℝ → E) (hγ : Continuous γ) :
    (TopCat.toSSet.obj (TopCat.of E)).δ (0 : Fin 2)
      (actualContinuousPathAsSingular γ hγ) =
      TopCat.toSSetObj₀Equiv.symm (γ 1) := by
  apply TopCat.toSSetObj₀Equiv.injective
  change (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋0⦌))
    ((TopCat.toSSet.obj (TopCat.of E)).δ (0 : Fin 2)
      (actualContinuousPathAsSingular γ hγ)) default = γ 1
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rw [Subsingleton.elim (default : StdSimplex ℝ (Fin 1)) (StdSimplex.single 0),
    StdSimplex.map_single]
  simp [actualContinuousPathAsSingular]

theorem actualContinuousPathAsSingular_face_one {E : Type*}
    [TopologicalSpace E] (γ : ℝ → E) (hγ : Continuous γ) :
    (TopCat.toSSet.obj (TopCat.of E)).δ (1 : Fin 2)
      (actualContinuousPathAsSingular γ hγ) =
      TopCat.toSSetObj₀Equiv.symm (γ 0) := by
  apply TopCat.toSSetObj₀Equiv.injective
  change (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋0⦌))
    ((TopCat.toSSet.obj (TopCat.of E)).δ (1 : Fin 2)
      (actualContinuousPathAsSingular γ hγ)) default = γ 0
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rw [Subsingleton.elim (default : StdSimplex ℝ (Fin 1)) (StdSimplex.single 0),
    StdSimplex.map_single]
  simp [actualContinuousPathAsSingular]

theorem actualContinuousPathAsSingular_regular {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (γ : ActualRegularPath E) :
    actualContinuousPathAsSingular γ.toFun γ.continuous =
      actualRegularPathAsSingular γ := rfl

theorem actualContinuousPathAsSingular_boundary {E : Type}
    [TopologicalSpace E] (γ : ℝ → E) (hγ : Continuous γ) :
    singularBoundaryFinsupp (TopCat.of E) 0
      (Finsupp.single (actualContinuousPathAsSingular γ hγ) 1) =
    Finsupp.single (TopCat.toSSetObj₀Equiv.symm (γ 1)) 1 -
      Finsupp.single (TopCat.toSSetObj₀Equiv.symm (γ 0)) 1 := by
  rw [singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_two, actualContinuousPathAsSingular_face_zero,
    actualContinuousPathAsSingular_face_one, sub_eq_add_neg]

noncomputable def actualChartBallContinuousEdge {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ) (γ : ℝ → E)
    (hγ : Continuous γ)
    (hs : ∀ t, γ t ∈ (chartAt ℂ q).source)
    (hb : ∀ t, (chartAt ℂ q) (γ t) ∈ Metric.ball c r) :
    (TopCat.toSSet.obj (TopCat.of (ActualChartBall E q c r))) _⦋1⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of (ActualChartBall E q c r)) (.op ⦋1⦌)).symm
    ⟨fun u => ⟨γ ((TopCat.stdSimplexHomeomorphI.{0} u).down : ℝ),
      hs _, hb _⟩, by
      apply Continuous.subtype_mk
      exact hγ.comp (by fun_prop)⟩

theorem actualChartBallContinuousEdge_push {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ) (γ : ℝ → E)
    (hγ : Continuous γ)
    (hs : ∀ t, γ t ∈ (chartAt ℂ q).source)
    (hb : ∀ t, (chartAt ℂ q) (γ t) ∈ Metric.ball c r) :
    (TopCat.toSSet.map (actualChartBallInclusion q c r)).app (.op ⦋1⦌)
      (actualChartBallContinuousEdge q c r γ hγ hs hb) =
      actualContinuousPathAsSingular γ hγ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro u
  rfl

theorem actualChartBallContinuousEdge_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ) (γ : ℝ → E)
    (hγ : Continuous γ)
    (hs : ∀ t, γ t ∈ (chartAt ℂ q).source)
    (hb : ∀ t, (chartAt ℂ q) (γ t) ∈ Metric.ball c r) :
    singularBoundaryFinsupp (TopCat.of (ActualChartBall E q c r)) 0
      (Finsupp.single (actualChartBallContinuousEdge q c r γ hγ hs hb) 1) =
    Finsupp.single (TopCat.toSSetObj₀Equiv.symm
      (⟨γ 1, hs 1, hb 1⟩ : ActualChartBall E q c r)) 1 -
    Finsupp.single (TopCat.toSSetObj₀Equiv.symm
      (⟨γ 0, hs 0, hb 0⟩ : ActualChartBall E q c r)) 1 := by
  let δ : ℝ → ActualChartBall E q c r :=
    fun t => ⟨γ t, hs t, hb t⟩
  have hδ : Continuous δ := by
    apply Continuous.subtype_mk
    exact hγ
  change singularBoundaryFinsupp (TopCat.of (ActualChartBall E q c r)) 0
      (Finsupp.single (actualContinuousPathAsSingular δ hδ) 1) = _
  exact actualContinuousPathAsSingular_boundary δ hδ

theorem actualContinuousChartBallEdge_regularize {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (γ : ℝ → E) (hγ : Continuous γ)
    (hs : ∀ t, γ t ∈ (chartAt ℂ q).source)
    (hb : ∀ t, (chartAt ℂ q) (γ t) ∈ Metric.ball c r) :
    ∃ a : ActualRegularPath E,
      a.toFun 0 = γ 0 ∧ a.toFun 1 = γ 1 ∧
      (∀ t, a.toFun t ∈ (chartAt ℂ q).source) ∧
      (∀ t, (chartAt ℂ q) (a.toFun t) ∈ Metric.ball c r) ∧
      ∃ b : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ,
        singularBoundaryFinsupp (TopCat.of E) 1 b =
          Finsupp.single (actualContinuousPathAsSingular γ hγ) 1 -
          Finsupp.single (actualRegularPathAsSingular a) 1 := by
  let z : Metric.ball c r := ⟨(chartAt ℂ q) (γ 0), hb 0⟩
  let w : Metric.ball c r := ⟨(chartAt ℂ q) (γ 1), hb 1⟩
  let a := actualChartBallRegularArc q c r htarget z w
  have ha0 : a.toFun 0 = γ 0 := by
    change actualChartSmoothArc q c r htarget z w 0 = γ 0
    rw [actualChartSmoothArc_zero]
    change (chartAt ℂ q).symm ((chartAt ℂ q) (γ 0)) = γ 0
    exact (chartAt ℂ q).left_inv (hs 0)
  have ha1 : a.toFun 1 = γ 1 := by
    change actualChartSmoothArc q c r htarget z w 1 = γ 1
    rw [actualChartSmoothArc_one]
    change (chartAt ℂ q).symm ((chartAt ℂ q) (γ 1)) = γ 1
    exact (chartAt ℂ q).left_inv (hs 1)
  have has : ∀ t, a.toFun t ∈ (chartAt ℂ q).source :=
    actualChartSmoothArc_source q c r htarget z w
  have hab : ∀ t, (chartAt ℂ q) (a.toFun t) ∈ Metric.ball c r :=
    actualChartSmoothArc_chart_ball q c r htarget z w
  let X := ActualChartBall E q c r
  let e := actualChartBallContinuousEdge q c r γ hγ hs hb
  let d := actualChartBallEdge q c r a has hab
  have hcycle : singularBoundaryFinsupp (TopCat.of X) 0
      (Finsupp.single e 1 - Finsupp.single d 1) = 0 := by
    simp only [map_sub]
    rw [actualChartBallContinuousEdge_boundary,
      actualChartBallEdge_boundary]
    have h0 : (⟨a.toFun 0, has 0, hab 0⟩ : X) =
        (⟨γ 0, hs 0, hb 0⟩ : X) := Subtype.ext ha0
    have h1 : (⟨a.toFun 1, has 1, hab 1⟩ : X) =
        (⟨γ 1, hs 1, hb 1⟩ : X) := Subtype.ext ha1
    rw [h0, h1]
    abel
  letI : ContractibleSpace X := actualChartBall_contractible q c r
    htarget ⟨z, z.2⟩
  obtain ⟨b, hbfill⟩ := actualSingularCycle_fill_contractible X
    (Finsupp.single e 1 - Finsupp.single d 1) hcycle
  refine ⟨a, ha0, ha1, has, hab,
    singularFinsuppPush (actualChartBallInclusion q c r) 2 b, ?_⟩
  rw [singularFinsuppPush_boundary, hbfill, map_sub]
  simp only [singularFinsuppPush, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  change Finsupp.single
      ((TopCat.toSSet.map (actualChartBallInclusion q c r)).app (.op ⦋1⦌) e) 1 -
      Finsupp.single
        ((TopCat.toSSet.map (actualChartBallInclusion q c r)).app (.op ⦋1⦌) d) 1 = _
  rw [actualChartBallContinuousEdge_push, actualChartBallEdge_push]

noncomputable def actualSingularOneSimplexPath (E : Type) [TopologicalSpace E]
    (σ : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌) : ℝ → E :=
  fun t => (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) σ)
    (TopCat.stdSimplexHomeomorphI.{0}.symm
      (ULift.up (Set.projIcc (0 : ℝ) 1 zero_le_one t)))

theorem actualSingularOneSimplexPath_continuous (E : Type)
    [TopologicalSpace E]
    (σ : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌) :
    Continuous (actualSingularOneSimplexPath E σ) := by
  exact (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) σ).continuous.comp
    (TopCat.stdSimplexHomeomorphI.{0}.symm.continuous.comp
      (by fun_prop))

theorem actualSingularOneSimplexPath_asSingular (E : Type)
    [TopologicalSpace E]
    (σ : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌) :
    actualContinuousPathAsSingular (actualSingularOneSimplexPath E σ)
      (actualSingularOneSimplexPath_continuous E σ) = σ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro u
  change (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) σ)
      (TopCat.stdSimplexHomeomorphI.{0}.symm
        (ULift.up (Set.projIcc (0 : ℝ) 1 zero_le_one
          (TopCat.stdSimplexHomeomorphI.{0} u).down.1))) = _
  rw [Set.projIcc_of_mem zero_le_one
    (TopCat.stdSimplexHomeomorphI.{0} u).down.2]
  change (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) σ)
    (TopCat.stdSimplexHomeomorphI.{0}.symm
      (TopCat.stdSimplexHomeomorphI.{0} u)) = _
  rw [Homeomorph.symm_apply_apply]

theorem actualChartSmallSingularEdge_regularize {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (σ : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌)
    (hs : ∀ u : StdSimplex ℝ (Fin 2),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) σ) u ∈
        (chartAt ℂ q).source)
    (hb : ∀ u : StdSimplex ℝ (Fin 2),
      (chartAt ℂ q)
        ((TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) σ) u) ∈
          Metric.ball c r) :
    ∃ a : ActualRegularPath E,
      a.toFun 0 = actualSingularOneSimplexPath E σ 0 ∧
      a.toFun 1 = actualSingularOneSimplexPath E σ 1 ∧
      (∀ t, a.toFun t ∈ (chartAt ℂ q).source) ∧
      (∀ t, (chartAt ℂ q) (a.toFun t) ∈ Metric.ball c r) ∧
      ∃ b : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ,
        singularBoundaryFinsupp (TopCat.of E) 1 b =
          Finsupp.single σ 1 -
          Finsupp.single (actualRegularPathAsSingular a) 1 := by
  let γ := actualSingularOneSimplexPath E σ
  have hγ := actualSingularOneSimplexPath_continuous E σ
  have hsγ : ∀ t, γ t ∈ (chartAt ℂ q).source := by
    intro t
    exact hs _
  have hbγ : ∀ t, (chartAt ℂ q) (γ t) ∈ Metric.ball c r := by
    intro t
    exact hb _
  obtain ⟨a, ha0, ha1, has, hab, b, hboundary⟩ :=
    actualContinuousChartBallEdge_regularize q c r htarget γ hγ hsγ hbγ
  refine ⟨a, ha0, ha1, has, hab, b, ?_⟩
  have hσ : actualContinuousPathAsSingular γ hγ = σ :=
    actualSingularOneSimplexPath_asSingular E σ
  rw [hσ] at hboundary
  exact hboundary

def actualChartBallOpenSet {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ) : Set E :=
  {x | x ∈ (chartAt ℂ q).source ∧ (chartAt ℂ q) x ∈ Metric.ball c r}

theorem actualChartBallOpenSet_isOpen {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (c : ℂ) (r : ℝ) :
    IsOpen (actualChartBallOpenSet q c r) := by
  exact (chartAt ℂ q).isOpen_inter_preimage Metric.isOpen_ball

theorem actualChartBallOpenSet_at_point {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] (x : E) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target ∧
      x ∈ actualChartBallOpenSet x ((chartAt ℂ x) x) r := by
  have hx : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  obtain ⟨r, hr, htarget⟩ := Metric.isOpen_iff.mp
    (chartAt ℂ x).open_target ((chartAt ℂ x) x)
    ((chartAt ℂ x).map_source hx)
  exact ⟨r, hr, htarget, hx, Metric.mem_ball_self hr⟩

structure ActualChartBallIndex (E : Type*)
    [TopologicalSpace E] [ChartedSpace ℂ E] where
  q : E
  c : ℂ
  r : ℝ
  target : Metric.ball c r ⊆ (chartAt ℂ q).target

def actualChartBallCover {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (i : ActualChartBallIndex E) : Set E :=
  actualChartBallOpenSet i.q i.c i.r

theorem actualChartBallCover_isOpen {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (i : ActualChartBallIndex E) : IsOpen (actualChartBallCover i) :=
  actualChartBallOpenSet_isOpen i.q i.c i.r

theorem actualChartBallCover_covers {E : Type*}
    [TopologicalSpace E] [ChartedSpace ℂ E] (x : E) :
    ∃ i : ActualChartBallIndex E, x ∈ actualChartBallCover i := by
  obtain ⟨r, hr, ht, hx⟩ := actualChartBallOpenSet_at_point x
  exact ⟨⟨x, (chartAt ℂ x) x, r, ht⟩, hx⟩

noncomputable local instance (n : ℕ) :
    MetricSpace (StdSimplex ℝ (Fin (n + 1))) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).comapMetricSpace
    (fun t => (t.weights : Fin (n + 1) → ℝ))

theorem actualSingularSimplex_chartBallLebesgue {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (n : ℕ) (σ : (TopCat.toSSet.obj (TopCat.of E)) _⦋n⦌) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u : StdSimplex ℝ (Fin (n + 1)),
        ∃ i : ActualChartBallIndex E,
          ∀ v ∈ Metric.ball u δ,
            (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋n⦌) σ) v ∈
              actualChartBallCover i := by
  let f := TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋n⦌) σ
  let U : ActualChartBallIndex E → Set (StdSimplex ℝ (Fin (n + 1))) :=
    fun i => f ⁻¹' actualChartBallCover i
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    exact (actualChartBallCover_isOpen i).preimage f.continuous
  have hcover : (Set.univ : Set (StdSimplex ℝ (Fin (n + 1)))) ⊆
      ⋃ i, U i := by
    intro u _
    obtain ⟨i, hi⟩ := actualChartBallCover_covers (f u)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨δ, hδ, hballs⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hU hcover
  refine ⟨δ, hδ, ?_⟩
  intro u
  obtain ⟨i, hi⟩ := hballs u (Set.mem_univ u)
  exact ⟨i, fun v hv => hi hv⟩

theorem actualSingularSimplex_chartBallSubdivision {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (n : ℕ) (σ : (TopCat.toSSet.obj (TopCat.of E)) _⦋n⦌) :
    ∃ k : ℕ,
      ∀ ss : List (Equiv.Perm (Fin (n + 1))), ss.length = k →
        ∃ i : ActualChartBallIndex E,
          ∀ u : StdSimplex ℝ (Fin (n + 1)),
            (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋n⦌) σ)
              (barycentricFlagIterate n ss u) ∈ actualChartBallCover i := by
  obtain ⟨δ, hδ, hcover⟩ := actualSingularSimplex_chartBallLebesgue n σ
  obtain ⟨k, hk⟩ := barycentricFlagIterate_eventually_small n δ hδ
  refine ⟨k, ?_⟩
  intro ss hss
  let t : StdSimplex ℝ (Fin (n + 1)) := .single 0
  obtain ⟨i, hi⟩ := hcover (barycentricFlagIterate n ss t)
  refine ⟨i, fun u => hi _ ?_⟩
  exact Metric.mem_ball.mpr (hk ss hss u t)

theorem actualSingularSimplexFamily_chartBallLebesgue {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (n : ℕ)
    (fs : List ((TopCat.toSSet.obj (TopCat.of E)) _⦋n⦌)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ σ ∈ fs, ∀ u : StdSimplex ℝ (Fin (n + 1)),
        ∃ i : ActualChartBallIndex E,
          ∀ v ∈ Metric.ball u δ,
            (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋n⦌) σ) v ∈
              actualChartBallCover i := by
  induction fs with
  | nil =>
      exact ⟨1, by norm_num, by simp⟩
  | cons σ fs ih =>
      obtain ⟨δσ, hδσ, hσ⟩ := actualSingularSimplex_chartBallLebesgue n σ
      obtain ⟨δfs, hδfs, hfs⟩ := ih
      refine ⟨min δσ δfs, lt_min hδσ hδfs, ?_⟩
      intro τ hτ u
      rcases List.mem_cons.mp hτ with rfl | hτ
      · obtain ⟨i, hi⟩ := hσ u
        refine ⟨i, fun v hv => hi v ?_⟩
        exact Metric.ball_subset_ball (min_le_left _ _) hv
      · obtain ⟨i, hi⟩ := hfs τ hτ u
        refine ⟨i, fun v hv => hi v ?_⟩
        exact Metric.ball_subset_ball (min_le_right _ _) hv

theorem actualSingularSimplexFamily_chartBallSubdivision {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (n : ℕ)
    (fs : List ((TopCat.toSSet.obj (TopCat.of E)) _⦋n⦌)) :
    ∃ k : ℕ,
      ∀ σ ∈ fs,
      ∀ ss : List (Equiv.Perm (Fin (n + 1))), ss.length = k →
        ∃ i : ActualChartBallIndex E,
          ∀ u : StdSimplex ℝ (Fin (n + 1)),
            (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋n⦌) σ)
              (barycentricFlagIterate n ss u) ∈ actualChartBallCover i := by
  obtain ⟨δ, hδ, hcover⟩ := actualSingularSimplexFamily_chartBallLebesgue n fs
  obtain ⟨k, hk⟩ := barycentricFlagIterate_eventually_small n δ hδ
  refine ⟨k, ?_⟩
  intro σ hσ ss hss
  let t : StdSimplex ℝ (Fin (n + 1)) := .single 0
  obtain ⟨i, hi⟩ := hcover σ hσ (barycentricFlagIterate n ss t)
  refine ⟨i, fun u => hi _ ?_⟩
  exact Metric.mem_ball.mpr (hk ss hss u t)

theorem actualSingularBarycentricIterateList_chartSmall {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of E)) _⦋n⦌ →₀ ℤ) :
    ∃ k : ℕ,
      ∀ y ∈ (singularBarycentricIterateList (TopCat.of E) n k c).support,
        ∃ i : ActualChartBallIndex E,
          ∀ u : StdSimplex ℝ (Fin (n + 1)),
            (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋n⦌) y) u ∈
              actualChartBallCover i := by
  let fs : List ((TopCat.toSSet.obj (TopCat.of E)) _⦋n⦌) := c.support.toList
  obtain ⟨k, hk⟩ := actualSingularSimplexFamily_chartBallSubdivision n fs
  refine ⟨k, ?_⟩
  intro y hy
  obtain ⟨x, hx, ss, hlen, rfl⟩ :=
    singularBarycentricIterateList_support (TopCat.of E) n k c y hy
  obtain ⟨i, hi⟩ := hk x (by simpa [fs] using hx) ss hlen
  refine ⟨i, ?_⟩
  intro u
  rw [singularFlagIterate_eval]
  exact hi u

theorem actualSingularBarycentricIterateList_eq_iterate (X : TopCat)
    (n k : ℕ) (c : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) :
    singularBarycentricIterateList X n k c =
      singularBarycentricIterate X n k c := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change singularBarycentricFinsupp X n
          (singularBarycentricIterateList X n k c) =
        singularBarycentricFinsupp X n
          (singularBarycentricIterate X n k c)
      rw [ih]

theorem actualSingularBarycentricIterate_chartSmall {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E]
    (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of E)) _⦋n⦌ →₀ ℤ) :
    ∃ k : ℕ,
      ∀ y ∈ (singularBarycentricIterate (TopCat.of E) n k c).support,
        ∃ i : ActualChartBallIndex E,
          ∀ u : StdSimplex ℝ (Fin (n + 1)),
            (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋n⦌) y) u ∈
              actualChartBallCover i := by
  obtain ⟨k, hk⟩ := actualSingularBarycentricIterateList_chartSmall n c
  refine ⟨k, ?_⟩
  intro y hy
  rw [← actualSingularBarycentricIterateList_eq_iterate] at hy
  exact hk y hy

theorem actualChartSmallSingularChain_regularize {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (c : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌ →₀ ℤ)
    (hc : ∀ y ∈ c.support,
      ∃ i : ActualChartBallIndex E,
        ∀ u : StdSimplex ℝ (Fin 2),
          (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌) y) u ∈
            actualChartBallCover i) :
    ∃ a : ActualRegularOneChains E,
      ∃ b : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ,
        singularBoundaryFinsupp (TopCat.of E) 1 b =
          c - actualRegularChainsToSingular a := by
  classical
  have hlocal (y : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌)
      (hy : y ∈ c.support) :
      ∃ a : ActualRegularPath E,
        ∃ b : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ,
          singularBoundaryFinsupp (TopCat.of E) 1 b =
            Finsupp.single y 1 - Finsupp.single (actualRegularPathAsSingular a) 1 := by
    obtain ⟨i, hi⟩ := hc y hy
    obtain ⟨a, _, _, _, _, b, hb⟩ :=
      actualChartSmallSingularEdge_regularize i.q i.c i.r i.target y
        (fun u => (hi u).1) (fun u => (hi u).2)
    exact ⟨a, b, hb⟩
  choose a b hb using hlocal
  let A : ActualRegularOneChains E :=
    ∑ y ∈ c.support.attach, Finsupp.single (a y.1 y.2) (c y.1)
  let B : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ :=
    ∑ y ∈ c.support.attach, (c y.1) • b y.1 y.2
  refine ⟨A, B, ?_⟩
  have hc_repr : c = ∑ y ∈ c.support, Finsupp.single y (c y) := by
    simpa [Finsupp.sum] using (Finsupp.sum_single c).symm
  rw [hc_repr]
  simp only [B, A, map_sum, map_smul]
  rw [← Finset.sum_attach (s := c.support)
    (f := fun y => Finsupp.single y (c y))]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  rw [show Finsupp.single y.1 (c y.1) =
      (c y.1) • Finsupp.single y.1 1 by simp,
    show Finsupp.single (a y.1 y.2) (c y.1) =
      (c y.1) • Finsupp.single (a y.1 y.2) 1 by simp,
    map_smul, hb y.1 y.2]
  rw [smul_sub]
  congr 1
  simp [actualRegularChainsToSingular, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

theorem actualSingularOneCycle_regularize {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (c : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌ →₀ ℤ)
    (hc : singularBoundaryFinsupp (TopCat.of E) 0 c = 0) :
    ∃ a : ActualRegularOneChains E,
      ∃ b : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ,
        singularBoundaryFinsupp (TopCat.of E) 1 b =
          c - actualRegularChainsToSingular a := by
  obtain ⟨k, hk⟩ := actualSingularBarycentricIterate_chartSmall 1 c
  let c' := singularBarycentricIterate (TopCat.of E) 1 k c
  obtain ⟨a, b, hb⟩ := actualChartSmallSingularChain_regularize c' hk
  have hcarrier := singularCarrierHomotopyIterate_boundary_succ
    (TopCat.of E) 0 k c
  rw [hc, map_zero, add_zero] at hcarrier
  refine ⟨a, b - singularCarrierHomotopyIterate (TopCat.of E) 1 k c, ?_⟩
  rw [map_sub, hb]
  change _ = c - actualRegularChainsToSingular a
  rw [hcarrier]
  abel

theorem actualRegularPointsToSingular_injective {E : Type}
    [TopologicalSpace E] :
    Function.Injective (actualRegularPointsToSingular (E := E)) := by
  intro a b hab
  dsimp only [actualRegularPointsToSingular, Finsupp.lmapDomain_apply] at hab
  exact Finsupp.mapDomain_injective TopCat.toSSetObj₀Equiv.symm.injective hab

theorem actualSingularOneCycle_regularize_cycle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (c : (TopCat.toSSet.obj (TopCat.of E)) _⦋1⦌ →₀ ℤ)
    (hc : singularBoundaryFinsupp (TopCat.of E) 0 c = 0) :
    ∃ a : ActualRegularOneCycles E,
      ∃ b : (TopCat.toSSet.obj (TopCat.of E)) _⦋2⦌ →₀ ℤ,
        singularBoundaryFinsupp (TopCat.of E) 1 b =
          c - actualRegularChainsToSingular a.1 := by
  obtain ⟨a, b, hb⟩ := actualSingularOneCycle_regularize c hc
  have hboundary := congrArg
    (singularBoundaryFinsupp (TopCat.of E) 0) hb
  rw [singularBoundaryFinsupp_comp_zero, map_sub, hc,
    show singularBoundaryFinsupp (TopCat.of E) 0
      (actualRegularChainsToSingular a) =
      actualRegularPointsToSingular (actualRegularChainBoundary a) from
        LinearMap.congr_fun (actualRegularChainsToSingular_boundary (E := E)) a] at hboundary
  have ha : actualRegularChainBoundary a = 0 :=
    actualRegularPointsToSingular_injective (by simpa using hboundary.symm)
  exact ⟨⟨a, ha⟩, b, hb⟩

theorem actualRegularChartHomologyToSingular_surjective {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    Function.Surjective (actualRegularChartHomologyToSingular (E := E)) := by
  intro z
  obtain ⟨c, rfl⟩ :=
    (actualSingularTwoBoundaries E).mkQ_surjective z
  obtain ⟨a, b, hb⟩ :=
    actualSingularOneCycle_regularize_cycle c.1 c.2
  refine ⟨(actualRegularChartTwoBoundaryToCycles (E := E)).range.mkQ a, ?_⟩
  rw [actualRegularChartHomologyToSingular_mk]
  apply Submodule.Quotient.eq _ |>.mpr
  change actualRegularCyclesToSingular a - c ∈ actualSingularTwoBoundaries E
  refine ⟨-b, ?_⟩
  apply Subtype.ext
  change singularBoundaryFinsupp (TopCat.of E) 1 (-b) =
    actualRegularChainsToSingular a.1 - c.1
  rw [map_neg, hb]
  abel

theorem actualRegularChartHomologyToProject_surjective {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    Function.Surjective (actualRegularChartHomologyToProject (E := E)) := by
  intro z
  let y := (actualSingularHOneIsoProject E).inv z
  have hy : (actualSingularHOneIsoProject E).hom y = z := by
    exact (actualSingularHOneIsoProject E).inv_hom_id_apply z
  rw [← hy]
  obtain ⟨x, hx⟩ := actualRegularChartHomologyToSingular_surjective y
  refine ⟨x, ?_⟩
  change (actualSingularHOneIsoProject E).hom
    (actualRegularChartHomologyToSingular x) = _
  rw [hx]

noncomputable def actualChartBallRegularTriangle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (q : E) (c : ℂ) (r : ℝ)
    (htarget : Metric.ball c r ⊆ (chartAt ℂ q).target)
    (z₀ z₁ z₂ : Metric.ball c r) : ActualRegularChartTriangle E where
  edge01 := actualChartBallRegularArc q c r htarget z₀ z₁
  edge12 := actualChartBallRegularArc q c r htarget z₁ z₂
  edge20 := actualChartBallRegularArc q c r htarget z₂ z₀
  chartCenter := q
  ballCenter := c
  radius := r
  edge_source := by
    intro γ hγ t
    rcases hγ with h | h | h
    · subst γ
      exact actualChartSmoothArc_source q c r htarget z₀ z₁ t
    · subst γ
      exact actualChartSmoothArc_source q c r htarget z₁ z₂ t
    · subst γ
      exact actualChartSmoothArc_source q c r htarget z₂ z₀ t
  edge_ball := by
    intro γ hγ t
    rcases hγ with h | h | h
    · subst γ
      exact actualChartSmoothArc_chart_ball q c r htarget z₀ z₁ t
    · subst γ
      exact actualChartSmoothArc_chart_ball q c r htarget z₁ z₂ t
    · subst γ
      exact actualChartSmoothArc_chart_ball q c r htarget z₂ z₀ t
  ball_target := htarget
  endpoint01 := by
    change actualChartSmoothArc q c r htarget z₀ z₁ 1 =
      actualChartSmoothArc q c r htarget z₁ z₂ 0
    rw [actualChartSmoothArc_one, actualChartSmoothArc_zero]
  endpoint12 := by
    change actualChartSmoothArc q c r htarget z₁ z₂ 1 =
      actualChartSmoothArc q c r htarget z₂ z₀ 0
    rw [actualChartSmoothArc_one, actualChartSmoothArc_zero]
  endpoint20 := by
    change actualChartSmoothArc q c r htarget z₂ z₀ 1 =
      actualChartSmoothArc q c r htarget z₀ z₁ 0
    rw [actualChartSmoothArc_one, actualChartSmoothArc_zero]

noncomputable def actualRegularChainModThree {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualRegularOneChains E →ₗ[ℤ] ZMod 3 :=
  Finsupp.linearCombination ℤ (fun _ => 1)

theorem actualRegularChainModThree_triangle_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    (actualRegularChainModThree (E := E)).comp
      (actualRegularChartTwoBoundary (E := E)) = 0 := by
  apply Finsupp.lhom_ext
  intro Δ n
  simp [actualRegularChainModThree, actualRegularChartTwoBoundary,
    Finsupp.linearCombination_single]
  calc
    (n : ZMod 3) + n + n = n * 3 := by ring
    _ = 0 := by
      have h3 : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
      rw [h3, mul_zero]

noncomputable def actualRegularCycleModThree {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualRegularOneCycles E →ₗ[ℤ] ZMod 3 :=
  (actualRegularChainModThree (E := E)).comp (ActualRegularOneCycles E).subtype

theorem actualRegularCycleModThree_chart_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    (actualRegularChartTwoBoundaryToCycles (E := E)).range ≤
      (actualRegularCycleModThree (E := E)).ker := by
  intro z hz
  obtain ⟨c, rfl⟩ := hz
  have h := LinearMap.congr_fun
    (actualRegularChainModThree_triangle_zero (E := E)) c
  simpa [actualRegularCycleModThree, actualRegularChartTwoBoundaryToCycles] using h

noncomputable def actualRegularChartHomologyModThree {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualRegularChartHomology E →ₗ[ℤ] ZMod 3 :=
  (actualRegularChartTwoBoundaryToCycles (E := E)).range.liftQ
    (actualRegularCycleModThree (E := E))
    (actualRegularCycleModThree_chart_zero (E := E))

noncomputable def actualRegularConstantCycle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (x : E) : ActualRegularOneCycles E :=
  ⟨Finsupp.single (ActualRegularPath.const x) 1, by
    change actualRegularChainBoundary _ = 0
    rw [actualRegularChainBoundary_single]
    simp [ActualRegularPath.const]⟩

theorem actualRegularConstantCycle_period_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (x : E) :
    actualRegularCyclePeriod s (actualRegularConstantCycle x) = 0 := by
  change actualRegularChainIntegral s
    (Finsupp.single (ActualRegularPath.const x) 1) = 0
  rw [actualRegularChainIntegral_single]
  exact actualPathIntegral_const s x

theorem actualRegularConstantCycle_modThree {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (x : E) :
    actualRegularChartHomologyModThree
      ((actualRegularChartTwoBoundaryToCycles (E := E)).range.mkQ
        (actualRegularConstantCycle x)) = 1 := by
  simp [actualRegularChartHomologyModThree, actualRegularCycleModThree,
    actualRegularConstantCycle, actualRegularChainModThree]

noncomputable def actualConstantSingularSimplex (E : Type)
    [TopologicalSpace E] (x : E) (n : ℕ) :
    (TopCat.toSSet.obj (TopCat.of E)) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋n⦌)).symm
    (ContinuousMap.const _ x)

theorem actualConstantSingularSimplex_face (E : Type)
    [TopologicalSpace E] (x : E) (n : ℕ) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of E)).δ i
      (actualConstantSingularSimplex E x (n + 1)) =
      actualConstantSingularSimplex E x n := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋n⦌)).injective
  ext t
  rfl

theorem actualRegularConstantPath_singular (E : Type)
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (x : E) :
    actualRegularPathAsSingular (ActualRegularPath.const x) =
      actualConstantSingularSimplex E x 1 := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋1⦌)).injective
  ext t
  rfl

theorem actualConstantSingularSimplex_bounds (E : Type)
    [TopologicalSpace E] (x : E) :
    singularBoundaryFinsupp (TopCat.of E) 1
      (Finsupp.single (actualConstantSingularSimplex E x 2) 1) =
      Finsupp.single (actualConstantSingularSimplex E x 1) 1 := by
  rw [singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_succ, actualConstantSingularSimplex_face]

theorem actualRegularConstantCycle_maps_zero {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (x : E) :
    actualRegularChartHomologyToSingular
      ((actualRegularChartTwoBoundaryToCycles (E := E)).range.mkQ
        (actualRegularConstantCycle x)) = 0 := by
  rw [actualRegularChartHomologyToSingular_mk]
  apply Submodule.Quotient.mk_eq_zero _ |>.mpr
  refine ⟨Finsupp.single (actualConstantSingularSimplex E x 2) 1, ?_⟩
  apply Subtype.ext
  change singularBoundaryFinsupp (TopCat.of E) 1
      (Finsupp.single (actualConstantSingularSimplex E x 2) 1) =
    actualRegularChainsToSingular
      (Finsupp.single (ActualRegularPath.const x) 1)
  rw [actualConstantSingularSimplex_bounds]
  simp [actualRegularChainsToSingular, Finsupp.lmapDomain_apply,
    actualRegularConstantPath_singular]

theorem actualRegularChartHomologyToSingular_not_injective {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (x : E) :
    ¬ Function.Injective (actualRegularChartHomologyToSingular (E := E)) := by
  intro hinj
  have hmap : actualRegularChartHomologyToSingular
      ((actualRegularChartTwoBoundaryToCycles (E := E)).range.mkQ
        (actualRegularConstantCycle x)) =
      actualRegularChartHomologyToSingular 0 := by
    rw [actualRegularConstantCycle_maps_zero, map_zero]
  have hz := hinj hmap
  have h := congrArg (actualRegularChartHomologyModThree (E := E)) hz
  rw [actualRegularConstantCycle_modThree, map_zero] at h
  exact one_ne_zero h

end CanonicalDimensionTwo
