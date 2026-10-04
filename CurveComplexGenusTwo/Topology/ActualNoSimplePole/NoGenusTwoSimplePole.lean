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
import Mathlib.Topology.Connected.Clopen
import Mathlib.LinearAlgebra.Dimension.Finrank
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereProbe
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Covering.Basic
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation

open scoped Manifold ContDiff Bundle
open Bundle
open CategoryTheory CategoryTheory.Limits
open Filter Topology
open Set AlgebraicTopology CurveComplex CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable abbrev ActualCanonicalSection (E : Type*) [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :=
  ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ∞
    (fun x : E => TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial E ℂ x)

noncomputable def actualCanonicalEvaluation {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] (x : E) :
    ActualCanonicalSection E →ₗ[ℂ] ℂ where
  toFun := fun s => s x ((tangentSpaceCastModel 𝓘(ℂ) x).symm 1)
  map_add' := by intro s t; simp
  map_smul' := by intro c s; simp

private theorem actualCanonicalEvaluation_apply_eq_zero_iff_fiber_zero
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (x : E) (s : ActualCanonicalSection E) :
    actualCanonicalEvaluation x s = 0 ↔ s x = 0 := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    change s x v = 0
    let c := tangentSpaceCastModel 𝓘(ℂ) x
    have hv : v = (c v) • c.symm (1 : ℂ) := by
      apply c.injective
      rw [c.map_smul, c.apply_symm_apply]
      simp
    rw [hv, map_smul]
    have hs : s x (c.symm 1) = 0 := h
    simp [hs]
  · intro h
    simp [actualCanonicalEvaluation, h]

private theorem actualCanonicalEvaluation_ne_zero_iff_exists_nonzero_fiber
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (x : E) :
    actualCanonicalEvaluation x ≠ 0 ↔
      ∃ s : ActualCanonicalSection E, s x ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    apply h
    apply LinearMap.ext
    intro s
    exact (actualCanonicalEvaluation_apply_eq_zero_iff_fiber_zero x s).2 (hn s)
  · rintro ⟨s, hs⟩ h
    exact hs ((actualCanonicalEvaluation_apply_eq_zero_iff_fiber_zero x s).1
      (by rw [h]; exact LinearMap.zero_apply s))

private theorem actualCanonicalEvaluation_eq_zero_iff_all_fibers_zero
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (x : E) :
    actualCanonicalEvaluation x = 0 ↔
      ∀ s : ActualCanonicalSection E, s x = 0 := by
  constructor
  · intro h s
    apply (actualCanonicalEvaluation_apply_eq_zero_iff_fiber_zero x s).1
    rw [h]
    exact LinearMap.zero_apply s
  · intro h
    apply LinearMap.ext
    intro s
    exact (actualCanonicalEvaluation_apply_eq_zero_iff_fiber_zero x s).2 (h s)

private theorem actualCanonicalEvaluation_mem_ker_iff_fiber_zero
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (x : E) (s : ActualCanonicalSection E) :
    s ∈ (actualCanonicalEvaluation x).ker ↔ s x = 0 := by
  exact (LinearMap.mem_ker).trans (actualCanonicalEvaluation_apply_eq_zero_iff_fiber_zero x s)

private theorem actualCanonicalSection_cancel_fiber
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (x : E)
    (s t : ActualCanonicalSection E) (hs : s x ≠ 0) :
    let c := actualCanonicalEvaluation x t / actualCanonicalEvaluation x s
    (t - c • s) x = 0 := by
  dsimp only
  have hs' : actualCanonicalEvaluation x s ≠ 0 := by
    intro hz
    exact hs ((actualCanonicalEvaluation_apply_eq_zero_iff_fiber_zero x s).1 hz)
  apply (actualCanonicalEvaluation_apply_eq_zero_iff_fiber_zero x _).1
  rw [map_sub, map_smul]
  simp [hs']

private theorem compact_open_map_surjective
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [PreconnectedSpace Y]
    {f : X → Y} (hf : Continuous f) (ho : IsOpenMap f) :
    Function.Surjective f := by
  have hclosed : IsClosed (Set.range f) := (isCompact_range hf).isClosed
  have hopen : IsOpen (Set.range f) := ho.isOpen_range
  have hn : (Set.range f).Nonempty := ⟨f (Classical.choice inferInstance),
    Set.mem_range_self _⟩
  have htop := (IsClopen.eq_univ ⟨hclosed, hopen⟩ hn)
  exact Set.range_eq_univ.mp htop

private theorem compact_open_injective_map_homeomorph
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [PreconnectedSpace Y]
    {f : X → Y} (hf : Continuous f) (ho : IsOpenMap f)
    (hi : Function.Injective f) :
    Nonempty (X ≃ₜ Y) := by
  have hs := compact_open_map_surjective hf ho
  let e : X ≃ Y := Equiv.ofBijective f ⟨hi, hs⟩
  exact ⟨e.toHomeomorphOfContinuousOpen hf ho⟩

private theorem evaluation_nonzero_of_vanishing_finrank_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hV : Module.finrank ℂ V = 2) (ev : V →ₗ[ℂ] ℂ)
    (hvanish : Module.finrank ℂ ev.ker = 1) : ev ≠ 0 := by
  intro hzero
  have hker : ev.ker = ⊤ := by simp [hzero]
  rw [hker, finrank_top, hV] at hvanish
  omega

private theorem actualCanonicalEvaluation_nonzero_of_RR_finranks
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E]
    [FiniteDimensional ℂ (ActualCanonicalSection E)]
    (hDim : Module.finrank ℂ (ActualCanonicalSection E) = 2)
    (hRR : ∀ x : E, Module.finrank ℂ (actualCanonicalEvaluation x).ker = 1) :
    ∀ x : E, actualCanonicalEvaluation x ≠ 0 := by
  intro x
  exact evaluation_nonzero_of_vanishing_finrank_one hDim _ (hRR x)

private theorem genus_two_no_open_injective_map_to_h1_trivial
    (E Y : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    [TopologicalSpace Y] [T2Space Y] [PreconnectedSpace Y]
    (hg : CurveComplex.IsGenus E 2)
    (hY : IsZero (CurveComplex.integralHomology Y 1))
    (f : E → Y) (hf : Continuous f) (ho : IsOpenMap f) :
    ¬ Function.Injective f := by
  classical
  letI : CurveComplex.ClosedSurface E := Classical.choice hg.2.1
  letI : Nonempty E := hg.1
  intro hi
  obtain ⟨e⟩ := compact_open_injective_map_homeomorph hf ho hi
  have he := CircleHomologyComputation.homotopyHomologyIso e.toHomotopyEquiv 1
  obtain ⟨H⟩ := hg.2.2.2
  have hzero : IsZero (CurveComplex.integralHomology E 1) := hY.of_iso he
  have hzero4 : IsZero (ModuleCat.of ℤ (Fin 4 → ℤ)) := hzero.of_iso H.symm
  letI := ModuleCat.subsingleton_of_isZero hzero4
  have h : (fun _ : Fin 4 => (1 : ℤ)) = (fun _ : Fin 4 => (0 : ℤ)) := Subsingleton.elim _ _
  have hh := congrFun h 0
  norm_num at hh

private noncomputable def onePointPoleExtension
    {X : Type*} [TopologicalSpace X] (p : X) (f : X → ℂ) : X → OnePoint ℂ :=
  by
    classical
    exact fun x => if x = p then OnePoint.infty else (f x : OnePoint ℂ)

private theorem onePointPoleExtension_continuous
    {X : Type*} [TopologicalSpace X] [T1Space X]
    (p : X) (f : X → ℂ)
    (hf : ContinuousOn f ({p}ᶜ : Set X))
    (hpole : Tendsto f (𝓝[≠] p) (Bornology.cobounded ℂ)) :
    Continuous (onePointPoleExtension p f) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = p
  · subst x
    let g := onePointPoleExtension p f
    have hfinfty : Tendsto (fun x : X => (f x : OnePoint ℂ)) (𝓝[≠] p)
        (𝓝 (OnePoint.infty : OnePoint ℂ)) := by
      apply OnePoint.tendsto_coe_infty.comp
      exact hpole.mono_right (by
        rw [Metric.cobounded_eq_cocompact]
        exact Filter.cocompact_le_coclosedCompact)
    have hpunctured : Tendsto g (𝓝[≠] p) (𝓝 (g p)) := by
      have heq : g =ᶠ[𝓝[≠] p] (fun x : X => (f x : OnePoint ℂ)) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        change x ≠ p at hx
        simp [g, onePointPoleExtension, hx]
      simpa [g, onePointPoleExtension] using hfinfty.congr' heq.symm
    change Tendsto g (𝓝 p) (𝓝 (g p))
    rw [← nhdsNE_sup_pure]
    exact hpunctured.sup (tendsto_pure_nhds g p)
  · have hlocal : ContinuousAt f x := hf.continuousAt
        (isOpen_compl_singleton.mem_nhds hx)
    have heq : onePointPoleExtension p f =ᶠ[𝓝 x]
        (fun y : X => (f y : OnePoint ℂ)) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
      change y ≠ p at hy
      simp [onePointPoleExtension, hy]
    exact (OnePoint.continuous_coe.continuousAt.comp hlocal).congr_of_eventuallyEq
      (by simpa [Function.comp_def] using heq)

private theorem chart_meromorphic_pole_tendsto_cobounded
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (f : E → ℂ) (a : ℂ → ℂ)
    (hlocal : f =ᶠ[𝓝[≠] p] fun x => a ((chartAt ℂ p) x))
    (horder : meromorphicOrderAt a ((chartAt ℂ p) p) < 0) :
    Tendsto f (𝓝[≠] p) (Bornology.cobounded ℂ) := by
  let c := chartAt ℂ p
  have hp : p ∈ c.source := mem_chart_source ℂ p
  have hc : Tendsto c (𝓝[≠] p) (𝓝[≠] (c p)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(c.continuousAt hp).tendsto.mono_left nhdsWithin_le_nhds,
        c.eventually_ne_nhdsWithin hp⟩
  exact (tendsto_cobounded_of_meromorphicOrderAt_neg horder).comp hc |>.congr' hlocal.symm

private theorem onePointPoleExtension_continuous_of_chart_pole
    {E : Type*} [TopologicalSpace E] [T1Space E] [ChartedSpace ℂ E]
    (p : E) (f : E → ℂ) (a : ℂ → ℂ)
    (hf : ContinuousOn f ({p}ᶜ : Set E))
    (hlocal : f =ᶠ[𝓝[≠] p] fun x => a ((chartAt ℂ p) x))
    (horder : meromorphicOrderAt a ((chartAt ℂ p) p) < 0) :
    Continuous (onePointPoleExtension p f) :=
  onePointPoleExtension_continuous p f hf
    (chart_meromorphic_pole_tendsto_cobounded p f a hlocal horder)

private theorem onePointPoleExtension_injective_iff
    {E : Type*} [TopologicalSpace E] (p : E) (f : E → ℂ) :
    Function.Injective (onePointPoleExtension p f) ↔
      Set.InjOn f ({p}ᶜ : Set E) := by
  constructor
  · intro hi x hx y hy hxy
    apply hi
    have hx' : x ≠ p := hx
    have hy' : y ≠ p := hy
    simp [onePointPoleExtension, hx', hy', hxy]
  · intro hi x y hxy
    by_cases hx : x = p
    · subst x
      by_cases hy : y = p
      · exact hy.symm
      · have hbad : (OnePoint.infty : OnePoint ℂ) = (f y : OnePoint ℂ) := by
          simpa [onePointPoleExtension, hy] using hxy
        exact False.elim ((OnePoint.infty_ne_coe (f y)) hbad)
    · by_cases hy : y = p
      · subst y
        have hbad : (f x : OnePoint ℂ) = OnePoint.infty := by
          simpa [onePointPoleExtension, hx] using hxy
        exact False.elim ((OnePoint.coe_ne_infty (f x)) hbad)
      · apply hi hx hy
        exact OnePoint.coe_injective (by simpa [onePointPoleExtension, hx, hy] using hxy)

private noncomputable def onePointComplexHomeoSphereTwo :
    OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  apply onePointEquivSphereOfFinrankEq
  norm_num

private theorem chart_analytic_nonconstant_locally_open
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (x : E) (f : E → ℂ) (a : ℂ → ℂ)
    (ha : AnalyticAt ℂ a ((chartAt ℂ x) x))
    (hlocal : f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y))
    (hpoint : f x = a ((chartAt ℂ x) x))
    (hnonconstant : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      a z = a ((chartAt ℂ x) x)) :
    𝓝 (f x) ≤ map f (𝓝 x) := by
  let c := chartAt ℂ x
  have hx : x ∈ c.source := mem_chart_source ℂ x
  have hchart : map c (𝓝 x) = 𝓝 (c x) := c.map_nhds_eq hx
  have hopen : 𝓝 (a (c x)) ≤ map a (𝓝 (c x)) :=
    ha.eventually_constant_or_nhds_le_map_nhds_aux.resolve_left hnonconstant
  rw [hpoint]
  rw [← hchart] at hopen
  calc
    𝓝 (a (c x)) ≤ map (a ∘ c) (𝓝 x) := by simpa [map_map] using hopen
    _ = map f (𝓝 x) := (map_congr hlocal).symm

private theorem onePointPoleExtension_locally_open_away_p
    {E : Type*} [TopologicalSpace E] [T1Space E] [ChartedSpace ℂ E]
    (p x : E) (f : E → ℂ) (a : ℂ → ℂ)
    (hxp : x ≠ p)
    (ha : AnalyticAt ℂ a ((chartAt ℂ x) x))
    (hlocal : f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y))
    (hpoint : f x = a ((chartAt ℂ x) x))
    (hnonconstant : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      a z = a ((chartAt ℂ x) x)) :
    𝓝 (onePointPoleExtension p f x) ≤
      map (onePointPoleExtension p f) (𝓝 x) := by
  have hreg := chart_analytic_nonconstant_locally_open x f a ha hlocal hpoint hnonconstant
  have hnear : onePointPoleExtension p f =ᶠ[𝓝 x]
      (fun y : E => (f y : OnePoint ℂ)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hxp] with y hy
    change y ≠ p at hy
    simp [onePointPoleExtension, hy]
  calc
    𝓝 (onePointPoleExtension p f x) = 𝓝 (f x : OnePoint ℂ) := by
      simp [onePointPoleExtension, hxp]
    _ ≤ map ((↑) : ℂ → OnePoint ℂ) (𝓝 (f x)) := OnePoint.isOpenMap_coe.nhds_le _
    _ ≤ map ((↑) : ℂ → OnePoint ℂ) (map f (𝓝 x)) := map_mono hreg
    _ = map (onePointPoleExtension p f) (𝓝 x) := by
      rw [map_map]
      exact (map_congr hnear).symm

private theorem simplePoleReciprocal_analytic_and_deriv
    (z₀ : ℂ) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ ≠ 0) :
    AnalyticAt ℂ (fun z => (z - z₀) / g z) z₀ ∧
      HasDerivAt (fun z => (z - z₀) / g z) (g z₀)⁻¹ z₀ := by
  have hnum : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ := by
    convert (hasDerivAt_id z₀).sub_const z₀ using 1 <;> simp
  constructor
  · exact (analyticAt_id.sub analyticAt_const).div hg hg0
  · convert hnum.div hg.differentiableAt.hasDerivAt hg0 using 1
      <;> simp [div_eq_mul_inv, pow_two, hg0, mul_assoc]

private theorem simplePoleReciprocal_local_equiv_data
    (z₀ : ℂ) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ ≠ 0) :
    let b := fun z : ℂ => (z - z₀) / g z
    map b (𝓝 z₀) = 𝓝 0 ∧
      ∃ U ∈ 𝓝 z₀, Set.InjOn b U := by
  dsimp only
  obtain ⟨hAnal, hDeriv⟩ := simplePoleReciprocal_analytic_and_deriv z₀ g hg hg0
  have hStrict : HasStrictDerivAt (fun z : ℂ => (z - z₀) / g z)
      (g z₀)⁻¹ z₀ := by
    simpa [hDeriv.deriv] using hAnal.hasStrictDerivAt
  have hb0 : (z₀ - z₀) / g z₀ = (0 : ℂ) := by simp
  constructor
  · simpa [hb0] using hStrict.map_nhds_eq (inv_ne_zero hg0)
  · let b : ℂ → ℂ := fun z => (z - z₀) / g z
    let r := HasStrictDerivAt.localInverse b (g z₀)⁻¹ z₀ hStrict (inv_ne_zero hg0)
    let U : Set ℂ := {z | r (b z) = z}
    have hU : U ∈ 𝓝 z₀ := hStrict.eventually_left_inverse (inv_ne_zero hg0)
    refine ⟨U, hU, ?_⟩
    intro x hx y hy hxy
    change b x = b y at hxy
    calc
      x = r (b x) := hx.symm
      _ = r (b y) := by rw [hxy]
      _ = y := hy

private theorem meromorphicOrder_neg_one_factorization
    (z₀ : ℂ) (a : ℂ → ℂ) (ha : MeromorphicAt a z₀)
    (horder : meromorphicOrderAt a z₀ = (-1 : ℤ)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      a =ᶠ[𝓝[≠] z₀] fun z => g z / (z - z₀) := by
  obtain ⟨g, hg, hg0, heq⟩ := (meromorphicOrderAt_eq_int_iff ha).1 horder
  refine ⟨g, hg, hg0, ?_⟩
  filter_upwards [heq] with z hz
  simpa [div_eq_mul_inv, mul_comm] using hz

private noncomputable def onePointComplexInv : OnePoint ℂ → OnePoint ℂ := by
  classical
  exact fun w => w.elim ((0 : ℂ) : OnePoint ℂ)
    (fun z => if z = 0 then OnePoint.infty else ((z⁻¹ : ℂ) : OnePoint ℂ))

private theorem onePointComplexInv_continuous : Continuous onePointComplexInv := by
  apply (OnePoint.continuous_iff onePointComplexInv).mpr
  constructor
  · change Tendsto (fun z : ℂ => if z = 0 then (OnePoint.infty : OnePoint ℂ)
        else ((z⁻¹ : ℂ) : OnePoint ℂ)) (Filter.coclosedCompact ℂ)
        (𝓝 ((0 : ℂ) : OnePoint ℂ))
    have hInv : Tendsto (fun z : ℂ => ((z⁻¹ : ℂ) : OnePoint ℂ))
        (Filter.coclosedCompact ℂ) (𝓝 ((0 : ℂ) : OnePoint ℂ)) := by
      apply OnePoint.continuous_coe.continuousAt.tendsto.comp
      rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      exact Filter.tendsto_inv₀_cobounded
    apply hInv.congr'
    have hnonzero : {z : ℂ | z ≠ 0} ∈ Filter.coclosedCompact ℂ := by
      exact (show IsCompact ({0} : Set ℂ) from isCompact_singleton).compl_mem_coclosedCompact_of_isClosed isClosed_singleton
    filter_upwards [hnonzero] with z hz
    simp [hz]
  · change Continuous (onePointPoleExtension (0 : ℂ) Inv.inv)
    apply onePointPoleExtension_continuous
    · exact continuousOn_inv₀
    · exact Filter.tendsto_inv₀_nhdsNE_zero

private theorem onePointComplexInv_involutive : Function.Involutive onePointComplexInv := by
  intro w
  induction w using OnePoint.rec with
  | infty => simp [onePointComplexInv]
  | coe z =>
      by_cases hz : z = 0
      · simp [onePointComplexInv, hz]
      · simp [onePointComplexInv, hz, inv_ne_zero hz]

private noncomputable def onePointComplexInvHomeo : OnePoint ℂ ≃ₜ OnePoint ℂ where
  toFun := onePointComplexInv
  invFun := onePointComplexInv
  left_inv := onePointComplexInv_involutive
  right_inv := onePointComplexInv_involutive
  continuous_toFun := onePointComplexInv_continuous
  continuous_invFun := onePointComplexInv_continuous

private theorem onePointPoleExtension_open_at_simple_pole
    {E : Type*} [TopologicalSpace E] (p : E)
    (F G : E → OnePoint ℂ)
    (hFG : onePointComplexInv ∘ F =ᶠ[𝓝 p] G)
    (hG : map G (𝓝 p) = 𝓝 ((0 : ℂ) : OnePoint ℂ)) :
    map F (𝓝 p) = 𝓝 (OnePoint.infty : OnePoint ℂ) := by
  have hcomp : map (onePointComplexInv ∘ F) (𝓝 p) =
      𝓝 ((0 : ℂ) : OnePoint ℂ) := by
    rw [map_congr hFG, hG]
  have hinfty : map onePointComplexInv (𝓝 (OnePoint.infty : OnePoint ℂ)) =
      𝓝 ((0 : ℂ) : OnePoint ℂ) := by
    have hh := onePointComplexInvHomeo.map_nhds_eq (OnePoint.infty : OnePoint ℂ)
    change map onePointComplexInv (𝓝 (OnePoint.infty : OnePoint ℂ)) =
      𝓝 (onePointComplexInv (OnePoint.infty : OnePoint ℂ)) at hh
    simpa [onePointComplexInv] using hh
  have hmap : map onePointComplexInv (map F (𝓝 p)) =
      map onePointComplexInv (𝓝 (OnePoint.infty : OnePoint ℂ)) := by
    rw [hinfty]
    simpa [map_map, Function.comp_def] using hcomp
  have hinv := congrArg (fun l => map onePointComplexInv l) hmap
  have hinvfun : onePointComplexInv ∘ onePointComplexInv ∘ F = F := by
    funext x
    simp only [Function.comp_apply]
    exact onePointComplexInv_involutive (F x)
  have hdouble : onePointComplexInv ∘ onePointComplexInv = id := by
    funext x
    exact onePointComplexInv_involutive x
  have hdoublemap : map onePointComplexInv (map onePointComplexInv
      (𝓝 (OnePoint.infty : OnePoint ℂ))) =
      𝓝 (OnePoint.infty : OnePoint ℂ) := by
    rw [map_map, hdouble, map_id]
  rw [hdoublemap] at hinv
  simpa [map_map, hinvfun] using hinv

private theorem onePointPoleExtension_locally_open_at_simple_pole
    {E : Type*} [TopologicalSpace E] [T1Space E] [ChartedSpace ℂ E]
    (p : E) (f : E → ℂ) (g : ℂ → ℂ)
    (hg : AnalyticAt ℂ g ((chartAt ℂ p) p))
    (hg0 : g ((chartAt ℂ p) p) ≠ 0)
    (hlocal : f =ᶠ[𝓝[≠] p] fun x =>
      g ((chartAt ℂ p) x) / ((chartAt ℂ p) x - (chartAt ℂ p) p)) :
    map (onePointPoleExtension p f) (𝓝 p) =
      𝓝 (OnePoint.infty : OnePoint ℂ) ∧
    ∃ U ∈ 𝓝 p, Set.InjOn (onePointPoleExtension p f) U := by
  let c := chartAt ℂ p
  let z₀ := c p
  let b : ℂ → ℂ := fun z => (z - z₀) / g z
  let F := onePointPoleExtension p f
  let G : E → OnePoint ℂ := fun x => (b (c x) : OnePoint ℂ)
  have hp : p ∈ c.source := mem_chart_source ℂ p
  have hc : map c (𝓝 p) = 𝓝 z₀ := c.map_nhds_eq hp
  obtain ⟨hb, U, hU, hbu⟩ :=
    simplePoleReciprocal_local_equiv_data z₀ g hg hg0
  have hG : map G (𝓝 p) = 𝓝 ((0 : ℂ) : OnePoint ℂ) := by
    calc
      map G (𝓝 p) = map ((↑) : ℂ → OnePoint ℂ) (map b (map c (𝓝 p))) := by
        simp [G, map_map, Function.comp_def]
      _ = 𝓝 ((0 : ℂ) : OnePoint ℂ) := by
        rw [hc, hb, OnePoint.nhds_coe_eq]
  have hgn : ∀ᶠ x in 𝓝 p, g (c x) ≠ 0 :=
    (hg.continuousAt.comp (c.continuousAt hp)).eventually_ne hg0
  have hgn' : ∀ᶠ x in 𝓝[≠] p, g (c x) ≠ 0 :=
    nhdsWithin_le_nhds hgn
  have hcz : ∀ᶠ x in 𝓝[≠] p, c x ≠ z₀ :=
    c.eventually_ne_nhdsWithin hp
  have hFGpunctured : onePointComplexInv ∘ F =ᶠ[𝓝[≠] p] G := by
    filter_upwards [hlocal, hgn', hcz,
      self_mem_nhdsWithin] with x hfx hgx hcx hxp
    have hxp' : x ≠ p := hxp
    have hden : c x - z₀ ≠ 0 := sub_ne_zero.mpr hcx
    have hmodel : f x = g (c x) / (c x - z₀) := hfx
    have hfxne : f x ≠ 0 := by
      rw [hmodel]
      exact div_ne_zero hgx hden
    have hinvmodel : (f x)⁻¹ = b (c x) := by
      rw [hmodel]
      dsimp [b]
      field_simp
    simpa [F, G, onePointComplexInv, onePointPoleExtension, hxp',
      hfxne] using congrArg (fun z : ℂ => (z : OnePoint ℂ)) hinvmodel
  have hFG : onePointComplexInv ∘ F =ᶠ[𝓝 p] G := by
    rw [← nhdsNE_sup_pure]
    apply eventually_sup.mpr
    constructor
    · exact hFGpunctured
    have hpvalue : (onePointComplexInv ∘ F) p = G p := by
      simp [F, G, b, z₀, onePointComplexInv, onePointPoleExtension]
    · simpa only [Filter.eventually_pure] using hpvalue
  constructor
  · exact onePointPoleExtension_open_at_simple_pole p F G hFG hG
  · obtain ⟨S, hS, hSFG⟩ := Filter.Eventually.exists_mem hFG
    refine ⟨S ∩ c.source ∩ c ⁻¹' U, ?_, ?_⟩
    · exact inter_mem (inter_mem hS (c.open_source.mem_nhds hp))
        (by rwa [← hc] at hU)
    · intro x hx y hy hFxy
      have hxS : x ∈ S := hx.1.1
      have hyS : y ∈ S := hy.1.1
      have hxc : x ∈ c.source := hx.1.2
      have hyc : y ∈ c.source := hy.1.2
      have hxU : c x ∈ U := hx.2
      have hyU : c y ∈ U := hy.2
      have hGxy : G x = G y := by
        change F x = F y at hFxy
        rw [← hSFG x hxS, ← hSFG y hyS, Function.comp_apply,
          Function.comp_apply, hFxy]
      have hbc : b (c x) = b (c y) := OnePoint.coe_injective hGxy
      have hcx : c x = c y := hbu hxU hyU hbc
      exact c.injOn hxc hyc hcx

private theorem onePointPoleExtension_locally_open_at_order_neg_one
    {E : Type*} [TopologicalSpace E] [T1Space E] [ChartedSpace ℂ E]
    (p : E) (f : E → ℂ) (a : ℂ → ℂ)
    (ha : MeromorphicAt a ((chartAt ℂ p) p))
    (horder : meromorphicOrderAt a ((chartAt ℂ p) p) = (-1 : ℤ))
    (hlocal : f =ᶠ[𝓝[≠] p] fun x => a ((chartAt ℂ p) x)) :
    map (onePointPoleExtension p f) (𝓝 p) =
      𝓝 (OnePoint.infty : OnePoint ℂ) ∧
    ∃ U ∈ 𝓝 p, Set.InjOn (onePointPoleExtension p f) U := by
  let c := chartAt ℂ p
  have hp : p ∈ c.source := mem_chart_source ℂ p
  have hc : Tendsto c (𝓝[≠] p) (𝓝[≠] (c p)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(c.continuousAt hp).tendsto.mono_left nhdsWithin_le_nhds,
        c.eventually_ne_nhdsWithin hp⟩
  obtain ⟨g, hg, hg0, hmodel⟩ :=
    meromorphicOrder_neg_one_factorization (c p) a ha horder
  have hfmodel : f =ᶠ[𝓝[≠] p] fun x => g (c x) / (c x - c p) := by
    exact hlocal.trans (hmodel.comp_tendsto hc)
  exact onePointPoleExtension_locally_open_at_simple_pole p f g hg hg0 hfmodel

private theorem sphere_two_integral_homology_one_isZero :
    IsZero (CurveComplex.integralHomology
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) 1) := by
  classical
  let puncturedChart (n : ℕ) (v : SphereSpace n) :
      ↥({v}ᶜ : Set (SphereSpace n)) ≃ₜ EuclideanSpace ℝ (Fin n) := by
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) := ⟨by simp⟩
    exact (Homeomorph.setCongr (stereographic'_source v).symm).trans
      ((stereographic' n v).toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr (stereographic'_target v)).trans (Homeomorph.Set.univ _)))
  have puncturedChart_antipode (n : ℕ) (v : SphereSpace n) :
      puncturedChart n v ⟨-v, by simpa using (ne_neg_of_mem_unit_sphere ℝ v).symm⟩ = 0 := by
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) := ⟨by simp⟩
    change (stereographic' n v) (-v) = 0
    simp [stereographic', stereographic_apply_neg]
  have punctured_contractible (n : ℕ) (v : SphereSpace n) :
      ContractibleSpace ↥({v}ᶜ : Set (SphereSpace n)) :=
    (puncturedChart n v).contractibleSpace
  let overlapChart (n : ℕ) (v : SphereSpace n) :
      ↥(({v}ᶜ : Set (SphereSpace n)) ∩ {-v}ᶜ) ≃ₜ
        ↥({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := {
    toFun x := ⟨puncturedChart n v ⟨x.val, x.property.1⟩, by
      change puncturedChart n v ⟨x.val, x.property.1⟩ ≠ 0
      rw [← puncturedChart_antipode n v]
      intro h
      have hh := congrArg Subtype.val ((puncturedChart n v).injective h)
      exact x.property.2 hh⟩
    invFun y := ⟨((puncturedChart n v).symm y.val).val,
      ((puncturedChart n v).symm y.val).property, by
      change ((puncturedChart n v).symm y.val).val ≠ -v
      intro h
      apply y.property
      have hh : (puncturedChart n v).symm y.val =
          ⟨-v, by simpa using (ne_neg_of_mem_unit_sphere ℝ v).symm⟩ := Subtype.ext h
      have := congrArg (puncturedChart n v) hh
      simpa [puncturedChart_antipode] using this⟩
    left_inv x := by apply Subtype.ext; simp
    right_inv y := by apply Subtype.ext; simp
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (puncturedChart n v).continuous.comp (continuous_subtype_val.subtype_mk _)
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp ((puncturedChart n v).symm.continuous.comp continuous_subtype_val)
  }
  have antipodal_open_cover (n : ℕ) (v : SphereSpace n) :
      ({v}ᶜ : Set (SphereSpace n)) ∪ {-v}ᶜ = univ := by
    ext x
    simp only [mem_union, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
    by_cases h : x = v
    · right
      subst x
      exact ne_neg_of_mem_unit_sphere ℝ v
    · exact Or.inl h
  let v : SphereSpace 2 := ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.1 0⟩
  let X := TopCat.of (SphereSpace 2)
  let U : Set X := {v}ᶜ
  let V : Set X := {-v}ᶜ
  let hU : IsOpen U := isClosed_singleton.isOpen_compl
  let hV : IsOpen V := isClosed_singleton.isOpen_compl
  let hc : U ∪ V = univ := antipodal_open_cover 2 v
  letI : ContractibleSpace U := punctured_contractible 2 v
  letI : ContractibleSpace V := punctured_contractible 2 (-v)
  letI : PathConnectedSpace ↥({(0 : EuclideanSpace ℝ (Fin 2))}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_compl_singleton_of_one_lt_rank
      (Module.one_lt_rank_of_one_lt_finrank (by simp)) (0 : EuclideanSpace ℝ (Fin 2)))
  letI : PathConnectedSpace ↥(U ∩ V) := (overlapChart 2 v).symm.pathConnectedSpace
  let RZ := ModuleCat.of ℤ ℤ
  let F := (singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj RZ
  let inc : TopCat.of ↥(U ∩ V) ⟶ TopCat.of U :=
    TopCat.ofHom ⟨fun x => ⟨x.val, x.property.1⟩, by fun_prop⟩
  have hg : Function.Injective (actualMVDifference X U V 0) := by
    apply (injective_iff_map_eq_zero (actualMVDifference X U V 0).hom).mpr
    intro x hx
    have hxu := congrArg Prod.fst hx
    rw [actualMVDifference_apply] at hxu
    change F.map inc x = 0 at hxu
    have he := CircleHomologyComputation.augmentation_naturality inc
    have hex := congrArg (fun m => m x) he
    change (TopCat.of U).singularHomology₀ε RZ (F.map inc x) =
      (TopCat.of ↥(U ∩ V)).singularHomology₀ε RZ x at hex
    rw [hxu, map_zero] at hex
    have hi := (ModuleCat.mono_iff_injective ((TopCat.of ↥(U ∩ V)).singularHomology₀ε RZ)).mp
      (inferInstance : Mono ((TopCat.of ↥(U ∩ V)).singularHomology₀ε RZ))
    apply hi
    simpa using hex.symm
  have hu1 : IsZero (H U 1) := CircleHomologyComputation.contractible_positive_homology U 1 (by omega)
  have hv1 : IsZero (H V 1) := CircleHomologyComputation.contractible_positive_homology V 1 (by omega)
  letI := ModuleCat.subsingleton_of_isZero hu1
  letI := ModuleCat.subsingleton_of_isZero hv1
  have hz (x : H X 1) : x = 0 := by
    have hd : actualMVConnecting X U V hU hV hc 0 x = 0 := by
      apply hg
      have he := congrArg (fun m => m x) (actualMVConnecting_difference X U V hU hV hc 0)
      simpa using he
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (actualMV_exact_ambient X U V hU hV hc 0) x hd
    have hy0 : y = 0 := Subsingleton.elim _ _
    simpa [hy0] using hy.symm
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

private theorem onePoint_complex_integral_homology_one_isZero :
    IsZero (CurveComplex.integralHomology (OnePoint ℂ) 1) := by
  have he := CircleHomologyComputation.homotopyHomologyIso
    onePointComplexHomeoSphereTwo.toHomotopyEquiv 1
  exact sphere_two_integral_homology_one_isZero.of_iso he

private theorem genus_two_no_open_injective_map_to_onePoint_complex
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (F : E → OnePoint ℂ) (hF : Continuous F) (ho : IsOpenMap F) :
    ¬ Function.Injective F := by
  exact genus_two_no_open_injective_map_to_h1_trivial E (OnePoint ℂ) hg
    onePoint_complex_integral_homology_one_isZero F hF ho

private theorem genus_two_simple_pole_global_analytic_map_noninjective
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (p : E) (f : E → ℂ) (a : ℂ → ℂ)
    (hf : ContinuousOn f ({p}ᶜ : Set E))
    (ha : letI : ChartedSpace ℂ E := A;
      MeromorphicAt a ((chartAt ℂ p) p))
    (horder : letI : ChartedSpace ℂ E := A;
      meromorphicOrderAt a ((chartAt ℂ p) p) = (-1 : ℤ))
    (hlocal : letI : ChartedSpace ℂ E := A;
      f =ᶠ[𝓝[≠] p] fun x => a ((chartAt ℂ p) x))
    (hreg : letI : ChartedSpace ℂ E := A;
      ∀ x : E, x ≠ p → ∃ aₓ : ℂ → ℂ,
        AnalyticAt ℂ aₓ ((chartAt ℂ x) x) ∧
        (f =ᶠ[𝓝 x] fun y => aₓ ((chartAt ℂ x) y)) ∧
        f x = aₓ ((chartAt ℂ x) x) ∧
        ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x), aₓ z = aₓ ((chartAt ℂ x) x)) :
    ¬ Set.InjOn f ({p}ᶜ : Set E) := by
  classical
  letI : CurveComplex.ClosedSurface E := Classical.choice hg.2.1
  letI : ChartedSpace ℂ E := A
  have hnegative : meromorphicOrderAt a ((chartAt ℂ p) p) < 0 := by
    rw [horder]
    exact_mod_cast (show (-1 : ℤ) < 0 by omega)
  have hF : Continuous (onePointPoleExtension p f) :=
    onePointPoleExtension_continuous_of_chart_pole p f a hf hlocal hnegative
  have ho : IsOpenMap (onePointPoleExtension p f) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    by_cases hxp : x = p
    · subst x
      have hpole :=
        (onePointPoleExtension_locally_open_at_order_neg_one p f a ha horder hlocal).1
      simpa [onePointPoleExtension] using le_of_eq hpole.symm
    · obtain ⟨aₓ, haₓ, hlocalₓ, hpointₓ, hnonconstantₓ⟩ := hreg x hxp
      exact onePointPoleExtension_locally_open_away_p p x f aₓ hxp haₓ
        hlocalₓ hpointₓ hnonconstantₓ
  intro hi
  exact genus_two_no_open_injective_map_to_onePoint_complex E hg
    (onePointPoleExtension p f) hF ho
    ((onePointPoleExtension_injective_iff p f).2 hi)

private theorem surface_chart_meromorphic_germ_unique
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (x : E) (f : E → ℂ) (a b : ℂ → ℂ)
    (ha : f =ᶠ[𝓝[≠] x] fun y => a ((chartAt ℂ x) y))
    (hb : f =ᶠ[𝓝[≠] x] fun y => b ((chartAt ℂ x) y)) :
    a =ᶠ[𝓝[≠] ((chartAt ℂ x) x)] b := by
  let c := chartAt ℂ x
  have hx : x ∈ c.source := mem_chart_source ℂ x
  have hcx : c x ∈ c.target := c.map_source hx
  have hcsymm0 : Tendsto c.symm (𝓝[≠] (c x))
      (𝓝[≠] (c.symm (c x))) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(c.symm.continuousAt hcx).tendsto.mono_left nhdsWithin_le_nhds,
        c.symm.eventually_ne_nhdsWithin hcx⟩
  have hcsymm : Tendsto c.symm (𝓝[≠] (c x)) (𝓝[≠] x) := by
    simpa [c.left_inv hx] using hcsymm0
  have h12 : (fun y => a (c y)) =ᶠ[𝓝[≠] x] fun y => b (c y) :=
    ha.symm.trans hb
  have h12' := h12.comp_tendsto hcsymm
  have ht : ∀ᶠ z in 𝓝[≠] (c x), z ∈ c.target :=
    nhdsWithin_le_nhds (c.open_target.mem_nhds hcx)
  filter_upwards [h12', ht] with z hz hzt
  simpa [c.right_inv hzt] using hz

private theorem surface_chart_meromorphic_order_unique
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (x : E) (f : E → ℂ) (a b : ℂ → ℂ)
    (ha : f =ᶠ[𝓝[≠] x] fun y => a ((chartAt ℂ x) y))
    (hb : f =ᶠ[𝓝[≠] x] fun y => b ((chartAt ℂ x) y)) :
    meromorphicOrderAt a ((chartAt ℂ x) x) =
      meromorphicOrderAt b ((chartAt ℂ x) x) :=
  meromorphicOrderAt_congr (surface_chart_meromorphic_germ_unique x f a b ha hb)

def SurfaceMeromorphicAt
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (f : E → ℂ) (x : E) : Prop :=
  ∃ a : ℂ → ℂ, MeromorphicAt a ((chartAt ℂ x) x) ∧
    f =ᶠ[𝓝[≠] x] fun y => a ((chartAt ℂ x) y)

noncomputable def surfaceMeromorphicOrderAt
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (f : E → ℂ) (x : E) (h : SurfaceMeromorphicAt f x) : WithTop ℤ :=
  meromorphicOrderAt (Classical.choose h) ((chartAt ℂ x) x)

private theorem surfaceMeromorphicOrderAt_eq_chart_order
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (f : E → ℂ) (x : E) (h : SurfaceMeromorphicAt f x)
    (a : ℂ → ℂ)
    (ha : f =ᶠ[𝓝[≠] x] fun y => a ((chartAt ℂ x) y)) :
    surfaceMeromorphicOrderAt f x h =
      meromorphicOrderAt a ((chartAt ℂ x) x) := by
  exact surface_chart_meromorphic_order_unique x f (Classical.choose h) a
    (Classical.choose_spec h).2 ha

private theorem meromorphicOrder_neg_one_sub_const
    (z₀ : ℂ) (a : ℂ → ℂ) (ha : MeromorphicAt a z₀)
    (horder : meromorphicOrderAt a z₀ = (-1 : ℤ)) (c : ℂ) :
    meromorphicOrderAt (fun z => a z - c) z₀ = (-1 : ℤ) := by
  have hconst : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun _ : ℂ => (-c)) z₀ :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (-c)) z₀).meromorphicOrderAt_nonneg
  have hlt : meromorphicOrderAt a z₀ <
      meromorphicOrderAt (fun _ : ℂ => (-c)) z₀ := by
    rw [horder]
    exact lt_of_lt_of_le (by exact_mod_cast (show (-1 : ℤ) < 0 by omega)) hconst
  have hsum := meromorphicOrderAt_add_eq_left_of_lt
    (MeromorphicAt.const (-c) z₀) hlt
  have hfun : (fun z => a z - c) = a + fun _ => -c := by
    funext z
    simp [sub_eq_add_neg]
  rw [hfun]
  exact hsum.trans horder

private theorem surface_simple_pole_sub_const
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (f : E → ℂ) (p : E) (h : SurfaceMeromorphicAt f p)
    (hpole : surfaceMeromorphicOrderAt f p h = (-1 : ℤ)) (c : ℂ) :
    ∃ hsub : SurfaceMeromorphicAt (fun x => f x - c) p,
      surfaceMeromorphicOrderAt (fun x => f x - c) p hsub = (-1 : ℤ) := by
  let a := Classical.choose h
  have ha : MeromorphicAt a ((chartAt ℂ p) p) := (Classical.choose_spec h).1
  have hlocal : f =ᶠ[𝓝[≠] p] fun y => a ((chartAt ℂ p) y) :=
    (Classical.choose_spec h).2
  have horder : meromorphicOrderAt a ((chartAt ℂ p) p) = (-1 : ℤ) := by
    rwa [surfaceMeromorphicOrderAt_eq_chart_order f p h a hlocal] at hpole
  have hlocalSub : (fun x => f x - c) =ᶠ[𝓝[≠] p]
      fun x => a ((chartAt ℂ p) x) - c := by
    filter_upwards [hlocal] with x hx
    rw [hx]
  let hsub : SurfaceMeromorphicAt (fun x => f x - c) p :=
    ⟨fun z => a z - c, ha.sub (MeromorphicAt.const c _), hlocalSub⟩
  refine ⟨hsub, ?_⟩
  rw [surfaceMeromorphicOrderAt_eq_chart_order _ _ hsub (fun z => a z - c) hlocalSub]
  exact meromorphicOrder_neg_one_sub_const ((chartAt ℂ p) p) a ha horder c

structure SurfaceMeromorphicFunction
    (E : Type*) [TopologicalSpace E] [ChartedSpace ℂ E] where
  toFun : E → ℂ
  meromorphicAt : ∀ x : E, SurfaceMeromorphicAt toFun x

noncomputable def SurfaceMeromorphicFunction.divisorOrder
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (x : E) : WithTop ℤ :=
  surfaceMeromorphicOrderAt F.toFun x (F.meromorphicAt x)

private theorem SurfaceMeromorphicFunction.divisorOrder_eq_chart_order
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (x : E) (a : ℂ → ℂ)
    (ha : F.toFun =ᶠ[𝓝[≠] x] fun y => a ((chartAt ℂ x) y)) :
    F.divisorOrder x = meromorphicOrderAt a ((chartAt ℂ x) x) :=
  surfaceMeromorphicOrderAt_eq_chart_order F.toFun x (F.meromorphicAt x) a ha

private noncomputable def SurfaceMeromorphicFunction.subConst
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (c : ℂ) : SurfaceMeromorphicFunction E where
  toFun := fun x => F.toFun x - c
  meromorphicAt := by
    intro x
    obtain ⟨a, ha, hlocal⟩ := F.meromorphicAt x
    refine ⟨fun z => a z - c, ha.sub (MeromorphicAt.const c _), ?_⟩
    filter_upwards [hlocal] with y hy
    rw [hy]

private theorem SurfaceMeromorphicFunction.simple_pole_subConst_order
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (p : E)
    (hpole : F.divisorOrder p = (-1 : ℤ)) (c : ℂ) :
    (F.subConst c).divisorOrder p = (-1 : ℤ) := by
  obtain ⟨hsub, horder⟩ := surface_simple_pole_sub_const
    F.toFun p (F.meromorphicAt p) hpole c
  exact horder

private theorem SurfaceMeromorphicFunction.fiber_point_has_positive_order
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (x : E) (c : ℂ) (a : ℂ → ℂ)
    (ha : AnalyticAt ℂ a ((chartAt ℂ x) x))
    (hlocal : F.toFun =ᶠ[𝓝[≠] x] fun y => a ((chartAt ℂ x) y))
    (hpoint : F.toFun x = a ((chartAt ℂ x) x))
    (hfiber : F.toFun x = c) :
    0 < (F.subConst c).divisorOrder x := by
  have hsub : (F.subConst c).toFun =ᶠ[𝓝[≠] x]
      fun y => (a ((chartAt ℂ x) y) - c) := by
    filter_upwards [hlocal] with y hy
    exact congrArg (· - c) hy
  rw [(F.subConst c).divisorOrder_eq_chart_order x (fun z => a z - c) hsub]
  have hcont : ContinuousAt (fun z => a z - c) ((chartAt ℂ x) x) :=
    ha.continuousAt.sub continuousAt_const
  have hzero : a ((chartAt ℂ x) x) - c = 0 := by
    rw [← hpoint, hfiber]
    simp
  have htend : Tendsto (fun z => a z - c)
      (𝓝[≠] ((chartAt ℂ x) x)) (𝓝 0) := by
    simpa [hzero] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hmer : MeromorphicAt (fun z => a z - c) ((chartAt ℂ x) x) :=
    (ha.sub analyticAt_const).meromorphicAt
  exact (tendsto_zero_iff_meromorphicOrderAt_pos hmer).1 htend

private theorem SurfaceMeromorphicFunction.fiber_iff_positive_order
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (x : E) (c : ℂ) (a : ℂ → ℂ)
    (ha : AnalyticAt ℂ a ((chartAt ℂ x) x))
    (hlocal : F.toFun =ᶠ[𝓝[≠] x] fun y => a ((chartAt ℂ x) y))
    (hpoint : F.toFun x = a ((chartAt ℂ x) x)) :
    F.toFun x = c ↔ 0 < (F.subConst c).divisorOrder x := by
  constructor
  · exact F.fiber_point_has_positive_order x c a ha hlocal hpoint
  · intro hpos
    have hsub : (F.subConst c).toFun =ᶠ[𝓝[≠] x]
        fun y => (a ((chartAt ℂ x) y) - c) := by
      filter_upwards [hlocal] with y hy
      exact congrArg (· - c) hy
    rw [(F.subConst c).divisorOrder_eq_chart_order x (fun z => a z - c) hsub] at hpos
    have hlim : Tendsto (fun z => a z - c)
        (𝓝[≠] ((chartAt ℂ x) x))
        (𝓝 (a ((chartAt ℂ x) x) - c)) :=
      (ha.continuousAt.sub continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds
    have hzero : a ((chartAt ℂ x) x) - c = 0 :=
      tendsto_nhds_unique hlim (tendsto_zero_of_meromorphicOrderAt_pos hpos)
    rw [hpoint]
    exact sub_eq_zero.mp hzero

private theorem SurfaceMeromorphicFunction.divisorOrder_nonneg_of_analytic_chart
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (x : E) (a : ℂ → ℂ)
    (ha : AnalyticAt ℂ a ((chartAt ℂ x) x))
    (hlocal : F.toFun =ᶠ[𝓝[≠] x] fun y => a ((chartAt ℂ x) y)) :
    0 ≤ F.divisorOrder x := by
  rw [F.divisorOrder_eq_chart_order x a hlocal]
  exact ha.meromorphicOrderAt_nonneg

private theorem SurfaceMeromorphicFunction.subConst_no_other_poles
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (p : E)
    (hreg : ∀ x : E, x ≠ p → ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      F.toFun =ᶠ[𝓝[≠] x] fun y => a ((chartAt ℂ x) y))
    (c : ℂ) :
    ∀ x : E, x ≠ p → 0 ≤ (F.subConst c).divisorOrder x := by
  intro x hxp
  obtain ⟨a, ha, hlocal⟩ := hreg x hxp
  have hsub : (F.subConst c).toFun =ᶠ[𝓝[≠] x]
      fun y => a ((chartAt ℂ x) y) - c := by
    filter_upwards [hlocal] with y hy
    exact congrArg (· - c) hy
  exact (F.subConst c).divisorOrder_nonneg_of_analytic_chart x
    (fun z => a z - c) (ha.sub analyticAt_const) hsub

private theorem surface_analytic_fiber_isolated
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (f : E → ℂ) (x : E) (a : ℂ → ℂ)
    (ha : AnalyticAt ℂ a ((chartAt ℂ x) x))
    (hlocal : f =ᶠ[𝓝[≠] x] fun y => a ((chartAt ℂ x) y))
    (hpoint : f x = a ((chartAt ℂ x) x))
    (hnonconstant : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      a z = a ((chartAt ℂ x) x)) :
    ∀ᶠ y in 𝓝[≠] x, f y ≠ f x := by
  let ch := chartAt ℂ x
  have hx : x ∈ ch.source := mem_chart_source ℂ x
  have hc : Tendsto ch (𝓝[≠] x) (𝓝[≠] (ch x)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(ch.continuousAt hx).tendsto.mono_left nhdsWithin_le_nhds,
        ch.eventually_ne_nhdsWithin hx⟩
  have haev : ∀ᶠ z in 𝓝[≠] (ch x), a z ≠ a (ch x) :=
    (ha.eventually_eq_or_eventually_ne analyticAt_const).resolve_left hnonconstant
  filter_upwards [hlocal, hc haev] with y hfy hne
  rw [hfy, hpoint]
  exact hne

private theorem compact_surface_simple_pole_fiber_finite
    {E : Type*} [TopologicalSpace E] [T2Space E] [CompactSpace E]
    [ChartedSpace ℂ E]
    (p : E) (f : E → ℂ)
    (hF : Continuous (onePointPoleExtension p f))
    (hreg : ∀ x : E, x ≠ p → ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      (f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
      f x = a ((chartAt ℂ x) x) ∧
      ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x), a z = a ((chartAt ℂ x) x))
    (c : ℂ) :
    Set.Finite {x : E | x ≠ p ∧ f x = c} := by
  let s : Set E := {x | x ≠ p ∧ f x = c}
  have hs : s = (onePointPoleExtension p f) ⁻¹' {(c : OnePoint ℂ)} := by
    ext x
    by_cases hx : x = p
    · simp [s, onePointPoleExtension, hx]
    · simp [s, onePointPoleExtension, hx]
  have hclosed : IsClosed s := by
    rw [hs]
    exact isClosed_singleton.preimage hF
  have hcompact : IsCompact s := hclosed.isCompact
  have hdiscrete : IsDiscrete s := by
    apply isDiscrete_iff_nhdsNE.mpr
    intro x hx
    obtain ⟨a, ha, hlocal, hpoint, hnonconstant⟩ := hreg x hx.1
    have hiso := surface_analytic_fiber_isolated f x a ha
      (hlocal.filter_mono nhdsWithin_le_nhds) hpoint hnonconstant
    have hcompl : sᶜ ∈ 𝓝[≠] x := by
      filter_upwards [hiso] with y hy
      intro hys
      exact hy (hys.2.trans hx.2.symm)
    have hd : Disjoint (𝓝[≠] x) (𝓟 s) :=
      Filter.disjoint_iff.mpr
        ⟨sᶜ, hcompl, s, mem_principal_self s,
          Set.disjoint_left.mpr (by intro y hyn hys; exact hyn hys)⟩
    exact disjoint_iff.mp hd
  exact hcompact.finite hdiscrete

private theorem compact_surface_no_everywhere_locally_nonconstant_holomorphic_map
    {E : Type*} [TopologicalSpace E] [T2Space E]
    [CompactSpace E] [Nonempty E] [ChartedSpace ℂ E]
    (f : E → ℂ) (hf : Continuous f)
    (hreg : ∀ x : E, ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      (f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
      f x = a ((chartAt ℂ x) x) ∧
      ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x), a z = a ((chartAt ℂ x) x)) :
    False := by
  have ho : IsOpenMap f := by
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    obtain ⟨a, ha, hlocal, hpoint, hnonconstant⟩ := hreg x
    exact chart_analytic_nonconstant_locally_open x f a ha hlocal hpoint hnonconstant
  have hsurj : Function.Surjective f := compact_open_map_surjective hf ho
  have hcompact : IsCompact (Set.univ : Set ℂ) := by
    simpa [Set.range_eq_univ.mpr hsurj] using isCompact_range hf
  exact (not_compactSpace_iff.mpr inferInstance) (isCompact_univ_iff.mp hcompact)

private theorem analyticAt_eventually_not_locally_constant
    (a : ℂ → ℂ) (z₀ : ℂ) (ha : AnalyticAt ℂ a z₀)
    (hnonconstant : ¬ ∀ᶠ z in 𝓝 z₀, a z = a z₀) :
    ∀ᶠ z in 𝓝 z₀, ¬ ∀ᶠ w in 𝓝 z, a w = a z := by
  obtain ⟨r, hr, hball⟩ := ha.exists_ball_analyticOnNhd
  apply Filter.Eventually.mono (Metric.ball_mem_nhds z₀ hr)
  intro z hz hconst
  have hconstAnalytic : AnalyticOnNhd ℂ (fun _ : ℂ => a z) (Metric.ball z₀ r) :=
    fun _ _ => analyticAt_const
  have hEq : Set.EqOn a (fun _ : ℂ => a z) (Metric.ball z₀ r) :=
    hball.eqOn_of_preconnected_of_eventuallyEq hconstAnalytic
      (convex_ball z₀ r).isPreconnected hz hconst
  have hz₀ : a z₀ = a z := hEq (Metric.mem_ball_self hr)
  apply hnonconstant
  filter_upwards [Metric.ball_mem_nhds z₀ hr] with w hw
  exact (hEq hw).trans hz₀.symm

private theorem surface_chart_eventually_constant_iff
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (x : E) (f : E → ℂ) (a : ℂ → ℂ)
    (hlocal : f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y))
    (hpoint : f x = a ((chartAt ℂ x) x)) :
    (∀ᶠ y in 𝓝 x, f y = f x) ↔
      ∀ᶠ z in 𝓝 ((chartAt ℂ x) x), a z = a ((chartAt ℂ x) x) := by
  let c := chartAt ℂ x
  have hx : x ∈ c.source := mem_chart_source ℂ x
  have hcx : c x ∈ c.target := c.map_source hx
  have hchart : map c (𝓝 x) = 𝓝 (c x) := c.map_nhds_eq hx
  constructor
  · intro hconst
    have hs : (fun y => a (c y)) =ᶠ[𝓝 x] (fun _ => a (c x)) := by
      filter_upwards [hlocal, hconst] with y hfy hcy
      rw [← hfy, hcy, hpoint]
    have hsymm : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
      simpa [c.left_inv hx] using (c.symm.continuousAt hcx).tendsto
    have ht : ∀ᶠ z in 𝓝 (c x), z ∈ c.target := c.open_target.mem_nhds hcx
    filter_upwards [hs.comp_tendsto hsymm, ht] with z hz hzt
    simpa [c.right_inv hzt] using hz
  · intro hconst
    have hs : (fun y => a (c y)) =ᶠ[𝓝 x] (fun _ => a (c x)) := by
      rw [← hchart] at hconst
      exact hconst
    filter_upwards [hlocal, hs] with y hfy hcy
    rw [hfy, hcy, hpoint]

private theorem surface_chart_eventually_not_locally_constant
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (x : E) (f : E → ℂ) (a : ℂ → ℂ)
    (ha : AnalyticAt ℂ a ((chartAt ℂ x) x))
    (hlocal : f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y))
    (hnonconstant : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      a z = a ((chartAt ℂ x) x)) :
    ∀ᶠ y in 𝓝 x, ¬ ∀ᶠ z in 𝓝 y, f z = f y := by
  let c := chartAt ℂ x
  have hx : x ∈ c.source := mem_chart_source ℂ x
  have hnearAnalytic :=
    (c.continuousAt hx).tendsto.eventually
      (analyticAt_eventually_not_locally_constant a (c x) ha hnonconstant)
  have hnearLocal : ∀ᶠ y in 𝓝 x,
      f =ᶠ[𝓝 y] fun z => a (c z) :=
    isOpen_setOfPred_eventually_nhds.mem_nhds hlocal
  filter_upwards [hnearAnalytic, hnearLocal, c.open_source.mem_nhds hx]
    with y hnot hlocaly hy hconst
  have hpointy : f y = a (c y) := hlocaly.eq_of_nhds
  have hconstChart : ∀ᶠ z in 𝓝 y, a (c z) = a (c y) := by
    filter_upwards [hlocaly, hconst] with z hz hcz
    rw [← hz, hcz, hpointy]
  have hconstA : ∀ᶠ z in 𝓝 (c y), a z = a (c y) := by
    rw [← c.map_nhds_eq hy]
    exact hconstChart
  exact hnot hconstA

private theorem surface_global_analytic_constant_or_nowhere_locally_constant
    {E : Type*} [TopologicalSpace E] [PreconnectedSpace E]
    [ChartedSpace ℂ E] (f : E → ℂ)
    (hreg : ∀ x : E, ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      (f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
      f x = a ((chartAt ℂ x) x)) :
    (∀ x y : E, f x = f y) ∨
      ∀ x : E, ¬ ∀ᶠ y in 𝓝 x, f y = f x := by
  let S : Set E := {x | ∀ᶠ y in 𝓝 x, f y = f x}
  have hopenS : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have ho : IsOpen {y : E | ∀ᶠ z in 𝓝 y, f z = f x} :=
      isOpen_setOfPred_eventually_nhds
    apply Filter.mem_of_superset (ho.mem_nhds hx)
    intro y hy
    have hxy : f y = f x := hy.self_of_nhds
    simpa [S, hxy] using hy
  have hopenC : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨a, ha, hlocal, hpoint⟩ := hreg x
    have hnonconstant : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
        a z = a ((chartAt ℂ x) x) := by
      intro hconst
      exact hx ((surface_chart_eventually_constant_iff x f a hlocal hpoint).2 hconst)
    exact surface_chart_eventually_not_locally_constant x f a ha hlocal hnonconstant
  by_cases hS : S.Nonempty
  · have hclosedS : IsClosed S := by simpa using hopenC.isClosed_compl
    have htop : S = Set.univ := IsClopen.eq_univ ⟨hclosedS, hopenS⟩ hS
    left
    apply IsLocallyConstant.iff_is_const.mp
    apply (IsLocallyConstant.iff_eventually_eq f).2
    intro x
    have hx : x ∈ S := by rw [htop]; trivial
    exact hx
  · right
    intro x hx
    exact hS ⟨x, hx⟩

private theorem compact_surface_global_analytic_map_constant
    {E : Type*} [TopologicalSpace E] [T2Space E]
    [CompactSpace E] [Nonempty E] [PreconnectedSpace E]
    [ChartedSpace ℂ E] (f : E → ℂ)
    (hreg : ∀ x : E, ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      (f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
      f x = a ((chartAt ℂ x) x)) :
    ∀ x y : E, f x = f y := by
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨a, ha, hlocal, _⟩ := hreg x
    have hchart : ContinuousAt (chartAt ℂ x) x :=
      (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
    exact (ha.continuousAt.comp hchart).congr_of_eventuallyEq hlocal
  rcases surface_global_analytic_constant_or_nowhere_locally_constant f hreg with h | h
  · exact h
  · exact False.elim <| compact_surface_no_everywhere_locally_nonconstant_holomorphic_map
      f hf (fun x => by
        obtain ⟨a, ha, hlocal, hpoint⟩ := hreg x
        refine ⟨a, ha, hlocal, hpoint, ?_⟩
        intro hconst
        exact h x ((surface_chart_eventually_constant_iff x f a hlocal hpoint).2 hconst))

private theorem complex_punctured_ball_connected (z : ℂ) (r : ℝ) (hr : 0 < r) :
    IsConnected (Metric.ball z r \ {z}) := by
  let F := OpenPartialHomeomorph.univBall z r
  have hsource : F.source = Set.univ := OpenPartialHomeomorph.univBall_source z r
  have htarget : F.target = Metric.ball z r :=
    OpenPartialHomeomorph.univBall_target z hr
  have hF : Continuous F := OpenPartialHomeomorph.continuous_univBall z r
  have hzero : F 0 = z := OpenPartialHomeomorph.univBall_apply_zero z r
  have hi : F '' ({0} : Set ℂ)ᶜ = Metric.ball z r \ {z} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← htarget]
        exact F.map_source (hsource ▸ Set.mem_univ x)
      · intro he
        have hx0 : x = 0 := F.injOn (hsource ▸ Set.mem_univ x)
          (hsource ▸ Set.mem_univ 0)
          ((Set.mem_singleton_iff.mp he).trans hzero.symm)
        exact hx (Set.mem_singleton_iff.mpr hx0)
    · rintro ⟨hy, hyn⟩
      have hyt : y ∈ F.target := htarget ▸ hy
      refine ⟨F.symm y, ?_, F.right_inv hyt⟩
      intro he
      have hyz : y = z := (F.right_inv hyt).symm.trans
        ((congrArg F (Set.mem_singleton_iff.mp he)).trans hzero)
      exact hyn (Set.mem_singleton_iff.mpr hyz)
  rw [← hi]
  exact (isConnected_compl_singleton_of_one_lt_rank
    (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) 0).image F hF.continuousOn

private theorem connected_open_puncture_of_connected_local
    {E : Type} [TopologicalSpace E] [T2Space E]
    [LocallyConnectedSpace E]
    {U N : Set E} (p : E)
    (hU : IsOpen U) (hcU : IsConnected U)
    (hN : IsOpen N) (hpN : p ∈ N) (hNU : N ⊆ U)
    (hcN : IsConnected (N \ {p})) :
    IsConnected (U \ {p}) := by
  obtain ⟨x, hx⟩ := hcN.nonempty
  let C := connectedComponentIn (U \ {p}) x
  have hxU : x ∈ U \ {p} := ⟨hNU hx.1, hx.2⟩
  have hcC : IsConnected C := isConnected_connectedComponentIn_iff.mpr hxU
  have hNC : N \ {p} ⊆ C := hcN.isPreconnected.subset_connectedComponentIn hx
    (fun y hy => ⟨hNU hy.1, hy.2⟩)
  have hCsub : C ⊆ U \ {p} := connectedComponentIn_subset _ _
  have hcomp : CurveComplex.HyperellipticModel.IsComplementComponent
      (Uᶜ ∪ ({p} : Set E)) C := by
    apply CurveComplex.HyperellipticModel.complementComponent_iff_componentIn.mpr
    refine ⟨x, ?_, ?_⟩
    · simpa only [Set.mem_compl_iff, Set.mem_union, not_or, not_not,
        Set.mem_sdiff] using hxU
    · change connectedComponentIn (U \ {p}) x = _
      congr 1
      ext y
      simp [and_comm]
  have hclosed : IsClosed (Uᶜ ∪ {p}) := hU.isClosed_compl.union isClosed_singleton
  have hCopen : IsOpen C :=
    CurveComplex.HyperellipticModel.complementComponent_open hclosed hcomp
  have heq : C ∪ {p} = C ∪ N := by
    ext y
    constructor
    · rintro (hy | hy)
      · exact Or.inl hy
      · exact Or.inr ((mem_singleton_iff.mp hy) ▸ hpN)
    · rintro (hy | hy)
      · exact Or.inl hy
      · by_cases hyp : y = p
        · exact Or.inr (mem_singleton_iff.mpr hyp)
        · exact Or.inl (hNC ⟨hy, hyp⟩)
  have hopen : IsOpen (C ∪ {p}) := heq ▸ hCopen.union hN
  have hfront : frontier C ⊆ Uᶜ ∪ {p} :=
    CurveComplex.HyperellipticModel.complementComponent_frontier_subset hclosed hcomp
  have hall : U ⊆ C ∪ {p} := hcU.isPreconnected.subset_of_closure_inter_subset hopen
    ⟨x, hxU.1, Or.inl (mem_connectedComponentIn hxU)⟩ (by
      rintro y ⟨hy, hyU⟩
      rw [closure_union, isClosed_singleton.closure_eq] at hy
      rcases hy with hy | hy
      · by_cases hyC : y ∈ C
        · exact Or.inl hyC
        · have hf : y ∈ frontier C := by
            rw [frontier, hCopen.interior_eq]
            exact ⟨hy, hyC⟩
          rcases hfront hf with hn | hp
          · exact False.elim (hn hyU)
          · exact Or.inr hp
      · exact Or.inr hy)
  have he : U \ {p} = C := by
    apply Subset.antisymm
    · intro y hy
      exact (hall hy.1).resolve_right hy.2
    · exact hCsub
  exact he.symm ▸ hcC

private theorem complex_chart_has_connected_punctured_neighborhood
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E] (p : E) :
    ∃ N : Set E, IsOpen N ∧ p ∈ N ∧ IsConnected (N \ {p}) := by
  let c := chartAt ℂ p
  have hp : p ∈ c.source := mem_chart_source ℂ p
  have hcp : c p ∈ c.target := c.map_source hp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c p) hcp
  let B := Metric.ball (c p) r
  let N := c.symm '' B
  have hN : IsOpen N := c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hball
  have hpN : p ∈ N := ⟨c p, Metric.mem_ball_self hr, c.left_inv hp⟩
  have himage : c.symm '' (B \ {c p}) = N \ {p} := by
    ext x
    constructor
    · rintro ⟨z, ⟨hzB, hzne⟩, rfl⟩
      refine ⟨⟨z, hzB, rfl⟩, ?_⟩
      intro hzp
      have hz : z = c p := c.symm.injOn (hball hzB)
        hcp ((Set.mem_singleton_iff.mp hzp).trans (c.left_inv hp).symm)
      exact hzne (Set.mem_singleton_iff.mpr hz)
    · rintro ⟨⟨z, hzB, rfl⟩, hzne⟩
      refine ⟨z, ⟨hzB, ?_⟩, rfl⟩
      intro hz
      exact hzne (Set.mem_singleton_iff.mpr
        ((congrArg c.symm (Set.mem_singleton_iff.mp hz)).trans (c.left_inv hp)))
  refine ⟨N, hN, hpN, ?_⟩
  rw [← himage]
  exact (complex_punctured_ball_connected (c p) r hr).image c.symm
    (c.symm.continuousOn.mono (fun z hz => hball hz.1))

private theorem connected_complex_surface_puncture_connected
    (E : Type) [TopologicalSpace E] [T2Space E]
    [ConnectedSpace E] [ChartedSpace ℂ E] (p : E) :
    IsConnected ({p}ᶜ : Set E) := by
  letI : LocallyConnectedSpace E := ChartedSpace.locallyConnectedSpace ℂ E
  obtain ⟨N, hN, hpN, hcN⟩ := complex_chart_has_connected_punctured_neighborhood p
  have h := connected_open_puncture_of_connected_local p
    isOpen_univ isConnected_univ hN hpN (Set.subset_univ _) hcN
  convert h using 1
  ext x
  simp

private theorem surface_analytic_constant_or_nowhere_locally_constant_on_open
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (U : Set E) (hU : IsOpen U) (hcU : IsPreconnected U)
    (f : E → ℂ)
    (hreg : ∀ x ∈ U, ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      (f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
      f x = a ((chartAt ℂ x) x)) :
    (∀ x ∈ U, ∀ y ∈ U, f x = f y) ∨
      ∀ x ∈ U, ¬ ∀ᶠ y in 𝓝 x, f y = f x := by
  let A : Set E := {x | ∀ᶠ y in 𝓝 x, f y = f x}
  let B : Set E := {x | x ∈ U ∧ ¬ ∀ᶠ y in 𝓝 x, f y = f x}
  have hA : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have ho : IsOpen {y : E | ∀ᶠ z in 𝓝 y, f z = f x} :=
      isOpen_setOfPred_eventually_nhds
    apply Filter.mem_of_superset (ho.mem_nhds hx)
    intro y hy
    have hxy : f y = f x := hy.self_of_nhds
    simpa [A, hxy] using hy
  have hB : IsOpen B := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨a, ha, hlocal, hpoint⟩ := hreg x hx.1
    have hnonconstant : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
        a z = a ((chartAt ℂ x) x) := by
      intro hconst
      exact hx.2 ((surface_chart_eventually_constant_iff x f a hlocal hpoint).2 hconst)
    filter_upwards [hU.mem_nhds hx.1,
      surface_chart_eventually_not_locally_constant x f a ha hlocal hnonconstant]
      with y hyU hyNot
    exact ⟨hyU, hyNot⟩
  have hdisj : Disjoint A B := Set.disjoint_left.mpr (by
    intro x hxA hxB
    exact hxB.2 hxA)
  have hcover : U ⊆ A ∪ B := by
    intro x hxU
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr ⟨hxU, hxA⟩
  by_cases hnonempty : (U ∩ A).Nonempty
  · have hUA : U ⊆ A :=
      hcU.subset_left_of_subset_union hA hB hdisj hcover hnonempty
    left
    letI : PreconnectedSpace U := Subtype.preconnectedSpace hcU
    have hlc : IsLocallyConstant (fun x : U => f x.val) := by
      apply (IsLocallyConstant.iff_eventually_eq _).2
      intro x
      exact continuous_subtype_val.continuousAt.tendsto.eventually (hUA x.property)
    intro x hx y hy
    exact (IsLocallyConstant.iff_is_const.mp hlc) ⟨x, hx⟩ ⟨y, hy⟩
  · right
    intro x hx hconst
    exact hnonempty ⟨x, hx, hconst⟩

private theorem simple_pole_germ_not_eventually_constant
    (a : ℂ → ℂ) (z₀ : ℂ)
    (horder : meromorphicOrderAt a z₀ = (-1 : ℤ)) (c : ℂ) :
    ¬ a =ᶠ[𝓝[≠] z₀] (fun _ => c) := by
  intro hconst
  have hsame := meromorphicOrderAt_congr hconst
  have hnonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun _ : ℂ => c) z₀ :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) z₀).meromorphicOrderAt_nonneg
  rw [← hsame, horder] at hnonneg
  exact (show ¬ (0 : WithTop ℤ) ≤ (-1 : ℤ) by decide) hnonneg

private theorem SurfaceMeromorphicFunction.simple_pole_not_constant_away
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (p : E)
    (hpole : F.divisorOrder p = (-1 : ℤ)) (c : ℂ) :
    ¬ ∀ x : E, x ≠ p → F.toFun x = c := by
  intro hconst
  obtain ⟨a, ha, hlocal⟩ := F.meromorphicAt p
  have hconstLocal : F.toFun =ᶠ[𝓝[≠] p] (fun _ => c) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hconst x hx
  have haConst := surface_chart_meromorphic_germ_unique p F.toFun a
    (fun _ => c) hlocal hconstLocal
  have horder : meromorphicOrderAt a ((chartAt ℂ p) p) = (-1 : ℤ) := by
    rwa [F.divisorOrder_eq_chart_order p a hlocal] at hpole
  exact simple_pole_germ_not_eventually_constant a _ horder c haConst

private theorem SurfaceMeromorphicFunction.simple_pole_regular_charts_nonconstant
    (E : Type) [TopologicalSpace E] [T2Space E]
    [ConnectedSpace E] [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (p : E)
    (hpole : F.divisorOrder p = (-1 : ℤ))
    (hreg : ∀ x : E, x ≠ p → ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      (F.toFun =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
      F.toFun x = a ((chartAt ℂ x) x)) :
    ∀ x : E, x ≠ p → ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      (F.toFun =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
      F.toFun x = a ((chartAt ℂ x) x) ∧
      ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x), a z = a ((chartAt ℂ x) x) := by
  have hcU := connected_complex_surface_puncture_connected E p
  have hregU (x : E) (hx : x ∈ ({p}ᶜ : Set E)) :
      ∃ a : ℂ → ℂ,
        AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
        (F.toFun =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
        F.toFun x = a ((chartAt ℂ x) x) :=
    hreg x (by simpa using hx)
  have hnowhere : ∀ x ∈ ({p}ᶜ : Set E),
      ¬ ∀ᶠ y in 𝓝 x, F.toFun y = F.toFun x := by
    rcases surface_analytic_constant_or_nowhere_locally_constant_on_open
      ({p}ᶜ : Set E) isOpen_compl_singleton hcU.isPreconnected
      F.toFun hregU with hconstant | hnonconstant
    · obtain ⟨q, hq⟩ := hcU.nonempty
      exfalso
      apply F.simple_pole_not_constant_away p hpole (F.toFun q)
      intro x hx
      exact hconstant x (by simpa using hx) q hq
    · exact hnonconstant
  intro x hx
  obtain ⟨a, ha, hlocal, hpoint⟩ := hreg x hx
  refine ⟨a, ha, hlocal, hpoint, ?_⟩
  intro hconst
  exact hnowhere x (by simpa using hx)
    ((surface_chart_eventually_constant_iff x F.toFun a hlocal hpoint).2 hconst)

private theorem SurfaceMeromorphicFunction.genus_two_simple_pole_noninjective
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (p : E)
    (hpole : F.divisorOrder p = (-1 : ℤ))
    (hreg : ∀ x : E, x ≠ p → ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      (F.toFun =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
      F.toFun x = a ((chartAt ℂ x) x)) :
    ¬ Set.InjOn F.toFun ({p}ᶜ : Set E) := by
  letI : CurveComplex.ClosedSurface E := Classical.choice hg.2.1
  obtain ⟨a, ha, hlocal⟩ := F.meromorphicAt p
  have horder : meromorphicOrderAt a ((chartAt ℂ p) p) = (-1 : ℤ) := by
    rwa [F.divisorOrder_eq_chart_order p a hlocal] at hpole
  have hf : ContinuousOn F.toFun ({p}ᶜ : Set E) := by
    intro x hx
    obtain ⟨aₓ, haₓ, hlocalₓ, _⟩ := hreg x (by simpa using hx)
    have hchart : ContinuousAt (chartAt ℂ x) x :=
      (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
    exact ((haₓ.continuousAt.comp hchart).congr_of_eventuallyEq hlocalₓ).continuousWithinAt
  have hregStrong := F.simple_pole_regular_charts_nonconstant E p hpole hreg
  exact genus_two_simple_pole_global_analytic_map_noninjective E hg
    (inferInstance : ChartedSpace ℂ E) p F.toFun a hf ha horder hlocal hregStrong

private theorem analyticAt_nonconstant_deriv_isolated_zero
    (a : ℂ → ℂ) (z₀ : ℂ) (ha : AnalyticAt ℂ a z₀)
    (hnonconstant : ¬ ∀ᶠ z in 𝓝 z₀, a z = a z₀) :
    ∀ᶠ z in 𝓝[≠] z₀, deriv a z ≠ 0 := by
  have hnotzero : ¬ ∀ᶠ z in 𝓝 z₀, deriv a z = 0 := by
    intro hzero
    have horder : analyticOrderAt (deriv a) z₀ = ⊤ :=
      analyticOrderAt_eq_top.mpr hzero
    have hsuborder : analyticOrderAt (fun z => a z - a z₀) z₀ = ⊤ := by
      simpa [horder] using (ha.analyticOrderAt_deriv_add_one).symm
    exact hnonconstant (by
      simpa [sub_eq_zero] using (analyticOrderAt_eq_top.mp hsuborder))
  exact (ha.deriv.eventually_eq_zero_or_eventually_ne_zero).resolve_left hnotzero

private def LocallyInjectiveAt
    {X Y : Type*} [TopologicalSpace X] (f : X → Y) (x : X) : Prop :=
  ∃ U : Set X, U ∈ 𝓝 x ∧ Set.InjOn f U

private theorem isOpen_locallyInjectiveAt
    {X Y : Type*} [TopologicalSpace X] (f : X → Y) :
    IsOpen {x : X | LocallyInjectiveAt f x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hU, hinj⟩ := hx
  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
  apply Filter.mem_of_superset (hVopen.mem_nhds hxV)
  intro y hy
  exact ⟨U, Filter.mem_of_superset (hVopen.mem_nhds hy) hVU, hinj⟩

private theorem analyticAt_deriv_ne_zero_locally_injective
    (a : ℂ → ℂ) (z : ℂ) (ha : AnalyticAt ℂ a z)
    (hd : deriv a z ≠ 0) :
    LocallyInjectiveAt a z := by
  let r := HasStrictDerivAt.localInverse a (deriv a z) z
    ha.hasStrictDerivAt hd
  let U : Set ℂ := {w | r (a w) = w}
  have hU : U ∈ 𝓝 z := ha.hasStrictDerivAt.eventually_left_inverse hd
  refine ⟨U, hU, ?_⟩
  intro x hx y hy hxy
  calc
    x = r (a x) := hx.symm
    _ = r (a y) := by rw [hxy]
    _ = y := hy

private theorem surface_chart_deriv_ne_zero_locally_injective
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (f : E → ℂ) (x : E) (a : ℂ → ℂ)
    (ha : AnalyticAt ℂ a ((chartAt ℂ x) x))
    (hlocal : f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y))
    (hd : deriv a ((chartAt ℂ x) x) ≠ 0) :
    LocallyInjectiveAt f x := by
  let c := chartAt ℂ x
  have hx : x ∈ c.source := mem_chart_source ℂ x
  obtain ⟨W, hW, hinjW⟩ :=
    analyticAt_deriv_ne_zero_locally_injective a (c x) ha hd
  let U : Set E := {y | c y ∈ W ∧ y ∈ c.source ∧ f y = a (c y)}
  have hU : U ∈ 𝓝 x := by
    filter_upwards [(c.continuousAt hx).tendsto.eventually hW,
      c.open_source.mem_nhds hx, hlocal] with y hyW hySource hyEq
    exact ⟨hyW, hySource, hyEq⟩
  refine ⟨U, hU, ?_⟩
  intro y hy z hz hfyz
  have hcyz : c y = c z := hinjW hy.1 hz.1 (by
    calc
      a (c y) = f y := hy.2.2.symm
      _ = f z := hfyz
      _ = a (c z) := hz.2.2)
  exact c.injOn hy.2.1 hz.2.1 hcyz

private theorem open_chart_deriv_ne_zero_locally_injective
    {E : Type*} [TopologicalSpace E]
    (c : OpenPartialHomeomorph E ℂ)
    (f : E → ℂ) (x : E) (hx : x ∈ c.source) (a : ℂ → ℂ)
    (ha : AnalyticAt ℂ a (c x))
    (hlocal : f =ᶠ[𝓝 x] fun y => a (c y))
    (hd : deriv a (c x) ≠ 0) :
    LocallyInjectiveAt f x := by
  obtain ⟨W, hW, hinjW⟩ :=
    analyticAt_deriv_ne_zero_locally_injective a (c x) ha hd
  let U : Set E := {y | c y ∈ W ∧ y ∈ c.source ∧ f y = a (c y)}
  have hU : U ∈ 𝓝 x := by
    filter_upwards [(c.continuousAt hx).tendsto.eventually hW,
      c.open_source.mem_nhds hx, hlocal] with y hyW hySource hyEq
    exact ⟨hyW, hySource, hyEq⟩
  refine ⟨U, hU, ?_⟩
  intro y hy z hz hfyz
  have hcyz : c y = c z := hinjW hy.1 hz.1 (by
    calc
      a (c y) = f y := hy.2.2.symm
      _ = f z := hfyz
      _ = a (c z) := hz.2.2)
  exact c.injOn hy.2.1 hz.2.1 hcyz

private theorem onePointPoleExtension_locallyInjective_of_chart_deriv_ne_zero
    {E : Type*} [TopologicalSpace E] [T1Space E] [ChartedSpace ℂ E]
    (p x : E) (f : E → ℂ) (a : ℂ → ℂ) (hxp : x ≠ p)
    (ha : AnalyticAt ℂ a ((chartAt ℂ x) x))
    (hlocal : f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y))
    (hd : deriv a ((chartAt ℂ x) x) ≠ 0) :
    LocallyInjectiveAt (onePointPoleExtension p f) x := by
  obtain ⟨U, hU, hinjU⟩ :=
    surface_chart_deriv_ne_zero_locally_injective f x a ha hlocal hd
  refine ⟨U ∩ {p}ᶜ, Filter.inter_mem hU (isOpen_compl_singleton.mem_nhds hxp), ?_⟩
  intro y hy z hz hEq
  have hyne : y ≠ p := by simpa using hy.2
  have hzne : z ≠ p := by simpa using hz.2
  have hEqF : f y = f z := OnePoint.coe_injective (by
    simpa [onePointPoleExtension, hyne, hzne] using hEq)
  exact hinjU hy.1 hz.1 hEqF

private theorem onePointPoleExtension_regular_branch_isolated
    {E : Type*} [TopologicalSpace E] [T1Space E] [ChartedSpace ℂ E]
    (p x : E) (f : E → ℂ) (a : ℂ → ℂ) (hxp : x ≠ p)
    (ha : AnalyticAt ℂ a ((chartAt ℂ x) x))
    (hlocal : f =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y))
    (hnonconstant : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      a z = a ((chartAt ℂ x) x)) :
    ∀ᶠ y in 𝓝[≠] x,
      LocallyInjectiveAt (onePointPoleExtension p f) y := by
  let c := chartAt ℂ x
  have hx : x ∈ c.source := mem_chart_source ℂ x
  have hc : Tendsto c (𝓝[≠] x) (𝓝[≠] (c x)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(c.continuousAt hx).tendsto.mono_left nhdsWithin_le_nhds,
        c.eventually_ne_nhdsWithin hx⟩
  have hderiv := hc.eventually
    (analyticAt_nonconstant_deriv_isolated_zero a (c x) ha hnonconstant)
  have hanalytic : ∀ᶠ y in 𝓝[≠] x, AnalyticAt ℂ a (c y) :=
    ((c.continuousAt hx).tendsto.eventually
      ha.eventually_analyticAt).filter_mono nhdsWithin_le_nhds
  have hnearLocal : ∀ᶠ y in 𝓝[≠] x,
      f =ᶠ[𝓝 y] fun z => a (c z) :=
    (show ∀ᶠ y in 𝓝 x, f =ᶠ[𝓝 y] fun z => a (c z) from
      isOpen_setOfPred_eventually_nhds.mem_nhds hlocal).filter_mono
        nhdsWithin_le_nhds
  have hnearSource : ∀ᶠ y in 𝓝[≠] x, y ∈ c.source :=
    (show ∀ᶠ y in 𝓝 x, y ∈ c.source from
      c.open_source.mem_nhds hx).filter_mono nhdsWithin_le_nhds
  have hnearAway : ∀ᶠ y in 𝓝[≠] x, y ∈ ({p}ᶜ : Set E) :=
    (show ∀ᶠ y in 𝓝 x, y ∈ ({p}ᶜ : Set E) from
      isOpen_compl_singleton.mem_nhds hxp).filter_mono nhdsWithin_le_nhds
  filter_upwards [hderiv, hanalytic, hnearLocal, hnearSource, hnearAway]
    with y hdy hay hly hys hyp
  have hynp : y ≠ p := by simpa using hyp
  obtain ⟨U, hU, hinjU⟩ :=
    open_chart_deriv_ne_zero_locally_injective c f y hys a hay hly hdy
  refine ⟨U ∩ {p}ᶜ, Filter.inter_mem hU (isOpen_compl_singleton.mem_nhds hynp), ?_⟩
  intro u hu v hv huv
  have hunp : u ≠ p := by simpa using hu.2
  have hvnp : v ≠ p := by simpa using hv.2
  have huvF : f u = f v := OnePoint.coe_injective (by
    simpa [onePointPoleExtension, hunp, hvnp] using huv)
  exact hinjU hu.1 hv.1 huvF

private theorem SurfaceMeromorphicFunction.simple_pole_branch_set_finite
    (E : Type) [TopologicalSpace E] [T2Space E]
    [CompactSpace E] [ConnectedSpace E] [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (p : E)
    (hpole : F.divisorOrder p = (-1 : ℤ))
    (hreg : ∀ x : E, x ≠ p → ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      (F.toFun =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
      F.toFun x = a ((chartAt ℂ x) x)) :
    Set.Finite {x : E |
      ¬ LocallyInjectiveAt (onePointPoleExtension p F.toFun) x} := by
  let G := onePointPoleExtension p F.toFun
  let C : Set E := {x | ¬ LocallyInjectiveAt G x}
  have hclosed : IsClosed C := isOpen_locallyInjectiveAt G |>.isClosed_compl
  have hcompact : IsCompact C := hclosed.isCompact
  have hregStrong := F.simple_pole_regular_charts_nonconstant E p hpole hreg
  obtain ⟨a, ha, hlocal⟩ := F.meromorphicAt p
  have horder : meromorphicOrderAt a ((chartAt ℂ p) p) = (-1 : ℤ) := by
    rwa [F.divisorOrder_eq_chart_order p a hlocal] at hpole
  have hpLocal : LocallyInjectiveAt G p :=
    (onePointPoleExtension_locally_open_at_order_neg_one p F.toFun a ha
      horder hlocal).2
  have hdiscrete : IsDiscrete C := by
    apply isDiscrete_iff_nhdsNE.mpr
    intro x hx
    have hxp : x ≠ p := by
      intro he
      subst x
      exact hx hpLocal
    obtain ⟨aₓ, haₓ, hlocalₓ, _, hnonconstantₓ⟩ := hregStrong x hxp
    have hiso : ∀ᶠ y in 𝓝[≠] x, y ∈ Cᶜ :=
      (onePointPoleExtension_regular_branch_isolated p x F.toFun aₓ hxp
        haₓ hlocalₓ hnonconstantₓ).mono (by intro y hy; simpa [C, G] using hy)
    have hd : Disjoint (𝓝[≠] x) (𝓟 C) :=
      Filter.disjoint_iff.mpr
        ⟨Cᶜ, hiso, C, mem_principal_self C,
          Set.disjoint_left.mpr (by intro y hyn hys; exact hyn hys)⟩
    exact disjoint_iff.mp hd
  exact hcompact.finite hdiscrete

private theorem SurfaceMeromorphicFunction.simple_pole_branch_values_finite
    (E : Type) [TopologicalSpace E] [T2Space E]
    [CompactSpace E] [ConnectedSpace E] [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (p : E)
    (hpole : F.divisorOrder p = (-1 : ℤ))
    (hreg : ∀ x : E, x ≠ p → ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      (F.toFun =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
      F.toFun x = a ((chartAt ℂ x) x)) :
    Set.Finite ((onePointPoleExtension p F.toFun) ''
      {x : E | ¬ LocallyInjectiveAt (onePointPoleExtension p F.toFun) x}) ∧
    (OnePoint.infty : OnePoint ℂ) ∉ (onePointPoleExtension p F.toFun) ''
      {x : E | ¬ LocallyInjectiveAt (onePointPoleExtension p F.toFun) x} := by
  constructor
  · exact (F.simple_pole_branch_set_finite E p hpole hreg).image _
  · rintro ⟨x, hx, hxi⟩
    have hxp : x = p := by
      by_contra hne
      simp [onePointPoleExtension, hne] at hxi
    subst x
    obtain ⟨a, ha, hlocal⟩ := F.meromorphicAt p
    have horder : meromorphicOrderAt a ((chartAt ℂ p) p) = (-1 : ℤ) := by
      rwa [F.divisorOrder_eq_chart_order p a hlocal] at hpole
    exact hx (onePointPoleExtension_locally_open_at_order_neg_one
      p F.toFun a ha horder hlocal).2

private theorem onePoint_complex_compl_finite_connected
    (V : Set (OnePoint ℂ)) (hV : V.Finite)
    (hInf : (OnePoint.infty : OnePoint ℂ) ∉ V) :
    IsConnected Vᶜ := by
  let S : Set ℂ := ((↑) : ℂ → OnePoint ℂ) ⁻¹' V
  have hSfinite : S.Finite := hV.preimage OnePoint.coe_injective.injOn
  have hSconn : IsConnected Sᶜ :=
    hSfinite.countable.isConnected_compl_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)
  let T : Set (OnePoint ℂ) := ((↑) : ℂ → OnePoint ℂ) '' Sᶜ
  have hTconn : IsConnected T :=
    hSconn.image _ OnePoint.continuous_coe.continuousOn
  have hTdense : Dense T :=
    OnePoint.denseRange_coe.dense_image OnePoint.continuous_coe
      (hSfinite.countable.dense_compl ℂ)
  apply hTconn.subset_closure
  · rintro w ⟨z, hz, rfl⟩
    exact hz
  · intro w _
    rw [hTdense.closure_eq]
    trivial

private theorem continuous_open_isLocalHomeomorphOn_locallyInjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (ho : IsOpenMap f) :
    IsLocalHomeomorphOn f {x | LocallyInjectiveAt f x} := by
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mpr
  intro x hx
  obtain ⟨U, hU, hinj⟩ := hx
  refine ⟨interior U,
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hU), ?_⟩
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact hf.comp continuous_subtype_val
  · exact Set.injOn_iff_injective.mp (hinj.mono interior_subset)
  · exact ho.domRestrict isOpen_interior

private theorem SurfaceMeromorphicFunction.simple_pole_regular_value_covering
    (E : Type) [TopologicalSpace E] [T2Space E]
    [CompactSpace E] [ConnectedSpace E] [ChartedSpace ℂ E]
    (F : SurfaceMeromorphicFunction E) (p : E)
    (hpole : F.divisorOrder p = (-1 : ℤ))
    (hreg : ∀ x : E, x ≠ p → ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
      (F.toFun =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
      F.toFun x = a ((chartAt ℂ x) x)) :
    let G := onePointPoleExtension p F.toFun
    let V := G '' {x : E | ¬ LocallyInjectiveAt G x}
    V.Finite ∧ (OnePoint.infty : OnePoint ℂ) ∉ V ∧
      IsConnected Vᶜ ∧ IsCoveringMapOn G Vᶜ := by
  dsimp
  let G := onePointPoleExtension p F.toFun
  let V := G '' {x : E | ¬ LocallyInjectiveAt G x}
  obtain ⟨hVfinite, hInf⟩ := F.simple_pole_branch_values_finite E p hpole hreg
  have hVconnected := onePoint_complex_compl_finite_connected V hVfinite hInf
  obtain ⟨a, ha, hlocal⟩ := F.meromorphicAt p
  have horder : meromorphicOrderAt a ((chartAt ℂ p) p) = (-1 : ℤ) := by
    rwa [F.divisorOrder_eq_chart_order p a hlocal] at hpole
  have hnegative : meromorphicOrderAt a ((chartAt ℂ p) p) < 0 := by
    rw [horder]
    exact_mod_cast (show (-1 : ℤ) < 0 by omega)
  have hf : ContinuousOn F.toFun ({p}ᶜ : Set E) := by
    intro x hx
    obtain ⟨aₓ, haₓ, hlocalₓ, _⟩ := hreg x (by simpa using hx)
    have hchart : ContinuousAt (chartAt ℂ x) x :=
      (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
    exact ((haₓ.continuousAt.comp hchart).congr_of_eventuallyEq hlocalₓ).continuousWithinAt
  have hGcont : Continuous G :=
    onePointPoleExtension_continuous_of_chart_pole p F.toFun a
      hf hlocal hnegative
  have hregStrong := F.simple_pole_regular_charts_nonconstant E p hpole hreg
  have hGopen : IsOpenMap G := by
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    by_cases hxp : x = p
    · subst x
      have hpoleOpen :=
        (onePointPoleExtension_locally_open_at_order_neg_one p F.toFun a ha horder hlocal).1
      simpa [G, onePointPoleExtension] using le_of_eq hpoleOpen.symm
    · obtain ⟨aₓ, haₓ, hlocalₓ, hpointₓ, hnonconstantₓ⟩ := hregStrong x hxp
      exact onePointPoleExtension_locally_open_away_p p x F.toFun aₓ
        hxp haₓ hlocalₓ hpointₓ hnonconstantₓ
  have hlocalHomeo : IsLocalHomeomorphOn G (G ⁻¹' Vᶜ) :=
    (continuous_open_isLocalHomeomorphOn_locallyInjective G hGcont hGopen).mono
      (by
        intro x hx
        by_contra hnot
        exact hx ⟨x, hnot, rfl⟩)
  refine ⟨hVfinite, hInf, hVconnected, ?_⟩
  exact IsCoveringMapOn.of_isLocalHomeomorphOn hGcont hlocalHomeo

private theorem evenlyCovered_subsingleton_fiber_locally_constant
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (f : E → X) (x : X) (I : Type*) [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) :
    ∃ U : Set X, x ∈ U ∧ IsOpen U ∧
      ∀ y ∈ U, Subsingleton (f ⁻¹' {y}) ↔ Subsingleton (f ⁻¹' {x}) := by
  rcases h with ⟨hdisc, U, hxU, hU, hpre, H, hH⟩
  refine ⟨U, hxU, hU, ?_⟩
  intro y hyU
  have hx : IsEvenlyCovered f x I := ⟨hdisc, U, hxU, hU, hpre, H, hH⟩
  have hy : IsEvenlyCovered f y I := ⟨hdisc, U, hyU, hU, hpre, H, hH⟩
  constructor
  · intro hsub
    letI : Subsingleton (f ⁻¹' {y}) := hsub
    have hI : Subsingleton I :=
      ⟨fun a b => hy.fiberHomeomorph.injective (Subsingleton.elim _ _)⟩
    letI : Subsingleton I := hI
    exact ⟨fun a b => hx.fiberHomeomorph.symm.injective (Subsingleton.elim _ _)⟩
  · intro hsub
    letI : Subsingleton (f ⁻¹' {x}) := hsub
    have hI : Subsingleton I :=
      ⟨fun a b => hx.fiberHomeomorph.injective (Subsingleton.elim _ _)⟩
    letI : Subsingleton I := hI
    exact ⟨fun a b => hy.fiberHomeomorph.symm.injective (Subsingleton.elim _ _)⟩

private theorem covering_subsingleton_fibers_of_connected_base
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (f : E → X) (s : Set X) (hsopen : IsOpen s) (hsconn : IsConnected s)
    (hcover : IsCoveringMapOn f s)
    (x : X) (hx : x ∈ s) (hxsub : Subsingleton (f ⁻¹' {x})) :
    ∀ y ∈ s, Subsingleton (f ⁻¹' {y}) := by
  let A : Set X := {y | y ∈ s ∧ Subsingleton (f ⁻¹' {y})}
  let B : Set X := {y | y ∈ s ∧ ¬ Subsingleton (f ⁻¹' {y})}
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨U, hyU, hUopen, hconst⟩ :=
      evenlyCovered_subsingleton_fiber_locally_constant f y _ (hcover y hy.1)
    have hsub : U ∩ s ⊆ A := by
      intro z hz
      exact ⟨hz.2, (hconst z hz.1).2 hy.2⟩
    exact Filter.mem_of_superset ((hUopen.inter hsopen).mem_nhds ⟨hyU, hy.1⟩) hsub
  have hBopen : IsOpen B := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨U, hyU, hUopen, hconst⟩ :=
      evenlyCovered_subsingleton_fiber_locally_constant f y _ (hcover y hy.1)
    have hsub : U ∩ s ⊆ B := by
      intro z hz
      exact ⟨hz.2, fun h => hy.2 ((hconst z hz.1).1 h)⟩
    exact Filter.mem_of_superset ((hUopen.inter hsopen).mem_nhds ⟨hyU, hy.1⟩) hsub
  have hdisj : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro y hyA hyB
    exact hyB.2 hyA.2
  have hcoverAB : s ⊆ A ∪ B := by
    intro y hy
    by_cases h : Subsingleton (f ⁻¹' {y})
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr ⟨hy, h⟩
  have hnonempty : (s ∩ A).Nonempty := ⟨x, hx, hx, hxsub⟩
  have hsA := hsconn.isPreconnected.subset_left_of_subset_union
    hAopen hBopen hdisj hcoverAB hnonempty
  intro y hy
  exact (hsA hy).2

private theorem onePoint_complex_compl_finite_dense
    (V : Set (OnePoint ℂ)) (hV : V.Finite)
    (hInf : (OnePoint.infty : OnePoint ℂ) ∉ V) :
    Dense Vᶜ := by
  let S : Set ℂ := ((↑) : ℂ → OnePoint ℂ) ⁻¹' V
  have hSfinite : S.Finite := hV.preimage OnePoint.coe_injective.injOn
  have hTdense : Dense (((↑) : ℂ → OnePoint ℂ) '' Sᶜ) :=
    OnePoint.denseRange_coe.dense_image OnePoint.continuous_coe
      (hSfinite.countable.dense_compl ℂ)
  apply hTdense.mono
  rintro w ⟨z, hz, rfl⟩
  exact hz

private theorem continuous_open_injective_of_subsingleton_fibers_on_dense
    {E X : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace X]
    (f : E → X) (ho : IsOpenMap f) (s : Set X) (hs : Dense s)
    (hsub : ∀ y ∈ s, Subsingleton (f ⁻¹' {y})) :
    Function.Injective f := by
  intro x y hxy
  by_contra hne
  obtain ⟨U, W, hU, hW, hxU, hyW, hUW⟩ := t2_separation hne
  have hIopen : IsOpen (f '' U ∩ f '' W) := (ho U hU).inter (ho W hW)
  have hInonempty : (f '' U ∩ f '' W).Nonempty := by
    refine ⟨f x, ⟨x, hxU, rfl⟩, ?_⟩
    exact ⟨y, hyW, hxy.symm⟩
  obtain ⟨z, hz, hzs⟩ := hs.inter_open_nonempty _ hIopen hInonempty
  obtain ⟨a, haU, haz⟩ := hz.1
  obtain ⟨b, hbW, hbz⟩ := hz.2
  have hab : a = b := by
    have hzsub := hsub z hzs
    exact congrArg Subtype.val
      (hzsub.elim (⟨a, by simpa [haz]⟩ : f ⁻¹' {z})
        (⟨b, by simpa [hbz]⟩ : f ⁻¹' {z}))
  exact (Set.disjoint_left.mp hUW) haU (hab ▸ hbW)

theorem SurfaceMeromorphicFunction.genus_two_no_simple_pole
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (F : SurfaceMeromorphicFunction E) (p : E)
    (hpole : letI : ChartedSpace ℂ E := A;
      F.divisorOrder p = (-1 : ℤ))
    (hreg : letI : ChartedSpace ℂ E := A;
      ∀ x : E, x ≠ p → ∃ a : ℂ → ℂ,
        AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
        (F.toFun =ᶠ[𝓝 x] fun y => a ((chartAt ℂ x) y)) ∧
        F.toFun x = a ((chartAt ℂ x) x)) : False := by
  classical
  letI : CurveComplex.ClosedSurface E := Classical.choice hg.2.1
  letI : ChartedSpace ℂ E := A
  let G := onePointPoleExtension p F.toFun
  let V := G '' {x : E | ¬ LocallyInjectiveAt G x}
  obtain ⟨hVfinite, hInf, hVconn, hcover⟩ :=
    F.simple_pole_regular_value_covering E p hpole hreg
  have hVopen : IsOpen Vᶜ := hVfinite.isClosed.isOpen_compl
  have hInfFiber : Subsingleton (G ⁻¹' {(OnePoint.infty : OnePoint ℂ)}) := by
    have heq : G ⁻¹' {(OnePoint.infty : OnePoint ℂ)} = {p} := by
      ext x
      by_cases hxp : x = p
      · subst x
        simp [G, onePointPoleExtension]
      · simp [G, onePointPoleExtension, hxp]
    rw [heq]
    infer_instance
  have hsub := covering_subsingleton_fibers_of_connected_base G Vᶜ hVopen
    hVconn hcover OnePoint.infty hInf hInfFiber
  obtain ⟨a, ha, hlocal⟩ := F.meromorphicAt p
  have horder : meromorphicOrderAt a ((chartAt ℂ p) p) = (-1 : ℤ) := by
    rwa [F.divisorOrder_eq_chart_order p a hlocal] at hpole
  have hregStrong := F.simple_pole_regular_charts_nonconstant E p hpole hreg
  have hGopen : IsOpenMap G := by
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    by_cases hxp : x = p
    · subst x
      have hpoleOpen :=
        (onePointPoleExtension_locally_open_at_order_neg_one p F.toFun a ha horder hlocal).1
      simpa [G, onePointPoleExtension] using le_of_eq hpoleOpen.symm
    · obtain ⟨aₓ, haₓ, hlocalₓ, hpointₓ, hnonconstantₓ⟩ := hregStrong x hxp
      exact onePointPoleExtension_locally_open_away_p p x F.toFun aₓ
        hxp haₓ hlocalₓ hpointₓ hnonconstantₓ
  have hinj : Function.Injective G :=
    continuous_open_injective_of_subsingleton_fibers_on_dense G
      hGopen Vᶜ (onePoint_complex_compl_finite_dense V hVfinite hInf) hsub
  have hf : ContinuousOn F.toFun ({p}ᶜ : Set E) := by
    intro x hx
    obtain ⟨aₓ, haₓ, hlocalₓ, _⟩ := hreg x (by simpa using hx)
    have hchart : ContinuousAt (chartAt ℂ x) x :=
      (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
    exact ((haₓ.continuousAt.comp hchart).congr_of_eventuallyEq hlocalₓ).continuousWithinAt
  have hnoninj := genus_two_simple_pole_global_analytic_map_noninjective
    E hg A p F.toFun a hf ha horder hlocal hregStrong
  exact hnoninj ((onePointPoleExtension_injective_iff p F.toFun).1 hinj)

#print axioms SurfaceMeromorphicFunction.genus_two_no_simple_pole
