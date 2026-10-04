import CurveComplexGenusTwo.Topology.ActualNoSimplePole.NoGenusTwoSimplePole

open scoped Manifold ContDiff Bundle
open Bundle
open CategoryTheory CategoryTheory.Limits
open Filter Topology
open Set AlgebraicTopology CurveComplex CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace SameAtlasRRReview

/-- Literal meromorphic functions with at most a simple pole at p:
functions are defined off p, eliminating irrelevant assigned values at a pole. -/
noncomputable def actualH0Point
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (p : E) :
    Submodule ℂ ({x : E // x ≠ p} → ℂ) where
  carrier := {f |
    (∀ x : E, ∀ hx : x ≠ p, ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ p ∉ W ∧
      ∃ a : ℂ → ℂ, AnalyticAt ℂ a ((chartAt ℂ x) x) ∧
        ∀ᶠ y in 𝓝 x, ∀ hy : y ≠ p, f ⟨y,hy⟩ = a ((chartAt ℂ x) y)) ∧
    ∃ a : ℂ → ℂ, AnalyticAt ℂ a ((chartAt ℂ p) p) ∧
      ∀ᶠ y in 𝓝[≠] p, ∀ hy : y ≠ p,
        (((chartAt ℂ p) y) - ((chartAt ℂ p) p)) * f ⟨y,hy⟩ =
          a ((chartAt ℂ p) y)}
  zero_mem' := by
    letI : T1Space E := ChartedSpace.t1Space ℂ E
    constructor
    · intro x hx
      refine ⟨{p}ᶜ, isOpen_compl_singleton, by simpa using hx, by simp,
        0, analyticAt_const, ?_⟩
      filter_upwards with y
      intro hy
      simp
    · refine ⟨0, analyticAt_const, ?_⟩
      filter_upwards with y
      intro hy
      simp
  add_mem' := by
    intro f g hf hg
    constructor
    · intro x hx
      obtain ⟨Wf, hWf, hxWf, hpWf, af, haf, hef⟩ := hf.1 x hx
      obtain ⟨Wg, hWg, hxWg, hpWg, ag, hag, heg⟩ := hg.1 x hx
      refine ⟨Wf ∩ Wg, hWf.inter hWg, ⟨hxWf, hxWg⟩, ?_, af + ag,
        haf.add hag, ?_⟩
      · exact fun h => hpWf h.1
      · filter_upwards [hef, heg] with y hfy hgy hy
        simp [hfy hy, hgy hy]
    · obtain ⟨af, haf, hef⟩ := hf.2
      obtain ⟨ag, hag, heg⟩ := hg.2
      refine ⟨af + ag, haf.add hag, ?_⟩
      filter_upwards [hef, heg] with y hfy hgy hy
      simp [mul_add, hfy hy, hgy hy]
  smul_mem' := by
    intro c f hf
    constructor
    · intro x hx
      obtain ⟨W, hW, hxW, hpW, a, ha, he⟩ := hf.1 x hx
      refine ⟨W, hW, hxW, hpW, c • a, ha.const_smul, ?_⟩
      filter_upwards [he] with y hfy hy
      simp [hfy hy, smul_eq_mul]
    · obtain ⟨a, ha, he⟩ := hf.2
      refine ⟨c • a, ha.const_smul, ?_⟩
      filter_upwards [he] with y hfy hy
      simp [hfy hy, smul_eq_mul, mul_left_comm]

private theorem punctured_chart_germ_unique
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

private theorem pole_witness_value_unique
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (f : {x : E // x ≠ p} → ℂ) (a b : ℂ → ℂ)
    (ha : AnalyticAt ℂ a ((chartAt ℂ p) p))
    (hb : AnalyticAt ℂ b ((chartAt ℂ p) p))
    (hfa : ∀ᶠ y in 𝓝[≠] p, ∀ hy : y ≠ p,
      ((chartAt ℂ p) y - (chartAt ℂ p) p) * f ⟨y, hy⟩ =
        a ((chartAt ℂ p) y))
    (hfb : ∀ᶠ y in 𝓝[≠] p, ∀ hy : y ≠ p,
      ((chartAt ℂ p) y - (chartAt ℂ p) p) * f ⟨y, hy⟩ =
        b ((chartAt ℂ p) y)) :
    a ((chartAt ℂ p) p) = b ((chartAt ℂ p) p) := by
  classical
  let F : E → ℂ := fun y =>
    if hy : y = p then 0 else
      ((chartAt ℂ p) y - (chartAt ℂ p) p) * f ⟨y, hy⟩
  have hFa : F =ᶠ[𝓝[≠] p] fun y => a ((chartAt ℂ p) y) := by
    filter_upwards [hfa, self_mem_nhdsWithin] with y hfy hy
    have hyn : y ≠ p := by simpa using hy
    simpa [F, hyn] using hfy hyn
  have hFb : F =ᶠ[𝓝[≠] p] fun y => b ((chartAt ℂ p) y) := by
    filter_upwards [hfb, self_mem_nhdsWithin] with y hfy hy
    have hyn : y ≠ p := by simpa using hy
    simpa [F, hyn] using hfy hyn
  have hEq := punctured_chart_germ_unique p F a b hFa hFb
  exact tendsto_nhds_unique_of_eventuallyEq
    (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hb.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hEq

private noncomputable def poleNumerator
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (p : E) (f : actualH0Point p) : ℂ → ℂ :=
  Classical.choose f.property.2

private theorem poleNumerator_spec
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (p : E) (f : actualH0Point p) :
    AnalyticAt ℂ (poleNumerator p f) ((chartAt ℂ p) p) ∧
      ∀ᶠ y in 𝓝[≠] p, ∀ hy : y ≠ p,
        ((chartAt ℂ p) y - (chartAt ℂ p) p) * f.1 ⟨y, hy⟩ =
          poleNumerator p f ((chartAt ℂ p) y) :=
  Classical.choose_spec f.property.2

private noncomputable def poleCoefficient
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (p : E) : actualH0Point p →ₗ[ℂ] ℂ where
  toFun f := poleNumerator p f ((chartAt ℂ p) p)
  map_add' := by
    intro f g
    obtain ⟨hfgAn, hfg⟩ := poleNumerator_spec p (f + g)
    obtain ⟨hfAn, hf⟩ := poleNumerator_spec p f
    obtain ⟨hgAn, hg⟩ := poleNumerator_spec p g
    apply pole_witness_value_unique p (f + g : actualH0Point p).1
      (poleNumerator p (f + g)) (poleNumerator p f + poleNumerator p g)
      hfgAn (hfAn.add hgAn) hfg
    filter_upwards [hf, hg] with y hfy hgy hy
    change ((chartAt ℂ p) y - (chartAt ℂ p) p) *
      (f.1 ⟨y, hy⟩ + g.1 ⟨y, hy⟩) = _
    rw [mul_add, hfy hy, hgy hy]
    rfl
  map_smul' := by
    intro c f
    obtain ⟨hcfAn, hcf⟩ := poleNumerator_spec p (c • f)
    obtain ⟨hfAn, hf⟩ := poleNumerator_spec p f
    apply pole_witness_value_unique p (c • f : actualH0Point p).1
      (poleNumerator p (c • f)) (c • poleNumerator p f)
      hcfAn hfAn.const_smul hcf
    filter_upwards [hf] with y hfy hy
    change ((chartAt ℂ p) y - (chartAt ℂ p) p) *
      (c * f.1 ⟨y, hy⟩) = _
    rw [mul_left_comm, hfy hy]
    rfl

end SameAtlasRRReview

namespace SameAtlasRRLocal

open SameAtlasRRReview
open TopologicalSpace
set_option synthInstance.maxHeartbeats 1000000

variable {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]

/-- A scalar function on an open set, analytic in the fixed ambient charts. -/
def IsHolOn (U : Opens E) (f : U → ℂ) : Prop :=
  ∀ x : U, ∃ a : ℂ → ℂ, AnalyticAt ℂ a ((chartAt ℂ (x : E)) x) ∧
    ∀ᶠ y in 𝓝 (x : E), ∀ hy : y ∈ U,
      f ⟨y, hy⟩ = a ((chartAt ℂ (x : E)) y)

/-- Local holomorphic scalar sections for the same atlas. -/
def HolOn (U : Opens E) : Submodule ℂ (U → ℂ) where
  carrier := {f | IsHolOn U f}
  zero_mem' := by
    intro x
    refine ⟨0, analyticAt_const, ?_⟩
    filter_upwards with y
    intro hy
    rfl
  add_mem' := by
    intro f g hf hg x
    obtain ⟨af, haf, hgf⟩ := hf x
    obtain ⟨ag, hag, hgg⟩ := hg x
    refine ⟨af + ag, haf.add hag, ?_⟩
    filter_upwards [hgf, hgg] with y hfy hgy hy
    simp [hfy hy, hgy hy]
  smul_mem' := by
    intro c f hf x
    obtain ⟨a, ha, hfa⟩ := hf x
    refine ⟨c • a, ha.const_smul, ?_⟩
    filter_upwards [hfa] with y hfy hy
    simp [hfy hy, smul_eq_mul]

/-- Local functions away from `p`, with at most a simple pole when `p ∈ U`. -/
def IsPoleOneOn (p : E) (U : Opens E)
    (f : {x : U // (x : E) ≠ p} → ℂ) : Prop :=
  (∀ x : U, ∀ hx : (x : E) ≠ p,
    ∃ a : ℂ → ℂ, AnalyticAt ℂ a ((chartAt ℂ (x : E)) x) ∧
      ∀ᶠ y in 𝓝 (x : E), ∀ hyU : y ∈ U, ∀ hyp : y ≠ p,
        f ⟨⟨y, hyU⟩, hyp⟩ = a ((chartAt ℂ (x : E)) y)) ∧
  (p ∈ U → ∃ a : ℂ → ℂ, AnalyticAt ℂ a ((chartAt ℂ p) p) ∧
    ∀ᶠ y in 𝓝[≠] p, ∀ hyU : y ∈ U, ∀ hyp : y ≠ p,
      ((chartAt ℂ p) y - (chartAt ℂ p) p) * f ⟨⟨y, hyU⟩, hyp⟩ =
        a ((chartAt ℂ p) y))

/-- The puncture is removed from the domain; no value is assigned at `p`. -/
def PoleOneOn (p : E) (U : Opens E) :
    Submodule ℂ ({x : U // (x : E) ≠ p} → ℂ) where
  carrier := {f | IsPoleOneOn p U f}
  zero_mem' := by
    constructor
    · intro x hx
      refine ⟨0, analyticAt_const, ?_⟩
      filter_upwards with y
      intro hyU hyp
      rfl
    · intro hp
      refine ⟨0, analyticAt_const, ?_⟩
      filter_upwards with y
      intro hyU hyp
      simp
  add_mem' := by
    intro f g hf hg
    constructor
    · intro x hx
      obtain ⟨af, haf, hgf⟩ := hf.1 x hx
      obtain ⟨ag, hag, hgg⟩ := hg.1 x hx
      refine ⟨af + ag, haf.add hag, ?_⟩
      filter_upwards [hgf, hgg] with y hfy hgy hyU hyp
      simp [hfy hyU hyp, hgy hyU hyp]
    · intro hp
      obtain ⟨af, haf, hgf⟩ := hf.2 hp
      obtain ⟨ag, hag, hgg⟩ := hg.2 hp
      refine ⟨af + ag, haf.add hag, ?_⟩
      filter_upwards [hgf, hgg] with y hfy hgy hyU hyp
      simp [mul_add, hfy hyU hyp, hgy hyU hyp]
  smul_mem' := by
    intro c f hf
    constructor
    · intro x hx
      obtain ⟨a, ha, hfa⟩ := hf.1 x hx
      refine ⟨c • a, ha.const_smul, ?_⟩
      filter_upwards [hfa] with y hfy hyU hyp
      simp [hfy hyU hyp, smul_eq_mul]
    · intro hp
      obtain ⟨a, ha, hfa⟩ := hf.2 hp
      refine ⟨c • a, ha.const_smul, ?_⟩
      filter_upwards [hfa] with y hfy hyU hyp
      simp [hfy hyU hyp, smul_eq_mul, mul_left_comm]

/-- Holomorphic cotangent sections on the induced complex atlas of the open set. -/
noncomputable abbrev CanonicalOn (U : Opens E) :=
  ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ∞
    (fun x : U => TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial U ℂ x)

/-- Restriction of a local holomorphic scalar section. -/
noncomputable def HolOn.restrict {U V : Opens E} (hVU : V ≤ U) :
    HolOn U →ₗ[ℂ] HolOn V where
  toFun f := ⟨fun x => f.1 ⟨x, hVU x.property⟩, by
    intro x
    obtain ⟨a, ha, hfa⟩ := f.property ⟨x, hVU x.property⟩
    refine ⟨a, ha, ?_⟩
    filter_upwards [hfa] with y hfy hy
    exact hfy (hVU hy)⟩
  map_add' := by
    intro f g
    ext x
    rfl
  map_smul' := by
    intro c f
    ext x
    rfl

/-- Restriction of a local one-pole section, retaining the exact punctured domain. -/
noncomputable def PoleOneOn.restrict (p : E) {U V : Opens E} (hVU : V ≤ U) :
    PoleOneOn p U →ₗ[ℂ] PoleOneOn p V where
  toFun f := ⟨fun x => f.1 ⟨⟨x.1, hVU x.1.property⟩, x.2⟩, by
    constructor
    · intro x hx
      obtain ⟨a, ha, hfa⟩ := f.property.1 ⟨x, hVU x.property⟩ hx
      refine ⟨a, ha, ?_⟩
      filter_upwards [hfa] with y hfy hyU hyp
      exact hfy (hVU hyU) hyp
    · intro hp
      obtain ⟨a, ha, hfa⟩ := f.property.2 (hVU hp)
      refine ⟨a, ha, ?_⟩
      filter_upwards [hfa] with y hfy hyU hyp
      exact hfy (hVU hyU) hyp⟩
  map_add' := by
    intro f g
    ext x
    rfl
  map_smul' := by
    intro c f
    ext x
    rfl

/-- Restriction of a cotangent section to an open submanifold. -/
private theorem tangentSymmL_inclusion {U V : Opens E} (hVU : V ≤ U)
    (x y : V) (hxy : y ∈ (chartAt ℂ x).source) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ) : V → Type _) x).symmL ℂ y =
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ) : U → Type _)
      (Opens.inclusion hVU x)).symmL ℂ (Opens.inclusion hVU y) := by
  have hxyU : Opens.inclusion hVU y ∈
      (chartAt ℂ (Opens.inclusion hVU x)).source := by
    simpa [Opens.chartAt_eq] using hxy
  rw [TangentBundle.symmL_trivializationAt_eq_core hxy,
    TangentBundle.symmL_trivializationAt_eq_core hxyU,
    tangentBundleCore_coordChange_achart,
    tangentBundleCore_coordChange_achart]
  simp only [extChartAt_coe, extChartAt_coe_symm, Function.comp_apply,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, id_eq, range_id]
  have hinv : Set.EqOn
      (chartAt ℂ (Opens.inclusion hVU x)).symm
      (Opens.inclusion hVU ∘ (chartAt ℂ x).symm)
      (chartAt ℂ x).target := by
    simpa only [Opens.chartAt_eq] using
      ((chartAt ℂ (x : E)).subtypeRestr_symm_eqOn_of_le
        (show Nonempty V from ⟨x⟩)
        (show Nonempty U from ⟨Opens.inclusion hVU x⟩) hVU)
  have hpoint : (chartAt ℂ x) y =
      (chartAt ℂ (Opens.inclusion hVU x)) (Opens.inclusion hVU y) := rfl
  have htrans : ((chartAt ℂ y : ↥V → ℂ) ∘ (chartAt ℂ x).symm) =ᶠ[
      𝓝 ((chartAt ℂ x) y)]
      ((chartAt ℂ (Opens.inclusion hVU y) : ↥U → ℂ) ∘
        (chartAt ℂ (Opens.inclusion hVU x)).symm) := by
    have ht : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) y) :=
      (chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hxy)
    filter_upwards [ht] with z hz
    have he := hinv hz
    change (chartAt ℂ y) ((chartAt ℂ x).symm z) =
      (chartAt ℂ (Opens.inclusion hVU y))
        ((chartAt ℂ (Opens.inclusion hVU x)).symm z)
    rw [he]
    rfl
  rw [← hpoint]
  exact (htrans.filter_mono nhdsWithin_le_nhds).fderivWithin_eq_of_mem
    (Set.mem_univ _)

private theorem tangentSymmL_subtype {U : Opens E} (x y : U)
    (hxy : y ∈ (chartAt ℂ x).source) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ) : U → Type _) x).symmL ℂ y =
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ) : E → Type _) x.1).symmL ℂ y.1 := by
  have hxyE : (y : E) ∈ (chartAt ℂ (x : E)).source := by
    simpa [Opens.chartAt_eq] using hxy
  rw [TangentBundle.symmL_trivializationAt_eq_core hxy,
    TangentBundle.symmL_trivializationAt_eq_core hxyE,
    tangentBundleCore_coordChange_achart,
    tangentBundleCore_coordChange_achart]
  simp only [extChartAt_coe, extChartAt_coe_symm, Function.comp_apply,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, id_eq, range_id]
  have hinv : Set.EqOn (chartAt ℂ (x : E)).symm
      (Subtype.val ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target := by
    simpa only [Opens.chartAt_eq] using
      ((chartAt ℂ (x : E)).subtypeRestr_symm_eqOn
        (show Nonempty U from ⟨x⟩))
  have hpoint : (chartAt ℂ x) y = (chartAt ℂ (x : E)) (y : E) := rfl
  have htrans : ((chartAt ℂ y : U → ℂ) ∘ (chartAt ℂ x).symm) =ᶠ[
      𝓝 ((chartAt ℂ x) y)]
      ((chartAt ℂ (y : E) : E → ℂ) ∘ (chartAt ℂ (x : E)).symm) := by
    have ht : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) y) :=
      (chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hxy)
    filter_upwards [ht] with z hz
    have he := hinv hz
    change (chartAt ℂ y) ((chartAt ℂ x).symm z) =
      (chartAt ℂ (y : E)) ((chartAt ℂ (x : E)).symm z)
    rw [he]
    rfl
  rw [← hpoint]
  exact (htrans.filter_mono nhdsWithin_le_nhds).fderivWithin_eq_of_mem
    (Set.mem_univ _)

theorem CanonicalOn.restrict_exists {U V : Opens E} (hVU : V ≤ U) :
    ∃ r : CanonicalOn U →ₗ[ℂ] CanonicalOn V,
      ∀ s x, r s x ((tangentSpaceCastModel 𝓘(ℂ) x).symm 1) =
        s (Opens.inclusion hVU x)
          ((tangentSpaceCastModel 𝓘(ℂ) (Opens.inclusion hVU x)).symm 1) := by
  refine ⟨{
    toFun := fun s => ⟨fun x => s (Opens.inclusion hVU x), ?_⟩
    map_add' := ?_
    map_smul' := ?_ }, ?_⟩
  · intro x
    apply (contMDiffAt_hom_bundle _).2
    constructor
    · exact contMDiffAt_id
    · have hs := ((contMDiffAt_hom_bundle _).mp
        (s.contMDiff (Opens.inclusion hVU x))).2
      have hi := (contMDiff_inclusion hVU : CMDiff ∞ (Opens.inclusion hVU : V → U))
      have hcomp := hs.comp x hi.contMDiffAt
      apply ContMDiffAt.congr_of_eventuallyEq hcomp
      have hsrc : (chartAt ℂ x).source ∈ 𝓝 x :=
        (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
      filter_upwards [hsrc] with y hy
      simp [Function.comp_apply, ContinuousLinearMap.inCoordinates,
        Bundle.Trivial.fiberBundle_trivializationAt']
      exact congrArg (fun L : ℂ →L[ℂ] ℂ => (s (Opens.inclusion hVU y)).comp L)
        (tangentSymmL_inclusion hVU x y hy)
  · intro s t
    ext x
    rfl
  · intro c s
    ext x
    rfl
  · intro s x
    rfl

noncomputable def CanonicalOn.restrict {U V : Opens E} (hVU : V ≤ U) :
    CanonicalOn U →ₗ[ℂ] CanonicalOn V :=
  Classical.choose (CanonicalOn.restrict_exists hVU)

private theorem canonicalFiber_ext {U : Opens E} {x : U}
    (s t : TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial U ℂ x)
    (h : s ((tangentSpaceCastModel 𝓘(ℂ) x).symm 1) =
      t ((tangentSpaceCastModel 𝓘(ℂ) x).symm 1)) : s = t := by
  apply ContinuousLinearMap.ext
  intro v
  let c := tangentSpaceCastModel 𝓘(ℂ) x
  have hv : v = (c v) • c.symm (1 : ℂ) := by
    apply c.injective
    rw [c.map_smul, c.apply_symm_apply]
    simp
  rw [hv, map_smul, map_smul, h]

private theorem canonicalRestrict_apply {U V : Opens E} (hVU : V ≤ U)
    (s : CanonicalOn U) (x : V) :
    CanonicalOn.restrict hVU s x = s (Opens.inclusion hVU x) := by
  apply canonicalFiber_ext
  exact Classical.choose_spec (CanonicalOn.restrict_exists hVU) s x

private theorem canonicalCover_ext (U : Opens E) (ι : Type*) (V : ι → Opens E)
    (hcover : U = ⨆ i, V i) (hsub : ∀ i, V i ≤ U)
    (s t : CanonicalOn U)
    (h : ∀ i, CanonicalOn.restrict (hsub i) s = CanonicalOn.restrict (hsub i) t) :
    s = t := by
  apply ContMDiffSection.ext
  intro x
  have hx : ∃ i, (x : E) ∈ V i := by
    exact Opens.mem_iSup.mp (hcover ▸ x.property)
  obtain ⟨i, hxi⟩ := hx
  have hi := congrArg (fun v : CanonicalOn (V i) => v ⟨x, hxi⟩) (h i)
  simpa [canonicalRestrict_apply] using hi

private theorem contMDiffAt_of_open_restrict {U V : Opens E} (hVU : V ≤ U)
    (F : U → ℂ →L[ℂ] ℂ) (x : V)
    (h : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞
      (fun y : V => F (Opens.inclusion hVU y)) x) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞ F
      (Opens.inclusion hVU x) := by
  exact ((contDiffWithinAt_localInvariantProp ∞).liftPropAt_iff_comp_inclusion
    hVU F x).mpr h

/-- Compatible holomorphic local sections glue uniquely on an open cover. -/
theorem HolOn.glue (U : Opens E) (ι : Type*) (V : ι → Opens E)
    (hcover : U = ⨆ i, V i) (hsub : ∀ i, V i ≤ U) (f : ∀ i, HolOn (V i))
    (hcompat : ∀ i j, HolOn.restrict (show V i ⊓ V j ≤ V i by simp) (f i) =
      HolOn.restrict (show V i ⊓ V j ≤ V j by simp) (f j)) :
    ∃! g : HolOn U, ∀ i, HolOn.restrict (hsub i) g = f i := by
  classical
  have cover (x : E) (hx : x ∈ U) : ∃ i, x ∈ V i := by
    rw [hcover, Opens.mem_iSup] at hx
    exact hx
  have compat (i j : ι) (x : E) (hi : x ∈ V i) (hj : x ∈ V j) :
      (f i).1 ⟨x, hi⟩ = (f j).1 ⟨x, hj⟩ := by
    have h := congrArg (fun s : HolOn (V i ⊓ V j) => s.1 ⟨x, ⟨hi, hj⟩⟩)
      (hcompat i j)
    simpa [HolOn.restrict] using h
  let gfun : U → ℂ := fun x =>
    (f (Classical.choose (cover x.1 x.2))).1
      ⟨x.1, Classical.choose_spec (cover x.1 x.2)⟩
  have value (i : ι) (x : E) (hx : x ∈ V i) :
      gfun ⟨x, hsub i hx⟩ = (f i).1 ⟨x, hx⟩ := by
    dsimp [gfun]
    exact compat _ i x (Classical.choose_spec (cover x (hsub i hx))) hx
  have hmem : IsHolOn U gfun := by
    intro x
    obtain ⟨i, hxi⟩ := cover x.1 x.2
    obtain ⟨a, ha, hfa⟩ := (f i).property ⟨x.1, hxi⟩
    refine ⟨a, ha, ?_⟩
    have hVi : (V i : Set E) ∈ 𝓝 (x : E) := (V i).isOpen.mem_nhds hxi
    filter_upwards [hfa, hVi] with y hfy hyVi hyU
    rw [value i y hyVi]
    exact hfy hyVi
  refine ⟨⟨gfun, hmem⟩, ?_, ?_⟩
  · intro i
    ext x
    exact value i x.1 x.2
  · intro g hg
    ext x
    obtain ⟨i, hxi⟩ := cover x.1 x.2
    have hi := congrArg (fun s : HolOn (V i) => s.1 ⟨x.1, hxi⟩) (hg i)
    simpa [HolOn.restrict, value i x.1 hxi] using hi

/-- Compatible simple-pole sections glue uniquely without filling the puncture. -/
theorem PoleOneOn.glue (p : E) (U : Opens E) (ι : Type*) (V : ι → Opens E)
    (hcover : U = ⨆ i, V i) (hsub : ∀ i, V i ≤ U)
    (f : ∀ i, PoleOneOn p (V i))
    (hcompat : ∀ i j, PoleOneOn.restrict p (show V i ⊓ V j ≤ V i by simp) (f i) =
      PoleOneOn.restrict p (show V i ⊓ V j ≤ V j by simp) (f j)) :
    ∃! g : PoleOneOn p U,
      ∀ i, PoleOneOn.restrict p (hsub i) g = f i := by
  classical
  have cover (x : E) (hx : x ∈ U) : ∃ i, x ∈ V i := by
    rw [hcover, Opens.mem_iSup] at hx
    exact hx
  have compat (i j : ι) (x : E) (hi : x ∈ V i) (hj : x ∈ V j)
      (hyp : x ≠ p) :
      (f i).1 ⟨⟨x, hi⟩, hyp⟩ = (f j).1 ⟨⟨x, hj⟩, hyp⟩ := by
    have h := congrArg (fun s : PoleOneOn p (V i ⊓ V j) =>
      s.1 ⟨⟨x, ⟨hi, hj⟩⟩, hyp⟩) (hcompat i j)
    simpa [PoleOneOn.restrict] using h
  let gfun : {x : U // (x : E) ≠ p} → ℂ := fun x =>
    (f (Classical.choose (cover x.1.1 x.1.2))).1
      ⟨⟨x.1.1, Classical.choose_spec (cover x.1.1 x.1.2)⟩, x.2⟩
  have value (i : ι) (x : E) (hx : x ∈ V i) (hyp : x ≠ p) :
      gfun ⟨⟨x, hsub i hx⟩, hyp⟩ = (f i).1 ⟨⟨x, hx⟩, hyp⟩ := by
    dsimp [gfun]
    exact compat _ i x (Classical.choose_spec (cover x (hsub i hx))) hx hyp
  have hmem : IsPoleOneOn p U gfun := by
    constructor
    · intro x hx
      obtain ⟨i, hxi⟩ := cover x.1 x.2
      obtain ⟨a, ha, hfa⟩ := (f i).property.1 ⟨x.1, hxi⟩ hx
      refine ⟨a, ha, ?_⟩
      have hVi : (V i : Set E) ∈ 𝓝 (x : E) := (V i).isOpen.mem_nhds hxi
      filter_upwards [hfa, hVi] with y hfy hyVi hyU hyp
      rw [value i y hyVi hyp]
      exact hfy hyVi hyp
    · intro hp
      obtain ⟨i, hpi⟩ := cover p hp
      obtain ⟨a, ha, hfa⟩ := (f i).property.2 hpi
      refine ⟨a, ha, ?_⟩
      have hVi : (V i : Set E) ∈ 𝓝[≠] p :=
        nhdsWithin_le_nhds ((V i).isOpen.mem_nhds hpi)
      filter_upwards [hfa, hVi] with y hfy hyVi hyU hyp
      rw [value i y hyVi hyp]
      exact hfy hyVi hyp
  refine ⟨⟨gfun, hmem⟩, ?_, ?_⟩
  · intro i
    ext x
    exact value i x.1.1 x.1.2 x.2
  · intro g hg
    ext x
    obtain ⟨i, hxi⟩ := cover x.1.1 x.1.2
    have hi := congrArg (fun s : PoleOneOn p (V i) =>
      s.1 ⟨⟨x.1.1, hxi⟩, x.2⟩) (hg i)
    simpa [PoleOneOn.restrict, value i x.1.1 hxi x.2] using hi

/-- Compatible local cotangent sections glue uniquely. -/
theorem CanonicalOn.glue (U : Opens E) (ι : Type*) (V : ι → Opens E)
    (hcover : U = ⨆ i, V i) (hsub : ∀ i, V i ≤ U)
    (f : ∀ i, CanonicalOn (V i))
    (hcompat : ∀ i j, CanonicalOn.restrict (show V i ⊓ V j ≤ V i by simp) (f i) =
      CanonicalOn.restrict (show V i ⊓ V j ≤ V j by simp) (f j)) :
    ∃! g : CanonicalOn U,
      ∀ i, CanonicalOn.restrict (hsub i) g = f i := by
  classical
  have cover (x : E) (hx : x ∈ U) : ∃ i, x ∈ V i := by
    rw [hcover, Opens.mem_iSup] at hx
    exact hx
  have compat (i j : ι) (x : E) (hi : x ∈ V i) (hj : x ∈ V j) :
      f i ⟨x, hi⟩ = f j ⟨x, hj⟩ := by
    have h := congrArg (fun s : CanonicalOn (V i ⊓ V j) => s ⟨x, ⟨hi, hj⟩⟩)
      (hcompat i j)
    simpa [canonicalRestrict_apply] using h
  let gfun : ∀ x : U,
      TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial U ℂ x := fun x =>
    f (Classical.choose (cover x.1 x.2))
      ⟨x.1, Classical.choose_spec (cover x.1 x.2)⟩
  have value (i : ι) (x : E) (hx : x ∈ V i) :
      gfun ⟨x, hsub i hx⟩ = f i ⟨x, hx⟩ := by
    dsimp [gfun]
    exact compat _ i x (Classical.choose_spec (cover x (hsub i hx))) hx
  let g : CanonicalOn U := ⟨gfun, by
    intro x
    apply (contMDiffAt_hom_bundle _).2
    constructor
    · exact contMDiffAt_id
    · obtain ⟨i, hxi⟩ := cover x.1 x.2
      let xi : V i := ⟨x.1, hxi⟩
      have hxEq : Opens.inclusion (hsub i) xi = x := Subtype.ext rfl
      rw [← hxEq]
      let coord : U → ℂ →L[ℂ] ℂ := fun y =>
        ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) : U → Type _)
          ℂ (Bundle.Trivial U ℂ) (Opens.inclusion (hsub i) xi) y
            (Opens.inclusion (hsub i) xi) y (gfun y)
      apply contMDiffAt_of_open_restrict (hsub i) coord xi
      have hf := ((contMDiffAt_hom_bundle _).mp ((f i).contMDiff xi)).2
      apply ContMDiffAt.congr_of_eventuallyEq hf
      have hsrc : (chartAt ℂ xi).source ∈ 𝓝 xi :=
        (chartAt ℂ xi).open_source.mem_nhds (mem_chart_source ℂ xi)
      filter_upwards [hsrc] with y hy
      dsimp [coord]
      rw [value i y.1 y.2]
      simp [ContinuousLinearMap.inCoordinates,
        Bundle.Trivial.fiberBundle_trivializationAt',
        tangentSymmL_inclusion (hsub i) xi y hy]⟩
  refine ⟨g, ?_, ?_⟩
  · intro i
    apply ContMDiffSection.ext
    intro x
    rw [canonicalRestrict_apply]
    change gfun ⟨x.1, hsub i x.2⟩ = f i x
    exact value i x.1 x.2
  · intro g hg
    apply canonicalCover_ext U ι V hcover hsub
    intro i
    exact (hg i).trans (by
      apply ContMDiffSection.ext
      intro x
      rw [canonicalRestrict_apply]
      change f i x = gfun ⟨x.1, hsub i x.2⟩
      exact (value i x.1 x.2).symm)

/-- Leading chart numerator of a local simple-pole section. -/
private theorem poleNumeratorValue_unique (p : E) (U : Opens E) (hp : p ∈ U)
    (f : {x : U // (x : E) ≠ p} → ℂ) (a b : ℂ → ℂ)
    (ha : AnalyticAt ℂ a ((chartAt ℂ p) p))
    (hb : AnalyticAt ℂ b ((chartAt ℂ p) p))
    (hfa : ∀ᶠ y in 𝓝[≠] p, ∀ hyU : y ∈ U, ∀ hyp : y ≠ p,
      ((chartAt ℂ p) y - (chartAt ℂ p) p) * f ⟨⟨y, hyU⟩, hyp⟩ =
        a ((chartAt ℂ p) y))
    (hfb : ∀ᶠ y in 𝓝[≠] p, ∀ hyU : y ∈ U, ∀ hyp : y ≠ p,
      ((chartAt ℂ p) y - (chartAt ℂ p) p) * f ⟨⟨y, hyU⟩, hyp⟩ =
        b ((chartAt ℂ p) y)) :
    a ((chartAt ℂ p) p) = b ((chartAt ℂ p) p) := by
  classical
  have hU : (U : Set E) ∈ 𝓝[≠] p :=
    nhdsWithin_le_nhds (U.isOpen.mem_nhds hp)
  have hFb : (fun y : E => a ((chartAt ℂ p) y)) =ᶠ[𝓝[≠] p]
      fun y => b ((chartAt ℂ p) y) := by
    filter_upwards [hfa, hfb, hU, self_mem_nhdsWithin] with y hfy hgy hyU hyp
    have hyn : y ≠ p := by simpa using hyp
    exact (hfy hyU hyn).symm.trans (hgy hyU hyn)
  have hEq := SameAtlasRRReview.punctured_chart_germ_unique p
    (fun y : E => a ((chartAt ℂ p) y)) a b (Filter.EventuallyEq.rfl) hFb
  exact tendsto_nhds_unique_of_eventuallyEq
    (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hb.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hEq

noncomputable def coeffAt (p : E) (U : Opens E) (hp : p ∈ U) :
    PoleOneOn p U →ₗ[ℂ] ℂ where
  toFun f := (Classical.choose (f.property.2 hp)) ((chartAt ℂ p) p)
  map_add' := by
    intro f g
    obtain ⟨hfgAn, hfg⟩ := Classical.choose_spec ((f + g).property.2 hp)
    obtain ⟨hfAn, hf⟩ := Classical.choose_spec (f.property.2 hp)
    obtain ⟨hgAn, hg⟩ := Classical.choose_spec (g.property.2 hp)
    apply poleNumeratorValue_unique p U hp (f + g : PoleOneOn p U).1
      (Classical.choose ((f + g).property.2 hp))
      (Classical.choose (f.property.2 hp) + Classical.choose (g.property.2 hp))
      hfgAn (hfAn.add hgAn) hfg
    filter_upwards [hf, hg] with y hfy hgy hyU hyp
    change ((chartAt ℂ p) y - (chartAt ℂ p) p) *
      (f.1 ⟨⟨y, hyU⟩, hyp⟩ + g.1 ⟨⟨y, hyU⟩, hyp⟩) = _
    rw [mul_add, hfy hyU hyp, hgy hyU hyp]
    rfl
  map_smul' := by
    intro c f
    obtain ⟨hcfAn, hcf⟩ := Classical.choose_spec ((c • f).property.2 hp)
    obtain ⟨hfAn, hf⟩ := Classical.choose_spec (f.property.2 hp)
    apply poleNumeratorValue_unique p U hp (c • f : PoleOneOn p U).1
      (Classical.choose ((c • f).property.2 hp)) (c • Classical.choose (f.property.2 hp))
      hcfAn hfAn.const_smul hcf
    filter_upwards [hf] with y hfy hyU hyp
    change ((chartAt ℂ p) y - (chartAt ℂ p) p) *
      (c * f.1 ⟨⟨y, hyU⟩, hyp⟩) = _
    rw [mul_left_comm, hfy hyU hyp]
    rfl

/-- The local simple-pole sections over the whole surface are the literal
`actualH0Point`, not an alternative global certificate space. -/
noncomputable def poleOneOnTopEquiv (p : E) :
    PoleOneOn p ⊤ ≃ₗ[ℂ] actualH0Point p where
  toFun f := ⟨fun x => f.1 ⟨⟨x, trivial⟩, x.property⟩, by
    letI : T1Space E := ChartedSpace.t1Space ℂ E
    constructor
    · intro x hx
      obtain ⟨a, ha, hfa⟩ := f.property.1 ⟨x, trivial⟩ hx
      refine ⟨{p}ᶜ, isOpen_compl_singleton, by simpa using hx, by simp,
        a, ha, ?_⟩
      filter_upwards [hfa] with y hfy hy
      exact hfy trivial hy
    · obtain ⟨a, ha, hfa⟩ := f.property.2 trivial
      refine ⟨a, ha, ?_⟩
      filter_upwards [hfa] with y hfy hy
      exact hfy trivial hy⟩
  invFun f := ⟨fun x => f.1 ⟨x.1, x.2⟩, by
    constructor
    · intro x hx
      obtain ⟨W, hW, hxW, hpW, a, ha, hfa⟩ := f.property.1 x hx
      refine ⟨a, ha, ?_⟩
      filter_upwards [hfa] with y hfy hyU hyp
      exact hfy hyp
    · intro hp
      obtain ⟨a, ha, hfa⟩ := f.property.2
      refine ⟨a, ha, ?_⟩
      filter_upwards [hfa] with y hfy hyU hyp
      exact hfy hyp⟩
  left_inv := by
    intro f
    ext x
    rfl
  right_inv := by
    intro f
    ext x
    rfl
  map_add' := by
    intro f g
    ext x
    rfl
  map_smul' := by
    intro c f
    ext x
    rfl

/-- The full open subset inherits exactly the original cotangent bundle. -/
theorem canonicalOnTopEquiv_exists :
    ∃ e : CanonicalOn (E := E) ⊤ ≃ₗ[ℂ] ActualCanonicalSection E,
      ∀ (p : E) (s : CanonicalOn (E := E) ⊤),
        s ⟨p, trivial⟩
          ((tangentSpaceCastModel 𝓘(ℂ) (⟨p, trivial⟩ : (⊤ : Opens E))).symm 1) =
        actualCanonicalEvaluation p (e s) := by
  let toGlobal (s : CanonicalOn (E := E) ⊤) : ActualCanonicalSection E :=
    ⟨fun p => s ⟨p, trivial⟩, by
      intro p
      apply (contMDiffAt_hom_bundle _).2
      constructor
      · exact contMDiffAt_id
      · let F : E → ℂ →L[ℂ] ℂ := fun q =>
          ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) : E → Type _)
            ℂ (Bundle.Trivial E ℂ) p q p q (s ⟨q, trivial⟩)
        apply (contMDiffAt_subtype_iff (U := (⊤ : Opens E))
          (f := F) (x := (⟨p, trivial⟩ : (⊤ : Opens E)))).mp
        have hs := ((contMDiffAt_hom_bundle _).mp
          (s.contMDiff (⟨p, trivial⟩ : (⊤ : Opens E)))).2
        apply ContMDiffAt.congr_of_eventuallyEq hs
        have hsrc : (chartAt ℂ (⟨p, trivial⟩ : (⊤ : Opens E))).source ∈
            𝓝 (⟨p, trivial⟩ : (⊤ : Opens E)) :=
          (chartAt ℂ (⟨p, trivial⟩ : (⊤ : Opens E))).open_source.mem_nhds
            (mem_chart_source ℂ (⟨p, trivial⟩ : (⊤ : Opens E)))
        filter_upwards [hsrc] with y hy
        simp [F, ContinuousLinearMap.inCoordinates,
          Bundle.Trivial.fiberBundle_trivializationAt',
          tangentSymmL_subtype (⟨p, trivial⟩ : (⊤ : Opens E)) y hy]⟩
  let toTop (s : ActualCanonicalSection E) : CanonicalOn (E := E) ⊤ :=
    ⟨fun x => s x.1, by
      intro x
      apply (contMDiffAt_hom_bundle _).2
      constructor
      · exact contMDiffAt_id
      · let F : E → ℂ →L[ℂ] ℂ := fun q =>
          ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) : E → Type _)
            ℂ (Bundle.Trivial E ℂ) x.1 q x.1 q (s q)
        have hF := ((contMDiffAt_hom_bundle _).mp (s.contMDiff x.1)).2
        have hFs := (contMDiffAt_subtype_iff (U := (⊤ : Opens E))
          (f := F) (x := x)).mpr hF
        apply ContMDiffAt.congr_of_eventuallyEq hFs
        have hsrc : (chartAt ℂ x).source ∈ 𝓝 x :=
          (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
        filter_upwards [hsrc] with y hy
        simp [F, ContinuousLinearMap.inCoordinates,
          Bundle.Trivial.fiberBundle_trivializationAt',
          tangentSymmL_subtype x y hy]⟩
  refine ⟨{
    toFun := toGlobal
    invFun := toTop
    left_inv := by
      intro s
      apply ContMDiffSection.ext
      intro x
      rfl
    right_inv := by
      intro s
      apply ContMDiffSection.ext
      intro x
      rfl
    map_add' := by
      intro s t
      apply ContMDiffSection.ext
      intro x
      rfl
    map_smul' := by
      intro c s
      apply ContMDiffSection.ext
      intro x
      rfl }, ?_⟩
  intro p s
  rfl

noncomputable def canonicalOnTopEquiv :
    CanonicalOn (E := E) ⊤ ≃ₗ[ℂ] ActualCanonicalSection E :=
  Classical.choose canonicalOnTopEquiv_exists

theorem coeffAt_top_commutes (p : E) (f : PoleOneOn p ⊤) :
    coeffAt p ⊤ (by trivial) f =
      poleCoefficient p (poleOneOnTopEquiv p f) := by
  obtain ⟨ha, hfa⟩ := Classical.choose_spec (f.property.2 trivial)
  obtain ⟨hb, hfb⟩ := SameAtlasRRReview.poleNumerator_spec p
    (poleOneOnTopEquiv p f)
  apply SameAtlasRRReview.pole_witness_value_unique p
    (poleOneOnTopEquiv p f).1
    (Classical.choose (f.property.2 trivial))
    (SameAtlasRRReview.poleNumerator p (poleOneOnTopEquiv p f))
    ha hb
  · filter_upwards [hfa] with y hfy hy
    exact hfy trivial hy
  · exact hfb

theorem canonical_eval_top_commutes (p : E) (s : CanonicalOn (E := E) ⊤) :
    s ⟨p, trivial⟩
      ((tangentSpaceCastModel 𝓘(ℂ) (⟨p, trivial⟩ : (⊤ : Opens E))).symm 1) =
      actualCanonicalEvaluation p (canonicalOnTopEquiv s) :=
  Classical.choose_spec canonicalOnTopEquiv_exists p s

end SameAtlasRRLocal

#print axioms SameAtlasRRLocal.HolOn
#print axioms SameAtlasRRLocal.PoleOneOn
#print axioms SameAtlasRRLocal.HolOn.restrict
#print axioms SameAtlasRRLocal.PoleOneOn.restrict
#print axioms SameAtlasRRLocal.HolOn.glue
#print axioms SameAtlasRRLocal.PoleOneOn.glue
#print axioms SameAtlasRRLocal.coeffAt
#print axioms SameAtlasRRLocal.poleOneOnTopEquiv
#print axioms SameAtlasRRLocal.coeffAt_top_commutes
#print axioms SameAtlasRRLocal.CanonicalOn.restrict_exists
#print axioms SameAtlasRRLocal.CanonicalOn.restrict
#print axioms SameAtlasRRLocal.CanonicalOn.glue
#print axioms SameAtlasRRLocal.canonicalOnTopEquiv_exists
#print axioms SameAtlasRRLocal.canonicalOnTopEquiv
#print axioms SameAtlasRRLocal.canonical_eval_top_commutes

namespace SameAtlasRRReview

private theorem analytic_quotient_of_zero (a : ℂ → ℂ) (z : ℂ)
    (ha : AnalyticAt ℂ a z) (hz : a z = 0) :
    ∃ b : ℂ → ℂ, AnalyticAt ℂ b z ∧
      ∀ w : ℂ, a w = (w - z) * b w := by
  obtain ⟨P, hP⟩ := ha
  refine ⟨dslope a z, (hP.has_fpower_series_dslope_fslope).analyticAt, ?_⟩
  intro w
  simpa [hz, smul_eq_mul] using (sub_smul_dslope a z w).symm

end SameAtlasRRReview

namespace SameAtlasRRLocal

open SameAtlasRRReview
open TopologicalSpace
set_option synthInstance.maxHeartbeats 1000000

variable {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]


noncomputable def holToPole (p : E) (U : Opens E) : HolOn U →ₗ[ℂ] PoleOneOn p U where
  toFun f := ⟨fun y => f.1 y.1, by
    constructor
    · intro x hx
      obtain ⟨a, ha, he⟩ := f.property x
      exact ⟨a, ha, by
        filter_upwards [he] with y hy hyU hyp
        exact hy hyU⟩
    · intro hp
      obtain ⟨a, ha, he⟩ := f.property ⟨p, hp⟩
      refine ⟨fun z => (z - (chartAt ℂ p) p) * a z,
        (analyticAt_id.sub analyticAt_const).mul ha, ?_⟩
      filter_upwards [he.filter_mono nhdsWithin_le_nhds] with y hy hyU hyp
      rw [hy hyU]⟩
  map_add' := by intro f g; ext x; rfl
  map_smul' := by intro c f; ext x; rfl

theorem coeffAt_holToPole_zero (p : E) (U : Opens E) (hp : p ∈ U)
    (f : HolOn U) : coeffAt p U hp (holToPole p U f) = 0 := by
  obtain ⟨a, ha, he⟩ := f.property ⟨p, hp⟩
  let b := Classical.choose ((holToPole p U f).property.2 hp)
  obtain ⟨hb, hbe⟩ := Classical.choose_spec ((holToPole p U f).property.2 hp)
  have h := poleNumeratorValue_unique p U hp (holToPole p U f).1 b
    (fun z => (z - (chartAt ℂ p) p) * a z) hb
    ((analyticAt_id.sub analyticAt_const).mul ha) hbe
    (by
      filter_upwards [he.filter_mono nhdsWithin_le_nhds] with y hy hyU hyp
      simpa [holToPole] using congrArg
        (fun v : ℂ => ((chartAt ℂ p) y - (chartAt ℂ p) p) * v) (hy hyU))
  exact h.trans (by simp)

private theorem poleOneOn_zero_coefficient_local_extension
    (p : E) (U : Opens E) (hp : p ∈ U) (f : PoleOneOn p U)
    (hf : coeffAt p U hp f = 0) :
    ∃ g : HolOn U, holToPole p U g = f := by
  classical
  letI : T1Space E := ChartedSpace.t1Space ℂ E
  let a := Classical.choose (f.property.2 hp)
  obtain ⟨ha, hfa⟩ := Classical.choose_spec (f.property.2 hp)
  have hazero : a ((chartAt ℂ p) p) = 0 := hf
  obtain ⟨b, hb, hfactor⟩ := SameAtlasRRReview.analytic_quotient_of_zero
    a ((chartAt ℂ p) p) ha hazero
  have hnear : ∀ᶠ y in 𝓝[≠] p, ∀ hyU : y ∈ U, ∀ hyp : y ≠ p,
      f.1 ⟨⟨y, hyU⟩, hyp⟩ = b ((chartAt ℂ p) y) := by
    have hne : ∀ᶠ y in 𝓝[≠] p, (chartAt ℂ p) y ≠ (chartAt ℂ p) p :=
      (chartAt ℂ p).eventually_ne_nhdsWithin (mem_chart_source ℂ p)
    filter_upwards [hfa, hne] with y hfy hcy hyU hyp
    have hm := hfy hyU hyp
    change _ = a ((chartAt ℂ p) y) at hm
    rw [hfactor] at hm
    exact mul_left_cancel₀ (sub_ne_zero.mpr hcy) hm
  let F : U → ℂ := fun x =>
    if hx : (x : E) = p then b ((chartAt ℂ p) p) else f.1 ⟨x, hx⟩
  have hF : IsHolOn U F := by
    intro x
    by_cases hx : (x : E) = p
    · have hxU : (x : E) ∈ U := x.property
      have hxp : x = ⟨p, hp⟩ := Subtype.ext hx
      subst x
      refine ⟨b, hb, ?_⟩
      rw [← pure_sup_nhdsNE p]
      constructor
      · simp [F]
      · filter_upwards [hnear, self_mem_nhdsWithin] with y hfy hy hyU
        have hyn : y ≠ p := by simpa using hy
        simpa [F, hyn] using hfy hyU hyn
    · obtain ⟨a', ha', hfa'⟩ := f.property.1 x hx
      refine ⟨a', ha', ?_⟩
      filter_upwards [hfa', isOpen_compl_singleton.mem_nhds hx]
        with y hfy hy hyU
      have hyn : y ≠ p := by simpa using hy
      simpa [F, hyn] using hfy hyU hyn
  refine ⟨⟨F, hF⟩, ?_⟩
  ext x
  have hx : (x.1 : E) ≠ p := x.2
  simp [holToPole, F, hx]

theorem coeffAt_ker_eq_holToPole_range (p : E) (U : Opens E) (hp : p ∈ U) :
    (coeffAt p U hp).ker = (holToPole p U).range := by
  ext f
  constructor
  · intro hf
    exact poleOneOn_zero_coefficient_local_extension p U hp f (LinearMap.mem_ker.mp hf)
  · rintro ⟨g, rfl⟩
    exact LinearMap.mem_ker.mpr (coeffAt_holToPole_zero p U hp g)

noncomputable abbrev localPointPrincipalPartQuotient (p : E) (U : Opens E) :=
  PoleOneOn p U ⧸ (holToPole p U).range

noncomputable def localPointCoefficient (p : E) (U : Opens E) (hp : p ∈ U) :
    localPointPrincipalPartQuotient p U →ₗ[ℂ] ℂ :=
  (holToPole p U).range.liftQ (coeffAt p U hp)
    (coeffAt_ker_eq_holToPole_range p U hp).symm.le

theorem localPointCoefficient_injective (p : E) (U : Opens E) (hp : p ∈ U) :
    Function.Injective (localPointCoefficient p U hp) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot' _ (coeffAt p U hp)
    (coeffAt_ker_eq_holToPole_range p U hp).symm

theorem localPointCoefficient_mkQ (p : E) (U : Opens E) (hp : p ∈ U)
    (f : PoleOneOn p U) :
    localPointCoefficient p U hp ((holToPole p U).range.mkQ f) = coeffAt p U hp f :=
  rfl

/-- Off the marked point, the pole condition is exactly ordinary holomorphy. -/
noncomputable def poleToHolAway (p : E) (U : Opens E) (hp : p ∉ U) :
    PoleOneOn p U →ₗ[ℂ] HolOn U where
  toFun f := ⟨fun x => f.1 ⟨x, fun hx => hp (hx ▸ x.property)⟩, by
    intro x
    have hx : (x : E) ≠ p := fun h => hp (h ▸ x.property)
    obtain ⟨a, ha, he⟩ := f.property.1 x hx
    refine ⟨a, ha, ?_⟩
    filter_upwards [he] with y hy hyU
    exact hy hyU (fun h => hp (h ▸ hyU))⟩
  map_add' := by intro f g; ext x; rfl
  map_smul' := by intro c f; ext x; rfl

theorem poleToHolAway_left_inv (p : E) (U : Opens E) (hp : p ∉ U)
    (f : PoleOneOn p U) : holToPole p U (poleToHolAway p U hp f) = f := by
  ext x
  rfl

theorem poleToHolAway_right_inv (p : E) (U : Opens E) (hp : p ∉ U)
    (f : HolOn U) : poleToHolAway p U hp (holToPole p U f) = f := by
  ext x
  rfl

noncomputable def poleHolAwayEquiv (p : E) (U : Opens E) (hp : p ∉ U) :
    PoleOneOn p U ≃ₗ[ℂ] HolOn U :=
  LinearEquiv.ofLinear (poleToHolAway p U hp) (holToPole p U)
    (by ext f x; rfl) (by ext f x; rfl)

theorem holToPole_injective (p : E) (U : Opens E) :
    Function.Injective (holToPole p U) := by
  refine LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr ?_)
  intro f hf
  apply Subtype.ext
  funext x
  by_cases hx : (x : E) = p
  · have hp : p ∈ U := hx ▸ x.property
    obtain ⟨a, ha, he⟩ := f.property ⟨p, hp⟩
    have hfa : (fun _ : E => (0 : ℂ)) =ᶠ[𝓝[≠] p]
        fun y => a ((chartAt ℂ p) y) := by
      have hU : (U : Set E) ∈ 𝓝[≠] p :=
        nhdsWithin_le_nhds (U.isOpen.mem_nhds hp)
      filter_upwards [he.filter_mono nhdsWithin_le_nhds, hU,
        self_mem_nhdsWithin] with y hy hyU hyp
      have hyn : y ≠ p := by simpa using hyp
      have hfzero : f.1 ⟨y, hyU⟩ = 0 := by
        have h := congrArg (fun g : PoleOneOn p U => g.1 ⟨⟨y, hyU⟩, hyn⟩) hf
        simpa [holToPole] using h
      exact hfzero.symm.trans (hy hyU)
    have hEq := SameAtlasRRReview.punctured_chart_germ_unique p
      (fun _ : E => (0 : ℂ)) (fun _ => 0) a
      (Filter.EventuallyEq.rfl) hfa
    have hazero : a ((chartAt ℂ p) p) = 0 := by
      symm
      exact tendsto_nhds_unique_of_eventuallyEq
        ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ))
          ((chartAt ℂ p) p)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hEq
    have hpvalue : f.1 ⟨p, hp⟩ = a ((chartAt ℂ p) p) :=
      (Filter.Eventually.self_of_nhds he) hp
    have hxp : x = ⟨p, hp⟩ := Subtype.ext hx
    simpa [hxp, hpvalue, hazero]
  · have h := congrArg (fun g : PoleOneOn p U => g.1 ⟨x, hx⟩) hf
    simpa [holToPole] using h

noncomputable def puncturedOpen (p : E) : Opens E :=
  ⟨{p}ᶜ, by
    letI : T1Space E := ChartedSpace.t1Space ℂ E
    exact isOpen_compl_singleton⟩

noncomputable def overlapOpen (p : E) (U : Opens E) : Opens E :=
  U ⊓ puncturedOpen p

private theorem point_not_mem_overlap (p : E) (U : Opens E) :
    p ∉ overlapOpen p U := by
  intro hp
  exact hp.2 rfl

noncomputable def twoOpenCoboundary (p : E) (U : Opens E) :
    HolOn U × HolOn (puncturedOpen p) →ₗ[ℂ] HolOn (overlapOpen p U) where
  toFun h := HolOn.restrict (show overlapOpen p U ≤ U by simp [overlapOpen]) h.1 -
    HolOn.restrict (show overlapOpen p U ≤ puncturedOpen p by simp [overlapOpen]) h.2
  map_add' := by intro h k; simp [add_sub_add_comm]
  map_smul' := by intro c h; simp [smul_sub]

noncomputable abbrev twoOpenCechOne (p : E) (U : Opens E) :=
  HolOn (overlapOpen p U) ⧸ (twoOpenCoboundary p U).range

noncomputable def localPoleCechBoundary (p : E) (U : Opens E) :
    PoleOneOn p U →ₗ[ℂ] twoOpenCechOne p U :=
  (twoOpenCoboundary p U).range.mkQ.comp
    ((poleToHolAway p (overlapOpen p U) (point_not_mem_overlap p U)).comp
      (PoleOneOn.restrict p (show overlapOpen p U ≤ U by simp [overlapOpen])))

noncomputable def globalPoleRestrict (p : E) (U : Opens E) :
    PoleOneOn p ⊤ →ₗ[ℂ] PoleOneOn p U :=
  PoleOneOn.restrict p (show U ≤ (⊤ : Opens E) by simp)

theorem localPoleCechBoundary_global_zero (p : E) (U : Opens E)
    (f : PoleOneOn p ⊤) :
    localPoleCechBoundary p U (globalPoleRestrict p U f) = 0 := by
  let V := puncturedOpen p
  let W := overlapOpen p U
  let fV : HolOn V := poleToHolAway p V (by simp [V, puncturedOpen])
    (PoleOneOn.restrict p (show V ≤ (⊤ : Opens E) by simp) f)
  have hmem : (poleToHolAway p W (point_not_mem_overlap p U))
      (PoleOneOn.restrict p (show W ≤ U by simp [W, overlapOpen])
        (globalPoleRestrict p U f)) ∈ (twoOpenCoboundary p U).range := by
    refine ⟨(0, -fV), ?_⟩
    ext x
    simp [twoOpenCoboundary, HolOn.restrict, poleToHolAway,
      PoleOneOn.restrict, globalPoleRestrict, fV, W, V]
  change (twoOpenCoboundary p U).range.mkQ _ = 0
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  exact hmem

private theorem twoOpen_cover (p : E) (U : Opens E) (hp : p ∈ U) :
    (⊤ : Opens E) = ⨆ i : Bool, if i then puncturedOpen p else U := by
  ext x
  constructor
  · intro _
    by_cases hx : x = p
    · subst x
      exact Opens.mem_iSup.mpr ⟨false, by simpa using hp⟩
    · exact Opens.mem_iSup.mpr ⟨true, by simpa [puncturedOpen] using hx⟩
  · intro _
    trivial

theorem localPoleCechBoundary_zero_gives_global_correction
    (p : E) (U : Opens E) (hp : p ∈ U) (a : PoleOneOn p U)
    (ha : localPoleCechBoundary p U a = 0) :
    ∃ (g : PoleOneOn p ⊤) (h : HolOn U),
      globalPoleRestrict p U g = a - holToPole p U h := by
  let V := puncturedOpen p
  let W := overlapOpen p U
  have hclass : (poleToHolAway p W (point_not_mem_overlap p U))
      (PoleOneOn.restrict p (show W ≤ U by simp [W, overlapOpen]) a) ∈
        (twoOpenCoboundary p U).range := by
    change (twoOpenCoboundary p U).range.mkQ _ = 0 at ha
    rwa [← LinearMap.mem_ker, Submodule.ker_mkQ] at ha
  obtain ⟨⟨hU, hV⟩, hUV⟩ := hclass
  let C : Bool → Opens E := fun i => if i then V else U
  let pieces : (i : Bool) → PoleOneOn p (C i) := fun i => by
    cases i
    · exact a - holToPole p U hU
    · exact -holToPole p V hV
  have hcompat : ∀ i j, PoleOneOn.restrict p
      (show C i ⊓ C j ≤ C i by simp) (pieces i) =
      PoleOneOn.restrict p (show C i ⊓ C j ≤ C j by simp) (pieces j) := by
    intro i j
    cases i <;> cases j
    · rfl
    · ext x
      have hx : (x.1.1 : E) ∈ W := x.1.property
      have heq := congrArg (fun k : HolOn W => k.1 ⟨x.1.1, hx⟩) hUV
      simp [twoOpenCoboundary, HolOn.restrict, poleToHolAway, holToPole,
        PoleOneOn.restrict, W, C, pieces] at heq ⊢
      linear_combination -heq
    · ext x
      have hx : (x.1.1 : E) ∈ W := by
        exact ⟨x.1.property.2, x.1.property.1⟩
      have heq := congrArg (fun k : HolOn W => k.1 ⟨x.1.1, hx⟩) hUV
      simp [twoOpenCoboundary, HolOn.restrict, poleToHolAway, holToPole,
        PoleOneOn.restrict, W, C, pieces] at heq ⊢
      linear_combination heq
    · rfl
  obtain ⟨g, hg, _⟩ := PoleOneOn.glue p ⊤ Bool C
    (by simpa [C, V] using twoOpen_cover p U hp)
    (by intro i; simp [C]) pieces hcompat
  refine ⟨g, hU, ?_⟩
  simpa [globalPoleRestrict, C, pieces] using hg false

theorem coeffAt_restrict (p : E) {U V : Opens E} (hVU : V ≤ U)
    (hpV : p ∈ V) (f : PoleOneOn p U) :
    coeffAt p V hpV (PoleOneOn.restrict p hVU f) =
      coeffAt p U (hVU hpV) f := by
  let a := Classical.choose ((PoleOneOn.restrict p hVU f).property.2 hpV)
  let b := Classical.choose (f.property.2 (hVU hpV))
  obtain ⟨ha, hfa⟩ := Classical.choose_spec
    ((PoleOneOn.restrict p hVU f).property.2 hpV)
  obtain ⟨hb, hfb⟩ := Classical.choose_spec (f.property.2 (hVU hpV))
  apply poleNumeratorValue_unique p V hpV
    (PoleOneOn.restrict p hVU f).1 a b ha hb hfa
  filter_upwards [hfb] with y hy hyV hyp
  simpa [PoleOneOn.restrict] using hy (hVU hyV) hyp

theorem coeffAt_global_restrict (p : E) (U : Opens E) (hp : p ∈ U)
    (f : PoleOneOn p ⊤) :
    coeffAt p U hp (globalPoleRestrict p U f) = coeffAt p ⊤ trivial f := by
  exact coeffAt_restrict p (show U ≤ (⊤ : Opens E) by simp) hp f

theorem localPoleCechBoundary_hol_zero (p : E) (U : Opens E)
    (f : HolOn U) :
    localPoleCechBoundary p U (holToPole p U f) = 0 := by
  let W := overlapOpen p U
  have hmem : (poleToHolAway p W (point_not_mem_overlap p U))
      (PoleOneOn.restrict p (show W ≤ U by simp [W, overlapOpen])
        (holToPole p U f)) ∈ (twoOpenCoboundary p U).range := by
    refine ⟨(f, 0), ?_⟩
    ext x
    simp [twoOpenCoboundary, HolOn.restrict, poleToHolAway,
      PoleOneOn.restrict, holToPole, W]
  change (twoOpenCoboundary p U).range.mkQ _ = 0
  rwa [← LinearMap.mem_ker, Submodule.ker_mkQ]


theorem twoOpenCech_exact_at_coefficients (p : E) (U : Opens E) (hp : p ∈ U)
    (c : ℂ) :
    (∃ f : PoleOneOn p U,
      coeffAt p U hp f = c ∧ localPoleCechBoundary p U f = 0) ↔
      ∃ g : actualH0Point p, poleCoefficient p g = c := by
  constructor
  · rintro ⟨f, hcoeff, hclass⟩
    obtain ⟨g, h, hrestrict⟩ :=
      localPoleCechBoundary_zero_gives_global_correction p U hp f hclass
    have heq := congrArg (coeffAt p U hp) hrestrict
    have hlocal : coeffAt p U hp (globalPoleRestrict p U g) = c := by
      simpa [map_sub, coeffAt_holToPole_zero p U hp h, hcoeff] using heq
    refine ⟨poleOneOnTopEquiv p g, ?_⟩
    rw [← coeffAt_top_commutes p g, ← coeffAt_global_restrict p U hp g]
    exact hlocal
  · rintro ⟨g, hg⟩
    let fTop : PoleOneOn p ⊤ := (poleOneOnTopEquiv p).symm g
    refine ⟨globalPoleRestrict p U fTop, ?_,
      localPoleCechBoundary_global_zero p U fTop⟩
    rw [coeffAt_global_restrict, coeffAt_top_commutes]
    simpa [fTop] using hg

private theorem chart_transition_analytic (p x : E)
    (hx : x ∈ (chartAt ℂ p).source) :
    AnalyticAt ℂ (fun z : ℂ => (chartAt ℂ p) ((chartAt ℂ x).symm z))
      ((chartAt ℂ x) x) := by
  let z := (chartAt ℂ x) x
  have hxchart : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hz : z ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hxchart
  have hsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (chartAt ℂ x).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hz
  have hchart : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (chartAt ℂ p) x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hx
  have hchart' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (chartAt ℂ p)
      ((chartAt ℂ x).symm z) := by
    simpa [z, (chartAt ℂ x).left_inv hxchart] using hchart
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞
      ((chartAt ℂ p) ∘ (chartAt ℂ x).symm) z := by
    exact hchart'.comp z hsymm
  have hsmooth : ContDiffAt ℂ ∞
      ((chartAt ℂ p) ∘ (chartAt ℂ x).symm) z := hcomp.contDiffAt
  obtain ⟨s, hs, hdiff⟩ := hsmooth.contDiffOn (m := 1) (by simp) (by simp)
  exact (hdiff.differentiableOn (by norm_num)).analyticAt hs

noncomputable def chartSourceOpen (p : E) : Opens E :=
  ⟨(chartAt ℂ p).source, (chartAt ℂ p).open_source⟩

noncomputable def chartPoleSection (p : E) (c : ℂ) :
    PoleOneOn p (chartSourceOpen p) := by
  let z₀ := (chartAt ℂ p) p
  refine ⟨fun y => c / ((chartAt ℂ p) y.1.1 - z₀), ?_⟩
  constructor
  · intro x hx
    let b : ℂ → ℂ := fun z => (chartAt ℂ p) ((chartAt ℂ (x : E)).symm z)
    have hb : AnalyticAt ℂ b ((chartAt ℂ (x : E)) x) :=
      chart_transition_analytic p x.1 x.property
    have hsrc : (x : E) ∈ (chartAt ℂ (x : E)).source :=
      mem_chart_source ℂ (x : E)
    have hbval : b ((chartAt ℂ (x : E)) x) = (chartAt ℂ p) x := by
      simp [b, (chartAt ℂ (x : E)).left_inv hsrc]
    have hne : (chartAt ℂ p) x ≠ z₀ := by
      intro h
      exact hx ((chartAt ℂ p).injOn x.property (mem_chart_source ℂ p) h)
    refine ⟨fun z => c / (b z - z₀),
      analyticAt_const.div (hb.sub analyticAt_const)
        (by simpa [hbval] using sub_ne_zero.mpr hne), ?_⟩
    filter_upwards [(chartAt ℂ (x : E)).open_source.mem_nhds hsrc]
      with y hy hyU hyp
    simp [b, (chartAt ℂ (x : E)).left_inv hy]
  · intro hp
    refine ⟨fun _ => c, analyticAt_const, ?_⟩
    filter_upwards with y hyU hyp
    have hne : (chartAt ℂ p) y ≠ z₀ := by
      intro h
      exact hyp ((chartAt ℂ p).injOn hyU (mem_chart_source ℂ p) h)
    simpa [z₀] using mul_div_cancel₀ c (sub_ne_zero.mpr hne)

theorem coeffAt_chartPoleSection (p : E) (c : ℂ) :
    coeffAt p (chartSourceOpen p) (mem_chart_source ℂ p)
      (chartPoleSection p c) = c := by
  let U := chartSourceOpen p
  let a := Classical.choose ((chartPoleSection p c).property.2
    (mem_chart_source ℂ p))
  obtain ⟨ha, hfa⟩ := Classical.choose_spec
    ((chartPoleSection p c).property.2 (mem_chart_source ℂ p))
  change a ((chartAt ℂ p) p) = c
  apply poleNumeratorValue_unique p U (mem_chart_source ℂ p)
    (chartPoleSection p c).1 a (fun _ => c) ha analyticAt_const hfa
  filter_upwards with y hyU hyp
  have hne : (chartAt ℂ p) y ≠ (chartAt ℂ p) p := by
    intro h
    exact hyp ((chartAt ℂ p).injOn hyU (mem_chart_source ℂ p) h)
  simpa [chartPoleSection] using mul_div_cancel₀ c (sub_ne_zero.mpr hne)

noncomputable def chartPoleLinear (p : E) :
    ℂ →ₗ[ℂ] PoleOneOn p (chartSourceOpen p) where
  toFun := chartPoleSection p
  map_add' := by
    intro c d
    ext x
    simp [chartPoleSection, add_div]
  map_smul' := by
    intro c d
    ext x
    simp [chartPoleSection, smul_eq_mul, mul_div_assoc]

noncomputable def scalarCechBoundary (p : E) :
    ℂ →ₗ[ℂ] twoOpenCechOne p (chartSourceOpen p) :=
  (localPoleCechBoundary p (chartSourceOpen p)).comp (chartPoleLinear p)

theorem scalarCechBoundary_ker (p : E) :
    (scalarCechBoundary p).ker = (SameAtlasRRReview.poleCoefficient p).range := by
  ext c
  rw [LinearMap.mem_ker]
  change localPoleCechBoundary p (chartSourceOpen p) (chartPoleSection p c) = 0 ↔ _
  rw [LinearMap.mem_range]
  rw [← (twoOpenCech_exact_at_coefficients p (chartSourceOpen p)
    (mem_chart_source ℂ p) c)]
  constructor
  · intro hc
    exact ⟨chartPoleSection p c, coeffAt_chartPoleSection p c, hc⟩
  · rintro ⟨f, hfcoeff, hfclass⟩
    have hdiff : coeffAt p (chartSourceOpen p) (mem_chart_source ℂ p)
        (chartPoleSection p c - f) = 0 := by
      rw [map_sub, coeffAt_chartPoleSection, hfcoeff, sub_self]
    obtain ⟨h, hh⟩ := (LinearMap.mem_range).mp
      ((coeffAt_ker_eq_holToPole_range p (chartSourceOpen p)
        (mem_chart_source ℂ p)).symm ▸ LinearMap.mem_ker.mpr hdiff)
    have hzero := localPoleCechBoundary_hol_zero p (chartSourceOpen p) h
    have heq := congrArg (localPoleCechBoundary p (chartSourceOpen p)) hh
    rw [hzero, map_sub, hfclass, sub_zero] at heq
    exact heq.symm

noncomputable def principalPartCechEmbedding (p : E) :
    (ℂ ⧸ (SameAtlasRRReview.poleCoefficient p).range) →ₗ[ℂ]
      twoOpenCechOne p (chartSourceOpen p) :=
  (SameAtlasRRReview.poleCoefficient p).range.liftQ (scalarCechBoundary p)
    (scalarCechBoundary_ker p).symm.le

theorem principalPartCechEmbedding_injective (p : E) :
    Function.Injective (principalPartCechEmbedding p) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot' _ (scalarCechBoundary p)
    (scalarCechBoundary_ker p).symm

theorem principalPartCechEmbedding_mkQ (p : E) (c : ℂ) :
    principalPartCechEmbedding p
      ((SameAtlasRRReview.poleCoefficient p).range.mkQ c) =
      scalarCechBoundary p c :=
  rfl


end SameAtlasRRLocal
