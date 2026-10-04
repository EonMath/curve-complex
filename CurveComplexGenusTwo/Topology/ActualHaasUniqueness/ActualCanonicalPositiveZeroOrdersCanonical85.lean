import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Compactness.Compact
import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualGenusTwoCanonicalSectionZeroOrderSumComplete
import Mathlib.Analysis.Complex.CauchyIntegral
open scoped Manifold ContDiff Bundle
open Bundle Filter Topology
set_option backward.isDefEq.respectTransparency false

private theorem coefficient_analytic {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (s : ActualCanonicalSection E) (q : E) :
    AnalyticAt ℂ
      (fun z => (ContinuousLinearMap.inCoordinates
        ℂ (fun x : E => TangentSpace 𝓘(ℂ) x) ℂ (Bundle.Trivial E ℂ)
        q ((chartAt ℂ q).symm z) q ((chartAt ℂ q).symm z)
        (s ((chartAt ℂ q).symm z))) (1 : ℂ))
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
  exact hd.analyticAt (hU.mem_nhds hqU)

private theorem coefficient_zero_iff_near {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q : E) :
    ∀ᶠ x in 𝓝 q,
      (ContinuousLinearMap.inCoordinates
        ℂ (fun x : E => TangentSpace 𝓘(ℂ) x) ℂ (Bundle.Trivial E ℂ)
        q x q x (s x)) (1 : ℂ) = 0 ↔ s x = 0 := by
  let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℂ) x) q
  have hq : q ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  filter_upwards [e.open_baseSet.mem_nhds hq] with x hbase
  let c := e.continuousLinearEquivAt ℂ x hbase
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]
  change s x (e.symmL ℂ x 1) = 0 ↔ s x = 0
  have hc : c.symm (1 : ℂ) = e.symmL ℂ x 1 := by
    exact congrFun (e.symm_continuousLinearEquivAt_eq (R := ℂ) hbase) 1
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    change s x v = 0
    have hv : v = (c v) • c.symm (1 : ℂ) := by
      apply c.injective
      rw [c.map_smul, c.apply_symm_apply]
      simp
    rw [hv, map_smul, hc, h, smul_zero]
  · intro h
    rw [h]
    rfl

private theorem literal_analytic_zero_germ {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (s : ActualCanonicalSection E) (q : E) :
    ∃ a : ℂ → ℂ, AnalyticAt ℂ a ((chartAt ℂ q) q) ∧
      ∀ᶠ x in 𝓝 q, a ((chartAt ℂ q) x) = 0 ↔ s x = 0 := by
  let a : ℂ → ℂ := fun z => (ContinuousLinearMap.inCoordinates
      ℂ (fun x : E => TangentSpace 𝓘(ℂ) x) ℂ (Bundle.Trivial E ℂ)
      q ((chartAt ℂ q).symm z) q ((chartAt ℂ q).symm z)
      (s ((chartAt ℂ q).symm z))) 1
  refine ⟨a, coefficient_analytic s q, ?_⟩
  filter_upwards [coefficient_zero_iff_near s q,
    (chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q)] with x hx hs
  dsimp only [a]
  rw [(chartAt ℂ q).left_inv hs]
  exact hx

private theorem zero_set_closed {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (s : ActualCanonicalSection E) :
    IsClosed {x : E | s x = 0} := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  change s q ≠ 0 at hq
  let V := fun x : E => TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial E ℂ x
  let e := trivializationAt (ℂ →L[ℂ] ℂ) V q
  let σ : E → TotalSpace (ℂ →L[ℂ] ℂ) V :=
    fun x => TotalSpace.mk' (ℂ →L[ℂ] ℂ) (E := V) x (s x)
  have hbase : q ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  have hc : ContinuousAt (fun x => (e (σ x)).2) q :=
    (contMDiffAt_totalSpace.mp (s.contMDiff q)).2.continuousAt
  have hn : (e (σ q)).2 ≠ 0 := by
    change (e (TotalSpace.mk' (ℂ →L[ℂ] ℂ) q (s q))).2 ≠ 0
    rw [e.apply_eq_prod_continuousLinearEquivAt ℂ q hbase (s q)]
    change e.continuousLinearEquivAt ℂ q hbase (s q) ≠ 0
    intro hz
    apply hq
    apply (e.continuousLinearEquivAt ℂ q hbase).injective
    rw [map_zero]
    exact hz
  have hnonzero : ∀ᶠ x in 𝓝 q, (e (σ x)).2 ≠ 0 :=
    hc.eventually (isOpen_compl_singleton.mem_nhds hn)
  filter_upwards [hnonzero, e.open_baseSet.mem_nhds hbase] with x hx hb
  change s x ≠ 0
  intro hz
  apply hx
  change (e (TotalSpace.mk' (ℂ →L[ℂ] ℂ) x (s x))).2 = 0
  rw [e.apply_eq_prod_continuousLinearEquivAt ℂ x hb (s x)]
  change e.continuousLinearEquivAt ℂ x hb (s x) = 0
  rw [hz]
  exact (e.continuousLinearEquivAt ℂ x hb).map_zero

private theorem actual_zero_germ_dichotomy {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] (s : ActualCanonicalSection E) (q : E) :
    (∀ᶠ x in 𝓝 q, s x = 0) ∨ ∀ᶠ x in 𝓝[≠] q, s x ≠ 0 := by
  obtain ⟨a, ha, hzero⟩ := literal_analytic_zero_germ s q
  let c := chartAt ℂ q
  have hq : q ∈ c.source := mem_chart_source ℂ q
  rcases ha.eventually_eq_zero_or_eventually_ne_zero with hz | hn
  · left
    filter_upwards [(c.continuousAt hq).tendsto.eventually hz, hzero] with x hx he
    exact he.mp hx
  · right
    have ht : Tendsto c (𝓝[≠] q) (𝓝[≠] (c q)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨(c.continuousAt hq).tendsto.mono_left nhdsWithin_le_nhds,
          c.eventually_ne_nhdsWithin hq⟩
    filter_upwards [ht.eventually hn, hzero.filter_mono nhdsWithin_le_nhds] with x hx he
    exact fun hz => hx (he.mpr hz)

private theorem nonzero_finite_support {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] [CompactSpace E] [ConnectedSpace E]
    (s : ActualCanonicalSection E) (hs : s ≠ 0) :
    {x : E | s x = 0}.Finite := by
  classical
  let Z : Set E := {x | s x = 0}
  let U : Set E := interior Z
  have hUcompl : IsOpen Uᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    have hqzero : ¬ ∀ᶠ x in 𝓝 q, s x = 0 := by
      intro h
      exact hq (mem_interior_iff_mem_nhds.mpr h)
    have hn := (actual_zero_germ_dichotomy s q).resolve_left hqzero
    have hnear := eventually_nhdsWithin_iff.mp hn
    filter_upwards [hnear] with x hx
    change x ∉ U
    by_cases hxq : x = q
    · subst x
      exact hq
    · intro hxU
      have hxZ : x ∈ Z := interior_subset hxU
      exact hx hxq hxZ
  have hUclosed : IsClosed U := isOpen_compl_iff.mp hUcompl
  have hUopen : IsOpen U := isOpen_interior
  have hUempty : U = ∅ := by
    rcases isClopen_iff.mp (show IsClopen U from ⟨hUclosed, hUopen⟩) with he | hu
    · exact he
    · exfalso
      apply hs
      apply ContMDiffSection.ext
      intro x
      have hx : x ∈ U := hu ▸ Set.mem_univ x
      have hxZ : x ∈ Z := interior_subset hx
      exact hxZ
  have hpunctured : ∀ q : E, ∀ᶠ x in 𝓝[≠] q, s x ≠ 0 := by
    intro q
    apply (actual_zero_germ_dichotomy s q).resolve_left
    intro h
    have hx : q ∈ U := mem_interior_iff_mem_nhds.mpr h
    rw [hUempty] at hx
    exact hx
  have hdiscrete : IsDiscrete Z := by
    apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
    intro q hq
    obtain ⟨V, hprop, hV, hqV⟩ := eventually_nhds_iff.mp
      (eventually_nhdsWithin_iff.mp (hpunctured q))
    refine ⟨V, hV, ?_⟩
    ext x
    constructor
    · intro hx
      by_contra hne
      exact hprop x hx.1 hne hx.2
    · intro hx
      have heq : x = q := hx
      subst x
      exact ⟨hqV, hq⟩
  exact (zero_set_closed s).isCompact.finite hdiscrete

theorem actual_canonical_section_finite_positive_zero_orders {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] [CompactSpace E] [ConnectedSpace E] [T1Space E]
    (s : ActualCanonicalSection E) (hs : s ≠ 0) (q : E) :
    analyticOrderAt (actualCanonicalLocalCoefficient s q) ((chartAt ℂ q) q) ≠ ⊤ ∧
      (s q = 0 → 0 < actualCanonicalZeroOrder s q) := by
  classical
  let c := chartAt ℂ q
  let a := actualCanonicalLocalCoefficient s q
  have hq : q ∈ c.source := mem_chart_source ℂ q
  have hcq : c q ∈ c.target := c.map_source hq
  have hfinite := nonzero_finite_support s hs
  have hqnot : q ∉ ({x : E | s x = 0} \ {q}) := by simp
  have havoid : ∀ᶠ x in 𝓝 q, x ∉ ({x : E | s x = 0} \ {q}) :=
    (hfinite.diff (t := {q})).isClosed.isOpen_compl.mem_nhds hqnot
  have hisolated : ∀ᶠ x in 𝓝[≠] q, s x ≠ 0 := by
    filter_upwards [havoid.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hne
    exact fun hz => hx ⟨hz, hne⟩
  have htfull : Tendsto c.symm (𝓝 (c q)) (𝓝 q) := by
    simpa only [c.left_inv hq] using (c.symm.continuousAt hcq).tendsto
  have htpunct : Tendsto c.symm (𝓝[≠] (c q)) (𝓝[≠] q) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨htfull.mono_left nhdsWithin_le_nhds, ?_⟩
    simpa only [c.left_inv hq, Set.mem_compl_iff, Set.mem_singleton_iff] using
      c.symm.eventually_ne_nhdsWithin hcq
  have hcoeffzero := htfull.eventually (coefficient_zero_iff_near s q)
  have hane : ∀ᶠ z in 𝓝[≠] (c q), a z ≠ 0 := by
    filter_upwards [htpunct.eventually hisolated,
      hcoeffzero.filter_mono nhdsWithin_le_nhds] with z hz he
    exact fun hzero => hz (he.mp hzero)
  have htop : analyticOrderAt a (c q) ≠ ⊤ := by
    intro h
    have hz := analyticOrderAt_eq_top.mp h
    obtain ⟨z, hzero, hne⟩ := ((hz.filter_mono nhdsWithin_le_nhds).and hane).exists
    exact hne hzero
  refine ⟨htop, ?_⟩
  intro hsq
  have ha : AnalyticAt ℂ a (c q) := coefficient_analytic s q
  have hcoeffq := (coefficient_zero_iff_near s q).self_of_nhds
  have haq : a (c q) = 0 := by
    dsimp only [a, actualCanonicalLocalCoefficient]
    rw [c.left_inv hq]
    exact hcoeffq.mpr hsq
  have hn : analyticOrderAt a (c q) ≠ 0 := ha.analyticOrderAt_ne_zero.mpr haq
  apply Nat.pos_of_ne_zero
  intro hnzero
  apply hn
  rw [← Nat.cast_analyticOrderNatAt htop]
  change (actualCanonicalZeroOrder s q : ℕ∞) = 0
  rw [hnzero]
  rfl
