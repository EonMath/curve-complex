import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.VectorBundle.Basic

open scoped Manifold ContDiff Bundle Topology
open Bundle Set

private theorem actual_literal_nondegenerate_zero_is_isolated
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x) (q : E)
    (hq : V q = 0)
    (D : ℂ ≃L[ℝ] ℂ)
    (hC1 : ContDiffAt ℝ 1
      (fun w : ℂ =>
        let x := (chartAt ℂ q).symm ((chartAt ℂ q) q + w)
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
          (TotalSpace.mk' ℂ x (V x))).2) 0)
    (hD : HasFDerivAt
      (fun w : ℂ =>
        let x := (chartAt ℂ q).symm ((chartAt ℂ q) q + w)
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
          (TotalSpace.mk' ℂ x (V x))).2)
      D.toContinuousLinearMap 0) :
    ∃ U : Set E, IsOpen U ∧ q ∈ U ∧ ∀ y ∈ U, V y = 0 → y = q := by
  let c := chartAt ℂ q
  let t := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  let g : ℂ → ℂ := fun w =>
    (t (TotalSpace.mk' ℂ (c.symm (c q + w)) (V (c.symm (c q + w))))).2
  have hg0 : g 0 = 0 := by
    have hbase : q ∈ t.baseSet := mem_baseSet_trivializationAt ℂ _ q
    change (t ⟨c.symm (c q + 0), V (c.symm (c q + 0))⟩).2 = 0
    have hbasec : c.symm (c q) = q := c.left_inv (mem_chart_source ℂ q)
    rw [add_zero, hbasec, hq]
    rw [← t.continuousLinearMapAt_apply_of_mem (R := ℝ) hbase]
    simp
  have hs : HasStrictFDerivAt g D.toContinuousLinearMap 0 :=
    hC1.hasStrictFDerivAt' hD (by norm_num)
  let e := hs.toOpenPartialHomeomorph g
  let T : Set ℂ := {z | z - c q ∈ e.source}
  have hT : IsOpen T := e.open_source.preimage (continuous_id.sub continuous_const)
  let U : Set E := c.source ∩ c ⁻¹' T
  have hU : IsOpen U := c.isOpen_inter_preimage hT
  have hqU : q ∈ U := by
    constructor
    · exact mem_chart_source ℂ q
    · change c q - c q ∈ e.source
      simpa using hs.mem_toOpenPartialHomeomorph_source
  refine ⟨U, hU, hqU, ?_⟩
  intro y hy hy0
  have hyc : y ∈ c.source := hy.1
  let w : ℂ := c y - c q
  have hw : w ∈ e.source := hy.2
  have hcw : c q + w = c y := by simp [w]
  have hgw : g w = 0 := by
    have hbase : y ∈ t.baseSet := by simpa [t] using hyc
    change (t ⟨c.symm (c q + w), V (c.symm (c q + w))⟩).2 = 0
    rw [hcw, c.left_inv hyc, hy0]
    rw [← t.continuousLinearMapAt_apply_of_mem (R := ℝ) hbase]
    simp
  have hw0 : w = 0 := by
    apply e.injOn hw hs.mem_toOpenPartialHomeomorph_source
    change g w = g 0
    rw [hgw, hg0]
  have hcy : c y = c q := sub_eq_zero.mp hw0
  exact c.injOn hyc (mem_chart_source ℂ q) hcy

#print axioms actual_literal_nondegenerate_zero_is_isolated

theorem actual_literal_nondegenerate_tangent_zeros_finite
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [T2Space E] [CompactSpace E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hV : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (V x)))
    (hC1 : ∀ q : E, V q = 0 → ContDiffAt ℝ 1
      (fun w : ℂ =>
        let x := (chartAt ℂ q).symm ((chartAt ℂ q) q + w)
        (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
          (TotalSpace.mk' ℂ x (V x))).2) 0)
    (hD : ∀ q : E, V q = 0 → ∃ D : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt
        (fun w : ℂ =>
          let x := (chartAt ℂ q).symm ((chartAt ℂ q) q + w)
          (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
            (TotalSpace.mk' ℂ x (V x))).2)
        D.toContinuousLinearMap 0) :
    ∃ Z : Finset E, (Z : Set E) = {x | V x = 0} := by
  classical
  let Z : Set E := {x | V x = 0}
  have hclosed : IsClosed Z := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    let t := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) x
    let b : E → ℂ := fun y => (t (TotalSpace.mk' ℂ y (V y))).2
    have hbase : x ∈ t.baseSet := mem_baseSet_trivializationAt ℂ _ x
    have hbOn : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ b t.baseSet :=
      (t.contMDiffOn_section_baseSet_iff).mp hV.contMDiffOn
    have hbcont : ContinuousAt b x :=
      ((hbOn x hbase).contMDiffAt (t.open_baseSet.mem_nhds hbase)).continuousAt
    have hbnonzero : b x ≠ 0 := by
      intro hbzero
      have hmap : t.continuousLinearMapAt ℝ x (V x) = 0 := by
        rw [t.continuousLinearMapAt_apply_of_mem (R := ℝ) hbase]
        exact hbzero
      have hinv := congrArg (t.symmL ℝ x) hmap
      rw [t.symmL_continuousLinearMapAt hbase, map_zero] at hinv
      exact hx hinv
    have hne : ∀ᶠ y in 𝓝 x, b y ≠ 0 :=
      hbcont.tendsto.eventually (isOpen_compl_singleton.mem_nhds hbnonzero)
    have hs : ∀ᶠ y in 𝓝 x, y ∈ t.baseSet :=
      t.open_baseSet.mem_nhds hbase
    filter_upwards [hne, hs] with y hyb hybase hyzero
    have hby : b y = 0 := by
      change (t (TotalSpace.mk' ℂ y (V y))).2 = 0
      change V y = 0 at hyzero
      rw [← t.continuousLinearMapAt_apply_of_mem (R := ℝ) hybase, hyzero, map_zero]
    exact hyb hby
  letI : CompactSpace Z := isCompact_iff_compactSpace.mp hclosed.isCompact
  have hdisc : DiscreteTopology Z := by
    apply discreteTopology_subtype_iff'.mpr
    intro q hq
    obtain ⟨D, hDeriv⟩ := hD q hq
    obtain ⟨U, hU, hqU, huniq⟩ :=
      actual_literal_nondegenerate_zero_is_isolated V q hq D (hC1 q hq) hDeriv
    refine ⟨U, hU, ?_⟩
    ext y
    constructor
    · intro hy
      exact huniq y hy.1 hy.2
    · intro hy
      subst y
      exact ⟨hqU, hq⟩
  have hfin : Z.Finite := finite_coe_iff.mpr finite_of_compact_of_discrete
  exact ⟨hfin.toFinset, hfin.coe_toFinset⟩

#print axioms actual_literal_nondegenerate_tangent_zeros_finite
