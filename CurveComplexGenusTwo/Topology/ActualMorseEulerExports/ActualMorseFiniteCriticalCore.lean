import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseCoreParameterStability
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.DiscreteSubset

open Set Filter Topology

theorem actual_compact_regular_zero_set_finite
    (g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hg : ContDiffOn ℝ 1 g U)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (hregular : ∀ x ∈ K, g x = 0 → (fderiv ℝ g x).det ≠ 0) :
    {x : ℂ | x ∈ K ∧ g x = 0}.Finite := by
  let Z : Set ℂ := {x | x ∈ K ∧ g x = 0}
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hgK : Continuous (fun x : K => g x.val) :=
    continuousOn_iff_continuous_domRestrict.mp (hg.continuousOn.mono hKU)
  have hZcompact : IsCompact Z := by
    have hclosed : IsClosed {x : K | g x.val = 0} :=
      isClosed_eq hgK continuous_const
    have hcompact : IsCompact {x : K | g x.val = 0} := hclosed.isCompact
    have himage : IsCompact ((Subtype.val : K → ℂ) '' {x : K | g x.val = 0}) :=
      hcompact.image continuous_subtype_val
    convert himage using 1
    ext x
    simp [Z, and_comm]
  have hdisc : DiscreteTopology Z := by
    apply discreteTopology_subtype_iff'.mpr
    intro x hx
    have hxK : x ∈ K := hx.1
    have hxU : x ∈ U := hKU hxK
    have hdet := hregular x hxK hx.2
    let D := (fderiv ℝ g x).toContinuousLinearEquivOfDetNeZero hdet
    have hD : HasFDerivAt g D.toContinuousLinearMap x := by
      convert (((hg x hxU).contDiffAt (hU.mem_nhds hxU)).differentiableAt
        (by norm_num)).hasFDerivAt using 1
      exact (fderiv ℝ g x).coe_toContinuousLinearEquivOfDetNeZero hdet |>.symm
    have hs : HasStrictFDerivAt g D.toContinuousLinearMap x :=
      ((hg x hxU).contDiffAt (hU.mem_nhds hxU)).hasStrictFDerivAt'
        hD (by norm_num)
    let e := hs.toOpenPartialHomeomorph g
    refine ⟨e.source, e.open_source, ?_⟩
    ext y
    constructor
    · intro hy
      have hyx : y = x := by
        apply e.injOn hy.1 hs.mem_toOpenPartialHomeomorph_source
        change g y = g x
        rw [hy.2.2, hx.2]
      exact hyx
    · intro hy
      subst y
      exact ⟨hs.mem_toOpenPartialHomeomorph_source, hx⟩
  letI : CompactSpace Z := isCompact_iff_compactSpace.mp hZcompact
  letI : DiscreteTopology Z := hdisc
  exact finite_coe_iff.mpr finite_of_compact_of_discrete

