import CurveComplexGenusTwo.Topology.ActualPointMittagLeffler.ActualChartTestFormExtensionV2
open TopologicalSpace SameAtlasAnalyticCohomology Filter
open scoped Manifold ContDiff Bundle Distributions Topology
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
namespace CanonicalDimensionTwo
universe u
theorem actualChartTestFormExtension_continuous
    {E : Type u} [TopologicalSpace E] [T2Space E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] (a : E) :
    Continuous (actualChartTestFormExtension a) := by
  classical
  have hcomp (K : Compacts ℂ) (n : ℕ) (T : ℂ → ℂ)
      (p : ContDiffMapSupportedIn ℂ ℂ ⊤ K × ℂ)
      (hT : ∀ᶠ z in 𝓝 p.2, ContDiffAt ℝ ∞ T z) :
      ContinuousAt (fun q : ContDiffMapSupportedIn ℂ ℂ ⊤ K × ℂ =>
        iteratedFDeriv ℝ n ((q.1 : ℂ → ℂ) ∘ T) q.2) p := by
    have hj (k : ℕ) : ContinuousAt
        (fun q : ContDiffMapSupportedIn ℂ ℂ ⊤ K × ℂ => iteratedFDeriv ℝ k q.1 (T q.2)) p := by
      have ht := (hT.self_of_nhds.continuousAt.comp continuousAt_snd)
      have hh := ((ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k).continuous.continuousAt.comp
        continuousAt_fst).eval ht
      simpa only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply] using! hh
    have hg (k : ℕ) : ContinuousAt
        (fun q : ContDiffMapSupportedIn ℂ ℂ ⊤ K × ℂ => iteratedFDeriv ℝ k T q.2) p :=
      (hT.self_of_nhds.continuousAt_iteratedFDeriv (by simp)).comp continuousAt_snd
    have hs : ContinuousAt (fun q : ContDiffMapSupportedIn ℂ ℂ ⊤ K × ℂ =>
        (ftaylorSeries ℝ q.1 (T q.2)).taylorComp (ftaylorSeries ℝ T q.2) n) p := by
      apply tendsto_finsetSum
      intro c hc
      change ContinuousAt (fun q => c.compAlongOrderedFinpartitionL ℝ ℂ ℂ ℂ
        (iteratedFDeriv ℝ c.length q.1 (T q.2))
        (fun i => iteratedFDeriv ℝ (c.partSize i) T q.2)) p
      exact ((c.compAlongOrderedFinpartitionL ℝ ℂ ℂ ℂ).continuous.continuousAt.comp
        (hj c.length)).eval (continuousAt_pi.mpr fun i => hg (c.partSize i))
    apply hs.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hT] with q hq
    exact iteratedFDeriv_comp q.1.contDiff.contDiffAt hq (by simp)
  have hmul (K : Compacts ℂ) (n : ℕ) (T B : ℂ → ℂ)
      (p : ContDiffMapSupportedIn ℂ ℂ ⊤ K × ℂ)
      (hT : ∀ᶠ z in 𝓝 p.2, ContDiffAt ℝ ∞ T z)
      (hB : ∀ᶠ z in 𝓝 p.2, ContDiffAt ℝ ∞ B z) :
      ContinuousAt (fun q : ContDiffMapSupportedIn ℂ ℂ ⊤ K × ℂ =>
        iteratedFDeriv ℝ n (fun w => q.1 (T w) * B w) q.2) p := by
    let H (q : ContDiffMapSupportedIn ℂ ℂ ⊤ K) (w : ℂ) : ℂ × ℂ := (q (T w), B w)
    have hv : ContinuousAt (fun q : ContDiffMapSupportedIn ℂ ℂ ⊤ K × ℂ => H q.1 q.2) p := by
      have ht := hT.self_of_nhds.continuousAt.comp continuousAt_snd
      have hh := ((ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ).continuous.continuousAt.comp
        continuousAt_fst).eval ht
      exact hh.prodMk (hB.self_of_nhds.continuousAt.comp continuousAt_snd)
    have hj (k : ℕ) : ContinuousAt
        (fun q : ContDiffMapSupportedIn ℂ ℂ ⊤ K × ℂ => iteratedFDeriv ℝ k (H q.1) q.2) p := by
      have hh := (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin k => ℂ) ℂ ℂ).continuous.continuousAt.comp
        ((hcomp K k T p hT).prodMk
          ((hB.self_of_nhds.continuousAt_iteratedFDeriv (by simp)).comp continuousAt_snd))
      apply hh.congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hT,
        continuous_snd.continuousAt.preimage_mem_nhds hB] with q hqT hqB
      exact iteratedFDeriv_prodMk (q.1.contDiff.contDiffAt.comp q.2 hqT) hqB (by simp)
    have hm : ContDiff ℝ ∞ (fun x : ℂ × ℂ => x.1 * x.2) := contDiff_fst.mul contDiff_snd
    have hs : ContinuousAt (fun q : ContDiffMapSupportedIn ℂ ℂ ⊤ K × ℂ =>
        (ftaylorSeries ℝ (fun x : ℂ × ℂ => x.1 * x.2) (H q.1 q.2)).taylorComp
          (ftaylorSeries ℝ (H q.1) q.2) n) p := by
      apply tendsto_finsetSum
      intro c hc
      change ContinuousAt (fun q => c.compAlongOrderedFinpartitionL ℝ ℂ (ℂ × ℂ) ℂ
        (iteratedFDeriv ℝ c.length (fun x : ℂ × ℂ => x.1 * x.2) (H q.1 q.2))
        (fun i => iteratedFDeriv ℝ (c.partSize i) (H q.1) q.2)) p
      exact ((c.compAlongOrderedFinpartitionL ℝ ℂ (ℂ × ℂ) ℂ).continuous.continuousAt.comp
        ((hm.continuous_iteratedFDeriv (by simp)).continuousAt.comp hv)).eval
          (continuousAt_pi.mpr fun i => hj (c.partSize i))
    apply hs.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hT,
      continuous_snd.continuousAt.preimage_mem_nhds hB] with q hqT hqB
    exact iteratedFDeriv_comp hm.contDiffAt
      ((q.1.contDiff.contDiffAt.comp q.2 hqT).prodMk hqB) (by simp)
  change @Continuous _ _ _ (TopologicalSpace.induced
    (fun f => fun b n => smoothZeroOneJet b n f) inferInstance) (actualChartTestFormExtension a)
  rw [continuous_induced_rng]
  apply continuous_pi
  intro b
  apply continuous_pi
  intro n
  let L : TestFunction (actualChartTestOpen a) ℂ ⊤ →ₗ[ℂ] C(ChartTarget b, RealJet n) :=
    { toFun := fun φ => smoothZeroOneJet b n (actualChartTestFormExtension a φ)
      map_add' := by
        intro φ ψ
        apply ContinuousMap.ext
        intro z
        change iteratedFDeriv ℝ n
          (fun w => (actualChartTestFormExtension a (φ + ψ)).1 b ((extChartAt 𝓘(ℂ) b).symm w)) z.1 = _
        rw [map_add]
        exact iteratedFDeriv_add_apply
          (((actualChartTestFormExtension a φ).property.2.1 b).contDiffAt
            ((isOpen_extChartAt_target b).mem_nhds z.property) |>.of_le (by simp))
          (((actualChartTestFormExtension a ψ).property.2.1 b).contDiffAt
            ((isOpen_extChartAt_target b).mem_nhds z.property) |>.of_le (by simp))
      map_smul' := by
        intro c φ
        apply ContinuousMap.ext
        intro z
        change iteratedFDeriv ℝ n
          (fun w => (actualChartTestFormExtension a (c • φ)).1 b ((extChartAt 𝓘(ℂ) b).symm w)) z.1 = _
        rw [map_smul]
        exact iteratedFDeriv_const_smul_apply (a := c)
          (((actualChartTestFormExtension a φ).property.2.1 b).contDiffAt
            ((isOpen_extChartAt_target b).mem_nhds z.property) |>.of_le (by simp)) }
  change Continuous L
  rw [TestFunction.continuous_iff_continuous_comp]
  intro K hK
  apply ContinuousMap.continuous_of_continuous_uncurry
  rw [continuous_iff_continuousAt]
  intro p
  let ca := extChartAt 𝓘(ℂ) a
  let cb := extChartAt 𝓘(ℂ) b
  let F (φ : ContDiffMapSupportedIn ℂ ℂ ⊤ K) : SmoothZeroOne E :=
    actualChartTestFormExtension a (TestFunction.ofSupportedIn hK φ)
  change ContinuousAt (fun q : ContDiffMapSupportedIn ℂ ℂ ⊤ K × ChartTarget b =>
    iteratedFDeriv ℝ n (fun w => (F q.1).1 b (cb.symm w)) q.2.1) p
  have hcoord (z : ℂ) (hz : z ∈ cb.target) (ha : cb.symm z ∈ ca.source) :
      ContDiffAt ℝ ∞ (ca ∘ cb.symm) z := by
    have ht := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) (n := ∞) a b
      (show z ∈ (cb.symm ≫ ca).source from ⟨hz, ha⟩)
    have ht' : ContDiffAt ℂ ∞ (ca ∘ cb.symm) z := by
      simpa [ca, cb, contDiffWithinAt_univ] using ht
    exact ht'.restrict_scalars ℝ
  let B : ℂ → ℂ := fun w => (star (chartTransitionDerivative a b (cb.symm w)))⁻¹
  have hfactor (z : ℂ) (hz : z ∈ cb.target) (ha : cb.symm z ∈ ca.source) :
      ContDiffAt ℝ ∞ B z := by
    have ht : ContDiffAt ℂ ∞ (ca ∘ cb.symm) z := by
      have ht := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) (n := ∞) a b
        (show z ∈ (cb.symm ≫ ca).source from ⟨hz, ha⟩)
      simpa [ca, cb, contDiffWithinAt_univ] using ht
    have hrev : ContDiffAt ℂ ∞ (cb ∘ ca.symm) (ca (cb.symm z)) := by
      have hb : cb.symm z ∈ cb.source := cb.map_target hz
      have hh : ca.symm (ca (cb.symm z)) ∈ cb.source := by
        simpa only [ca.left_inv ha] using hb
      have ht := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) (n := ∞) b a
        (show ca (cb.symm z) ∈ (ca.symm ≫ cb).source from ⟨ca.map_source ha, hh⟩)
      simpa [ca, cb, contDiffWithinAt_univ] using ht
    have hq : ContDiffAt ℂ ∞
        (fun w => chartTransitionDerivative a b (cb.symm w)) z := by
      have hd : ContDiffAt ℂ ∞ (fun w => (fderiv ℂ (cb ∘ ca.symm) w) (1 : ℂ))
          (ca (cb.symm z)) :=
        (hrev.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
      exact hd.comp z ht
    have hs : ContDiffAt ℝ ∞
        (fun w => star (chartTransitionDerivative a b (cb.symm w))) z :=
      Complex.conjCLE.contDiff.contDiffAt.comp z (hq.restrict_scalars ℝ)
    exact hs.fun_inv (star_ne_zero.mpr (chartTransitionDerivative_ne_zero a b _ ha (cb.map_target hz)))
  have hcoordinate_eq (φ : ContDiffMapSupportedIn ℂ ℂ ⊤ K)
      (z : ℂ) (hz : z ∈ cb.target) (ha : cb.symm z ∈ ca.source) :
      iteratedFDeriv ℝ n (fun w => (F φ).1 b (cb.symm w)) z =
        iteratedFDeriv ℝ n (fun w => φ (ca (cb.symm w)) * B w) z := by
    have he : (fun w => (F φ).1 b (cb.symm w)) =ᶠ[𝓝 z] (fun w => φ (ca (cb.symm w)) * B w) := by
      filter_upwards [(isOpen_extChartAt_target b).mem_nhds hz,
        (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ)) hz).preimage_mem_nhds
          (extChartAt_source_mem_nhds' ha)] with w hwt hw
      change (if cb.symm w ∈ ca.source ∧ cb.symm w ∈ cb.source
        then φ (ca (cb.symm w)) / star (chartTransitionDerivative a b (cb.symm w)) else 0) =
        φ (ca (cb.symm w)) * B w
      rw [ite_eq_left ⟨hw, cb.map_target hwt⟩]
      rfl
    exact (he.iteratedFDeriv ℝ n).self_of_nhds
  by_cases ha : cb.symm p.2.1 ∈ ca.source
  · have hn : ∀ᶠ z in 𝓝 p.2.1, z ∈ cb.target ∧ cb.symm z ∈ ca.source := by
      filter_upwards [(isOpen_extChartAt_target b).mem_nhds p.2.property,
        (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ)) p.2.property).preimage_mem_nhds
          (extChartAt_source_mem_nhds' ha)] with z hz hza
      exact ⟨hz, hza⟩
    have ht : ∀ᶠ z in 𝓝 p.2.1, ContDiffAt ℝ ∞ (ca ∘ cb.symm) z :=
      hn.mono fun z hz => hcoord z hz.1 hz.2
    have hB : ∀ᶠ z in 𝓝 p.2.1, ContDiffAt ℝ ∞ B z :=
      hn.mono fun z hz => hfactor z hz.1 hz.2
    have hj : ContinuousAt (fun q : ContDiffMapSupportedIn ℂ ℂ ⊤ K × ChartTarget b =>
        (q.1, q.2.1)) p :=
      continuousAt_fst.prodMk (continuous_subtype_val.continuousAt.comp continuousAt_snd)
    have hc := (hmul K n (ca ∘ cb.symm) B (p.1, p.2.1) ht hB).comp
      (f := fun q : ContDiffMapSupportedIn ℂ ℂ ⊤ K × ChartTarget b => (q.1, q.2.1)) hj
    apply hc.congr_of_eventuallyEq
    filter_upwards [(continuous_subtype_val.continuousAt.comp continuousAt_snd).preimage_mem_nhds hn]
      with q hq
    exact hcoordinate_eq q.1 q.2.1 hq.1 hq.2
  · have hcK : IsCompact (ca.symm '' (K : Set ℂ)) :=
      K.isCompact.image_of_continuousOn ((continuousOn_extChartAt_symm a).mono hK)
    have hk : cb.symm p.2.1 ∉ ca.symm '' (K : Set ℂ) := by
      rintro ⟨z, hz, he⟩
      apply ha
      rw [← he]
      exact ca.map_target (hK hz)
    have hn : ∀ᶠ z in 𝓝 p.2.1, cb.symm z ∉ ca.symm '' (K : Set ℂ) :=
      (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ)) p.2.property).preimage_mem_nhds
        (hcK.isClosed.isOpen_compl.mem_nhds hk)
    have hzero (φ : ContDiffMapSupportedIn ℂ ℂ ⊤ K) (z : ℂ)
        (hz : z ∈ cb.target) (hk : cb.symm z ∉ ca.symm '' (K : Set ℂ)) :
        iteratedFDeriv ℝ n (fun w => (F φ).1 b (cb.symm w)) z = 0 := by
      have he : (fun w => (F φ).1 b (cb.symm w)) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [(continuousAt_extChartAt_symm'' (I := 𝓘(ℂ)) hz).preimage_mem_nhds
          (hcK.isClosed.isOpen_compl.mem_nhds hk)] with w hw
        change (if cb.symm w ∈ ca.source ∧ cb.symm w ∈ cb.source
          then φ (ca (cb.symm w)) / star (chartTransitionDerivative a b (cb.symm w)) else 0) = 0
        split_ifs with hs
        · have hφ : φ (ca (cb.symm w)) = 0 := by
            apply φ.zero_on_compl
            intro hv
            exact hw ⟨ca (cb.symm w), hv, ca.left_inv hs.1⟩
          rw [hφ, zero_div]
        · rfl
      rw [(he.iteratedFDeriv ℝ n).self_of_nhds]
      simp
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [(continuous_subtype_val.continuousAt.comp continuousAt_snd).preimage_mem_nhds hn]
      with q hq
    exact hzero q.1 q.2.1 q.2.property hq


end CanonicalDimensionTwo
