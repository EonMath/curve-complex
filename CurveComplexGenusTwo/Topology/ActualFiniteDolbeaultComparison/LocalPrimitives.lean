import CurveComplexGenusTwo.Topology.ActualFiniteDolbeaultComparison.PartitionDependencies
import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.ActualDbarHolomorphicKernel
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
open TopologicalSpace SameAtlasRRLocal Filter Topology
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
open scoped Manifold ContDiff Bundle
attribute [local instance] Classical.propDecidable
namespace SameAtlasAnalyticCohomology
universe u v
variable {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]
variable (U : OpenCover.{u,v} E) [Fintype U.Index]

/-- The literal weighted local partition primitive, extended by zero off U_i.
Its smoothness is asserted only at points in U_i. -/
noncomputable def localPartitionPrimitive (P : SubordinateSmoothPartition U)
    (g : oneCocycles U) (i : U.Index) (x : E) : ℂ := by
  classical
  exact if hxi : x ∈ U.opens i then
    ∑ j, if hxj : x ∈ U.opens j then
      (P.weight j x : ℂ) * (g.1 i j).1 ⟨x, ⟨hxi, hxj⟩⟩ else 0
    else 0

theorem localPartitionPrimitive_overlap (P : SubordinateSmoothPartition U)
    (g : oneCocycles U) (i k : U.Index) (x : E)
    (hxi : x ∈ U.opens i) (hxk : x ∈ U.opens k) :
    localPartitionPrimitive U P g i x - localPartitionPrimitive U P g k x =
      (g.1 i k).1 ⟨x, ⟨hxi, hxk⟩⟩ := by
  unfold localPartitionPrimitive
  simp only [dite_eq_left hxi, dite_eq_left hxk]
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ j, (P.weight j x : ℂ) * (g.1 i k).1 ⟨x, ⟨hxi, hxk⟩⟩ := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hxj : x ∈ U.opens j
      · simp only [dite_eq_left hxj]
        have hc := congrArg (fun f => f.1 ⟨x, ⟨⟨hxi, hxk⟩, hxj⟩⟩)
          (g.property i k j)
        simp only [HolOn.restrict, LinearMap.coe_mk, AddHom.coe_mk,
          Submodule.coe_sub, Pi.sub_apply, Submodule.coe_add, Pi.add_apply,
          Submodule.coe_zero, Pi.zero_apply] at hc
        linear_combination -(P.weight j x : ℂ) * hc
      · have hw : P.weight j x = 0 := by
          apply Function.notMem_support.1
          intro hx
          exact hxj (P.supportWeight j (subset_closure hx))
        simp only [dite_eq_right hxj, hw, Complex.ofReal_zero, zero_mul, sub_zero]
    _ = _ := by
      rw [← Finset.sum_mul]
      have hs : (∑ j, (P.weight j x : ℂ)) = 1 := by
        exact_mod_cast P.partitionOne x
      rw [hs, one_mul]

theorem localPartitionPrimitive_contDiffAt (P : SubordinateSmoothPartition U)
    (g : oneCocycles U) (i : U.Index) (a x : E)
    (hxi : x ∈ U.opens i) (hxa : x ∈ (extChartAt 𝓘(ℂ) a).source) :
    ContDiffAt ℝ ∞
      (fun z : ℂ => localPartitionPrimitive U P g i ((extChartAt 𝓘(ℂ) a).symm z))
      ((extChartAt 𝓘(ℂ) a) x) := by
  unfold localPartitionPrimitive
  have hhol (U : Opens E) (f : HolOn U) (a x : E) (hx : x ∈ U)
      (hxa : x ∈ (extChartAt 𝓘(ℂ) a).source) :
      ContDiffAt ℂ ∞ (fun z : ℂ =>
        if hy : (extChartAt 𝓘(ℂ) a).symm z ∈ U then
          f.1 ⟨(extChartAt 𝓘(ℂ) a).symm z, hy⟩ else 0)
        ((extChartAt 𝓘(ℂ) a) x) := by
    obtain ⟨h, ha, hh⟩ := f.property ⟨x, hx⟩
    have hc : ContDiffAt ℂ ∞
        (extChartAt 𝓘(ℂ) x ∘ (extChartAt 𝓘(ℂ) a).symm)
        ((extChartAt 𝓘(ℂ) a) x) := by
      have hm : (extChartAt 𝓘(ℂ) a) x ∈
          ((extChartAt 𝓘(ℂ) a).symm ≫ extChartAt 𝓘(ℂ) x).source := by
        exact ⟨(extChartAt 𝓘(ℂ) a).map_source hxa,
          by
            change (extChartAt 𝓘(ℂ) a).symm ((extChartAt 𝓘(ℂ) a) x) ∈
              (extChartAt 𝓘(ℂ) x).source
            rw [(extChartAt 𝓘(ℂ) a).left_inv hxa]
            exact mem_extChartAt_source x⟩
      simpa only [modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ] using
        contDiffWithinAt_ext_coord_change x a hm
    have ha' : ContDiffAt ℂ ∞ h
        ((extChartAt 𝓘(ℂ) x ∘ (extChartAt 𝓘(ℂ) a).symm)
          ((extChartAt 𝓘(ℂ) a) x)) := by
      rw [Function.comp_apply, (extChartAt 𝓘(ℂ) a).left_inv hxa]
      simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply, id_eq] using
        (ha.contDiffAt : ContDiffAt ℂ ∞ h ((chartAt ℂ x) x))
    apply (ha'.comp _ hc).congr_of_eventuallyEq
    have htend : Tendsto (extChartAt 𝓘(ℂ) a).symm
        (𝓝 ((extChartAt 𝓘(ℂ) a) x)) (𝓝 x) := by
      simpa only [(extChartAt 𝓘(ℂ) a).left_inv hxa] using
        (continuousAt_extChartAt_symm' hxa).tendsto
    have hU := htend.eventually (U.isOpen.mem_nhds hx)
    have hh' := htend.eventually hh
    filter_upwards [hU, hh'] with z hz hhz
    split
    · next hzz =>
        simpa only [Function.comp_apply, extChartAt_coe, modelWithCornersSelf_coe, id_eq] using hhz hzz
    · next hzz => exact False.elim (hzz hz)
  have htend : Tendsto (extChartAt 𝓘(ℂ) a).symm
      (𝓝 ((extChartAt 𝓘(ℂ) a) x)) (𝓝 x) := by
    simpa only [(extChartAt 𝓘(ℂ) a).left_inv hxa] using
      (continuousAt_extChartAt_symm' hxa).tendsto
  have hUi := htend.eventually ((U.opens i).isOpen.mem_nhds hxi)
  let F (j : U.Index) (z : ℂ) : ℂ :=
    (P.weight j ((extChartAt 𝓘(ℂ) a).symm z) : ℂ) *
      (if hz : (extChartAt 𝓘(ℂ) a).symm z ∈ U.opens i ⊓ U.opens j then
        (g.1 i j).1 ⟨(extChartAt 𝓘(ℂ) a).symm z, hz⟩ else 0)
  have hj : ∀ j, ContDiffAt ℝ ∞ (F j) ((extChartAt 𝓘(ℂ) a) x) := by
    intro j
    by_cases hxj : x ∈ U.opens j
    · have hw := (P.smoothWeight j a).contDiffAt
        (extChartAt_target_mem_nhds' ((extChartAt 𝓘(ℂ) a).map_source hxa))
      have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp
        ((extChartAt 𝓘(ℂ) a) x) hw
      exact hc.mul ((hhol (U.opens i ⊓ U.opens j) (g.1 i j) a x ⟨hxi,hxj⟩ hxa).restrict_scalars ℝ)
    · have hs : x ∉ tsupport (P.weight j) := fun h => hxj (P.supportWeight j h)
      have he : P.weight j =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hs
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [htend.eventually he] with z hz
      change P.weight j ((extChartAt 𝓘(ℂ) a).symm z) = 0 at hz
      simp only [F, hz, Complex.ofReal_zero, zero_mul]
  apply (ContDiffAt.sum (s := Finset.univ) (fun j _ => hj j)).congr_of_eventuallyEq
  filter_upwards [hUi] with z hz
  split
  · next hzi =>
      apply Finset.sum_congr rfl
      intro j hj
      split
      · next hzj =>
          split
          · rfl
          · next hzij => exact False.elim (hzij ⟨hzi,hzj⟩)
      · next hzj =>
          split
          · next hzij => exact False.elim (hzj hzij.2)
          · exact (mul_zero _).symm
  · next hzi => exact False.elim (hzi hz)

theorem localPartitionPrimitive_chartDbar (P : SubordinateSmoothPartition U)
    (g : oneCocycles U) (i : U.Index) (a x : E)
    (hxi : x ∈ U.opens i) (hxa : x ∈ (extChartAt 𝓘(ℂ) a).source) :
    chartDbar a (localPartitionPrimitive U P g i) x =
      chartCechDbarCoefficient U a P.weight g i x hxi := by
  have hhol (U : Opens E) (f : HolOn U) (a x : E) (hx : x ∈ U)
      (hxa : x ∈ (extChartAt 𝓘(ℂ) a).source) :
      ContDiffAt ℂ ∞ (fun z : ℂ =>
        if hy : (extChartAt 𝓘(ℂ) a).symm z ∈ U then
          f.1 ⟨(extChartAt 𝓘(ℂ) a).symm z, hy⟩ else 0)
        ((extChartAt 𝓘(ℂ) a) x) := by
    obtain ⟨h, ha, hh⟩ := f.property ⟨x, hx⟩
    have hc : ContDiffAt ℂ ∞
        (extChartAt 𝓘(ℂ) x ∘ (extChartAt 𝓘(ℂ) a).symm)
        ((extChartAt 𝓘(ℂ) a) x) := by
      have hm : (extChartAt 𝓘(ℂ) a) x ∈
          ((extChartAt 𝓘(ℂ) a).symm ≫ extChartAt 𝓘(ℂ) x).source := by
        exact ⟨(extChartAt 𝓘(ℂ) a).map_source hxa,
          by
            change (extChartAt 𝓘(ℂ) a).symm ((extChartAt 𝓘(ℂ) a) x) ∈
              (extChartAt 𝓘(ℂ) x).source
            rw [(extChartAt 𝓘(ℂ) a).left_inv hxa]
            exact mem_extChartAt_source x⟩
      simpa only [modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ] using
        contDiffWithinAt_ext_coord_change x a hm
    have ha' : ContDiffAt ℂ ∞ h
        ((extChartAt 𝓘(ℂ) x ∘ (extChartAt 𝓘(ℂ) a).symm)
          ((extChartAt 𝓘(ℂ) a) x)) := by
      rw [Function.comp_apply, (extChartAt 𝓘(ℂ) a).left_inv hxa]
      simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply, id_eq] using
        (ha.contDiffAt : ContDiffAt ℂ ∞ h ((chartAt ℂ x) x))
    apply (ha'.comp _ hc).congr_of_eventuallyEq
    have htend : Tendsto (extChartAt 𝓘(ℂ) a).symm
        (𝓝 ((extChartAt 𝓘(ℂ) a) x)) (𝓝 x) := by
      simpa only [(extChartAt 𝓘(ℂ) a).left_inv hxa] using
        (continuousAt_extChartAt_symm' hxa).tendsto
    have hU := htend.eventually (U.isOpen.mem_nhds hx)
    have hh' := htend.eventually hh
    filter_upwards [hU, hh'] with z hz hhz
    split
    · next hzz =>
        simpa only [Function.comp_apply, extChartAt_coe, modelWithCornersSelf_coe, id_eq] using hhz hzz
    · next hzz => exact False.elim (hzz hz)
  have hprod (r f : ℂ → ℂ) (z : ℂ)
      (hr : DifferentiableAt ℝ r z) (hf : DifferentiableAt ℂ f z) :
      CanonicalDimensionTwo.LocalDbar.dbar (fun w => r w * f w) z =
        f z * CanonicalDimensionTwo.LocalDbar.dbar r z := by
    have hfr : DifferentiableAt ℝ f z := hf.restrictScalars ℝ
    have hz := (CanonicalDimensionTwo.actualDbar_zero_iff_complex_differentiableAt hfr).mpr hf
    have hz' : fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I = 0 := by
      simpa only [CanonicalDimensionTwo.LocalDbar.dbar, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] using hz
    unfold CanonicalDimensionTwo.LocalDbar.dbar
    rw [fderiv_fun_mul hr hfr]
    simp only [add_apply, smul_apply, smul_eq_mul]
    calc
      _ = f z * ((fderiv ℝ r z 1 + Complex.I * fderiv ℝ r z Complex.I) / 2) +
          r z * ((fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2) := by ring
      _ = _ := by rw [hz']; ring
  let z₀ : ℂ := (extChartAt 𝓘(ℂ) a) x
  let R (j : U.Index) (z : ℂ) : ℂ := (P.weight j ((extChartAt 𝓘(ℂ) a).symm z) : ℂ)
  let H (j : U.Index) (z : ℂ) : ℂ :=
    if hz : (extChartAt 𝓘(ℂ) a).symm z ∈ U.opens i ⊓ U.opens j then
      (g.1 i j).1 ⟨(extChartAt 𝓘(ℂ) a).symm z, hz⟩ else 0
  let F (j : U.Index) (z : ℂ) : ℂ := R j z * H j z
  have htend : Tendsto (extChartAt 𝓘(ℂ) a).symm (𝓝 z₀) (𝓝 x) := by
    simpa only [(extChartAt 𝓘(ℂ) a).left_inv hxa] using
      (continuousAt_extChartAt_symm' hxa).tendsto
  have hUi := htend.eventually ((U.opens i).isOpen.mem_nhds hxi)
  have heq : (fun z : ℂ => localPartitionPrimitive U P g i ((extChartAt 𝓘(ℂ) a).symm z))
      =ᶠ[𝓝 z₀] (fun z => ∑ j, F j z) := by
    filter_upwards [hUi] with z hz
    unfold localPartitionPrimitive
    split
    · next hzi =>
        apply Finset.sum_congr rfl
        intro j hj
        dsimp only [F, R, H]
        split
        · next hzj =>
            split
            · rfl
            · next hzij => exact False.elim (hzij ⟨hzi,hzj⟩)
        · next hzj =>
            split
            · next hzij => exact False.elim (hzj hzij.2)
            · exact (mul_zero _).symm
    · next hzi => exact False.elim (hzi hz)
  have hR (j : U.Index) : DifferentiableAt ℝ (R j) z₀ := by
    have hw := (P.smoothWeight j a).contDiffAt
      (extChartAt_target_mem_nhds' ((extChartAt 𝓘(ℂ) a).map_source hxa))
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z₀ hw).differentiableAt (by simp)
  have hF0 (j : U.Index) (hxj : x ∉ U.opens j) : F j =ᶠ[𝓝 z₀] 0 := by
    have hs : x ∉ tsupport (P.weight j) := fun h => hxj (P.supportWeight j h)
    have he : P.weight j =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hs
    filter_upwards [htend.eventually he] with z hz
    change P.weight j ((extChartAt 𝓘(ℂ) a).symm z) = 0 at hz
    simp only [F, R, hz, Complex.ofReal_zero, zero_mul, Pi.zero_apply]
  have hF (j : U.Index) : DifferentiableAt ℝ (F j) z₀ := by
    by_cases hxj : x ∈ U.opens j
    · exact (hR j).mul (((hhol (U.opens i ⊓ U.opens j) (g.1 i j) a x
        ⟨hxi,hxj⟩ hxa).restrict_scalars ℝ).differentiableAt (by simp))
    · exact (differentiableAt_const (c := (0 : ℂ))).congr_of_eventuallyEq (hF0 j hxj)
  have hterm (j : U.Index) : CanonicalDimensionTwo.LocalDbar.dbar (F j) z₀ =
      (if hxj : x ∈ U.opens j then
        (g.1 i j).1 ⟨x, ⟨hxi,hxj⟩⟩ * chartDbarWeight a (P.weight j) x else 0) := by
    by_cases hxj : x ∈ U.opens j
    · have hH : DifferentiableAt ℂ (H j) z₀ :=
        (hhol (U.opens i ⊓ U.opens j) (g.1 i j) a x ⟨hxi,hxj⟩ hxa).differentiableAt (by simp)
      have hp := hprod (R j) (H j) z₀ (hR j) hH
      have hvalue : H j z₀ = (g.1 i j).1 ⟨x, ⟨hxi,hxj⟩⟩ := by
        simp only [H, z₀, (extChartAt 𝓘(ℂ) a).left_inv hxa,
          dite_eq_left (show x ∈ U.opens i ⊓ U.opens j from ⟨hxi,hxj⟩)]
      rw [hvalue] at hp
      simpa only [F, R, z₀, chartDbarWeight, chartDbar,
        CanonicalDimensionTwo.LocalDbar.dbar, dite_eq_left hxj] using hp
    · rw [dite_eq_right hxj]
      unfold CanonicalDimensionTwo.LocalDbar.dbar
      rw [(hF0 j hxj).fderiv_eq]
      simp
  unfold chartDbar chartCechDbarCoefficient
  change ((fderiv ℝ
      (fun z : ℂ => localPartitionPrimitive U P g i ((extChartAt 𝓘(ℂ) a).symm z)) z₀) 1 +
      Complex.I * (fderiv ℝ
      (fun z : ℂ => localPartitionPrimitive U P g i ((extChartAt 𝓘(ℂ) a).symm z)) z₀) Complex.I) / 2 = _
  rw [heq.fderiv_eq, fderiv_fun_sum (fun j _ => hF j)]
  simp only [sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl (fun j _ => hterm j)


/-- A literal HolOn section extended by zero is complex-smooth near every
point in its open domain, in every supplied preferred chart. -/
theorem holOn_chartExtension_contDiffAt (W : Opens E) (f : HolOn W)
    (a x : E) (hx : x ∈ W) (hxa : x ∈ (extChartAt 𝓘(ℂ) a).source) :
    ContDiffAt ℂ ∞ (fun z : ℂ =>
      if hy : (extChartAt 𝓘(ℂ) a).symm z ∈ W then
        f.1 ⟨(extChartAt 𝓘(ℂ) a).symm z, hy⟩ else 0)
      ((extChartAt 𝓘(ℂ) a) x) := by
  obtain ⟨h, ha, hh⟩ := f.property ⟨x, hx⟩
  have hc : ContDiffAt ℂ ∞
      (extChartAt 𝓘(ℂ) x ∘ (extChartAt 𝓘(ℂ) a).symm)
      ((extChartAt 𝓘(ℂ) a) x) := by
    have hm : (extChartAt 𝓘(ℂ) a) x ∈
        ((extChartAt 𝓘(ℂ) a).symm ≫ extChartAt 𝓘(ℂ) x).source := by
      exact ⟨(extChartAt 𝓘(ℂ) a).map_source hxa,
        by
          change (extChartAt 𝓘(ℂ) a).symm ((extChartAt 𝓘(ℂ) a) x) ∈
            (extChartAt 𝓘(ℂ) x).source
          rw [(extChartAt 𝓘(ℂ) a).left_inv hxa]
          exact mem_extChartAt_source x⟩
    simpa only [modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ] using
      contDiffWithinAt_ext_coord_change x a hm
  have ha' : ContDiffAt ℂ ∞ h
      ((extChartAt 𝓘(ℂ) x ∘ (extChartAt 𝓘(ℂ) a).symm)
        ((extChartAt 𝓘(ℂ) a) x)) := by
    rw [Function.comp_apply, (extChartAt 𝓘(ℂ) a).left_inv hxa]
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply, id_eq] using
      (ha.contDiffAt : ContDiffAt ℂ ∞ h ((chartAt ℂ x) x))
  apply (ha'.comp _ hc).congr_of_eventuallyEq
  have htend : Tendsto (extChartAt 𝓘(ℂ) a).symm
      (𝓝 ((extChartAt 𝓘(ℂ) a) x)) (𝓝 x) := by
    simpa only [(extChartAt 𝓘(ℂ) a).left_inv hxa] using
      (continuousAt_extChartAt_symm' hxa).tendsto
  have hU := htend.eventually (W.isOpen.mem_nhds hx)
  have hh' := htend.eventually hh
  filter_upwards [hU, hh'] with z hz hhz
  split
  · next hzz =>
      simpa only [Function.comp_apply, extChartAt_coe, modelWithCornersSelf_coe, id_eq] using hhz hzz
  · next hzz => exact False.elim (hzz hz)

theorem chartDbarWeight_of_notMem (P : SubordinateSmoothPartition U)
    (j : U.Index) (a x : E) (hxa : x ∈ (extChartAt 𝓘(ℂ) a).source)
    (hxj : x ∉ U.opens j) : chartDbarWeight a (P.weight j) x = 0 := by
  have hs : x ∉ tsupport (P.weight j) := fun h => hxj (P.supportWeight j h)
  have he : P.weight j =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hs
  have htend : Tendsto (extChartAt 𝓘(ℂ) a).symm
      (𝓝 ((extChartAt 𝓘(ℂ) a) x)) (𝓝 x) := by
    simpa only [(extChartAt 𝓘(ℂ) a).left_inv hxa] using
      (continuousAt_extChartAt_symm' hxa).tendsto
  have hc := htend.eventually he
  have ht : (fun z : ℂ => (P.weight j ((extChartAt 𝓘(ℂ) a).symm z) : ℂ)) =ᶠ[
      𝓝 ((extChartAt 𝓘(ℂ) a) x)] 0 := by
    filter_upwards [hc] with z hz
    change (P.weight j ((extChartAt 𝓘(ℂ) a).symm z) : ℂ) = 0
    change P.weight j ((extChartAt 𝓘(ℂ) a).symm z) = 0 at hz
    rw [hz, Complex.ofReal_zero]
  unfold chartDbarWeight chartDbar
  dsimp only
  rw [ht.fderiv_eq]
  simp

/-- The actual chartwise smooth kernel on an arbitrary open domain. -/
theorem localSmooth_zero_chartDbar_isHolOn
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] (W : Opens E) (f : E → ℂ)
    (hs : ∀ (a x : E), x ∈ W → x ∈ (extChartAt 𝓘(ℂ) a).source →
      ContDiffAt ℝ ∞ (fun z : ℂ => f ((extChartAt 𝓘(ℂ) a).symm z))
        ((extChartAt 𝓘(ℂ) a) x))
    (hz : ∀ (a x : E), x ∈ W → x ∈ (extChartAt 𝓘(ℂ) a).source →
      chartDbar a f x = 0) : IsHolOn W (fun x => f x) := by
  apply CanonicalDimensionTwo.actualHolOn_of_chart_smooth_dbar_zero
  · intro x
    let a : E := x
    let V : Set ℂ := (chartAt ℂ a).target ∩ (chartAt ℂ a).symm ⁻¹' (W : Set E)
    have hV : IsOpen V := (chartAt ℂ a).isOpen_inter_preimage_symm W.isOpen
    have hxV : (chartAt ℂ a) a ∈ V := by
      refine ⟨(chartAt ℂ a).map_source (mem_chart_source ℂ a), ?_⟩
      change (chartAt ℂ a).symm ((chartAt ℂ a) a) ∈ W
      rw [(chartAt ℂ a).left_inv (mem_chart_source ℂ a)]
      exact x.property
    refine ⟨V, hV, hxV, ?_⟩
    intro z hzz
    have hy : (chartAt ℂ a).symm z ∈ (extChartAt 𝓘(ℂ) a).source := by
      simpa only [extChartAt_source] using (chartAt ℂ a).map_target hzz.1
    have hc := hs a ((chartAt ℂ a).symm z) hzz.2 hy
    have hc' : ContDiffAt ℝ ∞ (fun z : ℂ => f ((chartAt ℂ a).symm z)) z := by
      simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq,
        (chartAt ℂ a).right_inv hzz.1] using hc
    exact hc'.contDiffWithinAt
  · intro x
    have ht : Tendsto (chartAt ℂ (x : E)).symm
        (𝓝 ((chartAt ℂ (x : E)) x)) (𝓝 (x : E)) := by
      simpa only [(chartAt ℂ (x : E)).left_inv (mem_chart_source ℂ (x : E))] using
        ((chartAt ℂ (x : E)).continuousAt_symm
          ((chartAt ℂ (x : E)).map_source (mem_chart_source ℂ (x : E)))).tendsto
    filter_upwards [(chartAt ℂ (x : E)).open_target.mem_nhds
      ((chartAt ℂ (x : E)).map_source (mem_chart_source ℂ (x : E))),
      ht.eventually (W.isOpen.mem_nhds x.property)] with z hzt hzW
    have hy : (chartAt ℂ (x : E)).symm z ∈ (extChartAt 𝓘(ℂ) (x : E)).source := by
      simpa only [extChartAt_source] using (chartAt ℂ (x : E)).map_target hzt
    have h := hz (x : E) ((chartAt ℂ (x : E)).symm z) hzW hy
    simpa only [chartDbar, CanonicalDimensionTwo.LocalDbar.dbar,
      extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq,
      (chartAt ℂ (x : E)).right_inv hzt] using h


end SameAtlasAnalyticCohomology
