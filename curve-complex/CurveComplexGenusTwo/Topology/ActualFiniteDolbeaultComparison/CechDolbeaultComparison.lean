import CurveComplexGenusTwo.Topology.ActualFiniteDolbeaultComparison.LocalPrimitives
open TopologicalSpace SameAtlasRRLocal Filter Topology
open scoped Manifold ContDiff Bundle
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000
namespace SameAtlasAnalyticCohomology
universe u v
variable {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]
variable (U : OpenCover E)
attribute [local instance] Classical.propDecidable
abbrev DolbeaultHZeroOne (E : Type u) [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] := SmoothZeroOne E ⧸ (dolbeaultDbar (E := E)).range

private theorem coefficient_eq [Fintype U.Index] (P : SubordinateSmoothPartition U)
    (g : oneCocycles U) (a x : E) (hxa : x ∈ (extChartAt 𝓘(ℂ) a).source)
    (i k : U.Index) (hxi : x ∈ U.opens i) (hxk : x ∈ U.opens k) :
    chartCechDbarCoefficient U a P.weight g i x hxi =
      chartCechDbarCoefficient U a P.weight g k x hxk := by
  let H : ℂ → ℂ := fun z =>
    if hz : (extChartAt 𝓘(ℂ) a).symm z ∈ U.opens i ⊓ U.opens k then
      (g.1 i k).1 ⟨(extChartAt 𝓘(ℂ) a).symm z, hz⟩ else 0
  have hH : DifferentiableAt ℂ H ((extChartAt 𝓘(ℂ) a) x) :=
    (holOn_chartExtension_contDiffAt (U.opens i ⊓ U.opens k) (g.1 i k)
      a x ⟨hxi,hxk⟩ hxa).differentiableAt (by simp)
  have hHr : DifferentiableAt ℝ H ((extChartAt 𝓘(ℂ) a) x) := hH.restrictScalars ℝ
  have hzero := (CanonicalDimensionTwo.actualDbar_zero_iff_complex_differentiableAt hHr).mpr hH
  have hfi := (localPartitionPrimitive_contDiffAt U P g i a x hxi hxa).differentiableAt (by simp)
  have hfk := (localPartitionPrimitive_contDiffAt U P g k a x hxk hxa).differentiableAt (by simp)
  have htend : Tendsto (extChartAt 𝓘(ℂ) a).symm
      (𝓝 ((extChartAt 𝓘(ℂ) a) x)) (𝓝 x) := by
    simpa only [(extChartAt 𝓘(ℂ) a).left_inv hxa] using
      (continuousAt_extChartAt_symm' hxa).tendsto
  have heq : (fun z : ℂ =>
      localPartitionPrimitive U P g i ((extChartAt 𝓘(ℂ) a).symm z) -
      localPartitionPrimitive U P g k ((extChartAt 𝓘(ℂ) a).symm z))
      =ᶠ[𝓝 ((extChartAt 𝓘(ℂ) a) x)] H := by
    filter_upwards [htend.eventually ((U.opens i).isOpen.mem_nhds hxi),
      htend.eventually ((U.opens k).isOpen.mem_nhds hxk)] with z hzi hzk
    rw [localPartitionPrimitive_overlap U P g i k _ hzi hzk]
    dsimp only [H]
    split
    · rfl
    · next hn => exact False.elim (hn ⟨hzi,hzk⟩)
  have heq' := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_sub hfi hfk] at heq'
  rw [← localPartitionPrimitive_chartDbar U P g i a x hxi hxa,
    ← localPartitionPrimitive_chartDbar U P g k a x hxk hxa]
  apply sub_eq_zero.mp
  have hh : chartDbar a (localPartitionPrimitive U P g i) x -
      chartDbar a (localPartitionPrimitive U P g k) x =
      CanonicalDimensionTwo.LocalDbar.dbar H ((extChartAt 𝓘(ℂ) a) x) := by
    unfold chartDbar CanonicalDimensionTwo.LocalDbar.dbar
    dsimp only
    rw [← heq']
    simp only [sub_apply]
    ring
  rw [hh, hzero]

noncomputable def cechToDolbeault [Fintype U.Index]
    (P : SubordinateSmoothPartition U) : oneCocycles U →ₗ[ℂ] SmoothZeroOne E where
  toFun g := by
    classical
    exact ⟨fun a x => if x ∈ (extChartAt 𝓘(ℂ) a).source then
      chartCechDbarCoefficient U a P.weight g (coverIndex U x) x (coverIndex_mem U x)
      else 0, by
      refine ⟨?_, ?_, ?_⟩
      · intro a x hx
        exact ite_eq_right hx
      · intro a z hz
        let x : E := (extChartAt 𝓘(ℂ) a).symm z
        have hx : x ∈ (extChartAt 𝓘(ℂ) a).source := (extChartAt 𝓘(ℂ) a).map_target hz
        let i := coverIndex U x
        have hxi : x ∈ U.opens i := coverIndex_mem U x
        let F : ℂ → ℂ := fun w => localPartitionPrimitive U P g i ((extChartAt 𝓘(ℂ) a).symm w)
        have hf : ContDiffAt ℝ ∞ F z := by
          simpa only [F, x, (extChartAt 𝓘(ℂ) a).right_inv hz] using
            localPartitionPrimitive_contDiffAt U P g i a x hxi hx
        have hd : ContDiffAt ℝ ∞ (fderiv ℝ F) z := hf.fderiv_right (by simp)
        have h1 := hd.clm_apply (contDiffAt_const (c := (1 : ℂ)))
        have hI := hd.clm_apply (contDiffAt_const (c := Complex.I))
        have hs : ContDiffAt ℝ ∞
            (fun w => ((fderiv ℝ F w) 1 + Complex.I * (fderiv ℝ F w) Complex.I) / 2) z := by
          simpa only [smul_eq_mul] using (h1.add (hI.const_smul Complex.I)).div_const (2 : ℂ)
        apply (hs.congr_of_eventuallyEq ?_).contDiffWithinAt
        have htend : Tendsto (extChartAt 𝓘(ℂ) a).symm (𝓝 z) (𝓝 x) := by
          simpa only [x, (extChartAt 𝓘(ℂ) a).right_inv hz] using
            (continuousAt_extChartAt_symm' hx).tendsto
        filter_upwards [(isOpen_extChartAt_target a).mem_nhds hz,
          htend.eventually ((U.opens i).isOpen.mem_nhds hxi)] with w hwt hwi
        have hws := (extChartAt 𝓘(ℂ) a).map_target hwt
        rw [ite_eq_left hws,
          coefficient_eq U P g a _ hws (coverIndex U _) i (coverIndex_mem U _) hwi,
          ← localPartitionPrimitive_chartDbar U P g i a _ hwi hws]
        simp only [chartDbar, F, (extChartAt 𝓘(ℂ) a).right_inv hwt]
      · intro a b x ha hb
        simp only [ite_eq_left ha, ite_eq_left hb]
        rw [← localPartitionPrimitive_chartDbar U P g (coverIndex U x) b x (coverIndex_mem U x) hb,
          ← localPartitionPrimitive_chartDbar U P g (coverIndex U x) a x (coverIndex_mem U x) ha]
        exact chartDbar_transition a b x _ ha hb
          ((localPartitionPrimitive_contDiffAt U P g (coverIndex U x) a x
            (coverIndex_mem U x) ha).of_le (by simp))⟩
  map_add' := by
    intro g h
    apply Subtype.ext
    funext a x
    by_cases hx : x ∈ (extChartAt 𝓘(ℂ) a).source
    · simp only [ite_eq_left hx, Submodule.coe_add, Pi.add_apply]
      unfold chartCechDbarCoefficient
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      split
      · next hxj => simp only [dite_eq_left hxj, Submodule.coe_add, Pi.add_apply, add_mul]
      · next hxj => simp only [dite_eq_right hxj, zero_add]
    · simp only [ite_eq_right hx, Submodule.coe_add, Pi.add_apply, zero_add]
  map_smul' := by
    intro c g
    apply Subtype.ext
    funext a x
    by_cases hx : x ∈ (extChartAt 𝓘(ℂ) a).source
    · simp only [ite_eq_left hx, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
      unfold chartCechDbarCoefficient
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      split
      · next hxj =>
          simp only [dite_eq_left hxj, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
          ring
      · next hxj => simp only [dite_eq_right hxj, mul_zero]
    · simp only [ite_eq_right hx, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_zero]

theorem cechToDolbeault_local [Fintype U.Index] (P : SubordinateSmoothPartition U)
    (a x : E) (hx : x ∈ (extChartAt 𝓘(ℂ) a).source)
    (g : oneCocycles U) (i : U.Index) (hxi : x ∈ U.opens i) :
    (cechToDolbeault U P g).1 a x =
      chartCechDbarCoefficient U a P.weight g i x hxi := by
  change (if x ∈ (extChartAt 𝓘(ℂ) a).source then
    chartCechDbarCoefficient U a P.weight g (coverIndex U x) x (coverIndex_mem U x) else 0) = _
  rw [ite_eq_left hx]
  exact coefficient_eq U P g a x hx _ i (coverIndex_mem U x) hxi

theorem cechToDolbeault_coboundary [Fintype U.Index]
    (P : SubordinateSmoothPartition U) (f : CechZero U) :
    cechToDolbeault U P (deltaZeroToCocycles U f) ∈
      (dolbeaultDbar (E := E)).range := by
  classical
  let G : E → ℂ := fun x => ∑ j,
    (P.weight j x : ℂ) * (if hxj : x ∈ U.opens j then (f j).1 ⟨x,hxj⟩ else 0)
  have hG : G ∈ smoothZeroSubmodule (E := E) := by
    intro a z hz
    let x : E := (extChartAt 𝓘(ℂ) a).symm z
    have hxa : x ∈ (extChartAt 𝓘(ℂ) a).source := (extChartAt 𝓘(ℂ) a).map_target hz
    have htend : Tendsto (extChartAt 𝓘(ℂ) a).symm (𝓝 z) (𝓝 x) := by
      simpa only [x, (extChartAt 𝓘(ℂ) a).right_inv hz] using
        (continuousAt_extChartAt_symm' hxa).tendsto
    have hj (j : U.Index) : ContDiffAt ℝ ∞ (fun w : ℂ =>
        (P.weight j ((extChartAt 𝓘(ℂ) a).symm w) : ℂ) *
          (if hyj : (extChartAt 𝓘(ℂ) a).symm w ∈ U.opens j then
            (f j).1 ⟨(extChartAt 𝓘(ℂ) a).symm w,hyj⟩ else 0)) z := by
      by_cases hxj : x ∈ U.opens j
      · have hw := (P.smoothWeight j a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds hz)
        have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp z hw
        have hh := holOn_chartExtension_contDiffAt (U.opens j) (f j) a x hxj hxa
        have hh' : ContDiffAt ℝ ∞ (fun w : ℂ =>
            if hyj : (extChartAt 𝓘(ℂ) a).symm w ∈ U.opens j then
              (f j).1 ⟨(extChartAt 𝓘(ℂ) a).symm w,hyj⟩ else 0) z := by
          simpa only [x, (extChartAt 𝓘(ℂ) a).right_inv hz] using hh.restrict_scalars ℝ
        exact hc.mul hh'
      · have hs : x ∉ tsupport (P.weight j) := fun h => hxj (P.supportWeight j h)
        have he : P.weight j =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hs
        apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        filter_upwards [htend.eventually he] with w hw
        change P.weight j ((extChartAt 𝓘(ℂ) a).symm w) = 0 at hw
        simp only [hw, Complex.ofReal_zero, zero_mul, Pi.zero_apply]
    exact (ContDiffAt.sum (fun j _ => hj j)).contDiffWithinAt
  have hpoint (i : U.Index) (y : E) (hyi : y ∈ U.opens i) :
      G y - localPartitionPrimitive U P (deltaZeroToCocycles U f) i y = (f i).1 ⟨y,hyi⟩ := by
    unfold localPartitionPrimitive
    rw [dite_eq_left hyi]
    dsimp only [G]
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ j, (P.weight j y : ℂ) * (f i).1 ⟨y,hyi⟩ := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hyj : y ∈ U.opens j
        · simp only [dite_eq_left hyj, deltaZeroToCocycles, deltaZero,
            LinearMap.coe_mk, AddHom.coe_mk, HolOn.restrict,
            Submodule.coe_sub, Pi.sub_apply]
          ring
        · have hw : P.weight j y = 0 := by
            apply Function.notMem_support.1
            intro h
            exact hyj (P.supportWeight j (subset_closure h))
          simp only [dite_eq_right hyj, hw, Complex.ofReal_zero, zero_mul, sub_zero]
      _ = _ := by
        rw [← Finset.sum_mul]
        have hw : (∑ j, (P.weight j y : ℂ)) = 1 := by exact_mod_cast P.partitionOne y
        rw [hw, one_mul]
  let F : SmoothZero E := ⟨G,hG⟩
  refine ⟨F, ?_⟩
  apply Subtype.ext
  funext a x
  by_cases hxa : x ∈ (extChartAt 𝓘(ℂ) a).source
  · let i := coverIndex U x
    have hxi : x ∈ U.opens i := coverIndex_mem U x
    change (if x ∈ (extChartAt 𝓘(ℂ) a).source then chartDbar a G x else 0) =
      (cechToDolbeault U P (deltaZeroToCocycles U f)).1 a x
    rw [ite_eq_left hxa]
    rw [cechToDolbeault_local U P a x hxa _ i hxi,
      ← localPartitionPrimitive_chartDbar U P _ i a x hxi hxa]
    let H : ℂ → ℂ := fun z => if hz : (extChartAt 𝓘(ℂ) a).symm z ∈ U.opens i then
      (f i).1 ⟨(extChartAt 𝓘(ℂ) a).symm z,hz⟩ else 0
    have hh : DifferentiableAt ℂ H ((extChartAt 𝓘(ℂ) a) x) :=
      (holOn_chartExtension_contDiffAt (U.opens i) (f i) a x hxi hxa).differentiableAt (by simp)
    have hzero := (CanonicalDimensionTwo.actualDbar_zero_iff_complex_differentiableAt
      (hh.restrictScalars ℝ)).mpr hh
    have htend : Tendsto (extChartAt 𝓘(ℂ) a).symm
        (𝓝 ((extChartAt 𝓘(ℂ) a) x)) (𝓝 x) := by
      simpa only [(extChartAt 𝓘(ℂ) a).left_inv hxa] using
        (continuousAt_extChartAt_symm' hxa).tendsto
    have heq : (fun z : ℂ => G ((extChartAt 𝓘(ℂ) a).symm z) -
        localPartitionPrimitive U P (deltaZeroToCocycles U f) i ((extChartAt 𝓘(ℂ) a).symm z))
        =ᶠ[𝓝 ((extChartAt 𝓘(ℂ) a) x)] H := by
      filter_upwards [htend.eventually ((U.opens i).isOpen.mem_nhds hxi)] with z hz
      rw [hpoint i _ hz]
      dsimp only [H]
      split
      · rfl
      · next hn => exact False.elim (hn hz)
    have hgd := ((hG a).contDiffAt (extChartAt_target_mem_nhds'
      ((extChartAt 𝓘(ℂ) a).map_source hxa))).differentiableAt (by simp)
    have hfd := (localPartitionPrimitive_contDiffAt U P (deltaZeroToCocycles U f) i a x hxi hxa).differentiableAt (by simp)
    have heq' := heq.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_sub hgd hfd] at heq'
    apply sub_eq_zero.mp
    have hd : chartDbar a G x - chartDbar a (localPartitionPrimitive U P (deltaZeroToCocycles U f) i) x =
        CanonicalDimensionTwo.LocalDbar.dbar H ((extChartAt 𝓘(ℂ) a) x) := by
      unfold chartDbar CanonicalDimensionTwo.LocalDbar.dbar
      dsimp only
      rw [← heq']
      simp only [sub_apply]
      ring
    rw [hd,hzero]
  · change (if x ∈ (extChartAt 𝓘(ℂ) a).source then chartDbar a F.1 x else 0) = _
    simp only [ite_eq_right hxa, cechToDolbeault, LinearMap.coe_mk, AddHom.coe_mk]


private theorem comparison_representatives [Fintype U.Index]
    (P : SubordinateSmoothPartition U) (g h : oneCocycles U)
    (hc : classOf U g = classOf U h) :
    Submodule.mkQ (dolbeaultDbar (E := E)).range (cechToDolbeault U P g) =
      Submodule.mkQ (dolbeaultDbar (E := E)).range (cechToDolbeault U P h) := by
  have he := congrArg Subtype.val hc
  change (Submodule.Quotient.mk g.1 : cochainQuotient U) = Submodule.Quotient.mk h.1 at he
  have hm : g.1 - h.1 ∈ (deltaZero U).range := (Submodule.Quotient.eq _).mp he
  obtain ⟨f,hf⟩ := hm
  have hδ : deltaZeroToCocycles U f = g - h := by
    apply Subtype.ext
    exact hf
  apply (Submodule.Quotient.eq _).mpr
  change cechToDolbeault U P g - cechToDolbeault U P h ∈ (dolbeaultDbar (E := E)).range
  rw [← map_sub, ← hδ]
  exact cechToDolbeault_coboundary U P f

/-- Descend the explicit smooth form through the actual Čech quotient. -/
noncomputable def cechDolbeaultComparison [Fintype U.Index]
    (P : SubordinateSmoothPartition U) : CechHOne U →ₗ[ℂ] DolbeaultHZeroOne E where
  toFun x := Submodule.mkQ (dolbeaultDbar (E := E)).range
    (cechToDolbeault U P (Classical.choose (classOf_surjective U x)))
  map_add' := by
    intro x y
    rw [← map_add, ← map_add]
    apply comparison_representatives U P
    rw [map_add, Classical.choose_spec (classOf_surjective U x),
      Classical.choose_spec (classOf_surjective U y)]
    exact Classical.choose_spec (classOf_surjective U (x+y))
  map_smul' := by
    intro c x
    rw [← map_smul, ← map_smul]
    apply comparison_representatives U P
    rw [map_smul, Classical.choose_spec (classOf_surjective U x)]
    exact Classical.choose_spec (classOf_surjective U (c • x))

theorem cechDolbeaultComparison_classOf [Fintype U.Index]
    (P : SubordinateSmoothPartition U) (g : oneCocycles U) :
    cechDolbeaultComparison U P (classOf U g) =
      Submodule.mkQ (dolbeaultDbar (E := E)).range (cechToDolbeault U P g) := by
  change Submodule.mkQ (dolbeaultDbar (E := E)).range
    (cechToDolbeault U P (Classical.choose (classOf_surjective U (classOf U g)))) = _
  exact comparison_representatives U P _ g (Classical.choose_spec (classOf_surjective U (classOf U g)))

end SameAtlasAnalyticCohomology
