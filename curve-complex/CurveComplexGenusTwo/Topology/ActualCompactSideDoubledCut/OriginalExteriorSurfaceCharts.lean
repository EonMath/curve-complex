import CurveComplexGenusTwo.Topology.ActualCompactSideDoubledCut.OriginalExteriorRadialCharts
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualBoundaryProperArcStrip

open Set Topology Metric CurveComplex
open scoped Manifold ContDiff

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem source_chart_exterior_radius
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x y : S) (R : ℝ)
    (hy : y ∈ (chartAt Plane x).source)
    (hyQ : y ∉ OriginalBoundaryArc.openDisk S x R) :
    R ≤ ‖(chartAt Plane x) y - (chartAt Plane x) x‖ := by
  apply le_of_not_gt
  intro hlt
  have hball : (chartAt Plane x) y ∈
      Metric.ball ((chartAt Plane x) x) R := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hlt
  apply hyQ
  exact ⟨(chartAt Plane x) y, hball,
    (chartAt Plane x).left_inv hy⟩

theorem source_chart_symm_exterior
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target)
    (z : Plane) (hz : z ∈ (chartAt Plane x).target)
    (hRz : R ≤ ‖z - (chartAt Plane x) x‖) :
    (chartAt Plane x).symm z ∉ OriginalBoundaryArc.openDisk S x R := by
  rintro ⟨w,hw,hzw⟩
  have hwtarget : w ∈ (chartAt Plane x).target :=
    htarget (Metric.ball_subset_closedBall hw)
  have hweq : w = z := (chartAt Plane x).symm.injOn hwtarget hz hzw
  have hwr : ‖w - (chartAt Plane x) x‖ < R := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hw
  exact (not_lt_of_ge hRz) (hweq ▸ hwr)

def sourceExteriorPatch
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) : Set (OriginalBoundaryArc.Q S x R) :=
  {y | y.val ∈ (chartAt Plane x).source}

theorem sourceExteriorPatch_isOpen
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) : IsOpen (sourceExteriorPatch S x R) :=
  (chartAt Plane x).open_source.preimage continuous_subtype_val

def coordinateExteriorPatch
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) :
    Set ↥(CenteredPlaneExterior ((chartAt Plane x) x) R) :=
  {z | z.val ∈ (chartAt Plane x).target}

theorem coordinateExteriorPatch_isOpen
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) : IsOpen (coordinateExteriorPatch S x R) :=
  (chartAt Plane x).open_target.preimage continuous_subtype_val

noncomputable def sourceExteriorPatchHomeomorph
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target) :
    ↥(sourceExteriorPatch S x R) ≃ₜ
      ↥(coordinateExteriorPatch S x R) where
  toFun y := ⟨⟨(chartAt Plane x) y.val.val,
    source_chart_exterior_radius S x y.val.val R y.property y.val.property⟩,
      (chartAt Plane x).map_source y.property⟩
  invFun z := ⟨⟨(chartAt Plane x).symm z.val.val,
    source_chart_symm_exterior S x R htarget z.val.val z.property z.val.property⟩,
      (chartAt Plane x).map_target z.property⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact (chartAt Plane x).left_inv y.property
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact (chartAt Plane x).right_inv z.property
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (chartAt Plane x).continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.property)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (chartAt Plane x).continuousOn_symm.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun z => z.property)

noncomputable def sourceExteriorPatchChart
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target)
    (y : ↥(sourceExteriorPatch S x R)) :
    OpenPartialHomeomorph (OriginalBoundaryArc.Q S x R)
      (EuclideanHalfSpace 2) := by
  let c := (chartAt Plane x) x
  let h := sourceExteriorPatchHomeomorph S x R htarget
  let z : ↥(coordinateExteriorPatch S x R) := h y
  let U : TopologicalSpace.Opens ↥(CenteredPlaneExterior c R) :=
    ⟨coordinateExteriorPatch S x R, coordinateExteriorPatch_isOpen S x R⟩
  letI : Nonempty U := ⟨z⟩
  let e := (centeredExteriorChart c R hR z.val).subtypeRestr
    (show Nonempty U from ⟨z⟩)
  let p := h.toOpenPartialHomeomorph.trans e
  have hp : Topology.IsOpenEmbedding
      (Subtype.val : ↥(sourceExteriorPatch S x R) → OriginalBoundaryArc.Q S x R) :=
    ⟨Topology.IsEmbedding.subtypeVal, by
      simpa only [Subtype.range_coe] using sourceExteriorPatch_isOpen S x R⟩
  exact p.lift_openEmbedding hp

theorem sourceExteriorPatchChart_mem_source
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target)
    (y : ↥(sourceExteriorPatch S x R)) :
    y.val ∈ (sourceExteriorPatchChart S x R hR htarget y).source := by
  let c := (chartAt Plane x) x
  let h := sourceExteriorPatchHomeomorph S x R htarget
  let z : ↥(coordinateExteriorPatch S x R) := h y
  let U : TopologicalSpace.Opens ↥(CenteredPlaneExterior c R) :=
    ⟨coordinateExteriorPatch S x R, coordinateExteriorPatch_isOpen S x R⟩
  let e := (centeredExteriorChart c R hR z.val).subtypeRestr
    (show Nonempty U from ⟨z⟩)
  let p := h.toOpenPartialHomeomorph.trans e
  change y.val ∈ (p.lift_openEmbedding
    (show Topology.IsOpenEmbedding
      (Subtype.val : ↥(sourceExteriorPatch S x R) → OriginalBoundaryArc.Q S x R)
      from ⟨Topology.IsEmbedding.subtypeVal, by
        simpa only [Subtype.range_coe] using sourceExteriorPatch_isOpen S x R⟩)).source
  rw [OpenPartialHomeomorph.lift_openEmbedding_source]
  refine ⟨y, ?_, rfl⟩
  have he : z ∈ e.source := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact centeredExteriorChart_mem_source c R hR z.val
  simpa [p, h, z] using he

theorem sourceExteriorPatchChart_coord0
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target)
    (y : ↥(sourceExteriorPatch S x R)) :
    ((sourceExteriorPatchChart S x R hR htarget y) y.val).val 0 =
      ‖(chartAt Plane x) y.val.val - (chartAt Plane x) x‖ / R - 1 := by
  let c := (chartAt Plane x) x
  let z : ↥(CenteredPlaneExterior c R) :=
    ⟨(chartAt Plane x) y.val.val,
      source_chart_exterior_radius S x y.val.val R y.property y.val.property⟩
  simp only [sourceExteriorPatchChart, OpenPartialHomeomorph.lift_openEmbedding_apply,
    OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply]
  change ((centeredExteriorChart c R hR z) z).val 0 =
    ‖z.val - c‖ / R - 1
  exact centeredExteriorChart_coord0 c R hR z

def sourceClosedDisk
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) : Set S :=
  (chartAt Plane x).symm '' Metric.closedBall ((chartAt Plane x) x) R

theorem sourceClosedDisk_isCompact
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target) : IsCompact (sourceClosedDisk S x R) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((chartAt Plane x).continuousOn_symm.mono htarget)

theorem sourceClosedDisk_subset_chart_source
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target) :
    sourceClosedDisk S x R ⊆ (chartAt Plane x).source := by
  rintro y ⟨z,hz,rfl⟩
  exact (chartAt Plane x).map_target (htarget hz)

theorem sourceOpenDisk_subset_closedDisk
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) :
    OriginalBoundaryArc.openDisk S x R ⊆ sourceClosedDisk S x R :=
  Set.image_mono Metric.ball_subset_closedBall

def sourceOutsideClosedDiskPatch
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) : Set (OriginalBoundaryArc.Q S x R) :=
  {y | y.val ∈ (sourceClosedDisk S x R)ᶜ}

theorem sourceOutsideClosedDiskPatch_isOpen
    (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (x : S) (R : ℝ)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target) :
    IsOpen (sourceOutsideClosedDiskPatch S x R) :=
  (sourceClosedDisk_isCompact S x R htarget).isClosed.isOpen_compl.preimage
    continuous_subtype_val

noncomputable def sourceOutsideClosedDiskPatchHomeomorph
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) :
    ↥(sourceOutsideClosedDiskPatch S x R) ≃ₜ
      ↥(sourceClosedDisk S x R)ᶜ where
  toFun y := ⟨y.val.val,y.property⟩
  invFun y := ⟨⟨y.val, by
    intro hy
    exact y.property (sourceOpenDisk_subset_closedDisk S x R hy)⟩,y.property⟩
  left_inv y := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def sourceOutsideClosedDiskChart
    (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (x : S) (R : ℝ)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target)
    (y : ↥(sourceOutsideClosedDiskPatch S x R)) :
    OpenPartialHomeomorph (OriginalBoundaryArc.Q S x R)
      (EuclideanHalfSpace 2) := by
  let h := sourceOutsideClosedDiskPatchHomeomorph S x R
  let z : ↥(sourceClosedDisk S x R)ᶜ := h y
  let U : TopologicalSpace.Opens S :=
    ⟨(sourceClosedDisk S x R)ᶜ,
      (sourceClosedDisk_isCompact S x R htarget).isClosed.isOpen_compl⟩
  let e := ((chartAt Plane y.val.val).subtypeRestr
    (show Nonempty U from ⟨z⟩)).trans
      (planeInteriorOpenEmbedding_isOpenEmbedding.toOpenPartialHomeomorph
        planeInteriorOpenEmbedding)
  let p := h.toOpenPartialHomeomorph.trans e
  have hp : Topology.IsOpenEmbedding
      (Subtype.val : ↥(sourceOutsideClosedDiskPatch S x R) → OriginalBoundaryArc.Q S x R) :=
    ⟨Topology.IsEmbedding.subtypeVal, by
      simpa only [Subtype.range_coe] using
        sourceOutsideClosedDiskPatch_isOpen S x R htarget⟩
  exact p.lift_openEmbedding hp

theorem sourceOutsideClosedDiskChart_mem_source
    (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (x : S) (R : ℝ)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target)
    (y : ↥(sourceOutsideClosedDiskPatch S x R)) :
    y.val ∈ (sourceOutsideClosedDiskChart S x R htarget y).source := by
  let h := sourceOutsideClosedDiskPatchHomeomorph S x R
  let z : ↥(sourceClosedDisk S x R)ᶜ := h y
  let U : TopologicalSpace.Opens S :=
    ⟨(sourceClosedDisk S x R)ᶜ,
      (sourceClosedDisk_isCompact S x R htarget).isClosed.isOpen_compl⟩
  let e := ((chartAt Plane y.val.val).subtypeRestr
    (show Nonempty U from ⟨z⟩)).trans
      (planeInteriorOpenEmbedding_isOpenEmbedding.toOpenPartialHomeomorph
        planeInteriorOpenEmbedding)
  let p := h.toOpenPartialHomeomorph.trans e
  change y.val ∈ (p.lift_openEmbedding
    (show Topology.IsOpenEmbedding
      (Subtype.val : ↥(sourceOutsideClosedDiskPatch S x R) → OriginalBoundaryArc.Q S x R)
      from ⟨Topology.IsEmbedding.subtypeVal, by
        simpa only [Subtype.range_coe] using
          sourceOutsideClosedDiskPatch_isOpen S x R htarget⟩)).source
  rw [OpenPartialHomeomorph.lift_openEmbedding_source]
  refine ⟨y, ?_, rfl⟩
  have hz : z ∈ e.source := by
    simp only [e, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.subtypeRestr_source]
    exact ⟨mem_chart_source Plane y.val.val, trivial⟩
  simpa [p, h, z] using hz

theorem sourceOutsideClosedDiskChart_coord0_pos
    (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (x : S) (R : ℝ)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target)
    (y : ↥(sourceOutsideClosedDiskPatch S x R)) :
    0 < ((sourceOutsideClosedDiskChart S x R htarget y) y.val).val 0 := by
  simp only [sourceOutsideClosedDiskChart,
    OpenPartialHomeomorph.lift_openEmbedding_apply,
    OpenPartialHomeomorph.trans_apply,
    Homeomorph.toOpenPartialHomeomorph_apply,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  exact planeInteriorOpenEmbedding_coord0_pos ((chartAt Plane y.val.val) y.val.val)

theorem sourceExterior_has_halfSpace_charts
    (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target) :
    ∀ y : OriginalBoundaryArc.Q S x R,
      ∃ e : OpenPartialHomeomorph (OriginalBoundaryArc.Q S x R)
        (EuclideanHalfSpace 2), y ∈ e.source := by
  intro y
  by_cases hy : y ∈ sourceExteriorPatch S x R
  · let v : ↥(sourceExteriorPatch S x R) := ⟨y,hy⟩
    exact ⟨sourceExteriorPatchChart S x R hR htarget v,
      sourceExteriorPatchChart_mem_source S x R hR htarget v⟩
  · have hout : y ∈ sourceOutsideClosedDiskPatch S x R := by
      intro hD
      exact hy (sourceClosedDisk_subset_chart_source S x R htarget hD)
    let v : ↥(sourceOutsideClosedDiskPatch S x R) := ⟨y,hout⟩
    exact ⟨sourceOutsideClosedDiskChart S x R htarget v,
      sourceOutsideClosedDiskChart_mem_source S x R htarget v⟩

theorem sourceExterior_boundary_chart_zero
    (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target)
    (y : OriginalBoundaryArc.Q S x R)
    (hyB : y.val ∈ OriginalBoundaryArc.boundaryCircle S x R) :
    ∃ e : OpenPartialHomeomorph (OriginalBoundaryArc.Q S x R)
      (EuclideanHalfSpace 2),
      y ∈ e.source ∧ (e y).val 0 = 0 := by
  obtain ⟨z,hz,hyz⟩ := hyB
  have hzt : z ∈ (chartAt Plane x).target :=
    htarget (Metric.sphere_subset_closedBall hz)
  have hychart : y.val ∈ (chartAt Plane x).source := by
    rw [← hyz]
    exact (chartAt Plane x).map_target hzt
  let v : ↥(sourceExteriorPatch S x R) := ⟨y,hychart⟩
  refine ⟨sourceExteriorPatchChart S x R hR htarget v,
    sourceExteriorPatchChart_mem_source S x R hR htarget v, ?_⟩
  rw [sourceExteriorPatchChart_coord0]
  have hcoord : (chartAt Plane x) y.val = z := by
    rw [← hyz]
    exact (chartAt Plane x).right_inv hzt
  rw [hcoord]
  have hn : ‖z - (chartAt Plane x) x‖ = R := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using hz
  rw [hn]
  field_simp
  ring

theorem sourceExterior_nonboundary_chart_pos
    (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target)
    (y : OriginalBoundaryArc.Q S x R)
    (hyB : y.val ∉ OriginalBoundaryArc.boundaryCircle S x R) :
    ∃ e : OpenPartialHomeomorph (OriginalBoundaryArc.Q S x R)
      (EuclideanHalfSpace 2),
      y ∈ e.source ∧ 0 < (e y).val 0 := by
  by_cases hy : y ∈ sourceExteriorPatch S x R
  · let v : ↥(sourceExteriorPatch S x R) := ⟨y,hy⟩
    refine ⟨sourceExteriorPatchChart S x R hR htarget v,
      sourceExteriorPatchChart_mem_source S x R hR htarget v, ?_⟩
    rw [sourceExteriorPatchChart_coord0]
    have hge := source_chart_exterior_radius S x y.val R hy y.property
    have hne : ‖(chartAt Plane x) y.val - (chartAt Plane x) x‖ ≠ R := by
      intro heq
      apply hyB
      exact ⟨(chartAt Plane x) y.val,
        by simpa only [Metric.mem_sphere, dist_eq_norm] using heq,
        (chartAt Plane x).left_inv hy⟩
    have hgt : R < ‖(chartAt Plane x) y.val - (chartAt Plane x) x‖ :=
      lt_of_le_of_ne hge hne.symm
    have hdiv : 1 < ‖(chartAt Plane x) y.val - (chartAt Plane x) x‖ / R := by
      exact (lt_div_iff₀ hR).2 (by simpa only [one_mul] using hgt)
    linarith
  · have hout : y ∈ sourceOutsideClosedDiskPatch S x R := by
      intro hD
      exact hy (sourceClosedDisk_subset_chart_source S x R htarget hD)
    let v : ↥(sourceOutsideClosedDiskPatch S x R) := ⟨y,hout⟩
    exact ⟨sourceOutsideClosedDiskChart S x R htarget v,
      sourceOutsideClosedDiskChart_mem_source S x R htarget v,
      sourceOutsideClosedDiskChart_coord0_pos S x R htarget v⟩

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
