import CurveComplexGenusTwo.Topology.ActualCompactSideDoubledCut.CutOffCentersCharts

open Set Topology Metric
open scoped Manifold ContDiff

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem radial_exterior_iff
    (R : ℝ) (hR : 0 < R) (z : ↥({0}ᶜ : Set Plane)) :
    R ≤ ‖z.val‖ ↔
      1 ≤ ((homeomorphSphereProd Plane R hR z).2 : ℝ) := by
  rw [homeomorphSphereProd_apply_snd_coe]
  simpa only [one_mul] using
    ((le_div_iff₀ hR).symm : (1 : ℝ) * R ≤ ‖z.val‖ ↔ 1 ≤ ‖z.val‖ / R)

private abbrev PlaneExterior (R : ℝ) : Set Plane :=
  {z | R ≤ ‖z‖}

noncomputable def exteriorPuncturedHomeomorph
    (R : ℝ) (hR : 0 < R) :
    ↥(PlaneExterior R) ≃ₜ {z : ↥({0}ᶜ : Set Plane) // R ≤ ‖z.val‖} where
  toFun z := ⟨⟨z.val, by
    intro hz
    have hzero : z.val = 0 := Set.mem_singleton_iff.mp hz
    have hnorm := z.property
    change R ≤ ‖z.val‖ at hnorm
    rw [hzero, norm_zero] at hnorm
    linarith⟩, z.property⟩
  invFun z := ⟨z.val.val,z.property⟩
  left_inv z := rfl
  right_inv z := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def radialTargetHomeomorph
    (R : ℝ) :
    {p : Metric.sphere (0 : Plane) R × Set.Ioi (0 : ℝ) // 1 ≤ p.2.val} ≃ₜ
      (Metric.sphere (0 : Plane) R × Set.Ici (1 : ℝ)) where
  toFun p := (p.val.1, ⟨p.val.2.val,p.property⟩)
  invFun p := ⟨(p.1,⟨p.2.val,by
    change 0 < p.2.val
    exact lt_of_lt_of_le zero_lt_one p.2.property⟩),p.2.property⟩
  left_inv p := rfl
  right_inv p := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def radialExteriorHomeomorph
    (R : ℝ) (hR : 0 < R) :
    ↥(PlaneExterior R) ≃ₜ
      (Metric.sphere (0 : Plane) R × Set.Ici (1 : ℝ)) :=
  ((exteriorPuncturedHomeomorph R hR).trans
    ((homeomorphSphereProd Plane R hR).subtype
      (fun z => radial_exterior_iff R hR z))).trans
    (radialTargetHomeomorph R)

noncomputable def sphereScaleHomeomorph (R : ℝ) (hR : 0 < R) :
    Metric.sphere (0 : Plane) R ≃ₜ Metric.sphere (0 : Plane) 1 where
  toFun z := ⟨R⁻¹ • z.val, by
    have hz : ‖z.val‖ = R := mem_sphere_zero_iff_norm.mp z.property
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR), hz]
    exact inv_mul_cancel₀ hR.ne'⟩
  invFun z := ⟨R • z.val, by
    have hz : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hR, hz]
    ring⟩
  left_inv z := by
    apply Subtype.ext
    change R • (R⁻¹ • z.val) = z.val
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  right_inv z := by
    apply Subtype.ext
    change R⁻¹ • (R • z.val) = z.val
    rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def radialShiftHomeomorph :
    Set.Ici (1 : ℝ) ≃ₜ Set.Ici (0 : ℝ) where
  toFun r := ⟨r.val - 1, by
    change 0 ≤ r.val - 1
    exact sub_nonneg.mpr r.property⟩
  invFun r := ⟨r.val + 1, by
    change 1 ≤ r.val + 1
    linarith [show 0 ≤ r.val from r.property]⟩
  left_inv r := by apply Subtype.ext; dsimp; ring
  right_inv r := by apply Subtype.ext; dsimp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private abbrev UnitCircle := Metric.sphere (0 : Plane) 1
private abbrev Nonneg := Set.Ici (0 : ℝ)

noncomputable def unitCircleRadialChart (v : UnitCircle) :
    OpenPartialHomeomorph (UnitCircle × Nonneg) (EuclideanHalfSpace 2) := by
  let e1 : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ :=
    (EuclideanSpace.equiv (Fin 1) ℝ).toHomeomorph.trans
      (Homeomorph.funUnique (Fin 1) ℝ)
  let e : (EuclideanSpace ℝ (Fin 1) × Nonneg) ≃ₜ (ℝ × Nonneg) :=
    e1.prodCongr (Homeomorph.refl Nonneg)
  exact ((chartAt (EuclideanSpace ℝ (Fin 1)) v).prod
    (OpenPartialHomeomorph.refl Nonneg)).transHomeomorph
      (e.trans halfPlaneEuclidean)

theorem unitCircleRadialChart_mem_source (v : UnitCircle) (r : Nonneg) :
    (v,r) ∈ (unitCircleRadialChart v).source := by
  simp [unitCircleRadialChart, OpenPartialHomeomorph.prod_source,
    mem_chart_source]

noncomputable def exteriorProductHomeomorph (R : ℝ) (hR : 0 < R) :
    ↥(PlaneExterior R) ≃ₜ (UnitCircle × Nonneg) :=
  (radialExteriorHomeomorph R hR).trans
    ((sphereScaleHomeomorph R hR).prodCongr radialShiftHomeomorph)

noncomputable def planeExteriorChart (R : ℝ) (hR : 0 < R)
    (z : ↥(PlaneExterior R)) :
    OpenPartialHomeomorph ↥(PlaneExterior R) (EuclideanHalfSpace 2) :=
  (exteriorProductHomeomorph R hR).toOpenPartialHomeomorph.trans
    (unitCircleRadialChart (exteriorProductHomeomorph R hR z).1)

theorem planeExteriorChart_mem_source (R : ℝ) (hR : 0 < R)
    (z : ↥(PlaneExterior R)) :
    z ∈ (planeExteriorChart R hR z).source := by
  simpa [planeExteriorChart] using
    (unitCircleRadialChart_mem_source
      (exteriorProductHomeomorph R hR z).1
      (exteriorProductHomeomorph R hR z).2)

theorem unitCircleRadialChart_coord0 (v : UnitCircle) (r : Nonneg) :
    ((unitCircleRadialChart v) (v,r)).val 0 = r.val := by
  simp [unitCircleRadialChart, halfPlaneEuclidean_coord0]

theorem planeExteriorChart_coord0 (R : ℝ) (hR : 0 < R)
    (z : ↥(PlaneExterior R)) :
    ((planeExteriorChart R hR z) z).val 0 = ‖z.val‖ / R - 1 := by
  simp [planeExteriorChart, exteriorProductHomeomorph,
    unitCircleRadialChart_coord0, radialExteriorHomeomorph,
    exteriorPuncturedHomeomorph, radialTargetHomeomorph,
    radialShiftHomeomorph, radial_exterior_iff]

abbrev CenteredPlaneExterior (c : Plane) (R : ℝ) : Set Plane :=
  {z | R ≤ ‖z - c‖}

noncomputable def centeredExteriorHomeomorph (c : Plane) (R : ℝ) :
    ↥(CenteredPlaneExterior c R) ≃ₜ ↥(PlaneExterior R) where
  toFun z := ⟨z.val - c, z.property⟩
  invFun z := ⟨z.val + c, by
    change R ≤ ‖z.val + c - c‖
    simpa only [add_sub_cancel_right] using
      (show R ≤ ‖z.val‖ from z.property)⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def centeredExteriorChart (c : Plane) (R : ℝ) (hR : 0 < R)
    (z : ↥(CenteredPlaneExterior c R)) :
    OpenPartialHomeomorph ↥(CenteredPlaneExterior c R) (EuclideanHalfSpace 2) :=
  (centeredExteriorHomeomorph c R).toOpenPartialHomeomorph.trans
    (planeExteriorChart R hR (centeredExteriorHomeomorph c R z))

theorem centeredExteriorChart_mem_source (c : Plane) (R : ℝ) (hR : 0 < R)
    (z : ↥(CenteredPlaneExterior c R)) :
    z ∈ (centeredExteriorChart c R hR z).source := by
  simpa [centeredExteriorChart] using
    planeExteriorChart_mem_source R hR (centeredExteriorHomeomorph c R z)

theorem centeredExteriorChart_coord0 (c : Plane) (R : ℝ) (hR : 0 < R)
    (z : ↥(CenteredPlaneExterior c R)) :
    ((centeredExteriorChart c R hR z) z).val 0 =
      ‖z.val - c‖ / R - 1 := by
  simpa [centeredExteriorChart, centeredExteriorHomeomorph] using
    planeExteriorChart_coord0 R hR (centeredExteriorHomeomorph c R z)

noncomputable def planeInteriorOpenEmbedding : Plane → EuclideanHalfSpace 2 := by
  let e2 : Plane ≃ₜ ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans
      (Homeomorph.finTwoArrow (X := ℝ))
  let ex : ℝ ≃ₜ Set.Ioi (0 : ℝ) := Real.expOrderIso.toHomeomorph
  let i : Set.Ioi (0 : ℝ) → Nonneg :=
    Set.inclusion (show Set.Ioi (0 : ℝ) ⊆ Nonneg from by
      intro x hx
      change 0 ≤ x
      exact le_of_lt hx)
  exact fun p => halfPlaneEuclidean
    ((e2 p).2, i (ex (e2 p).1))

theorem planeInteriorOpenEmbedding_isOpenEmbedding :
    Topology.IsOpenEmbedding planeInteriorOpenEmbedding := by
  let e2 : Plane ≃ₜ ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans
      (Homeomorph.finTwoArrow (X := ℝ))
  let ex : ℝ ≃ₜ Set.Ioi (0 : ℝ) := Real.expOrderIso.toHomeomorph
  let swap : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.prodComm ℝ ℝ
  let e : Plane ≃ₜ (ℝ × Set.Ioi (0 : ℝ)) :=
    e2.trans (swap.trans ((Homeomorph.refl ℝ).prodCongr ex))
  let i : Set.Ioi (0 : ℝ) → Nonneg :=
    Set.inclusion (show Set.Ioi (0 : ℝ) ⊆ Nonneg from by
      intro x hx
      change 0 ≤ x
      exact le_of_lt hx)
  have hi : Topology.IsOpenEmbedding i :=
    Topology.IsOpenEmbedding.inclusion (show Set.Ioi (0 : ℝ) ⊆ Nonneg from by
      intro x hx
      change 0 ≤ x
      exact le_of_lt hx) (by
      exact isOpen_lt continuous_const continuous_subtype_val)
  have hp : Topology.IsOpenEmbedding
      (fun p : ℝ × Set.Ioi (0 : ℝ) => (p.1, i p.2)) :=
    (Homeomorph.refl ℝ).isOpenEmbedding.prodMap hi
  exact halfPlaneEuclidean.isOpenEmbedding.comp (hp.comp e.isOpenEmbedding)

theorem planeInteriorOpenEmbedding_coord0_pos (p : Plane) :
    0 < (planeInteriorOpenEmbedding p).val 0 := by
  rw [planeInteriorOpenEmbedding, halfPlaneEuclidean_coord0]
  exact Real.exp_pos _

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
