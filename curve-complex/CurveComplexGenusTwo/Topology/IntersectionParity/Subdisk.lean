import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import CurveComplexGenusTwo.Topology.IntersectionParity.DiscRangeCoordinates

open Set Topology Bornology

namespace CurveComplex.LocalSurgery

/-- Actual planar disk recognition inside an already embedded disk. This
supplies the smaller disk for a selected crosscut and excludes an entire
essential curve lying in the old disk. -/
theorem curve_in_embedded_disk_bounds_subdisk
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (c : Curve S)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d) (hc : c.image ⊆ Set.range d) :
    ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S),
      Topology.IsEmbedding e ∧
      e '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} = c.image ∧
      Set.range e ⊆ Set.range d := by
  classical
  let l := curveInDiscLift c d hd hc
  let r := curveInDiscCoordinates c d hd hc
  have hdl (z : Circle) : d (l z) = c.map z :=
    congrArg Subtype.val (hd.toHomeomorph.apply_symm_apply ⟨c.map z, hc ⟨z, rfl⟩⟩)
  have hl : IsEmbedding l := IsEmbedding.of_comp l.continuous d.continuous (by
    have heq : d ∘ l = c.map := funext hdl
    rw [heq]
    exact c.embedded)
  have hr : IsEmbedding r := IsEmbedding.subtypeVal.comp hl
  let cr : Curve Schoenflies.Plane := ⟨r, hr⟩
  have hJ : Schoenflies.IsJordanCurve cr.image := isJordanCurve_range_of_isEmbedding_circle r hr
  have hCball : cr.image ⊆ Metric.closedBall (0 : Schoenflies.Plane) 1 := by
    rintro x ⟨z, rfl⟩
    exact (l z).property
  have hinside : Schoenflies.inside cr.image ⊆ Metric.closedBall (0 : Schoenflies.Plane) 1 := by
    intro x hx
    by_contra hxnot
    have hnorm : 1 < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hxnot
    let ray := (fun t : ℝ => t • x) '' Set.Ici (1 : ℝ)
    have hray : IsPreconnected ray := isPreconnected_Ici.image _
      (continuous_id.smul continuous_const).continuousOn
    have hxray : x ∈ ray := ⟨1, by simp, one_smul ℝ x⟩
    have hRayOff : ray ⊆ cr.imageᶜ := by
      rintro y ⟨t, ht, rfl⟩ hy
      change 1 ≤ t at ht
      have hb := hCball hy
      have hb' : ‖t • x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hb
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ t)] at hb'
      nlinarith [norm_nonneg x]
    have hRayCC := hray.subset_connectedComponentIn hxray hRayOff
    obtain ⟨R, hR⟩ := hx.2.exists_norm_le
    let t := max 1 ((R + 1) / ‖x‖)
    have ht : 1 ≤ t := le_max_left _ _
    have hbound := hR (t • x) (hRayCC ⟨t, ht, rfl⟩)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ t)] at hbound
    have hdiv : (R + 1) / ‖x‖ ≤ t := le_max_right _ _
    have hmul := (div_le_iff₀ (by linarith : 0 < ‖x‖)).mp hdiv
    linarith
  obtain ⟨p, hp, hpb⟩ := jordan_curve_bounds_disc cr hJ
  have hpRange : Set.range p = Schoenflies.inside cr.image ∪ cr.image :=
    embedded_disc_range_eq_closed_inside p hp cr.image hJ hpb
  have hpball (u : Metric.closedBall (0 : Schoenflies.Plane) 1) :
      p u ∈ Metric.closedBall (0 : Schoenflies.Plane) 1 :=
    Set.union_subset hinside hCball (hpRange ▸ Set.mem_range_self u)
  let pD : C(Metric.closedBall (0 : Schoenflies.Plane) 1,
      Metric.closedBall (0 : Schoenflies.Plane) 1) :=
    ⟨fun u => ⟨p u, hpball u⟩, p.continuous.subtype_mk hpball⟩
  let e := d.comp pD
  refine ⟨e, hd.comp (hp.codRestrict _ hpball), ?_, ?_⟩
  · change (d ∘ pD) '' {x | x.val ∈ Metric.sphere (0 : Schoenflies.Plane) 1} = c.image
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hpu : p u ∈ cr.image := hpb ▸ Set.mem_image_of_mem p hu
      obtain ⟨z, hz⟩ := hpu
      have hpD : pD u = l z := Subtype.ext hz.symm
      change d (pD u) ∈ c.image
      rw [hpD, hdl]
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      have hrz : r z ∈ p '' {x | x.val ∈ Metric.sphere (0 : Schoenflies.Plane) 1} :=
        hpb.symm ▸ Set.mem_range_self z
      obtain ⟨u, hu, hpu⟩ := hrz
      refine ⟨u, hu, ?_⟩
      have hpD : pD u = l z := Subtype.ext hpu
      change d (pD u) = c.map z
      rw [hpD, hdl]
  · rintro y ⟨u, rfl⟩
    exact ⟨pD u, rfl⟩

end CurveComplex.LocalSurgery
