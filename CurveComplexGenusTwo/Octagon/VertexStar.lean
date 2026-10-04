import CurveComplexGenusTwo.Octagon.VertexChartGlueWave11
import CurveComplexGenusTwo.Octagon.OctagonAtlasCoverageWave10

namespace CurveComplex.Octagon

private theorem star_eight_interval_cover (v : ℝ) (hv0 : 0 ≤ v) (hv8 : v ≤ 8) :
    ∃ (i : Side) (t : unitInterval), v = (i.val : ℝ) + (t : ℝ) := by
  by_cases hvlt : v < 8
  · let i : Side := ⟨Nat.floor v, (Nat.floor_lt hv0).2 hvlt⟩
    have hlow : (Nat.floor v : ℝ) ≤ v := Nat.floor_le hv0
    have hhigh : v < (Nat.floor v : ℝ) + 1 := by
      simpa using (Nat.lt_succ_floor v)
    let t : unitInterval := ⟨v - (Nat.floor v : ℝ), by
      constructor <;> linarith⟩
    refine ⟨i, t, ?_⟩
    dsimp [i, t]
    ring
  · have hv : v = 8 := by linarith
    refine ⟨(7 : Side), (1 : unitInterval), ?_⟩
    norm_num [hv]

theorem radialSector_surjective (x : Disk) :
    ∃ (i : Side) (r t : unitInterval), radialSector i r t = x := by
  let z : Circle := Circle.exp (Complex.arg (x : ℂ))
  have hcircle : Circle.exp '' Set.Icc (-Real.pi / 8) (-Real.pi / 8 + 2 * Real.pi) =
      Set.univ := by
    exact (Circle.periodic_exp.image_Icc Real.two_pi_pos _).trans
      Circle.exp_surjective.range_eq
  have hz : z ∈ Circle.exp '' Set.Icc (-Real.pi / 8) (-Real.pi / 8 + 2 * Real.pi) := by
    rw [hcircle]
    trivial
  obtain ⟨θ, hθ, hθz⟩ := hz
  let v : ℝ := 4 * θ / Real.pi + 1 / 2
  have hv0 : 0 ≤ v := by
    dsimp [v]
    have := (le_div_iff₀ Real.pi_pos).2 (show - (1 / 2 : ℝ) * Real.pi ≤ 4 * θ by linarith [hθ.1])
    linarith
  have hv8 : v ≤ 8 := by
    dsimp [v]
    have := (div_le_iff₀ Real.pi_pos).2 (show 4 * θ ≤ (15 / 2 : ℝ) * Real.pi by linarith [hθ.2])
    linarith
  obtain ⟨i, t, hvt⟩ := star_eight_interval_cover v hv0 hv8
  have hnorm : ‖(x : ℂ)‖ ≤ 1 := by
    have hx := x.property
    rwa [Metric.mem_closedBall, dist_zero_right] at hx
  let r : unitInterval := ⟨1 - ‖(x : ℂ)‖, by constructor <;> linarith [norm_nonneg (x : ℂ)]⟩
  refine ⟨i, r, t, ?_⟩
  apply Subtype.ext
  have hangle : 2 * Real.pi * ((i.val : ℝ) + (t : ℝ) - 1 / 2) / 8 = θ := by
    rw [← hvt]
    dsimp [v]
    field_simp [Real.pi_ne_zero]
    ring
  change (1 - (r : ℝ)) • (Circle.exp _ : ℂ) = (x : ℂ)
  rw [hangle, hθz]
  dsimp [r, z]
  simpa [Circle.coe_exp, RCLike.real_smul_eq_coe_smul] using
    Complex.norm_mul_exp_arg_mul_I (x : ℂ)

-- Every representative of the quotient vertex is the center of its sector.
theorem radialSector_vertex_radius_zero (i : Side) (r t : unitInterval)
    (h : mk (radialSector i r t) = mk (vertexPoint 0)) :
    sectorLocalRadius r t = 0 := by
  have hx : radialSector i r t ∈ vertexSet := by
    rw [← vertex_fiber_eq_vertexSet 0]
    exact h
  obtain ⟨j, hj⟩ := hx
  have hn := congrArg (fun x : Disk => ‖(x : ℂ)‖) hj
  rw [radialSector_norm] at hn
  have hv : ‖(vertexPoint j : ℂ)‖ = 1 := side_norm j 0
  rw [hv] at hn
  have hr : r = 0 := by apply Subtype.ext; change (r : ℝ) = 0; dsimp [sectorRadial] at hn; linarith
  subst r
  have hC : Circle.exp (2 * Real.pi * ((i.val : ℝ) + t - 1 / 2) / 8) =
      Circle.exp (2 * Real.pi * (j.val : ℝ) / 8) := by
    apply Circle.ext
    simpa [radialSector, vertexPoint, side] using (congrArg (fun x : Disk => (x : ℂ)) hj).symm
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hC
  have hang : (i.val : ℝ) + t - 1 / 2 = (j.val : ℝ) + 8 * (m : ℝ) := by
    field_simp [Real.pi_ne_zero] at hm
    nlinarith [hm]
  have hz : (j.val : ℤ) + 8 * m - (i.val : ℤ) = 0 := by
    have ht0 := t.property.1
    have ht1 := t.property.2
    have hlo : (-1 : ℝ) < ((j.val : ℤ) + 8 * m - (i.val : ℤ) : ℤ) := by
      push_cast
      linarith
    have hhi : (((j.val : ℤ) + 8 * m - (i.val : ℤ) : ℤ) : ℝ) < 1 := by
      push_cast
      linarith
    have h1 : (-1 : ℤ) < (j.val : ℤ) + 8 * m - (i.val : ℤ) := by exact_mod_cast hlo
    have h2 : (j.val : ℤ) + 8 * m - (i.val : ℤ) < 1 := by exact_mod_cast hhi
    omega
  have hzr : (j.val : ℝ) + 8 * (m : ℝ) - (i.val : ℝ) = 0 := by exact_mod_cast hz
  have ht : (t : ℝ) = 1 / 2 := by linarith
  simp [sectorLocalRadius, sectorLocalComplex, ht]

theorem vertexModelSource_vertex_interior :
    mk (vertexPoint 0) ∈ interior (Set.range vertexModelSource) := by
  letI : T2Space Surface := quotient_t2
  let bad : Set (unitInterval × unitInterval) :=
    {p | (1 : ℝ) / 4 ≤ sectorLocalRadius p.1 p.2}
  have hbad : IsCompact bad :=
    (isClosed_Ici.preimage continuous_sectorLocalRadius).isCompact
  let B : Set Surface := ⋃ i : Side,
    (fun p : unitInterval × unitInterval => mk (radialSector i p.1 p.2)) '' bad
  have hB : IsClosed B := by
    apply isClosed_iUnion_of_finite
    intro i
    exact (hbad.image (continuous_mk.comp (continuous_radialSector i))).isClosed
  have hv : mk (vertexPoint 0) ∈ Bᶜ := by
    intro hx
    obtain ⟨i, p, hp, heq⟩ := Set.mem_iUnion.mp hx
    have hz := radialSector_vertex_radius_zero i p.1 p.2 heq
    change 1 / 4 ≤ sectorLocalRadius p.1 p.2 at hp
    rw [hz] at hp
    norm_num at hp
  have hsub : Bᶜ ⊆ Set.range vertexModelSource := by
    intro q hq
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    obtain ⟨i, r, t, hirt⟩ := radialSector_surjective x
    have hsmall : sectorLocalRadius r t ≤ 1 / 4 := by
      by_contra hn
      apply hq
      apply Set.mem_iUnion.mpr
      refine ⟨i, (r, t), ?_, congrArg mk hirt⟩
      exact le_of_lt (lt_of_not_ge hn)
    obtain ⟨k, hk⟩ := vertexCycle_bijective.2 i
    refine ⟨(k, ⟨(r, t), hsmall⟩), ?_⟩
    change mk (radialSector (vertexCycle k) r t) = mk x
    rw [hk, hirt]
  apply interior_mono hsub
  rwa [hB.isOpen_compl.interior_eq]

end CurveComplex.Octagon
