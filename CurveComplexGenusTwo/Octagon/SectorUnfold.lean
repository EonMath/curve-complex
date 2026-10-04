import CurveComplexGenusTwo.Octagon.VertexChart

namespace CurveComplex.Octagon

/-! Algebraic coordinates for the eight source sectors.  The real pair is the
   tangent/normal coordinate at a polygon vertex.  Its positive tangent ray is
   the outgoing half-edge, and its negative ray is the incoming half-edge. -/

noncomputable def sectorVector (r t : unitInterval) : ℝ × ℝ :=
  ((t : ℝ) - 1 / 2, (r : ℝ))

noncomputable def sectorVectorInverse (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.2, v.1 + 1 / 2)

theorem sectorVector_inverse (r t : unitInterval) :
    sectorVectorInverse (sectorVector r t) = ((r : ℝ), (t : ℝ)) := by
  simp [sectorVector, sectorVectorInverse]

theorem sectorVectorInverse_left (v : ℝ × ℝ) :
    ((sectorVectorInverse v).2 - 1 / 2, (sectorVectorInverse v).1) = v := by
  rcases v with ⟨x, y⟩
  simp [sectorVectorInverse]

noncomputable def sectorLocalComplex (r t : unitInterval) : ℂ :=
  ((t : ℝ) - 1 / 2 : ℝ) + (r : ℝ) * Complex.I

theorem sectorLocalComplex_re (r t : unitInterval) :
    (sectorLocalComplex r t).re = (t : ℝ) - 1 / 2 := by
  simp [sectorLocalComplex]

theorem sectorLocalComplex_im (r t : unitInterval) :
    (sectorLocalComplex r t).im = (r : ℝ) := by
  simp [sectorLocalComplex]

noncomputable def sectorLocalRadius (r t : unitInterval) : ℝ :=
  ‖sectorLocalComplex r t‖

noncomputable def sectorLocalAngle (r t : unitInterval) : ℝ :=
  Complex.arg (sectorLocalComplex r t)

theorem sectorLocalAngle_nonneg (r t : unitInterval) :
    0 ≤ sectorLocalAngle r t := by
  rw [sectorLocalAngle, Complex.arg_nonneg_iff, sectorLocalComplex_im]
  exact r.property.1

theorem sectorLocalAngle_le_pi (r t : unitInterval) :
    sectorLocalAngle r t ≤ Real.pi := by
  exact Complex.arg_le_pi _

theorem sectorLocal_radius_cos (r t : unitInterval) :
    sectorLocalRadius r t * Real.cos (sectorLocalAngle r t) =
      (t : ℝ) - 1 / 2 := by
  simp [sectorLocalRadius, sectorLocalAngle, sectorLocalComplex_re]

theorem sectorLocal_radius_sin (r t : unitInterval) :
    sectorLocalRadius r t * Real.sin (sectorLocalAngle r t) =
      (r : ℝ) := by
  simp [sectorLocalRadius, sectorLocalAngle, sectorLocalComplex_im]

theorem sectorLocal_polar_inverse (r t : unitInterval) :
    (sectorLocalRadius r t * Real.sin (sectorLocalAngle r t),
      sectorLocalRadius r t * Real.cos (sectorLocalAngle r t) + 1 / 2) =
        ((r : ℝ), (t : ℝ)) := by
  simp [sectorLocal_radius_sin, sectorLocal_radius_cos]

/-- A radial coefficient for `radialSector`; the inverse is literal subtraction. -/
def sectorRadial (r : unitInterval) : ℝ := 1 - r

theorem sectorRadial_inverse (r : unitInterval) : 1 - sectorRadial r = (r : ℝ) := by
  simp [sectorRadial]

theorem sectorRadial_nonneg (r : unitInterval) : 0 ≤ sectorRadial r := by
  unfold sectorRadial
  linarith [r.property.2]

theorem sectorRadial_pos {r : unitInterval} (hr : r ≠ 1) : 0 < sectorRadial r := by
  have hrne : (r : ℝ) ≠ 1 := by
    intro h
    exact hr (Subtype.ext h)
  exact sub_pos.mpr (lt_of_le_of_ne r.property.2 hrne)

/-- The norm recovers the radial coefficient of the geometric source sector. -/
theorem radialSector_norm (i : Side) (r t : unitInterval) :
    ‖(radialSector i r t : ℂ)‖ = sectorRadial r := by
  change ‖(1 - (r : ℝ)) •
      (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (t : ℝ) - 1 / 2) / 8) : ℂ)‖ =
    sectorRadial r
  rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs]
  rw [abs_of_nonneg (by simpa [sectorRadial] using sectorRadial_nonneg r)]
  rfl

theorem radialSector_radial_inverse (i : Side) (r t : unitInterval) :
    1 - ‖(radialSector i r t : ℂ)‖ = (r : ℝ) := by
  rw [radialSector_norm]
  exact sectorRadial_inverse r

theorem radialSector_eq_implies_radial_eq (i j : Side) (r s t u : unitInterval)
    (h : radialSector i r t = radialSector j s u) : r = s := by
  apply Subtype.ext
  have hn := congrArg (fun x : Disk => ‖(x : ℂ)‖) h
  rw [radialSector_norm, radialSector_norm] at hn
  dsimp [sectorRadial] at hn
  linarith

/-- The normalized angular coordinate of one source sector. -/
noncomputable def sectorSourceAngle (i : Side) (t : unitInterval) : ℝ :=
  (i.val : ℝ) + t - 1 / 2

theorem sectorSourceAngle_inverse (i : Side) (t : unitInterval) :
    sectorSourceAngle i t - i.val + 1 / 2 = (t : ℝ) := by
  unfold sectorSourceAngle
  ring

theorem sectorSourceAngle_injective (i : Side) :
    Function.Injective (sectorSourceAngle i) := by
  intro t u h
  apply Subtype.ext
  have ht := sectorSourceAngle_inverse i t
  have hu := sectorSourceAngle_inverse i u
  linarith

/-- Eight indexed source sheets, in their original radial/angle coordinates.
    This records the algebra before the quotient folds paired half-edges. -/
noncomputable def indexedSectorCoordinates (k : Fin 8)
    (p : unitInterval × unitInterval) : ℝ × ℝ :=
  (sectorRadial p.1, sectorSourceAngle (vertexCycle k) p.2)

noncomputable def indexedSectorInverse (k : Fin 8) (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - p.1, p.2 - (vertexCycle k).val + 1 / 2)

theorem indexedSectorInverse_apply (k : Fin 8) (r t : unitInterval) :
    indexedSectorInverse k (indexedSectorCoordinates k (r, t)) =
      ((r : ℝ), (t : ℝ)) := by
  apply Prod.ext
  · exact sectorRadial_inverse r
  · exact sectorSourceAngle_inverse (vertexCycle k) t

theorem indexedSectorCoordinates_inverse (k : Fin 8) (p : ℝ × ℝ) :
    (1 - (indexedSectorInverse k p).1,
      (vertexCycle k).val + (indexedSectorInverse k p).2 - 1 / 2) = p := by
  rcases p with ⟨ρ, θ⟩
  simp [indexedSectorInverse]
  ring

theorem radialSector_angular_inverse (i : Side) (r t u : unitInterval)
    (hr : r ≠ 1) (h : radialSector i r t = radialSector i r u) : t = u := by
  have hpos : 0 < sectorRadial r := sectorRadial_pos hr
  have hcomplex :
      (Circle.exp (2 * Real.pi * sectorSourceAngle i t / 8) : ℂ) =
        (Circle.exp (2 * Real.pi * sectorSourceAngle i u / 8) : ℂ) := by
    have hh := congrArg (fun x : Disk => (x : ℂ)) h
    change (1 - (r : ℝ)) •
      (Circle.exp (2 * Real.pi * sectorSourceAngle i t / 8) : ℂ) =
      (1 - (r : ℝ)) •
      (Circle.exp (2 * Real.pi * sectorSourceAngle i u / 8) : ℂ) at hh
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_eq_mul, smul_eq_mul] at hh
    have hreal : (1 - (r : ℝ)) ≠ 0 := by
      simpa [sectorRadial] using ne_of_gt hpos
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hreal) hh
  have hcircle : Circle.exp (2 * Real.pi * sectorSourceAngle i t / 8) =
      Circle.exp (2 * Real.pi * sectorSourceAngle i u / 8) :=
    Circle.ext hcomplex
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hcircle
  have hang : (t : ℝ) = u + 8 * (m : ℝ) := by
    have h' := hm
    dsimp [sectorSourceAngle] at h'
    field_simp [Real.pi_ne_zero] at h'
    nlinarith [h']
  have hm0 : m = 0 := by
    by_contra hmne
    rcases lt_or_gt_of_ne hmne with hneg | hpos
    · have hle : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      linarith [t.property.1, u.property.2]
    · have hge : (m : ℝ) ≥ 1 := by exact_mod_cast (show m ≥ 1 by omega)
      linarith [t.property.2, u.property.1]
  apply Subtype.ext
  simpa [hm0] using hang

theorem radialSector_injective_fixed_side (i : Side) (r s t u : unitInterval)
    (hr : r ≠ 1) (h : radialSector i r t = radialSector i s u) :
    r = s ∧ t = u := by
  have hrs := radialSector_eq_implies_radial_eq i i r s t u h
  subst s
  exact ⟨rfl, radialSector_angular_inverse i r t u hr h⟩

/-! A common seam parameter `s` runs from a vertex to the midpoint of its
    outgoing edge.  Reversal sends it to the incoming half-edge at the next
    sector in `vertexCycle`. -/

noncomputable def seamHalf (s : unitInterval) : unitInterval :=
  ⟨(s : ℝ) / 2, by
    constructor
    · exact div_nonneg s.property.1 (by norm_num)
    · linarith [s.property.2]⟩

noncomputable def outgoingHalf (s : unitInterval) : unitInterval :=
  ⟨(1 + (s : ℝ)) / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩

noncomputable def incomingHalf (s : unitInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩

theorem outgoingHalf_angle (i : Side) (s : unitInterval) :
    sectorSourceAngle i (outgoingHalf s) = (i.val : ℝ) + s / 2 := by
  simp [sectorSourceAngle, outgoingHalf]
  ring

theorem incomingHalf_angle (i : Side) (s : unitInterval) :
    sectorSourceAngle i (incomingHalf s) = (i.val : ℝ) - s / 2 := by
  simp [sectorSourceAngle, incomingHalf]
  ring

theorem sectorVector_outgoing (s : unitInterval) :
    sectorVector 0 (outgoingHalf s) = ((s : ℝ) / 2, 0) := by
  apply Prod.ext
  · change (1 + (s : ℝ)) / 2 - 1 / 2 = s / 2
    ring
  · rfl

theorem sectorVector_incoming (s : unitInterval) :
    sectorVector 0 (incomingHalf s) = (-(s : ℝ) / 2, 0) := by
  apply Prod.ext
  · change (1 - (s : ℝ)) / 2 - 1 / 2 = -s / 2
    ring
  · rfl

theorem sectorLocalComplex_outgoing (s : unitInterval) :
    sectorLocalComplex 0 (outgoingHalf s) = ((s : ℝ) / 2 : ℂ) := by
  apply Complex.ext
  · simp [sectorLocalComplex, outgoingHalf]
    ring
  · simp [sectorLocalComplex]

theorem sectorLocalComplex_incoming (s : unitInterval) :
    sectorLocalComplex 0 (incomingHalf s) = (-(s : ℝ) / 2 : ℂ) := by
  apply Complex.ext
  · simp [sectorLocalComplex, incomingHalf]
    ring
  · simp [sectorLocalComplex]

theorem sectorLocalRadius_outgoing (s : unitInterval) :
    sectorLocalRadius 0 (outgoingHalf s) = (s : ℝ) / 2 := by
  simp [sectorLocalRadius, sectorLocalComplex_outgoing,
    Real.norm_eq_abs, abs_of_nonneg s.property.1]

theorem sectorLocalRadius_incoming (s : unitInterval) :
    sectorLocalRadius 0 (incomingHalf s) = (s : ℝ) / 2 := by
  simp [sectorLocalRadius, sectorLocalComplex_incoming,
    Real.norm_eq_abs, abs_of_nonneg s.property.1]

theorem sectorLocalAngle_outgoing (s : unitInterval) :
    sectorLocalAngle 0 (outgoingHalf s) = 0 := by
  rw [sectorLocalAngle, sectorLocalComplex_outgoing]
  convert Complex.arg_ofReal_of_nonneg
    (div_nonneg s.property.1 (by norm_num : (0 : ℝ) ≤ 2)) using 1
  norm_num

theorem sectorLocalAngle_incoming (s : unitInterval) (hs : s ≠ 0) :
    sectorLocalAngle 0 (incomingHalf s) = Real.pi := by
  have hspos : (0 : ℝ) < s := by
    have hsne : (s : ℝ) ≠ 0 := by
      intro h
      exact hs (Subtype.ext h)
    exact lt_of_le_of_ne s.property.1 (Ne.symm hsne)
  rw [sectorLocalAngle, sectorLocalComplex_incoming]
  simpa only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat] using
    (Complex.arg_ofReal_of_neg (show -(s : ℝ) / 2 < 0 by linarith))

/-- Explicit planar unfolding: each source half-plane uses one eighth of the
    full turn; the local polar angle is reversed so paired half-edges meet. -/
noncomputable def sectorUnfoldAngle (k : Fin 8) (r t : unitInterval) : ℝ :=
  2 * Real.pi * ((k.val : ℝ) + 1 - sectorLocalAngle r t / Real.pi) / 8

theorem sectorUnfoldAngle_bounds (k : Fin 8) (r t : unitInterval) :
    2 * Real.pi * (k.val : ℝ) / 8 ≤ sectorUnfoldAngle k r t ∧
      sectorUnfoldAngle k r t ≤ 2 * Real.pi * ((k.val : ℝ) + 1) / 8 := by
  have hθ0 := sectorLocalAngle_nonneg r t
  have hθ1 := sectorLocalAngle_le_pi r t
  have hpi := Real.pi_pos
  have hq0 : 0 ≤ sectorLocalAngle r t / Real.pi := div_nonneg hθ0 hpi.le
  have hq1 : sectorLocalAngle r t / Real.pi ≤ 1 :=
    (div_le_one hpi).mpr hθ1
  unfold sectorUnfoldAngle
  constructor <;> nlinarith

noncomputable def sectorUnfoldPoint (k : Fin 8) (r t : unitInterval) : ℂ :=
  sectorLocalRadius r t • (Circle.exp (sectorUnfoldAngle k r t) : ℂ)

theorem sectorUnfoldPoint_norm (k : Fin 8) (r t : unitInterval) :
    ‖sectorUnfoldPoint k r t‖ = sectorLocalRadius r t := by
  rw [sectorUnfoldPoint, norm_smul, Circle.norm_coe, mul_one,
    Real.norm_eq_abs]
  rw [abs_of_nonneg (show 0 ≤ sectorLocalRadius r t from norm_nonneg _)]

theorem sectorUnfoldPoint_polar_inverse (k : Fin 8) (r t : unitInterval) :
    (‖sectorUnfoldPoint k r t‖ * Real.sin (sectorLocalAngle r t),
      ‖sectorUnfoldPoint k r t‖ * Real.cos (sectorLocalAngle r t) + 1 / 2) =
        ((r : ℝ), (t : ℝ)) := by
  rw [sectorUnfoldPoint_norm]
  exact sectorLocal_polar_inverse r t

theorem sectorUnfoldPoint_injective_fixed_sector (k : Fin 8)
    (r s t u : unitInterval)
    (h : sectorUnfoldPoint k r t = sectorUnfoldPoint k s u) :
    r = s ∧ t = u := by
  have hρ : sectorLocalRadius r t = sectorLocalRadius s u := by
    have hn := congrArg (fun z : ℂ => ‖z‖) h
    simpa only [sectorUnfoldPoint_norm] using hn
  have hcoords (ha : sectorLocalAngle r t = sectorLocalAngle s u) :
      r = s ∧ t = u := by
    constructor
    · apply Subtype.ext
      have hr := sectorLocal_radius_sin r t
      have hs := sectorLocal_radius_sin s u
      rw [hρ, ha] at hr
      linarith
    · apply Subtype.ext
      have ht := sectorLocal_radius_cos r t
      have hu := sectorLocal_radius_cos s u
      rw [hρ, ha] at ht
      linarith
  by_cases hzero : sectorLocalRadius r t = 0
  · have hzero' : sectorLocalRadius s u = 0 := hρ ▸ hzero
    constructor
    · apply Subtype.ext
      have hr := sectorLocal_radius_sin r t
      have hs := sectorLocal_radius_sin s u
      rw [hzero] at hr
      rw [hzero'] at hs
      linarith
    · apply Subtype.ext
      have ht := sectorLocal_radius_cos r t
      have hu := sectorLocal_radius_cos s u
      rw [hzero] at ht
      rw [hzero'] at hu
      linarith
  · have hcomplex :
        (Circle.exp (sectorUnfoldAngle k r t) : ℂ) =
          (Circle.exp (sectorUnfoldAngle k s u) : ℂ) := by
      unfold sectorUnfoldPoint at h
      rw [hρ] at h
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
        RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul, smul_eq_mul] at h
      have hzero' : sectorLocalRadius s u ≠ 0 := by
        rw [← hρ]
        exact hzero
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hzero') h
    have hcircle : Circle.exp (sectorUnfoldAngle k r t) =
        Circle.exp (sectorUnfoldAngle k s u) := Circle.ext hcomplex
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hcircle
    have hb₁ := sectorUnfoldAngle_bounds k r t
    have hb₂ := sectorUnfoldAngle_bounds k s u
    have hpi := Real.pi_pos
    have hm0 : m = 0 := by
      by_contra hmne
      rcases lt_or_gt_of_ne hmne with hneg | hpos
      · have hmle : (m : ℝ) ≤ -1 := by
          exact_mod_cast (show m ≤ -1 by omega)
        nlinarith [hm]
      · have hmge : (m : ℝ) ≥ 1 := by
          exact_mod_cast (show m ≥ 1 by omega)
        nlinarith [hm]
    have hangle : sectorUnfoldAngle k r t = sectorUnfoldAngle k s u := by
      simpa [hm0] using hm
    have hlocal : sectorLocalAngle r t = sectorLocalAngle s u := by
      unfold sectorUnfoldAngle at hangle
      field_simp [Real.pi_ne_zero] at hangle
      nlinarith [hangle]
    exact hcoords hlocal

theorem sectorUnfoldAngle_outgoing (k : Fin 8) (s : unitInterval) :
    sectorUnfoldAngle k 0 (outgoingHalf s) =
      2 * Real.pi * ((k.val : ℝ) + 1) / 8 := by
  simp [sectorUnfoldAngle, sectorLocalAngle_outgoing]

theorem sectorUnfoldAngle_incoming (k : Fin 8) (s : unitInterval)
    (hs : s ≠ 0) :
    sectorUnfoldAngle k 0 (incomingHalf s) =
      2 * Real.pi * (k.val : ℝ) / 8 := by
  rw [sectorUnfoldAngle, sectorLocalAngle_incoming s hs,
    div_self Real.pi_ne_zero]
  ring

/-- The explicit planar map agrees on the two source representatives of each
    nonvertex seam; at the final seam the angles differ by a full turn. -/
theorem sectorUnfoldPoint_seam (k : Fin 8) (s : unitInterval) (hs : s ≠ 0) :
    sectorUnfoldPoint k 0 (outgoingHalf s) =
      sectorUnfoldPoint (next k) 0 (incomingHalf s) := by
  unfold sectorUnfoldPoint
  rw [sectorLocalRadius_outgoing, sectorLocalRadius_incoming,
    sectorUnfoldAngle_outgoing, sectorUnfoldAngle_incoming (next k) s hs]
  congr 1
  apply congrArg (fun c : Circle => (c : ℂ))
  apply Circle.exp_eq_exp.mpr
  fin_cases k
  case «7» =>
    refine ⟨1, ?_⟩
    simp [next]
    ring
  all_goals
    refine ⟨0, ?_⟩
    simp [next] <;> ring

theorem sectorUnfoldPoint_seam_all (k : Fin 8) (s : unitInterval) :
    sectorUnfoldPoint k 0 (outgoingHalf s) =
      sectorUnfoldPoint (next k) 0 (incomingHalf s) := by
  by_cases hs : s = 0
  · subst s
    unfold sectorUnfoldPoint
    rw [sectorLocalRadius_outgoing, sectorLocalRadius_incoming]
    norm_num
  · exact sectorUnfoldPoint_seam k s hs

theorem radialSector_outgoing_eq_side (i : Side) (s : unitInterval) :
    radialSector i 0 (outgoingHalf s) = side i (seamHalf s) := by
  apply Subtype.ext
  change (1 - (0 : ℝ)) •
      (Circle.exp (2 * Real.pi * sectorSourceAngle i (outgoingHalf s) / 8) : ℂ) =
    (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (seamHalf s : ℝ)) / 8) : ℂ)
  rw [outgoingHalf_angle]
  simp [seamHalf]

theorem radialSector_incoming_eq_side (i : Side) (s : unitInterval) :
    radialSector (vertexSuccessor i) 0 (incomingHalf s) =
      side (pair i) (unitInterval.symm (seamHalf s)) := by
  apply Subtype.ext
  change (1 - (0 : ℝ)) •
      (Circle.exp (2 * Real.pi * sectorSourceAngle (vertexSuccessor i)
        (incomingHalf s) / 8) : ℂ) =
    (Circle.exp (2 * Real.pi * ((pair i).val +
      (unitInterval.symm (seamHalf s) : ℝ)) / 8) : ℂ)
  rw [incomingHalf_angle]
  simp only [sub_zero, one_smul]
  apply congrArg (fun c : Circle => (c : ℂ))
  apply Circle.exp_eq_exp.mpr
  fin_cases i
  case «5» =>
    refine ⟨-1, ?_⟩
    simp [vertexSuccessor, next, pair, seamHalf, unitInterval.symm]
    ring
  all_goals
    refine ⟨0, ?_⟩
    simp [vertexSuccessor, next, pair, seamHalf, unitInterval.symm] <;> ring

theorem radialSector_seam_quotient (k : Fin 8) (s : unitInterval) :
    mk (radialSector (vertexCycle k) 0 (outgoingHalf s)) =
      mk (radialSector (vertexCycle (next k)) 0 (incomingHalf s)) := by
  rw [radialSector_outgoing_eq_side, vertexCycle_next,
    radialSector_incoming_eq_side]
  exact side_pairing (vertexCycle k) (seamHalf s)

/-- Away from the common vertex, the seam has precisely the two displayed
    source representatives. -/
theorem radialSector_seam_exact_fiber (k : Fin 8) (s : unitInterval)
    (hs : s ≠ 0) :
    mk ⁻¹' ({mk (radialSector (vertexCycle k) 0 (outgoingHalf s))} : Set Surface) =
      {radialSector (vertexCycle k) 0 (outgoingHalf s),
       radialSector (vertexCycle (next k)) 0 (incomingHalf s)} := by
  have hs0 : seamHalf s ≠ 0 := by
    intro h
    have hval := congrArg (fun x : unitInterval => (x : ℝ)) h
    have hsval : (s : ℝ) = 0 := by
      simpa [seamHalf] using (show (s : ℝ) / 2 = 0 by simpa [seamHalf] using hval)
    exact hs (Subtype.ext hsval)
  have hs1 : seamHalf s ≠ 1 := by
    intro h
    have hval := congrArg (fun x : unitInterval => (x : ℝ)) h
    have hsle := s.property.2
    simp [seamHalf] at hval
    linarith
  rw [radialSector_outgoing_eq_side,
    show radialSector (vertexCycle (next k)) 0 (incomingHalf s) =
      side (pair (vertexCycle k)) (unitInterval.symm (seamHalf s)) by
        rw [vertexCycle_next]
        exact radialSector_incoming_eq_side (vertexCycle k) s]
  exact vertex_seam_exact_fiber (vertexCycle k) (seamHalf s) hs0 hs1

end CurveComplex.Octagon
