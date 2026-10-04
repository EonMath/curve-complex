import CurveComplexGenusTwo.Cover.HemisphereAttaching

namespace AlternatingSphereCover

abbrev CoordinateDisk :=
  {v : EuclideanSpace ℝ (Fin 2) // (v 0)^2 + (v 1)^2 ≤ 1}

theorem coordinate_disk_iff_closedBall (v : EuclideanSpace ℝ (Fin 2)) :
    (v 0)^2 + (v 1)^2 ≤ 1 ↔
      v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  have hn : ‖v‖^2 = (v 0)^2 + (v 1)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
  rw [Metric.mem_closedBall, dist_zero_right]
  constructor <;> intro h <;> nlinarith [norm_nonneg v]

noncomputable def coordinateDiskClosedBallHomeomorph :
    CoordinateDisk ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  apply Homeomorph.setCongr
  ext v
  exact coordinate_disk_iff_closedBall v

theorem sphere_coordinate_squares (p : Sphere) :
    (p.val 0)^2 + (p.val 1)^2 + (p.val 2)^2 = 1 := by
  have hp : ‖p.val‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using p.property
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) p.val
  rw [hp] at hn
  simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc] using hn.symm

def horizontal (p : Sphere) : EuclideanSpace ℝ (Fin 2) :=
  !₂[p.val 0, p.val 1]

theorem horizontal_mem_disk (p : Sphere) :
    (horizontal p 0)^2 + (horizontal p 1)^2 ≤ 1 := by
  have h := sphere_coordinate_squares p
  dsimp [horizontal]
  nlinarith [sq_nonneg (p.val 2)]

def diskProjection (p : Sphere) : CoordinateDisk :=
  ⟨horizontal p, horizontal_mem_disk p⟩

theorem diskProjection_continuous : Continuous diskProjection := by
  apply Continuous.subtype_mk
  unfold horizontal
  fun_prop

def northDiskProjection (p : NorthHemisphere) : CoordinateDisk :=
  diskProjection p.val

theorem northDiskProjection_continuous : Continuous northDiskProjection :=
  diskProjection_continuous.comp continuous_subtype_val

theorem northDiskProjection_injective : Function.Injective northDiskProjection := by
  intro p q h
  have h0 := congrArg (fun v : CoordinateDisk => v.val 0) h
  have h1 := congrArg (fun v : CoordinateDisk => v.val 1) h
  have hsq1 := sphere_coordinate_squares p.val
  have hsq2 := sphere_coordinate_squares q.val
  have hz : p.val.val 2 = q.val.val 2 := by
    have hn1 : 0 ≤ p.val.val 2 := p.property
    have hn2 : 0 ≤ q.val.val 2 := q.property
    dsimp [northDiskProjection, diskProjection, horizontal] at h0 h1
    have hzsq : (p.val.val 2)^2 = (q.val.val 2)^2 := by
      rw [h0, h1] at hsq1
      linarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hzsq with heq | heq
    · exact heq
    · nlinarith
  apply Subtype.ext
  apply Subtype.ext
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact hz

noncomputable def northDiskLift (v : CoordinateDisk) : NorthHemisphere := by
  let z : ℝ := Real.sqrt (1 - (v.val 0)^2 - (v.val 1)^2)
  have hzsq : z^2 = 1 - (v.val 0)^2 - (v.val 1)^2 := by
    apply Real.sq_sqrt
    nlinarith [v.property]
  have hn : ‖(!₂[v.val 0, v.val 1, z] : EuclideanSpace ℝ (Fin 3))‖^2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
    nlinarith
  have hnorm : ‖(!₂[v.val 0, v.val 1, z] : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    nlinarith [norm_nonneg (!₂[v.val 0, v.val 1, z] : EuclideanSpace ℝ (Fin 3))]
  exact ⟨⟨!₂[v.val 0, v.val 1, z], by simpa [Metric.mem_sphere, dist_zero_right] using hnorm⟩,
    by exact Real.sqrt_nonneg _⟩

theorem northDiskProjection_surjective : Function.Surjective northDiskProjection := by
  intro v
  refine ⟨northDiskLift v, ?_⟩
  apply Subtype.ext
  ext i
  fin_cases i <;> rfl

private instance : CompactSpace NorthHemisphere := by
  have hc : IsClosed {p : Sphere | 0 ≤ height p} :=
    isClosed_le continuous_const height_continuous
  exact isCompact_iff_compactSpace.mp hc.isCompact

noncomputable def northDiskEquiv : NorthHemisphere ≃ CoordinateDisk :=
  Equiv.ofBijective northDiskProjection
    ⟨northDiskProjection_injective, northDiskProjection_surjective⟩

noncomputable def northHemisphereDiskHomeomorph :
    NorthHemisphere ≃ₜ CoordinateDisk :=
  (show Continuous (northDiskEquiv : NorthHemisphere → CoordinateDisk) from
    northDiskProjection_continuous).homeoOfEquivCompactToT2

def southDiskProjection (p : SouthHemisphere) : CoordinateDisk :=
  diskProjection p.val

theorem southDiskProjection_continuous : Continuous southDiskProjection :=
  diskProjection_continuous.comp continuous_subtype_val

theorem southDiskProjection_injective : Function.Injective southDiskProjection := by
  intro p q h
  have h0 := congrArg (fun v : CoordinateDisk => v.val 0) h
  have h1 := congrArg (fun v : CoordinateDisk => v.val 1) h
  have hsq1 := sphere_coordinate_squares p.val
  have hsq2 := sphere_coordinate_squares q.val
  have hz : p.val.val 2 = q.val.val 2 := by
    have hn1 : p.val.val 2 ≤ 0 := p.property
    have hn2 : q.val.val 2 ≤ 0 := q.property
    dsimp [southDiskProjection, diskProjection, horizontal] at h0 h1
    have hzsq : (p.val.val 2)^2 = (q.val.val 2)^2 := by
      rw [h0, h1] at hsq1
      linarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hzsq with heq | heq
    · exact heq
    · nlinarith
  apply Subtype.ext
  apply Subtype.ext
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact hz

noncomputable def southDiskLift (v : CoordinateDisk) : SouthHemisphere := by
  let z : ℝ := -Real.sqrt (1 - (v.val 0)^2 - (v.val 1)^2)
  have hzsq : z^2 = 1 - (v.val 0)^2 - (v.val 1)^2 := by
    dsimp [z]
    rw [neg_sq, Real.sq_sqrt (by nlinarith [v.property])]
  have hn : ‖(!₂[v.val 0, v.val 1, z] : EuclideanSpace ℝ (Fin 3))‖^2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
    nlinarith
  have hnorm : ‖(!₂[v.val 0, v.val 1, z] : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    nlinarith [norm_nonneg (!₂[v.val 0, v.val 1, z] : EuclideanSpace ℝ (Fin 3))]
  exact ⟨⟨!₂[v.val 0, v.val 1, z], by simpa [Metric.mem_sphere, dist_zero_right] using hnorm⟩,
    by exact neg_nonpos.mpr (Real.sqrt_nonneg _)⟩

theorem southDiskProjection_surjective : Function.Surjective southDiskProjection := by
  intro v
  refine ⟨southDiskLift v, ?_⟩
  apply Subtype.ext
  ext i
  fin_cases i <;> rfl

private instance : CompactSpace SouthHemisphere := by
  have hc : IsClosed {p : Sphere | height p ≤ 0} :=
    isClosed_le height_continuous continuous_const
  exact isCompact_iff_compactSpace.mp hc.isCompact

noncomputable def southDiskEquiv : SouthHemisphere ≃ CoordinateDisk :=
  Equiv.ofBijective southDiskProjection
    ⟨southDiskProjection_injective, southDiskProjection_surjective⟩

noncomputable def southHemisphereDiskHomeomorph :
    SouthHemisphere ≃ₜ CoordinateDisk :=
  (show Continuous (southDiskEquiv : SouthHemisphere → CoordinateDisk) from
    southDiskProjection_continuous).homeoOfEquivCompactToT2

/-- Standard closed-ball characteristic maps for all four faces. -/
noncomputable def northDiskFace (sheet : Bool)
    (v : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) : Total :=
  northFace sheet (northHemisphereDiskHomeomorph.symm
    (coordinateDiskClosedBallHomeomorph.symm v))

noncomputable def southDiskFace (sheet : Bool)
    (v : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) : Total :=
  southFace sheet (southHemisphereDiskHomeomorph.symm
    (coordinateDiskClosedBallHomeomorph.symm v))

theorem northDiskFace_continuous (sheet : Bool) : Continuous (northDiskFace sheet) :=
  (northFace_continuous sheet).comp
    (northHemisphereDiskHomeomorph.symm.continuous.comp
      coordinateDiskClosedBallHomeomorph.symm.continuous)

theorem southDiskFace_continuous (sheet : Bool) : Continuous (southDiskFace sheet) :=
  (southFace_continuous sheet).comp
    (southHemisphereDiskHomeomorph.symm.continuous.comp
      coordinateDiskClosedBallHomeomorph.symm.continuous)

theorem northDiskFace_injective (sheet : Bool) :
    Function.Injective (northDiskFace sheet) :=
  (northFace_injective sheet).comp
    (northHemisphereDiskHomeomorph.symm.injective.comp
      coordinateDiskClosedBallHomeomorph.symm.injective)

theorem southDiskFace_injective (sheet : Bool) :
    Function.Injective (southDiskFace sheet) :=
  (southFace_injective sheet).comp
    (southHemisphereDiskHomeomorph.symm.injective.comp
      coordinateDiskClosedBallHomeomorph.symm.injective)

/-- Counterclockwise order, starting at the positive horizontal axis. -/
def cyclicBranch (i : Fin 6) : Fin 6 := (![0, 2, 4, 1, 5, 3]) i

def uncyclicBranch (i : Fin 6) : Fin 6 := (![0, 3, 1, 5, 2, 4]) i

theorem uncyclic_cyclic (i : Fin 6) :
    uncyclicBranch (cyclicBranch i) = i := by
  fin_cases i <;> decide

theorem cyclic_uncyclic (i : Fin 6) :
    cyclicBranch (uncyclicBranch i) = i := by
  fin_cases i <;> decide

def cyclicBranchEquiv : Fin 6 ≃ Fin 6 where
  toFun := cyclicBranch
  invFun := uncyclicBranch
  left_inv := uncyclic_cyclic
  right_inv := cyclic_uncyclic

noncomputable def boundaryVertex (i : Fin 6) : CoordinateDisk :=
  diskProjection (branchPoint (cyclicBranch i))

theorem branchPoint_height_zero (i : Fin 6) : height (branchPoint i) = 0 := by
  fin_cases i <;> norm_num [height, branchPoint, branchVector]

theorem boundaryVertex_on_circle (i : Fin 6) :
    (boundaryVertex i).val 0 ^ 2 + (boundaryVertex i).val 1 ^ 2 = 1 := by
  have hs := sphere_coordinate_squares (branchPoint (cyclicBranch i))
  have hz := branchPoint_height_zero (cyclicBranch i)
  dsimp [boundaryVertex, diskProjection, horizontal]
  dsimp [height] at hz
  nlinarith

theorem boundaryVertex_injective : Function.Injective boundaryVertex := by
  intro i j h
  have h0 := congrArg (fun v : CoordinateDisk => v.val 0) h
  have h1 := congrArg (fun v : CoordinateDisk => v.val 1) h
  have hp : branchPoint (cyclicBranch i) = branchPoint (cyclicBranch j) := by
    apply Subtype.ext
    ext k
    fin_cases k
    · simpa [boundaryVertex, diskProjection, horizontal] using h0
    · simpa [boundaryVertex, diskProjection, horizontal] using h1
    · simpa [height] using
        (branchPoint_height_zero (cyclicBranch i)).trans
          (branchPoint_height_zero (cyclicBranch j)).symm
  exact cyclicBranchEquiv.injective (branchPoint_injective hp)

theorem branch_iff_cyclic_vertex (p : Sphere) :
    branch p ↔ ∃ i : Fin 6, p = branchPoint (cyclicBranch i) := by
  rw [branch_iff_mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨uncyclicBranch j, by rw [cyclic_uncyclic]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨cyclicBranch i, rfl⟩

noncomputable def seamA (p : Sphere) : ℝ := Real.sqrt 3 * p.val 0 - p.val 1
noncomputable def seamB (p : Sphere) : ℝ := Real.sqrt 3 * p.val 0 + p.val 1

theorem seamPolynomial_factor (p : Sphere) :
    seamPolynomial p = p.val 1 * seamA p * seamB p := by
  have hs : (Real.sqrt (3 : ℝ))^2 = 3 := Real.sq_sqrt (by norm_num)
  unfold seamPolynomial seamA seamB
  calc
    p.val 1 * (3 * p.val 0 ^ 2 - p.val 1 ^ 2) =
        p.val 1 * ((Real.sqrt 3)^2 * p.val 0 ^ 2 - p.val 1 ^ 2) := by rw [hs]
    _ = p.val 1 * (Real.sqrt 3 * p.val 0 - p.val 1) *
        (Real.sqrt 3 * p.val 0 + p.val 1) := by ring

/-- The six open sectors of the equatorial disk boundary, in cyclic order. -/
noncomputable def arcSector (i : Fin 6) (p : Sphere) : Prop :=
  height p = 0 ∧
  match i.val with
  | 0 => 0 < p.val 1 ∧ 0 < seamA p ∧ 0 < seamB p
  | 1 => 0 < p.val 1 ∧ seamA p < 0 ∧ 0 < seamB p
  | 2 => 0 < p.val 1 ∧ seamA p < 0 ∧ seamB p < 0
  | 3 => p.val 1 < 0 ∧ seamA p < 0 ∧ seamB p < 0
  | 4 => p.val 1 < 0 ∧ 0 < seamA p ∧ seamB p < 0
  | _ => p.val 1 < 0 ∧ 0 < seamA p ∧ 0 < seamB p

theorem arcSector_nonbranch {i : Fin 6} {p : Sphere} (h : arcSector i p) :
    ¬ branch p := by
  intro hb
  have hprod : p.val 1 * seamA p * seamB p = 0 := by
    rw [← seamPolynomial_factor]
    exact hb.2
  fin_cases i <;> dsimp [arcSector] at h <;>
    rcases h with ⟨_, h1, h2, h3⟩ <;>
    simp only [mul_eq_zero] at hprod <;>
    rcases hprod with (h1z | h2z) | h3z <;> linarith

theorem arcSector_alternating_sign {i : Fin 6} {p : Sphere}
    (h : arcSector i p) :
    (0 < seamPolynomial p ↔ i.val % 2 = 0) := by
  fin_cases i <;> dsimp [arcSector] at h <;>
    rcases h with ⟨_, h1, h2, h3⟩ <;>
    rw [seamPolynomial_factor] <;>
    norm_num <;>
    first
    | exact mul_pos (mul_pos h1 h2) h3
    | exact le_of_lt (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h1 h2) h3)
    | exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg h1 h2) h3
    | exact le_of_lt (mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg h1 h2) h3)
    | exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos h1 h2) h3
    | exact le_of_lt (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h1 h2) h3)

theorem arcSector_exists {p : Sphere} (hh : height p = 0)
    (hb : ¬ branch p) : ∃ i : Fin 6, arcSector i p := by
  have hpne : seamPolynomial p ≠ 0 := fun h => hb ⟨hh, h⟩
  rw [seamPolynomial_factor] at hpne
  have hyne : p.val 1 ≠ 0 := by
    intro h
    exact hpne (by simp [h])
  have hAne : seamA p ≠ 0 := by
    intro h
    exact hpne (by simp [h])
  have hBne : seamB p ≠ 0 := by
    intro h
    exact hpne (by simp [h])
  rcases lt_or_gt_of_ne hyne with hyneg | hypos
  · rcases lt_or_gt_of_ne hAne with hAneg | hApos
    · rcases lt_or_gt_of_ne hBne with hBneg | hBpos
      · exact ⟨3, by simp [arcSector, hh, hyneg, hAneg, hBneg]⟩
      · exfalso
        dsimp [seamA, seamB] at hAneg hBpos
        linarith
    · rcases lt_or_gt_of_ne hBne with hBneg | hBpos
      · exact ⟨4, by simp [arcSector, hh, hyneg, hApos, hBneg]⟩
      · exact ⟨5, by simp [arcSector, hh, hyneg, hApos, hBpos]⟩
  · rcases lt_or_gt_of_ne hAne with hAneg | hApos
    · rcases lt_or_gt_of_ne hBne with hBneg | hBpos
      · exact ⟨2, by simp [arcSector, hh, hypos, hAneg, hBneg]⟩
      · exact ⟨1, by simp [arcSector, hh, hypos, hAneg, hBpos]⟩
    · rcases lt_or_gt_of_ne hBne with hBneg | hBpos
      · exfalso
        dsimp [seamA, seamB] at hApos hBneg
        linarith
      · exact ⟨0, by simp [arcSector, hh, hypos, hApos, hBpos]⟩

theorem arcSector_unique {p : Sphere} {i j : Fin 6}
    (hi : arcSector i p) (hj : arcSector j p) : i = j := by
  fin_cases i <;> fin_cases j <;> simp_all [arcSector] <;> linarith

theorem equator_nonbranch_unique_sector {p : Sphere}
    (hh : height p = 0) (hb : ¬ branch p) :
    ∃! i : Fin 6, arcSector i p := by
  obtain ⟨i, hi⟩ := arcSector_exists hh hb
  exact ⟨i, hi, fun j hj => arcSector_unique hj hi⟩

/-- Weak sector inequalities include the two endpoints of each open arc. -/
noncomputable def closedArcSector (i : Fin 6) (p : Sphere) : Prop :=
  height p = 0 ∧
  match i.val with
  | 0 => 0 ≤ p.val 1 ∧ 0 ≤ seamA p ∧ 0 ≤ seamB p
  | 1 => 0 ≤ p.val 1 ∧ seamA p ≤ 0 ∧ 0 ≤ seamB p
  | 2 => 0 ≤ p.val 1 ∧ seamA p ≤ 0 ∧ seamB p ≤ 0
  | 3 => p.val 1 ≤ 0 ∧ seamA p ≤ 0 ∧ seamB p ≤ 0
  | 4 => p.val 1 ≤ 0 ∧ 0 ≤ seamA p ∧ seamB p ≤ 0
  | _ => p.val 1 ≤ 0 ∧ 0 ≤ seamA p ∧ 0 ≤ seamB p

theorem arcSector_subset_closed {i : Fin 6} {p : Sphere}
    (h : arcSector i p) : closedArcSector i p := by
  fin_cases i <;> simp_all [arcSector, closedArcSector, le_of_lt]

theorem closedArcSector_branch_iff_endpoints (i j : Fin 6) :
    closedArcSector i (branchPoint (cyclicBranch j)) ↔ j = i ∨ j = i + 1 := by
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  fin_cases i <;> fin_cases j <;>
    norm_num [closedArcSector, cyclicBranch, branchPoint, branchVector,
      height, seamA, seamB, div_eq_mul_inv]

/-- On the actual quotient, crossing sector `i` swaps sheets exactly when
`i` is even. -/
theorem sector_attachment {i : Fin 6} {p : Sphere}
    (h : arcSector i p) (s t : Bool) :
    northCharacteristic (northBoundary p h.1 s) =
      southCharacteristic (southBoundary p h.1 t) ↔
      t = if i.val % 2 = 0 then !s else s := by
  change (Quotient.mk setoid (equatorRaw p h.1 true s) : Total) =
    Quotient.mk setoid (equatorRaw p h.1 false t) ↔ _
  have hb := arcSector_nonbranch h
  have hs := arcSector_alternating_sign h
  by_cases heven : i.val % 2 = 0
  · simpa [heven] using equator_glue_positive p h.1 hb (hs.mpr heven) s t
  · have hnonpos : ¬ 0 < seamPolynomial p := fun hpos => heven (hs.mp hpos)
    simpa [heven] using equator_glue_nonpositive p h.1 hb hnonpos s t

end AlternatingSphereCover
