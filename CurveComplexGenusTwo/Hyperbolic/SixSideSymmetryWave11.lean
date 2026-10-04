import CurveComplexGenusTwo.Hyperbolic.HyperbolicSeamWave11

namespace CurveComplex.Hyperbolic.IdealHexagonDouble

open CurveComplex.Hyperbolic

private theorem idealVertex_norm (i : Fin 6) : ‖idealHexagonVertex i‖ = 1 := by
  simpa [Metric.mem_sphere, dist_zero_right] using
    idealHexagonVertex_mem_circle i

noncomputable def discRotation (i : Fin 6)
    (w : Metric.ball (0 : ℂ) 1) : Metric.ball (0 : ℂ) 1 :=
  ⟨idealHexagonVertex i * w.1, by
    have hw : ‖(w : ℂ)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using w.property
    simpa only [Metric.mem_ball, dist_zero_right, norm_mul,
      idealVertex_norm i, one_mul] using hw⟩

noncomputable def discRotationInverse (i : Fin 6)
    (w : Metric.ball (0 : ℂ) 1) : Metric.ball (0 : ℂ) 1 :=
  ⟨star (idealHexagonVertex i) * w.1, by
    have hw : ‖(w : ℂ)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using w.property
    simpa only [Metric.mem_ball, dist_zero_right, norm_mul,
      norm_star, idealVertex_norm i, one_mul] using hw⟩

private theorem idealVertex_mul_conj (i : Fin 6) :
    idealHexagonVertex i * star (idealHexagonVertex i) = 1 := by
  simpa [Complex.star_def, idealVertex_norm i] using
    (RCLike.mul_conj (idealHexagonVertex i))

private theorem idealVertex_conj_mul (i : Fin 6) :
    star (idealHexagonVertex i) * idealHexagonVertex i = 1 := by
  rw [mul_comm, idealVertex_mul_conj]

theorem discRotation_left_inv (i : Fin 6) (w : Metric.ball (0 : ℂ) 1) :
    discRotationInverse i (discRotation i w) = w := by
  apply Subtype.ext
  change star (idealHexagonVertex i) * (idealHexagonVertex i * w.1) = w.1
  rw [← mul_assoc, idealVertex_conj_mul, one_mul]

theorem discRotation_right_inv (i : Fin 6) (w : Metric.ball (0 : ℂ) 1) :
    discRotation i (discRotationInverse i w) = w := by
  apply Subtype.ext
  change idealHexagonVertex i * (star (idealHexagonVertex i) * w.1) = w.1
  rw [← mul_assoc, idealVertex_mul_conj, one_mul]

noncomputable def discRotationEquiv (i : Fin 6) :
    Metric.ball (0 : ℂ) 1 ≃ Metric.ball (0 : ℂ) 1 where
  toFun := discRotation i
  invFun := discRotationInverse i
  left_inv := discRotation_left_inv i
  right_inv := discRotation_right_inv i

private theorem discRotation_cosh_dist (i : Fin 6)
    (u v : Metric.ball (0 : ℂ) 1) :
    Real.cosh (dist (cayleyInverse (discRotation i u))
      (cayleyInverse (discRotation i v))) =
      Real.cosh (dist (cayleyInverse u) (cayleyInverse v)) := by
  rw [cayleyInverse_cosh_dist, cayleyInverse_cosh_dist]
  have hn (w : ℂ) :
      Complex.normSq (idealHexagonVertex i * w) = Complex.normSq w := by
    rw [Complex.normSq_mul, idealHexagonVertex_normSq]
    ring
  change 1 + 2 * Complex.normSq
    (idealHexagonVertex i * (u : ℂ) - idealHexagonVertex i * (v : ℂ)) /
      ((1 - Complex.normSq (idealHexagonVertex i * (u : ℂ))) *
       (1 - Complex.normSq (idealHexagonVertex i * (v : ℂ)))) = _
  rw [← mul_sub, hn, hn, hn]

noncomputable def h2Rotation (i : Fin 6) (z : H2) : H2 :=
  cayleyInverse (discRotation i (cayleyOpen z))

noncomputable def h2RotationInverse (i : Fin 6) (z : H2) : H2 :=
  cayleyInverse (discRotationInverse i (cayleyOpen z))

theorem h2Rotation_left_inv (i : Fin 6) (z : H2) :
    h2RotationInverse i (h2Rotation i z) = z := by
  unfold h2RotationInverse h2Rotation
  rw [show cayleyOpen (cayleyInverse (discRotation i (cayleyOpen z))) =
    discRotation i (cayleyOpen z) from cayleyHomeomorph.apply_symm_apply _]
  rw [discRotation_left_inv]
  exact cayleyHomeomorph.symm_apply_apply z

theorem h2Rotation_right_inv (i : Fin 6) (z : H2) :
    h2Rotation i (h2RotationInverse i z) = z := by
  unfold h2RotationInverse h2Rotation
  rw [show cayleyOpen (cayleyInverse (discRotationInverse i (cayleyOpen z))) =
    discRotationInverse i (cayleyOpen z) from cayleyHomeomorph.apply_symm_apply _]
  rw [discRotation_right_inv]
  exact cayleyHomeomorph.symm_apply_apply z

theorem h2Rotation_dist (i : Fin 6) (z w : H2) :
    dist (h2Rotation i z) (h2Rotation i w) = dist z w := by
  apply Real.cosh_injOn dist_nonneg dist_nonneg
  simpa [h2Rotation, cayleyOpen, cayleyInverse_cayley] using
    discRotation_cosh_dist i (cayleyOpen z) (cayleyOpen w)

noncomputable def h2RotationIso (i : Fin 6) : H2 ≃ᵢ H2 where
  toFun := h2Rotation i
  invFun := h2RotationInverse i
  left_inv := h2Rotation_left_inv i
  right_inv := h2Rotation_right_inv i
  isometry_toFun := Isometry.of_dist_eq (h2Rotation_dist i)

/-- Multiplication by the first ideal vertex advances the six labels. -/
theorem idealVertex_rotate_next (i : Fin 6) :
    idealHexagonVertex i * idealHexagonVertex 1 =
      idealHexagonVertex (i + 1) := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  fin_cases i <;> apply Complex.ext <;>
    simp [idealHexagonVertex, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [hs]

theorem h2Rotation_cayley (i : Fin 6) (z : H2) :
    (cayley (h2Rotation i z) : ℂ) =
      idealHexagonVertex i * (cayley z : ℂ) := by
  exact cayley_cayleyInverse (discRotation i (cayleyOpen z))

theorem h2Rotation_zero (z : H2) : h2Rotation 0 z = z := by
  change cayleyInverse (discRotation 0 (cayleyOpen z)) = z
  have hdisc : discRotation 0 (cayleyOpen z) = cayleyOpen z := by
    apply Subtype.ext
    simp [discRotation, idealHexagonVertex]
  rw [hdisc]
  exact cayleyHomeomorph.symm_apply_apply z

noncomputable def sideReflectionIso (i : Fin 6) : H2 ≃ᵢ H2 :=
  ((h2RotationIso i).symm.trans sideZeroReflectionEquiv).trans
    (h2RotationIso i)

def rotatedSideGeodesic (i : Fin 6) : Set H2 :=
  h2Rotation i '' sideZeroGeodesic

theorem sideReflection_fixed_iff (i : Fin 6) (z : H2) :
    sideReflectionIso i z = z ↔ z ∈ rotatedSideGeodesic i := by
  constructor
  · intro h
    refine ⟨(h2RotationIso i).symm z, ?_, ?_⟩
    · apply (sideZeroReflection_fixed_iff _).1
      have hs : (h2RotationIso i)
          (sideZeroReflectionEquiv ((h2RotationIso i).symm z)) =
          (h2RotationIso i) ((h2RotationIso i).symm z) := by
        simpa [sideReflectionIso] using h
      exact (h2RotationIso i).injective hs
    · exact (h2RotationIso i).apply_symm_apply z
  · rintro ⟨w, hw, rfl⟩
    change (h2RotationIso i)
      (sideZeroReflectionEquiv ((h2RotationIso i).symm (h2Rotation i w))) =
      h2Rotation i w
    have heq : (h2RotationIso i).symm (h2Rotation i w) = w :=
      (h2RotationIso i).symm_apply_apply w
    rw [heq]
    change h2Rotation i (sideZeroReflection w) = h2Rotation i w
    rw [(sideZeroReflection_fixed_iff w).2 hw]

theorem sideReflection_dist (i : Fin 6) (z w : H2) :
    dist (sideReflectionIso i z) (sideReflectionIso i w) = dist z w :=
  (sideReflectionIso i).isometry.dist_eq z w

theorem sideReflection_involutive (i : Fin 6) (z : H2) :
    sideReflectionIso i (sideReflectionIso i z) = z := by
  simp only [sideReflectionIso, IsometryEquiv.trans_apply,
    IsometryEquiv.symm_apply_apply]
  change h2Rotation i
    (sideZeroReflection (sideZeroReflection ((h2RotationIso i).symm z))) = z
  rw [sideZeroReflection_involutive]
  exact (h2RotationIso i).apply_symm_apply z

theorem sideRotation_ideal_endpoints (i : Fin 6) :
    idealHexagonVertex i * idealHexagonVertex 0 = idealHexagonVertex i ∧
      idealHexagonVertex i * idealHexagonVertex 1 =
        idealHexagonVertex (i + 1) := by
  exact ⟨by simp [idealHexagonVertex], idealVertex_rotate_next i⟩

/-- The same concrete ideal polygon in the coordinate normalization of side `i`. -/
def rotatedIdealHexagonClosed (i : Fin 6) : Set H2 :=
  h2Rotation i '' idealHexagonClosed

theorem rotatedIdealHexagonClosed_zero :
    rotatedIdealHexagonClosed 0 = idealHexagonClosed := by
  ext z
  simp [rotatedIdealHexagonClosed, h2Rotation_zero]

def rotatedSideBall (i : Fin 6) : Set H2 :=
  h2Rotation i '' Metric.ball sideZeroBase sideZeroLocalRadius

noncomputable def rotatedSideBase (i : Fin 6) : H2 :=
  h2Rotation i sideZeroBase

theorem rotatedSideBall_eq_ball (i : Fin 6) :
    rotatedSideBall i =
      Metric.ball (rotatedSideBase i) sideZeroLocalRadius :=
  (h2RotationIso i).image_ball sideZeroBase sideZeroLocalRadius

theorem rotatedSideBall_open (i : Fin 6) : IsOpen (rotatedSideBall i) := by
  rw [rotatedSideBall_eq_ball]
  exact Metric.isOpen_ball

theorem rotatedSideBase_on_seam (i : Fin 6) :
    rotatedSideBase i ∈ rotatedSideGeodesic i :=
  ⟨sideZeroBase, sideZeroBase_on_seam, rfl⟩

theorem rotatedSideBase_in_polygon (i : Fin 6) :
    rotatedSideBase i ∈ rotatedIdealHexagonClosed i :=
  ⟨sideZeroBase, sideZeroBase_in_polygon, rfl⟩

theorem rotatedSideBall_polygon_iff (i : Fin 6) (z : H2)
    (hz : z ∈ rotatedSideBall i) :
    z ∈ rotatedIdealHexagonClosed i ↔
      sideZeroAbscissa ≤ ((h2RotationIso i).symm z).re := by
  obtain ⟨w, hw, rfl⟩ := hz
  have heq : (h2RotationIso i).symm (h2Rotation i w) = w :=
    (h2RotationIso i).symm_apply_apply w
  rw [heq]
  constructor
  · rintro ⟨v, hv, hzw⟩
    have : v = w := (h2RotationIso i).injective hzw
    subst v
    exact hv.1
  · intro h
    exact ⟨w, (sideZero_ball_polygon_iff w hw).2 h, rfl⟩

/-- This conditional form isolates the remaining region-invariance obligation:
once the explicit ideal-hexagon region is shown rotation invariant, every
transported chart is literally a chart of that same region. -/
theorem rotatedSideBall_actual_polygon_iff (i : Fin 6)
    (hregion : rotatedIdealHexagonClosed i = idealHexagonClosed)
    (z : H2) (hz : z ∈ rotatedSideBall i) :
    z ∈ idealHexagonClosed ↔
      sideZeroAbscissa ≤ ((h2RotationIso i).symm z).re := by
  rw [← hregion]
  exact rotatedSideBall_polygon_iff i z hz

theorem rotatedSideBall_avoids_other_sides (i : Fin 6) (z : H2)
    (hz : z ∈ rotatedSideBall i) :
    (((h2RotationIso i).symm z).re ≠ -sideZeroAbscissa) ∧
      ∀ j : Fin 4,
        finiteSideExcess j ((h2RotationIso i).symm z) ≠ 0 := by
  obtain ⟨w, hw, rfl⟩ := hz
  have heq : (h2RotationIso i).symm (h2Rotation i w) = w :=
    (h2RotationIso i).symm_apply_apply w
  rw [heq]
  exact sideZero_ball_avoids_other_sides w hw

/-- The transported side chart is an isometry onto its actual polygon-side
ball in the side-indexed coordinate normalization. -/
noncomputable def rotatedSideLocalChart (i : Fin 6) :
    sideZeroGluedPatch ≃ᵢ rotatedSideBall i := by
  let f : sideZeroGluedPatch → rotatedSideBall i :=
    fun x => ⟨h2Rotation i (seamCoordinate x.1),
      ⟨seamCoordinate x.1, x.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply seamCoordinate_injective
      apply (h2RotationIso i).injective
      exact congrArg Subtype.val h
    · intro y
      obtain ⟨w, hw, hy⟩ := y.2
      obtain ⟨x, hx⟩ := seamCoordinate_surjective w
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change seamCoordinate x ∈ Metric.ball sideZeroBase sideZeroLocalRadius
        rw [hx]
        exact hw
      · apply Subtype.ext
        simpa [f, hx] using hy
  exact {
    toEquiv := Equiv.ofBijective f hf
    isometry_toFun := Isometry.of_dist_eq (by
      intro x y
      change dist (h2Rotation i (seamCoordinate x.1))
        (h2Rotation i (seamCoordinate y.1)) = dist x y
      rw [h2Rotation_dist]
      exact (sideZero_local_chart_distance x y).symm)
  }

/-- Change of normalized hyperbolic coordinates from side `i` to side `j`. -/
noncomputable def sideTransition (i j : Fin 6) : H2 ≃ᵢ H2 :=
  (h2RotationIso i).symm.trans (h2RotationIso j)

theorem sideTransition_dist (i j : Fin 6) (z w : H2) :
    dist (sideTransition i j z) (sideTransition i j w) = dist z w :=
  (sideTransition i j).isometry.dist_eq z w

theorem sideTransition_chart_formula (i j : Fin 6)
    (x : sideZeroGluedPatch) :
    (rotatedSideLocalChart j x).1 =
      sideTransition i j (rotatedSideLocalChart i x).1 := by
  change h2Rotation j (seamCoordinate x.1) =
    h2Rotation j ((h2RotationIso i).symm
      (h2Rotation i (seamCoordinate x.1)))
  have heq : (h2RotationIso i).symm
      (h2Rotation i (seamCoordinate x.1)) = seamCoordinate x.1 :=
    (h2RotationIso i).symm_apply_apply (seamCoordinate x.1)
  rw [heq]

theorem sideTransition_cocycle (i j k : Fin 6) (z : H2) :
    sideTransition j k (sideTransition i j z) = sideTransition i k z := by
  simp [sideTransition]

theorem sideTransition_maps_chart_ball (i j : Fin 6) :
    sideTransition i j '' rotatedSideBall i = rotatedSideBall j := by
  ext z
  constructor
  · rintro ⟨u, ⟨w, hw, rfl⟩, rfl⟩
    have heq : (h2RotationIso i).symm (h2Rotation i w) = w :=
      (h2RotationIso i).symm_apply_apply w
    change h2Rotation j ((h2RotationIso i).symm (h2Rotation i w)) ∈
      rotatedSideBall j
    rw [heq]
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨h2Rotation i w, ⟨w, hw, rfl⟩, ?_⟩
    have heq : (h2RotationIso i).symm (h2Rotation i w) = w :=
      (h2RotationIso i).symm_apply_apply w
    change h2Rotation j ((h2RotationIso i).symm (h2Rotation i w)) =
      h2Rotation j w
    rw [heq]

end CurveComplex.Hyperbolic.IdealHexagonDouble
