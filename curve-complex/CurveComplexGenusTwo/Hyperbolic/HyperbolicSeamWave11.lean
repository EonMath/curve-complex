import CurveComplexGenusTwo.Hyperbolic.HexagonCoordinates
import CurveComplexGenusTwo.Hyperbolic.DiscMetric

namespace CurveComplex.Hyperbolic.IdealHexagonDouble

open CurveComplex.Hyperbolic

/-- The vertical ideal side with finite endpoint `-√3` in upper-half-plane coordinates. -/
noncomputable def sideZeroAbscissa : ℝ := -Real.sqrt 3

/-- Reflection across the complete geodesic through the side. -/
noncomputable def sideZeroReflection (z : H2) : H2 :=
  ⟨⟨2 * sideZeroAbscissa - z.re, z.im⟩, by exact z.im_pos⟩

@[simp] theorem sideZeroReflection_re (z : H2) :
    (sideZeroReflection z).re = 2 * sideZeroAbscissa - z.re := rfl

@[simp] theorem sideZeroReflection_im (z : H2) :
    (sideZeroReflection z).im = z.im := rfl

theorem sideZeroReflection_involutive (z : H2) :
    sideZeroReflection (sideZeroReflection z) = z := by
  apply UpperHalfPlane.ext_re_im
  · simp [sideZeroReflection]
  · rfl

theorem sideZeroReflection_dist (z w : H2) :
    dist (sideZeroReflection z) (sideZeroReflection w) = dist z w := by
  apply Real.cosh_injOn dist_nonneg dist_nonneg
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist']
  simp only [sideZeroReflection_re, sideZeroReflection_im]
  congr 1
  ring

theorem sideZeroReflection_isometry : Isometry sideZeroReflection :=
  Isometry.of_dist_eq sideZeroReflection_dist

noncomputable def sideZeroReflectionEquiv : H2 ≃ᵢ H2 where
  toFun := sideZeroReflection
  invFun := sideZeroReflection
  left_inv := sideZeroReflection_involutive
  right_inv := sideZeroReflection_involutive
  isometry_toFun := sideZeroReflection_isometry

def sideZeroGeodesic : Set H2 := {z | z.re = sideZeroAbscissa}

noncomputable def sideZeroPath (t : ℝ) : H2 :=
  UpperHalfPlane.mk ⟨sideZeroAbscissa, Real.exp t⟩ (Real.exp_pos t)

theorem sideZeroPath_isometry : Isometry sideZeroPath :=
  UpperHalfPlane.isometry_vertical_line sideZeroAbscissa

theorem sideZeroPath_range : Set.range sideZeroPath = sideZeroGeodesic := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    rfl
  · intro hz
    refine ⟨Real.log z.im, ?_⟩
    apply UpperHalfPlane.ext_re_im
    · exact hz.symm
    · exact Real.exp_log z.im_pos

theorem sideZeroReflection_fixed_iff (z : H2) :
    sideZeroReflection z = z ↔ z ∈ sideZeroGeodesic := by
  constructor
  · intro h
    have hr := congrArg UpperHalfPlane.re h
    simp only [sideZeroReflection_re] at hr
    change z.re = sideZeroAbscissa
    linarith
  · intro h
    apply UpperHalfPlane.ext_re_im
    · change 2 * sideZeroAbscissa - z.re = z.re
      change z.re = sideZeroAbscissa at h
      linarith
    · rfl

theorem sideZeroReflection_opposes_halfspaces (z : H2) :
    sideZeroAbscissa ≤ (sideZeroReflection z).re ↔ z.re ≤ sideZeroAbscissa := by
  simp only [sideZeroReflection_re]
  constructor <;> intro h <;> linarith

/-- The second ideal endpoint of side zero maps to the finite endpoint of the
vertical geodesic. The first ideal endpoint is `1`, hence maps to infinity. -/
theorem sideZero_finite_ideal_endpoint :
    Complex.I * (1 + idealHexagonVertex 1) /
      (1 - idealHexagonVertex 1) = (sideZeroAbscissa : ℂ) := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hd : (1 : ℂ) - idealHexagonVertex 1 ≠ 0 := by
    intro h
    have heq : idealHexagonVertex 1 = idealHexagonVertex 0 := by
      simpa [idealHexagonVertex] using (sub_eq_zero.mp h).symm
    have : (1 : Fin 6) = 0 := idealHexagonVertex_injective heq
    exact (by decide : (1 : Fin 6) ≠ 0) this
  apply (div_eq_iff hd).2
  apply Complex.ext
  · simp [idealHexagonVertex, sideZeroAbscissa, Complex.mul_re,
      Complex.sub_re, Complex.add_re]
    nlinarith [hs]
  · simp [idealHexagonVertex, sideZeroAbscissa, Complex.mul_im,
      Complex.sub_im, Complex.add_im]
    nlinarith [hs]

theorem sideZero_first_ideal_endpoint : idealHexagonVertex 0 = 1 := rfl

/-- Both copies of the closed side half-plane, with the true seam retained. -/
abbrev SideHalfPlane := {z : H2 // sideZeroAbscissa ≤ z.re}
abbrev SideCopy := Fin 2 × SideHalfPlane

noncomputable def developed (p : SideCopy) : H2 :=
  if p.1 = 0 then p.2.1 else sideZeroReflection p.2.1

theorem developed_continuous : Continuous developed := by
  have hclopen : IsClopen {p : SideCopy | p.1 = 0} := by
    constructor
    · exact (isClosed_discrete ({0} : Set (Fin 2))).preimage continuous_fst
    · exact (isOpen_discrete ({0} : Set (Fin 2))).preimage continuous_fst
  have hfront : frontier {p : SideCopy | p.1 = 0} = ∅ :=
    hclopen.frontier_eq
  have hfirst : Continuous (fun p : SideCopy => p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hsecond : Continuous (fun p : SideCopy => sideZeroReflection p.2.1) :=
    sideZeroReflection_isometry.continuous.comp hfirst
  unfold developed
  exact Continuous.if (by
    intro p hp
    rw [hfront] at hp
    simp at hp) hfirst hsecond

def seamRel (p q : SideCopy) : Prop := developed p = developed q

theorem seamRel_refl (p : SideCopy) : seamRel p p := rfl
theorem seamRel_symm {p q : SideCopy} (h : seamRel p q) : seamRel q p := h.symm
theorem seamRel_trans {p q r : SideCopy} (hpq : seamRel p q)
    (hqr : seamRel q r) : seamRel p r := hpq.trans hqr

instance : Setoid SideCopy where
  r := seamRel
  iseqv := ⟨seamRel_refl, @seamRel_symm, @seamRel_trans⟩

abbrev SideGluing := Quotient (inferInstance : Setoid SideCopy)

noncomputable def seamCoordinate : SideGluing → H2 :=
  Quotient.lift developed (by intro p q h; exact h)

theorem seamCoordinate_continuous : Continuous seamCoordinate :=
  developed_continuous.quotient_lift (by intro p q h; exact h)

theorem seamCoordinate_mk (p : SideCopy) :
    seamCoordinate (Quotient.mk'' p) = developed p := rfl

theorem seamCoordinate_injective : Function.Injective seamCoordinate := by
  intro x y h
  induction x using Quotient.inductionOn with
  | _ p =>
    induction y using Quotient.inductionOn with
    | _ q => exact Quotient.sound h

theorem seamCoordinate_surjective : Function.Surjective seamCoordinate := by
  intro z
  by_cases hz : sideZeroAbscissa ≤ z.re
  · exact ⟨Quotient.mk'' (0, ⟨z, hz⟩), by simp [seamCoordinate_mk, developed]⟩
  · have hr : sideZeroAbscissa ≤ (sideZeroReflection z).re :=
      (sideZeroReflection_opposes_halfspaces z).mpr (le_of_not_ge hz)
    refine ⟨Quotient.mk'' (1, ⟨sideZeroReflection z, hr⟩), ?_⟩
    simp [seamCoordinate_mk, developed, sideZeroReflection_involutive]

theorem seamCoordinate_bijective : Function.Bijective seamCoordinate :=
  ⟨seamCoordinate_injective, seamCoordinate_surjective⟩

theorem developed_zero (z : SideHalfPlane) : developed (0, z) = z.1 := by
  simp [developed]

theorem developed_one (z : SideHalfPlane) :
    developed (1, z) = sideZeroReflection z.1 := by
  simp [developed]

/-- Opposite copies meet exactly on the geodesic, and only at matching points. -/
theorem seamRel_zero_one_iff (z w : SideHalfPlane) :
    seamRel (0, z) (1, w) ↔ z.1 = w.1 ∧ z.1 ∈ sideZeroGeodesic := by
  rw [seamRel, developed_zero, developed_one]
  constructor
  · intro h
    have hre := congrArg UpperHalfPlane.re h
    simp only [sideZeroReflection_re] at hre
    have hz : z.1.re = sideZeroAbscissa := by
      have := z.property
      have := w.property
      linarith
    have hw : w.1.re = sideZeroAbscissa := by
      have := z.property
      have := w.property
      linarith
    have hfix : sideZeroReflection w.1 = w.1 :=
      (sideZeroReflection_fixed_iff w.1).2 hw
    exact ⟨h.trans hfix, hz⟩
  · rintro ⟨heq, hz⟩
    rw [heq]
    exact ((sideZeroReflection_fixed_iff w.1).2 (heq ▸ hz)).symm

theorem seamRel_zero_zero_iff (z w : SideHalfPlane) :
    seamRel (0, z) (0, w) ↔ z = w := by
  simp [seamRel, developed_zero, Subtype.ext_iff]

theorem seamRel_one_one_iff (z w : SideHalfPlane) :
    seamRel (1, z) (1, w) ↔ z = w := by
  rw [seamRel, developed_one, developed_one]
  constructor
  · intro h
    apply Subtype.ext
    exact sideZeroReflectionEquiv.injective h
  · intro h
    simp [h]

noncomputable def seamDistance (x y : SideGluing) : ℝ :=
  dist (seamCoordinate x) (seamCoordinate y)

theorem seamDistance_eq_zero_iff (x y : SideGluing) :
    seamDistance x y = 0 ↔ x = y := by
  rw [seamDistance, dist_eq_zero]
  exact seamCoordinate_injective.eq_iff

theorem seamDistance_triangle (x y z : SideGluing) :
    seamDistance x z ≤ seamDistance x y + seamDistance y z :=
  dist_triangle _ _ _

noncomputable instance : MetricSpace SideGluing :=
  MetricSpace.induced seamCoordinate seamCoordinate_injective inferInstance

theorem seamCoordinate_isometry : Isometry seamCoordinate :=
  Isometry.of_dist_eq (by intro x y; rfl)

noncomputable def seamCoordinateIso : SideGluing ≃ᵢ H2 where
  toEquiv := Equiv.ofBijective seamCoordinate seamCoordinate_bijective
  isometry_toFun := seamCoordinate_isometry

theorem seamDistance_eq_dist (x y : SideGluing) :
    seamDistance x y = dist x y := rfl

theorem same_sheet_distance (c : Fin 2) (z w : SideHalfPlane) :
    seamDistance (Quotient.mk'' (c, z)) (Quotient.mk'' (c, w)) = dist z w := by
  fin_cases c
  · simpa [seamDistance, seamCoordinate_mk, developed_zero] using
      (show dist z.1 w.1 = dist z w from rfl)
  · simp [seamDistance, seamCoordinate_mk, developed_one,
      sideZeroReflection_dist]
    rfl

theorem cross_sheet_distance (z w : SideHalfPlane) :
    seamDistance (Quotient.mk'' (0, z)) (Quotient.mk'' (1, w)) =
      dist z.1 (sideZeroReflection w.1) := by
  simp [seamDistance, seamCoordinate_mk, developed_zero, developed_one]

theorem paired_seam_points_equal (z : SideHalfPlane)
    (hz : z.1 ∈ sideZeroGeodesic) :
    (Quotient.mk'' (0, z) : SideGluing) = Quotient.mk'' (1, z) := by
  apply Quotient.sound
  exact (seamRel_zero_one_iff z z).2 ⟨rfl, hz⟩

/-! The following is the closed ideal hexagon in upper-half-plane coordinates.
Its finite ideal vertices, in boundary order, are `c, c/3, 0, -c/3, -c`,
where `c = -√3`; the sixth vertex is infinity. The four circular sides are
orthogonal to the real boundary. -/

private theorem sideZeroAbscissa_sq : sideZeroAbscissa ^ 2 = 3 := by
  simp [sideZeroAbscissa]

private theorem sideZeroAbscissa_neg : sideZeroAbscissa < 0 := by
  exact neg_lt_zero.mpr (Real.sqrt_pos.2 (by norm_num))

def finiteIdealIndex (i : Fin 5) : Fin 6 := ⟨i.val + 1, by omega⟩

noncomputable def finiteIdealEndpoint : Fin 5 → ℝ
  | 0 => sideZeroAbscissa
  | 1 => sideZeroAbscissa / 3
  | 2 => 0
  | 3 => -sideZeroAbscissa / 3
  | 4 => -sideZeroAbscissa

/-- Cayley images of the five finite ideal vertices, in boundary order. -/
theorem finiteIdealEndpoint_cayley (i : Fin 5) :
    Complex.I * (1 + idealHexagonVertex (finiteIdealIndex i)) /
      (1 - idealHexagonVertex (finiteIdealIndex i)) =
      (finiteIdealEndpoint i : ℂ) := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hd : (1 : ℂ) - idealHexagonVertex (finiteIdealIndex i) ≠ 0 := by
    intro h
    have heq : idealHexagonVertex (finiteIdealIndex i) = idealHexagonVertex 0 := by
      simpa [idealHexagonVertex] using (sub_eq_zero.mp h).symm
    have hi : finiteIdealIndex i = 0 := idealHexagonVertex_injective heq
    have hne : finiteIdealIndex i ≠ 0 := by
      fin_cases i <;> decide
    exact hne hi
  apply (div_eq_iff hd).2
  fin_cases i <;> apply Complex.ext <;>
    simp [finiteIdealIndex, finiteIdealEndpoint, idealHexagonVertex,
      sideZeroAbscissa, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] <;>
    nlinarith [hs]

noncomputable def finiteSideCenter : Fin 4 → ℝ
  | 0 => 2 * sideZeroAbscissa / 3
  | 1 => sideZeroAbscissa / 6
  | 2 => -sideZeroAbscissa / 6
  | 3 => -2 * sideZeroAbscissa / 3

noncomputable def finiteSideRadius : Fin 4 → ℝ
  | 0 => -sideZeroAbscissa / 3
  | 1 => -sideZeroAbscissa / 6
  | 2 => -sideZeroAbscissa / 6
  | 3 => -sideZeroAbscissa / 3

theorem finiteSide_endpoints (i : Fin 4) :
    finiteSideCenter i - finiteSideRadius i =
        finiteIdealEndpoint ⟨i.val, by omega⟩ ∧
      finiteSideCenter i + finiteSideRadius i =
        finiteIdealEndpoint ⟨i.val + 1, by omega⟩ := by
  fin_cases i <;> simp [finiteSideCenter, finiteSideRadius,
    finiteIdealEndpoint] <;> try ring
  all_goals trivial

noncomputable def finiteSideExcess (i : Fin 4) (z : H2) : ℝ :=
  (z.re - finiteSideCenter i) ^ 2 + z.im ^ 2 - finiteSideRadius i ^ 2

theorem finiteSideExcess_continuous (i : Fin 4) :
    Continuous (finiteSideExcess i) := by
  unfold finiteSideExcess
  fun_prop

/-- Closed region bounded by the two vertical and four circular ideal sides. -/
def idealHexagonClosed : Set H2 :=
  {z | sideZeroAbscissa ≤ z.re ∧ z.re ≤ -sideZeroAbscissa ∧
    ∀ i : Fin 4, 0 ≤ finiteSideExcess i z}

/-- Strict satisfaction of every side constraint except side zero. -/
def sideZeroSafe : Set H2 :=
  {z | z.re < -sideZeroAbscissa ∧
    ∀ i : Fin 4, 0 < finiteSideExcess i z}

theorem sideZeroSafe_open : IsOpen sideZeroSafe := by
  have h : IsOpen ({z : H2 | z.re < -sideZeroAbscissa} ∩
      ⋂ i : Fin 4, {z : H2 | 0 < finiteSideExcess i z}) := by
    apply (isOpen_lt UpperHalfPlane.continuous_re continuous_const).inter
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (finiteSideExcess_continuous i)
  convert h using 1
  ext z
  simp [sideZeroSafe]

noncomputable def sideZeroBase : H2 :=
  UpperHalfPlane.mk ⟨sideZeroAbscissa, 2⟩ (by norm_num)

theorem sideZeroBase_on_seam : sideZeroBase ∈ sideZeroGeodesic := rfl

theorem sideZeroBase_safe : sideZeroBase ∈ sideZeroSafe := by
  constructor
  · dsimp [sideZeroBase]
    linarith [sideZeroAbscissa_neg]
  · intro i
    fin_cases i <;> simp [finiteSideExcess, finiteSideCenter,
      finiteSideRadius, sideZeroBase] <;>
      nlinarith [sideZeroAbscissa_sq, sq_nonneg sideZeroAbscissa]

theorem idealHexagonClosed_local_iff (z : H2) (hz : z ∈ sideZeroSafe) :
    z ∈ idealHexagonClosed ↔ sideZeroAbscissa ≤ z.re := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, le_of_lt hz.1, fun i => le_of_lt (hz.2 i)⟩

/-- Positive separation from the other five ideal sides at a non-vertex point. -/
theorem exists_sideZero_local_radius :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball sideZeroBase ε ⊆ sideZeroSafe :=
  (Metric.isOpen_iff.mp sideZeroSafe_open) sideZeroBase sideZeroBase_safe

noncomputable def sideZeroLocalRadius : ℝ :=
  Classical.choose exists_sideZero_local_radius

theorem sideZeroLocalRadius_pos : 0 < sideZeroLocalRadius :=
  (Classical.choose_spec exists_sideZero_local_radius).1

theorem sideZero_ball_safe :
    Metric.ball sideZeroBase sideZeroLocalRadius ⊆ sideZeroSafe :=
  (Classical.choose_spec exists_sideZero_local_radius).2

theorem sideZero_ball_polygon_iff (z : H2)
    (hz : z ∈ Metric.ball sideZeroBase sideZeroLocalRadius) :
    z ∈ idealHexagonClosed ↔ sideZeroAbscissa ≤ z.re :=
  idealHexagonClosed_local_iff z (sideZero_ball_safe hz)

theorem sideZero_ball_avoids_other_sides (z : H2)
    (hz : z ∈ Metric.ball sideZeroBase sideZeroLocalRadius) :
    z.re ≠ -sideZeroAbscissa ∧
      ∀ i : Fin 4, finiteSideExcess i z ≠ 0 := by
  have hs := sideZero_ball_safe hz
  exact ⟨ne_of_lt hs.1, fun i => ne_of_gt (hs.2 i)⟩

theorem sideZeroBase_in_polygon : sideZeroBase ∈ idealHexagonClosed := by
  have hb : sideZeroBase ∈ Metric.ball sideZeroBase sideZeroLocalRadius := by
    simpa [Metric.mem_ball] using sideZeroLocalRadius_pos
  exact (sideZero_ball_polygon_iff sideZeroBase hb).2 (le_of_eq rfl)

theorem sideZero_ball_reflection (z : H2) :
    sideZeroReflection z ∈ Metric.ball sideZeroBase sideZeroLocalRadius ↔
      z ∈ Metric.ball sideZeroBase sideZeroLocalRadius := by
  have hf : sideZeroReflection sideZeroBase = sideZeroBase :=
    (sideZeroReflection_fixed_iff sideZeroBase).2 sideZeroBase_on_seam
  have hd : dist (sideZeroReflection z) sideZeroBase = dist z sideZeroBase := by
    conv_lhs => rw [← hf]
    exact sideZeroReflection_dist z sideZeroBase
  simp only [Metric.mem_ball, hd]

/-- Every first-sheet point in the local chart belongs to the concrete closed
hexagon, and reflection sends the second sheet to the other side. -/
theorem sideZero_local_polygon_membership (z : SideHalfPlane)
    (hz : z.1 ∈ Metric.ball sideZeroBase sideZeroLocalRadius) :
    z.1 ∈ idealHexagonClosed :=
  (sideZero_ball_polygon_iff z.1 hz).2 z.property

theorem sideZero_local_coordinate_ball (p : SideCopy) :
    developed p ∈ Metric.ball sideZeroBase sideZeroLocalRadius ↔
      p.2.1 ∈ Metric.ball sideZeroBase sideZeroLocalRadius := by
  rcases p with ⟨c, z⟩
  fin_cases c
  · simp [developed]
  · simpa [developed] using (sideZero_ball_reflection z.1)

/-- The local glued patch consists precisely of copies of polygon points in
the chosen ball, viewed inside the side-only quotient. -/
def sideZeroGluedPatch : Set SideGluing :=
  seamCoordinate ⁻¹' Metric.ball sideZeroBase sideZeroLocalRadius

theorem sideZeroGluedPatch_open : IsOpen sideZeroGluedPatch :=
  Metric.isOpen_ball.preimage seamCoordinate_continuous

theorem sideZeroGluedPatch_mk_iff (p : SideCopy) :
    (Quotient.mk'' p : SideGluing) ∈ sideZeroGluedPatch ↔
      p.2.1 ∈ Metric.ball sideZeroBase sideZeroLocalRadius := by
  exact sideZero_local_coordinate_ball p

theorem sideZeroGluedPatch_representative_polygon (p : SideCopy)
    (hp : (Quotient.mk'' p : SideGluing) ∈ sideZeroGluedPatch) :
    p.2.1 ∈ idealHexagonClosed :=
  sideZero_local_polygon_membership p.2
    ((sideZeroGluedPatch_mk_iff p).1 hp)

abbrev IdealHexagonPoint := {z : H2 // z ∈ idealHexagonClosed}
abbrev IdealHexagonCopy := Fin 2 × IdealHexagonPoint

def idealHexagonCopyToSide (p : IdealHexagonCopy) : SideCopy :=
  (p.1, ⟨p.2.1, p.2.2.1⟩)

def idealHexagonCopy_mk (p : IdealHexagonCopy) : SideGluing :=
  Quotient.mk'' (idealHexagonCopyToSide p)

theorem sideZeroGluedPatch_has_hexagon_representative
    (x : SideGluing) (hx : x ∈ sideZeroGluedPatch) :
    ∃ p : IdealHexagonCopy,
      p.2.1 ∈ Metric.ball sideZeroBase sideZeroLocalRadius ∧
        idealHexagonCopy_mk p = x := by
  induction x using Quotient.inductionOn with
  | _ p =>
    have hpolygon := sideZeroGluedPatch_representative_polygon p hx
    refine ⟨(p.1, ⟨p.2.1, hpolygon⟩), ?_, ?_⟩
    · exact (sideZeroGluedPatch_mk_iff p).1 hx
    · rfl

theorem idealHexagonCopy_local_iff (p : IdealHexagonCopy) :
    idealHexagonCopy_mk p ∈ sideZeroGluedPatch ↔
      p.2.1 ∈ Metric.ball sideZeroBase sideZeroLocalRadius := by
  exact sideZeroGluedPatch_mk_iff (idealHexagonCopyToSide p)

theorem sideZero_local_chart_onto_ball :
    seamCoordinate '' sideZeroGluedPatch =
      Metric.ball sideZeroBase sideZeroLocalRadius := by
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨x, hx, rfl⟩
    exact hx
  · intro y hy
    obtain ⟨x, rfl⟩ := seamCoordinate_surjective y
    exact ⟨x, hy, rfl⟩

theorem sideZero_local_chart_distance (x y : sideZeroGluedPatch) :
    dist x y = dist (seamCoordinate x.1) (seamCoordinate y.1) := rfl

/-- The metric chart of the doubled hexagon near a non-vertex point of side
zero. Its domain consists of polygon points by the membership theorem above. -/
noncomputable def sideZeroLocalChart :
    sideZeroGluedPatch ≃ᵢ
      Metric.ball sideZeroBase sideZeroLocalRadius := by
  let f : sideZeroGluedPatch →
      Metric.ball sideZeroBase sideZeroLocalRadius :=
    fun x => ⟨seamCoordinate x.1, x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact seamCoordinate_injective (congrArg Subtype.val h)
    · intro y
      obtain ⟨x, hx⟩ := seamCoordinate_surjective y.1
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change seamCoordinate x ∈ Metric.ball sideZeroBase sideZeroLocalRadius
        rw [hx]
        exact y.2
      · apply Subtype.ext
        exact hx
  exact {
    toEquiv := Equiv.ofBijective f hf
    isometry_toFun := Isometry.of_dist_eq (by intro x y; rfl)
  }

end CurveComplex.Hyperbolic.IdealHexagonDouble
