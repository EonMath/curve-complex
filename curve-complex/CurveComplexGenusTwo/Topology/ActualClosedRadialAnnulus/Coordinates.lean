import CurveComplexGenusTwo.CWHurewicz.AnnulusHomotopy
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Connected.PathConnected

open Set
open scoped Topology

noncomputable section

/-!
Statement-only scaffold for Leaf A of the caller's
`actual_derivative_sign_euler/CRITICAL_HANDLE_LEAF_REVIEW_REQUEST.md`.

Source: literal elementary polar-coordinate geometry on the closed radial
annulus, using exactly the maps specified by that request. Every mathematical
proof field and theorem remains `sorry`. The functions themselves are given
by their actual formulas; no closed-annulus topology is assumed as input.

The canonical imported `Annulus` is OPEN (1 < norm < 2). Its public `radial`
map lands in `MidCircle` of radius 3/2. The final theorem below supplies the
explicit unit-normalization bridge to that actual imported map.
-/

/-- The literal CLOSED radial annulus, including both boundary circles. -/
abbrev ActualClosedRadialAnnulus (r R : ℝ) :=
  {z : ℂ // r ≤ ‖z‖ ∧ ‖z‖ ≤ R}

/-- Well-definedness of the literal angular coordinate `z / ‖z‖`. -/
theorem actual_closed_radial_annulus_normalize_mem_circle
    {r R : ℝ} (hr : 0 < r) (z : ActualClosedRadialAnnulus r R) :
    (z : ℂ) / (‖(z : ℂ)‖ : ℂ) ∈ Submonoid.unitSphere ℂ := by
  apply mem_sphere_zero_iff_norm.mpr
  have hn : 0 < ‖(z : ℂ)‖ := lt_of_lt_of_le hr z.property.1
  simp [Complex.norm_real, ne_of_gt hn]

/-- Well-definedness of the literal inverse polar-coordinate map. -/
theorem actual_closed_radial_annulus_synthesize_mem
    {r R : ℝ} (hr : 0 < r) (p : Circle × Set.Icc r R) :
    r ≤ ‖(p.2 : ℝ) • (p.1 : ℂ)‖ ∧
      ‖(p.2 : ℝ) • (p.1 : ℂ)‖ ≤ R := by
  have ht : 0 ≤ (p.2 : ℝ) := le_trans hr.le p.2.property.1
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, Circle.norm_coe,
    mul_one, Set.mem_Icc] using p.2.property

/-- The actual angular and radial coordinates. The second component is the
closed-interval subtype witness already carried by `z`. -/
def actualClosedRadialAnnulusCoordinates
    {r R : ℝ} (hr : 0 < r) (z : ActualClosedRadialAnnulus r R) :
    Circle × Set.Icc r R :=
  (⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ),
      actual_closed_radial_annulus_normalize_mem_circle hr z⟩,
    ⟨‖(z : ℂ)‖, z.property⟩)

/-- The actual inverse map `(w,t) ↦ t • w`, with REAL scalar multiplication. -/
def actualClosedRadialAnnulusSynthesize
    {r R : ℝ} (hr : 0 < r) (p : Circle × Set.Icc r R) :
    ActualClosedRadialAnnulus r R :=
  ⟨(p.2 : ℝ) • (p.1 : ℂ),
    actual_closed_radial_annulus_synthesize_mem hr p⟩

/-- The canonical polar-coordinate homeomorphism of the literal closed radial
annulus. The radial interval may be degenerate: the hypothesis is `r ≤ R`.
Both inverse identities and both continuity obligations are proof fields. -/
def actualClosedRadialAnnulusHomeomorph
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) :
    ActualClosedRadialAnnulus r R ≃ₜ (Circle × Set.Icc r R) where
  toFun := actualClosedRadialAnnulusCoordinates hr
  invFun := actualClosedRadialAnnulusSynthesize hr
  left_inv := by
    intro z
    apply Subtype.ext
    have hn : (‖(z : ℂ)‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hr z.property.1))
    dsimp [actualClosedRadialAnnulusCoordinates, actualClosedRadialAnnulusSynthesize]
    field_simp
  right_inv := by
    intro p
    have ht : 0 < (p.2 : ℝ) := lt_of_lt_of_le hr p.2.property.1
    have hn : ‖(p.2 : ℝ) • (p.1 : ℂ)‖ = (p.2 : ℝ) := by
      simp [Real.norm_eq_abs, abs_of_pos ht]
    apply Prod.ext
    · apply Circle.ext
      change ((p.2 : ℝ) • (p.1 : ℂ)) / (‖(p.2 : ℝ) • (p.1 : ℂ)‖ : ℂ) = (p.1 : ℂ)
      rw [hn, Complex.real_smul]
      field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
    · apply Subtype.ext
      exact hn
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      have hn : Continuous fun z : ActualClosedRadialAnnulus r R => (‖(z : ℂ)‖ : ℂ) :=
        Complex.continuous_ofReal.comp (continuous_norm.comp continuous_subtype_val)
      exact continuous_subtype_val.div₀ hn (fun z => Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_of_lt_of_le hr z.property.1)))
    · exact (continuous_norm.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)

/-- The chosen inner-circle inclusion `w ↦ r • w`. Its radius is the left
endpoint of the same closed interval, valid also when `r = R`. -/
def actualClosedRadialAnnulusInnerCircleIncl
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) (w : Circle) :
    ActualClosedRadialAnnulus r R :=
  actualClosedRadialAnnulusSynthesize hr (w, ⟨r, ⟨le_rfl, hR⟩⟩)

/-- The actual radial homotopy equivalence to the unit circle, with forward
map `z ↦ z/‖z‖` and backward map `w ↦ r • w`.
Continuity and the two homotopy-inverse conditions remain proof obligations. -/
def actualClosedRadialAnnulusCircleHomotopyEquiv
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) :
    ContinuousMap.HomotopyEquiv (ActualClosedRadialAnnulus r R) Circle where
  toFun := ⟨fun z => (actualClosedRadialAnnulusCoordinates hr z).1, by
    exact (actualClosedRadialAnnulusHomeomorph hr hR).continuous.fst⟩
  invFun := ⟨actualClosedRadialAnnulusInnerCircleIncl hr hR, by
    exact (actualClosedRadialAnnulusHomeomorph hr hR).symm.continuous.comp
      (continuous_id.prodMk continuous_const)⟩
  left_inv := by
    let e := actualClosedRadialAnnulusHomeomorph hr hR
    let H : unitInterval × ActualClosedRadialAnnulus r R → Circle × Set.Icc r R :=
      fun p => ((actualClosedRadialAnnulusCoordinates hr p.2).1,
        ⟨(1 - (p.1 : ℝ)) * r + (p.1 : ℝ) * ‖(p.2 : ℂ)‖, by
          have ht0 := p.1.property.1
          have ht1 := p.1.property.2
          have hz0 := p.2.property.1
          have hz1 := p.2.property.2
          constructor
          · nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hz0)]
          · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hR),
              mul_nonneg ht0 (sub_nonneg.mpr hz1)]⟩)
    have hH : Continuous H := by
      apply Continuous.prodMk
      · exact e.continuous.fst.comp continuous_snd
      · apply Continuous.subtype_mk
        have ht : Continuous fun p : unitInterval × ActualClosedRadialAnnulus r R =>
            (p.1 : ℝ) := continuous_subtype_val.comp continuous_fst
        have hz : Continuous fun p : unitInterval × ActualClosedRadialAnnulus r R =>
            ‖(p.2 : ℂ)‖ := (continuous_subtype_val.comp continuous_snd).norm
        exact ((continuous_const.sub ht).mul continuous_const).add (ht.mul hz)
    refine ⟨{
      toFun := fun p => actualClosedRadialAnnulusSynthesize hr (H p)
      continuous_toFun := e.symm.continuous.comp hH
      map_zero_left := ?_
      map_one_left := ?_
    }⟩
    · intro z
      change actualClosedRadialAnnulusSynthesize hr (H (0, z)) =
        actualClosedRadialAnnulusInnerCircleIncl hr hR
          (actualClosedRadialAnnulusCoordinates hr z).1
      apply Subtype.ext
      simp [H, actualClosedRadialAnnulusSynthesize, actualClosedRadialAnnulusInnerCircleIncl]
    · intro z
      change actualClosedRadialAnnulusSynthesize hr (H (1, z)) = z
      simp only [H, Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
      exact e.left_inv z
  right_inv := by
    have heq :
        (⟨fun z => (actualClosedRadialAnnulusCoordinates hr z).1,
          (actualClosedRadialAnnulusHomeomorph hr hR).continuous.fst⟩ :
          C(ActualClosedRadialAnnulus r R, Circle)).comp
        ⟨actualClosedRadialAnnulusInnerCircleIncl hr hR,
          (actualClosedRadialAnnulusHomeomorph hr hR).symm.continuous.comp
            (continuous_id.prodMk continuous_const)⟩ = ContinuousMap.id Circle := by
      ext w
      exact congrArg (fun p : Circle × Set.Icc r R => (p.1 : ℂ))
        ((actualClosedRadialAnnulusHomeomorph hr hR).right_inv (w, ⟨r, le_rfl, hR⟩))
    rw [heq]

/-- An explicit path-connected-space producer for the literal closed annulus.
It includes nonemptiness and paths between every pair of points. -/
theorem actual_closed_radial_annulus_pathConnectedSpace
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) :
    PathConnectedSpace (ActualClosedRadialAnnulus r R) := by
  let : PathConnectedSpace Circle :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) (0 : ℂ)
        (by norm_num : (0 : ℝ) ≤ 1))
  let : PathConnectedSpace (Set.Icc r R) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc r R).isPathConnected ⟨r, le_rfl, hR⟩)
  exact (actualClosedRadialAnnulusHomeomorph hr hR).symm.pathConnectedSpace

/-- The explicit normalization bridge to the canonical OPEN annulus radial
map. This is an equality of actual formulas on their common domain; it does
not replace either closed radial inequality by a strict one.

The imported `radial : Annulus → MidCircle` multiplies `z` by `(3/2)/‖z‖`;
scaling its output by `2/3` gives the unit angular coordinate used here. -/
theorem actual_closed_radial_annulus_canonical_open_radial_bridge
    {r R : ℝ} (hr : 0 < r) (z : Annulus)
    (hz : r ≤ ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ ≤ R) :
    ((actualClosedRadialAnnulusCoordinates hr
      (⟨(z : ℂ), hz⟩ : ActualClosedRadialAnnulus r R)).1 : ℂ) =
      (2 / 3 : ℝ) • (radial z : ℂ) := by
  change (z : ℂ) / (‖(z : ℂ)‖ : ℂ) =
    (2 / 3 : ℝ) • (((3 / 2 : ℝ) / ‖(z : ℂ)‖) • (z : ℂ))
  rw [smul_smul, Complex.real_smul]
  push_cast
  ring
