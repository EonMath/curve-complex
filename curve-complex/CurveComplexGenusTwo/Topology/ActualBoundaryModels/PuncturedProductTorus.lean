import CurveComplexGenusTwo.Topology.ActualBoundaryModels.Definitions
import ClassificationOfSurfaces.LeanEval.ChallengeDeps
import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage
import ClassificationOfSurfaces.DiskSquare
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.LocalAtTarget

namespace CurveComplex.Hyperbolic
open Set Topology CategoryTheory
open LeanEval.Topology.ClassificationOfSurfaces
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Explicit one-handle/one-boundary representative interior, identified with
the punctured PRODUCT torus required by the original cut/link consumers. -/
theorem actual_one_handle_one_boundary_model_punctured_product_torus :
    Nonempty (ActualOneBoundaryOrientableOpenModel 1 ≃ₜ
      {z : Circle × Circle // z ≠ (1,1)}) := by
  classical
  let weights : List ℕ := [1,1,1,1,4,4,4]
  have hwpos : WeightedCircle.Positive weights := by
    intro w hw
    simp [weights] at hw
    rcases hw with rfl | rfl <;> decide
  have hwnil : weights ≠ [] := by decide
  let b : Circle ≃ₜ DiskSquare.boundary :=
    (WeightedCircle.circleHomeomorph weights hwpos hwnil).trans
      (DiskSquare.quarterRotation.trans DiskSquare.circleBoundaryHomeomorph)
  let d : Complex.ClosedUnitDisc ≃ₜ DiskSquare.square :=
    (PolygonCell.closedUnitDiscHomeomorph 7).symm.trans
      (DiskSquare.cellSquareHomeomorph b)
  have hdside (i : Fin 7) (t : unitInterval) :
      d (Complex.ClosedUnitDisc.bdyPtOfReal (((i : ℝ) + (t : ℝ)) / 7)) =
        DiskSquare.boundaryInclusion (DiskSquare.circleBoundaryHomeomorph
          (Circle.exp (Real.pi / 4 + Real.pi / 8 *
            ((weights.take i.val).sum + weights.get ⟨i.val, by change i.val < 7; exact i.isLt⟩ * (t : ℝ))))) := by
    have hside := PolygonCell.closedUnitDiscHomeomorph_side (m := 7) i t
    norm_num at hside
    rw [← hside]
    change DiskSquare.cellSquareHomeomorph b (PolygonCell.side i t) = _
    change DiskSquare.cellSquareHomeomorph b
      (PolygonCell.ofCircle 7 (Circle.exp (PolygonCell.sideAngle i t))) = _
    rw [DiskSquare.cellSquareHomeomorph_ofCircle]
    congr 1
    change DiskSquare.circleBoundaryHomeomorph
      (Circle.exp (Real.pi / 4) *
        WeightedCircle.circleHomeomorph weights hwpos hwnil
          (Circle.exp (PolygonCell.sideAngle i t))) = _
    have h := WeightedCircle.circleHomeomorph_exp_index_add' weights hwpos hwnil
      (⟨i.val, by change i.val < 7; exact i.isLt⟩ : Fin weights.length) t
    have harg : PolygonCell.sideAngle i t =
        2 * Real.pi / weights.length * ((i : ℝ) + (t : ℝ)) := by
      simp only [PolygonCell.sideAngle, weights, List.length_cons, List.length_nil]
      push_cast
      ring
    rw [harg, h, ← Circle.exp_add]
    congr 2
    norm_num [weights]
    left
    ring
  have hdouter (u : ℝ) (hu : u ∈ Set.Icc 0 4) :
      d (Complex.ClosedUnitDisc.bdyPtOfReal (u / 7)) =
        DiskSquare.boundaryInclusion (DiskSquare.circleBoundaryHomeomorph
          (Circle.exp (Real.pi / 4 + Real.pi / 8 * u))) := by
    have hstretch : WeightedCircle.stretch weights u = u := by
      simp only [weights, WeightedCircle.stretch, Nat.cast_one, Nat.cast_ofNat]
      split_ifs <;> linarith [hu.1, hu.2]
    have hx : u ∈ Set.Ico 0 (weights.length : ℝ) := by
      norm_num [weights]
      exact ⟨hu.1, by linarith [hu.2]⟩
    have h := WeightedCircle.circleHomeomorph_exp_of_mem_Ico weights hwpos hwnil u hx
    have heq : d (Complex.ClosedUnitDisc.bdyPtOfReal (u / 7)) =
        DiskSquare.boundaryInclusion (b (Circle.exp (2 * Real.pi / 7 * u))) := by
      change DiskSquare.cellSquareHomeomorph b
        ((PolygonCell.closedUnitDiscHomeomorph 7).symm _) = _
      have hsource : (PolygonCell.closedUnitDiscHomeomorph 7).symm
          (Complex.ClosedUnitDisc.bdyPtOfReal (u / 7)) =
          PolygonCell.ofCircle 7 (Circle.exp (2 * Real.pi / 7 * u)) := by
        apply PolygonCell.ext
        change (Circle.exp (2 * Real.pi * (u / 7)) : ℂ) =
          (Circle.exp (2 * Real.pi / 7 * u) : ℂ)
        congr 2
        ring
      rw [hsource, DiskSquare.cellSquareHomeomorph_ofCircle]
    rw [heq]
    congr 1
    change DiskSquare.circleBoundaryHomeomorph
      (Circle.exp (Real.pi / 4) *
        WeightedCircle.circleHomeomorph weights hwpos hwnil
          (Circle.exp (2 * Real.pi / 7 * u))) = _
    norm_num [weights] at h
    rw [h, hstretch, ← Circle.exp_add]
    congr 2
    ring
  have hquarter (z : Circle) :
      (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi / 2) * z)).val =
        Complex.I * (DiskSquare.circleBoundaryHomeomorph z).val := by
    have hi : (Circle.exp (Real.pi / 2) : ℂ) = Complex.I := by
      rw [Circle.coe_exp]
      push_cast
      exact Complex.exp_pi_div_two_mul_I
    have hmax : DiskSquare.maxAbs (Complex.I * (z : ℂ)) = DiskSquare.maxAbs z := by
      simp [DiskSquare.maxAbs, Complex.mul_re, Complex.mul_im, abs_neg, max_comm]
    rw [DiskSquare.circleBoundaryHomeomorph_val, DiskSquare.circleBoundaryHomeomorph_val]
    unfold DiskSquare.radialToBoundary
    simp only [Circle.coe_mul, hi, hmax]
    ring
  have hright (theta : ℝ) (htheta : theta ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) :
      (DiskSquare.circleBoundaryHomeomorph (Circle.exp theta)).val =
        Complex.mk 1 (Real.tan theta) := by
    have hcos : 0 ≤ Real.cos theta :=
      Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [htheta.1, Real.pi_pos], by nlinarith [htheta.2, Real.pi_pos]⟩
    have hmax : DiskSquare.maxAbs (Circle.exp theta : ℂ) = Real.cos theta := by
      simp only [DiskSquare.maxAbs, Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, abs_of_nonneg hcos]
      exact max_eq_left (DiskSquare.abs_sin_le_cos_of_mem_Icc htheta)
    apply Complex.ext
    · exact DiskSquare.radialToBoundary_re_eq_one_of_angle htheta
    · rw [DiskSquare.circleBoundaryHomeomorph_val]
      change (DiskSquare.radialToBoundary (Circle.exp theta) _).im = Real.tan theta
      rw [DiskSquare.radialToBoundary, Complex.div_ofReal_im, hmax]
      simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_im, Real.tan_eq_sin_div_cos]
  have htop (theta : ℝ) (htheta : theta ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) :
      (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi / 2 + theta))).val =
        Complex.mk (-Real.tan theta) 1 := by
    rw [Circle.exp_add, hquarter, hright theta htheta]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hleft (theta : ℝ) (htheta : theta ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) :
      (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi + theta))).val =
        Complex.mk (-1) (-Real.tan theta) := by
    rw [show Real.pi + theta = Real.pi / 2 + (Real.pi / 2 + theta) by ring,
      Circle.exp_add, hquarter, htop theta htheta]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hbottom (theta : ℝ) (htheta : theta ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) :
      (DiskSquare.circleBoundaryHomeomorph (Circle.exp (3 * Real.pi / 2 + theta))).val =
        Complex.mk (Real.tan theta) (-1) := by
    rw [show 3 * Real.pi / 2 + theta = Real.pi / 2 + (Real.pi + theta) by ring,
      Circle.exp_add, hquarter, hleft theta htheta]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  let angle : ℝ → Circle := fun x => Circle.exp (5 * Real.pi / 4 - 4 * Real.arctan x)
  have hangcont : Continuous angle := by dsimp [angle]; fun_prop
  let perimeter : ℝ → DiskSquare.boundary := fun x => DiskSquare.circleBoundaryHomeomorph (angle x)
  have hpercont : Continuous perimeter := DiskSquare.circleBoundaryHomeomorph.continuous.comp hangcont
  let radial : DiskSquare.square → ℂ := fun z => ((z.val.im + 1) / 2) • (perimeter z.val.re).val
  have hradcont : Continuous radial := by
    dsimp [radial]
    exact ((Complex.continuous_im.comp continuous_subtype_val).add continuous_const |>.div_const 2).smul
      (continuous_subtype_val.comp (hpercont.comp (Complex.continuous_re.comp continuous_subtype_val)))
  let torusMap : DiskSquare.square → Circle × Circle :=
    fun z => (Circle.exp (Real.pi * (radial z).re), Circle.exp (Real.pi * (radial z).im))
  have htoruscont : Continuous torusMap := by dsimp [torusMap]; fun_prop
  have hradbounds (z : DiskSquare.square) :
      0 ≤ (z.val.im + 1) / 2 ∧ (z.val.im + 1) / 2 ≤ 1 := by
    have him := (abs_le.mp (DiskSquare.abs_im_le_maxAbs z.val |>.trans z.property))
    constructor <;> linarith
  have hradmax (z : DiskSquare.square) :
      DiskSquare.maxAbs (radial z) = (z.val.im + 1) / 2 := by
    dsimp only [radial]
    rw [DiskSquare.maxAbs_smul_of_nonneg _ (hradbounds z).1]
    have hp : DiskSquare.maxAbs (perimeter z.val.re).val = 1 := (perimeter z.val.re).property
    rw [hp, mul_one]
  have hexpzero (x : ℝ) (hx : |x| ≤ 1) : Circle.exp (Real.pi * x) = 1 ↔ x = 0 := by
    constructor
    · intro he
      have he' : Circle.exp (Real.pi * x) = Circle.exp 0 := by simpa using he
      obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he'
      have hxk : x = 2 * (k : ℝ) := by nlinarith [Real.pi_pos]
      have hbounds := abs_le.mp hx
      have hklo : (-1 : ℤ) < k := by
        have : (-1 : ℝ) < (k : ℝ) := by nlinarith
        exact_mod_cast this
      have hkhi : k < (1 : ℤ) := by
        have : (k : ℝ) < (1 : ℝ) := by nlinarith
        exact_mod_cast this
      have hkzero : k = 0 := by omega
      simpa [hkzero] using hxk
    · rintro rfl
      simp
  have hcollapsed (z : DiskSquare.square) : torusMap z = (1,1) ↔ z.val.im = -1 := by
    have hrle : DiskSquare.maxAbs (radial z) ≤ 1 := (hradmax z).trans_le (hradbounds z).2
    constructor
    · intro he
      have hre : (radial z).re = 0 :=
        (hexpzero _ (DiskSquare.abs_re_le_maxAbs _ |>.trans hrle)).mp (congrArg Prod.fst he)
      have him : (radial z).im = 0 :=
        (hexpzero _ (DiskSquare.abs_im_le_maxAbs _ |>.trans hrle)).mp (congrArg Prod.snd he)
      have hz : radial z = 0 := Complex.ext hre him
      have hm := hradmax z
      rw [hz, DiskSquare.maxAbs_zero] at hm
      linarith
    · intro hz
      simp [torusMap, radial, hz]
  have hseam : angle (-1) = angle 1 := by
    apply Circle.exp_eq_exp.mpr
    refine ⟨1, ?_⟩
    simp only [Real.arctan_neg, Real.arctan_one, Int.cast_one]
    ring
  have hsameSeam (z w : DiskSquare.square)
      (hz : z.val.re = -1) (hw : w.val.re = 1) (hy : z.val.im = w.val.im) :
      torusMap z = torusMap w := by
    have hr : radial z = radial w := by
      dsimp [radial, perimeter]
      rw [hz, hw, hy, hseam]
    dsimp [torusMap]
    rw [hr]
  have hatanbounds (x : ℝ) (hx : |x| ≤ 1) :
      -(Real.pi / 4) ≤ Real.arctan x ∧ Real.arctan x ≤ Real.pi / 4 := by
    have h := abs_le.mp hx
    constructor
    · simpa [Real.arctan_neg, Real.arctan_one] using Real.arctan_strictMono.monotone h.1
    · simpa [Real.arctan_one] using Real.arctan_strictMono.monotone h.2
  have hangleKernel (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
      (he : angle x = angle y) : x = y ∨ (x = -1 ∧ y = 1) ∨ (x = 1 ∧ y = -1) := by
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
    change 5 * Real.pi / 4 - 4 * Real.arctan x =
      5 * Real.pi / 4 - 4 * Real.arctan y + (k : ℝ) * (2 * Real.pi) at hk
    have hxb := hatanbounds x hx
    have hyb := hatanbounds y hy
    have hklo : (-1 : ℤ) ≤ k := by
      have : (-1 : ℝ) ≤ (k : ℝ) := by nlinarith [Real.pi_pos]
      exact_mod_cast this
    have hkhi : k ≤ (1 : ℤ) := by
      have : (k : ℝ) ≤ (1 : ℝ) := by nlinarith [Real.pi_pos]
      exact_mod_cast this
    have cases : k = 0 ∨ k = 1 ∨ k = -1 := by omega
    rcases cases with hzero | hone | hneg
    · left
      apply Real.arctan_injective
      simp only [hzero, Int.cast_zero, zero_mul, add_zero] at hk
      linarith
    · right; left
      simp only [hone, Int.cast_one, one_mul] at hk
      constructor
      · apply Real.arctan_injective
        rw [Real.arctan_neg, Real.arctan_one]
        linarith
      · apply Real.arctan_injective
        rw [Real.arctan_one]
        linarith
    · right; right
      simp only [hneg, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at hk
      constructor
      · apply Real.arctan_injective
        rw [Real.arctan_one]
        linarith
      · apply Real.arctan_injective
        rw [Real.arctan_neg, Real.arctan_one]
        linarith
  have hangleSurj (z : Circle) : ∃ x : ℝ, |x| ≤ 1 ∧ angle x = z := by
    let a := z.val.arg
    have halow : -Real.pi < a := Complex.neg_pi_lt_arg _
    have hahi : a ≤ Real.pi := Complex.arg_le_pi _
    let theta := if Real.pi / 4 ≤ a then a else a + 2 * Real.pi
    have htheta : Real.pi / 4 ≤ theta ∧ theta ≤ 9 * Real.pi / 4 := by
      dsimp [theta]
      split_ifs with h <;> constructor <;> nlinarith [Real.pi_pos]
    have hexp : Circle.exp theta = z := by
      dsimp [theta, a]
      split_ifs
      · exact Circle.exp_arg z
      · rw [Circle.exp_add, Circle.exp_two_pi, mul_one]
        exact Circle.exp_arg z
    let x := Real.tan ((5 * Real.pi / 4 - theta) / 4)
    have hatan : Real.arctan x = (5 * Real.pi / 4 - theta) / 4 :=
      Real.arctan_tan (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    refine ⟨x, ?_, ?_⟩
    · apply abs_le.mpr
      constructor
      · apply Real.arctan_strictMono.le_iff_le.mp
        rw [Real.arctan_neg, Real.arctan_one, hatan]
        linarith [htheta.2]
      · apply Real.arctan_strictMono.le_iff_le.mp
        rw [Real.arctan_one, hatan]
        linarith [htheta.1]
    · dsimp [angle]
      rw [hatan, show 5 * Real.pi / 4 - 4 * ((5 * Real.pi / 4 - theta) / 4) = theta by ring]
      exact hexp
  have htorusSurj : Function.Surjective torusMap := by
    intro z
    obtain ⟨a, ha, hea⟩ := Circle.surjOn_exp_neg_pi_pi (show z.1 ∈ (Set.univ : Set Circle) from trivial)
    obtain ⟨c, hc, hec⟩ := Circle.surjOn_exp_neg_pi_pi (show z.2 ∈ (Set.univ : Set Circle) from trivial)
    let w : ℂ := Complex.mk (a / Real.pi) (c / Real.pi)
    have hw : DiskSquare.maxAbs w ≤ 1 := by
      apply max_le
      · apply abs_le.mpr
        dsimp [w]
        constructor
        · apply (le_div_iff₀ Real.pi_pos).mpr
          nlinarith [ha.1]
        · apply (div_le_iff₀ Real.pi_pos).mpr
          nlinarith [ha.2]
      · apply abs_le.mpr
        dsimp [w]
        constructor
        · apply (le_div_iff₀ Real.pi_pos).mpr
          nlinarith [hc.1]
        · apply (div_le_iff₀ Real.pi_pos).mpr
          nlinarith [hc.2]
    have hproject : (Circle.exp (Real.pi * w.re), Circle.exp (Real.pi * w.im)) = z := by
      apply Prod.ext
      · dsimp [w]
        rw [mul_div_cancel₀ _ Real.pi_ne_zero]
        exact hea
      · dsimp [w]
        rw [mul_div_cancel₀ _ Real.pi_ne_zero]
        exact hec
    by_cases hwzero : w = 0
    · let x : DiskSquare.square := ⟨Complex.mk 0 (-1), by norm_num [DiskSquare.square, DiskSquare.maxAbs]⟩
      refine ⟨x, ?_⟩
      have h := (hcollapsed x).mpr (by rfl)
      rw [hwzero] at hproject
      exact h.trans (by simpa using hproject)
    · let r := DiskSquare.maxAbs w
      have hr : 0 < r := DiskSquare.maxAbs_pos hwzero
      let wb : DiskSquare.boundary := ⟨w / r, by
        exact (DiskSquare.maxAbs_div_of_pos w hr).trans (div_self hr.ne')⟩
      obtain ⟨x, hx, hax⟩ := hangleSurj (DiskSquare.circleBoundaryHomeomorph.symm wb)
      have hpx : perimeter x = wb := by
        dsimp [perimeter]
        rw [hax, Homeomorph.apply_symm_apply]
      let sq : DiskSquare.square := ⟨Complex.mk x (2 * r - 1), by
        change max |x| |2 * r - 1| ≤ 1
        apply max_le
        · exact hx
        · apply abs_le.mpr
          constructor <;> dsimp [r] at * <;> linarith⟩
      refine ⟨sq, ?_⟩
      have hrad : radial sq = w := by
        dsimp only [radial, sq]
        change (((2 * r - 1) + 1) / 2) • (perimeter x).val = w
        rw [show ((2 * r - 1) + 1) / 2 = r by ring, hpx]
        change r • (w / (r : ℂ)) = w
        rw [Complex.real_smul]
        field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
      change (Circle.exp (Real.pi * (radial sq).re), Circle.exp (Real.pi * (radial sq).im)) = z
      rw [hrad]
      exact hproject
  have htheta (u : ℝ) (hu : u ∈ Set.Icc 0 4) :
      -Real.pi / 4 + Real.pi / 8 * u ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4) := by
    constructor <;> nlinarith [hu.1, hu.2, Real.pi_pos]
  have hDtop (u : ℝ) (hu : u ∈ Set.Icc 0 4) :
      (d (Complex.ClosedUnitDisc.bdyPtOfReal (u / 7))).val =
        Complex.mk (-Real.tan (-Real.pi / 4 + Real.pi / 8 * u)) 1 := by
    rw [hdouter u hu]
    change (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi / 4 + Real.pi / 8 * u))).val = _
    rw [show Real.pi / 4 + Real.pi / 8 * u = Real.pi / 2 + (-Real.pi / 4 + Real.pi / 8 * u) by ring]
    exact htop _ (htheta u hu)
  have hRadTop (u : ℝ) (hu : u ∈ Set.Icc 0 4) :
      radial (d (Complex.ClosedUnitDisc.bdyPtOfReal (u / 7))) =
        (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi / 4 + Real.pi / 2 * u))).val := by
    have hatan : Real.arctan (-Real.tan (-Real.pi / 4 + Real.pi / 8 * u)) =
        -(-Real.pi / 4 + Real.pi / 8 * u) := by
      rw [Real.arctan_neg, Real.arctan_tan
        (by have h := htheta u hu; nlinarith [h.1, Real.pi_pos])
        (by have h := htheta u hu; nlinarith [h.2, Real.pi_pos])]
    have hrad : radial (d (Complex.ClosedUnitDisc.bdyPtOfReal (u / 7))) =
        (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi / 4 + Real.pi / 2 * u))).val := by
      dsimp only [radial, perimeter, angle]
      rw [hDtop u hu]
      simp only [show (Complex.mk (-Real.tan (-Real.pi / 4 + Real.pi / 8 * u)) 1).im = 1 from rfl,
        show (Complex.mk (-Real.tan (-Real.pi / 4 + Real.pi / 8 * u)) 1).re =
          -Real.tan (-Real.pi / 4 + Real.pi / 8 * u) from rfl]
      rw [hatan, show 5 * Real.pi / 4 - 4 * -(-Real.pi / 4 + Real.pi / 8 * u) =
          Real.pi / 4 + Real.pi / 2 * u by ring]
      norm_num
    exact hrad
  have hFtop (u : ℝ) (hu : u ∈ Set.Icc 0 4) :
      torusMap (d (Complex.ClosedUnitDisc.bdyPtOfReal (u / 7))) =
        (Circle.exp (Real.pi * (DiskSquare.circleBoundaryHomeomorph
            (Circle.exp (Real.pi / 4 + Real.pi / 2 * u))).val.re),
          Circle.exp (Real.pi * (DiskSquare.circleBoundaryHomeomorph
            (Circle.exp (Real.pi / 4 + Real.pi / 2 * u))).val.im)) := by
    have hatan : Real.arctan (-Real.tan (-Real.pi / 4 + Real.pi / 8 * u)) =
        -(-Real.pi / 4 + Real.pi / 8 * u) := by
      rw [Real.arctan_neg, Real.arctan_tan
        (by have h := htheta u hu; nlinarith [h.1, Real.pi_pos])
        (by have h := htheta u hu; nlinarith [h.2, Real.pi_pos])]
    have hrad : radial (d (Complex.ClosedUnitDisc.bdyPtOfReal (u / 7))) =
        (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi / 4 + Real.pi / 2 * u))).val := by
      dsimp only [radial, perimeter, angle]
      rw [hDtop u hu]
      simp only [show (Complex.mk (-Real.tan (-Real.pi / 4 + Real.pi / 8 * u)) 1).im = 1 from rfl,
        show (Complex.mk (-Real.tan (-Real.pi / 4 + Real.pi / 8 * u)) 1).re =
          -Real.tan (-Real.pi / 4 + Real.pi / 8 * u) from rfl]
      rw [hatan, show 5 * Real.pi / 4 - 4 * -(-Real.pi / 4 + Real.pi / 8 * u) =
          Real.pi / 4 + Real.pi / 2 * u by ring]
      norm_num
    change (Circle.exp (Real.pi * (radial _).re), Circle.exp (Real.pi * (radial _).im)) = _
    rw [hrad]
  have hlocaltheta (t : unitInterval) :
      -Real.pi / 4 + Real.pi / 2 * (t : ℝ) ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4) := by
    constructor <;> nlinarith [t.property.1, t.property.2, Real.pi_pos]
  have hDbottom (t : unitInterval) :
      (d (Complex.ClosedUnitDisc.bdyPtOfReal ((5 + (t : ℝ)) / 7))).val =
        Complex.mk (Real.tan (-Real.pi / 4 + Real.pi / 2 * t)) (-1) := by
    have h := hdside (5 : Fin 7) t
    norm_num [weights] at h
    rw [h, ← Circle.exp_add]
    change (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi / 4 + Real.pi / 8 * (8 + 4 * (t : ℝ))))).val = _
    rw [show Real.pi / 4 + Real.pi / 8 * (8 + 4 * (t : ℝ)) =
        3 * Real.pi / 2 + (-Real.pi / 4 + Real.pi / 2 * t) by ring]
    exact hbottom _ (hlocaltheta t)
  have hDleft (t : unitInterval) :
      (d (Complex.ClosedUnitDisc.bdyPtOfReal ((4 + (t : ℝ)) / 7))).val =
        Complex.mk (-1) (-Real.tan (-Real.pi / 4 + Real.pi / 2 * t)) := by
    have h := hdside (4 : Fin 7) t
    norm_num [weights] at h
    rw [h, ← Circle.exp_add]
    change (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi / 4 + Real.pi / 8 * (4 + 4 * (t : ℝ))))).val = _
    rw [show Real.pi / 4 + Real.pi / 8 * (4 + 4 * (t : ℝ)) =
        Real.pi + (-Real.pi / 4 + Real.pi / 2 * t) by ring]
    exact hleft _ (hlocaltheta t)
  have hDright (t : unitInterval) :
      (d (Complex.ClosedUnitDisc.bdyPtOfReal ((7 - (t : ℝ)) / 7))).val =
        Complex.mk 1 (-Real.tan (-Real.pi / 4 + Real.pi / 2 * t)) := by
    have h := hdside (6 : Fin 7) (unitInterval.symm t)
    norm_num [weights, unitInterval.coe_symm_eq] at h
    rw [show 7 - (t : ℝ) = 6 + (1 - (t : ℝ)) by ring, h, ← Circle.exp_add]
    change (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi / 4 + Real.pi / 8 * (12 + 4 * (1 - (t : ℝ)))))).val = _
    have he : Circle.exp (Real.pi / 4 + Real.pi / 8 * (12 + 4 * (1 - (t : ℝ)))) =
        Circle.exp (-(-Real.pi / 4 + Real.pi / 2 * t)) := by
      apply Circle.exp_eq_exp.mpr
      refine ⟨1, ?_⟩
      norm_num
      ring
    rw [he, hright _ (by have h := hlocaltheta t; constructor <;> linarith [h.1, h.2]), Real.tan_neg]
  have hexppi : Circle.exp Real.pi = Circle.exp (-Real.pi) := by
    apply Circle.exp_eq_exp.mpr
    refine ⟨1, ?_⟩
    norm_num
    ring
  have hgen : ∀ z w, OrientableRel 1 1 z w → torusMap (d z) = torusMap (d w) := by
    intro z w h
    cases h with
    | a t i =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      norm_num
      rw [hFtop t (by constructor <;> linarith [t.property.1, t.property.2]),
        hFtop (3 - (t : ℝ)) (by constructor <;> linarith [t.property.1, t.property.2])]
      have h1 := htop _ (hlocaltheta t)
      have h2 := hbottom (-(-Real.pi / 4 + Real.pi / 2 * t))
        (by have h := hlocaltheta t; constructor <;> linarith [h.1, h.2])
      rw [show Real.pi / 4 + Real.pi / 2 * (t : ℝ) =
        Real.pi / 2 + (-Real.pi / 4 + Real.pi / 2 * t) by ring, h1]
      rw [show Real.pi / 4 + Real.pi / 2 * (3 - (t : ℝ)) =
        3 * Real.pi / 2 + -(-Real.pi / 4 + Real.pi / 2 * t) by ring, h2]
      simp only [Real.tan_neg]
      apply Prod.ext
      · rfl
      · simpa using hexppi
    | b t i =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      norm_num
      rw [hFtop (1 + (t : ℝ)) (by constructor <;> linarith [t.property.1, t.property.2]),
        hFtop (4 - (t : ℝ)) (by constructor <;> linarith [t.property.1, t.property.2])]
      rw [show Real.pi / 4 + Real.pi / 2 * (1 + (t : ℝ)) =
        Real.pi + (-Real.pi / 4 + Real.pi / 2 * t) by ring, hleft _ (hlocaltheta t)]
      have he : Circle.exp (Real.pi / 4 + Real.pi / 2 * (4 - (t : ℝ))) =
          Circle.exp (-(-Real.pi / 4 + Real.pi / 2 * t)) := by
        apply Circle.exp_eq_exp.mpr
        refine ⟨1, ?_⟩
        norm_num
        ring
      rw [he, hright _ (by have h := hlocaltheta t; constructor <;> linarith [h.1, h.2]), Real.tan_neg]
      apply Prod.ext
      · simpa using hexppi.symm
      · rfl
    | c t i =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      norm_num
      have hleftperiod : Complex.ClosedUnitDisc.bdyPtOfReal (-(t : ℝ) / 7) =
          Complex.ClosedUnitDisc.bdyPtOfReal ((7 - (t : ℝ)) / 7) := by
        symm
        convert Complex.ClosedUnitDisc.bdyPtOfReal_add_int (-(t : ℝ) / 7) (1 : ℤ) using 1 <;> push_cast <;> ring
      have hrightperiod : Complex.ClosedUnitDisc.bdyPtOfReal (((t : ℝ) - 3) / 7) =
          Complex.ClosedUnitDisc.bdyPtOfReal ((4 + (t : ℝ)) / 7) := by
        symm
        convert Complex.ClosedUnitDisc.bdyPtOfReal_add_int (((t : ℝ) - 3) / 7) (1 : ℤ) using 1 <;> push_cast <;> ring
      rw [hleftperiod, hrightperiod]
      apply Eq.symm
      apply hsameSeam
      · rw [hDleft]
      · rw [hDright]
      · rw [hDleft, hDright]
  have hParameter (x : ℝ) (hx : |x| ≤ 1) : ∃ t : unitInterval,
      -Real.pi / 4 + Real.pi / 2 * (t : ℝ) = Real.arctan x := by
    have h := hatanbounds x hx
    let t : unitInterval := ⟨2 * (Real.arctan x + Real.pi / 4) / Real.pi, by
      constructor
      · apply (le_div_iff₀ Real.pi_pos).mpr
        nlinarith [h.1]
      · apply (div_le_iff₀ Real.pi_pos).mpr
        nlinarith [h.2]⟩
    refine ⟨t, ?_⟩
    dsimp [t]
    field_simp
    ring
  have hSeamQ (t : unitInterval) :
      Quot.mk (OrientableRel 1 1) (Complex.ClosedUnitDisc.bdyPtOfReal ((4 + (t : ℝ)) / 7)) =
        Quot.mk (OrientableRel 1 1) (Complex.ClosedUnitDisc.bdyPtOfReal ((7 - (t : ℝ)) / 7)) := by
    have h := Quot.sound (OrientableRel.c (p := 1) (n := 1) t (0 : Fin 1))
    norm_num at h
    have hl : Complex.ClosedUnitDisc.bdyPtOfReal (((t : ℝ) - 3) / 7) =
        Complex.ClosedUnitDisc.bdyPtOfReal ((4 + (t : ℝ)) / 7) := by
      symm
      convert Complex.ClosedUnitDisc.bdyPtOfReal_add_int (((t : ℝ) - 3) / 7) (1 : ℤ) using 1 <;> push_cast <;> ring
    have hr : Complex.ClosedUnitDisc.bdyPtOfReal (-(t : ℝ) / 7) =
        Complex.ClosedUnitDisc.bdyPtOfReal ((7 - (t : ℝ)) / 7) := by
      symm
      convert Complex.ClosedUnitDisc.bdyPtOfReal_add_int (-(t : ℝ) / 7) (1 : ℤ) using 1 <;> push_cast <;> ring
    rw [hl, hr] at h
    exact h.symm
  have hRelSeam (z w : Complex.ClosedUnitDisc)
      (hz : (d z).val.re = -1) (hw : (d w).val.re = 1)
      (hy : (d z).val.im = (d w).val.im) : Quot.mk (OrientableRel 1 1) z = Quot.mk (OrientableRel 1 1) w := by
    have hybound : |-(d z).val.im| ≤ 1 := by
      rw [abs_neg]
      exact DiskSquare.abs_im_le_maxAbs _ |>.trans (d z).property
    obtain ⟨t, ht⟩ := hParameter (-(d z).val.im) hybound
    have hdz : d (Complex.ClosedUnitDisc.bdyPtOfReal ((4 + (t : ℝ)) / 7)) = d z := by
      apply Subtype.ext
      rw [hDleft t, ht, Real.tan_arctan, neg_neg]
      apply Complex.ext
      · exact hz.symm
      · rfl
    have hdw : d (Complex.ClosedUnitDisc.bdyPtOfReal ((7 - (t : ℝ)) / 7)) = d w := by
      apply Subtype.ext
      rw [hDright t, ht, Real.tan_arctan, neg_neg]
      apply Complex.ext
      · exact hw.symm
      · exact hy
    rw [← d.injective hdz, ← d.injective hdw]
    exact hSeamQ t
  have hRelRadial (z w : Complex.ClosedUnitDisc)
      (hz : radial (d z) ≠ 0) (hzw : radial (d z) = radial (d w)) :
      Quot.mk (OrientableRel 1 1) z = Quot.mk (OrientableRel 1 1) w := by
    have hm : DiskSquare.maxAbs (radial (d z)) = DiskSquare.maxAbs (radial (d w)) := congrArg DiskSquare.maxAbs hzw
    rw [hradmax, hradmax] at hm
    have hy : (d z).val.im = (d w).val.im := by linarith
    have hpos : 0 < ((d z).val.im + 1) / 2 := by
      rw [← hradmax]
      exact DiskSquare.maxAbs_pos hz
    have hval : (perimeter (d z).val.re).val = (perimeter (d w).val.re).val := by
      dsimp [radial] at hzw
      rw [← hy] at hzw
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hpos.ne') hzw
    have hper : perimeter (d z).val.re = perimeter (d w).val.re := Subtype.ext hval
    have hang : angle (d z).val.re = angle (d w).val.re := DiskSquare.circleBoundaryHomeomorph.injective hper
    have hzx := DiskSquare.abs_re_le_maxAbs (d z).val |>.trans (d z).property
    have hwx := DiskSquare.abs_re_le_maxAbs (d w).val |>.trans (d w).property
    rcases hangleKernel _ _ hzx hwx hang with heq | hends | hends
    · have hd : d z = d w := by
        apply Subtype.ext
        exact Complex.ext heq hy
      exact congrArg (Quot.mk (OrientableRel 1 1)) (d.injective hd)
    · exact hRelSeam z w hends.1 hends.2 hy
    · exact (hRelSeam w z hends.2 hends.1 hy.symm).symm
  have hRadA (t : unitInterval) :
      radial (d (Complex.ClosedUnitDisc.bdyPtOfReal ((t : ℝ) / 7))) =
        Complex.mk (-Real.tan (-Real.pi / 4 + Real.pi / 2 * t)) 1 := by
    rw [hRadTop t (by constructor <;> linarith [t.property.1, t.property.2])]
    rw [show Real.pi / 4 + Real.pi / 2 * (t : ℝ) = Real.pi / 2 + (-Real.pi / 4 + Real.pi / 2 * t) by ring]
    exact htop _ (hlocaltheta t)
  have hRadAneg (t : unitInterval) :
      radial (d (Complex.ClosedUnitDisc.bdyPtOfReal ((3 - (t : ℝ)) / 7))) =
        Complex.mk (-Real.tan (-Real.pi / 4 + Real.pi / 2 * t)) (-1) := by
    rw [hRadTop (3 - (t : ℝ)) (by constructor <;> linarith [t.property.1, t.property.2])]
    rw [show Real.pi / 4 + Real.pi / 2 * (3 - (t : ℝ)) = 3 * Real.pi / 2 + -(-Real.pi / 4 + Real.pi / 2 * t) by ring]
    rw [hbottom _ (by have h := hlocaltheta t; constructor <;> linarith [h.1, h.2]), Real.tan_neg]
  have hRadB (t : unitInterval) :
      radial (d (Complex.ClosedUnitDisc.bdyPtOfReal ((1 + (t : ℝ)) / 7))) =
        Complex.mk (-1) (-Real.tan (-Real.pi / 4 + Real.pi / 2 * t)) := by
    rw [hRadTop (1 + (t : ℝ)) (by constructor <;> linarith [t.property.1, t.property.2])]
    rw [show Real.pi / 4 + Real.pi / 2 * (1 + (t : ℝ)) = Real.pi + (-Real.pi / 4 + Real.pi / 2 * t) by ring]
    exact hleft _ (hlocaltheta t)
  have hRadBneg (t : unitInterval) :
      radial (d (Complex.ClosedUnitDisc.bdyPtOfReal ((4 - (t : ℝ)) / 7))) =
        Complex.mk 1 (-Real.tan (-Real.pi / 4 + Real.pi / 2 * t)) := by
    rw [hRadTop (4 - (t : ℝ)) (by constructor <;> linarith [t.property.1, t.property.2])]
    have he : Circle.exp (Real.pi / 4 + Real.pi / 2 * (4 - (t : ℝ))) =
        Circle.exp (-(-Real.pi / 4 + Real.pi / 2 * t)) := by
      apply Circle.exp_eq_exp.mpr
      refine ⟨1, ?_⟩
      norm_num
      ring
    rw [he, hright _ (by have h := hlocaltheta t; constructor <;> linarith [h.1, h.2]), Real.tan_neg]
  have hRelH (z w : Complex.ClosedUnitDisc)
      (hz : (radial (d z)).im = 1) (hw : (radial (d w)).im = -1)
      (hx : (radial (d z)).re = (radial (d w)).re) :
      Quot.mk (OrientableRel 1 1) z = Quot.mk (OrientableRel 1 1) w := by
    have hbound : |-(radial (d z)).re| ≤ 1 := by
      rw [abs_neg]
      exact (DiskSquare.abs_re_le_maxAbs _).trans ((hradmax _).trans_le (hradbounds _).2)
    obtain ⟨t, ht⟩ := hParameter (-(radial (d z)).re) hbound
    have hrz : radial (d z) = radial (d (Complex.ClosedUnitDisc.bdyPtOfReal ((t : ℝ) / 7))) := by
      rw [hRadA t, ht, Real.tan_arctan, neg_neg]
      apply Complex.ext
      · rfl
      · exact hz
    have hrw : radial (d w) = radial (d (Complex.ClosedUnitDisc.bdyPtOfReal ((3 - (t : ℝ)) / 7))) := by
      rw [hRadAneg t, ht, Real.tan_arctan, neg_neg]
      apply Complex.ext
      · exact hx.symm
      · exact hw
    have hz0 : radial (d z) ≠ 0 := by
      intro h
      have hh := congrArg Complex.im h
      rw [hz] at hh
      norm_num at hh
    have hw0 : radial (d w) ≠ 0 := by
      intro h
      have hh := congrArg Complex.im h
      rw [hw] at hh
      norm_num at hh
    have h := Quot.sound (OrientableRel.a (p := 1) (n := 1) t (0 : Fin 1))
    norm_num at h
    exact (hRelRadial z _ hz0 hrz).trans (h.trans (hRelRadial w _ hw0 hrw).symm)
  have hRelV (z w : Complex.ClosedUnitDisc)
      (hz : (radial (d z)).re = -1) (hw : (radial (d w)).re = 1)
      (hy : (radial (d z)).im = (radial (d w)).im) :
      Quot.mk (OrientableRel 1 1) z = Quot.mk (OrientableRel 1 1) w := by
    have hbound : |-(radial (d z)).im| ≤ 1 := by
      rw [abs_neg]
      exact (DiskSquare.abs_im_le_maxAbs _).trans ((hradmax _).trans_le (hradbounds _).2)
    obtain ⟨t, ht⟩ := hParameter (-(radial (d z)).im) hbound
    have hrz : radial (d z) = radial (d (Complex.ClosedUnitDisc.bdyPtOfReal ((1 + (t : ℝ)) / 7))) := by
      rw [hRadB t, ht, Real.tan_arctan, neg_neg]
      apply Complex.ext
      · exact hz
      · rfl
    have hrw : radial (d w) = radial (d (Complex.ClosedUnitDisc.bdyPtOfReal ((4 - (t : ℝ)) / 7))) := by
      rw [hRadBneg t, ht, Real.tan_arctan, neg_neg]
      apply Complex.ext
      · exact hw
      · exact hy.symm
    have hz0 : radial (d z) ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      rw [hz] at hh
      norm_num at hh
    have hw0 : radial (d w) ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      rw [hw] at hh
      norm_num at hh
    have h := Quot.sound (OrientableRel.b (p := 1) (n := 1) t (0 : Fin 1))
    norm_num at h
    exact (hRelRadial z _ hz0 hrz).trans (h.trans (hRelRadial w _ hw0 hrw).symm)
  let f : Quot (OrientableRel 1 1) → Circle × Circle :=
    Quot.lift (torusMap ∘ d) hgen
  have hfcont : Continuous f := continuous_quot_lift hgen (htoruscont.comp d.continuous)
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := htorusSurj y
    refine ⟨Quot.mk _ (d.symm x), ?_⟩
    change torusMap (d (d.symm x)) = y
    rw [Homeomorph.apply_symm_apply]
    exact hx
  let actualBoundary : Set (Quot (OrientableRel 1 1)) := ActualOneBoundaryOrientableBoundary 1
  have hbottomperiod (t : unitInterval) :
      Complex.ClosedUnitDisc.bdyPtOfReal ((5 + (t : ℝ)) / 7) =
        Complex.ClosedUnitDisc.bdyPtOfReal (-(1 + (unitInterval.symm t : ℝ)) / 7) := by
    convert Complex.ClosedUnitDisc.bdyPtOfReal_add_int
      (-(1 + (unitInterval.symm t : ℝ)) / 7) (1 : ℤ) using 1 <;>
      simp only [unitInterval.coe_symm_eq, Int.cast_one] <;> congr 1 <;> ring
  have hcollapsedBoundary (q : Quot (OrientableRel 1 1)) :
      f q = (1,1) ↔ q ∈ actualBoundary := by
    constructor
    · induction q using Quot.inductionOn with
      | _ z =>
        intro hz
        have hzy : (d z).val.im = -1 := (hcollapsed (d z)).mp hz
        have hzx : |(d z).val.re| ≤ 1 :=
          DiskSquare.abs_re_le_maxAbs _ |>.trans (d z).property
        have hatan := hatanbounds (d z).val.re hzx
        let t : unitInterval := ⟨2 * (Real.arctan (d z).val.re + Real.pi / 4) / Real.pi, by
          constructor
          · apply (le_div_iff₀ Real.pi_pos).mpr
            nlinarith [hatan.1]
          · apply (div_le_iff₀ Real.pi_pos).mpr
            nlinarith [hatan.2]⟩
        have hthetaeq : -Real.pi / 4 + Real.pi / 2 * (t : ℝ) = Real.arctan (d z).val.re := by
          dsimp [t]
          field_simp
          ring
        have hd : d (Complex.ClosedUnitDisc.bdyPtOfReal ((5 + (t : ℝ)) / 7)) = d z := by
          apply Subtype.ext
          rw [hDbottom t, hthetaeq, Real.tan_arctan]
          apply Complex.ext
          · rfl
          · exact hzy.symm
        have hzpoint := d.injective hd
        refine ⟨unitInterval.symm t, ?_⟩
        change Quot.mk (OrientableRel 1 1)
          (Complex.ClosedUnitDisc.bdyPtOfReal (-(1 + (unitInterval.symm t : ℝ)) / (4 * ((1 : ℕ) : ℝ) + 3))) = _
        norm_num only [Nat.cast_one, mul_one]
        rw [← hbottomperiod t, hzpoint]
    · rintro ⟨t, rfl⟩
      have hb := hDbottom (unitInterval.symm t)
      have hperiod := hbottomperiod (unitInterval.symm t)
      simp only [unitInterval.symm_symm] at hperiod
      change torusMap (d (Complex.ClosedUnitDisc.bdyPtOfReal (-(1 + (t : ℝ)) / (4 * ((1 : ℕ) : ℝ) + 3)))) = _
      norm_num only [Nat.cast_one, mul_one]
      rw [← hperiod]
      apply (hcollapsed _).mpr
      rw [hb]
  have hRadSurj (v : ℂ) (hv : DiskSquare.maxAbs v ≤ 1) :
      ∃ z : Complex.ClosedUnitDisc, radial (d z) = v := by
    by_cases hv0 : v = 0
    · let sq : DiskSquare.square := ⟨Complex.mk 0 (-1), by norm_num [DiskSquare.square, DiskSquare.maxAbs]⟩
      refine ⟨d.symm sq, ?_⟩
      rw [Homeomorph.apply_symm_apply, hv0]
      simp [radial, sq]
    · let r := DiskSquare.maxAbs v
      have hr : 0 < r := DiskSquare.maxAbs_pos hv0
      let vb : DiskSquare.boundary := ⟨v / r, by
        exact (DiskSquare.maxAbs_div_of_pos v hr).trans (div_self hr.ne')⟩
      obtain ⟨x, hx, hax⟩ := hangleSurj (DiskSquare.circleBoundaryHomeomorph.symm vb)
      have hpx : perimeter x = vb := by
        dsimp [perimeter]
        rw [hax, Homeomorph.apply_symm_apply]
      let sq : DiskSquare.square := ⟨Complex.mk x (2 * r - 1), by
        change max |x| |2 * r - 1| ≤ 1
        apply max_le
        · exact hx
        · apply abs_le.mpr
          constructor <;> dsimp [r] at * <;> linarith⟩
      refine ⟨d.symm sq, ?_⟩
      rw [Homeomorph.apply_symm_apply]
      dsimp only [radial, sq]
      rw [show ((2 * r - 1) + 1) / 2 = r by ring, hpx]
      change r • (v / (r : ℂ)) = v
      rw [Complex.real_smul]
      field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
  have hCoordKernel (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
      (h : Circle.exp (Real.pi * x) = Circle.exp (Real.pi * y)) :
      x = y ∨ (x = 1 ∧ y = -1) ∨ (x = -1 ∧ y = 1) := by
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp h
    have hxy : x = y + 2 * (k : ℝ) := by nlinarith [Real.pi_pos]
    have hxb := abs_le.mp hx
    have hyb := abs_le.mp hy
    have hklo : (-1 : ℤ) ≤ k := by
      have : (-1 : ℝ) ≤ (k : ℝ) := by linarith
      exact_mod_cast this
    have hkhi : k ≤ (1 : ℤ) := by
      have : (k : ℝ) ≤ (1 : ℝ) := by linarith
      exact_mod_cast this
    have hcases : k = 0 ∨ k = 1 ∨ k = -1 := by omega
    rcases hcases with hk0 | hk1 | hkn
    · left
      simpa [hk0] using hxy
    · right; left
      simp only [hk1, Int.cast_one, mul_one] at hxy
      constructor <;> linarith
    · right; right
      simp only [hkn, Int.cast_neg, Int.cast_one, mul_neg_one] at hxy
      constructor <;> linarith
  have hfFiberInjective (q r : Quot (OrientableRel 1 1))
      (hq : f q ≠ (1,1)) (hqr : f q = f r) : q = r := by
    induction q using Quot.inductionOn with
    | _ z =>
      induction r using Quot.inductionOn with
      | _ w =>
        have hz0 : radial (d z) ≠ 0 := by
          intro hz
          apply hq
          change torusMap (d z) = (1,1)
          simp [torusMap, hz]
        have hzb : DiskSquare.maxAbs (radial (d z)) ≤ 1 := (hradmax _).trans_le (hradbounds _).2
        have hwb : DiskSquare.maxAbs (radial (d w)) ≤ 1 := (hradmax _).trans_le (hradbounds _).2
        have hx := hCoordKernel (radial (d z)).re (radial (d w)).re
          ((DiskSquare.abs_re_le_maxAbs _).trans hzb) ((DiskSquare.abs_re_le_maxAbs _).trans hwb)
          (congrArg Prod.fst hqr)
        have hy := hCoordKernel (radial (d z)).im (radial (d w)).im
          ((DiskSquare.abs_im_le_maxAbs _).trans hzb) ((DiskSquare.abs_im_le_maxAbs _).trans hwb)
          (congrArg Prod.snd hqr)
        let mid : ℂ := Complex.mk (radial (d z)).re (radial (d w)).im
        have hmid : DiskSquare.maxAbs mid ≤ 1 :=
          max_le ((DiskSquare.abs_re_le_maxAbs (radial (d z))).trans hzb)
            ((DiskSquare.abs_im_le_maxAbs (radial (d w))).trans hwb)
        obtain ⟨m, hm⟩ := hRadSurj mid hmid
        have hmre : (radial (d m)).re = (radial (d z)).re := by simpa [mid] using congrArg Complex.re hm
        have hmim : (radial (d m)).im = (radial (d w)).im := by simpa [mid] using congrArg Complex.im hm
        have hzm : Quot.mk (OrientableRel 1 1) z = Quot.mk (OrientableRel 1 1) m := by
          rcases hy with heq | hends | hends
          · apply hRelRadial z m hz0
            exact Complex.ext hmre.symm (heq.trans hmim.symm)
          · exact hRelH z m hends.1 (hmim.trans hends.2) hmre.symm
          · exact (hRelH m z (hmim.trans hends.2) hends.1 hmre).symm
        have hm0 : radial (d m) ≠ 0 := by
          intro hzero
          apply hq
          rw [hzm]
          change torusMap (d m) = (1,1)
          simp [torusMap, hzero]
        have hmw : Quot.mk (OrientableRel 1 1) m = Quot.mk (OrientableRel 1 1) w := by
          rcases hx with heq | hends | hends
          · apply hRelRadial m w hm0
            exact Complex.ext (hmre.trans heq) hmim
          · exact (hRelV w m hends.2 (hmre.trans hends.1) hmim.symm).symm
          · exact hRelV m w (hmre.trans hends.1) hends.2 hmim
        exact hzm.trans hmw
  let targetSet : Set (Circle × Circle) := {z | z ≠ (1,1)}
  let fr := targetSet.restrictPreimage f
  have hfrcont : Continuous fr := hfcont.restrictPreimage
  have hfrclosed : IsClosedMap fr := hfcont.isClosedMap.restrictPreimage targetSet
  have hfrbij : Function.Bijective fr := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hfFiberInjective x.val y.val x.property (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx⟩ := hfsurj y.val
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change f x ≠ (1,1)
        rw [hx]
        exact y.property
      · exact Subtype.ext hx
  let eOpen : {q : Quot (OrientableRel 1 1) // q ∉ actualBoundary} ≃ₜ
      {q : Quot (OrientableRel 1 1) // f q ∈ targetSet} :=
    (Homeomorph.refl _).subtype (fun q => (not_congr (hcollapsedBoundary q)).symm)
  have hModel : Nonempty ({q : Quot (OrientableRel 1 1) // q ∉ actualBoundary} ≃ₜ
      {z : Circle × Circle // z ≠ (1,1)}) :=
    ⟨eOpen.trans ((Equiv.ofBijective fr hfrbij).toHomeomorphOfContinuousClosed hfrcont hfrclosed)⟩
  exact hModel

end CurveComplex.Hyperbolic
