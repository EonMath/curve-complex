import CurveComplexGenusTwo.Topology.ActualBoundaryModels.Definitions
import ClassificationOfSurfaces.LeanEval.ChallengeDeps
import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage
import ClassificationOfSurfaces.TriangleCell
import ClassificationOfSurfaces.RepresentativeCarrier
import ClassificationOfSurfaces.Moise.FacewiseComparison
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace CurveComplex.Hyperbolic
open Set Topology CategoryTheory
open LeanEval.Topology.ClassificationOfSurfaces
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]



theorem actual_zero_handle_one_boundary_model_closed_disc :
    ∃ d : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
        Quot (OrientableRel 0 1),
      ∀ x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
        d x ∈ ActualOneBoundaryOrientableBoundary 0 ↔
          x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  classical
  let T := TriangleCell.StandardTriangle
  let a : Fin 3 → T → ℝ := fun j z => Moise.LocallyFiniteTriangleComplex.triCoord j z.val
  have hac (j : Fin 3) : Continuous (a j) :=
    (Moise.LocallyFiniteTriangleComplex.continuous_triCoord j).comp continuous_subtype_val
  have hann (z : T) (j : Fin 3) : 0 ≤ a j z :=
    (Moise.LocallyFiniteTriangleComplex.mem_standardFaceRegion_iff.mp z.property) j
  have hasum (z : T) : a 0 z + a 1 z + a 2 z = 1 := by
    simpa [a, Fin.sum_univ_three, add_assoc] using
      Moise.LocallyFiniteTriangleComplex.sum_triCoord z.val
  have haext (z w : T) (h1 : a 1 z = a 1 w) (h2 : a 2 z = a 2 w) : z = w := by
    apply Subtype.ext
    apply Moise.LocallyFiniteTriangleComplex.stdTriBasis.ext_elem
    intro j
    fin_cases j
    · change a 0 z = a 0 w
      linarith [hasum z, hasum w]
    · exact h1
    · exact h2
  let radius : T → ℝ := fun z => a 1 z + a 2 z
  have hrc : Continuous radius := (hac 1).add (hac 2)
  have hrbounds (z : T) : 0 ≤ radius z ∧ radius z ≤ 1 := by
    dsimp [radius]
    constructor
    · exact add_nonneg (hann z 1) (hann z 2)
    · linarith [hasum z, hann z 0]
  let raw : T → ℂ := fun z => (radius z : ℂ) *
    (Circle.exp (2 * Real.pi * (a 2 z / radius z)) : ℂ)
  have hrawnorm (z : T) : ‖raw z‖ = radius z := by
    dsimp only [raw]
    rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hrbounds z).1]
  have hrawcont : Continuous raw := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : radius z = 0
    · have hrawz : raw z = 0 := by simp [raw, hz]
      change Filter.Tendsto raw (𝓝 z) (𝓝 (raw z))
      rw [hrawz]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [hrawnorm, hz] using
        (show Filter.Tendsto radius (𝓝 z) (𝓝 (radius z)) from hrc.continuousAt)
    · have hc : ContinuousAt (fun w : T =>
          (Circle.exp (2 * Real.pi * (a 2 w / radius w)) : ℂ)) z := by
        exact continuous_subtype_val.continuousAt.comp
          (Circle.exp.continuous.continuousAt.comp
            (continuousAt_const.mul ((hac 2).continuousAt.div hrc.continuousAt hz)))
      exact (Complex.continuous_ofReal.comp hrc).continuousAt.mul hc
  let F : T → Complex.ClosedUnitDisc := fun z => ⟨raw z, by
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [hrawnorm]
    exact (hrbounds z).2⟩
  have hFc : Continuous F := hrawcont.subtype_mk _
  let point (r u : ℝ) : Moise.Plane := AffineMap.lineMap
      (Moise.standardTriangleVertex 0)
      (AffineMap.lineMap (Moise.standardTriangleVertex 1)
        (Moise.standardTriangleVertex 2) u) r
  have hpointcoords (r u : ℝ) :
      Moise.LocallyFiniteTriangleComplex.triCoord 0 (point r u) = 1-r ∧
      Moise.LocallyFiniteTriangleComplex.triCoord 1 (point r u) = r*(1-u) ∧
      Moise.LocallyFiniteTriangleComplex.triCoord 2 (point r u) = r*u := by
    dsimp only [point]
    simp only [Moise.LocallyFiniteTriangleComplex.triCoord_lineMap]
    simp [
      Moise.LocallyFiniteTriangleComplex.triCoord_vertex_ne,
      AffineMap.lineMap_apply_module]
  have hpointmem (r u : ℝ) (hr : r ∈ Icc (0 : ℝ) 1)
      (hu : u ∈ Icc (0 : ℝ) 1) : point r u ∈ TriangleCell.StandardTriangle := by
    apply Moise.LocallyFiniteTriangleComplex.mem_standardFaceRegion_iff.mpr
    intro j
    fin_cases j
    · change 0 ≤ Moise.LocallyFiniteTriangleComplex.triCoord 0 (point r u)
      rw [(hpointcoords r u).1]; linarith [hr.2]
    · change 0 ≤ Moise.LocallyFiniteTriangleComplex.triCoord 1 (point r u)
      rw [(hpointcoords r u).2.1]; exact mul_nonneg hr.1 (sub_nonneg.mpr hu.2)
    · change 0 ≤ Moise.LocallyFiniteTriangleComplex.triCoord 2 (point r u)
      rw [(hpointcoords r u).2.2]; exact mul_nonneg hr.1 hu.1
  let P (r u : ℝ) (hr : r ∈ Icc (0 : ℝ) 1)
      (hu : u ∈ Icc (0 : ℝ) 1) : T := ⟨point r u, hpointmem r u hr hu⟩
  have hPr (r u : ℝ) (hr : r ∈ Icc (0 : ℝ) 1)
      (hu : u ∈ Icc (0 : ℝ) 1) : radius (P r u hr hu) = r := by
    change Moise.LocallyFiniteTriangleComplex.triCoord 1 (point r u) +
      Moise.LocallyFiniteTriangleComplex.triCoord 2 (point r u) = r
    rw [(hpointcoords r u).2.1, (hpointcoords r u).2.2]
    ring
  have hPF (r u : ℝ) (hr : r ∈ Icc (0 : ℝ) 1)
      (hu : u ∈ Icc (0 : ℝ) 1) :
      (F (P r u hr hu)).val = (r : ℂ) * (Circle.exp (2 * Real.pi * u) : ℂ) := by
    change raw (P r u hr hu) = _
    dsimp only [raw]
    rw [hPr r u hr hu]
    by_cases hr0 : r = 0
    · simp [hr0]
    · have ha : a 2 (P r u hr hu) = r*u := (hpointcoords r u).2.2
      rw [ha, mul_div_cancel_left₀ u hr0]
  let conjD : Complex.ClosedUnitDisc ≃ₜ Complex.ClosedUnitDisc :=
    Complex.conjCLE.toHomeomorph.subtype (fun z => by
      change z ∈ Metric.closedBall 0 1 ↔ (starRingEnd ℂ) z ∈ Metric.closedBall 0 1
      simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj])
  have hconjbdy (u : ℝ) : conjD (Complex.ClosedUnitDisc.bdyPtOfReal (-u)) =
      Complex.ClosedUnitDisc.bdyPtOfReal u := by
    apply Subtype.ext
    change (starRingEnd ℂ) ((Real.fourierChar (-u) : Circle) : ℂ) =
      (Real.fourierChar u : ℂ)
    change (starRingEnd ℂ) (Complex.exp ((2 * Real.pi * (-u) : ℝ) * Complex.I)) =
      Complex.exp ((2 * Real.pi * u : ℝ) * Complex.I)
    rw [← Complex.exp_conj]
    congr 1
    simp
    left
    exact Complex.conj_ofReal 2
  let d : Complex.ClosedUnitDisc ≃ₜ T := conjD.trans
    ((PolygonCell.closedUnitDiscHomeomorph 3).symm.trans TriangleCell.cellHomeomorph)
  have hdside (i : Fin 3) (t : unitInterval) :
      (d (Complex.ClosedUnitDisc.bdyPtOfReal (-((i : ℝ)+(t : ℝ))/3))).val =
      AffineMap.lineMap (Moise.standardTriangleVertex i)
        (Moise.standardTriangleVertex (finRotate 3 i)) (t : ℝ) := by
    change (TriangleCell.cellHomeomorph
      ((PolygonCell.closedUnitDiscHomeomorph 3).symm
        (conjD (Complex.ClosedUnitDisc.bdyPtOfReal _)))).val = _
    have hu : -((i : ℝ) + (t : ℝ)) / 3 = -(((i : ℝ)+(t : ℝ))/3) := by ring
    rw [hu, hconjbdy]
    have hs := PolygonCell.closedUnitDiscHomeomorph_side (m := 3) i t
    norm_num at hs
    rw [← hs, Homeomorph.symm_apply_apply, TriangleCell.cellHomeomorph_side]
  have hdcoords (i : Fin 3) (t : unitInterval) (j : Fin 3) :
      a j (d (Complex.ClosedUnitDisc.bdyPtOfReal (-((i : ℝ)+(t : ℝ))/3))) =
      (1-(t : ℝ)) * (if j = i then 1 else 0) +
      (t : ℝ) * (if j = finRotate 3 i then 1 else 0) := by
    dsimp only [a]
    rw [hdside, Moise.LocallyFiniteTriangleComplex.triCoord_lineMap]
    have hv (k : Fin 3) : Moise.LocallyFiniteTriangleComplex.triCoord j
        (Moise.standardTriangleVertex k) = if j=k then 1 else 0 := by
      split_ifs with h
      · subst k; exact Moise.LocallyFiniteTriangleComplex.triCoord_vertex_self j
      · exact Moise.LocallyFiniteTriangleComplex.triCoord_vertex_ne h
    rw [hv, hv, AffineMap.lineMap_apply_module]
    rfl
  have hdP0 (t : unitInterval) :
      d (Complex.ClosedUnitDisc.bdyPtOfReal (-(t : ℝ)/3)) =
        P t 0 t.property (by norm_num) := by
    apply haext
    · have h := hdcoords 0 t 1
      norm_num at h
      change a 1 _ = Moise.LocallyFiniteTriangleComplex.triCoord 1 (point t 0)
      rw [(hpointcoords t 0).2.1]
      simpa using h
    · have h := hdcoords 0 t 2
      norm_num at h
      change a 2 _ = Moise.LocallyFiniteTriangleComplex.triCoord 2 (point t 0)
      rw [(hpointcoords t 0).2.2]
      simpa using h
  have hdP1 (t : unitInterval) :
      d (Complex.ClosedUnitDisc.bdyPtOfReal (-(3-(t : ℝ))/3)) =
        P t 1 t.property (by norm_num) := by
    have he : -(3-(t : ℝ))/3 = -((2 : Fin 3)+(unitInterval.symm t : ℝ))/3 := by
      simp only [unitInterval.coe_symm_eq]; norm_num; ring
    rw [he]
    apply haext
    · have h := hdcoords 2 (unitInterval.symm t) 1
      norm_num at h
      change a 1 _ = Moise.LocallyFiniteTriangleComplex.triCoord 1 (point t 1)
      rw [(hpointcoords t 1).2.1]
      simpa using h
    · have h := hdcoords 2 (unitInterval.symm t) 2
      norm_num [unitInterval.coe_symm_eq] at h
      change a 2 _ = Moise.LocallyFiniteTriangleComplex.triCoord 2 (point t 1)
      rw [(hpointcoords t 1).2.2]
      simpa using h
  have hdPH (t : unitInterval) :
      d (Complex.ClosedUnitDisc.bdyPtOfReal (-(1+(t : ℝ))/3)) =
        P 1 t (by norm_num) t.property := by
    apply haext
    · have h := hdcoords 1 t 1
      norm_num at h
      change a 1 _ = Moise.LocallyFiniteTriangleComplex.triCoord 1 (point 1 t)
      rw [(hpointcoords 1 t).2.1]
      simpa using h
    · have h := hdcoords 1 t 2
      norm_num at h
      change a 2 _ = Moise.LocallyFiniteTriangleComplex.triCoord 2 (point 1 t)
      rw [(hpointcoords 1 t).2.2]
      simpa using h
  have hgen (z w : Complex.ClosedUnitDisc) (h : OrientableRel 0 1 z w) :
      F (d z) = F (d w) := by
    cases h with
    | a t i => exact Fin.elim0 i
    | b t i => exact Fin.elim0 i
    | c t i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      norm_num only [Fin.val_zero, Nat.cast_zero, Nat.cast_one, mul_zero,
        mul_one, zero_add]
      apply Subtype.ext
      rw [hdP0, hdP1, hPF t 0 t.property (by norm_num),
        hPF t 1 t.property (by norm_num)]
      simp
  let f : Quot (OrientableRel 0 1) → Complex.ClosedUnitDisc := Quot.lift
      (F ∘ d) hgen
  have hfc : Continuous f := continuous_quot_lift _ (hFc.comp d.continuous)
  have hunitSurj (c : Circle) : ∃ u : ℝ, u ∈ Icc (0 : ℝ) 1 ∧
      Circle.exp (2 * Real.pi*u) = c := by
    let theta := if 0 ≤ c.val.arg then c.val.arg else c.val.arg+2*Real.pi
    have ht : 0 ≤ theta ∧ theta ≤ 2*Real.pi := by
      dsimp [theta]
      split_ifs <;> constructor <;>
        linarith [Complex.neg_pi_lt_arg c.val, Complex.arg_le_pi c.val, Real.pi_pos]
    refine ⟨theta/(2*Real.pi), ⟨div_nonneg ht.1 (by positivity),
      (div_le_one₀ (by positivity)).mpr ht.2⟩, ?_⟩
    rw [mul_div_cancel₀ theta (by positivity)]
    dsimp [theta]
    split_ifs
    · exact Circle.exp_arg c
    · rw [Circle.exp_add, Circle.exp_two_pi, mul_one]; exact Circle.exp_arg c
  have hFsurj : Function.Surjective F := by
    intro z
    have hr : ‖z.val‖ ∈ Icc (0 : ℝ) 1 := ⟨norm_nonneg _, by
      simpa only [Metric.mem_closedBall, dist_zero_right] using z.property⟩
    by_cases hz : z.val = 0
    · refine ⟨P 0 0 (by norm_num) (by norm_num), ?_⟩
      apply Subtype.ext
      rw [hPF 0 0 (by norm_num) (by norm_num)]
      simp [hz]
    · let c := Circle.direction z.val hz
      obtain ⟨u,hu,he⟩ := hunitSurj c
      refine ⟨P ‖z.val‖ u hr hu, ?_⟩
      apply Subtype.ext
      rw [hPF ‖z.val‖ u hr hu, he]
      change (‖z.val‖ : ℂ) * (z.val / ‖z.val‖) = z.val
      field_simp [norm_ne_zero_iff.mpr hz]
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨w,hw⟩ := hFsurj z
    refine ⟨Quot.mk _ (d.symm w), ?_⟩
    change F (d (d.symm w)) = z
    rw [Homeomorph.apply_symm_apply, hw]
  have huBounds (z : T) (hr : 0 < radius z) :
      a 2 z / radius z ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (hann z 2) hr.le
    · apply (div_le_one₀ hr).mpr
      dsimp [radius]
      linarith [hann z 1]
  have hrepresent (z : T) (hr : 0 < radius z) :
      z = P (radius z) (a 2 z / radius z) (hrbounds z) (huBounds z hr) := by
    apply haext
    · change a 1 z = Moise.LocallyFiniteTriangleComplex.triCoord 1
        (point (radius z) (a 2 z / radius z))
      rw [(hpointcoords _ _).2.1]
      field_simp
      dsimp [radius]
      ring
    · change a 2 z = Moise.LocallyFiniteTriangleComplex.triCoord 2
        (point (radius z) (a 2 z / radius z))
      rw [(hpointcoords _ _).2.2]
      field_simp
  have hunitKernel (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
      (hv : v ∈ Icc (0 : ℝ) 1)
      (he : Circle.exp (2*Real.pi*u) = Circle.exp (2*Real.pi*v)) :
      u=v ∨ (u=0 ∧ v=1) ∨ (u=1 ∧ v=0) := by
    obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp he
    have huv : u=v+(k : ℝ) := by nlinarith [Real.pi_pos]
    have klo : (-1 : ℤ) ≤ k := by
      have : (-1 : ℝ) ≤ (k : ℝ) := by linarith [hu.1,hv.2]
      exact_mod_cast this
    have khi : k ≤ (1 : ℤ) := by
      have : (k : ℝ) ≤ (1 : ℝ) := by linarith [hu.2,hv.1]
      exact_mod_cast this
    have hcases : k=0 ∨ k= -1 ∨ k=1 := by omega
    rcases hcases with rfl | rfl | rfl
    · left; simpa using huv
    · right; left
      norm_num at huv
      constructor <;> linarith [hu.1,hv.2]
    · right; right
      norm_num at huv
      constructor <;> linarith [hu.2,hv.1]
  let q : T → Quot (OrientableRel 0 1) := fun z => Quot.mk _ (d.symm z)
  have hqseam (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      q (P r 0 hr (by norm_num)) = q (P r 1 hr (by norm_num)) := by
    let t : unitInterval := ⟨r,hr⟩
    dsimp only [q]
    rw [← hdP0 t, ← hdP1 t, Homeomorph.symm_apply_apply,
      Homeomorph.symm_apply_apply]
    have h := Quot.sound (OrientableRel.c (p := 0) (n := 1) t (0 : Fin 1))
    norm_num at h
    convert h using 1 <;> congr 2 <;> ring
  have hFfiber (z w : T) (he : F z = F w) : q z = q w := by
    have hr : radius z = radius w := by
      have hn := congrArg (fun x : Complex.ClosedUnitDisc => ‖x.val‖) he
      exact (hrawnorm z).symm.trans (hn.trans (hrawnorm w))
    by_cases hz : radius z = 0
    · have hw : radius w = 0 := hr.symm.trans hz
      have h1 : a 1 z = a 1 w := by
        dsimp [radius] at hz hw
        linarith [hann z 1,hann z 2,hann w 1,hann w 2]
      have h2 : a 2 z = a 2 w := by
        dsimp [radius] at hz hw
        linarith [hann z 1,hann z 2,hann w 1,hann w 2]
      exact congrArg q (haext z w h1 h2)
    · have hrz : 0 < radius z := lt_of_le_of_ne (hrbounds z).1 (Ne.symm hz)
      have hrw : 0 < radius w := hr ▸ hrz
      let u := a 2 z / radius z
      let v := a 2 w / radius w
      have huc : u ∈ Icc (0 : ℝ) 1 := huBounds z hrz
      have hvc : v ∈ Icc (0 : ℝ) 1 := huBounds w hrw
      have hec : Circle.exp (2*Real.pi*u) = Circle.exp (2*Real.pi*v) := by
        apply Subtype.ext
        have heval := congrArg Subtype.val he
        change raw z = raw w at heval
        change (radius z : ℂ) * (Circle.exp (2*Real.pi*u) : ℂ) =
          (radius w : ℂ) * (Circle.exp (2*Real.pi*v) : ℂ) at heval
        rw [← hr] at heval
        exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hz) heval
      have hzP := hrepresent z hrz
      have hwP := hrepresent w hrw
      rcases hunitKernel u v huc hvc hec with huv | huv | huv
      · have hzw : z=w := by
          rw [hzP,hwP]
          apply Subtype.ext
          change point (radius z) u = point (radius w) v
          rw [hr,huv]
        exact congrArg q hzw
      · have hzp : z=P (radius z) 0 (hrbounds z) (by norm_num) := by
          exact hzP.trans (by
            apply Subtype.ext
            change point (radius z) u = point (radius z) _
            rw [huv.1])
        have hwp : w=P (radius z) 1 (hrbounds z) (by norm_num) := by
          exact hwP.trans (by
            apply Subtype.ext
            change point (radius w) v = point (radius z) _
            rw [← hr, huv.2])
        rw [hzp,hwp]
        exact hqseam (radius z) (hrbounds z)
      · have hzp : z=P (radius z) 1 (hrbounds z) (by norm_num) := by
          exact hzP.trans (by
            apply Subtype.ext
            change point (radius z) u = point (radius z) _
            rw [huv.1])
        have hwp : w=P (radius z) 0 (hrbounds z) (by norm_num) := by
          exact hwP.trans (by
            apply Subtype.ext
            change point (radius w) v = point (radius z) _
            rw [← hr, huv.2])
        rw [hzp,hwp]
        exact (hqseam (radius z) (hrbounds z)).symm
  have hfinj : Function.Injective f := by
    intro x y h
    induction x using Quot.inductionOn with
    | _ z =>
      induction y using Quot.inductionOn with
      | _ w =>
        have hq := hFfiber (d z) (d w) h
        simpa only [q, Homeomorph.symm_apply_apply] using hq
  have hboundary (x : Quot (OrientableRel 0 1)) :
      ‖(f x).val‖ = 1 ↔ x ∈ ActualOneBoundaryOrientableBoundary 0 := by
    constructor
    · induction x using Quot.inductionOn with
      | _ z =>
        intro hn
        have hr : radius (d z) = 1 := (hrawnorm (d z)).symm.trans hn
        have hrpos : 0 < radius (d z) := by rw [hr]; norm_num
        let u := a 2 (d z) / radius (d z)
        let t : unitInterval := ⟨u,huBounds (d z) hrpos⟩
        have hzP : d z = P 1 t (by norm_num) t.property := by
          exact (hrepresent (d z) hrpos).trans (by
            apply Subtype.ext
            change point (radius (d z)) u = point 1 u
            rw [hr])
        have hz : z = Complex.ClosedUnitDisc.bdyPtOfReal (-(1+(t : ℝ))/3) :=
          d.injective (hzP.trans (hdPH t).symm)
        refine ⟨t, ?_⟩
        change Quot.mk (OrientableRel 0 1)
          (Complex.ClosedUnitDisc.bdyPtOfReal (-(1+(t : ℝ))/(4*((0 : ℕ) : ℝ)+3))) = _
        norm_num only [Nat.cast_zero,mul_zero,zero_add]
        rw [← hz]
    · rintro ⟨t,rfl⟩
      change ‖(F (d (Complex.ClosedUnitDisc.bdyPtOfReal
        (-(1+(t : ℝ))/(4*((0 : ℕ) : ℝ)+3))))).val‖ = 1
      norm_num only [Nat.cast_zero,mul_zero,zero_add]
      rw [hdPH]
      exact (hrawnorm _).trans (hPr 1 t (by norm_num) t.property)
  let ef : Quot (OrientableRel 0 1) ≃ₜ Complex.ClosedUnitDisc :=
    (Equiv.ofBijective f ⟨hfinj,hfsurj⟩).toHomeomorphOfContinuousClosed hfc hfc.isClosedMap
  let ed : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
      Complex.ClosedUnitDisc :=
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype (fun z => by
      change z ∈ Metric.closedBall 0 1 ↔
        Complex.orthonormalBasisOneI.repr.symm z ∈ Metric.closedBall 0 1
      simp only [Metric.mem_closedBall,dist_zero_right,
        Complex.orthonormalBasisOneI.repr.symm.norm_map])
  have hmodel : ∃ k : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
        Quot (OrientableRel 0 1),
      ∀ x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
        k x ∈ ActualOneBoundaryOrientableBoundary 0 ↔
          x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    refine ⟨ed.trans ef.symm, ?_⟩
    intro x
    rw [← hboundary]
    have hf : f ((ed.trans ef.symm) x) = ed x := ef.apply_symm_apply (ed x)
    rw [hf]
    change ‖Complex.orthonormalBasisOneI.repr.symm x.val‖ = 1 ↔
      x.val ∈ Metric.sphere 0 1
    rw [Complex.orthonormalBasisOneI.repr.symm.norm_map,
      Metric.mem_sphere,dist_zero_right]
  exact hmodel

end CurveComplex.Hyperbolic
