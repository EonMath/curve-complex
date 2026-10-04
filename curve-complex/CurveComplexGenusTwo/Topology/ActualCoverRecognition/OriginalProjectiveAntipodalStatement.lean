import ClassificationOfSurfaces.SphereQuotientHomeomorph
import ClassificationOfSurfaces.RepresentativeCarrier
import Mathlib.Topology.Covering.Quotient
import Mathlib.Algebra.GroupWithZero.Units.Fintype

namespace CurveComplex.LocalSurgery
open LeanEval.Topology.ClassificationOfSurfaces

theorem original_projective_plane_disk_antipodal_orbit_homeomorphism
    (action : MulAction ℤˣ SphereRepresentative)
    (hScalar : letI := action
      ∀ (v : ℤˣ) (x : SphereRepresentative), (v • x).val = v.val • x.val) :
    letI := action
    Nonempty ((Quot (NonOrientableRel 1 0)) ≃ₜ
      Quotient (MulAction.orbitRel ℤˣ SphereRepresentative)) := by
  classical
  letI := action
  letI : ContinuousConstSMul ℤˣ SphereRepresentative := ⟨fun v => by
    apply continuous_induced_rng.mpr
    have heq : (fun x : SphereRepresentative => (v • x).val) =
        (fun x : SphereRepresentative => v.val • x.val) := funext (hScalar v)
    change Continuous (fun x : SphereRepresentative => (v • x).val)
    rw [heq]
    exact continuous_const_smul _ |>.comp continuous_subtype_val⟩
  have hbdy (t : ℝ) :
      (Complex.ClosedUnitDisc.bdyPtOfReal (t + 1 / 2)).val =
        -(Complex.ClosedUnitDisc.bdyPtOfReal t).val := by
    change Complex.exp (↑(2 * Real.pi * (t + 1 / 2)) * Complex.I) =
      -Complex.exp (↑(2 * Real.pi * t) * Complex.I)
    rw [show (↑(2 * Real.pi * (t + 1 / 2)) : ℂ) * Complex.I =
      ↑(2 * Real.pi * t) * Complex.I + ↑Real.pi * Complex.I by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
  have hrel (z w : Complex.ClosedUnitDisc)
      (hz : z.val ∈ Metric.sphere 0 1) (hw : w.val = -z.val) :
      Relation.EqvGen (NonOrientableRel 1 0) z w := by
    let p := (PolygonCell.closedUnitDiscHomeomorph 1).symm z
    obtain ⟨i, t, ht⟩ := PolygonCell.exists_side_eq_of_mem_sphere (n := 1) (by decide) p hz
    have hzparam : z = Complex.ClosedUnitDisc.bdyPtOfReal (t : ℝ) := by
      have h := congrArg (PolygonCell.closedUnitDiscHomeomorph 1) ht
      simpa [PolygonCell.closedUnitDiscHomeomorph_side, Fin.eq_zero i, p] using h.symm
    by_cases htlow : (t : ℝ) ≤ 1 / 2
    · let x : Set.Icc (0 : ℝ) 1 := ⟨2 * t, by constructor <;> nlinarith [t.property.1]⟩
      have hgen := NonOrientableRel.a (p := 1) (n := 0) x (0 : Fin 1)
      have heq : (2 * (0 : Fin 1).val + (x : ℝ)) / (2 * (1 : ℕ) + 3 * (0 : ℕ)) = t := by dsimp [x]; norm_num <;> ring
      have heq' : (2 * (0 : Fin 1).val + 1 + (x : ℝ)) / (2 * (1 : ℕ) + 3 * (0 : ℕ)) = (t : ℝ) + 1 / 2 := by dsimp [x]; norm_num <;> ring
      rw [heq, heq'] at hgen
      rw [hzparam]
      have hwparam : w = Complex.ClosedUnitDisc.bdyPtOfReal ((t : ℝ) + 1 / 2) := by
        apply Subtype.ext
        rw [hbdy, ← hzparam, hw]
      rw [hwparam]
      exact Relation.EqvGen.rel _ _ hgen
    · let x : Set.Icc (0 : ℝ) 1 := ⟨2 * t - 1, by constructor <;> nlinarith [t.property.2]⟩
      have hgen := NonOrientableRel.a (p := 1) (n := 0) x (0 : Fin 1)
      have heq : (2 * (0 : Fin 1).val + (x : ℝ)) / (2 * (1 : ℕ) + 3 * (0 : ℕ)) = (t : ℝ) - 1 / 2 := by dsimp [x]; norm_num <;> ring
      have heq' : (2 * (0 : Fin 1).val + 1 + (x : ℝ)) / (2 * (1 : ℕ) + 3 * (0 : ℕ)) = t := by dsimp [x]; norm_num <;> ring
      rw [heq, heq'] at hgen
      rw [hzparam]
      have hwparam : w = Complex.ClosedUnitDisc.bdyPtOfReal ((t : ℝ) - 1 / 2) := by
        apply Subtype.ext
        have h := hbdy ((t : ℝ) - 1 / 2)
        rw [sub_add_cancel] at h
        rw [hzparam] at hw
        calc
          w.val = -(Complex.ClosedUnitDisc.bdyPtOfReal (t : ℝ)).val := hw
          _ = (Complex.ClosedUnitDisc.bdyPtOfReal ((t : ℝ) - 1 / 2)).val := by rw [h, neg_neg]
      rw [hwparam]
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hgen)
  let up : Complex.ClosedUnitDisc → SphereRepresentative :=
    fun z => PolygonCell.upperHemisphere ((PolygonCell.closedUnitDiscHomeomorph 1).symm z)
  have hupcont : Continuous up :=
    PolygonCell.upperHemisphere.continuous.comp (PolygonCell.closedUnitDiscHomeomorph 1).symm.continuous
  let q : SphereRepresentative → Quotient (MulAction.orbitRel ℤˣ SphereRepresentative) := Quotient.mk (MulAction.orbitRel ℤˣ SphereRepresentative)
  have hgen : ∀ z w, NonOrientableRel 1 0 z w → q (up z) = q (up w) := by
    intro z w h
    cases h with
    | a x i =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      apply Quotient.sound
      change ∃ v : ℤˣ, v • up _ = up _
      refine ⟨-1, ?_⟩
      apply Subtype.ext
      rw [hScalar]
      have hb :
          (Complex.ClosedUnitDisc.bdyPtOfReal ((1 + (x : ℝ)) / 2)).val =
            -(Complex.ClosedUnitDisc.bdyPtOfReal ((x : ℝ) / 2)).val := by
        convert hbdy ((x : ℝ) / 2) using 1 <;> congr 2 <;> ring
      have hheight (r : ℝ) :
          PolygonCell.hemisphereHeight
            ((PolygonCell.closedUnitDiscHomeomorph 1).symm (Complex.ClosedUnitDisc.bdyPtOfReal r)) = 0 := by
        unfold PolygonCell.hemisphereHeight
        have hh : ‖(Complex.ClosedUnitDisc.bdyPtOfReal r).val‖ = 1 :=
          Circle.norm_coe (Real.fourierChar r)
        change Real.sqrt (1 - Complex.normSq (Complex.ClosedUnitDisc.bdyPtOfReal r).val) = 0
        rw [Complex.normSq_eq_norm_sq, hh]
        norm_num
      ext j
      fin_cases j
      · simp [up, PolygonCell.upperHemisphere, PolygonCell.upperHemisphereVector,
          PolygonCell.closedUnitDiscHomeomorph, hb]
      · simp [up, PolygonCell.upperHemisphere, PolygonCell.upperHemisphereVector,
          PolygonCell.closedUnitDiscHomeomorph, hb]
      · change (-1 : ℤ) • PolygonCell.hemisphereHeight
          ((PolygonCell.closedUnitDiscHomeomorph 1).symm _) =
          PolygonCell.hemisphereHeight ((PolygonCell.closedUnitDiscHomeomorph 1).symm _)
        simp [hheight]
    | c x i => exact Fin.elim0 i
  let f : Quot (NonOrientableRel 1 0) → Quotient (MulAction.orbitRel ℤˣ SphereRepresentative) :=
    Quot.lift (q ∘ up) hgen
  have hfcont : Continuous f := continuous_quot_lift hgen (continuous_quotient_mk'.comp hupcont)
  have hfinj : Function.Injective f := by
    intro a b hab
    induction a using Quot.inductionOn with
    | _ z =>
      induction b using Quot.inductionOn with
      | _ w =>
        have horb : MulAction.orbitRel ℤˣ SphereRepresentative (up z) (up w) := Quotient.exact hab
        obtain ⟨v, hv⟩ := horb
        change v • up w = up z at hv
        rcases Int.units_eq_one_or v with hvone | hvneg
        · rw [hvone, one_smul] at hv
          have h := PolygonCell.upperHemisphere_injective hv
          apply congrArg (Quot.mk (NonOrientableRel 1 0))
          exact ((PolygonCell.closedUnitDiscHomeomorph 1).symm.injective h).symm
        · rw [hvneg] at hv
          have hvval := congrArg Subtype.val hv
          rw [hScalar] at hvval
          have hheight :
              -PolygonCell.hemisphereHeight ((PolygonCell.closedUnitDiscHomeomorph 1).symm w) =
              PolygonCell.hemisphereHeight ((PolygonCell.closedUnitDiscHomeomorph 1).symm z) := by
            simpa [up, PolygonCell.upperHemisphere, PolygonCell.upperHemisphereVector] using congrArg (fun x => x 2) hvval
          have hzero : PolygonCell.hemisphereHeight ((PolygonCell.closedUnitDiscHomeomorph 1).symm z) = 0 := by
            nlinarith [PolygonCell.hemisphereHeight_nonneg ((PolygonCell.closedUnitDiscHomeomorph 1).symm z),
              PolygonCell.hemisphereHeight_nonneg ((PolygonCell.closedUnitDiscHomeomorph 1).symm w)]
          have hw : w.val = -z.val := by
            apply Complex.ext
            · have h := congrArg (fun x => x 0) hvval
              simpa [up, PolygonCell.upperHemisphere, PolygonCell.upperHemisphereVector,
                PolygonCell.closedUnitDiscHomeomorph, nsmulRec] using (neg_eq_iff_eq_neg.mp h)
            · have h := congrArg (fun x => x 1) hvval
              simpa [up, PolygonCell.upperHemisphere, PolygonCell.upperHemisphereVector,
                PolygonCell.closedUnitDiscHomeomorph, nsmulRec] using (neg_eq_iff_eq_neg.mp h)
          exact Quot.eqvGen_sound (hrel z w
            (PolygonCell.mem_sphere_of_hemisphereHeight_eq_zero _ hzero) hw)
  have hfsurj : Function.Surjective f := by
    intro a
    induction a using Quotient.inductionOn with
    | _ x =>
      by_cases hx : 0 ≤ x.val 2
      · refine ⟨Quot.mk _ ((PolygonCell.closedUnitDiscHomeomorph 1) (PolygonCell.sphereDiskPoint x)), ?_⟩
        change q (up _) = q x
        congr 1
        simpa [up] using PolygonCell.upperHemisphere_sphereDiskPoint x hx
      · let y := (-1 : ℤˣ) • x
        have hy : 0 ≤ y.val 2 := by
          dsimp [y]
          rw [hScalar]
          simpa using le_of_lt (neg_pos.mpr (lt_of_not_ge hx))
        refine ⟨Quot.mk _ ((PolygonCell.closedUnitDiscHomeomorph 1) (PolygonCell.sphereDiskPoint y)), ?_⟩
        change q (up _) = q x
        have heq : up ((PolygonCell.closedUnitDiscHomeomorph 1) (PolygonCell.sphereDiskPoint y)) = y := by
          simpa [up] using PolygonCell.upperHemisphere_sphereDiskPoint y hy
        rw [heq]
        exact Quotient.sound ⟨-1, rfl⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hfinj, hfsurj⟩) hfcont⟩

end CurveComplex.LocalSurgery
