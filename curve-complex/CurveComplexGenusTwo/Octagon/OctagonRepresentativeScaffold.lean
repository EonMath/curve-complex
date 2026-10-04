import CurveComplexGenusTwo.Octagon.VertexEuclideanChart
import ClassificationOfSurfaces.Representatives

namespace CurveComplex.Octagon
open LeanEval.Topology.ClassificationOfSurfaces

/-- The equivalence closure of the actual side pairing is exactly the
classifier's closed orientable two-handle representative relation. -/
theorem octagon_relation_iff_orientable (x y : Disk) :
    Relation.r x y ↔ _root_.Relation.EqvGen (OrientableRel 2 0) x y := by
  have hside (i : Side) (t : unitInterval) :
      side i t = Complex.ClosedUnitDisc.bdyPtOfReal (((i.val : ℝ) + t) / 8) := by
    apply Subtype.ext
    simp only [side, Complex.ClosedUnitDisc.bdyPtOfReal, Real.fourierChar_apply']
    congr 2
    ring
  have hforward {x y : Disk} (h : SideGlue x y) :
      _root_.Relation.EqvGen (OrientableRel 2 0) x y := by
    obtain ⟨i, t, rfl, rfl⟩ := h
    fin_cases i
    · have h := (_root_.Relation.EqvGen.rel _ _ (OrientableRel.a (p := 2) (n := 0) t (0 : Fin 2)))
      norm_num [hside, pair, unitInterval.symm] at h ⊢
      convert h using 1
      congr 1
      ring
    · have h := (_root_.Relation.EqvGen.rel _ _ (OrientableRel.b (p := 2) (n := 0) t (0 : Fin 2)))
      norm_num [hside, pair, unitInterval.symm] at h ⊢
      convert h using 1
      congr 1
      ring
    · have h := (_root_.Relation.EqvGen.rel _ _ (OrientableRel.a (p := 2) (n := 0) (unitInterval.symm t) (0 : Fin 2))).symm
      norm_num [hside, pair, unitInterval.symm] at h ⊢
      convert h using 1
      congr 1
      ring
    · have h := (_root_.Relation.EqvGen.rel _ _ (OrientableRel.b (p := 2) (n := 0) (unitInterval.symm t) (0 : Fin 2))).symm
      norm_num [hside, pair, unitInterval.symm] at h ⊢
      convert h using 1
      congr 1
      ring
    · have h := (_root_.Relation.EqvGen.rel _ _ (OrientableRel.a (p := 2) (n := 0) t (1 : Fin 2)))
      norm_num [hside, pair, unitInterval.symm] at h ⊢
      convert h using 1
      congr 1
      ring
    · have h := (_root_.Relation.EqvGen.rel _ _ (OrientableRel.b (p := 2) (n := 0) t (1 : Fin 2)))
      norm_num [hside, pair, unitInterval.symm] at h ⊢
      convert h using 1
      congr 1
      ring
    · have h := (_root_.Relation.EqvGen.rel _ _ (OrientableRel.a (p := 2) (n := 0) (unitInterval.symm t) (1 : Fin 2))).symm
      norm_num [hside, pair, unitInterval.symm] at h ⊢
      convert h using 1
      congr 1
      ring
    · have h := (_root_.Relation.EqvGen.rel _ _ (OrientableRel.b (p := 2) (n := 0) (unitInterval.symm t) (1 : Fin 2))).symm
      norm_num [hside, pair, unitInterval.symm] at h ⊢
      convert h using 1
      congr 1
      ring
  have hback {x y : Disk} (h : OrientableRel 2 0 x y) : Relation.r x y := by
    cases h with
    | a t i =>
      fin_cases i
      · apply _root_.Relation.EqvGen.rel
        refine ⟨(0 : Side), t, ?_, ?_⟩ <;>
          rw [hside] <;> norm_num [pair, unitInterval.symm]
        all_goals congr 1
        all_goals ring
      · apply _root_.Relation.EqvGen.rel
        refine ⟨(4 : Side), t, ?_, ?_⟩ <;>
          rw [hside] <;> norm_num [pair, unitInterval.symm]
        all_goals congr 1
        all_goals ring
    | b t i =>
      fin_cases i
      · apply _root_.Relation.EqvGen.rel
        refine ⟨(1 : Side), t, ?_, ?_⟩ <;>
          rw [hside] <;> norm_num [pair, unitInterval.symm]
        all_goals congr 1
        all_goals ring
      · apply _root_.Relation.EqvGen.rel
        refine ⟨(5 : Side), t, ?_, ?_⟩ <;>
          rw [hside] <;> norm_num [pair, unitInterval.symm]
        all_goals congr 1
        all_goals ring
    | c t i => exact Fin.elim0 i
  constructor
  · intro h
    induction h with
    | rel x y h => exact hforward h
    | refl x => exact .refl x
    | symm x y h ih => exact ih.symm
    | trans x y z h₁ h₂ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  · intro h
    induction h with
    | rel x y h => exact hback h
    | refl x => exact .refl x
    | symm x y h ih => exact ih.symm
    | trans x y z h₁ h₂ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- Identity on disk representatives descends to a homeomorphism to the
standard closed orientable genus-two polygonal representative. -/
noncomputable def octagonOrientableGenusTwoHomeomorph :
    Surface ≃ₜ Quot (OrientableRel 2 0) := by
  let f : Surface → Quot (OrientableRel 2 0) :=
    Quotient.lift (Quot.mk (OrientableRel 2 0)) (fun x y h =>
      Quot.eq.mpr ((octagon_relation_iff_orientable x y).mp h))
  let g : Quot (OrientableRel 2 0) → Surface :=
    Quot.lift mk (fun x y h => Quotient.sound
      ((octagon_relation_iff_orientable x y).mpr (.rel x y h)))
  exact {
    toFun := f
    invFun := g
    left_inv := by
      intro q
      induction q using Quotient.inductionOn with
      | _ x => rfl
    right_inv := by
      intro q
      induction q using Quot.inductionOn with
      | _ x => rfl
    continuous_toFun := continuous_quot_lift _ continuous_quot_mk
    continuous_invFun := continuous_quot_lift _ continuous_mk }

theorem octagonOrientableGenusTwoHomeomorph_mk (x : Disk) :
    octagonOrientableGenusTwoHomeomorph (mk x) = Quot.mk (OrientableRel 2 0) x := by
  rfl

end CurveComplex.Octagon
