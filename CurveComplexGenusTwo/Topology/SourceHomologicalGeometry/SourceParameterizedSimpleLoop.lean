import CurveComplexGenusTwo.Topology.SourceCycleActual.SourceEssentialCurveComplete
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex Set Topology

/-- Endpoint-only collision of an actual interval loop yields an actual embedded
Circle. The loop is not assumed nullhomotopic or essential. -/
theorem simple_loop_gives_parameterized_curve
    {X : Type} [TopologicalSpace X] [T2Space X]
    (x : X) (l : Path x x)
    (hcoll : ∀ s t : CurveComplex.Interval, l s = l t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    ∃ c : Curve X, c.image = Set.range l ∧
      ∀ t : CurveComplex.Interval, c.map (Circle.exp (2 * Real.pi * t.val)) = l t := by
  let r := AddCircle.EndpointIdent (1 : ℝ) 0
  let j : Icc (0 : ℝ) (0 + 1) → CurveComplex.Interval := fun t => ⟨t.val, by simpa using t.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hrespect : ∀ a b, r a b → l (j a) = l (j b) := by
    rintro a b ⟨⟩
    simpa [j] using l.source.trans l.target.symm
  let L : Quot r → X := Quot.lift (fun t => l (j t)) hrespect
  have hL : Continuous L := continuous_quot_lift _ (l.continuous.comp hj)
  have hLi : Function.Injective L := by
    intro a b
    induction a using Quot.inductionOn with | h a =>
      induction b using Quot.inductionOn with | h b =>
        intro hab
        rcases hcoll (j a) (j b) hab with he | ⟨ha, hb⟩ | ⟨ha, hb⟩
        · apply congrArg (Quot.mk r)
          exact Subtype.ext (congrArg (fun t : CurveComplex.Interval => t.val) he)
        · have ha' : a = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : CurveComplex.Interval => t.val) ha)
          have hb' : b = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : CurveComplex.Interval => t.val) hb)
          subst a; subst b
          exact Quot.sound AddCircle.EndpointIdent.mk
        · have ha' : a = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : CurveComplex.Interval => t.val) ha)
          have hb' : b = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : CurveComplex.Interval => t.val) hb)
          subst a; subst b
          exact (Quot.sound AddCircle.EndpointIdent.mk).symm
  let e : Circle ≃ₜ Quot r :=
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.trans
      (AddCircle.homeoIccQuot (1 : ℝ) 0)
  let c : Curve X := ⟨L ∘ e, ((hL.comp e.continuous).isClosedEmbedding (hLi.comp e.injective)).isEmbedding⟩
  have hparameter (t : CurveComplex.Interval) :
      c.map (Circle.exp (2 * Real.pi * t.val)) = l t := by
    let q : Quot r := Quot.mk r ⟨t.val, by simpa using t.property⟩
    have he : e.symm q = Circle.exp (2 * Real.pi * t.val) := by
      change AddCircle.homeomorphCircle one_ne_zero
        ((AddCircle.homeoIccQuot (1 : ℝ) 0).symm q) = _
      change AddCircle.homeomorphCircle one_ne_zero (t.val : AddCircle (1 : ℝ)) = _
      simp only [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk, div_one]
    have heq := congrArg e he
    rw [e.apply_symm_apply] at heq
    change L (e (Circle.exp (2 * Real.pi * t.val))) = l t
    rw [←heq]
  refine ⟨c, ?_, hparameter⟩
  change range (L ∘ e) = range l
  rw [e.surjective.range_comp]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quot.inductionOn with | h t =>
      exact ⟨j t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Quot.mk r ⟨t.val, by simpa using t.property⟩, rfl⟩

end CurveComplexGenusTwo.SourceTopology
