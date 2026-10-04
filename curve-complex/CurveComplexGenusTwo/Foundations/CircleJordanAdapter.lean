import CurveComplexGenusTwo.Foundations.PlanarCoverProducer
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import ClassificationOfSurfaces.Moise.Brouwer

namespace CurveComplex

open Topology Set

private abbrev Plane := Schoenflies.Plane

/-- An embedded Mathlib unit circle is a Jordan curve in Schoenflies' interval
loop representation. -/
theorem isJordanCurve_range_of_isEmbedding_circle
    (r : C(Circle, Plane)) (hr : IsEmbedding r) :
    Schoenflies.IsJordanCurve (Set.range r) := by
  classical
  let e : AddCircle (1 : ℝ) ≃ₜ Circle :=
    AddCircle.homeomorphCircle one_ne_zero
  let f : ℝ → Plane := fun t => r (e (t : AddCircle (1 : ℝ)))
  have hfcont : Continuous f := by
    exact r.continuous.comp (e.continuous.comp (AddCircle.continuous_mk' 1))
  have hfclose : f 0 = f 1 := by
    change r (e (0 : AddCircle (1 : ℝ))) = r (e ((1 : ℝ) : AddCircle (1 : ℝ)))
    rw [AddCircle.coe_period]
  have hfinj : Set.InjOn f (Set.Ico (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have hxy' : e (x : AddCircle (1 : ℝ)) = e (y : AddCircle (1 : ℝ)) :=
      hr.injective hxy
    have hxy'' : (x : AddCircle (1 : ℝ)) = (y : AddCircle (1 : ℝ)) :=
      e.injective hxy'
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (a := (0 : ℝ)) (p := (1 : ℝ)) (by simpa using hx) (by simpa using hy)).mp hxy''
  have hfimage : f '' Set.Icc (0 : ℝ) 1 = Set.range r := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨e (t : AddCircle (1 : ℝ)), rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨t, ht, hte⟩ := AddCircle.eq_coe_Ico (e.symm y)
      refine ⟨t, ?_, ?_⟩
      · exact ⟨ht.1, le_of_lt ht.2⟩
      · change r (e (t : AddCircle (1 : ℝ))) = r y
        rw [hte, e.apply_symm_apply]
  exact ⟨f, ⟨hfcont.continuousOn, hfclose, hfinj⟩, hfimage⟩

/-- A nullhomotopic simple closed curve bounds an embedded disc whenever its
base has a planar quotient cover. -/
theorem boundsDisc_of_nullhomotopic_planar_quotient_cover_complete
    {G S : Type*} [Group G] [MulAction G Plane]
    [TopologicalSpace S] [T2Space S]
    (p : Plane → S) (hp : IsQuotientCoveringMap p G)
    (c : Curve S)
    (hc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, S)).Nullhomotopic) :
    BoundsDisc c :=
  boundsDisc_of_nullhomotopic_planar_quotient_cover p hp c hc
    isJordanCurve_range_of_isEmbedding_circle
    (fun u =>
      LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.BrouwerFixedPoint.brouwer_fixed_point
        u u.continuous)

end CurveComplex
