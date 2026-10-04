import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib
open scoped unitInterval
open Topology

namespace CurveComplex.LocalSurgery

/-- The usual once-around parametrization; Mathlib's Circle.exp is already continuous. -/
noncomputable def intervalCircleParameter : C(I, Circle) :=
  Circle.exp.comp ⟨fun u : I => 2 * Real.pi * (u : ℝ),
    continuous_const.mul continuous_subtype_val⟩

/-- Actual interval-parametrized loop of the assigned embedded circle. -/
noncomputable def intervalCurveLoop {S : Type*} [TopologicalSpace S] (a : Curve S) : C(I, S) :=
  (⟨a.map, a.embedded.continuous⟩ : C(Circle, S)).comp intervalCircleParameter

/-- The concrete cylinder map through the ambient isotopy, not an assumed trace. -/
noncomputable def ambientCurveLoopSweep {S : Type*} [TopologicalSpace S]
    (a : Curve S) (H : AmbientIsotopy S) : C(I × I, S) :=
  ⟨fun z => H.map (z.1, intervalCurveLoop a z.2),
    H.map.continuous.comp
      (continuous_fst.prodMk ((intervalCurveLoop a).continuous.comp continuous_snd))⟩

/-- Canonical lift of the initial loop into any already constructed covering.
The missing geometric construction is the cover itself, not this lift operation. -/
noncomputable def curveInitialCoverLift
    {E S : Type*} [TopologicalSpace E] [TopologicalSpace S]
    {p : E → S} (cov : IsCoveringMap p) (a : Curve S)
    (e : E) (he : p e = intervalCurveLoop a 0) : C(I, E) :=
  ⟨cov.liftPath (intervalCurveLoop a) e he.symm,
    (cov.liftPath (intervalCurveLoop a) e he.symm).continuous⟩

/-- Rotate the initial parameter so finite endpoint crossing sets can be avoided. -/
noncomputable def intervalCircleParameterFrom (z : Circle) : C(I, Circle) :=
  ⟨fun u => z * intervalCircleParameter u,
    continuous_const.mul intervalCircleParameter.continuous⟩

noncomputable def intervalCurveLoopFrom
    {S : Type*} [TopologicalSpace S] (a : Curve S) (z : Circle) : C(I, S) :=
  (⟨a.map, a.embedded.continuous⟩ : C(Circle, S)).comp
    (intervalCircleParameterFrom z)

noncomputable def ambientCurveLoopSweepFrom
    {S : Type*} [TopologicalSpace S] (a : Curve S)
    (H : AmbientIsotopy S) (z : Circle) : C(I × I, S) :=
  ⟨fun u => H.map (u.1, intervalCurveLoopFrom a z u.2),
    H.map.continuous.comp
      (continuous_fst.prodMk
        ((intervalCurveLoopFrom a z).continuous.comp continuous_snd))⟩

end CurveComplex.LocalSurgery
