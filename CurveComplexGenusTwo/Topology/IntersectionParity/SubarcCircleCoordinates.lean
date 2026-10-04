import CurveComplexGenusTwo.Foundations.Definitions

namespace CurveComplex.LocalSurgery

noncomputable def subarcCircleCoordinates
    {S : Type*} [TopologicalSpace S] (a : Curve S)
    (f : C(Interval, S)) (hfa : Set.range f ⊆ a.image) : C(Interval, Circle) :=
  ⟨fun t => a.embedded.toHomeomorph.symm ⟨f t, hfa ⟨t, rfl⟩⟩,
    a.embedded.toHomeomorph.symm.continuous.comp
      (f.continuous.subtype_mk (fun t => hfa ⟨t, rfl⟩))⟩

noncomputable def subarcAngleCoordinates
    {S : Type*} [TopologicalSpace S] (a : Curve S)
    (f : C(Interval, S)) (hfa : Set.range f ⊆ a.image) : C(Interval, ℝ) :=
  Circle.isCoveringMap_exp.liftPath (subarcCircleCoordinates a f hfa)
    (subarcCircleCoordinates a f hfa 0).val.arg (Circle.exp_arg _).symm

end CurveComplex.LocalSurgery
