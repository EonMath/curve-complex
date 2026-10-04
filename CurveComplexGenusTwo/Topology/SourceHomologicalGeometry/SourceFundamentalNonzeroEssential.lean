import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceHomologicallyNonzeroCurveCanonicalProof

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CategoryTheory.Limits CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem essential_of_curve_fundamental_nonzero
    {S : Type} [TopologicalSpace S] (c : Curve S)
    (hc : HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩)) 1
      CircleFundamentalCycle.fundamentalClass ≠ 0) : Essential c := by
  intro hd
  obtain ⟨y,⟨H⟩⟩ := boundsDisc_curveMap_nullhomotopic c hd
  let f := TopCat.ofHom (⟨c.map,c.embedded.continuous⟩ : C(Circle,S))
  have hz := CurveComplex.WeightedFlowScratch.singularHomologyMap_zero_of_nullhomotopy f y H 1 (by omega)
  have ha : HomologicalComplex.homologyMap (actualSingularFunctor.map f) 1 = 0 := by
    apply (cancel_epi (singularHomologyRepresentation (TopCat.of Circle) 1).hom).mp
    change (singularHomologyRepresentation (TopCat.of Circle) 1).hom ≫
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map f) = _
    rw [←singularHomologyRepresentation_naturality,hz]
    simp
  apply hc
  change HomologicalComplex.homologyMap (actualSingularFunctor.map f) 1 CircleFundamentalCycle.fundamentalClass = 0
  rw [ha]
  rfl

end CurveComplexGenusTwo.SourceTopology
