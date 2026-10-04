import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceHomologicallyNonzeroCurveCanonicalProof
import CurveComplexGenusTwo.Octagon.AttachingHomologyZero

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CategoryTheory.Limits CurveComplexGenusTwo.CWHurewicz CircleFundamentalCycle
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem curve_fundamental_zero_of_chain_filling
    {S : Type} [TopologicalSpace S] (c : Curve S)
    (w : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ)
    (hw : singularBoundaryFinsupp (TopCat.of S) 1 w =
      singularFinsuppPush (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩) 1 circleBoundaryChain) :
    HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩)) 1
      fundamentalClass = 0 := by
  let f := TopCat.ofHom (⟨c.map,c.embedded.continuous⟩ : C(Circle,S))
  let z : (mvAmbientComplex (TopCat.of Circle)).X 1 := circleBoundaryChain
  have hz : (mvAmbientComplex (TopCat.of Circle)).d 1 0 z = 0 := circle_boundary_is_cycle
  have himg : (singularFinsuppMap f).f 1 z = singularBoundaryFinsupp (TopCat.of S) 1 w := by
    rw [singularFinsuppMap_f]
    exact hw.symm
  have hcycle : (mvAmbientComplex (TopCat.of S)).d 1 0 ((singularFinsuppMap f).f 1 z) = 0 := by
    rw [himg]
    exact congrArg (fun g => g w) ((mvAmbientComplex (TopCat.of S)).d_comp_d 2 1 0)
  have hc := cycleClass_map (singularFinsuppMap f) 1 z hz hcycle
  have hb : cycleClass (mvAmbientComplex (TopCat.of S)) 1 ((singularFinsuppMap f).f 1 z) hcycle = 0 :=
    CurveComplex.Octagon.AttachingMap.cycleClass_boundary _ _ _ w himg.symm
  rw [hb] at hc
  have hn := congrArg (fun g => g (cycleClass (mvAmbientComplex (TopCat.of Circle)) 1 z hz))
    (singularHomologyRepresentation_naturality f 1)
  change (singularHomologyRepresentation (TopCat.of S) 1).hom
    (HomologicalComplex.homologyMap (singularFinsuppMap f) 1
      (cycleClass (mvAmbientComplex (TopCat.of Circle)) 1 z hz)) = _ at hn
  rw [hc,map_zero] at hn
  exact hn.symm

end CurveComplexGenusTwo.SourceTopology
