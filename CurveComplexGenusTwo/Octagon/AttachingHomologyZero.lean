import CurveComplexGenusTwo.Octagon.AttachingMap
import CurveComplexGenusTwo.CWHurewicz.CircleFundamentalCycle
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz CircleFundamentalCycle
namespace CurveComplex.Octagon.AttachingMap
theorem cycleClass_boundary (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (z : K.X 1) (hz : K.d 1 0 z = 0) (w : K.X 2) (hw : K.d 2 1 w = z) :
    cycleClass K 1 z hz = 0 := by
  have h : scalar _ z = scalar _ w ≫ K.d 2 1 := by
    rw [scalar_naturality, hw]
  have he := K.liftCycles_homologyπ_eq_zero_of_boundary (scalar _ z) 0 (by simp)
    (scalar _ w) h
  exact congrArg (fun f => f (1:ℤ)) he
theorem fundamentalClass_image_zero :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom attachingMap)) fundamentalClass = 0 := by
  let f : TopCat.of Circle ⟶ X := TopCat.ofHom attachingMap
  let z : (mvAmbientComplex (TopCat.of Circle)).X 1 := circleBoundaryChain
  have hz : (mvAmbientComplex (TopCat.of Circle)).d 1 0 z = 0 := circle_boundary_is_cycle
  have himg : (singularFinsuppMap f).f 1 z = singularBoundaryFinsupp X 1 fillingChain := by
    rw [singularFinsuppMap_f]
    exact attaching_circle_chain_bounds
  have hw : (mvAmbientComplex X).d 1 0 ((singularFinsuppMap f).f 1 z) = 0 := by
    rw [himg]
    exact congrArg (fun g => g fillingChain) ((mvAmbientComplex X).d_comp_d 2 1 0)
  have hc := cycleClass_map (singularFinsuppMap f) 1 z hz hw
  have hb : cycleClass (mvAmbientComplex X) 1 ((singularFinsuppMap f).f 1 z) hw = 0 := by
    apply cycleClass_boundary _ _ _ fillingChain
    exact himg.symm
  rw [hb] at hc
  have hn := congrArg (fun g => g (cycleClass (mvAmbientComplex (TopCat.of Circle)) 1 z hz))
    (singularHomologyRepresentation_naturality f 1)
  change (singularHomologyRepresentation X 1).hom
    (HomologicalComplex.homologyMap (singularFinsuppMap f) 1
      (cycleClass (mvAmbientComplex (TopCat.of Circle)) 1 z hz)) = _ at hn
  rw [hc, map_zero] at hn
  exact hn.symm
theorem attaching_h1_map_zero :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom attachingMap)) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨n, rfl⟩ := fundamentalClass_generates x
  change (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom attachingMap)).hom (n • fundamentalClass) = 0
  rw [map_zsmul]
  rw [fundamentalClass_image_zero]
  change n • (0 : H X 1) = 0
  exact zsmul_zero n
end CurveComplex.Octagon.AttachingMap
