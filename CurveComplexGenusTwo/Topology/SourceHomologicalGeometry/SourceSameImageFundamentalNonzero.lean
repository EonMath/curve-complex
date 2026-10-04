import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceHomologicallyNonzeroCurveCanonicalProof

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CategoryTheory.Limits CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem curve_fundamental_nonzero_of_same_image
    {S : Type} [TopologicalSpace S] (c d : Curve S) (himage : c.image = d.image)
    (hc : HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩)) 1
      CircleFundamentalCycle.fundamentalClass ≠ 0) :
    HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom ⟨d.map,d.embedded.continuous⟩)) 1
      CircleFundamentalCycle.fundamentalClass ≠ 0 := by
  intro hd
  let cf : C(Circle,S) := ⟨c.map,c.embedded.continuous⟩
  let df : C(Circle,S) := ⟨d.map,d.embedded.continuous⟩
  have hcarry (x : Circle) : cf x ∈ d.image := by
    rw [←himage]
    exact ⟨x,rfl⟩
  let e := d.embedded.toHomeomorph
  let lift : C(Circle,Circle) := ⟨fun x => e.symm ⟨cf x,hcarry x⟩,
    e.symm.continuous.comp (cf.continuous.subtype_mk hcarry)⟩
  have heq : df.comp lift = cf := by
    ext x
    have hh := congrArg Subtype.val (e.apply_symm_apply (⟨cf x,hcarry x⟩ : d.image))
    exact hh
  have hzero : HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom df)) 1 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨n,hn⟩ := CircleFundamentalCycle.fundamentalClass_generates x
    rw [←hn,map_zsmul,hd]
    change n • (0 : H S 1) = 0
    exact zsmul_zero n
  apply hc
  have hfactor : TopCat.ofHom cf = TopCat.ofHom lift ≫ TopCat.ofHom df := by
    ext x
    exact congrFun (congrArg (fun f : C(Circle,S) => (f : Circle → S)) heq.symm) x
  change HomologicalComplex.homologyMap (actualSingularFunctor.map (TopCat.ofHom cf)) 1
    CircleFundamentalCycle.fundamentalClass = 0
  rw [hfactor,actualSingularFunctor.map_comp,HomologicalComplex.homologyMap_comp,hzero,comp_zero] <;> rfl

end CurveComplexGenusTwo.SourceTopology
