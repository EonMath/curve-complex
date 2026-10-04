import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceHomologicallyNonzeroCurveCanonicalProof

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CategoryTheory.Limits CurveComplexGenusTwo.CWHurewicz
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem carried_cycle_fills_of_curve_fundamental_zero
    {S : Type} [TopologicalSpace S] (c : Curve S)
    (chain : (TopCat.toSSet.obj (TopCat.of S)) _⦋1⦌ →₀ ℤ)
    (hchain : singularBoundaryFinsupp (TopCat.of S) 0 chain = 0)
    (hcarry : ∀ a ∈ chain.support, ∀ z,
      TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a z ∈ c.image)
    (hc : HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩)) 1
      CircleFundamentalCycle.fundamentalClass = 0) :
    ∃ b : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
      singularBoundaryFinsupp (TopCat.of S) 1 b = chain := by
  obtain ⟨cycle,hcycle,hpush⟩ := singular_cycle_carried_by_curve_lifts c chain hchain hcarry
  have hzero : ((mvAmbientComplex (TopCat.of Circle)).sc 1).g cycle = 0 := by
    change (mvAmbientComplex (TopCat.of Circle)).d 1 ((ComplexShape.down ℕ).next 1) cycle = 0
    rw [ChainComplex.next_nat_succ]
    exact LinearMap.mem_ker.mp hcycle
  obtain ⟨b,hb⟩ := CurveComplex.WeightedFlowScratch.chainMap_cycle_fills_of_homologyMap_zero
    (singularFinsuppMap (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩)) 1 cycle hzero
    (circle_chainMap_zero_of_fundamental_zero ⟨c.map,c.embedded.continuous⟩ hc)
  refine ⟨b,?_⟩
  simp only [mvAmbientComplex,ChainComplex.of_d,singularFinsuppMap_f] at hb
  change singularBoundaryFinsupp (TopCat.of S) 1 b =
    singularFinsuppPush (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩) 1 cycle at hb
  exact hb.trans hpush

end CurveComplexGenusTwo.SourceTopology
