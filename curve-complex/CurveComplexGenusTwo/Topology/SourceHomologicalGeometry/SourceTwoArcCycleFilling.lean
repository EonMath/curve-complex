import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceCarriedCycleFundamentalZeroFills

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CategoryTheory.Limits CurveComplexGenusTwo.CWHurewicz Convexity PathChains
open CurveComplex.BranchedDoubleCover
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem two_arc_cycle_fills_of_curve_fundamental_zero
    {S : Type} [TopologicalSpace S] {x y : S} (p q : Path x y) (c : Curve S)
    (hp : Set.range p ⊆ c.image) (hq : Set.range q ⊆ c.image)
    (hc : HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩)) 1
      CircleFundamentalCycle.fundamentalClass = 0) :
    ∃ B : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
      singularBoundaryFinsupp (TopCat.of S) 1 B =
        Finsupp.single (edgeSimplex p.toContinuousMap 0 1) 1 -
          Finsupp.single (edgeSimplex q.toContinuousMap 0 1) 1 := by
  classical
  apply carried_cycle_fills_of_curve_fundamental_zero c _ _ _ hc
  · rw [map_sub,edgeSimplex_boundary,edgeSimplex_boundary]
    change (Finsupp.single (vertexSimplex (p 1)) 1 - Finsupp.single (vertexSimplex (p 0)) 1) -
      (Finsupp.single (vertexSimplex (q 1)) 1 - Finsupp.single (vertexSimplex (q 0)) 1) = 0
    rw [p.target,p.source,q.target,q.source]
    abel
  · intro a ha z
    have hm := Finset.mem_union.mp (Finsupp.support_sub ha)
    rcases hm with h | h
    · have he : a = edgeSimplex p.toContinuousMap 0 1 := by
        simpa using h
      subst a
      exact hp ⟨weightedTime 1 ![0,1] z,rfl⟩
    · have he : a = edgeSimplex q.toContinuousMap 0 1 := by
        simpa using h
      subst a
      exact hq ⟨weightedTime 1 ![0,1] z,rfl⟩

end CurveComplexGenusTwo.SourceTopology
