import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceClosedSurfaceThetaRetentionCanonicalProof
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceHomologicallyNonzeroCurveCanonicalProof

import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceTwoArcParameterizedCurve
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceTwoArcLoopChainCorrection
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceTwoArcCycleFilling
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceSameImageFundamentalNonzero
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceFundamentalZeroOfChainFilling

namespace CurveComplex
open CurveComplexGenusTwo.CWHurewicz CurveComplexGenusTwo.SourceTopology
open CurveComplexGenusTwo.SourceTopology.PathChains
open scoped Simplicial
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem source_first_return_homologically_nonzero_branch
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D)
    (hb : HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom ⟨b.map,b.embedded.continuous⟩)) 1
      CircleFundamentalCycle.fundamentalClass ≠ 0) :
    ∃ i : Bool, HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom
        ⟨(B.boundary i).map,(B.boundary i).embedded.continuous⟩)) 1
      CircleFundamentalCycle.fundamentalClass ≠ 0 := by
  classical
  let p : Path D.start D.finish :=
    ⟨B.closing false,B.closing_zero false,B.closing_one false⟩
  let q : Path D.start D.finish :=
    ⟨B.closing true,B.closing_zero true,B.closing_one true⟩
  let r : Path D.start D.finish := ⟨D.first,D.first_zero,D.first_one⟩
  have hcross (s t : CurveComplex.Interval) (he : p s = q t) :
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    have hmem : p s ∈ Set.range (B.closing false) ∩ Set.range (B.closing true) :=
      ⟨⟨s,rfl⟩,⟨t,he.symm⟩⟩
    rw [B.closing_inter] at hmem
    rcases Set.mem_insert_iff.mp hmem with hs | hs
    · left
      have hp0 : p s = p 0 := hs.trans p.source.symm
      have hq0 : q t = q 0 := he.symm.trans (hs.trans q.source.symm)
      exact ⟨(B.closing_embedded false).injective hp0,
        (B.closing_embedded true).injective hq0⟩
    · right
      have hs' : p s = D.finish := Set.mem_singleton_iff.mp hs
      have hp1 : p s = p 1 := hs'.trans p.target.symm
      have hq1 : q t = q 1 := he.symm.trans (hs'.trans q.target.symm)
      exact ⟨(B.closing_embedded false).injective hp1,
        (B.closing_embedded true).injective hq1⟩
  obtain ⟨c,himage,hparam⟩ := two_embedded_arcs_parameterized_curve p q
    (B.closing_embedded false).injective (B.closing_embedded true).injective hcross
  have hcb : c.image = b.image := himage.trans B.closing_cover
  have hc := curve_fundamental_nonzero_of_same_image b c hcb.symm hb
  by_contra hn
  have hzero (i : Bool) : HomologicalComplex.homologyMap
      (actualSingularFunctor.map (TopCat.ofHom
        ⟨(B.boundary i).map,(B.boundary i).embedded.continuous⟩)) 1
      CircleFundamentalCycle.fundamentalClass = 0 := by
    by_contra hi
    exact hn ⟨i,hi⟩
  have hr (i : Bool) : Set.range r ⊆ (B.boundary i).image := by
    rw [B.boundary_image]
    intro x hx
    exact Or.inl hx
  have hp : Set.range p ⊆ (B.boundary false).image := by
    rw [B.boundary_image]
    intro x hx
    exact Or.inr hx
  have hq : Set.range q ⊆ (B.boundary true).image := by
    rw [B.boundary_image]
    intro x hx
    exact Or.inr hx
  obtain ⟨P,hP⟩ := two_arc_cycle_fills_of_curve_fundamental_zero r p
    (B.boundary false) (hr false) hp (hzero false)
  obtain ⟨Q,hQ⟩ := two_arc_cycle_fills_of_curve_fundamental_zero r q
    (B.boundary true) (hr true) hq (hzero true)
  obtain ⟨A,hA⟩ := two_arc_loop_fundamental_chain_correction p q c hparam
  apply hc
  apply curve_fundamental_zero_of_chain_filling c (A+Q-P)
  rw [map_sub,map_add,hA,hQ,hP]
  abel

end CurveComplex
