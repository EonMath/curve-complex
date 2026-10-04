import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage
import CurveComplexGenusTwo.Topology.ActualConnectivity.ActualMain12NonboundingCircle
import CurveComplexGenusTwo.Topology.ActualConnectivity.ActualMain12SeparatingFundamentalZero
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
namespace CurveComplex
open Set Topology Schoenflies CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz CurveComplexGenusTwo.SourceTopology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
-- Original approved Main12 seed from the shared literal nonbounding circle
-- and the verified exact original whole embedded-circle collar producer.
theorem source_genus_two_nonseparating_curve_exists
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2) :
    ∃ c : EssentialCurve S, Nonseparating c.val := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  obtain ⟨c,z,hz,hnfill⟩ := source_positive_genus_nonbounding_embedded_circle_cycle S 2 (by omega) hS
  have hc : Essential c := by
    intro hdisc
    exact hnfill (boundsDisc_singularCircleCycle_fills c hdisc z hz)
  by_cases hns : Nonseparating c
  · exact ⟨⟨c,hc⟩,hns⟩
  · have hCollar : ∃ e : C(Set.Ioo (-1:ℝ) 1 × Circle,S),
        IsOpenEmbedding e ∧ ∀ w : Circle,e (⟨0,by norm_num⟩,w)=c.map w := by
      exact LocalSurgery.actual_original_essential_circle_has_annular_collar
        S 2 (by omega) hS ⟨c,hc⟩
    obtain ⟨e,he,hcore⟩ := hCollar
    have hfund := source_separating_curve_actual_annular_fundamental_zero S hS c hns e he hcore
    have hmap := circle_chainMap_zero_of_fundamental_zero
      ⟨c.map,c.embedded.continuous⟩ hfund
    have hcycle : ((mvAmbientComplex (TopCat.of Circle)).sc 1).g z=0 := by
      change (mvAmbientComplex (TopCat.of Circle)).d 1 ((ComplexShape.down ℕ).next 1) z=0
      rw [ChainComplex.next_nat_succ]
      exact LinearMap.mem_ker.mp hz
    obtain ⟨b,hb⟩ := WeightedFlowScratch.chainMap_cycle_fills_of_homologyMap_zero
      (singularFinsuppMap (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩)) 1 z hcycle hmap
    apply (hnfill ?_).elim
    refine ⟨b,?_⟩
    simp only [mvAmbientComplex,ChainComplex.of_d,singularFinsuppMap_f] at hb
    exact hb
end CurveComplex
