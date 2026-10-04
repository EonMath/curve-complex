import CurveComplexGenusTwo.Topology.ActualOriginalArticle.Main12OriginalCanonicalImportsHaasConditionalV15
import SourceTopologyMainBound
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.SourceRealization
import CurveComplexGenusTwo.Topology.Basic
import CurveComplexGenusTwo.Foundations.RealizationCW
import CurveComplexGenusTwo.CWHurewicz.RealizationWhiteheadConsumer
import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.KernelEndpoints

open Topology CategoryTheory CategoryTheory.Limits
namespace CurveComplexGenusTwo.CWHurewicz
private theorem allPiTrivialOfSimplyConnectedAcyclic {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
    (hacyclic : CurveComplexGenusTwo.Topology.IsAcyclicIntegral X) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : X, Subsingleton (HomotopyGroup.Pi n X x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn x
    rcases n with _ | _ | k
    · omega
    · exact (HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)).injective.subsingleton
    · have hlower (j : ℕ) (hj : 1 ≤ j) (hjn : j < k+2) :
          Subsingleton (HomotopyGroup.Pi j X x) := ih j hjn hj x
      have hinj := CWFirstDegree.geometric_injective k x hlower
      have hz : IsZero (H X (k+2)) := hacyclic.1 (k+2) (by omega)
      letI := ModuleCat.subsingleton_of_isZero hz
      exact hinj.subsingleton
private theorem contractibleSimplyConnectedAcyclicCW {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
    (hacyclic : CurveComplexGenusTwo.Topology.IsAcyclicIntegral X) : ContractibleSpace X := by
  exact contractibleOfCWAllPiSubsingletonT2_actual (allPiTrivialOfSimplyConnectedAcyclic hacyclic)
end CurveComplexGenusTwo.CWHurewicz

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex
open CurveComplexGenusTwo.Topology
open scoped Manifold ContDiff

theorem c1_contractible_genusTwo
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (hS : IsGenus S 2) :
    ContractibleSpace (curveComplexRealization S 1) := by
  letI : SimplyConnectedSpace (curveComplexRealization S 1) :=
    c1_simplyConnected_allGenus S 2 (by omega) hS
  have hacyclic : IsAcyclicIntegral (curveComplexRealization S 1) :=
    c1_acyclic_genusTwo S hS
  exact CWHurewicz.contractibleSimplyConnectedAcyclicCW hacyclic

end CurveComplexGenusTwo.SourceTopology
