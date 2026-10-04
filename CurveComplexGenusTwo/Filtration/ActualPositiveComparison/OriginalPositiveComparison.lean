import CurveComplexGenusTwo.Foundations.SingularComparison
import CurveComplexGenusTwo.Topology.Basic
import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.ActualConnectivity.ActualMain12FullConnectivity
import CurveComplexGenusTwo.Filtration.ActualPositiveComparison.PositiveComparison
namespace CurveGenusTwo.Filtration
open CurveComplex
open CurveComplex.HyperellipticModel
open CurveComplexGenusTwo.Topology
open CurveComplexGenusTwo.SourceTopology
variable {V : Type} [DecidableEq V] [LinearOrder V]

abbrev toAbstractComplex (K : FiniteComplex V) :
    AbstractSimplicialComplex (ActiveVertex K) := geometricComplex K

abbrev weakRealization (K : FiniteComplex V) := geometricRealization K

theorem augmented_singular_comparison_positive (K : FiniteComplex V)
    (n : ℕ) (hn : 0 < n) :
    Nonempty (ModuleCat.of ℤ (reducedHomology K n) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (weakRealization K))) := by
  have hdec : (inferInstance : DecidableEq V) =
      (LinearOrder.toDecidableEq : DecidableEq V) := Subsingleton.elim _ _
  cases hdec
  exact augmented_singular_comparison_positive_canonical K n hn
end CurveGenusTwo.Filtration
