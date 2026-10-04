import CurveComplexGenusTwo.Octagon.GraphMV.GraphVertexContraction
import CurveComplexGenusTwo.Octagon.GraphMV.GraphMiddleComponents
import CurveComplexGenusTwo.Octagon.GraphMV.GraphMVNumericalReduction
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseStatements

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.Octagon.AttachingMap.GraphMV

private abbrev GX := TopCat.of BoundaryGraph
private abbrev U : Set GX := vertexStar
private abbrev V : Set GX := edgeMiddles

theorem graphMV_pair_positive_zero (n : ℕ) (hn : 0 < n) :
    IsZero (ModuleCat.of ℤ (H U n × H V n)) := by
  letI : ContractibleSpace U := vertexStar_contractible
  have hu : IsZero (H U n) :=
    CircleHomologyComputation.contractible_positive_homology U n hn
  have hv : IsZero (H V n) := edgeMiddles_positive_homology n hn
  letI := ModuleCat.subsingleton_of_isZero hu
  letI := ModuleCat.subsingleton_of_isZero hv
  exact ModuleCat.isZero_of_subsingleton _

theorem graph_higher_zero_of_overlap
    (hoverlap : ∀ n : ℕ, 0 < n → IsZero (H ↥(U ∩ V) n))
    (n : ℕ) (hn : 2 ≤ n) : IsZero (H BoundaryGraph n) :=
  graph_higher_zero_of_components graphMV_pair_positive_zero hoverlap n hn

def graph_H1_iso_of_coordinate_map
    (e : H ↥(U ∩ V) 0 ≃ₗ[ℤ] CurveComplex.Octagon.GraphMV.OverlapCoordinates)
    (hdiff : ∀ x : H ↥(U ∩ V) 0,
      graphMVDifference 0 x = 0 ↔
        CurveComplex.Octagon.GraphMV.difference (e x) = 0) :
    H BoundaryGraph 1 ≅ ModuleCat.of ℤ (Fin 4 → ℤ) :=
  graph_H1_iso_of_coordinates (graphMV_pair_positive_zero 1 (by omega)) e hdiff

end CurveComplex.Octagon.AttachingMap.GraphMV

#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.graphMV_pair_positive_zero
#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.graph_H1_iso_of_coordinate_map
