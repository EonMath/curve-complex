import CurveComplexGenusTwo.Octagon.GraphMV.GraphCoverBasic
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.Octagon.AttachingMap.GraphMV

private abbrev GX := TopCat.of BoundaryGraph
private abbrev U : Set GX := vertexStar
private abbrev V : Set GX := edgeMiddles

def graphMVDifference (n : ℕ) :
    H ↥(U ∩ V) n ⟶ ModuleCat.of ℤ (H U n × H V n) :=
  actualMVDifference GX U V n

def graphMVSum (n : ℕ) :
    ModuleCat.of ℤ (H U n × H V n) ⟶ H BoundaryGraph n :=
  actualMVSum GX U V n

def graphMVConnecting (n : ℕ) :
    H BoundaryGraph (n + 1) ⟶ H ↥(U ∩ V) n :=
  actualMVConnecting GX U V vertexStar_open edgeMiddles_open graph_cover n

theorem graphMV_connecting_difference (n : ℕ) :
    graphMVConnecting n ≫ graphMVDifference n = 0 :=
  actualMVConnecting_difference GX U V vertexStar_open edgeMiddles_open graph_cover n

theorem graphMV_sum_connecting (n : ℕ) :
    graphMVSum (n + 1) ≫ graphMVConnecting n = 0 :=
  actualMVSum_connecting GX U V vertexStar_open edgeMiddles_open graph_cover n

theorem graphMV_exact_intersection (n : ℕ) :
    (ShortComplex.mk (graphMVConnecting n) (graphMVDifference n)
      (graphMV_connecting_difference n)).Exact :=
  actualMV_exact_intersection GX U V vertexStar_open edgeMiddles_open graph_cover n

theorem graphMV_exact_ambient (n : ℕ) :
    (ShortComplex.mk (graphMVSum (n + 1)) (graphMVConnecting n)
      (graphMV_sum_connecting n)).Exact :=
  actualMV_exact_ambient GX U V vertexStar_open edgeMiddles_open graph_cover n

theorem graph_higher_zero_of_components
    (hpair : ∀ n : ℕ, 0 < n →
      IsZero (ModuleCat.of ℤ (H U n × H V n)))
    (hoverlap : ∀ n : ℕ, 0 < n → IsZero (H ↥(U ∩ V) n))
    (n : ℕ) (hn : 2 ≤ n) : IsZero (H BoundaryGraph n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have ex := graphMV_exact_ambient k
  exact ex.isZero_X₂ ((hpair (k + 1) (by omega)).eq_of_src _ _)
    ((hoverlap k (by omega)).eq_of_tgt _ _)

end CurveComplex.Octagon.AttachingMap.GraphMV

#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.graphMV_exact_intersection
#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.graphMV_exact_ambient
#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.graph_higher_zero_of_components
