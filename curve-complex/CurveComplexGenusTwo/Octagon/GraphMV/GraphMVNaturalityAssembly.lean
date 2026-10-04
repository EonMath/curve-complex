import CurveComplexGenusTwo.Octagon.GraphMV.GraphMVAssembly

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.Octagon.AttachingMap.GraphMV

private abbrev GX := TopCat.of BoundaryGraph
private abbrev U : Set GX := vertexStar
private abbrev V : Set GX := edgeMiddles

private def starInclusionZero : H ↥(U ∩ V) 0 ⟶ H U 0 :=
  actualSubsetHomologyMap GX (U ∩ V) U Set.inter_subset_left 0

private def edgeInclusionZero : H ↥(U ∩ V) 0 ⟶ H V 0 :=
  actualSubsetHomologyMap GX (U ∩ V) V Set.inter_subset_right 0

def vertexStarHZeroEquiv : H U 0 ≃ₗ[ℤ] ℤ := by
  letI : ContractibleSpace U := vertexStar_contractible
  exact (asIso ((TopCat.of U).singularHomology₀ε (ModuleCat.of ℤ ℤ))).toLinearEquiv

theorem vertex_star_naturality_of_overlap_sum
    (e : H ↥(U ∩ V) 0 ≃ₗ[ℤ] CurveComplex.Octagon.GraphMV.OverlapCoordinates)
    (hSum : ∀ x : H ↥(U ∩ V) 0,
      ((TopCat.of ↥(U ∩ V)).singularHomology₀ε (ModuleCat.of ℤ ℤ)) x =
        ∑ i : Fin 4, (e x (i, false) + e x (i, true)))
    (x : H ↥(U ∩ V) 0) :
    vertexStarHZeroEquiv (starInclusionZero x) =
      ∑ i : Fin 4, (e x (i, false) + e x (i, true)) := by
  have hn := congrArg (fun f => f x)
    (CircleHomologyComputation.augmentation_naturality
      (singularSubsetInclusion GX (U ∩ V) U Set.inter_subset_left))
  change vertexStarHZeroEquiv (starInclusionZero x) =
    ((TopCat.of ↥(U ∩ V)).singularHomology₀ε (ModuleCat.of ℤ ℤ)) x at hn
  exact hn.trans (hSum x)

theorem graph_difference_kernel_of_naturality
    (e : H ↥(U ∩ V) 0 ≃ₗ[ℤ] CurveComplex.Octagon.GraphMV.OverlapCoordinates)
    (eStar : H U 0 ≃ₗ[ℤ] ℤ)
    (eEdge : H V 0 ≃ₗ[ℤ] (Fin 4 → ℤ))
    (hStar : ∀ x : H ↥(U ∩ V) 0,
      eStar (starInclusionZero x) =
        ∑ i : Fin 4, (e x (i, false) + e x (i, true)))
    (hEdge : ∀ (x : H ↥(U ∩ V) 0) (i : Fin 4),
      eEdge (edgeInclusionZero x) i = e x (i, false) + e x (i, true))
    (x : H ↥(U ∩ V) 0) :
    graphMVDifference 0 x = 0 ↔
      CurveComplex.Octagon.GraphMV.difference (e x) = 0 := by
  rw [show graphMVDifference 0 x =
      (starInclusionZero x, -edgeInclusionZero x) from
    actualMVDifference_apply GX U V 0 x]
  constructor
  · intro h
    have hs : starInclusionZero x = 0 := congrArg Prod.fst h
    have he : edgeInclusionZero x = 0 := by
      have h' := congrArg Prod.snd h
      exact neg_eq_zero.mp h'
    apply Prod.ext
    · change (∑ i : Fin 4, (e x (i, false) + e x (i, true))) = 0
      rw [← hStar, hs, map_zero]
    · funext i
      change e x (i, false) + e x (i, true) = 0
      rw [← hEdge, he, map_zero]
      rfl
  · intro h
    have hs : starInclusionZero x = 0 := by
      apply eStar.injective
      rw [hStar]
      rw [map_zero]
      have hsum := congrArg Prod.fst h
      change (∑ i : Fin 4, (e x (i, false) + e x (i, true))) = 0 at hsum
      exact hsum
    have he : edgeInclusionZero x = 0 := by
      apply eEdge.injective
      funext i
      rw [hEdge]
      simp only [Pi.zero_apply, map_zero]
      have hcoord := congrFun (congrArg Prod.snd h) i
      change e x (i, false) + e x (i, true) = 0 at hcoord
      exact hcoord
    simp [hs, he]

def graph_H1_iso_of_naturality
    (e : H ↥(U ∩ V) 0 ≃ₗ[ℤ] CurveComplex.Octagon.GraphMV.OverlapCoordinates)
    (eStar : H U 0 ≃ₗ[ℤ] ℤ)
    (eEdge : H V 0 ≃ₗ[ℤ] (Fin 4 → ℤ))
    (hStar : ∀ x : H ↥(U ∩ V) 0,
      eStar (starInclusionZero x) =
        ∑ i : Fin 4, (e x (i, false) + e x (i, true)))
    (hEdge : ∀ (x : H ↥(U ∩ V) 0) (i : Fin 4),
      eEdge (edgeInclusionZero x) i = e x (i, false) + e x (i, true)) :
    H BoundaryGraph 1 ≅ ModuleCat.of ℤ (Fin 4 → ℤ) :=
  graph_H1_iso_of_coordinate_map e
    (graph_difference_kernel_of_naturality e eStar eEdge hStar hEdge)

def graph_H1_iso_of_overlap_edge_data
    (e : H ↥(U ∩ V) 0 ≃ₗ[ℤ] CurveComplex.Octagon.GraphMV.OverlapCoordinates)
    (eEdge : H V 0 ≃ₗ[ℤ] (Fin 4 → ℤ))
    (hSum : ∀ x : H ↥(U ∩ V) 0,
      ((TopCat.of ↥(U ∩ V)).singularHomology₀ε (ModuleCat.of ℤ ℤ)) x =
        ∑ i : Fin 4, (e x (i, false) + e x (i, true)))
    (hEdge : ∀ (x : H ↥(U ∩ V) 0) (i : Fin 4),
      eEdge (edgeInclusionZero x) i = e x (i, false) + e x (i, true)) :
    H BoundaryGraph 1 ≅ ModuleCat.of ℤ (Fin 4 → ℤ) :=
  graph_H1_iso_of_naturality e vertexStarHZeroEquiv eEdge
    (vertex_star_naturality_of_overlap_sum e hSum) hEdge

end CurveComplex.Octagon.AttachingMap.GraphMV

#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.graph_H1_iso_of_naturality
#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.vertex_star_naturality_of_overlap_sum
#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.graph_H1_iso_of_overlap_edge_data
