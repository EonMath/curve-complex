import CurveComplexGenusTwo.Octagon.GraphMV.OverlapHZero
import CurveComplexGenusTwo.Octagon.GraphMV.GraphMiddleComponents
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation

noncomputable section
open CategoryTheory CategoryTheory.Limits CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.Octagon.AttachingMap.GraphMV

set_option backward.isDefEq.respectTransparency false

private abbrev GX := TopCat.of BoundaryGraph
private abbrev U : Set GX := vertexStar
private abbrev V : Set GX := edgeMiddles
private abbrev Overlap := U ∩ V

/-- The middle-edge H0 basis is induced by the actual interval chart's edge projection. -/
def edgeHZeroCoordinates : H V 0 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  ((homotopyHomologyIso edgeMiddlesHomotopyFin 0) ≪≫
    finiteDiscreteH0Iso (Fin 4)).toLinearEquiv

private def edgeInclusionZero : H Overlap 0 ⟶ H V 0 :=
  actualSubsetHomologyMap GX Overlap V Set.inter_subset_right 0

private theorem quotientChart_index (x : Overlap) :
    (edgeMiddlesIntervalChart ⟨x.1, x.2.2⟩).1 =
      (overlapQuotientChart.symm x).1.1 := by
  let y := overlapQuotientChart.symm x
  have hq : edgeMiddlesQuotientChart ⟨y.1, y.2.2⟩ = ⟨x.1, x.2.2⟩ := by
    apply Subtype.ext
    change graphEdgeMap y.1 = x.1
    exact congrArg Subtype.val (overlapQuotientChart.apply_symm_apply x)
  have he : edgeMiddlesQuotientChart.symm ⟨x.1, x.2.2⟩ =
      ⟨y.1, y.2.2⟩ := by
    rw [← hq]
    exact edgeMiddlesQuotientChart.symm_apply_apply _
  change (middleParameterChart (edgeMiddlesQuotientChart.symm ⟨x.1,x.2.2⟩)).1 =
    y.1.1
  rw [he]
  rfl

private theorem middleHomotopy_index (x : edgeMiddles) :
    edgeMiddlesHomotopyFin.toFun x = (edgeMiddlesIntervalChart x).1 := by
  simp [edgeMiddlesHomotopyFin]
  rfl

private theorem edgeHZero_point (x : edgeMiddles) :
    edgeHZeroCoordinates
      (pointClass (TopCat.toSSet.obj (TopCat.of edgeMiddles))
        (TopCat.toSSetObj₀Equiv.symm x) (1 : ℤ)) =
      Pi.single (edgeMiddlesIntervalChart x).1 (1 : ℤ) := by
  have hmap : pointClass (TopCat.toSSet.obj (TopCat.of edgeMiddles))
      (TopCat.toSSetObj₀Equiv.symm x) ≫
        (homotopyHomologyIso edgeMiddlesHomotopyFin 0).hom =
      pointClass (TopCat.toSSet.obj (TopCat.of (Fin 4)))
        (TopCat.toSSetObj₀Equiv.symm (edgeMiddlesIntervalChart x).1) := by
    change pointClass _ _ ≫
      HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.ofHom edgeMiddlesHomotopyFin.toFun)) RZ) 0 = _
    rw [pointClass_map]
    congr 1
  change (pointClass (TopCat.toSSet.obj (TopCat.of edgeMiddles))
    (TopCat.toSSetObj₀Equiv.symm x) ≫
      ((homotopyHomologyIso edgeMiddlesHomotopyFin 0).hom ≫
        (finiteDiscreteH0Iso (Fin 4)).hom)) (1 : ℤ) = _
  rw [← Category.assoc, hmap]
  exact finiteDiscreteH0Iso_point (Fin 4) _

private theorem overlapPoint_edge_index_candidate (p : Fin 4 × Bool) :
    (edgeMiddlesIntervalChart
      ⟨(overlapPoint p).1, (overlapPoint p).2.2⟩).1 = p.1 := by
  calc
    (edgeMiddlesIntervalChart
      ⟨(overlapPoint p).1, (overlapPoint p).2.2⟩).1 =
        (overlapQuotientChart.symm (overlapPoint p)).1.1 :=
          quotientChart_index (overlapPoint p)
    _ = (overlapIntervalChart (overlapPoint p)).1 :=
      (overlap_chart_index_public (overlapPoint p)).symm
    _ = p.1 := by simp [overlapPoint]

private theorem edgeHZero_overlap_point_candidate (p : Fin 4 × Bool) :
    edgeHZeroCoordinates
      (actualSubsetHomologyMap GX Overlap edgeMiddles Set.inter_subset_right 0
        (pointClass (TopCat.toSSet.obj (TopCat.of Overlap))
          (TopCat.toSSetObj₀Equiv.symm (overlapPoint p)) (1 : ℤ))) =
      Pi.single p.1 (1 : ℤ) := by
  let q : edgeMiddles := ⟨(overlapPoint p).1, (overlapPoint p).2.2⟩
  have hmap : pointClass (TopCat.toSSet.obj (TopCat.of Overlap))
      (TopCat.toSSetObj₀Equiv.symm (overlapPoint p)) ≫
      actualSubsetHomologyMap GX Overlap edgeMiddles Set.inter_subset_right 0 =
    pointClass (TopCat.toSSet.obj (TopCat.of edgeMiddles))
      (TopCat.toSSetObj₀Equiv.symm q) := by
    change pointClass _ _ ≫
      HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map
          (singularSubsetInclusion GX Overlap edgeMiddles Set.inter_subset_right)) RZ) 0 = _
    rw [pointClass_map]
    congr 1
  change edgeHZeroCoordinates
    ((pointClass (TopCat.toSSet.obj (TopCat.of Overlap))
      (TopCat.toSSetObj₀Equiv.symm (overlapPoint p)) ≫
        actualSubsetHomologyMap GX Overlap edgeMiddles Set.inter_subset_right 0) (1 : ℤ)) = _
  rw [hmap]
  exact (edgeHZero_point q).trans
    (congrArg (fun i : Fin 4 => Pi.single i (1 : ℤ))
      (overlapPoint_edge_index_candidate p))

private theorem edgeInclusion_coordinates_candidate
    (x : H Overlap 0) (i : Fin 4) :
    edgeHZeroCoordinates
        (actualSubsetHomologyMap GX Overlap edgeMiddles Set.inter_subset_right 0 x) i =
      overlapHZeroCoordinates x (i, false) +
        overlapHZeroCoordinates x (i, true) := by
  let L : (Fin 4 × Bool → ℤ) →ₗ[ℤ] ℤ :=
    (LinearMap.proj (R := ℤ) (φ := fun _ : Fin 4 => ℤ) i).comp
      (edgeHZeroCoordinates.toLinearMap.comp
        ((actualSubsetHomologyMap GX Overlap edgeMiddles
          Set.inter_subset_right 0).hom.comp
            overlapHZeroCoordinates.symm.toLinearMap))
  let R : (Fin 4 × Bool → ℤ) →ₗ[ℤ] ℤ :=
    LinearMap.proj (R := ℤ) (φ := fun _ : Fin 4 × Bool => ℤ) (i, false) +
      LinearMap.proj (R := ℤ) (φ := fun _ : Fin 4 × Bool => ℤ) (i, true)
  have hLR : L = R := by
    apply (Pi.basisFun ℤ (Fin 4 × Bool)).ext
    intro p
    simp only [Pi.basisFun_apply]
    have hp : overlapHZeroCoordinates.symm (Pi.single p (1 : ℤ)) =
        pointClass (TopCat.toSSet.obj (TopCat.of Overlap))
          (TopCat.toSSetObj₀Equiv.symm (overlapPoint p)) (1 : ℤ) := by
      apply overlapHZeroCoordinates.injective
      rw [overlapHZeroCoordinates.apply_symm_apply,
        overlapHZeroCoordinates_point]
    change edgeHZeroCoordinates
      (actualSubsetHomologyMap GX Overlap edgeMiddles Set.inter_subset_right 0
        (overlapHZeroCoordinates.symm (Pi.single p (1 : ℤ)))) i =
      (Pi.single p (1 : ℤ) : Fin 4 × Bool → ℤ) (i, false) +
        (Pi.single p (1 : ℤ) : Fin 4 × Bool → ℤ) (i, true)
    rw [hp, edgeHZero_overlap_point_candidate]
    rcases p with ⟨j,b⟩
    cases b <;> by_cases h : j = i <;> simp [h]
  have h := congrArg (fun f : (Fin 4 × Bool → ℤ) →ₗ[ℤ] ℤ =>
    f (overlapHZeroCoordinates x)) hLR
  simpa [L, R] using h

/-- The overlap point on edge `p.1` lands in that same actual middle interval. -/
theorem overlapPoint_edge_index (p : Fin 4 × Bool) :
    (edgeMiddlesIntervalChart
      ⟨(overlapPoint p).1, (overlapPoint p).2.2⟩).1 = p.1 := by
  exact overlapPoint_edge_index_candidate p

theorem edgeHZeroCoordinates_overlap_point (p : Fin 4 × Bool) :
    edgeHZeroCoordinates
      (edgeInclusionZero
        (pointClass (TopCat.toSSet.obj (TopCat.of Overlap))
          (TopCat.toSSetObj₀Equiv.symm (overlapPoint p)) (1 : ℤ))) =
      Pi.single p.1 (1 : ℤ) := by
  exact edgeHZero_overlap_point_candidate p

/-- Actual H0 inclusion identifies the low and high overlap points on each edge. -/
theorem edgeInclusion_coordinates (x : H Overlap 0) (i : Fin 4) :
    edgeHZeroCoordinates (edgeInclusionZero x) i =
      overlapHZeroCoordinates x (i, false) +
        overlapHZeroCoordinates x (i, true) := by
  exact edgeInclusion_coordinates_candidate x i

#print axioms overlapPoint_edge_index
#print axioms edgeHZeroCoordinates_overlap_point
#print axioms edgeInclusion_coordinates

end CurveComplex.Octagon.AttachingMap.GraphMV
