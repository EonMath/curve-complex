import CurveComplexGenusTwo.Topology.CapBandGeometry.BandMVPoints

noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.CapBandGeometry
set_option backward.isDefEq.respectTransparency false
variable {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)

def bandMVMiddleInclusionZero : H ↥(bandMVU D B ∩ bandMVV D B) 0 ⟶ H (bandMVV D B) 0 :=
  actualSubsetHomologyMap (bandTopCat D B) _ _ Set.inter_subset_right 0

theorem bandMVMiddleInclusion_point (i : Fin 4) :
    bandMVVHZeroCoordinates D B (bandMVMiddleInclusionZero D B
      (pointClass (TopCat.toSSet.obj (TopCat.of ↥(bandMVU D B ∩ bandMVV D B)))
        (TopCat.toSSetObj₀Equiv.symm (bandMVOverlapPoint D B i)) (1 : ℤ))) =
      Pi.single (⟨i.val / 2, by omega⟩ : Fin 2) (1 : ℤ) := by
  let q : bandMVV D B := ⟨(bandMVOverlapPoint D B i).1, (bandMVOverlapPoint D B i).2.2⟩
  have hmap : pointClass (TopCat.toSSet.obj (TopCat.of ↥(bandMVU D B ∩ bandMVV D B)))
      (TopCat.toSSetObj₀Equiv.symm (bandMVOverlapPoint D B i)) ≫
        bandMVMiddleInclusionZero D B =
      pointClass (TopCat.toSSet.obj (TopCat.of (bandMVV D B)))
        (TopCat.toSSetObj₀Equiv.symm q) := by
    change pointClass _ _ ≫ HomologicalComplex.homologyMap (SSet.chainComplexMap
      (TopCat.toSSet.map (singularSubsetInclusion (bandTopCat D B) _ _
        Set.inter_subset_right)) RZ) 0 = _
    rw [pointClass_map]
    congr 1
  change bandMVVHZeroCoordinates D B
    ((pointClass _ _ ≫ bandMVMiddleInclusionZero D B) (1 : ℤ)) = _
  rw [hmap]
  change finiteHomotopyHZeroCoordinates (bandMVVHomotopyFinTwo D B)
    (pointClass _ _ (1 : ℤ)) = _
  rw [finiteHomotopyHZeroCoordinates_point]
  exact congrArg (fun j : Fin 2 => Pi.single j (1 : ℤ))
    (bandMVOverlapPoint_middle_index D B i)

/-- Actual inclusion identifies overlap windows 0/1 and 2/3 respectively. -/
theorem bandMVMiddleInclusion_coordinates
    (x : H ↥(bandMVU D B ∩ bandMVV D B) 0) (i : Fin 2) :
    bandMVVHZeroCoordinates D B (bandMVMiddleInclusionZero D B x) i =
      bandMVOverlapHZeroCoordinates D B x ⟨2*i.val, by omega⟩ +
        bandMVOverlapHZeroCoordinates D B x ⟨2*i.val+1, by omega⟩ := by
  let e := bandMVOverlapHZeroCoordinates D B
  let L : (Fin 4 → ℤ) →ₗ[ℤ] ℤ :=
    (LinearMap.proj (R := ℤ) (φ := fun _ : Fin 2 => ℤ) i).comp
      ((bandMVVHZeroCoordinates D B).toLinearMap.comp
        ((bandMVMiddleInclusionZero D B).hom.comp e.symm.toLinearMap))
  let R : (Fin 4 → ℤ) →ₗ[ℤ] ℤ :=
    LinearMap.proj (R := ℤ) (φ := fun _ : Fin 4 => ℤ) ⟨2*i.val, by omega⟩ +
      LinearMap.proj (R := ℤ) (φ := fun _ : Fin 4 => ℤ) ⟨2*i.val+1, by omega⟩
  have hLR : L = R := by
    apply (Pi.basisFun ℤ (Fin 4)).ext
    intro j
    simp only [Pi.basisFun_apply]
    have hp : e.symm (Pi.single j (1 : ℤ)) =
        pointClass (TopCat.toSSet.obj (TopCat.of ↥(bandMVU D B ∩ bandMVV D B)))
          (TopCat.toSSetObj₀Equiv.symm (bandMVOverlapPoint D B j)) (1 : ℤ) := by
      apply e.injective
      rw [e.apply_symm_apply, bandMVOverlapHZeroCoordinates_point]
    change bandMVVHZeroCoordinates D B (bandMVMiddleInclusionZero D B
      (e.symm (Pi.single j (1 : ℤ)))) i =
      (Pi.single j (1 : ℤ) : Fin 4 → ℤ) ⟨2*i.val, by omega⟩ +
        (Pi.single j (1 : ℤ) : Fin 4 → ℤ) ⟨2*i.val+1, by omega⟩
    rw [hp, bandMVMiddleInclusion_point]
    fin_cases i <;> fin_cases j <;> simp
  have h := congrArg (fun f : (Fin 4 → ℤ) →ₗ[ℤ] ℤ => f (e x)) hLR
  simpa [L, R] using h

theorem bandMVOverlap_augmentation_sum
    (x : H ↥(bandMVU D B ∩ bandMVV D B) 0) :
    ((TopCat.of ↥(bandMVU D B ∩ bandMVV D B)).singularHomology₀ε
      (ModuleCat.of ℤ ℤ)) x = ∑ i : Fin 4, bandMVOverlapHZeroCoordinates D B x i := by
  classical
  let e := bandMVOverlapHZeroCoordinates D B
  let P : Fin 4 → H ↥(bandMVU D B ∩ bandMVV D B) 0 := fun i =>
    pointClass (TopCat.toSSet.obj (TopCat.of ↥(bandMVU D B ∩ bandMVV D B)))
      (TopCat.toSSetObj₀Equiv.symm (bandMVOverlapPoint D B i)) (1 : ℤ)
  have hp (i : Fin 4) : e (P i) = Pi.single i (1 : ℤ) :=
    bandMVOverlapHZeroCoordinates_point D B i
  have hdecomp : x = ∑ i : Fin 4, (e x i) • P i := by
    apply e.injective
    rw [map_sum]
    simp only [map_zsmul, hp]
    have hsingle (i : Fin 4) :
        (e x i) • (Pi.single i (1 : ℤ) : Fin 4 → ℤ) = Pi.single i (e x i) := by
      funext j
      by_cases h : j = i
      · subst j; simp
      · simp [Pi.single_apply, h]
    simp only [hsingle]
    exact (Finset.univ_sum_single (e x)).symm
  have ha (i : Fin 4) :
      ((TopCat.of ↥(bandMVU D B ∩ bandMVV D B)).singularHomology₀ε
        (ModuleCat.of ℤ ℤ)) (P i) = 1 := by
    have hm : pointClass (TopCat.toSSet.obj (TopCat.of ↥(bandMVU D B ∩ bandMVV D B)))
        (TopCat.toSSetObj₀Equiv.symm (bandMVOverlapPoint D B i)) ≫
        ((TopCat.of ↥(bandMVU D B ∩ bandMVV D B)).singularHomology₀ε
          (ModuleCat.of ℤ ℤ)) = 𝟙 _ := by
      simp [pointClass, TopCat.singularHomology₀ε, SSet.homology₀ε]
    exact congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => f (1 : ℤ)) hm
  conv_lhs => rw [hdecomp]
  simp only [map_sum, map_zsmul, ha, smul_eq_mul, mul_one]
  rfl


def bandMVSquareInclusionZero : H ↥(bandMVU D B ∩ bandMVV D B) 0 ⟶ H (bandMVU D B) 0 :=
  actualSubsetHomologyMap (bandTopCat D B) _ _ Set.inter_subset_left 0

theorem bandMVSquareInclusion_coordinates
    (x : H ↥(bandMVU D B ∩ bandMVV D B) 0) :
    bandMVUHZeroCoordinates D B (bandMVSquareInclusionZero D B x) =
      ∑ i : Fin 4, bandMVOverlapHZeroCoordinates D B x i := by
  have hn := congrArg (fun f => f x) (augmentation_naturality
    (singularSubsetInclusion (bandTopCat D B) _ _ Set.inter_subset_left))
  change bandMVUHZeroCoordinates D B (bandMVSquareInclusionZero D B x) =
    ((TopCat.of ↥(bandMVU D B ∩ bandMVV D B)).singularHomology₀ε
      (ModuleCat.of ℤ ℤ)) x at hn
  exact hn.trans (bandMVOverlap_augmentation_sum D B x)

#print axioms bandMVSquareInclusion_coordinates
#print axioms bandMVMiddleInclusion_coordinates
end CurveComplex.CapBandGeometry
