import CurveComplexGenusTwo.Topology.CapBandGeometry.OverlapBandHomology
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseStatements

noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.CapBandGeometry

def subsetPreimageChart {S : Type} [TopologicalSpace S] (N A : Set S) (hA : A ⊆ N) :
    ↥((Subtype.val : N → S) ⁻¹' A) ≃ₜ A where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, hA x.2⟩, x.2⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)

abbrev bandTopCat := TopCat.of (bandUnion D B)
def bandMVU : Set (bandTopCat D B) := (Subtype.val : bandUnion D B → S) ⁻¹' squareCollars D B
def bandMVV : Set (bandTopCat D B) := (Subtype.val : bandUnion D B → S) ⁻¹' middleBands B

theorem bandMVU_open : IsOpen (bandMVU D B) := squareCollars_relative_open D B
theorem bandMVV_open : IsOpen (bandMVV D B) := middleBands_relative_open D B

theorem bandMV_cover : bandMVU D B ∪ bandMVV D B = Set.univ := by
  ext x
  simp only [bandMVU, bandMVV, Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true]
  have hx := x.2
  exact (Set.ext_iff.mp (squareCollars_middleBands_cover D B) (x : S)).mpr hx

def bandMVUChart : bandMVU D B ≃ₜ squareCollars D B :=
  subsetPreimageChart _ _ (fun _ hx => (squareCollars_middleBands_cover D B) ▸ Or.inl hx)
def bandMVVChart : bandMVV D B ≃ₜ middleBands B :=
  subsetPreimageChart _ _ (fun _ hx => (squareCollars_middleBands_cover D B) ▸ Or.inr hx)
def bandMVOverlapChart : ↥(bandMVU D B ∩ bandMVV D B) ≃ₜ
    ↥(squareCollars D B ∩ middleBands B) :=
  subsetPreimageChart (bandUnion D B) (squareCollars D B ∩ middleBands B)
    (fun _ hx => (squareCollars_middleBands_cover D B) ▸ Or.inl hx.1)

theorem bandMVU_contractible : ContractibleSpace (bandMVU D B) := by
  letI := squareCollars_contractible D B
  exact (bandMVUChart D B).contractibleSpace

def bandMVVHomotopyFinTwo : ContinuousMap.HomotopyEquiv (bandMVV D B) (Fin 2) :=
  (bandMVVChart D B).toHomotopyEquiv.trans (middleBandHomotopyFinTwo B)
def bandMVOverlapHomotopyFinFour :
    ContinuousMap.HomotopyEquiv ↥(bandMVU D B ∩ bandMVV D B) (Fin 4) :=
  (bandMVOverlapChart D B).toHomotopyEquiv.trans (overlapBandHomotopyFinFour D B)

def bandMVOverlapHZeroCoordinates :
    H ↥(bandMVU D B ∩ bandMVV D B) 0 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  ((homotopyHomologyIso (bandMVOverlapHomotopyFinFour D B) 0) ≪≫
    CurveComplex.Octagon.AttachingMap.GraphMV.finiteDiscreteH0Iso (Fin 4)).toLinearEquiv

def bandMVVHZeroCoordinates : H (bandMVV D B) 0 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((homotopyHomologyIso (bandMVVHomotopyFinTwo D B) 0) ≪≫
    CurveComplex.Octagon.AttachingMap.GraphMV.finiteDiscreteH0Iso (Fin 2)).toLinearEquiv

def bandMVUHZeroCoordinates : H (bandMVU D B) 0 ≃ₗ[ℤ] ℤ := by
  letI := bandMVU_contractible D B
  exact (asIso ((TopCat.of (bandMVU D B)).singularHomology₀ε
    (ModuleCat.of ℤ ℤ))).toLinearEquiv

theorem bandMV_pair_positive_zero (n : ℕ) (hn : 0 < n) :
    IsZero (ModuleCat.of ℤ (H (bandMVU D B) n × H (bandMVV D B) n)) := by
  letI := bandMVU_contractible D B
  have hu := contractible_positive_homology (bandMVU D B) n hn
  have hv : IsZero (H (bandMVV D B) n) :=
    (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of (Fin 2)) (by omega)).of_iso
        (homotopyHomologyIso (bandMVVHomotopyFinTwo D B) n)
  letI := ModuleCat.subsingleton_of_isZero hu
  letI := ModuleCat.subsingleton_of_isZero hv
  exact ModuleCat.isZero_of_subsingleton _

#print axioms bandMVOverlapHZeroCoordinates
#print axioms bandMVUHZeroCoordinates
#print axioms bandMV_pair_positive_zero
end CurveComplex.CapBandGeometry
