import CurveComplexGenusTwo.Topology.CapBandGeometry.BandMVActual
import CurveComplexGenusTwo.Topology.CapBandGeometry.FiniteHZeroCoordinates

noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.CapBandGeometry
variable {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)

def bandMVOverlapPoint (i : Fin 4) : ↥(bandMVU D B ∩ bandMVV D B) :=
  (bandMVOverlapChart D B).symm ((overlapBandRectangleChart D B).symm
    (i, (⟨7/24, by norm_num⟩, ⟨0, by norm_num⟩)))

theorem bandMVOverlapPoint_index (i : Fin 4) :
    (bandMVOverlapHomotopyFinFour D B).toFun (bandMVOverlapPoint D B i) = i := by
  simp only [bandMVOverlapHomotopyFinFour, ContinuousMap.HomotopyEquiv.trans,
    Homeomorph.toHomotopyEquiv, ContinuousMap.comp_apply, bandMVOverlapPoint,
    Homeomorph.apply_symm_apply]
  change ((overlapBandHomotopyFinFour D B).toFun
    ((overlapBandRectangleChart D B).symm (i, (⟨7/24, by norm_num⟩, ⟨0, by norm_num⟩)))) = i
  simp [overlapBandHomotopyFinFour, ContinuousMap.HomotopyEquiv.prodCongr]

theorem bandMVOverlapPoint_middle_index (i : Fin 4) :
    (bandMVVHomotopyFinTwo D B).toFun
      ⟨(bandMVOverlapPoint D B i).1, (bandMVOverlapPoint D B i).2.2⟩ =
      ⟨i.val / 2, by omega⟩ := by
  let t : (Ioo (1/4 : ℝ) (3/4)) :=
    if i.val % 2 = 0 then ⟨7/24, by norm_num⟩ else ⟨17/24, by norm_num⟩
  let j : Fin 2 := ⟨i.val / 2, by omega⟩
  let q : bandMVV D B := (bandMVVChart D B).symm
    ((middleBandRectangleChart B).symm (j, (t, ⟨0, by norm_num⟩)))
  have heq : (⟨(bandMVOverlapPoint D B i).1, (bandMVOverlapPoint D B i).2.2⟩ :
      bandMVV D B) = q := by
    apply Subtype.ext
    apply Subtype.ext
    fin_cases i
    · rfl
    · change B.first (⟨7/24 + 5/12, _⟩, ⟨0, _⟩) = B.first (⟨17/24, _⟩, ⟨0, _⟩)
      congr 1
      apply Prod.ext
      · apply Subtype.ext; norm_num
      · rfl
    · rfl
    · change B.second (⟨7/24 + 5/12, _⟩, ⟨0, _⟩) = B.second (⟨17/24, _⟩, ⟨0, _⟩)
      congr 1
      apply Prod.ext
      · apply Subtype.ext; norm_num
      · rfl
  rw [heq]
  simp [q, bandMVVHomotopyFinTwo, middleBandHomotopyFinTwo,
    ContinuousMap.HomotopyEquiv.prodCongr]
  rfl

theorem bandMVOverlapHZeroCoordinates_point (i : Fin 4) :
    bandMVOverlapHZeroCoordinates D B
      (pointClass (TopCat.toSSet.obj (TopCat.of ↥(bandMVU D B ∩ bandMVV D B)))
        (TopCat.toSSetObj₀Equiv.symm (bandMVOverlapPoint D B i)) (1 : ℤ)) =
      Pi.single i (1 : ℤ) := by
  change finiteHomotopyHZeroCoordinates (bandMVOverlapHomotopyFinFour D B) _ = _
  rw [finiteHomotopyHZeroCoordinates_point, bandMVOverlapPoint_index]

#print axioms bandMVOverlapPoint_middle_index
#print axioms bandMVOverlapHZeroCoordinates_point
end CurveComplex.CapBandGeometry
