import CurveComplexGenusTwo.Topology.CapBandGeometry.MiddleBandHomology

noncomputable section
open Set Topology unitInterval CategoryTheory CategoryTheory.Limits CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.CapBandGeometry

abbrev LowBandInterval := Ioo (1/4 : ℝ) (1/3)
abbrev HighBandInterval := Ioo (2/3 : ℝ) (3/4)
def overlapParameters : Set ℝ := LowBandInterval ∪ HighBandInterval

private def highToLow : HighBandInterval ≃ₜ LowBandInterval where
  toFun x := ⟨x.1 - 5/12, by constructor <;> linarith [x.2.1, x.2.2]⟩
  invFun x := ⟨x.1 + 5/12, by constructor <;> linarith [x.2.1, x.2.2]⟩
  left_inv x := by apply Subtype.ext; dsimp; ring
  right_inv x := by apply Subtype.ext; dsimp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def overlapIntervalChart : overlapParameters ≃ₜ (Fin 2 × LowBandInterval) := by
  let F : LowBandInterval → ℝ := Subtype.val
  let G : HighBandInterval → ℝ := Subtype.val
  have hF : IsEmbedding F := IsEmbedding.subtypeVal
  have hG : IsEmbedding G := IsEmbedding.subtypeVal
  have hFr : Set.range F = LowBandInterval := Subtype.range_coe
  have hGr : Set.range G = HighBandInterval := Subtype.range_coe
  have hlh : Disjoint (closure (Set.range F)) (Set.range G) := by
    rw [hFr, hGr, show closure LowBandInterval = Icc (1/4 : ℝ) (1/3) from
      closure_Ioo (by norm_num)]
    apply Set.disjoint_left.mpr
    intro x hx hy
    linarith [hx.2, hy.1]
  have hhl : Disjoint (Set.range F) (closure (Set.range G)) := by
    rw [hFr, hGr, show closure HighBandInterval = Icc (2/3 : ℝ) (3/4) from
      closure_Ioo (by norm_num)]
    apply Set.disjoint_left.mpr
    intro x hx hy
    linarith [hx.2, hy.1]
  have hemb := hF.sumElim hG hlh hhl
  have hr : Set.range (Sum.elim F G) = overlapParameters := by
    rw [Sum.elim_range, hFr, hGr]
    rfl
  exact (hemb.toHomeomorph.trans (Homeomorph.setCongr hr)).symm.trans
    ((Homeomorph.sumCongr (Homeomorph.refl _) highToLow).trans (sumTwoChart _))

theorem overlapBands_eq_parameters
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    squareCollars D B ∩ middleBands B =
      bandSlice B.first overlapParameters ∪ bandSlice B.second overlapParameters := by
  rw [squareCollars_middleBands_intersection D B]
  have hunion (F : I × BandWidth → S) (J K : Set ℝ) :
      bandSlice F (J ∪ K) = bandSlice F J ∪ bandSlice F K := by
    change F '' ((fun p : I × BandWidth => (p.1 : ℝ)) ⁻¹' (J ∪ K)) = _
    rw [Set.preimage_union, Set.image_union]
    rfl
  rw [overlapParameters, hunion, hunion]
  ext x
  simp only [LowBandInterval, HighBandInterval, Set.mem_union]
  tauto

/-- Actual four overlap rectangles, with index order first-low, first-high,
second-low, second-high. -/
def overlapBandRectangleChart
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    ↥(squareCollars D B ∩ middleBands B) ≃ₜ
      (Fin 4 × (LowBandInterval × BandWidth)) := by
  have hJ : overlapParameters ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    rcases ht with ht | ht <;> constructor <;> linarith [ht.1, ht.2]
  let e := (Homeomorph.setCongr (overlapBands_eq_parameters D B)).trans
    (twoBandWindowChart B overlapParameters hJ)
  let e2 := (overlapIntervalChart.prodCongr (Homeomorph.refl BandWidth)).trans
    (Homeomorph.prodAssoc (Fin 2) LowBandInterval BandWidth)
  let e3 := (Homeomorph.prodAssoc (Fin 2) (Fin 2) (LowBandInterval × BandWidth)).symm
  exact e.trans (((Homeomorph.refl (Fin 2)).prodCongr e2).trans
    (e3.trans (finProdFinEquiv.toHomeomorphOfDiscrete.prodCongr (Homeomorph.refl _))))

def overlapBandHomotopyFinFour
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    ContinuousMap.HomotopyEquiv ↥(squareCollars D B ∩ middleBands B) (Fin 4) := by
  letI : ContractibleSpace LowBandInterval :=
    (convex_Ioo _ _).contractibleSpace ⟨7/24, by norm_num⟩
  letI : ContractibleSpace BandWidth :=
    (convex_Icc (-1 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  exact (overlapBandRectangleChart D B).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl (Fin 4)).prodCongr
      (ContractibleSpace.hequiv_unit (LowBandInterval × BandWidth)).some).trans
        (Homeomorph.prodUnique (Fin 4) Unit).toHomotopyEquiv)

def overlapBandHZeroCoordinates
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    H ↥(squareCollars D B ∩ middleBands B) 0 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  ((homotopyHomologyIso (overlapBandHomotopyFinFour D B) 0) ≪≫
    CurveComplex.Octagon.AttachingMap.GraphMV.finiteDiscreteH0Iso (Fin 4)).toLinearEquiv

theorem overlapBand_positive_homology
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (n : ℕ) (hn : 0 < n) : IsZero (H ↥(squareCollars D B ∩ middleBands B) n) := by
  exact (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of (Fin 4)) (by omega)).of_iso
      (homotopyHomologyIso (overlapBandHomotopyFinFour D B) n)

#print axioms overlapBandRectangleChart
#print axioms overlapBandHZeroCoordinates
#print axioms overlapBand_positive_homology
end CurveComplex.CapBandGeometry
