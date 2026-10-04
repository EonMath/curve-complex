import CurveComplexGenusTwo.Topology.CapBandGeometry.CapBandPacket
import CurveComplexGenusTwo.Octagon.GraphMV.DiscreteHZero
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers

noncomputable section
open Set Topology unitInterval CategoryTheory CategoryTheory.Limits CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.CapBandGeometry

abbrev MiddleRectangle := Ioo (1/4 : ℝ) (3/4) × BandWidth

private def twoPointIndex : (PUnit.{1} ⊕ PUnit.{1}) ≃ Fin 2 where
  toFun := Sum.elim (fun _ => 0) (fun _ => 1)
  invFun i := if i = 0 then Sum.inl PUnit.unit else Sum.inr PUnit.unit
  left_inv p := by cases p <;> simp
  right_inv i := by fin_cases i <;> simp

def sumTwoChart (X : Type) [TopologicalSpace X] : (X ⊕ X) ≃ₜ
    (Fin 2 × X) :=
  ((Homeomorph.sumCongr (Homeomorph.uniqueProd PUnit.{1} X).symm
    (Homeomorph.uniqueProd PUnit.{1} X).symm).trans
      Homeomorph.sumProdDistrib.symm).trans
        (twoPointIndex.toHomeomorphOfDiscrete.prodCongr (Homeomorph.refl _))

/-- The actual middle-band cover set is two literal contractible rectangles. -/
def twoBandWindowChart
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D)
    (J : Set ℝ) (hJ : J ⊆ Icc (0 : ℝ) 1) :
    ↥(bandSlice B.first J ∪ bandSlice B.second J) ≃ₜ (Fin 2 × (J × BandWidth)) := by
  let e1 := bandSliceHomeomorph B.first B.first_embedded _ hJ
  let e2 := bandSliceHomeomorph B.second B.second_embedded _ hJ
  let F : (J × BandWidth) → S := Subtype.val ∘ e1
  let G : (J × BandWidth) → S := Subtype.val ∘ e2
  have hF : IsEmbedding F := IsEmbedding.subtypeVal.comp e1.isEmbedding
  have hG : IsEmbedding G := IsEmbedding.subtypeVal.comp e2.isEmbedding
  have hFrange : Set.range F = bandSlice B.first J := by
    rw [show F = Subtype.val ∘ e1 from rfl, Set.range_comp, e1.surjective.range_eq,
      Set.image_univ, Subtype.range_coe]
  have hGrange : Set.range G = bandSlice B.second J := by
    rw [show G = Subtype.val ∘ e2 from rfl, Set.range_comp, e2.surjective.range_eq,
      Set.image_univ, Subtype.range_coe]
  have hFsub : Set.range F ⊆ Set.range B.first := hFrange ▸ Set.image_subset_range _ _
  have hGsub : Set.range G ⊆ Set.range B.second := hGrange ▸ Set.image_subset_range _ _
  have hFc : closure (Set.range F) ⊆ Set.range B.first :=
    closure_minimal hFsub (isCompact_range B.first_embedded.continuous).isClosed
  have hGc : closure (Set.range G) ⊆ Set.range B.second :=
    closure_minimal hGsub (isCompact_range B.second_embedded.continuous).isClosed
  have hemb := hF.sumElim hG (B.bands_disjoint.mono hFc hGsub)
    (B.bands_disjoint.mono hFsub hGc)
  have hrange : Set.range (Sum.elim F G) = bandSlice B.first J ∪ bandSlice B.second J := by
    rw [Sum.elim_range, hFrange, hGrange]
  exact (hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)).symm.trans (sumTwoChart _)

theorem twoBandWindowChart_symm_first
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D)
    (J : Set ℝ) (hJ : J ⊆ Icc (0 : ℝ) 1) (p : J × BandWidth) :
    ((twoBandWindowChart B J hJ).symm (0, p) : S) =
      B.first (⟨p.1, hJ p.1.2⟩, p.2) := by
  rfl

theorem twoBandWindowChart_symm_second
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D)
    (J : Set ℝ) (hJ : J ⊆ Icc (0 : ℝ) 1) (p : J × BandWidth) :
    ((twoBandWindowChart B J hJ).symm (1, p) : S) =
      B.second (⟨p.1, hJ p.1.2⟩, p.2) := by
  rfl

def middleBandRectangleChart
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D) :
    middleBands B ≃ₜ (Fin 2 × MiddleRectangle) :=
  twoBandWindowChart B _ (fun _ ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)

/-- This homotopy equivalence is derived from the actual two band embeddings. -/
def middleBandHomotopyFinTwo
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D) :
    ContinuousMap.HomotopyEquiv (middleBands B) (Fin 2) := by
  letI : ContractibleSpace (Ioo (1/4 : ℝ) (3/4)) :=
    (convex_Ioo _ _).contractibleSpace ⟨1/2, by norm_num⟩
  letI : ContractibleSpace BandWidth :=
    (convex_Icc (-1 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  exact (middleBandRectangleChart B).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl (Fin 2)).prodCongr
      (ContractibleSpace.hequiv_unit MiddleRectangle).some).trans
        (Homeomorph.prodUnique (Fin 2) Unit).toHomotopyEquiv)

/-- Actual H0 coordinates of the two middle rectangles. -/
def middleBandHZeroCoordinates
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D) :
    H (middleBands B) 0 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((homotopyHomologyIso (middleBandHomotopyFinTwo B) 0) ≪≫
    CurveComplex.Octagon.AttachingMap.GraphMV.finiteDiscreteH0Iso (Fin 2)).toLinearEquiv

theorem middleBand_positive_homology
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D)
    (n : ℕ) (hn : 0 < n) : IsZero (H (middleBands B) n) := by
  exact (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of (Fin 2)) (by omega)).of_iso
      (homotopyHomologyIso (middleBandHomotopyFinTwo B) n)

#print axioms middleBandHZeroCoordinates
#print axioms middleBand_positive_homology
#print axioms middleBandRectangleChart
#print axioms middleBandHomotopyFinTwo
end CurveComplex.CapBandGeometry
