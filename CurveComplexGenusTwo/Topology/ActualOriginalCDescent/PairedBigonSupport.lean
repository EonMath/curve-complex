import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14DeckSeparatedBigonSupport
import Mathlib.Topology.Separation.Regular

namespace CurveComplex.HyperellipticModel
open Set Topology

theorem paired_disk_has_deck_separated_support
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S)
    {a b : Curve E} (D : LocalSurgery.TwoCurveDisk a b)
    (hdis : Disjoint (range D.disk) (M.cover.deck '' range D.disk)) :
    ∃ V : Set E, IsOpen V ∧ range D.disk ⊆ V ∧
      Disjoint (closure V) (M.cover.deck '' closure V) ∧
      Disjoint (closure V)
        (M.cover.projection ⁻¹' (M.cover.branch : Set S)) := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have hA : IsClosed (range D.disk) := (isCompact_range D.disk.continuous).isClosed
  have hDA : IsClosed (M.cover.deck '' range D.disk) :=
    M.cover.deck.isClosedMap _ hA
  obtain ⟨U, W, hU, hW, hAU, hDAW, hUW⟩ :=
    normal_separation hA hDA hdis
  let O := U ∩ M.cover.deck ⁻¹' W
  have hO : IsOpen O := hU.inter (hW.preimage M.cover.deck.continuous)
  have hAO : range D.disk ⊆ O := by
    intro x hx
    exact ⟨hAU hx, hDAW ⟨x, hx, rfl⟩⟩
  obtain ⟨V, hV, hAV, hclV⟩ := normal_exists_closure_subset hA hO hAO
  have hclsep : Disjoint (closure V) (M.cover.deck '' closure V) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨y, hy, rfl⟩
    exact Set.disjoint_left.mp hUW (hclV hx).1 (hclV hy).2
  refine ⟨V, hV, hAV, hclsep, ?_⟩
  apply Set.disjoint_left.mpr
  intro x hx hxR
  have hfixed : M.cover.deck x = x := (M.cover.fixed_iff_branch x).mpr hxR
  exact Set.disjoint_left.mp hclsep hx ⟨x, hx, hfixed⟩

theorem paired_disk_has_deck_separated_support_avoiding
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S)
    {a b : Curve E} (D : LocalSurgery.TwoCurveDisk a b)
    (hdis : Disjoint (range D.disk) (M.cover.deck '' range D.disk))
    (F : Set E) (hF : IsClosed F)
    (hDF : Disjoint (range D.disk) F) :
    ∃ V : Set E, IsOpen V ∧ range D.disk ⊆ V ∧
      Disjoint (closure V) (M.cover.deck '' closure V) ∧
      Disjoint (closure V) (M.cover.projection ⁻¹' (M.cover.branch : Set S)) ∧
      Disjoint (closure V) F := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  obtain ⟨V0, hV0, hDV0, hsep0, hbranch0⟩ :=
    paired_disk_has_deck_separated_support M D hdis
  let O := V0 ∩ Fᶜ
  have hO : IsOpen O := hV0.inter hF.isOpen_compl
  have hDO : range D.disk ⊆ O := by
    intro x hx
    exact ⟨hDV0 hx, Set.disjoint_left.mp hDF hx⟩
  have hDclosed : IsClosed (range D.disk) :=
    (isCompact_range D.disk.continuous).isClosed
  obtain ⟨V, hV, hDV, hclV⟩ := normal_exists_closure_subset hDclosed hO hDO
  refine ⟨V, hV, hDV, ?_, ?_, ?_⟩
  · apply hsep0.mono
    · exact (hclV.trans Set.inter_subset_left).trans subset_closure
    · exact Set.image_mono ((hclV.trans Set.inter_subset_left).trans subset_closure)
  · exact hbranch0.mono_left
      ((hclV.trans Set.inter_subset_left).trans subset_closure)
  · apply Set.disjoint_left.mpr
    intro x hx hxF
    exact (hclV hx).2 hxF

end CurveComplex.HyperellipticModel
