import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14BigonBoundary
import Mathlib.Topology.Separation.Regular

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- An actual full-preimage empty bigon has an open operation support whose
closed support is disjoint from its actual deck translate. No support or
equivariance certificate is supplied. -/
theorem innermost_full_preimage_deck_separated_support
    (M : HyperellipticModel E S) (a b : EssentialCurve E)
    (ht : Transverse a.val b.val) (B : LocalSurgery.TwoCurveDisk a.val b.val)
    (c d : PuncturedCircle M)
    (ha : a.val.image = M.cover.projection ⁻¹' c.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.image)
    (htbase : Transverse c.curve d.curve)
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
    ∃ V : Set E, IsOpen V ∧ range B.disk ⊆ V ∧
      Disjoint (closure V) (M.cover.deck '' closure V) ∧
      Disjoint (closure V) (M.cover.projection ⁻¹' (M.cover.branch : Set S)) := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have hA : IsClosed (range B.disk) := (isCompact_range B.disk.continuous).isClosed
  have hDA : IsClosed (M.cover.deck '' range B.disk) :=
    M.cover.deck.isClosedMap _ hA
  have hsep := M.innermost_full_preimage_disk_disjoint_deck a b ht B c d ha hb htbase hempty
  obtain ⟨U,W,hU,hW,hAU,hDAW,hUW⟩ := normal_separation hA hDA hsep
  let O := U ∩ M.cover.deck ⁻¹' W
  have hO : IsOpen O := hU.inter (hW.preimage M.cover.deck.continuous)
  have hAO : range B.disk ⊆ O := by
    intro x hx
    exact ⟨hAU hx,hDAW ⟨x,hx,rfl⟩⟩
  obtain ⟨V,hV,hAV,hclV⟩ := normal_exists_closure_subset hA hO hAO
  have hclsep : Disjoint (closure V) (M.cover.deck '' closure V) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨y,hy,rfl⟩
    exact Set.disjoint_left.mp hUW (hclV hx).1 (hclV hy).2
  refine ⟨V,hV,hAV,hclsep,?_⟩
  apply Set.disjoint_left.mpr
  intro x hx hxR
  have hfixed : M.cover.deck x = x := (M.cover.fixed_iff_branch x).mpr hxR
  exact Set.disjoint_left.mp hclsep hx ⟨x,hx,hfixed⟩
end CurveComplex.HyperellipticModel
