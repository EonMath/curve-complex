import CurveComplexGenusTwo.Topology.ThetaRetention.ActualThetaComponents
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualCurveDensity
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualArcNonseparation
import CurveComplexGenusTwo.Topology.ThetaRetention.DenseTwoComponents
import CurveComplexGenusTwo.Topology.ThetaRetention.ThetaGeometry

namespace CurveComplex
open Set Topology Schoenflies

/-- Candidate for independent statement review. For the actual theta graph
formed by a first-return arc and the two complementary arcs of a nonseparating
current curve on the source genus-two surface, one produced raw boundary has
connected complement. No retention or connectivity conclusion is a premise. -/
theorem source_closed_surface_theta_nonseparating_retention
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (hns : Nonseparating b) :
    ∃ i : Bool, Nonseparating (B.boundary i) := by
  let : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace Plane S
  let p : Path (D.first 0) (D.first 1) := ⟨D.first,rfl,rfl⟩
  have hY : IsConnected (Set.range D.first)ᶜ := source_embedded_path_complement_connected p D.first_embedded
  obtain ⟨l,hl,r,hr,hcov⟩ := source_theta_complement_at_most_two S D hns
  let W := b.imageᶜ \ Set.range D.first
  let L := connectedComponentIn W l
  let R := connectedComponentIn W r
  have hL : IsConnected L := isConnected_connectedComponentIn_iff.mpr hl
  have hR : IsConnected R := isConnected_connectedComponentIn_iff.mpr hr
  have hW : W = L ∪ R := by
    apply Subset.antisymm
    · exact fun x hx => hcov x hx
    · exact union_subset (connectedComponentIn_subset W l) (connectedComponentIn_subset W r)
  have hYopen : IsOpen (Set.range D.first)ᶜ := (isCompact_range D.first.continuous).isClosed.isOpen_compl
  have hWdense : (Set.range D.first)ᶜ ⊆ closure W := by
    have hbDense := source_curve_complement_dense b
    intro x hx
    have hh := hYopen.inter_closure ⟨hx,hbDense x⟩
    have heq : (Set.range D.first)ᶜ ∩ b.imageᶜ = W := by
      ext z
      simp only [W,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_sdiff]
      exact and_comm
    rwa [heq] at hh
  have hUopen : IsOpen (B.boundary false).imageᶜ :=
    (isCompact_range (B.boundary false).embedded.continuous).isClosed.isOpen_compl
  have hVopen : IsOpen (B.boundary true).imageᶜ :=
    (isCompact_range (B.boundary true).embedded.continuous).isClosed.isOpen_compl
  have hWboth : W ⊆ (B.boundary false).imageᶜ ∩ (B.boundary true).imageᶜ := by
    rw [theta_complement_inter D B]
  have hLW : L ⊆ W := connectedComponentIn_subset W l
  have hRW : R ⊆ W := connectedComponentIn_subset W r
  have hDense : (Set.range D.first)ᶜ ⊆ closure (L ∪ R) := by rw [← hW]; exact hWdense
  rcases theta_open_cover_connected_member hY hUopen hVopen (theta_complement_union D B)
    hL hR (fun x hx => (hWboth (hLW hx)).1) (fun x hx => (hWboth (hLW hx)).2)
    (fun x hx => (hWboth (hRW hx)).1) (fun x hx => (hWboth (hRW hx)).2) hDense with h | h
  · exact ⟨false,h⟩
  · exact ⟨true,h⟩


end CurveComplex
