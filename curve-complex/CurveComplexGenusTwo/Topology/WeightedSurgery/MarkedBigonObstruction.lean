import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualFiniteTransverseNewArc
import Mathlib.Topology.Connected.Basic

namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A marked arc entering a region whose interior contains no marks must meet
its frontier. The frontier contact is produced from connectedness, rather
than supplied as replacement data. -/
theorem actual_marked_arc_entering_region_hits_frontier
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M) (K : Set S)
    (hmarks : Disjoint (interior K) (M.cover.branch : Set S))
    (hin : (a.val.image ∩ interior K).Nonempty) :
    (a.val.image ∩ frontier K).Nonempty := by
  classical
  by_contra hnot
  have haway : Disjoint a.val.image (frontier K) :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hnot)
  have hconnected : IsPreconnected a.val.image := by
    exact isPreconnected_range a.val.continuous
  have hcover : a.val.image ⊆ interior K ∪ (closure K)ᶜ := by
    intro x hx
    by_cases hi : x ∈ interior K
    · exact Or.inl hi
    · right
      intro hc
      exact disjoint_left.mp haway hx ⟨hc, hi⟩
  have hfull : a.val.image ⊆ interior K :=
    hconnected.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left (interior_subset.trans subset_closure)) hcover hin
  exact disjoint_left.mp hmarks (hfull ⟨0, rfl⟩) a.val.start_marked

/-- Any other old arc entering an actual marked-free bigon must cross its new
side. The old side cannot account for that frontier contact, because the
old system is interior-disjoint. -/
theorem actual_relative_bigon_obstruction_on_new_side
    (M : HyperellipticModel E S) {ι : Type} (old : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
    (a : EssentialMarkedArc M) (i j : ι) (hji : j ≠ i)
    (K : Set S) (firstSide newSide : Set S)
    (hfrontier : frontier K = firstSide ∪ newSide)
    (hfirst : firstSide ⊆ (old i).val.image)
    (hnew : newSide ⊆ a.val.image)
    (hmarks : Disjoint K (M.cover.branch : Set S))
    (hclosed : IsClosed K)
    (hin : ((old j).val.image ∩ interior K).Nonempty) :
    ∃ p ∈ newSide, p ∈ ArcSurgery.crossings M (old j) a := by
  have himarks : Disjoint (interior K) (M.cover.branch : Set S) :=
    hmarks.mono_left interior_subset
  obtain ⟨p,hpold,hpfront⟩ := actual_marked_arc_entering_region_hits_frontier
    M (old j) K himarks hin
  have hpK : p ∈ K := by
    exact hclosed.closure_eq ▸ frontier_subset_closure hpfront
  have hpunmarked : p ∉ (M.cover.branch : Set S) := fun hp =>
    disjoint_left.mp hmarks hpK hp
  have hpj : p ∈ arcInterior M (old j) := ⟨hpold,hpunmarked⟩
  rw [hfrontier] at hpfront
  rcases hpfront with hpfirst | hpnew
  · exact False.elim (disjoint_left.mp (hd j i hji) hpj ⟨hfirst hpfirst,hpunmarked⟩)
  · exact ⟨p,hpnew,hpj,hnew hpnew,hpunmarked⟩

end CurveComplex.HyperellipticModel
