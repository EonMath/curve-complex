import CurveComplexGenusTwo.Topology.ThetaRetention.ActualNonseparatingEssential

open CurveComplex Set Topology

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

/-- A connected piece attaches to a connected graph even if it only reaches
the graph at a limit point. This is the topology of a cut-core side meeting
the original arc-and-boundary graph. -/
private theorem connected_union_of_closure_meets
    {S : Type} [TopologicalSpace S] (F W : Set S)
    (hF : IsConnected F) (hW : IsConnected W)
    (hmeets : (closure W ∩ F).Nonempty) :
    IsConnected (F ∪ W) := by
  obtain ⟨p, hpcl, hpF⟩ := hmeets
  have hWp : IsConnected (W ∪ {p}) := by
    apply hW.subset_closure
    · exact Set.subset_union_left
    · exact Set.union_subset (subset_closure) (by
        rintro x hx
        simpa only [Set.mem_singleton_iff.mp hx] using hpcl)
  have hcommon : (F ∩ (W ∪ {p})).Nonempty :=
    ⟨p, hpF, Or.inr (Set.mem_singleton p)⟩
  have h := hF.union hcommon hWp
  have heq : F ∪ (W ∪ {p}) = F ∪ W := by
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro (hf | hw | rfl)
      · exact Or.inl hf
      · exact Or.inr hw
      · exact Or.inl hpF
    · rintro (hf | hw)
      · exact Or.inl hf
      · exact Or.inr (Or.inl hw)
  rwa [heq] at h

/-- If every connected piece of a curve complement reaches the connected
forbidden graph, the whole complement is connected. -/
theorem connected_complement_of_forbidden_graph_attachments
    {S : Type} [TopologicalSpace S]
    (F : Set S) {ι : Type} (W : ι → Set S)
    (hF : IsConnected F)
    (hW : ∀ i, IsConnected (W i))
    (hmeets : ∀ i, (closure (W i) ∩ F).Nonempty) :
    IsConnected (F ∪ ⋃ i, W i) := by
  let A : Option ι → Set S
    | none => F
    | some i => F ∪ W i
  have hA : ∀ i, IsConnected (A i) := by
    intro i
    cases i with
    | none => exact hF
    | some i => exact connected_union_of_closure_meets F (W i) hF (hW i) (hmeets i)
  have hcommon : (⋂ i, A i).Nonempty := by
    obtain ⟨x, hx⟩ := hF.1
    refine ⟨x, ?_⟩
    rw [Set.mem_iInter]
    intro i
    cases i with
    | none => exact hx
    | some i => exact Or.inl hx
  have hconn : IsConnected (⋃ i, A i) := by
    refine ⟨?_, isPreconnected_iUnion hcommon (fun i => (hA i).isPreconnected)⟩
    exact ⟨hF.1.some, Set.mem_iUnion.mpr ⟨none, hF.1.some_mem⟩⟩
  have heq : F ∪ (⋃ i, W i) = ⋃ i, A i := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (hx | ⟨i, hi⟩)
      · exact ⟨none, hx⟩
      · exact ⟨some i, Or.inr hi⟩
    · rintro ⟨i, hi⟩
      cases i with
      | none => exact Or.inl hi
      | some i =>
          rcases hi with hF' | hW'
          · exact Or.inl hF'
          · exact Or.inr ⟨i, hW'⟩
  rw [heq]
  exact hconn

/-- A circle selected from a cut core is essential in the original capped
surface once every complementary side attaches to the forbidden graph. -/
theorem essential_of_forbidden_graph_attachments
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (c : Curve S) (F : Set S) {ι : Type} (W : ι → Set S)
    (hF : IsConnected F)
    (hW : ∀ i, IsConnected (W i))
    (hmeets : ∀ i, (closure (W i) ∩ F).Nonempty)
    (hcover : c.imageᶜ = F ∪ ⋃ i, W i) :
    Essential c := by
  apply source_nonseparating_curve_essential S c
  change IsConnected c.imageᶜ
  rw [hcover]
  exact connected_complement_of_forbidden_graph_attachments F W hF hW hmeets

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
