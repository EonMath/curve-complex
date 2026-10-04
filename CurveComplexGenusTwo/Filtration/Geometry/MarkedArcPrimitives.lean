import CurveComplexGenusTwo.Dictionary.MarkedSphere

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

noncomputable local instance integrationLocalInstance_MarkedArcPrimitives_1 : DecidableEq S := Classical.decEq _

/-- Both ends, allowing their coincidence for a loop. -/
noncomputable def markedArcEndset {M : HyperellipticModel E S} (a : MarkedArc M) :
    Finset S := by
  classical
  exact {a.map ⟨0, by norm_num⟩, a.map ⟨1, by norm_num⟩}

theorem markedArcEndset_subset_branch {M : HyperellipticModel E S} (a : MarkedArc M) :
    markedArcEndset a ⊆ M.cover.branch := by
  classical
  intro x hx
  simp only [markedArcEndset, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact a.start_marked
  · exact a.end_marked

theorem markedArc_image_inter_branch {M : HyperellipticModel E S} (a : MarkedArc M) :
    a.image ∩ (M.cover.branch : Set S) = (markedArcEndset a : Set S) := by
  classical
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, ht⟩
    rcases a.marked_only_at_ends t ht with h | h
    · subst t
      simp [markedArcEndset]
    · subst t
      simp [markedArcEndset]
  · intro hx
    change x ∈ markedArcEndset a at hx
    simp only [markedArcEndset, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨⟨⟨0, by norm_num⟩, rfl⟩, a.start_marked⟩
    · exact ⟨⟨⟨1, by norm_num⟩, rfl⟩, a.end_marked⟩

theorem markedArc_image_connected {M : HyperellipticModel E S} (a : MarkedArc M) :
    IsConnected a.image := isConnected_range a.continuous

theorem markedArc_image_compact {M : HyperellipticModel E S} (a : MarkedArc M) :
    IsCompact a.image := isCompact_range a.continuous

theorem markedArc_disjoint_interiors_inter_image {M : HyperellipticModel E S}
    (a b : MarkedArc M)
    (hd : Disjoint (a.image \ (M.cover.branch : Set S))
      (b.image \ (M.cover.branch : Set S))) :
    a.image ∩ b.image = ((markedArcEndset a : Set S) ∩ (markedArcEndset b : Set S)) := by
  classical
  ext x
  constructor
  · rintro ⟨ha, hb⟩
    have hx : x ∈ (M.cover.branch : Set S) := by
      by_contra hn
      exact Set.disjoint_left.mp hd ⟨ha, hn⟩ ⟨hb, hn⟩
    exact ⟨(markedArc_image_inter_branch a ▸ ⟨ha, hx⟩),
      (markedArc_image_inter_branch b ▸ ⟨hb, hx⟩)⟩
  · rintro ⟨ha, hb⟩
    have ha' : x ∈ a.image ∩ (M.cover.branch : Set S) := by
      rw [markedArc_image_inter_branch]
      exact ha
    have hb' : x ∈ b.image ∩ (M.cover.branch : Set S) := by
      rw [markedArc_image_inter_branch]
      exact hb
    exact ⟨ha'.1, hb'.1⟩

/-- The actual marked vertices of a finite representative family. -/
noncomputable def markedFamilyVertices {M : HyperellipticModel E S}
    {ι : Type*} [Fintype ι] (r : ι → MarkedArc M) : Finset S := by
  classical
  exact Finset.univ.biUnion (fun i => markedArcEndset (r i))

theorem markedFamilyVertices_subset_branch {M : HyperellipticModel E S}
    {ι : Type*} [Fintype ι] (r : ι → MarkedArc M) :
    markedFamilyVertices r ⊆ M.cover.branch := by
  classical
  intro x hx
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
  exact markedArcEndset_subset_branch (r i) hi

theorem markedFamilyVertices_card_le_six {M : HyperellipticModel E S}
    {ι : Type*} [Fintype ι] (r : ι → MarkedArc M) :
    (markedFamilyVertices r).card ≤ 6 := by
  rw [← M.cover.branch_card]
  exact Finset.card_le_card (markedFamilyVertices_subset_branch r)

/-- The embedded representative graph meets the marks exactly at its vertex union. -/
theorem markedFamily_graph_inter_branch {M : HyperellipticModel E S}
    {ι : Type*} [Fintype ι] (r : ι → MarkedArc M) :
    (⋃ i, (r i).image) ∩ (M.cover.branch : Set S) =
      (markedFamilyVertices r : Set S) := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hb⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have he : x ∈ markedArcEndset (r i) := by
      change x ∈ (markedArcEndset (r i) : Set S)
      rw [← markedArc_image_inter_branch]
      exact ⟨hi, hb⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, he⟩
  · intro hx
    obtain ⟨i, _, he⟩ := Finset.mem_biUnion.mp hx
    have hi : x ∈ (r i).image ∩ (M.cover.branch : Set S) := by
      rw [markedArc_image_inter_branch]
      exact he
    exact ⟨Set.mem_iUnion.mpr ⟨i, hi.1⟩, hi.2⟩

/-- Positive graph support consumes at least one of the six marks. -/
theorem markedFamily_unmet_card_le_five {M : HyperellipticModel E S}
    {ι : Type*} [Fintype ι] [Nonempty ι] (r : ι → MarkedArc M) :
    (M.cover.branch \ markedFamilyVertices r).card ≤ 5 := by
  classical
  have hnon : (markedFamilyVertices r).Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    refine ⟨(r i).map ⟨0, by norm_num⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_univ _, by simp [markedArcEndset]⟩
  have hc := Finset.card_sdiff_add_card_eq_card (markedFamilyVertices_subset_branch r)
  rw [M.cover.branch_card] at hc
  have hp := Finset.card_pos.mpr hnon
  omega


/-- A source endpoint object is connected because its actual arcs share an endpoint. -/
theorem markedFamily_graph_connected_of_common_endpoint {M : HyperellipticModel E S}
    {ι : Type*} [Nonempty ι] (r : ι → MarkedArc M) (b : S)
    (hb : ∀ i, b ∈ markedArcEndset (r i)) :
    IsConnected (⋃ i, (r i).image) := by
  apply IsConnected.iUnion_of_reflTransGen (fun i => markedArc_image_connected (r i))
  intro i j
  apply Relation.ReflTransGen.single
  refine ⟨b, ?_, ?_⟩
  · have h : b ∈ (r i).image ∩ (M.cover.branch : Set S) := by
      rw [markedArc_image_inter_branch]
      exact hb i
    exact h.1
  · have h : b ∈ (r j).image ∩ (M.cover.branch : Set S) := by
      rw [markedArc_image_inter_branch]
      exact hb j
    exact h.1

/-- The finite simultaneous representative graph is compact. -/
theorem markedFamily_graph_compact {M : HyperellipticModel E S}
    {ι : Type*} [Finite ι] (r : ι → MarkedArc M) :
    IsCompact (⋃ i, (r i).image) := isCompact_iUnion (fun i => markedArc_image_compact (r i))


end CurveComplex.HyperellipticModel
