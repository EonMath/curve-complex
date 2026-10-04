import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSourceSurgeryBranches

namespace CurveComplex
open Set

variable {S : Type} [TopologicalSpace S] {a b : Curve S}
  (D : SourceFirstReturnBoundary a b) (B : SourceTwoSurgeryBranches D)

theorem theta_first_inter_current :
    Set.range D.first ∩ b.image = {D.start,D.finish} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨t,rfl⟩,ht⟩
    by_cases h0 : t = 0
    · simp [h0,D.first_zero]
    by_cases h1 : t = 1
    · simp [h1,D.first_one]
    exact False.elim (D.first_interior_avoids t h0 h1 ht)
  · rintro x (rfl | hx)
    · exact ⟨⟨0,D.first_zero⟩,D.start_mem.2⟩
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨⟨1,D.first_one⟩,D.finish_mem.2⟩

theorem theta_closing_subset_current (i : Bool) :
    Set.range (B.closing i) ⊆ b.image := by
  rw [← B.closing_cover]
  cases i <;> intro x hx
  · exact Or.inl hx
  · exact Or.inr hx

theorem theta_boundary_union :
    (B.boundary false).image ∪ (B.boundary true).image = Set.range D.first ∪ b.image := by
  rw [B.boundary_image,B.boundary_image,← B.closing_cover]
  ext x
  simp only [Set.mem_union]
  tauto

theorem theta_boundary_inter :
    (B.boundary false).image ∩ (B.boundary true).image = Set.range D.first := by
  rw [B.boundary_image,B.boundary_image]
  have hP : ({D.start,D.finish} : Set S) ⊆ Set.range D.first := by
    rintro x (rfl | hx)
    · exact ⟨0,D.first_zero⟩
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨1,D.first_one⟩
  ext x
  constructor
  · rintro ⟨hx | hx,hy | hy⟩
    · exact hx
    · exact hx
    · exact hy
    · exact hP (B.closing_inter ▸ ⟨hx,hy⟩)
  · intro hx
    exact ⟨Or.inl hx,Or.inl hx⟩

theorem theta_boundary_diff (i : Bool) :
    (B.boundary i).image \ (B.boundary (!i)).image =
      Set.range (B.closing i) \ {D.start,D.finish} := by
  have hInt : Set.range (B.closing i) ∩ Set.range (B.closing (!i)) =
      {D.start,D.finish} := by
    cases i
    · exact B.closing_inter
    · simpa [Set.inter_comm] using B.closing_inter
  rw [B.boundary_image,B.boundary_image]
  ext x
  constructor
  · rintro ⟨hx | hx,hn⟩
    · exact False.elim (hn (Or.inl hx))
    · refine ⟨hx,?_⟩
      intro hp
      have hm : x ∈ Set.range (B.closing i) ∩ Set.range (B.closing (!i)) := hInt.symm ▸ hp
      exact hn (Or.inr hm.2)
  · rintro ⟨hx,hp⟩
    refine ⟨Or.inr hx,?_⟩
    rintro (hf | ho)
    · exact hp (theta_first_inter_current D ▸ ⟨hf,theta_closing_subset_current D B i hx⟩)
    · exact hp (hInt ▸ ⟨hx,ho⟩)

theorem theta_closing_open_image (i : Bool) :
    Set.range (B.closing i) \ {D.start,D.finish} =
      B.closing i '' Set.Ioo (0 : Interval) 1 := by
  ext x
  constructor
  · rintro ⟨⟨t,rfl⟩,hn⟩
    refine ⟨t,⟨?_,?_⟩,rfl⟩
    · have h0 : t ≠ 0 := by intro he; apply hn; simp [he,B.closing_zero]
      exact lt_of_le_of_ne (show (0 : Interval) ≤ t from t.property.1) (Ne.symm h0)
    · have h1 : t ≠ 1 := by intro he; apply hn; simp [he,B.closing_one]
      exact lt_of_le_of_ne (show t ≤ (1 : Interval) from t.property.2) h1
  · rintro ⟨t,ht,rfl⟩
    refine ⟨⟨t,rfl⟩,?_⟩
    rintro (he | he)
    · have ht0 := (B.closing_embedded i).injective (he.trans (B.closing_zero i).symm)
      exact (ne_of_gt ht.1) ht0
    · rw [Set.mem_singleton_iff] at he
      have ht1 := (B.closing_embedded i).injective (he.trans (B.closing_one i).symm)
      exact (ne_of_lt ht.2) ht1

theorem theta_closing_open_connected (i : Bool) :
    IsConnected (Set.range (B.closing i) \ {D.start,D.finish}) := by
  rw [theta_closing_open_image D B i]
  apply IsConnected.image
    (isConnected_Ioo (show (0 : Interval) < 1 from zero_lt_one))
  exact (B.closing i).continuous.continuousOn

end CurveComplex
#print axioms CurveComplex.theta_first_inter_current
#print axioms CurveComplex.theta_boundary_diff
#print axioms CurveComplex.theta_closing_open_connected

namespace CurveComplex
open Set
variable {S : Type} [TopologicalSpace S] {a b : Curve S}
  (D : SourceFirstReturnBoundary a b) (B : SourceTwoSurgeryBranches D)

theorem theta_complement_inter :
    (B.boundary false).imageᶜ ∩ (B.boundary true).imageᶜ =
      b.imageᶜ \ Set.range D.first := by
  rw [← Set.compl_union,theta_boundary_union D B]
  ext x
  simp only [Set.mem_compl_iff,Set.mem_union,Set.mem_sdiff]
  tauto

theorem theta_complement_union :
    (B.boundary false).imageᶜ ∪ (B.boundary true).imageᶜ =
      (Set.range D.first)ᶜ := by
  rw [← Set.compl_inter,theta_boundary_inter D B]

theorem theta_branch_complement_decomposition (i : Bool) :
    (B.boundary i).imageᶜ = (b.imageᶜ \ Set.range D.first) ∪
      (Set.range (B.closing (!i)) \ {D.start,D.finish}) := by
  have hcover := theta_boundary_union D B
  have hdiff := theta_boundary_diff D B (!i)
  simp only [Bool.not_not] at hdiff
  rw [← hdiff]
  cases i <;> ext x <;>
    simp only [Bool.not_false,Bool.not_true,Set.mem_compl_iff,Set.mem_union,Set.mem_sdiff]
  · have hu : x ∈ (B.boundary false).image ∪ (B.boundary true).image ↔
        x ∈ Set.range D.first ∪ b.image := by rw [hcover]
    simp only [Set.mem_union] at hu
    have hf : x ∈ Set.range D.first → x ∈ (B.boundary false).image := by
      rw [B.boundary_image]; exact Or.inl
    tauto
  · have hu : x ∈ (B.boundary false).image ∪ (B.boundary true).image ↔
        x ∈ Set.range D.first ∪ b.image := by rw [hcover]
    simp only [Set.mem_union] at hu
    have hf : x ∈ Set.range D.first → x ∈ (B.boundary true).image := by
      rw [B.boundary_image]; exact Or.inl
    tauto

end CurveComplex
#print axioms CurveComplex.theta_branch_complement_decomposition
