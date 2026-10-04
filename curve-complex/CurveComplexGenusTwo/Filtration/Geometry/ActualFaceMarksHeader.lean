import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
namespace CurveComplex.HyperellipticModel
open Set
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance integrationLocalInstance_ActualFaceMarksHeader_1 : DecidableEq S := Classical.decEq _
noncomputable local instance integrationLocalInstance_ActualFaceMarksHeader_2 : DecidableEq (Set S) := Classical.decEq _
noncomputable local instance integrationLocalInstance_ActualFaceMarksHeader_3 (p : Prop) : Decidable p := Classical.propDecidable p

theorem actual_face_marks_partition_card (M : HyperellipticModel E S) {ι : Type*} [Fintype ι]
    (r : ι → MarkedArc M) (F : Finset (Set S))
    (hF : ∀ U ∈ F, IsComplementComponent (⋃ i, (r i).image) U)
    (hcover : ∀ x ∈ (⋃ i, (r i).image)ᶜ, ∃ U ∈ F, x ∈ U) :
    ∑ U ∈ F, (M.cover.branch.filter (· ∈ U)).card =
      6 - (markedFamilyVertices r).card := by
  classical
  let marks : Set S → Finset S := fun U => M.cover.branch.filter (· ∈ U)
  have hp : (F : Set (Set S)).PairwiseDisjoint marks := by
    intro U hU V hV hne
    apply Finset.disjoint_left.mpr
    intro x hxU hxV
    exact Set.disjoint_left.mp (complementComponents_disjoint (hF U hU) (hF V hV) hne)
      (Finset.mem_filter.mp hxU).2 (Finset.mem_filter.mp hxV).2
  have hunion : F.biUnion marks = M.cover.branch \ markedFamilyVertices r := by
    ext x
    constructor
    · intro hx
      obtain ⟨U,hU,hxU⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hb, hxU⟩ := Finset.mem_filter.mp hxU
      refine Finset.mem_sdiff.mpr ⟨hb, ?_⟩
      intro hxv
      have hxg : x ∈ ⋃ i, (r i).image := by
        have h : x ∈ (⋃ i, (r i).image) ∩ (M.cover.branch : Set S) := by
          rw [markedFamily_graph_inter_branch]
          exact hxv
        exact h.1
      exact (hF U hU).2.2.1 hxU hxg
    · intro hx
      obtain ⟨hb,hnot⟩ := Finset.mem_sdiff.mp hx
      have hxg : x ∈ (⋃ i, (r i).image)ᶜ := by
        intro hxg
        have h : x ∈ (markedFamilyVertices r : Set S) := by
          rw [← markedFamily_graph_inter_branch]
          exact ⟨hxg,hb⟩
        exact hnot h
      obtain ⟨U,hU,hxU⟩ := hcover x hxg
      exact Finset.mem_biUnion.mpr ⟨U,hU,Finset.mem_filter.mpr ⟨hb,hxU⟩⟩
  rw [← Finset.card_biUnion hp, hunion,
    Finset.card_sdiff_of_subset (markedFamilyVertices_subset_branch r)]
  rw [M.cover.branch_card]
-- Arithmetic consumer for actual weighted face counts; this does not produce faces.

theorem weighted_six_mark_euler_bound (vertices edges faces components unused : ℕ)
    (hmarks : vertices + unused = 6)
    (heuler : vertices + faces = edges + components + 1)
    (hweighted : 3 * faces ≤ 2 * edges + 3 * unused)
    (hc : 1 ≤ components) : edges ≤ 12 := by
  omega

end CurveComplex.HyperellipticModel
