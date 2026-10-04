import CurveComplexGenusTwo.Topology.ArcCounts.ActualLowDegreeAssembly
import CurveComplexGenusTwo.Topology.ArcCounts.ActualTwoTraceShape
namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_nonloop_low_degree_face_contains_branch
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (hsigma : sigma.Nonempty)
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (hnonloop : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1)
    (U : Set S) (hU : IsComplementComponent (⋃ k, (r k).val.image) U)
    (hdegree : actualIncidentEdgeDegree M r U < 3) :
    ∃ b ∈ M.cover.branch, b ∈ U := by
  classical
  by_contra hn
  have hfree : ∀ b ∈ M.cover.branch, b ∉ U := by simpa using hn
  obtain ⟨i,j,hij,hi,hj,hboundary,hpair,hparallel⟩ :=
    actual_unmarked_low_degree_two_nonparallel_traces M hsigma r hr hd U hU hdegree hfree
  obtain ⟨p,hp⟩ := hpair.1
  have hc := actual_nonparallel_nonloop_pair_complement_connected M (r i) (r j)
    (hnonloop i) (hnonloop j) (hd i j hij)
    (hparallel (hnonloop i) (hnonloop j)) p (hpair.2.2.1 hp)
  have hwhole : U = ((r i).val.image ∪ (r j).val.image)ᶜ :=
    (hpair.2.2.2 _ hc hpair.2.2.1 (fun x hx => hx)).symm
  have hsubset : M.cover.branch ⊆ markedArcEndset (r i).val ∪ markedArcEndset (r j).val := by
    intro b hb
    have hnot := hfree b hb
    rw [hwhole] at hnot
    have hbimg : b ∈ (r i).val.image ∪ (r j).val.image := by
      by_contra h
      exact hnot h
    rcases hbimg with hbi | hbj
    · apply Finset.mem_union_left
      change b ∈ (markedArcEndset (r i).val : Set S)
      rw [← markedArc_image_inter_branch]
      exact ⟨hbi,hb⟩
    · apply Finset.mem_union_right
      change b ∈ (markedArcEndset (r j).val : Set S)
      rw [← markedArc_image_inter_branch]
      exact ⟨hbj,hb⟩
  have hcard := Finset.card_le_card hsubset
  have hu := Finset.card_union_le (markedArcEndset (r i).val) (markedArcEndset (r j).val)
  have hi : (markedArcEndset (r i).val).card = 2 := by simp [markedArcEndset,hnonloop i]
  have hj : (markedArcEndset (r j).val).card = 2 := by simp [markedArcEndset,hnonloop j]
  rw [M.cover.branch_card] at hcard
  omega

theorem actual_nonloop_low_degree_faces_card_le_unused_branch
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (hsigma : sigma.Nonempty)
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (hnonloop : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1)
    (F : Finset (Set S))
    (hF : ∀ U ∈ F, IsComplementComponent (⋃ i, (r i).val.image) U) :
    (F.filter (fun U => actualIncidentEdgeDegree M r U < 3)).card ≤
      6 - (markedFamilyVertices (fun i => (r i).val)).card := by
  classical
  let L := F.filter (fun U => actualIncidentEdgeDegree M r U < 3)
  have hempty : (L.filter (fun U => ∀ b ∈ M.cover.branch, b ∉ U)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro U hU
    obtain ⟨hUL,hfree⟩ := Finset.mem_filter.mp hU
    obtain ⟨hUF,hdegree⟩ := Finset.mem_filter.mp hUL
    obtain ⟨b,hb,hbU⟩ := actual_nonloop_low_degree_face_contains_branch M hsigma r hr hd
      hnonloop U (hF U hUF) hdegree
    exact hfree b hb hbU
  have hbudget := actual_low_degree_faces_card_le_unused_plus_unmarked M r F hF
  change L.card ≤ (6 - (markedFamilyVertices (fun i => (r i).val)).card) +
    (L.filter (fun U => ∀ b ∈ M.cover.branch, b ∉ U)).card at hbudget
  simpa [hempty] using hbudget
end CurveComplex.HyperellipticModel
