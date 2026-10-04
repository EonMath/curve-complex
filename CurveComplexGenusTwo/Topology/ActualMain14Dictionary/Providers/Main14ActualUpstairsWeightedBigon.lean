import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.WeightedBigonReplacementStatement
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14DeckSeparatedBigonSupport
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14PairedDeckOperation

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 4000000

/-- Specialize the actual source weighted surgery to the given two upstairs
curves, in a support constructed disjoint from its deck translate. The strict
single-operation decrease and actual paired equivariant operation are both
produced; no surgery, support, or equivariance certificate is supplied. -/
theorem innermost_full_preimage_actual_weighted_bigon_operation
    (M : HyperellipticModel E S) (a b : EssentialCurve E)
    (ht : Transverse a.val b.val) (B : LocalSurgery.TwoCurveDisk a.val b.val)
    (c d : PuncturedCircle M)
    (ha : a.val.image = M.cover.projection ⁻¹' c.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.image)
    (htbase : Transverse c.curve d.curve)
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
    ∃ V : Set E, ∃ H : AmbientIsotopy E, ∃ a' b' : EssentialCurve E,
    ∃ K : AmbientIsotopy E,
      IsOpen V ∧ range B.disk ⊆ V ∧
      Disjoint (closure V) (M.cover.deck '' closure V) ∧
      ((H.finalMap '' a.val.image = a'.val.image ∧ b' = b) ∨
        (H.finalMap '' b.val.image = b'.val.image ∧ a' = a)) ∧
      (∀ t x, x ∉ V → H.map (t,x) = x) ∧
      Quotient.mk (essentialCurveSetoid E) a' = Quotient.mk (essentialCurveSetoid E) a ∧
      Quotient.mk (essentialCurveSetoid E) b' = Quotient.mk (essentialCurveSetoid E) b ∧
      Transverse a'.val b'.val ∧
      (a'.val.image ∩ b'.val.image).ncard < (a.val.image ∩ b.val.image).ncard ∧
      (∀ t x, K.map (t,x) = M.cover.deck (H.map (t,M.cover.deck (H.map (t,x))))) ∧
      (∀ t x, K.map (t,M.cover.deck x) = M.cover.deck (K.map (t,x))) ∧
      (∀ t x, M.cover.projection x ∈ M.cover.branch → K.map (t,x) = x) := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  obtain ⟨V,hV,hBV,hsep,hfreeV⟩ :=
    M.innermost_full_preimage_deck_separated_support a b ht B c d ha hb htbase hempty
  let r : Bool → EssentialCurve E := fun i => if i then b else a
  have hr : ∀ i j, i ≠ j → Transverse (r i).val (r j).val := by
    intro i j hij
    cases i <;> cases j
    · exact False.elim (hij rfl)
    · exact ht
    · exact transverse_symm_of_chart ht
    · exact False.elim (hij rfl)
  have hclean := LocalSurgery.empty_two_curve_disk_has_clean_sides a b ht B hempty
  obtain ⟨k,H,r',hkw,hfixed,himage,hfix,hclass,htrans,henergy⟩ :=
    FiniteMinimalCompatibility.finite_family_weighted_bigon_replacement E Bool r hr
      false true (by decide) B.firstCorner B.secondCorner B.corners_ne
      B.firstSide B.secondSide B.first_embedded B.second_embedded
      B.first_zero B.second_zero B.first_one B.second_one
      B.first_on_curve B.second_on_curve hclean.1 hclean.2
      B.disk B.disk_embedded B.boundary_eq hempty V hV hBV
  have hdrop : ((r' false).val.image ∩ (r' true).val.image).ncard <
      (a.val.image ∩ b.val.image).ncard := by
    simp only [Fintype.sum_bool] at henergy
    simp only [Bool.false_eq_true,Bool.true_eq_false,if_false,if_true,zero_add,add_zero] at henergy
    simp only [r,Bool.false_eq_true,ite_false,ite_true,Set.inter_comm] at henergy
    omega
  have hsepV : Disjoint V (M.cover.deck '' V) :=
    hsep.mono subset_closure (Set.image_mono subset_closure)
  obtain ⟨K,hK,hKeq,hKV,hKτV,hKfix,hKram⟩ :=
    M.cover.supported_paired_deck_operation H V hsepV hfix
  refine ⟨V,H,r' false,r' true,K,hV,hBV,hsep,?_,hfix,?_,?_,htrans false true (by decide),hdrop,hK,hKeq,hKram⟩
  · cases k
    · left
      exact ⟨himage,hfixed true (by decide)⟩
    · right
      exact ⟨himage,hfixed false (by decide)⟩
  · exact hclass false
  · exact hclass true
end CurveComplex.HyperellipticModel
