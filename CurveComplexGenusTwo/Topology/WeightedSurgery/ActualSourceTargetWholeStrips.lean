import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualFiniteEventPositionTransport
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Topology.Smoothing.SphereAtlasProof

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- A non-loop actual representative is embedded on the entire closed interval. -/
theorem actual_nonloop_representative_embedded
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (ha : a.val.map 0 ≠ a.val.map 1) : IsEmbedding a.val.map := by
  let : T2Space S := M.sphere.symm.t2Space
  have hinj : Function.Injective a.val.map := by
    intro t u he
    rcases a.val.injective_except_loop_closure t u he with h | h
    · exact h
    · rcases h with ⟨ht,hu⟩ | ⟨ht,hu⟩
      · subst t; subst u; exact False.elim (ha he)
      · subst t; subst u; exact False.elim (ha he.symm)
  exact (a.val.continuous.isClosedEmbedding hinj).isEmbedding

/-- Produce a WHOLE target-dependent strip from the actual non-loop arc.
Its only marked points are its two exact center endpoints: no supplied collar,
chart, geometric disk, isotopy or reaching script is required. -/
theorem actual_nonloop_whole_marked_strip
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (ha : a.val.map 0 ≠ a.val.map 1) :
    ∃ B : Interval × Set.Icc (-1:ℝ) 1 → S,
      IsEmbedding B ∧
      (∀ t, B (t,⟨0,by norm_num⟩) = a.val.map t) ∧
      (∀ z, B z ∈ M.cover.branch ↔
        z = ((0:Interval),⟨0,by norm_num⟩) ∨
        z = ((1:Interval),⟨0,by norm_num⟩)) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let endpointSet : Finset S := {a.val.map 0,a.val.map 1}
  let others : Finset S := M.cover.branch \ endpointSet
  let := (actualSphereSmoothAtlas M).charts
  let U : Set S := (others : Set S)ᶜ
  have hU : IsOpen U := others.finite_toSet.isClosed.isOpen_compl
  have haU : range a.val.map ⊆ U := by
    rintro x ⟨t,rfl⟩ ht
    obtain ⟨hm,hn⟩ := Finset.mem_sdiff.mp ht
    apply hn
    rcases a.val.marked_only_at_ends t hm with ht | ht <;>
      subst t <;> simp [endpointSet]
  obtain ⟨B,hB,hcenter,hBU⟩ := CurveComplex.source_whole_embedded_arc_strip
    ⟨a.val.map,a.val.continuous⟩ (actual_nonloop_representative_embedded M a ha) U hU haU
  refine ⟨B,hB,hcenter,?_⟩
  intro z
  constructor
  · intro hz
    have hn : B z ∉ (others : Set S) := hBU (mem_range_self z)
    have he : B z ∈ endpointSet := by
      by_contra h
      exact hn (Finset.mem_sdiff.mpr ⟨hz,h⟩)
    rcases Finset.mem_insert.mp he with he | he
    · left
      apply hB.injective
      exact he.trans (hcenter 0).symm
    · right
      apply hB.injective
      exact (Finset.mem_singleton.mp he).trans (hcenter 1).symm
  · rintro (rfl | rfl)
    · rw [hcenter]; exact a.val.start_marked
    · rw [hcenter]; exact a.val.end_marked

/-- Quotient equality produces actual target-reaching WHOLE strip transport,
with exact endpoint marks and final center image b. This theorem does not
claim stationary-anchor or stationary-protected-graph preservation. -/
theorem actual_same_class_whole_strip_transport
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 ≠ a.val.map 1) (hab : vertex M a = vertex M b) :
    ∃ G : AmbientIsotopy S,
      (∀ t p, p ∈ M.cover.branch → G.map (t,p) = p) ∧
      ∃ B : Interval → (Interval × Set.Icc (-1:ℝ) 1 → S),
        Continuous (fun z : Interval × (Interval × Set.Icc (-1:ℝ) 1) => B z.1 z.2) ∧
        (∀ t, IsEmbedding (B t)) ∧
        (∀ r, B 0 (r,⟨0,by norm_num⟩) = a.val.map r) ∧
        (range (fun r => B 1 (r,⟨0,by norm_num⟩)) = b.val.image) ∧
        (∀ t z, B t z ∈ M.cover.branch ↔
          z = ((0:Interval),⟨0,by norm_num⟩) ∨
          z = ((1:Interval),⟨0,by norm_num⟩)) := by
  obtain ⟨G,hm,hend⟩ := (show MarkedIsotopyRel M a.val.image b.val.image from Quotient.exact hab)
  obtain ⟨B,hB,hcenter,hmarks⟩ := actual_nonloop_whole_marked_strip M a ha
  let C : Interval → (Interval × Set.Icc (-1:ℝ) 1 → S) :=
    fun t z => G.map (t,B z)
  have hemb (t : Interval) : IsEmbedding (C t) := by
    obtain ⟨h,hh⟩ := G.homeomorphism_at t
    have he : C t = h ∘ B := by funext z; exact (hh (B z)).symm
    rw [he]
    exact h.isEmbedding.comp hB
  refine ⟨G,hm,C,?_,hemb,?_,?_,?_⟩
  · exact G.map.continuous.comp (continuous_fst.prodMk (hB.continuous.comp continuous_snd))
  · intro r
    exact (G.at_zero _).trans (hcenter r)
  · change range (fun r => G.map (1,B (r,⟨0,by norm_num⟩))) = _
    simp_rw [hcenter]
    change range ((fun z => G.map (1,z)) ∘ a.val.map) = _
    rw [Set.range_comp]
    exact hend
  · intro t z
    have hiff : C t z ∈ M.cover.branch ↔ B z ∈ M.cover.branch := by
      constructor
      · intro hz
        obtain ⟨h,hh⟩ := G.homeomorphism_at t
        have he : B z = C t z := by
          apply h.injective
          rw [hh,hh]
          exact (hm t _ hz).symm
        exact he ▸ hz
      · intro hz
        change G.map (t,B z) ∈ M.cover.branch
        rwa [hm t _ hz]
    exact hiff.trans (hmarks z)

end
end CurveComplex.HyperellipticModel.ArcSurgery
