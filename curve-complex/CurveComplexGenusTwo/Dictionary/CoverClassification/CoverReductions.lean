import CurveComplexGenusTwo.Dictionary.BranchedCover

namespace CurveComplex.BranchedDoubleCover

variable {X Y B C : Type*}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace B] [TopologicalSpace C]

/-- The nontrivial member of each regular two-point fiber is intrinsic. -/
theorem deck_commutes_of_projection_commutes
    (q : BranchedDoubleCover X B) (r : BranchedDoubleCover Y C)
    (h : X ≃ₜ Y) (k : B ≃ₜ C)
    (hp : ∀ x, r.projection (h x) = k (q.projection x)) :
    ∀ x, r.deck (h x) = h (q.deck x) := by
  intro x
  have hf : r.projection (h x) = r.projection (h (q.deck x)) := by
    rw [hp, hp, q.projection_deck]
  rcases (r.fiber_pair (h x) (h (q.deck x))).mp hf with heq | heq
  · have hfix : q.deck x = x := h.injective heq
    have hsame : r.deck (h x) = h x := by
      by_contra hne
      obtain ⟨z, hz⟩ := h.surjective (r.deck (h x))
      have hproj : q.projection z = q.projection x := by
        apply k.injective
        rw [← hp, hz, r.projection_deck, hp]
      rcases (q.fiber_pair x z).mp hproj.symm with hzx | hzx
      · exact hne (hz.symm.trans (congrArg h hzx))
      · exact hne (hz.symm.trans (congrArg h (hzx.trans hfix)))
    rw [hfix]
    exact hsame
  · exact heq.symm

/-- A compact Hausdorff total space makes the projection closed. -/
theorem projection_isClosedMap [CompactSpace X] [T2Space B]
    (q : BranchedDoubleCover X B) : IsClosedMap q.projection :=
  q.projection_continuous.isClosedMap

/-- The original branched projection, not just its complement restriction,
 is a quotient map. -/
theorem projection_isQuotientMap [CompactSpace X] [T2Space B]
    (q : BranchedDoubleCover X B) : Topology.IsQuotientMap q.projection :=
  q.projection_isClosedMap.isQuotientMap q.projection_continuous q.projection_surjective

/-- At a branch fiber, projection commutation forces continuity of any
set-theoretic lift. Compactness replaces a separate chart-extension estimate. -/
theorem continuousAt_lift_at_branch [CompactSpace Y] [T2Space C]
    (q : BranchedDoubleCover X B) (r : BranchedDoubleCover Y C)
    (k : B ≃ₜ C) (f : X → Y)
    (hp : ∀ x, r.projection (f x) = k (q.projection x))
    (x : X) (hx : r.projection (f x) ∈ r.branch) : ContinuousAt f x := by
  have hfix : r.deck (f x) = f x := (r.fixed_iff_branch _).mpr hx
  have hfiber : r.projection ⁻¹' {r.projection (f x)} = {f x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hy
      rcases (r.fiber_pair (f x) y).mp hy.symm with he | he
      · exact he
      · exact he.trans hfix
    · rintro rfl
      rfl
  have hb := r.projection_isClosedMap.comap_nhds_le
    (y := r.projection (f x))
  rw [hfiber, nhdsSet_singleton] at hb
  have ht : Filter.Tendsto (r.projection ∘ f) (nhds x)
      (nhds (r.projection (f x))) := by
    simpa only [Function.comp_def, hp] using
      (k.continuous.comp q.projection_continuous).tendsto x
  exact (Filter.tendsto_comap_iff.mpr ht).mono_right hb

/-- Continuity on the unbranched locus suffices for a set-theoretic lift
commuting with the projections. This includes every ramification point. -/
theorem continuous_lift_of_continuousOn_regular [CompactSpace Y] [T2Space C]
    (q : BranchedDoubleCover X B) (r : BranchedDoubleCover Y C)
    (k : B ≃ₜ C) (f : X → Y)
    (hp : ∀ x, r.projection (f x) = k (q.projection x))
    (hreg : ContinuousOn f {x | r.projection (f x) ∉ r.branch}) : Continuous f := by
  have hopen : IsOpen {x | r.projection (f x) ∉ r.branch} := by
    simp_rw [hp]
    exact r.branch.finite_toSet.isClosed.isOpen_compl.preimage
      (k.continuous.comp q.projection_continuous)
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : r.projection (f x) ∈ r.branch
  · exact continuousAt_lift_at_branch q r k f hp x hx
  · exact hreg.continuousAt (hopen.mem_nhds hx)

end CurveComplex.BranchedDoubleCover
