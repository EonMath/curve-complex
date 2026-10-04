import ActualCover
import CurveComplexGenusTwo.Dictionary.MarkedSphere

namespace CurveComplex
open scoped Manifold ContDiff

theorem actual_alternating_model_transfer
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (hS : IsGenus S 2) (e : S ≃ₜ AlternatingSphereCover.Total) :
    Nonempty (HyperellipticModel S
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  classical
  let B := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  let q₀ := AlternatingSphereCover.actualBranchedDoubleCover
  let q : BranchedDoubleCover S B := {
    projection := q₀.projection ∘ e
    projection_continuous := q₀.projection_continuous.comp e.continuous
    projection_surjective := q₀.projection_surjective.comp e.surjective
    deck := (e.trans q₀.deck).trans e.symm
    deck_involution := by
      intro x
      change e.symm (q₀.deck (e (e.symm (q₀.deck (e x))))) = x
      rw [e.apply_symm_apply, q₀.deck_involution, e.symm_apply_apply]
    branch := q₀.branch
    branch_card := q₀.branch_card
    fixed_iff_branch := by
      intro x
      change e.symm (q₀.deck (e x)) = x ↔ q₀.projection (e x) ∈ q₀.branch
      constructor
      · intro h
        apply (q₀.fixed_iff_branch (e x)).mp
        have he := congrArg e h
        simpa only [e.apply_symm_apply] using he
      · intro h
        rw [(q₀.fixed_iff_branch (e x)).mpr h, e.symm_apply_apply]
    projection_deck := by
      intro x
      change q₀.projection (e (e.symm (q₀.deck (e x)))) = q₀.projection (e x)
      rw [e.apply_symm_apply, q₀.projection_deck]
    fiber_pair := by
      intro x y
      change q₀.projection (e x) = q₀.projection (e y) ↔
        y = x ∨ y = e.symm (q₀.deck (e x))
      rw [q₀.fiber_pair]
      constructor
      · rintro (h | h)
        · exact Or.inl (e.injective h)
        · exact Or.inr (by
            apply e.injective
            rw [e.apply_symm_apply]
            exact h)
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr (e.apply_symm_apply _)
    unbranched_cover := q₀.unbranched_cover.comp_homeomorph e
    branch_chart := by
      intro w hw
      let c := q₀.branch_chart (e w) hw
      exact {
        upstairs := e.transOpenPartialHomeomorph c.upstairs
        downstairs := c.downstairs
        upstairs_mem := by
          change e w ∈ c.upstairs.source
          exact c.upstairs_mem
        downstairs_mem := c.downstairs_mem
        upstairs_center := c.upstairs_center
        downstairs_center := c.downstairs_center
        image_mem := by
          intro x hx
          change e x ∈ c.upstairs.source at hx
          exact c.image_mem (e x) hx
        square := by
          intro x hx
          change e x ∈ c.upstairs.source at hx
          exact c.square (e x) hx }
  }
  exact ⟨{ cover := q, sphere := Homeomorph.refl B, genusTwo := hS }⟩

end CurveComplex
