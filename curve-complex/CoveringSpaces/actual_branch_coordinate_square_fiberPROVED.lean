import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Algebra.Ring.Commute

open Set

theorem actual_branch_coordinate_square_fiber {E : Type*} [TopologicalSpace E] (f : E → E)
    (e : OpenPartialHomeomorph E ℂ) (U : Set E)
    (hU : U ⊆ e.source) (hstable : Set.MapsTo f U U)
    (hneg : ∀ x ∈ U, e (f x) = -e x) :
    ∀ x ∈ U, ∀ y ∈ U,
      (e y) ^ 2 = (e x) ^ 2 ↔ y = x ∨ y = f x := by
  intro x hx y hy
  constructor
  · intro h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
    · exact Or.inl (e.injOn (hU hy) (hU hx) h)
    · exact Or.inr (e.injOn (hU hy) (hU (hstable hx))
        (h.trans (hneg x hx).symm))
  · rintro (rfl | rfl)
    · rfl
    · rw [hneg x hx]
      ring
