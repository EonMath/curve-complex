import Mathlib
open scoped unitInterval
open Topology

namespace CurveComplex.LocalSurgery

/-- Closure of a lifted loop is invariant through a free loop homotopy.
No finiteness or two-sheet hypothesis is needed for this covering-space step. -/
theorem covering_lift_loop_closure_invariant
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cov : IsCoveringMap p)
    (H : C(I × I, X)) (hloop : ∀ t : I, H (t, 0) = H (t, 1))
    (f : C(I, E)) (hzero : ∀ u : I, H (0, u) = p (f u)) :
    cov.liftHomotopy H f hzero (1, 0) = cov.liftHomotopy H f hzero (1, 1) ↔
      f 0 = f 1 := by
  let L := cov.liftHomotopy H f hzero
  let g₀ : I → E := fun t => L (t, 0)
  let g₁ : I → E := fun t => L (t, 1)
  have hg₀ : Continuous g₀ :=
    L.continuous.comp (continuous_id.prodMk continuous_const)
  have hg₁ : Continuous g₁ :=
    L.continuous.comp (continuous_id.prodMk continuous_const)
  have hlifts (t u : I) : p (L (t, u)) = H (t, u) :=
    congrFun (cov.liftHomotopy_lifts H f hzero) (t, u)
  have hproj : p ∘ g₀ = p ∘ g₁ := by
    funext t
    exact (hlifts t 0).trans ((hloop t).trans (hlifts t 1).symm)
  constructor
  · intro hclosed
    have heq := cov.eq_of_comp_eq hg₀ hg₁ hproj (1 : I) hclosed
    have hstart := congrFun heq (0 : I)
    change L (0, 0) = L (0, 1) at hstart
    dsimp only [L] at hstart
    rw [cov.liftHomotopy_zero, cov.liftHomotopy_zero] at hstart
    exact hstart
  · intro hclosed
    have hstart : g₀ 0 = g₁ 0 := by
      change L (0, 0) = L (0, 1)
      dsimp only [L]
      rw [cov.liftHomotopy_zero, cov.liftHomotopy_zero]
      exact hclosed
    exact congrFun (cov.eq_of_comp_eq hg₀ hg₁ hproj (0 : I) hstart) (1 : I)

end CurveComplex.LocalSurgery
