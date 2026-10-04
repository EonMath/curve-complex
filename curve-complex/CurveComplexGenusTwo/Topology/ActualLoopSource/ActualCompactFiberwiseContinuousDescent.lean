import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Basic

namespace CurveComplex
open Topology
noncomputable section

/-- A literal fiber-coherent compact map constructs its continuous descent.
Used to retain a loop's marked endpoint identification without a false interval inverse. -/
theorem actual_compact_fiberwise_continuous_descent
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactSpace X] [T2Space Y]
    (q : C(X,Y)) (hsurj : Function.Surjective q) (F : C(X,Z))
    (hcoherent : ∀ x y, q x=q y → F x=F y) :
    ∃ G : C(Y,Z), ∀ x, G (q x)=F x := by
  classical
  let g : Y → Z := F ∘ Function.surjInv hsurj
  have hg (x : X) : g (q x)=F x :=
    hcoherent _ x (Function.surjInv_eq hsurj (q x))
  have hq : IsQuotientMap q := q.continuous.isClosedMap.isQuotientMap q.continuous hsurj
  have hc : Continuous g := hq.continuous_iff.mpr (by
    have he : g ∘ q = F := funext hg
    rw [he]
    exact F.continuous)
  exact ⟨⟨g,hc⟩,hg⟩
end
end CurveComplex
