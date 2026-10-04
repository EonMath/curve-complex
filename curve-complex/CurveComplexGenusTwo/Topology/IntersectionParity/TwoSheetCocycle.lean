import Mathlib
open Set Topology

namespace CurveComplex.LocalSurgery

/- Construction substrate for cutting and doubling along an embedded curve.
The source-specific atlas and transition functions must still be CONSTRUCTED;
this file neither assumes nor concludes intersection parity. -/

/-- Mod-two transition data on an actual open cover. -/
structure TwoSheetCocycle (ι S : Type*) [TopologicalSpace S] where
  domain : ι → Set S
  open_domain : ∀ i, IsOpen (domain i)
  indexAt : S → ι
  mem_at : ∀ x, x ∈ domain (indexAt x)
  transition : ι → ι → S → ZMod 2
  continuous_change : ∀ i j, ContinuousOn (transition i j) (domain i ∩ domain j)
  self : ∀ i x, x ∈ domain i → transition i i x = 0
  cocycle : ∀ i j k x, x ∈ domain i ∩ domain j ∩ domain k →
    transition i j x + transition j k x = transition i k x

/-- Genuine bundle gluing, delegated to Mathlib's FiberBundleCore. -/
noncomputable def TwoSheetCocycle.bundleCore
    {ι S : Type*} [TopologicalSpace S] (A : TwoSheetCocycle ι S) :
    FiberBundleCore ι S (ZMod 2) where
  baseSet := A.domain
  isOpen_baseSet := A.open_domain
  indexAt := A.indexAt
  mem_baseSet_at := A.mem_at
  coordChange := fun i j x v => v + A.transition i j x
  coordChange_self := by
    intro i x hx v
    rw [A.self i x hx, add_zero]
  continuousOn_coordChange := by
    intro i j
    have hAdd : Continuous (fun q : ZMod 2 × ZMod 2 => q.1 + q.2) :=
      continuous_of_discreteTopology
    exact hAdd.comp_continuousOn
      (continuous_snd.continuousOn.prodMk
        ((A.continuous_change i j).comp continuous_fst.continuousOn
          (fun _ h => h.1)))
  coordChange_comp := by
    intro i j k x hx v
    rw [add_assoc, A.cocycle i j k x hx]

/-- The total space carries Mathlib's generated bundle topology. -/
abbrev TwoSheetCocycle.TotalSpace
    {ι S : Type*} [TopologicalSpace S] (A : TwoSheetCocycle ι S) :=
  A.bundleCore.TotalSpace

/-- Its fibers are literally ZMod 2, not a cardinality surrogate. -/
noncomputable abbrev TwoSheetCocycle.projection
    {ι S : Type*} [TopologicalSpace S] (A : TwoSheetCocycle ι S) :
    A.TotalSpace → S := A.bundleCore.proj

-- Construction checks: Mathlib infers the total-space topology and bundle instance.
section ConstructionChecks
variable {ι S : Type*} [TopologicalSpace S] (A : TwoSheetCocycle ι S)
#check A.bundleCore.localTrivAt
#check (FiberBundle.isCoveringMap (F := ZMod 2) (E := A.bundleCore.Fiber))
end ConstructionChecks

end CurveComplex.LocalSurgery
