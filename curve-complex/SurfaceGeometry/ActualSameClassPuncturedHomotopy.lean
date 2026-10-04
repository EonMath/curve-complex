import ActualSameClassMarkedSweep
import Mathlib.Topology.Homotopy.Path

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- Same class constructs paths homotopic in the original endpoint-relative
punctured surface, with source parametrization literal and target IMAGE literal.
No equality with the target's chosen parametrization is asserted. -/
theorem actual_same_class_endpoint_relative_path_homotopy
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b) :
    ∃ hu : a.val.map 0 ∈ ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ,
    ∃ hv : a.val.map 1 ∈ ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ,
    ∃ α β : Path (⟨a.val.map 0,hu⟩ : ↑(((M.cover.branch : Set S) \
      {a.val.map 0,a.val.map 1})ᶜ)) ⟨a.val.map 1,hv⟩,
      (∀ t, (α t).val = a.val.map t) ∧
      range (fun t => (β t).val) = b.val.image ∧ α.Homotopic β ∧
      (∀ t, t ≠ 0 → t ≠ 1 → (β t).val ∉ (M.cover.branch : Set S)) := by
  obtain ⟨F,h0,hcollision,hends,hmarks,himage⟩ :=
    actual_same_class_endpoint_relative_punctured_sweep M a b hclass
  have hu : a.val.map 0 ∈ ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ := by simp
  have hv : a.val.map 1 ∈ ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ := by simp
  let α : Path (⟨a.val.map 0,hu⟩ : ↑(((M.cover.branch : Set S) \
      {a.val.map 0,a.val.map 1})ᶜ)) ⟨a.val.map 1,hv⟩ := {
    toFun := fun t => F (0,t)
    continuous_toFun := F.continuous.comp (continuous_const.prodMk continuous_id)
    source' := Subtype.ext (hends 0).1
    target' := Subtype.ext (hends 0).2 }
  let β : Path (⟨a.val.map 0,hu⟩ : ↑(((M.cover.branch : Set S) \
      {a.val.map 0,a.val.map 1})ᶜ)) ⟨a.val.map 1,hv⟩ := {
    toFun := fun t => F (1,t)
    continuous_toFun := F.continuous.comp (continuous_const.prodMk continuous_id)
    source' := Subtype.ext (hends 1).1
    target' := Subtype.ext (hends 1).2 }
  have H : α.Homotopy β := {
    toFun := F
    continuous_toFun := F.continuous
    map_zero_left := fun t => rfl
    map_one_left := fun t => rfl
    prop' := by
      intro τ t ht
      rcases ht with rfl | ht
      · exact Subtype.ext ((hends τ).1.trans (hends 0).1.symm)
      · rw [mem_singleton_iff] at ht
        subst t
        exact Subtype.ext ((hends τ).2.trans (hends 0).2.symm) }
  exact ⟨hu,hv,α,β,h0,himage,⟨H⟩,hmarks 1⟩
end
end CurveComplex.HyperellipticModel
