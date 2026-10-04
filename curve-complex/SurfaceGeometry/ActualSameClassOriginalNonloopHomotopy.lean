import ActualSameClassPuncturedHomotopy
import ActualEmbeddedTracePathHomotopy

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- Source same class constructs homotopy between the ORIGINAL nonloop
parametrizations once their ordered endpoints agree. The final sweep target
is converted using actual coordinates on b, not supplied parametrization data. -/
theorem actual_same_class_original_nonloop_path_homotopy
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b)
    (ha : a.val.map 0 ≠ a.val.map 1)
    (h0 : a.val.map 0 = b.val.map 0) (h1 : a.val.map 1 = b.val.map 1) :
    ∃ hu : a.val.map 0 ∈ ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ,
    ∃ hv : a.val.map 1 ∈ ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ,
    ∃ α β : Path (⟨a.val.map 0,hu⟩ : ↑(((M.cover.branch : Set S) \
      {a.val.map 0,a.val.map 1})ᶜ)) ⟨a.val.map 1,hv⟩,
      (∀ t, (α t).val = a.val.map t) ∧
      (∀ t, (β t).val = b.val.map t) ∧ α.Homotopic β := by
  obtain ⟨hu,hv,α,γ,hα,hγ,H,hγmarks⟩ :=
    actual_same_class_endpoint_relative_path_homotopy M a b hclass
  have hb : b.val.map 0 ≠ b.val.map 1 := by simpa only [← h0,← h1] using ha
  have havoid (t : Interval) : b.val.map t ∈
      ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ := by
    rintro ⟨hm,hn⟩
    rcases b.val.marked_only_at_ends t hm with rfl | rfl
    · exact hn (Or.inl h0.symm)
    · exact hn (Or.inr (mem_singleton_iff.mpr h1.symm))
  let g : C(Interval,↑(((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ)) :=
    ⟨fun t => ⟨b.val.map t,havoid t⟩,b.val.continuous.subtype_mk _⟩
  have hg : IsEmbedding g := IsEmbedding.of_comp g.continuous continuous_subtype_val
    (NonLoopArc.isEmbedding ⟨b.val,hb⟩)
  let β : Path (⟨a.val.map 0,hu⟩ : ↑(((M.cover.branch : Set S) \
      {a.val.map 0,a.val.map 1})ᶜ)) ⟨a.val.map 1,hv⟩ := {
    toFun := g
    continuous_toFun := g.continuous
    source' := Subtype.ext h0.symm
    target' := Subtype.ext h1.symm }
  have hγg : range γ ⊆ range g := by
    rintro z ⟨t,rfl⟩
    have hz : (γ t).val ∈ b.val.image := hγ ▸ mem_range_self t
    obtain ⟨s,hs⟩ := hz
    exact ⟨s,Subtype.ext hs⟩
  have hβg : range β ⊆ range g := fun _ hz => hz
  exact ⟨hu,hv,α,β,hα,fun _ => rfl,H.trans
    (CurveComplex.actual_paths_on_embedded_interval_homotopic g hg γ β hγg hβg)⟩
end
end CurveComplex.HyperellipticModel
