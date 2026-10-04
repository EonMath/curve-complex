import ActualSameClassNonloopEmptyRegion

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- Actual same-class nonloops construct homotopic ORIGINAL paths, with
orientation chosen from the source endpoint data rather than assumed. -/
theorem actual_same_class_unoriented_nonloop_path_homotopy
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b)
    (ha : a.val.map 0 ≠ a.val.map 1) :
    ∃ hu : a.val.map 0 ∈ ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ,
    ∃ hv : a.val.map 1 ∈ ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ,
    ∃ α β : Path (⟨a.val.map 0,hu⟩ : ↑(((M.cover.branch : Set S) \
      {a.val.map 0,a.val.map 1})ᶜ)) ⟨a.val.map 1,hv⟩,
      (∀ t, (α t).val = a.val.map t) ∧
      ((∀ t, (β t).val = b.val.map t) ∨
        (∀ t, (β t).val = b.val.map (unitInterval.symm t))) ∧ α.Homotopic β := by
  rcases actual_same_class_nonloop_endpoint_orientation M a b hclass ha with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · obtain ⟨hu,hv,α,β,hα,hβ,H⟩ :=
      actual_same_class_original_nonloop_path_homotopy M a b hclass ha h0 h1
    exact ⟨hu,hv,α,β,hα,Or.inl hβ,H⟩
  · obtain ⟨hu,hv,α,γ,hα,hγ,H,hγmarks⟩ :=
      actual_same_class_endpoint_relative_path_homotopy M a b hclass
    have hb : b.val.map 0 ≠ b.val.map 1 := by
      intro he
      exact ha (h0.trans (he.symm.trans h1.symm))
    have havoid (t : Interval) : b.val.map t ∈
        ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ := by
      rintro ⟨hm,hn⟩
      rcases b.val.marked_only_at_ends t hm with rfl | rfl
      · exact hn (Or.inr (mem_singleton_iff.mpr h1.symm))
      · exact hn (Or.inl h0.symm)
    let g : C(Interval,↑(((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ)) :=
      ⟨fun t => ⟨b.val.map t,havoid t⟩,b.val.continuous.subtype_mk _⟩
    have hg : IsEmbedding g := IsEmbedding.of_comp g.continuous continuous_subtype_val
      (NonLoopArc.isEmbedding ⟨b.val,hb⟩)
    let β : Path (⟨a.val.map 0,hu⟩ : ↑(((M.cover.branch : Set S) \
        {a.val.map 0,a.val.map 1})ᶜ)) ⟨a.val.map 1,hv⟩ := {
      toFun := fun t => g (unitInterval.symm t)
      continuous_toFun := g.continuous.comp unitInterval.continuous_symm
      source' := Subtype.ext (by change b.val.map (unitInterval.symm 0) = a.val.map 0; rw [unitInterval.symm_zero]; exact h0.symm)
      target' := Subtype.ext (by change b.val.map (unitInterval.symm 1) = a.val.map 1; rw [unitInterval.symm_one]; exact h1.symm) }
    have hγg : range γ ⊆ range g := by
      rintro z ⟨t,rfl⟩
      have hz : (γ t).val ∈ b.val.image := hγ ▸ mem_range_self t
      obtain ⟨s,hs⟩ := hz
      exact ⟨s,Subtype.ext hs⟩
    have hβg : range β ⊆ range g := by
      rintro z ⟨t,rfl⟩
      exact mem_range_self (unitInterval.symm t)
    exact ⟨hu,hv,α,β,hα,Or.inr (fun _ => rfl),H.trans
      (CurveComplex.actual_paths_on_embedded_interval_homotopic g hg γ β hγg hβg)⟩

/-- With no mutual interior contacts, literal same-class nonloops select an
actual empty comparison region WITHOUT ordered endpoint agreement as input. -/
theorem actual_same_class_original_parallel_nonloop_empty_region
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b)
    (ha : a.val.map 0 ≠ a.val.map 1)
    (hmeet : a.val.image ∩ b.val.image = {a.val.map 0,a.val.map 1}) :
    ∃ Ω : Set S, IsComplementComponent (a.val.image ∪ b.val.image) Ω ∧
      frontier Ω = a.val.image ∪ b.val.image ∧ Disjoint Ω (M.cover.branch : Set S) := by
  obtain ⟨hu,hv,α,β,hα,hβ,hhom⟩ :=
    actual_same_class_unoriented_nonloop_path_homotopy M a b hclass ha
  let f : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
  let g : C(Interval,S) := ⟨fun t => (β t).val,continuous_subtype_val.comp β.continuous⟩
  have hgimage : range g = b.val.image := by
    rcases hβ with hβ | hβ
    · apply congrArg range
      exact funext hβ
    · calc
        range g = range (b.val.map ∘ unitInterval.symm) := congrArg range (funext hβ)
        _ = range b.val.map := unitInterval.symmHomeomorph.surjective.range_comp _
  have hb : b.val.map 0 ≠ b.val.map 1 := by
    rcases actual_same_class_nonloop_endpoint_orientation M a b hclass ha with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · simpa only [← h0,← h1] using ha
    · intro he
      exact ha (h0.trans (he.symm.trans h1.symm))
  have hg : IsEmbedding g := by
    rcases hβ with hβ | hβ
    · have he : (g : Interval → S) = b.val.map := funext hβ
      rw [he]
      exact NonLoopArc.isEmbedding ⟨b.val,hb⟩
    · have he : (g : Interval → S) = b.val.map ∘ unitInterval.symm := funext hβ
      rw [he]
      exact (NonLoopArc.isEmbedding ⟨b.val,hb⟩).comp unitInterval.symmHomeomorph.isEmbedding
  have hg0 : g 0 = a.val.map 0 := congrArg Subtype.val β.source
  have hg1 : g 1 = a.val.map 1 := congrArg Subtype.val β.target
  have hinter : range f ∩ range g = {a.val.map 0,a.val.map 1} := by
    rw [hgimage]
    exact hmeet
  obtain ⟨Ω,hn,hconn,hsub,hmax,hfrontier,hfree⟩ :=
    actual_two_endpoint_punctured_homotopic_jordan_sides_have_empty_region M f g
      (a.val.map 0) (a.val.map 1) (NonLoopArc.isEmbedding ⟨a.val,ha⟩)
      hg rfl hg0 rfl hg1 ha hinter hu hv α β hα (fun _ => rfl) hhom
  rw [hgimage] at hsub hmax hfrontier
  exact ⟨Ω,⟨hn,hconn,hsub,hmax⟩,hfrontier,hfree⟩
end
end CurveComplex.HyperellipticModel
