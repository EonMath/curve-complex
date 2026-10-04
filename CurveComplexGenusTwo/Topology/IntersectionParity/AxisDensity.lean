import Mathlib
namespace CurveComplex.LocalSurgery

/-- An actual chart mapping a locus into the vertical axis gives a dense
complement inside its source, including after restriction to an open overlap. -/
theorem axis_chart_complement_dense
    {S : Type*} [TopologicalSpace S] (A : Set S)
    (h : OpenPartialHomeomorph S (ℝ × ℝ))
    (hh : ∀ x ∈ h.source, x ∈ A ↔ (h x).1 = 0)
    (W : Set S) (hW : IsOpen W) (hWh : W ⊆ h.source) :
    Dense {x : W | (x : S) ∉ A} := by
  let f : W → ℝ × ℝ := fun x => h x
  have hopen : IsOpenMap f := by
    intro U hU
    have hvalOpen : IsOpen (Subtype.val '' U) := hW.isOpenMap_subtype_val U hU
    have hsub : Subtype.val '' U ⊆ h.source := by
      rintro x ⟨y, hy, rfl⟩
      exact hWh y.property
    have ho := h.isOpen_image_of_subset_source hvalOpen hsub
    simpa only [Set.image_image, Function.comp_def] using ho
  have hd : Dense (({0}ᶜ : Set ℝ) ×ˢ (Set.univ : Set ℝ)) :=
    (dense_compl_singleton (0 : ℝ)).prod dense_univ
  have hp := hd.preimage hopen
  convert hp using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, and_true, f]
  exact not_congr (hh x (hWh x.property))

end CurveComplex.LocalSurgery
