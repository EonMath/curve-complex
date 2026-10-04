import CurveComplexGenusTwo.Dependencies.SpherePort

namespace CurveComplex.SpherePort

private def chartEmbed (c : JordanCurve) (P : Chart c) :
    Schoenflies.Plane → Sphere := fun y => (P.plane.symm y : Sphere)

private theorem chartEmbed_continuous (c : JordanCurve) (P : Chart c) :
    Continuous (chartEmbed c P) :=
  continuous_subtype_val.comp P.plane.symm.continuous

private theorem chartEmbed_embedding (c : JordanCurve) (P : Chart c) :
    Topology.IsEmbedding (chartEmbed c P) :=
  Topology.IsEmbedding.subtypeVal.comp P.plane.symm.isEmbedding

noncomputable def chartOnePoint (c : JordanCurve) (P : Chart c) :
    OnePoint Schoenflies.Plane ≃ₜ Sphere := by
  apply OnePoint.equivOfIsEmbeddingOfRangeEq P.puncture
    (chartEmbed c P) (chartEmbed_embedding c P)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (P.plane.symm y).property
  · intro hx
    refine ⟨P.plane ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val (P.plane.symm_apply_apply ⟨x, hx⟩)

@[simp] theorem chartOnePoint_some (c : JordanCurve) (P : Chart c)
    (y : Schoenflies.Plane) :
    chartOnePoint c P (OnePoint.some y) = chartEmbed c P y := by
  simp [chartOnePoint, OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]

@[simp] theorem chartOnePoint_infty (c : JordanCurve) (P : Chart c) :
    chartOnePoint c P OnePoint.infty = P.puncture := by
  simp [chartOnePoint, OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty]

theorem pullback_eq_image (c : JordanCurve) (P : Chart c)
    (A : Set Schoenflies.Plane) :
    P.pullback c A = chartEmbed c P '' A := by
  ext x
  constructor
  · rintro ⟨hx, hA⟩
    refine ⟨P.plane ⟨x, hx⟩, hA, ?_⟩
    exact congrArg Subtype.val (P.plane.symm_apply_apply ⟨x, hx⟩)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(P.plane.symm y).property, ?_⟩
    have heq : (⟨chartEmbed c P y, (P.plane.symm y).property⟩ :
        {x : Sphere // x ≠ P.puncture}) = P.plane.symm y := Subtype.ext rfl
    simpa [heq] using hy

theorem chart_pullback_closure (c : JordanCurve) (P : Chart c)
    (A : Set Schoenflies.Plane) (hA : IsCompact (closure A)) :
    closure (P.pullback c A) = P.pullback c (closure A) := by
  rw [pullback_eq_image, pullback_eq_image]
  apply Set.Subset.antisymm
  · apply closure_minimal (Set.image_mono subset_closure)
    exact (hA.image (chartEmbed_continuous c P)).isClosed
  · exact image_closure_subset_closure_image (chartEmbed_continuous c P)

noncomputable def chart_pullback_closure_homeomorph (c : JordanCurve) (P : Chart c)
    (A : Set Schoenflies.Plane) (hA : IsCompact (closure A)) :
    closure A ≃ₜ closure (P.pullback c A) := by
  rw [chart_pullback_closure c P A hA, pullback_eq_image]
  exact (chartEmbed_embedding c P).homeomorphImage (closure A)

def compactifiedOutside (A : Set Schoenflies.Plane) :
    Set (OnePoint Schoenflies.Plane) :=
  {OnePoint.infty} ∪ OnePoint.some '' A

theorem closure_compactifiedOutside (A : Set Schoenflies.Plane) :
    closure (compactifiedOutside A) = compactifiedOutside (closure A) := by
  have hclosed : IsClosed (compactifiedOutside (closure A)) := by
    apply isOpen_compl_iff.mp
    have hcomp : (compactifiedOutside (closure A))ᶜ =
        OnePoint.some '' (closure A)ᶜ := by
      ext x
      cases x with
      | infty => simp [compactifiedOutside]
      | coe y => simp [compactifiedOutside]
    rw [hcomp]
    exact OnePoint.isOpen_image_coe.mpr isClosed_closure.isOpen_compl
  apply Set.Subset.antisymm
  · apply closure_minimal
    · exact Set.union_subset_union_right _ (Set.image_mono subset_closure)
    · exact hclosed
  · intro x hx
    rcases hx with hx | hx
    · exact subset_closure (Or.inl hx)
    · exact closure_mono (Set.subset_union_right)
        (image_closure_subset_closure_image OnePoint.continuous_coe hx)

theorem chart_outside_eq_image (c : JordanCurve) (P : Chart c) :
    P.outside c = chartOnePoint c P ''
      compactifiedOutside (Schoenflies.outside (P.planeImage c)) := by
  rw [Chart.outside, pullback_eq_image]
  ext x
  simp only [compactifiedOutside, Set.image_union, Set.image_singleton,
    Set.image_image, chartOnePoint_infty, chartOnePoint_some]

noncomputable def chart_outside_closure_homeomorph (c : JordanCurve) (P : Chart c) :
    closure (compactifiedOutside (Schoenflies.outside (P.planeImage c))) ≃ₜ
      closure (P.outside c) := by
  let h := chartOnePoint c P
  apply Homeomorph.sets h
  ext x
  rw [Set.mem_preimage, chart_outside_eq_image]
  change x ∈ closure (compactifiedOutside (Schoenflies.outside (P.planeImage c))) ↔
    h x ∈ closure (h '' compactifiedOutside (Schoenflies.outside (P.planeImage c)))
  rw [← h.image_closure]
  exact ⟨fun hx => Set.mem_image_of_mem h hx, fun hx => by
    rcases hx with ⟨y, hy, hxy⟩
    exact h.injective hxy ▸ hy⟩

end CurveComplex.SpherePort
