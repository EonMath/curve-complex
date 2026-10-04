import CurveComplexGenusTwo.Foundations.RealizationCW

namespace CurveComplex

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

private def faceEquiv (e : V ≃ W) (σ : Finset V) :
    (σ.image e) ≃ σ where
  toFun w := ⟨e.symm w.1, by
    rcases Finset.mem_image.mp w.2 with ⟨v, hv, heq⟩
    simpa [← heq] using hv⟩
  invFun v := ⟨e v.1, Finset.mem_image.mpr ⟨v, v.2, rfl⟩⟩
  left_inv w := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp

private noncomputable def simplexRelabel (e : V ≃ W) (σ : Finset V) :
    FiniteSimplex σ → FiniteSimplex (σ.image e) := by
  intro x
  refine ⟨fun w => x.val (faceEquiv e σ w), ?_, ?_⟩
  · intro w
    exact x.property.1 _
  · exact (Fintype.sum_equiv (faceEquiv e σ)
      (fun w => x.val (faceEquiv e σ w)) x.val (fun _ => rfl)).trans x.property.2

omit [DecidableEq V] in
private theorem simplexRelabel_continuous (e : V ≃ W) (σ : Finset V) :
    Continuous (simplexRelabel e σ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  exact (continuous_apply (faceEquiv e σ w)).comp continuous_subtype_val

noncomputable def vertexRelabelPoint
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (e : V ≃ W)
    (hface : ∀ σ : Finset V, σ ∈ K.faces ↔ σ.image e ∈ L.faces)
    (x : RealizationPoint K) : RealizationPoint L := by
  refine ⟨fun w => x.weight (e.symm w), fun w => x.nonneg _, ?_⟩
  obtain ⟨σ, hσ, hz, hs⟩ := x.liesInFace
  refine ⟨σ.image e, (hface σ).mp hσ, ?_, ?_⟩
  · intro w hw
    apply hz
    intro hv
    exact hw (Finset.mem_image.mpr ⟨e.symm w, hv, e.apply_symm_apply w⟩)
  · rw [Finset.sum_image (e.injective.injOn)]
    simpa only [e.symm_apply_apply] using hs

omit [DecidableEq V] in
private theorem relabel_face
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (e : V ≃ W)
    (hface : ∀ σ : Finset V, σ ∈ K.faces ↔ σ.image e ∈ L.faces)
    (σ : Finset V) (hσ : σ ∈ K.faces) (x : FiniteSimplex σ) :
    vertexRelabelPoint K L e hface (faceInclusion K σ hσ x) =
      faceInclusion L (σ.image e) ((hface σ).mp hσ)
        (simplexRelabel e σ x) := by
  apply RealizationPoint.ext
  funext w
  by_cases hw : w ∈ σ.image e
  · have hv : e.symm w ∈ σ := (faceEquiv e σ ⟨w, hw⟩).2
    simp only [vertexRelabelPoint, faceInclusion, simplexRelabel,
      dite_eq_left hw, dite_eq_left hv]
    rfl
  · have hv : e.symm w ∉ σ := by
      intro hv
      exact hw (Finset.mem_image.mpr ⟨e.symm w, hv, e.apply_symm_apply w⟩)
    simp only [vertexRelabelPoint, faceInclusion,
      dite_eq_right hw, dite_eq_right hv]

omit [DecidableEq V] in
theorem vertexRelabelPoint_continuous
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (e : V ≃ W)
    (hface : ∀ σ : Finset V, σ ∈ K.faces ↔ σ.image e ∈ L.faces) :
    Continuous (vertexRelabelPoint K L e hface) := by
  rw [continuous_def]
  intro U hU σ hσ
  have heq : vertexRelabelPoint K L e hface ∘ faceInclusion K σ hσ =
      faceInclusion L (σ.image e) ((hface σ).mp hσ) ∘
        simplexRelabel e σ := by
    funext x
    exact relabel_face K L e hface σ hσ x
  change IsOpen ((vertexRelabelPoint K L e hface ∘ faceInclusion K σ hσ) ⁻¹' U)
  rw [heq]
  exact (hU _ ((hface σ).mp hσ)).preimage
    (simplexRelabel_continuous e σ)

noncomputable def realizationHomeomorphOfVertexEquiv
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (e : V ≃ W)
    (hface : ∀ σ : Finset V, σ ∈ K.faces ↔ σ.image e ∈ L.faces) :
    RealizationPoint K ≃ₜ RealizationPoint L := by
  let hreverse : ∀ τ : Finset W,
      τ ∈ L.faces ↔ τ.image e.symm ∈ K.faces := by
    intro τ
    have hi := hface (τ.image e.symm)
    simpa [Finset.image_image] using hi.symm
  refine {
    toFun := vertexRelabelPoint K L e hface
    invFun := vertexRelabelPoint L K e.symm hreverse
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := vertexRelabelPoint_continuous K L e hface
    continuous_invFun := vertexRelabelPoint_continuous L K e.symm hreverse }
  · intro x
    apply RealizationPoint.ext
    funext v
    simp [vertexRelabelPoint]
  · intro y
    apply RealizationPoint.ext
    funext w
    simp [vertexRelabelPoint]

theorem realizationHomeomorphOfVertexEquiv_weight
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (e : V ≃ W)
    (hface : ∀ σ : Finset V, σ ∈ K.faces ↔ σ.image e ∈ L.faces)
    (x : RealizationPoint K) (w : W) :
    (realizationHomeomorphOfVertexEquiv K L e hface x).weight w =
      x.weight (e.symm w) := rfl

end CurveComplex
