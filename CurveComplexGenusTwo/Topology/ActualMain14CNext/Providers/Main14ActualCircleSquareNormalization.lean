import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import Schoenflies.JordanSchoenflies

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 4000000

/-- Normalize the original actual punctured circle to the model square in a
plane chart omitting an actual branch point. Neither chart nor normalized
circle is a supplied premise. -/
theorem actual_punctured_circle_square_normalization
    (M : HyperellipticModel E S) (c : PuncturedCircle M) :
    ∃ p : S, p ∈ M.cover.branch ∧ ∃ F : OpenPartialHomeomorph S Plane,
      F.source = {p}ᶜ ∧ F.target = univ ∧ c.image ⊆ F.source ∧ F '' c.image = modelCurve := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨p,hp⟩ : M.cover.branch.Nonempty := Finset.card_pos.mp (by rw [M.cover.branch_card]; norm_num)
  have havoid (x : S) (hx : x ∈ c.image) : x ≠ p := by
    intro he; exact Set.disjoint_left.mp c.avoids_branch hx (he.symm ▸ hp)
  let e := M.puncturedPlane p
  let f : Plane → S := fun z => (e.symm z).val
  have hf : IsOpenEmbedding f :=
    isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
  let α : C(Circle,Plane) := ⟨fun t => e ⟨c.curve.map t,havoid _ (Set.mem_range_self t)⟩,
    e.continuous.comp (c.curve.embedded.continuous.subtype_mk _)⟩
  have hfα (t : Circle) : f (α t) = c.curve.map t := congrArg Subtype.val (e.symm_apply_apply _)
  have hα : IsEmbedding α := (α.continuous.isClosedEmbedding (by
    intro t u he
    apply c.curve.embedded.injective
    exact (hfα t).symm.trans ((congrArg f he).trans (hfα u)))).isEmbedding
  have hJ := isJordanCurve_range_of_isEmbedding_circle α hα
  obtain ⟨h⟩ := hJ.homeomorph_modelCurve
  obtain ⟨H,hH⟩ := jordan_schoenflies_of_homeomorph hJ isJordanCurve_modelCurve h
  have himage : H '' range α = modelCurve := by
    ext z; constructor
    · rintro ⟨x,hx,rfl⟩
      rw [hH ⟨x,hx⟩]
      exact (h ⟨x,hx⟩).property
    · intro hz
      let u := h.symm ⟨z,hz⟩
      exact ⟨u.val,u.property,(hH u).trans (congrArg Subtype.val (h.apply_symm_apply ⟨z,hz⟩))⟩
  let G := hf.toOpenPartialHomeomorph f
  let F := G.symm.trans H.toOpenPartialHomeomorph
  have hFs : F.source = range f := by
    simp only [F,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.symm_source,
      G,IsOpenEmbedding.toOpenPartialHomeomorph_target,Homeomorph.toOpenPartialHomeomorph_source,
      Set.preimage_univ,Set.inter_univ]
  have hFt : F.target = univ := by
    simp only [F,OpenPartialHomeomorph.trans_target,OpenPartialHomeomorph.symm_target,
      G,IsOpenEmbedding.toOpenPartialHomeomorph_source,Homeomorph.toOpenPartialHomeomorph_target,
      Set.preimage_univ,Set.inter_univ]
  have hFrange : range f = {p}ᶜ := by
    ext x; constructor
    · rintro ⟨z,rfl⟩; exact (e.symm z).property
    · intro hx; exact ⟨e ⟨x,hx⟩,congrArg Subtype.val (e.symm_apply_apply _)⟩
  have hcsrc : c.image ⊆ F.source := by
    rw [hFs,hFrange]
    intro x hx; exact havoid x hx
  have hEval (z : Plane) : F (f z) = H z := by
    change H (G.symm (f z)) = H z
    rw [hf.toOpenPartialHomeomorph_left_inv]
  have hEvalα (t : Circle) : F (c.curve.map t) = H (α t) := by rw [← hfα t,hEval]
  have hcimage : F '' c.image = modelCurve := by
    change F '' range c.curve.map = _
    rw [← Set.range_comp,show F ∘ c.curve.map = H ∘ α from funext hEvalα,Set.range_comp,himage]
  exact ⟨p,hp,F,hFs.trans hFrange,hFt,hcsrc,hcimage⟩
end CurveComplex.HyperellipticModel
