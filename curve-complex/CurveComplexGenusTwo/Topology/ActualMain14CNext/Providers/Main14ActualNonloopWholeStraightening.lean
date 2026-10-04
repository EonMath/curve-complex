import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Topology.CompletedJordan
import CurveComplexGenusTwo.Topology.FrontierCircle.BandStraightening
import CurveComplexGenusTwo.Intersection.ChartedArcCertificateInput

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 4000000

/-- Construct an actual chart straightening the whole original nonloop arc, including both endpoints. No chart or straightening certificate is supplied. -/
theorem actual_nonloop_whole_arc_straightening
    (M : HyperellipticModel E S) (a : NonLoopArc M) :
    ∃ p : S, p ∈ M.cover.branch ∧ ∃ F : OpenPartialHomeomorph S Plane,
      F.source = {p}ᶜ ∧ F.target = univ ∧ a.image ⊆ F.source ∧ F '' a.image = sideTop := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨p,hp,hpa⟩ := a.exists_marked_puncture
  have havoid (x : S) (hx : x ∈ a.image) : x ≠ p := by
    intro he; exact hpa (he ▸ hx)
  let e := M.puncturedPlane p
  let f : Plane → S := fun z => (e.symm z).val
  have hf : IsOpenEmbedding f :=
    isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
  let α : C(Interval,Plane) := ⟨fun t => e ⟨a.val.map t,havoid _ (Set.mem_range_self t)⟩,
    e.continuous.comp (a.val.continuous.subtype_mk _)⟩
  have hfα (t : Interval) : f (α t) = a.val.map t := congrArg Subtype.val (e.symm_apply_apply _)
  have hα : IsEmbedding α := (α.continuous.isClosedEmbedding (by
    intro t u he
    apply a.injective
    exact (hfα t).symm.trans ((congrArg f he).trans (hfα u)))).isEmbedding
  let fc : ℝ → Plane := α ∘ Set.projIcc 0 1 zero_le_one
  have hfc : Continuous fc := α.continuous.comp continuous_projIcc
  have hfcval (t : Interval) : fc t = α t := by
    simp [fc,Set.projIcc_of_mem zero_le_one t.property]
  have hfi : InjOn fc (Set.Icc (0:ℝ) 1) := by
    intro t ht u hu he
    have he' : α ⟨t,ht⟩ = α ⟨u,hu⟩ := by simpa only [← hfcval] using he
    exact congrArg Subtype.val (hα.injective he')
  have hfcim : fc '' Set.Icc (0:ℝ) 1 = Set.range α := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,ht⟩,by simp [fc,Set.projIcc_of_mem zero_le_one ht]⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t,t.property,hfcval t⟩
  have hP : IsArcBetween (Set.range α) (α 0) (α 1) :=
    ⟨fc,hfc.continuousOn,hfi,hfcim,hfcval 0,hfcval 1⟩
  obtain ⟨A,hA,hmeet,hJ⟩ := exists_jordan_completion_of_isArcBetween hP
  obtain ⟨H,himage⟩ := exists_ambient_straightening_to_top hA hP hmeet hJ
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
  have hcsrc : a.image ⊆ F.source := by
    rw [hFs,hFrange]
    intro x hx; exact havoid x hx
  have hEval (z : Plane) : F (f z) = H z := by
    change H (G.symm (f z)) = H z
    rw [hf.toOpenPartialHomeomorph_left_inv]
  have hEvalα (t : Interval) : F (a.val.map t) = H (α t) := by rw [← hfα t,hEval]
  have hcimage : F '' a.image = sideTop := by
    change F '' range a.val.map = _
    rw [← Set.range_comp,show F ∘ a.val.map = H ∘ α from funext hEvalα,Set.range_comp,himage]
  exact ⟨p,hp,F,hFs.trans hFrange,hFt,hcsrc,hcimage⟩
end CurveComplex.HyperellipticModel
