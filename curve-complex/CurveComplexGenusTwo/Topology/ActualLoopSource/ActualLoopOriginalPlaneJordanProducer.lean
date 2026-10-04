import CurveComplexGenusTwo.Dictionary.JordanEssentiality
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- An original loop supplies its own off-trace puncture and actual planar
Jordan parametrization, preserving the literal base and both original germs. -/
theorem actual_loop_original_plane_jordan_producer
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (ha : a.val.map 0=a.val.map 1) :
    ∃ p : S, ∃ hp : p ∉ a.val.image,
    ∃ γ : C(Interval,Plane),
      (∀ t, γ t=M.puncturedPlane p ⟨a.val.map t,by
        intro he; exact hp (he ▸ mem_range_self t)⟩) ∧
      IsJordanCurve (range γ) ∧
      (∀ s t, γ s=γ t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) := by
  obtain ⟨T⟩ := markedLoop_disc_decomposition_exists M a.val ha
  let D := T.discs 0
  let z : JordanClosedDisk := ⟨0,by simp⟩
  let p : S := (D.closedDisk z).val
  have hp : p ∉ a.val.image := by
    intro hh
    have hn := (D.disk_boundary z).mp hh
    change ‖(0:Plane)‖=1 at hn
    norm_num at hn
  let γ : C(Interval,Plane) := {
    toFun := fun t => M.puncturedPlane p ⟨a.val.map t,by
      intro he; exact hp (he ▸ mem_range_self t)⟩
    continuous_toFun := (M.puncturedPlane p).continuous.comp
      (a.val.continuous.subtype_mk (fun t => show a.val.map t≠p from fun he => hp (he ▸ mem_range_self t))) }
  have hcollision (s t : Interval) (he : γ s=γ t) :
      s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) := by
    exact a.val.injective_except_loop_closure s t
      (congrArg Subtype.val ((M.puncturedPlane p).injective he))
  let f : ℝ → Plane := γ ∘ projIcc 0 1 zero_le_one
  have hf : Continuous f := γ.continuous.comp continuous_projIcc
  have hfi (t : Interval) : f t=γ t := by simp [f,projIcc_of_mem]
  have hC : IsJordanCurve (range γ) := by
    refine ⟨f,⟨hf.continuousOn,?_,?_⟩,?_⟩
    · have he : γ 0=γ 1 := by
        apply (M.puncturedPlane p).injective.eq_iff.mpr
        exact Subtype.ext ha
      simpa [f,projIcc_of_mem] using he
    · intro s hs t ht he
      let si : Interval := ⟨s,hs.1,hs.2.le⟩
      let ti : Interval := ⟨t,ht.1,ht.2.le⟩
      have he' : γ si=γ ti := (hfi si).symm.trans (he.trans (hfi ti))
      rcases hcollision si ti he' with hh | hh | hh
      · exact congrArg Subtype.val hh
      · exact False.elim (ht.2.ne (congrArg Subtype.val hh.2))
      · exact False.elim (hs.2.ne (congrArg Subtype.val hh.1))
    · ext x
      constructor
      · rintro ⟨t,ht,rfl⟩; exact ⟨⟨t,ht⟩,(hfi ⟨t,ht⟩).symm⟩
      · rintro ⟨t,rfl⟩; exact ⟨t,t.property,hfi t⟩
  exact ⟨p,hp,γ,(fun _ => rfl),hC,hcollision⟩
end CurveComplex.HyperellipticModel
