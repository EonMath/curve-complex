import CurveComplexGenusTwo.Dictionary.Circle24.OneMarkRadialFilling
import CurveComplexGenusTwo.Dictionary.Circle24.DiscRecentering
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 5000000

/-- Fill the whole preimage of a one-mark disk with two actual radial strips.
The strips are produced and their union exhausts the entire closed cell, not
merely a neighborhood of its branch point. A chosen boundary anchor is kept. -/
theorem one_mark_disc_full_cell_filling
    (M : HyperellipticModel E S)
    (f : C(Metric.closedBall (0:Schoenflies.Plane) 1,S)) (hf : IsEmbedding f)
    (m : Metric.closedBall (0:Schoenflies.Plane) 1) (hm : ‖m.val‖ < 1)
    (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m)
    (β : C(Interval,Metric.closedBall (0:Schoenflies.Plane) 1))
    (hends : β 0 = β 1)
    (hcoll : ∀ s t, β s=β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hrange : Set.range β = {z | ‖z.val‖=1})
    (e : E) (he : M.cover.projection e = f (β 0)) :
    ∃ h : Metric.closedBall (0:Schoenflies.Plane) 1 ≃ₜ
        Metric.closedBall (0:Schoenflies.Plane) 1,
    ∃ L : C(Interval × Interval,E),
      h ⟨0,by simp⟩=m ∧ (∀ z, ‖z.val‖=1 → h z=z) ∧ L (1,0)=e ∧
      (∀ r t : Interval, M.cover.projection (L (r,t)) =
        f (h ⟨(r:ℝ) • (β t).val,by
          have hn : ‖(β t).val‖=1 := by
            have hh := Set.mem_range_self t (f := β)
            rw [hrange] at hh
            exact hh
          simpa only [Metric.mem_closedBall,dist_zero_right,norm_smul,
            Real.norm_eq_abs,abs_of_nonneg r.property.1,hn,mul_one] using r.property.2⟩)) ∧
      (∀ r : Interval, L (r,1)=M.cover.deck (L (r,0))) ∧
      (∀ t t' : Interval, L (0,t)=L (0,t')) ∧
      Set.range L ∪ M.cover.deck '' Set.range L =
        M.cover.projection ⁻¹' Set.range f := by
  obtain ⟨h,hexpl,hzero,hboundary⟩ := CurveComplex.closed_disc_recenter m hm
  let f' : C(Metric.closedBall (0:Schoenflies.Plane) 1,S) := f.comp ⟨h,h.continuous⟩
  let z₀ : Metric.closedBall (0:Schoenflies.Plane) 1 := ⟨0,by simp⟩
  have honly' (z) : f' z ∈ M.cover.branch ↔ z=z₀ := by
    change f (h z) ∈ M.cover.branch ↔ z=z₀
    rw [honly]
    exact ⟨fun hz => h.injective (hz.trans hzero.symm),fun hz => hz ▸ hzero⟩
  have hnorm (t : Interval) : ‖(β t).val‖=1 := by
    have hh := Set.mem_range_self t (f := β)
    rw [hrange] at hh
    exact hh
  have he' : M.cover.projection e = f' (β 0) := by
    change M.cover.projection e=f (h (β 0))
    rw [hboundary _ (hnorm 0)]
    exact he
  obtain ⟨Γ,hΓanchor,hΓπ,hΓedge,hΓzero⟩ :=
    M.one_mark_disc_anchored_radial_filling f' (hf.comp h.isEmbedding) z₀
      (by simp [z₀]) honly' β hends hcoll hrange e he'
  let L : C(Interval × Interval,E) :=
    Γ.comp ⟨fun z => ⟨(z.1.val,z.2.val),⟨z.1.property,z.2.property⟩⟩,
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  have hπ (r t : Interval) : M.cover.projection (L (r,t)) =
      f (h (discRadialContraction z₀ r (β t))) := hΓπ r t
  have hπval (r t : Interval) :
      (discRadialContraction z₀ r (β t)).val = (r:ℝ) • (β t).val := by
    simp [discRadialContraction,z₀]
  refine ⟨h,L,hzero,hboundary,hΓanchor,?_,hΓedge,hΓzero,?_⟩
  · intro r t
    convert hπ r t using 1
    apply congrArg (fun z => f (h z))
    exact Subtype.ext (hπval r t).symm
  · ext y
    constructor
    · rintro (⟨⟨r,t⟩,rfl⟩ | ⟨x,⟨⟨r,t⟩,rfl⟩,rfl⟩)
      · exact ⟨h (discRadialContraction z₀ r (β t)),(hπ r t).symm⟩
      · exact ⟨h (discRadialContraction z₀ r (β t)),
          ((M.cover.projection_deck (L (r,t))).trans (hπ r t)).symm⟩
    · rintro ⟨z,hz⟩
      let z' := h.symm z
      have hz'norm : ‖z'.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using z'.property
      let r : Interval := ⟨‖z'.val‖,⟨norm_nonneg _,hz'norm⟩⟩
      have hrad : ∃ t : Interval, discRadialContraction z₀ r (β t)=z' := by
        by_cases hz' : z'.val=0
        · refine ⟨0,?_⟩
          apply Subtype.ext
          simp [discRadialContraction,z₀,r,hz']
        · have hpos : 0 < ‖z'.val‖ := norm_pos_iff.mpr hz'
          let u : Metric.closedBall (0:Schoenflies.Plane) 1 :=
            ⟨‖z'.val‖⁻¹ • z'.val,by
              simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,
                Real.norm_eq_abs,abs_inv,abs_of_pos hpos,inv_mul_cancel₀ (ne_of_gt hpos),le_refl]⟩
          have hu : ‖u.val‖=1 := by
            simp [u,norm_smul,ne_of_gt hpos]
          have hurange : u ∈ Set.range β := by
            rw [hrange]
            exact hu
          obtain ⟨t,ht⟩ := hurange
          refine ⟨t,?_⟩
          apply Subtype.ext
          rw [hπval,ht]
          change ‖z'.val‖ • (‖z'.val‖⁻¹ • z'.val)=z'.val
          rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hpos),one_smul]
      obtain ⟨t,ht⟩ := hrad
      have hproj : M.cover.projection (L (r,t))=M.cover.projection y := by
        rw [hπ,ht]
        exact (congrArg f (h.apply_symm_apply z)).trans hz
      rcases (M.cover.fiber_pair (L (r,t)) y).mp hproj with hy | hy
      · exact Or.inl ⟨(r,t),hy.symm⟩
      · exact Or.inr ⟨L (r,t),⟨(r,t),rfl⟩,hy.symm⟩

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.one_mark_disc_full_cell_filling
