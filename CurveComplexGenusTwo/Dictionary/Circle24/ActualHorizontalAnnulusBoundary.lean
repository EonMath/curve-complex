import CurveComplexGenusTwo.Dictionary.Circle24.ActualVerticalAnnulusBoundary
import CurveComplexGenusTwo.Dictionary.Circle24.ActualCircle24Corridor
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 15000000

/-- Coordinate interchange transports the actual construction, not merely a
hypothesis that a horizontal two-mark rectangle is annular. -/
theorem two_mark_rectangle_actual_annulus_horizontal_boundary
    (M : HyperellipticModel E S)
    (f : C(Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1,S)) (hf : IsEmbedding f)
    (p q : Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)
    (hmarks : ∀ z, f z ∈ M.cover.branch ↔ z=p ∨ z=q)
    (hp : p.val ∈ interior (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1))
    (hq : q.val ∈ interior (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1))
    (k : ℝ) (hk0 : -1<k) (hk1 : k<1) (hpk : p.val.2<k) (hkq : k<q.val.2) :
    ∃ H : Circle × Interval ≃ₜ M.cover.projection ⁻¹' Set.range f,
      Set.range (fun z : Circle => (H (z,0)).val) ∪
        Set.range (fun z : Circle => (H (z,1)).val)=
        M.cover.projection ⁻¹' (f '' {z | z.val ∈ frontier (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)}) := by
  let h : (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) ≃ₜ (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) :=
    { toFun := fun x => ⟨(x.val.2,x.val.1),⟨x.property.2,x.property.1⟩⟩
      invFun := fun x => ⟨(x.val.2,x.val.1),⟨x.property.2,x.property.1⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := ((continuous_snd.comp continuous_subtype_val).prodMk
        (continuous_fst.comp continuous_subtype_val)).subtype_mk _
      continuous_invFun := ((continuous_snd.comp continuous_subtype_val).prodMk
        (continuous_fst.comp continuous_subtype_val)).subtype_mk _ }
  have hinvol (z) : h (h z)=z := rfl
  let fs : C(Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1,S) := f.comp ⟨h,h.continuous⟩
  have hms (z) : fs z ∈ M.cover.branch ↔ z=h p ∨ z=h q := by
    change f (h z) ∈ M.cover.branch ↔ _
    rw [hmarks]
    constructor
    · rintro (hz | hz)
      · left; simpa only [hinvol] using congrArg h hz
      · right; simpa only [hinvol] using congrArg h hz
    · rintro (rfl | rfl) <;> simp [h]
  have hi (z : Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)
      (hz : z.val ∈ interior (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)) :
      (h z).val ∈ interior (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) := by
    simp only [interior_prod_eq,interior_Icc,mem_prod] at hz ⊢
    exact ⟨hz.2,hz.1⟩
  obtain ⟨H,hB⟩ := M.two_mark_rectangle_actual_annulus_vertical_boundary fs (hf.comp h.isEmbedding)
    (h p) (h q) hms (hi p hp) (hi q hq) k hk0 hk1 hpk hkq
  have hfull : Set.range fs=Set.range f := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩; exact ⟨h z,rfl⟩
    · rintro ⟨z,rfl⟩; exact ⟨h z,by simp [fs,h]⟩
  have hbound : fs '' {z | z.val ∈ frontier (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)}=
      f '' {z | z.val ∈ frontier (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)} := by
    have hfi (z : Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) :
        (h z).val ∈ frontier (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) ↔
          z.val ∈ frontier (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) := by
      simp only [frontier,closure_prod_eq,closure_Icc,interior_prod_eq,interior_Icc,
        mem_sdiff,mem_prod,mem_Icc,mem_Ioo]
      exact ⟨fun hz => ⟨⟨hz.1.2,hz.1.1⟩,fun hi => hz.2 ⟨hi.2,hi.1⟩⟩,
        fun hz => ⟨⟨hz.1.2,hz.1.1⟩,fun hi => hz.2 ⟨hi.2,hi.1⟩⟩⟩
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩; exact ⟨h z,(hfi z).mpr hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      refine ⟨h z,(hfi (h z)).mp ?_,?_⟩
      · change z.val ∈ frontier (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) at hz
        simpa only [hinvol] using hz
      · simp [fs,h]
  refine ⟨H.trans (Homeomorph.setCongr (congrArg (fun A => M.cover.projection ⁻¹' A) hfull)),?_⟩
  change Set.range (fun z : Circle => (H (z,0)).val) ∪ Set.range (fun z : Circle => (H (z,1)).val)=_
  rw [hB,hbound]


end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.two_mark_rectangle_actual_annulus_horizontal_boundary
