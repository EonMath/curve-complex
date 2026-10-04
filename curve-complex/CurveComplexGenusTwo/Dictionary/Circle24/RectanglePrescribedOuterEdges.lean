import CurveComplexGenusTwo.Dictionary.Circle24.ActualPrescribedOuterEdges
import CurveComplexGenusTwo.Dictionary.Circle24.RectangleDiskLift
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 9000000

/-- A complete rectangular one-mark cell, with both seam charts tied to the
actual prescribed boundary lift, through the whole polar filling. -/
theorem one_mark_rectangle_square_prescribed_outer_edges
    (M : HyperellipticModel E S)
    (a b c d : ℝ) (hab : a<b) (hcd : c<d)
    (f : C(Icc a b ×ˢ Icc c d,S)) (hf : IsEmbedding f)
    (m : Icc a b ×ˢ Icc c d) (hm : m.val ∈ interior (Icc a b ×ˢ Icc c d))
    (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m)
    (β : C(Interval,Icc a b ×ˢ Icc c d))
    (hends : β 0=β 1)
    (hcoll : ∀ s t, β s=β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hrange : Set.range β={z | z.val ∈ frontier (Icc a b ×ˢ Icc c d)})
    (η : C(Interval,E)) (hηπ : ∀ t, M.cover.projection (η t)=f (β (halfInterval t))) :
    ∃ D : (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) ≃ₜ M.cover.projection ⁻¹' Set.range f,
      (∀ t : Interval, (D (squareLeftSeam t)).val=η t) ∧
      (∀ t : Interval, (D (squareRightSeam t)).val=M.cover.deck (η t)) ∧
      ∃ γ : C(Interval,E), (∀ t, M.cover.projection (γ t)=f (β t)) ∧
        (∀ t, (D (unitSquareRaw (t,1))).val=γ (lateInterval t)) ∧
        (∀ t, (D (unitSquareRaw (unitInterval.symm t,0))).val=M.cover.deck (γ (lateInterval t))) := by
  obtain ⟨h,hi,hb⟩ := closed_rectangle_disk_chart a b c d hab hcd
  let fd : C(Metric.closedBall (0:Schoenflies.Plane) 1,S) := f.comp ⟨h,h.continuous⟩
  let md := h.symm m
  let bd : C(Interval,Metric.closedBall (0:Schoenflies.Plane) 1) :=
    ⟨fun t => h.symm (β t),h.symm.continuous.comp β.continuous⟩
  have hmd : ‖md.val‖<1 := (hi md).mp (by simpa only [md,h.apply_symm_apply] using hm)
  have hmarks (z) : fd z ∈ M.cover.branch ↔ z=md := by
    change f (h z) ∈ M.cover.branch ↔ z=h.symm m
    rw [honly]
    exact ⟨fun hz => h.injective (hz.trans (h.apply_symm_apply m).symm),
      fun hz => by rw [hz,h.apply_symm_apply]⟩
  have bcoll (s t) (he : bd s=bd t) := hcoll s t (h.symm.injective he)
  have brange : Set.range bd={z | ‖z.val‖=1} := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      apply (hb _).mp
      change (h (h.symm (β t))).val ∈ frontier (Icc a b ×ˢ Icc c d)
      rw [h.apply_symm_apply]
      have hh := Set.mem_range_self t (f:=β)
      rw [hrange] at hh
      exact hh
    · intro hz
      have hmemb : h z ∈ Set.range β := by rw [hrange]; exact (hb z).mpr hz
      obtain ⟨t,ht⟩ := hmemb
      exact ⟨t,by change h.symm (β t)=z; rw [ht,h.symm_apply_apply]⟩
  have betapi (t) : M.cover.projection (η t)=fd (bd (halfInterval t)) := by
    change M.cover.projection (η t)=f (h (h.symm (β (halfInterval t))))
    rw [h.apply_symm_apply]
    exact hηπ t
  obtain ⟨D,hL,hR,γ,hγπ,hTop,hBottom⟩ := M.one_mark_disc_square_prescribed_outer_edges fd (hf.comp h.isEmbedding)
    md hmd hmarks bd (congrArg h.symm hends) bcoll brange η betapi
  have hfr : Set.range fd=Set.range f := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩; exact ⟨h z,rfl⟩
    · rintro ⟨z,rfl⟩; exact ⟨h.symm z,by change f (h (h.symm z))=f z; rw [h.apply_symm_apply]⟩
  refine ⟨D.trans (Homeomorph.setCongr (congrArg (fun A => M.cover.projection ⁻¹' A) hfr)),hL,hR,γ,?_,hTop,hBottom⟩
  intro t
  have hh := hγπ t
  change M.cover.projection (γ t)=f (h (h.symm (β t))) at hh
  simpa only [h.apply_symm_apply] using hh

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.one_mark_rectangle_square_prescribed_outer_edges
