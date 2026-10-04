import CurveComplexGenusTwo.Dictionary.Circle24.ActualHorizontalAnnulusBoundary
import CurveComplexGenusTwo.Dictionary.Circle24.ClosedTwoMarkSideAdapter
import CurveComplexGenusTwo.Dictionary.Circle24.RectangleDiskLift
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 15000000

theorem two_mark_square_boundary_annulus
    (M : HyperellipticModel E S) (a : Circle24 M)
    (f : C(Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1,S)) (hf : IsEmbedding f)
    (houter : f '' {z | z.val ∈ frontier (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)}=a.val.image)
    (hcount : (by classical exact (M.cover.branch.filter (· ∈ f '' {z | z.val ∈ interior (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)})).card=2)) :
    ∃ H : Circle × Interval ≃ₜ M.cover.projection ⁻¹' Set.range f,
      Set.range (fun z : Circle => (H (z,0)).val) ∪ Set.range (fun z : Circle => (H (z,1)).val)=M.cover.projection ⁻¹' a.val.image := by
  have hav (z) (hz : z.val ∈ frontier (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)) : f z ∉ M.cover.branch := by
    intro hb
    have himg : f z ∈ a.val.image := houter ▸ ⟨z,hz,rfl⟩
    exact Set.disjoint_left.mp a.val.avoids_branch himg hb
  obtain ⟨l,r,b,t,hlr,hbt,hsub,hshape,p,q,hmarks,hsep,havoid⟩ :=
    M.cover.two_mark_square_has_branch_free_corridor f hf hav hcount
  have h : ∃ H : Circle × Interval ≃ₜ M.cover.projection ⁻¹' Set.range f,
      Set.range (fun z : Circle => (H (z,0)).val) ∪ Set.range (fun z : Circle => (H (z,1)).val)=
        M.cover.projection ⁻¹' (f '' {z | z.val ∈ frontier (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)}) := by
    have hi (z : Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)
        (hz : f z ∈ M.cover.branch) :
        z.val ∈ interior (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) := by
      by_contra hn
      have hclosed : IsClosed (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) := isClosed_Icc.prod isClosed_Icc
      have hfront : z.val ∈ frontier (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) :=
        ⟨hclosed.closure_eq.symm ▸ z.property,hn⟩
      have himg : f z ∈ a.val.image := houter ▸ ⟨z,hfront,rfl⟩
      exact Set.disjoint_left.mp a.val.avoids_branch himg hz
    have hp := hi p ((hmarks p).mpr (Or.inl rfl))
    have hq := hi q ((hmarks q).mpr (Or.inr rfl))
  
    rcases hshape with ⟨hb,ht,hl,hr⟩ | ⟨hl,hr,hb,ht⟩
    · subst b; subst t
      have hv : (p.val.1<l ∧ r<q.val.1) ∨ (q.val.1<l ∧ r<p.val.1) := by
        rcases hsep with hv | hh
        · exact hv
        · rcases hh with hh | hh
          · exact False.elim ((not_lt_of_ge p.property.2.1) hh.1)
          · exact False.elim ((not_lt_of_ge q.property.2.1) hh.1)
      rcases hv with hv | hv
      · exact M.two_mark_rectangle_actual_annulus_vertical_boundary f hf p q hmarks hp hq ((l+r)/2)
          (by linarith) (by linarith) (by linarith [hv.1]) (by linarith [hv.2])
      · exact M.two_mark_rectangle_actual_annulus_vertical_boundary f hf q p
          (fun z => (hmarks z).trans or_comm) hq hp ((l+r)/2)
          (by linarith) (by linarith) (by linarith [hv.1]) (by linarith [hv.2])
    · subst l; subst r
      have hv : (p.val.2<b ∧ t<q.val.2) ∨ (q.val.2<b ∧ t<p.val.2) := by
        rcases hsep with hh | hv
        · rcases hh with hh | hh
          · exact False.elim ((not_lt_of_ge p.property.1.1) hh.1)
          · exact False.elim ((not_lt_of_ge q.property.1.1) hh.1)
        · exact hv
      rcases hv with hv | hv
      · exact M.two_mark_rectangle_actual_annulus_horizontal_boundary f hf p q hmarks hp hq ((b+t)/2)
          (by linarith) (by linarith) (by linarith [hv.1]) (by linarith [hv.2])
      · exact M.two_mark_rectangle_actual_annulus_horizontal_boundary f hf q p
          (fun z => (hmarks z).trans or_comm) hq hp ((b+t)/2)
          (by linarith) (by linarith) (by linarith [hv.1]) (by linarith [hv.2])
  
  simpa only [houter] using h


/-- Exact disk-lift annulus interface for any given closed two-mark disk side.
Its disk witness is not used as an unproved boundary-preserving map. -/
theorem circle24_disk_lift_annulus_given_closed_set
    (M : HyperellipticModel E S) (a : Circle24 M) (D : Set S)
    (hD : IsClosed D) (hfront : frontier D=a.val.image)
    (hcount : (by classical exact (M.cover.branch.filter (· ∈ interior D)).card=2)) :
    ∃ H : Circle × Interval ≃ₜ M.cover.projection ⁻¹' D,
      Set.range (fun z : Circle => (H (z,0)).val) ∪
        Set.range (fun z : Circle => (H (z,1)).val)=M.cover.projection ⁻¹' a.val.image := by
  classical
  obtain ⟨U,d,hU,hUc,hUi,hcl,hdb,hdi⟩ := M.arbitrary_two_mark_closed_side_adapter a D hD hfront hcount
  obtain ⟨h,hi,hb⟩ := closed_rectangle_disk_chart (-1) 1 (-1) 1 (by norm_num) (by norm_num)
  let f : C(Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1,S) :=
    ⟨fun z => (d (h.symm z)).val,continuous_subtype_val.comp (d.continuous.comp h.symm.continuous)⟩
  have hf : IsEmbedding f := Topology.IsEmbedding.subtypeVal.comp (d.isEmbedding.comp h.symm.isEmbedding)
  have hfr : Set.range f=D := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩; exact (d _).property
    · intro hy
      refine ⟨h (d.symm ⟨y,hy⟩),?_⟩
      change (d (h.symm (h (d.symm ⟨y,hy⟩)))).val=y
      rw [h.symm_apply_apply,d.apply_symm_apply]
  have hboundary (z) : f z ∈ a.val.image ↔ z.val ∈ frontier (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) := by
    change (d (h.symm z)).val ∈ a.val.image ↔ _
    rw [hdb,← hb,h.apply_symm_apply]
  have houter : f '' {z | z.val ∈ frontier (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)}=a.val.image := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩; exact (hboundary z).mpr hz
    · intro hy
      have hyD : y ∈ D := hcl.symm ▸ Or.inr hy
      obtain ⟨z,hz⟩ := hfr.symm ▸ hyD
      exact ⟨z,(hboundary z).mp (hz ▸ hy),hz⟩
  have hir : f '' {z | z.val ∈ interior (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)}=interior D := by
    rw [← hUi]
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      change z.val ∈ interior (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) at hz
      apply (hdi _).mpr
      exact (hi _).mp (by simpa only [h.apply_symm_apply] using hz)
    · intro hy
      have hyD : y ∈ D := hcl.symm ▸ Or.inl hy
      let z := h (d.symm ⟨y,hyD⟩)
      refine ⟨z,?_,?_⟩
      · exact (hi _).mpr ((hdi _).mp (by simpa only [d.apply_symm_apply] using hy))
      · change (d (h.symm (h (d.symm ⟨y,hyD⟩)))).val=y
        rw [h.symm_apply_apply,d.apply_symm_apply]
  have hc : (M.cover.branch.filter (· ∈ f '' {z | z.val ∈ interior (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)})).card=2 := by
    rw [hir]; exact hcount
  obtain ⟨H,hB⟩ := M.two_mark_square_boundary_annulus a f hf houter hc
  exact ⟨H.trans (Homeomorph.setCongr (congrArg (fun A => M.cover.projection ⁻¹' A) hfr)),hB⟩


/-- The exact original interface, expressed through the given disk's fields.
The finite-set ncard condition is converted without changing its meaning. -/
theorem circle24_disk_lift_annulus_exact_fields
    (M : HyperellipticModel E S) (a : Circle24 M) (D : Set S)
    (d : Metric.closedBall (0:Schoenflies.Plane) 1 ≃ₜ D)
    (hfront : frontier D=a.val.image)
    (hcount : Set.ncard ((M.cover.branch : Set S) ∩ interior D)=2) :
    ∃ H : Circle × Interval ≃ₜ M.cover.projection ⁻¹' D,
      Set.range (fun z : Circle => (H (z,0)).val) ∪
        Set.range (fun z : Circle => (H (z,1)).val)=M.cover.projection ⁻¹' a.val.image := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  have hcompact : IsCompact D := by
    have hc := isCompact_range (continuous_subtype_val.comp d.continuous)
    have he : Set.range (fun z => (d z).val)=D := by
      ext y
      constructor
      · rintro ⟨z,rfl⟩; exact (d z).property
      · intro hy; exact ⟨d.symm ⟨y,hy⟩,congrArg Subtype.val (d.apply_symm_apply ⟨y,hy⟩)⟩
    change IsCompact (Set.range (fun z => (d z).val)) at hc
    rwa [he] at hc
  have hc : (M.cover.branch.filter (· ∈ interior D)).card=2 := by
    have he : ((M.cover.branch.filter (· ∈ interior D) : Finset S) : Set S)=
        (M.cover.branch : Set S) ∩ interior D := by ext y; simp
    rw [← Set.ncard_coe_finset,he]
    exact hcount
  exact M.circle24_disk_lift_annulus_given_closed_set a D hcompact.isClosed hfront hc

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.two_mark_square_boundary_annulus

#print axioms CurveComplex.HyperellipticModel.circle24_disk_lift_annulus_given_closed_set

#print axioms CurveComplex.HyperellipticModel.circle24_disk_lift_annulus_exact_fields
