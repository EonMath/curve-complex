import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualPrescribedTargetGeometry
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualInternalSurfaceSides

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- The literal affine core parametrization covers the prescribed closed core. -/
theorem actualCoreParameter_range (α β : ℝ) (hα : 0 ≤ α) (hβ : β ≤ 1) (hαβ : α < β) :
    range (actualCoreParameter α β hα hβ hαβ.le) =
      {r : Interval | α ≤ r.val ∧ r.val ≤ β} := by
  ext r
  constructor
  · rintro ⟨t,rfl⟩
    dsimp [actualCoreParameter]
    constructor <;> nlinarith [t.property.1,t.property.2]
  · intro hr
    have hd : 0 < β-α := sub_pos.mpr hαβ
    let t : Interval := ⟨(r.val-α)/(β-α),div_nonneg (sub_nonneg.mpr hr.1) hd.le,
      (div_le_one hd).mpr (by linarith [hr.2])⟩
    refine ⟨t,?_⟩
    apply Subtype.ext
    dsimp [actualCoreParameter,t]
    field_simp
    ring

/-- Construct an actual compact fixed-anchor strip whose intersection with the
ENTIRE original anchor image is exactly its center, including LOOP anchors.
The source compact core is chosen away from the loop-closing endpoint mark.
No exact-axis chart, bank data or projection assumption is supplied. -/
theorem actual_anchor_interior_core_exact_strip
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (α β : ℝ) (hα : 0 < α) (hβ : β < 1) (hαβ : α < β) :
    ∃ B : Interval × Set.Icc (-1:ℝ) 1 → S,
      IsEmbedding B ∧
      (∀ t, B (t,⟨0,by norm_num⟩) =
        anchor.val.map (actualCoreParameter α β hα.le hβ.le hαβ.le t)) ∧
      (∀ z, B z ∉ M.cover.branch) ∧
      (∀ z, B z ∈ anchor.val.image ↔ z.2.val = 0) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let := (actualSphereSmoothAtlas M).charts
  let a := α/2
  let b := (β+1)/2
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : b < 1 := by dsimp [b]; linarith
  have hab : a < b := by dsimp [a,b]; linarith
  have haα : a < α := by dsimp [a]; linarith
  have hβb : β < b := by dsimp [b]; linarith
  let c : C(Interval,S) := ⟨anchor.val.map ∘ actualCoreParameter a b ha.le hb.le hab.le,
    anchor.val.continuous.comp (actualCoreParameter_continuous _ _ _ _ _)⟩
  have hcM : range c ⊆ (M.cover.branch : Set S)ᶜ := by
    rintro z ⟨t,rfl⟩ hm
    have hbounds : 0 < (actualCoreParameter a b ha.le hb.le hab.le t).val ∧
        (actualCoreParameter a b ha.le hb.le hab.le t).val < 1 := by
      dsimp [actualCoreParameter]
      constructor <;> nlinarith [t.property.1,t.property.2]
    rcases anchor.val.marked_only_at_ends _ hm with he | he
    · have he := congrArg Subtype.val he
      change (actualCoreParameter a b ha.le hb.le hab.le t).val=0 at he
      linarith [hbounds.1]
    · have he := congrArg Subtype.val he
      change (actualCoreParameter a b ha.le hb.le hab.le t).val=1 at he
      linarith [hbounds.2]
  obtain ⟨E,hE,hEc,hEM⟩ := CurveComplex.source_whole_embedded_arc_strip c
    (actual_marked_interior_core_embedded M anchor a b ha hb hab)
    (M.cover.branch : Set S)ᶜ M.cover.branch.finite_toSet.isClosed.isOpen_compl hcM
  let γ := (α-a)/(b-a)
  let η := (β-a)/(b-a)
  have hba : 0 < b-a := sub_pos.mpr hab
  have hγ : 0 < γ := div_pos (sub_pos.mpr haα) hba
  have hη : η < 1 := (div_lt_one hba).mpr (by linarith)
  have hγη : γ < η := div_lt_div_of_pos_right (by linarith) hba
  let q := actualCoreParameter γ η hγ.le hη.le hγη.le
  have hqcenter (t : Interval) :
      actualCoreParameter a b ha.le hb.le hab.le (q t) =
        actualCoreParameter α β hα.le hβ.le hαβ.le t := by
    apply Subtype.ext
    dsimp [q,actualCoreParameter,γ,η]
    field_simp
    ring
  have hqi : Function.Injective q := by
    intro t u he
    have hr := congrArg Subtype.val he
    dsimp [q,actualCoreParameter] at hr
    apply Subtype.ext
    nlinarith
  let R : Interval × Icc (-1:ℝ) 1 → S := fun z => E (q z.1,z.2)
  have hR : IsEmbedding R := by
    have hcR : Continuous R := hE.continuous.comp
      ((actualCoreParameter_continuous _ _ _ _ _).comp continuous_fst |>.prodMk continuous_snd)
    have hiR : Function.Injective R := by
      intro z w he
      have heq := hE.injective he
      exact Prod.ext (hqi (congrArg Prod.fst heq)) (by simpa using congrArg Prod.snd heq)
    exact (hcR.isClosedEmbedding hiR).isEmbedding
  have hRc (t : Interval) : R (t,⟨0,by norm_num⟩) =
      anchor.val.map (actualCoreParameter α β hα.le hβ.le hαβ.le t) := by
    change E (q t,⟨0,by norm_num⟩) = _
    rw [hEc]
    change anchor.val.map (actualCoreParameter a b ha.le hb.le hab.le (q t)) = _
    rw [hqcenter]
  let Tail : Set S := anchor.val.map '' {r : Interval | r.val ≤ a ∨ b ≤ r.val}
  have hTail : IsClosed Tail :=
    (IsCompact.image (by
      apply IsClosed.isCompact
      exact (isClosed_Iic.preimage continuous_subtype_val).union
        (isClosed_Ici.preimage continuous_subtype_val)) anchor.val.continuous).isClosed
  have hcenterTail (t : Interval) : R (t,⟨0,by norm_num⟩) ∉ Tail := by
    rw [hRc]
    rintro ⟨r,hr,he⟩
    let s := actualCoreParameter α β hα.le hβ.le hαβ.le t
    have hs : α ≤ s.val ∧ s.val ≤ β := by
      have hh := actualCoreParameter_range α β hα.le hβ.le hαβ
      have hm : s ∈ range (actualCoreParameter α β hα.le hβ.le hαβ.le) := mem_range_self t
      rw [hh] at hm
      exact hm
    rcases anchor.val.injective_except_loop_closure r s he with hh | hh | hh
    · subst r
      rcases hr with hr | hr <;> linarith
    · have he := congrArg Subtype.val hh.2
      change s.val=1 at he
      linarith [hs.2]
    · have he := congrArg Subtype.val hh.2
      change s.val=0 at he
      linarith [hs.1]
  obtain ⟨ρ,hρ,N,hN,hNT,hNR,hNc⟩ := CurveComplex.source_shrink_embedded_strip_in_open
    R hR Tailᶜ hTail.isOpen_compl hcenterTail
  refine ⟨N,hN,fun t => (hNc t).trans (hRc t),?_,?_⟩
  · intro z
    rw [hNR]
    exact hEM (mem_range_self _)
  · intro z
    constructor
    · rintro ⟨r,hr⟩
      have hrTail : ¬ (r.val ≤ a ∨ b ≤ r.val) := by
        intro h
        exact hNT (mem_range_self z) ⟨r,h,hr⟩
      have hrbounds : a ≤ r.val ∧ r.val ≤ b := by
        push Not at hrTail
        exact ⟨hrTail.1.le,hrTail.2.le⟩
      have hrRange : r ∈ range (actualCoreParameter a b ha.le hb.le hab.le) := by
        rw [actualCoreParameter_range a b ha.le hb.le hab]
        exact hrbounds
      obtain ⟨t,ht⟩ := hrRange
      have he : E (t,⟨0,by norm_num⟩) = N z := by
        rw [hEc]
        change anchor.val.map (actualCoreParameter a b ha.le hb.le hab.le t) = _
        rw [ht]
        exact hr
      rw [hNR] at he
      have heq := congrArg (fun w : Interval × Icc (-1:ℝ) 1 => w.2.val) (hE.injective he)
      change 0 = ρ*z.2.val at heq
      exact (mul_eq_zero.mp heq.symm).resolve_left hρ.1.ne'
    · intro hz
      have hzz : z.2 = (⟨0,by norm_num⟩ : Icc (-1:ℝ) 1) := Subtype.ext hz
      rw [← Prod.eta z,hzz,hNc,hRc]
      exact mem_range_self _

end
end CurveComplex.HyperellipticModel.ArcSurgery
