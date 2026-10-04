import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualSourceTargetWholeStrips
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualPrescribedBigonFinalAlignment

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def actualCoreParameter (α β : ℝ) (hα : 0 ≤ α) (hβ : β ≤ 1) (hαβ : α ≤ β)
    (t : Interval) : Interval :=
  ⟨(1-t.val)*α+t.val*β,by
    constructor
    · nlinarith [t.property.1,t.property.2]
    · nlinarith [t.property.1,t.property.2]⟩

theorem actualCoreParameter_continuous (α β : ℝ) (hα : 0 ≤ α) (hβ : β ≤ 1)
    (hαβ : α ≤ β) : Continuous (actualCoreParameter α β hα hβ hαβ) := by
  unfold actualCoreParameter
  fun_prop

/-- Strictly interior source cores are genuinely embedded, including cores of
LOOP arcs. Both exceptional loop-closing alternatives are excluded by bounds. -/
theorem actual_marked_interior_core_embedded
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (α β : ℝ) (hα : 0 < α) (hβ : β < 1) (hαβ : α < β) :
    IsEmbedding (a.val.map ∘ actualCoreParameter α β hα.le hβ.le hαβ.le) := by
  let : T2Space S := M.sphere.symm.t2Space
  have hc : Continuous (a.val.map ∘ actualCoreParameter α β hα.le hβ.le hαβ.le) :=
    a.val.continuous.comp (actualCoreParameter_continuous _ _ _ _ _)
  have hb (t : Interval) : 0 < (actualCoreParameter α β hα.le hβ.le hαβ.le t).val ∧
      (actualCoreParameter α β hα.le hβ.le hαβ.le t).val < 1 := by
    dsimp [actualCoreParameter]
    constructor <;> nlinarith [t.property.1,t.property.2]
  have hi : Function.Injective (a.val.map ∘ actualCoreParameter α β hα.le hβ.le hαβ.le) := by
    intro t u he
    rcases a.val.injective_except_loop_closure _ _ he with hh | hh | hh
    · have hr := congrArg Subtype.val hh
      dsimp [actualCoreParameter] at hr
      apply Subtype.ext
      nlinarith
    · have hr := congrArg Subtype.val hh.1
      have hbt := (hb t).1
      change (actualCoreParameter α β hα.le hβ.le hαβ.le t).val = 0 at hr
      linarith
    · have hr := congrArg Subtype.val hh.1
      have hbt := (hb t).2
      change (actualCoreParameter α β hα.le hβ.le hαβ.le t).val = 1 at hr
      linarith
  exact (hc.isClosedEmbedding hi).isEmbedding

/-- From an actual target interior point in any open region, CHOOSE the literal
parameter endpoints of a compact embedded target core and produce its entire
strip in that region. No core endpoints, chart, collar or replacement move are
supplied. This is valid even when the actual target representative is a loop. -/
theorem actual_target_point_produces_local_core_strip
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (r : Interval) (hr : 0 < r.val ∧ r.val < 1)
    (U : Set S) (hU : IsOpen U) (haU : a.val.map r ∈ U) :
    ∃ α β : ℝ, ∃ hα : 0 < α, ∃ hβ : β < 1, ∃ hαβ : α < β,
      α < r.val ∧ r.val < β ∧
      ∃ B : Interval × Set.Icc (-1:ℝ) 1 → S,
        IsEmbedding B ∧
        (∀ t, B (t,⟨0,by norm_num⟩) =
          a.val.map (actualCoreParameter α β hα.le hβ.le hαβ.le t)) ∧
        range B ⊆ U ∧ a.val.map r ∈ range B := by
  let : T2Space S := M.sphere.symm.t2Space
  let := (actualSphereSmoothAtlas M).charts
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
    ((hU.preimage a.val.continuous).mem_nhds haU)
  let ε := min (δ/2) (min (r.val/2) ((1-r.val)/2))
  have hε : 0 < ε := lt_min (half_pos hδ) (lt_min (half_pos hr.1) (by linarith))
  have hεδ : ε < δ := by have h := min_le_left (δ/2) (min (r.val/2) ((1-r.val)/2)); dsimp [ε]; linarith
  have hεr : ε ≤ r.val/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ (1-r.val)/2 := (min_le_right _ _).trans (min_le_right _ _)
  let α := r.val-ε
  let β := r.val+ε
  have hα : 0 < α := by dsimp [α]; linarith
  have hβ : β < 1 := by dsimp [β]; linarith
  have hαβ : α < β := by dsimp [α,β]; linarith
  let c : C(Interval,S) := ⟨a.val.map ∘ actualCoreParameter α β hα.le hβ.le hαβ.le,
    a.val.continuous.comp (actualCoreParameter_continuous _ _ _ _ _)⟩
  have hcU : range c ⊆ U := by
    rintro z ⟨t,rfl⟩
    apply hball
    rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq,abs_lt]
    dsimp [actualCoreParameter,α,β,c]
    constructor <;> nlinarith [t.property.1,t.property.2]
  obtain ⟨B,hB,hcenter,hBU⟩ := CurveComplex.source_whole_embedded_arc_strip c
    (actual_marked_interior_core_embedded M a α β hα hβ hαβ) U hU hcU
  refine ⟨α,β,hα,hβ,hαβ,by dsimp [α]; linarith,by dsimp [β]; linarith,
    B,hB,hcenter,hBU,?_⟩
  refine ⟨((⟨(1:ℝ)/2,by norm_num⟩:Interval),⟨0,by norm_num⟩),?_⟩
  rw [hcenter]
  change a.val.map (actualCoreParameter α β hα.le hβ.le hαβ.le _) = a.val.map r
  congr 1
  apply Subtype.ext
  dsimp [actualCoreParameter,α,β]
  ring

/-- A target point away from the anchor PRODUCES a local core strip avoiding
the marks, the whole stationary anchor, and EVERY other prescribed Q arc. -/
theorem actual_target_position_complementary_core_strip
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (hF : IsArcSimplex M F)
    (Q : FinitePosition M anchor F) (v : {v // v ∈ F})
    (r : Interval) (hr : 0 < r.val ∧ r.val < 1)
    (hra : (Q.rep v).val.map r ∉ anchor.val.image) :
    ∃ α β : ℝ, ∃ hα : 0 < α, ∃ hβ : β < 1, ∃ hαβ : α < β,
      α < r.val ∧ r.val < β ∧
      ∃ B : Interval × Set.Icc (-1:ℝ) 1 → S,
        IsEmbedding B ∧
        (∀ t, B (t,⟨0,by norm_num⟩) =
          (Q.rep v).val.map (actualCoreParameter α β hα.le hβ.le hαβ.le t)) ∧
        (∀ z ∈ range B, z ∉ M.cover.branch ∧ z ∉ anchor.val.image ∧
          ∀ w, w ≠ v → z ∉ (Q.rep w).val.image) ∧ (Q.rep v).val.map r ∈ range B := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let others : Set S := ⋃ w : {w // w ∈ F}, ⋃ (_ : w ≠ v), (Q.rep w).val.image
  have hothers : IsCompact others := isCompact_iUnion (fun w =>
    isCompact_iUnion (fun _ => isCompact_range (Q.rep w).val.continuous))
  let U : Set S := ((M.cover.branch : Set S) ∪ anchor.val.image ∪ others)ᶜ
  have hU : IsOpen U :=
    ((M.cover.branch.finite_toSet.isClosed.union
      (isCompact_range anchor.val.continuous).isClosed).union hothers.isClosed).isOpen_compl
  have hm : (Q.rep v).val.map r ∉ M.cover.branch := by
    intro hm
    rcases (Q.rep v).val.marked_only_at_ends r hm with hh | hh
    · have hh := congrArg Subtype.val hh; change r.val=0 at hh; linarith [hr.1]
    · have hh := congrArg Subtype.val hh; change r.val=1 at hh; linarith [hr.2]
  have hro : (Q.rep v).val.map r ∉ others := by
    intro hz
    obtain ⟨w,hw⟩ := mem_iUnion.mp hz
    obtain ⟨hwv,hzw⟩ := mem_iUnion.mp hw
    exact disjoint_left.mp (actual_position_family_disjoint M anchor F hF Q v w hwv.symm)
      ⟨mem_range_self r,hm⟩ ⟨hzw,hm⟩
  have hrU : (Q.rep v).val.map r ∈ U := by
    rintro ((hm' | ha) | ho)
    · exact hm hm'
    · exact hra ha
    · exact hro ho
  obtain ⟨α,β,hα,hβ,hαβ,har,hrb,B,hB,hcenter,hBU,hrB⟩ :=
    actual_target_point_produces_local_core_strip M (Q.rep v) r hr U hU hrU
  refine ⟨α,β,hα,hβ,hαβ,har,hrb,B,hB,hcenter,?_,hrB⟩
  intro z hz
  have hzU := hBU hz
  refine ⟨fun hm => hzU (Or.inl (Or.inl hm)),fun ha => hzU (Or.inl (Or.inr ha)),?_⟩
  intro w hw hzW
  exact hzU (Or.inr (mem_iUnion.mpr ⟨w,mem_iUnion.mpr ⟨hw,hzW⟩⟩))

end
end CurveComplex.HyperellipticModel.ArcSurgery
