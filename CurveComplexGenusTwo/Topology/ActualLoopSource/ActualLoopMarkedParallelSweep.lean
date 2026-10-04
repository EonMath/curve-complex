import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLoopMarkedClosedDiskCollar
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLoopParallelRadialGeometry

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- The ORIGINAL loop constructs a genuine marked parallel sweep using an
actual Schoenflies boundary collar. Loop closure and its literal marked base
are retained; terminal interior is off the entire original loop trace. -/
theorem actual_loop_marked_parallel_sweep
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1) :
    ∃ F : C(Interval × Interval,S),
      (∀ t, F (0,t)=a.val.map t) ∧
      (∀ τ s t, F (τ,s)=F (τ,t) →
        s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
      (∀ τ, F (τ,0)=a.val.map 0 ∧ F (τ,1)=a.val.map 1) ∧
      (∀ τ t, t≠0 → t≠1 → F (τ,t) ∉ (M.cover.branch : Set S)) ∧
      (∀ τ s t, a.val.map s=a.val.map t → F (τ,s)=F (τ,t)) ∧
      ∀ t, t≠0 → t≠1 → F (1,t) ∉ a.val.image := by
  obtain ⟨U,D,ρ,hρ,hρ1,hcollar⟩ := actual_loop_marked_closed_disk_collar M a ha
  have hcl (t : Interval) : a.val.map t ∈ closure U := by
    rw [D.closure_eq]
    exact Or.inr (mem_range_self t)
  let L : C(Interval,closure U) := ⟨fun t => ⟨a.val.map t,hcl t⟩,a.val.continuous.subtype_mk hcl⟩
  let α : C(Interval,JordanClosedDisk) := ⟨fun t => D.closedDisk.symm (L t),
    D.closedDisk.symm.continuous.comp L.continuous⟩
  have hα (t : Interval) : (D.closedDisk (α t)).val=a.val.map t :=
    congrArg Subtype.val (D.closedDisk.apply_symm_apply (L t))
  have hαnorm (t : Interval) : ‖(α t).val‖=1 := by
    apply (D.disk_boundary (α t)).mp
    rw [hα]
    exact mem_range_self t
  let c : JordanPlane := (α 0).val
  have hc : ‖c‖=1 := hαnorm 0
  have hαend : α 1=α 0 := by
    apply D.closedDisk.injective
    apply Subtype.ext
    rw [hα,hα]
    exact ha.symm
  let β : C(Interval × Interval,JordanClosedDisk) :=
    ⟨fun z => ⟨actualLoopParallelRadius ρ c z.1 (α z.2).val • (α z.2).val,by
      rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (lt_trans hρ (actual_loop_parallel_radius_bounds ρ hρ hρ1 c hc z.1 _ (hαnorm z.2)).1),
        hαnorm,mul_one]
      exact (actual_loop_parallel_radius_bounds ρ hρ hρ1 c hc z.1 _ (hαnorm z.2)).2⟩,
      by
        apply Continuous.subtype_mk
        dsimp [actualLoopParallelRadius]
        fun_prop⟩
  let F : C(Interval × Interval,S) := ⟨fun z => (D.closedDisk (β z)).val,
    continuous_subtype_val.comp (D.closedDisk.continuous.comp β.continuous)⟩
  have hβnorm (τ t : Interval) : ‖(β (τ,t)).val‖=actualLoopParallelRadius ρ c τ (α t).val := by
    change ‖actualLoopParallelRadius ρ c τ (α t).val • (α t).val‖=_
    rw [norm_smul,Real.norm_eq_abs,
      abs_of_pos (lt_trans hρ (actual_loop_parallel_radius_bounds ρ hρ hρ1 c hc τ _ (hαnorm t)).1),
      hαnorm,mul_one]
  have hβzero (t : Interval) : β (0,t)=α t := by
    apply Subtype.ext
    simp [β,actualLoopParallelRadius]
  have hβends (τ : Interval) : β (τ,0)=α 0 ∧ β (τ,1)=α 0 := by
    constructor <;> apply Subtype.ext
    · simp [β,actualLoopParallelRadius,c]
    · change actualLoopParallelRadius ρ c τ (α 1).val • (α 1).val=(α 0).val
      rw [hαend]
      simp [actualLoopParallelRadius,c]
  have hbaseOnly (τ t : Interval) (he : F (τ,t)=a.val.map 0) : a.val.map t=a.val.map 0 := by
    have hb : β (τ,t)=α 0 := D.closedDisk.injective (Subtype.ext (he.trans (hα 0).symm))
    have hr : actualLoopParallelRadius ρ c τ (α t).val=1 := by
      rw [← hβnorm,hb,hαnorm]
    have hp := congrArg Subtype.val hb
    change actualLoopParallelRadius ρ c τ (α t).val • (α t).val=(α 0).val at hp
    rw [hr,one_smul] at hp
    have hat : α t=α 0 := Subtype.ext hp
    rw [← hα,hat,hα]
  refine ⟨F,?_,?_,?_,?_,?_,?_⟩
  · intro t
    change (D.closedDisk (β (0,t))).val=a.val.map t
    rw [hβzero,hα]
  · intro τ s t he
    have hβeq : β (τ,s)=β (τ,t) := D.closedDisk.injective (Subtype.ext he)
    have hh := congrArg Subtype.val hβeq
    have hαeq : α s=α t := Subtype.ext
      (actual_loop_parallel_unit_injective ρ hρ hρ1 c hc τ _ _ (hαnorm s) (hαnorm t) hh)
    apply a.val.injective_except_loop_closure
    rw [← hα,← hα,hαeq]
  · intro τ
    constructor
    · change (D.closedDisk (β (τ,0))).val=a.val.map 0
      rw [(hβends τ).1,hα]
    · change (D.closedDisk (β (τ,1))).val=a.val.map 1
      rw [(hβends τ).2,hα,ha]
  · intro τ t ht0 ht1 hm
    have hb : F (τ,t)=a.val.map 0 := by
      by_contra hn
      apply hcollar (β (τ,t))
        (by rw [hβnorm]; exact (actual_loop_parallel_radius_bounds ρ hρ hρ1 c hc τ _ (hαnorm t)).1.le)
      exact ⟨hm,by simpa [F] using hn⟩
    have hm' : a.val.map t ∈ M.cover.branch := hbaseOnly τ t hb ▸ a.val.start_marked
    exact (a.val.marked_only_at_ends t hm').elim ht0 ht1
  · intro τ s t he
    have hat : α s=α t := D.closedDisk.injective
      (Subtype.ext ((hα s).trans (he.trans (hα t).symm)))
    have hbt : β (τ,s)=β (τ,t) := by
      apply Subtype.ext
      change actualLoopParallelRadius ρ c τ (α s).val • (α s).val =
        actualLoopParallelRadius ρ c τ (α t).val • (α t).val
      rw [hat]
    exact congrArg (fun z : JordanClosedDisk => (D.closedDisk z).val) hbt
  · intro t ht0 ht1 hh
    have hαne : (α t).val≠c := by
      intro he
      have hat : α t=α 0 := Subtype.ext he
      have he' : a.val.map t=a.val.map 0 := by rw [← hα,hat,hα]
      exact (a.val.marked_only_at_ends t (he' ▸ a.val.start_marked)).elim ht0 ht1
    have hnormlt : ‖(β (1,t)).val‖<1 := by
      rw [hβnorm]
      exact actual_loop_parallel_radius_strict ρ hρ1 c 1 (by norm_num) _ hαne
    exact (ne_of_lt hnormlt) ((D.disk_boundary (β (1,t))).mp hh)
end
end CurveComplex.HyperellipticModel
