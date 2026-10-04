import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassMarkedSweep
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLoopParallelImageSweep
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualContinuousSweepConcatenation
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section
/-- Original same-class LOOP data construct an embedded-except-closure sweep
from b to a marked parallel of a, with zero-free terminal interior. -/
theorem actual_same_class_target_avoiding_loop_sweep
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0=a.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b) :
    ∃ K : C(Interval × Interval,S),
      (∀ t, K (0,t)=b.val.map t) ∧
      (∀ τ s t, K (τ,s)=K (τ,t) → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
      (∀ τ, K (τ,0)=b.val.map 0 ∧ K (τ,1)=b.val.map 1) ∧
      (∀ τ t, t≠0 → t≠1 → K (τ,t) ∉ (M.cover.branch : Set S)) ∧
      ∀ t, t≠0 → t≠1 → K (1,t) ∉ a.val.image := by
  obtain ⟨F,hzero,hinj,hends,hmarks,himage⟩ := actual_same_class_marked_arc_sweep M b a hclass.symm
  obtain ⟨P,hPzero,hPinj,hPbase,hPmarks,hPtop⟩ := actual_loop_parallel_image_sweep M a ha
  have hmem (t : Interval) : F (1,t) ∈ a.val.image := by
    rw [← himage]
    exact mem_range_self t
  let L : C(Interval,a.val.image) := ⟨fun t => ⟨F (1,t),hmem t⟩,
    (F.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk hmem⟩
  have hbase (t : Interval) (hm : F (1,t) ∈ (M.cover.branch : Set S)) : F (1,t)=a.val.map 0 := by
    obtain ⟨s,hs⟩ := hmem t
    have hsm : a.val.map s ∈ (M.cover.branch : Set S) := hs ▸ hm
    rcases a.val.marked_only_at_ends s hsm with rfl | rfl
    · exact hs.symm
    · exact hs.symm.trans ha.symm
  have hLends : L 0=⟨a.val.map 0,mem_range_self 0⟩ ∧ L 1=⟨a.val.map 0,mem_range_self 0⟩ := by
    constructor <;> apply Subtype.ext
    · exact hbase 0 ((hends 1).1 ▸ b.val.start_marked)
    · exact hbase 1 ((hends 1).2 ▸ b.val.end_marked)
  have hLinterior (t : Interval) (ht0 : t≠0) (ht1 : t≠1) : (L t).val≠a.val.map 0 := by
    intro he
    change F (1,t)=a.val.map 0 at he
    exact hmarks 1 t ht0 ht1 (he ▸ a.val.start_marked)
  let Q : C(Interval × Interval,S) := ⟨fun z => P (z.1,L z.2),
    P.continuous.comp (continuous_fst.prodMk (L.continuous.comp continuous_snd))⟩
  have hQzero (t : Interval) : Q (0,t)=F (1,t) := hPzero (L t)
  have hQinj (τ s t : Interval) (he : Q (τ,s)=Q (τ,t)) :
      s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) := by
    have hh := hPinj τ he
    exact hinj 1 s t (congrArg Subtype.val hh)
  have hQends (τ : Interval) : Q (τ,0)=b.val.map 0 ∧ Q (τ,1)=b.val.map 1 := by
    have hz : a.val.map 0=b.val.map 0 := (congrArg Subtype.val hLends.1).symm.trans (hends 1).1
    have ho : a.val.map 0=b.val.map 1 := (congrArg Subtype.val hLends.2).symm.trans (hends 1).2
    constructor
    · change P (τ,L 0)=_
      rw [hLends.1,hPbase,hz]
    · change P (τ,L 1)=_
      rw [hLends.2,hPbase,ho]
  obtain ⟨K,hKzero,hKone,hKslices⟩ := CurveComplex.actual_continuous_sweep_concatenation F Q
    (fun t => (hQzero t).symm)
  refine ⟨K,(fun t => (hKzero t).trans (hzero t)),?_,?_,?_,?_⟩
  · intro τ s t he
    rcases hKslices τ with ⟨σ,hσ⟩ | ⟨σ,hσ⟩
    · exact hinj σ s t ((hσ s).symm.trans (he.trans (hσ t)))
    · exact hQinj σ s t ((hσ s).symm.trans (he.trans (hσ t)))
  · intro τ
    rcases hKslices τ with ⟨σ,hσ⟩ | ⟨σ,hσ⟩
    · exact ⟨(hσ 0).trans (hends σ).1,(hσ 1).trans (hends σ).2⟩
    · exact ⟨(hσ 0).trans (hQends σ).1,(hσ 1).trans (hQends σ).2⟩
  · intro τ t ht0 ht1
    rcases hKslices τ with ⟨σ,hσ⟩ | ⟨σ,hσ⟩
    · rw [hσ t]; exact hmarks σ t ht0 ht1
    · rw [hσ t]; exact hPmarks σ (L t) (hLinterior t ht0 ht1)
  · intro t ht0 ht1
    rw [hKone t]
    exact hPtop (L t) (hLinterior t ht0 ht1)
end
end CurveComplex.HyperellipticModel
