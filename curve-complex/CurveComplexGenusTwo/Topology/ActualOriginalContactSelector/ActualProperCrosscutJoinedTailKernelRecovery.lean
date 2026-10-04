import Mathlib
namespace CurveComplex.LocalSurgery
open Set Topology
open scoped unitInterval
abbrev Interval := unitInterval
/-- Reuse of the embeddedPathTrans helper in canonical ActualReturningSubarc, preserving its proof. -/
theorem actualEmbeddedContactPathTrans {Y : Type} [TopologicalSpace Y] [T2Space Y]
    {x y z : Y} (p : Path x y) (q : Path y z)
    (hp : Topology.IsEmbedding p) (hq : Topology.IsEmbedding q)
    (hinter : Set.range p ∩ Set.range q = {y}) :
    Topology.IsEmbedding (p.trans q) := by
  apply ((p.trans q).continuous.isClosedEmbedding ?_).isEmbedding
  intro t u he
  simp only [Path.trans_apply] at he
  split_ifs at he with ht hu
  · have hv := congrArg Subtype.val (hp.injective he)
    apply Subtype.ext
    change 2*t.val = 2*u.val at hv
    linarith
  · let t0 : Interval := ⟨2*t.val,by constructor <;> linarith [t.property.1]⟩
    let u1 : Interval := ⟨2*u.val-1,by constructor <;> linarith [u.property.2]⟩
    change p t0 = q u1 at he
    have hpy : p t0 = y := by
      have hm : p t0 ∈ Set.range p ∩ Set.range q := ⟨⟨t0,rfl⟩,⟨u1,he.symm⟩⟩
      rw [hinter] at hm
      exact Set.mem_singleton_iff.mp hm
    have hqu : q u1 = y := he.symm.trans hpy
    have ht0 := congrArg Subtype.val (hp.injective (hpy.trans p.target.symm))
    have hu1 := congrArg Subtype.val (hq.injective (hqu.trans q.source.symm))
    apply Subtype.ext
    change 2*t.val = 1 at ht0
    change 2*u.val-1 = 0 at hu1
    linarith
  · let t1 : Interval := ⟨2*t.val-1,by constructor <;> linarith [t.property.2]⟩
    let u0 : Interval := ⟨2*u.val,by constructor <;> linarith [u.property.1]⟩
    change q t1 = p u0 at he
    have hpu : p u0 = y := by
      have hm : p u0 ∈ Set.range p ∩ Set.range q := ⟨⟨u0,rfl⟩,⟨t1,he⟩⟩
      rw [hinter] at hm
      exact Set.mem_singleton_iff.mp hm
    have hqt : q t1 = y := he.trans hpu
    have ht1 := congrArg Subtype.val (hq.injective (hqt.trans q.source.symm))
    have hu0 := congrArg Subtype.val (hp.injective (hpu.trans p.target.symm))
    apply Subtype.ext
    change 2*t.val-1 = 0 at ht1
    change 2*u.val = 1 at hu0
    linarith
  · have hv := congrArg Subtype.val (hq.injective he)
    apply Subtype.ext
    change 2*t.val-1 = 2*u.val-1 at hv
    linarith

theorem actualJoinedPathInteriorOfPositiveFirstAndNonterminalSecond
    {x y z : unitInterval × unitInterval} (p : Path x y) (q : Path y z)
    (hp : ∀ t : unitInterval,t≠0 → (p t).1∈Ioo (0 : unitInterval) 1 ∧ (p t).2∈Ioo (0 : unitInterval) 1)
    (hq : ∀ t : unitInterval,t≠1 → (q t).1∈Ioo (0 : unitInterval) 1 ∧ (q t).2∈Ioo (0 : unitInterval) 1) :
    ∀ t : unitInterval,t∈Ioo (0 : unitInterval) 1 →
      ((p.trans q) t).1∈Ioo (0 : unitInterval) 1 ∧ ((p.trans q) t).2∈Ioo (0 : unitInterval) 1 := by
  intro t ht
  rw [Path.trans_apply]
  split_ifs with h
  · apply hp
    intro he
    have hv := congrArg Subtype.val he
    change 2*t.val=0 at hv
    have hh : 0<t.val := ht.1
    linarith only [hh,hv]
  · apply hq
    intro he
    have hv := congrArg Subtype.val he
    change 2*t.val-1=1 at hv
    have hh : t.val<1 := ht.2
    linarith only [hh,hv]
end CurveComplex.LocalSurgery
