import Mathlib

open Set Topology unitInterval
namespace CurveComplex

/-- Concatenation of two embedded paths meeting only at the joining endpoint. -/
theorem isEmbedding_path_trans_of_inter_singleton_probe
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {a b c : S} (p : Path a b) (q : Path b c)
    (hp : IsEmbedding p) (hq : IsEmbedding q)
    (hinter : Set.range p ∩ Set.range q = {b}) :
    IsEmbedding (p.trans q) := by
  apply ((p.trans q).continuous.isClosedEmbedding ?_).isEmbedding
  intro t u he
  rw [Path.trans_apply,Path.trans_apply] at he
  split_ifs at he with ht hu hu
  · apply Subtype.ext
    have hh := congrArg Subtype.val (hp.injective he)
    dsimp at hh
    linarith
  · have hm : p ⟨2*t,(mul_pos_mem_iff zero_lt_two).2 ⟨t.property.1,ht⟩⟩ ∈
        Set.range p ∩ Set.range q := ⟨Set.mem_range_self _,⟨_,he.symm⟩⟩
    have hy : p ⟨2*t,(mul_pos_mem_iff zero_lt_two).2 ⟨t.property.1,ht⟩⟩ = b := by
      simpa [hinter] using hm
    have hh := congrArg Subtype.val (hq.injective (he.symm.trans (hy.trans q.source.symm)))
    dsimp at hh
    exfalso
    linarith
  · have hm : p ⟨2*u,(mul_pos_mem_iff zero_lt_two).2 ⟨u.property.1,hu⟩⟩ ∈
        Set.range p ∩ Set.range q := ⟨Set.mem_range_self _,⟨_,he⟩⟩
    have hy : p ⟨2*u,(mul_pos_mem_iff zero_lt_two).2 ⟨u.property.1,hu⟩⟩ = b := by
      simpa [hinter] using hm
    have hh := congrArg Subtype.val (hq.injective (he.trans (hy.trans q.source.symm)))
    dsimp at hh
    exfalso
    linarith
  · apply Subtype.ext
    have hh := congrArg Subtype.val (hq.injective he)
    dsimp at hh
    linarith

#print axioms isEmbedding_path_trans_of_inter_singleton_probe
end CurveComplex
