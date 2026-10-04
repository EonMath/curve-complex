import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualSignedCornerConnector
namespace CurveComplex
open Set Topology

/-- Join two actual embedded source arcs at their sole common endpoint,
constructing an embedded arc with exact union image and exact outer ports. -/
theorem source_embedded_arc_concatenation
    {S : Type} [TopologicalSpace S] [T2Space S]
    (f g : C(Interval,S)) (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hfg : f 1 = g 0) (hmeet : Set.range f ∩ Set.range g = {f 1}) :
    ∃ h : C(Interval,S), IsEmbedding h ∧ h 0 = f 0 ∧ h 1 = g 1 ∧
      Set.range h = Set.range f ∪ Set.range g := by
  let p : Path (f 0) (f 1) := ⟨f,rfl,rfl⟩
  let q : Path (f 1) (g 1) := ⟨g,hfg.symm,rfl⟩
  let h : C(Interval,S) := (p.trans q).toContinuousMap
  have hcross (s t : Interval) (he : f s = g t) : s = 1 ∧ t = 0 := by
    have hh : f s ∈ Set.range f ∩ Set.range g := ⟨⟨s,rfl⟩,⟨t,he.symm⟩⟩
    rw [hmeet] at hh
    have hh' : f s = f 1 := Set.mem_singleton_iff.mp hh
    exact ⟨hf.injective hh',hg.injective (he.symm.trans (hh'.trans hfg))⟩
  have hi : Function.Injective h := by
    intro s t he
    change (p.trans q) s = (p.trans q) t at he
    simp only [Path.trans_apply] at he
    split_ifs at he with hs ht ht
    · have hh := hf.injective he
      apply Subtype.ext
      have hc := congrArg Subtype.val hh
      change 2*(s:ℝ) = 2*(t:ℝ) at hc
      linarith
    · obtain ⟨h1,h0⟩ := hcross _ _ he
      have hc0 := congrArg Subtype.val h0
      change 2*(t:ℝ)-1=0 at hc0
      exact False.elim (ht (by linarith))
    · obtain ⟨h1,h0⟩ := hcross _ _ he.symm
      have hc0 := congrArg Subtype.val h0
      change 2*(s:ℝ)-1=0 at hc0
      exact False.elim (hs (by linarith))
    · have hh := hg.injective he
      apply Subtype.ext
      have hc := congrArg Subtype.val hh
      change 2*(s:ℝ)-1 = 2*(t:ℝ)-1 at hc
      linarith
  refine ⟨h,(h.continuous.isClosedEmbedding hi).isEmbedding,?_,?_,?_⟩
  · exact (p.trans q).source
  · exact (p.trans q).target
  · exact p.trans_range q
end CurveComplex
#print axioms CurveComplex.source_embedded_arc_concatenation
