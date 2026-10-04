import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualCentralOnlyAttachedWalkProjectionKernelRecovery
namespace CurveComplex.LocalSurgery
/-- A simple actual path terminating at a mark uses one last chosen tail; its
remaining central walk is unchanged. -/
theorem actualTerminalMarkedAttachedWalkProjects
    {V M : Type*} (G : SimpleGraph V) (H : SimpleGraph (Sum V M))
    (Tail : V → M → Prop)
    (hcentral : ∀ u v,H.Adj (Sum.inl u) (Sum.inl v) → G.Adj u v)
    (hmark : ∀ m n,¬H.Adj (Sum.inr m) (Sum.inr n))
    (htail : ∀ m v,H.Adj (Sum.inr m) (Sum.inl v) → Tail v m)
    {u : V} {m : M} (P : H.Walk (Sum.inl u) (Sum.inr m)) (hP : P.IsPath)
    (hOnlyMark : ∀ n,Sum.inr n∈P.support → n=m) :
    ∃ v : V,Tail v m ∧ ∃ Q : G.Walk v u,Q.IsPath := by
  have hR : P.reverse.IsPath := hP.reverse
  have hOnlyR : ∀ n,Sum.inr n∈P.reverse.support → n=m := by
    intro n hn
    exact hOnlyMark n (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hn)
  cases hRev : P.reverse with
  | @cons _ k _ hadj R =>
    rw [hRev] at hR hOnlyR
    cases k with
    | inr n => exact (hmark m n hadj).elim
    | inl v =>
      obtain ⟨hRR,hfresh⟩ := (SimpleGraph.Walk.cons_isPath_iff hadj R).mp hR
      have hOnly : ∀ r∈R.support,∃ x : V,r=Sum.inl x := by
        intro r hr
        cases r with
        | inl x => exact ⟨x,rfl⟩
        | inr n =>
          have hnm := hOnlyR n (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons];exact Or.inr hr)
          subst n
          exact (hfresh hr).elim
      obtain ⟨Q,hQ,hSupport⟩ := actualCentralOnlyAttachedWalkProjects G H hcentral R hRR hOnly
      exact ⟨v,htail m v hadj,Q,hQ⟩
end CurveComplex.LocalSurgery
