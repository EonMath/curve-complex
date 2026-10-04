import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.Nodup
namespace CurveComplex.LocalSurgery
/-- Project the central part of the actual attachment walk; no tail or edge is reselected. -/
theorem actualCentralOnlyAttachedWalkProjects
    {V M : Type*} (G : SimpleGraph V) (H : SimpleGraph (Sum V M))
    (hcentral : ∀ u v,H.Adj (Sum.inl u) (Sum.inl v) → G.Adj u v)
    {u v : V} (P : H.Walk (Sum.inl u) (Sum.inl v))
    (hP : P.IsPath) (hOnly : ∀ r∈P.support,∃ x : V,r=Sum.inl x) :
    ∃ Q : G.Walk u v,Q.IsPath ∧ Q.support.map Sum.inl=P.support := by
  have hproject : ∀ {a b : Sum V M} (p : H.Walk a b),
      (∀ r∈p.support,∃ x : V,r=Sum.inl x) →
      ∀ u v : V,Sum.inl u=a → Sum.inl v=b →
        ∃ q : G.Walk u v,q.support.map Sum.inl=p.support := by
    intro a b p
    induction p with
    | nil =>
      intro hOnly u v hu hv
      have he : u=v := Sum.inl.inj (hu.trans hv.symm)
      subst v
      refine ⟨SimpleGraph.Walk.nil,?_⟩
      simp only [SimpleGraph.Walk.support_nil,List.map_cons,List.map_nil,hu]
    | @cons a k b hadj p ih =>
      intro hOnly u v hu hv
      have htail : ∀ r∈p.support,∃ x : V,r=Sum.inl x := by
        intro r hr
        exact hOnly r (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons];exact Or.inr hr)
      obtain ⟨x,hx⟩ := htail k (SimpleGraph.Walk.start_mem_support p)
      obtain ⟨q,hq⟩ := ih htail x v hx.symm hv
      have hAdj : G.Adj u x := hcentral u x (hu.symm ▸ hx ▸ hadj)
      refine ⟨SimpleGraph.Walk.cons hAdj q,?_⟩
      simp only [SimpleGraph.Walk.support_cons,List.map_cons,hq,hu]
  obtain ⟨Q,hQ⟩ := hproject P hOnly u v rfl rfl
  refine ⟨Q,?_,hQ⟩
  apply SimpleGraph.Walk.IsPath.mk'
  apply (List.nodup_map_iff Sum.inl_injective).mp
  rw [hQ]
  exact hP.support_nodup
end CurveComplex.LocalSurgery
