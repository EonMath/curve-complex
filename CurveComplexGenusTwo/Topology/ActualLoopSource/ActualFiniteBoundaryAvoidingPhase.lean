import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedIntervalMesh
import Mathlib.Order.Interval.Set.Infinite
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Finite actual boundary contact parameters produce a phase avoiding every
contact at every interior mesh node. Reuses the finite-phase construction of
the adjacent sweep, without any adjacency/nonloop premise. -/
theorem actual_finite_boundary_avoiding_phase
    (events : Set Interval) (hf : events.Finite) (m : ℕ) (hm : 0 < m) :
    ∃ θ : ℝ,0<θ ∧ θ<1 ∧
      ∀ k : Fin m,∀ t : Interval,t.val=(k.val+θ)/m → t ∉ events := by
  classical
  let forbidden : Set ℝ := ⋃ k : Fin m,
    (fun t : Interval => (m:ℝ)*t.val-k.val) '' events
  have hforbidden : forbidden.Finite := Set.finite_iUnion (fun k => hf.image _)
  obtain ⟨θ,hθ,havoid⟩ :=
    (Set.Ioo_infinite (by norm_num : (0:ℝ)<1)).exists_notMem_finite hforbidden
  refine ⟨θ,hθ.1,hθ.2,?_⟩
  intro k t ht hevent
  apply havoid
  apply mem_iUnion.mpr
  refine ⟨k,t,hevent,?_⟩
  have hmR : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  change (m:ℝ)*t.val-k.val=θ
  rw [ht]
  field_simp
  ring
end CurveComplex.HyperellipticModel
