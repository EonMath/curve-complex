import CurveComplexGenusTwo.Topology.Smoothing.FiniteStarSeed
import Mathlib.Topology.Algebra.Module.Basic
open Set Metric Schoenflies

-- The only new cell boundary is the inserted actual radius; old fan
-- boundaries remain old boundaries. The two open new cells are disjoint.
theorem sector_split_frontier_invariant (Q : Set Plane) (hQ : IsClosed Q) (e : Plane) (he : e ≠ 0)
    (hint : (Q ∩ {x | 0 ≤ Plane.det e x}) ∩
      (Q ∩ {x | Plane.det e x ≤ 0}) = segment ℝ (0:Plane) e) :
    let Q₁ := Q ∩ {x | 0 ≤ Plane.det e x}
    let Q₂ := Q ∩ {x | Plane.det e x ≤ 0}
    frontier Q₁ ⊆ frontier Q ∪ segment ℝ (0:Plane) e ∧
      frontier Q₂ ⊆ frontier Q ∪ segment ℝ (0:Plane) e ∧
      Disjoint (interior Q₁) (interior Q₂) := by
  intro Q₁ Q₂
  have hcont : Continuous (fun x : Plane => Plane.det e x) := by
    unfold Plane.det
    exact (continuous_const.mul (Plane.continuous_coord 1)).sub
      (continuous_const.mul (Plane.continuous_coord 0))
  have hclosed₁ : IsClosed Q₁ := hQ.inter (isClosed_le continuous_const hcont)
  have hclosed₂ : IsClosed Q₂ := hQ.inter (isClosed_le hcont continuous_const)
  have hfront₁ : frontier Q₁ ⊆ frontier Q ∪ segment ℝ (0:Plane) e := by
    intro x hx
    rcases frontier_inter_subset Q {x | 0 ≤ Plane.det e x} hx with hxQ | hxD
    · exact Or.inl hxQ.1
    · have heq : Plane.det e x = 0 := (frontier_le_subset_eq continuous_const hcont hxD.2).symm
      have hx₁ : x ∈ Q₁ := hclosed₁.closure_eq ▸ frontier_subset_closure hx
      have hx₂ : x ∈ Q₂ := ⟨hx₁.1,heq.le⟩
      exact Or.inr (hint ▸ ⟨hx₁,hx₂⟩)
  have hfront₂ : frontier Q₂ ⊆ frontier Q ∪ segment ℝ (0:Plane) e := by
    intro x hx
    rcases frontier_inter_subset Q {x | Plane.det e x ≤ 0} hx with hxQ | hxD
    · exact Or.inl hxQ.1
    · have heq : Plane.det e x = 0 := frontier_le_subset_eq hcont continuous_const hxD.2
      have hx₂ : x ∈ Q₂ := hclosed₂.closure_eq ▸ frontier_subset_closure hx
      have hx₁ : x ∈ Q₁ := ⟨hx₂.1,heq.ge⟩
      exact Or.inr (hint ▸ ⟨hx₁,hx₂⟩)
  refine ⟨hfront₁,hfront₂,?_⟩
  let D : Plane →ₗ[ℝ] ℝ := {
    toFun := fun x => Plane.det e x
    map_add' := Plane.det_add_right e
    map_smul' := fun r x => Plane.det_smul_right r e x }
  apply Set.disjoint_left.mpr
  intro x hx₁ hx₂
  have hker : Q₁ ∩ Q₂ ⊆ (D.ker : Set Plane) := by
    rintro y ⟨hy₁,hy₂⟩
    change Plane.det e y = 0
    exact le_antisymm hy₂.2 hy₁.2
  have hxinter : x ∈ interior (Q₁ ∩ Q₂) := by
    rw [interior_inter]
    exact ⟨hx₁,hx₂⟩
  have hxker : x ∈ interior (D.ker : Set Plane) := interior_mono hker hxinter
  have htop : D.ker = ⊤ := D.ker.eq_top_of_nonempty_interior' ⟨x,hxker⟩
  have hperp : Plane.perp e ∈ D.ker := htop.symm ▸ Submodule.mem_top
  have hzero : Plane.det e (Plane.perp e) = 0 := hperp
  rw [Plane.det_perp_self] at hzero
  exact (sq_pos_of_pos (norm_pos_iff.mpr he)).ne' hzero

#print axioms sector_split_frontier_invariant
