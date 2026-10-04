import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformGridEdgeParameterGeometry
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Literal vertical open-seam points belong only to the two adjacent physical
cells, and retain the original seam parameter in those cells. -/
theorem actual_uniform_vertical_open_seam_cell_incidence
    (n : ℕ) (hn : 0<n) (node : Fin (n+1)) (i : Fin n) (s : Interval)
    (hs : 0<s.val ∧ s.val < 1) (k : Fin n × Fin n) (z : Interval × Interval)
    (he : (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
      ArcFinitePosition.intervalMeshParameter n hn k.2 z.2)=
      (actualHalfMeshParameter n hn ⟨2*node.val,by omega⟩,
        ArcFinitePosition.intervalMeshParameter n hn i s)) :
    k.2=i ∧ z.2=s ∧
      ((k.1.val=node.val ∧ z.1=0) ∨ (k.1.val+1=node.val ∧ z.1=1)) := by
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  have hsame : k.2=i ∧ z.2=s := by
    rcases actual_uniform_mesh_interval_collision n hn i k.2 s z.2 hy.symm with h | ⟨hb,_⟩
    · exact ⟨h.1.symm,h.2.symm⟩
    · rcases hb with h | h
      · have h0 := hs.1
        simp [h] at h0
      · have h1 := hs.2
        simp [h] at h1
  refine ⟨hsame.1,hsame.2,?_⟩
  have hnR : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hv := congrArg Subtype.val hx
  rw [actual_half_mesh_parameter_vertex n hn node] at hv
  have hh : (k.1.val:ℝ)+z.1.val=(node.val:ℝ) := (div_left_inj' hnR).mp hv
  rcases actual_uniform_mesh_node_edge_endpoint n hn k.1 node z.1 hx with hz | hz
  · left
    refine ⟨?_,hz⟩
    rw [hz] at hh
    change (k.1.val:ℝ)+0=(node.val:ℝ) at hh
    simp only [add_zero] at hh
    exact_mod_cast hh
  · right
    refine ⟨?_,hz⟩
    rw [hz] at hh
    change (k.1.val:ℝ)+1=(node.val:ℝ) at hh
    exact_mod_cast hh
/-- Horizontal counterpart, with the same original parameter and both literal
adjacent cells, obtained by swapping the physical coordinates. -/
theorem actual_uniform_horizontal_open_seam_cell_incidence
    (n : ℕ) (hn : 0<n) (node : Fin (n+1)) (i : Fin n) (s : Interval)
    (hs : 0<s.val ∧ s.val < 1) (k : Fin n × Fin n) (z : Interval × Interval)
    (he : (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
      ArcFinitePosition.intervalMeshParameter n hn k.2 z.2)=
      (ArcFinitePosition.intervalMeshParameter n hn i s,
        actualHalfMeshParameter n hn ⟨2*node.val,by omega⟩)) :
    k.1=i ∧ z.1=s ∧
      ((k.2.val=node.val ∧ z.2=0) ∨ (k.2.val+1=node.val ∧ z.2=1)) := by
  exact actual_uniform_vertical_open_seam_cell_incidence n hn node i s hs
    (k.2,k.1) (z.2,z.1) (congrArg Prod.swap he)
end CurveComplex.HyperellipticModel
