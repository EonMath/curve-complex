import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformMeshAdjacentSeam
namespace CurveComplex.HyperellipticModel
open Set Topology
theorem actual_uniform_mesh_interval_collision (n : ℕ) (hn : 0<n) (i j : Fin n) (s t : Interval)
      (hh : ArcFinitePosition.intervalMeshParameter n hn i s=
        ArcFinitePosition.intervalMeshParameter n hn j t) :
      (i=j ∧ s=t) ∨ ((s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) := by
    have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hv := congrArg Subtype.val hh
    change ((i.val:ℝ)+s.val)/n=((j.val:ℝ)+t.val)/n at hv
    have hv' := (div_left_inj' hnR).mp hv
    by_cases hij : i=j
    · left
      refine ⟨hij,?_⟩
      subst j
      exact Subtype.ext (by linarith only [hv'])
    · rcases lt_or_gt_of_ne hij with hij | hji
      · have hi : (i.val:ℝ)+1≤ j.val := by exact_mod_cast hij
        have hs : s=1 := Subtype.ext (by change s.val=1; linarith only [hv',hi,t.property.1,s.property.2])
        have ht : t=0 := Subtype.ext (by change t.val=0; linarith only [hv',hi,t.property.1,s.property.2])
        exact Or.inr ⟨Or.inr hs,Or.inl ht⟩
      · have hi : (j.val:ℝ)+1≤ i.val := by exact_mod_cast hji
        have hs : s=0 := Subtype.ext (by change s.val=0; linarith only [hv',hi,s.property.1,t.property.2])
        have ht : t=1 := Subtype.ext (by change t.val=1; linarith only [hv',hi,s.property.1,t.property.2])
        exact Or.inr ⟨Or.inl hs,Or.inr ht⟩
/-- Different grid nodes are genuinely different parameter points. -/
theorem actual_uniform_mesh_node_injective (n : ℕ) (hn : 0<n) :
    Function.Injective (fun j : Fin (n+1) =>
      actualHalfMeshParameter n hn ⟨2*j.val,by omega⟩) := by
  intro j k he
  have hv := congrArg Subtype.val he
  rw [actual_half_mesh_parameter_vertex n hn j,
    actual_half_mesh_parameter_vertex n hn k] at hv
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  apply Fin.ext
  exact_mod_cast (div_left_inj' hnR).mp hv
/-- A literal grid node can lie on a mesh edge only at an actual endpoint. -/
theorem actual_uniform_mesh_node_edge_endpoint (n : ℕ) (hn : 0<n)
    (i : Fin n) (j : Fin (n+1)) (t : Interval)
    (he : ArcFinitePosition.intervalMeshParameter n hn i t=
      actualHalfMeshParameter n hn ⟨2*j.val,by omega⟩) : t=0 ∨ t=1 := by
  have hv := congrArg Subtype.val he
  rw [actual_half_mesh_parameter_vertex n hn j] at hv
  change ((i.val:ℝ)+t.val)/n=(j.val:ℝ)/n at hv
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hh := (div_left_inj' hnR).mp hv
  by_cases hji : j.val≤ i.val
  · have hjiR : (j.val:ℝ)≤ i.val := by exact_mod_cast hji
    left
    apply Subtype.ext
    change t.val=0
    linarith only [hh,hjiR,t.property.1]
  · have hijR : (i.val:ℝ)+1≤ j.val := by exact_mod_cast (show i.val+1≤ j.val by omega)
    right
    apply Subtype.ext
    change t.val=1
    linarith only [hh,hijR,t.property.2]
end CurveComplex.HyperellipticModel
