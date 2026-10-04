import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformGridEdgeParameterGeometry
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- A literal affine mesh edge is injective, so restricting a finite actual
boundary contact set to it remains finite. -/
theorem actual_uniform_mesh_parameter_injective (n : ℕ) (hn : 0<n) (i : Fin n) :
    Function.Injective (ArcFinitePosition.intervalMeshParameter n hn i) := by
  intro t u he
  have hh := congrArg Subtype.val he
  change ((i.val:ℝ)+t.val)/n=((i.val:ℝ)+u.val)/n at hh
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hv := (div_left_inj' hnR).mp hh
  exact Subtype.ext (by linarith only [hv])
theorem actual_uniform_mesh_finite_contact_restriction
    {Y : Type} [TopologicalSpace Y] (old : Set Y) (g : C(Interval,Y))
    (hfinite : {t : Interval | g t ∈ old}.Finite)
    (n : ℕ) (hn : 0<n) (i : Fin n) :
    {t : Interval | g (ArcFinitePosition.intervalMeshParameter n hn i t) ∈ old}.Finite := by
  change ((ArcFinitePosition.intervalMeshParameter n hn i) ⁻¹' {t : Interval | g t ∈ old}).Finite
  exact Set.Finite.preimage (actual_uniform_mesh_parameter_injective n hn i).injOn hfinite
theorem actual_uniform_mesh_node_zero (n : ℕ) (hn : 0<n) :
    actualHalfMeshParameter n hn ⟨0,by omega⟩=0 := by
  apply Subtype.ext
  simp [actualHalfMeshParameter]
theorem actual_uniform_mesh_node_last (n : ℕ) (hn : 0<n) :
    actualHalfMeshParameter n hn ⟨2*n,by omega⟩=1 := by
  apply Subtype.ext
  change ((2*n:ℕ):ℝ)/(2*n)=1
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    div_self (mul_ne_zero (by norm_num : (2:ℝ)≠0) hnR)
end CurveComplex.HyperellipticModel
