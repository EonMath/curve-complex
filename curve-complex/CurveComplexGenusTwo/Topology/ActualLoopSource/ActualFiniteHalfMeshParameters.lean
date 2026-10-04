import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedLoopOffCellCutoff
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual finite half-mesh parameter containing both cell vertices and poles. -/
noncomputable def actualHalfMeshParameter (n : ℕ) (hn : 0<n) (k : Fin (2*n+1)) : Interval :=
  ⟨(k.val:ℝ)/(2*n),by
    have hnR : (0:ℝ)<n := by exact_mod_cast hn
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
    · apply (div_le_one (by positivity : (0:ℝ)<2*n)).mpr
      exact_mod_cast Nat.lt_succ_iff.mp k.isLt⟩
/-- Every genuine original cell pole is literally in the constructed cloud. -/
theorem actual_half_mesh_parameter_cell_pole (n : ℕ) (hn : 0<n) (i : Fin n) :
    actualHalfMeshParameter n hn ⟨2*i.val+1,by omega⟩=
      ArcFinitePosition.intervalMeshParameter n hn i ⟨1/2,by norm_num⟩ := by
  apply Subtype.ext
  change ((2*i.val+1:ℕ):ℝ)/(2*n)=((i.val:ℝ)+1/2)/n
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  push_cast
  field_simp
/-- Every genuine original cell vertex is literally in the constructed cloud. -/
theorem actual_half_mesh_parameter_vertex (n : ℕ) (hn : 0<n) (i : Fin (n+1)) :
    (actualHalfMeshParameter n hn ⟨2*i.val,by omega⟩:ℝ)=(i.val:ℝ)/n := by
  change ((2*i.val:ℕ):ℝ)/(2*n)=(i.val:ℝ)/n
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  push_cast
  field_simp
end CurveComplex.HyperellipticModel
