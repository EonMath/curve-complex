import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualComparisonPolarNormEmbeddingLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies

-- A literal uniform gap from the SAME supplied core, for both original outer traces.
example (G : C(Circle × Interval,Circle × Interval)) (hGe : IsEmbedding G)
    (r : Circle ≃ₜ Circle)
    (hcore : ∀ z, G (z,⟨1/2,by norm_num⟩)=(r z,⟨1/2,by norm_num⟩)) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1/4 ∧
      ∀ z, ε < |((G (z,0)).2:ℝ)-1/2| ∧
        ε < |((G (z,1)).2:ℝ)-1/2| := by
  audit_main14_base3
    have hpos (z : Circle) (a : Interval) (ha : a=0 ∨ a=1) :
        0 < |((G (z,a)).2:ℝ)-1/2| := by
      apply abs_pos.mpr
      intro he
      have hv : ((G (z,a)).2:ℝ)=1/2 := by linarith
      have hh : G (r.symm (G (z,a)).1,⟨1/2,by norm_num⟩)=G (z,a) := by
        rw [hcore,r.apply_symm_apply]
        exact Prod.ext rfl (Subtype.ext hv.symm)
      have heq := congrArg Prod.snd (hGe.injective hh)
      have hv' := congrArg Subtype.val heq
      rcases ha with rfl | rfl
      · change (1/2:ℝ)=0 at hv'
        norm_num at hv'
      · change (1/2:ℝ)=1 at hv'
        norm_num at hv'
    let f0 : Circle → ℝ := fun z => |((G (z,0)).2:ℝ)-1/2|
    let f1 : Circle → ℝ := fun z => |((G (z,1)).2:ℝ)-1/2|
    have hc0 : Continuous f0 := by dsimp [f0]; fun_prop
    have hc1 : Continuous f1 := by dsimp [f1]; fun_prop
    obtain ⟨z0,hz0,hmin0⟩ := (isCompact_univ : IsCompact (Set.univ : Set Circle)).exists_isMinOn
      Set.univ_nonempty hc0.continuousOn
    obtain ⟨z1,hz1,hmin1⟩ := (isCompact_univ : IsCompact (Set.univ : Set Circle)).exists_isMinOn
      Set.univ_nonempty hc1.continuousOn
    have hp0 : 0 < f0 z0 := hpos z0 0 (Or.inl rfl)
    have hp1 : 0 < f1 z1 := hpos z1 1 (Or.inr rfl)
    let ε : ℝ := min ((min (f0 z0) (f1 z1))/2) (1/8)
    have hp : 0 < ε := lt_min (half_pos (lt_min hp0 hp1)) (by norm_num)
    have he0 : ε ≤ f0 z0 / 2 := (min_le_left _ _).trans
      ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)).mpr (min_le_left _ _))
    have he1 : ε ≤ f1 z1 / 2 := (min_le_left _ _).trans
      ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)).mpr (min_le_right _ _))
    refine ⟨ε,hp,lt_of_le_of_lt (min_le_right _ _) (by norm_num),?_⟩
    intro z
    have hm0 := hmin0 (a := z) (Set.mem_univ z)
    have hm1 := hmin1 (a := z) (Set.mem_univ z)
    change f0 z0 ≤ f0 z at hm0
    change f1 z1 ≤ f1 z at hm1
    change ε < f0 z ∧ ε < f1 z
    constructor <;> linarith
end CurveComplex.HyperellipticModel
