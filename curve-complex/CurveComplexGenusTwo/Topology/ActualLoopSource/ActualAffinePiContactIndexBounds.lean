import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualAffinePiLevelGraph
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual endpoint phase stripes bound ALL affine old-axis contact indices
in one explicitly constructed finite integer interval. -/
theorem actual_affine_pi_contact_index_bounds
    {X : Type} [TopologicalSpace X] (a b : C(X,ℝ)) (p q : ℤ)
    (ha : ∀ x, a x ∈ Ioo ((p:ℝ)*Real.pi) (((p:ℝ)+1)*Real.pi))
    (hb : ∀ x, b x ∈ Ioo ((q:ℝ)*Real.pi) (((q:ℝ)+1)*Real.pi)) :
    ∀ x (τ : unitInterval) (k : ℤ),
      (1-(τ:ℝ))*a x+(τ:ℝ)*b x=(k:ℝ)*Real.pi →
        k ∈ Finset.Icc (min p q+1) (max p q) := by
  intro x τ k he
  have hpL : (min p q:ℝ)≤(p:ℝ) := by exact_mod_cast min_le_left p q
  have hqL : (min p q:ℝ)≤(q:ℝ) := by exact_mod_cast min_le_right p q
  have hpU : (p:ℝ)≤(max p q:ℝ) := by exact_mod_cast le_max_left p q
  have hqU : (q:ℝ)≤(max p q:ℝ) := by exact_mod_cast le_max_right p q
  have hax : a x ∈ Ioo ((min p q:ℝ)*Real.pi) (((max p q:ℝ)+1)*Real.pi) :=
    ⟨(mul_le_mul_of_nonneg_right hpL Real.pi_pos.le).trans_lt (ha x).1,
      (ha x).2.trans_le (mul_le_mul_of_nonneg_right (by linarith : (p:ℝ)+1≤(max p q:ℝ)+1) Real.pi_pos.le)⟩
  have hbx : b x ∈ Ioo ((min p q:ℝ)*Real.pi) (((max p q:ℝ)+1)*Real.pi) :=
    ⟨(mul_le_mul_of_nonneg_right hqL Real.pi_pos.le).trans_lt (hb x).1,
      (hb x).2.trans_le (mul_le_mul_of_nonneg_right (by linarith : (q:ℝ)+1≤(max p q:ℝ)+1) Real.pi_pos.le)⟩
  have hphase : (1-(τ:ℝ))*a x+(τ:ℝ)*b x ∈
      Ioo ((min p q:ℝ)*Real.pi) (((max p q:ℝ)+1)*Real.pi) := by
    simpa only [smul_eq_mul] using (convex_Ioo (𝕜:=ℝ) ((min p q:ℝ)*Real.pi)
      (((max p q:ℝ)+1)*Real.pi)) hax hbx
      (show 0≤1-(τ:ℝ) by linarith [τ.property.2]) τ.property.1 (by ring)
  rw [he] at hphase
  have hklR : (min p q:ℝ)<k := (mul_lt_mul_iff_of_pos_right Real.pi_pos).mp hphase.1
  have hkuR : (k:ℝ)<(max p q:ℝ)+1 := (mul_lt_mul_iff_of_pos_right Real.pi_pos).mp hphase.2
  have hkl : min p q<k := by exact_mod_cast hklR
  have hku : k < max p q+1 := by exact_mod_cast hkuR
  exact Finset.mem_Icc.mpr ⟨Int.add_one_le_iff.mpr hkl,Int.lt_add_one_iff.mp hku⟩
/-- Equal consecutive-π stripes produce NO affine old-axis contact, rather
than a degenerate graph with a vanishing denominator. -/
theorem actual_affine_pi_same_stripe_no_contacts
    {X : Type} [TopologicalSpace X] (a b : C(X,ℝ)) (p : ℤ)
    (ha : ∀ x, a x ∈ Ioo ((p:ℝ)*Real.pi) (((p:ℝ)+1)*Real.pi))
    (hb : ∀ x, b x ∈ Ioo ((p:ℝ)*Real.pi) (((p:ℝ)+1)*Real.pi)) :
    ∀ x (τ : unitInterval) (k : ℤ),
      (1-(τ:ℝ))*a x+(τ:ℝ)*b x≠(k:ℝ)*Real.pi := by
  intro x τ k he
  have h := actual_affine_pi_contact_index_bounds a b p p ha hb x τ k he
  have hh := Finset.mem_Icc.mp h
  simp only [min_self,max_self] at hh
  omega
end CurveComplex.HyperellipticModel
