import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualNonrealLogarithmPiStripe
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual consecutive-π phase bounds construct the unique continuous time
graph of each intermediate old-axis contact. No contact graph is supplied. -/
theorem actual_affine_pi_level_graph
    {X : Type} [TopologicalSpace X] (a b : C(X,ℝ)) (p q k : ℤ)
    (ha : ∀ x, a x ∈ Ioo ((p:ℝ)*Real.pi) (((p:ℝ)+1)*Real.pi))
    (hb : ∀ x, b x ∈ Ioo ((q:ℝ)*Real.pi) (((q:ℝ)+1)*Real.pi))
    (hpk : p<k) (hkq : k≤q) :
    ∃ γ : C(X,unitInterval),
      (∀ x, 0<(γ x:ℝ) ∧ (γ x:ℝ)<1) ∧
      (∀ x, (γ x:ℝ)=((k:ℝ)*Real.pi-a x)/(b x-a x)) ∧
      ∀ x (τ : unitInterval),
        (1-(τ:ℝ))*a x+(τ:ℝ)*b x=(k:ℝ)*Real.pi ↔ τ=γ x := by
  have hpkR : (p:ℝ)+1≤k := by exact_mod_cast (Int.add_one_le_iff.mpr hpk)
  have hkqR : (k:ℝ)≤q := by exact_mod_cast hkq
  have hac (x : X) : a x<(k:ℝ)*Real.pi :=
    (ha x).2.trans_le (mul_le_mul_of_nonneg_right hpkR Real.pi_pos.le)
  have hcb (x : X) : (k:ℝ)*Real.pi<b x :=
    (mul_le_mul_of_nonneg_right hkqR Real.pi_pos.le).trans_lt (hb x).1
  have hden (x : X) : 0<b x-a x := sub_pos.mpr ((hac x).trans (hcb x))
  have hbounds (x : X) : ((k:ℝ)*Real.pi-a x)/(b x-a x) ∈ unitInterval :=
    ⟨div_nonneg (sub_nonneg.mpr (hac x).le) (hden x).le,
      (div_le_one (hden x)).mpr (by linarith [hcb x])⟩
  let γ : C(X,unitInterval) := {
    toFun := fun x => ⟨((k:ℝ)*Real.pi-a x)/(b x-a x),by
      constructor
      · exact div_nonneg (sub_nonneg.mpr (hac x).le) (hden x).le
      · exact (div_le_one (hden x)).mpr (by linarith [hcb x])⟩
    continuous_toFun := ((continuous_const.sub a.continuous).div
      (b.continuous.sub a.continuous) (fun x => (hden x).ne')).subtype_mk hbounds }
  refine ⟨γ,?_,(fun _ => rfl),?_⟩
  · intro x
    change 0<((k:ℝ)*Real.pi-a x)/(b x-a x) ∧ ((k:ℝ)*Real.pi-a x)/(b x-a x)<1
    exact ⟨div_pos (sub_pos.mpr (hac x)) (hden x),
      (div_lt_one (hden x)).mpr (by linarith [hcb x])⟩
  · intro x τ
    constructor
    · intro he
      apply Subtype.ext
      change (τ:ℝ)=((k:ℝ)*Real.pi-a x)/(b x-a x)
      apply (eq_div_iff (hden x).ne').mpr
      nlinarith
    · intro he
      rw [he]
      change (1-((k:ℝ)*Real.pi-a x)/(b x-a x))*a x+
        (((k:ℝ)*Real.pi-a x)/(b x-a x))*b x=(k:ℝ)*Real.pi
      field_simp [(hden x).ne']
      ring
end CurveComplex.HyperellipticModel
