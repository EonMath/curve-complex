import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareConvexConeFilling
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual conical filling produces its injective zero-contact radial map.
The contact directions are selected from the literal boundary normals, not
provided as a geometric contact-family certificate. -/
theorem actual_square_cone_actual_zero_radials
    (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
    (f : C({z : ℝ × ℝ // ‖z‖=1},V)) (center : V) (hc : center.val.2≠0) :
    ∃ G : C({z : ℝ × ℝ // ‖z‖≤1},V),
      (∀ z : {z : ℝ × ℝ // ‖z‖=1},G ⟨z.val,z.property.le⟩=f z) ∧
    ∃ q : C({z : {z : ℝ × ℝ // ‖z‖=1} | (f z).val.2/center.val.2≤0},
      {z : ℝ × ℝ // ‖z‖≤1}),
      Function.Injective q ∧
      (∀ z,(q z).val=(1/(1-(f z.val).val.2/center.val.2)) • z.val.val) ∧
      (∀ z,(G (q z)).val.2=0) := by
  obtain ⟨cone,G,hconesurj,hcone,hfill⟩ := actual_square_convex_cone_filling V hV f center
  let N := {z : {z : ℝ × ℝ // ‖z‖=1} | (f z).val.2/center.val.2≤0}
  let h : C(N,ℝ) := ⟨fun z => (f z.val).val.2/center.val.2,by fun_prop⟩
  have hn (z : N) : h z≤0 := z.property
  have hd (z : N) : 0<1-h z := by linarith only [hn z]
  let radius : C(N,Interval) :=
    ⟨fun z => ⟨1/(1-h z),⟨(one_div_pos.mpr (hd z)).le,
      (div_le_one (hd z)).mpr (by linarith only [hn z])⟩⟩,
      (continuous_const.div (continuous_const.sub h.continuous)
        (fun z => (hd z).ne')).subtype_mk _⟩
  have hrpos (z : N) : 0<(radius z).val := one_div_pos.mpr (hd z)
  let q : C(N,{z : ℝ × ℝ // ‖z‖≤1}) :=
    ⟨fun z => ⟨(radius z).val • z.val.val,by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hrpos z),z.val.property,mul_one]
      exact (radius z).property.2⟩,by fun_prop⟩
  have hnorm (z : N) : ‖(q z).val‖=(radius z).val := by
    change ‖(radius z).val • z.val.val‖=(radius z).val
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hrpos z),z.val.property,mul_one]
  have hinj : Function.Injective q := by
    intro z w he
    have hr : (radius z).val=(radius w).val := by rw [← hnorm z,← hnorm w,he]
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    change (radius z).val • z.val.val=(radius w).val • w.val.val at hh
    rw [← hr] at hh
    exact smul_right_injective (ℝ × ℝ) (ne_of_gt (hrpos z)) hh
  have hboundary (z : {z : ℝ × ℝ // ‖z‖=1}) : G ⟨z.val,z.property.le⟩=f z := by
    have he : cone (0,z)=⟨z.val,z.property.le⟩ := by
      apply Subtype.ext
      rw [hcone]
      simp
    apply Subtype.ext
    have hh := hfill (0,z)
    rw [he] at hh
    change (G ⟨z.val,z.property.le⟩).val=(1-(0:ℝ)) • (f z).val+(0:ℝ) • center.val at hh
    simpa only [sub_zero,one_smul,zero_smul,add_zero] using hh
  refine ⟨G,hboundary,q,hinj,(fun _ => rfl),?_⟩
  intro z
  let r : Interval := ⟨1-(radius z).val,by
    constructor <;> linarith only [(radius z).property.1,(radius z).property.2]⟩
  have he : cone (r,z.val)=q z := by
    apply Subtype.ext
    rw [hcone]
    change (1-(1-(radius z).val)) • z.val.val=(radius z).val • z.val.val
    congr 1
    ring
  have hh := congrArg Prod.snd (hfill (r,z.val))
  rw [he] at hh
  change (G (q z)).val.2=(1-r.val)*(f z.val).val.2+r.val*center.val.2 at hh
  rw [hh]
  change (1-(1-1/(1-(f z.val).val.2/center.val.2)))*(f z.val).val.2+
    (1-1/(1-(f z.val).val.2/center.val.2))*center.val.2=0
  have hden : 1-(f z.val).val.2/center.val.2≠0 := (hd z).ne'
  have hsub : center.val.2-(f z.val).val.2≠0 := by
    intro heq
    have heq' := sub_eq_zero.mp heq
    rw [← heq',div_self hc,sub_self] at hden
    exact hden rfl
  field_simp [hc,hden,hsub]
  ring
end CurveComplex.HyperellipticModel
