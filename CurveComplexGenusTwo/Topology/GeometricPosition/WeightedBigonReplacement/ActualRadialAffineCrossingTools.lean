import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualEmbeddedLocalLineTools
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
open Set Topology Schoenflies
namespace CurveComplex

theorem actual_positive_radial_segment_graph
    (a b q : Plane) (ha : 0 < a 1) (hb : b 1 < 0)
    (hq : 0 < q 1) (hmem : q ∈ segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b) :
    q 0 = (a 0/a 1)*q 1 := by
  rcases hmem with hmem | hmem
  · rw [segment_eq_image'] at hmem
    obtain ⟨t,ht,he⟩ := hmem
    have h0 := congrArg (fun x : Plane => x 0) he
    have h1 := congrArg (fun x : Plane => x 1) he
    change 0+t*(a 0-0) = q 0 at h0
    change 0+t*(a 1-0) = q 1 at h1
    rw [←h0,←h1]
    field_simp
    ring
  · rw [segment_eq_image'] at hmem
    obtain ⟨t,ht,he⟩ := hmem
    have h1 := congrArg (fun x : Plane => x 1) he
    change 0+t*(b 1-0) = q 1 at h1
    nlinarith only [ht.1,hb,hq,h1]

theorem actual_signed_radial_segment_graph
    (a b p q : Plane) (ha : 0 < a 1) (hb : b 1 < 0) (hp : p 1 ≠ 0)
    (hq : 0 < q 1*p 1) (hmem : q ∈ segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b) :
    q 0 = (if 0 < p 1 then a 0/a 1 else b 0/b 1)*q 1 := by
  by_cases hpp : 0 < p 1
  · rw [ite_eq_left hpp]
    have hqq : 0 < q 1 := by nlinarith only [hq,hpp]
    exact actual_positive_radial_segment_graph a b q ha hb hqq hmem
  · rw [ite_eq_right hpp]
    have hpn : p 1 < 0 := lt_of_le_of_ne (le_of_not_gt hpp) hp
    have hqq : q 1 < 0 := by nlinarith only [hq,hpn]
    rcases hmem with hmem | hmem
    · rw [segment_eq_image'] at hmem
      obtain ⟨t,ht,he⟩ := hmem
      have hy := congrArg (fun q : Plane => q 1) he
      change 0+t*(a 1-0) = q 1 at hy
      nlinarith only [ht.1,ha,hqq,hy]
    · rw [segment_eq_image'] at hmem
      obtain ⟨t,ht,he⟩ := hmem
      have h0 := congrArg (fun q : Plane => q 0) he
      have h1 := congrArg (fun q : Plane => q 1) he
      change 0+t*(b 0-0) = q 0 at h0
      change 0+t*(b 1-0) = q 1 at h1
      rw [←h0,←h1]
      field_simp [ne_of_lt hb]
      ring

theorem actual_signed_fan_segment_radial_affine_chart
    (x0 x1 y1 : ℝ) (hx0 : x0 ≠ 0) (hy1 : y1 ≠ 0)
    (a b p : Plane) (ha : 0 < a 1) (hb : b 1 < 0)
    (hpp : p 1 ≠ 0)
    (hpseg : p ∈ segment ℝ (Plane.mk x0 0) (Plane.mk x1 y1))
    (hpray : p ∈ segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b) :
    ∃ L : Plane ≃ₜ ℝ × ℝ, ∃ α k : ℝ,
      (∀ q, L q = (q 1,q 0-x0-((x1-x0)/y1)*q 1)) ∧
      (∀ q ∈ segment ℝ (Plane.mk x0 0) (Plane.mk x1 y1), (L q).2 = 0) ∧
      (∀ q, 0 < q 1*p 1 → q ∈ segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b →
        (L q).1 = α+k*(L q).2) := by
  let m := (x1-x0)/y1
  let radialSlope := if 0 < p 1 then a 0/a 1 else b 0/b 1
  let slope := radialSlope-m
  have hseg : ∀ q ∈ segment ℝ (Plane.mk x0 0) (Plane.mk x1 y1), q 0 = x0+m*q 1 := by
    intro q hq
    rw [segment_eq_image'] at hq
    obtain ⟨t,ht,he⟩ := hq
    have h0 := congrArg (fun x : Plane => x 0) he
    have h1 := congrArg (fun x : Plane => x 1) he
    change x0+t*(x1-x0) = q 0 at h0
    change 0+t*(y1-0) = q 1 at h1
    dsimp [m]
    rw [←h0,←h1]
    field_simp
    ring
  have hrad0 := actual_signed_radial_segment_graph a b p p ha hb hpp (mul_self_pos.mpr hpp) hpray
  have hrad : p 0 = radialSlope*p 1 := hrad0
  have he : slope*p 1 = x0 := by
    have hh := hseg p hpseg
    dsimp [slope]
    nlinarith only [hh,hrad]
  have hslope : slope ≠ 0 := by intro hz; rw [hz,zero_mul] at he; exact hx0 he.symm
  let L : Plane ≃ₜ ℝ × ℝ := {
    toFun := fun q => (q 1,q 0-x0-m*q 1)
    invFun := fun q => Plane.mk (q.2+x0+m*q.1) q.1
    left_inv := by intro q; ext i; fin_cases i <;> dsimp [Plane.mk] <;> ring
    right_inv := by intro q; ext <;> dsimp [Plane.mk] <;> ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  refine ⟨L,x0/slope,1/slope,(fun q => rfl),?_,?_⟩
  · intro q hq
    change q 0-x0-m*q 1 = 0
    rw [hseg q hq]
    ring
  · intro q hq hqray
    have hh0 := actual_signed_radial_segment_graph a b p q ha hb hpp hq hqray
    have hh : q 0 = radialSlope*q 1 := hh0
    change q 1 = x0/slope+(1/slope)*(q 0-x0-m*q 1)
    have heq : q 0-x0-m*q 1 = slope*q 1-x0 := by
      rw [hh]
      dsimp only [slope]
      ring
    rw [heq]
    field_simp [hslope]
    ring

end CurveComplex
