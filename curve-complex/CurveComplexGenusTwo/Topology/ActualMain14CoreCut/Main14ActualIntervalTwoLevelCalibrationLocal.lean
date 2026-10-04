import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualEmbeddedPairTrackInverseLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
set_option maxHeartbeats 3000000

-- Coordinate calibration for the SAME supplied annulus; the G3 motion itself
-- is reused unchanged after this actual parameter homeomorphism.
example (b : ℝ) (hb0 : 1/2 < b) (hb1 : b < 1) :
    ∃ h : Interval ≃ₜ Interval,
      h 0 = 0 ∧ h 1 = 1 ∧
      h ⟨1/3,by norm_num⟩ = ⟨1/2,by norm_num⟩ ∧
      (h ⟨2/3,by norm_num⟩ : ℝ) = b := by
  audit_main14_base3
    let f : Interval → ℝ := fun u =>
      if (u:ℝ) ≤ 1/3 then 3*(u:ℝ)/2
      else if (u:ℝ) ≤ 2/3 then 1/2+3*(b-1/2)*((u:ℝ)-1/3)
      else b+3*(1-b)*((u:ℝ)-2/3)
    have hfmem (u : Interval) : f u ∈ Set.Icc (0:ℝ) 1 := by
      dsimp [f]
      split_ifs <;> constructor <;> nlinarith [u.property.1,u.property.2]
    have hc2 : Continuous (fun u : Interval =>
        if (u:ℝ) ≤ 2/3 then 1/2+3*(b-1/2)*((u:ℝ)-1/3)
        else b+3*(1-b)*((u:ℝ)-2/3)) := by
      apply continuous_if_le (by fun_prop) continuous_const (by fun_prop) (by fun_prop)
      intro u hu
      rw [hu]
      ring
    have hfc : Continuous f := by
      apply continuous_if_le (by fun_prop) continuous_const (by fun_prop) hc2.continuousOn
      intro u hu
      rw [hu,if_pos (by norm_num : (1/3:ℝ) ≤ 2/3)]
      ring
    have hmono : StrictMono f := by
      intro x y hxy
      have hxyR : (x:ℝ) < (y:ℝ) := hxy
      have hcentral : 0 < 3*(b-1/2)*((y:ℝ)-(x:ℝ)) :=
        mul_pos (mul_pos (by norm_num) (sub_pos.mpr hb0)) (sub_pos.mpr hxyR)
      have houter : 0 < 3*(1-b)*((y:ℝ)-(x:ℝ)) :=
        mul_pos (mul_pos (by norm_num) (sub_pos.mpr hb1)) (sub_pos.mpr hxyR)
      dsimp [f]
      split_ifs <;> nlinarith [x.property.1,x.property.2,y.property.1,y.property.2]
    let F : Interval → Interval := fun u => ⟨f u,hfmem u⟩
    have hFc : Continuous F := hfc.subtype_mk _
    have hF0 : F 0 = 0 := Subtype.ext (by norm_num [F,f])
    have hF1 : F 1 = 1 := Subtype.ext (by norm_num [F,f]; ring)
    have hFs : Function.Surjective F := by
      have hconn := (isConnected_range hFc).isPreconnected.ordConnected
      intro u
      exact hconn.out ⟨0,hF0⟩ ⟨1,hF1⟩ u.property
    have hFi : Function.Injective F := by
      intro x y hxy
      exact hmono.injective (congrArg Subtype.val hxy)
    let h : Interval ≃ₜ Interval :=
      (Equiv.ofBijective F ⟨hFi,hFs⟩).toHomeomorphOfContinuousClosed hFc hFc.isClosedMap
    refine ⟨h,hF0,hF1,?_,?_⟩
    · apply Subtype.ext
      change f ⟨1/3,by norm_num⟩ = 1/2
      norm_num [f]
    · change f ⟨2/3,by norm_num⟩ = b
      norm_num [f]
      ring
end CurveComplex.HyperellipticModel
