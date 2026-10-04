import CurveComplexGenusTwo.Topology.ActualHarerCrossingAxes.ActualHarerCornerGeometryDefinitions
import CurveComplexGenusTwo.Topology.Smoothing.PrescribedPairRadializationProof

open Set Topology Metric Schoenflies CurveComplex
namespace ActualHarerCornerGeometry

noncomputable def radialMovingCoordinates (v : Plane) (hv : v ≠ 0) : Plane ≃ₜ (ℝ × ℝ) := by
  let n := v 0 ^ 2 + v 1 ^ 2
  have hn : n ≠ 0 := by
    intro h
    have h0 : v 0 = 0 := by dsimp [n] at h; nlinarith [sq_nonneg (v 1)]
    have h1 : v 1 = 0 := by dsimp [n] at h; nlinarith [sq_nonneg (v 0)]
    exact hv (by ext i; fin_cases i <;> assumption)
  exact {
    toEquiv := {
      toFun := fun z => (Plane.det v z, (v 0*z 0+v 1*z 1)/n)
      invFun := fun z => Plane.mk (z.2*v 0-z.1*v 1/n) (z.2*v 1+z.1*v 0/n)
      left_inv := by
        intro z
        ext i
        fin_cases i <;> dsimp [Plane.det, Plane.mk] <;> field_simp <;> dsimp [n] <;> ring
      right_inv := by
        intro z
        apply Prod.ext <;> dsimp [Plane.det, Plane.mk] <;> field_simp <;> dsimp [n] <;> ring }
    continuous_toFun := by dsimp [Plane.det]; fun_prop
    continuous_invFun := by fun_prop }

@[simp] theorem radialMovingCoordinates_zero (v : Plane) (hv : v ≠ 0) :
    radialMovingCoordinates v hv 0 = (0,0) := by
  simp [radialMovingCoordinates,Plane.det]

@[simp] theorem radialMovingCoordinates_self (v : Plane) (hv : v ≠ 0) :
    radialMovingCoordinates v hv v = (0,1) := by
  have hn : v 0 ^ 2 + v 1 ^ 2 ≠ 0 := by
    intro h
    have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 1)]
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0)]
    exact hv (by ext i; fin_cases i <;> assumption)
  apply Prod.ext
  · change Plane.det v v = 0; exact Plane.det_self v
  · change (v 0*v 0+v 1*v 1)/(v 0^2+v 1^2) = 1
    simpa only [pow_two] using div_self hn



@[simp] theorem radialMovingCoordinates_smul (v : Plane) (hv : v ≠ 0) (r : ℝ) (z : Plane) :
    radialMovingCoordinates v hv (r • z) = r • radialMovingCoordinates v hv z := by
  apply Prod.ext
  · exact Plane.det_smul_right r v z
  · change (v 0*(r*z 0)+v 1*(r*z 1))/(v 0^2+v 1^2) =
      r*((v 0*z 0+v 1*z 1)/(v 0^2+v 1^2))
    ring

theorem radial_axis_segment_iff (v : Plane) (hv : v ≠ 0) (r : ℝ)
    (hr : r < ‖v‖) (x : Plane) (hx : ‖x‖ ≤ r) :
    x ∈ segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v) ↔ Plane.det v x = 0 := by
  constructor
  · intro hm
    rcases hm with hm | hm
    · obtain ⟨a,b,ha,hb,hab,rfl⟩ := hm
      simp [Plane.det_add_right]
    · obtain ⟨a,b,ha,hb,hab,rfl⟩ := hm
      simp [Plane.det_add_right,Plane.det]
      <;> ring
  · intro hdet
    obtain ⟨a,ha⟩ := (Plane.det_eq_zero_iff_smul v x hv).mp hdet
    have hna : |a| ≤ 1 := by
      have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
      rw [ha,norm_smul,Real.norm_eq_abs] at hx
      nlinarith
    rcases le_total 0 a with hp|hn
    · apply Or.inl
      rw [ha]
      exact ⟨1-a,a,sub_nonneg.mpr ((le_abs_self a).trans hna),hp,by ring,by simp⟩
    · apply Or.inr
      have hxneg : x = (-a) • (-v) := by rw [ha]; module
      rw [hxneg]
      exact ⟨1-(-a),-a,sub_nonneg.mpr ((neg_le_abs a).trans hna),
        neg_nonneg.mpr hn,by ring,by simp⟩

noncomputable def radialHalfplaneShear (a b : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toEquiv := {
    toFun := fun z => (z.1,z.2-(a*max z.1 0+b*min z.1 0))
    invFun := fun z => (z.1,z.2+(a*max z.1 0+b*min z.1 0))
    left_inv := by intro z; apply Prod.ext <;> dsimp <;> ring
    right_inv := by intro z; apply Prod.ext <;> dsimp <;> ring }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop





@[simp] theorem radialHalfplaneShear_axis (a b y : ℝ) :
    radialHalfplaneShear a b (0,y) = (0,y) := by
  simp [radialHalfplaneShear]

theorem radialHalfplaneShear_positive (u v : ℝ × ℝ) (hu : 0 < u.1) (hv : v.1 < 0)
    (t : ℝ) (ht : 0 ≤ t) :
    radialHalfplaneShear (u.2/u.1) (v.2/v.1) (t • u) = (t*u.1,0) := by
  apply Prod.ext
  · rfl
  · change t*u.2 - (u.2/u.1*max (t*u.1) 0 + v.2/v.1*min (t*u.1) 0) = 0
    rw [max_eq_left (mul_nonneg ht hu.le),min_eq_right (mul_nonneg ht hu.le)]
    field_simp [ne_of_gt hu,ne_of_lt hv]
    <;> ring

theorem radialHalfplaneShear_negative (u v : ℝ × ℝ) (hu : 0 < u.1) (hv : v.1 < 0)
    (t : ℝ) (ht : 0 ≤ t) :
    radialHalfplaneShear (u.2/u.1) (v.2/v.1) (t • v) = (t*v.1,0) := by
  apply Prod.ext
  · rfl
  · change t*v.2 - (u.2/u.1*max (t*v.1) 0 + v.2/v.1*min (t*v.1) 0) = 0
    rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos ht hv.le),
      min_eq_left (mul_nonpos_of_nonneg_of_nonpos ht hv.le)]
    field_simp [ne_of_gt hu,ne_of_lt hv]
    <;> ring

end ActualHarerCornerGeometry

namespace ActualHarerCornerGeometry

theorem positive_interval_germ_sample {S : Type*} [TopologicalSpace S]
    (β : Interval → S) (hβ : Continuous β) (W : Set S) (hW : IsOpen W)
    (hβ0 : β 0 ∈ W) (c : Interval) (hc : 0 < c.val) :
    ∃ t : Interval, 0 < t.val ∧ t < c ∧ β t ∈ W := by
  obtain ⟨r,hr,hrr⟩ := Metric.isOpen_iff.mp (hW.preimage hβ) 0 hβ0
  let t : Interval := ⟨min r c.val / 2,⟨half_pos (lt_min hr hc) |>.le,by
    have hm := min_le_right r c.val
    linarith [c.property.2]⟩⟩
  have ht0 : 0 < t.val := half_pos (lt_min hr hc)
  have htc : t < c := by change min r c.val / 2 < c.val; linarith [min_le_right r c.val]
  refine ⟨t,ht0,htc,hrr ?_⟩
  rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
  change |t.val-0| < r
  rw [sub_zero,abs_of_pos ht0]
  change min r c.val / 2 < r
  linarith [min_le_left r c.val]

end ActualHarerCornerGeometry

namespace ActualHarerCornerGeometry

@[simp] theorem radialHalfplaneShear_smul (a b t : ℝ) (ht : 0 ≤ t) (z : ℝ × ℝ) :
    radialHalfplaneShear a b (t • z) = t • radialHalfplaneShear a b z := by
  apply Prod.ext
  · rfl
  · change t*z.2 - (a*max (t*z.1) 0+b*min (t*z.1) 0) =
      t*(z.2-(a*max z.1 0+b*min z.1 0))
    rw [← mul_zero t,← mul_max_of_nonneg _ _ ht,← mul_min_of_nonneg _ _ ht]
    ring

noncomputable def horizontalReflection (σ : ℝ) (hσ : σ = -1 ∨ σ = 1) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toEquiv := {
    toFun := fun z => (σ*z.1,z.2)
    invFun := fun z => (σ*z.1,z.2)
    left_inv := by intro z; rcases hσ with rfl | rfl <;> simp
    right_inv := by intro z; rcases hσ with rfl | rfl <;> simp }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop



@[simp] theorem horizontalReflection_smul (σ : ℝ) (hσ : σ = -1 ∨ σ = 1)
    (r : ℝ) (z : ℝ × ℝ) : horizontalReflection σ hσ (r • z) = r • horizontalReflection σ hσ z := by
  apply Prod.ext
  · change σ*(r*z.1) = r*(σ*z.1); ring
  · rfl

@[simp] theorem horizontalReflection_axis (σ : ℝ) (hσ : σ = -1 ∨ σ = 1) (y : ℝ) :
    horizontalReflection σ hσ (0,y) = (0,y) := by simp [horizontalReflection]

theorem axis_ray_membership (B : Plane ≃ₜ (ℝ × ℝ))
    (hB0 : B 0 = (0,0)) (hBsmul : ∀ a : ℝ, 0 ≤ a → ∀ z, B (a • z) = a • B z)
    (v z : Plane) (c : ℝ) (hc : c ≠ 0) (hv : B v = (c,0))
    (hnorm : ‖z‖ < ‖v‖) :
    z ∈ segment ℝ (0:Plane) v ↔ (B z).2 = 0 ∧ 0 ≤ (B z).1/c := by
  constructor
  · rintro ⟨a,b,ha,hb,hab,he⟩
    have hz : z = b • v := by simpa using he.symm
    rw [hz,hBsmul b hb,hv]
    change b*0 = 0 ∧ 0 ≤ (b*c)/c
    simp [hc,hb]
  · rintro ⟨hz,hsgn⟩
    let a : ℝ := (B z).1/c
    have he : B z = B (a • v) := by
      rw [hBsmul a hsgn,hv]
      apply Prod.ext
      · change (B z).1 = a*c
        exact (div_mul_cancel₀ _ hc).symm
      · simpa using hz
    have hez := B.injective he
    have hvne : v ≠ 0 := by intro h; rw [h,hB0] at hv; exact hc (congrArg Prod.fst hv).symm
    have hnv := norm_pos_iff.mpr hvne
    have ha : a ≤ 1 := by
      rw [hez,norm_smul,Real.norm_eq_abs,abs_of_nonneg hsgn] at hnorm
      nlinarith
    exact ⟨1-a,a,sub_nonneg.mpr ha,hsgn,by ring,by simpa using hez.symm⟩

end ActualHarerCornerGeometry

namespace ActualHarerCornerGeometry

theorem ordered_ray_signs {α : Type*} [LinearOrder α] (u c : α) (x : ℝ)
    (hz : x = 0 ↔ u = c)
    (hrays : (x ≤ 0 ∧ u ≤ c) ∨ (0 ≤ x ∧ c ≤ u)) :
    (x < 0 ↔ u < c) ∧ (0 < x ↔ c < u) := by
  constructor
  · constructor
    · intro hx
      rcases hrays with hh | hh
      · exact lt_of_le_of_ne hh.2 (fun he => (ne_of_lt hx) (hz.mpr he))
      · exact False.elim (not_le_of_gt hx hh.1)
    · intro hu
      rcases hrays with hh | hh
      · exact lt_of_le_of_ne hh.1 (fun he => (ne_of_lt hu) (hz.mp he))
      · exact False.elim (not_le_of_gt hu hh.2)
  · constructor
    · intro hx
      rcases hrays with hh | hh
      · exact False.elim (not_le_of_gt hx hh.1)
      · exact lt_of_le_of_ne hh.2 (fun he => (ne_of_gt hx) (hz.mpr he.symm))
    · intro hu
      rcases hrays with hh | hh
      · exact False.elim (not_le_of_gt hu hh.2)
      · exact lt_of_le_of_ne hh.1 (fun he => (ne_of_gt hu) (hz.mp he.symm))

end ActualHarerCornerGeometry
