import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualEndpointPortSelection
namespace CurveComplex
open Set Topology Schoenflies Metric
/-- Select one ACTUAL positive width for a finite family of prescribed plane
displacements. Every resulting displacement lies in the prescribed ball. -/
theorem source_finite_small_displacement_width
    (K : Type) [Fintype K] (v : K → Plane) (r : ℝ) (hr : 0<r) :
    ∃ ε : ℝ, 0<ε ∧ ε≤1/2 ∧ ∀ k, ‖ε • v k‖<r := by
  let U : Set ℝ := ⋂ k, {ε | ‖ε • v k‖<r}
  have hU : IsOpen U := isOpen_iInter_of_finite (fun k =>
    isOpen_lt (by fun_prop) continuous_const)
  have hzero : (0:ℝ) ∈ U := by
    apply Set.mem_iInter.mpr
    intro k
    change ‖(0:ℝ) • v k‖<r
    simp only [zero_smul,norm_zero]
    exact hr
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hU 0 hzero
  let ε : ℝ := min (δ/2) (1/2)
  have hε : 0<ε := lt_min (half_pos hδ) (by norm_num)
  have hεδ : ε<δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεU : ε ∈ U := hball (by
    rw [mem_ball,Real.dist_eq,sub_zero,abs_of_pos hε]
    exact hεδ)
  exact ⟨ε,hε,min_le_right _ _,fun k => Set.mem_iInter.mp hεU k⟩

/-- Actual signed widths match any two finite corner normal-frame weights.
They are nonzero, uniformly small, and both start-corner shifts are positive;
the finish signs are free, as required by the one-extra-contact budget. -/
theorem source_two_corner_signed_frame_widths
    (α β : Bool → ℝ) (hα : ∀ k, α k ≠ 0) (hβ : ∀ k, β k ≠ 0)
    (r : ℝ) (hr : 0<r) :
    ∃ w z : Set.Icc (-1:ℝ) 1,
      (w:ℝ)≠0 ∧ (z:ℝ)≠0 ∧
      ∃ v : Bool → Plane,
        (∀ k, v k=Plane.mk (α k*(w:ℝ)) (β k*(z:ℝ))) ∧
        (∀ k, ‖v k‖<r) ∧ (∀ k, v k 0≠0 ∧ v k 1≠0) ∧
        0<v false 0 ∧ 0<v false 1 := by
  classical
  let sx : ℝ := if 0<α false then 1 else -1
  let sy : ℝ := if 0<β false then 1 else -1
  have hsx : sx=1 ∨ sx=-1 := by dsimp [sx]; split <;> simp
  have hsy : sy=1 ∨ sy=-1 := by dsimp [sy]; split <;> simp
  have hsx0 : sx≠0 := by rcases hsx with h | h <;> rw [h] <;> norm_num
  have hsy0 : sy≠0 := by rcases hsy with h | h <;> rw [h] <;> norm_num
  have hαs : 0<α false*sx := by
    dsimp [sx]
    split_ifs with h
    · simpa using h
    · have hn : α false<0 := lt_of_le_of_ne (le_of_not_gt h) (hα false)
      simpa using neg_pos.mpr hn
  have hβs : 0<β false*sy := by
    dsimp [sy]
    split_ifs with h
    · simpa using h
    · have hn : β false<0 := lt_of_le_of_ne (le_of_not_gt h) (hβ false)
      simpa using neg_pos.mpr hn
  let a : Bool → Plane := fun k => Plane.mk (α k*sx) (β k*sy)
  obtain ⟨ε,hε,hεhalf,hsmall⟩ := source_finite_small_displacement_width Bool a r hr
  let w : Set.Icc (-1:ℝ) 1 := ⟨sx*ε,by
    rcases hsx with h | h <;> rw [h] <;> constructor <;> nlinarith⟩
  let z : Set.Icc (-1:ℝ) 1 := ⟨sy*ε,by
    rcases hsy with h | h <;> rw [h] <;> constructor <;> nlinarith⟩
  have hw : (w:ℝ)≠0 := mul_ne_zero hsx0 hε.ne'
  have hz : (z:ℝ)≠0 := mul_ne_zero hsy0 hε.ne'
  let v : Bool → Plane := fun k => ε • a k
  have hvc (k) : v k=Plane.mk (α k*(w:ℝ)) (β k*(z:ℝ)) := by
    ext j
    fin_cases j
    · change ε*(α k*sx)=α k*(sx*ε); ring
    · change ε*(β k*sy)=β k*(sy*ε); ring
  refine ⟨w,z,hw,hz,v,hvc,hsmall,?_,?_,?_⟩
  · intro k
    rw [hvc]
    exact ⟨mul_ne_zero (hα k) hw,mul_ne_zero (hβ k) hz⟩
  · rw [hvc]
    change 0<α false*(sx*ε)
    rw [← mul_assoc]
    exact mul_pos hαs hε
  · rw [hvc]
    change 0<β false*(sy*ε)
    rw [← mul_assoc]
    exact mul_pos hβs hε
end CurveComplex
#print axioms CurveComplex.source_finite_small_displacement_width
#print axioms CurveComplex.source_two_corner_signed_frame_widths
