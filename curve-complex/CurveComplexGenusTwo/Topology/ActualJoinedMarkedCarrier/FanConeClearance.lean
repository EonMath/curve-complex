import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.UniformContactPatchTools
namespace CurveComplex
open Set Topology Schoenflies
set_option maxHeartbeats 5000000

theorem actual_finite_fan_positive_cone_clearance {I : Type} [Fintype I]
    (v : I → Plane) (hside : ∀ i, v i 1=0 → v i 0 ≤ 0) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ ∀ z : Plane,
      0 < z 0 → -κ*z 0 < z 1 → z 1 < κ*z 0 →
        ∀ i, z ∉ segment ℝ (0:Plane) (v i) := by
  classical
  let Q : I → Set Plane := fun i => if v i 1=0 then {z | z 0 ≤ 0}
    else {z | v i 1*z 0-v i 0*z 1=0}
  have hQclosed (i : I) : IsClosed (Q i) := by
    dsimp [Q]
    split_ifs
    · exact isClosed_le (by fun_prop) continuous_const
    · exact isClosed_eq (by fun_prop) continuous_const
  let W : Set Plane := (⋃ i, Q i)ᶜ
  have hW : IsOpen W := (isClosed_iUnion_of_finite hQclosed).isOpen_compl
  have hbase : Plane.mk 1 0 ∈ W := by
    intro hh
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hh
    dsimp [Q] at hi
    split_ifs at hi with hv
    · change (1:ℝ) ≤ 0 at hi; linarith
    · change v i 1*1-v i 0*0=0 at hi
      exact hv (by simpa using hi)
  let q : ℝ → Plane := fun h => Plane.mk 1 h
  have hq : Continuous q := by fun_prop
  have hz : (0:ℝ) ∈ q ⁻¹' W := hbase
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (hW.preimage hq) 0 hz
  let κ := min ε 1
  have hκ : 0 < κ := lt_min hε zero_lt_one
  refine ⟨κ,hκ,min_le_right _ _,?_⟩
  intro z hx hlo hhi i hzseg
  let h := z 1/z 0
  have habs : |h| < ε := lt_of_lt_of_le (abs_lt.mpr
    ⟨(lt_div_iff₀ hx).mpr hlo,(div_lt_iff₀ hx).mpr hhi⟩) (min_le_left ε 1)
  have hendpoint : Plane.mk 1 h ∈ W := hball (by
    simpa [Metric.mem_ball,Real.dist_eq] using habs)
  have hnotQ : Plane.mk 1 h ∉ Q i := fun hh => hendpoint (Set.mem_iUnion.mpr ⟨i,hh⟩)
  rw [segment_eq_image'] at hzseg
  obtain ⟨u,hu,he⟩ := hzseg
  have hz0 : z 0=u*v i 0 := by
    have hh := congrArg (fun q : Plane => q 0) he
    change 0+u*(v i 0-0)=z 0 at hh
    simpa using hh.symm
  have hz1 : z 1=u*v i 1 := by
    have hh := congrArg (fun q : Plane => q 1) he
    change 0+u*(v i 1-0)=z 1 at hh
    simpa using hh.symm
  apply hnotQ
  dsimp [Q]
  split_ifs with hv
  · change (1:ℝ) ≤ 0
    have hn : z 0 ≤ 0 := hz0 ▸ mul_nonpos_of_nonneg_of_nonpos hu.1 (hside i hv)
    linarith
  · change v i 1*1-v i 0*h=0
    have hc : (v i 1-v i 0*h)*z 0=0 := by
      calc
        (v i 1-v i 0*h)*z 0 = v i 1*z 0-v i 0*z 1 := by
          dsimp [h]
          field_simp
        _ = 0 := by rw [hz0,hz1]; ring
    simpa using (mul_eq_zero.mp hc).resolve_right (ne_of_gt hx)
end CurveComplex
