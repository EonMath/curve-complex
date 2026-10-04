import CurveComplexGenusTwo.Filtration.Geometry.ActualClosedObstacleRadialEnlargement

namespace CurveComplex
open Set Topology Schoenflies
set_option maxHeartbeats 4000000

/-- A uniformly small actual radial push moves the model square boundary off
itself while fixing every actual finite mark away from that boundary and
fixing the exterior of a fixed compact neighborhood. -/
theorem actual_finite_marked_radial_parallel
    (B : Finset (ℝ × ℝ)) (hB : ∀ z ∈ B, ‖z‖ ≠ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/8 ∧ ∃ H : AmbientIsotopy (ℝ × ℝ),
      (∀ t z, z ∈ B → H.map (t,z) = z) ∧
      (∀ z, ‖z‖ = 1 → ‖H.finalMap z‖ = 1+ε) ∧
      (∀ t z, 2 ≤ ‖z‖ → H.map (t,z) = z) := by
  classical
  have small : ∀ B : Finset (ℝ × ℝ), (∀ z ∈ B, ‖z‖ ≠ 1) →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/8 ∧ ∀ z ∈ B, 2*ε ≤ |‖z‖-1| := by
    intro B
    induction B using Finset.induction_on with
    | empty => intro h; exact ⟨1/8,by norm_num,by norm_num,by simp⟩
    | @insert z B hz ih =>
      intro h
      obtain ⟨ε,hε,hεb,hεB⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
      have ha : 0 < |‖z‖-1| := abs_pos.mpr (sub_ne_zero.mpr (h z (Finset.mem_insert_self _ _)))
      refine ⟨min ε (|‖z‖-1|/2),lt_min hε (by positivity),(min_le_left _ _).trans hεb,?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with hxz | hx
      · subst x
        have h := min_le_right ε (|‖z‖-1|/2); linarith
      · have h := min_le_left ε (|‖z‖-1|/2); have hb := hεB x hx; linarith
  obtain ⟨ε,hε,hεb,hεB⟩ := small B hB
  obtain ⟨H,hmap,hzero,hnorm⟩ := actual_relative_radial_isotopy (fun _ => ε)
    continuous_const (fun _ => hε.le) (fun _ => hεb)
  refine ⟨ε,hε,hεb,H,?_,hnorm,?_⟩
  · intro t z hz
    by_cases hzeroz : z = 0
    · subst z; rw [hmap]; simp
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hzeroz
    have ht : t.val*ε ≤ ε := mul_le_of_le_one_left hε.le t.property.2
    have hb := hεB z hz
    have hv : t.val*ε-|‖z‖-1|/2 ≤ 0 := by linarith
    rw [hmap,max_eq_left hv,add_zero,div_self hn,one_smul]
  · intro t z hz
    have hn : ‖z‖ ≠ 0 := by linarith
    have ht : t.val*ε ≤ ε := mul_le_of_le_one_left hε.le t.property.2
    have ha : |‖z‖-1| = ‖z‖-1 := abs_of_nonneg (by linarith)
    have hv : t.val*ε-|‖z‖-1|/2 ≤ 0 := by rw [ha]; linarith
    rw [hmap,max_eq_left hv,add_zero,div_self hn,one_smul]
end CurveComplex
