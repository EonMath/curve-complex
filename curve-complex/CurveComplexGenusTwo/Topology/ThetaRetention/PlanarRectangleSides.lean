import CurveComplexGenusTwo.Topology.ThetaRetention.SurfaceLocalSides
import Schoenflies.Plane
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.Real

namespace CurveComplex
open Set Topology Schoenflies

/-- The open rectangle in Euclidean plane written in coordinates. -/
def thetaRect (l r b t : ℝ) : Set Plane := {z | l < z 0 ∧ z 0 < r ∧ b < z 1 ∧ z 1 < t}

theorem thetaRect_open (l r b t : ℝ) : IsOpen (thetaRect l r b t) := by
  have ho : IsOpen ((fun z : Plane => z 0) ⁻¹' Ioo l r ∩ (fun z : Plane => z 1) ⁻¹' Ioo b t) :=
    (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
  convert ho using 1
  ext z
  simp [thetaRect,and_assoc]

theorem thetaRect_connected {l r b t : ℝ} (hlr : l < r) (hbt : b < t) :
    IsConnected (thetaRect l r b t) := by
  have heq : thetaRect l r b t = (fun z : ℝ × ℝ => Plane.mk z.1 z.2) '' (Ioo l r ×ˢ Ioo b t) := by
    ext z
    constructor
    · intro hz
      refine ⟨(z 0,z 1),⟨⟨hz.1,hz.2.1⟩,hz.2.2⟩,?_⟩
      ext i
      fin_cases i <;> rfl
    · rintro ⟨⟨x,y⟩,hx,rfl⟩
      exact ⟨hx.1.1,hx.1.2,hx.2.1,hx.2.2⟩
  rw [heq]
  exact ((isConnected_Ioo hlr).prod (isConnected_Ioo hbt)).image _ (by fun_prop)

/-- Every point on the horizontal center lies in the closure of either open
half rectangle. This is stated directly in coordinates to simplify chart transport. -/
theorem thetaRect_center_mem_closure {l r b t x c : ℝ}
    (hx : l < x ∧ x < r) (hbc : b < c) (hct : c < t) :
    Plane.mk x c ∈ closure (thetaRect l r b c) ∧
      Plane.mk x c ∈ closure (thetaRect l r c t) := by
  have hleft : c ∈ closure (Ioo b c) := by rw [closure_Ioo hbc.ne]; exact ⟨hbc.le,le_rfl⟩
  have hright : c ∈ closure (Ioo c t) := by rw [closure_Ioo hct.ne]; exact ⟨le_rfl,hct.le⟩
  have himage (a d : ℝ) : (fun y : ℝ => Plane.mk x y) '' Ioo a d ⊆ thetaRect l r a d := by
    rintro z ⟨y,hy,rfl⟩
    exact ⟨hx.1,hx.2,hy.1,hy.2⟩
  have hc : Continuous (fun y : ℝ => Plane.mk x y) := by fun_prop
  exact ⟨closure_mono (himage b c) (hc.continuousWithinAt.mem_closure_image hleft),
    closure_mono (himage c t) (hc.continuousWithinAt.mem_closure_image hright)⟩

/-- A horizontal slit through a rectangle supplies the actual two local sides. -/
theorem thetaRect_local_sides
    {l r b t c : ℝ} (hlr : l < r) (hbc : b < c) (hct : c < t) :
    ∃ C : SurfaceLocalSides (thetaRect l r b t) {z : Plane | z 1 = c},
      C.nbhd = thetaRect l r b t := by
  refine ⟨{
    nbhd := thetaRect l r b t
    left := thetaRect l r b c
    right := thetaRect l r c t
    isOpen_nbhd := thetaRect_open _ _ _ _
    nbhd_subset := Subset.rfl
    nbhd_diff := ?_
    connected_left := thetaRect_connected hlr hbc
    connected_right := thetaRect_connected hlr hct
    limit_left := ?_
    limit_right := ?_ },rfl⟩
  · ext z
    constructor
    · rintro ⟨hz,hn⟩
      have hne : z 1 ≠ c := hn
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨hz.1,hz.2.1,hz.2.2.1,h⟩
      · exact Or.inr ⟨hz.1,hz.2.1,h,hz.2.2.2⟩
    · rintro (hz | hz)
      · exact ⟨⟨hz.1,hz.2.1,hz.2.2.1,hz.2.2.2.trans hct⟩,ne_of_lt hz.2.2.2⟩
      · exact ⟨⟨hz.1,hz.2.1,hbc.trans hz.2.2.1,hz.2.2.2⟩,ne_of_gt hz.2.2.1⟩
  · rintro z ⟨hz,hzc⟩
    have heq : z = Plane.mk (z 0) c := by
      ext i
      fin_cases i
      · rfl
      · exact hzc
    rw [heq]
    exact (thetaRect_center_mem_closure ⟨hz.1,hz.2.1⟩ hbc hct).1
  · rintro z ⟨hz,hzc⟩
    have heq : z = Plane.mk (z 0) c := by
      ext i
      fin_cases i
      · rfl
      · exact hzc
    rw [heq]
    exact (thetaRect_center_mem_closure ⟨hz.1,hz.2.1⟩ hbc hct).2

end CurveComplex
#print axioms CurveComplex.thetaRect_local_sides
