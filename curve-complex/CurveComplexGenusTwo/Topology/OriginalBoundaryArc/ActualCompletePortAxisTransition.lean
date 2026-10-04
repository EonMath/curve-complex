import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.AxisChartSideSeparation
namespace CurveComplex
open Set
set_option maxHeartbeats 2000000
/-- Transfer an actual complete charted port to another actual axis chart.
A positive pair of port parameters with opposite sides is produced. -/
theorem actual_charted_port_complete_opposite_sides
    {S : Type} [TopologicalSpace S]
    (P : C(Icc (-1 : ℝ) 1,S))
    (A B : OpenPartialHomeomorph S (ℝ × ℝ))
    (hA : ∀ w, P w ∈ A.source ∧ A (P w) = (0,(w:ℝ)/2))
    (hB : P ⟨0,by norm_num⟩ ∈ B.source)
    (haxis : ∀ x ∈ A.source ∩ B.source, (A x).2 = 0 ↔ (B x).2 = 0) :
    ∃ r : ℝ, ∃ hr : 0 < r ∧ r ≤ 1,
      (∀ w : Icc (-1 : ℝ) 1,
        P ⟨r*(w:ℝ),by constructor <;> nlinarith [hr.1,hr.2,w.property.1,w.property.2]⟩ ∈ B.source) ∧
      P ⟨r,by constructor <;> linarith [hr.1,hr.2]⟩ ∈ B.source ∧
      P ⟨-r,by constructor <;> linarith [hr.1,hr.2]⟩ ∈ B.source ∧
      ((0 < (B (P ⟨r,by constructor <;> linarith [hr.1,hr.2]⟩)).2 ∧
          (B (P ⟨-r,by constructor <;> linarith [hr.1,hr.2]⟩)).2 < 0) ∨
       ((B (P ⟨r,by constructor <;> linarith [hr.1,hr.2]⟩)).2 < 0 ∧
          0 < (B (P ⟨-r,by constructor <;> linarith [hr.1,hr.2]⟩)).2)) := by
  let T := A.symm.trans B
  have hA0 : A (P ⟨0,by norm_num⟩) = (0,0) := by simpa using (hA ⟨0,by norm_num⟩).2
  have h0target : (0,0) ∈ A.target := hA0 ▸ A.map_source (hA ⟨0,by norm_num⟩).1
  have h0inv : A.symm (0,0) = P ⟨0,by norm_num⟩ := by
    rw [← hA0]
    exact A.left_inv (hA ⟨0,by norm_num⟩).1
  have h0T : (0,0) ∈ T.source := by
    change (0,0) ∈ A.target ∩ A.symm ⁻¹' B.source
    refine ⟨h0target,?_⟩
    change A.symm (0,0) ∈ B.source
    rw [h0inv]
    exact hB
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (T.open_source.mem_nhds h0T)
  let r := min (ε/2) (1/2)
  have hr : 0 < r ∧ r ≤ 1 :=
    ⟨lt_min (half_pos hε) (by norm_num),(min_le_right _ _).trans (by norm_num)⟩
  have hrε : r < ε := (min_le_left _ _).trans_lt (by linarith)
  have hO : Ioo (-r) r ×ˢ Ioo (-r) r ⊆ T.source := by
    intro z hz
    apply hball
    rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero]
    exact max_lt (abs_lt.mpr (by constructor <;> linarith [hz.1.1,hz.1.2]))
      (abs_lt.mpr (by constructor <;> linarith [hz.2.1,hz.2.2]))
  have hTa : ∀ z ∈ Ioo (-r) r ×ˢ Ioo (-r) r, (T z).2=0 ↔ z.2=0 := by
    intro z hz
    have hzs := hO hz
    change z ∈ A.target ∩ A.symm ⁻¹' B.source at hzs
    have hx : A.symm z ∈ A.source ∩ B.source := ⟨A.map_target hzs.1,hzs.2⟩
    have hh := haxis (A.symm z) hx
    rw [A.right_inv hzs.1] at hh
    exact hh.symm
  obtain hside := actual_axis_chart_transverse_sides T r hr.1 hO hTa
  let p : Icc (-1 : ℝ) 1 := ⟨r,by constructor <;> linarith [hr.1,hr.2]⟩
  let n : Icc (-1 : ℝ) 1 := ⟨-r,by constructor <;> linarith [hr.1,hr.2]⟩
  have hport (w : Icc (-1 : ℝ) 1) : A.symm (0,(w:ℝ)/2)=P w := by
    rw [← (hA w).2]
    exact A.left_inv (hA w).1
  have hpT : (0,r/2) ∈ T.source := hO (by constructor <;> constructor <;> linarith [hr.1])
  have hnT : (0,-r/2) ∈ T.source := hO (by constructor <;> constructor <;> linarith [hr.1])
  have hpB : P p ∈ B.source := by
    have hh : (0,r/2) ∈ A.target ∩ A.symm ⁻¹' B.source := hpT
    have hh2 := hh.2
    change A.symm (0,r/2) ∈ B.source at hh2
    rw [hport p] at hh2
    exact hh2
  have hnB : P n ∈ B.source := by
    have hh : (0,-r/2) ∈ A.target ∩ A.symm ⁻¹' B.source := hnT
    have hh2 := hh.2
    change A.symm (0,-r/2) ∈ B.source at hh2
    rw [hport n] at hh2
    exact hh2
  refine ⟨r,hr,?_,hpB,hnB,?_⟩
  · intro w
    have hws : (0,r*(w:ℝ)/2) ∈ T.source := hO (by
      constructor
      · constructor <;> linarith [hr.1]
      · constructor <;> nlinarith [hr.1,w.property.1,w.property.2])
    change (0,r*(w:ℝ)/2) ∈ A.target ∩ A.symm ⁻¹' B.source at hws
    have hh := hws.2
    change A.symm (0,r*(w:ℝ)/2) ∈ B.source at hh
    rw [hport ⟨r*(w:ℝ),by constructor <;> nlinarith [hr.1,hr.2,w.property.1,w.property.2]⟩] at hh
    exact hh
  · change (0 < (B (A.symm (0,r/2))).2 ∧ (B (A.symm (0,-r/2))).2 < 0) ∨
    ((B (A.symm (0,r/2))).2 < 0 ∧ 0 < (B (A.symm (0,-r/2))).2) at hside
    rw [hport p,hport n] at hside
    exact hside
end CurveComplex
