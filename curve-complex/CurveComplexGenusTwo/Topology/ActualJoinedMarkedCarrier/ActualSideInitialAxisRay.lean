import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualChartArcTools
import Mathlib.Topology.Order.IntermediateValue
namespace CurveComplex
open Set Topology Metric Schoenflies
set_option maxHeartbeats 5000000

theorem actual_embedded_side_initial_chart_axis_ray
    {S : Type} [TopologicalSpace S]
    (side : C(Interval,S)) (hside : IsEmbedding side)
    (F : OpenPartialHomeomorph S Plane) (h0 : side 0 ∈ F.source) (hF0 : F (side 0)=0)
    (hAxis : ∀ t : Interval, side t ∈ F.source → F (side t) 1=0) :
    ∃ σ ell : ℝ, (σ=-1 ∨ σ=1) ∧ 0 < ell ∧
      ∀ x ∈ Icc (0:ℝ) ell, Plane.mk (σ*x) 0 ∈ F.target ∧
        F.symm (Plane.mk (σ*x) 0) ∈ range side := by
  have hOpen : IsOpen (side ⁻¹' F.source) := F.open_source.preimage side.continuous
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hOpen 0 h0
  let r := min ε 1 / 2
  have hr : 0 < r := half_pos (lt_min hε zero_lt_one)
  have hrε : r < ε := by dsimp [r]; linarith [min_le_left ε 1]
  have hr1 : r < 1 := by dsimp [r]; linarith [min_le_right ε 1]
  let k : Interval → Interval := fun t => ⟨r*t.val,
    mul_nonneg hr.le t.property.1,
    (mul_le_of_le_one_right hr.le t.property.2).trans hr1.le⟩
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hS (t : Interval) : side (k t) ∈ F.source := hball (by
    change dist (k t) (0:Interval)<ε
    rw [Subtype.dist_eq,Real.dist_eq]
    change |r*t.val-0|<ε
    rw [sub_zero,abs_of_nonneg (mul_nonneg hr.le t.property.1)]
    exact (mul_le_of_le_one_right hr.le t.property.2).trans_lt hrε)
  let β : Interval → ℝ := fun t => F (side (k t)) 0
  have hβ : Continuous β := (show Continuous (fun z : Plane => z 0) by fun_prop).comp
    (F.continuousOn.comp_continuous (side.continuous.comp hk) hS)
  have hβ0 : β 0=0 := by
    have hk0 : k 0=0 := by apply Subtype.ext; simp [k]
    change F (side (k 0)) 0=0
    rw [hk0,hF0]
    rfl
  have hβ1 : β 1≠0 := by
    intro he
    have hsame : F (side (k 1))=F (side 0) := by
      rw [hF0]
      ext i
      fin_cases i
      · exact he
      · exact hAxis (k 1) (hS 1)
    have hk0 : k 1=0 := hside.injective (F.injOn (hS 1) h0 hsame)
    have hr0 := congrArg Subtype.val hk0
    change r*1=0 at hr0
    linarith
  have hRange : OrdConnected (range β) := (isPreconnected_range hβ).ordConnected
  have hLift (x : ℝ) (hx : x ∈ uIcc (β 0) (β 1)) :
      Plane.mk x 0 ∈ F.target ∧ F.symm (Plane.mk x 0) ∈ range side := by
    obtain ⟨t,ht⟩ := hRange.uIcc_subset (Set.mem_range_self 0) (Set.mem_range_self 1) hx
    have he : F (side (k t))=Plane.mk x 0 := by
      ext i
      fin_cases i
      · exact ht
      · exact hAxis (k t) (hS t)
    refine ⟨he ▸ F.map_source (hS t),?_⟩
    refine ⟨k t,?_⟩
    rw [← he,F.left_inv (hS t)]
  by_cases hb : 0 < β 1
  · refine ⟨1,β 1,Or.inr rfl,hb,?_⟩
    intro x hx
    apply hLift
    simpa [hβ0,uIcc_of_le hb.le] using hx
  · have hn : β 1 < 0 := lt_of_le_of_ne (le_of_not_gt hb) hβ1
    refine ⟨-1,-β 1,Or.inl rfl,neg_pos.mpr hn,?_⟩
    intro x hx
    apply hLift
    rw [hβ0,uIcc_of_ge hn.le]
    simp only [neg_one_mul]
    exact ⟨by linarith [hx.2],by linarith [hx.1]⟩
end CurveComplex
