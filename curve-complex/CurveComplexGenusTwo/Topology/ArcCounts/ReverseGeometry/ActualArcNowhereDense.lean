import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import Mathlib.Topology.GDelta.Basic
namespace CurveComplex
open Set Topology Schoenflies
theorem source_actual_embedded_arc_nowhere_dense
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (f : C(Interval,S)) (hf : IsEmbedding f) : IsNowhereDense (range f) := by
  obtain ⟨E,hE,hcenter,_⟩ := source_whole_embedded_arc_strip f hf univ isOpen_univ (subset_univ _)
  apply (isCompact_range f.continuous).isClosed.isNowhereDense_iff.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨t,rfl⟩ := interior_subset hx
  let z : Set.Icc (-1:ℝ) 1 := ⟨0,by norm_num⟩
  let g : Set.Icc (-1:ℝ) 1 → S := fun s => E (t,s)
  have hg : Continuous g := hE.continuous.comp (continuous_const.prodMk continuous_id)
  have hopen : IsOpen (g ⁻¹' interior (range f)) := isOpen_interior.preimage hg
  have hz : z ∈ g ⁻¹' interior (range f) := by
    change E (t,z) ∈ interior (range f)
    rw [hcenter]
    exact hx
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen z hz
  let s : ℝ := min (ε/2) (1/2)
  have hspos : 0 < s := lt_min (half_pos hε) (by norm_num)
  have hs1 : s ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let w : Set.Icc (-1:ℝ) 1 := ⟨s,⟨by linarith,hs1⟩⟩
  have hwball : w ∈ Metric.ball z ε := by
    change dist s (0:ℝ) < ε
    rw [Real.dist_eq,sub_zero,abs_of_pos hspos]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hwimage : g w ∈ range f := interior_subset (hball hwball)
  obtain ⟨u,hu⟩ := hwimage
  have heq : E (t,w) = E (u,z) := hu.symm.trans (hcenter u).symm
  have hs0 : s = 0 := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => p.2.val) (hE.injective heq)
  exact hspos.ne' hs0
end CurveComplex
