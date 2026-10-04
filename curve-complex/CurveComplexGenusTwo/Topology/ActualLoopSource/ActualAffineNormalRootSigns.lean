import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualScalarMeshBoundaryIncidence
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- A genuine affine normal segment with clear source endpoint changes sign
at every root. The input is its literal scalar formula, not sign-change data. -/
theorem actual_affine_normal_root_signs
    (α β : ℝ) (hα : α≠0) (u v w : Interval)
    (hu : (1-u.val)*α+u.val*β=0) (hv : v<u) (hw : u<w) :
    (1-v.val)*α+v.val*β≠0 ∧ (1-w.val)*α+w.val*β≠0 ∧
    ((0<(1-v.val)*α+v.val*β) ↔ ¬(0<(1-w.val)*α+w.val*β)) := by
  have hs : β≠α := by intro he; rw [he] at hu; exact hα (by nlinarith only [hu])
  have hvl : v.val < u.val := hv
  have hwl : u.val < w.val := hw
  rcases lt_or_gt_of_ne hs with hs | hs
  · have hl : 0<(1-v.val)*α+v.val*β := by
      have hh := mul_pos (sub_pos.mpr hvl) (sub_pos.mpr hs)
      nlinarith only [hh,hu]
    have hr : (1-w.val)*α+w.val*β < 0 := by
      have hh := mul_pos (sub_pos.mpr hwl) (sub_pos.mpr hs)
      nlinarith only [hh,hu]
    exact ⟨ne_of_gt hl,ne_of_lt hr,by simp only [hl,not_lt.mpr hr.le,true_iff,not_false_eq_true]⟩
  · have hl : (1-v.val)*α+v.val*β < 0 := by
      have hh := mul_pos (sub_pos.mpr hvl) (sub_pos.mpr hs)
      nlinarith only [hh,hu]
    have hr : 0<(1-w.val)*α+w.val*β := by
      have hh := mul_pos (sub_pos.mpr hwl) (sub_pos.mpr hs)
      nlinarith only [hh,hu]
    exact ⟨ne_of_lt hl,ne_of_gt hr,by simp only [hr,not_lt.mpr hl.le,false_iff,not_true_eq_false]⟩
end CurveComplex.HyperellipticModel
