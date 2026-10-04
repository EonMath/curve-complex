import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualProductBoundedZeroExtension
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual normalized cutoff: full redraw on the inner half germ and the
literal original movie at the outer seam. -/
theorem actual_endpoint_inner_cutoff (d : ℝ) (hd : 0<d) :
    ∃ c : C(Icc (0:ℝ) d,unitInterval),
      (∀ t, t.val≤d/2 → c t=1) ∧ c ⟨d,hd.le,le_rfl⟩=0 := by
  let c : C(Icc (0:ℝ) d,unitInterval) :=
    ⟨fun t => ⟨min 1 (max 0 (2-2*t.val/d)),
      le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩,by fun_prop⟩
  refine ⟨c,?_,?_⟩
  · intro t ht
    apply Subtype.ext
    change min 1 (max 0 (2-2*t.val/d))=1
    apply min_eq_left
    apply le_trans _ (le_max_right _ _)
    have hh : 2*t.val/d≤1 := (div_le_iff₀ hd).mpr (by nlinarith)
    linarith
  · apply Subtype.ext
    change min 1 (max 0 (2-2*d/d))=0
    have hh : 2*d/d=2 := by field_simp
    rw [hh]
    norm_num
end CurveComplex.HyperellipticModel
