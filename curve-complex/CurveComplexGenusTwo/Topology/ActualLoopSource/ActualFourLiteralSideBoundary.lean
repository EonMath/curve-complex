import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteClosedCellGluing
namespace CurveComplex.HyperellipticModel
open Set Topology
theorem actual_four_literal_side_boundary {Y : Type} [TopologicalSpace Y] {bl br tl tr : Y}
    (bottom : Path bl br) (right : Path br tr) (top : Path tl tr) (left : Path bl tl) :
    ∃ f : C({z : ℝ × ℝ // ‖z‖ = 1},Y),
      ∀ z, (z.val.2 = -1 → f z = bottom ((actualNormalizedMaxNormSquare ⟨z.val,z.property.le⟩).1)) ∧
        (z.val.1 = 1 → f z = right ((actualNormalizedMaxNormSquare ⟨z.val,z.property.le⟩).2)) ∧
        (z.val.2 = 1 → f z = top ((actualNormalizedMaxNormSquare ⟨z.val,z.property.le⟩).1)) ∧
        (z.val.1 = -1 → f z = left ((actualNormalizedMaxNormSquare ⟨z.val,z.property.le⟩).2)) := by
  let B := {z : ℝ × ℝ // ‖z‖ = 1}
  let bc : C(B,Interval × Interval) :=
    ⟨fun z => actualNormalizedMaxNormSquare ⟨z.val,z.property.le⟩,by fun_prop⟩
  let xc : C(B,Interval) := ⟨fun z => (bc z).1,continuous_fst.comp bc.continuous⟩
  let yc : C(B,Interval) := ⟨fun z => (bc z).2,continuous_snd.comp bc.continuous⟩
  have xzero (z : B) (hz : z.val.1 = -1) : xc z = 0 := by
    apply Subtype.ext
    change (z.val.1+1)/2 = 0
    rw [hz]
    norm_num
  have xone (z : B) (hz : z.val.1 = 1) : xc z = 1 := by
    apply Subtype.ext
    change (z.val.1+1)/2 = 1
    rw [hz]
    norm_num
  have yzero (z : B) (hz : z.val.2 = -1) : yc z = 0 := by
    apply Subtype.ext
    change (z.val.2+1)/2 = 0
    rw [hz]
    norm_num
  have yone (z : B) (hz : z.val.2 = 1) : yc z = 1 := by
    apply Subtype.ext
    change (z.val.2+1)/2 = 1
    rw [hz]
    norm_num
  let D : Fin 4 → Set B := fun i =>
    if i.val = 0 then {z | z.val.2 = -1} else
    if i.val = 1 then {z | z.val.1 = 1} else
    if i.val = 2 then {z | z.val.2 = 1} else {z | z.val.1 = -1}
  let edges : Fin 4 → C(B,Y) := fun i =>
    if i.val = 0 then bottom.toContinuousMap.comp xc else
    if i.val = 1 then right.toContinuousMap.comp yc else
    if i.val = 2 then top.toContinuousMap.comp xc else left.toContinuousMap.comp yc
  have hD : ∀ i, IsClosed (D i) := by
    intro i
    fin_cases i <;> simp only [D] <;>
      exact isClosed_eq (by fun_prop) continuous_const
  have hcover : ∀ z : B, ∃ i, z ∈ D i := by
    intro z
    have hn : max |z.val.1| |z.val.2| = 1 := by
      simpa only [Prod.norm_def,Real.norm_eq_abs] using z.property
    have hpair : |z.val.1| = 1 ∨ |z.val.2| = 1 := by
      by_cases hx : |z.val.1| = 1
      · exact Or.inl hx
      · right
        by_contra hy
        have hxlt : |z.val.1| < 1 := lt_of_le_of_ne ((le_max_left _ _).trans hn.le) hx
        have hylt : |z.val.2| < 1 := lt_of_le_of_ne ((le_max_right _ _).trans hn.le) hy
        have hmax := max_lt hxlt hylt
        rw [hn] at hmax
        exact lt_irrefl _ hmax
    rcases hpair with hx | hy
    · by_cases hx0 : 0 ≤ z.val.1
      · refine ⟨1,?_⟩
        change z.val.1 = 1
        rwa [abs_of_nonneg hx0] at hx
      · refine ⟨3,?_⟩
        change z.val.1 = -1
        rw [abs_of_neg (lt_of_not_ge hx0)] at hx
        linarith
    · by_cases hy0 : 0 ≤ z.val.2
      · refine ⟨2,?_⟩
        change z.val.2 = 1
        rwa [abs_of_nonneg hy0] at hy
      · refine ⟨0,?_⟩
        change z.val.2 = -1
        rw [abs_of_neg (lt_of_not_ge hy0)] at hy
        linarith
  have hagree : ∀ i j z, z ∈ D i → z ∈ D j → edges i z = edges j z := by
    intro i j z hi hj
    fin_cases i <;> fin_cases j <;> simp [D,edges,ContinuousMap.comp_apply] at hi hj ⊢
    all_goals first
      | rfl
      | (exfalso; linarith)
      | (simp_all only [Path.source,Path.target])
  obtain ⟨f,hf⟩ := actual_finite_closed_cell_gluing D hD hcover edges hagree
  refine ⟨f,?_⟩
  intro z
  exact ⟨fun hz => hf 0 z hz,fun hz => hf 1 z hz,fun hz => hf 2 z hz,fun hz => hf 3 z hz⟩
end CurveComplex.HyperellipticModel
