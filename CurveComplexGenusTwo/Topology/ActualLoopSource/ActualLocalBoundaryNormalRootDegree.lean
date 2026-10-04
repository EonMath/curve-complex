import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLiteralCellBoundarySourceNormal
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- A literal boundary coordinate's genuine local normal sign flip gives exact
local endpoint incidence at its actual root, using the positive source pole. -/
theorem actual_local_boundary_normal_root_degree_one
    (coordinate : C(Interval × Interval,Interval × Icc (-1:ℝ) 1))
    (A : Type) (arc : A → C(Interval,Interval × Interval))
    (hdegree : ∀ (i : Fin 4) (u : Interval),0<u.val → u.val < 1 →
      (coordinate (actualLiteralCellSide i u)).2.val=0 →
      ∀ δ : ℝ,0<δ →
      (∀ v w : Interval,u.val-δ<v.val → v<u → u<w → w.val<u.val+δ →
        (coordinate (actualLiteralCellSide i v)).2.val/(1/2:ℝ)≠0 ∧
        (coordinate (actualLiteralCellSide i w)).2.val/(1/2:ℝ)≠0 ∧
        ((0<(coordinate (actualLiteralCellSide i v)).2.val/(1/2:ℝ)) ↔
          ¬(0<(coordinate (actualLiteralCellSide i w)).2.val/(1/2:ℝ)))) →
      {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=actualLiteralCellSide i u}.ncard=1)
    (i : Fin 4) (u : Interval) (hu : 0<u.val ∧ u.val < 1)
    (hzero : (coordinate (actualLiteralCellSide i u)).2.val=0)
    (δ : ℝ) (hδ : 0<δ)
    (hflip : ∀ v w : Interval,u.val-δ<v.val → v<u → u<w → w.val<u.val+δ →
      (coordinate (actualLiteralCellSide i v)).2.val≠0 ∧
      (coordinate (actualLiteralCellSide i w)).2.val≠0 ∧
      ((0<(coordinate (actualLiteralCellSide i v)).2.val) ↔
        ¬(0<(coordinate (actualLiteralCellSide i w)).2.val))) :
    {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=actualLiteralCellSide i u}.ncard=1 := by
  apply hdegree i u hu.1 hu.2 hzero δ hδ
  intro v w hvl hvh hwl hwh
  obtain ⟨hv,hw,hf⟩ := hflip v w hvl hvh hwl hwh
  exact actual_positive_normal_pole_signs _ _ hv hw hf
end CurveComplex.HyperellipticModel
