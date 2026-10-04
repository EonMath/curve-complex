import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSelectedCellGenuineSurfaceBoundaryDegreeMovie
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPositiveNormalPoleSigns
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- An actual selected-cell boundary agrees with the actual final shared-edge
movie. Its coordinate normal is the edge's literal BC inverse normal, so the
source affine crossing forces exact local boundary incidence one. -/
theorem actual_selected_cell_literal_shared_edge_degree_one
    {S : Type} [TopologicalSpace S]
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC)
    (G : C(Interval × Interval,S))
    (coordinate : C(Interval × Interval,Interval × Icc (-1:ℝ) 1))
    (hdecode : ∀ z,BC (coordinate z)=G z)
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
    (i : Fin 4) (edge : C(Interval,S))
    (hside : ∀ t,G (actualLiteralCellSide i t)=edge t)
    (finalQ : C(Interval,range BC)) (hQ : ∀ t,(finalQ t).val=edge t)
    (u : Interval) (hu0 : 0<u.val) (hu1 : u.val < 1)
    (hzero : (hBC.toHomeomorph.symm (finalQ u)).2.val=0)
    (hflip : ∀ v w,v<u → u<w →
      (hBC.toHomeomorph.symm (finalQ v)).2.val≠0 ∧
      (hBC.toHomeomorph.symm (finalQ w)).2.val≠0 ∧
      ((0<(hBC.toHomeomorph.symm (finalQ v)).2.val) ↔
        ¬(0<(hBC.toHomeomorph.symm (finalQ w)).2.val))) :
    {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=actualLiteralCellSide i u}.ncard=1 := by
  have hcoord (t : Interval) : coordinate (actualLiteralCellSide i t)=hBC.toHomeomorph.symm (finalQ t) := by
    apply hBC.injective
    exact ((hdecode _).trans (hside t)).trans
      ((congrArg Subtype.val (hBC.toHomeomorph.apply_symm_apply (finalQ t))).trans (hQ t)).symm
  apply hdegree i u hu0 hu1 (by rw [hcoord,hzero]) 1 (by norm_num)
  intro v w hvl hvh hwl hwh
  rw [hcoord,hcoord]
  obtain ⟨hv,hw,hf⟩ := hflip v w hvh hwl
  exact actual_positive_normal_pole_signs _ _ hv hw hf
end CurveComplex.HyperellipticModel
