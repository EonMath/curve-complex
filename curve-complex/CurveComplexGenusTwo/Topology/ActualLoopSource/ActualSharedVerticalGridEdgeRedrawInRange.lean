import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSharedGridEdgeEndpointClear
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualCommonStripFiniteEdgeRedrawInRange
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual vertical grid edge of a selected original cell: derive its strip
coordinate map from the already constructed movie, prove its endpoint clearance
from the actual mesh data, and construct the finite-contact edge redraw. -/
theorem actual_shared_vertical_grid_edge_redraw_in_range
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC)
    (hmarks : ∀ z,BC z ∉ (M.cover.branch : Set S))
    (haxis : ∀ z,BC z ∈ a.val.image ↔ z.2.val=0)
    (R : C((Interval × Interval) × Interval,S)) (n : ℕ) (hn : 0<n)
    (cell : (Fin n × Fin n) → Set (Interval × Interval))
    (hcell : ∀ k,cell k=range (fun z : Interval × Interval =>
      (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2)))
    (label : (Fin n × Fin n) → Bool)
    (hrange : ∀ k,label k=true → ∀ z ∈ cell k,∀ σ,R (z,σ) ∈ range BC)
    (hvertex : ∀ i j : Fin (n+1),(0< i.val ∧ i.val<n) ∨ (0< j.val ∧ j.val<n) →
      R ((actualHalfMeshParameter n hn ⟨2*i.val,by omega⟩,
        actualHalfMeshParameter n hn ⟨2*j.val,by omega⟩),1) ∉ a.val.image)
    (i : Fin n) (j : Fin (n+1)) (hj : 0< j.val ∧ j.val<n)
    (htrue : label (⟨j.val,hj.2⟩,i)=true) :
    ∃ edge : C(Interval,S),∃ H : C(Interval × Interval,S),
      (∀ t,H (0,t)=R ((actualHalfMeshParameter n hn ⟨2*j.val,by omega⟩,
        ArcFinitePosition.intervalMeshParameter n hn i t),1)) ∧
      (∀ t,H (1,t)=edge t) ∧
      (∀ σ,H (σ,0)=R ((actualHalfMeshParameter n hn ⟨2*j.val,by omega⟩,
          ArcFinitePosition.intervalMeshParameter n hn i 0),1) ∧
        H (σ,1)=R ((actualHalfMeshParameter n hn ⟨2*j.val,by omega⟩,
          ArcFinitePosition.intervalMeshParameter n hn i 1),1)) ∧
      (∀ z,H z ∉ (M.cover.branch : Set S)) ∧
      (∀ z,H z ∈ range BC) ∧ (∀ t,edge t ∈ range BC) ∧
      (edge 0 ∉ a.val.image ∧ edge 1 ∉ a.val.image) ∧
      {t : Interval | edge t ∈ a.val.image}.Finite ∧
      (∀ t u,edge t ∈ a.val.image → edge u ∈ a.val.image → t=u) ∧
      (∀ t,edge t ∈ a.val.image → t≠0 ∧ t≠1) := by
  let node := actualHalfMeshParameter n hn ⟨2*j.val,by omega⟩
  let k : Fin n × Fin n := (⟨j.val,hj.2⟩,i)
  have hnode : ArcFinitePosition.intervalMeshParameter n hn k.1 0=node := by
    apply Subtype.ext
    rw [actual_half_mesh_parameter_vertex]
    change ((j.val:ℝ)+0)/n=(j.val:ℝ)/n
    simp
  let original : C(Interval,S) :=
    ⟨fun t => R ((node,ArcFinitePosition.intervalMeshParameter n hn i t),1),by
      exact R.continuous.comp
        ((continuous_const.prodMk (ArcFinitePosition.intervalMeshParameter_continuous n hn i)).prodMk continuous_const)⟩
  have horiginal (t) : original t ∈ range BC := by
    apply hrange k htrue _ _ 1
    rw [hcell k]
    refine ⟨(0,t),?_⟩
    exact Prod.ext hnode rfl
  let Q : C(Interval,range BC) := ⟨fun t => ⟨original t,horiginal t⟩,
    original.continuous.subtype_mk horiginal⟩
  let F : C(Interval × Interval,S) := ⟨fun z => R ((z.2,z.1),1),by fun_prop⟩
  have hvertexFlip : ∀ u v : Fin (n+1),
      (0< u.val ∧ u.val<n) ∨ (0< v.val ∧ v.val<n) →
      F (actualHalfMeshParameter n hn ⟨2*u.val,by omega⟩,
        actualHalfMeshParameter n hn ⟨2*v.val,by omega⟩) ∉ a.val.image := by
    intro u v huv
    exact hvertex v u huv.symm
  obtain ⟨hstart,hend⟩ := actual_shared_grid_edge_endpoint_clear
    a.val.image F n hn hvertexFlip i j hj
  exact actual_common_strip_finite_edge_redraw_in_range M a BC hBC hmarks haxis
    original Q (fun _ => rfl) hstart hend
end CurveComplex.HyperellipticModel
