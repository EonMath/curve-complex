import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedUniformMeshVertexClear
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Every literal horizontal interior grid edge has two noncorner endpoints;
therefore the actual boundary-safe vertex producer clears both endpoints. -/
theorem actual_shared_grid_edge_endpoint_clear
    {S : Type} [TopologicalSpace S] (old : Set S) (F : C(Interval × Interval,S))
    (n : ℕ) (hn : 0<n)
    (hvertex : ∀ i j : Fin (n+1),(0< i.val ∧ i.val<n) ∨ (0< j.val ∧ j.val<n) →
      F (actualHalfMeshParameter n hn ⟨2*i.val,by omega⟩,
        actualHalfMeshParameter n hn ⟨2*j.val,by omega⟩) ∉ old)
    (i : Fin n) (j : Fin (n+1)) (hj : 0< j.val ∧ j.val<n) :
    F (ArcFinitePosition.intervalMeshParameter n hn i 0,
        actualHalfMeshParameter n hn ⟨2*j.val,by omega⟩) ∉ old ∧
      F (ArcFinitePosition.intervalMeshParameter n hn i 1,
        actualHalfMeshParameter n hn ⟨2*j.val,by omega⟩) ∉ old := by
  have hstart := hvertex i.castSucc j (Or.inr hj)
  have hend := hvertex i.succ j (Or.inr hj)
  have hs : actualHalfMeshParameter n hn ⟨2*i.castSucc.val,by omega⟩=
      ArcFinitePosition.intervalMeshParameter n hn i 0 := by
    apply Subtype.ext
    rw [actual_half_mesh_parameter_vertex]
    change (i.val:ℝ)/n=((i.val:ℝ)+0)/n
    simp
  have he : actualHalfMeshParameter n hn ⟨2*i.succ.val,by omega⟩=
      ArcFinitePosition.intervalMeshParameter n hn i 1 := by
    apply Subtype.ext
    rw [actual_half_mesh_parameter_vertex]
    change ((i.val+1:ℕ):ℝ)/n=((i.val:ℝ)+1)/n
    push_cast
    rfl
  rw [hs] at hstart
  rw [he] at hend
  exact ⟨hstart,hend⟩
end CurveComplex.HyperellipticModel
