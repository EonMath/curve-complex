import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSharedHorizontalGridEdgeFamily
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Literal common node of two adjacent affine cells, with no reparametrization
or asserted matching endpoint supplied. -/
theorem actual_uniform_mesh_adjacent_seam (n : ℕ) (hn : 0<n)
    (j : Fin n) (hj : 0< j.val) :
    ArcFinitePosition.intervalMeshParameter n hn ⟨j.val-1,by omega⟩ 1=
      ArcFinitePosition.intervalMeshParameter n hn j 0 := by
  apply Subtype.ext
  change (((j.val-1:ℕ):ℝ)+(1:ℝ))/n=((j.val:ℝ)+(0:ℝ))/n
  rw [Nat.cast_sub (by omega : 1≤j.val)]
  simp
/-- At an actual selected/off horizontal interface, the whole unchanged seam
is old-free. This derives why that seam needs no redraw from the produced
unselected-cell clearance, including all its endpoints. -/
theorem actual_horizontal_off_interface_clear
    {Y : Type} [TopologicalSpace Y] (old : Set Y)
    (R : C((Interval × Interval) × Interval,Y))
    (n : ℕ) (hn : 0<n) (label : (Fin n × Fin n) → Bool)
    (hoff : ∀ k,label k=false → ∀ z : Interval × Interval,∀ σ,
      R ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),σ) ∉ old)
    (i j : Fin n) (hj : 0< j.val)
    (hfalse : label (i,j)=false ∨ label (i,⟨j.val-1,by omega⟩)=false) :
    ∀ t σ,R ((ArcFinitePosition.intervalMeshParameter n hn i t,
      ArcFinitePosition.intervalMeshParameter n hn j 0),σ) ∉ old := by
  intro t σ
  rcases hfalse with h | h
  · exact hoff (i,j) h (t,0) σ
  · have hh := hoff (i,⟨j.val-1,by omega⟩) h (t,1) σ
    rw [actual_uniform_mesh_adjacent_seam n hn j hj] at hh
    exact hh
/-- The corresponding actual vertical selected/off interface is also old-free
at every time and every literal seam parameter. -/
theorem actual_vertical_off_interface_clear
    {Y : Type} [TopologicalSpace Y] (old : Set Y)
    (R : C((Interval × Interval) × Interval,Y))
    (n : ℕ) (hn : 0<n) (label : (Fin n × Fin n) → Bool)
    (hoff : ∀ k,label k=false → ∀ z : Interval × Interval,∀ σ,
      R ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),σ) ∉ old)
    (i j : Fin n) (hj : 0< j.val)
    (hfalse : label (j,i)=false ∨ label (⟨j.val-1,by omega⟩,i)=false) :
    ∀ t σ,R ((ArcFinitePosition.intervalMeshParameter n hn j 0,
      ArcFinitePosition.intervalMeshParameter n hn i t),σ) ∉ old := by
  intro t σ
  rcases hfalse with h | h
  · exact hoff (j,i) h (0,t) σ
  · have hh := hoff (⟨j.val-1,by omega⟩,i) h (1,t) σ
    rw [actual_uniform_mesh_adjacent_seam n hn j hj] at hh
    exact hh
end CurveComplex.HyperellipticModel
