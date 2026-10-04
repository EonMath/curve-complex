import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteHalfMeshParameters
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedLoopBoundaryAvoidingCellSupport
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- The actual movie constructs one shift clearing ALL interior half-mesh
vertices and cell poles in its common strip, while every off cell has zero
weight. No finite point cloud or vertex perturbation is an input. -/
theorem actual_prepared_loop_boundary_safe_half_mesh_shift
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (G : C(Interval × Interval,S)) (events : Set Interval) (hfiniteEvents : events.Finite)
    (T : Set (Interval × Interval)) (hT : IsOpen T) (hcontacts : G ⁻¹' a.val.image ⊆ T)
    (ψ : C(T,ℝ)) (hψ : ∀ x,ψ x<1)
    (hψzero : ∀ x : T,ψ x=0 ↔ G x.val ∈ a.val.image) :
    ∃ n : ℕ, ∃ hn : 0<n,
      (∀ k : Fin n,0<k.val → ∀ t : Interval,t.val=(k.val:ℝ)/n → t ∉ events) ∧
    ∃ cell : (Fin n × Fin n) → Set (Interval × Interval),
      (∀ k,cell k=range (fun z : Interval × Interval =>
        (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
          ArcFinitePosition.intervalMeshParameter n hn k.2 z.2))) ∧
      (∀ k,IsClosed (cell k)) ∧ (∀ z,∃ k,z ∈ cell k) ∧
    ∃ label : (Fin n × Fin n) → Bool,
      (∀ k,label k=true → cell k ⊆ T) ∧
      (∀ k,label k=false → ∀ z ∈ cell k,G z ∉ a.val.image) ∧
    ∃ support : Set (Interval × Interval),IsClosed support ∧ ∃ hST : support ⊆ T,
      G ⁻¹' a.val.image ⊆ interior support ∧
    ∃ (δ : ℝ) (weight : C(Interval × Interval,ℝ)),0<δ ∧
      (∀ z,weight z ∈ Icc (0:ℝ) 1) ∧
      (∀ z,z ∉ support → weight z=0) ∧
      (∀ k,label k=false → ∀ z ∈ cell k,weight z=0) ∧
      (∀ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → weight z=0) ∧
      (∀ (i j : Fin (2*n+1))
        (hz : (actualHalfMeshParameter n hn i,actualHalfMeshParameter n hn j) ∈ T),
        0<(actualHalfMeshParameter n hn i:ℝ) → (actualHalfMeshParameter n hn i:ℝ)<1 →
        0<(actualHalfMeshParameter n hn j:ℝ) → (actualHalfMeshParameter n hn j:ℝ)<1 →
        ψ ⟨(actualHalfMeshParameter n hn i,actualHalfMeshParameter n hn j),hz⟩+
          δ*weight (actualHalfMeshParameter n hn i,actualHalfMeshParameter n hn j)≠0) ∧
      (∀ z (hz : z ∈ support),ψ ⟨z,hST hz⟩+δ*weight z<1) := by
  classical
  obtain ⟨n,hn,hmeshAvoid,cell,hcell,hclosed,hcover,label,hcellT,hcellOff,
    support,hsupport,hsupportClosed,hsupportT,hcontactsSupport,
    cutoff,hcutoffRange,hcutoffOff,hcutoffOutside,hcutoffContacts⟩ :=
    actual_prepared_loop_boundary_avoiding_cell_support M a events hfiniteEvents G T hT hcontacts
  let coord (k : Fin (2*n+1) × Fin (2*n+1)) :=
    (actualHalfMeshParameter n hn k.1,actualHalfMeshParameter n hn k.2)
  let I := {k : Fin (2*n+1) × Fin (2*n+1) |
    coord k ∈ T ∧ 0<(coord k).1.val ∧ (coord k).1.val<1 ∧
      0<(coord k).2.val ∧ (coord k).2.val<1}
  let point : I → T := fun k => ⟨coord k.val,k.property.1⟩
  have hpoint : ∀ k,0<(point k).val.1.val ∧ (point k).val.1.val<1 ∧
      0<(point k).val.2.val ∧ (point k).val.2.val<1 := fun k => k.property.2
  have hzero : ∀ k,ψ (point k)=0 → cutoff (point k).val=1 :=
    fun k hk => hcutoffContacts _ ((hψzero (point k)).mp hk)
  obtain ⟨δ,weight,hδ,hweightEq,hweightRange,hboundary,hclear,hbound⟩ :=
    actual_prepared_square_supported_normal_shift T support hsupportClosed hsupportT
      ψ hψ cutoff hcutoffRange point hpoint hzero
  have hoff : ∀ z,z ∉ support → weight z=0 := by
    intro z hz
    rw [hweightEq z,hcutoffOutside z (fun hi => hz (interior_subset hi)),zero_mul]
  have hfalse : ∀ k,label k=false → ∀ z ∈ cell k,weight z=0 := by
    intro k hk z hz
    rw [hweightEq z,hcutoffOff k hk z hz,zero_mul]
  refine ⟨n,hn,hmeshAvoid,cell,hcell,hclosed,hcover,label,hcellT,hcellOff,support,
    hsupportClosed,hsupportT,hcontactsSupport,δ,weight,hδ,hweightRange,hoff,hfalse,hboundary,?_,hbound⟩
  intro i j hz hi0 hi1 hj0 hj1
  exact hclear ⟨(i,j),hz,hi0,hi1,hj0,hj1⟩
end CurveComplex.HyperellipticModel
