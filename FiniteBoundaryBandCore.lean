import ClassificationOfSurfaces.Moise.GeometricTriangulation
import ClassificationOfSurfaces.Topology.InvarianceOfDomain
import Mathlib.Analysis.Complex.Circle
import CurveComplexGenusTwo.Foundations.Definitions

open Set Topology CurveComplex
open scoped Manifold ContDiff
open LeanEval.Topology.ClassificationOfSurfaces

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry

/-- The literal valence-one edges of the finite triangle family. -/
noncomputable def boundaryEdges {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset (Finset V)) : Finset (Finset V) :=
  (TriangleFamily.edges F).filter fun e => (F.filter fun t => e ⊆ t).card = 1

/-- Exactly the vertices on a literal valence-one edge; unused vertices are ignored. -/
noncomputable def boundaryVertices {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset (Finset V)) : Finset V := (boundaryEdges F).biUnion id

/-- The boundary-edge stratum in the actual barycentric realization. -/
def boundaryLocus {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset (Finset V)) : Set (GeometricRealization V F) :=
  {q | ∃ e ∈ boundaryEdges F, q.val ∈ GeometricFace V e}

/-- The actual finite boundary graph; adjacency is membership of the unordered pair. -/
def boundaryAdjacent {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset (Finset V)) (v w : V) : Prop := {v,w} ∈ boundaryEdges F

/-- A finite ordered path of all triangles incident to this boundary vertex. -/
structure OrderedBoundaryFan {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset (Finset V)) (v : V) where
  length : ℕ
  positive : 1 ≤ length
  vertex : Fin (length+1) → V
  injective : Function.Injective vertex
  off_center : ∀ i, vertex i ≠ v
  triangles_exact : ∀ t : Finset V, t ∈ F ∧ v ∈ t ↔
    ∃ i : Fin length, t = {v,vertex i.castSucc,vertex i.succ}
  boundary_edges_exact : ∀ e : Finset V, e ∈ boundaryEdges F ∧ v ∈ e ↔
    e = {v,vertex 0} ∨ e = {v,vertex (Fin.last length)}

/-- Fans are concrete finite incidence data, not an assumed collar. -/
def HasOrderedBoundaryFans {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset (Finset V)) : Prop :=
  ∀ v ∈ boundaryVertices F, Nonempty (OrderedBoundaryFan F v)

/-- The literal cyclic successor, including the last-to-first seam. -/
def cyclicNext (m : ℕ) (hm : 3 ≤ m) (i : Fin m) : Fin m :=
  ⟨(i.val+1)%m, Nat.mod_lt _ (by omega)⟩

/-- The fixed Circle clock of the i-th edge, for every closed-edge parameter. -/
noncomputable def edgeClock (m : ℕ) (i : Fin m) (s : Interval) : Circle :=
  Circle.exp (2 * Real.pi * ((i.val : ℝ) + (s : ℝ)) / (m : ℝ))

/-- One whole boundary-graph component, with its injective cyclic vertex word
and the literal piecewise-affine barycentric Circle parametrization. -/
structure BoundaryCycle {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset (Finset V)) where
  length : ℕ
  length_ge_three : 3 ≤ length
  vertex : Fin length → V
  vertex_injective : Function.Injective vertex
  component_edges_exact : ∀ e : Finset V,
    (e ∈ boundaryEdges F ∧ ∃ v ∈ e, Relation.ReflTransGen (boundaryAdjacent F)
      (vertex ⟨0,by omega⟩) v) ↔
    ∃ i : Fin length, e = {vertex i,vertex (cyclicNext length length_ge_three i)}
  circle : C(Circle, GeometricRealization V F)
  circle_clock : ∀ (i : Fin length) (s : Interval) (v : V),
    (circle (edgeClock length i s)).val v =
      (1 - (s : ℝ)) * (if vertex i = v then 1 else 0) +
      (s : ℝ) * (if vertex (cyclicNext length length_ge_three i) = v then 1 else 0)

/-- An actual inward band on the SAME finite realization, together with
closed edge patches and all complete cyclic seam/collision data. -/
structure BoundaryCycleInwardBand {V : Type} [Fintype V] [DecidableEq V]
    {F : Finset (Finset V)} (c : BoundaryCycle F)
    (U : Set (GeometricRealization V F)) where
  band : C(Interval × Circle, GeometricRealization V F)
  embedded : IsEmbedding band
  zero_clock : ∀ z, band (0,z) = c.circle z
  supported : range band ⊆ U
  boundary_exact : ∀ (t : Interval) z, band (t,z) ∈ boundaryLocus F ↔ t = 0
  positive_open : IsOpenEmbedding (fun z : Ioo (0 : ℝ) 1 × Circle =>
    band (⟨z.1.val,⟨z.1.property.1.le,z.1.property.2.le⟩⟩,z.2))
  patch : Fin c.length → C(Interval × Interval, GeometricRealization V F)
  patch_clock : ∀ i t s, patch i (t,s) = band (t,edgeClock c.length i s)
  whole_seam : ∀ i t, patch i (t,1) =
    patch (cyclicNext c.length c.length_ge_three i) (t,0)
  exact_collision : ∀ i j t s t' s', patch i (t,s) = patch j (t',s') ↔
    t = t' ∧ edgeClock c.length i s = edgeClock c.length j s'
  patch_cover : range band = ⋃ i, range (patch i)

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry
