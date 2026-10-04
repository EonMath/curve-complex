import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Topology.GlobalMonodromy.GlobalLoopSubdivision
import CurveComplexGenusTwo.Topology.ActualRegionalContactGeometry.RegionalFiniteContactGeometry
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryNullGeometry
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open CurveComplex Set Topology
open CurveComplex.BranchedDoubleCover
open scoped BigOperators

namespace RegionalTotalDecrease

/-- The two actual interval endpoints, with no chosen orientation of the terminal arc. -/
def endpoint (i : Fin 2) : Interval := if i = 0 then 0 else 1

/-- The observer is the `none` member of the exact augmented family. -/
def augmented {X ι : Type*} [TopologicalSpace X]
    (r : ι → C(Interval,X)) (α : C(Interval,X)) (i : Option ι) : C(Interval,X) :=
  i.elim α r

/-- Exactly the original finite whole-contact and endpoint invariant bundle. -/
def FamilyInvariant {X ι : Type*} [TopologicalSpace X]
    (r : ι → C(Interval,X)) (α : C(Interval,X)) : Prop :=
  (∀ i j, i ≠ j → (range (r i) ∩ range (r j)).Finite) ∧
  (∀ i j, i ≠ j → r i 0 ≠ r j 0 ∧ r i 0 ≠ r j 1 ∧
    r i 1 ≠ r j 0 ∧ r i 1 ≠ r j 1) ∧
  (∀ i, α 0 ∉ range (r i)) ∧ (∀ i, α 1 ∉ range (r i)) ∧
  (∀ i, (range α ∩ range (r i)).Finite)

/-- An actual F movie preserving both named strata and the exact final trace. -/
def ClassMovie {X : Type*} [TopologicalSpace X] (B T : Set X)
    (a b : C(Interval,X)) (H : AmbientIsotopy X) : Prop :=
  (∀ t, (fun y => H.map (t,y)) '' B = B) ∧
  (∀ t, (fun y => H.map (t,y)) '' T = T) ∧
  H.finalMap '' range a = range b

/-- An actual paired clean ordinary disk, tied to the same whole proper arcs. -/
structure PairedBigonDisk {S : Type} [TopologicalSpace S]
    (F : Set S) (T : Set ↥F) (a b : C(Interval,↥F)) where
  first : C(Interval,↥F)
  second : C(Interval,↥F)
  first_embedded : IsEmbedding first
  second_embedded : IsEmbedding second
  aStart : Interval
  aFinish : Interval
  bStart : Interval
  bFinish : Interval
  a_distinct : aStart ≠ aFinish
  b_distinct : bStart ≠ bFinish
  first_eq : ∀ t, first t = a (intervalAffine aStart aFinish t)
  second_eq : ∀ t, second t = b (intervalAffine bStart bFinish t)
  zero_eq : first 0 = second 0
  one_eq : first 1 = second 1
  corners_distinct : first 0 ≠ first 1
  corners_off_frontier : first 0 ∉ T ∧ first 1 ∉ T
  sides_inter : range first ∩ range second = {first 0,first 1}
  disk : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F)
  disk_embedded : IsEmbedding disk
  boundary_image : disk '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
    range first ∪ range second
  whole_first : range disk ∩ range a = range first
  whole_second : range disk ∩ range b = range second
  ambient_interior : ∀ y ∈ range disk, y.val ∈ interior F
  strict_interior_clear : ∀ z, z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 →
    disk z ∉ range a ∧ disk z ∉ range b

/-- A paired clean half disk. The B side is not required to avoid third endpoints. -/
structure PairedHalfBigonDisk {S : Type} [TopologicalSpace S]
    (F : Set S) (B T : Set ↥F) (a b : C(Interval,↥F)) where
  first : C(Interval,↥F)
  second : C(Interval,↥F)
  boundarySide : C(Interval,↥F)
  first_embedded : IsEmbedding first
  second_embedded : IsEmbedding second
  boundary_embedded : IsEmbedding boundarySide
  aStart : Interval
  aFinish : Interval
  bStart : Interval
  bFinish : Interval
  a_distinct : aStart ≠ aFinish
  b_distinct : bStart ≠ bFinish
  first_eq : ∀ t, first t = a (intervalAffine aStart aFinish t)
  second_eq : ∀ t, second t = b (intervalAffine bStart bFinish t)
  first_zero : first 0 ∈ B
  second_zero : second 0 ∈ B
  boundary_endpoints_distinct : first 0 ≠ second 0
  corner_eq : first 1 = second 1
  corner_off_frontier : first 1 ∉ T
  first_interior : ∀ t ∈ Ioo (0 : Interval) 1, first t ∉ T
  second_interior : ∀ t ∈ Ioo (0 : Interval) 1, second t ∉ T
  boundary_in_B : ∀ t, boundarySide t ∈ B
  boundary_zero : boundarySide 0 = first 0
  boundary_one : boundarySide 1 = second 0
  sides_inter : range first ∩ range second = {first 1}
  first_boundary_inter : range first ∩ range boundarySide = {first 0}
  second_boundary_inter : range second ∩ range boundarySide = {second 0}
  loop : Curve ↥F
  loop_image : loop.image = range first ∪ range second ∪ range boundarySide
  disk : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F)
  disk_embedded : IsEmbedding disk
  boundary_image : disk '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
    range first ∪ range second ∪ range boundarySide
  whole_first : range disk ∩ range a = range first
  whole_second : range disk ∩ range b = range second
  whole_frontier : range disk ∩ T = range boundarySide
  strict_interior_clear : ∀ z, z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 →
    disk z ∉ range a ∧ disk z ∉ range b ∧ disk z ∉ T

/-- Literal reverse-L₀ / D / L₁ thirds. Clamping only makes the clock total;
on its own piece each clock equals the stated affine parameter. -/
noncomputable def comparisonReturn {Y : Type*} [TopologicalSpace Y]
    (L : Fin 2 → C(Interval,Y)) (D : C(Interval,Y)) (t : Interval) : Y :=
  if t.val ≤ (1/3 : ℝ) then L 0 (projIcc 0 1 zero_le_one (1 - 3*t.val))
  else if t.val ≤ (2/3 : ℝ) then D (projIcc 0 1 zero_le_one (3*t.val - 1))
  else L 1 (projIcc 0 1 zero_le_one (3*t.val - 2))

end RegionalTotalDecrease
