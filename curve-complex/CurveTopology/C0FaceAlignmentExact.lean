import OriginalArcFaceCurveCarriers
import ActualOriginalFiniteProperArcSystemsSimultaneousAlignmentEssentialContext

open Set Topology CurveComplex
open scoped Manifold ContDiff
set_option autoImplicit false

namespace CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers
open OriginalBoundaryArc
variable (S : Type) [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (x : S) (R : ℝ)

theorem simultaneousRepresentatives_alignment
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (τ : Finset (ArcVertex S x R)) (hτ : τ ∈ (arcComplex S x R).faces)
    (a b : SimultaneousRepresentatives S x R τ) :
    ∃ H : AmbientIsotopy (Q S x R),
      (∀ t : Interval, (fun q => H.map (t, q)) '' boundaryQ S x R = boundaryQ S x R) ∧
      ∀ u : ↥τ, H.finalMap '' Set.range (a.arc u).val.val =
        Set.range (b.arc u).val.val := by
  classical
  apply actual_original_finite_essential_proper_arc_systems_simultaneous_alignment
    S g hg hS x R hR htarget ↥τ
    (fun u => (a.arc u).val.val) (fun u => (b.arc u).val.val)
  · intro u
    exact ⟨(a.arc u).val.property.1, (b.arc u).val.property.1⟩
  · intro u
    exact ⟨(a.arc u).val.property.2.1, (a.arc u).val.property.2.2.1,
      (b.arc u).val.property.2.1, (b.arc u).val.property.2.2.1⟩
  · intro u t ht
    exact ⟨(a.arc u).val.property.2.2.2 t ht,
      (b.arc u).val.property.2.2.2 t ht⟩
  · intro u
    exact (a.arc u).property
  · intro u
    exact (b.arc u).property
  · intro u w huw
    exact ⟨a.disjoint u w huw, b.disjoint u w huw⟩
  · intro u w huw hrel
    apply huw
    apply Subtype.ext
    calc
      u.val = Quot.mk (arcRel S x R) (a.arc u) := (a.class_eq u).symm
      _ = Quot.mk (arcRel S x R) (a.arc w) :=
        (arc_class_eq_iff_actual_relation S x R (a.arc u) (a.arc w)).2 hrel
      _ = w.val := a.class_eq w
  · intro u
    apply (arc_class_eq_iff_actual_relation S x R (a.arc u) (b.arc u)).1
    exact (a.class_eq u).trans (b.class_eq u).symm


end CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers
