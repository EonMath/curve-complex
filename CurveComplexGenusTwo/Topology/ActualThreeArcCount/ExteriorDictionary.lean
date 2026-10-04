import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualBoundaryProperArcStrip

open Set Topology CurveComplex Metric
open scoped Manifold ContDiff

namespace CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

theorem exterior_interior_eq_complement_chart_closed_disk (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    interior (openDisk S x R)ᶜ =
      (openDisk S x R ∪ boundaryCircle S x R)ᶜ := by
  letI : ClosedSurface S := Classical.choice hS.2.1
  let E := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let p := E x
  let D : Set S := E.symm '' closedBall p R
  have hD : IsCompact D := (isCompact_closedBall _ _).image_of_continuousOn
    (E.continuousOn_symm.mono htarget)
  have hDs : D ⊆ E.source := by
    rintro y ⟨z,hz,rfl⟩
    exact E.map_target (htarget hz)
  have hI : E.IsImage D (closedBall p R) := by
    intro y hy
    constructor
    · intro hz
      exact ⟨E y,hz,E.left_inv hy⟩
    · rintro ⟨z,hz,rfl⟩
      rwa [E.right_inv (htarget hz)]
  have hi : interior D = openDisk S x R := by
    have hh := hI.interior.symm_image_eq
    rw [interior_closedBall _ hR.ne',inter_eq_right.mpr
      (Metric.ball_subset_closedBall.trans htarget),inter_eq_right.mpr
      ((interior_subset : interior D ⊆ D).trans hDs)] at hh
    exact hh.symm
  let f : closedBall p R → S := fun z => E.symm z.val
  have hfc : Continuous f := by
    apply E.continuousOn_symm.comp_continuous continuous_subtype_val
    intro z
    exact htarget z.property
  have hfi : Function.Injective f := by
    intro y z he
    exact Subtype.ext (E.symm.injOn (htarget y.property) (htarget z.property) he)
  have hfe : IsEmbedding f := (hfc.isClosedEmbedding hfi).isEmbedding
  have hrange : range f = D := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z.val,z.property,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hz⟩,rfl⟩
  have hreg : closure (interior D) = D := by
    rw [←hrange]
    apply embedded_planar_region_regular_closed _ (isCompact_closedBall _ _) _ f hfe
    rw [interior_closedBall _ hR.ne',closure_ball _ hR.ne']
  have hclosure : closure (openDisk S x R) = D := by rw [←hi]; exact hreg
  have hpartition : D = openDisk S x R ∪ boundaryCircle S x R := by
    dsimp [D,openDisk,boundaryCircle]
    rw [← image_union]
    congr 1
    exact (ball_union_sphere).symm
  rw [interior_compl,hclosure,hpartition]

end CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc
