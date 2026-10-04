import CurveComplexGenusTwo.Topology.ActualThreeArcCount.StripOpenCover
import CurveComplexGenusTwo.Topology.ActualThreeArcCount.ChartCapSurjection
import CurveComplexGenusTwo.Topology.ActualThreeArcCount.FiniteOpenCoverCount
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

open CurveComplex Set Topology CategoryTheory
open CurveComplexGenusTwo.CWHurewicz
open scoped Manifold ContDiff
noncomputable section
namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut
private abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem original_proper_arc_cut_count
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target) :
    let Q : Set S := exterior S x R
    let B : Set S := originalBoundary S x R
    ∀ (n : ℕ) (a : Fin n → C(Interval, ↥Q)),
      (∀ i, Topology.IsEmbedding (a i)) →
      (∀ i, (a i 0).val ∈ B ∧ (a i 1).val ∈ B) →
      (∀ i t, t ∈ Set.Ioo (0 : Interval) 1 → (a i t).val ∉ B) →
      (∀ i j, i ≠ j → Disjoint (Set.range (a i)) (Set.range (a j))) →
      (∀ U : Set S,
        CurveComplex.HyperellipticModel.IsComplementComponent
          (OriginalBoundaryArc.openDisk S x R ∪ B ∪ arcTrace a) U →
        U ⊆ interior Q →
        DiskRegion Q U ∨ BoundaryAnnulusRegion Q B U) →
      2 * g ≤ n := by
  classical
  dsimp only
  intro n a hemb hend hint hpairwise hregions
  letI : ClosedSurface S := Classical.choice hS.2.1
  let D := (OriginalBoundaryArc.openDisk S x R ∪ originalBoundary S x R ∪ arcTrace a)ᶜ
  obtain ⟨W, hW, hdisj, hcover, hoverlap⟩ :=
    original_disjoint_strips_open_cover S g hg hS x R hR htarget n a hemb hend hint hpairwise
  have hzero : homologyInclusion S D 1 = 0 :=
    original_standard_complement_homologyInclusion_zero S g hS x R hR htarget n a hregions 1 (by omega)
  have hD : IsOpen D := by
    have hball : IsCompact ((chartAt Plane x).symm ''
        Metric.closedBall ((chartAt Plane x) x) R) :=
      (isCompact_closedBall _ _).image_of_continuousOn
        ((chartAt Plane x).continuousOn_symm.mono htarget)
    have hbase : OriginalBoundaryArc.openDisk S x R ∪ originalBoundary S x R =
        (chartAt Plane x).symm '' Metric.closedBall ((chartAt Plane x) x) R := by
      simp only [OriginalBoundaryArc.openDisk, originalBoundary, OriginalBoundaryArc.boundaryCircle,
        ← Set.image_union, Metric.ball_union_sphere]
    suffices hc : IsClosed (OriginalBoundaryArc.openDisk S x R ∪ originalBoundary S x R ∪ arcTrace a) from hc.isOpen_compl
    change IsClosed ((OriginalBoundaryArc.openDisk S x R ∪ originalBoundary S x R) ∪ arcTrace a)
    rw [hbase]
    exact hball.isClosed.union (isClosed_iUnion_of_finite (fun i =>
      (isCompact_range (continuous_subtype_val.comp (a i).continuous)).isClosed))
  have hgenerators : ∃ v : Fin n → H S 1,
      ∀ y : H ↥(D ∪ ⋃ i, W i) 1,
        homologyInclusion S (D ∪ ⋃ i, W i) 1 y ∈ Submodule.span ℤ (Set.range v) := by
    have hh := finite_disjoint_open_cover_image_generators S D hD W hW hdisj hoverlap hzero
      (Finset.univ : Finset (Fin n))
    have hunion : (D ∪ ⋃ i ∈ (Finset.univ : Finset (Fin n)), W i) = D ∪ ⋃ i, W i := by simp
    rw [hunion, Finset.card_univ, Fintype.card_fin] at hh
    exact hh
  obtain ⟨v, hv⟩ := hgenerators
  change D ∪ ⋃ i, W i = interior (exterior S x R) at hcover
  rw [hcover] at hv
  have hsurj := original_open_exterior_homologyInclusion_surjective S g hS x R hR htarget
  have hspan : ∀ y : H S 1, y ∈ Submodule.span ℤ (Set.range v) := by
    intro y
    obtain ⟨z, rfl⟩ := hsurj y
    exact hv z
  let q := Fintype.linearCombination ℤ v
  have hq : Function.Surjective q := by
    intro y
    have hy := hspan y
    rwa [← Fintype.range_linearCombination, LinearMap.mem_range] at hy
  obtain ⟨e⟩ := hS.2.2.2
  let k := e.toLinearEquiv.toLinearMap.comp q
  have hk : Function.Surjective k := e.toLinearEquiv.surjective.comp hq
  have hfin := LinearMap.finrank_le_finrank_of_surjective hk
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using hfin

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
