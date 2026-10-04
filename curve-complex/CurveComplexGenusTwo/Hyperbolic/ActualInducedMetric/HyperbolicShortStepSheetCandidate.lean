import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualCoverLocalCharts
import CurveComplexGenusTwo.Hyperbolic.CompactSegmentParametrization
import Mathlib.Analysis.Convex.Topology

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]

theorem hyperbolic_ball_inter_preconnected (a b : H2) (r s : ℝ) :
    IsPreconnected (Metric.ball a r ∩ Metric.ball b s) := by
  apply (UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image).mp
  rw [Set.image_inter UpperHalfPlane.coe_injective,
    UpperHalfPlane.image_coe_ball, UpperHalfPlane.image_coe_ball]
  exact ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected

private theorem hyperbolic_ball_inter_isPreconnected (a b : H2) (r s : ℝ) :
    IsPreconnected (Metric.ball a r ∩ Metric.ball b s) := by
  apply (UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image).mp
  rw [Set.image_inter UpperHalfPlane.coe_injective,
    UpperHalfPlane.image_coe_ball, UpperHalfPlane.image_coe_ball]
  exact ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected

theorem hyperbolic_short_step_stays_in_sheet {B : Type} [MetricSpace B] (b : E → B)
    (e : OpenPartialHomeomorph E H2) (c : H2) (s : ℝ)
    (htarget : e.target = Metric.ball c s)
    (hcontract : ∀ y ∈ e.source, ∀ z ∈ e.source, dist (b y) (b z) ≤ dist (e y) (e z))
    (A D : Set E) (hA : IsOpen A) (hD : IsOpen D) (hdisj : Disjoint A D)
    (o : B) (r : ℝ) (hcover : b ⁻¹' Metric.ball o r ⊆ A ∪ D)
    (x y : E) (hx : x ∈ e.source) (hy : y ∈ e.source) (hxA : x ∈ A)
    (hshort : dist (b x) o + dist (e x) (e y) < r) : y ∈ A := by
  let t := r - dist (b x) o
  have ht : 0 < t := by dsimp [t]; linarith [(dist_nonneg : 0 ≤ dist (e x) (e y))]
  let C := Metric.ball c s ∩ Metric.ball (e x) t
  have hC : IsPreconnected C := hyperbolic_ball_inter_isPreconnected _ _ _ _
  have hCtarget : C ⊆ e.target := by rw [htarget]; exact Set.inter_subset_left
  let K := e.symm '' C
  have hK : IsPreconnected K := hC.image e.symm (e.continuousOn_symm.mono hCtarget)
  have hxC : e x ∈ C := ⟨htarget ▸ e.map_source hx, Metric.mem_ball_self ht⟩
  have hyC : e y ∈ C := by
    refine ⟨htarget ▸ e.map_source hy, ?_⟩
    change dist (e y) (e x) < t
    rw [dist_comm]
    dsimp [t]
    linarith
  have hxK : x ∈ K := ⟨e x, hxC, e.left_inv hx⟩
  have hyK : y ∈ K := ⟨e y, hyC, e.left_inv hy⟩
  have hKB : K ⊆ b ⁻¹' Metric.ball o r := by
    rintro z ⟨w, hw, rfl⟩
    have hws : e.symm w ∈ e.source := e.map_target (hCtarget hw)
    have hdist := hcontract (e.symm w) hws x hx
    rw [e.right_inv (hCtarget hw)] at hdist
    have hwball : dist w (e x) < t := hw.2
    change dist (b (e.symm w)) o < r
    have hh := dist_triangle (b (e.symm w)) (b x) o
    dsimp [t] at hwball
    linarith
  have hKA := hK.subset_left_of_subset_union hA hD hdisj
    (hKB.trans hcover) ⟨x, hxK, hxA⟩
  exact hKA hyK

end CurveComplex.Hyperbolic
