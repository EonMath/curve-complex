import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualChartSupportedTranslation
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualSmallSupportedTranslationBound
namespace CurveComplex
open Set Topology Schoenflies Metric
/-- Actual surface lift with global displacement control in chart coordinates. -/
theorem source_chart_small_supported_translation_with_displacement
    (S : Type*) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (E : OpenPartialHomeomorph S Plane)
    (hSquare : Plane.closedSquare (0 : Plane) 1 ⊆ E.target)
    (v : Plane) (hv : ‖v‖ < 1/4) :
    ∃ G : AmbientIsotopy S,
      (∀ t x, x ∈ E.source → G.map (t,x) ∈ E.source) ∧
      (∀ t x, x ∈ E.source → ‖E x‖ ≤ 1/4 →
        E (G.map (t,x)) = E x+(t:ℝ) • v) ∧
      (∀ t x, x ∈ E.source → 1/2 ≤ ‖E x‖ → G.map (t,x)=x) ∧
      (∀ t x, x ∉ E.source → G.map (t,x)=x) ∧
      ∀ t x, x ∈ E.source → ‖E (G.map (t,x))-E x‖ ≤ ‖v‖ := by
  have hC : IsCompact (closedBall (0 : Plane) (1/2)) := isCompact_closedBall _ _
  have hCV : closedBall (0 : Plane) (1/2) ⊆ E.target := by
    intro z hz
    apply hSquare
    rw [mem_closedSquare_zero_one]
    have hn : ‖z‖ ≤ 1/2 := by simpa only [mem_closedBall,dist_zero_right] using hz
    exact (Plane.supNorm_le_norm z).trans (by linarith)
  obtain ⟨H,hmove,hfix,hdisp⟩ := source_small_supported_plane_translation_with_displacement v hv
  obtain ⟨K,G,hcoord,hGU,hGfix⟩ := position_surface_chart_lift S
    E.source E.target E.open_source E.toHomeomorphSourceTarget
    (closedBall 0 (1/2)) hC hCV H (by
      intro t x hx
      apply hfix
      have hh : ¬ dist x (0 : Plane) ≤ 1/2 := hx
      simpa only [dist_zero_right] using (lt_of_not_ge hh).le)
  have hsource (t : Interval) (x : S) (hx : x ∈ E.source) :
      G.map (t,x) ∈ E.source := by
    rw [hGU t ⟨x,hx⟩]
    exact (K.map (t,⟨x,hx⟩)).property
  have hformula (t : Interval) (x : S) (hx : x ∈ E.source) :
      E (G.map (t,x)) = H.map (t,E x) := by
    rw [hGU t ⟨x,hx⟩]
    exact hcoord t ⟨x,hx⟩
  refine ⟨G,hsource,?_,?_,hGfix,?_⟩
  · intro t x hx hn
    rw [hformula t x hx,hmove t (E x) hn]
  · intro t x hx hn
    apply E.injOn (hsource t x hx) hx
    rw [hformula t x hx,hfix t (E x) hn]
  · intro t x hx
    rw [hformula t x hx]
    exact hdisp t (E x)
end CurveComplex

#print axioms CurveComplex.source_chart_small_supported_translation_with_displacement
