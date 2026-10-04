import CurveComplexGenusTwo.Topology.Smoothing.SphereAtlasProof
import CurveComplexGenusTwo.Topology.Smoothing.ActualGermArcs
import CurveComplexGenusTwo.Topology.Smoothing.UniformActualGerms

open Set
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The actual incident germs admit one uniformly cut finite star in the
prescribed smooth atlas. The selected neighborhood avoids the central pieces,
nonincident arcs and every other mark; loop incidences are retained separately. -/
theorem actual_endpoint_star_in_smooth_chart
    (M : HyperellipticModel E S) (C : SphereSmoothAtlas S)
    (ι : Type) [Fintype ι] (a : ι → EssentialMarkedArc M)
    (p : S) (hp : p ∈ M.cover.branch) :
    letI := C.charts
    ∃ U : Set S, IsOpen U ∧ p ∈ U ∧
      U ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source ∧
      (∀ q, q ∈ M.cover.branch → q ∈ U → q = p) ∧
      (∀ i t, (1 / 4 : ℝ) ≤ (t : Interval).val → t.val ≤ 3 / 4 → (a i).val.map t ∉ U) ∧
      (∀ i, (a i).val.map ⟨0, by norm_num⟩ ≠ p →
        (a i).val.map ⟨1, by norm_num⟩ ≠ p → Disjoint (a i).val.image U) ∧
      ∃ (r : ℝ) (hr : 0 < r) (hrhalf : r < 1 / 2),
        ∀ (i : ι) (terminal : Bool),
          (if terminal then (a i).val.map ⟨1, by norm_num⟩
            else (a i).val.map ⟨0, by norm_num⟩) = p →
          (∀ t : Interval, (a i).val.map
            (endpointGermParameter terminal r hr (by linarith) t) ∈ U) ∧
          Schoenflies.IsArcBetween
            (Set.range (fun t : Interval =>
              (chartAt (EuclideanSpace ℝ (Fin 2)) p)
                ((a i).val.map (endpointGermParameter terminal r hr (by linarith) t))))
            ((chartAt (EuclideanSpace ℝ (Fin 2)) p)
              ((a i).val.map (endpointGermParameter terminal r hr (by linarith) ⟨0, by norm_num⟩)))
            ((chartAt (EuclideanSpace ℝ (Fin 2)) p)
              ((a i).val.map (endpointGermParameter terminal r hr (by linarith) ⟨1, by norm_num⟩))) := by
  classical
  letI := C.charts
  letI : T2Space S := M.sphere.symm.t2Space
  let otherMarks : Set S := (M.cover.branch : Set S) \ {p}
  have hotherClosed : IsClosed otherMarks := by
    exact (M.cover.branch.finite_toSet.sdiff).isClosed
  let W := (chartAt (EuclideanSpace ℝ (Fin 2)) p).source ∩ otherMarksᶜ
  have hW : IsOpen W := (chartAt (EuclideanSpace ℝ (Fin 2)) p).open_source.inter hotherClosed.isOpen_compl
  have hpW : p ∈ W := ⟨mem_chart_source _ p, by simp [otherMarks]⟩
  obtain ⟨U, hU, hpU, hUW, hcentral, hnoninc⟩ := actual_endpoint_isolation
    M ι a p hp (1 / 4) (by norm_num) (by norm_num) W hW hpW
  obtain ⟨r, hr, hrhalf, hstart, hend⟩ := uniform_actual_endpoint_germs M ι a p U hU hpU
  have hchart : U ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source :=
    fun x hx => (hUW hx).1
  refine ⟨U, hU, hpU, hchart, ?_, ?_, hnoninc, r, hr, hrhalf, ?_⟩
  · intro q hq hqU
    by_contra hqp
    exact (hUW hqU).2 ⟨hq, by simpa using hqp⟩
  · intro i t ht0 ht1
    exact hcentral i t ht0 (by linarith)
  · intro i b hb
    have hsub : ∀ t : Interval, (a i).val.map
        (endpointGermParameter b r hr (by linarith) t) ∈ U := by
      intro t
      cases b
      · apply hstart i hb
        change r * t.val ≤ r
        nlinarith [t.property.2]
      · apply hend i hb
        change 1 - r ≤ 1 - r * t.val
        nlinarith [t.property.2]
    exact ⟨hsub, actual_endpoint_germ_chart_arc M (a i) b r hr (by linarith)
      (chartAt (EuclideanSpace ℝ (Fin 2)) p) (fun t => hchart (hsub t))⟩

#print axioms actual_endpoint_star_in_smooth_chart
end CurveComplex.HyperellipticModel
