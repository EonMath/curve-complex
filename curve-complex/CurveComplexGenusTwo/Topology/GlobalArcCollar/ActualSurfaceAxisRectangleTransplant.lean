import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualSupportedChartConjugation
namespace CurveComplex
open Set Topology Schoenflies

def sourceSquareTransverseNarrow (δ : ℝ) (hδ : 0 < δ ∧ δ ≤ 1)
    (z : ↥(Plane.closedSquare 0 1)) : ↥(Plane.closedSquare 0 1) :=
  ⟨Plane.mk (z.val 0) (δ * z.val 1), by
    have hz : max |z.val 0| |z.val 1| ≤ 1 := by
      simpa [Plane.closedSquare, Plane.supDist, Plane.supNorm] using z.property
    have hx := (le_max_left _ _).trans hz
    have hy := (le_max_right _ _).trans hz
    simpa [Plane.closedSquare, Plane.supDist, Plane.supNorm, abs_mul,
      abs_of_pos hδ.1] using
      max_le hx ((mul_le_mul_of_nonneg_left hy hδ.1.le).trans
        (by simpa using hδ.2))⟩

/-- Actual surface rectangle replacement, with center and support control.
The sign is produced from the embedded local geometry. -/
theorem source_surface_axis_rectangle_transplant
    {S : Type} [TopologicalSpace S] [T2Space S]
    (e : OpenPartialHomeomorph S Plane)
    (ht : Plane.closedSquare 0 2 ⊆ e.target)
    (f : C(Interval,S))
    (haxis : ∀ u, f u ∈ e.source → e (f u) 1 = 0)
    (B : ↥(Plane.closedSquare 0 1) → S) (hB : IsEmbedding B)
    (hBs : Set.range B ⊆ e.source)
    (hc : ∀ t : Icc (-1 : ℝ) 1,
      e (B ⟨Plane.mk t 0, by
        simpa [Plane.closedSquare, Plane.supDist, Plane.supNorm] using abs_le.mpr t.property⟩) =
        Plane.mk t 0)
    (hmeet : Set.range (e ∘ B) ∩ {z : Plane | z 1 = 0} =
      (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ ∧ δ ≤ 1, ∃ σ : ℝ, ∃ F : S ≃ₜ S,
      (σ = -1 ∨ σ = 1) ∧
      (∀ u, F (f u) = f u) ∧
      (∀ x, x ∉ e.source ∩ e ⁻¹' Plane.openSquare 0 2 → F x = x) ∧
      ∀ z : ↥(Plane.closedSquare 0 1),
        F (B (sourceSquareTransverseNarrow δ hδ z)) ∈ e.source ∧
        e (F (B (sourceSquareTransverseNarrow δ hδ z))) =
          Plane.mk (z.val 0) (σ * z.val 1) := by
  let P : ↥(Plane.closedSquare 0 1) → Plane := e ∘ B
  have hPc : Continuous P := e.continuousOn.comp_continuous hB.continuous
    (fun z => hBs (Set.mem_range_self z))
  have hPi : Function.Injective P := by
    intro z w he
    exact hB.injective (e.injOn (hBs (Set.mem_range_self z))
      (hBs (Set.mem_range_self w)) he)
  have hPe : IsEmbedding P := by
    letI : CompactSpace ↥(Plane.closedSquare 0 1) :=
      isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
    exact (hPc.isClosedEmbedding hPi).isEmbedding
  obtain ⟨δ,hδ,σ,G,hσ,hGfix,hGaxis,hGformula⟩ :=
    source_axis_rectangle_transplant P hPe hc hmeet
  obtain ⟨F,hFfix,hFformula,hFfixed⟩ :=
    source_transport_supported_chart_homeomorphism e
      (Plane.closedSquare 0 2) (Plane.openSquare 0 2)
      (isCompact_closedSquare 0 2) (Plane.isOpen_openSquare 0 2)
      (fun z hz => by
        change Plane.supDist z 0 ≤ 2
        exact (show Plane.supDist z 0 < 2 from hz).le) ht G hGfix
  have hGaxis' : ∀ z : Plane, z 1 = 0 → G z = z := by
    intro z hz
    have he : z = Plane.mk (z 0) 0 := by
      apply PiLp.ext
      intro i
      fin_cases i
      · rfl
      · exact hz
    rw [he,hGaxis]
  refine ⟨δ,hδ,σ,F,hσ,?_,hFfix,?_⟩
  · intro u
    by_cases hs : f u ∈ e.source
    · exact hFfixed _ hs (hGaxis' _ (haxis u hs))
    · exact hFfix _ (fun h => hs h.1)
  · intro z
    let q := sourceSquareTransverseNarrow δ hδ z
    have hgf : G (e (B q)) = Plane.mk (z.val 0) (σ*z.val 1) := hGformula z
    by_cases hmem : e (B q) ∈ Plane.closedSquare 0 2
    · obtain ⟨hsource,hcoord⟩ := hFformula (B q) (hBs (Set.mem_range_self q)) hmem
      exact ⟨hsource,hcoord.trans hgf⟩
    · have hout : e (B q) ∉ Plane.openSquare 0 2 := by
        intro ho
        exact hmem (show Plane.supDist (e (B q)) 0 ≤ 2 from
          (show Plane.supDist (e (B q)) 0 < 2 from ho).le)
      have hFx := hFfix (B q) (fun h => hout h.2)
      rw [hFx]
      exact ⟨hBs (Set.mem_range_self q),(hGfix _ hout).symm.trans hgf⟩
end CurveComplex
#print axioms CurveComplex.source_surface_axis_rectangle_transplant
