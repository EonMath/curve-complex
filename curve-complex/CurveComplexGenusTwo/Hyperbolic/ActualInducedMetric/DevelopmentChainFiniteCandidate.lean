import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.DevelopmentChainLawsCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E : Type} [TopologicalSpace E] [PreconnectedSpace E]

theorem developmentChainEDist_finite_of_chart_coverage (F : Set (OpenPartialHomeomorph E H2))
    (hcover : ∀ x : E, ∃ e ∈ F, x ∈ e.source) (x y : E) :
    developmentChainEDist F x y ≠ ⊤ := by
  have hstep (e : OpenPartialHomeomorph E H2) (he : e ∈ F)
      (z w : E) (hz : z ∈ e.source) (hw : w ∈ e.source) :
      developmentChainEDist F z w ≠ ⊤ := by
    have hh := developmentChainEDist_le_chain
      (DevelopmentChain.cons e he hz hw (DevelopmentChain.nil w))
    simp only [add_zero] at hh
    exact ne_top_of_le_ne_top (edist_ne_top (e z) (e w)) hh
  have hreach (z w : E) (hz : developmentChainEDist F x z ≠ ⊤)
      (hzw : developmentChainEDist F z w ≠ ⊤) : developmentChainEDist F x w ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hz, hzw⟩)
      (developmentChainEDist_triangle F x z w)
  let R : Set E := {z | developmentChainEDist F x z ≠ ⊤}
  have hR : IsOpen R := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨e, he, hze⟩ := hcover z
    apply Filter.mem_of_superset (e.open_source.mem_nhds hze)
    intro w hw
    exact hreach z w hz (hstep e he z w hze hw)
  have hRc : IsOpen Rᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨e, he, hze⟩ := hcover z
    apply Filter.mem_of_superset (e.open_source.mem_nhds hze)
    intro w hw hwr
    exact hz (hreach w z hwr (hstep e he w z hw hze))
  have hRuniv : R = Set.univ :=
    (show IsClopen R from ⟨by simpa only [compl_compl] using hRc.isClosed_compl, hR⟩).eq_univ
      ⟨x, by simp [R, developmentChainEDist_self]⟩
  have hy : y ∈ R := by rw [hRuniv]; exact Set.mem_univ y
  exact hy

end CurveComplex.Hyperbolic
