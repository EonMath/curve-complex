import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualChartSupportedTranslation
namespace CurveComplex
open Set Topology Schoenflies Metric
/-- Derive a positive displacement radius that retains an ACTUAL compact set
inside a requested open neighborhood under any small supported chart map. -/
theorem source_compact_chart_displacement_radius
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (E : OpenPartialHomeomorph S Plane)
    (hSquare : Plane.closedSquare (0 : Plane) 1 ⊆ E.target)
    (K U : Set S) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (f : S → S),
        (∀ x, x ∉ E.source → f x=x) →
        (∀ x, x ∈ E.source → f x ∈ E.source) →
        (∀ x, x ∈ E.source → 1/2 ≤ ‖E x‖ → f x=x) →
        (∀ x, x ∈ E.source → ‖E (f x)-E x‖ < r) → f '' K ⊆ U := by
  have hCV : closedBall (0 : Plane) (1/2) ⊆ E.target := by
    intro z hz
    apply hSquare
    rw [mem_closedSquare_zero_one]
    have hn : ‖z‖ ≤ 1/2 := by simpa only [mem_closedBall,dist_zero_right] using hz
    exact (Plane.supNorm_le_norm z).trans (by linarith)
  let C : Set S := E.symm '' closedBall (0 : Plane) (1/2)
  have hC : IsCompact C :=
    (isCompact_closedBall _ _).image_of_continuousOn (E.symm.continuousOn.mono hCV)
  have hCs : C ⊆ E.source := by
    rintro x ⟨z,hz,rfl⟩
    exact E.symm.mapsTo (hCV hz)
  let Y : Set Plane := E '' (K ∩ C)
  have hY : IsCompact Y :=
    (hC.inter_left hK.isClosed).image_of_continuousOn
      (E.continuousOn.mono (fun x hx=>hCs hx.2))
  let V : Set Plane := E.target ∩ E.symm ⁻¹' U
  have hV : IsOpen V := E.isOpen_inter_preimage_symm hU
  have hYV : Y ⊆ V := by
    rintro y ⟨x,hx,rfl⟩
    refine ⟨E.mapsTo (hCs hx.2),?_⟩
    change E.symm (E x) ∈ U
    rw [E.left_inv (hCs hx.2)]
    exact hKU hx.1
  obtain ⟨r,hr,hthick⟩ := hY.exists_thickening_subset_open hV hYV
  refine ⟨r,hr,?_⟩
  intro f hfix hsource hfar hmove
  rintro y ⟨x,hxK,rfl⟩
  by_cases hxE : x ∈ E.source
  · by_cases hhalf : 1/2 ≤ ‖E x‖
    · rw [hfar x hxE hhalf]; exact hKU hxK
    · have hxC : x ∈ C := by
        refine ⟨E x,?_,E.left_inv hxE⟩
        simpa only [mem_closedBall,dist_zero_right] using (le_of_not_ge hhalf)
      have hyV : E (f x) ∈ V := hthick
        (Metric.mem_thickening_iff.mpr ⟨E x,⟨x,⟨hxK,hxC⟩,rfl⟩,by
          simpa only [dist_eq_norm] using hmove x hxE⟩)
      have hyU := hyV.2
      change E.symm (E (f x)) ∈ U at hyU
      rw [E.left_inv (hsource x hxE)] at hyU
      exact hyU
  · rw [hfix x hxE]; exact hKU hxK
end CurveComplex

#print axioms CurveComplex.source_compact_chart_displacement_radius
