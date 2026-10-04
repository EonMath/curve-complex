import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualChartSupportedTranslation
namespace CurveComplex
open Set Topology Schoenflies Metric
/-- Translate an ACTUAL whole closed curve by a supported surface ambient
isotopy. The local image predicate is pulled back by the exact affine inverse. -/
theorem source_closed_curve_supported_chart_translation
    (S : Type*) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (c : Curve S) (E : OpenPartialHomeomorph S Plane)
    (hSquare : Plane.closedSquare (0 : Plane) 1 ⊆ E.target)
    (P : Plane → Prop) (htrace : ∀ x ∈ E.source, x ∈ c.image ↔ P (E x))
    (v : Plane) (hv : ‖v‖ < 1/4) :
    ∃ G : AmbientIsotopy S, ∃ d : Curve S,
      d.image = G.finalMap '' c.image ∧ AmbientIsotopy.Rel c.image d.image ∧
      (∀ t x, x ∈ E.source → G.map (t,x) ∈ E.source) ∧
      (∀ t x, x ∈ E.source → ‖E x‖ ≤ 1/4 →
        E (G.map (t,x))=E x+(t:ℝ) • v) ∧
      (∀ t x, x ∉ E.source → G.map (t,x)=x) ∧
      (∀ x ∈ E.source, ‖E x-v‖ ≤ 1/4 → (x ∈ d.image ↔ P (E x-v))) := by
  classical
  obtain ⟨G,hsource,hmove,hannulus,hfix⟩ :=
    source_chart_small_supported_translation S E hSquare v hv
  obtain ⟨e,he⟩ := G.homeomorphism_at ⟨1,by norm_num⟩
  let d : Curve S := ⟨e ∘ c.map,e.isEmbedding.comp c.embedded⟩
  have hd : d.image = G.finalMap '' c.image := by
    change Set.range (e ∘ c.map) = G.finalMap '' Set.range c.map
    rw [Set.range_comp]
    exact Set.image_congr (fun x _ => he x)
  refine ⟨G,d,hd,⟨G,hd.symm⟩,hsource,hmove,hfix,?_⟩
  intro x hx hn
  let z : Plane := E x-v
  have hz : z ∈ E.target := by
    apply hSquare
    rw [mem_closedSquare_zero_one]
    exact (Plane.supNorm_le_norm z).trans (hn.trans (by norm_num))
  let y : S := E.symm z
  have hy : y ∈ E.source := E.symm.map_source hz
  have hEy : E y=z := E.right_inv hz
  have hGy : G.finalMap y=x := by
    apply E.injOn (hsource ⟨1,by norm_num⟩ y hy) hx
    rw [hmove ⟨1,by norm_num⟩ y hy (by simpa only [hEy] using hn)]
    simp [hEy,z]
  have hinj : Function.Injective G.finalMap := by
    intro a b hab
    apply e.injective
    exact (he a).trans (hab.trans (he b).symm)
  have hmem : x ∈ d.image ↔ y ∈ c.image := by
    rw [hd]
    constructor
    · rintro ⟨w,hw,hwx⟩
      have hwy := hinj (hwx.trans hGy.symm)
      simpa only [hwy] using hw
    · intro hh
      exact ⟨y,hh,hGy⟩
  rw [hmem,htrace y hy,hEy]
end CurveComplex
#print axioms CurveComplex.source_closed_curve_supported_chart_translation
