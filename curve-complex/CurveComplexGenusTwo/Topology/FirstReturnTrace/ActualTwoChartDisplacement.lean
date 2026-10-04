import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualDisjointChartTranslations
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualChartSupportedTranslationBound
set_option maxHeartbeats 3000000
namespace CurveComplex
open Set Topology Schoenflies Metric
theorem source_two_disjoint_closed_curve_chart_translations_with_displacement
    (S : Type*) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (c : Curve S) (E : Bool → OpenPartialHomeomorph S Plane)
    (hsquare : ∀ k, Plane.closedSquare (0 : Plane) 1 ⊆ (E k).target)
    (hdis : Disjoint (E false).source (E true).source)
    (P : Bool → Plane → Prop)
    (htrace : ∀ k x, x ∈ (E k).source → (x ∈ c.image ↔ P k (E k x)))
    (v : Bool → Plane) (hv : ∀ k, ‖v k‖ < 1/4) :
    ∃ H : AmbientIsotopy S, ∃ d : Curve S,
      d.image = H.finalMap '' c.image ∧ AmbientIsotopy.Rel c.image d.image ∧
      (∀ t x, x ∉ (E false).source ∪ (E true).source → H.map (t,x)=x) ∧
      (∀ k t x, x ∈ (E k).source → H.map (t,x) ∈ (E k).source) ∧
      (∀ k t x, x ∈ (E k).source → ‖E k x‖ ≤ 1/4 →
        E k (H.map (t,x))=E k x+(t:ℝ) • v k) ∧
      (∀ k x, x ∈ (E k).source → ‖E k x-v k‖ ≤ 1/4 →
        (x ∈ d.image ↔ P k (E k x-v k))) ∧
      (∀ k t x, x ∈ (E k).source → 1/2 ≤ ‖E k x‖ → H.map (t,x)=x) ∧
      ∀ k t x, x ∈ (E k).source → ‖E k (H.map (t,x))-E k x‖ ≤ ‖v k‖ := by
  have hClosedBound
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
        (∀ x ∈ E.source, ‖E x-v‖ ≤ 1/4 → (x ∈ d.image ↔ P (E x-v))) ∧
        (∀ t x, x ∈ E.source → 1/2 ≤ ‖E x‖ → G.map (t,x)=x) ∧
        ∀ t x, x ∈ E.source → ‖E (G.map (t,x))-E x‖ ≤ ‖v‖ := by
    classical
    obtain ⟨G,hsource,hmove,hannulus,hfix,hdisp⟩ :=
      source_chart_small_supported_translation_with_displacement S E hSquare v hv
    obtain ⟨e,he⟩ := G.homeomorphism_at ⟨1,by norm_num⟩
    let d : Curve S := ⟨e ∘ c.map,e.isEmbedding.comp c.embedded⟩
    have hd : d.image = G.finalMap '' c.image := by
      change Set.range (e ∘ c.map) = G.finalMap '' Set.range c.map
      rw [Set.range_comp]
      exact Set.image_congr (fun x _ => he x)
    refine ⟨G,d,hd,⟨G,hd.symm⟩,hsource,hmove,hfix,?_,hannulus,hdisp⟩
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
  classical
  obtain ⟨G0,d0,hd0,hr0,hs0,hm0,hf0,ht0,hfar0,hdisp0⟩ :=
    hClosedBound c (E false)
      (hsquare false) (P false) (htrace false) (v false) (hv false)
  have hout0 (x : S) (hx : x ∉ (E false).source) : x ∈ d0.image ↔ x ∈ c.image := by
    rw [hd0]
    exact source_supported_curve_image_outside G0 c.image (E false).source hf0 x hx
  have htrace1 (x : S) (hx : x ∈ (E true).source) : x ∈ d0.image ↔ P true (E true x) :=
    (hout0 x (fun h => Set.disjoint_left.mp hdis h hx)).trans (htrace true x hx)
  obtain ⟨G1,d1,hd1,hr1,hs1,hm1,hf1,ht1,hfar1,hdisp1⟩ :=
    hClosedBound d0 (E true)
      (hsquare true) (P true) htrace1 (v true) (hv true)
  let F : Interval × S → S := fun p => G1.map (p.1,G0.map p)
  have hFc : Continuous F := G1.map.continuous.comp
    (continuous_fst.prodMk G0.map.continuous)
  let H : AmbientIsotopy S := {
    map := ⟨F,hFc⟩
    homeomorphism_at := by
      intro t
      obtain ⟨e,he⟩ := G0.homeomorphism_at t
      obtain ⟨f,hf⟩ := G1.homeomorphism_at t
      refine ⟨e.trans f,?_⟩
      intro x
      change f (e x)=G1.map (t,G0.map (t,x))
      rw [he,hf]
    at_zero := by
      intro x
      change G1.map (⟨0,by norm_num⟩,G0.map (⟨0,by norm_num⟩,x))=x
      rw [G0.at_zero,G1.at_zero] }
  have hH (t : Interval) (x : S) : H.map (t,x)=G1.map (t,G0.map (t,x)) := rfl
  have hfirst (t : Interval) (x : S) (hx : x ∈ (E false).source) :
      H.map (t,x)=G0.map (t,x) := by
    rw [hH]
    exact hf1 t _ (fun h => Set.disjoint_left.mp hdis (hs0 t x hx) h)
  have hsecond (t : Interval) (x : S) (hx : x ∈ (E true).source) :
      H.map (t,x)=G1.map (t,x) := by
    rw [hH,hf0 t x (fun h => Set.disjoint_left.mp hdis h hx)]
  have hfinal : H.finalMap=G1.finalMap ∘ G0.finalMap := rfl
  have hd : d1.image=H.finalMap '' c.image := by
    rw [hd1,hd0,Set.image_image,hfinal]
    rfl
  have hout1 (x : S) (hx : x ∉ (E true).source) : x ∈ d1.image ↔ x ∈ d0.image := by
    rw [hd1]
    exact source_supported_curve_image_outside G1 d0.image (E true).source hf1 x hx
  refine ⟨H,d1,hd,⟨H,hd.symm⟩,?_,?_,?_,?_,?_,?_⟩
  · intro t x hx
    rw [Set.mem_union,not_or] at hx
    rw [hH,hf0 t x hx.1,hf1 t x hx.2]
  · intro k t x hx
    cases k
    · rw [hfirst t x hx]; exact hs0 t x hx
    · rw [hsecond t x hx]; exact hs1 t x hx
  · intro k t x hx hn
    cases k
    · rw [hfirst t x hx]; exact hm0 t x hx hn
    · rw [hsecond t x hx]; exact hm1 t x hx hn
  · intro k x hx hn
    cases k
    · exact (hout1 x (fun h => Set.disjoint_left.mp hdis hx h)).trans (ht0 x hx hn)
    · exact ht1 x hx hn
  · intro k t x hx hn
    cases k
    · rw [hfirst t x hx]; exact hfar0 t x hx hn
    · rw [hsecond t x hx]; exact hfar1 t x hx hn
  · intro k t x hx
    cases k
    · rw [hfirst t x hx]; exact hdisp0 t x hx
    · rw [hsecond t x hx]; exact hdisp1 t x hx
end CurveComplex

#print axioms CurveComplex.source_two_disjoint_closed_curve_chart_translations_with_displacement
