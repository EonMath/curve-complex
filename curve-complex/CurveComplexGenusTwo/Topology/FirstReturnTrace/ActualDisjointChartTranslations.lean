import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualTranslatedCurveChart
namespace CurveComplex
open Set Topology Schoenflies Metric
/-- A genuinely supported ambient map preserves the whole curve image outside
its support, by injectivity of the time-one homeomorphism. -/
theorem source_supported_curve_image_outside
    {S : Type*} [TopologicalSpace S] (H : AmbientIsotopy S)
    (A U : Set S) (hfix : ∀ t x, x ∉ U → H.map (t,x)=x) :
    ∀ x, x ∉ U → (x ∈ H.finalMap '' A ↔ x ∈ A) := by
  obtain ⟨e,he⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hi : Function.Injective H.finalMap := by
    intro x y h
    exact e.injective ((he x).trans (h.trans (he y).symm))
  intro x hx
  have hfx : H.finalMap x=x := hfix ⟨1,by norm_num⟩ x hx
  constructor
  · rintro ⟨y,hy,hyx⟩
    exact (hi (hyx.trans hfx.symm)) ▸ hy
  · intro hh
    exact ⟨x,hh,hfx⟩

/-- Apply actual supported translations in two disjoint charts to one whole
closed curve. Both precise local traces survive the global composition. -/
theorem source_two_disjoint_closed_curve_chart_translations
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
      ∀ k x, x ∈ (E k).source → ‖E k x-v k‖ ≤ 1/4 →
        (x ∈ d.image ↔ P k (E k x-v k)) := by
  classical
  obtain ⟨G0,d0,hd0,hr0,hs0,hm0,hf0,ht0⟩ :=
    source_closed_curve_supported_chart_translation S c (E false)
      (hsquare false) (P false) (htrace false) (v false) (hv false)
  have hout0 (x : S) (hx : x ∉ (E false).source) : x ∈ d0.image ↔ x ∈ c.image := by
    rw [hd0]
    exact source_supported_curve_image_outside G0 c.image (E false).source hf0 x hx
  have htrace1 (x : S) (hx : x ∈ (E true).source) : x ∈ d0.image ↔ P true (E true x) :=
    (hout0 x (fun h => Set.disjoint_left.mp hdis h hx)).trans (htrace true x hx)
  obtain ⟨G1,d1,hd1,hr1,hs1,hm1,hf1,ht1⟩ :=
    source_closed_curve_supported_chart_translation S d0 (E true)
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
  refine ⟨H,d1,hd,⟨H,hd.symm⟩,?_,?_,?_,?_⟩
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
end CurveComplex
#print axioms CurveComplex.source_supported_curve_image_outside
#print axioms CurveComplex.source_two_disjoint_closed_curve_chart_translations
