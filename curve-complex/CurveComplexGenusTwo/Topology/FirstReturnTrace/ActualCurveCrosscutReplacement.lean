import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualFiniteCurveReplacement

namespace CurveComplex
open Set Topology Schoenflies

/-- Apply one supported proper square crosscut replacement to an ANY embedded
closed source curve, with arbitrary actual boundary endpoints. The output is a
closed ambient isotope, its exact replacement image, and pointwise ambient
support at EVERY time. This includes the corner L-to-diagonal replacement. -/
theorem source_curve_surface_crosscut_replacement
    (S : Type*) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (c : Curve S) (E : OpenPartialHomeomorph S Plane)
    (hSquare : Plane.closedSquare 0 1 ⊆ E.target)
    (A B : Set Plane) (u v : Plane)
    (hA : IsArcBetween A u v) (hB : IsArcBetween B u v)
    (hu : u ∈ modelCurve) (hv : v ∈ modelCurve)
    (hAi : A \ {u,v} ⊆ Plane.openSquare 0 1)
    (hBi : B \ {u,v} ⊆ Plane.openSquare 0 1)
    (hc : {x : S | x ∈ E.source ∧ E x ∈ Plane.closedSquare 0 1} ∩ c.image =
      {x : S | x ∈ E.source ∧ E x ∈ A}) :
    ∃ H : AmbientIsotopy S, ∃ d : Curve S,
      AmbientIsotopy.Rel c.image d.image ∧
      H.finalMap '' c.image = d.image ∧
      d.image = (c.image \ {x : S | x ∈ E.source ∧ E x ∈ A}) ∪
        {x : S | x ∈ E.source ∧ E x ∈ B} ∧
      ∀ t x, x ∉ {x : S | x ∈ E.source ∧ E x ∈ Plane.openSquare 0 1} →
        H.map (t,x) = x := by
  let Ap : Set S := {x | x ∈ E.source ∧ E x ∈ A}
  let Bp : Set S := {x | x ∈ E.source ∧ E x ∈ B}
  let Dp : Set S := {x | x ∈ E.source ∧ E x ∈ Plane.openSquare 0 1}
  have hPull (F : Set Plane) :
      {x : S | ∃ y : E.source, y.val = x ∧ (E.toHomeomorphSourceTarget y : Plane) ∈ F} =
      {x : S | x ∈ E.source ∧ E x ∈ F} := by
    ext x
    constructor
    · rintro ⟨y,rfl,hy⟩
      exact ⟨y.property,hy⟩
    · exact fun hx => ⟨⟨x,hx.1⟩,rfl,hx.2⟩
  obtain ⟨H,hHAp,hHfix⟩ := position_crosscut_surface_square_support S E.source E.target
    E.open_source E.toHomeomorphSourceTarget hSquare A B u v hA hB hu hv hAi hBi
  rw [hPull,hPull] at hHAp
  simp only [hPull] at hHfix
  have hApcurve : Ap ⊆ c.image := by
    intro x hx
    have hh : x ∈ {x : S | x ∈ E.source ∧ E x ∈ Plane.closedSquare 0 1} ∩ c.image :=
      hc.symm ▸ hx
    exact hh.2
  have hDcurve : Dp ∩ c.image ⊆ Ap := by
    intro x hx
    change x ∈ {x : S | x ∈ E.source ∧ E x ∈ A}
    rw [← hc]
    exact ⟨⟨hx.1.1,Plane.openSquare_subset_closedSquare 0 1 hx.1.2⟩,hx.2⟩
  have hfixRest (x : S) (hx : x ∈ c.image \ Ap) : H.finalMap x = x :=
    hHfix ⟨1,by norm_num⟩ x (fun hh => hx.2 (hDcurve ⟨hh,hx.1⟩))
  have hrest : H.finalMap '' (c.image \ Ap) = c.image \ Ap := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa [hfixRest y hy] using hy
    · intro hx
      exact ⟨x,hx,hfixRest x hx⟩
  obtain ⟨e,he⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  let d : Curve S := ⟨e ∘ c.map,e.isEmbedding.comp c.embedded⟩
  have hd : d.image = H.finalMap '' c.image := by
    change Set.range (e ∘ c.map) = H.finalMap '' Set.range c.map
    rw [Set.range_comp]
    exact Set.image_congr (fun x _ => he x)
  refine ⟨H,d,⟨H,hd.symm⟩,hd.symm,?_,hHfix⟩
  rw [hd]
  calc
    H.finalMap '' c.image = H.finalMap '' ((c.image \ Ap) ∪ Ap) :=
      congrArg (fun X => H.finalMap '' X) (Set.sdiff_union_of_subset hApcurve).symm
    _ = _ := by rw [Set.image_union,hrest,hHAp]

end CurveComplex
#print axioms CurveComplex.source_curve_surface_crosscut_replacement
