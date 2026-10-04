import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSingleReferenceOpenFinitePosition
namespace CurveComplex
open Set
/-- Finite position inside a prescribed open region, with the entire complement
fixed throughout the actual ambient isotopy and the final whole curve retained. -/
theorem actual_open_finite_position_retains_source
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace Schoenflies.Plane S] [ClosedSurface S]
    (a c : EssentialCurve S) (W : Set S) (hW : IsOpen W)
    (hcW : c.val.image ⊆ W) :
    ∃ F : AmbientIsotopy S, ∃ d : EssentialCurve S,
      (∀ t x, x ∉ W → F.map (t,x) = x) ∧
      (∀ t x, x ∈ W → F.map (t,x) ∈ W) ∧
      d.val.image = F.finalMap '' c.val.image ∧
      d.val.image ⊆ W ∧
      Quotient.mk (essentialCurveSetoid S) d = Quotient.mk (essentialCurveSetoid S) c ∧
      Transverse a.val d.val := by
  obtain ⟨F,d,hfix,himage,hclass,htrans⟩ :=
    actual_single_reference_open_finite_position S a c W hW hcW
  have hstay : ∀ t x, x ∈ W → F.map (t,x) ∈ W := by
    intro t x hx
    by_contra hout
    obtain ⟨e,he⟩ := F.homeomorphism_at t
    have heq : e (F.map (t,x)) = e x := by
      rw [he, hfix t (F.map (t,x)) hout, he]
    have heq' : F.map (t,x) = x := e.injective heq
    exact hout (heq'.symm ▸ hx)
  refine ⟨F,d,hfix,hstay,himage,?_,hclass,htrans⟩
  rw [himage]
  rintro x ⟨y,hy,rfl⟩
  exact hstay ⟨1,by norm_num⟩ y (hcW hy)
end CurveComplex
