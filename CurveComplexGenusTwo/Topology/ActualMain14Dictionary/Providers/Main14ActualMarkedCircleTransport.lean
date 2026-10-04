import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualMarkedCircleTransport
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
theorem actual_marked_isotopy_circle33_transport
    (M : HyperellipticModel E S) (c : Circle33 M) (L : AmbientIsotopy S)
    (hfix : ∀ t x, x ∈ M.cover.branch → L.map (t,x) = x) :
    ∃ c' : Circle33 M, c'.val.image = L.finalMap '' c.val.image ∧
      MarkedIsotopyRel M c.val.image c'.val.image := by
  classical
  obtain ⟨e,he⟩ := L.homeomorphism_at ⟨1,by norm_num⟩
  have hefinal : (e : S → S) = L.finalMap := funext he
  obtain ⟨c',hi,hs⟩ := M.actual_marked_homeomorph_circle_transport c.val e
    (fun x hx => (he x).trans (hfix _ x hx))
  refine ⟨⟨c',hs 3 3 c.property⟩,?_,L,hfix,?_⟩
  · simpa only [hefinal] using hi
  · simpa only [hefinal] using hi.symm
end CurveComplex.HyperellipticModel
