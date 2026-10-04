import CurveComplexGenusTwo.Hyperbolic.OriginalG3Annulus.ActualDisjointHomotopicAnnulus
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualInducedClosedHyperbolicMetricProof
import CurveComplexGenusTwo.Dictionary.ActualCircle24Components

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]

theorem actual_model_ambient_isotopic_essential_pair_collared_annulus
    (M : HyperellipticModel E S) (a b : Curve E)
    (ha : Essential a) (hb : Essential b)
    (hrel : AmbientIsotopy.Rel a.image b.image)
    (hdis : Disjoint a.image b.image) :
    ∃ B : Circle × Interval → E, Topology.IsEmbedding B ∧
      Set.range (fun z : Circle => B (z,⟨1/3,by norm_num⟩)) = a.image ∧
      Set.range (fun z : Circle => B (z,⟨2/3,by norm_num⟩)) = b.image ∧
      IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
  obtain ⟨H,hH⟩ := hrel
  obtain ⟨e,he⟩ := H.homeomorphism_at 1
  let b' : Curve E := ⟨e ∘ a.map,e.isEmbedding.comp a.embedded⟩
  have hb'image : b'.image = b.image := by
    change Set.range (e ∘ a.map) = b.image
    rw [Set.range_comp]
    change (e : E → E) '' a.image = b.image
    have hfinal : H.finalMap = e := funext (fun x => (he x).symm)
    rw [← hfinal]
    exact hH
  have hb' : Essential b' := by
    intro hdisc
    apply hb
    obtain ⟨f,hf,hboundary⟩ := hdisc
    exact ⟨f,hf,hboundary.trans hb'image⟩
  have hhom : CurveComplex.Hyperbolic.FreeHomotopic
      ⟨a.map,a.embedded.continuous⟩
      ⟨b'.map,b'.embedded.continuous⟩ := by
    let F : C(Circle × Interval,E) :=
      ⟨fun p => H.map (p.2,a.map p.1),
        H.map.continuous.comp
          (continuous_snd.prodMk (a.embedded.continuous.comp continuous_fst))⟩
    refine ⟨F,?_,?_⟩
    · intro z
      exact H.at_zero (a.map z)
    · intro z
      change H.finalMap (a.map z) = e (a.map z)
      exact (he _).symm
  obtain ⟨atlas,_,Hmetric,_,_,_,_,_,_,_,_⟩ :=
    CurveComplex.Hyperbolic.actual_induced_closed_hyperbolic_metric M
  let : ChartedSpace Schoenflies.Plane E := atlas
  obtain ⟨B,hB,hBa,hBb,hBopen⟩ :=
    CurveComplex.Hyperbolic.actual_disjoint_essential_homotopic_curves_have_collared_annulus
      Hmetric a b' ha hb' hhom (hb'image ▸ hdis)
  exact ⟨B,hB,hBa,hBb.trans hb'image,hBopen⟩

end CurveComplex.HyperellipticModel
