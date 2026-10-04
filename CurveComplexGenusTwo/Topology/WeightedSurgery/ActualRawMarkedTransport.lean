import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualCrossingSlideSystem

namespace CurveComplex.HyperellipticModel.ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

theorem markedArc_eq_of_map_eq (M : HyperellipticModel E S) (a b : MarkedArc M)
    (h : a.map = b.map) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem markedArc_transport_inverse (M : HyperellipticModel E S)
    (a : MarkedArc M) (h : S ≃ₜ S) (hm : ∀ z, z ∈ M.cover.branch → h z = z)
    (hi : ∀ z, z ∈ M.cover.branch → h.symm z = z) :
    (a.transport h hm).transport h.symm hi = a := by
  apply markedArc_eq_of_map_eq
  funext r
  exact h.symm_apply_apply (a.map r)

theorem essentialMarkedArc_transport_iff (M : HyperellipticModel E S)
    (a : MarkedArc M) (h : S ≃ₜ S) (hm : ∀ z, z ∈ M.cover.branch → h z = z) :
    IsEssentialMarkedArc M (a.transport h hm) ↔ IsEssentialMarkedArc M a := by
  have hi : ∀ z, z ∈ M.cover.branch → h.symm z = z := by
    intro z hz
    apply h.injective
    rw [h.apply_symm_apply,hm z hz]
  constructor
  · intro he
    have ht := essential_transport (⟨a.transport h hm,he⟩ : EssentialMarkedArc M) h.symm hi
    rw [markedArc_transport_inverse M a h hm hi] at ht
    exact ht
  · intro he
    exact essential_transport (⟨a,he⟩ : EssentialMarkedArc M) h hm

def timeRawTransport (M : HyperellipticModel E S) (G : AmbientIsotopy S)
    (hm : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p)
    (t : Interval) (a : MarkedArc M) : MarkedArc M :=
  a.transport (timeHomeomorph G t) (fun p hp => (timeHomeomorph_apply G t p).trans (hm t p hp))

theorem timeRawTransport_map (M : HyperellipticModel E S) (G : AmbientIsotopy S)
    (hm : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p)
    (t : Interval) (a : MarkedArc M) (r : Interval) :
    (timeRawTransport M G hm t a).map r = G.map (t,a.map r) :=
  timeHomeomorph_apply G t _

end
end CurveComplex.HyperellipticModel.ArcSurgery
