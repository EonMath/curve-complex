import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14FullPreimageTransversalityDescent
import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14ActualMarkedCircleTransport

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
set_option maxHeartbeats 4000000
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]

/-- The actual strict operation closes on the literal 3|3 full-preimage input
objects: all downstairs marking and transversality hypotheses for another step
are derived, as are both downstairs isotopies and the strict upstairs decrease. -/
theorem circle33_actual_strict_bigon_iteration_step
    (M : HyperellipticModel E S) (a b : EssentialCurve E)
    (ht : Transverse a.val b.val) (B : LocalSurgery.TwoCurveDisk a.val b.val)
    (c d : Circle33 M)
    (ha : a.val.image = M.cover.projection ⁻¹' c.val.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.val.image)
    (htbase : Transverse c.val.curve d.val.curve)
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
    ∃ a' b' : EssentialCurve E, ∃ c' d' : Circle33 M,
      a'.val.image = M.cover.projection ⁻¹' c'.val.image ∧
      b'.val.image = M.cover.projection ⁻¹' d'.val.image ∧
      Quotient.mk (essentialCurveSetoid E) a' = Quotient.mk (essentialCurveSetoid E) a ∧
      Quotient.mk (essentialCurveSetoid E) b' = Quotient.mk (essentialCurveSetoid E) b ∧
      MarkedIsotopyRel M c.val.image c'.val.image ∧
      MarkedIsotopyRel M d.val.image d'.val.image ∧
      Transverse a'.val b'.val ∧ Transverse c'.val.curve d'.val.curve ∧
      (a'.val.image ∩ b'.val.image).ncard < (a.val.image ∩ b.val.image).ncard := by
  classical
  obtain ⟨a',b',L,hchoice,hca,hcb,ht',hdrop,hfix⟩ :=
    M.innermost_full_preimage_actual_marked_strict_bigon_operation a b ht B c.val d.val ha hb htbase hempty
  rcases hchoice with ⟨hia,hb'⟩ | ⟨hib,ha'⟩
  · subst b'
    obtain ⟨c',hc',hciso⟩ := M.actual_marked_isotopy_circle33_transport c L hfix
    have hia' : a'.val.image = M.cover.projection ⁻¹' c'.val.image := by rw [hc']; exact hia
    have htbase' := M.cover.transverse_full_preimages_descends a'.val b.val c'.val.curve d.val.curve
      hia' hb c'.val.avoids_branch ht'
    exact ⟨a',b,c',d,hia',hb,hca,hcb,hciso,(markedIsotopy_equivalence M).refl _,ht',htbase',hdrop⟩
  · subst a'
    obtain ⟨d',hd',hdiso⟩ := M.actual_marked_isotopy_circle33_transport d L hfix
    have hib' : b'.val.image = M.cover.projection ⁻¹' d'.val.image := by rw [hd']; exact hib
    have htbase' := M.cover.transverse_full_preimages_descends a.val b'.val c.val.curve d'.val.curve
      ha hib' c.val.avoids_branch ht'
    exact ⟨a,b',c,d',ha,hib',hca,hcb,(markedIsotopy_equivalence M).refl _,hdiso,ht',htbase',hdrop⟩
end CurveComplex.HyperellipticModel
