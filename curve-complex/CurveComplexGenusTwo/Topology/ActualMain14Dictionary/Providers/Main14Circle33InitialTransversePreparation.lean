import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14Circle33FiniteBigonFreeEndpoint
import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14ActualMarkedCircleTransport
import CurveComplexGenusTwo.Dictionary.CircleVertexAPI
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14MarkedCircleTransverseExtension
import CurveComplexGenusTwo.Dictionary.ActualDictionaryEssential

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
open scoped Manifold ContDiff
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 8000000

/-- Original arbitrary 3|3 circles admit actual marked-isotopic transverse
representatives, with the first circle unchanged. No transverse preparation,
curve essentialness on the whole sphere, or support certificate is supplied. -/
theorem circle33_actual_initial_transverse_preparation
    (M : HyperellipticModel E S) (c d : Circle33 M) :
    ∃ d' : Circle33 M,
      MarkedIsotopyRel M d.val.image d'.val.image ∧
      Transverse c.val.curve d'.val.curve ∧
      Transverse (M.circle33_essential_preimage c).val
        (M.circle33_essential_preimage d').val := by
  classical
  let A := M.actualSphereSmoothAtlas
  letI : ChartedSpace Plane S := A.charts
  letI : IsManifold (𝓡 2) ∞ S := A.manifold
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by
      rw [← Module.finrank_eq_rank]
      simp) (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num))
  letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI : ClosedSurface S := {}
  obtain ⟨H,d₀,himage,hfix,ht⟩ := M.actual_marked_two_circle_transverse_extension c.val d.val
  obtain ⟨d',hd',hdiso⟩ := M.actual_marked_isotopy_circle33_transport d H hfix
  have hdi : d'.val.curve.image = d₀.image := hd'.trans himage.symm
  have htbase := transverse_of_curve_images_eq c.val.curve d'.val.curve c.val.curve d₀ rfl hdi ht
  have htup := M.cover.transverse_full_preimages_lifts
    (M.circle33_essential_preimage c).val (M.circle33_essential_preimage d').val
    c.val.curve d'.val.curve
    (M.circle33_essential_preimage_image c) (M.circle33_essential_preimage_image d')
    c.val.avoids_branch htbase
  exact ⟨d',hdiso,htbase,htup⟩

/-- Apply actual marked transverse preparation and actual finite elimination
to the original unrestricted circle33 descent input. The endpoint has no
TwoCurveDisk, keeps the original marked-circle relations, and retains the
arbitrary original upstairs isotopy; no new endpoint premise is introduced. -/
theorem circle33_original_isotopy_actual_disk_free_reduction
    (M : HyperellipticModel E S) (c d : Circle33 M)
    (hiso : AmbientIsotopy.Rel (M.cover.projection ⁻¹' c.val.image)
      (M.cover.projection ⁻¹' d.val.image)) :
    ∃ a' b' : EssentialCurve E, ∃ c' d' : Circle33 M,
      a'.val.image = M.cover.projection ⁻¹' c'.val.image ∧
      b'.val.image = M.cover.projection ⁻¹' d'.val.image ∧
      MarkedIsotopyRel M c.val.image c'.val.image ∧
      MarkedIsotopyRel M d.val.image d'.val.image ∧
      AmbientIsotopy.Rel a'.val.image b'.val.image ∧
      Transverse a'.val b'.val ∧ Transverse c'.val.curve d'.val.curve ∧
      IsEmpty (LocalSurgery.TwoCurveDisk a'.val b'.val) := by
  obtain ⟨d₀,hdiso,htbase,htup⟩ := M.circle33_actual_initial_transverse_preparation c d
  have hiso₀ : AmbientIsotopy.Rel (M.circle33_essential_preimage c).val.image
      (M.circle33_essential_preimage d₀).val.image := by
    rw [M.circle33_essential_preimage_image,M.circle33_essential_preimage_image]
    exact ambientIsotopy_equivalence.trans hiso (M.marked_isotopy_preimage hdiso)
  obtain ⟨a',b',c',d',ha',hb',hci,hdi,hiso',ht',htbase',hfree⟩ :=
    M.circle33_isotopic_actual_finite_bigon_free_endpoint
      (M.circle33_essential_preimage c) (M.circle33_essential_preimage d₀) c d₀
      htup (M.circle33_essential_preimage_image c) (M.circle33_essential_preimage_image d₀)
      htbase hiso₀
  exact ⟨a',b',c',d',ha',hb',hci,(markedIsotopy_equivalence M).trans hdiso hdi,
    hiso',ht',htbase',hfree⟩
end CurveComplex.HyperellipticModel
