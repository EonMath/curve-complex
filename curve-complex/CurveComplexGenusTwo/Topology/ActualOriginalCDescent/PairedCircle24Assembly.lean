import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedMarkedCircleTransport
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedTransverseDescent
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedSimultaneousTransport
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedCountBinding
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedTransverseBinding
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedSurgeryFullOperation
import CurveComplexGenusTwo.Topology.IsotopyCurveTransport

namespace CurveComplex.HyperellipticModel
open Set Topology

private theorem paired_circle24_first_family_finish
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (c d : Circle24 M)
    (a0 a1 b0 b1 a0' a1' : EssentialCurve E)
    (H K : AmbientIsotopy E)
    (ha : a0.val.image ∪ a1.val.image = M.cover.projection ⁻¹' c.val.image)
    (hb : b0.val.image ∪ b1.val.image = M.cover.projection ⁻¹' d.val.image)
    (hAd : Disjoint a0.val.image a1.val.image)
    (hBd : Disjoint b0.val.image b1.val.image)
    (hDA : M.cover.deck '' a0.val.image = a1.val.image)
    (hDB : M.cover.deck '' b0.val.image = b1.val.image)
    (hH0 : H.finalMap '' a0.val.image = b0.val.image)
    (hH1 : H.finalMap '' a1.val.image = b1.val.image)
    (hap0 : Set.BijOn M.cover.projection a0.val.image c.val.image)
    (hap1 : Set.BijOn M.cover.projection a1.val.image c.val.image)
    (hbp0 : Set.BijOn M.cover.projection b0.val.image d.val.image)
    (hbp1 : Set.BijOn M.cover.projection b1.val.image d.val.image)
    (hAc0 : IsConnected a0.val.imageᶜ)
    (hAc1 : IsConnected a1.val.imageᶜ)
    (hBc0 : IsConnected b0.val.imageᶜ)
    (hBc1 : IsConnected b1.val.imageᶜ)
    (hK0 : a0'.val.image = K.finalMap '' a0.val.image)
    (hK1 : a1'.val.image = K.finalMap '' a1.val.image)
    (hKeq : ∀ t x, K.map (t, M.cover.deck x) =
      M.cover.deck (K.map (t, x)))
    (hKram : ∀ t x, M.cover.projection x ∈ M.cover.branch →
      K.map (t, x) = x)
    (ht00 : Transverse a0'.val b0.val)
    (ht01 : Transverse a0'.val b1.val)
    (ht10 : Transverse a1'.val b0.val)
    (ht11 : Transverse a1'.val b1.val)
    (hstrict :
      ((a0'.val.image ∪ a1'.val.image) ∩
        (b0.val.image ∪ b1.val.image)).ncard <
      ((a0.val.image ∪ a1.val.image) ∩
        (b0.val.image ∪ b1.val.image)).ncard) :
    ∃ c' : Circle24 M, ∃ H' : AmbientIsotopy E,
      MarkedIsotopyRel M c.val.image c'.val.image ∧
      Transverse c'.val.curve d.val.curve ∧
      a0'.val.image ∪ a1'.val.image =
        M.cover.projection ⁻¹' c'.val.image ∧
      Disjoint a0'.val.image a1'.val.image ∧
      M.cover.deck '' a0'.val.image = a1'.val.image ∧
      H'.finalMap '' a0'.val.image = b0.val.image ∧
      H'.finalMap '' a1'.val.image = b1.val.image ∧
      Set.BijOn M.cover.projection a0'.val.image c'.val.image ∧
      Set.BijOn M.cover.projection a1'.val.image c'.val.image ∧
      IsConnected a0'.val.imageᶜ ∧ IsConnected a1'.val.imageᶜ ∧
      ((a0'.val.image ∪ a1'.val.image) ∩
        (b0.val.image ∪ b1.val.image)).ncard <
      ((a0.val.image ∪ a1.val.image) ∩
        (b0.val.image ∪ b1.val.image)).ncard := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  obtain ⟨L, c', hcomm, hmarks, hc', hiso, hfull⟩ :=
    paired_branchfixed_circle24_endpoint_transport M c K hKeq hKram
  have ha' : a0'.val.image ∪ a1'.val.image =
      M.cover.projection ⁻¹' c'.val.image := by
    rw [hK0, hK1, ← Set.image_union, ha]
    exact hfull
  obtain ⟨e, he⟩ := K.homeomorphism_at ⟨1, by norm_num⟩
  have hinj : Function.Injective K.finalMap := by
    intro x y hxy
    apply e.injective
    change K.map (⟨1, by norm_num⟩, x) =
      K.map (⟨1, by norm_num⟩, y) at hxy
    simpa only [← he] using hxy
  have hAd' : Disjoint a0'.val.image a1'.val.image := by
    rw [hK0, hK1]
    exact Set.disjoint_image_of_injective hinj hAd
  have hDA' : M.cover.deck '' a0'.val.image = a1'.val.image := by
    rw [hK0, hK1, ← hDA, Set.image_image, Set.image_image]
    apply Set.image_congr
    intro x _
    exact (hKeq (⟨1, by norm_num⟩) x).symm
  obtain ⟨H', hH'0, hH'1⟩ :=
    (simultaneous_paired_relation_transport
      a0.val.image a1.val.image b0.val.image b1.val.image H K hH0 hH1).1
  have htbase : Transverse c'.val.curve d.val.curve :=
    transverse_paired_four_component_preimages_descends M.cover
      a0'.val a1'.val b0.val b1.val c'.val.curve d.val.curve
      ha' hb hAd' hBd c'.val.avoids_branch ht00 ht01 ht10 ht11
  refine ⟨c', H', hiso, htbase, ha', hAd', hDA', ?_, ?_, ?_, ?_, ?_, ?_, hstrict⟩
  · rw [hK0]
    exact hH'0
  · rw [hK1]
    exact hH'1
  · rw [hK0, hc']
    exact paired_component_projection_bijOn_transport M.cover K L hcomm
      a0.val.image c.val.image hap0
  · rw [hK1, hc']
    exact paired_component_projection_bijOn_transport M.cover K L hcomm
      a1.val.image c.val.image hap1
  · rw [hK0]
    exact paired_component_connected_complement_transport K a0.val.image hAc0
  · rw [hK1]
    exact paired_component_connected_complement_transport K a1.val.image hAc1

private theorem paired_circle24_second_family_finish
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (c d : Circle24 M)
    (a0 a1 b0 b1 b0' b1' : EssentialCurve E)
    (H K : AmbientIsotopy E)
    (ha : a0.val.image ∪ a1.val.image = M.cover.projection ⁻¹' c.val.image)
    (hb : b0.val.image ∪ b1.val.image = M.cover.projection ⁻¹' d.val.image)
    (hAd : Disjoint a0.val.image a1.val.image)
    (hBd : Disjoint b0.val.image b1.val.image)
    (hDA : M.cover.deck '' a0.val.image = a1.val.image)
    (hDB : M.cover.deck '' b0.val.image = b1.val.image)
    (hH0 : H.finalMap '' a0.val.image = b0.val.image)
    (hH1 : H.finalMap '' a1.val.image = b1.val.image)
    (hap0 : Set.BijOn M.cover.projection a0.val.image c.val.image)
    (hap1 : Set.BijOn M.cover.projection a1.val.image c.val.image)
    (hbp0 : Set.BijOn M.cover.projection b0.val.image d.val.image)
    (hbp1 : Set.BijOn M.cover.projection b1.val.image d.val.image)
    (hAc0 : IsConnected a0.val.imageᶜ)
    (hAc1 : IsConnected a1.val.imageᶜ)
    (hBc0 : IsConnected b0.val.imageᶜ)
    (hBc1 : IsConnected b1.val.imageᶜ)
    (hK0 : b0'.val.image = K.finalMap '' b0.val.image)
    (hK1 : b1'.val.image = K.finalMap '' b1.val.image)
    (hKeq : ∀ t x, K.map (t, M.cover.deck x) =
      M.cover.deck (K.map (t, x)))
    (hKram : ∀ t x, M.cover.projection x ∈ M.cover.branch →
      K.map (t, x) = x)
    (ht00 : Transverse a0.val b0'.val)
    (ht01 : Transverse a0.val b1'.val)
    (ht10 : Transverse a1.val b0'.val)
    (ht11 : Transverse a1.val b1'.val)
    (hstrict :
      ((a0.val.image ∪ a1.val.image) ∩
        (b0'.val.image ∪ b1'.val.image)).ncard <
      ((a0.val.image ∪ a1.val.image) ∩
        (b0.val.image ∪ b1.val.image)).ncard) :
    ∃ d' : Circle24 M, ∃ H' : AmbientIsotopy E,
      MarkedIsotopyRel M d.val.image d'.val.image ∧
      Transverse c.val.curve d'.val.curve ∧
      b0'.val.image ∪ b1'.val.image =
        M.cover.projection ⁻¹' d'.val.image ∧
      Disjoint b0'.val.image b1'.val.image ∧
      M.cover.deck '' b0'.val.image = b1'.val.image ∧
      H'.finalMap '' a0.val.image = b0'.val.image ∧
      H'.finalMap '' a1.val.image = b1'.val.image ∧
      Set.BijOn M.cover.projection b0'.val.image d'.val.image ∧
      Set.BijOn M.cover.projection b1'.val.image d'.val.image ∧
      IsConnected b0'.val.imageᶜ ∧ IsConnected b1'.val.imageᶜ ∧
      ((a0.val.image ∪ a1.val.image) ∩
        (b0'.val.image ∪ b1'.val.image)).ncard <
      ((a0.val.image ∪ a1.val.image) ∩
        (b0.val.image ∪ b1.val.image)).ncard := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  obtain ⟨L, d', hcomm, hmarks, hd', hiso, hfull⟩ :=
    paired_branchfixed_circle24_endpoint_transport M d K hKeq hKram
  have hb' : b0'.val.image ∪ b1'.val.image =
      M.cover.projection ⁻¹' d'.val.image := by
    rw [hK0, hK1, ← Set.image_union, hb]
    exact hfull
  obtain ⟨e, he⟩ := K.homeomorphism_at ⟨1, by norm_num⟩
  have hinj : Function.Injective K.finalMap := by
    intro x y hxy
    apply e.injective
    change K.map (⟨1, by norm_num⟩, x) =
      K.map (⟨1, by norm_num⟩, y) at hxy
    simpa only [← he] using hxy
  have hBd' : Disjoint b0'.val.image b1'.val.image := by
    rw [hK0, hK1]
    exact Set.disjoint_image_of_injective hinj hBd
  have hDB' : M.cover.deck '' b0'.val.image = b1'.val.image := by
    rw [hK0, hK1, ← hDB, Set.image_image, Set.image_image]
    apply Set.image_congr
    intro x _
    exact (hKeq (⟨1, by norm_num⟩) x).symm
  obtain ⟨H', hH'0, hH'1⟩ :=
    (simultaneous_paired_relation_transport
      a0.val.image a1.val.image b0.val.image b1.val.image H K hH0 hH1).2
  have htbase : Transverse c.val.curve d'.val.curve :=
    transverse_paired_four_component_preimages_descends M.cover
      a0.val a1.val b0'.val b1'.val c.val.curve d'.val.curve
      ha hb' hAd hBd' c.val.avoids_branch ht00 ht01 ht10 ht11
  refine ⟨d', H', hiso, htbase, hb', hBd', hDB', ?_, ?_, ?_, ?_, ?_, ?_, hstrict⟩
  · rw [hK0]
    exact hH'0
  · rw [hK1]
    exact hH'1
  · rw [hK0, hd']
    exact paired_component_projection_bijOn_transport M.cover K L hcomm
      b0.val.image d.val.image hbp0
  · rw [hK1, hd']
    exact paired_component_projection_bijOn_transport M.cover K L hcomm
      b1.val.image d.val.image hbp1
  · rw [hK0]
    exact paired_component_connected_complement_transport K b0.val.image hBc0
  · rw [hK1]
    exact paired_component_connected_complement_transport K b1.val.image hBc1

theorem actual_circle24_paired_globally_empty_disk_strict_step
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (c d : Circle24 M)
    (a0 a1 b0 b1 : EssentialCurve E) (H : AmbientIsotopy E)
    (ha : a0.val.image ∪ a1.val.image = M.cover.projection ⁻¹' c.val.image)
    (hb : b0.val.image ∪ b1.val.image = M.cover.projection ⁻¹' d.val.image)
    (hAd : Disjoint a0.val.image a1.val.image)
    (hBd : Disjoint b0.val.image b1.val.image)
    (hDA : M.cover.deck '' a0.val.image = a1.val.image)
    (hDB : M.cover.deck '' b0.val.image = b1.val.image)
    (hH0 : H.finalMap '' a0.val.image = b0.val.image)
    (hH1 : H.finalMap '' a1.val.image = b1.val.image)
    (hap0 : Set.BijOn M.cover.projection a0.val.image c.val.image)
    (hap1 : Set.BijOn M.cover.projection a1.val.image c.val.image)
    (hbp0 : Set.BijOn M.cover.projection b0.val.image d.val.image)
    (hbp1 : Set.BijOn M.cover.projection b1.val.image d.val.image)
    (hAc0 : IsConnected a0.val.imageᶜ)
    (hAc1 : IsConnected a1.val.imageᶜ)
    (hBc0 : IsConnected b0.val.imageᶜ)
    (hBc1 : IsConnected b1.val.imageᶜ)
    (ht00 : Transverse a0.val b0.val)
    (ht01 : Transverse a0.val b1.val)
    (ht10 : Transverse a1.val b0.val)
    (ht11 : Transverse a1.val b1.val)
    (D : LocalSurgery.TwoCurveDisk a0.val b0.val)
    (hGlobal : Disjoint D.openInterior
      ((a0.val.image ∪ a1.val.image) ∪
        (b0.val.image ∪ b1.val.image))) :
    ∃ c' d' : Circle24 M,
      MarkedIsotopyRel M c.val.image c'.val.image ∧
      MarkedIsotopyRel M d.val.image d'.val.image ∧
      Transverse c'.val.curve d'.val.curve ∧
      ∃ a0' a1' b0' b1' : EssentialCurve E, ∃ H' : AmbientIsotopy E,
        a0'.val.image ∪ a1'.val.image = M.cover.projection ⁻¹' c'.val.image ∧
        b0'.val.image ∪ b1'.val.image = M.cover.projection ⁻¹' d'.val.image ∧
        Disjoint a0'.val.image a1'.val.image ∧
        Disjoint b0'.val.image b1'.val.image ∧
        M.cover.deck '' a0'.val.image = a1'.val.image ∧
        M.cover.deck '' b0'.val.image = b1'.val.image ∧
        H'.finalMap '' a0'.val.image = b0'.val.image ∧
        H'.finalMap '' a1'.val.image = b1'.val.image ∧
        Set.BijOn M.cover.projection a0'.val.image c'.val.image ∧
        Set.BijOn M.cover.projection a1'.val.image c'.val.image ∧
        Set.BijOn M.cover.projection b0'.val.image d'.val.image ∧
        Set.BijOn M.cover.projection b1'.val.image d'.val.image ∧
        IsConnected a0'.val.imageᶜ ∧ IsConnected a1'.val.imageᶜ ∧
        IsConnected b0'.val.imageᶜ ∧ IsConnected b1'.val.imageᶜ ∧
        Transverse a0'.val b0'.val ∧ Transverse a0'.val b1'.val ∧
        Transverse a1'.val b0'.val ∧ Transverse a1'.val b1'.val ∧
        ((a0'.val.image ∪ a1'.val.image) ∩
          (b0'.val.image ∪ b1'.val.image)).ncard <
        ((a0.val.image ∪ a1.val.image) ∩
          (b0.val.image ∪ b1.val.image)).ncard := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  let r : Bool × Fin 2 → EssentialCurve E :=
    fun p => if p.1 then (![b0, b1] p.2) else (![a0, a1] p.2)
  obtain ⟨V, J, K, k, r', _, _, _, _, hchoice, hfixed, himage,
    hfix, hpartner, htrans, hdrop, hK, hKeq, hKV, _, hKram⟩ :=
    paired_local_four_component_weighted_motion M a0 a1 b0 b1
      hAd hBd hDA hDB ht00 ht01 ht10 ht11 D hGlobal
  have hImages := paired_supported_motion_component_images M.cover
    a0 a1 b0 b1 hDA hDB V J K hfix hpartner hK hKV
  have ht : ∀ i j : Fin 2,
      Transverse (![a0, a1] i).val (![b0, b1] j).val := by
    intro i j
    fin_cases i
    · fin_cases j
      · exact ht00
      · exact ht01
    · fin_cases j
      · exact ht10
      · exact ht11
  have hmarkRefl (C : Set S) : MarkedIsotopyRel M C C := by
    refine ⟨AmbientIsotopy.identity S, ?_, ?_⟩
    · intro t x hx
      rfl
    · exact Set.image_id C
  rcases hchoice with hk | hk
  · subst k
    obtain ⟨a0', ha0', _⟩ := position_essential_curve_of_isotopy K a0
    obtain ⟨a1', ha1', _⟩ := position_essential_curve_of_isotopy K a1
    have hfixedA : ∀ p, p ≠ (false, 0) → r' p = r p := hfixed
    have himageA : J.finalMap '' a0.val.image = (r' (false, 0)).val.image := by
      simpa [r] using himage
    have htransA := paired_first_side_weighted_transverse_bind M.cover
      a0 a1 b0 b1 a0' a1' hDB r' hfixedA
      (ha0'.trans (hImages.1.trans himageA))
      (ha1'.trans (hImages.2.1.trans (congrArg (M.cover.deck '' ·) himageA)))
      htrans
    have hstrictA := paired_first_side_weighted_data_strict_count M
      a0 a1 b0 b1 hAd hBd hDA hDB ht J K r' hfixedA himageA
      (fun t x hx => hpartner t x (Or.inl hx))
      hImages.1 hImages.2.1 htrans (by simpa only [r] using hdrop)
    have hstrictA' :
        ((a0'.val.image ∪ a1'.val.image) ∩
          (b0.val.image ∪ b1.val.image)).ncard <
        ((a0.val.image ∪ a1.val.image) ∩
          (b0.val.image ∪ b1.val.image)).ncard := by
      simpa only [ha0', ha1'] using hstrictA
    obtain ⟨c', H', hcIso, htbase, ha', hAd', hDA', hH'0, hH'1,
      hap0', hap1', hAc0', hAc1', hstrict⟩ :=
      paired_circle24_first_family_finish M c d a0 a1 b0 b1 a0' a1'
        H K ha hb hAd hBd hDA hDB hH0 hH1 hap0 hap1 hbp0 hbp1
        hAc0 hAc1 hBc0 hBc1 ha0' ha1' hKeq hKram
        htransA.1 htransA.2.1 htransA.2.2.1 htransA.2.2.2 hstrictA'
    exact ⟨c', d, hcIso, hmarkRefl _, htbase,
      a0', a1', b0, b1, H', ha', hb, hAd', hBd, hDA', hDB,
      hH'0, hH'1, hap0', hap1', hbp0, hbp1,
      hAc0', hAc1', hBc0, hBc1,
      htransA.1, htransA.2.1, htransA.2.2.1, htransA.2.2.2,
      hstrict⟩
  · subst k
    obtain ⟨b0', hb0', _⟩ := position_essential_curve_of_isotopy K b0
    obtain ⟨b1', hb1', _⟩ := position_essential_curve_of_isotopy K b1
    have hfixedB : ∀ p, p ≠ (true, 0) → r' p = r p := hfixed
    have himageB : J.finalMap '' b0.val.image = (r' (true, 0)).val.image := by
      simpa [r] using himage
    have htransB := paired_second_side_weighted_transverse_bind M.cover
      a0 a1 b0 b1 b0' b1' hDA r' hfixedB
      (hb0'.trans (hImages.2.2.1.trans himageB))
      (hb1'.trans (hImages.2.2.2.trans (congrArg (M.cover.deck '' ·) himageB)))
      htrans
    have hstrictB := paired_second_side_weighted_data_strict_count M
      a0 a1 b0 b1 hAd hBd hDA hDB ht J K r' hfixedB himageB
      (fun t x hx => hpartner t x (Or.inr hx))
      hImages.2.2.1 hImages.2.2.2 htrans (by simpa only [r] using hdrop)
    have hstrictB' :
        ((a0.val.image ∪ a1.val.image) ∩
          (b0'.val.image ∪ b1'.val.image)).ncard <
        ((a0.val.image ∪ a1.val.image) ∩
          (b0.val.image ∪ b1.val.image)).ncard := by
      simpa only [hb0', hb1'] using hstrictB
    obtain ⟨d', H', hdIso, htbase, hb', hBd', hDB', hH'0, hH'1,
      hbp0', hbp1', hBc0', hBc1', hstrict⟩ :=
      paired_circle24_second_family_finish M c d a0 a1 b0 b1 b0' b1'
        H K ha hb hAd hBd hDA hDB hH0 hH1 hap0 hap1 hbp0 hbp1
        hAc0 hAc1 hBc0 hBc1 hb0' hb1' hKeq hKram
        htransB.1 htransB.2.1 htransB.2.2.1 htransB.2.2.2 hstrictB'
    exact ⟨c, d', hmarkRefl _, hdIso, htbase,
      a0, a1, b0', b1', H', ha, hb', hAd, hBd', hDA, hDB',
      hH'0, hH'1, hap0, hap1, hbp0', hbp1',
      hAc0, hAc1, hBc0', hBc1',
      htransB.1, htransB.2.1, htransB.2.2.1, htransB.2.2.2,
      hstrict⟩

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_circle24_paired_multicurve_strict_step
    (M : HyperellipticModel E S) (c d : Circle24 M)
    (a0 a1 b0 b1 : EssentialCurve E) (H : AmbientIsotopy E)
    (ha : a0.val.image ∪ a1.val.image = M.cover.projection ⁻¹' c.val.image)
    (hb : b0.val.image ∪ b1.val.image = M.cover.projection ⁻¹' d.val.image)
    (hAd : Disjoint a0.val.image a1.val.image)
    (hBd : Disjoint b0.val.image b1.val.image)
    (hDA : M.cover.deck '' a0.val.image = a1.val.image)
    (hDB : M.cover.deck '' b0.val.image = b1.val.image)
    (hH0 : H.finalMap '' a0.val.image = b0.val.image)
    (hH1 : H.finalMap '' a1.val.image = b1.val.image)
    (hap0 : Set.BijOn M.cover.projection a0.val.image c.val.image)
    (hap1 : Set.BijOn M.cover.projection a1.val.image c.val.image)
    (hbp0 : Set.BijOn M.cover.projection b0.val.image d.val.image)
    (hbp1 : Set.BijOn M.cover.projection b1.val.image d.val.image)
    (hAc0 : IsConnected a0.val.imageᶜ)
    (hAc1 : IsConnected a1.val.imageᶜ)
    (hBc0 : IsConnected b0.val.imageᶜ)
    (hBc1 : IsConnected b1.val.imageᶜ)
    (htbase : Transverse c.val.curve d.val.curve)
    (ht00 : Transverse a0.val b0.val)
    (ht01 : Transverse a0.val b1.val)
    (ht10 : Transverse a1.val b0.val)
    (ht11 : Transverse a1.val b1.val)
    (hDisk : Nonempty (LocalSurgery.TwoCurveDisk a0.val b0.val) ∨
      Nonempty (LocalSurgery.TwoCurveDisk a0.val b1.val) ∨
      Nonempty (LocalSurgery.TwoCurveDisk a1.val b0.val) ∨
      Nonempty (LocalSurgery.TwoCurveDisk a1.val b1.val)) :
    ∃ c' d' : Circle24 M,
      MarkedIsotopyRel M c.val.image c'.val.image ∧
      MarkedIsotopyRel M d.val.image d'.val.image ∧
      Transverse c'.val.curve d'.val.curve ∧
      ∃ a0' a1' b0' b1' : EssentialCurve E, ∃ H' : AmbientIsotopy E,
        a0'.val.image ∪ a1'.val.image = M.cover.projection ⁻¹' c'.val.image ∧
        b0'.val.image ∪ b1'.val.image = M.cover.projection ⁻¹' d'.val.image ∧
        Disjoint a0'.val.image a1'.val.image ∧
        Disjoint b0'.val.image b1'.val.image ∧
        M.cover.deck '' a0'.val.image = a1'.val.image ∧
        M.cover.deck '' b0'.val.image = b1'.val.image ∧
        H'.finalMap '' a0'.val.image = b0'.val.image ∧
        H'.finalMap '' a1'.val.image = b1'.val.image ∧
        Set.BijOn M.cover.projection a0'.val.image c'.val.image ∧
        Set.BijOn M.cover.projection a1'.val.image c'.val.image ∧
        Set.BijOn M.cover.projection b0'.val.image d'.val.image ∧
        Set.BijOn M.cover.projection b1'.val.image d'.val.image ∧
        IsConnected a0'.val.imageᶜ ∧ IsConnected a1'.val.imageᶜ ∧
        IsConnected b0'.val.imageᶜ ∧ IsConnected b1'.val.imageᶜ ∧
        Transverse a0'.val b0'.val ∧ Transverse a0'.val b1'.val ∧
        Transverse a1'.val b0'.val ∧ Transverse a1'.val b1'.val ∧
        ((a0'.val.image ∪ a1'.val.image) ∩
          (b0'.val.image ∪ b1'.val.image)).ncard <
        ((a0.val.image ∪ a1.val.image) ∩
          (b0.val.image ∪ b1.val.image)).ncard := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have ht : ∀ i j, Transverse (![a0, a1] i).val (![b0, b1] j).val := by
    intro i j
    fin_cases i
    · fin_cases j
      · exact ht00
      · exact ht01
    · fin_cases j
      · exact ht10
      · exact ht11
  obtain ⟨i0, j0, ⟨D0⟩⟩ :
      ∃ i0 j0 : Fin 2,
        Nonempty (LocalSurgery.TwoCurveDisk (![a0, a1] i0).val
          (![b0, b1] j0).val) := by
    rcases hDisk with h00 | h01 | h10 | h11
    · exact ⟨0, 0, h00⟩
    · exact ⟨0, 1, h01⟩
    · exact ⟨1, 0, h10⟩
    · exact ⟨1, 1, h11⟩
  obtain ⟨i, j, D, hGlobal⟩ :=
    LocalSurgery.four_component_disk_has_globally_empty_interior
      (![a0, a1]) (![b0, b1]) hAd hBd ht i0 j0 D0
  obtain ⟨K, hKeq, hKram, hcase⟩ :=
    paired_any_globally_empty_disk_full_four_component_operation M
      a0 a1 b0 b1 hAd hBd hDA hDB ht00 ht01 ht10 ht11 i j D hGlobal
  have hmarkRefl (C : Set S) : MarkedIsotopyRel M C C := by
    refine ⟨AmbientIsotopy.identity S, ?_, ?_⟩
    · intro t x hx
      rfl
    · exact Set.image_id C
  rcases hcase with hA | hB
  · obtain ⟨a0', a1', ha0', ha1', ht00', ht01', ht10', ht11', hstrictA⟩ := hA
    obtain ⟨c', H', hcIso, htbase', ha', hAd', hDA', hH'0, hH'1,
      hap0', hap1', hAc0', hAc1', hstrict⟩ :=
      paired_circle24_first_family_finish M c d a0 a1 b0 b1 a0' a1'
        H K ha hb hAd hBd hDA hDB hH0 hH1 hap0 hap1 hbp0 hbp1
        hAc0 hAc1 hBc0 hBc1 ha0' ha1' hKeq hKram
        ht00' ht01' ht10' ht11' hstrictA
    exact ⟨c', d, hcIso, hmarkRefl _, htbase',
      a0', a1', b0, b1, H', ha', hb, hAd', hBd, hDA', hDB,
      hH'0, hH'1, hap0', hap1', hbp0, hbp1,
      hAc0', hAc1', hBc0, hBc1, ht00', ht01', ht10', ht11', hstrict⟩
  · obtain ⟨b0', b1', hb0', hb1', ht00', ht01', ht10', ht11', hstrictB⟩ := hB
    obtain ⟨d', H', hdIso, htbase', hb', hBd', hDB', hH'0, hH'1,
      hbp0', hbp1', hBc0', hBc1', hstrict⟩ :=
      paired_circle24_second_family_finish M c d a0 a1 b0 b1 b0' b1'
        H K ha hb hAd hBd hDA hDB hH0 hH1 hap0 hap1 hbp0 hbp1
        hAc0 hAc1 hBc0 hBc1 hb0' hb1' hKeq hKram
        ht00' ht01' ht10' ht11' hstrictB
    exact ⟨c, d', hmarkRefl _, hdIso, htbase',
      a0, a1, b0', b1', H', ha, hb', hAd, hBd', hDA, hDB',
      hH'0, hH'1, hap0, hap1, hbp0', hbp1',
      hAc0, hAc1, hBc0', hBc1', ht00', ht01', ht10', ht11', hstrict⟩

end CurveComplex.HyperellipticModel
