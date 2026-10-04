import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14TransverseImageEquality
import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14ActualUpstairsWeightedBigon
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14PairedSupportedTransversality
import CurveComplexGenusTwo.Topology.IsotopyCurveTransport

namespace CurveComplex
open Set Topology Schoenflies
set_option maxHeartbeats 4000000

namespace HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Plane E]

/-- The constructed deck-equivariant paired ambient isotopy actually reduces
crossings and preserves essentialness and both original vertex classes. -/
theorem paired_isotopy_actual_strict_drop
    (M : HyperellipticModel E S) (a b : EssentialCurve E)
    (ht : Transverse a.val b.val)
    (hA : M.cover.deck '' a.val.image = a.val.image)
    (hB : M.cover.deck '' b.val.image = b.val.image)
    (V : Set E) (hsep : Disjoint (closure V) (M.cover.deck '' closure V))
    (H K : AmbientIsotopy E) (d : EssentialCurve E)
    (himage : H.finalMap '' a.val.image = d.val.image)
    (hfix : ∀ t x, x ∉ V → H.map (t,x) = x)
    (htH : Transverse d.val b.val)
    (hdrop : (d.val.image ∩ b.val.image).ncard < (a.val.image ∩ b.val.image).ncard)
    (hK : ∀ t x, K.map (t,x) = M.cover.deck (H.map (t,M.cover.deck (H.map (t,x))))) :
    ∃ a' : EssentialCurve E,
      K.finalMap '' a.val.image = a'.val.image ∧
      Quotient.mk (essentialCurveSetoid E) a' = Quotient.mk (essentialCurveSetoid E) a ∧
      Transverse a'.val b.val ∧
      (a'.val.image ∩ b.val.image).ncard < (a.val.image ∩ b.val.image).ncard := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  obtain ⟨e,he⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hefinal : (e : E → E) = H.finalMap := funext he
  have hei : (LocalSurgery.homeomorphCurve e a.val).image = d.val.image := by
    change Set.range (e ∘ a.val.map) = d.val.image
    rw [Set.range_comp,hefinal]
    exact himage
  have htH' := transverse_of_curve_images_eq
    (LocalSurgery.homeomorphCurve e a.val) b.val d.val b.val hei rfl htH
  have hd : ((LocalSurgery.homeomorphCurve e a.val).image ∩ b.val.image).ncard <
      (a.val.image ∩ b.val.image).ncard := by rw [hei]; exact hdrop
  have hpair := paired_supported_homeomorph_transverse_drop M.cover.deck e M.cover.deck_involution
    V hsep (fun x hx => by rw [hefinal]; exact hfix _ x hx) a.val b.val hA hB ht htH' hd
  obtain ⟨a',hi,hclass⟩ := position_essential_curve_of_isotopy K a
  have hfin : (e.trans ((M.cover.deck.trans e).trans M.cover.deck) : E → E) = K.finalMap := by
    funext x
    change M.cover.deck (e (M.cover.deck (e x))) = K.finalMap x
    rw [hefinal]
    exact (hK _ x).symm
  have hpi : (LocalSurgery.homeomorphCurve (e.trans ((M.cover.deck.trans e).trans M.cover.deck)) a.val).image = a'.val.image := by
    change Set.range ((e.trans ((M.cover.deck.trans e).trans M.cover.deck)) ∘ a.val.map) = _
    rw [Set.range_comp,hfin]
    exact hi.symm
  refine ⟨a',hi.symm,hclass,?_,?_⟩
  · exact transverse_of_curve_images_eq a'.val b.val _ b.val hpi.symm rfl hpair.1
  · simpa only [hpi] using hpair.2

/-- An actual empty upstairs full-preimage bigon produces an actual
mark-fixing, deck-equivariant ambient operation with a genuine strict decrease.
All support, replacement, essentialness and crossing data are derived from
that bigon and the original cover; none is an extra source premise. -/
theorem innermost_full_preimage_actual_equivariant_strict_bigon_operation
    (M : HyperellipticModel E S) (a b : EssentialCurve E)
    (ht : Transverse a.val b.val) (B : LocalSurgery.TwoCurveDisk a.val b.val)
    (c d : PuncturedCircle M)
    (ha : a.val.image = M.cover.projection ⁻¹' c.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.image)
    (htbase : Transverse c.curve d.curve)
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
    ∃ a' b' : EssentialCurve E, ∃ K : AmbientIsotopy E,
      ((K.finalMap '' a.val.image = a'.val.image ∧ b' = b) ∨
        (K.finalMap '' b.val.image = b'.val.image ∧ a' = a)) ∧
      Quotient.mk (essentialCurveSetoid E) a' = Quotient.mk (essentialCurveSetoid E) a ∧
      Quotient.mk (essentialCurveSetoid E) b' = Quotient.mk (essentialCurveSetoid E) b ∧
      Transverse a'.val b'.val ∧
      (a'.val.image ∩ b'.val.image).ncard < (a.val.image ∩ b.val.image).ncard ∧
      (∀ t x, K.map (t,M.cover.deck x) = M.cover.deck (K.map (t,x))) ∧
      (∀ t x, M.cover.projection x ∈ M.cover.branch → K.map (t,x) = x) := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have hinv (A : Set S) : M.cover.deck '' (M.cover.projection ⁻¹' A) = M.cover.projection ⁻¹' A := by
    ext x; constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [Set.mem_preimage,M.cover.projection_deck] using hy
    · intro hx
      refine ⟨M.cover.deck x,?_,M.cover.deck_involution x⟩
      simpa only [Set.mem_preimage,M.cover.projection_deck] using hx
  have hA : M.cover.deck '' a.val.image = a.val.image := by rw [ha]; exact hinv _
  have hB : M.cover.deck '' b.val.image = b.val.image := by rw [hb]; exact hinv _
  obtain ⟨V,H,a₀,b₀,K,hV,hBV,hsep,hchoice,hfix,hca,hcb,htH,hdrop,hK,hKeq,hKram⟩ :=
    M.innermost_full_preimage_actual_weighted_bigon_operation a b ht B c d ha hb htbase hempty
  rcases hchoice with ⟨hi,hb₀⟩ | ⟨hi,ha₀⟩
  · subst b₀
    obtain ⟨a',hi',hclass,ht',hd'⟩ :=
      M.paired_isotopy_actual_strict_drop a b ht hA hB V hsep H K a₀ hi hfix htH hdrop hK
    exact ⟨a',b,K,Or.inl ⟨hi',rfl⟩,hclass,rfl,ht',hd',hKeq,hKram⟩
  · subst a₀
    have hdrop' : (b₀.val.image ∩ a.val.image).ncard < (b.val.image ∩ a.val.image).ncard := by
      simpa only [Set.inter_comm] using hdrop
    obtain ⟨b',hi',hclass,ht',hd'⟩ :=
      M.paired_isotopy_actual_strict_drop b a (transverse_symm_of_chart ht) hB hA V hsep H K b₀
        hi hfix (transverse_symm_of_chart htH) hdrop' hK
    refine ⟨a,b',K,Or.inr ⟨hi',rfl⟩,rfl,hclass,transverse_symm_of_chart ht',?_,hKeq,hKram⟩
    simpa only [Set.inter_comm] using hd'
end HyperellipticModel
end CurveComplex
