import ActualRawEndpointSeparatedEntirePairClearedMarkedDisk_VERIFIED
import ActualRawCommonBaseLoopsEntirePairClearedMarkedDisk_VERIFIED
import ActualRawUnequalEndpointNonloopsEntirePairClearedMarkedDisk_VERIFIED
import ActualRawOriginalPairOrientationPremises_VERIFIED
import ActualRawPhysicalEndpointCaseSplit_VERIFIED
import ActualRawAlignedNonloopOriginalSubpathsPuncturedHomotopic_RECOVERY_CANDIDATE
import ActualRawMixedLoopMarkedCornerDecoderCandidate
/- A static naming bridge for the pinned numeric private namespace; it only emits an identifier. -/
open Lean in
macro:max "rawFrozenProof%" mod:str decl:str : term => do
  let mut n := Name.mkStr Name.anonymous "_private"
  for c in mod.getString.splitOn "." do
    n := Name.mkStr n c
  n := Name.mkNum n 0
  for c in decl.getString.splitOn "." do
    n := Name.mkStr n c
  `(term| @$(mkIdent n):ident)


namespace CurveComplex.HyperellipticModel
open Set Topology ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance (M : HyperellipticModel E S) : DecidableEq (EssentialArcClass M) := Classical.decEq _
private noncomputable def actualRawEndpointSeparatedProducesEntirePairClearedMarkedDisk := rawFrozenProof% "ActualRawEndpointSeparatedEntirePairClearedMarkedDisk_VERIFIED" "CurveComplex.HyperellipticModel.actualRawEndpointSeparatedProducesEntirePairClearedMarkedDisk"
private noncomputable def actualRawCommonBaseLoopsProduceEntirePairClearedMarkedDisk := rawFrozenProof% "ActualRawCommonBaseLoopsEntirePairClearedMarkedDisk_VERIFIED" "CurveComplex.HyperellipticModel.actualRawCommonBaseLoopsProduceEntirePairClearedMarkedDisk"
private noncomputable def actualOriginalPuncturedSidesDiskRealization := rawFrozenProof% "ActualRawCommonBaseLoopsEntirePairClearedMarkedDisk_VERIFIED" "CurveComplex.HyperellipticModel.actualOriginalPuncturedSidesDiskRealization"
private noncomputable def actualInnermostOriginalTwoSideDiskClearance := rawFrozenProof% "ActualRawCommonBaseLoopsEntirePairClearedMarkedDisk_VERIFIED" "CurveComplex.HyperellipticModel.actualInnermostOriginalTwoSideDiskClearance"
private noncomputable def actualRawUnequalEndpointNonloopsProduceEntirePairClearedMarkedDisk := rawFrozenProof% "ActualRawUnequalEndpointNonloopsEntirePairClearedMarkedDisk_VERIFIED" "CurveComplex.HyperellipticModel.actualRawUnequalEndpointNonloopsProduceEntirePairClearedMarkedDisk"
private noncomputable def actualRawOriginalPairReversalPremises := rawFrozenProof% "ActualRawOriginalPairOrientationPremises_VERIFIED" "CurveComplex.HyperellipticModel.actualRawOriginalPairReversalPremises"
private noncomputable def actualRawOriginalPairSwappedPremises := rawFrozenProof% "ActualRawOriginalPairOrientationPremises_VERIFIED" "CurveComplex.HyperellipticModel.actualRawOriginalPairSwappedPremises"
private noncomputable def actualEmptyOriginalDiskPhysicalTraceTransfer := rawFrozenProof% "ActualRawOriginalPairOrientationPremises_VERIFIED" "CurveComplex.HyperellipticModel.actualEmptyOriginalDiskPhysicalTraceTransfer"
private noncomputable def actualEmptyOriginalDiskSwap := rawFrozenProof% "ActualRawOriginalPairOrientationPremises_VERIFIED" "CurveComplex.HyperellipticModel.actualEmptyOriginalDiskSwap"
private noncomputable def actualOriginalLoopContactIsCommonPhysicalBase := rawFrozenProof% "ActualRawPhysicalEndpointCaseSplit_VERIFIED" "CurveComplex.HyperellipticModel.actualOriginalLoopContactIsCommonPhysicalBase"
private noncomputable def actualOriginalLoopNonloopContactOrientation := rawFrozenProof% "ActualRawPhysicalEndpointCaseSplit_VERIFIED" "CurveComplex.HyperellipticModel.actualOriginalLoopNonloopContactOrientation"
private noncomputable def actualOriginalEqualEndpointSetsGiveOrientation := rawFrozenProof% "ActualRawPhysicalEndpointCaseSplit_VERIFIED" "CurveComplex.HyperellipticModel.actualOriginalEqualEndpointSetsGiveOrientation"
private noncomputable def actualRawAlignedNonloopOriginalSubpathsPuncturedHomotopic := rawFrozenProof% "ActualRawAlignedNonloopOriginalSubpathsPuncturedHomotopic_RECOVERY_CANDIDATE" "CurveComplex.HyperellipticModel.actualRawAlignedNonloopOriginalSubpathsPuncturedHomotopic"
private noncomputable def actual_raw_mixed_loop_marked_corner_decoder := rawFrozenProof% "ActualRawMixedLoopMarkedCornerDecoderCandidate" "CurveComplex.HyperellipticModel.actual_raw_mixed_loop_marked_corner_decoder"

private theorem actualRawAlignedNonloopsProduceEntirePairClearedMarkedDisk
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0≠a.val.map 1)
    (hne : vertex M a≠vertex M b) (hc : IsArcSimplex M {vertex M a,vertex M b})
    (hb0 : b.val.map 0=a.val.map 0) (hb1 : b.val.map 1=a.val.map 1)
    (hf : (crossings M a b).Finite)
    (ht : ∀ p∈crossings M a b,CrossesInDisk M a b p)
    (hp : (crossings M a b).Nonempty) :
    ∃ B : ActualMarkedTwoSideDisk M a b,
      Disjoint B.openInterior (a.val.image ∪ b.val.image) ∧
      (B.firstCorner∈crossings M a b ∨ B.secondCorner∈crossings M a b) := by
  obtain ⟨p,hp⟩ := hp
  obtain ⟨f,g,u,v,hf',hg,hfa,hgb,hf0,hg0,hf1,hg1,huv,hinter,hvcross,hucontact,
    hu,hv,α,β,hα,hβ,hhom⟩ := actualRawAlignedNonloopOriginalSubpathsPuncturedHomotopic
      M a b ha hne hc hb0 hb1 hf ht p hp
  obtain ⟨D,hDf,hDg,hDu,hDv⟩ := actualOriginalPuncturedSidesDiskRealization
    M a b f g u v hf' hg hfa hgb hf0 hg0 hf1 hg1 huv hinter hu hv α β hα hβ hhom
  obtain ⟨B,_,hfree,hpositive⟩ := actualInnermostOriginalTwoSideDiskClearance
    M a b hf ht D (Or.inr (hDv.symm ▸ hvcross))
  exact ⟨B,hfree,hpositive⟩
private theorem actualRawOldLoopAllPhysicalEndpointCases
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0=a.val.map 1)
    (hne : vertex M a≠vertex M b)
    (hc : IsArcSimplex M {vertex M a,vertex M b})
    (hf : (crossings M a b).Finite)
    (ht : ∀ p∈crossings M a b,CrossesInDisk M a b p)
    (hp : (crossings M a b).Nonempty) :
    ∃ B : ActualMarkedTwoSideDisk M a b,
      Disjoint B.openInterior (a.val.image ∪ b.val.image) ∧
      (B.firstCorner∈crossings M a b ∨ B.secondCorner∈crossings M a b) := by
  classical
  by_cases hsep : ∀ c : Interval,c=0 ∨ c=1 → b.val.map c∉a.val.image
  · exact actualRawEndpointSeparatedProducesEntirePairClearedMarkedDisk M a b hne hc hf ht hp hsep
  by_cases hb : b.val.map 0=b.val.map 1
  · obtain ⟨h0,h1⟩ := actualOriginalLoopContactIsCommonPhysicalBase M a b ha hb hsep
    exact actualRawCommonBaseLoopsProduceEntirePairClearedMarkedDisk M a b ha hne hc h0 h1 hf ht hp
  rcases actualOriginalLoopNonloopContactOrientation M a b ha hb hsep with h | h
  · obtain ⟨D,hD⟩ := actual_raw_mixed_loop_marked_corner_decoder M a b ha hne hc h.1 h.2 hf ht hp
    obtain ⟨B,_,hfree,hpositive⟩ := actualInnermostOriginalTwoSideDiskClearance M a b hf ht D hD
    exact ⟨B,hfree,hpositive⟩
  · obtain ⟨hne',hc',hf',ht',hp'⟩ := actualRawOriginalPairReversalPremises M a b hne hc hf ht hp
    have h0 : b.reverse.val.map 0=a.val.map 0 := by simpa using h.1
    have h1 : b.reverse.val.map 1∉a.val.image := by simpa using h.2
    obtain ⟨D,hD⟩ := actual_raw_mixed_loop_marked_corner_decoder M a b.reverse ha hne' hc' h0 h1 hf' ht' hp'
    obtain ⟨B,_,hfree,hpositive⟩ := actualInnermostOriginalTwoSideDiskClearance M a b.reverse hf' ht' D hD
    obtain ⟨B',_,_,_,hfree',hpositive'⟩ := actualEmptyOriginalDiskPhysicalTraceTransfer
      M a b a b.reverse rfl b.reverse_image B hfree hpositive
    exact ⟨B',hfree',hpositive'⟩

theorem actual_raw_compatible_pair_marked_bigon_selector
(M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
(hclasses : ArcSurgery.vertex M a ≠ ArcSurgery.vertex M b)
(hcompatible : IsArcSimplex M {ArcSurgery.vertex M a, ArcSurgery.vertex M b})
(hfinite : (ArcSurgery.crossings M a b).Finite)
(htransverse : ∀ p ∈ ArcSurgery.crossings M a b,
  ArcSurgery.CrossesInDisk M a b p)
(hcontact : (ArcSurgery.crossings M a b).Nonempty) :
∃ B : ActualMarkedTwoSideDisk M a b,
  Disjoint B.openInterior (a.val.image ∪ b.val.image) ∧
  (B.firstCorner ∈ ArcSurgery.crossings M a b ∨
    B.secondCorner ∈ ArcSurgery.crossings M a b) := by
  classical
  by_cases ha : a.val.map 0=a.val.map 1
  · exact actualRawOldLoopAllPhysicalEndpointCases M a b ha hclasses hcompatible hfinite htransverse hcontact
  by_cases hb : b.val.map 0=b.val.map 1
  · obtain ⟨hne',hc',hf',ht',hp'⟩ := actualRawOriginalPairSwappedPremises
      M a b hclasses hcompatible hfinite htransverse hcontact
    obtain ⟨B,hfree,hpositive⟩ := actualRawOldLoopAllPhysicalEndpointCases M b a hb hne' hc' hf' ht' hp'
    obtain ⟨B',_,_,_,hfree',hpositive'⟩ := actualEmptyOriginalDiskSwap M a b B hfree hpositive
    exact ⟨B',hfree',hpositive'⟩
  by_cases he : classEndpoints M (vertex M a)=classEndpoints M (vertex M b)
  · rcases actualOriginalEqualEndpointSetsGiveOrientation M a b ha he with h | h
    · exact actualRawAlignedNonloopsProduceEntirePairClearedMarkedDisk
        M a b ha hclasses hcompatible h.1 h.2 hfinite htransverse hcontact
    · obtain ⟨hne',hc',hf',ht',hp'⟩ := actualRawOriginalPairReversalPremises
        M a b hclasses hcompatible hfinite htransverse hcontact
      have h0 : b.reverse.val.map 0=a.val.map 0 := by simpa using h.1
      have h1 : b.reverse.val.map 1=a.val.map 1 := by simpa using h.2
      obtain ⟨B,hfree,hpositive⟩ := actualRawAlignedNonloopsProduceEntirePairClearedMarkedDisk
        M a b.reverse ha hne' hc' h0 h1 hf' ht' hp'
      obtain ⟨B',_,_,_,hfree',hpositive'⟩ := actualEmptyOriginalDiskPhysicalTraceTransfer
        M a b a b.reverse rfl b.reverse_image B hfree hpositive
      exact ⟨B',hfree',hpositive'⟩
  · exact actualRawUnequalEndpointNonloopsProduceEntirePairClearedMarkedDisk
      M a b hclasses hcompatible ha hb he hfinite htransverse hcontact

end CurveComplex.HyperellipticModel
