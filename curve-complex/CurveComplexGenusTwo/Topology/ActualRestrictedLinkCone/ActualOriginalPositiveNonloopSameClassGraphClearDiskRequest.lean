import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopUnconditionalFinitePreparationFullTargetPrivate
import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualNonloopOriginalSubpathsFromActualSweepPrivate
import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualNonloopOriginalSubpathsOrientationConditionalPrivate
import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopContactDiskFromOriginalSubpathsPrivate
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedEmptyBigonCleanSides

open Lean Elab Term in
elab "checkedRLApprovedDiskActualSweepKernel" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualNonloopOriginalSubpathsFromActualSweepPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_nonloop_original_subpaths_punctured_homotopic_of_actual_sweep_private
  discard <| getConstInfo n
  return mkConst n
open Lean Elab Term in
elab "checkedRLApprovedDiskSameClassOrientationBridge" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualNonloopOriginalSubpathsOrientationConditionalPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_original_same_class_nonloop_subpaths_of_aligned_actual_sweep_selector_private
  discard <| getConstInfo n
  return mkConst n
open Lean Elab Term in
elab "checkedRLApprovedDiskOriginalSubpathsDiskCleanup" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopContactDiskFromOriginalSubpathsPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_original_nonloop_entire_pair_graph_clear_disk_of_original_subpaths_private
  discard <| getConstInfo n
  return mkConst n

namespace CurveComplex.HyperellipticModel
open Set Metric Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Exact original same-class positive NONLOOP contact disk.
The given finite original disjoint/partly aligned families determine the fixed graph.
Independent endpoint clocks are allowed; no ordered endpoint equality is assumed.
The output sides lie on the literal original traces, the open disk avoids the
entire original pair, all marks, and the entire literal already aligned J graph.
At least one corner is a genuine original interior crossing. -/
theorem actual_original_positive_nonloop_same_class_entire_pair_and_graph_clear_disk
    (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
    (F J : Finset (EssentialArcClass M)) (hTF : T.val ⊆ F) (hJT : J ⊆ T.val)
    (r r0 : {w // w ∈ F} → EssentialMarkedArc M)
    (rT : {w // w ∈ T.val} → EssentialMarkedArc M)
    (hd0 : ∀ w z,w≠z → Disjoint (arcInterior M (r0 w)) (arcInterior M (r0 z)))
    (u : {w // w ∈ T.val}) (hu : u.val ∉ J)
    (hdT : ∀ w : {w // w ∈ T.val},w.val ∈ J → Disjoint (arcInterior M (rT w)) (arcInterior M (rT u)))
    (haligned0 : ∀ w : {w // w ∈ T.val},w.val ∈ J → r0 ⟨w.val,hTF w.property⟩=rT w)
    (hgraph : actualObjectTrace M r0 J=actualObjectTrace M r J)
    (hab : Quotient.mk (essentialArcSetoid M) (r0 ⟨u.val,hTF u.property⟩)=
      Quotient.mk (essentialArcSetoid M) (rT u))
    (ha : (r0 ⟨u.val,hTF u.property⟩).val.map 0≠(r0 ⟨u.val,hTF u.property⟩).val.map 1)
    (hfinite : (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).Finite)
    (hcross : ∀ q ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
      ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) q)
    (q : S) (hq : q ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)) :
    ∃ D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u),
      Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image ∪
          (M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
      (D.firstCorner∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u) ∨
        D.secondCorner∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)) := by
  classical
  have hSubpaths := checkedRLApprovedDiskSameClassOrientationBridge
    (fun M a b => checkedRLApprovedDiskActualSweepKernel M a b)
    M (r0 ⟨u.val,hTF u.property⟩) (rT u) ha hab hfinite hcross q hq
  exact checkedRLApprovedDiskOriginalSubpathsDiskCleanup M p T F J hTF hJT
    r r0 rT hd0 u hu hdT haligned0 hgraph hab ha hfinite hcross hSubpaths
end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.actual_original_positive_nonloop_same_class_entire_pair_and_graph_clear_disk
