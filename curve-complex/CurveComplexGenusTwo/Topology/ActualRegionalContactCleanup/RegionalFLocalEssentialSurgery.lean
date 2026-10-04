import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalFQRawBranchRange
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalOriginalQArcReverse
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalQBranchEssentialToF
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalQTerminalLeafConsumer
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalSameRangeEssential

open CurveComplex Set Topology
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

theorem regional_F_first_contact_raw_pair_has_essential_branch
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (R : ℝ) (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F B : Set S) (hFQ : F ⊆ (openDisk S x R)ᶜ)
    (hB : B = boundaryCircle S x R)
    (aF bF dF eF : C(Interval,↥F))
    (aQ bQ : EssentialProperArc S x R)
    (dQ eQ : ProperArc S x R)
    (ha : ∀ t, (aF t).val = (aQ.val.val t).val)
    (hb : ∀ t, (bF t).val = (bQ.val.val t).val)
    (hd : ∀ t, (dF t).val = (dQ.val t).val)
    (he : ∀ t, (eF t).val = (eQ.val t).val)
    (r u : Interval) (hr0 : 0 < r) (hr1 : r < 1)
    (hu0 : 0 < u) (hu1 : u < 1)
    (hcontact : aF r = bF u)
    (hprefix : ∀ s t : Interval, t ≤ r → bF s = aF t → s = u ∧ t = r)
    (hd0 : dF 0 = aF 0) (he0 : eF 0 = aF 0)
    (hd1 : dF 1 = bF 0) (he1 : eF 1 = bF 1)
    (hdimage : Set.range dF =
      (aF '' Set.Icc 0 r) ∪ (bF '' Set.Icc 0 u))
    (heimage : Set.range eF =
      (aF '' Set.Icc 0 r) ∪ (bF '' Set.Icc u 1)) :
    (¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ B) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding D ∧
        D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range dF ∪ Set.range v) ∨
    (¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ B) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding D ∧
        D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range eF ∪ Set.range v) := by
  obtain ⟨ar,har,hrangeA⟩ := regional_original_Q_essential_arc_reverse x R aQ
  obtain ⟨dr,hdr,hdrange⟩ := regional_original_Q_proper_arc_reverse x R dQ
  obtain ⟨er,her,herange⟩ := regional_original_Q_proper_arc_reverse x R eQ
  have hcrossQ : bQ.val.val u = aQ.val.val r := by
    apply Subtype.ext
    exact (hb u).symm.trans ((congrArg Subtype.val hcontact).symm.trans (ha r))
  have hprefixQ : ∀ s t : Interval, t ≤ r →
      bQ.val.val s = aQ.val.val t → s = u ∧ t = r := by
    intro s t ht heq
    have hst : bF s = aF t := Subtype.ext
      ((hb s).trans ((congrArg Subtype.val heq).trans (ha t).symm))
    exact hprefix s t ht hst
  have hdr0 : dr.val 0 = bQ.val.val 0 := by
    rw [hdr,unitInterval.symm_zero]
    apply Subtype.ext
    exact (hd 1).symm.trans ((congrArg Subtype.val hd1).trans (hb 0))
  have her0 : er.val 0 = bQ.val.val 1 := by
    rw [her,unitInterval.symm_zero]
    apply Subtype.ext
    exact (he 1).symm.trans ((congrArg Subtype.val he1).trans (hb 1))
  have hdr1 : dr.val 1 = aQ.val.val 0 := by
    rw [hdr,unitInterval.symm_one]
    apply Subtype.ext
    exact (hd 0).symm.trans ((congrArg Subtype.val hd0).trans (ha 0))
  have her1 : er.val 1 = aQ.val.val 0 := by
    rw [her,unitInterval.symm_one]
    apply Subtype.ext
    exact (he 0).symm.trans ((congrArg Subtype.val he0).trans (ha 0))
  have hdQrange : Set.range dr.val =
      (bQ.val.val '' Set.Icc 0 u) ∪ (aQ.val.val '' Set.Icc 0 r) := by
    rw [hdrange]
    have h := regional_F_raw_branch_range_transports_to_Q F (openDisk S x R)ᶜ
      hFQ aF bF dF aQ.val.val bQ.val.val dQ.val ha hb hd r u false hdimage
    change Set.range dQ.val = _
    rw [h]
    exact Set.union_comm _ _
  have heQrange : Set.range er.val =
      (bQ.val.val '' Set.Icc u 1) ∪ (aQ.val.val '' Set.Icc 0 r) := by
    rw [herange]
    have h := regional_F_raw_branch_range_transports_to_Q F (openDisk S x R)ᶜ
      hFQ aF bF eF aQ.val.val bQ.val.val eQ.val ha hb he r u true heimage
    change Set.range eQ.val = _
    rw [h]
    exact Set.union_comm _ _
  rcases regional_Q_initial_prefix_terminal_surgery_has_essential_branch
      S x R g hg hS hR htarget aQ bQ ar har dr er u r hu0 hu1 hr0 hr1
      hcrossQ hprefixQ hdr0 her0 hdr1 her1
      hdQrange heQrange with hD | hE
  · left
    have hqd : ¬ boundaryParallel S x R dQ :=
      regional_original_Q_essential_same_range x R dr dQ hdrange hD
    exact regional_Q_essential_same_trace_branch_is_F_essential x R F B
      hFQ hB dF dQ hd hqd
  · right
    have hqe : ¬ boundaryParallel S x R eQ :=
      regional_original_Q_essential_same_range x R er eQ herange hE
    exact regional_Q_essential_same_trace_branch_is_F_essential x R F B
      hFQ hB eF eQ he hqe

#print axioms regional_F_first_contact_raw_pair_has_essential_branch
