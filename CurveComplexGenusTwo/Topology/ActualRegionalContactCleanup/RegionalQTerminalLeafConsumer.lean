import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalActualSubpathRange
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalReverseFirstContact
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalReverseTailPrefix
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalQTerminalLeafImportProbe

open CurveComplex Set Topology
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

theorem regional_Q_initial_prefix_terminal_surgery_has_essential_branch
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (R : ℝ) (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (a b ar : EssentialProperArc S x R)
    (har : ∀ t, ar.val.val t = a.val.val (unitInterval.symm t))
    (d e : ProperArc S x R) (u r : Interval)
    (hu0 : 0 < u) (hu1 : u < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hcross : b.val.val u = a.val.val r)
    (hprefix : ∀ s t : Interval, t ≤ r →
      b.val.val s = a.val.val t → s = u ∧ t = r)
    (hd0 : d.val 0 = b.val.val 0)
    (he0 : e.val 0 = b.val.val 1)
    (hd1 : d.val 1 = a.val.val 0)
    (he1 : e.val 1 = a.val.val 0)
    (hdimage : Set.range d.val =
      (b.val.val '' Set.Icc 0 u) ∪ (a.val.val '' Set.Icc 0 r))
    (heimage : Set.range e.val =
      (b.val.val '' Set.Icc u 1) ∪ (a.val.val '' Set.Icc 0 r)) :
    ¬ boundaryParallel S x R d ∨ ¬ boundaryParallel S x R e := by
  let v : Interval := unitInterval.symm r
  have hv0 : 0 < v := by
    have h : (r : ℝ) < 1 := hr1
    change 0 < 1-(r : ℝ)
    linarith only [h]
  have hv1 : v < 1 := by
    have h : (0 : ℝ) < (r : ℝ) := hr0
    change 1-(r : ℝ) < 1
    linarith only [h]
  have hcross' : b.val.val u = ar.val.val v := by
    rw [har]
    change b.val.val u = a.val.val (unitInterval.symm (unitInterval.symm r))
    rw [unitInterval.symm_involutive]
    exact hcross
  have htail : ∀ s t : Interval, v ≤ t →
      b.val.val s = ar.val.val t → s = u ∧ t = v := by
    intro s t ht he
    have hc : b.val.val s = a.val.val (unitInterval.symm t) := by
      rw [har] at he
      exact he
    exact regional_prefix_first_contact_becomes_reversed_tail_first_contact
      a.val.val b.val.val r u hprefix s t ht hc
  have hd1' : d.val 1 = ar.val.val 1 := by
    rw [har,unitInterval.symm_one]
    exact hd1
  have he1' : e.val 1 = ar.val.val 1 := by
    rw [har,unitInterval.symm_one]
    exact he1
  let pb : Path (b.val.val 0) (b.val.val 1) :=
    { toContinuousMap := b.val.val, source' := rfl, target' := rfl }
  let pa : Path (ar.val.val 0) (ar.val.val 1) :=
    { toContinuousMap := ar.val.val, source' := rfl, target' := rfl }
  have htailRange : ar.val.val '' Set.Icc v 1 =
      a.val.val '' Set.Icc 0 r := by
    have he : ar.val.val = fun t => a.val.val (unitInterval.symm t) :=
      funext har
    rw [he]
    exact regional_reversed_anchor_tail_is_original_prefix a.val.val r
  have hdimage' : Set.range d.val =
      Set.range (CurveComplex.BranchedDoubleCover.actualSubpath pb 0 u) ∪
      Set.range (CurveComplex.BranchedDoubleCover.actualSubpath pa v 1) := by
    rw [regional_actualSubpath_range_of_le pb 0 u u.property.1,
      regional_actualSubpath_range_of_le pa v 1 v.property.2]
    exact hdimage.trans (congrArg₂ (· ∪ ·) rfl htailRange.symm)
  have heimage' : Set.range e.val =
      Set.range (CurveComplex.BranchedDoubleCover.actualSubpath pb u 1) ∪
      Set.range (CurveComplex.BranchedDoubleCover.actualSubpath pa v 1) := by
    rw [regional_actualSubpath_range_of_le pb u 1 u.property.2,
      regional_actualSubpath_range_of_le pa v 1 v.property.2]
    exact heimage.trans (congrArg₂ (· ∪ ·) rfl htailRange.symm)
  exact regionalOriginalQTerminalLeaf S x R g hg hS hR htarget ar b d e
    u v hu0 hu1 hv0 hv1 hcross' htail hd0 he0 hd1' he1'
    hdimage' heimage'

#print axioms regional_Q_initial_prefix_terminal_surgery_has_essential_branch
