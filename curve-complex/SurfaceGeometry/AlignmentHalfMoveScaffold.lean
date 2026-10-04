import OriginalHalfDiskBoundarySideRelativeOpen
import RectangleOneFreeEndCrosscutsMotion
import RelativeCleanHalfAlignmentCollar
import RelativeCleanHalfAlignmentCrosscuts
import Lean.Util.CollectAxioms

import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalBRecognitionConsumer
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryRectangle.DisjointFreeBoundaryRectangle
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.ProperBoundaryRectangleCollaredExtension
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.InteriorRailProtectedMotion
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.ActualOriginalGraphRelativeFreePosition
import CurveComplexGenusTwo.Topology.ActualFreeBoundarySupportedContactDrop.FreeBoundarySupportedContactDrop
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryAllCrossing.FreeBoundaryAllCrossingTarget
import CurveComplexGenusTwo.Topology.ActualHarerSupportedBypass.ActualWholeArcGraphSupportedBypassAssembly
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import RegionalHalfDiskDescent
import CurveComplexGenusTwo.Topology.ActualRegionalCompatibleReturn.RegionalHalfDiskContactCleanup

open Set Topology CurveComplex
open scoped Manifold ContDiff

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- Exact actual-Q half-bigon contact drop with terminal protected-range restoration.
The supplied three-side disk may contain the original u/v interiors; the separately
owned actual empty-subdisk descent is a proof dependency, not a new premise. -/
theorem original_Q_half_bigon_terminal_restoring_contact_drop
    (S : Type) [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ (u v : C(Interval, ↥Q)),
      IsEmbedding u → IsEmbedding v →
      (u 0 ∈ B ∧ u 1 ∈ B ∧ v 0 ∈ B ∧ v 1 ∈ B) →
      (∀ t ∈ Ioo (0 : Interval) 1, u t ∉ B ∧ v t ∉ B) →
      (∀ f ∈ ({u,v} : Set C(Interval, ↥Q)),
        ¬ ∃ w : C(Interval, ↥Q), IsEmbedding w ∧ (∀ t, w t ∈ B) ∧
          ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
            IsEmbedding e ∧
            e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
              Set.range f ∪ Set.range w) →
      Disjoint ({u 0,u 1} : Set ↥Q) {v 0,v 1} →
      (Set.range u ∩ Set.range v).Finite →
      RegionalEmbeddedFamily.RegionalAllInteriorContactsCross Q u v →
      ∀ (J : Type) [Fintype J] (c : J → C(Interval, ↥Q)),
        (∀ j, IsEmbedding (c j)) →
        (∀ j, c j 0 ∈ B ∧ c j 1 ∈ B) →
        (∀ j t, t ∈ Ioo (0 : Interval) 1 → c j t ∉ B) →
        (∀ j, ¬ ∃ w : C(Interval, ↥Q), IsEmbedding w ∧ (∀ t, w t ∈ B) ∧
          ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
            IsEmbedding e ∧
            e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
              Set.range (c j) ∪ Set.range w) →
        (∀ j k, j ≠ k → Disjoint (Set.range (c j)) (Set.range (c k))) →
        (∀ j, Disjoint (Set.range u) (Set.range (c j)) ∧
          Disjoint (Set.range v) (Set.range (c j))) →
        ∀ (N : CoherentEndpointMotion.FreeBoundaryNullGeometry.NullHalfBigonBoundary B u v)
          (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q)),
          IsEmbedding d →
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range N.first ∪ Set.range N.second ∪ Set.range N.boundarySide →
          ∃ (v' : C(Interval, ↥Q)) (K : AmbientIsotopy ↥Q),
            IsEmbedding v' ∧ (v' 0 ∈ B ∧ v' 1 ∈ B) ∧
            (∀ t ∈ Ioo (0 : Interval) 1, v' t ∉ B) ∧
            Disjoint ({u 0,u 1} : Set ↥Q) {v' 0,v' 1} ∧
            (Set.range u ∩ Set.range v').Finite ∧
            (∀ t, (fun y => K.map (t,y)) '' B = B) ∧
            (∀ j, K.finalMap '' Set.range (c j) = Set.range (c j)) ∧
            K.finalMap '' Set.range v = Set.range v' ∧
            (Set.range u ∩ Set.range v').ncard < (Set.range u ∩ Set.range v).ncard := by
  classical
  intro Q B a q ha hq hends hmid hessential hEndpointSep hFinite hCross
    J instJ c hc hcEnds hcInterior hcEssential hcDisjoint hOff N d hd hboundary
  letI : ClosedSurface S := Classical.choice hS.2.1
  have haEnds : a 0 ∈ B ∧ a 1 ∈ B := ⟨hends.1,hends.2.1⟩
  have hqEnds : q 0 ∈ B ∧ q 1 ∈ B := hends.2.2
  have haInterior : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B := fun t ht => (hmid t ht).1
  have hqInterior : ∀ t ∈ Ioo (0 : Interval) 1, q t ∉ B := fun t ht => (hmid t ht).2
  have haEssential := hessential a (by simp)
  have hqEssential := hessential q (by simp)
  let Ready (q' : C(Interval, ↥Q)) (K : AmbientIsotopy ↥Q) : Prop :=
    IsEmbedding q' ∧ (q' 0 ∈ B ∧ q' 1 ∈ B) ∧
    (∀ t ∈ Ioo (0 : Interval) 1, q' t ∉ B) ∧
    Disjoint ({a 0,a 1} : Set ↥Q) {q' 0,q' 1} ∧
    (Set.range a ∩ Set.range q').Finite ∧
    (∀ t, (fun y => K.map (t,y)) '' B = B) ∧
    (∀ j, K.finalMap '' Set.range (c j) = Set.range (c j)) ∧
    K.finalMap '' Set.range q = Set.range q'
  suffices H : ∃ q' K, Ready q' K ∧ (Set.range a ∩ Set.range q').ncard <
      (Set.range a ∩ Set.range q).ncard by
    obtain ⟨q',K,hK,hdrop⟩ := H
    exact ⟨q',K,hK.1,hK.2.1,hK.2.2.1,hK.2.2.2.1,hK.2.2.2.2.1,
      hK.2.2.2.2.2.1,hK.2.2.2.2.2.2.1,hK.2.2.2.2.2.2.2,hdrop⟩
  have hFrontier : frontier Q = (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R :=
    CoherentEndpointMotion.chart_deleted_disk_complement_frontier
      (chartAt (EuclideanSpace ℝ (Fin 2)) x) _ R hR htarget
  have hBoundaryFrontier (y : ↥Q) : y ∈ B ↔ y.val ∈ frontier Q := by
    rw [hFrontier]
    rfl
  let E₀ := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let D₀ : Set S := E₀.symm '' Metric.ball (E₀ x) R
  let C₀ : Set S := E₀.symm '' Metric.closedBall (E₀ x) R
  have hD₀open : IsOpen D₀ := E₀.symm.isOpen_image_of_subset_source
    Metric.isOpen_ball (Metric.ball_subset_closedBall.trans htarget)
  have hQclosed : IsClosed Q := hD₀open.isClosed_compl
  have hQcompact : IsCompact Q := hQclosed.isCompact
  have hxNotQ : x ∉ Q := by
    intro hx
    exact hx ⟨E₀ x,by simpa only [E₀,Metric.mem_ball,dist_self] using hR,
      E₀.left_inv (mem_chart_source _ _)⟩
  have hBdConnected : IsConnected (frontier Q) := by
    obtain ⟨c,hc⟩ := CoherentEndpointMotion.FreeBoundaryContactRepair.chartSphere_curve
      S E₀ (E₀ x) R hR htarget
    rw [hFrontier,← hc]
    exact isConnected_range c.embedded.continuous
  have hQconnected : IsConnected Q := by
    refine ⟨hBdConnected.nonempty.mono hQclosed.frontier_subset,?_⟩
    apply isPreconnected_closed_iff.mpr
    intro U V hU hV hcover hQU hQV
    by_contra hnone
    have hApart : ∀ z ∈ Q, z ∈ U → z ∈ V → False := by
      intro z hz hu hv
      exact hnone ⟨z,hz,hu,hv⟩
    have hNoAvoid
        (T W : Set S) (hT : IsClosed T) (hW : IsClosed W)
        (hcoverTW : Q ⊆ T ∪ W) (hQT : (Q ∩ T).Nonempty)
        (hApartTW : ∀ z ∈ Q, z ∈ T → z ∈ W → False)
        (hAvoid : ¬ (frontier Q ∩ T).Nonempty) : False := by
      have hOpenEq : Q ∩ T = interior Q ∩ Wᶜ := by
        ext z
        constructor
        · rintro ⟨hz,hzT⟩
          refine ⟨(mem_interior_iff_notMem_frontier hz).mpr ?_,?_⟩
          · intro hzF
            exact hAvoid ⟨z,hzF,hzT⟩
          · exact hApartTW z hz hzT
        · rintro ⟨hz,hzW⟩
          exact ⟨interior_subset hz,(hcoverTW (interior_subset hz)).resolve_right hzW⟩
      have hClopen : IsClopen (Q ∩ T) :=
        ⟨hQclosed.inter hT,hOpenEq.symm ▸ isOpen_interior.inter hW.isOpen_compl⟩
      have hAll := hClopen.eq_univ hQT
      exact hxNotQ ((hAll.symm ▸ Set.mem_univ x : x ∈ Q ∩ T).1)
    have hFU : (frontier Q ∩ U).Nonempty := by
      by_contra h
      exact hNoAvoid U V hU hV hcover hQU hApart h
    have hFV : (frontier Q ∩ V).Nonempty := by
      by_contra h
      exact hNoAvoid V U hV hU (fun z hz => (hcover hz).symm) hQV
        (fun z hz hv hu => hApart z hz hu hv) h
    obtain ⟨z,hzF,hzU,hzV⟩ := isPreconnected_closed_iff.mp hBdConnected.isPreconnected
      U V hU hV (fun z hz => hcover (hQclosed.frontier_subset hz)) hFU hFV
    exact hApart z (hQclosed.frontier_subset hzF) hzU hzV
  have hC₀compact : IsCompact C₀ := (isCompact_closedBall _ _).image_of_continuousOn
    (E₀.continuousOn_symm.mono htarget)
  have hC₀source : C₀ ⊆ E₀.source := by
    rintro z ⟨w,hw,rfl⟩
    exact E₀.map_target (htarget hw)
  have hClosureD₀ : closure D₀ = C₀ := by
    apply Set.Subset.antisymm
    · exact hC₀compact.isClosed.closure_subset_iff.mpr
        (Set.image_mono Metric.ball_subset_closedBall)
    · rintro z ⟨w,hw,rfl⟩
      have hwcl : w ∈ closure (Metric.ball (E₀ x) R) := by
        rw [closure_ball _ hR.ne']
        exact hw
      have hc : ContinuousOn E₀.symm (closure (Metric.ball (E₀ x) R)) := by
        rw [closure_ball _ hR.ne']
        exact E₀.continuousOn_symm.mono htarget
      exact hc.image_closure ⟨w,hwcl,rfl⟩
  have hInteriorC₀ : interior C₀ = D₀ := by
    have hImage : E₀.IsImage C₀ (Metric.closedBall (E₀ x) R) := by
      intro z hz
      constructor
      · intro hw
        exact ⟨E₀ z,hw,E₀.left_inv hz⟩
      · rintro ⟨w,hw,rfl⟩
        rwa [E₀.right_inv (htarget hw)]
    have hI := hImage.interior.symm_image_eq
    rw [interior_closedBall _ hR.ne',Set.inter_eq_right.mpr
      (Metric.ball_subset_closedBall.trans htarget),Set.inter_eq_right.mpr
      (interior_subset.trans hC₀source)] at hI
    exact hI.symm
  have hQregular : closure (interior Q) = Q := by
    change closure (interior D₀ᶜ) = D₀ᶜ
    rw [interior_compl,closure_compl,hClosureD₀,hInteriorC₀]
  have hbaseQ : E₀.symm '' Metric.sphere (E₀ x) R ⊆ Q := by
    change (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ Q
    rw [← hFrontier]
    exact hQclosed.frontier_subset
  have hOrdinaryDrop
      (N : CoherentEndpointMotion.FreeBoundaryNullGeometry.NullBigonBoundary B a q)
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q))
      (hd : IsEmbedding d)
      (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range N.first ∪ Set.range N.second) :
      ∃ v T, Ready v T ∧
        (Set.range a ∩ Set.range v).ncard < (Set.range a ∩ Set.range q).ncard := by
    have hBfree : Disjoint B (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
      apply Set.disjoint_left.mpr
      rintro y hy ⟨z, hz, rfl⟩
      exact RegionalEmbeddedFamily.embedded_regional_disk_interior_avoids_frontier
        S Q d hd z hz ((hBoundaryFrontier _).mp hy)
    obtain ⟨p, r, e, hp, hr, he, hpa, hrq, hpr0, hpr1, heb, hesub, heEmpty⟩ :=
      CoherentEndpointMotion.actual_two_side_disk_in_subset_has_empty_subdisk
        Q B a q ha hq haEnds hqEnds hFinite
        N.first N.second N.first_embedded N.second_embedded N.first_on_a N.second_on_b
        N.zero_eq N.one_eq d hd hboundary hBfree
    have hProtected : ∀ j, Disjoint (Set.range (c j)) (Set.range e) := by
      intro j
      exact (CoherentEndpointMotion.actual_ordinary_two_side_disk_clears_protected_arc
        Q B a q (c j) (hcEnds j).1 N.first N.second
        N.first_on_a N.second_on_b d hd hboundary hBfree
        ((hOff j).1).symm ((hOff j).2).symm).mono_right hesub
    let moving : Option J → C(Interval, ↥Q) := fun k =>
      match k with
      | none => q
      | some j => c j
    let anchor : Unit → C(Interval, ↥Q) := fun _ => a
    have hmEmb : ∀ k, IsEmbedding (moving k) := by
      rintro (_ | j)
      · exact hq
      · exact hc j
    have hmDisjoint : ∀ k l, k ≠ l → Disjoint (Set.range (moving k)) (Set.range (moving l)) := by
      rintro (_ | k) (_ | l) hkl
      · exact (hkl rfl).elim
      · exact (hOff l).2
      · exact ((hOff k).2).symm
      · exact hcDisjoint k l (fun h => hkl (congrArg some h))
    have hUnion : (⋃ k, Set.range (moving k)) = Set.range q ∪ ⋃ j : J, Set.range (c j) := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨_ | j, hy⟩
        · exact Or.inl hy
        · exact Or.inr ⟨j, hy⟩
      · rintro (hy | ⟨j, hy⟩)
        · exact ⟨none, hy⟩
        · exact ⟨some j, hy⟩
    have hAnchor : (⋃ k, Set.range (anchor k)) = Set.range a := by
      ext y
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
        exact hk
      · intro hy
        exact Set.mem_iUnion.mpr ⟨(), hy⟩
    have hFamilyFinite : ((⋃ k, Set.range (anchor k)) ∩ (⋃ k, Set.range (moving k))).Finite := by
      rw [hAnchor, hUnion, Set.inter_union_distrib_left]
      have hNo : Set.range a ∩ (⋃ j : J, Set.range (c j)) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro y ⟨hy, hh⟩
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hh
        exact Set.disjoint_left.mp ((hOff j).1) hy hj
      rw [hNo, Set.union_empty]
      exact hFinite
    have hmEnds : ∀ k, (moving k 0).val ∈ frontier Q ∧ (moving k 1).val ∈ frontier Q := by
      rintro (_ | j)
      · exact ⟨(hBoundaryFrontier _).mp hqEnds.1, (hBoundaryFrontier _).mp hqEnds.2⟩
      · exact ⟨(hBoundaryFrontier _).mp (hcEnds j).1,
          (hBoundaryFrontier _).mp (hcEnds j).2⟩
    have hmInterior : ∀ k t, t ∈ Ioo (0 : Interval) 1 → (moving k t).val ∉ frontier Q := by
      rintro (_ | j) t ht
      · exact fun h => hqInterior t ht ((hBoundaryFrontier _).mpr h)
      · exact fun h => hcInterior j t ht ((hBoundaryFrontier _).mpr h)
    let ps : C(Interval, S) := ⟨fun t => (p t).val, continuous_subtype_val.comp p.continuous⟩
    let rs : C(Interval, S) := ⟨fun t => (r t).val, continuous_subtype_val.comp r.continuous⟩
    let es : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S) :=
      ⟨fun z => (e z).val, continuous_subtype_val.comp e.continuous⟩
    have hps : Set.range ps ⊆ Set.range (fun t : Interval => (anchor () t).val) := by
      rintro y ⟨t, rfl⟩
      obtain ⟨s, hs⟩ := hpa (Set.mem_range_self t)
      exact ⟨s, congrArg Subtype.val hs⟩
    have hrs : Set.range rs ⊆ Set.range (fun t : Interval => (moving none t).val) := by
      rintro y ⟨t, rfl⟩
      obtain ⟨s, hs⟩ := hrq (Set.mem_range_self t)
      exact ⟨s, congrArg Subtype.val hs⟩
    have hesb : es '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range ps ∪ Set.range rs := by
      change (Subtype.val ∘ e) '' _ = Set.range (Subtype.val ∘ p) ∪ Set.range (Subtype.val ∘ r)
      rw [Set.image_comp, heb, Set.image_union, Set.range_comp, Set.range_comp]
    have hesEmpty : Disjoint (es '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        ((⋃ k, Set.range (fun t : Interval => (anchor k t).val)) ∪
          (⋃ k, Set.range (fun t : Interval => (moving k t).val))) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨z, hz, rfl⟩ (hy | hy)
      · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
        obtain ⟨s, hs⟩ := hk
        exact Set.disjoint_left.mp heEmpty ⟨z, hz, rfl⟩ (Or.inl ⟨s, Subtype.ext hs⟩)
      · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
        obtain ⟨s, hs⟩ := hk
        cases k with
        | none => exact Set.disjoint_left.mp heEmpty ⟨z, hz, rfl⟩ (Or.inr ⟨s, Subtype.ext hs⟩)
        | some j =>
          exact Set.disjoint_left.mp (hProtected j)
            ⟨s, Subtype.ext hs⟩ (Set.mem_range_self z)
    have hGenuine : ps 0 ∉ frontier Q := by
      obtain ⟨s, hs⟩ := hpa (Set.mem_range_self 0)
      obtain ⟨t, ht⟩ := hrq (Set.mem_range_self 0)
      have hst : a s = q t := hs.trans (hpr0.trans ht.symm)
      have hint := CoherentEndpointMotion.FreeBoundaryContactRepair.free_boundary_contact_parameters_interior
        B a q ⟨haEnds.1, haEnds.2, hqEnds.1, hqEnds.2⟩
        (fun t ht => ⟨haInterior t ht, hqInterior t ht⟩) hEndpointSep s t hst
      intro h
      apply haInterior s hint.1
      exact (hBoundaryFrontier _).mpr ((congrArg Subtype.val hs).symm ▸ h)
    have hBypass : ∃ (r : Option J) (E : OpenPartialHomeomorph S Schoenflies.Plane)
      (A B : Set Schoenflies.Plane) (u v : Schoenflies.Plane),
      Schoenflies.Plane.closedSquare 0 1 ⊆ E.target ∧
      Schoenflies.IsArcBetween A u v ∧ Schoenflies.IsArcBetween B u v ∧
      u ∈ Schoenflies.modelCurve ∧ v ∈ Schoenflies.modelCurve ∧
      A \ {u, v} ⊆ Schoenflies.Plane.openSquare 0 1 ∧
      B \ {u, v} ⊆ Schoenflies.Plane.openSquare 0 1 ∧
      {y : S | y ∈ E.source ∧ E y ∈ Schoenflies.Plane.openSquare 0 1} ⊆ interior Q ∧
      {z : S | z ∈ E.source ∧ E z ∈ A} ⊆ Q ∧
      ({y : ↥Q | y.val ∈ {z : S |
          z ∈ E.source ∧ E z ∈ Schoenflies.Plane.closedSquare 0 1}} ∩ Set.range (moving r) =
        {y : ↥Q | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ A}}) ∧
      ({y : ↥Q | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ B}} ∩
        (⋃ k, Set.range (anchor k)) ⊆
        (⋃ k, Set.range (moving k)) ∩ (⋃ k, Set.range (anchor k))) ∧
      (∃ p : ↥Q,
        p ∈ {y : ↥Q | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ A}} ∩
          (⋃ k, Set.range (anchor k)) ∧
        p ∉ {y : ↥Q | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ B}}) ∧
      (∀ k, k ≠ r → ∀ y ∈ Set.range (moving k),
        y.val ∉ {z : S | z ∈ E.source ∧ E z ∈ Schoenflies.Plane.openSquare 0 1}) := by
      exact
        ActualHarerSupportedBypass.actual_empty_whole_arc_graph_disk_constructs_supported_replacement_crosscut
          S Q Unit (Option J) anchor moving (fun _ => ha) hmEmb
          (fun k l h => (h (Subsingleton.elim k l)).elim) hmDisjoint hFamilyFinite
          (fun _ => (hBoundaryFrontier _).mp haEnds.1)
          (fun _ => (hBoundaryFrontier _).mp haEnds.2)
          (fun k => (hmEnds k).1) (fun k => (hmEnds k).2)
          (fun _ t ht h => haInterior t ht ((hBoundaryFrontier _).mpr h)) hmInterior
          () none ps rs (IsEmbedding.subtypeVal.comp hp) (IsEmbedding.subtypeVal.comp hr)
          hps hrs (congrArg Subtype.val hpr0) (congrArg Subtype.val hpr1) es
          (IsEmbedding.subtypeVal.comp he) hesb (by rintro _ ⟨z, rfl⟩; exact (e z).property)
          hesEmpty (Or.inl hGenuine)
    obtain ⟨k, E, U, V, u, v, hSquare, hU, hV, hu, hv, hUi, hVi, hInside, hUF,
        hTrace, hRetain, ⟨y, hy, hyNew⟩, hAvoid⟩ := hBypass
    have hk : k = none := by
      cases k with
      | none => rfl
      | some j =>
        have hyMoving : y ∈ Set.range (c j) := (hTrace.symm ▸ hy.1).2
        have hyAnchor : y ∈ Set.range a := hAnchor ▸ hy.2
        exact False.elim (Set.disjoint_left.mp ((hOff j).1) hyAnchor hyMoving)
    subst k
    have hRetainSelected :
        {y : ↥Q | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ V}} ∩ Set.range a ⊆
          Set.range q ∩ Set.range a := by
      rintro z ⟨hzV,hzi⟩
      have hzAll := hRetain ⟨hzV, hAnchor.symm ▸ hzi⟩
      rw [hUnion] at hzAll
      rcases hzAll.1 with hzq | hzP
      · exact ⟨hzq,hzi⟩
      · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hzP
        exact False.elim (Set.disjoint_left.mp
          ((hOff j).1) hzi hj)
    have hyAnchor : y ∈ Set.range a := hAnchor ▸ hy.2
    let Up : Set ↥Q := {y | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ U}}
    let Vp : Set ↥Q := {y | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ V}}
    let W : Set S := {z | z ∈ E.source ∧ E z ∈ Schoenflies.Plane.openSquare 0 1}
    have hPull (C : Set Schoenflies.Plane) :
        {z : S | ∃ w : E.source, w.val = z ∧
          (E.toHomeomorphSourceTarget w : Schoenflies.Plane) ∈ C} =
        {z : S | z ∈ E.source ∧ E z ∈ C} := by
      ext z
      constructor
      · rintro ⟨w,rfl,hw⟩
        exact ⟨w.property,hw⟩
      · rintro ⟨hz,hc⟩
        exact ⟨⟨z,hz⟩,rfl,hc⟩
    obtain ⟨M,hMmove,hMfix⟩ :=
      position_crosscut_surface_square_support S E.source E.target E.open_source
        E.toHomeomorphSourceTarget hSquare U V u v hU hV hu hv hUi hVi
    rw [hPull U,hPull V] at hMmove
    rw [hPull (Schoenflies.Plane.openSquare 0 1)] at hMfix
    obtain ⟨K,hKM,hKfix,hKfront⟩ :=
      regional_ambient_isotopy_restricts_with_support Q W hInside M hMfix
    let q' : C(Interval,↥Q) :=
      ⟨fun t => K.finalMap (q t),
        K.map.continuous.comp (continuous_const.prodMk q.continuous)⟩
    obtain ⟨k,kEq⟩ := K.homeomorphism_at 1
    have hKemb : IsEmbedding (fun y => K.finalMap y) := by
      convert k.isEmbedding using 1
      funext y
      exact (kEq y).symm
    have hq' : IsEmbedding q' := hKemb.comp hq
    have hq'0 : q' 0 = q 0 := hKfront 1 (q 0) ((hBoundaryFrontier _).mp hqEnds.1)
    have hq'1 : q' 1 = q 1 := hKfront 1 (q 1) ((hBoundaryFrontier _).mp hqEnds.2)
    have hq'Interior : ∀ t ∈ Ioo (0 : Interval) 1, q' t ∉ B := by
      intro t ht h
      have hFix := hKfront 1 (q' t) ((hBoundaryFrontier _).mp h)
      have heq : q' t = q t := hKemb.injective hFix
      exact hqInterior t ht (heq ▸ h)
    have hq'Range : K.finalMap '' Set.range q = Set.range q' := by
      exact (Set.range_comp K.finalMap q).symm
    have hUp : Up ⊆ Set.range q := by
      intro z hz
      change z ∈ {z : ↥Q | z.val ∈ {w : S | w ∈ E.source ∧ E w ∈ U}} at hz
      exact (hTrace.symm ▸ hz).2
    have hWTrace : {z : ↥Q | z.val ∈ W} ∩ Set.range q ⊆ Up := by
      rintro z ⟨hzW,hzq⟩
      change z ∈ {z : ↥Q | z.val ∈ {w : S | w ∈ E.source ∧ E w ∈ U}}
      rw [← hTrace]
      exact ⟨⟨hzW.1,Schoenflies.Plane.openSquare_subset_closedSquare 0 1 hzW.2⟩,hzq⟩
    have hMove : K.finalMap '' Up = Vp := by
      ext z
      constructor
      · rintro ⟨w,hw,hwz⟩
        have hz : z.val ∈ M.finalMap '' {w : S | w ∈ E.source ∧ E w ∈ U} :=
          ⟨w.val,hw,(hKM 1 w).symm.trans (congrArg Subtype.val hwz)⟩
        change z.val ∈ {w : S | w ∈ E.source ∧ E w ∈ V}
        exact hMmove ▸ hz
      · intro hz
        have hzV : z.val ∈ {w : S | w ∈ E.source ∧ E w ∈ V} := hz
        have hzM : z.val ∈ M.finalMap '' {w : S | w ∈ E.source ∧ E w ∈ U} :=
          hMmove.symm ▸ hzV
        obtain ⟨w,hw,hwz⟩ := hzM
        let wQ : ↥Q := ⟨w,hUF hw⟩
        exact ⟨wQ,hw,Subtype.ext ((hKM 1 wQ).trans hwz)⟩
    have hRestFix (z : ↥Q) (hz : z ∈ Set.range q \ Up) : K.finalMap z = z :=
      hKfix 1 z (fun hzW => hz.2 (hWTrace ⟨hzW,hz.1⟩))
    have hRest : K.finalMap '' (Set.range q \ Up) = Set.range q \ Up := by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        simpa only [hRestFix w hw] using hw
      · intro hz
        exact ⟨z,hz,hRestFix z hz⟩
    have hNewTrace : Set.range q' = (Set.range q \ Up) ∪ Vp := by
      rw [← hq'Range]
      calc
        K.finalMap '' Set.range q = K.finalMap '' ((Set.range q \ Up) ∪ Up) :=
          congrArg (fun Z => K.finalMap '' Z) (Set.sdiff_union_of_subset hUp).symm
        _ = (Set.range q \ Up) ∪ Vp := by rw [Set.image_union,hRest,hMove]
    have hSubset : ((Set.range q \ Up) ∪ Vp) ∩ Set.range a ⊆
        Set.range q ∩ Set.range a := by
      rintro z ⟨hz,hzi⟩
      rcases hz with hz | hz
      · exact ⟨hz.1,hzi⟩
      · exact hRetainSelected ⟨hz,hzi⟩
    have hMissing : y ∉ ((Set.range q \ Up) ∪ Vp) ∩ Set.range a := by
      rintro ⟨hy',_⟩
      rcases hy' with hy' | hy'
      · exact hy'.2 hy.1
      · exact hyNew hy'
    have hFiniteRev : (Set.range q ∩ Set.range a).Finite := by
      simpa only [Set.inter_comm] using hFinite
    have hDrop : (((Set.range q \ Up) ∪ Vp) ∩ Set.range a).Finite ∧
        (((Set.range q \ Up) ∪ Vp) ∩ Set.range a).ncard <
          (Set.range q ∩ Set.range a).ncard := by
      refine ⟨hFiniteRev.subset hSubset,Set.ncard_lt_ncard ?_ hFiniteRev⟩
      apply Set.ssubset_iff_subset_ne.mpr
      refine ⟨hSubset,?_⟩
      intro heq
      exact hMissing (heq.symm ▸ ⟨hUp hy.1,hyAnchor⟩)
    have hNewFinite : (Set.range a ∩ Set.range q').Finite := by
      rw [Set.inter_comm,hNewTrace]
      exact hDrop.1
    have hNewDrop : (Set.range a ∩ Set.range q').ncard <
        (Set.range a ∩ Set.range q).ncard := by
      rw [Set.inter_comm (Set.range a) (Set.range q'),hNewTrace]
      simpa only [Set.inter_comm (Set.range a) (Set.range q)] using hDrop.2
    have hKB : ∀ t, (fun z => K.map (t,z)) '' B = B := by
      intro t
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        change K.map (t,w) ∈ B
        rw [hKfront t w ((hBoundaryFrontier _).mp hw)]
        exact hw
      · intro hz
        exact ⟨z,hz,hKfront t z ((hBoundaryFrontier _).mp hz)⟩
    refine ⟨q',K,?_,hNewDrop⟩
    refine ⟨hq',?_,hq'Interior,?_,hNewFinite,hKB,?_,hq'Range⟩
    · rw [hq'0,hq'1]
      exact hqEnds
    · rw [hq'0,hq'1]
      exact hEndpointSep
    · intro j
      have hFix (z : ↥Q) (hz : z ∈ Set.range (c j)) : K.finalMap z = z :=
        hKfix 1 z (hAvoid (some j) (by simp) z hz)
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        rw [hFix w hw]
        exact hw
      · intro hz
        exact ⟨z,hz,hFix z hz⟩
  have hDescent := regional_actual_interval_half_disk_has_empty_subdisk
    S g hg hS x R hR htarget Q hQcompact hQconnected hbaseQ
    (Set.Subset.rfl) hQregular PEmpty (fun j => PEmpty.elim j)
    (fun j => PEmpty.elim j) (fun j => PEmpty.elim j)
    (by simpa using hFrontier)
    ⟨⟨a,ha,haEnds.1,haEnds.2,
      fun t ht => fun h => haInterior t ht ((hBoundaryFrontier _).mpr h)⟩,haEssential⟩
    ⟨⟨q,hq,hqEnds.1,hqEnds.2,
      fun t ht => fun h => hqInterior t ht ((hBoundaryFrontier _).mpr h)⟩,hqEssential⟩
    (by simpa only [Set.disjoint_insert_left,Set.disjoint_singleton_left,
        Set.mem_insert_iff,Set.mem_singleton_iff,not_or,and_assoc] using hEndpointSep)
    hFinite hCross N d hd hboundary
  rcases hDescent with ⟨M,e,he,heb,hesub,hempty⟩ | ⟨M,e,he,heb,hesub,hempty⟩
  · exact hOrdinaryDrop M e he heb
  · have hClean : Set.range e ∩ (Set.range a ∩ Set.range q) = {M.first 1} := by
      exact regional_empty_three_side_half_disk_whole_contact_cleanup
        S g hg hS x R hR htarget Q hQcompact hQconnected hbaseQ
        (Set.Subset.rfl) hQregular PEmpty (fun j => PEmpty.elim j)
        (fun j => PEmpty.elim j) (fun j => PEmpty.elim j)
        (by simpa using hFrontier)
        ⟨⟨a,ha,haEnds.1,haEnds.2,
          fun t ht => fun h => haInterior t ht ((hBoundaryFrontier _).mpr h)⟩,haEssential⟩
        ⟨⟨q,hq,hqEnds.1,hqEnds.2,
          fun t ht => fun h => hqInterior t ht ((hBoundaryFrontier _).mpr h)⟩,hqEssential⟩
        (by simpa only [Set.disjoint_insert_left,Set.disjoint_singleton_left,
            Set.mem_insert_iff,Set.mem_singleton_iff,not_or,and_assoc] using hEndpointSep)
        hFinite hCross M e he heb hempty
    have hBfree : Disjoint B
        (e '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
      apply Set.disjoint_left.mpr
      rintro y hy ⟨z,hz,rfl⟩
      exact RegionalEmbeddedFamily.embedded_regional_disk_interior_avoids_frontier
        S Q e he z hz ((hBoundaryFrontier _).mp hy)
    have hFirstBoundary (t : Interval) (ht : M.first t ∈ B) : t = 0 := by
      by_contra ht0
      by_cases ht1 : t = 1
      · exact M.corner_off_boundary (ht1 ▸ ht)
      · exact M.first_interior t
          ⟨bot_lt_iff_ne_bot.mpr ht0,lt_top_iff_ne_top.mpr ht1⟩ ht
    have hSecondBoundary (t : Interval) (ht : M.second t ∈ B) : t = 0 := by
      by_contra ht0
      by_cases ht1 : t = 1
      · exact M.corner_off_boundary (M.corner_eq.symm ▸ (ht1 ▸ ht))
      · exact M.second_interior t
          ⟨bot_lt_iff_ne_bot.mpr ht0,lt_top_iff_ne_top.mpr ht1⟩ ht
    have hSideDisk : Set.range M.boundarySide ⊆ Set.range e := by
      intro y hy
      apply Set.image_subset_range e {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}
      rw [heb]
      exact Or.inr hy
    have hDiskBoundary : Set.range e ∩ B ⊆ Set.range M.boundarySide := by
      rintro y ⟨⟨z,rfl⟩,hzB⟩
      have hzSphere : z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
        apply le_antisymm z.property
        apply le_of_not_gt
        intro hz
        exact Set.disjoint_left.mp hBfree hzB ⟨z,hz,rfl⟩
      have hyBoundary : e z ∈ Set.range M.first ∪ Set.range M.second ∪ Set.range M.boundarySide :=
        heb ▸ ⟨z,hzSphere,rfl⟩
      rcases hyBoundary with (hFirst | hSecond) | hThird
      · obtain ⟨t,ht⟩ := hFirst
        have ht0 := hFirstBoundary t (ht.symm ▸ hzB)
        exact ⟨0,M.boundary_zero.trans (ht0 ▸ ht)⟩
      · obtain ⟨t,ht⟩ := hSecond
        have ht0 := hSecondBoundary t (ht.symm ▸ hzB)
        exact ⟨1,M.boundary_one.trans (ht0 ▸ ht)⟩
      · exact hThird
    have hProtectedInteriors : ∀ j,
        Disjoint ((c j) '' Ioo (0 : Interval) 1) (Set.range e) := by
      intro j
      apply essential_proper_arc_avoids_boundary_attached_disk_interior
        Q B (c j) (hc j) (hcEnds j) (hcInterior j)
        (hcEssential j) e he M.boundarySide M.boundary_embedded M.boundary_in_B hSideDisk hDiskBoundary
      rintro y ⟨hy,hybd⟩
      rw [heb] at hybd
      rcases hybd with (hFirst | hSecond) | hThird
      · exact False.elim (Set.disjoint_left.mp (hOff j).1 (M.first_on_a hFirst) hy)
      · exact False.elim (Set.disjoint_left.mp (hOff j).2 (M.second_on_b hSecond) hy)
      · obtain ⟨t,rfl⟩ := hThird
        exact M.boundary_in_B t
    let firstPath : Path (M.first 0) (M.first 1) := ⟨M.first,rfl,rfl⟩
    let secondPath : Path (M.second 0) (M.first 1) := ⟨M.second,rfl,M.corner_eq.symm⟩
    let sideArc : C(Interval,↥Q) := (firstPath.trans secondPath.symm).toContinuousMap
    have hSideArc : IsEmbedding sideArc := by
      apply isEmbedding_path_trans_of_inter_singleton_probe firstPath secondPath.symm
        M.first_embedded (M.second_embedded.comp unitInterval.symmHomeomorph.isEmbedding)
      rw [Path.symm_range]
      exact M.sides_inter
    have hSideArcRange : Set.range sideArc = Set.range M.first ∪ Set.range M.second := by
      change Set.range (firstPath.trans secondPath.symm) = _
      rw [Path.trans_range,Path.symm_range]
      rfl
    have hSideArc0 : sideArc 0 = M.first 0 := (firstPath.trans secondPath.symm).source
    have hSideArc1 : sideArc 1 = M.second 0 := (firstPath.trans secondPath.symm).target
    have hSideArcEnds : sideArc 0 ∈ B ∧ sideArc 1 ∈ B := by
      rw [hSideArc0,hSideArc1]
      exact ⟨M.first_zero_boundary,M.second_zero_boundary⟩
    have hSideArcInterior : ∀ t ∈ Ioo (0 : Interval) 1, sideArc t ∉ B := by
      intro t ht hB
      have hm : sideArc t ∈ Set.range M.first ∪ Set.range M.second :=
        hSideArcRange ▸ Set.mem_range_self t
      rcases hm with ⟨s,hs⟩ | ⟨s,hs⟩
      · have hs0 := hFirstBoundary s (hs.symm ▸ hB)
        have heq : sideArc t = sideArc 0 := hs.symm.trans (hs0 ▸ hSideArc0.symm)
        exact ht.1.ne' (hSideArc.injective heq)
      · have hs0 := hSecondBoundary s (hs.symm ▸ hB)
        have heq : sideArc t = sideArc 1 := hs.symm.trans (hs0 ▸ hSideArc1.symm)
        exact ht.2.ne (hSideArc.injective heq)
    have hSideArcBoundary : e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range sideArc ∪ Set.range M.boundarySide := by
      rw [hSideArcRange]
      exact heb
    have hSideArcClear : Disjoint (Set.range sideArc) (⋃ j, Set.range (c j)) := by
      apply Set.disjoint_left.mpr
      intro y hy hyc
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hyc
      rw [hSideArcRange] at hy
      rcases hy with hy | hy
      · exact Set.disjoint_left.mp (hOff j).1 (M.first_on_a hy) hj
      · exact Set.disjoint_left.mp (hOff j).2 (M.second_on_b hy) hj
    obtain ⟨E,hE,hEcenter,hEends,hEinterior,hEopen⟩ :=
      CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.source_actual_boundary_proper_arc_strip
        S x R g hg hS hR htarget ⟨sideArc,hSideArc,hSideArcEnds.1,hSideArcEnds.2,hSideArcInterior⟩
    obtain ⟨F,p,hF,hp,hFcenter,hFB,hFopen,hFrange⟩ :=
      CoherentEndpointMotion.signed_strip_normalize_with_center B sideArc
        E hE hEcenter hEends hEinterior hEopen
    let G : Set ↥Q := ⋃ j, Set.range (c j)
    have hGclosed : IsClosed G := isClosed_iUnion_of_finite
      (fun j => (isCompact_range (c j).continuous).isClosed)
    have hCenterClear : F '' {z | z.2 ∈ Icc p p} ⊆ Gᶜ := by
      rintro y ⟨z,hz,rfl⟩ hyG
      have hzEq : z.2 = p := le_antisymm hz.2 hz.1
      have hFy : F z = sideArc z.1 := by
        conv_lhs => rw [← Prod.eta z,hzEq]
        exact hFcenter z.1
      exact Set.disjoint_left.mp hSideArcClear (hFy.symm ▸ Set.mem_range_self z.1) hyG
    obtain ⟨l,r,hl0,hlp,hpr,hr1,hBandClear⟩ :=
      CoherentEndpointMotion.compact_strip_band_has_wider_band_in_open
        F Gᶜ hGclosed.isOpen_compl p p hp.1 hp.2 le_rfl hCenterClear
    obtain ⟨zSecond,hzSecond⟩ := M.second_on_b (Set.mem_range_self (0 : Interval))
    have hzSecondB : q zSecond ∈ B := by
      rw [hzSecond]
      exact M.second_zero_boundary
    have hzSecondEndpoint : zSecond = 0 ∨ zSecond = 1 := by
      by_cases hz0 : zSecond = 0
      · exact Or.inl hz0
      by_cases hz1 : zSecond = 1
      · exact Or.inr hz1
      exact (hqInterior zSecond
        ⟨bot_lt_iff_ne_bot.mpr hz0,lt_top_iff_ne_top.mpr hz1⟩ hzSecondB).elim
    obtain ⟨sCorner,hsCorner⟩ := M.second_on_b ⟨(1 : Interval),M.corner_eq.symm⟩
    have hsCornerB : q sCorner ∉ B := by
      rw [hsCorner]
      exact M.corner_off_boundary
    have hsCornerInterior : sCorner ∈ Ioo (0 : Interval) 1 := by
      constructor
      · exact bot_lt_iff_ne_bot.mpr (by
          intro hs0
          exact hsCornerB (hs0 ▸ hqEnds.1))
      · exact lt_top_iff_ne_top.mpr (by
          intro hs1
          exact hsCornerB (hs1 ▸ hqEnds.2))
    have hSecondParamRange : Set.range M.second = q '' Set.uIcc zSecond sCorner := by
      exact (ActualHarerCornerGeometry.embedded_subarc_parameter_interval
        q M.second hq M.second_embedded M.second_on_b zSecond sCorner
        hzSecond (hsCorner.trans M.corner_eq)).2
    obtain ⟨rCorner,hrCorner⟩ := M.first_on_a (Set.mem_range_self (1 : Interval))
    have hrCornerInterior : rCorner ∈ Ioo (0 : Interval) 1 := by
      constructor
      · exact bot_lt_iff_ne_bot.mpr (by
          intro hr0
          apply M.corner_off_boundary
          rw [← hrCorner,hr0]
          exact haEnds.1)
      · exact lt_top_iff_ne_top.mpr (by
          intro hr1
          apply M.corner_off_boundary
          rw [← hrCorner,hr1]
          exact haEnds.2)
    have hCrossCorner :
        RegionalEmbeddedFamily.RegionalTopologicalCrossing Q a q rCorner sCorner := by
      apply hCross rCorner sCorner hrCornerInterior hsCornerInterior
      rw [hrCorner,hsCorner]
    rcases hCrossCorner with ⟨crossChart,hCrossSides⟩
    let ξ : Interval ≃ₜ Interval := if zSecond = 0 then Homeomorph.refl _
      else unitInterval.symmHomeomorph
    have hξ0 : ξ 0 = zSecond := by
      rcases hzSecondEndpoint with hz | hz
      · simp [ξ,hz]
      · simp [ξ,hz]
    have hξ1 : ξ 1 = 0 ∨ ξ 1 = 1 := by
      dsimp [ξ]
      split_ifs <;> simp
    let qOriented : C(Interval,↥Q) := q.comp ⟨ξ,ξ.continuous⟩
    let sOriented : Interval := ξ.symm sCorner
    have hqOriented : IsEmbedding qOriented := hq.comp ξ.isEmbedding
    have hqOriented0 : qOriented 0 = M.second 0 := by
      change q (ξ 0) = M.second 0
      rw [hξ0,hzSecond]
    have hqOrientedCorner : qOriented sOriented = M.first 1 := by
      change q (ξ (ξ.symm sCorner)) = M.first 1
      rw [ξ.apply_symm_apply,hsCorner]
    have hqOrientedEnds : qOriented 0 ∈ B ∧ qOriented 1 ∈ B := by
      refine ⟨hqOriented0.symm ▸ M.second_zero_boundary,?_⟩
      change q (ξ 1) ∈ B
      rcases hξ1 with hξ1 | hξ1
      · rw [hξ1]; exact hqEnds.1
      · rw [hξ1]; exact hqEnds.2
    have hsOriented : sOriented ∈ Ioo (0 : Interval) 1 := by
      have hnB : qOriented sOriented ∉ B := hqOrientedCorner.symm ▸ M.corner_off_boundary
      constructor
      · exact bot_lt_iff_ne_bot.mpr (by intro heq; exact hnB (heq ▸ hqOrientedEnds.1))
      · exact lt_top_iff_ne_top.mpr (by intro heq; exact hnB (heq ▸ hqOrientedEnds.2))
    have hqOrientedRange : Set.range qOriented = Set.range q :=
      ξ.surjective.range_comp q
    have hSecondOrientedRange : Set.range M.second =
        qOriented '' Icc (0 : Interval) sOriented := by
      have hh := (ActualHarerCornerGeometry.embedded_subarc_parameter_interval
        qOriented M.second hqOriented M.second_embedded
        (hqOrientedRange.symm ▸ M.second_on_b) 0 sOriented
        hqOriented0 (hqOrientedCorner.trans M.corner_eq)).2
      simpa only [Set.uIcc_of_le hsOriented.1.le] using hh
    obtain ⟨zFirst,hzFirst⟩ := M.first_on_a (Set.mem_range_self (0 : Interval))
    have hFirstParamRange : Set.range M.first = a '' Set.uIcc zFirst rCorner :=
      (ActualHarerCornerGeometry.embedded_subarc_parameter_interval a M.first ha
        M.first_embedded M.first_on_a zFirst rCorner hzFirst hrCorner).2
    let aS : C(Interval,S) := ⟨fun t => (a t).val,continuous_subtype_val.comp a.continuous⟩
    let qS : C(Interval,S) := ⟨fun t => (q t).val,continuous_subtype_val.comp q.continuous⟩
    have haS : IsEmbedding aS := IsEmbedding.subtypeVal.comp ha
    have hqS : IsEmbedding qS := IsEmbedding.subtypeVal.comp hq
    have hCrossCenterSource : (a rCorner).val ∈ crossChart.chart.source := by
      have hh := crossChart.whole_a_trace.symm ▸ Set.mem_image_of_mem a
        (show rCorner ∈ Icc crossChart.aLeft crossChart.aRight from
          ⟨crossChart.a_cuts.2.1.le,crossChart.a_cuts.2.2.1.le⟩)
      exact hh.1.1
    let crossOpen : Set S := {y | y ∈ crossChart.chart.source ∧
      crossChart.chart y ∈ Schoenflies.Plane.openSquare 0 1}
    have hCrossOpen : IsOpen crossOpen := crossChart.chart.isOpen_inter_preimage
      (Schoenflies.Plane.isOpen_openSquare 0 1)
    let crossRestriction := crossChart.chart.restr crossOpen
    have hCrossRestrictionSource : crossRestriction.source =
        crossChart.chart.source ∩ crossOpen := by
      simp only [crossRestriction,OpenPartialHomeomorph.restr_source,hCrossOpen.interior_eq]
    have hCornerRestriction : qS sCorner ∈ crossRestriction.source := by
      rw [hCrossRestrictionSource]
      change (q sCorner).val ∈ _ ∩ _
      rw [← crossChart.contact]
      refine ⟨hCrossCenterSource,hCrossCenterSource,?_⟩
      rw [crossChart.contact_at_origin,Schoenflies.mem_openSquare_zero_one]
      norm_num [Schoenflies.Plane.supNorm]
    have hRestrictionInterior : crossRestriction.source ⊆ interior Q := by
      intro y hy
      have hy' := (hCrossRestrictionSource ▸ hy).2
      exact crossChart.closed_support_interior
        ⟨hy'.1,Schoenflies.Plane.openSquare_subset_closedSquare 0 1 hy'.2⟩
    have hCrossWhole (y : ↥Q) (hy : y.val ∈ crossChart.chart.source)
        (hySquare : crossChart.chart y.val ∈ Schoenflies.Plane.closedSquare 0 1) :
        y ∈ Set.range a ↔ crossChart.chart y.val 1 = 0 := by
      constructor
      · intro hya
        have hytrace : y ∈ a '' Icc crossChart.aLeft crossChart.aRight :=
          crossChart.whole_a_trace ▸ (show y ∈ _ ∩ Set.range a from ⟨⟨hy,hySquare⟩,hya⟩)
        obtain ⟨u,hu,rfl⟩ := hytrace
        have hh := crossChart.anchor_diameter ▸
          Set.mem_image_of_mem (fun t => crossChart.chart (a t).val) hu
        exact hh.2
      · intro hzero
        have hdiam : crossChart.chart y.val ∈
            (fun t => crossChart.chart (a t).val) '' Icc crossChart.aLeft crossChart.aRight :=
          crossChart.anchor_diameter.symm ▸ ⟨hySquare,hzero⟩
        obtain ⟨u,hu,heq⟩ := hdiam
        have hau := crossChart.whole_a_trace.symm ▸ Set.mem_image_of_mem a hu
        exact ⟨u,Subtype.ext (crossChart.chart.injOn hau.1.1 hy heq)⟩
    have hRestrictionAxis : ∀ y ∈ crossRestriction.source,
        y ∈ Set.range aS ↔ crossRestriction y 1 = 0 := by
      intro y hy
      have hyOpen := (hCrossRestrictionSource ▸ hy).2
      let yQ : ↥Q := ⟨y,interior_subset (hRestrictionInterior hy)⟩
      have hh := hCrossWhole yQ hyOpen.1
        (Schoenflies.Plane.openSquare_subset_closedSquare 0 1 hyOpen.2)
      constructor
      · rintro ⟨u,hu⟩
        exact hh.mp ⟨u,Subtype.ext hu⟩
      · intro hz
        obtain ⟨u,hu⟩ := hh.mpr hz
        exact ⟨u,congrArg Subtype.val hu⟩
    have hCornerNotGraph : (M.first 1).val ∉ Subtype.val '' G := by
      rintro ⟨y,hy,heq⟩
      have hyEq : y = M.first 1 := Subtype.ext heq
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hy
      exact Set.disjoint_left.mp (hOff j).1
        (M.first_on_a (Set.mem_range_self 1)) (hyEq ▸ hj)
    have hCornerNotBoundarySide : (M.first 1).val ∉
        Set.range (fun t : Interval => (M.boundarySide t).val) := by
      rintro ⟨t,ht⟩
      exact M.corner_off_boundary ((Subtype.ext ht : M.boundarySide t = M.first 1) ▸
        M.boundary_in_B t)
    let cornerNeighborhood : Set S := interior Q ∩ (Subtype.val '' G)ᶜ ∩
      (Set.range (fun t : Interval => (M.boundarySide t).val))ᶜ
    have hCornerNeighborhoodOpen : IsOpen cornerNeighborhood := by
      letI : CompactSpace ↥Q := isCompact_iff_compactSpace.mp hQcompact
      exact (isOpen_interior.inter
        (hGclosed.isCompact.image continuous_subtype_val).isClosed.isOpen_compl).inter
          (isCompact_range (continuous_subtype_val.comp M.boundarySide.continuous)).isClosed.isOpen_compl
    have hCornerNeighborhood : qS sCorner ∈ cornerNeighborhood := by
      refine ⟨⟨hRestrictionInterior hCornerRestriction,?_⟩,?_⟩
      · change (q sCorner).val ∉ Subtype.val '' G
        rw [hsCorner]; exact hCornerNotGraph
      · change (q sCorner).val ∉ Set.range (fun t : Interval => (M.boundarySide t).val)
        rw [hsCorner]; exact hCornerNotBoundarySide
    have hqRestrictionNhds : qS ⁻¹' crossRestriction.source ∈ 𝓝 sCorner :=
      qS.continuous.continuousAt.preimage_mem_nhds
        (crossRestriction.open_source.mem_nhds hCornerRestriction)
    obtain ⟨Lcut,Rcut,hsCuts,hCutsRestriction⟩ :=
      (mem_nhds_iff_exists_Ioo_subset'
        ⟨crossChart.bLeft,crossChart.b_cuts.2.1⟩
        ⟨crossChart.bRight,crossChart.b_cuts.2.2.1⟩).mp hqRestrictionNhds
    obtain ⟨axisLeft,hAxisLeft⟩ := exists_between (max_lt hsCuts.1 crossChart.b_cuts.2.1)
    obtain ⟨axisRight,hAxisRight⟩ := exists_between (lt_min hsCuts.2 crossChart.b_cuts.2.2.1)
    have hAxisWindow : ∀ u ∈ Icc axisLeft axisRight, qS u ∈ crossRestriction.source := by
      intro u hu
      exact hCutsRestriction ⟨(lt_of_le_of_lt (le_max_left _ _) hAxisLeft.1).trans_le hu.1,
        hu.2.trans_lt (hAxisRight.2.trans_le (min_le_left _ _))⟩
    have hAxisSigns : ∃ ε : ℝ, (ε = -1 ∨ ε = 1) ∧
        (∀ u ∈ Ico axisLeft sCorner, ε * crossRestriction (qS u) 1 < 0) ∧
        (∀ u ∈ Ioc sCorner axisRight, 0 < ε * crossRestriction (qS u) 1) := by
      rcases hCrossSides with ⟨hLeft,hRight⟩ | ⟨hLeft,hRight⟩
      · refine ⟨-1,Or.inl rfl,?_,?_⟩
        · intro u hu
          have hh := hLeft u ⟨(lt_of_le_of_lt (le_max_right _ _) hAxisLeft.1).trans_le hu.1,hu.2⟩
          change -1 * crossChart.chart (q u).val 1 < 0
          linarith
        · intro u hu
          have hh := hRight u ⟨hu.1,hu.2.trans_lt (hAxisRight.2.trans_le (min_le_right _ _))⟩
          change 0 < -1 * crossChart.chart (q u).val 1
          linarith
      · refine ⟨1,Or.inr rfl,?_,?_⟩
        · intro u hu
          have hh := hLeft u ⟨(lt_of_le_of_lt (le_max_right _ _) hAxisLeft.1).trans_le hu.1,hu.2⟩
          change 1 * crossChart.chart (q u).val 1 < 0
          simpa only [one_mul] using hh
        · intro u hu
          have hh := hRight u ⟨hu.1,hu.2.trans_lt (hAxisRight.2.trans_le (min_le_right _ _))⟩
          change 0 < 1 * crossChart.chart (q u).val 1
          simpa only [one_mul] using hh
    obtain ⟨axisSign,hAxisSign,hAxisBefore,hAxisAfter⟩ := hAxisSigns
    obtain ⟨cornerAxes,hCornerAxesSub,hCornerAxes⟩ :=
      ActualHarerCornerGeometry.actual_opposite_signed_arc_germs_construct_whole_pair_axis_chart
        S qS aS hqS haS sCorner rCorner axisLeft axisRight crossRestriction axisSign
        cornerNeighborhood hsCornerInterior hrCornerInterior
        (congrArg Subtype.val crossChart.contact.symm)
        hAxisLeft.2 hAxisRight.1 hAxisSign hCornerRestriction hCornerNeighborhoodOpen
        hCornerNeighborhood hRestrictionAxis hAxisWindow hAxisBefore hAxisAfter
    let firstS : C(Interval,S) :=
      ⟨fun t => (M.first t).val,continuous_subtype_val.comp M.first.continuous⟩
    let secondS : C(Interval,S) :=
      ⟨fun t => (M.second t).val,continuous_subtype_val.comp M.second.continuous⟩
    let boundaryS : C(Interval,S) :=
      ⟨fun t => (M.boundarySide t).val,continuous_subtype_val.comp M.boundarySide.continuous⟩
    let diskS : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
      ⟨fun z => (e z).val,continuous_subtype_val.comp e.continuous⟩
    have hFirstS : IsEmbedding firstS := IsEmbedding.subtypeVal.comp M.first_embedded
    have hSecondS : IsEmbedding secondS := IsEmbedding.subtypeVal.comp M.second_embedded
    have hDiskS : IsEmbedding diskS := IsEmbedding.subtypeVal.comp he
    have hFirstOnAS : Set.range firstS ⊆ Set.range aS := by
      rintro y ⟨t,rfl⟩
      obtain ⟨u,hu⟩ := M.first_on_a (Set.mem_range_self t)
      exact ⟨u,congrArg Subtype.val hu⟩
    have hSecondOnQS : Set.range secondS ⊆ Set.range qS := by
      rintro y ⟨t,rfl⟩
      obtain ⟨u,hu⟩ := M.second_on_b (Set.mem_range_self t)
      exact ⟨u,congrArg Subtype.val hu⟩
    have hQS0 : qS zSecond = secondS 0 := congrArg Subtype.val hzSecond
    have hQS1 : qS sCorner = secondS 1 := congrArg Subtype.val (hsCorner.trans M.corner_eq)
    have hAS0 : aS zFirst = firstS 0 := congrArg Subtype.val hzFirst
    have hAS1 : aS rCorner = firstS 1 := congrArg Subtype.val hrCorner
    obtain ⟨secondGerm,hSecondGermOpen,hSecondGermCenter,hSecondGermSub,hSecondGerm⟩ :=
      ActualHarerCornerGeometry.endpoint_ordered_subarc_germ qS secondS hqS hSecondS
        hSecondOnQS zSecond sCorner hQS0 hQS1 1 (Or.inr rfl)
        cornerAxes 0 1 hCornerAxes.anchor_axis
        (by simpa [ActualHarerCornerGeometry.endpointParameter] using hCornerAxes.center_mem)
        (by simpa [ActualHarerCornerGeometry.endpointParameter] using
          (fun u hu => (hCornerAxes.anchor_order u hu).2))
    obtain ⟨firstGerm,hFirstGermOpen,hFirstGermCenter,hFirstGermSub,hFirstGerm⟩ :=
      ActualHarerCornerGeometry.endpoint_ordered_subarc_germ aS firstS haS hFirstS
        hFirstOnAS zFirst rCorner hAS0 hAS1 1 (Or.inr rfl)
        cornerAxes 1 0 hCornerAxes.moving_axis
        (by have hcenter : aS rCorner = qS sCorner :=
              congrArg Subtype.val (hrCorner.trans hsCorner.symm)
            simpa only [ActualHarerCornerGeometry.endpointParameter,one_ne_zero,if_false,hcenter] using hCornerAxes.center_mem)
        (by simpa [ActualHarerCornerGeometry.endpointParameter] using hCornerAxes.moving_order)
    let cornerGerm : Set S := secondGerm ∩ firstGerm
    have hCornerGermOpen : IsOpen cornerGerm := hSecondGermOpen.inter hFirstGermOpen
    have hCornerGermSub : cornerGerm ⊆ cornerAxes.source := fun y hy => hSecondGermSub hy.1
    have hCornerGermCenter : (M.first 1).val ∈ cornerGerm := by
      refine ⟨?_,hFirstGermCenter⟩
      change (M.first 1).val ∈ secondGerm
      rw [M.corner_eq]
      exact hSecondGermCenter
    have hAxesCornerZero : cornerAxes (M.first 1).val = 0 := by
      rw [← hsCorner]
      exact hCornerAxes.center_zero
    have hCornerGermImageOpen : IsOpen (cornerAxes '' cornerGerm) :=
      cornerAxes.isOpen_image_of_subset_source hCornerGermOpen hCornerGermSub
    obtain ⟨cornerRadius,hCornerRadius,hCornerRadiusOne,hCornerSquareGerm⟩ :=
      ActualHarerCornerGeometry.small_closed_square_in_open
        (cornerAxes '' cornerGerm) hCornerGermImageOpen
        ⟨(M.first 1).val,hCornerGermCenter,hAxesCornerZero⟩
    have hCornerSquareTarget : Schoenflies.Plane.closedSquare 0 cornerRadius ⊆ cornerAxes.target := by
      intro z hz
      obtain ⟨y,hy,rfl⟩ := hCornerSquareGerm hz
      exact cornerAxes.map_source (hCornerGermSub hy)
    have hCornerSquare (z : Schoenflies.Plane) (hx : |z 0| < cornerRadius)
        (hy : |z 1| < cornerRadius) : z ∈ Schoenflies.Plane.closedSquare 0 cornerRadius := by
      simp only [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist,
        Schoenflies.Plane.supNorm,sub_zero,Set.mem_setOf_eq,max_le_iff]
      exact ⟨hx.le,hy.le⟩
    have hInverseInGerm (z : Schoenflies.Plane) (hx : |z 0| < cornerRadius)
        (hy : |z 1| < cornerRadius) : cornerAxes.symm z ∈ cornerGerm := by
      obtain ⟨y,hyG,hyz⟩ := hCornerSquareGerm (hCornerSquare z hx hy)
      rw [← hyz,cornerAxes.left_inv (hCornerGermSub hyG)]
      exact hyG
    let σq := ActualHarerCornerGeometry.inwardParameterSign 1 zSecond sCorner
    let σa := ActualHarerCornerGeometry.inwardParameterSign 1 zFirst rCorner
    have hσq : σq = -1 ∨ σq = 1 := by
      dsimp [σq,ActualHarerCornerGeometry.inwardParameterSign]
      split_ifs <;> simp
    have hσa : σa = -1 ∨ σa = 1 := by
      dsimp [σa,ActualHarerCornerGeometry.inwardParameterSign]
      split_ifs <;> simp
    have hSecondRay (z : Schoenflies.Plane) (hx : |z 0| < cornerRadius)
        (hy : |z 1| < cornerRadius) :
        cornerAxes.symm z ∈ Set.range secondS ↔ z 1 = 0 ∧ 0 ≤ σq * z 0 := by
      have hh := hSecondGerm (cornerAxes.symm z) (hInverseInGerm z hx hy).1
      rwa [cornerAxes.right_inv (hCornerSquareTarget (hCornerSquare z hx hy))] at hh
    have hFirstRay (z : Schoenflies.Plane) (hx : |z 0| < cornerRadius)
        (hy : |z 1| < cornerRadius) :
        cornerAxes.symm z ∈ Set.range firstS ↔ z 0 = 0 ∧ 0 ≤ σa * z 1 := by
      have hh := hFirstGerm (cornerAxes.symm z) (hInverseInGerm z hx hy).2
      rwa [cornerAxes.right_inv (hCornerSquareTarget (hCornerSquare z hx hy))] at hh
    have hDiskSBoundary : diskS '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range firstS ∪ Set.range secondS ∪ Set.range boundaryS := by
      change (Subtype.val ∘ e) '' _ = Set.range (Subtype.val ∘ M.first) ∪
        Set.range (Subtype.val ∘ M.second) ∪ Set.range (Subtype.val ∘ M.boundarySide)
      rw [Set.image_comp,heb,Set.image_union,Set.image_union,
        Set.range_comp,Set.range_comp,Set.range_comp]
    have hDiskSFrontier : frontier (Set.range diskS) =
        Set.range firstS ∪ Set.range secondS ∪ Set.range boundaryS := by
      rw [ActualHarerCornerGeometry.embedded_disk_frontier_image diskS hDiskS,hDiskSBoundary]
    have hCornerOffBoundaryS (y : S) (hy : y ∈ cornerAxes.source) : y ∉ Set.range boundaryS :=
      (hCornerAxesSub hy).2.2
    have hFrontierRays (z : Schoenflies.Plane) (hx : |z 0| < cornerRadius)
        (hy : |z 1| < cornerRadius) :
        cornerAxes.symm z ∈ frontier (Set.range diskS) ↔
          (z 1 = 0 ∧ 0 ≤ σq * z 0) ∨ (z 0 = 0 ∧ 0 ≤ σa * z 1) := by
      rw [hDiskSFrontier,Set.mem_union,Set.mem_union,hFirstRay z hx hy,hSecondRay z hx hy]
      have hn := hCornerOffBoundaryS (cornerAxes.symm z)
        (cornerAxes.map_target (hCornerSquareTarget (hCornerSquare z hx hy)))
      simp only [hn,or_false]
      exact or_comm
    have hNegativeCorner : cornerAxes.symm (Schoenflies.Plane.mk (σq * (-cornerRadius/2)) 0) ∉
        Set.range diskS := by
      let z := Schoenflies.Plane.mk (σq * (-cornerRadius/2)) 0
      have hx : |z 0| < cornerRadius := by
        change |σq * (-cornerRadius/2)| < cornerRadius
        rcases hσq with hs | hs <;> rw [hs] <;> simp only [neg_one_mul,one_mul,abs_neg]
        all_goals rw [abs_of_neg (by linarith : -cornerRadius/2 < 0)]; linarith
      have hy : |z 1| < cornerRadius := by simpa [z] using hCornerRadius
      have hzTarget := hCornerSquareTarget (hCornerSquare z hx hy)
      have hzSource := cornerAxes.map_target hzTarget
      have hzQ : cornerAxes.symm z ∈ Set.range qS := by
        apply (hCornerAxes.anchor_axis _ hzSource).mpr
        rw [cornerAxes.right_inv hzTarget]
        rfl
      have hzNotSecond : cornerAxes.symm z ∉ Set.range secondS := by
        intro hh
        have hsign := ((hSecondRay z hx hy).mp hh).2
        have hsquare : σq * σq = 1 := by rcases hσq with hs | hs <;> norm_num [hs]
        change 0 ≤ σq * (σq * (-cornerRadius/2)) at hsign
        rw [← mul_assoc,hsquare,one_mul] at hsign
        linarith
      have hzNotFirst : cornerAxes.symm z ∉ Set.range firstS := by
        intro hh
        have hxzero := ((hFirstRay z hx hy).mp hh).1
        change σq * (-cornerRadius/2) = 0 at hxzero
        rcases hσq with hs | hs <;> rw [hs] at hxzero <;> nlinarith
      intro hzD
      obtain ⟨w,hw⟩ := hzD
      obtain ⟨u,hu⟩ := hzQ
      have hqu : q u = e w := Subtype.ext (hu.trans hw.symm)
      have hwSphere : w.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
        apply le_antisymm w.property
        apply le_of_not_gt
        intro hwBall
        exact Set.disjoint_left.mp hempty ⟨w,hwBall,rfl⟩ (Or.inr ⟨u,hqu⟩)
      have hh : cornerAxes.symm z ∈ Set.range firstS ∪ Set.range secondS ∪ Set.range boundaryS :=
        hDiskSBoundary ▸ ⟨w,hwSphere,hw⟩
      rcases hh with (hh | hh) | hh
      · exact hzNotFirst hh
      · exact hzNotSecond hh
      · exact hCornerOffBoundaryS _ hzSource hh
    have hSameDiskQuadrant := ActualHarerCornerGeometry.signed_corner_closed_regular_set
      cornerAxes (Set.range diskS) (isCompact_range diskS.continuous).isClosed
      (by rw [CurveComplex.actual_embedded_disk_closure_interior diskS hDiskS])
      cornerRadius σq σa hCornerRadius hσq hσa
      (fun z hx hy => hCornerSquareTarget (hCornerSquare z hx hy))
      hFrontierRays hNegativeCorner
    have hOrientedOutgoingClear (u : Interval) (hsu : sOriented < u)
        (huSource : (qOriented u).val ∈ cornerAxes.source)
        (hu0 : |cornerAxes (qOriented u).val 0| < cornerRadius)
        (hu1 : |cornerAxes (qOriented u).val 1| < cornerRadius) :
        qOriented u ∉ Set.range e ∪ Set.range a := by
      let z := cornerAxes (qOriented u).val
      have hInverse : cornerAxes.symm z = (qOriented u).val := cornerAxes.left_inv huSource
      have hOnQ : (qOriented u).val ∈ Set.range qS := ⟨ξ u,rfl⟩
      have hHorizontal : z 1 = 0 := (hCornerAxes.anchor_axis _ huSource).mp hOnQ
      have hNotSecond : (qOriented u).val ∉ Set.range secondS := by
        rintro ⟨v,hv⟩
        have huSecond : qOriented u ∈ Set.range M.second := ⟨v,Subtype.ext hv⟩
        rw [hSecondOrientedRange] at huSecond
        obtain ⟨w,hw,hwu⟩ := huSecond
        exact (not_le_of_gt hsu) (hqOriented.injective hwu ▸ hw.2)
      rintro (huDisk | huA)
      · have huDiskS : (qOriented u).val ∈ Set.range diskS := by
          obtain ⟨v,hv⟩ := huDisk
          exact ⟨v,congrArg Subtype.val hv⟩
        have hsign := ((hSameDiskQuadrant z hu0 hu1).mp (hInverse.symm ▸ huDiskS)).1
        exact hNotSecond (hInverse ▸ (hSecondRay z hu0 hu1).mpr ⟨hHorizontal,hsign⟩)
      · have huAS : (qOriented u).val ∈ Set.range aS := by
          obtain ⟨v,hv⟩ := huA
          exact ⟨v,congrArg Subtype.val hv⟩
        have hVertical : z 0 = 0 := (hCornerAxes.moving_axis _ huSource).mp huAS
        have hz0 : z = 0 := by
          ext i
          fin_cases i
          · exact hVertical
          · exact hHorizontal
        have hCornerSource : (M.first 1).val ∈ cornerAxes.source := by
          rw [← hsCorner]
          exact hCornerAxes.center_mem
        have huCorner : qOriented u = M.first 1 := Subtype.ext
          (cornerAxes.injOn huSource hCornerSource (hz0.trans hAxesCornerZero.symm))
        exact (ne_of_gt hsu) (hqOriented.injective (huCorner.trans hqOrientedCorner.symm))
    have hH1Tail (W : Set ↥Q) (hW : IsOpen W) (hDiskW : Set.range e ⊆ W) :
        ∃ t : Interval, sOriented < t ∧ t < 1 ∧
          qOriented '' Icc (0 : Interval) t ⊆ W ∧
          Disjoint (qOriented '' Ioc sOriented t) (Set.range e ∪ Set.range a) ∧
          (∀ u ∈ Icc sOriented t, (qOriented u).val ∈ cornerAxes.source ∧
            |cornerAxes (qOriented u).val 0| < cornerRadius ∧
            |cornerAxes (qOriented u).val 1| < cornerRadius) := by
      let V : Set S := {y | y ∈ cornerAxes.source ∧
        cornerAxes y ∈ Schoenflies.Plane.openSquare 0 cornerRadius}
      have hV : IsOpen V := cornerAxes.isOpen_inter_preimage
        (Schoenflies.Plane.isOpen_openSquare 0 cornerRadius)
      have hCornerV : (qOriented sOriented).val ∈ V := by
        rw [hqOrientedCorner]
        refine ⟨hCornerGermSub hCornerGermCenter,?_⟩
        rw [hAxesCornerZero]
        simpa only [Schoenflies.Plane.openSquare,Schoenflies.Plane.supDist,
          Schoenflies.Plane.supNorm,sub_zero,Set.mem_setOf_eq,PiLp.zero_apply,
          abs_zero,max_self] using hCornerRadius
      have hSecondDisk : Set.range M.second ⊆ Set.range e := by
        intro y hy
        apply Set.image_subset_range e {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}
        rw [heb]
        exact Or.inl (Or.inr hy)
      have hCornerW : qOriented sOriented ∈ W :=
        hDiskW (hSecondDisk ⟨1,M.corner_eq.symm.trans hqOrientedCorner.symm⟩)
      have hLocalOpen : IsOpen (W ∩ Subtype.val ⁻¹' V) :=
        hW.inter (hV.preimage continuous_subtype_val)
      have hLocalNhds : qOriented ⁻¹' (W ∩ Subtype.val ⁻¹' V) ∈ 𝓝 sOriented :=
        qOriented.continuous.continuousAt.preimage_mem_nhds
          (hLocalOpen.mem_nhds ⟨hCornerW,hCornerV⟩)
      obtain ⟨uLeft,uRight,hsWindow,hWindow⟩ :=
        (mem_nhds_iff_exists_Ioo_subset' ⟨0,hsOriented.1⟩ ⟨1,hsOriented.2⟩).mp hLocalNhds
      obtain ⟨t,hst,ht⟩ := exists_between (lt_min hsWindow.2 hsOriented.2)
      have htOne : t < 1 := ht.trans_le (min_le_right _ _)
      have hClosedWindow : ∀ u ∈ Icc sOriented t,
          qOriented u ∈ W ∩ Subtype.val ⁻¹' V := by
        intro u hu
        exact hWindow ⟨hsWindow.1.trans_le hu.1,hu.2.trans_lt (ht.trans_le (min_le_left _ _))⟩
      have hCoords : ∀ u ∈ Icc sOriented t, (qOriented u).val ∈ cornerAxes.source ∧
          |cornerAxes (qOriented u).val 0| < cornerRadius ∧
          |cornerAxes (qOriented u).val 1| < cornerRadius := by
        intro u hu
        have hh := (hClosedWindow u hu).2
        refine ⟨hh.1,?_⟩
        have hcoord := hh.2
        simpa only [Schoenflies.Plane.openSquare,Schoenflies.Plane.supDist,
          Schoenflies.Plane.supNorm,sub_zero,Set.mem_setOf_eq,max_lt_iff] using hcoord
      refine ⟨t,hst,htOne,?_,?_,hCoords⟩
      · rintro y ⟨u,hu,rfl⟩
        by_cases hus : u ≤ sOriented
        · exact hDiskW (hSecondDisk (hSecondOrientedRange.symm ▸ ⟨u,⟨hu.1,hus⟩,rfl⟩))
        · exact (hClosedWindow u ⟨(lt_of_not_ge hus).le,hu.2⟩).1
      · apply Set.disjoint_left.mpr
        rintro y ⟨u,hu,rfl⟩ hy
        have hh := hCoords u ⟨hu.1.le,hu.2⟩
        exact hOrientedOutgoingClear u hu.1 hh.1 hh.2.1 hh.2.2 hy
    have hDiskBoundaryExact : Set.range e ∩ B = Set.range M.boundarySide := by
      apply Set.Subset.antisymm hDiskBoundary
      rintro y ⟨u,rfl⟩
      exact ⟨hSideDisk (Set.mem_range_self u),M.boundary_in_B u⟩
    have hBoundaryRelativeInterior : M.boundarySide '' Ioo (0 : Interval) 1 ⊆
        interior (Set.range e : Set ↥Q) :=
      original_half_disk_boundary_side_relative_open
        S g hg hS x R hR htarget a q M e he heb hDiskBoundaryExact
    have hRangeClosure (f : C(Interval,↥Q)) : Set.range f ⊆
        closure (f '' Ioo (0 : Interval) 1) := by
      rintro y ⟨u,rfl⟩
      apply image_closure_subset_closure_image f.continuous
      refine ⟨u,?_,rfl⟩
      rw [closure_Ioo (zero_ne_one : (0 : Interval) ≠ 1)]
      exact ⟨bot_le,le_top⟩
    have hInteriorContactClosure (f : C(Interval,↥Q)) (A : Set ↥Q)
        (hA : IsClosed A)
        (hMidA : ∀ u ∈ Ioo (0 : Interval) 1, f u ∈ Set.range e → f u ∈ A) :
        ∀ u : Interval, f u ∈ interior (Set.range e : Set ↥Q) → f u ∈ A := by
      have hSub : f '' Ioo (0 : Interval) 1 ⊆ (interior (Set.range e : Set ↥Q))ᶜ ∪ A := by
        rintro y ⟨u,hu,rfl⟩
        by_cases hi : f u ∈ interior (Set.range e : Set ↥Q)
        · exact Or.inr (hMidA u hu (interior_subset hi))
        · exact Or.inl hi
      have hClosure := closure_minimal hSub (isOpen_interior.isClosed_compl.union hA)
      intro u hu
      rcases hClosure (hRangeClosure f (Set.mem_range_self u)) with hn | hA
      · exact (hn hu).elim
      · exact hA
    have hProtectedNoRelativeInterior (j : J) (u : Interval) :
        c j u ∉ interior (Set.range e : Set ↥Q) := by
      intro hu
      have hh := hInteriorContactClosure (c j) ∅ isClosed_empty
        (fun v hv hvD => (Set.disjoint_left.mp (hProtectedInteriors j) ⟨v,hv,rfl⟩ hvD).elim) u hu
      exact hh
    have hProtectedBoundarySide (j : J) (u : Interval) (hu : u = 0 ∨ u = 1) :
        c j u ∉ Set.range M.boundarySide := by
      rintro ⟨v,hv⟩
      by_cases hv0 : v = 0
      · have hSelected : c j u ∈ Set.range a := by
          rw [← hv,hv0,M.boundary_zero]
          exact M.first_on_a (Set.mem_range_self 0)
        exact Set.disjoint_left.mp (hOff j).1 hSelected (Set.mem_range_self u)
      by_cases hv1 : v = 1
      · have hSelected : c j u ∈ Set.range q := by
          rw [← hv,hv1,M.boundary_one]
          exact M.second_on_b (Set.mem_range_self 0)
        exact Set.disjoint_left.mp (hOff j).2 hSelected (Set.mem_range_self u)
      exact hProtectedNoRelativeInterior j u
        (hBoundaryRelativeInterior ⟨v,⟨bot_lt_iff_ne_bot.mpr hv0,lt_top_iff_ne_top.mpr hv1⟩,hv⟩)
    have hDiskProtected : ∀ j, Disjoint (Set.range e) (Set.range (c j)) := by
      intro j
      apply Set.disjoint_right.mpr
      rintro y ⟨u,rfl⟩ huD
      by_cases hu0 : u = 0
      · have huB : c j u ∈ B := hu0 ▸ (hcEnds j).1
        exact hProtectedBoundarySide j u (Or.inl hu0) (hDiskBoundary ⟨huD,huB⟩)
      by_cases hu1 : u = 1
      · have huB : c j u ∈ B := hu1 ▸ (hcEnds j).2
        exact hProtectedBoundarySide j u (Or.inr hu1) (hDiskBoundary ⟨huD,huB⟩)
      exact Set.disjoint_left.mp (hProtectedInteriors j)
        ⟨u,⟨bot_lt_iff_ne_bot.mpr hu0,lt_top_iff_ne_top.mpr hu1⟩,rfl⟩ huD
    have hWholeDiskBoundary (y : ↥Q) (hyD : y ∈ Set.range e)
        (hyAQ : y ∈ Set.range a ∪ Set.range q) :
        y ∈ Set.range M.first ∪ Set.range M.second ∪ Set.range M.boundarySide := by
      obtain ⟨z,rfl⟩ := hyD
      have hzSphere : z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
        apply le_antisymm z.property
        apply le_of_not_gt
        intro hzBall
        exact Set.disjoint_left.mp hempty ⟨z,hzBall,rfl⟩ hyAQ
      exact heb ▸ ⟨z,hzSphere,rfl⟩
    have hDiskContactFirst (y : ↥Q) (hyD : y ∈ Set.range e)
        (hya : y ∈ Set.range a) (hyq : y ∈ Set.range q) : y = M.first 1 := by
      exact Set.mem_singleton_iff.mp (hClean ▸ ⟨hyD,hya,hyq⟩)
    have hFirstMid (u : Interval) (hu : u ∈ Ioo (0 : Interval) 1)
        (huD : a u ∈ Set.range e) : a u ∈ Set.range M.first := by
      rcases hWholeDiskBoundary (a u) huD (Or.inl (Set.mem_range_self u)) with (hFirst | hSecond) | hSide
      · exact hFirst
      · exact ⟨1,(hDiskContactFirst _ huD (Set.mem_range_self u) (M.second_on_b hSecond)).symm⟩
      · obtain ⟨v,hv⟩ := hSide
        exact (haInterior u hu (hv ▸ M.boundary_in_B v)).elim
    have hSecondMid (u : Interval) (hu : u ∈ Ioo (0 : Interval) 1)
        (huD : q u ∈ Set.range e) : q u ∈ Set.range M.second := by
      rcases hWholeDiskBoundary (q u) huD (Or.inr (Set.mem_range_self u)) with (hFirst | hSecond) | hSide
      · exact ⟨1,M.corner_eq.symm.trans
          (hDiskContactFirst _ huD (M.first_on_a hFirst) (Set.mem_range_self u)).symm⟩
      · exact hSecond
      · obtain ⟨v,hv⟩ := hSide
        exact (hqInterior u hu (hv ▸ M.boundary_in_B v)).elim
    have hFirstClosure := hInteriorContactClosure a (Set.range M.first)
      (isCompact_range M.first.continuous).isClosed hFirstMid
    have hSecondClosure := hInteriorContactClosure q (Set.range M.second)
      (isCompact_range M.second.continuous).isClosed hSecondMid
    have hWholeFirstExact : Set.range e ∩ Set.range a = Set.range M.first := by
      apply Set.Subset.antisymm
      · rintro y ⟨hyD,⟨u,rfl⟩⟩
        rcases hWholeDiskBoundary (a u) hyD (Or.inl (Set.mem_range_self u)) with (hFirst | hSecond) | hSide
        · exact hFirst
        · exact ⟨1,(hDiskContactFirst _ hyD (Set.mem_range_self u) (M.second_on_b hSecond)).symm⟩
        · obtain ⟨v,hv⟩ := hSide
          by_cases hv0 : v = 0
          · exact ⟨0,M.boundary_zero.symm.trans (hv0 ▸ hv)⟩
          by_cases hv1 : v = 1
          · have hSecond : a u ∈ Set.range M.second :=
              ⟨0,M.boundary_one.symm.trans (hv1 ▸ hv)⟩
            exact ⟨1,(hDiskContactFirst _ hyD (Set.mem_range_self u) (M.second_on_b hSecond)).symm⟩
          exact hFirstClosure u (hBoundaryRelativeInterior
            ⟨v,⟨bot_lt_iff_ne_bot.mpr hv0,lt_top_iff_ne_top.mpr hv1⟩,hv⟩)
      · intro y hy
        refine ⟨?_,M.first_on_a hy⟩
        apply Set.image_subset_range e {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}
        rw [heb]
        exact Or.inl (Or.inl hy)
    have hWholeSecondExact : Set.range e ∩ Set.range q = Set.range M.second := by
      apply Set.Subset.antisymm
      · rintro y ⟨hyD,⟨u,rfl⟩⟩
        rcases hWholeDiskBoundary (q u) hyD (Or.inr (Set.mem_range_self u)) with (hFirst | hSecond) | hSide
        · exact ⟨1,M.corner_eq.symm.trans
            (hDiskContactFirst _ hyD (M.first_on_a hFirst) (Set.mem_range_self u)).symm⟩
        · exact hSecond
        · obtain ⟨v,hv⟩ := hSide
          by_cases hv0 : v = 0
          · have hFirst : q u ∈ Set.range M.first :=
              ⟨0,M.boundary_zero.symm.trans (hv0 ▸ hv)⟩
            exact ⟨1,M.corner_eq.symm.trans
              (hDiskContactFirst _ hyD (M.first_on_a hFirst) (Set.mem_range_self u)).symm⟩
          by_cases hv1 : v = 1
          · exact ⟨0,M.boundary_one.symm.trans (hv1 ▸ hv)⟩
          exact hSecondClosure u (hBoundaryRelativeInterior
            ⟨v,⟨bot_lt_iff_ne_bot.mpr hv0,lt_top_iff_ne_top.mpr hv1⟩,hv⟩)
      · intro y hy
        refine ⟨?_,M.second_on_b hy⟩
        apply Set.image_subset_range e {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}
        rw [heb]
        exact Or.inl (Or.inr hy)
    have hDiskGraph : Disjoint (Set.range e) G := by
      apply Set.disjoint_left.mpr
      intro y hyD hyG
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hyG
      exact Set.disjoint_left.mp (hDiskProtected j) hyD hj
    let supportW : Set ↥Q := Gᶜ
    have hSupportWOpen : IsOpen supportW := hGclosed.isOpen_compl
    have hDiskSupportW : Set.range e ⊆ supportW := by
      intro y hyD hyG
      exact Set.disjoint_left.mp hDiskGraph hyD hyG
    have hSupportWGraph : Disjoint supportW G := disjoint_compl_left
    obtain ⟨tailEnd,hTailStart,hTailEnd,hTailSupport,hTailClear,hTailCoordinates⟩ :=
      hH1Tail supportW hSupportWOpen hDiskSupportW
    have hCellConsumer
        (cell : C(Interval × Interval,↥Q)) (hCell : IsEmbedding cell)
        (hCellBoundary : ∀ z, cell z ∈ B ↔ z.1 = 0)
        (hCellOpen : IsOpen (cell '' {z | z.1 < 1 ∧ z.2 ∈ Ioo (0 : Interval) 1}))
        (hCellSupport : Set.range cell ⊆ supportW)
        (old new : C(Interval,Interval × Interval))
        (hOld : IsEmbedding old) (hNew : IsEmbedding new)
        (hOldZero : (old 0).1 = 0) (hNewZero : (new 0).1 = 0)
        (hFar : old 1 = new 1) (hOldOne : (old 1).1 = 1)
        (hOldZeroWidth : (old 0).2 ∈ Ioo (0 : Interval) 1)
        (hNewZeroWidth : (new 0).2 ∈ Ioo (0 : Interval) 1)
        (hFarWidth : (old 1).2 ∈ Ioo (0 : Interval) 1)
        (hOldInterior : ∀ u ∈ Ioo (0 : Interval) 1,
          (old u).1 ∈ Ioo (0 : Interval) 1 ∧ (old u).2 ∈ Ioo (0 : Interval) 1)
        (hNewInterior : ∀ u ∈ Ioo (0 : Interval) 1,
          (new u).1 ∈ Ioo (0 : Interval) 1 ∧ (new u).2 ∈ Ioo (0 : Interval) 1)
        (hWholeTrace : Set.range cell ∩ Set.range q = Set.range (cell.comp old))
        (hNewClear : Disjoint (Set.range (cell.comp new)) (Set.range a))
        (hCornerTrace : M.first 1 ∈ Set.range (cell.comp old)) :
        ∃ K : AmbientIsotopy ↥Q,
          (∀ t, (fun y => K.map (t,y)) '' B = B) ∧
          (∀ j, K.finalMap '' Set.range (c j) = Set.range (c j)) ∧
          K.finalMap '' Set.range q =
            (Set.range q \ Set.range (cell.comp old)) ∪ Set.range (cell.comp new) ∧
          Set.range a ∩ (K.finalMap '' Set.range q) ⊆
            (Set.range a ∩ Set.range q) \ {M.first 1} := by
      obtain ⟨L,hLTrace,hLFix,hLBoundary⟩ :=
        CoherentEndpointMotion.rectangle_one_free_end_crosscuts_motion
          old new hOld hNew hOldZero hNewZero hFar hOldOne
          hOldZeroWidth hNewZeroWidth hFarWidth hOldInterior hNewInterior
      let V : Set (Interval × Interval) := {z | z.1 < 1 ∧ z.2 ∈ Ioo (0 : Interval) 1}
      have hFixOutside (t : Interval) (z : Interval × Interval) (hz : z ∉ V) :
          L.map (t,z) = z := by
        apply hLFix t z
        by_cases hx : z.1 = 1
        · exact Or.inl hx
        by_cases hy0 : z.2 = 0
        · exact Or.inr (Or.inl hy0)
        by_cases hy1 : z.2 = 1
        · exact Or.inr (Or.inr hy1)
        exact (hz ⟨lt_top_iff_ne_top.mpr hx,
          bot_lt_iff_ne_bot.mpr hy0,lt_top_iff_ne_top.mpr hy1⟩).elim
      obtain ⟨K,hKCell,hKOutside⟩ := CoherentEndpointMotion.embedded_cell_isotopy_extend
        cell hCell V hCellOpen L hFixOutside
      have hBoundaryIff (t : Interval) (y : ↥Q) : K.map (t,y) ∈ B ↔ y ∈ B := by
        by_cases hyCell : y ∈ Set.range cell
        · obtain ⟨z,rfl⟩ := hyCell
          rw [hKCell,hCellBoundary,hCellBoundary]
          exact hLBoundary t z
        · have hyOutside : y ∉ cell '' V := fun hy => hyCell (Set.image_subset_range _ _ hy)
          rw [hKOutside t y hyOutside]
      have hBSetwise (t : Interval) : (fun y => K.map (t,y)) '' B = B := by
        apply Set.Subset.antisymm
        · rintro y ⟨z,hz,rfl⟩
          exact (hBoundaryIff t z).mpr hz
        · intro y hy
          obtain ⟨k,hk⟩ := K.homeomorphism_at t
          obtain ⟨z,hz⟩ := k.surjective y
          have hzMap : K.map (t,z) = y := (hk z).symm.trans hz
          exact ⟨z,(hBoundaryIff t z).mp (hzMap.symm ▸ hy),hzMap⟩
      have hProtectedFix (j : J) (u : Interval) : K.finalMap (c j u) = c j u := by
        apply hKOutside 1
        rintro ⟨z,hz,hzc⟩
        have hcSupport : c j u ∈ supportW := hzc ▸ hCellSupport (Set.mem_range_self z)
        exact hcSupport (Set.mem_iUnion.mpr ⟨j,Set.mem_range_self u⟩)
      have hProtectedRestore (j : J) : K.finalMap '' Set.range (c j) = Set.range (c j) := by
        ext y
        constructor
        · rintro ⟨z,⟨u,rfl⟩,rfl⟩
          rw [hProtectedFix j u]
          exact Set.mem_range_self u
        · rintro ⟨u,rfl⟩
          exact ⟨c j u,Set.mem_range_self u,hProtectedFix j u⟩
      have hOldInQ : Set.range (cell.comp old) ⊆ Set.range q := by
        rw [← hWholeTrace]
        exact Set.inter_subset_right
      have hRemainderFix (y : ↥Q) (hy : y ∈ Set.range q \ Set.range (cell.comp old)) :
          K.finalMap y = y := by
        apply hKOutside 1
        intro hyCell
        exact hy.2 (hWholeTrace ▸ ⟨Set.image_subset_range _ _ hyCell,hy.1⟩)
      have hMovedTrace : K.finalMap '' Set.range (cell.comp old) = Set.range (cell.comp new) := by
        have hRangeOld : Set.range (cell.comp old) = cell '' Set.range old := by
          exact Set.range_comp cell old
        have hRangeNew : Set.range (cell.comp new) = cell '' Set.range new := by
          exact Set.range_comp cell new
        rw [hRangeOld,hRangeNew,← hLTrace,Set.image_image,Set.image_image]
        congr 1
        funext z
        exact hKCell 1 z
      have hWholeMoved : K.finalMap '' Set.range q =
          (Set.range q \ Set.range (cell.comp old)) ∪ Set.range (cell.comp new) := by
        ext y
        constructor
        · rintro ⟨z,hz,rfl⟩
          by_cases hzOld : z ∈ Set.range (cell.comp old)
          · exact Or.inr (hMovedTrace ▸ Set.mem_image_of_mem K.finalMap hzOld)
          · exact Or.inl ((hRemainderFix z ⟨hz,hzOld⟩).symm ▸ ⟨hz,hzOld⟩)
        · rintro (hy | hy)
          · exact ⟨y,hy.1,hRemainderFix y hy⟩
          · obtain ⟨z,hz,hzy⟩ := (show y ∈ K.finalMap '' Set.range (cell.comp old) from hMovedTrace.symm ▸ hy)
            exact ⟨z,hOldInQ hz,hzy⟩
      refine ⟨K,hBSetwise,hProtectedRestore,hWholeMoved,?_⟩
      rintro y ⟨hya,hyMoved⟩
      rw [hWholeMoved] at hyMoved
      rcases hyMoved with hyOld | hyNew
      · refine ⟨⟨hya,hyOld.1⟩,?_⟩
        intro hyCorner
        exact hyOld.2 ((Set.mem_singleton_iff.mp hyCorner).symm ▸ hCornerTrace)
      · exact (Set.disjoint_left.mp hNewClear hyNew hya).elim
    have hAClockInterior (u : Interval) (hu : aS u ∈ cornerAxes.source) :
        u ∈ Ioo (0:Interval) 1 := by
      have hnB : a u ∉ B := by
        intro hb
        have hi : (a u).val ∈ interior Q := (hCornerAxesSub hu).2.1.1
        exact (mem_interior_iff_notMem_frontier (a u).property).mp hi
          ((hBoundaryFrontier (a u)).mp hb)
      exact ⟨bot_lt_iff_ne_bot.mpr (fun hu0 => hnB (hu0.symm ▸ haEnds.1)),
        lt_top_iff_ne_top.mpr (fun hu1 => hnB (hu1.symm ▸ haEnds.2))⟩
    have hAxisContact : aS rCorner = qS sCorner :=
      congrArg Subtype.val (hrCorner.trans hsCorner.symm)
    let swapped_axis_packet : ∃ D : OpenPartialHomeomorph S Schoenflies.Plane,
        D.source = cornerAxes.source ∧
        (∀ y, D y 0 = cornerAxes y 1) ∧ (∀ y, D y 1 = cornerAxes y 0) ∧
        (∀ z, D.symm z = cornerAxes.symm (Schoenflies.Plane.mk (z 1) (z 0))) ∧
        (∀ ρ, Schoenflies.Plane.closedSquare 0 ρ ⊆ cornerAxes.target →
          Schoenflies.Plane.closedSquare 0 ρ ⊆ D.target) ∧
        ActualHarerCornerGeometry.OrderedWholePairAxes aS qS rCorner sCorner 0 1 D := by
      let sw : Schoenflies.Plane ≃ₜ Schoenflies.Plane := {
        toFun := fun z => Schoenflies.Plane.mk (z 1) (z 0)
        invFun := fun z => Schoenflies.Plane.mk (z 1) (z 0)
        left_inv := by intro z; ext i; fin_cases i <;> rfl
        right_inv := by intro z; ext i; fin_cases i <;> rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
      let D := cornerAxes.trans sw.toOpenPartialHomeomorph
      have hDs : D.source = cornerAxes.source := by simp [D]
      have hDt (z : Schoenflies.Plane) : z ∈ D.target ↔ sw.symm z ∈ cornerAxes.target := by
        simp [D,OpenPartialHomeomorph.trans_target]
      have hD0 (x : S) : D x 0 = cornerAxes x 1 := rfl
      have hD1 (x : S) : D x 1 = cornerAxes x 0 := rfl
      have hSwapSq (ρ : ℝ) (z : Schoenflies.Plane) (hz : z ∈ Schoenflies.Plane.closedSquare 0 ρ) :
          sw.symm z ∈ Schoenflies.Plane.closedSquare 0 ρ := by
        simp only [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,sub_zero,mem_setOf_eq,max_le_iff] at hz ⊢
        change |z 1| ≤ ρ ∧ |z 0| ≤ ρ
        exact hz.symm
      have hSquare (ρ : ℝ) (hρ : Schoenflies.Plane.closedSquare 0 ρ ⊆ cornerAxes.target) :
          Schoenflies.Plane.closedSquare 0 ρ ⊆ D.target := fun z hz => (hDt z).mpr (hρ (hSwapSq ρ z hz))
      have hNewAxes : ActualHarerCornerGeometry.OrderedWholePairAxes aS qS rCorner sCorner 0 1 D := {
        center_mem := hDs.symm ▸ (hAxisContact.symm ▸ hCornerAxes.center_mem)
        center_zero := by
          have hc : cornerAxes (aS rCorner) = 0 := hAxisContact.symm ▸ hCornerAxes.center_zero
          change sw (cornerAxes (aS rCorner)) = 0
          rw [hc]
          ext i
          fin_cases i <;> rfl
        square_subset := hSquare 1 hCornerAxes.square_subset
        anchor_axis := by
          intro x hx
          rw [hD1]
          exact hCornerAxes.moving_axis x (hDs ▸ hx)
        moving_axis := by
          intro x hx
          rw [hD0]
          exact hCornerAxes.anchor_axis x (hDs ▸ hx)
        anchor_order := by
          intro u hu
          rw [hD0]
          exact ⟨hAClockInterior u (hDs ▸ hu),hCornerAxes.moving_order u (hDs ▸ hu)⟩
        moving_order := by
          intro u hu
          rw [hD1]
          exact (hCornerAxes.anchor_order u (hDs ▸ hu)).2 }
      exact ⟨D,hDs,hD0,hD1,fun _ => rfl,hSquare,hNewAxes⟩
    obtain ⟨cornerChart,hCornerChartSource,hChart0,hChart1,hChartInverse,hChartSquare,hSwappedAxes⟩ :=
      swapped_axis_packet
    have hSwappedQuadrant (z : Schoenflies.Plane) (hx : |z 0| < cornerRadius)
        (hy : |z 1| < cornerRadius) :
        (cornerChart.symm z ∈ Set.range firstS ↔ z 1 = 0 ∧ 0 ≤ σa * z 0) ∧
        (cornerChart.symm z ∈ Set.range secondS ↔ z 0 = 0 ∧ 0 ≤ σq * z 1) ∧
        (cornerChart.symm z ∈ Set.range diskS ↔ 0 ≤ σa * z 0 ∧ 0 ≤ σq * z 1) := by
      rw [hChartInverse]
      let w := Schoenflies.Plane.mk (z 1) (z 0)
      have hw0 : |w 0| < cornerRadius := hy
      have hw1 : |w 1| < cornerRadius := hx
      refine ⟨?_,?_,?_⟩
      · exact hFirstRay w hw0 hw1
      · exact hSecondRay w hw0 hw1
      · have hdisk := hSameDiskQuadrant w hw0 hw1
        constructor
        · intro hm
          exact ⟨(hdisk.mp hm).2,(hdisk.mp hm).1⟩
        · rintro ⟨h0,h1⟩
          exact hdisk.mpr ⟨h1,h0⟩
    have hOutgoingSwapped (u : Interval) (hu : sOriented < u)
        (hy : (q (ξ u)).val ∈ cornerChart.source) :
        0 < -σq * (cornerChart (q (ξ u)).val) 1 := by
      have hs : qS (ξ u) ∈ cornerAxes.source := hCornerChartSource ▸ hy
      have horder := (hCornerAxes.anchor_order (ξ u) hs).2
      rw [hChart1]
      by_cases hz0 : zSecond = 0
      · have hξeq : ξ = Homeomorph.refl Interval := by simp [ξ,hz0]
        have hsEq : sOriented = sCorner := by simp [sOriented,hξeq]
        have hSigma : σq = -1 := by
          simp [σq,ActualHarerCornerGeometry.inwardParameterSign,hz0,
            not_lt_of_ge (bot_le : (0:Interval) ≤ sCorner)]
        rw [hSigma]
        simp only [neg_neg,one_mul]
        apply horder.2.mpr
        rw [hξeq]
        change sCorner < u
        simpa only [hsEq] using hu
      · have hz1 : zSecond = 1 := hzSecondEndpoint.resolve_left hz0
        have hξeq : ξ = unitInterval.symmHomeomorph := by simp [ξ,hz0]
        have hsVal : (sOriented:ℝ) = 1-(sCorner:ℝ) := by
          dsimp [sOriented]
          rw [hξeq]
          rfl
        have huVal : (ξ u:ℝ) = 1-(u:ℝ) := by rw [hξeq]; rfl
        have hparam : ξ u < sCorner := by
          change (ξ u:ℝ) < (sCorner:ℝ)
          have hout : (sOriented:ℝ) < u := hu
          rw [huVal]
          linarith only [hout,hsVal]
        have hSigma : σq = 1 := by
          simp [σq,ActualHarerCornerGeometry.inwardParameterSign,hz1,hsCornerInterior.2]
        have hneg := horder.1.mpr hparam
        rw [hSigma]
        rw [neg_mul,one_mul]
        exact neg_pos.mpr hneg
    have hξOriginal : ξ = Homeomorph.refl Interval ∨ ξ = unitInterval.symmHomeomorph := by
      dsimp [ξ]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hξs : ξ sOriented = sCorner := ξ.apply_symm_apply sCorner
    let dClean : CoherentEndpointMotion.RelativeCleanHalfAlignment.CleanHalfLocalData S Q B a q := {
      a_embedded := ha
      q_embedded := hq
      a_ends := haEnds
      q_ends := hqEnds
      a_interior := haInterior
      q_interior := hqInterior
      endpoint_separation := hEndpointSep
      finite_contacts := hFinite
      M := M
      e := e
      e_embedded := he
      disk_boundary := heb
      empty_interior := hempty
      clean_contact := hClean
      disk_a_trace := hWholeFirstExact
      disk_q_trace := hWholeSecondExact
      disk_B_trace := hDiskBoundaryExact
      beta_relative_interior := hBoundaryRelativeInterior
      sideArc := sideArc
      side_embedded := hSideArc
      side_range := hSideArcRange
      side_zero := hSideArc0
      side_one := hSideArc1
      side_interior := hSideArcInterior
      G := G
      G_closed := hGclosed
      disk_clear := hDiskGraph
      W := supportW
      W_open := hSupportWOpen
      disk_in_W := hDiskSupportW
      W_clear := hSupportWGraph
      F := F
      p := p
      F_embedded := hF
      p_interior := hp
      F_center := hFcenter
      F_boundary := hFB
      F_open := hFopen
      l := l
      r := r
      band_order := ⟨hl0,hlp,hpr,hr1⟩
      band_clear := hBandClear
      xi := ξ
      xi_original_clock := hξOriginal
      s := sOriented
      t := tailEnd
      tail_order := ⟨hsOriented.1,hTailStart,hTailEnd⟩
      q_initial := hqOriented0
      q_corner := hqOrientedCorner
      second_trace := hSecondOrientedRange
      tail_in_W := hTailSupport
      tail_exterior := hTailClear
      a_corner_parameter := rCorner
      a_corner := hrCorner
      axis_lo := 0
      axis_hi := 1
      cornerChart := cornerChart
      axes := by
        change ActualHarerCornerGeometry.OrderedWholePairAxes aS qS rCorner (ξ sOriented) 0 1 cornerChart
        rw [hξs]
        exact hSwappedAxes
      axis_interior := fun y hy => (hCornerAxesSub (hCornerChartSource ▸ hy)).2.1.1
      axis_clear := by
        intro y hy hG
        exact (hCornerAxesSub (hCornerChartSource ▸ hy)).2.1.2 ⟨y,hG,rfl⟩
      axis_beta_clear := by
        apply Set.disjoint_left.mpr
        intro y hy hβ
        exact (hCornerAxesSub (hCornerChartSource ▸ hy)).2.2 hβ
      radius := cornerRadius
      radius_bounds := ⟨hCornerRadius,hCornerRadiusOne⟩
      small_square := hChartSquare cornerRadius hCornerSquareTarget
      sigma := σa
      tau := σq
      signs := ⟨hσa,hσq⟩
      same_disk_quadrant := hSwappedQuadrant
      outgoing_axis_order := hOutgoingSwapped }
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `dClean
      let some value := localDecl.value? | Lean.throwError "Missing literal original clean-half data"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected clean-half data axiom: {ax}"
      Lean.logInfo m!"ORIGINAL_69_FIELD_DATA_AXIOMS: {found.toList}"
    have hMove : ∃ K : AmbientIsotopy ↥Q,
        (∀ t, (fun y => K.map (t,y)) '' B = B) ∧
        (∀ j, K.finalMap '' Set.range (c j) = Set.range (c j)) ∧
        Set.range a ∩ (K.finalMap '' Set.range q) ⊆
          (Set.range a ∩ Set.range q) \ {M.first 1} := by
      obtain ⟨collar⟩ :=
        CoherentEndpointMotion.RelativeCleanHalfAlignment.original_clean_half_disk_constructs_relative_collar
          S g hg hS x R hR htarget a q dClean
      obtain ⟨crosscuts⟩ :=
        CoherentEndpointMotion.RelativeCleanHalfAlignment.original_clean_half_collar_constructs_relative_crosscuts
          S g hg hS x R hR htarget a q dClean collar
      have hCellSupport : Set.range crosscuts.E ⊆ supportW := by
        rw [crosscuts.E_range]
        exact Set.union_subset hDiskSupportW collar.collar_in_W
      have hWholeTrace : Set.range crosscuts.E ∩ Set.range q =
          Set.range (crosscuts.E.comp crosscuts.old) := by
        rw [crosscuts.E_range,collar.whole_q_trace,crosscuts.old_trace]
      have hCornerTrace : M.first 1 ∈ Set.range (crosscuts.E.comp crosscuts.old) := by
        rw [crosscuts.old_trace]
        exact ⟨sOriented,⟨bot_le,hTailStart.le⟩,hqOrientedCorner⟩
      obtain ⟨K,hKB,hKP,hWholeMoved,hRemoval⟩ :=
        hCellConsumer crosscuts.E crosscuts.E_embedded crosscuts.E_boundary
          crosscuts.E_relative_open hCellSupport crosscuts.old crosscuts.new
          crosscuts.old_embedded crosscuts.new_embedded crosscuts.old_zero
          crosscuts.new_zero crosscuts.same_far_endpoint crosscuts.old_one
          crosscuts.old_zero_width crosscuts.new_zero_width crosscuts.far_width
          crosscuts.old_interior crosscuts.new_interior hWholeTrace
          crosscuts.new_clear_whole_a hCornerTrace
      exact ⟨K,hKB,hKP,hRemoval⟩
    obtain ⟨K,hKB,hKP,hRemoval⟩ := hMove
    let q' : C(Interval,↥Q) := ⟨fun t => K.finalMap (q t),
      K.map.continuous.comp (continuous_const.prodMk q.continuous)⟩
    obtain ⟨k,hk⟩ := K.homeomorphism_at 1
    have hkEq : (k : ↥Q → ↥Q) = K.finalMap := funext hk
    have hkB : k '' B = B := by simpa only [hk] using hKB 1
    have hKmem (y : ↥Q) : K.finalMap y ∈ B ↔ y ∈ B := by
      rw [← hkEq]
      constructor
      · intro hy
        obtain ⟨z,hz,hzy⟩ := (show k y ∈ k '' B from hkB.symm ▸ hy)
        exact k.injective hzy ▸ hz
      · intro hy
        exact hkB ▸ Set.mem_image_of_mem k hy
    have hq' : IsEmbedding q' := by
      exact (hkEq ▸ k.isEmbedding).comp hq
    have hq'Ends : q' 0 ∈ B ∧ q' 1 ∈ B :=
      ⟨(hKmem _).mpr hqEnds.1,(hKmem _).mpr hqEnds.2⟩
    have hq'Interior : ∀ t ∈ Ioo (0 : Interval) 1, q' t ∉ B := by
      intro t ht h
      exact hqInterior t ht ((hKmem _).mp h)
    have hq'Range : K.finalMap '' Set.range q = Set.range q' :=
      (Set.range_comp K.finalMap q).symm
    have hRemoval' : Set.range a ∩ Set.range q' ⊆
        (Set.range a ∩ Set.range q) \ {M.first 1} := by
      rw [← hq'Range]
      exact hRemoval
    have hSubset : Set.range a ∩ Set.range q' ⊆ Set.range a ∩ Set.range q :=
      hRemoval'.trans Set.sdiff_subset
    have hOldEndClear : ∀ s : Interval, s = 0 ∨ s = 1 → a s ∉ Set.range q := by
      intro s hs ⟨t,ht⟩
      have hsB : a s ∈ B := hs.elim (fun h => h ▸ haEnds.1) (fun h => h ▸ haEnds.2)
      have htB : q t ∈ B := ht ▸ hsB
      have htEnd : t = 0 ∨ t = 1 := by
        by_cases h0 : t = 0
        · exact Or.inl h0
        by_cases h1 : t = 1
        · exact Or.inr h1
        exact False.elim (hqInterior t
          ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩ htB)
      have hsEnd : a s ∈ ({a 0,a 1} : Set ↥Q) := by
        rcases hs with rfl | rfl <;> simp
      have htEnd' : q t ∈ ({q 0,q 1} : Set ↥Q) := by
        rcases htEnd with rfl | rfl <;> simp
      exact Set.disjoint_left.mp hEndpointSep hsEnd (ht ▸ htEnd')
    have hNewEndpointSep : Disjoint ({a 0,a 1} : Set ↥Q) {q' 0,q' 1} := by
      apply Set.disjoint_left.mpr
      intro y hyA hyQ
      have hyR : y ∈ Set.range q' := by
        rcases Set.mem_insert_iff.mp hyQ with rfl | hy
        · exact Set.mem_range_self 0
        · exact Set.mem_singleton_iff.mp hy ▸ Set.mem_range_self 1
      rcases Set.mem_insert_iff.mp hyA with rfl | hy
      · exact hOldEndClear 0 (Or.inl rfl) (hSubset ⟨Set.mem_range_self 0,hyR⟩).2
      · have hy1 : y = a 1 := Set.mem_singleton_iff.mp hy
        subst y
        exact hOldEndClear 1 (Or.inr rfl) (hSubset ⟨Set.mem_range_self 1,hyR⟩).2
    have hCornerOld : M.first 1 ∈ Set.range a ∩ Set.range q :=
      ⟨M.first_on_a (Set.mem_range_self 1),
        M.second_on_b ⟨1,M.corner_eq.symm⟩⟩
    have hDrop : (Set.range a ∩ Set.range q').ncard < (Set.range a ∩ Set.range q).ncard := by
      apply Set.ncard_lt_ncard _ hFinite
      apply Set.ssubset_iff_subset_ne.mpr
      refine ⟨hSubset,?_⟩
      intro heq
      exact (hRemoval' (heq.symm ▸ hCornerOld)).2 (Set.mem_singleton _)
    exact ⟨q',K,⟨hq',hq'Ends,hq'Interior,hNewEndpointSep,hFinite.subset hSubset,
      hKB,hKP,hq'Range⟩,hDrop⟩
