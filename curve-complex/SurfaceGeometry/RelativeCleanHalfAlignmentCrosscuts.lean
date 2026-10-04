import RelativeCleanHalfAlignmentHelpers
import CurveComplexGenusTwo.Topology.ActualThreeArcCount.ExteriorDictionary
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualInternalCollarCalibration
import CurveComplexGenusTwo.Topology.ActualHarerCrossingAxes.ActualHarerQuadrantHelpers
import CurveComplexGenusTwo.Topology.CrosscutBoundary
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.EmbeddedStripAmbientMotion
import CurveComplexGenusTwo.Topology.CapBandGeometry.LocalCapSeam
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.HalfPlaneBandOpenness
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualEmbeddedArcConcatenation
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryNullGeometry
import CurveComplexGenusTwo.Topology.ActualHarerCrossingAxes.ActualHarerCornerGeometryDefinitions
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualBoundaryProperArcStrip
import CurveComplexGenusTwo.Topology.ActualHarerDiskGluing.ActualHarerOptionalCollapseGluingProof
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeStripCrosscutMotion

open Set Topology CurveComplex Schoenflies

set_option maxHeartbeats 4000000

namespace CoherentEndpointMotion.RelativeCleanHalfAlignment

theorem original_clean_half_collar_constructs_relative_crosscuts
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆ (chartAt Plane x).target) :
    let Q : Set S := ((chartAt Plane x).symm '' Metric.ball ((chartAt Plane x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt Plane x).symm ''
      Metric.sphere ((chartAt Plane x) x) R}
    ∀ (a q : C(Interval, ↥Q)) (d : CleanHalfLocalData S Q B a q)
      (h : RelativeHalfCollar d), Nonempty (RelativeHalfCrosscuts d h) := by
  classical
  dsimp only
  intro a q d h
  let Q : Set S := ((chartAt Plane x).symm '' Metric.ball ((chartAt Plane x) x) R)ᶜ
  let B : Set ↥Q := {y | y.val ∈ (chartAt Plane x).symm ''
    Metric.sphere ((chartAt Plane x) x) R}
  letI : ClosedSurface S := Classical.choice hS.2.1
  have ht0 : (0 : Interval) < d.t := d.tail_order.1.trans d.tail_order.2.1
  have ht1 : d.t < (1 : Interval) := d.tail_order.2.2
  let clockPrefix : C(Interval, Interval) :=
    ⟨Set.Icc.convexComb 0 d.t, Set.Icc.continuous_convexComb 0 d.t⟩
  have clockPrefix_zero : clockPrefix 0 = 0 := Set.Icc.convexComb_zero 0 d.t
  have clockPrefix_one : clockPrefix 1 = d.t := Set.Icc.convexComb_one 0 d.t
  have clockPrefix_injective : Function.Injective clockPrefix := by
    intro u v huv
    apply Subtype.ext
    have he := congrArg Subtype.val huv
    simp only [clockPrefix, ContinuousMap.coe_mk, Set.Icc.coe_convexComb,
      Set.Icc.coe_zero, mul_zero, zero_add] at he
    have ht : (0 : ℝ) < d.t.val := ht0
    nlinarith
  have clockPrefix_range : range clockPrefix = Icc (0 : Interval) d.t := by
    ext v
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨Set.Icc.le_convexComb ht0.le u, Set.Icc.convexComb_le ht0.le u⟩
    · intro hv
      let u : Interval := ⟨v.val / d.t.val, ⟨
        div_nonneg v.property.1 ht0.le,
        (div_le_one (show (0 : ℝ) < d.t.val from ht0)).mpr hv.2⟩⟩
      refine ⟨u, ?_⟩
      apply Subtype.ext
      simp only [clockPrefix, ContinuousMap.coe_mk, Set.Icc.coe_convexComb,
        Set.Icc.coe_zero, mul_zero, zero_add]
      change v.val / d.t.val * d.t.val = v.val
      exact div_mul_cancel₀ _ (ne_of_gt (show (0 : ℝ) < d.t.val from ht0))
  let qOriented : C(Interval, _) := q.comp ⟨d.xi, d.xi.continuous⟩
  let oldActual := qOriented.comp clockPrefix
  have oldActual_embedded : IsEmbedding oldActual :=
    d.q_embedded.comp (d.xi.isEmbedding.comp
      (clockPrefix.continuous.isClosedEmbedding clockPrefix_injective).isEmbedding)
  have oldActual_zero : oldActual 0 = d.M.second 0 := by
    change q (d.xi (clockPrefix 0)) = _
    rw [clockPrefix_zero]
    exact d.q_initial
  have oldActual_one : oldActual 1 = q (d.xi d.t) := by
    change q (d.xi (clockPrefix 1)) = _
    rw [clockPrefix_one]
  have oldActual_trace : range oldActual =
      (fun u => q (d.xi u)) '' Icc 0 d.t := by
    change range (qOriented ∘ clockPrefix) = _
    rw [range_comp, clockPrefix_range]
    rfl
  have oldActual_in_cell : range oldActual ⊆ range h.enlargedDisk := by
    rw [h.enlarged_range, oldActual_trace, ← h.whole_q_trace]
    exact inter_subset_left
  have oldActual_in_W : range oldActual ⊆ d.W := by
    rw [oldActual_trace]
    exact d.tail_in_W
  have qOriented_boundary (v : Interval) :
      qOriented v ∈ B ↔ v = 0 ∨ v = 1 := by
    change q (d.xi v) ∈ B ↔ _
    constructor
    · intro hv
      have hEnd : d.xi v = 0 ∨ d.xi v = 1 := by
        by_contra hne
        have hne0 : d.xi v ≠ 0 := fun he => hne (Or.inl he)
        have hne1 : d.xi v ≠ 1 := fun he => hne (Or.inr he)
        have hi : d.xi v ∈ Ioo (0 : Interval) 1 :=
          ⟨lt_of_le_of_ne (show (0 : Interval) ≤ d.xi v from (d.xi v).property.1)
              hne0.symm,
           lt_of_le_of_ne (show d.xi v ≤ (1 : Interval) from (d.xi v).property.2)
              hne1⟩
        exact d.q_interior _ hi hv
      rcases d.xi_original_clock with he | he
      · simpa only [he, Homeomorph.refl_apply, id_eq] using hEnd
      · rcases hEnd with h0 | h1
        · right
          apply d.xi.injective
          rw [h0, he]
          exact (unitInterval.symm_one).symm
        · left
          apply d.xi.injective
          rw [h1, he]
          exact (unitInterval.symm_zero).symm
    · rintro (rfl | rfl)
      · rw [d.q_initial]
        exact d.M.second_zero_boundary
      · rcases d.xi_original_clock with he | he
        · have hi : d.xi 1 = 1 := by rw [he]; rfl
          rw [hi]
          exact d.q_ends.2
        · have hi : d.xi 1 = 0 := by rw [he]; exact unitInterval.symm_one
          rw [hi]
          exact d.q_ends.1
  have oldActual_boundary (u : Interval) : oldActual u ∈ B ↔ u = 0 := by
    change qOriented (clockPrefix u) ∈ B ↔ _
    rw [qOriented_boundary]
    constructor
    · rintro (h0 | h1)
      · exact clockPrefix_injective (h0.trans clockPrefix_zero.symm)
      · have hle := Set.Icc.convexComb_le ht0.le u
        change clockPrefix u ≤ d.t at hle
        rw [h1] at hle
        exact False.elim (not_le_of_gt ht1 hle)
    · intro he
      left
      rw [he, clockPrefix_zero]
  have far_on_outer_rail : oldActual 1 = h.H (h.eta 1) := by
    rw [oldActual_one, h.eta_exact_parameter, Set.Icc.convexComb_one]
  have far_clear_whole_a : oldActual 1 ∉ range a := by
    rw [oldActual_one]
    intro ha
    exact disjoint_left.mp d.tail_exterior
      (show q (d.xi d.t) ∈ (fun u => q (d.xi u)) '' Ioc d.s d.t from
        ⟨d.t, ⟨d.tail_order.2.1, le_rfl⟩, rfl⟩)
      (Or.inr ha)
  have collar_boundary (z : Interval × Interval) :
      h.H z ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := by
    constructor
    · intro hz
      by_contra he
      have h0 : z.1 ≠ 0 := fun hh => he (Or.inl hh)
      have h1 : z.1 ≠ 1 := fun hh => he (Or.inr hh)
      exact h.interior_off_B z.1
        ⟨lt_of_le_of_ne (show (0 : Interval) ≤ z.1 from z.1.property.1) h0.symm,
         lt_of_le_of_ne (show z.1 ≤ (1 : Interval) from z.1.property.2) h1⟩ z.2 hz
    · rintro (he | he)
      · have hz : z = (0, z.2) := Prod.ext he rfl
        rw [hz]
        exact (h.endpoints_in_B z.2).1
      · have hz : z = (1, z.2) := Prod.ext he rfl
        rw [hz]
        exact (h.endpoints_in_B z.2).2
  have oldActual_outer_boundary (u : Interval) :
      oldActual u ∈ h.enlargedDisk '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} ↔
        u = 0 ∨ u = 1 := by
    rw [h.enlarged_boundary]
    constructor
    · intro hu
      rcases hu with ((hbeta | hleft) | hright) | htop
      · left
        apply (oldActual_boundary u).mp
        obtain ⟨v, hv⟩ := hbeta
        rw [← hv]
        exact d.M.boundary_in_B v
      · left
        apply (oldActual_boundary u).mp
        obtain ⟨w, hw⟩ := hleft
        rw [← hw]
        exact (h.endpoints_in_B w).1
      · left
        apply (oldActual_boundary u).mp
        obtain ⟨w, hw⟩ := hright
        rw [← hw]
        exact (h.endpoints_in_B w).2
      · right
        obtain ⟨v, hv⟩ := htop
        change h.H (v,1) = oldActual u at hv
        by_cases hbefore : clockPrefix u ≤ d.s
        · have hinSecond : oldActual u ∈ range d.M.second := by
            rw [d.second_trace]
            exact ⟨clockPrefix u, ⟨(clockPrefix u).property.1, hbefore⟩, rfl⟩
          have hinDisk : oldActual u ∈ range d.e := by
            have hr : oldActual u ∈ range d.e ∩ range q := by
              rw [d.disk_q_trace]
              exact hinSecond
            exact hr.1
          have hinSeam : h.H (v,1) ∈ range d.sideArc := by
            rw [← h.disk_intersection]
            refine ⟨mem_range_self _, ?_⟩
            rw [hv]
            exact hinDisk
          obtain ⟨w, hw⟩ := hinSeam
          have he : h.H (v,1) = h.H (w,0) := hw.symm.trans (h.seam w).symm
          have hh := congrArg Prod.snd (h.H_embedded.injective he)
          exact False.elim (zero_ne_one hh.symm)
        · have hinTail : oldActual u ∈ range (h.H.comp h.eta) := by
            rw [h.eta_trace]
            exact ⟨clockPrefix u,
              ⟨(lt_of_not_ge hbefore).le, Set.Icc.convexComb_le ht0.le u⟩, rfl⟩
          obtain ⟨w, hw⟩ := hinTail
          have he : (v,1) = h.eta w :=
            h.H_embedded.injective (hv.trans hw.symm)
          have hw1 : w = 1 := by
            by_contra hwne1
            by_cases hw0 : w = 0
            · have hh := congrArg Prod.snd he
              rw [hw0, h.eta_zero] at hh
              exact zero_ne_one hh.symm
            · have hi : w ∈ Ioo (0 : Interval) 1 :=
                ⟨lt_of_le_of_ne (show (0 : Interval) ≤ w from w.property.1) (Ne.symm hw0),
                 lt_of_le_of_ne (show w ≤ (1 : Interval) from w.property.2) hwne1⟩
              have hlt := (h.eta_interior w hi).2.2
              have hh := congrArg Prod.snd he
              rw [← hh] at hlt
              exact lt_irrefl _ hlt
          apply clockPrefix_injective
          rw [clockPrefix_one]
          apply d.xi.injective
          apply d.q_embedded.injective
          change oldActual u = q (d.xi d.t)
          rw [← hw, hw1]
          exact (h.eta_exact_parameter 1).trans
            (congrArg (fun v => q (d.xi v)) (Set.Icc.convexComb_one d.s d.t))
    · rintro (rfl | rfl)
      · left; left; left
        rw [oldActual_zero]
        exact ⟨1, d.M.boundary_one⟩
      · right
        refine ⟨(h.eta 1).1, ?_⟩
        rw [far_on_outer_rail]
        apply congrArg h.H
        exact Prod.ext rfl h.eta_one.1.symm
  let oldInCell : C(Interval, range h.enlargedDisk) :=
    ⟨fun u => ⟨oldActual u, oldActual_in_cell (mem_range_self u)⟩,
      oldActual.continuous.subtype_mk _⟩
  let oldInDisk : C(Interval, Metric.closedBall (0 : Plane) 1) :=
    ⟨fun u => h.enlarged_embedded.toHomeomorph.symm (oldInCell u),
      h.enlarged_embedded.toHomeomorph.symm.continuous.comp oldInCell.continuous⟩
  have oldInDisk_actual (u : Interval) : h.enlargedDisk (oldInDisk u) = oldActual u :=
    congrArg Subtype.val (h.enlarged_embedded.toHomeomorph.apply_symm_apply (oldInCell u))
  have oldInCell_embedded : IsEmbedding oldInCell := by
    apply IsEmbedding.of_comp oldInCell.continuous continuous_subtype_val
    exact oldActual_embedded
  have oldInDisk_embedded : IsEmbedding oldInDisk :=
    h.enlarged_embedded.toHomeomorph.symm.isEmbedding.comp oldInCell_embedded
  have oldInDisk_sphere (u : Interval) :
      (oldInDisk u).val ∈ Metric.sphere (0 : Plane) 1 ↔ u = 0 ∨ u = 1 := by
    rw [← oldActual_outer_boundary u]
    constructor
    · intro hu
      exact ⟨oldInDisk u, hu, oldInDisk_actual u⟩
    · rintro ⟨z, hz, he⟩
      have hh : z = oldInDisk u := h.enlarged_embedded.injective
        (he.trans (oldInDisk_actual u).symm)
      exact hh ▸ hz
  have oldInDisk_interior (u : Interval) (hu : u ∈ Ioo (0 : Interval) 1) :
      (oldInDisk u).val ∈ Metric.ball (0 : Plane) 1 := by
    have hc := (oldInDisk u).property
    have hn : (oldInDisk u).val ∉ Metric.sphere (0 : Plane) 1 := by
      rw [oldInDisk_sphere]
      exact fun he => he.elim (fun he => (ne_of_gt hu.1) he)
        (fun he => (ne_of_lt hu.2) he)
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hc
    rw [Metric.mem_sphere] at hn
    exact lt_of_le_of_ne hc hn
  obtain ⟨diskSquare, diskSquare_boundary⟩ :=
    ActualHarerDiskGluing.unit_disk_square_boundary_homeomorph
  let squarePresentation : C(Interval × Interval, ↥Q) :=
    h.enlargedDisk.comp ⟨diskSquare.symm, diskSquare.symm.continuous⟩
  have squarePresentation_embedded : IsEmbedding squarePresentation :=
    h.enlarged_embedded.comp diskSquare.symm.isEmbedding
  have squarePresentation_range : range squarePresentation = range d.e ∪ range h.H := by
    change range (h.enlargedDisk ∘ diskSquare.symm) = _
    rw [diskSquare.symm.surjective.range_comp, h.enlarged_range]
  let oldInSquare : C(Interval, Interval × Interval) :=
    ⟨fun u => diskSquare (oldInDisk u), diskSquare.continuous.comp oldInDisk.continuous⟩
  have oldInSquare_embedded : IsEmbedding oldInSquare :=
    diskSquare.isEmbedding.comp oldInDisk_embedded
  have oldInSquare_actual (u : Interval) : squarePresentation (oldInSquare u) = oldActual u := by
    change h.enlargedDisk (diskSquare.symm (diskSquare (oldInDisk u))) = _
    rw [diskSquare.symm_apply_apply, oldInDisk_actual]
  have oldInSquare_trace : range (squarePresentation.comp oldInSquare) =
      (fun u => q (d.xi u)) '' Icc 0 d.t := by
    have he : squarePresentation.comp oldInSquare = oldActual := by
      ext u
      exact congrArg Subtype.val (oldInSquare_actual u)
    rw [he, oldActual_trace]
  have oldInSquare_boundary (u : Interval) :
      oldInSquare u ∈ ActualHarerDiskGluing.squareBoundary ↔ u = 0 ∨ u = 1 := by
    rw [← diskSquare_boundary]
    constructor
    · rintro ⟨z, hz, he⟩
      have hh : z = oldInDisk u := diskSquare.injective he
      exact (oldInDisk_sphere u).mp (hh ▸ hz)
    · intro hu
      exact ⟨oldInDisk u, (oldInDisk_sphere u).mpr hu, rfl⟩
  let leftEnd : C(Interval, ↥Q) :=
    ⟨fun w => h.H (0, unitInterval.symm w), by fun_prop⟩
  let rightEnd : C(Interval, ↥Q) := ⟨fun w => h.H (1,w), by fun_prop⟩
  let outerRail : C(Interval, ↥Q) := ⟨fun u => h.H (u,1), by fun_prop⟩
  have leftEnd_embedded : IsEmbedding leftEnd := by
    apply (leftEnd.continuous.isClosedEmbedding ?_).isEmbedding
    intro u v he
    exact unitInterval.symmHomeomorph.injective
      (congrArg Prod.snd (h.H_embedded.injective he))
  have rightEnd_embedded : IsEmbedding rightEnd := by
    apply (rightEnd.continuous.isClosedEmbedding ?_).isEmbedding
    intro u v he
    exact congrArg Prod.snd (h.H_embedded.injective he)
  have outerRail_embedded : IsEmbedding outerRail := by
    apply (outerRail.continuous.isClosedEmbedding ?_).isEmbedding
    intro u v he
    exact congrArg Prod.fst (h.H_embedded.injective he)
  have leftEnd_one : leftEnd 1 = d.M.boundarySide 0 := by
    change h.H (0, unitInterval.symm 1) = _
    rw [unitInterval.symm_one, h.seam, d.side_zero, d.M.boundary_zero]
  have rightEnd_zero : rightEnd 0 = d.M.boundarySide 1 := by
    change h.H (1,0) = _
    rw [h.seam, d.side_one, d.M.boundary_one]
  have leftEnd_beta_meet : range leftEnd ∩ range d.M.boundarySide = {leftEnd 1} := by
    ext y
    constructor
    · rintro ⟨⟨u, rfl⟩, v, hv⟩
      have hh := (h.beta_collision 0 (unitInterval.symm u) v).mp hv.symm
      rcases hh with ⟨_, hw, _⟩ | ⟨hn, _, _⟩
      · apply mem_singleton_iff.mpr
        change h.H (0, unitInterval.symm u) = leftEnd 1
        rw [hw, leftEnd_one, h.seam 0, d.side_zero, d.M.boundary_zero]
      · exact False.elim (zero_ne_one hn)
    · intro hy
      rw [mem_singleton_iff] at hy
      rw [hy]
      exact ⟨mem_range_self 1, ⟨0, leftEnd_one.symm⟩⟩
  obtain ⟨leftBeta, leftBeta_embedded, leftBeta_zero, leftBeta_one, leftBeta_range⟩ :=
    CurveComplex.source_embedded_arc_concatenation leftEnd d.M.boundarySide
      leftEnd_embedded d.M.boundary_embedded leftEnd_one leftEnd_beta_meet
  have leftBeta_right_meet : range leftBeta ∩ range rightEnd = {leftBeta 1} := by
    rw [leftBeta_range]
    ext y
    constructor
    · rintro ⟨(hl | hb), v, hv⟩
      · obtain ⟨u, hu⟩ := hl
        have he : h.H (0, unitInterval.symm u) = h.H (1,v) := hu.trans hv.symm
        have hn := congrArg Prod.fst (h.H_embedded.injective he)
        exact False.elim (zero_ne_one hn)
      · obtain ⟨u, hu⟩ := hb
        have he : h.H (1,v) = d.M.boundarySide u := hv.trans hu.symm
        have hh := (h.beta_collision 1 v u).mp he
        rcases hh with ⟨hn, _, _⟩ | ⟨_, _, hu1⟩
        · exact False.elim (zero_ne_one hn.symm)
        · apply mem_singleton_iff.mpr
          rw [← hu, hu1, leftBeta_one]
    · intro hy
      rw [mem_singleton_iff] at hy
      rw [hy, leftBeta_one]
      exact ⟨Or.inr (mem_range_self 1), ⟨0, rightEnd_zero⟩⟩
  obtain ⟨boundaryArc, boundaryArc_embedded, boundaryArc_zero, boundaryArc_one,
    boundaryArc_range⟩ := CurveComplex.source_embedded_arc_concatenation
      leftBeta rightEnd leftBeta_embedded rightEnd_embedded
      (leftBeta_one.trans rightEnd_zero.symm) leftBeta_right_meet
  have boundaryArc_complete : range boundaryArc =
      (range d.e ∪ range h.H) ∩ B := by
    rw [boundaryArc_range, leftBeta_range, h.enlarged_B_trace]
    have leftEnd_range : range leftEnd = range (fun w : Interval => h.H (0,w)) := by
      change range ((fun w : Interval => h.H (0,w)) ∘ unitInterval.symm) = _
      exact unitInterval.symmHomeomorph.surjective.range_comp _
    rw [leftEnd_range]
    change (range (fun w : Interval => h.H (0,w)) ∪ range d.M.boundarySide) ∪
      range (fun w : Interval => h.H (1,w)) = _
    rw [union_comm (range (fun w : Interval => h.H (0,w))) (range d.M.boundarySide)]
  have boundaryArc_in_B (u : Interval) : boundaryArc u ∈ B := by
    have hz : boundaryArc u ∈ range boundaryArc := mem_range_self u
    rw [boundaryArc_complete] at hz
    exact hz.2
  have boundaryArc_zero_eq : boundaryArc 0 = outerRail 0 := by
    rw [boundaryArc_zero, leftBeta_zero]
    change h.H (0, unitInterval.symm 0) = h.H (0,1)
    rw [unitInterval.symm_zero]
  have boundaryArc_one_eq : boundaryArc 1 = outerRail 1 := by
    rw [boundaryArc_one]
    rfl
  have boundaryArc_rail_collision (u v : Interval)
      (he : boundaryArc u = outerRail v) :
      (u = 0 ∧ v = 0) ∨ (u = 1 ∧ v = 1) := by
    have hvB : outerRail v ∈ B := he ▸ boundaryArc_in_B u
    rcases (collar_boundary (v,1)).mp hvB with hv | hv
    · change v = 0 at hv
      left
      refine ⟨boundaryArc_embedded.injective (he.trans ?_), hv⟩
      rw [hv, boundaryArc_zero_eq]
    · change v = 1 at hv
      right
      refine ⟨boundaryArc_embedded.injective (he.trans ?_), hv⟩
      rw [hv, boundaryArc_one_eq]
  have enlarged_two_arc_boundary :
      h.enlargedDisk '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
        range boundaryArc ∪ range outerRail := by
    rw [h.enlarged_boundary, boundaryArc_range, leftBeta_range]
    have leftEnd_range : range leftEnd = range (fun w : Interval => h.H (0,w)) := by
      change range ((fun w : Interval => h.H (0,w)) ∘ unitInterval.symm) = _
      exact unitInterval.symmHomeomorph.surjective.range_comp _
    rw [leftEnd_range]
    change _ = ((range (fun w : Interval => h.H (0,w)) ∪ range d.M.boundarySide) ∪
      range (fun w : Interval => h.H (1,w))) ∪ range (fun u : Interval => h.H (u,1))
    rw [union_comm (range (fun w : Interval => h.H (0,w))) (range d.M.boundarySide)]
  obtain ⟨P, P_embedded, P_range, P_top, P_other⟩ :=
    ActualHarerDiskGluing.actual_two_side_disk_constructs_prescribed_edge_square
      boundaryArc outerRail h.enlargedDisk boundaryArc_embedded outerRail_embedded
      h.enlarged_embedded boundaryArc_zero_eq boundaryArc_one_eq
      enlarged_two_arc_boundary boundaryArc_rail_collision
  have P_boundary (z : Interval × Interval) : P z ∈ B ↔ z.2 = 1 := by
    constructor
    · intro hz
      have hzcell : P z ∈ range d.e ∪ range h.H := by
        rw [← h.enlarged_range, ← P_range]
        exact mem_range_self z
      have hzarc : P z ∈ range boundaryArc :=
        boundaryArc_complete.symm ▸ ⟨hzcell, hz⟩
      obtain ⟨u, hu⟩ := hzarc
      have he : P z = P (u,1) := hu.symm.trans (P_top u).symm
      exact congrArg Prod.snd (P_embedded.injective he)
    · intro hz
      have he : z = (z.1,1) := Prod.ext rfl hz
      rw [he, P_top]
      exact boundaryArc_in_B z.1
  let rotateSquare : Interval × Interval ≃ₜ Interval × Interval :=
    (Homeomorph.prodComm Interval Interval).trans
      (Homeomorph.prodCongr (Homeomorph.refl Interval) unitInterval.symmHomeomorph)
  let oneBoundarySquare : C(Interval × Interval, ↥Q) :=
    P.comp ⟨rotateSquare, rotateSquare.continuous⟩
  have oneBoundarySquare_embedded : IsEmbedding oneBoundarySquare :=
    P_embedded.comp rotateSquare.isEmbedding
  have oneBoundarySquare_range : range oneBoundarySquare = range d.e ∪ range h.H := by
    change range (P ∘ rotateSquare) = _
    rw [rotateSquare.surjective.range_comp, P_range, h.enlarged_range]
  have oneBoundarySquare_boundary (z : Interval × Interval) :
      oneBoundarySquare z ∈ B ↔ z.1 = 0 := by
    change P (rotateSquare z) ∈ B ↔ _
    rw [P_boundary]
    change unitInterval.symm z.1 = 1 ↔ z.1 = 0
    constructor
    · intro he
      exact unitInterval.symmHomeomorph.injective (he.trans unitInterval.symm_zero.symm)
    · intro he
      rw [he, unitInterval.symm_zero]
  have P_outer_boundary : P '' ActualHarerDiskGluing.squareBoundary =
      h.enlargedDisk '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} := by
    rw [enlarged_two_arc_boundary]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with h0 | h1 | hw0 | hw1
      · right
        rw [← P_other]
        left; right
        refine ⟨z.2, ?_⟩
        exact congrArg P (Prod.ext h0.symm rfl)
      · right
        rw [← P_other]
        right
        refine ⟨z.2, ?_⟩
        exact congrArg P (Prod.ext h1.symm rfl)
      · right
        rw [← P_other]
        left; left
        refine ⟨z.1, ?_⟩
        exact congrArg P (Prod.ext rfl hw0.symm)
      · left
        have he : z = (z.1,1) := Prod.ext rfl hw1
        rw [he, P_top]
        exact mem_range_self z.1
    · rintro (hbeta | hrail)
      · obtain ⟨u, hu⟩ := hbeta
        exact ⟨(u,1), Or.inr (Or.inr (Or.inr rfl)), (P_top u).trans hu⟩
      · rw [← P_other] at hrail
        rcases hrail with (⟨u, hu⟩ | ⟨w, hw⟩) | ⟨w, hw⟩
        · exact ⟨(u,0), Or.inr (Or.inr (Or.inl rfl)), hu⟩
        · exact ⟨(0,w), Or.inl rfl, hw⟩
        · exact ⟨(1,w), Or.inr (Or.inl rfl), hw⟩
  have rotateSquare_boundary (z : Interval × Interval) :
      rotateSquare z ∈ ActualHarerDiskGluing.squareBoundary ↔
        z ∈ ActualHarerDiskGluing.squareBoundary := by
    change z.2 = 0 ∨ z.2 = 1 ∨ unitInterval.symm z.1 = 0 ∨
      unitInterval.symm z.1 = 1 ↔ z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1
    rw [unitInterval.symm_eq_zero, unitInterval.symm_eq_one]
    tauto
  have oneBoundarySquare_outer_boundary :
      oneBoundarySquare '' ActualHarerDiskGluing.squareBoundary =
        h.enlargedDisk '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} := by
    rw [← P_outer_boundary]
    ext y
    constructor
    · rintro ⟨z, hz, he⟩
      exact ⟨rotateSquare z, (rotateSquare_boundary z).mpr hz, he⟩
    · rintro ⟨z, hz, he⟩
      refine ⟨rotateSquare.symm z, ?_, ?_⟩
      · apply (rotateSquare_boundary _).mp
        rw [rotateSquare.apply_symm_apply]
        exact hz
      · change P (rotateSquare (rotateSquare.symm z)) = y
        rw [rotateSquare.apply_symm_apply]
        exact he
  have oldActual_in_oneSquare (u : Interval) : oldActual u ∈ range oneBoundarySquare := by
    rw [oneBoundarySquare_range, ← h.enlarged_range]
    exact oldActual_in_cell (mem_range_self u)
  let oldOneCell : C(Interval, range oneBoundarySquare) :=
    ⟨fun u => ⟨oldActual u, oldActual_in_oneSquare u⟩,
      oldActual.continuous.subtype_mk _⟩
  let oldOne : C(Interval, Interval × Interval) :=
    ⟨fun u => oneBoundarySquare_embedded.toHomeomorph.symm (oldOneCell u),
      oneBoundarySquare_embedded.toHomeomorph.symm.continuous.comp oldOneCell.continuous⟩
  have oldOne_actual (u : Interval) : oneBoundarySquare (oldOne u) = oldActual u :=
    congrArg Subtype.val
      (oneBoundarySquare_embedded.toHomeomorph.apply_symm_apply (oldOneCell u))
  have oldOneCell_embedded : IsEmbedding oldOneCell := by
    apply IsEmbedding.of_comp oldOneCell.continuous continuous_subtype_val
    exact oldActual_embedded
  have oldOne_embedded : IsEmbedding oldOne :=
    oneBoundarySquare_embedded.toHomeomorph.symm.isEmbedding.comp oldOneCell_embedded
  have oldOne_outer_boundary (u : Interval) :
      oldOne u ∈ ActualHarerDiskGluing.squareBoundary ↔ u = 0 ∨ u = 1 := by
    rw [← oldActual_outer_boundary u, ← oneBoundarySquare_outer_boundary]
    constructor
    · intro hu
      exact ⟨oldOne u, hu, oldOne_actual u⟩
    · rintro ⟨z, hz, he⟩
      have hh : z = oldOne u := oneBoundarySquare_embedded.injective
        (he.trans (oldOne_actual u).symm)
      exact hh ▸ hz
  have oldOne_zero : (oldOne 0).1 = 0 :=
    (oneBoundarySquare_boundary _).mp ((oldOne_actual 0).symm ▸
      (oldActual_boundary 0).mpr rfl)
  have oldOne_zero_width : (oldOne 0).2 ∈ Ioo (0 : Interval) 1 := by
    have heActual : oldActual 0 = h.H (1,0) :=
      oldActual_zero.trans (d.side_one.symm.trans (h.seam 1).symm)
    have hn0 : (oldOne 0).2 ≠ 0 := by
      intro he
      have hz : oldOne 0 = (0,0) := Prod.ext oldOne_zero he
      have hstart : oneBoundarySquare (0,0) = h.H (1,0) :=
        (congrArg oneBoundarySquare hz).symm.trans ((oldOne_actual 0).trans heActual)
      change P (0, unitInterval.symm 0) = _ at hstart
      rw [unitInterval.symm_zero, P_top, boundaryArc_zero_eq] at hstart
      have hh := congrArg Prod.fst (h.H_embedded.injective hstart)
      exact zero_ne_one hh
    have hn1 : (oldOne 0).2 ≠ 1 := by
      intro he
      have hz : oldOne 0 = (0,1) := Prod.ext oldOne_zero he
      have hstart : oneBoundarySquare (0,1) = h.H (1,0) :=
        (congrArg oneBoundarySquare hz).symm.trans ((oldOne_actual 0).trans heActual)
      change P (1, unitInterval.symm 0) = _ at hstart
      rw [unitInterval.symm_zero, P_top, boundaryArc_one_eq] at hstart
      have hh := congrArg Prod.snd (h.H_embedded.injective hstart)
      exact zero_ne_one hh.symm
    exact ⟨lt_of_le_of_ne (show (0 : Interval) ≤ (oldOne 0).2 from (oldOne 0).2.property.1)
        (Ne.symm hn0),
      lt_of_le_of_ne (show (oldOne 0).2 ≤ (1 : Interval) from (oldOne 0).2.property.2) hn1⟩
  have squareInterior_iff (z : Interval × Interval) :
      z ∈ Ioo (0 : Interval) 1 ×ˢ Ioo (0 : Interval) 1 ↔
        z ∉ ActualHarerDiskGluing.squareBoundary := by
    constructor
    · intro hz hb
      rcases hb with h0 | h1 | hw0 | hw1
      · exact (ne_of_gt hz.1.1) h0
      · exact (ne_of_lt hz.1.2) h1
      · exact (ne_of_gt hz.2.1) hw0
      · exact (ne_of_lt hz.2.2) hw1
    · intro hz
      have h0 : z.1 ≠ 0 := fun he => hz (Or.inl he)
      have h1 : z.1 ≠ 1 := fun he => hz (Or.inr (Or.inl he))
      have hw0 : z.2 ≠ 0 := fun he => hz (Or.inr (Or.inr (Or.inl he)))
      have hw1 : z.2 ≠ 1 := fun he => hz (Or.inr (Or.inr (Or.inr he)))
      exact ⟨⟨lt_of_le_of_ne (show (0 : Interval) ≤ z.1 from z.1.property.1) (Ne.symm h0),
        lt_of_le_of_ne (show z.1 ≤ (1 : Interval) from z.1.property.2) h1⟩,
        ⟨lt_of_le_of_ne (show (0 : Interval) ≤ z.2 from z.2.property.1) (Ne.symm hw0),
        lt_of_le_of_ne (show z.2 ≤ (1 : Interval) from z.2.property.2) hw1⟩⟩
  have oldOne_interior (u : Interval) (hu : u ∈ Ioo (0 : Interval) 1) :
      oldOne u ∈ Ioo (0 : Interval) 1 ×ˢ Ioo (0 : Interval) 1 := by
    rw [squareInterior_iff, oldOne_outer_boundary]
    exact fun he => he.elim (fun he => (ne_of_gt hu.1) he) (fun he => (ne_of_lt hu.2) he)
  have oldOne_trace : range (oneBoundarySquare.comp oldOne) =
      (fun u => q (d.xi u)) '' Icc 0 d.t := by
    have he : oneBoundarySquare.comp oldOne = oldActual := by
      ext u
      exact congrArg Subtype.val (oldOne_actual u)
    rw [he, oldActual_trace]
  have oldActual_a_trace : range oldActual ∩ range a = {d.M.first 1} := by
    ext y
    constructor
    · rintro ⟨⟨u, rfl⟩, ha⟩
      by_cases hu : clockPrefix u ≤ d.s
      · have hinSecond : oldActual u ∈ range d.M.second := by
          rw [d.second_trace]
          exact ⟨clockPrefix u, ⟨(clockPrefix u).property.1, hu⟩, rfl⟩
        have hinDisk : oldActual u ∈ range d.e := by
          have hh : oldActual u ∈ range d.e ∩ range q := by
            rw [d.disk_q_trace]
            exact hinSecond
          exact hh.1
        rw [← d.clean_contact]
        exact ⟨hinDisk, ha, ⟨d.xi (clockPrefix u), rfl⟩⟩
      · exact False.elim (disjoint_left.mp d.tail_exterior
          (show oldActual u ∈ (fun v => q (d.xi v)) '' Ioc d.s d.t from
            ⟨clockPrefix u, ⟨lt_of_not_ge hu, Set.Icc.convexComb_le ht0.le u⟩, rfl⟩)
          (Or.inr ha))
    · intro hy
      rw [mem_singleton_iff] at hy
      rw [hy]
      constructor
      · rw [oldActual_trace]
        exact ⟨d.s, ⟨d.tail_order.1.le, d.tail_order.2.1.le⟩, d.q_corner⟩
      · exact ⟨d.a_corner_parameter, d.a_corner⟩
  have oldOne_far_boundary : oldOne 1 ∈ ActualHarerDiskGluing.squareBoundary :=
    (oldOne_outer_boundary 1).mpr (Or.inr rfl)
  have oldOne_far_positive : (0 : Interval) < (oldOne 1).1 := by
    have hn : oldActual 1 ∉ B := by
      rw [oldActual_boundary]
      exact one_ne_zero
    have hcoord : (oldOne 1).1 ≠ 0 := by
      intro hz
      exact hn ((oldOne_actual 1) ▸ (oneBoundarySquare_boundary _).mpr hz)
    exact lt_of_le_of_ne (show (0 : Interval) ≤ (oldOne 1).1 from (oldOne 1).1.property.1)
      (Ne.symm hcoord)
  have oldOne_far_clear_whole_a : oneBoundarySquare (oldOne 1) ∉ range a :=
    (oldOne_actual 1).symm ▸ far_clear_whole_a
  have boundaryArc_relative_interior :
      boundaryArc '' Ioo (0 : Interval) 1 ⊆ interior (range oneBoundarySquare) := by
    rw [oneBoundarySquare_range, ← h.enlarged_range]
    let e := h.enlargedDisk
    have he : IsEmbedding e := h.enlarged_embedded
    let E := chartAt (EuclideanSpace ℝ (Fin 2)) x
    let p := E x
    let τ : BandWidth → Interval := fun w =>
      ⟨((w : ℝ) + 1) / 2, by constructor <;> linarith [w.property.1, w.property.2]⟩
    have hτc : Continuous τ := by dsimp [τ]; fun_prop
    have hτi : Function.Injective τ := by
      intro v w h
      apply Subtype.ext
      have hh := congrArg Subtype.val h
      dsimp [τ] at hh
      linarith
    let β : BandWidth → ↥Q := fun w => boundaryArc (τ w)
    have hβc : Continuous β := boundaryArc.continuous.comp hτc
    have hβi : Function.Injective β := boundaryArc_embedded.injective.comp hτi
    have hβsphere (w : BandWidth) : β w ∈
        e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      rw [enlarged_two_arc_boundary]
      exact Or.inl (mem_range_self _)
    let v : BandWidth → CapBandGeometry.CapDisk := fun w =>
      he.toHomeomorph.symm ⟨β w, image_subset_range _ _ (hβsphere w)⟩
    have hvimage (w : BandWidth) : e (v w) = β w :=
      congrArg Subtype.val (he.toHomeomorph.apply_symm_apply _)
    have hvnorm (w : BandWidth) : ‖(v w : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
      obtain ⟨z,hz,hzβ⟩ := hβsphere w
      have hvz : v w = z := he.injective ((hvimage w).trans hzβ.symm)
      rw [hvz]
      simpa [Metric.mem_sphere,dist_zero_right] using hz
    have hvc : Continuous v := he.toHomeomorph.symm.continuous.comp (hβc.subtype_mk _)
    have hvi : Function.Injective v := by
      intro w u h
      apply hβi
      exact (hvimage w).symm.trans ((congrArg e h).trans (hvimage u))
    let L : BandWidth × unitInterval → S := fun z =>
      (e (CapBandGeometry.diskRadialStrip v hvnorm z)).val
    have hL : IsEmbedding L := IsEmbedding.subtypeVal.comp
      (he.comp (CapBandGeometry.diskRadialStrip_embedded v hvnorm hvc hvi))
    have hLzero (w : BandWidth) : L (w,0) = (β w).val := by
      dsimp only [L]
      rw [CapBandGeometry.diskRadialStrip_zero, hvimage]
    have hβB (w : BandWidth) : (β w).val ∈ E.symm '' Metric.sphere p R :=
      boundaryArc_in_B (τ w)
    have hβsource (w : BandWidth) : (β w).val ∈ E.source := by
      obtain ⟨z,hz,hzβ⟩ := hβB w
      rw [← hzβ]
      exact E.map_target (htarget (Metric.sphere_subset_closedBall hz))
    have hβcoord (w : BandWidth) : E (β w).val ∈ Metric.sphere p R := by
      obtain ⟨z,hz,hzβ⟩ := hβB w
      rw [← hzβ,E.right_inv (htarget (Metric.sphere_subset_closedBall hz))]
      exact hz
    let u : BandWidth → CapBandGeometry.CapDisk := fun w =>
      ⟨R⁻¹ • (E (β w).val - p), by
        rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hR)]
        have hh : ‖E (β w).val - p‖ = R := by
          simpa only [Metric.mem_sphere,dist_eq_norm] using hβcoord w
        rw [hh,inv_mul_cancel₀ hR.ne']⟩
    have hunorm (w : BandWidth) : ‖(u w : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
      change ‖R⁻¹ • (E (β w).val - p)‖ = 1
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
      have hh : ‖E (β w).val - p‖ = R := by
        simpa only [Metric.mem_sphere,dist_eq_norm] using hβcoord w
      rw [hh,inv_mul_cancel₀ hR.ne']
    have huc : Continuous u := by
      apply Continuous.subtype_mk
      have hc : Continuous (fun w : BandWidth => E (β w).val) :=
        E.continuousOn.comp_continuous
          (continuous_subtype_val.comp hβc) hβsource
      exact (hc.sub continuous_const).const_smul R⁻¹
    have hui : Function.Injective u := by
      intro w z h
      apply hβi
      apply Subtype.ext
      apply E.injOn (hβsource w) (hβsource z)
      have hh := congrArg Subtype.val h
      change R⁻¹ • (E (β w).val - p) = R⁻¹ • (E (β z).val - p) at hh
      exact sub_left_injective ((smul_right_injective _ (inv_ne_zero hR.ne')) hh)
    let d : CapBandGeometry.CapDisk → S := fun z => E.symm (p + R • z.val)
    have hdt (z : CapBandGeometry.CapDisk) : p + R • z.val ∈ E.target := by
      apply htarget
      rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
        Real.norm_eq_abs,abs_of_pos hR]
      have hz : ‖z.val‖ ≤ 1 := by
        have hh := z.property
        change dist z.val (0 : EuclideanSpace ℝ (Fin 2)) ≤ 1 at hh
        simpa only [dist_zero_right] using hh
      nlinarith
    have hdc : Continuous d := E.continuousOn_symm.comp_continuous (by fun_prop) hdt
    have hdi : Function.Injective d := by
      intro z w h
      apply Subtype.ext
      have hh := E.symm.injOn (hdt z) (hdt w) h
      exact (smul_right_injective _ hR.ne') (add_left_cancel hh)
    have hd : IsEmbedding d := (hdc.isClosedEmbedding hdi).isEmbedding
    have huimage (w : BandWidth) : d (u w) = (β w).val := by
      change E.symm (p + R • (R⁻¹ • (E (β w).val - p))) = (β w).val
      rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul,add_sub_cancel,
        E.left_inv (hβsource w)]
    let T : BandWidth × unitInterval → S :=
      d ∘ CapBandGeometry.diskRadialStrip u hunorm
    have hT : IsEmbedding T := hd.comp
      (CapBandGeometry.diskRadialStrip_embedded u hunorm huc hui)
    have hTzero (w : BandWidth) : T (w,0) = (β w).val := by
      dsimp only [T,Function.comp_apply]
      rw [CapBandGeometry.diskRadialStrip_zero,huimage]
    have hTQ (z : BandWidth × unitInterval) (hz : T z ∈ Q) : z.2 = 0 := by
      by_contra hn
      have ht : 0 < (z.2 : ℝ) := lt_of_le_of_ne z.2.property.1
        (fun hh => hn (Subtype.ext hh.symm))
      apply hz
      refine ⟨p + R • (CapBandGeometry.diskRadialStrip u hunorm z).val,?_,rfl⟩
      rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,
        Real.norm_eq_abs,abs_of_pos hR]
      change R * ‖(1-(z.2:ℝ)/2) • (u z.1).val‖ < R
      rw [norm_smul,Real.norm_eq_abs,hunorm,mul_one,
        abs_of_pos (by linarith [z.2.property.2] : 0 < 1-(z.2:ℝ)/2)]
      nlinarith
    have hseam (w : BandWidth) : L (w,0) = T (w,0) :=
      (hLzero w).trans (hTzero w).symm
    have hLT : range L ∩ range T = range (fun w => L (w,0)) := by
      ext y
      constructor
      · rintro ⟨⟨z,rfl⟩,w,hw⟩
        have hwQ : T w ∈ Q := hw ▸ (e (CapBandGeometry.diskRadialStrip v hvnorm z)).property
        have hw0 := hTQ w hwQ
        refine ⟨w.1,?_⟩
        change L (w.1,0) = L z
        rw [hseam]
        exact (congrArg T (show (w.1,0) = w from Prod.ext rfl hw0.symm)).trans hw
      · rintro ⟨w,rfl⟩
        exact ⟨mem_range_self _,⟨(w,0),(hseam w).symm⟩⟩
    have hsub : (Subtype.val : ↥Q → S) ⁻¹' (range L ∪ range T) ⊆ range e := by
      intro y hy
      rcases hy with ⟨z,hz⟩ | ⟨z,hz⟩
      · exact ⟨CapBandGeometry.diskRadialStrip v hvnorm z,Subtype.ext hz⟩
      · have hz0 := hTQ z (hz ▸ y.property)
        have hyβ : (β z.1).val = y.val := by
          exact (hTzero z.1).symm.trans
            ((congrArg T (show (z.1,0) = z from Prod.ext rfl hz0.symm)).trans hz)
        exact (Subtype.ext hyβ) ▸ image_subset_range _ _ (hβsphere z.1)
    rintro y ⟨t,ht,rfl⟩
    let w : BandWidth := ⟨2*(t:ℝ)-1,by constructor <;> linarith [t.property.1,t.property.2]⟩
    have hwlo : (-1 : ℝ) < w := by change -1 < 2*(t:ℝ)-1; linarith [show (0 : ℝ) < t from ht.1]
    have hwhi : (w : ℝ) < 1 := by change 2*(t:ℝ)-1 < 1; linarith [show (t : ℝ) < 1 from ht.2]
    have hτw : τ w = t := by apply Subtype.ext; dsimp [τ,w]; ring
    have hi := glued_half_rectangles_seam_interior_probe L T hL hT hseam hLT w hwlo hwhi
    have hβw : β w = boundaryArc t := by dsimp only [β]; rw [hτw]
    rw [hLzero,hβw] at hi
    exact interior_maximal
      ((preimage_mono interior_subset).trans hsub)
      (isOpen_interior.preimage continuous_subtype_val) hi
  have oneSquare_strict_interior (z : Interval × Interval)
      (hz : z ∈ Ioo (0 : Interval) 1 ×ˢ Ioo (0 : Interval) 1) :
      oneBoundarySquare z ∈ interior (range oneBoundarySquare) := by
    let f : Plane → S := fun v =>
      (oneBoundarySquare (projIcc 0 1 zero_le_one (v 0),
        projIcc 0 1 zero_le_one (v 1))).val
    let U : Set Plane := {v | v 0 ∈ Ioo 0 1 ∧ v 1 ∈ Ioo 0 1}
    have hU : IsOpen U := (isOpen_Ioo.preimage (by fun_prop)).inter
      (isOpen_Ioo.preimage (by fun_prop))
    have hf : Continuous f := continuous_subtype_val.comp
      (oneBoundarySquare.continuous.comp
        ((continuous_projIcc.comp (by fun_prop)).prodMk
          (continuous_projIcc.comp (by fun_prop))))
    have hi : InjOn f U := by
      intro v hv w hw he
      have hh := oneBoundarySquare_embedded.injective (Subtype.ext he)
      have h0 := congrArg (fun p : Interval × Interval => (p.1 : ℝ)) hh
      have h1 := congrArg (fun p : Interval × Interval => (p.2 : ℝ)) hh
      simp only [projIcc_of_mem zero_le_one ⟨hv.1.1.le, hv.1.2.le⟩,
        projIcc_of_mem zero_le_one ⟨hw.1.1.le, hw.1.2.le⟩] at h0
      simp only [projIcc_of_mem zero_le_one ⟨hv.2.1.le, hv.2.2.le⟩,
        projIcc_of_mem zero_le_one ⟨hw.2.1.le, hw.2.2.le⟩] at h1
      ext i
      fin_cases i
      · exact h0
      · exact h1
    have hopen : IsOpen (f '' U) :=
      surface_invariance_of_domain_probe f U hU hf.continuousOn hi
    have hsub : (Subtype.val : ↥Q → S) ⁻¹' (f '' U) ⊆ range oneBoundarySquare := by
      rintro y ⟨v, hv, he⟩
      exact ⟨(projIcc 0 1 zero_le_one (v 0), projIcc 0 1 zero_le_one (v 1)),
        Subtype.ext he⟩
    apply (hopen.preimage continuous_subtype_val).subset_interior_iff.mpr hsub
    refine ⟨Plane.mk z.1 z.2, ⟨hz.1, hz.2⟩, ?_⟩
    simp [f, projIcc_of_mem zero_le_one z.1.property,
      projIcc_of_mem zero_le_one z.2.property]
  -- Residual 1: fix the whole B edge and mark the actual far endpoint.
  obtain ⟨K, K_left, K_outer, K_far, K_far_width⟩ :
      ∃ K : (Interval × Interval) ≃ₜ (Interval × Interval),
        (∀ z, z.1 = 0 → K z = z) ∧
        (∀ z, K z ∈ ActualHarerDiskGluing.squareBoundary ↔
          z ∈ ActualHarerDiskGluing.squareBoundary) ∧
        (K.symm (oldOne 1)).1 = 1 ∧
        (K.symm (oldOne 1)).2 ∈ Ioo (0 : Interval) 1 := by
    let p := oldOne 1
    have hp : p ∈ ActualHarerDiskGluing.squareBoundary := oldOne_far_boundary
    have hx : (0 : Interval) < p.1 := oldOne_far_positive
    classical
    let A : Set Plane := (sideBottom ∪ sideRight) ∪ sideTop
    have hA : IsArcBetween A cornerSW cornerNW := by
      apply isArcBetween_lowerSides.concatenate isArcBetween_sideTop
      intro z hz ht
      rcases hz with hb | hr
      · have hb1 := (mem_sideBottom.mp hb).1
        have ht1 := (mem_sideTop.mp ht).1
        linarith
      · exact (by
          ext i
          fin_cases i
          · exact (mem_sideRight.mp hr).1
          · exact (mem_sideTop.mp ht).1 : z = cornerNE)
    have hRA : sideLeft ∩ A = {cornerSW, cornerNW} := by
      ext z
      constructor
      · rintro ⟨hl, (hb | hr) | ht⟩
        · left
          ext i
          fin_cases i
          · exact (mem_sideLeft.mp hl).1
          · exact (mem_sideBottom.mp hb).1
        · have h0 := (mem_sideLeft.mp hl).1
          have h1 := (mem_sideRight.mp hr).1
          linarith
        · right
          ext i
          fin_cases i
          · exact (mem_sideLeft.mp hl).1
          · exact (mem_sideTop.mp ht).1
      · rintro (rfl | rfl)
        · exact ⟨isArcBetween_sideLeft.right_mem, Or.inl (Or.inl isArcBetween_sideBottom.left_mem)⟩
        · exact ⟨isArcBetween_sideLeft.left_mem, Or.inr isArcBetween_sideTop.right_mem⟩
    have hC : sideLeft ∪ A = modelCurve := by
      rw [modelCurve_eq_sides]
      dsimp [A]
      ext z
      simp only [mem_union]
      tauto
    let L : Interval × Interval → Plane := fun z => Plane.mk (2*(z.1:ℝ)-1) (2*(z.2:ℝ)-1)
    have hLc : Continuous L := by dsimp [L,Plane.mk]; fun_prop
    have hLi : Function.Injective L := by
      intro z w he
      apply Prod.ext <;> apply Subtype.ext
      · have hh := congrArg (fun v : Plane => v 0) he
        change 2*(z.1:ℝ)-1=2*(w.1:ℝ)-1 at hh
        linarith
      · have hh := congrArg (fun v : Plane => v 1) he
        change 2*(z.2:ℝ)-1=2*(w.2:ℝ)-1 at hh
        linarith
    have hLsquare (z : Interval × Interval) : L z ∈ Plane.closedSquare 0 1 := by
      rw [mem_closedSquare_zero_one]
      change max |2*(z.1:ℝ)-1| |2*(z.2:ℝ)-1| ≤ 1
      rw [max_le_iff]
      constructor <;> apply abs_le.mpr
      · change -1 ≤ 2*(z.1:ℝ)-1 ∧ 2*(z.1:ℝ)-1 ≤ 1
        constructor <;> linarith [z.1.property.1,z.1.property.2]
      · change -1 ≤ 2*(z.2:ℝ)-1 ∧ 2*(z.2:ℝ)-1 ≤ 1
        constructor <;> linarith [z.2.property.1,z.2.property.2]
    let LC : Interval × Interval → ↥(Plane.closedSquare 0 1) := fun z => ⟨L z,hLsquare z⟩
    have hLCc : Continuous LC := hLc.subtype_mk _
    have hLCb : Function.Bijective LC := by
      constructor
      · intro z w he
        exact hLi (congrArg Subtype.val he)
      · intro y
        have hy := mem_closedSquare_zero_one.mp y.property
        change max |y.val 0| |y.val 1| ≤ 1 at hy
        rw [max_le_iff] at hy
        have hy0 := abs_le.mp hy.1
        have hy1 := abs_le.mp hy.2
        let z : Interval × Interval := (⟨(y.val 0+1)/2,by constructor <;> linarith⟩,
          ⟨(y.val 1+1)/2,by constructor <;> linarith⟩)
        refine ⟨z,?_⟩
        apply Subtype.ext
        ext i
        fin_cases i <;> dsimp [LC,L,z,Plane.mk] <;> ring
    let J : (Interval × Interval) ≃ₜ ↥(Plane.closedSquare 0 1) :=
      hLCc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective LC hLCb)
    have hJ (z : Interval × Interval) : (J z).val = L z := rfl
    have hLleft (z : Interval × Interval) : L z ∈ sideLeft ↔ z.1 = 0 := by
      rw [mem_sideLeft]
      constructor
      · intro hz
        apply Subtype.ext
        change (z.1:ℝ)=0
        have hh := hz.1
        change 2*(z.1:ℝ)-1 = -1 at hh
        linarith
      · intro hz
        change 2*(z.1:ℝ)-1 = -1 ∧ |2*(z.2:ℝ)-1| ≤ 1
        rw [hz]
        constructor
        · norm_num [L,Plane.mk]
        · change |2*(z.2:ℝ)-1| ≤ 1
          apply abs_le.mpr
          constructor <;> linarith [z.2.property.1,z.2.property.2]
    have hLboundary (z : Interval × Interval) : L z ∈ modelCurve ↔
        z ∈ ActualHarerDiskGluing.squareBoundary := by
      rw [modelCurve_eq_sides]
      simp only [mem_union,mem_sideTop,mem_sideLeft,mem_sideBottom,mem_sideRight]
      have hxB : |2*(z.1:ℝ)-1| ≤ 1 := by
        apply abs_le.mpr; constructor <;> linarith [z.1.property.1,z.1.property.2]
      have hyB : |2*(z.2:ℝ)-1| ≤ 1 := by
        apply abs_le.mpr; constructor <;> linarith [z.2.property.1,z.2.property.2]
      change ((2*(z.2:ℝ)-1=1 ∧ |2*(z.1:ℝ)-1| ≤ 1) ∨
        (2*(z.1:ℝ)-1 = -1 ∧ |2*(z.2:ℝ)-1| ≤ 1)) ∨
        (2*(z.2:ℝ)-1 = -1 ∧ |2*(z.1:ℝ)-1| ≤ 1) ∨
        (2*(z.1:ℝ)-1=1 ∧ |2*(z.2:ℝ)-1| ≤ 1) ↔ _
      simp only [hxB,hyB,and_true]
      change _ ↔ z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1
      constructor
      · rintro ((ht | hl) | hb | hr)
        · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by change (z.2:ℝ)=1; linarith))))
        · exact Or.inl (Subtype.ext (by change (z.1:ℝ)=0; linarith))
        · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by change (z.2:ℝ)=0; linarith))))
        · exact Or.inr (Or.inl (Subtype.ext (by change (z.1:ℝ)=1; linarith)))
      · rintro (he | he | he | he)
        · rw [he]; norm_num
        · rw [he]; norm_num
        · rw [he]; norm_num
        · rw [he]; norm_num
    have hpA : L p ∈ A := by
      have hpC := (hLboundary p).mpr hp
      rw [← hC] at hpC
      rcases hpC with hpl | hpa
      · exact False.elim ((ne_of_gt hx) ((hLleft p).mp hpl))
      · exact hpa
    let m : Interval × Interval := (1,⟨1/2,by norm_num⟩)
    have hmA : L m ∈ A := by
      left; right
      rw [mem_sideRight]
      norm_num [L,m,Plane.mk]
    have hAkeep := hA
    obtain ⟨f,hfc,hfi,hfr,hf0,hf1⟩ := hAkeep
    let fI : Interval → Plane := fun u => f u
    have hfIc : Continuous fI := hfc.restrict
    have hfIi : Function.Injective fI := by
      intro u v he
      exact Subtype.ext (hfi u.property v.property he)
    have hfIE : IsEmbedding fI := (hfIc.isClosedEmbedding hfIi).isEmbedding
    have hfIr : range fI = A := by
      rw [← hfr]
      ext z
      constructor
      · rintro ⟨u,rfl⟩
        exact ⟨u,u.property,rfl⟩
      · rintro ⟨u,hu,rfl⟩
        exact ⟨⟨u,hu⟩,rfl⟩
    let e : Interval ≃ₜ ↥A := hfIE.toHomeomorph.trans (Homeomorph.setCongr hfIr)
    have he (u : Interval) : (e u).val = f u := rfl
    have he0 : (e 0).val = cornerSW := hf0
    have he1 : (e 1).val = cornerNW := hf1
    let v : Interval := e.symm ⟨L m,hmA⟩
    let w : Interval := e.symm ⟨L p,hpA⟩
    have hev : (e v).val = L m := congrArg Subtype.val (e.apply_symm_apply _)
    have hew : (e w).val = L p := congrArg Subtype.val (e.apply_symm_apply _)
    have hclockInterior (z : Interval × Interval) (hz : (0:Interval)<z.1)
        (hzA : L z ∈ A) : e.symm ⟨L z,hzA⟩ ∈ Ioo (0:Interval) 1 := by
      let u := e.symm ⟨L z,hzA⟩
      have heu : (e u).val = L z := congrArg Subtype.val (e.apply_symm_apply _)
      have hn0 : u ≠ 0 := by
        intro hu
        have hh := heu.symm.trans ((congrArg (fun t => (e t).val) hu).trans he0)
        have h0 := congrArg (fun t : Plane => t 0) hh
        change 2*(z.1:ℝ)-1 = -1 at h0
        have hz0 : 0<(z.1:ℝ) := hz
        linarith
      have hn1 : u ≠ 1 := by
        intro hu
        have hh := heu.symm.trans ((congrArg (fun t => (e t).val) hu).trans he1)
        have h0 := congrArg (fun t : Plane => t 0) hh
        change 2*(z.1:ℝ)-1 = -1 at h0
        have hz0 : 0<(z.1:ℝ) := hz
        linarith
      exact ⟨lt_of_le_of_ne (show (0:Interval)≤u from u.property.1) (Ne.symm hn0),
        lt_of_le_of_ne (show u≤(1:Interval) from u.property.2) hn1⟩
    obtain ⟨H,hHends,hHvw,hHmono⟩ := interval_point_isotopy v w
      (hclockInterior m (by norm_num [m]) hmA) (hclockInterior p hx hpA)
    obtain ⟨k,hk⟩ := H.homeomorphism_at 1
    have hk0 : k 0=0 := (hk 0).trans (hHends 1).1
    have hk1 : k 1=1 := (hk 1).trans (hHends 1).2
    have hkvw : k v=w := (hk v).trans hHvw
    let ae : ↥A ≃ₜ ↥A := (e.symm.trans k).trans e
    have hae0 : ae ⟨cornerSW,hA.left_mem⟩ = ⟨cornerSW,hA.left_mem⟩ := by
      apply e.symm.injective
      have hh : e.symm ⟨cornerSW,hA.left_mem⟩=0 := by
        apply e.injective
        rw [e.apply_symm_apply]
        apply Subtype.ext
        exact he0.symm
      simpa [ae,hh,hk0]
    have hae1 : ae ⟨cornerNW,hA.right_mem⟩ = ⟨cornerNW,hA.right_mem⟩ := by
      apply e.symm.injective
      have hh : e.symm ⟨cornerNW,hA.right_mem⟩=1 := by
        apply e.injective
        rw [e.apply_symm_apply]
        apply Subtype.ext
        exact he1.symm
      simpa [ae,hh,hk1]
    have haem : (ae ⟨L m,hmA⟩).val=L p := by
      change (e (k v)).val=L p
      rw [hkvw]
      exact hew
    let af : Plane → Plane := fun z => if hz:z∈A then (ae ⟨z,hz⟩).val else z
    let ag : Plane → Plane := fun z => if hz:z∈A then (ae.symm ⟨z,hz⟩).val else z
    have haf (z : Plane) (hz:z∈A) : af z=(ae ⟨z,hz⟩).val := by simp [af,hz]
    have hag (z : Plane) (hz:z∈A) : ag z=(ae.symm ⟨z,hz⟩).val := by simp [ag,hz]
    let aHomeo : ArcHomeo A A cornerSW cornerNW cornerSW cornerNW := {
      toFun:=af
      invFun:=ag
      continuousOn_toFun:=by
        rw [continuousOn_iff_continuous_restrict]
        exact (continuous_subtype_val.comp ae.continuous).congr (fun z => (haf z z.property).symm)
      continuousOn_invFun:=by
        rw [continuousOn_iff_continuous_restrict]
        exact (continuous_subtype_val.comp ae.symm.continuous).congr (fun z => (hag z z.property).symm)
      leftInvOn:=by
        intro z hz
        rw [haf z hz,hag _ (ae ⟨z,hz⟩).property]
        exact congrArg Subtype.val (ae.symm_apply_apply _)
      rightInvOn:=by
        intro z hz
        rw [hag z hz,haf _ (ae.symm ⟨z,hz⟩).property]
        exact congrArg Subtype.val (ae.apply_symm_apply _)
      image_eq:=by
        ext z
        constructor
        · rintro ⟨y,hy,rfl⟩
          rw [haf y hy]
          exact (ae ⟨y,hy⟩).property
        · intro hz
          refine ⟨(ae.symm ⟨z,hz⟩).val,(ae.symm ⟨z,hz⟩).property,?_⟩
          rw [haf]
          exact congrArg Subtype.val (ae.apply_symm_apply _)
      map_left:=(haf _ hA.left_mem).trans (congrArg Subtype.val hae0)
      map_right:=(haf _ hA.right_mem).trans (congrArg Subtype.val hae1) }
    obtain ⟨F,G,hFG,hFleft,hFA,hFimage⟩ := exists_closed_subdisk_homeomorph_fixing_arc
      isArcBetween_sideLeft.reverse hA hA hRA hRA aHomeo
    have hClosed : (sideLeft∪A)∪inside (sideLeft∪A)=Plane.closedSquare 0 1 := by
      rw [hC, modelCurve_union_inside]
    rw [hClosed] at hFG
    let eFG : ↥(Plane.closedSquare 0 1) ≃ₜ ↥(Plane.closedSquare 0 1) := {
      toFun:=fun z=>⟨F z,hFG.mapsTo z.property⟩
      invFun:=fun z=>⟨G z,hFG.mapsTo_inv z.property⟩
      left_inv:=by intro z; exact Subtype.ext (hFG.invOn.1 z.property)
      right_inv:=by intro z; exact Subtype.ext (hFG.invOn.2 z.property)
      continuous_toFun:=hFG.continuousOn.restrict.subtype_mk _
      continuous_invFun:=hFG.continuousOn_inv.restrict.subtype_mk _ }
    let K := (J.trans eFG).trans J.symm
    have hK (z : Interval × Interval) : L (K z)=F (L z) := by
      have hh := J.apply_symm_apply (eFG (J z))
      exact congrArg Subtype.val hh
    have hKleft (z : Interval × Interval) (hz:z.1=0) : K z=z := by
      apply hLi
      rw [hK]
      exact hFleft _ ((hLleft z).mpr hz)
    have hKBoundary (z : Interval × Interval) : K z ∈ ActualHarerDiskGluing.squareBoundary ↔
        z ∈ ActualHarerDiskGluing.squareBoundary := by
      have hFC : F '' modelCurve=modelCurve := by
        rw [← hC,image_union]
        have hFR : F '' sideLeft=sideLeft := by
          ext y
          constructor
          · rintro ⟨z,hz,rfl⟩
            rw [hFleft z hz]; exact hz
          · intro hy
            exact ⟨y,hy,hFleft y hy⟩
        rw [hFR,hFimage]
      rw [← hLboundary,← hLboundary,hK]
      constructor
      · intro hz
        rw [← hFC] at hz
        obtain ⟨y,hy,hey⟩ := hz
        have hh : y=L z := hFG.injOn
          (modelCurve_subset_closedSquare hy) (hLsquare z) hey
        exact hh ▸ hy
      · intro hz
        rw [← hFC]
        exact ⟨L z,hz,rfl⟩
    have hKm : K m=p := by
      apply hLi
      rw [hK,hFA _ hmA]
      exact (haf _ hmA).trans haem
    have hKfar : K.symm p=m := by
      apply K.injective
      rw [K.apply_symm_apply,hKm]
    refine ⟨K,hKleft,hKBoundary,?_,?_⟩
    · rw [hKfar]
    · rw [hKfar]
      change (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1
      norm_num

  let E : C(Interval × Interval, ↥Q) := oneBoundarySquare.comp ⟨K, K.continuous⟩
  let old : C(Interval, Interval × Interval) :=
    ⟨fun u => K.symm (oldOne u), K.symm.continuous.comp oldOne.continuous⟩
  have E_embedded : IsEmbedding E := oneBoundarySquare_embedded.comp K.isEmbedding
  have E_range : range E = range d.e ∪ range h.H := by
    change range (oneBoundarySquare ∘ K) = _
    rw [K.surjective.range_comp, oneBoundarySquare_range]
  have K_left_iff (z : Interval × Interval) : (K z).1 = 0 ↔ z.1 = 0 := by
    constructor
    · intro he
      have hh : K z = z := K.injective (K_left (K z) he)
      exact (congrArg Prod.fst hh).symm.trans he
    · intro he
      rw [K_left z he]
      exact he
  have E_boundary (z : Interval × Interval) : E z ∈ B ↔ z.1 = 0 := by
    change oneBoundarySquare (K z) ∈ B ↔ _
    rw [oneBoundarySquare_boundary, K_left_iff]
  -- Residual 2: openness is in the literal original Q, including its B edge.
  have E_relative_open : IsOpen (E '' {z | z.1 < 1 ∧ z.2 ∈ Ioo (0 : Interval) 1}) := by
    let Ω : Set (Interval × Interval) := {z | z.1 < 1 ∧ z.2 ∈ Ioo (0 : Interval) 1}
    have hΩ : IsOpen Ω := (isOpen_lt continuous_fst continuous_const).inter
      (isOpen_Ioo.preimage continuous_snd)
    obtain ⟨O, hO, heq⟩ := E_embedded.isInducing.image_eq_isOpen_inter_range hΩ
    have hint : E '' Ω ⊆ interior (range E) := by
      rintro y ⟨z, hz, rfl⟩
      have hEOne : range E = range oneBoundarySquare := by
        rw [E_range, oneBoundarySquare_range]
      rw [hEOne]
      by_cases hx : z.1 = 0
      · have hpoint : E z = boundaryArc z.2 := by
          change P (rotateSquare (K z)) = _
          rw [K_left z hx]
          change P (z.2, unitInterval.symm z.1) = _
          rw [hx, unitInterval.symm_zero, P_top]
        rw [hpoint]
        exact boundaryArc_relative_interior ⟨z.2, hz.2, rfl⟩
      · have hzint : z ∈ Ioo (0 : Interval) 1 ×ˢ Ioo (0 : Interval) 1 :=
          ⟨⟨lt_of_le_of_ne (show (0 : Interval) ≤ z.1 from z.1.property.1)
            (Ne.symm hx), hz.1⟩, hz.2⟩
        have hKint : K z ∈ Ioo (0 : Interval) 1 ×ˢ Ioo (0 : Interval) 1 := by
          rw [squareInterior_iff, K_outer]
          exact (squareInterior_iff _).mp hzint
        exact oneSquare_strict_interior (K z) hKint
    have hi : E '' Ω = O ∩ interior (range E) := by
      apply Subset.antisymm
      · intro y hy
        exact ⟨(heq ▸ hy).1, hint hy⟩
      · intro y hy
        rw [heq]
        exact ⟨hy.1, interior_subset hy.2⟩
    change IsOpen (E '' Ω)
    rw [hi]
    exact hO.inter isOpen_interior
  have old_embedded : IsEmbedding old := K.symm.isEmbedding.comp oldOne_embedded
  have old_zero_eq : old 0 = oldOne 0 := by
    apply K.injective
    change K (K.symm (oldOne 0)) = K (oldOne 0)
    rw [K.apply_symm_apply, K_left _ oldOne_zero]
  have old_zero : (old 0).1 = 0 := (congrArg Prod.fst old_zero_eq).trans oldOne_zero
  have old_zero_width : (old 0).2 ∈ Ioo (0 : Interval) 1 :=
    (congrArg Prod.snd old_zero_eq).symm ▸ oldOne_zero_width
  have old_one : (old 1).1 = 1 := K_far
  have far_width : (old 1).2 ∈ Ioo (0 : Interval) 1 := K_far_width
  have old_interior (u : Interval) (hu : u ∈ Ioo (0 : Interval) 1) :
      old u ∈ Ioo (0 : Interval) 1 ×ˢ Ioo (0 : Interval) 1 := by
    apply (squareInterior_iff _).mpr
    intro hb
    have hh : oldOne u ∈ ActualHarerDiskGluing.squareBoundary := by
      have hmem := (K_outer (old u)).mpr hb
      change K (K.symm (oldOne u)) ∈ _ at hmem
      rw [K.apply_symm_apply] at hmem
      exact hmem
    exact (squareInterior_iff _).mp (oldOne_interior u hu) hh
  have old_actual (u : Interval) : E (old u) = oldActual u := by
    change oneBoundarySquare (K (K.symm (oldOne u))) = _
    rw [K.apply_symm_apply, oldOne_actual]
  have old_trace : range (E.comp old) = (fun u => q (d.xi u)) '' Icc 0 d.t := by
    have he : E.comp old = oldActual := by
      ext u
      exact congrArg Subtype.val (old_actual u)
    rw [he, oldActual_trace]
  have outerRail_clear_disk (u : Interval) : outerRail u ∉ range d.e := by
    intro hu
    have hs : outerRail u ∈ range d.sideArc := by
      rw [← h.disk_intersection]
      exact ⟨mem_range_self (u,1), hu⟩
    obtain ⟨v, hv⟩ := hs
    have hh : h.H (u,1) = h.H (v,0) := hv.symm.trans (h.seam v).symm
    have hw := congrArg Prod.snd (h.H_embedded.injective hh)
    exact one_ne_zero hw
  have first_in_cell (u : Interval) : d.M.first u ∈ range E := by
    rw [E_range]
    left
    have hh : d.M.first u ∈ range d.e ∩ range a := by
      rw [d.disk_a_trace]
      exact mem_range_self u
    exact hh.1
  have first_off_B (u : Interval) (hu : u ≠ 0) : d.M.first u ∉ B := by
    by_cases hu1 : u = 1
    · rw [hu1]
      exact d.M.corner_off_boundary
    · exact d.M.first_interior u
        ⟨lt_of_le_of_ne (show (0 : Interval) ≤ u from u.property.1) (Ne.symm hu),
         lt_of_le_of_ne (show u ≤ (1 : Interval) from u.property.2) hu1⟩
  have first_not_sphere (u : Interval) (hu : u ≠ 0) :
      d.M.first u ∉ h.enlargedDisk '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} := by
    rw [enlarged_two_arc_boundary]
    rintro (hb | ht)
    · have hinB : d.M.first u ∈ B := by
        obtain ⟨v, hv⟩ := hb
        exact hv ▸ boundaryArc_in_B v
      exact first_off_B u hu hinB
    · obtain ⟨v, hv⟩ := ht
      apply outerRail_clear_disk v
      rw [hv]
      have hh : d.M.first u ∈ range d.e ∩ range a := by
        rw [d.disk_a_trace]
        exact mem_range_self u
      exact hh.1
  have E_outer_boundary : E '' ActualHarerDiskGluing.squareBoundary =
      h.enlargedDisk '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} := by
    rw [← oneBoundarySquare_outer_boundary]
    ext y
    constructor
    · rintro ⟨z, hz, he⟩
      exact ⟨K z, (K_outer z).mpr hz, he⟩
    · rintro ⟨z, hz, he⟩
      refine ⟨K.symm z, ?_, ?_⟩
      · apply (K_outer _).mp
        rw [K.apply_symm_apply]
        exact hz
      · change oneBoundarySquare (K (K.symm z)) = y
        rw [K.apply_symm_apply]
        exact he
  let firstCell : C(Interval, range E) :=
    ⟨fun u => ⟨d.M.first u, first_in_cell u⟩, d.M.first.continuous.subtype_mk _⟩
  let firstLift : C(Interval, Interval × Interval) :=
    ⟨fun u => E_embedded.toHomeomorph.symm (firstCell u),
      E_embedded.toHomeomorph.symm.continuous.comp firstCell.continuous⟩
  have firstLift_actual (u : Interval) : E (firstLift u) = d.M.first u :=
    congrArg Subtype.val (E_embedded.toHomeomorph.apply_symm_apply (firstCell u))
  have firstLift_zero : (firstLift 0).1 = 0 :=
    (E_boundary _).mp ((firstLift_actual 0).symm ▸ d.M.first_zero_boundary)
  have firstLift_zero_width : (firstLift 0).2 ∈ Ioo (0 : Interval) 1 := by
    have hleft (w : Interval) : E (0,w) = boundaryArc w := by
      change P (rotateSquare (K (0,w))) = _
      rw [K_left (0,w) rfl]
      change P (w, unitInterval.symm 0) = _
      rw [unitInterval.symm_zero, P_top]
    have hn (w : Interval) (hw : w = 0 ∨ w = 1) : (firstLift 0).2 ≠ w := by
      intro he
      have hz : firstLift 0 = (0,w) := Prod.ext firstLift_zero he
      have hβ : boundaryArc w = d.M.first 0 :=
        (hleft w).symm.trans ((congrArg E hz).symm.trans (firstLift_actual 0))
      have hout : d.M.first 0 ∈ range outerRail := by
        rcases hw with rfl | rfl
        · exact ⟨0, boundaryArc_zero_eq.symm.trans hβ⟩
        · exact ⟨1, boundaryArc_one_eq.symm.trans hβ⟩
      obtain ⟨u, hu⟩ := hout
      apply outerRail_clear_disk u
      rw [hu]
      have hmem : d.M.first 0 ∈ range d.e ∩ range a := by
        rw [d.disk_a_trace]
        exact mem_range_self 0
      exact hmem.1
    exact ⟨lt_of_le_of_ne (show (0 : Interval) ≤ (firstLift 0).2 from (firstLift 0).2.property.1)
        (Ne.symm (hn 0 (Or.inl rfl))),
      lt_of_le_of_ne (show (firstLift 0).2 ≤ (1 : Interval) from (firstLift 0).2.property.2)
        (hn 1 (Or.inr rfl))⟩
  have firstLift_positive_interior (u : Interval) (hu : u ≠ 0) :
      firstLift u ∈ Ioo (0 : Interval) 1 ×ˢ Ioo (0 : Interval) 1 := by
    rw [squareInterior_iff]
    intro hb
    apply first_not_sphere u hu
    rw [← E_outer_boundary]
    exact ⟨firstLift u, hb, firstLift_actual u⟩
  let core : Set ↥Q := E '' {z | z.1 < 1 ∧ z.2 ∈ Ioo (0 : Interval) 1}
  have core_open : IsOpen core := E_relative_open
  have first_in_core : range d.M.first ⊆ core := by
    rintro y ⟨u, rfl⟩
    refine ⟨firstLift u, ?_, firstLift_actual u⟩
    by_cases hu : u = 0
    · rw [hu]
      exact ⟨by rw [firstLift_zero]; exact zero_lt_one, firstLift_zero_width⟩
    · have hh := firstLift_positive_interior u hu
      exact ⟨hh.1.2, hh.2⟩
  have a_corner_interior : d.a_corner_parameter ∈ Ioo (0 : Interval) 1 := by
    have hn0 : d.a_corner_parameter ≠ 0 := by
      intro he
      exact d.M.corner_off_boundary (d.a_corner ▸ (he ▸ d.a_ends.1))
    have hn1 : d.a_corner_parameter ≠ 1 := by
      intro he
      exact d.M.corner_off_boundary (d.a_corner ▸ (he ▸ d.a_ends.2))
    exact ⟨lt_of_le_of_ne (show (0 : Interval) ≤ d.a_corner_parameter from
        d.a_corner_parameter.property.1) (Ne.symm hn0),
      lt_of_le_of_ne (show d.a_corner_parameter ≤ (1 : Interval) from
        d.a_corner_parameter.property.2) hn1⟩
  obtain ⟨a_start, a_start_eq⟩ := d.M.first_on_a (mem_range_self 0)
  have a_start_end : a_start = 0 ∨ a_start = 1 := by
    by_contra hn
    push_neg at hn
    exact d.a_interior a_start
      ⟨lt_of_le_of_ne (show (0 : Interval) ≤ a_start from a_start.property.1) (Ne.symm hn.1),
       lt_of_le_of_ne (show a_start ≤ (1 : Interval) from a_start.property.2) hn.2⟩
      (a_start_eq ▸ d.M.first_zero_boundary)
  obtain ⟨a_start_ne_corner, first_original_clock⟩ :=
    ActualHarerCornerGeometry.embedded_subarc_parameter_interval a d.M.first
      d.a_embedded d.M.first_embedded d.M.first_on_a a_start d.a_corner_parameter
      a_start_eq d.a_corner
  let properA : CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.ProperArc S x R :=
    ⟨a, d.a_embedded, d.a_ends.1, d.a_ends.2, d.a_interior⟩
  obtain ⟨aStrip, aStrip_embedded, aStrip_center, aStrip_ends,
    aStrip_interior, aStrip_open⟩ :=
    CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.source_actual_boundary_proper_arc_strip
      S x R g hg hS hR htarget properA
  let aAmbient : C(Interval, S) := ⟨fun u => (a u).val,
    continuous_subtype_val.comp a.continuous⟩
  let aStripAmbient : Interval × BandWidth → S := fun z => (aStrip z).val
  have aAmbient_embedded : IsEmbedding aAmbient := IsEmbedding.subtypeVal.comp d.a_embedded
  have aStripAmbient_embedded : IsEmbedding aStripAmbient :=
    IsEmbedding.subtypeVal.comp aStrip_embedded
  have aStripAmbient_center (u : Interval) :
      aStripAmbient (u,⟨0,by norm_num⟩) = aAmbient u :=
    congrArg Subtype.val (aStrip_center u)
  obtain ⟨coreAmbient, coreAmbient_open, coreAmbient_preimage⟩ :=
    IsEmbedding.subtypeVal.isInducing.isOpen_iff.mp core_open
  let V : Set S := coreAmbient ∩ d.cornerChart.source
  have V_open : IsOpen V := coreAmbient_open.inter d.cornerChart.open_source
  have V_in_Q : V ⊆ Q := fun y hy => interior_subset (d.axis_interior hy.2)
  have V_in_core (y : S) (hy : y ∈ V) : (⟨y,V_in_Q hy⟩ : ↥Q) ∈ core := by
    rw [← coreAmbient_preimage]
    exact hy.1
  have corner_in_V : aAmbient d.a_corner_parameter ∈ V := by
    constructor
    · have hcore : a d.a_corner_parameter ∈ core :=
        d.a_corner.symm ▸ first_in_core (mem_range_self 1)
      rw [← coreAmbient_preimage] at hcore
      exact hcore
    · exact d.axes.center_mem
  obtain ⟨widthFactor, widthFactor_bounds, stripSign, stripDelta, stripEta, F,
    stripSign_cases, stripDelta_pos, stripEta_pos, F_fixes_whole_a, F_outside_V,
    calibrated_formula⟩ := source_internal_collar_calibration aAmbient aAmbient_embedded
      aStripAmbient aStripAmbient_embedded aStripAmbient_center d.a_corner_parameter
      a_corner_interior d.cornerChart d.axes.center_mem d.axes.center_zero
      (fun u hu => (d.axes.anchor_axis _ hu).mp (mem_range_self u))
      univ V isOpen_univ V_open (subset_univ V) corner_in_V (subset_univ _)
  have F_preserves_Q (y : S) (hy : y ∈ Q) : F y ∈ Q := by
    by_contra hn
    have hout : F y ∉ V := fun hv => hn (V_in_Q hv)
    have hfix := F_outside_V (F y) hout
    have hh : F y = y := F.injective hfix
    exact hn (hh.symm ▸ hy)
  have Finv_preserves_Q (y : S) (hy : y ∈ Q) : F.symm y ∈ Q := by
    by_contra hn
    have hout : F.symm y ∉ V := fun hv => hn (V_in_Q hv)
    have hfix := F_outside_V (F.symm y) hout
    rw [F.apply_symm_apply] at hfix
    exact hn (hfix ▸ hy)
  let FQ : ↥Q ≃ₜ ↥Q := {
    toFun := fun y => ⟨F y, F_preserves_Q y y.property⟩
    invFun := fun y => ⟨F.symm y, Finv_preserves_Q y y.property⟩
    left_inv := by intro y; exact Subtype.ext (F.symm_apply_apply y)
    right_inv := by intro y; exact Subtype.ext (F.apply_symm_apply y)
    continuous_toFun := (F.continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (F.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
  have FQ_fixes_whole_a (u : Interval) : FQ (a u) = a u :=
    Subtype.ext (F_fixes_whole_a u)
  have FQ_preserves_core (y : ↥Q) : FQ y ∈ core ↔ y ∈ core := by
    constructor
    · intro hy
      by_contra hn
      have hout : y.val ∉ V := by
        intro hv
        exact hn (V_in_core y hv)
      have hfix : FQ y = y := Subtype.ext (F_outside_V y hout)
      exact hn (hfix ▸ hy)
    · intro hy
      by_contra hn
      have hout : (FQ y).val ∉ V := by
        intro hv
        exact hn (V_in_core (FQ y) hv)
      have hfix : FQ (FQ y) = FQ y := Subtype.ext (F_outside_V (FQ y) hout)
      exact hn ((FQ.injective hfix).symm ▸ hy)
  let calibratedA : C(Interval × BandWidth, ↥Q) := ⟨FQ ∘ aStrip,
    FQ.continuous.comp aStrip.continuous⟩
  have calibratedA_embedded : IsEmbedding calibratedA := FQ.isEmbedding.comp aStrip_embedded
  have calibratedA_center (u : Interval) : calibratedA (u,⟨0,by norm_num⟩) = a u := by
    change FQ (aStrip (u,⟨0,by norm_num⟩)) = _
    rw [aStrip_center, FQ_fixes_whole_a]
  have calibratedA_clear (u : Interval) (w : BandWidth) (hw : (w : ℝ) ≠ 0) :
      calibratedA (u,w) ∉ range a := by
    rintro ⟨v,hv⟩
    have hh : calibratedA (v,⟨0,by norm_num⟩) = calibratedA (u,w) :=
      (calibratedA_center v).trans hv
    have hz := congrArg Prod.snd (calibratedA_embedded.injective hh)
    exact hw (congrArg Subtype.val hz).symm
  let selectedClock : C(Interval, Interval) :=
    ⟨Set.Icc.convexComb a_start d.a_corner_parameter,
      Set.Icc.continuous_convexComb a_start d.a_corner_parameter⟩
  have selectedClock_zero : selectedClock 0 = a_start := by
    exact Set.Icc.convexComb_zero a_start d.a_corner_parameter
  have selectedClock_one : selectedClock 1 = d.a_corner_parameter := by
    exact Set.Icc.convexComb_one a_start d.a_corner_parameter
  have selectedClock_injective : Function.Injective selectedClock := by
    intro u v he
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    change (1-(u:ℝ))*(a_start:ℝ)+(u:ℝ)*(d.a_corner_parameter:ℝ)=
      (1-(v:ℝ))*(a_start:ℝ)+(v:ℝ)*(d.a_corner_parameter:ℝ) at hh
    have hn : (a_start:ℝ) ≠ (d.a_corner_parameter:ℝ) :=
      fun h => a_start_ne_corner (Subtype.ext h)
    apply (mul_left_cancel₀ (sub_ne_zero.mpr hn.symm))
    nlinarith
  have selectedClock_range : range selectedClock = uIcc a_start d.a_corner_parameter := by
    have hUniv : (univ : Set Interval) = Icc (0 : Interval) 1 := by
      ext z
      simp only [mem_univ,mem_Icc,true_iff]
      exact z.property
    have hr : range selectedClock = uIcc (selectedClock 0) (selectedClock 1) := by
      rw [← image_univ,hUniv]
      rcases selectedClock.continuous.strictMono_of_inj_boundedOrder' selectedClock_injective with hm | hm
      · rw [selectedClock.continuous.continuousOn.image_Icc_of_monotoneOn zero_le_one
          (hm.monotone.monotoneOn _)]
        exact (uIcc_of_le (hm zero_lt_one).le).symm
      · rw [selectedClock.continuous.continuousOn.image_Icc_of_antitoneOn zero_le_one
          (hm.antitone.antitoneOn _)]
        exact (uIcc_of_ge (hm zero_lt_one).le).symm
    rw [hr, selectedClock_zero, selectedClock_one]
  let selectedStrip : C(Interval × BandWidth, ↥Q) :=
    ⟨fun z => calibratedA (selectedClock z.1,z.2),
      calibratedA.continuous.comp ((selectedClock.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  have selectedCoordinates_injective : Function.Injective
      (fun z : Interval × BandWidth => (selectedClock z.1,z.2)) := by
    intro z w he
    have h0 := congrArg (fun r : Interval × BandWidth => r.1) he
    have h1 := congrArg (fun r : Interval × BandWidth => r.2) he
    exact Prod.ext (selectedClock_injective h0) h1
  have selectedStrip_embedded : IsEmbedding selectedStrip :=
    (selectedStrip.continuous.isClosedEmbedding
      (calibratedA_embedded.injective.comp selectedCoordinates_injective)).isEmbedding
  have selectedStrip_center_in_core (u : Interval) : selectedStrip (u,⟨0,by norm_num⟩) ∈ core := by
    change calibratedA (selectedClock u,⟨0,by norm_num⟩) ∈ _
    rw [calibratedA_center]
    apply first_in_core
    rw [first_original_clock]
    exact ⟨selectedClock u, selectedClock_range ▸ mem_range_self u, rfl⟩
  obtain ⟨selectedScale, selectedScale_bounds, narrowSelected,
    narrowSelected_embedded, narrowSelected_in_core, narrowSelected_exact,
    narrowSelected_center⟩ := source_shrink_embedded_strip_in_open selectedStrip
      selectedStrip_embedded core core_open selectedStrip_center_in_core
  have first_whole_q_collision (u v : Interval) (he : d.M.first u = q v) : u = 1 := by
    have hinDisk : d.M.first u ∈ range d.e := by
      have hh : d.M.first u ∈ range d.e ∩ range a := by
        rw [d.disk_a_trace]
        exact mem_range_self u
      exact hh.1
    have hcorner : d.M.first u = d.M.first 1 := by
      apply mem_singleton_iff.mp
      rw [← d.clean_contact]
      exact ⟨hinDisk, d.M.first_on_a (mem_range_self u), ⟨v,he.symm⟩⟩
    exact d.M.first_embedded.injective hcorner
  have selectedCenter_whole_q_collision (u v : Interval)
      (he : a (selectedClock u) = q v) : selectedClock u = d.a_corner_parameter := by
    have hf : a (selectedClock u) ∈ range d.M.first := by
      rw [first_original_clock]
      exact ⟨selectedClock u, selectedClock_range ▸ mem_range_self u, rfl⟩
    obtain ⟨w,hw⟩ := hf
    have hw1 := first_whole_q_collision w v (hw.trans he)
    exact d.a_embedded.injective ((hw.symm.trans (congrArg d.M.first hw1)).trans d.a_corner.symm)
  let remoteSelected : Set Interval :=
    {u | stripEta / 2 ≤ |(selectedClock u : ℝ) - (d.a_corner_parameter : ℝ)|}
  have remoteSelected_compact : IsCompact remoteSelected :=
    (isClosed_le continuous_const (by fun_prop)).isCompact
  have qRange_closed : IsClosed (range q) :=
    (isCompact_range q.continuous).isClosed
  let stripAvoidQ : Set (Interval × BandWidth) := selectedStrip ⁻¹' (range q)ᶜ
  have stripAvoidQ_open : IsOpen stripAvoidQ := qRange_closed.isOpen_compl.preimage selectedStrip.continuous
  have remoteCenter_avoids_q : remoteSelected ×ˢ ({⟨0,by norm_num⟩} : Set BandWidth) ⊆ stripAvoidQ := by
    rintro ⟨u,w⟩ ⟨hu,hw⟩
    have hw0 : w = ⟨0,by norm_num⟩ := hw
    subst w
    rintro ⟨v,hv⟩
    have hcenter : selectedStrip (u,⟨0,by norm_num⟩) = a (selectedClock u) :=
      calibratedA_center (selectedClock u)
    have hc := selectedCenter_whole_q_collision u v (hcenter.symm.trans hv.symm)
    have habs : |(selectedClock u : ℝ) - (d.a_corner_parameter : ℝ)| = 0 := by
      rw [hc,sub_self,abs_zero]
    change stripEta/2 ≤ |(selectedClock u:ℝ)-(d.a_corner_parameter:ℝ)| at hu
    rw [habs] at hu
    linarith [stripEta_pos]
  obtain ⟨remoteA, remoteW, remoteA_open, remoteW_open, remoteA_contains,
    remoteW_zero, remoteProduct_avoids⟩ := generalized_tube_lemma
      remoteSelected_compact isCompact_singleton stripAvoidQ_open remoteCenter_avoids_q
  let clipWidth : ℝ → BandWidth := projIcc (-1) 1 (by norm_num)
  have remoteZero_preimage : (0 : ℝ) ∈ clipWidth ⁻¹' remoteW := by
    simpa [clipWidth,projIcc_of_mem] using
      remoteW_zero (mem_singleton (⟨0,by norm_num⟩ : BandWidth))
  obtain ⟨remoteWidth, remoteWidth_pos, remoteWidth_ball⟩ := Metric.mem_nhds_iff.mp
    ((remoteW_open.preimage continuous_projIcc).mem_nhds remoteZero_preimage)
  have remoteWidth_avoids_q (u : Interval) (hu : u ∈ remoteSelected)
      (w : BandWidth) (hw : |(w : ℝ)| < remoteWidth) : selectedStrip (u,w) ∉ range q := by
    apply remoteProduct_avoids
    constructor
    · exact remoteA_contains hu
    · have hb : (w : ℝ) ∈ Metric.ball (0 : ℝ) remoteWidth := by
        simpa [Metric.mem_ball,Real.dist_eq] using hw
      simpa [clipWidth,projIcc_of_mem _ w.property] using remoteWidth_ball hb
  have FQ_fixes_B (y : ↥Q) (hy : y ∈ B) : FQ y = y := by
    apply Subtype.ext
    apply F_outside_V
    intro hv
    have hin := d.axis_interior hv.2
    rw [CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.exterior_interior_eq_complement_chart_closed_disk
      S g hS x R hR htarget] at hin
    exact hin (Or.inr hy)
  have FQ_B_iff (y : ↥Q) : FQ y ∈ B ↔ y ∈ B := by
    constructor
    · intro hy
      have hh := FQ.injective (FQ_fixes_B (FQ y) hy)
      exact hh ▸ hy
    · intro hy
      rw [FQ_fixes_B y hy]
      exact hy
  let pushWidthBound : ℝ := min (selectedScale/2) (min (remoteWidth/2) (1/2))
  have pushWidthBound_pos : 0 < pushWidthBound := by
    dsimp [pushWidthBound]
    exact lt_min (half_pos selectedScale_bounds.1)
      (lt_min (half_pos remoteWidth_pos) (by norm_num))
  have pushWidthBound_scale : pushWidthBound < selectedScale :=
    (min_le_left _ _).trans_lt (half_lt_self selectedScale_bounds.1)
  have pushWidthBound_remote : pushWidthBound < remoteWidth :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self remoteWidth_pos)
  have pushWidthBound_one : pushWidthBound < 1 := by
    have hh := (min_le_right (selectedScale/2) (min (remoteWidth/2) (1/2))).trans
      (min_le_right (remoteWidth/2) (1/2))
    dsimp [pushWidthBound]
    linarith
  let qForward : C(Interval, ↥Q) := h.H.comp h.eta
  have qForward_exact (u : Interval) : qForward u = q (d.xi (Set.Icc.convexComb d.s d.t u)) :=
    h.eta_exact_parameter u
  have qForward_zero : qForward 0 = a d.a_corner_parameter := by
    rw [qForward_exact,Set.Icc.convexComb_zero,d.q_corner,d.a_corner]
  let chartSmall : Set S := d.cornerChart.source ∩
    d.cornerChart ⁻¹' {v : Plane | |v 1| < stripDelta*pushWidthBound}
  have chartSmall_open : IsOpen chartSmall := d.cornerChart.isOpen_inter_preimage
    (isOpen_lt (by fun_prop) continuous_const)
  have qForward_small_open : IsOpen ((fun u => (qForward u).val) ⁻¹' chartSmall) :=
    chartSmall_open.preimage (continuous_subtype_val.comp qForward.continuous)
  have qForward_zero_small : (0 : Interval) ∈ (fun u => (qForward u).val) ⁻¹' chartSmall := by
    rw [mem_preimage,qForward_zero]
    refine ⟨d.axes.center_mem, ?_⟩
    change |d.cornerChart (a d.a_corner_parameter).val 1| < stripDelta*pushWidthBound
    rw [d.axes.center_zero]
    simpa using mul_pos stripDelta_pos pushWidthBound_pos
  obtain ⟨qSmallRadius, qSmallRadius_pos, qSmallRadius_ball⟩ := Metric.mem_nhds_iff.mp
    (qForward_small_open.mem_nhds qForward_zero_small)
  let forwardCut : Interval := ⟨min (qSmallRadius/2) (1/2),by
    constructor
    · positivity
    · exact (min_le_right _ _).trans (by norm_num)⟩
  have forwardCut_strict : forwardCut ∈ Ioo (0 : Interval) 1 := by
    constructor
    · change (0 : ℝ) < min (qSmallRadius/2) (1/2)
      positivity
    · change min (qSmallRadius/2) (1/2) < (1 : ℝ)
      exact (min_le_right _ _).trans_lt (by norm_num)
  have forwardCut_small : (qForward forwardCut).val ∈ chartSmall := by
    apply qSmallRadius_ball
    rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq,Set.Icc.coe_zero,sub_zero,
      abs_of_pos (show (0 : ℝ) < forwardCut from forwardCut_strict.1)]
    exact (min_le_left _ _).trans_lt (half_lt_self qSmallRadius_pos)
  let r₀ : Interval := Set.Icc.convexComb d.s d.t forwardCut
  have r₀_order : d.s < r₀ ∧ r₀ < d.t := by
    have hs : (d.s : ℝ) < d.t := d.tail_order.2.1
    have hu0 : (0 : ℝ) < forwardCut := forwardCut_strict.1
    have hu1 : (forwardCut : ℝ) < 1 := forwardCut_strict.2
    constructor <;> change _ < _
    · change (d.s:ℝ) < (1-(forwardCut:ℝ))*(d.s:ℝ)+(forwardCut:ℝ)*(d.t:ℝ)
      nlinarith
    · change (1-(forwardCut:ℝ))*(d.s:ℝ)+(forwardCut:ℝ)*(d.t:ℝ) < (d.t:ℝ)
      nlinarith
  have qr₀_source : (q (d.xi r₀)).val ∈ d.cornerChart.source :=
    (qForward_exact forwardCut) ▸ forwardCut_small.1
  have qr₀_small : |d.cornerChart (q (d.xi r₀)).val 1| < stripDelta*pushWidthBound :=
    (qForward_exact forwardCut) ▸ forwardCut_small.2
  have stripSign_sq : stripSign*stripSign = 1 := by
    rcases stripSign_cases with rfl | rfl <;> norm_num
  have stripSign_ne : stripSign ≠ 0 := by
    rcases stripSign_cases with rfl | rfl <;> norm_num
  have stripSign_abs : |stripSign|=1 := by
    rcases stripSign_cases with rfl | rfl <;> norm_num
  let selectedWidthValue : ℝ := d.cornerChart (q (d.xi r₀)).val 1 / (stripSign*stripDelta)
  have selectedWidth_small : |selectedWidthValue| < pushWidthBound := by
    dsimp only [selectedWidthValue]
    rw [abs_div,abs_mul,stripSign_abs,abs_of_pos stripDelta_pos,one_mul]
    exact (div_lt_iff₀ stripDelta_pos).mpr (by simpa [mul_comm] using qr₀_small)
  have selectedWidth_ne : selectedWidthValue ≠ 0 := by
    intro hn
    have hy0 : d.cornerChart (q (d.xi r₀)).val 1 = 0 :=
      (div_eq_zero_iff.mp hn).resolve_right (mul_ne_zero stripSign_ne stripDelta_pos.ne')
    have hh := d.outgoing_axis_order r₀ r₀_order.1 qr₀_source
    rw [hy0,mul_zero] at hh
    exact lt_irrefl _ hh
  let selectedWidth : BandWidth := ⟨selectedWidthValue,
    (abs_le.mp ((selectedWidth_small.trans pushWidthBound_one).le))⟩
  let actualWidth : BandWidth := ⟨widthFactor*(selectedWidth:ℝ),by
    constructor <;> nlinarith [selectedWidth.property.1,selectedWidth.property.2,
      widthFactor_bounds.1,widthFactor_bounds.2]⟩
  have actualWidth_ne : (actualWidth : ℝ) ≠ 0 :=
    mul_ne_zero widthFactor_bounds.1.ne' selectedWidth_ne
  have actualWidth_small : |(actualWidth : ℝ)| < pushWidthBound := by
    change |widthFactor*selectedWidthValue| < pushWidthBound
    rw [abs_mul,abs_of_pos widthFactor_bounds.1]
    exact (mul_le_mul_of_nonneg_right widthFactor_bounds.2 (abs_nonneg _)).trans_lt
      (by simpa using selectedWidth_small)
  let pushFirst : C(Interval, ↥Q) := ⟨fun u => selectedStrip (u,actualWidth),
    selectedStrip.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have pushFirst_embedded : IsEmbedding pushFirst :=
    (pushFirst.continuous.isClosedEmbedding (by
      intro u v he
      exact congrArg Prod.fst (selectedStrip_embedded.injective he))).isEmbedding
  have pushFirst_clear_whole_a : Disjoint (range pushFirst) (range a) := by
    apply disjoint_left.mpr
    rintro y ⟨u,rfl⟩ ha
    exact calibratedA_clear (selectedClock u) actualWidth actualWidth_ne ha
  have pushFirst_in_core (u : Interval) : pushFirst u ∈ core := by
    have hbound : |(actualWidth : ℝ)| ≤ selectedScale :=
      (actualWidth_small.trans pushWidthBound_scale).le
    let w : BandWidth := ⟨(actualWidth : ℝ)/selectedScale,by
      have habs : |(actualWidth:ℝ)| / selectedScale ≤ 1 :=
        (div_le_one selectedScale_bounds.1).mpr hbound
      rw [← abs_of_pos selectedScale_bounds.1, ← abs_div] at habs
      exact abs_le.mp habs⟩
    have he : pushFirst u = narrowSelected (u,w) := by
      rw [narrowSelected_exact]
      apply congrArg selectedStrip
      apply Prod.ext
      · rfl
      apply Subtype.ext
      change (actualWidth:ℝ) = selectedScale*((actualWidth:ℝ)/selectedScale)
      exact (mul_div_cancel₀ _ selectedScale_bounds.1.ne').symm
    rw [he]
    exact narrowSelected_in_core (mem_range_self (u,w))
  have pushFirst_one : pushFirst 1 = q (d.xi r₀) := by
    apply Subtype.ext
    have hform := calibrated_formula d.a_corner_parameter selectedWidth (by simpa using stripEta_pos)
    have haSource : aAmbient d.a_corner_parameter ∈ d.cornerChart.source := d.axes.center_mem
    have hqAxis := (d.axes.moving_axis _ qr₀_source).mp (mem_range_self (d.xi r₀))
    change (calibratedA (selectedClock 1,actualWidth)).val = _
    rw [selectedClock_one]
    apply d.cornerChart.injOn hform.1 qr₀_source
    rw [hform.2]
    have hcenter0 : d.cornerChart (aAmbient d.a_corner_parameter) = 0 := d.axes.center_zero
    rw [hcenter0]
    ext i
    fin_cases i
    · exact hqAxis.symm
    · change stripSign*stripDelta*(d.cornerChart (q (d.xi r₀)).val 1/(stripSign*stripDelta)) =
        d.cornerChart (q (d.xi r₀)).val 1
      exact mul_div_cancel₀ _ (mul_ne_zero stripSign_ne stripDelta_pos.ne')
  have pushFirst_whole_q_collision (u v : Interval) (he : pushFirst u = q v) : u = 1 := by
    by_cases hu : u ∈ remoteSelected
    · exact False.elim (remoteWidth_avoids_q u hu actualWidth
        (actualWidth_small.trans pushWidthBound_remote) ⟨v,he.symm⟩)
    · have hnear : |(selectedClock u : ℝ)-(d.a_corner_parameter:ℝ)| < stripEta := by
        change ¬ stripEta/2 ≤ _ at hu
        exact (lt_of_not_ge hu).trans (half_lt_self stripEta_pos)
      have hform := calibrated_formula (selectedClock u) selectedWidth hnear
      have hcenter := calibrated_formula (selectedClock u) (⟨0,by norm_num⟩ : BandWidth) hnear
      have haSource : aAmbient (selectedClock u) ∈ d.cornerChart.source := by
        simpa only [Subtype.coe_mk,mul_zero,aStripAmbient_center,F_fixes_whole_a] using hcenter.1
      have hqSource : (q v).val ∈ d.cornerChart.source := (congrArg Subtype.val he) ▸ hform.1
      have hqAxis := (d.axes.moving_axis _ hqSource).mp (mem_range_self v)
      have hx : d.cornerChart (aAmbient (selectedClock u)) 0 = 0 := by
        have hh := congrArg (fun z : Plane => z 0) hform.2
        have hv := congrArg (fun y : ↥Q => d.cornerChart y.val 0) he
        change d.cornerChart (calibratedA (selectedClock u,actualWidth)).val 0 = _ at hv
        change d.cornerChart (calibratedA (selectedClock u,actualWidth)).val 0 =
          d.cornerChart (aAmbient (selectedClock u)) 0 at hh
        rw [hv,hqAxis] at hh
        exact hh.symm
      have hy := (d.axes.anchor_axis _ haSource).mp (mem_range_self (selectedClock u))
      have hzero : d.cornerChart (aAmbient (selectedClock u)) = 0 := by
        ext i
        fin_cases i <;> assumption
      have haEq : aAmbient (selectedClock u) = aAmbient d.a_corner_parameter :=
        d.cornerChart.injOn haSource d.axes.center_mem (hzero.trans d.axes.center_zero.symm)
      have hc : selectedClock u = d.a_corner_parameter := aAmbient_embedded.injective haEq
      exact selectedClock_injective (hc.trans selectedClock_one.symm)
  have selectedClock_positive_interior (u : Interval) (hu : u ≠ 0) :
      selectedClock u ∈ Ioo (0 : Interval) 1 := by
    have hu0 : (0 : ℝ) < u := lt_of_le_of_ne u.property.1 (fun he => hu (Subtype.ext he.symm))
    have hc0 : (0 : ℝ) < d.a_corner_parameter := a_corner_interior.1
    have hc1 : (d.a_corner_parameter : ℝ) < 1 := a_corner_interior.2
    have hu1 := u.property.2
    rcases a_start_end with hs | hs
    · dsimp only [selectedClock,ContinuousMap.coe_mk]
      rw [hs]
      constructor
      · change 0 < (1-(u:ℝ))*0+(u:ℝ)*(d.a_corner_parameter:ℝ)
        nlinarith
      · change (1-(u:ℝ))*0+(u:ℝ)*(d.a_corner_parameter:ℝ) < 1
        nlinarith
    · dsimp only [selectedClock,ContinuousMap.coe_mk]
      rw [hs]
      constructor
      · change 0 < (1-(u:ℝ))*1+(u:ℝ)*(d.a_corner_parameter:ℝ)
        nlinarith
      · change (1-(u:ℝ))*1+(u:ℝ)*(d.a_corner_parameter:ℝ) < 1
        nlinarith
  have pushFirst_zero_B : pushFirst 0 ∈ B := by
    change FQ (aStrip (selectedClock 0,actualWidth)) ∈ B
    rw [FQ_B_iff,selectedClock_zero]
    rcases a_start_end with hs | hs
    · rw [hs]
      exact (aStrip_ends actualWidth).1
    · rw [hs]
      exact (aStrip_ends actualWidth).2
  have pushFirst_positive_off_B (u : Interval) (hu : u ≠ 0) : pushFirst u ∉ B := by
    change FQ (aStrip (selectedClock u,actualWidth)) ∉ B
    rw [FQ_B_iff]
    exact aStrip_interior _ (selectedClock_positive_interior u hu) actualWidth
  let tailClock : C(Interval, Interval) :=
    ⟨Set.Icc.convexComb r₀ d.t, Set.Icc.continuous_convexComb r₀ d.t⟩
  have tailClock_zero : tailClock 0 = r₀ := Set.Icc.convexComb_zero r₀ d.t
  have tailClock_one : tailClock 1 = d.t := Set.Icc.convexComb_one r₀ d.t
  have tailClock_injective : Function.Injective tailClock := by
    intro u v he
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    change (1-(u:ℝ))*(r₀:ℝ)+(u:ℝ)*(d.t:ℝ)=
      (1-(v:ℝ))*(r₀:ℝ)+(v:ℝ)*(d.t:ℝ) at hh
    have hrt : (r₀ : ℝ) < d.t := r₀_order.2
    nlinarith
  have tailClock_range : range tailClock = Icc r₀ d.t := by
    have hUniv : (univ : Set Interval) = Icc (0 : Interval) 1 := by
      ext z
      simp only [mem_univ,mem_Icc,true_iff]
      exact z.property
    have hm : StrictMono tailClock := by
      intro u v huv
      change (1-(u:ℝ))*(r₀:ℝ)+(u:ℝ)*(d.t:ℝ) <
        (1-(v:ℝ))*(r₀:ℝ)+(v:ℝ)*(d.t:ℝ)
      have hrt : (r₀ : ℝ) < d.t := r₀_order.2
      have huv' : (u : ℝ) < v := huv
      nlinarith
    rw [← image_univ,hUniv]
    rw [tailClock.continuous.continuousOn.image_Icc_of_monotoneOn zero_le_one
      (hm.monotone.monotoneOn _),tailClock_zero,tailClock_one]
  let tailActual : C(Interval, ↥Q) := qOriented.comp tailClock
  have tailActual_embedded : IsEmbedding tailActual :=
    d.q_embedded.comp (d.xi.isEmbedding.comp
      (tailClock.continuous.isClosedEmbedding tailClock_injective).isEmbedding)
  have tailActual_zero : tailActual 0 = q (d.xi r₀) := by
    change q (d.xi (tailClock 0)) = _
    rw [tailClock_zero]
  have tailActual_one : tailActual 1 = q (d.xi d.t) := by
    change q (d.xi (tailClock 1)) = _
    rw [tailClock_one]
  have tailActual_trace : range tailActual = (fun v => q (d.xi v)) '' Icc r₀ d.t := by
    change range ((fun v => q (d.xi v)) ∘ tailClock) = _
    rw [range_comp,tailClock_range]
  have tailActual_in_cell : range tailActual ⊆ range E := by
    intro y hy
    rw [tailActual_trace] at hy
    obtain ⟨v,hv,rfl⟩ := hy
    have hprefix : q (d.xi v) ∈ range (E.comp old) := by
      rw [old_trace]
      exact ⟨v,⟨(r₀_order.1.trans_le hv.1).le.trans' d.tail_order.1.le,hv.2⟩,rfl⟩
    obtain ⟨u,hu⟩ := hprefix
    exact ⟨old u,hu⟩
  have tailActual_clear_whole_a : Disjoint (range tailActual) (range a) := by
    apply disjoint_left.mpr
    intro y hy ha
    rw [tailActual_trace] at hy
    obtain ⟨v,hv,hvy⟩ := hy
    apply disjoint_left.mp d.tail_exterior
    · exact ⟨v,⟨r₀_order.1.trans_le hv.1,hv.2⟩,hvy⟩
    · exact Or.inr ha
  have pushFirst_tail_meet : range pushFirst ∩ range tailActual = {pushFirst 1} := by
    ext y
    constructor
    · rintro ⟨⟨u,rfl⟩,v,hv⟩
      have hu := pushFirst_whole_q_collision u (d.xi (tailClock v)) hv.symm
      rw [hu]
      exact mem_singleton _
    · intro hy
      rw [mem_singleton_iff] at hy
      rw [hy]
      exact ⟨mem_range_self 1,⟨0,tailActual_zero.trans pushFirst_one.symm⟩⟩
  obtain ⟨newActual, newActual_embedded, newActual_zero, newActual_one, newActual_range⟩ :=
    source_embedded_arc_concatenation pushFirst tailActual pushFirst_embedded tailActual_embedded
      (pushFirst_one.trans tailActual_zero.symm) pushFirst_tail_meet
  have newActual_in_cell : range newActual ⊆ range E := by
    rw [newActual_range]
    apply union_subset
    · rintro y ⟨u,rfl⟩
      exact image_subset_range _ _ (pushFirst_in_core u)
    · exact tailActual_in_cell
  have newActual_clear_whole_a : Disjoint (range newActual) (range a) := by
    rw [newActual_range]
    exact disjoint_union_left.mpr ⟨pushFirst_clear_whole_a,tailActual_clear_whole_a⟩
  let newCell : C(Interval, range E) :=
    ⟨fun u => ⟨newActual u,newActual_in_cell (mem_range_self u)⟩,
      newActual.continuous.subtype_mk _⟩
  let new : C(Interval, Interval × Interval) :=
    ⟨fun u => E_embedded.toHomeomorph.symm (newCell u),
      E_embedded.toHomeomorph.symm.continuous.comp newCell.continuous⟩
  have new_actual (u : Interval) : E (new u) = newActual u :=
    congrArg Subtype.val (E_embedded.toHomeomorph.apply_symm_apply (newCell u))
  have newCell_embedded : IsEmbedding newCell := by
    apply IsEmbedding.of_comp newCell.continuous continuous_subtype_val
    exact newActual_embedded
  have new_embedded : IsEmbedding new :=
    E_embedded.toHomeomorph.symm.isEmbedding.comp newCell_embedded
  have new_zero : (new 0).1 = 0 :=
    (E_boundary _).mp ((new_actual 0).symm ▸ (newActual_zero.symm ▸ pushFirst_zero_B))
  have new_zero_width : (new 0).2 ∈ Ioo (0 : Interval) 1 := by
    obtain ⟨z,hz,he⟩ := pushFirst_in_core 0
    have hh : z = new 0 := E_embedded.injective
      (he.trans (newActual_zero.symm.trans (new_actual 0).symm))
    exact hh ▸ hz.2
  have same_far_endpoint : old 1 = new 1 := by
    apply E_embedded.injective
    rw [old_actual,new_actual,newActual_one,tailActual_one,oldActual_one]
  have new_one : (new 1).1 = 1 := same_far_endpoint ▸ old_one
  have prefixSphere_iff (v : Interval) (hv : v ∈ Icc (0 : Interval) d.t) :
      q (d.xi v) ∈ h.enlargedDisk '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} ↔
        v = 0 ∨ v = d.t := by
    obtain ⟨u,hu⟩ := (clockPrefix_range.symm ▸ hv : v ∈ range clockPrefix)
    rw [← hu]
    change oldActual u ∈ _ ↔ clockPrefix u=0 ∨ clockPrefix u=d.t
    rw [oldActual_outer_boundary]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl clockPrefix_zero
      · exact Or.inr clockPrefix_one
    · rintro (he | he)
      · exact Or.inl (clockPrefix_injective (he.trans clockPrefix_zero.symm))
      · exact Or.inr (clockPrefix_injective (he.trans clockPrefix_one.symm))
  have new_interior (u : Interval) (hu : u ∈ Ioo (0 : Interval) 1) :
      new u ∈ Ioo (0 : Interval) 1 ×ˢ Ioo (0 : Interval) 1 := by
    rw [squareInterior_iff]
    intro hb
    have hSphere : newActual u ∈ h.enlargedDisk '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} := by
      rw [← E_outer_boundary]
      exact ⟨new u,hb,new_actual u⟩
    have hmem : newActual u ∈ range newActual := mem_range_self u
    rw [newActual_range] at hmem
    rcases hmem with ⟨v,hv⟩ | ⟨v,hv⟩
    · obtain ⟨z,hz,hez⟩ := pushFirst_in_core v
      have hnB : pushFirst v ∈ B := by
        have hzb : z ∈ ActualHarerDiskGluing.squareBoundary := by
          have hzz : z = new u := E_embedded.injective
            (hez.trans (hv.trans (new_actual u).symm))
          exact hzz.symm ▸ hb
        have hx0 : z.1 = 0 := by
          rcases hzb with hx | hx | hw0 | hw1
          · exact hx
          · exact False.elim ((ne_of_lt hz.1) hx)
          · exact False.elim ((ne_of_gt hz.2.1) hw0)
          · exact False.elim ((ne_of_lt hz.2.2) hw1)
        exact hez ▸ (E_boundary z).mpr hx0
      have hv0 : v = 0 := by
        by_contra hn
        exact pushFirst_positive_off_B v hn hnB
      have hu0 : u=0 := newActual_embedded.injective
        (hv.symm.trans ((congrArg pushFirst hv0).trans newActual_zero.symm))
      exact (ne_of_gt hu.1) hu0
    · have hclock : tailClock v ∈ Icc r₀ d.t := tailClock_range ▸ mem_range_self v
      have hprefix : tailClock v ∈ Icc (0 : Interval) d.t :=
        ⟨(d.tail_order.1.trans r₀_order.1).le.trans hclock.1,hclock.2⟩
      have hterminal := (prefixSphere_iff (tailClock v) hprefix).mp (hv ▸ hSphere)
      rcases hterminal with hn0 | ht
      · have hpos : (0 : Interval) < tailClock v :=
          (d.tail_order.1.trans r₀_order.1).trans_le hclock.1
        exact (ne_of_gt hpos) hn0
      · have hv1 : v=1 := tailClock_injective (ht.trans tailClock_one.symm)
        have hu1 : u=1 := newActual_embedded.injective
          (hv.symm.trans ((congrArg tailActual hv1).trans newActual_one.symm))
        exact (ne_of_lt hu.2) hu1
  have new_clear_whole_a : Disjoint (range (E.comp new)) (range a) := by
    have he : E.comp new = newActual := by
      ext u
      exact congrArg Subtype.val (new_actual u)
    rw [he]
    exact newActual_clear_whole_a
  exact ⟨{
    E := E
    E_embedded := E_embedded
    E_range := E_range
    E_boundary := E_boundary
    E_relative_open := E_relative_open
    old := old
    new := new
    old_embedded := old_embedded
    new_embedded := new_embedded
    old_zero := old_zero
    new_zero := new_zero
    old_one := old_one
    new_one := new_one
    old_zero_width := old_zero_width
    new_zero_width := new_zero_width
    same_far_endpoint := same_far_endpoint
    far_width := far_width
    old_interior := old_interior
    new_interior := new_interior
    old_trace := old_trace
    new_clear_whole_a := new_clear_whole_a }⟩

end CoherentEndpointMotion.RelativeCleanHalfAlignment
