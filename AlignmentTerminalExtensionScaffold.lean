import AlignmentHalfMoveScaffold
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
import CurveComplexGenusTwo.Topology.ActualRegionalCompatibleReturn.RegionalHalfDiskContactCleanup

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

open Set Topology CurveComplex
open scoped Manifold ContDiff

/-! A source-derived induction-state bridge for the approved simultaneous-
alignment statement.  This is deliberately a conditional helper: its
processed set, current isotopy, and partial terminal matches are induction
state supplied by the protected theorem's proof, not new premises of that
theorem.  The proof is left as the next formal obligation. -/

/-- Extend one partial finite alignment at terminal time.

The boundary circle `B` is preserved setwise at every time.  Processed arcs may
move during `K`; the only processed-label preservation required here is the
terminal equation on their original target ranges.  No pointwise or all-time
graph fixation, common boundary clock, or fixed-endpoint homotopy is assumed. -/
theorem original_disjoint_essential_arc_system_partial_alignment_terminal_extension
    (S : Type) [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ (J : Type) [Fintype J] (a b : J → C(Interval, ↥Q)),
      (∀ i, IsEmbedding (a i) ∧ IsEmbedding (b i)) →
      (∀ i, a i 0 ∈ B ∧ a i 1 ∈ B ∧ b i 0 ∈ B ∧ b i 1 ∈ B) →
      (∀ i t, t ∈ Set.Ioo (0 : Interval) 1 → a i t ∉ B ∧ b i t ∉ B) →
      (∀ i, ¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧
        (∀ t, c t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
          IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range (a i) ∪ Set.range c) →
      (∀ i, ¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧
        (∀ t, c t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
          IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range (b i) ∪ Set.range c) →
      (∀ i j, i ≠ j → Disjoint (Set.range (a i)) (Set.range (a j)) ∧
        Disjoint (Set.range (b i)) (Set.range (b j))) →
      (∀ i j, i ≠ j → ¬ ∃ H : AmbientIsotopy ↥Q,
        (∀ t, (fun y => H.map (t, y)) '' B = B) ∧
        H.finalMap '' Set.range (a i) = Set.range (a j)) →
      (∀ i, ∃ H : AmbientIsotopy ↥Q,
        (∀ t, (fun y => H.map (t, y)) '' B = B) ∧
        H.finalMap '' Set.range (a i) = Set.range (b i)) →
      ∀ (P : Finset J) (i : J), i ∉ P →
      ∀ (H : AmbientIsotopy ↥Q),
        (∀ t, (fun y => H.map (t, y)) '' B = B) →
        (∀ j ∈ P, H.finalMap '' Set.range (a j) = Set.range (b j)) →
        ∃ K : AmbientIsotopy ↥Q,
          (∀ t, (fun y => K.map (t, y)) '' B = B) ∧
          (∀ j ∈ P, K.finalMap '' Set.range (b j) = Set.range (b j)) ∧
          K.finalMap '' (H.finalMap '' Set.range (a i)) = Set.range (b i) := by
  classical
  intro Q B J instJ a b hemb hends hmid haessential hbessential
    hdisjoint hdistinct hclasses P i hi H hHB hProcessed
  by_cases hMatched : H.finalMap '' Set.range (a i) = Set.range (b i)
  · refine ⟨AmbientIsotopy.identity ↥Q, ?_, ?_, ?_⟩
    · intro t; exact Set.image_id B
    · intro j hj; exact Set.image_id (Set.range (b j))
    · change id '' (H.finalMap '' Set.range (a i)) = Set.range (b i)
      rw [Set.image_id]
      exact hMatched
  obtain ⟨e, he⟩ := H.homeomorphism_at 1
  have hFinal : ∀ y : ↥Q, e y = H.finalMap y := he
  have heB : e '' B = B := by
    calc
      e '' B = (fun y => H.map ((1 : Interval), y)) '' B :=
        congrArg (fun f : ↥Q → ↥Q => f '' B) (funext he)
      _ = B := hHB 1
  have heInvB : e.symm '' B = B := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, rfl⟩ := (show z ∈ e '' B from heB.symm ▸ hz)
      simpa only [e.symm_apply_apply] using hw
    · intro hy
      exact ⟨e y, heB ▸ ⟨y, hy, rfl⟩, e.symm_apply_apply y⟩
  let L : AmbientIsotopy ↥Q := {
    map := ⟨fun p => H.map (unitInterval.symm p.1, e.symm p.2),
      H.map.continuous.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk
        (e.symm.continuous.comp continuous_snd))⟩
    homeomorphism_at := by
      intro t
      obtain ⟨f, hf⟩ := H.homeomorphism_at (unitInterval.symm t)
      exact ⟨e.symm.trans f, fun y => hf (e.symm y)⟩
    at_zero := by
      intro y
      change H.map (unitInterval.symm 0, e.symm y) = y
      rw [unitInterval.symm_zero]
      exact (he (e.symm y)).symm.trans (e.apply_symm_apply y) }
  have hLFinal : ∀ y : ↥Q, L.finalMap y = e.symm y := by
    intro y
    change H.map (unitInterval.symm 1, e.symm y) = e.symm y
    rw [unitInterval.symm_one]
    exact H.at_zero _
  have hLB : ∀ t, (fun y => L.map (t, y)) '' B = B := by
    intro t
    change (fun y => H.map (unitInterval.symm t, e.symm y)) '' B = B
    rw [← Set.image_image (fun y => H.map (unitInterval.symm t, y)) e.symm,
      heInvB, hHB (unitInterval.symm t)]
  have hLeft : ∀ y : ↥Q, L.finalMap (H.finalMap y) = y := by
    intro y
    rw [hLFinal, ← hFinal, e.symm_apply_apply]
  have hRight : ∀ y : ↥Q, H.finalMap (L.finalMap y) = y := by
    intro y
    rw [hLFinal, ← hFinal, e.apply_symm_apply]
  have hResidualClasses : ∀ j, ∃ K : AmbientIsotopy ↥Q,
      (∀ t, (fun y => K.map (t, y)) '' B = B) ∧
      K.finalMap '' (H.finalMap '' Set.range (a j)) = Set.range (b j) := by
    intro j
    obtain ⟨I, hIB, hI⟩ := hclasses j
    refine ⟨L.compose I, ?_, ?_⟩
    · intro t
      change (fun y => I.map (t, L.map (t, y))) '' B = B
      rw [← Set.image_image (fun y => I.map (t, y)) (fun y => L.map (t, y)),
        hLB t, hIB t]
    · rw [AmbientIsotopy.compose_finalMap]
      change (fun y => I.finalMap (L.finalMap y)) ''
        (H.finalMap '' Set.range (a j)) = Set.range (b j)
      rw [← Set.image_image I.finalMap L.finalMap, Set.image_image L.finalMap H.finalMap]
      have hid : (fun y => L.finalMap (H.finalMap y)) = id := funext hLeft
      rw [hid, Set.image_id, hI]
  by_cases hPempty : P = ∅
  · obtain ⟨K, hKB, hKi⟩ := hResidualClasses i
    refine ⟨K, hKB, ?_, hKi⟩
    intro j hj
    simpa only [hPempty, Finset.notMem_empty] using hj
  let a' : J → C(Interval, ↥Q) := fun j =>
    ⟨fun t => H.finalMap (a j t),
      H.map.continuous.comp (continuous_const.prodMk (a j).continuous)⟩
  have hNormalizedRange : ∀ j, Set.range (a' j) = H.finalMap '' Set.range (a j) := by
    intro j
    exact Set.range_comp H.finalMap (a j)
  have hNormalizedEmbedding : ∀ j, IsEmbedding (a' j) := by
    intro j
    convert e.isEmbedding.comp (hemb j).1 using 1
    exact funext (fun t => (hFinal (a j t)).symm)
  have hNormalizedEnds : ∀ j, a' j 0 ∈ B ∧ a' j 1 ∈ B := by
    intro j
    exact ⟨hHB 1 ▸ ⟨a j 0, (hends j).1, rfl⟩,
      hHB 1 ▸ ⟨a j 1, (hends j).2.1, rfl⟩⟩
  have hNormalizedInterior : ∀ j t, t ∈ Ioo (0 : Interval) 1 → a' j t ∉ B := by
    intro j t ht hB
    obtain ⟨z, hz, hze⟩ := (show a' j t ∈ e '' B from heB.symm ▸ hB)
    have heq : z = a j t := e.injective (hze.trans (hFinal (a j t)).symm)
    exact (hmid j t ht).1 (heq ▸ hz)
  have hNormalizedEssential : ∀ j, ¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧
      (∀ t, c t ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
        IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range (a' j) ∪ Set.range c := by
    intro j
    rintro ⟨c, hc, hcB, d, hd, hdBoundary⟩
    let c' : C(Interval, ↥Q) := ⟨fun t => e.symm (c t), e.symm.continuous.comp c.continuous⟩
    let d' : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q) :=
      ⟨fun z => e.symm (d z), e.symm.continuous.comp d.continuous⟩
    apply haessential j
    refine ⟨c', e.symm.isEmbedding.comp hc, ?_, d', e.symm.isEmbedding.comp hd, ?_⟩
    · intro t
      exact heInvB ▸ ⟨c t, hcB t, rfl⟩
    · change (e.symm ∘ d) '' _ = Set.range (a j) ∪ Set.range (e.symm ∘ c)
      change (fun z => e.symm (d z)) '' _ = _
      rw [← Set.image_image e.symm d, hdBoundary, Set.image_union]
      have hInvRange : e.symm '' Set.range (a' j) = Set.range (a j) := by
        rw [hNormalizedRange, Set.image_image]
        have hid : (fun y => e.symm (H.finalMap y)) = id := by
          funext y
          change e.symm (H.finalMap y) = y
          rw [← hFinal, e.symm_apply_apply]
        rw [hid, Set.image_id]
      rw [hInvRange, Set.range_comp]
  have hNormalizedDisjoint : ∀ j k, j ≠ k →
      Disjoint (Set.range (a' j)) (Set.range (a' k)) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    rintro y ⟨s, hs⟩ ⟨t, ht⟩
    have hst : a j s = a k t := e.injective (by
      rw [hFinal, hFinal]
      exact hs.trans ht.symm)
    exact Set.disjoint_left.mp (hdisjoint j k hjk).1
      (Set.mem_range_self s) ⟨t, hst.symm⟩
  have hNormalizedDistinct : ∀ j k, j ≠ k → ¬ ∃ I : AmbientIsotopy ↥Q,
      (∀ t, (fun y => I.map (t, y)) '' B = B) ∧
      I.finalMap '' Set.range (a' j) = Set.range (a' k) := by
    intro j k hjk
    rintro ⟨I, hIB, hI⟩
    apply hdistinct j k hjk
    refine ⟨(H.compose I).compose L, ?_, ?_⟩
    · intro t
      change (fun y => L.map (t, I.map (t, H.map (t, y)))) '' B = B
      rw [← Set.image_image (fun y => L.map (t, y)) (fun y => I.map (t, H.map (t, y))),
        ← Set.image_image (fun y => I.map (t, y)) (fun y => H.map (t, y)),
        hHB t, hIB t, hLB t]
    · rw [AmbientIsotopy.compose_finalMap, AmbientIsotopy.compose_finalMap]
      change (fun y => L.finalMap (I.finalMap (H.finalMap y))) '' Set.range (a j) = _
      rw [← Set.image_image L.finalMap (fun y => I.finalMap (H.finalMap y)),
        ← Set.image_image I.finalMap H.finalMap, ← hNormalizedRange j, hI,
        hNormalizedRange k, Set.image_image]
      have hid : (fun y => L.finalMap (H.finalMap y)) = id := funext hLeft
      rw [hid, Set.image_id]
  have hNewOffProcessed : ∀ j ∈ P,
      Disjoint (Set.range (a' i)) (Set.range (b j)) := by
    intro j hj
    have hij : i ≠ j := fun heq => hi (heq ▸ hj)
    rw [← hProcessed j hj, ← hNormalizedRange j]
    exact hNormalizedDisjoint i j hij
  have hNewTargetOffProcessed : ∀ j ∈ P,
      Disjoint (Set.range (b i)) (Set.range (b j)) := by
    intro j hj
    exact (hdisjoint i j (fun heq => hi (heq ▸ hj))).2
  have hNewClassDistinctFromProcessed : ∀ j ∈ P, ¬ ∃ I : AmbientIsotopy ↥Q,
      (∀ t, (fun y => I.map (t, y)) '' B = B) ∧
      I.finalMap '' Set.range (a' i) = Set.range (b j) := by
    intro j hj
    rw [← hProcessed j hj, ← hNormalizedRange j]
    exact hNormalizedDistinct i j (fun heq => hi (heq ▸ hj))
  letI : ClosedSurface S := Classical.choice hS.2.1
  have hDisjointFinish (u : C(Interval, ↥Q)) (hu : IsEmbedding u)
      (huEnds : u 0 ∈ B ∧ u 1 ∈ B)
      (huInterior : ∀ t ∈ Ioo (0 : Interval) 1, u t ∉ B)
      (huEssential : ¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
          IsEmbedding d ∧ d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range u ∪ Set.range c)
      (huClass : ∃ I : AmbientIsotopy ↥Q,
        (∀ t, (fun y => I.map (t, y)) '' B = B) ∧
        I.finalMap '' Set.range u = Set.range (b i))
      (huOff : ∀ j ∈ P, Disjoint (Set.range u) (Set.range (b j)))
      (huDistinct : ∀ j ∈ P, ¬ ∃ I : AmbientIsotopy ↥Q,
        (∀ t, (fun y => I.map (t, y)) '' B = B) ∧
        I.finalMap '' Set.range u = Set.range (b j))
      (huDisjoint : Disjoint (Set.range u) (Set.range (b i))) :
      ∃ K : AmbientIsotopy ↥Q,
        (∀ t, (fun y => K.map (t, y)) '' B = B) ∧
        (∀ j ∈ P, K.finalMap '' Set.range (b j) = Set.range (b j)) ∧
        K.finalMap '' Set.range u = Set.range (b i) := by
    have hEndSep : Disjoint ({u 0, u 1} : Set ↥Q) {b i 0, b i 1} := by
      apply huDisjoint.mono
      · rintro y (rfl | rfl) <;> exact Set.mem_range_self _
      · rintro y (rfl | rfl) <;> exact Set.mem_range_self _
    have hFinite : (Set.range u ∩ Set.range (b i)).Finite := by
      rw [Set.disjoint_iff_inter_eq_empty.mp huDisjoint]
      exact Set.finite_empty
    obtain ⟨D, hD, hDu, hDb, hDB⟩ :=
      CoherentEndpointMotion.FreeBoundaryNullGeometry.source_actual_original_disjoint_free_boundary_class_bounds_proper_rectangle
        S g hg hS x R hR htarget u (b i) hu (hemb i).2
        ⟨huEnds.1, huEnds.2, (hends i).2.2.1, (hends i).2.2.2⟩
        (fun t ht => ⟨huInterior t ht, (hmid i t ht).2⟩)
        huEssential (hbessential i) hEndSep hFinite huClass huDisjoint
    obtain ⟨E, p, q, hE, hp, hq, hpq, hEp, hEq, hEB, hEopen⟩ :=
      CoherentEndpointMotion.FreeBoundaryNullGeometry.source_actual_original_proper_boundary_rectangle_has_collared_extension
        S g hg hS x R hR htarget D hD hDB
    have hEu : Set.range (fun t : Interval => E (t, p)) = Set.range u := hEp.trans hDu
    have hEb : Set.range (fun t : Interval => E (t, q)) = Set.range (b i) := hEq.trans hDb
    obtain ⟨k, hk⟩ := CoherentEndpointMotion.signed_interval_width_homeomorph
    let F : C(Interval × Interval, ↥Q) :=
      ⟨fun z => E (z.1, k z.2), E.continuous.comp
        (continuous_fst.prodMk (k.continuous.comp continuous_snd))⟩
    have hF : IsEmbedding F := hE.comp ((Homeomorph.refl Interval).prodCongr k).isEmbedding
    have hFB (z : Interval × Interval) : F z ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := hEB _
    have hWidth (t : Interval) : (k t).val ∈ Ioo (-1 : ℝ) 1 ↔ t ∈ Ioo (0 : Interval) 1 := by
      rw [hk]
      change (-1 < 2 * (t : ℝ) - 1 ∧ 2 * (t : ℝ) - 1 < 1) ↔
        (0 < (t : ℝ) ∧ (t : ℝ) < 1)
      constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith
    have hFopen : IsOpen (F '' {z | z.2 ∈ Ioo (0 : Interval) 1}) := by
      have heq : F '' {z | z.2 ∈ Ioo (0 : Interval) 1} =
          E '' {z | -1 < z.2.val ∧ z.2.val < 1} := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨(z.1, k z.2), (hWidth z.2).mpr hz, rfl⟩
        · rintro ⟨z, hz, rfl⟩
          refine ⟨(z.1, k.symm z.2), ?_, ?_⟩
          · apply (hWidth _).mp
            simpa only [k.apply_symm_apply, Set.mem_Ioo, Set.mem_setOf_eq] using hz
          · change E (z.1, k (k.symm z.2)) = E z
            rw [k.apply_symm_apply]
      rw [heq]
      exact hEopen
    let v := k.symm p
    let w := k.symm q
    have hv : v ∈ Ioo (0 : Interval) 1 := (hWidth v).mp (by
      change (k (k.symm p)).val ∈ Ioo (-1 : ℝ) 1
      simpa only [k.apply_symm_apply, Set.mem_Ioo, Set.mem_setOf_eq] using hp)
    have hw : w ∈ Ioo (0 : Interval) 1 := (hWidth w).mp (by
      change (k (k.symm q)).val ∈ Ioo (-1 : ℝ) 1
      simpa only [k.apply_symm_apply, Set.mem_Ioo, Set.mem_setOf_eq] using hq)
    have hvw : v ≠ w := k.symm.injective.ne hpq
    have hFv : Set.range (fun t : Interval => F (t, v)) = Set.range u := by
      simpa only [F, v, ContinuousMap.coe_mk, k.apply_symm_apply] using hEu
    have hFw : Set.range (fun t : Interval => F (t, w)) = Set.range (b i) := by
      simpa only [F, w, ContinuousMap.coe_mk, k.apply_symm_apply] using hEb
    let c : ↥P → C(Interval, ↥Q) := fun j => b j.val
    have hc : ∀ j, IsEmbedding (c j) := fun j => (hemb j.val).2
    have hcEnds : ∀ j, c j 0 ∈ B ∧ c j 1 ∈ B := fun j => (hends j.val).2.2
    have hcInterior : ∀ j t, t ∈ Ioo (0 : Interval) 1 → c j t ∉ B :=
      fun j t ht => (hmid j.val t ht).2
    have hcEssential : ∀ j, ¬ ∃ z : C(Interval, ↥Q), IsEmbedding z ∧ (∀ t, z t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q), IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range (c j) ∪ Set.range z := fun j => hbessential j.val
    have hcv : ∀ j, Disjoint (Set.range (c j)) (Set.range (fun t : Interval => F (t, v))) := by
      intro j
      rw [hFv]
      exact (huOff j.val j.property).symm
    have hcw : ∀ j, Disjoint (Set.range (c j)) (Set.range (fun t : Interval => F (t, w))) := by
      intro j
      rw [hFw]
      exact (hNewTargetOffProcessed j.val j.property).symm
    have hcvDistinct : ∀ j, ¬ ∃ I : AmbientIsotopy ↥Q,
        (∀ t, (fun y => I.map (t, y)) '' B = B) ∧
        I.finalMap '' Set.range (fun s : Interval => F (s, v)) = Set.range (c j) := by
      intro j
      rw [hFv]
      exact huDistinct j.val j.property
    have hcwDistinct : ∀ j, ¬ ∃ I : AmbientIsotopy ↥Q,
        (∀ t, (fun y => I.map (t, y)) '' B = B) ∧
        I.finalMap '' Set.range (fun s : Interval => F (s, w)) = Set.range (c j) := by
      intro j
      rw [hFw]
      rintro ⟨I, hIB, hI⟩
      obtain ⟨A, hAB, hA⟩ := huClass
      apply huDistinct j.val j.property
      refine ⟨A.compose I, ?_, ?_⟩
      · exact CoherentEndpointMotion.boundary_preserving_motion_compose B A I hAB hIB
      · rw [AmbientIsotopy.compose_finalMap, Set.image_comp, hA]
        exact hI
    rcases lt_or_gt_of_ne hvw with hlt | hgt
    · obtain ⟨K, hKB, hKvw, hKfix⟩ :=
        CoherentEndpointMotion.terminal_parallel_rails_preserve_distinct_essential_family
          B F hF hFopen hFB v w hv hw hlt c hc hcEnds hcInterior hcEssential
          hcvDistinct hcv hcw
      refine ⟨K, hKB, ?_, ?_⟩
      · intro j hj
        have hfix : ∀ y ∈ Set.range (b j), K.finalMap y = y := by
          rintro y ⟨s, rfl⟩
          exact hKfix 1 ⟨j, hj⟩ s
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          rw [hfix z hz]
          exact hz
        · intro hy
          exact ⟨y, hy, hfix y hy⟩
      · rw [← hFv, ← hFw, ← Set.range_comp]
        congr 1
        exact funext hKvw
    · obtain ⟨A, hAB, hAwv, hAfix⟩ :=
        CoherentEndpointMotion.terminal_parallel_rails_preserve_distinct_essential_family
          B F hF hFopen hFB w v hw hv hgt c hc hcEnds hcInterior hcEssential
          hcwDistinct hcw hcv
      have hAuv : A.finalMap '' Set.range (b i) = Set.range u := by
        rw [← hFw, ← hFv, ← Set.range_comp]
        congr 1
        exact funext hAwv
      obtain ⟨f, hf⟩ := A.homeomorphism_at 1
      have hfB : f '' B = B := by simpa only [hf] using hAB 1
      have hfInvB := CoherentEndpointMotion.boundary_preserving_homeomorph_inverse B f hfB
      let K : AmbientIsotopy ↥Q := {
        map := ⟨fun z => A.map (unitInterval.symm z.1, f.symm z.2),
          A.map.continuous.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk
            (f.symm.continuous.comp continuous_snd))⟩
        homeomorphism_at := by
          intro t
          obtain ⟨e, he⟩ := A.homeomorphism_at (unitInterval.symm t)
          exact ⟨f.symm.trans e, fun y => he (f.symm y)⟩
        at_zero := by
          intro y
          change A.map (unitInterval.symm 0, f.symm y) = y
          rw [unitInterval.symm_zero, ← hf, f.apply_symm_apply] }
      have hKFinal : ∀ y, K.finalMap y = f.symm y := by
        intro y
        change A.map (unitInterval.symm 1, f.symm y) = f.symm y
        rw [unitInterval.symm_one]
        exact A.at_zero _
      refine ⟨K, ?_, ?_, ?_⟩
      · intro t
        change (fun y => A.map (unitInterval.symm t, f.symm y)) '' B = B
        rw [← Set.image_image (fun y => A.map (unitInterval.symm t, y)) f.symm,
          hfInvB, hAB (unitInterval.symm t)]
      · intro j hj
        have hfix : ∀ y ∈ Set.range (b j), K.finalMap y = y := by
          rintro y ⟨s, rfl⟩
          rw [hKFinal]
          apply f.injective
          rw [f.apply_symm_apply, hf]
          exact (hAfix 1 ⟨j, hj⟩ s).symm
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          rw [hfix z hz]
          exact hz
        · intro hy
          exact ⟨y, hy, hfix y hy⟩
      · rw [← hAuv, Set.image_image]
        have hId : (fun y => K.finalMap (A.finalMap y)) = id := by
          funext y
          rw [hKFinal]
          change f.symm (A.map (1, y)) = y
          rw [← hf, f.symm_apply_apply]
        rw [hId, Set.image_id]
  suffices hJoint : ∃ K : AmbientIsotopy ↥Q,
      (∀ t, (fun y => K.map (t, y)) '' B = B) ∧
      (∀ j ∈ P, K.finalMap '' Set.range (b j) = Set.range (b j)) ∧
      K.finalMap '' Set.range (a' i) = Set.range (b i) by
    obtain ⟨K, hKB, hKP, hKi⟩ := hJoint
    exact ⟨K, hKB, hKP, by rw [← hNormalizedRange]; exact hKi⟩
  by_cases hSelectedDisjoint : Disjoint (Set.range (a' i)) (Set.range (b i))
  · apply hDisjointFinish (a' i) (hNormalizedEmbedding i) (hNormalizedEnds i)
      (hNormalizedInterior i) (hNormalizedEssential i) ?_
      hNewOffProcessed hNewClassDistinctFromProcessed hSelectedDisjoint
    simpa only [hNormalizedRange] using hResidualClasses i
  let Ready (q : C(Interval, ↥Q)) (A : AmbientIsotopy ↥Q) : Prop :=
    IsEmbedding q ∧ (q 0 ∈ B ∧ q 1 ∈ B) ∧
    (∀ t ∈ Ioo (0 : Interval) 1, q t ∉ B) ∧
    Disjoint ({b i 0, b i 1} : Set ↥Q) {q 0, q 1} ∧
    (Set.range (b i) ∩ Set.range q).Finite ∧
    (∀ t, (fun y => A.map (t, y)) '' B = B) ∧
    A.finalMap '' Set.range (a' i) = Set.range q ∧
    (∀ j ∈ P, A.finalMap '' Set.range (b j) = Set.range (b j))
  have hCandidates : ∃ n : ℕ, ∃ q A, Ready q A ∧
      (Set.range (b i) ∩ Set.range q).ncard = n := by
    obtain ⟨q, A, hq, hqEnds, hqInterior, hsep, hfin, hAB, hA, hFix⟩ :=
      CoherentEndpointMotion.original_finite_disjoint_family_selected_arc_relative_position
        S g hg hS x R hR htarget a' (b i) hNormalizedEmbedding (hemb i).2
        hNormalizedEnds (hends i).2.2 hNormalizedInterior
        (fun t ht => (hmid i t ht).2) hNormalizedDisjoint P i hi
    refine ⟨_, q, A, ⟨hq, hqEnds, hqInterior, hsep, hfin, hAB, hA, ?_⟩, rfl⟩
    intro j hj
    have hFixB : ∀ y ∈ Set.range (b j), A.finalMap y = y := by
      intro y hy
      exact hFix j hj 1 y (by rw [hNormalizedRange, hProcessed j hj]; exact hy)
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hFixB z hz]
      exact hz
    · intro hy
      exact ⟨y, hy, hFixB y hy⟩
  obtain ⟨q, A, hReady, hCount⟩ := Nat.find_spec hCandidates
  obtain ⟨hq, hqEnds, hqInterior, hEndpointSep, hFinite, hAB, hA, hAP⟩ := hReady
  have hMinimal (v : C(Interval, ↥Q)) (T : AmbientIsotopy ↥Q) (hv : Ready v T) :
      (Set.range (b i) ∩ Set.range q).ncard ≤
        (Set.range (b i) ∩ Set.range v).ncard := by
    rw [hCount]
    exact Nat.find_min' hCandidates ⟨v, T, hv, rfl⟩
  obtain ⟨f, hf⟩ := A.homeomorphism_at 1
  have hfFinal : (f : ↥Q → ↥Q) = A.finalMap := funext hf
  have hfB : f '' B = B := by simpa only [hf] using hAB 1
  have hqEssential : ¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q), IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range q ∪ Set.range c := by
    have hEss := (CoherentEndpointMotion.boundary_homeomorph_transports_literal_essential_arc
      B f hfB (a' i) (hNormalizedEmbedding i) (hNormalizedEnds i)
      (hNormalizedInterior i) (hNormalizedEssential i)).2.2.2
    have hRange : Set.range ((⟨f, f.continuous⟩ : C(↥Q, ↥Q)).comp (a' i)) =
        Set.range q := by
      change Set.range (f ∘ a' i) = _
      rw [Set.range_comp, hfFinal]
      exact hA
    simpa only [hRange] using hEss
  have hOriginalClass : ∃ K : AmbientIsotopy ↥Q,
      (∀ t, (fun y => K.map (t, y)) '' B = B) ∧
      K.finalMap '' Set.range (a' i) = Set.range (b i) := by
    simpa only [hNormalizedRange] using hResidualClasses i
  have hqClass : ∃ K : AmbientIsotopy ↥Q,
      (∀ t, (fun y => K.map (t, y)) '' B = B) ∧
      K.finalMap '' Set.range q = Set.range (b i) := by
    rw [← hA]
    exact CoherentEndpointMotion.boundary_motion_transports_individual_class
      B A hAB (Set.range (a' i)) (Set.range (b i)) hOriginalClass
  have hqOff : ∀ j ∈ P, Disjoint (Set.range q) (Set.range (b j)) := by
    intro j hj
    rw [← hA, ← hAP j hj, ← hfFinal]
    exact Set.disjoint_image_of_injective f.injective (hNewOffProcessed j hj)
  have hqDistinct : ∀ j ∈ P, ¬ ∃ I : AmbientIsotopy ↥Q,
      (∀ t, (fun y => I.map (t, y)) '' B = B) ∧
      I.finalMap '' Set.range q = Set.range (b j) := by
    intro j hj hClass
    apply hNewClassDistinctFromProcessed j hj
    exact (CoherentEndpointMotion.boundary_ambient_class_equivalence B).trans
      ⟨A, hAB, hA⟩ hClass
  have hFinishAtQ (K : AmbientIsotopy ↥Q)
      (hKB : ∀ t, (fun y => K.map (t, y)) '' B = B)
      (hKP : ∀ j ∈ P, K.finalMap '' Set.range (b j) = Set.range (b j))
      (hKq : K.finalMap '' Set.range q = Set.range (b i)) :
      ∃ K : AmbientIsotopy ↥Q,
        (∀ t, (fun y => K.map (t, y)) '' B = B) ∧
        (∀ j ∈ P, K.finalMap '' Set.range (b j) = Set.range (b j)) ∧
        K.finalMap '' Set.range (a' i) = Set.range (b i) := by
    refine ⟨A.compose K,
      CoherentEndpointMotion.boundary_preserving_motion_compose B A K hAB hKB, ?_, ?_⟩
    · intro j hj
      rw [AmbientIsotopy.compose_finalMap, Set.image_comp, hAP j hj, hKP j hj]
    · rw [AmbientIsotopy.compose_finalMap, Set.image_comp, hA, hKq]
  by_cases hqDisjoint : Disjoint (Set.range q) (Set.range (b i))
  · obtain ⟨K, hKB, hKP, hKq⟩ := hDisjointFinish q hq hqEnds hqInterior hqEssential
      hqClass hqOff hqDistinct hqDisjoint
    exact hFinishAtQ K hKB hKP hKq
  have hClassReverse := (CoherentEndpointMotion.boundary_ambient_class_equivalence B).symm hqClass
  obtain hSame | hCross :=
    CoherentEndpointMotion.FreeBoundaryContactRepair.source_actual_original_free_boundary_finite_contact_dichotomy
      S g hg hS x R hR htarget (b i) q (hemb i).2 hq
      ⟨(hends i).2.2.1, (hends i).2.2.2, hqEnds.1, hqEnds.2⟩
      (fun t ht => ⟨(hmid i t ht).2, hqInterior t ht⟩)
      (hbessential i) hqEssential hEndpointSep hFinite hClassReverse
  · obtain ⟨r, s, C, hC⟩ := hSame
    obtain ⟨D, _⟩ :=
      CoherentEndpointMotion.FreeBoundaryContactRepair.source_actual_original_free_boundary_same_side_supported_contact_drop
        S g hg hS x R hR htarget (b i) q (hemb i).2 hq
        ⟨(hends i).2.2.1, (hends i).2.2.2, hqEnds.1, hqEnds.2⟩
        (fun t ht => ⟨(hmid i t ht).2, hqInterior t ht⟩)
        (hbessential i) hqEssential hEndpointSep hFinite hClassReverse r s C hC
        ↥P (fun j => b j.val) (fun j => hqOff j.val j.property)
    have hNewReady : Ready D.replacement (A.compose D.motion) := by
      refine ⟨D.replacement_embedded, ?_, D.replacement_interior, ?_,
        D.replacement_contacts_finite,
        CoherentEndpointMotion.boundary_preserving_motion_compose B A D.motion hAB D.boundary_setwise,
        ?_, ?_⟩
      · rw [D.replacement_zero, D.replacement_one]
        exact hqEnds
      · rw [D.replacement_zero, D.replacement_one]
        exact hEndpointSep
      · rw [AmbientIsotopy.compose_finalMap, Set.image_comp, hA, D.whole_moving_trace]
      · intro j hj
        rw [AmbientIsotopy.compose_finalMap, Set.image_comp, hAP j hj]
        have hFix : ∀ y ∈ Set.range (b j), D.motion.finalMap y = y := by
          intro y hy
          exact D.graph_pointwise 1 y (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hy⟩)
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          rw [hFix z hz]
          exact hz
        · intro hy
          exact ⟨y, hy, hFix y hy⟩
    exact False.elim (not_lt_of_ge (hMinimal D.replacement (A.compose D.motion) hNewReady)
      D.strict_contact_decrease)
  have hContact : (Set.range (b i) ∩ Set.range q).Nonempty := by
    exact Set.not_disjoint_iff_nonempty_inter.mp (fun h => hqDisjoint h.symm)
  have hNullBoundary :=
    CoherentEndpointMotion.FreeBoundaryContactRepair.source_actual_original_free_boundary_all_crossing_selects_simple_Q_null_boundary
      S g hg hS x R hR htarget (b i) q (hemb i).2 hq
      ⟨(hends i).2.2.1, (hends i).2.2.2, hqEnds.1, hqEnds.2⟩
      (fun t ht => ⟨(hmid i t ht).2, hqInterior t ht⟩)
      (hbessential i) hqEssential hEndpointSep hFinite hClassReverse hContact hCross
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
  have hHalfClean
      (N : CoherentEndpointMotion.FreeBoundaryNullGeometry.NullHalfBigonBoundary B (b i) q)
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q))
      (hd : IsEmbedding d)
      (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range N.first ∪ Set.range N.second ∪ Set.range N.boundarySide)
      (hempty : Disjoint
        (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (Set.range (b i) ∪ Set.range q)) :
      Set.range d ∩ (Set.range (b i) ∩ Set.range q) = {N.first 1} := by
    exact regional_empty_three_side_half_disk_whole_contact_cleanup
      S g hg hS x R hR htarget Q hQcompact hQconnected hbaseQ
      (Set.Subset.rfl) hQregular PEmpty (fun j => PEmpty.elim j)
      (fun j => PEmpty.elim j) (fun j => PEmpty.elim j)
      (by simpa using hFrontier)
      ⟨⟨b i,(hemb i).2,(hends i).2.2.1,(hends i).2.2.2,
        fun t ht => fun h => (hmid i t ht).2 ((hBoundaryFrontier _).mpr h)⟩,hbessential i⟩
      ⟨⟨q,hq,hqEnds.1,hqEnds.2,
        fun t ht => fun h => hqInterior t ht ((hBoundaryFrontier _).mpr h)⟩,hqEssential⟩
      (by simpa only [Set.disjoint_insert_left,Set.disjoint_singleton_left,
          Set.mem_insert_iff,Set.mem_singleton_iff,not_or,and_assoc] using hEndpointSep)
      hFinite hCross N d hd hboundary hempty
  suffices hStrictDrop : ∃ v T, Ready v T ∧
      (Set.range (b i) ∩ Set.range v).ncard < (Set.range (b i) ∩ Set.range q).ncard by
    obtain ⟨v, T, hReady, hDrop⟩ := hStrictDrop
    exact False.elim (not_lt_of_ge (hMinimal v T hReady) hDrop)
  have hOrdinaryDrop
      (N : CoherentEndpointMotion.FreeBoundaryNullGeometry.NullBigonBoundary B (b i) q)
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q))
      (hd : IsEmbedding d)
      (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range N.first ∪ Set.range N.second) :
      ∃ v T, Ready v T ∧
        (Set.range (b i) ∩ Set.range v).ncard < (Set.range (b i) ∩ Set.range q).ncard := by
    have hBfree : Disjoint B (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
      apply Set.disjoint_left.mpr
      rintro y hy ⟨z, hz, rfl⟩
      exact RegionalEmbeddedFamily.embedded_regional_disk_interior_avoids_frontier
        S Q d hd z hz ((hBoundaryFrontier _).mp hy)
    obtain ⟨p, r, e, hp, hr, he, hpa, hrq, hpr0, hpr1, heb, hesub, heEmpty⟩ :=
      CoherentEndpointMotion.actual_two_side_disk_in_subset_has_empty_subdisk
        Q B (b i) q (hemb i).2 hq (hends i).2.2 hqEnds hFinite
        N.first N.second N.first_embedded N.second_embedded N.first_on_a N.second_on_b
        N.zero_eq N.one_eq d hd hboundary hBfree
    have hProtected : ∀ j ∈ P, Disjoint (Set.range (b j)) (Set.range e) := by
      intro j hj
      exact (CoherentEndpointMotion.actual_ordinary_two_side_disk_clears_protected_arc
        Q B (b i) q (b j) (hends j).2.2.1 N.first N.second
        N.first_on_a N.second_on_b d hd hboundary hBfree
        (hNewTargetOffProcessed j hj).symm (hqOff j hj).symm).mono_right hesub
    let moving : Option ↥P → C(Interval, ↥Q) := fun k =>
      match k with
      | none => q
      | some j => b j.val
    let anchor : Unit → C(Interval, ↥Q) := fun _ => b i
    have hmEmb : ∀ k, IsEmbedding (moving k) := by
      rintro (_ | j)
      · exact hq
      · exact (hemb j.val).2
    have hmDisjoint : ∀ k l, k ≠ l → Disjoint (Set.range (moving k)) (Set.range (moving l)) := by
      rintro (_ | k) (_ | l) hkl
      · exact (hkl rfl).elim
      · exact hqOff l.val l.property
      · exact (hqOff k.val k.property).symm
      · exact (hdisjoint k.val l.val (fun h => hkl (congrArg some (Subtype.ext h)))).2
    have hUnion : (⋃ k, Set.range (moving k)) = Set.range q ∪ ⋃ j : ↥P, Set.range (b j.val) := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨_ | j, hy⟩
        · exact Or.inl hy
        · exact Or.inr ⟨j, hy⟩
      · rintro (hy | ⟨j, hy⟩)
        · exact ⟨none, hy⟩
        · exact ⟨some j, hy⟩
    have hAnchor : (⋃ k, Set.range (anchor k)) = Set.range (b i) := by
      ext y
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
        exact hk
      · intro hy
        exact Set.mem_iUnion.mpr ⟨(), hy⟩
    have hFamilyFinite : ((⋃ k, Set.range (anchor k)) ∩ (⋃ k, Set.range (moving k))).Finite := by
      rw [hAnchor, hUnion, Set.inter_union_distrib_left]
      have hNo : Set.range (b i) ∩ (⋃ j : ↥P, Set.range (b j.val)) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro y ⟨hy, hh⟩
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hh
        exact Set.disjoint_left.mp (hNewTargetOffProcessed j.val j.property) hy hj
      rw [hNo, Set.union_empty]
      exact hFinite
    have hmEnds : ∀ k, (moving k 0).val ∈ frontier Q ∧ (moving k 1).val ∈ frontier Q := by
      rintro (_ | j)
      · exact ⟨(hBoundaryFrontier _).mp hqEnds.1, (hBoundaryFrontier _).mp hqEnds.2⟩
      · exact ⟨(hBoundaryFrontier _).mp (hends j.val).2.2.1,
          (hBoundaryFrontier _).mp (hends j.val).2.2.2⟩
    have hmInterior : ∀ k t, t ∈ Ioo (0 : Interval) 1 → (moving k t).val ∉ frontier Q := by
      rintro (_ | j) t ht
      · exact fun h => hqInterior t ht ((hBoundaryFrontier _).mpr h)
      · exact fun h => (hmid j.val t ht).2 ((hBoundaryFrontier _).mpr h)
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
          exact Set.disjoint_left.mp (hProtected j.val j.property)
            ⟨s, Subtype.ext hs⟩ (Set.mem_range_self z)
    have hGenuine : ps 0 ∉ frontier Q := by
      obtain ⟨s, hs⟩ := hpa (Set.mem_range_self 0)
      obtain ⟨t, ht⟩ := hrq (Set.mem_range_self 0)
      have hst : b i s = q t := hs.trans (hpr0.trans ht.symm)
      have hint := CoherentEndpointMotion.FreeBoundaryContactRepair.free_boundary_contact_parameters_interior
        B (b i) q ⟨(hends i).2.2.1, (hends i).2.2.2, hqEnds.1, hqEnds.2⟩
        (fun t ht => ⟨(hmid i t ht).2, hqInterior t ht⟩) hEndpointSep s t hst
      intro h
      apply (hmid i s hint.1).2
      exact (hBoundaryFrontier _).mpr ((congrArg Subtype.val hs).symm ▸ h)
    have hBypass : ∃ (r : Option ↥P) (E : OpenPartialHomeomorph S Schoenflies.Plane)
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
          S Q Unit (Option ↥P) anchor moving (fun _ => (hemb i).2) hmEmb
          (fun k l h => (h (Subsingleton.elim k l)).elim) hmDisjoint hFamilyFinite
          (fun _ => (hBoundaryFrontier _).mp (hends i).2.2.1)
          (fun _ => (hBoundaryFrontier _).mp (hends i).2.2.2)
          (fun k => (hmEnds k).1) (fun k => (hmEnds k).2)
          (fun _ t ht h => (hmid i t ht).2 ((hBoundaryFrontier _).mpr h)) hmInterior
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
        have hyMoving : y ∈ Set.range (b j.val) := (hTrace.symm ▸ hy.1).2
        have hyAnchor : y ∈ Set.range (b i) := hAnchor ▸ hy.2
        exact False.elim (Set.disjoint_left.mp (hNewTargetOffProcessed j.val j.property) hyAnchor hyMoving)
    subst k
    have hRetainSelected :
        {y : ↥Q | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ V}} ∩ Set.range (b i) ⊆
          Set.range q ∩ Set.range (b i) := by
      rintro z ⟨hzV,hzi⟩
      have hzAll := hRetain ⟨hzV, hAnchor.symm ▸ hzi⟩
      rw [hUnion] at hzAll
      rcases hzAll.1 with hzq | hzP
      · exact ⟨hzq,hzi⟩
      · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hzP
        exact False.elim (Set.disjoint_left.mp
          (hNewTargetOffProcessed j.val j.property) hzi hj)
    have hyAnchor : y ∈ Set.range (b i) := hAnchor ▸ hy.2
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
    have hSubset : ((Set.range q \ Up) ∪ Vp) ∩ Set.range (b i) ⊆
        Set.range q ∩ Set.range (b i) := by
      rintro z ⟨hz,hzi⟩
      rcases hz with hz | hz
      · exact ⟨hz.1,hzi⟩
      · exact hRetainSelected ⟨hz,hzi⟩
    have hMissing : y ∉ ((Set.range q \ Up) ∪ Vp) ∩ Set.range (b i) := by
      rintro ⟨hy',_⟩
      rcases hy' with hy' | hy'
      · exact hy'.2 hy.1
      · exact hyNew hy'
    have hFiniteRev : (Set.range q ∩ Set.range (b i)).Finite := by
      simpa only [Set.inter_comm] using hFinite
    have hDrop : (((Set.range q \ Up) ∪ Vp) ∩ Set.range (b i)).Finite ∧
        (((Set.range q \ Up) ∪ Vp) ∩ Set.range (b i)).ncard <
          (Set.range q ∩ Set.range (b i)).ncard := by
      refine ⟨hFiniteRev.subset hSubset,Set.ncard_lt_ncard ?_ hFiniteRev⟩
      apply Set.ssubset_iff_subset_ne.mpr
      refine ⟨hSubset,?_⟩
      intro heq
      exact hMissing (heq.symm ▸ ⟨hUp hy.1,hyAnchor⟩)
    have hNewFinite : (Set.range (b i) ∩ Set.range q').Finite := by
      rw [Set.inter_comm,hNewTrace]
      exact hDrop.1
    have hNewDrop : (Set.range (b i) ∩ Set.range q').ncard <
        (Set.range (b i) ∩ Set.range q).ncard := by
      rw [Set.inter_comm (Set.range (b i)) (Set.range q'),hNewTrace]
      simpa only [Set.inter_comm (Set.range (b i)) (Set.range q)] using hDrop.2
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
    refine ⟨q',A.compose K,?_,hNewDrop⟩
    refine ⟨hq',?_,hq'Interior,?_,hNewFinite,
      CoherentEndpointMotion.boundary_preserving_motion_compose B A K hAB hKB,?_,?_⟩
    · rw [hq'0,hq'1]
      exact hqEnds
    · rw [hq'0,hq'1]
      exact hEndpointSep
    · rw [AmbientIsotopy.compose_finalMap,Set.image_comp,hA,hq'Range]
    · intro j hj
      rw [AmbientIsotopy.compose_finalMap,Set.image_comp,hAP j hj]
      have hFix (z : ↥Q) (hz : z ∈ Set.range (b j)) : K.finalMap z = z :=
        hKfix 1 z (hAvoid (some ⟨j,hj⟩) (by simp) z hz)
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        rw [hFix w hw]
        exact hw
      · intro hz
        exact ⟨z,hz,hFix z hz⟩
  rcases hNullBoundary with hN | hN
  · obtain ⟨N⟩ := hN
    obtain ⟨d, hd, hdb⟩ := CoherentEndpointMotion.subset_nullhomotopic_curve_bounds_literal_disk
      S g hg hS Q N.loop N.loop_null
    exact hOrdinaryDrop N d hd (hdb.trans N.loop_image)
  · obtain ⟨N⟩ := hN
    obtain ⟨d, hd, hdb⟩ := CoherentEndpointMotion.subset_nullhomotopic_curve_bounds_literal_disk
      S g hg hS Q N.loop N.loop_null
    have hboundary := hdb.trans N.loop_image
    have hBfree : Disjoint B (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
      apply Set.disjoint_left.mpr
      rintro y hy ⟨z, hz, rfl⟩
      exact RegionalEmbeddedFamily.embedded_regional_disk_interior_avoids_frontier
        S Q d hd z hz ((hBoundaryFrontier _).mp hy)
    have hFirstBoundary (t : Interval) (ht : N.first t ∈ B) : t = 0 := by
      by_contra ht0
      by_cases ht1 : t = 1
      · exact N.corner_off_boundary (ht1 ▸ ht)
      · exact N.first_interior t ⟨bot_lt_iff_ne_bot.mpr ht0, lt_top_iff_ne_top.mpr ht1⟩ ht
    have hSecondBoundary (t : Interval) (ht : N.second t ∈ B) : t = 0 := by
      by_contra ht0
      by_cases ht1 : t = 1
      · exact N.corner_off_boundary (N.corner_eq.symm ▸ (ht1 ▸ ht))
      · exact N.second_interior t ⟨bot_lt_iff_ne_bot.mpr ht0, lt_top_iff_ne_top.mpr ht1⟩ ht
    have hSideDisk : Set.range N.boundarySide ⊆ Set.range d := by
      intro y hy
      apply Set.image_subset_range d {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}
      rw [hboundary]
      exact Or.inr hy
    have hDiskBoundary : Set.range d ∩ B ⊆ Set.range N.boundarySide := by
      rintro y ⟨⟨z, rfl⟩, hzB⟩
      have hzSphere : z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
        apply le_antisymm z.property
        apply le_of_not_gt
        intro hz
        exact Set.disjoint_left.mp hBfree hzB ⟨z, hz, rfl⟩
      have hyBoundary : d z ∈ Set.range N.first ∪ Set.range N.second ∪ Set.range N.boundarySide :=
        hboundary ▸ ⟨z, hzSphere, rfl⟩
      rcases hyBoundary with (hFirst | hSecond) | hThird
      · obtain ⟨t, ht⟩ := hFirst
        have ht0 := hFirstBoundary t (ht.symm ▸ hzB)
        exact ⟨0, N.boundary_zero.trans (ht0 ▸ ht)⟩
      · obtain ⟨t, ht⟩ := hSecond
        have ht0 := hSecondBoundary t (ht.symm ▸ hzB)
        exact ⟨1, N.boundary_one.trans (ht0 ▸ ht)⟩
      · exact hThird
    have hProtectedInteriors : ∀ j ∈ P,
        Disjoint ((b j) '' Ioo (0 : Interval) 1) (Set.range d) := by
      intro j hj
      apply essential_proper_arc_avoids_boundary_attached_disk_interior
        Q B (b j) (hemb j).2 (hends j).2.2 (fun t ht => (hmid j t ht).2)
        (hbessential j) d hd N.boundarySide N.boundary_embedded N.boundary_in_B hSideDisk hDiskBoundary
      rintro y ⟨hy, hybd⟩
      rw [hboundary] at hybd
      rcases hybd with (hFirst | hSecond) | hThird
      · exact False.elim (Set.disjoint_left.mp (hNewTargetOffProcessed j hj)
          (N.first_on_a hFirst) hy)
      · exact False.elim (Set.disjoint_left.mp (hqOff j hj) (N.second_on_b hSecond) hy)
      · obtain ⟨t, rfl⟩ := hThird
        exact N.boundary_in_B t
    -- Remaining geometry: realize a lower-contact terminal-restoring move
    -- from this literal three-side disk; self-intrusion and B-end behavior remain.
    have hPairEssential : ∀ v ∈ ({b i,q} : Set C(Interval,↥Q)),
        ¬ ∃ w : C(Interval,↥Q), IsEmbedding w ∧ (∀ t, w t ∈ B) ∧
          ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥Q),
            IsEmbedding e ∧
            e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
              Set.range v ∪ Set.range w := by
      intro v hv
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact hbessential i
      · exact hqEssential
    obtain ⟨v,T,hv,hvEnds,hvInterior,hvEndpointSep,hvFinite,hTB,hTP,hTv,hDrop⟩ :=
      original_Q_half_bigon_terminal_restoring_contact_drop
        S g hg hS x R hR htarget (b i) q (hemb i).2 hq
        ⟨(hends i).2.2.1,(hends i).2.2.2,hqEnds.1,hqEnds.2⟩
        (fun t ht => ⟨(hmid i t ht).2,hqInterior t ht⟩)
        hPairEssential hEndpointSep hFinite hCross
        ↥P (fun j => b j.val)
        (fun j => (hemb j.val).2)
        (fun j => (hends j.val).2.2)
        (fun j t ht => (hmid j.val t ht).2)
        (fun j => hbessential j.val)
        (fun j k hjk => (hdisjoint j.val k.val (fun h => hjk (Subtype.ext h))).2)
        (fun j => ⟨hNewTargetOffProcessed j.val j.property,hqOff j.val j.property⟩)
        N d hd hboundary
    refine ⟨v,A.compose T,?_,hDrop⟩
    refine ⟨hv,hvEnds,hvInterior,hvEndpointSep,hvFinite,
      CoherentEndpointMotion.boundary_preserving_motion_compose B A T hAB hTB,?_,?_⟩
    · rw [AmbientIsotopy.compose_finalMap,Set.image_comp,hA,hTv]
    · intro j hj
      rw [AmbientIsotopy.compose_finalMap,Set.image_comp,hAP j hj]
      exact hTP ⟨j,hj⟩
