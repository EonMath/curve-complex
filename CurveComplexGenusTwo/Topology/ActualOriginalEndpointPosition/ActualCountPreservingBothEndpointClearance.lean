import CurveComplexGenusTwo.Topology.ActualFixedTwoArmInsertion.ActualNewSourceArmRelativeTwoFixedSegments
import CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualMarkedEndpointSourceFanChart
import CurveComplexGenusTwo.Topology.Smoothing.JordanSectorCrosscutExtensionHeader
import CurveComplexGenusTwo.Topology.Smoothing.ConvexSectorChartHeader
import CurveComplexGenusTwo.Topology.Smoothing.JordanRegionIdentificationHeader
import CurveComplexGenusTwo.Topology.Smoothing.PrescribedPairRadializationProof
import CurveComplexGenusTwo.Topology.Smoothing.PointedCrosscutHeader
import CurveComplexGenusTwo.Topology.Smoothing.FiniteStarSeed
import CurveComplexGenusTwo.Topology.WeightedSurgery.SupportedEndpointRotation
import CurveComplexGenusTwo.Topology.Smoothing.FiniteActualStarRadialization
import Schoenflies.MatchedArc
import Schoenflies.BoundaryContinuity2
import CurveComplexGenusTwo.Topology.Smoothing.PointedPlaneIsotopyProof
import CurveComplexGenusTwo.Topology.ChartLift
import CurveComplexGenusTwo.Topology.Smoothing.ActualStarIntersection
import CurveComplexGenusTwo.Topology.Smoothing.ActualGermArcs
import CurveComplexGenusTwo.Topology.Smoothing.UniformActualGerms
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualMarkedCrossingTransport
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers


section

section
open Set Metric CurveComplex Schoenflies
set_option maxHeartbeats 1000000

private theorem actualTwoRayArcCover {d w x : Plane}
    (hd : Plane.IsDirection d) (hw : Plane.IsDirection w) (hdw : d ≠ w)
    (hx : x ≠ 0) (hxd : Plane.dir x ≠ d) (hxw : Plane.dir x ≠ w) :
    x ∈ Plane.arcCCW d w ∨ x ∈ Plane.arcCCW w d := by
  let D : Set Plane := {d, w}
  have hfin : D.Finite := by
    dsimp [D]
    exact Set.Finite.insert d (Set.finite_singleton w)
  have hdir : ∀ u ∈ D, Plane.IsDirection u := by
    intro u hu
    rcases (by simpa [D] using hu : u = d ∨ u = w) with rfl | rfl
    · exact hd
    · exact hw
  have htwo : ∃ a ∈ D, ∃ b ∈ D, a ≠ b := by
    exact ⟨d, by simp [D], w, by simp [D], hdw⟩
  have hnot : Plane.dir x ∉ D := by
    simpa [D] using ⟨hxd, hxw⟩
  obtain ⟨a, b, hp, hmem⟩ := Plane.exists_isSectorPair hfin hdir htwo hx hnot
  have ha : a = d ∨ a = w := by simpa [D] using hp.1
  have hb : b = d ∨ b = w := by simpa [D] using hp.2.1
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · exact False.elim (hp.2.2.1 rfl)
    · exact Or.inl hmem
  · rcases hb with rfl | rfl
    · exact Or.inr hmem
    · exact False.elim (hp.2.2.1 rfl)

private theorem actualTwoRayArcsDisjoint
    {d w : Plane} (hd : Plane.IsDirection d) (hw : Plane.IsDirection w)
    (hdw : d ≠ w) :
    Disjoint (Plane.arcCCW d w) (Plane.arcCCW w d) := by
  let D : Set Plane := {d, w}
  have hdir : ∀ u ∈ D, Plane.IsDirection u := by
    intro u hu
    rcases (by simpa [D] using hu : u = d ∨ u = w) with rfl | rfl
    · exact hd
    · exact hw
  have hpair : Plane.IsSectorPair D d w := by
    refine ⟨by simp [D], by simp [D], hdw, ?_⟩
    intro u hu
    rcases (by simpa [D] using hu : u = d ∨ u = w) with he | he
    · simpa only [he] using Plane.left_notMem_arcCCW d w
    · simpa only [he] using Plane.right_notMem_arcCCW d w
  have hpair' : Plane.IsSectorPair D w d := by
    refine ⟨by simp [D], by simp [D], hdw.symm, ?_⟩
    intro u hu
    rcases (by simpa [D] using hu : u = d ∨ u = w) with he | he
    · simpa only [he] using Plane.right_notMem_arcCCW w d
    · simpa only [he] using Plane.left_notMem_arcCCW w d
  exact Plane.arcCCW_disjoint_of_isSectorPair hdir hpair hpair' (Or.inl hdw)

private theorem actualSourcePrefixSelectsOneOfTwoRaySectors
    {d w : Plane} (hd : Plane.IsDirection d) (hw : Plane.IsDirection w)
    (hdw : d ≠ w) (γ : Interval → Plane)
    (hγ : Topology.IsClosedEmbedding γ) (hzero : γ 0 = 0)
    (cut : Interval) (hcut : 0 < cut.val)
    (havoid : ∀ t ∈ Ioo (0 : Interval) cut,
      γ t ∉ {z | ∃ s : ℝ, 0 ≤ s ∧ z = s • d} ∪
        {z | ∃ s : ℝ, 0 ≤ s ∧ z = s • w}) :
    (∀ t ∈ Ioo (0 : Interval) cut, γ t ∈ Plane.arcCCW d w) ∨
      (∀ t ∈ Ioo (0 : Interval) cut, γ t ∈ Plane.arcCCW w d) := by
  have hdisj : Disjoint (Plane.arcCCW d w) (Plane.arcCCW w d) :=
    actualTwoRayArcsDisjoint hd hw hdw
  let Y : Set Plane := γ '' Ioo (0 : Interval) cut
  have hconn : IsPreconnected Y := isPreconnected_Ioo.image γ hγ.continuous.continuousOn
  have hcover : Y ⊆ Plane.arcCCW d w ∪ Plane.arcCCW w d := by
    rintro z ⟨t, ht, rfl⟩
    have hz : γ t ≠ 0 := by
      intro he
      have heq : t = 0 := hγ.injective (he.trans hzero.symm)
      exact (ne_of_gt ht.1) heq
    have hdnot : Plane.dir (γ t) ≠ d := by
      intro he
      apply havoid t ht
      apply Or.inl
      refine ⟨‖γ t‖, norm_nonneg _, ?_⟩
      rw [← he]
      exact (Schoenflies.smul_norm_dir hz).symm
    have hwnot : Plane.dir (γ t) ≠ w := by
      intro he
      apply havoid t ht
      apply Or.inr
      refine ⟨‖γ t‖, norm_nonneg _, ?_⟩
      rw [← he]
      exact (Schoenflies.smul_norm_dir hz).symm
    exact actualTwoRayArcCover hd hw hdw hz hdnot hwnot
  let mid : Interval := ⟨cut.val / 2, by
    constructor
    · linarith
    · have hh := cut.property.2
      linarith⟩
  have hmid : mid ∈ Ioo (0 : Interval) cut := by
    constructor
    · change 0 < cut.val / 2
      linarith
    · change cut.val / 2 < cut.val
      linarith
  have hne : Y.Nonempty := ⟨γ mid, ⟨mid, hmid, rfl⟩⟩
  rcases hcover hne.some_mem with hleft | hright
  · have hsel : Y ⊆ Plane.arcCCW d w :=
      hconn.subset_left_of_subset_union (Plane.isOpen_arcCCW d w)
        (Plane.isOpen_arcCCW w d) hdisj hcover ⟨hne.some, hne.some_mem, hleft⟩
    exact Or.inl (fun t ht => hsel ⟨t, ht, rfl⟩)
  · have hsel : Y ⊆ Plane.arcCCW w d :=
      hconn.subset_left_of_subset_union (Plane.isOpen_arcCCW w d)
        (Plane.isOpen_arcCCW d w) hdisj.symm (fun z hz => (hcover hz).symm)
        ⟨hne.some, hne.some_mem, hright⟩
    exact Or.inr (fun t ht => hsel ⟨t, ht, rfl⟩)

private theorem actualFirstExitRetainsAngularSector
    {d w : Plane} (hd : Plane.IsDirection d) (hw : Plane.IsDirection w)
    (hdw : d ≠ w) (γ : Interval → Plane)
    (hγ : Topology.IsClosedEmbedding γ) (hzero : γ 0 = 0)
    (cut : Interval) (hcut : 0 < cut.val)
    (hprefix : ∀ t ∈ Ioo (0 : Interval) cut, γ t ∈ Plane.arcCCW d w)
    (havoid : γ cut ∉ {z | ∃ s : ℝ, 0 ≤ s ∧ z = s • d} ∪
      {z | ∃ s : ℝ, 0 ≤ s ∧ z = s • w}) :
    γ cut ∈ Plane.arcCCW d w := by
  have hcutcl : cut ∈ closure (Ioo (0 : Interval) cut) := by
    have hne : (0 : Interval) ≠ cut := by
      intro he
      have hh := congrArg Subtype.val he
      norm_num at hh
      linarith
    rw [closure_Ioo hne]
    exact ⟨hcut.le, le_refl cut⟩
  have hdisj := actualTwoRayArcsDisjoint hd hw hdw
  have hsub : Ioo (0 : Interval) cut ⊆ γ ⁻¹' (Plane.arcCCW w d)ᶜ := by
    intro t ht
    exact Set.disjoint_left.mp hdisj (hprefix t ht)
  have hclosed : IsClosed (γ ⁻¹' (Plane.arcCCW w d)ᶜ) :=
    (Plane.isOpen_arcCCW w d).isClosed_compl.preimage hγ.continuous
  have hnotReverse : γ cut ∉ Plane.arcCCW w d :=
    hclosed.closure_subset_iff.mpr hsub hcutcl
  have hcut0 : γ cut ≠ 0 := by
    intro he
    have h0 : cut = 0 := hγ.injective (he.trans hzero.symm)
    exact (ne_of_gt hcut) (congrArg Subtype.val h0)
  have hnotd : Plane.dir (γ cut) ≠ d := by
    intro he
    apply havoid
    apply Or.inl
    refine ⟨‖γ cut‖, norm_nonneg _, ?_⟩
    rw [← he]
    exact (Schoenflies.smul_norm_dir hcut0).symm
  have hnotw : Plane.dir (γ cut) ≠ w := by
    intro he
    apply havoid
    apply Or.inr
    refine ⟨‖γ cut‖, norm_nonneg _, ?_⟩
    rw [← he]
    exact (Schoenflies.smul_norm_dir hcut0).symm
  rcases actualTwoRayArcCover hd hw hdw hcut0 hnotd hnotw with h | h
  · exact h
  · exact False.elim (hnotReverse h)

private theorem actualShortClosedBallRayPointInFixedSegment
    {v z : Plane} (hv : v ≠ 0) {R : ℝ} (hRv : R < ‖v‖)
    (hzR : z ∈ closedBall (0 : Plane) R)
    (hzray : ∃ s : ℝ, 0 ≤ s ∧ z = s • Plane.dir v) :
    z ∈ segment ℝ (0 : Plane) v := by
  obtain ⟨s, hs, hz⟩ := hzray
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hsNorm : ‖z‖ = s := by
    rw [hz, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs,
      (Plane.isDirection_dir hv).norm, mul_one]
  have hslt : s < ‖v‖ := by
    have hb : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hzR
    linarith
  refine ⟨1 - s / ‖v‖, s / ‖v‖,
    by have hh := (div_le_one hvn).mpr hslt.le; linarith,
    div_nonneg hs hvn.le,
    by ring, ?_⟩
  calc
    (1 - s / ‖v‖) • (0 : Plane) + (s / ‖v‖) • v =
        (s / ‖v‖) • v := by simp
    _ = (s / ‖v‖) • (‖v‖ • Plane.dir v) := by rw [Schoenflies.smul_norm_dir hv]
    _ = s • Plane.dir v := by rw [smul_smul, div_mul_cancel₀ s hvn.ne']
    _ = z := hz.symm

private theorem actualShortBallSourceAvoidsFixedRays
    (v : Fin 2 → Plane) (hv : ∀ j, v j ≠ 0)
    {R : ℝ} (hRv : ∀ j, R < ‖v j‖)
    (γ : Interval → Plane)
    (havoid : ∀ t : Interval, 0 < t.val →
      γ t ∉ segment ℝ (0 : Plane) (v 0) ∪ segment ℝ (0 : Plane) (v 1))
    (t : Interval) (ht : 0 < t.val) (hball : γ t ∈ ball (0 : Plane) R) :
    γ t ∉ {z | ∃ s : ℝ, 0 ≤ s ∧ z = s • Plane.dir (v 0)} ∪
      {z | ∃ s : ℝ, 0 ≤ s ∧ z = s • Plane.dir (v 1)} := by
  intro h
  apply havoid t ht
  rcases h with h0 | h1
  · exact Or.inl (actualShortClosedBallRayPointInFixedSegment (hv 0) (hRv 0)
      (ball_subset_closedBall hball) h0)
  · exact Or.inr (actualShortClosedBallRayPointInFixedSegment (hv 1) (hRv 1)
      (ball_subset_closedBall hball) h1)

private theorem actualTwoFixedDirectionsDistinct
    (v : Fin 2 → Plane) (hv : ∀ j, v j ≠ 0)
    (hfan : segment ℝ (0 : Plane) (v 0) ∩
      segment ℝ (0 : Plane) (v 1) = {0})
    {R : ℝ} (hR : 0 < R) (hRv : ∀ j, R < ‖v j‖) :
    Plane.dir (v 0) ≠ Plane.dir (v 1) := by
  intro he
  let z : Plane := (R / 2) • Plane.dir (v 0)
  have hhalf : 0 < R / 2 := by linarith
  have hball : z ∈ ball (0 : Plane) R := by
    rw [mem_ball, dist_zero_right]
    change ‖(R / 2) • Plane.dir (v 0)‖ < R
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hhalf,
      (Plane.isDirection_dir (hv 0)).norm, mul_one]
    linarith
  have hz0 : z ∈ segment ℝ (0 : Plane) (v 0) :=
    actualShortClosedBallRayPointInFixedSegment (hv 0) (hRv 0)
      (ball_subset_closedBall hball)
      ⟨R / 2, hhalf.le, rfl⟩
  have hz1 : z ∈ segment ℝ (0 : Plane) (v 1) :=
    actualShortClosedBallRayPointInFixedSegment (hv 1) (hRv 1)
      (ball_subset_closedBall hball)
      ⟨R / 2, hhalf.le, by simp only [z, he]⟩
  have hez : z = 0 := by
    have hh : z ∈ ({0} : Set Plane) := by rw [← hfan]; exact ⟨hz0, hz1⟩
    simpa using hh
  have hn : ‖z‖ = R / 2 := by
    simp only [z, norm_smul, Real.norm_eq_abs, abs_of_pos hhalf,
      (Plane.isDirection_dir (hv 0)).norm, mul_one]
  rw [hez, norm_zero] at hn
  linarith

private theorem actualOriginalSourceFirstExitShortBall
    (γ : Interval → Plane) (hγ : Topology.IsClosedEmbedding γ) (hzero : γ 0 = 0)
    {R : ℝ} (hR : 0 < R) (hRend : R < ‖γ 1‖) :
    ∃ cut : Interval, 0 < cut.val ∧ cut.val < 1 ∧
      γ cut ∈ sphere (0 : Plane) R ∧
      ∀ t : Interval, t < cut → γ t ∈ ball (0 : Plane) R := by
  let α : Path (0 : Plane) (γ 1) := {
    toFun := γ
    continuous_toFun := hγ.continuous
    source' := hzero
    target' := rfl }
  have hout : γ 1 ∉ ball (0 : Plane) R := by
    intro hh
    have hn : ‖γ 1‖ < R := by simpa only [mem_ball, dist_zero_right] using hh
    linarith
  obtain ⟨cut, hc, hfront, hbefore⟩ :=
    CurveComplex.path_first_exit_frontier α (ball (0 : Plane) R)
      isOpen_ball (by simpa only [mem_ball, dist_self] using hR) hout
  have hsphere : γ cut ∈ sphere (0 : Plane) R := by
    have hh : α cut ∈ sphere (0 : Plane) R := by
      simpa only [frontier_ball (0 : Plane) (ne_of_gt hR)] using hfront
    exact hh
  have hc1 : cut.val < 1 := by
    apply lt_of_le_of_ne cut.property.2
    intro he
    have hcut : cut = 1 := Subtype.ext he
    have hn : ‖γ 1‖ = R := by
      simpa only [hcut, mem_sphere, dist_zero_right] using hsphere
    linarith
  exact ⟨cut, hc, hc1, hsphere, fun t ht => hbefore t ht⟩

private theorem actualOriginalPrefixInOneActualSector
    (v : Fin 2 → Plane) (hv : ∀ j, v j ≠ 0)
    (hfan : segment ℝ (0 : Plane) (v 0) ∩
      segment ℝ (0 : Plane) (v 1) = {0})
    (γ : Interval → Plane) (hγ : Topology.IsClosedEmbedding γ)
    (hzero : γ 0 = 0)
    (havoid : ∀ t : Interval, 0 < t.val →
      γ t ∉ segment ℝ (0 : Plane) (v 0) ∪
        segment ℝ (0 : Plane) (v 1))
    {R : ℝ} (hR : 0 < R) (hRv : ∀ j, R < ‖v j‖)
    (hRend : R < ‖γ 1‖) :
    ∃ cut : Interval, 0 < cut.val ∧ cut.val < 1 ∧
      γ cut ∈ sphere (0 : Plane) R ∧
      ((γ cut ∈ Plane.arcCCW (Plane.dir (v 0)) (Plane.dir (v 1)) ∧
          ∀ t ∈ Ioo (0 : Interval) cut,
            γ t ∈ Plane.cone 0 (Plane.arcCCW (Plane.dir (v 0)) (Plane.dir (v 1))) R) ∨
        (γ cut ∈ Plane.arcCCW (Plane.dir (v 1)) (Plane.dir (v 0)) ∧
          ∀ t ∈ Ioo (0 : Interval) cut,
            γ t ∈ Plane.cone 0 (Plane.arcCCW (Plane.dir (v 1)) (Plane.dir (v 0))) R)) := by
  obtain ⟨cut, hc, hc1, hsphere, hbefore⟩ :=
    actualOriginalSourceFirstExitShortBall γ hγ hzero hR hRend
  have hd : Plane.IsDirection (Plane.dir (v 0)) := Plane.isDirection_dir (hv 0)
  have hw : Plane.IsDirection (Plane.dir (v 1)) := Plane.isDirection_dir (hv 1)
  have hdw : Plane.dir (v 0) ≠ Plane.dir (v 1) :=
    actualTwoFixedDirectionsDistinct v hv hfan hR hRv
  have hrays : ∀ t ∈ Ioo (0 : Interval) cut,
      γ t ∉ {z | ∃ s : ℝ, 0 ≤ s ∧ z = s • Plane.dir (v 0)} ∪
        {z | ∃ s : ℝ, 0 ≤ s ∧ z = s • Plane.dir (v 1)} := by
    intro t ht
    exact actualShortBallSourceAvoidsFixedRays v hv hRv γ havoid t ht.1
      (hbefore t ht.2)
  have hclosedball : γ cut ∈ closedBall (0 : Plane) R :=
    sphere_subset_closedBall hsphere
  have hcutRays :
      γ cut ∉ {z | ∃ s : ℝ, 0 ≤ s ∧ z = s • Plane.dir (v 0)} ∪
        {z | ∃ s : ℝ, 0 ≤ s ∧ z = s • Plane.dir (v 1)} := by
    intro h
    apply havoid cut hc
    rcases h with h0 | h1
    · exact Or.inl (actualShortClosedBallRayPointInFixedSegment
        (hv 0) (hRv 0) hclosedball h0)
    · exact Or.inr (actualShortClosedBallRayPointInFixedSegment
        (hv 1) (hRv 1) hclosedball h1)
  rcases actualSourcePrefixSelectsOneOfTwoRaySectors hd hw hdw γ hγ hzero cut hc hrays
    with hleft | hright
  · have hendpoint := actualFirstExitRetainsAngularSector
      hd hw hdw γ hγ hzero cut hc hleft hcutRays
    refine ⟨cut, hc, hc1, hsphere, Or.inl ⟨hendpoint, ?_⟩⟩
    intro t ht
    apply Plane.mem_cone_iff.mpr
    exact ⟨by simpa only [sub_zero] using hleft t ht,
      mem_ball.mp (hbefore t ht.2)⟩
  · have hendpoint := actualFirstExitRetainsAngularSector
      hw hd hdw.symm γ hγ hzero cut hc hright (by simpa [union_comm] using hcutRays)
    refine ⟨cut, hc, hc1, hsphere, Or.inr ⟨hendpoint, ?_⟩⟩
    intro t ht
    apply Plane.mem_cone_iff.mpr
    exact ⟨by simpa only [sub_zero] using hright t ht,
      mem_ball.mp (hbefore t ht.2)⟩

private theorem actualJoinedRadialArmsArc
    {d w : Plane} (hd : Plane.IsDirection d) (hw : Plane.IsDirection w)
    (hdw : d ≠ w) {R : ℝ} (hR : 0 < R) :
    IsArcBetween
      (segment ℝ (R • d) (0 : Plane) ∪ segment ℝ (0 : Plane) (R • w))
      (R • d) (R • w) := by
  let γ := Path.segment (R • d) (0 : Plane)
  let δ := Path.segment (0 : Plane) (R • w)
  have hd0 : R • d ≠ (0 : Plane) := smul_ne_zero (ne_of_gt hR) hd.ne_zero
  have hw0 : (0 : Plane) ≠ R • w := (smul_ne_zero (ne_of_gt hR) hw.ne_zero).symm
  have hmeetSeg : segment ℝ (R • d) 0 ∩
      segment ℝ 0 (R • w) = {(0 : Plane)} := by
    have hsym : segment ℝ (R • d) (0 : Plane) = segment ℝ 0 (R • d) :=
      segment_symm ℝ _ _
    rw [hsym]
    apply Subset.antisymm
    · have hh := Schoenflies.radial_inter_radial (x := (0 : Plane))
        (d₁ := d) (d₂ := w) hd hw hdw hR
      simpa only [zero_add] using hh
    · intro z hz
      have he : z = 0 := by simpa using hz
      subst z
      exact ⟨left_mem_segment ℝ 0 (R • d), left_mem_segment ℝ 0 (R • w)⟩
  have hmeet : range γ ∩ range δ = {(0 : Plane)} := by
    simpa only [γ, δ, Path.range_segment] using hmeetSeg
  let η := γ.trans δ
  have hη : Function.Injective η :=
    LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
      γ δ (Path.segment_injective_of_ne hd0)
      (Path.segment_injective_of_ne hw0) hmeet
  refine ⟨η.extend, η.continuous_extend.continuousOn, ?_, ?_,
    η.extend_zero, η.extend_one⟩
  · intro s hs t ht he
    rw [Path.extend_apply _ hs, Path.extend_apply _ ht] at he
    exact congrArg Subtype.val (hη he)
  · exact (η.image_extend_of_subset (Subset.refl (Icc (0 : ℝ) 1))).trans
      (by simpa [γ, δ, Path.range_segment] using Path.trans_range γ δ)

private theorem actualRoundSupportJordanInside {R : ℝ} (hR : 0 < R) :
    IsJordanCurve (sphere (0 : Plane) R) ∧
      inside (sphere (0 : Plane) R) = ball (0 : Plane) R := by
  have hQclosed : IsClosed (closedBall (0 : Plane) R) := isClosed_closedBall
  have hQint : (interior (closedBall (0 : Plane) R)).Nonempty := by
    rw [interior_closedBall (0 : Plane) (ne_of_gt hR)]
    exact ⟨0, by simpa only [mem_ball, dist_self] using hR⟩
  have hSquareInt : (interior (Plane.closedSquare 0 1)).Nonempty := by
    rw [interior_closedSquare_zero_one]
    exact ⟨0, by simpa [mem_openSquare_zero_one, Plane.supNorm]⟩
  obtain ⟨E, _, _, hfront⟩ := exists_homeomorph_image_eq
    (convex_closedBall (0 : Plane) R) hQint
    (NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_closedBall)
    (Plane.convex_closedSquare 0 1) hSquareInt
    (NormedSpace.isVonNBounded_of_isBounded ℝ (Plane.isBounded_closedSquare 0 1))
  have hEsphere : E '' sphere (0 : Plane) R = modelCurve := by
    simpa only [frontier_closedBall (0 : Plane) (ne_of_gt hR),
      ← modelCurve_eq_frontier] using hfront
  have hJ : IsJordanCurve (sphere (0 : Plane) R) := by
    obtain ⟨f, hfloop, hfimage⟩ := isJordanCurve_modelCurve
    refine ⟨E.symm ∘ f, ?_, ?_⟩
    · rcases hfloop with ⟨hfcont, hfclose, hfinj⟩
      refine ⟨E.symm.continuous.comp_continuousOn hfcont, ?_, ?_⟩
      · exact congrArg E.symm hfclose
      · intro x hx y hy he
        exact hfinj hx hy (E.symm.injective he)
    · rw [image_comp, hfimage, ← hEsphere]
      exact E.symm_image_image (sphere (0 : Plane) R)
  have hsub : ball (0 : Plane) R ⊆ (sphere (0 : Plane) R)ᶜ := by
    intro x hx hs
    exact (ne_of_lt (mem_ball.mp hx)) (mem_sphere.mp hs)
  have hfr : frontier (ball (0 : Plane) R) ∩ (sphere (0 : Plane) R)ᶜ = ∅ := by
    rw [frontier_ball (0 : Plane) (ne_of_gt hR)]
    exact Set.inter_compl_self _
  have hzero : (0 : Plane) ∈ ball (0 : Plane) R := by
    simpa only [mem_ball, dist_self] using hR
  have hcomp := Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint
    Metric.isOpen_ball (Metric.isConnected_ball hR).isPreconnected hsub hfr hzero
  have hinside : (0 : Plane) ∈ inside (sphere (0 : Plane) R) := by
    refine ⟨hsub hzero, ?_⟩
    rw [hcomp]
    exact Metric.isBounded_ball
  exact ⟨hJ,
    ((jordan_curve_theorem hJ).connectedComponentIn_eq_inside hinside).symm.trans hcomp⟩

private theorem actualTwoRadialArmsInterior
    {d w : Plane} (hd : Plane.IsDirection d) (hw : Plane.IsDirection w)
    {R : ℝ} (hR : 0 < R) :
    (segment ℝ (R • d) (0 : Plane) ∪ segment ℝ (0 : Plane) (R • w)) \
      {R • d, R • w} ⊆ ball (0 : Plane) R := by
  intro z hz
  have hleft : z ≠ R • d := by
    intro he
    apply hz.2
    simp [he]
  have hright : z ≠ R • w := by
    intro he
    apply hz.2
    simp [he]
  have hzero : (0 : Plane) ∈ ball (0 : Plane) R := by
    simpa only [mem_ball, dist_self] using hR
  rcases hz.1 with hzleft | hzright
  · have hsym : segment ℝ (R • d) (0 : Plane) = segment ℝ 0 (R • d) :=
      segment_symm ℝ _ _
    rw [hsym] at hzleft
    by_cases hz0 : z = 0
    · exact hz0 ▸ hzero
    · have hopen : z ∈ openSegment ℝ (0 : Plane) (R • d) :=
        mem_openSegment_of_ne_left_right (Ne.symm hz0) (Ne.symm hleft) hzleft
      have hh := Schoenflies.mem_openSegment_radial (x := (0 : Plane)) (d := d) (r := R)
        hd hR (by simpa only [zero_add] using hopen)
      exact mem_ball.mpr hh.2
  · by_cases hz0 : z = 0
    · exact hz0 ▸ hzero
    · have hopen : z ∈ openSegment ℝ (0 : Plane) (R • w) :=
        mem_openSegment_of_ne_left_right (Ne.symm hz0) (Ne.symm hright) hzright
      have hh := Schoenflies.mem_openSegment_radial (x := (0 : Plane)) (d := w) (r := R)
        hw hR (by simpa only [zero_add] using hopen)
      exact mem_ball.mpr hh.2

private theorem actualTwoRadialCrosscutCells
    {d w : Plane} (hd : Plane.IsDirection d) (hw : Plane.IsDirection w)
    (hdw : d ≠ w) {R : ℝ} (hR : 0 < R) :
    let P := segment ℝ (R • d) (0 : Plane) ∪
      segment ℝ (0 : Plane) (R • w)
    ∃ A B : Set Plane,
      IsCutPair (sphere (0 : Plane) R) (R • d) (R • w) A B ∧
      inside (sphere (0 : Plane) R) \ P =
        inside (A ∪ P) ∪ inside (B ∪ P) ∧
      Disjoint (inside (A ∪ P)) (inside (B ∪ P)) ∧
      closure (inside (A ∪ P)) ∩ sphere (0 : Plane) R = A ∧
      closure (inside (B ∪ P)) ∩ sphere (0 : Plane) R = B := by
  intro P
  obtain ⟨hJ, hInside⟩ := actualRoundSupportJordanInside hR
  have hp : R • d ∈ sphere (0 : Plane) R := by
    rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hR, hd.norm, mul_one]
  have hq : R • w ∈ sphere (0 : Plane) R := by
    rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hR, hw.norm, mul_one]
  have hP : IsArcBetween P (R • d) (R • w) :=
    actualJoinedRadialArmsArc hd hw hdw hR
  obtain ⟨A, B, hcut⟩ := exists_isCutPair hJ hp hq hP.ne
  have hPi : P \ {R • d, R • w} ⊆ inside (sphere (0 : Plane) R) := by
    rw [hInside]
    exact actualTwoRadialArmsInterior hd hw hR
  have hclass := general_crosscut_arbitrary_of_endpoints hJ hP hcut hPi
  exact ⟨A, B, hcut, hclass.1, hclass.2.1,
    hclass.2.2.2.2.2.2.2.2.1, hclass.2.2.2.2.2.2.2.2.2⟩

private theorem actualCrosscutSideJordan
    {C A P : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hP : IsArcBetween P p q)
    (hAC : A ⊆ C) (hPi : P \ {p, q} ⊆ inside C) :
    IsJordanCurve (A ∪ P) := by
  apply isJordanCurve_union hA hP
  intro z hzA hzP
  by_contra hne
  exact inside_subset_compl (hPi ⟨hzP, hne⟩) (hAC hzA)

private theorem actualConeAvoidsRadialCrosscut
    {d w z : Plane} {R : ℝ}
    (hz : z ∈ Plane.cone 0 (Plane.arcCCW d w) R) :
    z ∉ segment ℝ (0 : Plane) (R • d) ∪
      segment ℝ (0 : Plane) (R • w) := by
  have harc : z ∈ Plane.arcCCW d w := by
    simpa only [sub_zero] using (Plane.mem_cone_iff.mp hz).1
  have hR : 0 ≤ R :=
    le_of_lt (lt_of_le_of_lt dist_nonneg (Plane.mem_cone_iff.mp hz).2)
  intro hzP
  rcases hzP with hzD | hzW
  · rw [segment_eq_image] at hzD
    obtain ⟨t, ht, htz⟩ := hzD
    have htz' : z = (t * R) • d := by simpa [smul_smul] using htz.symm
    rw [htz'] at harc
    exact (Plane.notMem_arcCCW_smul d w (mul_nonneg ht.1 hR)).1 harc
  · rw [segment_eq_image] at hzW
    obtain ⟨t, ht, htz⟩ := hzW
    have htz' : z = (t * R) • w := by simpa [smul_smul] using htz.symm
    rw [htz'] at harc
    exact (Plane.notMem_arcCCW_smul w d (mul_nonneg ht.1 hR)).2 harc

private theorem actualConeFallsInOneCrosscutCell
    {d w : Plane} (hd : Plane.IsDirection d) (hw : Plane.IsDirection w)
    (hdw : d ≠ w) {R : ℝ} (hR : 0 < R)
    {A B : Set Plane}
    (hcut : IsCutPair (sphere (0 : Plane) R) (R • d) (R • w) A B)
    (hsplit :
      let P := segment ℝ (R • d) (0 : Plane) ∪
        segment ℝ (0 : Plane) (R • w)
      inside (sphere (0 : Plane) R) \ P =
        inside (A ∪ P) ∪ inside (B ∪ P))
    (hdisj :
      let P := segment ℝ (R • d) (0 : Plane) ∪
        segment ℝ (0 : Plane) (R • w)
      Disjoint (inside (A ∪ P)) (inside (B ∪ P))) :
    let P := segment ℝ (R • d) (0 : Plane) ∪
      segment ℝ (0 : Plane) (R • w)
    Plane.cone 0 (Plane.arcCCW d w) R ⊆ inside (A ∪ P) ∨
      Plane.cone 0 (Plane.arcCCW d w) R ⊆ inside (B ∪ P) := by
  intro P
  obtain ⟨hJ, hInside⟩ := actualRoundSupportJordanInside hR
  have hP : IsArcBetween P (R • d) (R • w) :=
    actualJoinedRadialArmsArc hd hw hdw hR
  have hPi : P \ {R • d, R • w} ⊆ inside (sphere (0 : Plane) R) := by
    rw [hInside]
    exact actualTwoRadialArmsInterior hd hw hR
  have hJA : IsJordanCurve (A ∪ P) :=
    actualCrosscutSideJordan hcut.fst hP hcut.fst_subset hPi
  have hJB : IsJordanCurve (B ∪ P) :=
    actualCrosscutSideJordan hcut.snd hP hcut.snd_subset hPi
  let U := Plane.cone 0 (Plane.arcCCW d w) R
  have hconn : IsConnected U :=
    Plane.isConnected_cone_arcCCW_of_ne 0 hd hw hdw hR
  have hUP : U ⊆ inside (sphere (0 : Plane) R) \ P := by
    intro z hz
    constructor
    · rw [hInside]
      exact Plane.cone_subset_ball hz
    · intro hzP
      apply actualConeAvoidsRadialCrosscut hz
      rcases hzP with hzD | hzW
      · have hsym : segment ℝ (R • d) (0 : Plane) = segment ℝ 0 (R • d) :=
          segment_symm ℝ _ _
        exact Or.inl (hsym ▸ hzD)
      · exact Or.inr hzW
  have hcover : U ⊆ inside (A ∪ P) ∪ inside (B ∪ P) := by
    rw [← hsplit]
    exact hUP
  obtain ⟨z, hz⟩ := hconn.nonempty
  rcases hcover hz with hzA | hzB
  · exact Or.inl (hconn.isPreconnected.subset_left_of_subset_union
      (isOpen_inside hJA.isClosed) (isOpen_inside hJB.isClosed)
      hdisj hcover ⟨z, hz, hzA⟩)
  · exact Or.inr (hconn.isPreconnected.subset_left_of_subset_union
      (isOpen_inside hJB.isClosed) (isOpen_inside hJA.isClosed)
      hdisj.symm (fun y hy => (hcover hy).symm) ⟨z, hz, hzB⟩)

private theorem actualOpenSetContainsNonhorizontalPoint
    {U : Set Plane} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, x 1 ≠ 0 := by
  obtain ⟨p, hp⟩ := hne
  let f : ℝ → Plane := fun t => Plane.mk (p 0) t
  have hfc : Continuous f := by fun_prop
  have hW : IsOpen (f ⁻¹' U) := hU.preimage hfc
  have hpEq : f (p 1) = p := by
    ext i
    fin_cases i <;> simp [f]
  have hWne : (f ⁻¹' U).Nonempty := ⟨p 1, by simpa only [mem_preimage, hpEq] using hp⟩
  obtain ⟨t, ht, htW⟩ :=
    ((Set.finite_singleton (0 : ℝ)).countable.dense_compl ℝ).exists_mem_open hW hWne
  exact ⟨f t, htW, by simpa [f] using ht⟩

private theorem actualOpenSetAvoidsFiniteLines
    {K : Type} [Fintype K] (v : K → Plane)
    {U : Set Plane} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ q ∈ U, ∀ (k : K) (r : ℝ), q ≠ r • v k := by
  classical
  obtain ⟨x, hx, hx1⟩ := actualOpenSetContainsNonhorizontalPoint hU hne
  let f : ℝ → Plane := fun t => Plane.mk t (x 1)
  have hfc : Continuous f := by fun_prop
  let T : Set ℝ := range (fun k => (v k 0 / v k 1) * x 1)
  have hT : T.Finite := finite_range _
  have hxEq : f (x 0) = x := by
    ext i
    fin_cases i <;> simp [f]
  have hW : IsOpen (f ⁻¹' U) := hU.preimage hfc
  have hWne : (f ⁻¹' U).Nonempty := ⟨x 0, by simpa only [mem_preimage, hxEq] using hx⟩
  obtain ⟨t, htNot, htU⟩ := (hT.countable.dense_compl ℝ).exists_mem_open hW hWne
  refine ⟨f t, htU, ?_⟩
  intro k r he
  have he0 : t = r * v k 0 := by
    have hh := congrArg (fun z : Plane => z 0) he
    simpa [f] using hh
  have he1 : x 1 = r * v k 1 := by
    have hh := congrArg (fun z : Plane => z 1) he
    simpa [f] using hh
  have hv1 : v k 1 ≠ 0 := by intro hh; simp [hh] at he1; exact hx1 he1
  have htSlope : t = (v k 0 / v k 1) * x 1 := by
    rw [he0, he1]
    field_simp [hv1]
  apply htNot
  exact ⟨k, htSlope.symm⟩

private theorem actualBoundarySectorTargetBend
    {K : Type} [Fintype K] (oldVector : K → Plane)
    {d w b : Plane} {R : ℝ} (hR : 0 < R)
    (hbSphere : b ∈ sphere (0 : Plane) R)
    (hbArc : b ∈ Plane.arcCCW d w) :
    ∃ q : Plane, q ∈ Plane.cone 0 (Plane.arcCCW d w) R ∧
      (∀ r : ℝ, q ≠ r • b) ∧
      (∀ k : K, ∀ r : ℝ, q ≠ r • oldVector k) ∧
      segment ℝ q b \ {b} ⊆ Plane.cone 0 (Plane.arcCCW d w) R := by
  classical
  obtain ⟨ε, hε, hεArc⟩ :=
    Metric.isOpen_iff.mp (Plane.isOpen_arcCCW d w) b hbArc
  let U : Set Plane := ball b ε ∩ ball (0 : Plane) R
  have hU : IsOpen U := isOpen_ball.inter isOpen_ball
  have hbcl : b ∈ closure (ball (0 : Plane) R) := by
    rw [closure_ball (0 : Plane) (ne_of_gt hR)]
    exact sphere_subset_closedBall hbSphere
  obtain ⟨x, hxBall, hxNear⟩ := (Metric.mem_closure_iff.mp hbcl) ε hε
  have hUne : U.Nonempty := by
    refine ⟨x, ?_⟩
    exact ⟨by simpa only [mem_ball, dist_comm] using hxNear, hxBall⟩
  let allv : Option K → Plane := fun k => Option.casesOn k b oldVector
  obtain ⟨q, hqU, hqv⟩ := actualOpenSetAvoidsFiniteLines allv hU hUne
  have hqNear : q ∈ ball b ε := hqU.1
  have hqBall : q ∈ ball (0 : Plane) R := hqU.2
  have hqArc : q ∈ Plane.arcCCW d w := hεArc hqNear
  have hqCone : q ∈ Plane.cone 0 (Plane.arcCCW d w) R :=
    Plane.mem_cone_iff.mpr ⟨by simpa only [sub_zero] using hqArc, mem_ball.mp hqBall⟩
  refine ⟨q, hqCone, (fun r => hqv none r), (fun k r => hqv (some k) r), ?_⟩
  intro z hz
  have hzArc : z ∈ Plane.arcCCW d w := by
    apply hεArc
    have hbNear : b ∈ ball b ε := by simpa only [mem_ball, dist_self] using hε
    exact (convex_ball b ε).segment_subset hqNear hbNear hz.1
  have hzBall : z ∈ ball (0 : Plane) R := by
    have hzb : z ≠ b := by
      intro he
      exact hz.2 (by simp [he])
    by_cases hzq : z = q
    · exact hzq ▸ hqBall
    · have hopen : z ∈ openSegment ℝ q b :=
        mem_openSegment_of_ne_left_right (Ne.symm hzq) (Ne.symm hzb) hz.1
      have hqi : q ∈ interior (closedBall (0 : Plane) R) := by
        rw [interior_closedBall (0 : Plane) (ne_of_gt hR)]
        exact hqBall
      have hbi : b ∈ closedBall (0 : Plane) R := sphere_subset_closedBall hbSphere
      have hi := (convex_closedBall (0 : Plane) R).openSegment_interior_self_subset_interior
        hqi hbi hopen
      rwa [interior_closedBall (0 : Plane) (ne_of_gt hR)] at hi
  exact Plane.mem_cone_iff.mpr ⟨by simpa only [sub_zero] using hzArc, mem_ball.mp hzBall⟩

private theorem actualSimpleBentTargetArc
    {q b : Plane} (hb0 : b ≠ 0) (hqLine : ∀ r : ℝ, q ≠ r • b) :
    IsArcBetween (segment ℝ (0 : Plane) q ∪ segment ℝ q b) 0 b := by
  have hq0 : q ≠ 0 := by simpa using hqLine 0
  have hqb : q ≠ b := by simpa using hqLine 1
  have hind : ∀ r s : ℝ, r • q = s • b → r = 0 ∧ s = 0 := by
    intro r s he
    by_cases hr : r = 0
    · have hs : s = 0 := by
        have hh : s • b = 0 := by simpa [hr] using he.symm
        exact (smul_eq_zero.mp hh).resolve_right hb0
      exact ⟨hr, hs⟩
    · exfalso
      apply hqLine (r⁻¹ * s)
      have hh := congrArg (fun z : Plane => r⁻¹ • z) he
      simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using hh
  have hinter : segment ℝ (0 : Plane) q ∩ segment ℝ q b = {q} := by
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      obtain ⟨r, s, hr, hs, hrs, hx⟩ := hx
      obtain ⟨u, v, hu, hv, huv, hx'⟩ := hx'
      have he : (s - u) • q = v • b := by
        calc
          (s - u) • q = (r • (0 : Plane) + s • q) - u • q := by module
          _ = v • b := by rw [hx, ← hx']; module
      have hv0 := (hind _ _ he).2
      have hu1 : u = 1 := by linarith
      have hxe : x = q := by rw [← hx', hv0, hu1]; simp
      exact hxe
    · intro hx
      have he : x = q := hx
      subst x
      exact ⟨right_mem_segment ℝ 0 q, left_mem_segment ℝ q b⟩
  let γ := Path.segment (0 : Plane) q
  let δ := Path.segment q b
  have hmeet : range γ ∩ range δ = {q} := by
    simpa only [γ, δ, Path.range_segment] using hinter
  let η := γ.trans δ
  have hη : Function.Injective η :=
    LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
      γ δ (Path.segment_injective_of_ne hq0.symm)
      (Path.segment_injective_of_ne hqb) hmeet
  refine ⟨η.extend, η.continuous_extend.continuousOn, ?_, ?_,
    η.extend_zero, η.extend_one⟩
  · intro s hs t ht he
    rw [Path.extend_apply _ hs, Path.extend_apply _ ht] at he
    exact congrArg Subtype.val (hη he)
  · exact (η.image_extend_of_subset (Subset.refl (Icc (0 : ℝ) 1))).trans
      (by simpa [γ, δ, Path.range_segment] using Path.trans_range γ δ)

private theorem actualBentTargetInteriorInCone
    {d w q b : Plane} {R : ℝ}
    (hq : q ∈ Plane.cone 0 (Plane.arcCCW d w) R)
    (hqb : segment ℝ q b \ {b} ⊆ Plane.cone 0 (Plane.arcCCW d w) R) :
    (segment ℝ (0 : Plane) q ∪ segment ℝ q b) \ {0, b} ⊆
      Plane.cone 0 (Plane.arcCCW d w) R := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro he
    apply hz.2
    simp [he]
  have hzb : z ≠ b := by
    intro he
    apply hz.2
    simp [he]
  rcases hz.1 with hzq | hzbseg
  · by_cases hze : z = q
    · exact hze ▸ hq
    · have hopen : z ∈ openSegment ℝ (0 : Plane) q :=
        mem_openSegment_of_ne_left_right (Ne.symm hz0) (Ne.symm hze) hzq
      exact Schoenflies.openSegment_subset_cone_arcCCW hq hopen
  · exact hqb ⟨hzbseg, by simpa using hzb⟩

private theorem actualOriginalPrefixIsArc
    (γ : Interval → Plane) (hγ : Topology.IsClosedEmbedding γ)
    (hzero : γ 0 = 0) (cut : Interval) (hc : 0 < cut.val) :
    IsArcBetween (γ '' Icc (0 : Interval) cut) 0 (γ cut) := by
  let k : Interval → Interval := fun t => ⟨cut.val * t.val, by
    constructor
    · exact mul_nonneg cut.property.1 t.property.1
    · nlinarith [cut.property.1, cut.property.2, t.property.1, t.property.2]⟩
  let η : Path (0 : Plane) (γ cut) := {
    toFun := γ ∘ k
    continuous_toFun := hγ.continuous.comp (by fun_prop)
    source' := by simp [k, hzero]
    target' := by simp [k]
  }
  have hη : Function.Injective η := by
    intro u v he
    have hh := congrArg Subtype.val (hγ.injective he)
    change cut.val * u.val = cut.val * v.val at hh
    exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hc) hh)
  have hrange : range η = γ '' Icc (0 : Interval) cut := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨k t, ?_, rfl⟩
      exact ⟨(k t).property.1, by
        change cut.val * t.val ≤ cut.val
        nlinarith [cut.property.1, t.property.2]⟩
    · rintro ⟨u, hu, rfl⟩
      let t : Interval := ⟨u.val / cut.val, by
        constructor
        · exact div_nonneg u.property.1 hc.le
        · exact (div_le_one hc).mpr hu.2⟩
      refine ⟨t, ?_⟩
      change γ (k t) = γ u
      congr 1
      apply Subtype.ext
      change cut.val * (u.val / cut.val) = u.val
      field_simp [ne_of_gt hc]
  rw [← hrange]
  refine ⟨η.extend, η.continuous_extend.continuousOn, ?_, ?_,
    η.extend_zero, η.extend_one⟩
  · intro u hu v hv he
    rw [Path.extend_apply _ hu, Path.extend_apply _ hv] at he
    exact congrArg Subtype.val (hη he)
  · exact η.image_extend_of_subset (Subset.refl (Icc (0 : ℝ) 1))

private theorem actualSectorExitOnChosenBoundary
    {C A P U : Set Plane} {b : Plane}
    (hbC : b ∈ C) (hbU : b ∈ closure U)
    (hUA : U ⊆ inside (A ∪ P))
    (hfront : closure (inside (A ∪ P)) ∩ C = A) : b ∈ A := by
  rw [← hfront]
  exact ⟨(closure_mono hUA) hbU, hbC⟩

private theorem actualBentExitInConeClosure
    {d w q b : Plane} {R : ℝ}
    (hbq : b ≠ q)
    (hqb : segment ℝ q b \ {b} ⊆
      Plane.cone 0 (Plane.arcCCW d w) R) :
    b ∈ closure (Plane.cone 0 (Plane.arcCCW d w) R) := by
  have hopen : openSegment ℝ q b ⊆
      Plane.cone 0 (Plane.arcCCW d w) R := by
    intro z hz
    apply hqb
    exact ⟨openSegment_subset_segment ℝ q b hz,
      by intro he; subst z; exact hbq.symm (right_mem_openSegment_iff.mp hz)⟩
  apply (closure_mono hopen)
  exact segment_subset_closure_openSegment (right_mem_segment ℝ q b)

private theorem actualGermSegmentAvoidingNoncollinearRay
    {q v : Plane} (h : ∀ r : ℝ, q ≠ r • v) :
    segment ℝ (0 : Plane) q ∩
      {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • v} = {0} := by
  apply Subset.antisymm
  · rintro z ⟨hz, r, hr, hzr⟩
    rw [segment_eq_image] at hz
    obtain ⟨t, ht, htz⟩ := hz
    have htq : t • q = z := by simpa using htz
    by_cases ht0 : t = 0
    · simpa [ht0] using htq.symm
    · exfalso
      apply h (t⁻¹ * r)
      have he := congrArg (fun x : Plane => t⁻¹ • x) (htq.trans hzr)
      simpa only [smul_smul, inv_mul_cancel₀ ht0, one_smul] using he
  · intro z hz
    have hz0 : z = 0 := hz
    subst z
    exact ⟨left_mem_segment ℝ 0 q, 0, le_refl 0, by simp⟩

private theorem actualShortFixedSegmentTruncation
    {v : Plane} (hv : v ≠ 0) {R : ℝ} (hR : 0 < R)
    (hRv : R < ‖v‖) :
    segment ℝ (0 : Plane) v ∩ closedBall 0 R =
      segment ℝ 0 (R • Plane.dir v) := by
  have hh := Schoenflies.segment_inter_closedBall hv hR
    (show R ≤ dist (0 : Plane) v by
      rw [dist_zero_left]
      exact hRv.le)
  simpa only [sub_zero, zero_add, Plane.dir, smul_smul,
    div_eq_mul_inv] using hh

private theorem actualRelativeTwoArmExtensionInCell
    {K : Type} [Fintype K] (oldVector : K → Plane)
    (v : Fin 2 → Plane) (hv : ∀ j, v j ≠ 0)
    {R : ℝ} (hR : 0 < R) (hRv : ∀ j, R < ‖v j‖)
    (γ : Interval → Plane) (hγ : Topology.IsClosedEmbedding γ)
    (hzero : γ 0 = 0) (cut : Interval) (hc : 0 < cut.val)
    (hbSphere : γ cut ∈ sphere (0 : Plane) R)
    {d w : Plane} (hbArc : γ cut ∈ Plane.arcCCW d w)
    (hprefix : ∀ t ∈ Ioo (0 : Interval) cut,
      γ t ∈ Plane.cone 0 (Plane.arcCCW d w) R)
    (C : Set Plane) (hJ : IsJordanCurve C)
    (h0C : (0 : Plane) ∈ C) (hbC : γ cut ∈ C)
    (hcone : Plane.cone 0 (Plane.arcCCW d w) R ⊆ inside C)
    (hcellBall : inside C ⊆ ball (0 : Plane) R)
    (hfixedBoundary :
      segment ℝ (0 : Plane) (R • Plane.dir (v 0)) ∪
        segment ℝ (0 : Plane) (R • Plane.dir (v 1)) ⊆ C) :
    ∃ (F : Plane ≃ₜ Plane) (q : Plane),
      F '' (γ '' Icc (0 : Interval) cut) =
        segment ℝ 0 q ∪ segment ℝ q (γ cut) ∧
      F 0 = 0 ∧
      (∀ x, x ∉ ball (0 : Plane) R → F x = x) ∧
      (∀ x ∈ segment ℝ (0 : Plane) (v 0) ∪
        segment ℝ (0 : Plane) (v 1), F x = x) ∧
      q ∈ Plane.cone 0 (Plane.arcCCW d w) R ∧
      (∀ r : ℝ, q ≠ r • γ cut) ∧
      (∀ k : K, ∀ r : ℝ, q ≠ r • oldVector k) := by
  classical
  let b := γ cut
  obtain ⟨q, hqCone, hqbLine, hqOld, hqbSeg⟩ :=
    actualBoundarySectorTargetBend oldVector hR hbSphere hbArc
  have hb0 : b ≠ 0 := by
    intro he
    have hn : ‖b‖ = R := by
      simpa only [b, mem_sphere, dist_zero_right] using hbSphere
    simp [he] at hn
    linarith
  have hq0 : q ≠ 0 := by simpa using hqbLine 0
  let S : Set Plane := γ '' Icc (0 : Interval) cut
  let N : Set Plane := segment ℝ 0 q ∪ segment ℝ q b
  have hSArc : IsArcBetween S 0 b :=
    actualOriginalPrefixIsArc γ hγ hzero cut hc
  have hNArc : IsArcBetween N 0 b := actualSimpleBentTargetArc hb0 hqbLine
  have hSi : S \ {0,b} ⊆ inside C := by
    rintro z ⟨⟨t, ht, rfl⟩, hend⟩
    have ht0 : (0 : Interval) < t := by
      apply lt_of_le_of_ne ht.1
      intro he
      apply hend
      simp [← he, hzero]
    have htc : t < cut := by
      apply lt_of_le_of_ne ht.2
      intro he
      apply hend
      simp [he, b]
    exact hcone (hprefix t ⟨ht0, htc⟩)
  have hNi : N \ {0,b} ⊆ inside C :=
    (actualBentTargetInteriorInCone hqCone hqbSeg).trans hcone
  obtain ⟨e⟩ := exists_arcHomeo hSArc hNArc
  obtain ⟨F, hpoint, hFN, hfix⟩ :=
    jordan_sector_prescribed_crosscut_ambient_extension hJ h0C hbC
      hSArc hNArc hSi hNi e
  have hF0 : F 0 = 0 :=
    hfix 0 (fun h => inside_subset_compl h h0C)
  have hfixBall : ∀ x, x ∉ ball (0 : Plane) R → F x = x := by
    intro x hx
    exact hfix x (fun hi => hx (hcellBall hi))
  have hfixArms : ∀ x ∈ segment ℝ (0 : Plane) (v 0) ∪
      segment ℝ (0 : Plane) (v 1), F x = x := by
    intro x hx
    by_cases hxb : x ∈ ball (0 : Plane) R
    · apply hfix x
      have hxclosed : x ∈ closedBall (0 : Plane) R := ball_subset_closedBall hxb
      have hxP : x ∈ segment ℝ (0 : Plane) (R • Plane.dir (v 0)) ∪
          segment ℝ (0 : Plane) (R • Plane.dir (v 1)) := by
        rcases hx with hx0 | hx1
        · left
          rw [← actualShortFixedSegmentTruncation (hv 0) hR (hRv 0)]
          exact ⟨hx0, hxclosed⟩
        · right
          rw [← actualShortFixedSegmentTruncation (hv 1) hR (hRv 1)]
          exact ⟨hx1, hxclosed⟩
      exact fun hi => inside_subset_compl hi (hfixedBoundary hxP)
    · exact hfixBall x hxb
  exact ⟨F, q, hFN, hF0, hfixBall, hfixArms,
    hqCone, hqbLine, hqOld⟩

private theorem actualRelativeTwoArmExtensionForDirectedSector
    {K : Type} [Fintype K] (oldVector : K → Plane)
    (v : Fin 2 → Plane) (hv : ∀ j, v j ≠ 0)
    {R : ℝ} (hR : 0 < R) (hRv : ∀ j, R < ‖v j‖)
    (γ : Interval → Plane) (hγ : Topology.IsClosedEmbedding γ)
    (hzero : γ 0 = 0) (cut : Interval) (hc : 0 < cut.val)
    (hbSphere : γ cut ∈ sphere (0 : Plane) R)
    {d w : Plane} (hd : Plane.IsDirection d) (hw : Plane.IsDirection w)
    (hdw : d ≠ w) (hbArc : γ cut ∈ Plane.arcCCW d w)
    (hprefix : ∀ t ∈ Ioo (0 : Interval) cut,
      γ t ∈ Plane.cone 0 (Plane.arcCCW d w) R)
    (hPfixed :
      segment ℝ (0 : Plane) (R • Plane.dir (v 0)) ∪
        segment ℝ (0 : Plane) (R • Plane.dir (v 1)) ⊆
      segment ℝ (R • d) (0 : Plane) ∪
        segment ℝ (0 : Plane) (R • w)) :
    ∃ (F : Plane ≃ₜ Plane) (q : Plane),
      F '' (γ '' Icc (0 : Interval) cut) =
        segment ℝ 0 q ∪ segment ℝ q (γ cut) ∧
      F 0 = 0 ∧
      (∀ x, x ∉ ball (0 : Plane) R → F x = x) ∧
      (∀ x ∈ segment ℝ (0 : Plane) (v 0) ∪
        segment ℝ (0 : Plane) (v 1), F x = x) ∧
      q ∈ Plane.cone 0 (Plane.arcCCW d w) R ∧
      (∀ r : ℝ, q ≠ r • γ cut) ∧
      (∀ k : K, ∀ r : ℝ, q ≠ r • oldVector k) := by
  let P := segment ℝ (R • d) (0 : Plane) ∪
    segment ℝ (0 : Plane) (R • w)
  obtain ⟨A, B, hcut, hsplit, hdisj, hfrontA, hfrontB⟩ :=
    actualTwoRadialCrosscutCells hd hw hdw hR
  change inside (sphere (0 : Plane) R) \ P =
    inside (A ∪ P) ∪ inside (B ∪ P) at hsplit
  change closure (inside (A ∪ P)) ∩ sphere (0 : Plane) R = A at hfrontA
  change closure (inside (B ∪ P)) ∩ sphere (0 : Plane) R = B at hfrontB
  have hP : IsArcBetween P (R • d) (R • w) :=
    actualJoinedRadialArmsArc hd hw hdw hR
  obtain ⟨hJSphere, hInsideSphere⟩ := actualRoundSupportJordanInside hR
  have hPi : P \ {R • d, R • w} ⊆ inside (sphere (0 : Plane) R) := by
    rw [hInsideSphere]
    exact actualTwoRadialArmsInterior hd hw hR
  have hJA : IsJordanCurve (A ∪ P) :=
    actualCrosscutSideJordan hcut.fst hP hcut.fst_subset hPi
  have hJB : IsJordanCurve (B ∪ P) :=
    actualCrosscutSideJordan hcut.snd hP hcut.snd_subset hPi
  have h0P : (0 : Plane) ∈ P :=
    Or.inl (right_mem_segment ℝ (R • d) 0)
  obtain ⟨q, _, hqLine, _, hqSegment⟩ :=
    actualBoundarySectorTargetBend oldVector hR hbSphere hbArc
  have hbClosure : γ cut ∈ closure (Plane.cone 0 (Plane.arcCCW d w) R) :=
    actualBentExitInConeClosure (by simpa using (hqLine 1).symm) hqSegment
  rcases actualConeFallsInOneCrosscutCell hd hw hdw hR hcut hsplit hdisj with hcone | hcone
  · have hbA : γ cut ∈ A :=
      actualSectorExitOnChosenBoundary hbSphere hbClosure hcone hfrontA
    have hcellBall : inside (A ∪ P) ⊆ ball (0 : Plane) R := by
      intro z hz
      have hz' : z ∈ inside (sphere (0 : Plane) R) \ P := by
        rw [hsplit]
        exact Or.inl hz
      simpa only [hInsideSphere] using hz'.1
    exact actualRelativeTwoArmExtensionInCell oldVector v hv hR hRv γ hγ hzero
      cut hc hbSphere hbArc hprefix (A ∪ P) hJA (Or.inr h0P)
      (Or.inl hbA) hcone hcellBall
      (hPfixed.trans subset_union_right)
  · have hbB : γ cut ∈ B :=
      actualSectorExitOnChosenBoundary hbSphere hbClosure hcone hfrontB
    have hcellBall : inside (B ∪ P) ⊆ ball (0 : Plane) R := by
      intro z hz
      have hz' : z ∈ inside (sphere (0 : Plane) R) \ P := by
        rw [hsplit]
        exact Or.inr hz
      simpa only [hInsideSphere] using hz'.1
    exact actualRelativeTwoArmExtensionInCell oldVector v hv hR hRv γ hγ hzero
      cut hc hbSphere hbArc hprefix (B ∪ P) hJB (Or.inr h0P)
      (Or.inl hbB) hcone hcellBall
      (hPfixed.trans subset_union_right)

private theorem actualSourcePrefixPullback {p b q r s : Plane}
    (γ : Path p b) (hγ : Function.Injective γ)
    (F : Plane ≃ₜ Plane) (B C : Set Plane)
    (hC : IsArcBetween C r s) (hB : IsArcBetween B (F p) q)
    (hFC : F '' range γ ⊆ C) (hBC : B ⊆ C)
    (hq : q ∈ F '' range γ) (hqp : q ≠ F p) (hqb : q ≠ F b) :
    ∃ c : Interval, 0 < c ∧ c < 1 ∧ F '' (γ '' Icc 0 c) = B := by
  obtain ⟨x, ⟨c, rfl⟩, hcq⟩ := hq
  have hc0 : c ≠ 0 := by
    intro he
    subst c
    exact hqp (hcq.symm.trans (congrArg F γ.source))
  have hc1 : c ≠ 1 := by
    intro he
    subst c
    exact hqb (hcq.symm.trans (congrArg F γ.target))
  have hc : 0 < c := lt_of_le_of_ne c.property.1 hc0.symm
  have hclt : c < 1 := lt_of_le_of_ne c.property.2 hc1
  let k : Interval → Interval := fun t => ⟨c.val * t.val, by
    constructor
    · exact mul_nonneg c.property.1 t.property.1
    · nlinarith [c.property.1, c.property.2, t.property.1, t.property.2]⟩
  let η : Path (F p) q := {
    toFun := F ∘ γ ∘ k
    continuous_toFun := F.continuous.comp (γ.continuous.comp (by fun_prop))
    source' := by simp [k, γ.source]
    target' := by simpa [k] using hcq }
  have hη : Function.Injective η := by
    intro u v he
    have hh := congrArg Subtype.val (hγ (F.injective he))
    change c.val * u.val = c.val * v.val at hh
    exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hc) hh)
  have hrange : range η = F '' (γ '' Icc 0 c) := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨γ (k t), ⟨k t, ?_, rfl⟩, rfl⟩
      exact ⟨(k t).property.1, by
        change c.val * t.val ≤ c.val
        nlinarith [c.property.1, t.property.2]⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      let t : Interval := ⟨u.val / c.val, by
        constructor
        · exact div_nonneg u.property.1 hc.le
        · exact (div_le_one hc).mpr hu.2⟩
      refine ⟨t, ?_⟩
      change F (γ (k t)) = F (γ u)
      congr 2
      apply Subtype.ext
      change c.val * (u.val / c.val) = u.val
      field_simp [ne_of_gt hc]
  have hA : IsArcBetween (range η) (F p) q := by
    refine ⟨η.extend, η.continuous_extend.continuousOn, ?_, ?_,
      η.extend_zero, η.extend_one⟩
    · intro u hu v hv he
      rw [Path.extend_apply _ hu, Path.extend_apply _ hv] at he
      exact congrArg Subtype.val (hη he)
    · exact η.image_extend_of_subset (Subset.refl (Icc (0 : ℝ) 1))
  have hAC : range η ⊆ C := by
    rw [hrange]
    exact (image_mono (image_subset_range _ _)).trans hFC
  refine ⟨c, hc, hclt, ?_⟩
  exact hrange.symm.trans (hA.eq_of_subset_arc hB hC hAC hBC)

private theorem actualInjectivePathIsArc
    {p b : Plane} (γ : Path p b) (hγ : Function.Injective γ) :
    IsArcBetween (range γ) p b := by
  refine ⟨γ.extend, γ.continuous_extend.continuousOn, ?_, ?_,
    γ.extend_zero, γ.extend_one⟩
  · intro u hu v hv he
    rw [Path.extend_apply _ hu, Path.extend_apply _ hv] at he
    exact congrArg Subtype.val (hγ he)
  · exact γ.image_extend_of_subset (Subset.refl (Icc (0 : ℝ) 1))

private theorem actualStraightGermAvoidsTwoFixedSegments
    (v : Fin 2 → Plane) (hv : ∀ j, v j ≠ 0)
    {R : ℝ} (hR : 0 < R) (hRv : ∀ j, R < ‖v j‖)
    {d w q : Plane} (hq : q ∈ Plane.cone 0 (Plane.arcCCW d w) R)
    (hPfixed :
      segment ℝ (0 : Plane) (R • Plane.dir (v 0)) ∪
        segment ℝ (0 : Plane) (R • Plane.dir (v 1)) ⊆
      segment ℝ (R • d) (0 : Plane) ∪
        segment ℝ (0 : Plane) (R • w)) :
    segment ℝ 0 q ∩
      (segment ℝ (0 : Plane) (v 0) ∪
        segment ℝ (0 : Plane) (v 1)) = {0} := by
  have hqBall : q ∈ ball (0 : Plane) R := Plane.cone_subset_ball hq
  have hzeroBall : (0 : Plane) ∈ ball (0 : Plane) R := by
    simpa only [mem_ball, dist_self] using hR
  apply Subset.antisymm
  · intro z hz
    by_cases hz0 : z = 0
    · exact hz0
    have hzCone : z ∈ Plane.cone 0 (Plane.arcCCW d w) R := by
      by_cases hzq : z = q
      · exact hzq ▸ hq
      · exact Schoenflies.openSegment_subset_cone_arcCCW hq
          (mem_openSegment_of_ne_left_right (Ne.symm hz0) (Ne.symm hzq) hz.1)
    have hzBall : z ∈ ball (0 : Plane) R :=
      (convex_ball 0 R).segment_subset hzeroBall hqBall hz.1
    have hzClosed : z ∈ closedBall (0 : Plane) R := ball_subset_closedBall hzBall
    have hzShort : z ∈ segment ℝ (0 : Plane) (R • Plane.dir (v 0)) ∪
        segment ℝ (0 : Plane) (R • Plane.dir (v 1)) := by
      rcases hz.2 with hz0' | hz1'
      · left
        rw [← actualShortFixedSegmentTruncation (hv 0) hR (hRv 0)]
        exact ⟨hz0', hzClosed⟩
      · right
        rw [← actualShortFixedSegmentTruncation (hv 1) hR (hRv 1)]
        exact ⟨hz1', hzClosed⟩
    have hzP : z ∈ segment ℝ (0 : Plane) (R • d) ∪
        segment ℝ (0 : Plane) (R • w) := by
      rcases hPfixed hzShort with hzD | hzW
      · exact Or.inl (by simpa only [segment_symm] using hzD)
      · exact Or.inr hzW
    exact False.elim (actualConeAvoidsRadialCrosscut hzCone hzP)
  · intro z hz
    have he : z = 0 := hz
    subst z
    exact ⟨left_mem_segment ℝ 0 q,
      Or.inl (left_mem_segment ℝ 0 (v 0))⟩

private theorem actualNewSourceArmAtDirectedRadius
    {K : Type} [Fintype K] (oldVector : K → Plane)
    (v : Fin 2 → Plane) (hv : ∀ j, v j ≠ 0)
    {R : ℝ} (hR : 0 < R) (hRv : ∀ j, R < ‖v j‖)
    (γ : Interval → Plane) (hγ : Topology.IsClosedEmbedding γ)
    (hzero : γ 0 = 0) (hRend : R < ‖γ 1‖)
    (cut : Interval) (hc : 0 < cut.val)
    (hbSphere : γ cut ∈ sphere (0 : Plane) R)
    {d w : Plane} (hd : Plane.IsDirection d) (hw : Plane.IsDirection w)
    (hdw : d ≠ w) (hbArc : γ cut ∈ Plane.arcCCW d w)
    (hprefix : ∀ t ∈ Ioo (0 : Interval) cut,
      γ t ∈ Plane.cone 0 (Plane.arcCCW d w) R)
    (hPfixed :
      segment ℝ (0 : Plane) (R • Plane.dir (v 0)) ∪
        segment ℝ (0 : Plane) (R • Plane.dir (v 1)) ⊆
      segment ℝ (R • d) (0 : Plane) ∪
        segment ℝ (0 : Plane) (R • w)) :
    ∃ (F : Plane ≃ₜ Plane) (vector : Plane),
      F 0 = 0 ∧
      (∀ x, x ∉ ball (0 : Plane) R → F x = x) ∧
      (∀ x ∈ segment ℝ (0 : Plane) (v 0) ∪
        segment ℝ (0 : Plane) (v 1), F x = x) ∧
      ∃ c : Interval, 0 < c.val ∧ c.val < 1 ∧ vector ≠ 0 ∧
        F '' (γ '' Icc 0 c) = segment ℝ 0 vector ∧
        segment ℝ 0 vector ∩
          (segment ℝ (0 : Plane) (v 0) ∪
            segment ℝ (0 : Plane) (v 1)) = {0} ∧
        ∀ k, segment ℝ 0 vector ∩
          {z | ∃ s : ℝ, 0 ≤ s ∧ z = s • oldVector k} = {0} := by
  obtain ⟨F, q, hFN, hF0, hfixBall, hfixArms, hqCone, hqLine, hqOld⟩ :=
    actualRelativeTwoArmExtensionForDirectedSector oldVector v hv hR hRv
      γ hγ hzero cut hc hbSphere hd hw hdw hbArc hprefix hPfixed
  have hq0 : q ≠ 0 := by simpa using hqLine 0
  let α : Path (0 : Plane) (γ 1) := {
    toFun := γ
    continuous_toFun := hγ.continuous
    source' := hzero
    target' := rfl }
  have hα : Function.Injective α := hγ.injective
  have hfullArc : IsArcBetween (F '' range α) 0 (F (γ 1)) := by
    have hh := (actualInjectivePathIsArc α hα).image_of_injOn
      (S := Set.univ) (subset_univ _) F.continuous.continuousOn F.injective.injOn
    simpa only [hF0] using hh
  have hsub : segment ℝ (0 : Plane) q ⊆ F '' range α := by
    apply (show segment ℝ (0 : Plane) q ⊆
      segment ℝ 0 q ∪ segment ℝ q (γ cut) from subset_union_left).trans
    rw [← hFN]
    exact image_mono (image_subset_range _ _)
  have hqBall : q ∈ ball (0 : Plane) R := Plane.cone_subset_ball hqCone
  have hγ1outside : γ 1 ∉ ball (0 : Plane) R := by
    intro h
    have hn : ‖γ 1‖ < R := by
      simpa only [mem_ball, dist_zero_right] using h
    linarith
  have hFend : F (γ 1) = γ 1 := hfixBall (γ 1) hγ1outside
  have hqEnd : q ≠ F (γ 1) := by
    rw [hFend]
    intro he
    exact hγ1outside (he ▸ hqBall)
  obtain ⟨c, hc0, hc1, hcim⟩ := actualSourcePrefixPullback α hα F
    (segment ℝ (0 : Plane) q) (F '' range α) hfullArc
    (by simpa only [hF0] using isArcBetween_segment hq0.symm)
    Subset.rfl hsub (hsub (right_mem_segment ℝ 0 q))
    (by simpa only [hF0] using hq0) hqEnd
  exact ⟨F, q, hF0, hfixBall, hfixArms, c, hc0, hc1, hq0,
    hcim, actualStraightGermAvoidsTwoFixedSegments v hv hR hRv hqCone hPfixed,
    fun k => actualGermSegmentAvoidingNoncollinearRay (hqOld k)⟩

private theorem actualChooseTwoArmSupportRadius
    (v : Fin 2 → Plane) (hv : ∀ j, v j ≠ 0)
    (γ : Interval → Plane) (hγ : Topology.IsClosedEmbedding γ)
    (hzero : γ 0 = 0)
    (V : Set Plane) (hV : IsOpen V) (h0V : (0 : Plane) ∈ V) :
    ∃ R : ℝ, 0 < R ∧ closedBall (0 : Plane) R ⊆ V ∧
      R < ‖v 0‖ ∧ R < ‖v 1‖ ∧ R < ‖γ 1‖ := by
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV 0 h0V
  have hγ1 : γ 1 ≠ 0 := by
    intro he
    have h10 : (1 : Interval) = 0 := hγ.injective (he.trans hzero.symm)
    have hh := congrArg Subtype.val h10
    norm_num at hh
  have hM : 0 < min ε (min ‖v 0‖ (min ‖v 1‖ ‖γ 1‖)) := by
    simp only [lt_min_iff]
    exact ⟨hε, norm_pos_iff.mpr (hv 0),
      norm_pos_iff.mpr (hv 1), norm_pos_iff.mpr hγ1⟩
  let R := min ε (min ‖v 0‖ (min ‖v 1‖ ‖γ 1‖)) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hRε : R < ε := by
    dsimp [R]
    have hh := min_le_left ε (min ‖v 0‖ (min ‖v 1‖ ‖γ 1‖))
    linarith
  have hRv0 : R < ‖v 0‖ := by
    dsimp [R]
    have hh := (min_le_right ε (min ‖v 0‖ (min ‖v 1‖ ‖γ 1‖))).trans
      (min_le_left ‖v 0‖ (min ‖v 1‖ ‖γ 1‖))
    linarith
  have hRv1 : R < ‖v 1‖ := by
    dsimp [R]
    have hh := (min_le_right ε (min ‖v 0‖ (min ‖v 1‖ ‖γ 1‖))).trans
      ((min_le_right ‖v 0‖ (min ‖v 1‖ ‖γ 1‖)).trans
        (min_le_left ‖v 1‖ ‖γ 1‖))
    linarith
  have hRγ : R < ‖γ 1‖ := by
    dsimp [R]
    have hh := (min_le_right ε (min ‖v 0‖ (min ‖v 1‖ ‖γ 1‖))).trans
      ((min_le_right ‖v 0‖ (min ‖v 1‖ ‖γ 1‖)).trans
        (min_le_right ‖v 1‖ ‖γ 1‖))
    linarith
  exact ⟨R, hR, (closedBall_subset_ball hRε).trans hεV,
    hRv0, hRv1, hRγ⟩


#print axioms actualTwoRayArcCover
#print axioms actualTwoRayArcsDisjoint
#print axioms actualSourcePrefixSelectsOneOfTwoRaySectors
#print axioms actualFirstExitRetainsAngularSector
#print axioms actualShortClosedBallRayPointInFixedSegment
#print axioms actualShortBallSourceAvoidsFixedRays
#print axioms actualTwoFixedDirectionsDistinct
#print axioms actualOriginalSourceFirstExitShortBall
#print axioms actualOriginalPrefixInOneActualSector
#print axioms actualJoinedRadialArmsArc
#print axioms actualRoundSupportJordanInside
#print axioms actualTwoRadialArmsInterior
#print axioms actualTwoRadialCrosscutCells
#print axioms actualCrosscutSideJordan
#print axioms actualConeAvoidsRadialCrosscut
#print axioms actualConeFallsInOneCrosscutCell
#print axioms actualOpenSetContainsNonhorizontalPoint
#print axioms actualOpenSetAvoidsFiniteLines
#print axioms actualBoundarySectorTargetBend
#print axioms actualSimpleBentTargetArc
#print axioms actualBentTargetInteriorInCone
#print axioms actual_new_source_arm_relative_to_two_fixed_segments
end


open Set Schoenflies Metric Topology
namespace CurveComplex.HyperellipticModel

/-- The fixed common initial arm survives pointed replacement as an actual set. -/
private theorem actualPointedReplacementPreservesCommonArm
    {A B K : Set Plane} {a b p : Plane}
    (hA : IsArcBetween A a b) (hB : IsArcBetween B a b)
    (hK : IsArcBetween K a p) (hKA : K ⊆ A) (hKB : K ⊆ B)
    (hpA : p ∈ A \ {a,b}) (hpB : p ∈ B \ {a,b})
    (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
    (hAi : A \ {a,b} ⊆ Plane.openSquare 0 1)
    (hBi : B \ {a,b} ⊆ Plane.openSquare 0 1) :
    ∃ F : Plane ≃ₜ Plane, F p = p ∧ F '' A = B ∧ F '' K = K ∧
      ∀ x, x ∉ Plane.openSquare 0 1 → F x = x := by
  obtain ⟨F, hp, hAB, hfix⟩ :=
    CurveComplex.SeedProbeHeaders.pointed_relative_crosscut_replacement
      hA hB hpA hpB ha hb hAi hBi
  have haOut : a ∉ Plane.openSquare 0 1 := by
    rw [modelCurve_eq_frontier, (Plane.isClosed_closedSquare 0 1).frontier_eq,
      interior_closedSquare_zero_one] at ha
    exact ha.2
  have hFa : F a = a := hfix a haOut
  have hFK : IsArcBetween (F '' K) a p := by
    have hh := hK.image_of_injOn (S := Set.univ) (subset_univ K)
      F.continuous.continuousOn F.injective.injOn
    simpa only [hFa, hp] using hh
  have hFKB : F '' K ⊆ B := by
    rw [← hAB]
    exact image_mono hKA
  exact ⟨F, hp, hAB, hFK.eq_of_subset_arc hK hB hFKB hKB, hfix⟩

/-- Local preservation of the anchor arm and fixed exterior imply preservation
of the entire literal reference ray or line; no new anchor points are introduced. -/
private theorem actualReferenceImageOfPreservedLocalArm
    (F : Plane ≃ₜ Plane) {R K U : Set Plane}
    (hKU : K ⊆ R) (hlocal : R ∩ U ⊆ K)
    (hK : F '' K = K) (hfix : ∀ x, x ∉ U → F x = x) :
    F '' R = R := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    by_cases hxU : x ∈ U
    · apply hKU
      rw [← hK]
      exact mem_image_of_mem F (hlocal ⟨hx, hxU⟩)
    · simpa only [hfix x hxU] using hx
  · intro y hy
    by_cases hyU : y ∈ U
    · have hyK := hlocal ⟨hy, hyU⟩
      rw [← hK] at hyK
      obtain ⟨x, hx, hxy⟩ := hyK
      exact ⟨x, hKU hx, hxy⟩
    · exact ⟨y, hy, hfix y hyU⟩

/-- Recover the actual moved source arm from the joined crosscut image, retaining
its shared marked endpoint and excluding every other common-arm point. -/
private theorem actualOtherArmImageOfJoinedReplacement
    (F : Plane ≃ₜ Plane) {K L N : Set Plane} {p : Plane}
    (hKL : K ∩ L = {p}) (hKN : K ∩ N = {p})
    (hp : F p = p) (hK : F '' K = K)
    (hjoined : F '' (K ∪ L) = K ∪ N) : F '' L = N := by
  have hpL : p ∈ L := by
    have hh : p ∈ K ∩ L := by rw [hKL]; simp
    exact hh.2
  have hpN : p ∈ N := by
    have hh : p ∈ K ∩ N := by rw [hKN]; simp
    exact hh.2
  have himageK : ∀ x, F x ∈ K ↔ x ∈ K := by
    intro x
    constructor
    · intro hx
      rw [← hK] at hx
      exact F.injective.mem_set_image.mp hx
    · intro hx
      rw [← hK]
      exact mem_image_of_mem F hx
  apply Subset.antisymm
  · rintro y ⟨x, hxL, rfl⟩
    have hmem : F x ∈ K ∪ N := by
      rw [← hjoined]
      exact mem_image_of_mem F (Or.inr hxL)
    rcases hmem with hxK | hxN
    · have hx : x = p := by
        have hh : x ∈ K ∩ L := ⟨(himageK x).mp hxK, hxL⟩
        rw [hKL] at hh
        exact hh
      simpa only [hx, hp] using hpN
    · exact hxN
  · intro y hyN
    by_cases hyK : y ∈ K
    · have hy : y = p := by
        have hh : y ∈ K ∩ N := ⟨hyK, hyN⟩
        rw [hKN] at hh
        exact hh
      exact ⟨p, hpL, hp.trans hy.symm⟩
    · have hh : y ∈ F '' (K ∪ L) := by rw [hjoined]; exact Or.inr hyN
      obtain ⟨x, hx, hxy⟩ := hh
      rcases hx with hxK | hxL
      · exfalso
        apply hyK
        rw [← hxy]
        exact (himageK x).mpr hxK
      · exact ⟨x, hxL, hxy⟩

/-- A genuine direction in the upper half-plane avoiding all finitely many
old ray directions, including indexed repetitions. -/
private theorem actualUpperDirectionAvoidingFiniteRays
    {J : Type} [Fintype J] (v : J → Plane) :
    ∃ w : Plane, w 1 = 1 ∧
      ∀ j : J, ∀ r : ℝ, w ≠ r • v j := by
  classical
  obtain ⟨u, hu⟩ := (Set.finite_range (fun j => v j 0 / v j 1)).bddAbove
  refine ⟨Plane.mk (u + 1) 1, rfl, ?_⟩
  intro j r heq
  have hx : u + 1 = r * v j 0 := by
    have hh := congrArg (fun z : Plane => z 0) heq
    simpa using hh
  have hy : (1 : ℝ) = r * v j 1 := by
    have hh := congrArg (fun z : Plane => z 1) heq
    simpa using hh
  have hv : v j 1 ≠ 0 := by intro hz; simp [hz] at hy
  have hm : (u + 1) * v j 1 = v j 0 := by
    calc
      (u + 1) * v j 1 = (r * v j 0) * v j 1 := by rw [hx]
      _ = v j 0 * (r * v j 1) := by ring
      _ = v j 0 := by rw [← hy, mul_one]
  have he : u + 1 = v j 0 / v j 1 := (eq_div_iff hv).mpr hm
  have hb := hu (mem_range_self j)
  linarith

/-- Source-only crosscut surgery preserving the entire literal reference set.
The common arm is part of both actual crosscuts, not an avoidance certificate. -/
private theorem actualAnchorRelativeJoinedSourceCrosscutReplacement
    {K L N R : Set Plane} {a b p : Plane}
    (hA : IsArcBetween (K ∪ L) a b)
    (hB : IsArcBetween (K ∪ N) a b)
    (hK : IsArcBetween K a p)
    (hKL : K ∩ L = {p}) (hKN : K ∩ N = {p})
    (hpA : p ∈ (K ∪ L) \ {a,b})
    (hpB : p ∈ (K ∪ N) \ {a,b})
    (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
    (hAi : (K ∪ L) \ {a,b} ⊆ Plane.openSquare 0 1)
    (hBi : (K ∪ N) \ {a,b} ⊆ Plane.openSquare 0 1)
    (hKR : K ⊆ R) (hlocal : R ∩ Plane.openSquare 0 1 ⊆ K) :
    ∃ F : Plane ≃ₜ Plane, F p = p ∧ F '' L = N ∧ F '' R = R ∧
      ∀ x, x ∉ Plane.openSquare 0 1 → F x = x := by
  obtain ⟨F, hp, hjoined, hFK, hfix⟩ :=
    actualPointedReplacementPreservesCommonArm hA hB hK
      subset_union_left subset_union_left hpA hpB ha hb hAi hBi
  exact ⟨F, hp,
    actualOtherArmImageOfJoinedReplacement F hKL hKN hp hFK hjoined,
    actualReferenceImageOfPreservedLocalArm F hKR hlocal hFK hfix, hfix⟩

/-- The chosen genuine germ segment meets each old ray only at the marked center. -/
private theorem actualUpperGermSegmentAvoidingFiniteRays
    {J : Type} [Fintype J] (v : J → Plane) :
    ∃ w : Plane, w 1 = 1 ∧
      (∀ j, segment ℝ (0 : Plane) w ∩
        {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • v j} = {0}) ∧
      segment ℝ (0 : Plane) w ∩ {z : Plane | z 1 = 0} = {0} := by
  obtain ⟨w, hw, hav⟩ := actualUpperDirectionAvoidingFiniteRays v
  have hparam : ∀ z ∈ segment ℝ (0 : Plane) w,
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ t • w = z := by
    intro z hz
    rw [segment_eq_image] at hz
    obtain ⟨t, ht, htz⟩ := hz
    exact ⟨t, ht.1, ht.2, by simpa using htz⟩
  refine ⟨w, hw, ?_, ?_⟩
  · intro j
    apply Subset.antisymm
    · intro z hz
      obtain ⟨t, ht0, ht1, htz⟩ := hparam z hz.1
      obtain ⟨r, hr, hzr⟩ := hz.2
      by_cases ht : t = 0
      · simpa [ht] using htz.symm
      · exfalso
        apply hav j (t⁻¹ * r)
        have he := congrArg (fun x : Plane => t⁻¹ • x) (htz.trans hzr)
        simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using he
    · intro z hz
      have hz0 : z = 0 := hz
      subst z
      exact ⟨left_mem_segment ℝ 0 w, ⟨0, le_refl 0, by simp⟩⟩
  · apply Subset.antisymm
    · intro z hz
      obtain ⟨t, ht0, ht1, htz⟩ := hparam z hz.1
      have he := congrArg (fun x : Plane => x 1) htz
      have hzaxis : z 1 = 0 := hz.2
      have ht : t = 0 := (by simpa [hw] using he : t = z 1).trans hzaxis
      simpa [ht] using htz.symm
    · intro z hz
      have hz0 : z = 0 := hz
      subst z
      exact ⟨left_mem_segment ℝ 0 w, by simp⟩

/-- Actual path concatenation produces the crosscut needed by the relative
replacement. This is the canonical seed's existing join kernel. -/
private theorem actualJoinedSourceArmsArePointedArc
    {a b p : Plane} (γ : Path a p) (δ : Path p b)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hmeet : range γ ∩ range δ = {p}) :
    IsArcBetween (range γ ∪ range δ) a b ∧
      p ∈ (range γ ∪ range δ) \ {a,b} := by
  let η := γ.trans δ
  have hη : Function.Injective η :=
    LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
      γ δ hγ hδ hmeet
  constructor
  · refine ⟨η.extend, η.continuous_extend.continuousOn, ?_, ?_,
      η.extend_zero, η.extend_one⟩
    · intro s hs t ht he
      rw [Path.extend_apply _ hs, Path.extend_apply _ ht] at he
      exact congrArg Subtype.val (hη he)
    · exact (η.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))).trans
        (Path.trans_range γ δ)
  · refine ⟨Or.inl ⟨1, γ.target⟩, ?_⟩
    intro hp
    have hh : p = a ∨ p = b := by simpa using hp
    rcases hh with ha | hb
    · have he : (1 : CurveComplex.Interval) = 0 :=
        hγ (γ.target.trans (ha.trans γ.source.symm))
      exact one_ne_zero he
    · have he : (0 : CurveComplex.Interval) = 1 :=
        hδ (δ.source.trans (hb.trans δ.target.symm))
      exact zero_ne_one he

/-- The first-exit source arm is an actual prefix of the original source,
with genuine boundary endpoint and no contact with the literal reference. -/
private theorem actualReferenceAvoidingFirstExitSourceArm
    {q : Plane} (α : Path (0 : Plane) q)
    (hα : Function.Injective α) {R : Set Plane}
    (havoid : ∀ t : CurveComplex.Interval, 0 < t → α t ∉ R)
    (hq : q ∉ Plane.closedSquare 0 1) :
    ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
      ∃ γ : Path (0 : Plane) (α c), Function.Injective γ ∧
        α c ∈ modelCurve ∧
        (∀ t : CurveComplex.Interval, t < 1 → γ t ∈ Plane.openSquare 0 1) ∧
        (∀ t : CurveComplex.Interval, 0 < t → γ t ∉ R) ∧
        range γ = α '' Icc 0 c := by
  have hz : (0 : Plane) ∈ Plane.openSquare 0 1 := by
    rw [mem_openSquare_zero_one]
    simp [Plane.supNorm]
  have hqOpen : q ∉ Plane.openSquare 0 1 := by
    intro hh
    apply hq
    exact mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hh).le
  obtain ⟨c, hc, hfront, hbefore⟩ :=
    CurveComplex.path_first_exit_frontier α _ (Plane.isOpen_openSquare 0 1) hz hqOpen
  have hboundary : α c ∈ modelCurve := by
    rw [modelCurve_eq_frontier]
    exact Plane.frontier_openSquare_subset 0 1 hfront
  have hc1 : c < 1 := by
    apply lt_of_le_of_ne c.property.2
    intro he
    apply hq
    have hh := Plane.frontier_openSquare_subset 0 1 hfront
    have heI : c = (1 : CurveComplex.Interval) := Subtype.ext he
    rw [heI, α.target] at hh
    exact (Plane.isClosed_closedSquare 0 1).frontier_subset hh
  let k : CurveComplex.Interval → CurveComplex.Interval := fun t =>
    ⟨(c : ℝ) * (t : ℝ), by
      constructor
      · exact mul_nonneg c.property.1 t.property.1
      · nlinarith [c.property.1, c.property.2, t.property.1, t.property.2]⟩
  let γ : Path (0 : Plane) (α c) := {
    toFun := α ∘ k
    continuous_toFun := α.continuous.comp (by fun_prop)
    source' := by simp [k, α.source]
    target' := by simp [k] }
  refine ⟨c, hc, hc1, γ, ?_, hboundary, ?_, ?_, ?_⟩
  · intro s t he
    have hh := congrArg Subtype.val (hα he)
    change (c : ℝ) * (s : ℝ) = (c : ℝ) * (t : ℝ) at hh
    exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hc) hh)
  · intro t ht
    apply hbefore
    change (c : ℝ) * (t : ℝ) < c
    exact mul_lt_of_lt_one_right hc ht
  · intro t ht
    apply havoid
    change 0 < (c : ℝ) * (t : ℝ)
    exact mul_pos hc ht
  · apply Subset.antisymm
    · rintro z ⟨t, rfl⟩
      refine ⟨k t, ⟨?_, ?_⟩, rfl⟩
      · exact mul_nonneg c.property.1 t.property.1
      · change (c : ℝ) * (t : ℝ) ≤ c
        exact mul_le_of_le_one_right c.property.1 t.property.2
    · rintro z ⟨t, ht, rfl⟩
      let u : CurveComplex.Interval := ⟨(t : ℝ) / (c : ℝ),
        (div_nonneg ht.1 c.property.1), (div_le_one (show 0 < (c : ℝ) from hc)).mpr ht.2⟩
      refine ⟨u, ?_⟩
      change α (k u) = α t
      congr 1
      apply Subtype.ext
      change (c : ℝ) * ((t : ℝ) / (c : ℝ)) = t
      field_simp [ne_of_gt hc]

/-- Choose the new short germ in the actual exit's half-plane and avoid both
all old directions and the exit direction. Horizontal exits use the upper side. -/
private theorem actualTargetGermDirectionCompatibleWithExit
    {J : Type} [Fintype J] (v : J → Plane) (b : Plane) :
    ∃ w : Plane, (0 ≤ b 1 → w 1 = 1) ∧ (b 1 < 0 → w 1 = -1) ∧
      (∀ r : ℝ, w ≠ r • b) ∧ (∀ (j : J) (r : ℝ), w ≠ r • v j) := by
  let allv : Option J → Plane := fun j => Option.casesOn j b v
  obtain ⟨u, hu, hav⟩ := actualUpperDirectionAvoidingFiniteRays allv
  by_cases hb : b 1 < 0
  · refine ⟨-u, ?_, ?_, ?_, ?_⟩
    · intro hh
      exact False.elim ((not_le_of_gt hb) hh)
    · intro hh
      simp [hu]
    · intro r he
      apply hav none (-r)
      have hh := congrArg Neg.neg he
      simpa [allv] using hh
    · intro j r he
      apply hav (some j) (-r)
      have hh := congrArg Neg.neg he
      simpa [allv] using hh
  · refine ⟨u, (fun _ => hu), ?_, ?_, ?_⟩
    · intro hh
      exact False.elim (hb hh)
    · exact hav none
    · exact fun j => hav (some j)

/-- A two-segment actual target arm, retaining the original boundary exit.
Its first segment supplies the new straight germ. -/
private theorem actualSimpleTwoSegmentSourceTarget
    {q b : Plane} (hb : b ∈ modelCurve)
    (hq : q ∈ Plane.openSquare 0 1) (hq0 : q ≠ 0)
    (hind : ∀ r s : ℝ, r • q = s • b → r = 0 ∧ s = 0) :
    IsArcBetween (segment ℝ (0 : Plane) q ∪ segment ℝ q b) 0 b ∧
      (segment ℝ (0 : Plane) q ∪ segment ℝ q b) \ {0,b} ⊆
        Plane.openSquare 0 1 := by
  have hb0 : b ≠ 0 := by
    intro he
    have hh := (hind 0 1 (by simp [he])).2
    norm_num at hh
  have hqb : q ≠ b := by
    intro he
    have hh := (hind 1 1 (by simp [he])).1
    norm_num at hh
  have hinter : segment ℝ (0 : Plane) q ∩ segment ℝ q b = {q} := by
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      obtain ⟨r, s, hr, hs, hrs, hx⟩ := hx
      obtain ⟨u, v, hu, hv, huv, hx'⟩ := hx'
      have he : (s - u) • q = v • b := by
        calc
          (s - u) • q = (r • (0 : Plane) + s • q) - u • q := by module
          _ = v • b := by rw [hx, ← hx']; module
      have hv0 := (hind _ _ he).2
      have hu1 : u = 1 := by linarith
      have hxe : x = q := by rw [← hx', hv0, hu1]; simp
      exact hxe
    · intro hx
      have he : x = q := hx
      subst x
      exact ⟨right_mem_segment ℝ 0 q, left_mem_segment ℝ q b⟩
  let γ := Path.segment (0 : Plane) q
  let δ := Path.segment q b
  have ha := actualJoinedSourceArmsArePointedArc γ δ
    (Path.segment_injective_of_ne hq0.symm)
    (Path.segment_injective_of_ne hqb)
    (by simpa [γ, δ, Path.range_segment] using hinter)
  refine ⟨by simpa [γ, δ, Path.range_segment] using ha.1, ?_⟩
  have hqi : q ∈ interior (Plane.closedSquare 0 1) := by
    simpa only [interior_closedSquare_zero_one] using hq
  have hbc : b ∈ Plane.closedSquare 0 1 :=
    mem_closedSquare_zero_one.mpr (show Plane.supNorm b = 1 from hb).le
  have h0c : (0 : Plane) ∈ Plane.closedSquare 0 1 := by
    rw [mem_closedSquare_zero_one]
    simp [Plane.supNorm]
  intro x hx
  have hx0 : x ≠ 0 := by intro he; exact hx.2 (by simp [he])
  have hxb : x ≠ b := by intro he; exact hx.2 (by simp [he])
  by_cases hxq : x = q
  · simpa only [hxq] using hq
  · rw [← interior_closedSquare_zero_one]
    rcases hx.1 with hx | hx
    · exact (Plane.convex_closedSquare 0 1).openSegment_self_interior_subset_interior
        h0c hqi (mem_openSegment_of_ne_left_right hx0.symm (Ne.symm hxq) hx)
    · exact (Plane.convex_closedSquare 0 1).openSegment_interior_self_subset_interior
        hqi hbc (mem_openSegment_of_ne_left_right (Ne.symm hxq) hxb.symm hx)

/-- Both target segments genuinely avoid the fixed ray or axis except at zero. -/
private theorem actualTwoSegmentTargetAvoidsReference
    (anchorLoop : Bool) {q b : Plane}
    (hb : b ∉ {z : Plane | z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ z 0)})
    (hupper : 0 ≤ b 1 → 0 < q 1) (hlower : b 1 < 0 → q 1 < 0) :
    (segment ℝ (0 : Plane) q ∪ segment ℝ q b) ∩
      {z : Plane | z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ z 0)} = {0} := by
  have hq1 : q 1 ≠ 0 := by
    by_cases hbb : b 1 < 0
    · exact ne_of_lt (hlower hbb)
    · exact ne_of_gt (hupper (le_of_not_gt hbb))
  apply Subset.antisymm
  · intro z hz
    have hz1 : z 1 = 0 := hz.2.1
    rcases hz.1 with hzfirst | hzsecond
    · rw [segment_eq_image] at hzfirst
      obtain ⟨t, ht, htz⟩ := hzfirst
      have he := congrArg (fun x : Plane => x 1) htz
      have htq : t * q 1 = 0 := by simpa [hz1] using he
      have ht0 : t = 0 := (mul_eq_zero.mp htq).resolve_right hq1
      have hz0 : z = 0 := by simpa [ht0] using htz.symm
      exact hz0
    · obtain ⟨r, t, hr, ht, hrt, hzt⟩ := hzsecond
      have he := congrArg (fun x : Plane => x 1) hzt
      have he0 : r * q 1 + t * b 1 = 0 := by simpa [hz1] using he
      have hr0 : r = 0 := by
        by_cases hbb : b 1 < 0
        · have hqq := hlower hbb
          have htb : t * b 1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hbb.le
          nlinarith
        · have hbb0 := le_of_not_gt hbb
          have hqq := hupper hbb0
          have htb : 0 ≤ t * b 1 := mul_nonneg ht hbb0
          nlinarith
      have ht1 : t = 1 := by linarith
      have hzB : z = b := by simpa [hr0, ht1] using hzt.symm
      exfalso
      apply hb
      simpa only [hzB] using hz.2
  · intro z hz
    have hz0 : z = 0 := hz
    subst z
    exact ⟨Or.inl (left_mem_segment ℝ 0 q), by simp⟩

/- Reuse the canonical seed's unavailable proof-local prefix pullback kernel. -/
private theorem actualSourcePrefixPullback {p b q r s : Plane} (γ : Path p b) (hγ : Function.Injective γ)
    (F : Plane ≃ₜ Plane) (B C : Set Plane)
    (hC : IsArcBetween C r s) (hB : IsArcBetween B (F p) q)
    (hFC : F '' range γ ⊆ C) (hBC : B ⊆ C)
    (hq : q ∈ F '' range γ) (hqp : q ≠ F p) (hqb : q ≠ F b) :
    ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧ F '' (γ '' Icc 0 c) = B := by
  obtain ⟨x,⟨c,rfl⟩,hcq⟩ := hq
  have hc0 : c ≠ 0 := by intro he; subst c; exact hqp (hcq.symm.trans (congrArg F γ.source))
  have hc1 : c ≠ 1 := by intro he; subst c; exact hqb (hcq.symm.trans (congrArg F γ.target))
  have hc : 0 < c := lt_of_le_of_ne c.property.1 hc0.symm
  have hclt : c < 1 := lt_of_le_of_ne c.property.2 hc1
  let k : CurveComplex.Interval → CurveComplex.Interval := fun t => ⟨(c:ℝ)*(t:ℝ), by
    constructor
    · exact mul_nonneg c.property.1 t.property.1
    · nlinarith [c.property.1,c.property.2,t.property.1,t.property.2]⟩
  let η : Path (F p) q := {
    toFun := F ∘ γ ∘ k
    continuous_toFun := F.continuous.comp (γ.continuous.comp (by fun_prop))
    source' := by simp [k,γ.source]
    target' := by simpa [k] using hcq }
  have hη : Function.Injective η := by
    intro u v he
    have hh := congrArg Subtype.val (hγ (F.injective he))
    change (c:ℝ)*(u:ℝ) = (c:ℝ)*(v:ℝ) at hh
    exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hc) hh)
  have hrange : range η = F '' (γ '' Icc 0 c) := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      refine ⟨γ (k t),⟨k t,?_,rfl⟩,rfl⟩
      exact ⟨(k t).property.1,by change (c:ℝ)*(t:ℝ) ≤ c; nlinarith [c.property.1,t.property.2]⟩
    · rintro ⟨_,⟨u,hu,rfl⟩,rfl⟩
      let t : CurveComplex.Interval := ⟨(u:ℝ)/(c:ℝ),by
        constructor
        · exact div_nonneg u.property.1 hc.le
        · exact (div_le_one hc).mpr hu.2⟩
      refine ⟨t,?_⟩
      change F (γ (k t)) = F (γ u)
      congr 2
      apply Subtype.ext
      change (c:ℝ)*((u:ℝ)/(c:ℝ)) = u
      field_simp [ne_of_gt hc]
  have hA : IsArcBetween (range η) (F p) q := by
    refine ⟨η.extend,η.continuous_extend.continuousOn,?_,?_,η.extend_zero,η.extend_one⟩
    · intro u hu v hv he
      rw [Path.extend_apply _ hu,Path.extend_apply _ hv] at he
      exact congrArg Subtype.val (hη he)
    · exact η.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))
  have hAC : range η ⊆ C := by
    rw [hrange]
    exact (image_mono (image_subset_range _ _)).trans hFC
  refine ⟨c,hc,hclt,?_⟩
  exact hrange.symm.trans (hA.eq_of_subset_arc hB hC hAC hBC)

/-- Scale the exit-compatible actual direction into the square, retaining all
noncollinearity and half-plane facts required by the target polygon. -/
private theorem actualScaledTargetGermDirection
    {J : Type} [Fintype J] (v : J → Plane) {b : Plane}
    (hb0 : b ≠ 0) :
    ∃ q : Plane, q ∈ Plane.openSquare 0 1 ∧ q ≠ 0 ∧
      (0 ≤ b 1 → 0 < q 1) ∧ (b 1 < 0 → q 1 < 0) ∧
      (∀ r s : ℝ, r • q = s • b → r = 0 ∧ s = 0) ∧
      (∀ (j : J) (r : ℝ), q ≠ r • v j) := by
  obtain ⟨w, hwup, hwlo, hwb, hwv⟩ :=
    actualTargetGermDirectionCompatibleWithExit v b
  let ε : ℝ := 1 / (2 * (Plane.supNorm w + 1))
  have hD : 0 < 2 * (Plane.supNorm w + 1) := by
    have hh := Plane.supNorm_nonneg w
    positivity
  have hε : 0 < ε := one_div_pos.mpr hD
  let q : Plane := ε • w
  have hqi : q ∈ Plane.openSquare 0 1 := by
    rw [mem_openSquare_zero_one]
    change Plane.supNorm (ε • w) < 1
    rw [Plane.supNorm_smul, abs_of_pos hε]
    dsimp [ε]
    rw [one_div_mul_eq_div, div_lt_iff₀ hD]
    have hh := Plane.supNorm_nonneg w
    linarith
  have hqup : 0 ≤ b 1 → 0 < q 1 := by
    intro hh
    change 0 < ε * w 1
    rw [hwup hh]
    simpa only [mul_one] using hε
  have hqlo : b 1 < 0 → q 1 < 0 := by
    intro hh
    change ε * w 1 < 0
    rw [hwlo hh]
    linarith
  have hq0 : q ≠ 0 := by
    intro he
    by_cases hbb : b 1 < 0
    · have hh := hqlo hbb
      simp [he] at hh
    · have hh := hqup (le_of_not_gt hbb)
      simp [he] at hh
  refine ⟨q, hqi, hq0, hqup, hqlo, ?_, ?_⟩
  · intro r t he
    by_cases hr : r = 0
    · refine ⟨hr, ?_⟩
      have ht : t • b = 0 := by simpa [hr] using he.symm
      exact (smul_eq_zero.mp ht).resolve_right hb0
    · exfalso
      apply hwb ((r * ε)⁻¹ * t)
      have hh := congrArg (fun x : Plane => (r * ε)⁻¹ • x) he
      simp only [q, smul_smul] at hh
      simpa only [inv_mul_cancel₀ (mul_ne_zero hr (ne_of_gt hε)), one_smul] using hh
  · intro j r he
    apply hwv j (ε⁻¹ * r)
    have hh := congrArg (fun x : Plane => ε⁻¹ • x) he
    simpa [q, smul_smul, inv_mul_cancel₀ (ne_of_gt hε)] using hh

private theorem actualArcBetweenHasInjectivePath
    {A : Set Plane} {p q : Plane} (hA : IsArcBetween A p q) :
    ∃ γ : Path p q, Function.Injective γ ∧ range γ = A := by
  obtain ⟨f, hfc, hfi, hfA, hf0, hf1⟩ := hA
  let γ : Path p q := {
    toFun := fun t => f t
    continuous_toFun := hfc.comp_continuous continuous_subtype_val (fun t => t.property)
    source' := hf0
    target' := hf1 }
  refine ⟨γ, ?_, ?_⟩
  · intro s t he
    exact Subtype.ext (hfi s.property t.property he)
  · rw [← hfA]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩

private theorem actualFixedArmIntersectsReferenceAvoidingSource
    {K N R : Set Plane} (hKR : K ⊆ R) (h0K : (0 : Plane) ∈ K)
    (hNR : N ∩ R = {0}) : K ∩ N = {0} := by
  apply Subset.antisymm
  · intro z hz
    rw [← hNR]
    exact ⟨hz.2, hKR hz.1⟩
  · intro z hz
    have hz0 : z = 0 := hz
    subst z
    have h0N : (0 : Plane) ∈ N := by
      have hh : (0 : Plane) ∈ N ∩ R := by rw [hNR]; simp
      exact hh.1
    exact ⟨h0K, h0N⟩

private theorem actualPositiveReferenceSquareArm :
    let a : Plane := Plane.mk 1 0
    let R : Set Plane := {z | z 1 = 0 ∧ 0 ≤ z 0}
    let K := segment ℝ (0 : Plane) a
    a ∈ modelCurve ∧ IsArcBetween K a 0 ∧ K ⊆ R ∧
      R ∩ Plane.openSquare 0 1 ⊆ K ∧
      K \ {a} ⊆ Plane.openSquare 0 1 := by
  let a : Plane := Plane.mk 1 0
  let R : Set Plane := {z | z 1 = 0 ∧ 0 ≤ z 0}
  let K := segment ℝ (0 : Plane) a
  have ha : a ∈ modelCurve := by simp [a, Plane.supNorm, modelCurve]
  have ha0 : a ≠ 0 := by
    intro he
    have hh := congrArg (fun x : Plane => x 0) he
    simp [a] at hh
  refine ⟨ha, ?_, ?_, ?_, ?_⟩
  · change IsArcBetween K a 0
    rw [show K = segment ℝ a 0 from segment_symm ℝ 0 a]
    exact isArcBetween_segment ha0
  · intro z hz
    rw [segment_eq_image] at hz
    obtain ⟨t, ht, htz⟩ := hz
    have hzEq : z = t • a := by simpa using htz.symm
    change z 1 = 0 ∧ 0 ≤ z 0
    simp [hzEq, a, ht.1]
  · intro z hz
    have hz1 : z 1 = 0 := hz.1.1
    have hz0 : 0 ≤ z 0 := hz.1.2
    have hzLt : z 0 < 1 := lt_of_le_of_lt
      ((le_abs_self (z 0)).trans (Plane.abs_zero_le_supNorm z))
      (mem_openSquare_zero_one.mp hz.2)
    rw [segment_eq_image]
    refine ⟨z 0, ⟨hz0, hzLt.le⟩, ?_⟩
    simp only [smul_zero, zero_add]
    ext i
    fin_cases i
    · simp [a]
    · simp [a, hz1]
  · intro z hz
    have hzNot : z ≠ a := by simpa using hz.2
    have hzK : z ∈ segment ℝ (0 : Plane) a := hz.1
    rw [segment_eq_image] at hzK
    obtain ⟨t, ht, htz⟩ := hzK
    have hzEq : z = t • a := by simpa using htz.symm
    have htNe : t ≠ 1 := by
      intro he
      apply hzNot
      simpa [he] using hzEq
    have htLt : t < 1 := lt_of_le_of_ne ht.2 htNe
    rw [mem_openSquare_zero_one, hzEq, Plane.supNorm_smul,
      abs_of_nonneg ht.1, show Plane.supNorm a = 1 from ha, mul_one]
    exact htLt

/-- Actual supported one-arm radialization relative to the positive anchor ray.
The source need not have finite overlap with any old ray. -/
private theorem actualPositiveRayRelativeOneArmSquare
    {J : Type} [Fintype J] (v : J → Plane) {b : Plane}
    (α : Path (0 : Plane) b) (hα : Function.Injective α)
    (hb : b ∈ modelCurve)
    (hαi : ∀ t : CurveComplex.Interval, t < 1 → α t ∈ Plane.openSquare 0 1)
    (havoid : ∀ t : CurveComplex.Interval, 0 < t →
      α t ∉ {z : Plane | z 1 = 0 ∧ 0 ≤ z 0}) :
    let reference : Set Plane := {z | z 1 = 0 ∧ 0 ≤ z 0}
    ∃ F : Plane ≃ₜ Plane, F 0 = 0 ∧ F '' reference = reference ∧
      (∀ x, x ∉ Plane.openSquare 0 1 → F x = x) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ F '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          segment ℝ 0 q ∩ reference = {0} ∧
          ∀ (j : J) (r : ℝ), q ≠ r • v j := by
  let a : Plane := Plane.mk 1 0
  let R : Set Plane := {z | z 1 = 0 ∧ 0 ≤ z 0}
  let K := segment ℝ (0 : Plane) a
  obtain ⟨ha, hKArc, hKR, hlocal, hKi⟩ := actualPositiveReferenceSquareArm
  change a ∈ modelCurve at ha
  change IsArcBetween K a 0 at hKArc
  change K ⊆ R at hKR
  change R ∩ Plane.openSquare 0 1 ⊆ K at hlocal
  change K \ {a} ⊆ Plane.openSquare 0 1 at hKi
  have h0K : (0 : Plane) ∈ K := left_mem_segment ℝ 0 a
  have hbR : b ∉ R := by
    change b ∉ {z : Plane | z 1 = 0 ∧ 0 ≤ z 0}
    simpa only [α.target] using havoid 1 (by norm_num)
  have hb0 : b ≠ 0 := by
    intro he
    apply hbR
    simp [R, he]
  obtain ⟨q, hqi, hq0, hqup, hqlo, hind, hqv⟩ :=
    actualScaledTargetGermDirection v hb0
  let N := segment ℝ (0 : Plane) q ∪ segment ℝ q b
  obtain ⟨hNArc, hNi⟩ := actualSimpleTwoSegmentSourceTarget hb hqi hq0 hind
  change IsArcBetween N 0 b at hNArc
  change N \ {0,b} ⊆ Plane.openSquare 0 1 at hNi
  have hNR : N ∩ R = {0} := by
    simpa [N, R] using actualTwoSegmentTargetAvoidsReference false
      (by simpa [R] using hbR) hqup hqlo
  have hKN : K ∩ N = {0} :=
    actualFixedArmIntersectsReferenceAvoidingSource hKR h0K hNR
  have hαR : range α ∩ R = {0} := by
    apply Subset.antisymm
    · rintro z ⟨⟨t, rfl⟩, htR⟩
      by_cases ht : t = 0
      · simpa [ht, α.source]
      · exfalso
        exact havoid t (lt_of_le_of_ne t.property.1 (Ne.symm ht)) htR
    · intro z hz
      have hz0 : z = 0 := hz
      subst z
      exact ⟨⟨0, α.source⟩, by simp [R]⟩
  have hKα : K ∩ range α = {0} :=
    actualFixedArmIntersectsReferenceAvoidingSource hKR h0K hαR
  obtain ⟨κ, hκ, hκK⟩ := actualArcBetweenHasInjectivePath hKArc
  obtain ⟨ν, hν, hνN⟩ := actualArcBetweenHasInjectivePath hNArc
  obtain ⟨hA, hpA⟩ := actualJoinedSourceArmsArePointedArc κ α hκ hα
    (by simpa [hκK] using hKα)
  obtain ⟨hB, hpB⟩ := actualJoinedSourceArmsArePointedArc κ ν hκ hν
    (by simpa [hκK, hνN] using hKN)
  rw [hκK] at hA hpA
  rw [hκK, hνN] at hB hpB
  have hAi : (K ∪ range α) \ {a,b} ⊆ Plane.openSquare 0 1 := by
    intro z hz
    have hza : z ≠ a := fun he => hz.2 (by simp [he])
    have hzb : z ≠ b := fun he => hz.2 (by simp [he])
    rcases hz.1 with hzK | hzα
    · apply hKi
      exact ⟨hzK, by simpa using hza⟩
    · obtain ⟨t, rfl⟩ := hzα
      apply hαi
      apply lt_of_le_of_ne t.property.2
      intro he
      have heI : t = (1 : CurveComplex.Interval) := Subtype.ext he
      apply hz.2
      simp [heI, α.target]
  have hBi : (K ∪ N) \ {a,b} ⊆ Plane.openSquare 0 1 := by
    intro z hz
    have hza : z ≠ a := fun he => hz.2 (by simp [he])
    have hzb : z ≠ b := fun he => hz.2 (by simp [he])
    rcases hz.1 with hzK | hzN
    · exact hKi ⟨hzK, by simpa using hza⟩
    · by_cases hz0 : z = 0
      · rw [hz0, mem_openSquare_zero_one]
        simp [Plane.supNorm]
      · apply hNi
        exact ⟨hzN, by simpa using ⟨hz0, hzb⟩⟩
  obtain ⟨F, hF0, hFα, hFR, hfix⟩ :=
    actualAnchorRelativeJoinedSourceCrosscutReplacement hA hB hKArc
      hKα hKN hpA hpB ha hb hAi hBi hKR hlocal
  have hFb : F b = b := by
    apply hfix
    intro hh
    have hlt := mem_openSquare_zero_one.mp hh
    rw [show Plane.supNorm b = 1 from hb] at hlt
    exact (lt_irrefl 1) hlt
  have hqFb : q ≠ F b := by
    rw [hFb]
    intro he
    have hlt := mem_openSquare_zero_one.mp hqi
    rw [he, show Plane.supNorm b = 1 from hb] at hlt
    exact (lt_irrefl 1) hlt
  obtain ⟨c, hc, hc1, hcim⟩ := actualSourcePrefixPullback α hα F
    (segment ℝ (0 : Plane) q) N hNArc
    (by simpa only [hF0] using isArcBetween_segment hq0.symm)
    (by rw [hFα]) subset_union_left
    (by rw [hFα]; exact Or.inl (right_mem_segment ℝ 0 q))
    (by simpa only [hF0] using hq0) hqFb
  refine ⟨F, hF0, hFR, hfix, c, hc, hc1, q, hq0, hcim, ?_, hqv⟩
  apply Subset.antisymm
  · intro z hz
    rw [← hNR]
    exact ⟨Or.inl hz.1, hz.2⟩
  · intro z hz
    have hz0 : z = 0 := hz
    subst z
    exact ⟨left_mem_segment ℝ 0 q, by simp [R]⟩

private theorem actualInjectivePathIsArc
    {p q : Plane} (γ : Path p q) (hγ : Function.Injective γ) :
    IsArcBetween (range γ) p q := by
  refine ⟨γ.extend, γ.continuous_extend.continuousOn, ?_, ?_,
    γ.extend_zero, γ.extend_one⟩
  · intro s hs t ht he
    rw [Path.extend_apply _ hs, Path.extend_apply _ ht] at he
    exact congrArg Subtype.val (hγ he)
  · exact γ.image_extend_of_subset (Subset.refl (Icc (0 : ℝ) 1))

/-- Radialize a genuine source prefix without replacing it by an abstract
first-exit path. The final cut belongs to the original parametrization. -/
private theorem actualPositiveRayRelativeOriginalArmSquare
    {J : Type} [Fintype J] (v : J → Plane) {b : Plane}
    (α : Path (0 : Plane) b) (hα : Function.Injective α)
    (hb : b ∉ Plane.closedSquare 0 1)
    (havoid : ∀ t : CurveComplex.Interval, 0 < t →
      α t ∉ {z : Plane | z 1 = 0 ∧ 0 ≤ z 0}) :
    let reference : Set Plane := {z | z 1 = 0 ∧ 0 ≤ z 0}
    ∃ F : Plane ≃ₜ Plane, F 0 = 0 ∧ F '' reference = reference ∧
      (∀ x, x ∉ Plane.openSquare 0 1 → F x = x) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ F '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          segment ℝ 0 q ∩ reference = {0} ∧
          ∀ (j : J) (r : ℝ), q ≠ r • v j := by
  obtain ⟨d, hd, hd1, δ, hδ, hδb, hδi, hδavoid, hδrange⟩ :=
    actualReferenceAvoidingFirstExitSourceArm α hα havoid hb
  let allv : Option J → Plane := fun j => Option.casesOn j b v
  obtain ⟨F, hF0, hFR, hfix, cδ, hcδ, hcδ1, q, hq0, hqim, hqR, hqv⟩ :=
    actualPositiveRayRelativeOneArmSquare allv δ hδ hδb hδi hδavoid
  have hfullArc : IsArcBetween (F '' range α) 0 (F b) := by
    have hh := (actualInjectivePathIsArc α hα).image_of_injOn
      (S := Set.univ) (subset_univ _) F.continuous.continuousOn F.injective.injOn
    simpa only [hF0] using hh
  have hsub : segment ℝ (0 : Plane) q ⊆ F '' range α := by
    rw [← hqim]
    apply (image_mono (image_subset_range _ _)).trans
    apply image_mono
    rw [hδrange]
    exact image_subset_range _ _
  have hFb : F b = b := by
    apply hfix
    intro hh
    apply hb
    exact mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hh).le
  have hqFb : q ≠ F b := by
    rw [hFb]
    simpa [allv] using hqv none 1
  obtain ⟨c, hc, hc1, hcim⟩ := actualSourcePrefixPullback α hα F
    (segment ℝ (0 : Plane) q) (F '' range α) hfullArc
    (by simpa only [hF0] using isArcBetween_segment hq0.symm)
    Subset.rfl hsub (hsub (right_mem_segment ℝ 0 q))
    (by simpa only [hF0] using hq0) hqFb
  exact ⟨F, hF0, hFR, hfix, c, hc, hc1, q, hq0, hcim, hqR,
    fun j r => hqv (some j) r⟩

private theorem actualRelativeSquareWindow (o a b : Plane) (ha : a ≠ o) (hb : b ≠ o)
    (V : Set Plane) (hV : IsOpen V) (hoV : o ∈ V) :
    ∃ (E : Plane ≃ₜ Plane) (R scale : ℝ), 0 < R ∧ 0 < scale ∧
      closedBall o R ⊆ V ∧ E o = 0 ∧
      E a ∉ Plane.closedSquare 0 1 ∧ E b ∉ Plane.closedSquare 0 1 ∧
      (∀ x, E x ∈ Plane.openSquare 0 1 → x ∈ ball o R) ∧
      ∀ y, E.symm y = scale • y + o := by
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hoV)
  have pos (x : Plane) (hx : x ≠ o) : 0 < Plane.supNorm (x-o) := by
    have hnorm : 0 < ‖x-o‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    have hbound := Plane.norm_le_sqrt_two_mul_supNorm (x-o)
    by_contra hn
    have hprod : Real.sqrt 2 * Plane.supNorm (x-o) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (not_lt.mp hn)
    linarith
  let R := ε/2
  let scale := min (R/4) (min (Plane.supNorm (a-o)) (Plane.supNorm (b-o))) / 2
  have hR : 0 < R := half_pos hε
  have hscale : 0 < scale := half_pos (lt_min (by positivity) (lt_min (pos a ha) (pos b hb)))
  have hscaleR : scale < R/4 :=
    (half_lt_self (lt_min (by positivity) (lt_min (pos a ha) (pos b hb)))).trans_le (min_le_left _ _)
  have hscalea : scale < Plane.supNorm (a-o) :=
    (half_lt_self (lt_min (by positivity) (lt_min (pos a ha) (pos b hb)))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hscaleb : scale < Plane.supNorm (b-o) :=
    (half_lt_self (lt_min (by positivity) (lt_min (pos a ha) (pos b hb)))).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  let E : Plane ≃ₜ Plane := {
    toEquiv := {
      toFun := fun x => scale⁻¹ • (x-o)
      invFun := fun y => scale • y + o
      left_inv := by
        intro x
        dsimp only
        rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hscale),one_smul]
        abel
      right_inv := by
        intro y
        dsimp only
        rw [add_sub_cancel_right,smul_smul,inv_mul_cancel₀ (ne_of_gt hscale),one_smul] }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hEo : E o = 0 := by simp [E]
  have houtside (x : Plane) (hx : scale < Plane.supNorm (x-o)) : E x ∉ Plane.closedSquare 0 1 := by
    intro hm
    have hn := mem_closedSquare_zero_one.mp hm
    change Plane.supNorm (scale⁻¹ • (x-o)) ≤ 1 at hn
    rw [Plane.supNorm_smul,abs_of_pos (inv_pos.mpr hscale)] at hn
    have hh : Plane.supNorm (x-o) ≤ scale := by
      have ht := mul_le_mul_of_nonneg_left hn hscale.le
      rw [←mul_assoc,mul_inv_cancel₀ (ne_of_gt hscale),one_mul,mul_one] at ht
      exact ht
    exact not_le_of_gt hx hh
  have hinside (x : Plane) (hx : E x ∈ Plane.openSquare 0 1) : x ∈ ball o R := by
    have hsup := mem_openSquare_zero_one.mp hx
    have hsqrt : Real.sqrt 2 < 2 := by
      have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      have hp := Real.sqrt_nonneg (2:ℝ)
      nlinarith
    have hn : ‖E x‖ < 2 := by
      have hbound := Plane.norm_le_sqrt_two_mul_supNorm (E x)
      have hp := Plane.supNorm_nonneg (E x)
      nlinarith [Real.sqrt_nonneg (2:ℝ)]
    have hxe : x-o = scale • E x := by
      have hh := E.symm_apply_apply x
      change scale • E x + o = x at hh
      have hs := congrArg (fun y : Plane => y-o) hh
      simpa only [add_sub_cancel_right] using hs.symm
    rw [mem_ball,dist_eq_norm,hxe,norm_smul,Real.norm_eq_abs,abs_of_pos hscale]
    exact (mul_lt_mul_of_pos_left hn hscale).trans (by linarith)
  refine ⟨E,R,scale,hR,hscale,?_,hEo,houtside a hscalea,houtside b hscaleb,hinside,fun _ => rfl⟩
  exact (closedBall_subset_ball (by dsimp [R]; linarith)).trans hεV

private theorem actualPositiveScaleReferenceMembership
    (anchorLoop : Bool) {s : ℝ} (hs : 0 < s) (z : Plane) :
    (s • z) ∈ {x : Plane | x 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ x 0)} ↔
      z ∈ {x : Plane | x 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ x 0)} := by
  change (s * z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ s * z 0)) ↔
    (z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ z 0))
  constructor
  · rintro ⟨hy, hh | hx⟩
    · exact ⟨(mul_eq_zero.mp hy).resolve_left (ne_of_gt hs), Or.inl hh⟩
    · exact ⟨(mul_eq_zero.mp hy).resolve_left (ne_of_gt hs),
        Or.inr (nonneg_of_mul_nonneg_right hx hs)⟩
  · rintro ⟨hy, hh | hx⟩
    · exact ⟨by rw [hy, mul_zero], Or.inl hh⟩
    · exact ⟨by rw [hy, mul_zero], Or.inr (mul_nonneg hs.le hx)⟩

private theorem actualPositiveScaleReferenceImage
    (anchorLoop : Bool) {s : ℝ} (hs : 0 < s) :
    (fun z : Plane => s • z) ''
      {x : Plane | x 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ x 0)} =
      {x : Plane | x 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ x 0)} := by
  apply Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    exact (actualPositiveScaleReferenceMembership anchorLoop hs x).mpr hx
  · intro z hz
    refine ⟨s⁻¹ • z,
      (actualPositiveScaleReferenceMembership anchorLoop (inv_pos.mpr hs) z).mpr hz, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]

private theorem actualGermSegmentAvoidingNoncollinearRay
    {q v : Plane} (h : ∀ r : ℝ, q ≠ r • v) :
    segment ℝ (0 : Plane) q ∩ {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • v} = {0} := by
  apply Subset.antisymm
  · rintro z ⟨hz, r, hr, hzr⟩
    rw [segment_eq_image] at hz
    obtain ⟨t, ht, htz⟩ := hz
    have htq : t • q = z := by simpa using htz
    by_cases ht0 : t = 0
    · simpa [ht0] using htq.symm
    · exfalso
      apply h (t⁻¹ * r)
      have he := congrArg (fun x : Plane => t⁻¹ • x) (htq.trans hzr)
      simpa only [smul_smul, inv_mul_cancel₀ ht0, one_smul] using he
  · intro z hz
    have hz0 : z = 0 := hz
    subst z
    exact ⟨left_mem_segment ℝ 0 q, 0, le_refl 0, by simp⟩

/-- Actual one-arm producer in any prescribed neighborhood, preserving the
literal positive anchor ray through scaling and conjugation. -/
private theorem actualPositiveRayRelativeOneArm
    {J : Type} [Fintype J] (v : J → Plane) {b : Plane}
    (α : Path (0 : Plane) b) (hα : Function.Injective α)
    (havoid : ∀ t : CurveComplex.Interval, 0 < t →
      α t ∉ {z : Plane | z 1 = 0 ∧ 0 ≤ z 0})
    (V : Set Plane) (hV : IsOpen V) (h0V : (0 : Plane) ∈ V) :
    let reference : Set Plane := {z | z 1 = 0 ∧ 0 ≤ z 0}
    ∃ F : Plane ≃ₜ Plane, ∃ R : ℝ, 0 < R ∧ closedBall (0 : Plane) R ⊆ V ∧
      F 0 = 0 ∧ (∀ x, x ∉ ball (0 : Plane) R → F x = x) ∧
      F '' reference = reference ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ F '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          segment ℝ 0 q ∩ reference = {0} ∧
          ∀ j, segment ℝ 0 q ∩
            {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • v j} = {0} := by
  let ref : Set Plane := {z | z 1 = 0 ∧ 0 ≤ z 0}
  have hb0 : b ≠ 0 := by
    intro he
    have h10 : (1 : CurveComplex.Interval) = 0 :=
      hα (α.target.trans (he.trans α.source.symm))
    exact one_ne_zero h10
  obtain ⟨E, R, scale, hR, hs, hRV, hE0, hEb, _, hinside, hinv⟩ :=
    actualRelativeSquareWindow 0 b b hb0 hb0 V hV h0V
  have hinv' : ∀ y, E.symm y = scale • y := by
    intro y
    simpa using hinv y
  have hE : ∀ x, E x = scale⁻¹ • x := by
    intro x
    have hh := E.symm_apply_apply x
    rw [hinv'] at hh
    have he := congrArg (fun z : Plane => scale⁻¹ • z) hh
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul] using he
  have hER : E '' ref = ref := by
    have hh := actualPositiveScaleReferenceImage false (inv_pos.mpr hs)
    simpa [ref, hE] using hh
  have hEinvR : E.symm '' ref = ref := by
    have hh := actualPositiveScaleReferenceImage false hs
    simpa [ref, hinv'] using hh
  let α' : Path (0 : Plane) (E b) := {
    toFun := E ∘ α
    continuous_toFun := E.continuous.comp α.continuous
    source' := (congrArg E α.source).trans hE0
    target' := congrArg E α.target }
  have hα' : Function.Injective α' := fun s t he => hα (E.injective he)
  have havoid' : ∀ t : CurveComplex.Interval, 0 < t → α' t ∉ ref := by
    intro t ht he
    apply havoid t ht
    have hh : scale⁻¹ • α t ∈ ref := by simpa [α', hE] using he
    have hc := (actualPositiveScaleReferenceMembership false (inv_pos.mpr hs) (α t)).mp
      (by simpa [ref] using hh)
    simpa using hc
  obtain ⟨G, hG0, hGR, hGfix, c, hc, hc1, q, hq0, hqim, hqR, hqv⟩ :=
    actualPositiveRayRelativeOriginalArmSquare v α' hα' hEb havoid'
  let F : Plane ≃ₜ Plane := (E.trans G).trans E.symm
  have hF0 : F 0 = 0 := by
    change E.symm (G (E 0)) = 0
    rw [hE0, hG0, hinv']
    simp
  have hfix : ∀ x, x ∉ ball (0 : Plane) R → F x = x := by
    intro x hx
    change E.symm (G (E x)) = x
    rw [hGfix (E x) (fun he => hx (hinside x he)), E.symm_apply_apply]
  have himage (A : Set Plane) : F '' A = E.symm '' (G '' (E '' A)) := by
    rw [← image_comp, ← image_comp]
    rfl
  have hFR : F '' ref = ref := by
    rw [himage, hER, hGR, hEinvR]
  let A : Plane →ᵃ[ℝ] Plane := {
    toFun := fun y => scale • y
    linear := scale • LinearMap.id
    map_vadd' := by intro x y; change scale • (y+x) = scale • y + scale • x; module }
  have hA : (E.symm : Plane → Plane) = (A : Plane → Plane) := funext hinv'
  have hseg : E.symm '' segment ℝ (0 : Plane) q = segment ℝ 0 (scale • q) := by
    rw [hA, image_segment]
    simp [A]
  have hprefix : F '' (α '' Icc 0 c) = segment ℝ 0 (scale • q) := by
    have hαprefix : α' '' Icc 0 c = E '' (α '' Icc 0 c) := image_comp E α _
    rw [himage, ← hαprefix, hqim, hseg]
  have hscaledRef : segment ℝ 0 (scale • q) ∩ ref = {0} := by
    rw [← hseg, ← hEinvR, ← image_inter E.symm.injective, hqR, image_singleton, hinv']
    simp
  refine ⟨F, R, hR, hRV, hF0, hfix, hFR, c, hc, hc1, scale • q,
    smul_ne_zero (ne_of_gt hs) hq0, hprefix, hscaledRef, ?_⟩
  intro j
  apply actualGermSegmentAvoidingNoncollinearRay
  intro r he
  apply hqv j (scale⁻¹ * r)
  have hh := congrArg (fun x : Plane => scale⁻¹ • x) he
  simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul] using hh

private theorem actualUpperHalfSquareGeometry :
    let Q : Set Plane := Plane.closedSquare 0 1 ∩ {x | 0 ≤ x 1}
    IsClosed Q ∧ Convex ℝ Q ∧
      interior Q = Plane.openSquare 0 1 ∩ {x | 0 < x 1} ∧
      (interior Q).Nonempty ∧ Bornology.IsBounded Q ∧
      (0 : Plane) ∈ frontier Q ∧ IsJordanCurve (frontier Q) ∧
      interior Q = inside (frontier Q) := by
  let Q : Set Plane := Plane.closedSquare 0 1 ∩ {x | 0 ≤ x 1}
  let L : Plane →ₗ[ℝ] ℝ := {
    toFun := fun x => x 1
    map_add' := by intro x y; simp
    map_smul' := by intro r x; simp }
  have hL : Continuous L := Plane.continuous_coord 1
  have hsurj : Function.Surjective L := fun r => ⟨Plane.mk 0 r, rfl⟩
  have hopen : IsOpenMap L := L.isOpenMap_of_finiteDimensional hsurj
  have hhalf : interior {x : Plane | 0 ≤ x 1} = {x | 0 < x 1} := by
    change interior (L ⁻¹' Ici (0 : ℝ)) = L ⁻¹' Ioi (0 : ℝ)
    rw [← hopen.preimage_interior_eq_interior_preimage hL, interior_Ici]
  have hclosed : IsClosed Q := (Plane.isClosed_closedSquare 0 1).inter
    (isClosed_le continuous_const (Plane.continuous_coord 1))
  have hconv : Convex ℝ Q := by
    apply (Plane.convex_closedSquare 0 1).inter
    intro x hx y hy r t hr ht hrt
    change 0 ≤ r * x 1 + t * y 1
    exact add_nonneg (mul_nonneg hr hx) (mul_nonneg ht hy)
  have hInt : interior Q = Plane.openSquare 0 1 ∩ {x | 0 < x 1} := by
    rw [interior_inter, interior_closedSquare_zero_one, hhalf]
  have hne : (interior Q).Nonempty := by
    refine ⟨Plane.mk 0 (1/2), ?_⟩
    rw [hInt]
    constructor
    · rw [mem_openSquare_zero_one]
      norm_num [Plane.supNorm]
    · norm_num
  have hbounded : Bornology.IsBounded Q :=
    (Plane.isBounded_closedSquare 0 1).subset inter_subset_left
  have h0 : (0 : Plane) ∈ frontier Q := by
    rw [hclosed.frontier_eq]
    refine ⟨⟨?_, by simp⟩, ?_⟩
    · rw [mem_closedSquare_zero_one]
      simp [Plane.supNorm]
    · rw [hInt]
      simp
  obtain ⟨E, hEi, hEQ, hEf, hJ⟩ :=
    convex_sector_ambient_square_chart Q hconv hclosed hne hbounded
  have hclInt : closure (interior Q) = Q :=
    (hconv.closure_interior_eq_closure_of_nonempty_interior hne).trans hclosed.closure_eq
  have hfront : frontier (interior Q) = frontier Q := by
    simp only [frontier, isOpen_interior.interior_eq, hclInt, hclosed.closure_eq]
  have hInside : interior Q = inside (frontier Q) :=
    bounded_jordan_frontier_region_eq_inside hJ isOpen_interior
      (hconv.interior.isConnected hne) (hbounded.subset interior_subset) hfront
  exact ⟨hclosed, hconv, hInt, hne, hbounded, h0, hJ, hInside⟩

private theorem actualPositiveTwoSegmentTarget
    {q b : Plane} (hq : 0 < q 1) (hb : 0 < b 1) :
    ∀ z ∈ segment ℝ (0 : Plane) q ∪ segment ℝ q b,
      z ≠ 0 → 0 < z 1 := by
  intro z hz hz0
  rcases hz with hzfirst | hzsecond
  · rw [segment_eq_image] at hzfirst
    obtain ⟨t, ht, htz⟩ := hzfirst
    have htq : t • q = z := by simpa using htz
    have ht0 : t ≠ 0 := by intro he; apply hz0; simpa [he] using htq.symm
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have he := congrArg (fun x : Plane => x 1) htq
    change t * q 1 = z 1 at he
    rw [← he]
    exact mul_pos htpos hq
  · obtain ⟨r, t, hr, ht, hrt, hzt⟩ := hzsecond
    have he := congrArg (fun x : Plane => x 1) hzt
    change r * q 1 + t * b 1 = z 1 at he
    rw [← he]
    by_cases hr0 : r = 0
    · have ht1 : t = 1 := by linarith
      simpa [hr0, ht1] using hb
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne hr (Ne.symm hr0)) hq) (mul_nonneg ht hb.le)

/-- Source-only supported replacement in the genuine upper half-square.
The entire literal anchor axis is fixed pointwise. -/
private theorem actualAxisRelativeUpperArmSquare
    {J : Type} [Fintype J] (v : J → Plane) {b : Plane}
    (α : Path (0 : Plane) b) (hα : Function.Injective α)
    (hb : b ∈ modelCurve)
    (hαi : ∀ t : CurveComplex.Interval, t < 1 → α t ∈ Plane.openSquare 0 1)
    (hpos : ∀ t : CurveComplex.Interval, 0 < t → 0 < (α t) 1) :
    ∃ F : Plane ≃ₜ Plane, F 0 = 0 ∧
      (∀ x : Plane, x 1 = 0 → F x = x) ∧
      (∀ x, x ∉ Plane.openSquare 0 1 → F x = x) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ F '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          segment ℝ 0 q ∩ {x : Plane | x 1 = 0} = {0} ∧
          ∀ (j : J) (r : ℝ), q ≠ r • v j := by
  let Q : Set Plane := Plane.closedSquare 0 1 ∩ {x | 0 ≤ x 1}
  obtain ⟨hclosed, hconv, hInt, hne, hbounded, h0front, hJ, hInside⟩ :=
    actualUpperHalfSquareGeometry
  change interior Q = Plane.openSquare 0 1 ∩ {x | 0 < x 1} at hInt
  have hbpos : 0 < b 1 := by simpa only [α.target] using hpos 1 (by norm_num)
  have hb0 : b ≠ 0 := by intro he; simp [he] at hbpos
  obtain ⟨q, hqi, hq0, hqup, hqlo, hind, hqv⟩ := actualScaledTargetGermDirection v hb0
  have hqpos : 0 < q 1 := hqup hbpos.le
  let N := segment ℝ (0 : Plane) q ∪ segment ℝ q b
  obtain ⟨hNArc, hNi⟩ := actualSimpleTwoSegmentSourceTarget hb hqi hq0 hind
  change IsArcBetween N 0 b at hNArc
  have hNpos : ∀ z ∈ N, z ≠ 0 → 0 < z 1 := actualPositiveTwoSegmentTarget hqpos hbpos
  have hNinterior : N \ {0,b} ⊆ interior Q := by
    intro z hz
    have hz0 : z ≠ 0 := fun he => hz.2 (by simp [he])
    rw [hInt]
    exact ⟨hNi hz, hNpos z hz.1 hz0⟩
  have hAArc : IsArcBetween (range α) 0 b := actualInjectivePathIsArc α hα
  have hAinterior : range α \ {0,b} ⊆ interior Q := by
    rintro z ⟨⟨t, rfl⟩, htends⟩
    have ht0 : t ≠ 0 := by intro he; apply htends; simp [he, α.source]
    have ht1 : t ≠ 1 := by intro he; apply htends; simp [he, α.target]
    rw [hInt]
    exact ⟨hαi t (lt_of_le_of_ne t.property.2 ht1),
      hpos t (lt_of_le_of_ne t.property.1 ht0.symm)⟩
  have hbfront : b ∈ frontier Q := by
    rw [hclosed.frontier_eq]
    refine ⟨⟨mem_closedSquare_zero_one.mpr (show Plane.supNorm b = 1 from hb).le,
      hbpos.le⟩, ?_⟩
    rw [hInt]
    intro hh
    have hlt := mem_openSquare_zero_one.mp hh.1
    rw [show Plane.supNorm b = 1 from hb] at hlt
    exact (lt_irrefl 1) hlt
  obtain ⟨e⟩ := exists_arcHomeo hAArc hNArc
  obtain ⟨F, hpoint, hFN, hfix⟩ :=
    jordan_sector_prescribed_crosscut_ambient_extension hJ h0front hbfront hAArc hNArc
      (by simpa only [← hInside] using hAinterior)
      (by simpa only [← hInside] using hNinterior) e
  have hfixQ : ∀ x, x ∉ interior Q → F x = x := by
    simpa only [← hInside] using hfix
  have haxis : ∀ x : Plane, x 1 = 0 → F x = x := by
    intro x hx
    apply hfixQ
    rw [hInt]
    intro hh
    have hp : 0 < x 1 := hh.2
    rw [hx] at hp
    exact (lt_irrefl 0) hp
  have hF0 : F 0 = 0 := haxis 0 (by simp)
  have hFb : F b = b := hfixQ b ((hclosed.frontier_eq ▸ hbfront).2)
  have hfixSquare : ∀ x, x ∉ Plane.openSquare 0 1 → F x = x := by
    intro x hx
    apply hfixQ
    rw [hInt]
    exact fun hh => hx hh.1
  have hqFb : q ≠ F b := by
    rw [hFb]
    intro he
    have hh := (hind 1 1 (by simp [he])).1
    norm_num at hh
  obtain ⟨c, hc, hc1, hcim⟩ := actualSourcePrefixPullback α hα F
    (segment ℝ (0 : Plane) q) N hNArc
    (by simpa only [hF0] using isArcBetween_segment hq0.symm)
    (by rw [hFN]) subset_union_left
    (by rw [hFN]; exact Or.inl (right_mem_segment ℝ 0 q))
    (by simpa only [hF0] using hq0) hqFb
  refine ⟨F, hF0, haxis, hfixSquare, c, hc, hc1, q, hq0, hcim, ?_, hqv⟩
  apply Subset.antisymm
  · intro z hz
    by_cases hz0 : z = 0
    · exact hz0
    · have hh := hNpos z (Or.inl hz.1) hz0
      have hzero : z 1 = 0 := hz.2
      rw [hzero] at hh
      exact False.elim ((lt_irrefl 0) hh)
  · intro z hz
    have hz0 : z = 0 := hz
    subst z
    exact ⟨left_mem_segment ℝ 0 q, by simp⟩

/-- A genuine continuous source avoiding the entire axis selects one actual
half-plane; no source-side choice is supplied by the caller. -/
private theorem actualAxisAvoidingSourceSelectsHalfPlane
    {b : Plane} (α : Path (0 : Plane) b)
    (havoid : ∀ t : CurveComplex.Interval, 0 < t → (α t) 1 ≠ 0) :
    (∀ t : CurveComplex.Interval, 0 < t → 0 < (α t) 1) ∨
      (∀ t : CurveComplex.Interval, 0 < t → (α t) 1 < 0) := by
  let f : CurveComplex.Interval → ℝ := fun t => (α t) 1
  let Y : Set ℝ := f '' Ioc (0 : CurveComplex.Interval) 1
  have hfc : Continuous f := (Plane.continuous_coord 1).comp α.continuous
  have hconn : IsPreconnected Y := isPreconnected_Ioc.image f hfc.continuousOn
  have hcover : Y ⊆ Ioi (0 : ℝ) ∪ Iio 0 := by
    rintro x ⟨t, ht, rfl⟩
    rcases lt_or_gt_of_ne (havoid t ht.1) with hn | hp
    · exact Or.inr hn
    · exact Or.inl hp
  have hdisj : Disjoint (Ioi (0 : ℝ)) (Iio 0) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hp : (0 : ℝ) < x := hx
    have hn : x < 0 := hy
    exact (lt_irrefl 0) (lt_trans hp hn)
  have hbne : f 1 ≠ 0 := havoid 1 (by norm_num)
  rcases lt_or_gt_of_ne hbne with hbneg | hbpos
  · have hcover' : Y ⊆ Iio (0 : ℝ) ∪ Ioi 0 := by
      intro x hx
      exact (hcover hx).symm
    have hsel : Y ⊆ Iio (0 : ℝ) :=
      hconn.subset_left_of_subset_union isOpen_Iio isOpen_Ioi hdisj.symm hcover'
        ⟨f 1, ⟨⟨1, by norm_num, rfl⟩, hbneg⟩⟩
    exact Or.inr (fun t ht => hsel ⟨t, ⟨ht, t.property.2⟩, rfl⟩)
  · have hsel : Y ⊆ Ioi (0 : ℝ) :=
      hconn.subset_left_of_subset_union isOpen_Ioi isOpen_Iio hdisj hcover
        ⟨f 1, ⟨⟨1, by norm_num, rfl⟩, hbpos⟩⟩
    exact Or.inl (fun t ht => hsel ⟨t, ⟨ht, t.property.2⟩, rfl⟩)

private theorem actualNegationAxisImage :
    (fun x : Plane => -x) '' {x : Plane | x 1 = 0} = {x : Plane | x 1 = 0} := by
  apply Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    change -x 1 = 0
    exact neg_eq_zero.mpr hx
  · intro z hz
    refine ⟨-z, ?_, neg_neg z⟩
    change -z 1 = 0
    exact neg_eq_zero.mpr hz

private theorem actualAxisRelativeProperArmSquare
    {J : Type} [Fintype J] (v : J → Plane) {b : Plane}
    (α : Path (0 : Plane) b) (hα : Function.Injective α)
    (hb : b ∈ modelCurve)
    (hαi : ∀ t : CurveComplex.Interval, t < 1 → α t ∈ Plane.openSquare 0 1)
    (havoid : ∀ t : CurveComplex.Interval, 0 < t → (α t) 1 ≠ 0) :
    ∃ F : Plane ≃ₜ Plane, F 0 = 0 ∧
      (∀ x : Plane, x 1 = 0 → F x = x) ∧
      (∀ x, x ∉ Plane.openSquare 0 1 → F x = x) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ F '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          segment ℝ 0 q ∩ {x : Plane | x 1 = 0} = {0} ∧
          ∀ (j : J) (r : ℝ), q ≠ r • v j := by
  rcases actualAxisAvoidingSourceSelectsHalfPlane α havoid with hpos | hneg
  · exact actualAxisRelativeUpperArmSquare v α hα hb hαi hpos
  · let α' : Path (0 : Plane) (-b) := {
      toFun := fun t => -α t
      continuous_toFun := by fun_prop
      source' := by simp [α.source]
      target' := by simp [α.target] }
    have hα' : Function.Injective α' := fun s t he => hα (neg_injective he)
    have hb' : -b ∈ modelCurve := by
      change Plane.supNorm (-b) = 1
      have hbNorm : Plane.supNorm b = 1 := hb
      simpa only [Plane.supNorm, PiLp.neg_apply, abs_neg] using hbNorm
    have hα'i : ∀ t : CurveComplex.Interval, t < 1 → α' t ∈ Plane.openSquare 0 1 := by
      intro t ht
      rw [mem_openSquare_zero_one]
      have hh := mem_openSquare_zero_one.mp (hαi t ht)
      change Plane.supNorm (-α t) < 1
      simpa only [Plane.supNorm, PiLp.neg_apply, abs_neg] using hh
    have hα'pos : ∀ t : CurveComplex.Interval, 0 < t → 0 < (α' t) 1 := by
      intro t ht
      change 0 < -(α t) 1
      exact neg_pos.mpr (hneg t ht)
    obtain ⟨G, hG0, hGaxis, hGfix, c, hc, hc1, q, hq0, hqim, hqaxis, hqv⟩ :=
      actualAxisRelativeUpperArmSquare v α' hα' hb' hα'i hα'pos
    let N : Plane ≃ₜ Plane := Homeomorph.neg Plane
    let F : Plane ≃ₜ Plane := (N.trans G).trans N
    have hF0 : F 0 = 0 := by change -G (-0) = 0; simp [hG0]
    have hFaxis : ∀ x : Plane, x 1 = 0 → F x = x := by
      intro x hx
      change -G (-x) = x
      rw [hGaxis (-x) (by change -x 1 = 0; simp [hx]), neg_neg]
    have hfix : ∀ x, x ∉ Plane.openSquare 0 1 → F x = x := by
      intro x hx
      have hn : -x ∉ Plane.openSquare 0 1 := by
        intro hh
        apply hx
        rw [mem_openSquare_zero_one] at hh ⊢
        simpa only [Plane.supNorm, PiLp.neg_apply, abs_neg] using hh
      change -G (-x) = x
      rw [hGfix (-x) hn, neg_neg]
    have himage (A : Set Plane) : F '' A = N '' (G '' (N '' A)) := by
      rw [← image_comp, ← image_comp]
      rfl
    let A : Plane →ᵃ[ℝ] Plane := {
      toFun := fun x => -x
      linear := -LinearMap.id
      map_vadd' := by intro x y; change -(y+x) = -y + -x; module }
    have hNA : (N : Plane → Plane) = (A : Plane → Plane) := rfl
    have hseg : N '' segment ℝ (0 : Plane) q = segment ℝ 0 (-q) := by
      rw [hNA, image_segment]
      simp [A]
    have hαprefix : α' '' Icc 0 c = N '' (α '' Icc 0 c) := image_comp N α _
    have hprefix : F '' (α '' Icc 0 c) = segment ℝ 0 (-q) := by
      rw [himage, ← hαprefix, hqim, hseg]
    have haxis : segment ℝ 0 (-q) ∩ {x : Plane | x 1 = 0} = {0} := by
      have hNaxis : N '' {x : Plane | x 1 = 0} = {x : Plane | x 1 = 0} :=
        actualNegationAxisImage
      rw [← hseg, ← hNaxis, ← image_inter N.injective, hqaxis, image_singleton]
      simp [N]
    refine ⟨F, hF0, hFaxis, hfix, c, hc, hc1, -q, neg_ne_zero.mpr hq0, hprefix, haxis, ?_⟩
    intro j r he
    apply hqv j (-r)
    have hh := congrArg Neg.neg he
    simpa using hh

private theorem actualAxisRelativeOriginalArmSquare
    {J : Type} [Fintype J] (v : J → Plane) {b : Plane}
    (α : Path (0 : Plane) b) (hα : Function.Injective α)
    (hb : b ∉ Plane.closedSquare 0 1)
    (havoid : ∀ t : CurveComplex.Interval, 0 < t →
      α t ∉ {z : Plane | z 1 = 0}) :
    let reference : Set Plane := {z | z 1 = 0}
    ∃ F : Plane ≃ₜ Plane, F 0 = 0 ∧ F '' reference = reference ∧
      (∀ x, x ∉ Plane.openSquare 0 1 → F x = x) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ F '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          segment ℝ 0 q ∩ reference = {0} ∧
          ∀ (j : J) (r : ℝ), q ≠ r • v j := by
  obtain ⟨d, hd, hd1, δ, hδ, hδb, hδi, hδavoid, hδrange⟩ :=
    actualReferenceAvoidingFirstExitSourceArm α hα havoid hb
  let allv : Option J → Plane := fun j => Option.casesOn j b v
  obtain ⟨F, hF0, hFaxis, hfix, cδ, hcδ, hcδ1, q, hq0, hqim, hqR, hqv⟩ :=
    actualAxisRelativeProperArmSquare allv δ hδ hδb hδi hδavoid
  have hFR : F '' {z : Plane | z 1 = 0} = {z : Plane | z 1 = 0} := by
    apply Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      rw [hFaxis x hx]
      exact hx
    · intro z hz
      exact ⟨z, hz, hFaxis z hz⟩
  have hfullArc : IsArcBetween (F '' range α) 0 (F b) := by
    have hh := (actualInjectivePathIsArc α hα).image_of_injOn
      (S := Set.univ) (subset_univ _) F.continuous.continuousOn F.injective.injOn
    simpa only [hF0] using hh
  have hsub : segment ℝ (0 : Plane) q ⊆ F '' range α := by
    rw [← hqim]
    apply (image_mono (image_subset_range _ _)).trans
    apply image_mono
    rw [hδrange]
    exact image_subset_range _ _
  have hFb : F b = b := by
    apply hfix
    intro hh
    apply hb
    exact mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hh).le
  have hqFb : q ≠ F b := by
    rw [hFb]
    simpa [allv] using hqv none 1
  obtain ⟨c, hc, hc1, hcim⟩ := actualSourcePrefixPullback α hα F
    (segment ℝ (0 : Plane) q) (F '' range α) hfullArc
    (by simpa only [hF0] using isArcBetween_segment hq0.symm)
    Subset.rfl hsub (hsub (right_mem_segment ℝ 0 q))
    (by simpa only [hF0] using hq0) hqFb
  exact ⟨F, hF0, hFR, hfix, c, hc, hc1, q, hq0, hcim, hqR,
    fun j r => hqv (some j) r⟩

private theorem actualAxisRelativeOneArm
    {J : Type} [Fintype J] (v : J → Plane) {b : Plane}
    (α : Path (0 : Plane) b) (hα : Function.Injective α)
    (havoid : ∀ t : CurveComplex.Interval, 0 < t →
      α t ∉ {z : Plane | z 1 = 0})
    (V : Set Plane) (hV : IsOpen V) (h0V : (0 : Plane) ∈ V) :
    let reference : Set Plane := {z | z 1 = 0}
    ∃ F : Plane ≃ₜ Plane, ∃ R : ℝ, 0 < R ∧ closedBall (0 : Plane) R ⊆ V ∧
      F 0 = 0 ∧ (∀ x, x ∉ ball (0 : Plane) R → F x = x) ∧
      F '' reference = reference ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ F '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          segment ℝ 0 q ∩ reference = {0} ∧
          ∀ j, segment ℝ 0 q ∩
            {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • v j} = {0} := by
  let ref : Set Plane := {z | z 1 = 0}
  have hb0 : b ≠ 0 := by
    intro he
    have h10 : (1 : CurveComplex.Interval) = 0 :=
      hα (α.target.trans (he.trans α.source.symm))
    exact one_ne_zero h10
  obtain ⟨E, R, scale, hR, hs, hRV, hE0, hEb, _, hinside, hinv⟩ :=
    actualRelativeSquareWindow 0 b b hb0 hb0 V hV h0V
  have hinv' : ∀ y, E.symm y = scale • y := by
    intro y
    simpa using hinv y
  have hE : ∀ x, E x = scale⁻¹ • x := by
    intro x
    have hh := E.symm_apply_apply x
    rw [hinv'] at hh
    have he := congrArg (fun z : Plane => scale⁻¹ • z) hh
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul] using he
  have hER : E '' ref = ref := by
    have hh := actualPositiveScaleReferenceImage true (inv_pos.mpr hs)
    simpa [ref, hE] using hh
  have hEinvR : E.symm '' ref = ref := by
    have hh := actualPositiveScaleReferenceImage true hs
    simpa [ref, hinv'] using hh
  let α' : Path (0 : Plane) (E b) := {
    toFun := E ∘ α
    continuous_toFun := E.continuous.comp α.continuous
    source' := (congrArg E α.source).trans hE0
    target' := congrArg E α.target }
  have hα' : Function.Injective α' := fun s t he => hα (E.injective he)
  have havoid' : ∀ t : CurveComplex.Interval, 0 < t → α' t ∉ ref := by
    intro t ht he
    apply havoid t ht
    have hh : scale⁻¹ • α t ∈ ref := by simpa [α', hE] using he
    have hc := (actualPositiveScaleReferenceMembership true (inv_pos.mpr hs) (α t)).mp
      (by simpa [ref] using hh)
    simpa using hc
  obtain ⟨G, hG0, hGR, hGfix, c, hc, hc1, q, hq0, hqim, hqR, hqv⟩ :=
    actualAxisRelativeOriginalArmSquare v α' hα' hEb havoid'
  let F : Plane ≃ₜ Plane := (E.trans G).trans E.symm
  have hF0 : F 0 = 0 := by
    change E.symm (G (E 0)) = 0
    rw [hE0, hG0, hinv']
    simp
  have hfix : ∀ x, x ∉ ball (0 : Plane) R → F x = x := by
    intro x hx
    change E.symm (G (E x)) = x
    rw [hGfix (E x) (fun he => hx (hinside x he)), E.symm_apply_apply]
  have himage (A : Set Plane) : F '' A = E.symm '' (G '' (E '' A)) := by
    rw [← image_comp, ← image_comp]
    rfl
  have hFR : F '' ref = ref := by
    rw [himage, hER, hGR, hEinvR]
  let A : Plane →ᵃ[ℝ] Plane := {
    toFun := fun y => scale • y
    linear := scale • LinearMap.id
    map_vadd' := by intro x y; change scale • (y+x) = scale • y + scale • x; module }
  have hA : (E.symm : Plane → Plane) = (A : Plane → Plane) := funext hinv'
  have hseg : E.symm '' segment ℝ (0 : Plane) q = segment ℝ 0 (scale • q) := by
    rw [hA, image_segment]
    simp [A]
  have hprefix : F '' (α '' Icc 0 c) = segment ℝ 0 (scale • q) := by
    have hαprefix : α' '' Icc 0 c = E '' (α '' Icc 0 c) := image_comp E α _
    rw [himage, ← hαprefix, hqim, hseg]
  have hscaledRef : segment ℝ 0 (scale • q) ∩ ref = {0} := by
    rw [← hseg, ← hEinvR, ← image_inter E.symm.injective, hqR, image_singleton, hinv']
    simp
  refine ⟨F, R, hR, hRV, hF0, hfix, hFR, c, hc, hc1, scale • q,
    smul_ne_zero (ne_of_gt hs) hq0, hprefix, hscaledRef, ?_⟩
  intro j
  apply actualGermSegmentAvoidingNoncollinearRay
  intro r he
  apply hqv j (scale⁻¹ * r)
  have hh := congrArg (fun x : Plane => scale⁻¹ • x) he
  simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul] using hh


private theorem actualOneSourceReferenceRelativeRadialization
    {K : Type} [Fintype K] (v : K → Plane)
    (γ : CurveComplex.Interval → Plane) (hγ : IsClosedEmbedding γ)
    (hzero : γ 0 = 0) (anchorLoop : Bool)
    (havoid : ∀ t : CurveComplex.Interval, 0 < t →
      ¬ ((γ t) 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ (γ t) 0)))
    (V : Set Plane) (hV : IsOpen V) (h0V : (0 : Plane) ∈ V) :
    let ref : Set Plane := {z | z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ z 0)}
    ∃ F : Plane ≃ₜ Plane, ∃ R : ℝ, 0 < R ∧ closedBall (0 : Plane) R ⊆ V ∧
      F 0 = 0 ∧ (∀ x, x ∉ ball (0 : Plane) R → F x = x) ∧ F '' ref = ref ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ F '' (γ '' Icc 0 c) = segment ℝ 0 q ∧
          segment ℝ 0 q ∩ ref = {0} ∧
          ∀ k, segment ℝ 0 q ∩
            {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • v k} = {0} := by
  let α : Path (0 : Plane) (γ 1) := {
    toFun := γ
    continuous_toFun := hγ.continuous
    source' := hzero
    target' := rfl }
  cases anchorLoop
  · simp only [Bool.false_eq_true, false_or] at havoid ⊢
    exact actualPositiveRayRelativeOneArm v α hγ.injective havoid V hV h0V
  · simp only [true_or, and_true] at havoid ⊢
    exact actualAxisRelativeOneArm v α hγ.injective havoid V hV h0V

private theorem actualTransportedSourceAvoidsLiteralReference
    (F : Plane ≃ₜ Plane) {R : Set Plane} (hR : F '' R = R)
    (γ : CurveComplex.Interval → Plane)
    (havoid : ∀ t : CurveComplex.Interval, 0 < t → γ t ∉ R) :
    ∀ t : CurveComplex.Interval, 0 < t → F (γ t) ∉ R := by
  intro t ht hh
  apply havoid t ht
  rw [← hR] at hh
  exact F.injective.mem_set_image.mp hh

/-- The other genuine source arm avoids the whole already straightened prefix,
by actual original distinct-label intersection and embeddings. -/
private theorem actualSecondSourceAvoidsFirstRadialPrefix
    (F : Plane ≃ₜ Plane) (γ₀ γ₁ : CurveComplex.Interval → Plane)
    (hγ₁ : Function.Injective γ₁) (hzero₁ : γ₁ 0 = 0)
    (hmeet : range γ₀ ∩ range γ₁ = {0})
    (c : CurveComplex.Interval) (q : Plane)
    (hprefix : F '' (γ₀ '' Icc 0 c) = segment ℝ 0 q) :
    ∀ t : CurveComplex.Interval, 0 < t → F (γ₁ t) ∉ segment ℝ 0 q := by
  intro t ht hh
  rw [← hprefix] at hh
  obtain ⟨x, ⟨u, hu, rfl⟩, he⟩ := hh
  have hxy : γ₀ u = γ₁ t := F.injective he
  have h0 : γ₁ t ∈ range γ₀ ∩ range γ₁ :=
    ⟨⟨u, hxy⟩, ⟨t, rfl⟩⟩
  rw [hmeet] at h0
  have he0 : γ₁ t = 0 := h0
  have ht0 : t = 0 := hγ₁ (he0.trans hzero₁.symm)
  exact (ne_of_gt ht) ht0

private theorem actualReferenceInsideUnitBallHasAnchorArm
    (anchorLoop : Bool) {z : Plane}
    (hz : z ∈ {x : Plane | x 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ x 0)})
    (hn : ‖z‖ < 1) :
    z ∈ segment ℝ (0 : Plane) (Plane.mk 1 0) ∨
      (anchorLoop = true ∧ z ∈ segment ℝ (0 : Plane) (Plane.mk (-1) 0)) := by
  have hz1 : z 1 = 0 := hz.1
  have hxBound : |z 0| < 1 := lt_of_le_of_lt
    (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z 0) hn
  by_cases hx : 0 ≤ z 0
  · apply Or.inl
    rw [segment_eq_image]
    refine ⟨z 0, ⟨hx, (lt_of_le_of_lt (le_abs_self _) hxBound).le⟩, ?_⟩
    simp only [smul_zero, zero_add]
    ext i
    fin_cases i
    · simp
    · simp [hz1]
  · have hloop : anchorLoop = true := hz.2.resolve_right hx
    apply Or.inr
    refine ⟨hloop, ?_⟩
    rw [segment_eq_image]
    refine ⟨-z 0, ⟨neg_nonneg.mpr (le_of_not_ge hx), ?_⟩, ?_⟩
    · exact (lt_of_le_of_lt (neg_le_abs _) hxBound).le
    · simp only [smul_zero, zero_add]
      ext i
      fin_cases i
      · simp
      · simp [hz1]

/-- Fixed actual anchor segments cover the reference within the support ball.
Exterior fixation therefore retains the complete literal ray or axis. -/
private theorem actualFixedAnchorSegmentsPreserveWholeReference
    (F : Plane ≃ₜ Plane) (anchorLoop : Bool) {R : ℝ} (hR : R < 1)
    (houtside : ∀ x, x ∉ ball (0 : Plane) R → F x = x)
    (hpositive : ∀ x ∈ segment ℝ (0 : Plane) (Plane.mk 1 0), F x = x)
    (hnegative : anchorLoop = true →
      ∀ x ∈ segment ℝ (0 : Plane) (Plane.mk (-1) 0), F x = x) :
    (∀ x ∈ {z : Plane | z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ z 0)}, F x = x) ∧
      F '' {z : Plane | z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ z 0)} =
        {z : Plane | z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ z 0)} := by
  have hfix : ∀ x ∈ {z : Plane | z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ z 0)}, F x = x := by
    intro x hx
    by_cases hxBall : x ∈ ball (0 : Plane) R
    · have hxNorm : ‖x‖ < R := by simpa only [mem_ball, dist_zero_right] using hxBall
      rcases actualReferenceInsideUnitBallHasAnchorArm anchorLoop hx (hxNorm.trans hR) with hp | ⟨hl, hn⟩
      · exact hpositive x hp
      · exact hnegative hl x hn
    · exact houtside x hxBall
  refine ⟨hfix, ?_⟩
  apply Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    rw [hfix x hx]
    exact hx
  · intro z hz
    exact ⟨z, hz, hfix z hz⟩

/-- Select an actual point of the chosen convex source sector away from every
indexed old direction. The sector point is constructed, not supplied as a certificate. -/
private theorem actualOpenSectorPointAvoidingFiniteDirections
    {K : Type} [Fintype K] (v : K → Plane)
    {U : Set Plane} (hU : IsOpen U) {x : Plane} (hx : x ∈ U) (hx1 : x 1 ≠ 0) :
    ∃ q ∈ U, q 1 = x 1 ∧ ∀ (k : K) (r : ℝ), q ≠ r • v k := by
  classical
  let f : ℝ → Plane := fun t => Plane.mk t (x 1)
  have hfc : Continuous f := by fun_prop
  let T : Set ℝ := range (fun k => (v k 0 / v k 1) * x 1)
  have hT : T.Finite := finite_range _
  have hxEq : f (x 0) = x := by
    ext i
    fin_cases i <;> simp [f]
  have hW : IsOpen (f ⁻¹' U) := hU.preimage hfc
  have hWne : (f ⁻¹' U).Nonempty := ⟨x 0, by simpa only [mem_preimage, hxEq] using hx⟩
  obtain ⟨t, htNot, htU⟩ := (hT.countable.dense_compl ℝ).exists_mem_open hW hWne
  refine ⟨f t, htU, rfl, ?_⟩
  intro k r he
  have he0 : t = r * v k 0 := by
    have hh := congrArg (fun z : Plane => z 0) he
    simpa [f] using hh
  have he1 : x 1 = r * v k 1 := by
    have hh := congrArg (fun z : Plane => z 1) he
    simpa [f] using hh
  have hv1 : v k 1 ≠ 0 := by intro hh; simp [hh] at he1; exact hx1 he1
  have htSlope : t = (v k 0 / v k 1) * x 1 := by
    rw [he0, he1]
    field_simp [hv1]
  apply htNot
  exact ⟨k, htSlope.symm⟩

/-- Genuine source prefix replacement inside an actual convex fan cell. It fixes
all cell-exterior points and chooses its new straight germ away from indexed old rays. -/
private theorem actualOldAvoidingConvexSectorSourcePrefix
    {K : Type} [Fintype K] (v : K → Plane)
    (Q : Set Plane) (hclosed : IsClosed Q) (hconv : Convex ℝ Q)
    (hne : (interior Q).Nonempty) (hbounded : Bornology.IsBounded Q)
    (haxis : ∀ x : Plane, x 1 = 0 → x ∉ interior Q)
    (h0front : (0 : Plane) ∈ frontier Q)
    {a : Plane} (α : Path (0 : Plane) a) (hα : Function.Injective α)
    (ha : a ∉ Q) (c₀ : CurveComplex.Interval) (hc₀ : 0 < c₀)
    (hAArc : IsArcBetween (α '' Icc 0 c₀) 0 (α c₀))
    (hbfront : α c₀ ∈ frontier Q)
    (hAi : (α '' Icc 0 c₀) \ {0, α c₀} ⊆ interior Q) :
    ∃ F : Plane ≃ₜ Plane, F 0 = 0 ∧
      (∀ x, x ∉ interior Q → F x = x) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ F '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          segment ℝ 0 q ∩ {x : Plane | x 1 = 0} = {0} ∧
          ∀ k, segment ℝ 0 q ∩
            {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • v k} = {0} := by
  classical
  obtain ⟨x, hx⟩ := hne
  have hne : (interior Q).Nonempty := ⟨x, hx⟩
  have hx1 : x 1 ≠ 0 := fun he => haxis x he hx
  let b := α c₀
  let allv : Option K → Plane := fun k => Option.casesOn k b v
  obtain ⟨q, hqi, hq1, hqv⟩ := actualOpenSectorPointAvoidingFiniteDirections
    allv isOpen_interior hx hx1
  have hq0 : q ≠ 0 := by
    intro he
    apply hx1
    simpa [he] using hq1.symm
  have hb0 : b ≠ 0 := by
    intro he
    have ht0 : c₀ = 0 := hα (he.trans α.source.symm)
    exact (ne_of_gt hc₀) ht0
  have hqb : q ≠ b := by simpa [allv] using hqv none 1
  have hind : ∀ r t : ℝ, r • q = t • b → r = 0 ∧ t = 0 := by
    intro r t he
    by_cases hr : r = 0
    · refine ⟨hr, ?_⟩
      have ht : t • b = 0 := by simpa [hr] using he.symm
      exact (smul_eq_zero.mp ht).resolve_right hb0
    · exfalso
      apply hqv none (r⁻¹ * t)
      have hh := congrArg (fun z : Plane => r⁻¹ • z) he
      simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using hh
  have hinter : segment ℝ (0 : Plane) q ∩ segment ℝ q b = {q} := by
    apply Subset.antisymm
    · rintro z ⟨⟨r,t,hr,ht,hrt,hzt⟩,⟨u,w,hu,hw,huw,hzw⟩⟩
      have he : (t - u) • q = w • b := by
        calc
          (t-u) • q = (r • (0 : Plane) + t • q) - u • q := by module
          _ = w • b := by rw [hzt, ← hzw]; module
      have hw0 := (hind _ _ he).2
      have hu1 : u = 1 := by linarith
      have hzq : z = q := by rw [← hzw, hw0, hu1]; simp
      exact hzq
    · intro z hz
      have he : z = q := hz
      subst z
      exact ⟨right_mem_segment ℝ 0 q, left_mem_segment ℝ q b⟩
  obtain ⟨hNArc, _⟩ := actualJoinedSourceArmsArePointedArc
    (Path.segment (0 : Plane) q) (Path.segment q b)
    (Path.segment_injective_of_ne hq0.symm)
    (Path.segment_injective_of_ne hqb)
    (by simpa only [Path.range_segment] using hinter)
  simp only [Path.range_segment] at hNArc
  let N := segment ℝ (0 : Plane) q ∪ segment ℝ q b
  change IsArcBetween N 0 b at hNArc
  have h0Q : (0 : Plane) ∈ Q := hclosed.frontier_subset h0front
  have hbQ : b ∈ Q := hclosed.frontier_subset hbfront
  have hNi : N \ {0,b} ⊆ interior Q := by
    intro z hz
    have hz0 : z ≠ 0 := fun he => hz.2 (by simp [he])
    have hzb : z ≠ b := fun he => hz.2 (by simp [he])
    by_cases hzq : z = q
    · simpa only [hzq] using hqi
    · rcases hz.1 with hz | hz
      · exact hconv.openSegment_self_interior_subset_interior h0Q hqi
          (mem_openSegment_of_ne_left_right (Ne.symm hz0) (Ne.symm hzq) hz)
      · exact hconv.openSegment_interior_self_subset_interior hqi hbQ
          (mem_openSegment_of_ne_left_right (Ne.symm hzq) hzb.symm hz)
  obtain ⟨E, hEi, hEQ, hEf, hJ⟩ := convex_sector_ambient_square_chart Q hconv hclosed hne hbounded
  have hclInt : closure (interior Q) = Q :=
    (hconv.closure_interior_eq_closure_of_nonempty_interior hne).trans hclosed.closure_eq
  have hfront : frontier (interior Q) = frontier Q := by
    simp only [frontier, isOpen_interior.interior_eq, hclInt, hclosed.closure_eq]
  have hInside : interior Q = inside (frontier Q) :=
    bounded_jordan_frontier_region_eq_inside hJ isOpen_interior
      (hconv.interior.isConnected hne) (hbounded.subset interior_subset) hfront
  obtain ⟨e⟩ := exists_arcHomeo hAArc hNArc
  obtain ⟨F, hpoint, hFN, hfix⟩ :=
    jordan_sector_prescribed_crosscut_ambient_extension hJ h0front hbfront hAArc hNArc
      (by simpa only [← hInside] using hAi)
      (by simpa only [← hInside] using hNi) e
  have hfixQ : ∀ x, x ∉ interior Q → F x = x := by simpa only [← hInside] using hfix
  have hF0 : F 0 = 0 := hfixQ 0 ((hclosed.frontier_eq ▸ h0front).2)
  have hFa : F a = a := hfixQ a (fun hh => ha (interior_subset hh))
  have hqFa : q ≠ F a := by
    rw [hFa]
    intro he
    exact ha (he ▸ interior_subset hqi)
  have hfullArc : IsArcBetween (F '' range α) 0 (F a) := by
    have hh := (actualInjectivePathIsArc α hα).image_of_injOn
      (S := Set.univ) (subset_univ _) F.continuous.continuousOn F.injective.injOn
    simpa only [hF0] using hh
  have hsub : segment ℝ (0 : Plane) q ⊆ F '' range α := by
    apply (show segment ℝ (0 : Plane) q ⊆ N from subset_union_left).trans
    rw [← hFN]
    exact image_mono (image_subset_range _ _)
  obtain ⟨c, hc, hc1, hcim⟩ := actualSourcePrefixPullback α hα F
    (segment ℝ (0 : Plane) q) (F '' range α) hfullArc
    (by simpa only [hF0] using isArcBetween_segment hq0.symm)
    Subset.rfl hsub (hsub (right_mem_segment ℝ 0 q))
    (by simpa only [hF0] using hq0) hqFa
  have hsegAxis : segment ℝ (0 : Plane) q ∩ {z : Plane | z 1 = 0} = {0} := by
    apply Subset.antisymm
    · intro z hz
      by_cases hz0 : z = 0
      · exact hz0
      · apply False.elim
        apply haxis z hz.2
        by_cases hzq : z = q
        · simpa only [hzq] using hqi
        · exact hconv.openSegment_self_interior_subset_interior h0Q hqi
            (mem_openSegment_of_ne_left_right (Ne.symm hz0) (Ne.symm hzq) hz.1)
    · intro z hz
      have hz0 : z = 0 := hz
      subst z
      exact ⟨left_mem_segment ℝ 0 q, by simp⟩
  exact ⟨F, hF0, hfixQ, c, hc, hc1, q, hq0, hcim, hsegAxis,
    fun k => actualGermSegmentAvoidingNoncollinearRay (hqv (some k))⟩

#print axioms actualOldAvoidingConvexSectorSourcePrefix

#print axioms actualOpenSectorPointAvoidingFiniteDirections

#print axioms actualReferenceInsideUnitBallHasAnchorArm
#print axioms actualFixedAnchorSegmentsPreserveWholeReference

#print axioms actualTransportedSourceAvoidsLiteralReference
#print axioms actualSecondSourceAvoidsFirstRadialPrefix

#print axioms actualOneSourceReferenceRelativeRadialization

#print axioms actualAxisRelativeOneArm

#print axioms actualAxisRelativeOriginalArmSquare

#print axioms actualNegationAxisImage
#print axioms actualAxisRelativeProperArmSquare

#print axioms actualAxisAvoidingSourceSelectsHalfPlane

#print axioms actualAxisRelativeUpperArmSquare

#print axioms actualUpperHalfSquareGeometry
#print axioms actualPositiveTwoSegmentTarget

#print axioms actualGermSegmentAvoidingNoncollinearRay
#print axioms actualPositiveRayRelativeOneArm

#print axioms actualPositiveScaleReferenceMembership
#print axioms actualPositiveScaleReferenceImage

#print axioms actualRelativeSquareWindow

#print axioms actualInjectivePathIsArc
#print axioms actualPositiveRayRelativeOriginalArmSquare

#print axioms actualPositiveRayRelativeOneArmSquare

#print axioms actualPositiveReferenceSquareArm

#print axioms actualArcBetweenHasInjectivePath
#print axioms actualFixedArmIntersectsReferenceAvoidingSource

#print axioms actualScaledTargetGermDirection

#print axioms actualSourcePrefixPullback

#print axioms actualTwoSegmentTargetAvoidsReference

#print axioms actualSimpleTwoSegmentSourceTarget

#print axioms actualTargetGermDirectionCompatibleWithExit

#print axioms actualReferenceAvoidingFirstExitSourceArm

#print axioms actualJoinedSourceArmsArePointedArc

#print axioms actualUpperGermSegmentAvoidingFiniteRays

#print axioms actualPointedReplacementPreservesCommonArm
#print axioms actualReferenceImageOfPreservedLocalArm
#print axioms actualOtherArmImageOfJoinedReplacement
#print axioms actualUpperDirectionAvoidingFiniteRays
#print axioms actualAnchorRelativeJoinedSourceCrosscutReplacement

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel

private theorem actualFixedConvexFanFirstExit {J K : Type} (Q : K → Set Plane) (v : J → Plane)
    (R : ℝ) (hR : 0 < R)
    (hclosed : ∀ k, IsClosed (Q k)) (hconvex : ∀ k, Convex ℝ (Q k))
    (hzero : ∀ k, (0:Plane) ∈ Q k)
    (hinside : ∀ k, Q k ⊆ closedBall (0:Plane) R)
    (hcover : closedBall (0:Plane) R ⊆ ⋃ k, Q k)
    (hdisj : Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l))))
    (hfront : ∀ k, frontier (Q k) ⊆ Metric.sphere (0:Plane) R ∪ ⋃ j, segment ℝ (0:Plane) (v j))
    (hv : ∀ j, ‖v j‖ = R)
    {a : Plane} (α : Path (0:Plane) a) (hα : Function.Injective α)
    (ha : a ∉ closedBall (0:Plane) R)
    (havoid : ∀ t : CurveComplex.Interval, 0 < t.val → α t ∉ ⋃ j, segment ℝ (0:Plane) (v j)) :
    ∃ (c : CurveComplex.Interval) (k : K), 0 < c.val ∧ c.val < 1 ∧
      ‖α c‖ = R ∧ α c ∈ frontier (Q k) ∧
      IsArcBetween (α '' Icc 0 c) 0 (α c) ∧
      (α '' Icc 0 c) \ {0,α c} ⊆ interior (Q k) ∧
      segment ℝ (0:Plane) (α c) \ {0,α c} ⊆ interior (Q k) := by
  classical
  have select (U : K → Set Plane) (hU : ∀ k, IsOpen (U k))
      (hd : Pairwise (fun i j => Disjoint (U i) (U j)))
      (c t₀ : CurveComplex.Interval) (ht₀ : t₀ ∈ Ioo (0 : CurveComplex.Interval) c)
      (hc : ∀ t ∈ Ioo (0 : CurveComplex.Interval) c, α t ∈ ⋃ k, U k) :
      ∃ k, ∀ t ∈ Ioo (0 : CurveComplex.Interval) c, α t ∈ U k := by
    obtain ⟨k,hk⟩ := mem_iUnion.mp (hc t₀ ht₀)
    let W := ⋃ (j : K) (_ : j ≠ k), U j
    have hW : IsOpen W := isOpen_iUnion (fun j => isOpen_iUnion (fun _ => hU j))
    have hdW : Disjoint (U k) W := by
      apply Set.disjoint_left.mpr
      intro x hx hxW
      obtain ⟨j,hj⟩ := mem_iUnion.mp hxW
      obtain ⟨hne,hxj⟩ := mem_iUnion.mp hj
      exact Set.disjoint_left.mp (hd hne.symm) hx hxj
    have hp : α '' Ioo (0 : CurveComplex.Interval) c ⊆ U k ∪ W := by
      rintro x ⟨t,ht,rfl⟩
      obtain ⟨j,hj⟩ := mem_iUnion.mp (hc t ht)
      by_cases he : j = k
      · exact Or.inl (he ▸ hj)
      · exact Or.inr (mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨he,hj⟩⟩)
    have hsel : α '' Ioo (0 : CurveComplex.Interval) c ⊆ U k :=
      (isPreconnected_Ioo.image α α.continuous.continuousOn).subset_left_of_subset_union
        (hU k) hW hdW hp ⟨α t₀,⟨⟨t₀,ht₀,rfl⟩,hk⟩⟩
    exact ⟨k,fun t ht => hsel ⟨t,ht,rfl⟩⟩
  have nonsphere {x : Plane} (hb : x ∈ ball (0:Plane) R) : x ∉ Metric.sphere (0:Plane) R := by
    simp only [mem_ball,mem_sphere,dist_zero_right] at *
    exact ne_of_lt hb
  have haopen : a ∉ ball (0:Plane) R := fun hm => ha (ball_subset_closedBall hm)
  obtain ⟨c,hc,γ,hex,hγ,himage,hbefore⟩ :=
    CurveComplex.SeedProbeHeaders.embedded_first_exit_prefix α hα
      (ball (0:Plane) R) isOpen_ball (by simpa using hR) haopen
  have heR : ‖α c‖ = R := by
    rw [frontier_ball (0:Plane) (ne_of_gt hR)] at hex
    simpa only [mem_sphere,dist_zero_right] using hex
  have hc1 : c < 1 := by
    apply lt_of_le_of_ne c.property.2
    intro he
    apply ha
    rw [show c = 1 from Subtype.ext he] at heR
    simpa only [α.target,mem_closedBall,dist_zero_right] using heR.le
  have hrawbefore : ∀ t : CurveComplex.Interval, t < c → α t ∈ ball (0:Plane) R := by
    obtain ⟨d,hd,hdf,hdb⟩ := CurveComplex.path_first_exit_frontier α
      (ball (0:Plane) R) isOpen_ball (by simpa using hR) haopen
    have hdle : d ≤ c := by
      by_contra hn
      have hm := hdb c (lt_of_not_ge hn)
      exact (show α c ∉ ball (0:Plane) R from by simpa only [frontier,isOpen_ball.interior_eq] using hex.2) hm
    have hcd : c ≤ d := by
      by_contra hn
      have hdγ : α d ∈ range γ := by
        rw [himage]
        exact ⟨d,⟨d.property.1,(lt_of_not_ge hn).le⟩,rfl⟩
      obtain ⟨s,hs⟩ := hdγ
      have hs1 : s < 1 := by
        apply lt_of_le_of_ne s.property.2
        intro he
        have hsone : s = 1 := Subtype.ext he
        have hdc : d = c := hα (hs.symm.trans (hsone ▸ γ.target))
        exact (ne_of_lt (lt_of_not_ge hn)) hdc
      have hm := hbefore s hs1
      rw [hs] at hm
      exact (show α d ∉ ball (0:Plane) R from by simpa only [frontier,isOpen_ball.interior_eq] using hdf.2) hm
    exact fun t ht => hdb t (ht.trans_le hcd)
  have hcellcover : ∀ t ∈ Ioo (0 : CurveComplex.Interval) c, α t ∈ ⋃ k, interior (Q k) := by
    intro t ht
    have hb := hrawbefore t ht.2
    obtain ⟨k,hk⟩ := mem_iUnion.mp (hcover (ball_subset_closedBall hb))
    refine mem_iUnion.mpr ⟨k,?_⟩
    by_contra hn
    have hfr : α t ∈ frontier (Q k) := by
      rw [(hclosed k).frontier_eq]
      exact ⟨hk,hn⟩
    rcases hfront k hfr with hs | hf
    · exact (nonsphere hb) hs
    · exact havoid t ht.1 hf
  let t₀ : CurveComplex.Interval := ⟨c.val/2,by constructor <;> nlinarith [c.property.1,c.property.2]⟩
  have ht₀ : t₀ ∈ Ioo (0 : CurveComplex.Interval) c := by
    have hcr : 0 < c.val := hc
    constructor
    · change 0 < c.val/2
      linarith
    · change c.val/2 < c.val
      linarith
  obtain ⟨k,hk⟩ := select (fun k => interior (Q k)) (fun _ => isOpen_interior)
    hdisj c t₀ ht₀ hcellcover
  have heQ : α c ∈ Q k := by
    have hcc : c ∈ closure (Ioo (0 : CurveComplex.Interval) c : Set CurveComplex.Interval) := by
      rw [closure_Ioo (show (0 : CurveComplex.Interval) ≠ c from ne_of_lt hc)]
      exact ⟨hc.le,le_rfl⟩
    have hsub : Ioo (0 : CurveComplex.Interval) c ⊆ α ⁻¹' Q k := by
      intro t ht
      change α t ∈ Q k
      exact interior_subset (hk t ht)
    exact ((hclosed k).preimage α.continuous).closure_subset_iff.mpr hsub hcc
  have hefront : α c ∈ frontier (Q k) := by
    rw [(hclosed k).frontier_eq]
    refine ⟨heQ,?_⟩
    intro hm
    have hb : α c ∈ interior (closedBall (0:Plane) R) := interior_mono (hinside k) hm
    rw [interior_closedBall (0:Plane) (ne_of_gt hR)] at hb
    exact (nonsphere hb) (by simpa only [mem_sphere,dist_zero_right] using heR)
  have hArc : IsArcBetween (α '' Icc 0 c) 0 (α c) := by
    refine ⟨γ.extend,γ.continuous_extend.continuousOn,?_,?_,γ.extend_zero,γ.extend_one⟩
    · intro s hs t ht he
      rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
      exact congrArg Subtype.val (hγ he)
    · exact (γ.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))).trans himage
  refine ⟨c,k,hc,hc1,heR,hefront,hArc,?_,?_⟩
  · rintro x ⟨⟨t,ht,rfl⟩,hne⟩
    have ht0 : (0 : CurveComplex.Interval) < t := by
      apply lt_of_le_of_ne t.property.1
      intro he
      have he0 : t = 0 := Subtype.ext he.symm
      exact hne (by simp [he0,α.source])
    have htc : t < c := by
      apply lt_of_le_of_ne ht.2
      intro he
      exact hne (by simp [he])
    exact hk t ⟨ht0,htc⟩
  · intro x hx
    have hxQ : x ∈ Q k := (hconvex k).segment_subset (hzero k) heQ hx.1
    have hxne0 : x ≠ 0 := by intro he; exact hx.2 (by simp [he])
    have hxnee : x ≠ α c := by intro he; exact hx.2 (by simp [he])
    have hxo : x ∈ openSegment ℝ (0:Plane) (α c) :=
      mem_openSegment_of_ne_left_right hxne0.symm hxnee.symm hx.1
    obtain ⟨a,b,ha,hb,hab,hxb⟩ := hxo
    have hxb' : x = b • α c := by simpa using hxb.symm
    have hxball : x ∈ ball (0:Plane) R := by
      rw [mem_ball,dist_zero_right,hxb',norm_smul,Real.norm_eq_abs,abs_of_pos hb,heR]
      have hb1 : b < 1 := by linarith
      nlinarith
    by_contra hn
    have hxfr : x ∈ frontier (Q k) := by
      rw [(hclosed k).frontier_eq]
      exact ⟨hxQ,hn⟩
    rcases hfront k hxfr with hs | hf
    · exact (nonsphere hxball) hs
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hf
      have hejne : α c ≠ v j := by
        intro he
        apply havoid c hc
        exact mem_iUnion.mpr ⟨j,he ▸ right_mem_segment ℝ 0 (v j)⟩
      have hmeet := LeanEval.Topology.ClassificationOfSurfaces.Moise.radial_segments_inter
        (center := (0:Plane)) (p := α c) (q := v j) (radius := R) hR
        (by simpa only [dist_zero_right] using heR)
        (by simpa only [dist_zero_right] using hv j) hejne
      have hxzero : x ∈ ({0} : Set Plane) := hmeet ▸ ⟨hx.1,hj⟩
      exact hxne0 hxzero
#print axioms actualFixedConvexFanFirstExit

private theorem actualFixedConvexFanInsertCells {K : Type} (Q : K → Set Plane) (F : Set Plane)
    (R : ℝ) (hR : 0 < R)
    (hclosed : ∀ k, IsClosed (Q k)) (hconvex : ∀ k, Convex ℝ (Q k))
    (hzero : ∀ k, (0:Plane) ∈ Q k) (hinside : ∀ k, Q k ⊆ closedBall (0:Plane) R)
    (hcover : closedBall (0:Plane) R ⊆ ⋃ k, Q k)
    (hdisj : Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l))))
    (hfront : ∀ k, frontier (Q k) ⊆ Metric.sphere (0:Plane) R ∪ F)
    (hcellne : ∀ k, (interior (Q k)).Nonempty)
    (hcenter : ∀ k, (0:Plane) ∈ frontier (Q k))
    (hfan : ∀ k, Disjoint (interior (Q k)) F)
    (hsupport : ∀ k, ∃ L : Plane →L[ℝ] ℝ,
      (∀ x ∈ Q k, 0 ≤ L x) ∧ (∀ x ∈ Q k, L x = 0 → x ∈ F))
    (k₀ : K) (e : Plane) (heQ : e ∈ Q k₀) (heR : ‖e‖ = R) (heF : e ∉ F)
    (hproper : segment ℝ (0:Plane) e \ {0,e} ⊆ interior (Q k₀)) :
    ∃ (K' : Type) (Q' : K' → Set Plane),
      (∀ k, IsClosed (Q' k)) ∧ (∀ k, Convex ℝ (Q' k)) ∧
      (∀ k, (0:Plane) ∈ Q' k) ∧ (∀ k, Q' k ⊆ closedBall (0:Plane) R) ∧
      (closedBall (0:Plane) R ⊆ ⋃ k, Q' k) ∧
      (Pairwise (fun k l => Disjoint (interior (Q' k)) (interior (Q' l)))) ∧
      (∀ k, frontier (Q' k) ⊆ Metric.sphere (0:Plane) R ∪ (F ∪ segment ℝ (0:Plane) e)) ∧
      (∀ k, (interior (Q' k)).Nonempty) ∧ (∀ k, (0:Plane) ∈ frontier (Q' k)) ∧
      (∀ k, Disjoint (interior (Q' k)) (F ∪ segment ℝ (0:Plane) e)) ∧
      (∀ k, ∃ L : Plane →L[ℝ] ℝ,
        (∀ x ∈ Q' k, 0 ≤ L x) ∧
        (∀ x ∈ Q' k, L x = 0 → x ∈ F ∪ segment ℝ (0:Plane) e)) := by
  classical
  have halfInt (e : Plane) (he : e ≠ 0) :
      interior {x : Plane | 0 ≤ Plane.det e x} = {x | 0 < Plane.det e x} ∧
      interior {x : Plane | Plane.det e x ≤ 0} = {x | Plane.det e x < 0} := by
    let D : Plane →ₗ[ℝ] ℝ := {
      toFun := fun x => Plane.det e x
      map_add' := Plane.det_add_right e
      map_smul' := fun r x => Plane.det_smul_right r e x }
    have hcont : Continuous D := by
      change Continuous (fun x : Plane => Plane.det e x)
      unfold Plane.det
      exact (continuous_const.mul (Plane.continuous_coord 1)).sub
        (continuous_const.mul (Plane.continuous_coord 0))
    have hnorm : ‖e‖^2 ≠ 0 := ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr he))
    have hsurj : Function.Surjective D := by
      intro r
      refine ⟨(r / ‖e‖^2) • Plane.perp e,?_⟩
      change Plane.det e ((r / ‖e‖^2) • Plane.perp e) = r
      rw [Plane.det_smul_right,Plane.det_perp_self]
      exact div_mul_cancel₀ r hnorm
    have hopen : IsOpenMap D := D.isOpenMap_of_finiteDimensional hsurj
    constructor
    · change interior (D ⁻¹' Ici (0:ℝ)) = D ⁻¹' Ioi (0:ℝ)
      rw [← hopen.preimage_interior_eq_interior_preimage hcont,interior_Ici]
    · change interior (D ⁻¹' Iic (0:ℝ)) = D ⁻¹' Iio (0:ℝ)
      rw [← hopen.preimage_interior_eq_interior_preimage hcont,interior_Iic]
  have hen : e ≠ 0 := by intro he; simp [he] at heR; linarith
  obtain ⟨L,hL,hker⟩ := hsupport k₀
  have heL : 0 < L e := lt_of_le_of_ne (hL e heQ) (fun hz => heF (hker e heQ hz.symm))
  let A := Q k₀ ∩ {x | 0 ≤ Plane.det e x}
  let B := Q k₀ ∩ {x | Plane.det e x ≤ 0}
  obtain ⟨hab,hinter,hca,hcb⟩ := radial_sector_determinant_split
    (Q k₀) (hconvex k₀) R hR (hinside k₀) (hzero k₀) e heQ heR L hL heL
  have hcont : Continuous (fun x : Plane => Plane.det e x) := by
    unfold Plane.det
    exact (continuous_const.mul (Plane.continuous_coord 1)).sub
      (continuous_const.mul (Plane.continuous_coord 0))
  have haClosed : IsClosed A := (hclosed k₀).inter (isClosed_le continuous_const hcont)
  have hbClosed : IsClosed B := (hclosed k₀).inter (isClosed_le hcont continuous_const)
  obtain ⟨hfa,hfb,hdab⟩ := sector_split_frontier_invariant (Q k₀) (hclosed k₀) e hen hinter
  have hhalf : (1/2:ℝ) • e ∈ segment ℝ (0:Plane) e \ {0,e} := by
    refine ⟨⟨1/2,1/2,by norm_num,by norm_num,by norm_num,by simp⟩,?_⟩
    intro hh
    have hh' : (1/2:ℝ) • e = 0 ∨ (1/2:ℝ) • e = e := by simpa using hh
    rcases hh' with hh|hh
    · exact hen ((smul_eq_zero.mp hh).resolve_left (by norm_num))
    · have hz : (-1/2:ℝ) • e = 0 := by calc
        (-1/2:ℝ) • e = (1/2:ℝ) • e - e := by module
        _ = 0 := by rw [hh,sub_self]
      exact hen ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  obtain ⟨hneA,hneB⟩ := sector_split_interiors_nonempty (Q k₀) ((1/2:ℝ) • e) e
    (hproper hhalf) hen (by simp)
  let K' := Sum {k : K // k ≠ k₀} Bool
  let Q' : K' → Set Plane := Sum.elim (fun k => Q k.val) (fun b => if b then B else A)
  have hnewclosed : ∀ k, IsClosed (Q' k) := by
    intro k
    cases k with
    | inl k => exact hclosed k.val
    | inr b => cases b; exact haClosed; exact hbClosed
  have hmona : interior A ⊆ interior (Q k₀) := interior_mono inter_subset_left
  have hmonb : interior B ⊆ interior (Q k₀) := interior_mono inter_subset_left
  have hnewzero : ∀ k, (0:Plane) ∈ Q' k := by
    intro k
    cases k with
    | inl k => exact hzero k.val
    | inr b => cases b <;> exact ⟨hzero k₀,by simp [Plane.det]⟩
  have newSubsetOld : ∀ k : K', ∃ j : K, Q' k ⊆ Q j := by
    intro k
    cases k with
    | inl k => exact ⟨k.val,Subset.refl _⟩
    | inr b => cases b <;> exact ⟨k₀,inter_subset_left⟩
  have hnewinside : ∀ k, Q' k ⊆ closedBall (0:Plane) R := by
    intro k
    obtain ⟨j,hj⟩ := newSubsetOld k
    exact hj.trans (hinside j)
  have hnewcenter : ∀ k, (0:Plane) ∈ frontier (Q' k) := by
    intro k
    rw [(hnewclosed k).frontier_eq]
    refine ⟨hnewzero k,?_⟩
    intro hi
    obtain ⟨j,hj⟩ := newSubsetOld k
    have hj0 : (0:Plane) ∉ interior (Q j) := by
      have hh : (0:Plane) ∈ Q j \ interior (Q j) := (hclosed j).frontier_eq ▸ hcenter j
      exact hh.2
    exact hj0 (interior_mono hj hi)
  have hnewdisj : Pairwise (fun k l => Disjoint (interior (Q' k)) (interior (Q' l))) := by
    intro k l hkl
    cases k with
    | inl k =>
      cases l with
      | inl l => exact hdisj (fun he => hkl (congrArg Sum.inl (Subtype.ext he)))
      | inr b => cases b; exact (hdisj k.property).mono_right hmona; exact (hdisj k.property).mono_right hmonb
    | inr b =>
      cases l with
      | inl l => cases b; exact (hdisj l.property.symm).mono_left hmona; exact (hdisj l.property.symm).mono_left hmonb
      | inr c => cases b <;> cases c
                 · exact False.elim (hkl rfl)
                 · exact hdab
                 · exact hdab.symm
                 · exact False.elim (hkl rfl)
  have hnewfan : ∀ k, Disjoint (interior (Q' k)) (F ∪ segment ℝ (0:Plane) e) := by
    intro k
    apply Set.disjoint_left.mpr
    intro x hi hx
    obtain ⟨j,hj⟩ := newSubsetOld k
    rcases hx with hf|hr
    · exact Set.disjoint_left.mp (hfan j) (interior_mono hj hi) hf
    · have hd : Plane.det e x = 0 := by
        obtain ⟨a,b,ha,hb,hab,hx⟩ := hr
        rw [← hx]
        simp
      cases k with
      | inl k =>
        by_cases hx0 : x = 0
        · have hh : x ∈ frontier (Q' (.inl k)) := hx0.symm ▸ hnewcenter (.inl k)
          have hh' : x ∈ Q' (.inl k) \ interior (Q' (.inl k)) := (hnewclosed _).frontier_eq ▸ hh
          exact hh'.2 hi
        by_cases hxe : x = e
        · have hb : e ∈ ball (0:Plane) R := by
            have hh := interior_mono (hinside k.val) (show x ∈ interior (Q k.val) from hi)
            rw [interior_closedBall (0:Plane) (ne_of_gt hR),hxe] at hh
            exact hh
          have hh : ‖e‖ < R := by simpa only [mem_ball,dist_zero_right] using hb
          exact (ne_of_lt hh) heR
        have hip : x ∈ interior (Q k₀) := hproper ⟨hr,by simpa using And.intro hx0 hxe⟩
        exact Set.disjoint_left.mp (hdisj k.property) hi hip
      | inr b =>
        cases b
        · have hp := interior_mono (show A ⊆ {x | 0 ≤ Plane.det e x} from inter_subset_right) hi
          rw [(halfInt e hen).1] at hp
          exact (ne_of_gt (show 0 < Plane.det e x from hp)) hd
        · have hn := interior_mono (show B ⊆ {x | Plane.det e x ≤ 0} from inter_subset_right) hi
          rw [(halfInt e hen).2] at hn
          exact (ne_of_lt (show Plane.det e x < 0 from hn)) hd
  refine ⟨K',Q',hnewclosed,?_,hnewzero,hnewinside,?_,hnewdisj,?_,?_,hnewcenter,hnewfan,?_⟩
  · intro k
    cases k with
    | inl k => exact hconvex k.val
    | inr b => cases b; exact hca; exact hcb
  · intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover hx)
    by_cases hje : j = k₀
    · subst j
      have hxAB : x ∈ A ∪ B := hab.symm ▸ hj
      rcases hxAB with hxA|hxB
      · exact mem_iUnion.mpr ⟨.inr false,hxA⟩
      · exact mem_iUnion.mpr ⟨.inr true,hxB⟩
    · exact mem_iUnion.mpr ⟨.inl ⟨j,hje⟩,hj⟩
  · intro k x hx
    cases k with
    | inl k =>
      rcases hfront k.val hx with hs|hf
      · exact Or.inl hs
      · exact Or.inr (Or.inl hf)
    | inr b =>
      have hh : x ∈ frontier (Q k₀) ∪ segment ℝ (0:Plane) e := by
        cases b; exact hfa hx; exact hfb hx
      rcases hh with hfr|hr
      · rcases hfront k₀ hfr with hs|hf
        · exact Or.inl hs
        · exact Or.inr (Or.inl hf)
      · exact Or.inr (Or.inr hr)
  · intro k
    cases k with
    | inl k => exact hcellne k.val
    | inr b => cases b; exact hneA; exact hneB
  · intro k
    obtain ⟨j,hj⟩ := newSubsetOld k
    obtain ⟨Lj,hLj,hkj⟩ := hsupport j
    exact ⟨Lj,fun x hx => hLj x (hj hx),fun x hx he => Or.inl (hkj x (hj hx) he)⟩
#print axioms actualFixedConvexFanInsertCells

private theorem actualFixedAxisHalfCells (v : Plane) (R : ℝ) (hR : 0 < R) (hv : ‖v‖ = R) :
    ∃ Q : Bool → Set Plane,
      (∀ k, IsClosed (Q k)) ∧ (∀ k, Convex ℝ (Q k)) ∧
      (∀ k, (0:Plane) ∈ Q k) ∧ (∀ k, Q k ⊆ closedBall (0:Plane) R) ∧
      (closedBall (0:Plane) R ⊆ ⋃ k, Q k) ∧
      (Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l)))) ∧
      (∀ k, frontier (Q k) ⊆ Metric.sphere (0:Plane) R ∪
        (segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v))) ∧
      (∀ k, (interior (Q k)).Nonempty) ∧
      (∀ k, (0:Plane) ∈ frontier (Q k)) ∧
      (∀ k, Disjoint (interior (Q k))
        (segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v))) ∧
      (∀ k, ∃ L : Plane →L[ℝ] ℝ,
        (∀ x ∈ Q k, 0 ≤ L x) ∧
        (∀ x ∈ Q k, L x = 0 → x ∈ segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v))) := by
  have hvne : v ≠ 0 := by intro he; simp [he] at hv; linarith
  let D : Plane →ₗ[ℝ] ℝ := {
    toFun := fun x => Plane.det v x
    map_add' := Plane.det_add_right v
    map_smul' := fun r x => Plane.det_smul_right r v x }
  let L : Bool → Plane →L[ℝ] ℝ := fun b => if b then -D.toContinuousLinearMap else D.toContinuousLinearMap
  let Q : Bool → Set Plane := fun b => closedBall (0:Plane) R ∩ {x | 0 ≤ L b x}
  have hclosed : ∀ b, IsClosed (Q b) := fun b =>
    isClosed_closedBall.inter (isClosed_le continuous_const (L b).continuous)
  have hconvex : ∀ b, Convex ℝ (Q b) := by
    intro b
    apply (convex_closedBall (0:Plane) R).inter
    intro x hx y hy a b ha hb hab
    change 0 ≤ L _ (a • x + b • y)
    simp only [map_add,map_smul,smul_eq_mul]
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hzero : ∀ b, (0:Plane) ∈ Q b := by
    intro b
    exact ⟨by simpa using hR.le,by simp⟩
  have hinside : ∀ b, Q b ⊆ closedBall (0:Plane) R := fun _ => inter_subset_left
  have hlinearInt : ∀ b, interior {x | 0 ≤ L b x} = {x | 0 < L b x} := by
    intro b
    have hsurj : Function.Surjective (L b) := by
      intro r
      cases b
      · refine ⟨(r / ‖v‖^2) • Plane.perp v,?_⟩
        change Plane.det v ((r / ‖v‖^2) • Plane.perp v) = r
        rw [Plane.det_smul_right,Plane.det_perp_self]
        exact div_mul_cancel₀ r (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hvne)))
      · refine ⟨(-r / ‖v‖^2) • Plane.perp v,?_⟩
        change -Plane.det v ((-r / ‖v‖^2) • Plane.perp v) = r
        rw [Plane.det_smul_right,Plane.det_perp_self,div_mul_cancel₀ _
          (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hvne))),neg_neg]
    have hopen := (L b).toLinearMap.isOpenMap_of_finiteDimensional hsurj
    change IsOpenMap (L b) at hopen
    change interior ((L b) ⁻¹' Ici (0:ℝ)) = (L b) ⁻¹' Ioi (0:ℝ)
    rw [← hopen.preimage_interior_eq_interior_preimage (L b).continuous,interior_Ici]
  have hInt : ∀ b, interior (Q b) = ball (0:Plane) R ∩ {x | 0 < L b x} := by
    intro b
    rw [interior_inter,interior_closedBall (0:Plane) (ne_of_gt hR),hlinearInt]
  have kernelFan {x : Plane} (hx : x ∈ closedBall (0:Plane) R)
      (hdet : Plane.det v x = 0) : x ∈ segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v) := by
    obtain ⟨r,hr⟩ := (Plane.det_eq_zero_iff_smul v x hvne).mp hdet
    have hnr : |r| ≤ 1 := by
      have hh : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
      rw [hr,norm_smul,Real.norm_eq_abs,hv] at hh
      nlinarith
    rcases le_total 0 r with hp|hn
    · apply Or.inl
      rw [hr]
      have hr1 : r ≤ 1 := le_trans (le_abs_self r) hnr
      exact ⟨1-r,r,sub_nonneg.mpr hr1,hp,by ring,by simp⟩
    · apply Or.inr
      have hr1 : -r ≤ 1 := le_trans (neg_le_abs r) hnr
      have hxneg : x = (-r) • (-v) := by rw [hr]; module
      rw [hxneg]
      exact ⟨1-(-r),-r,sub_nonneg.mpr hr1,neg_nonneg.mpr hn,by ring,by simp⟩
  have hker : ∀ b x, L b x = 0 → Plane.det v x = 0 := by
    intro b x hx
    cases b
    · exact hx
    · change -Plane.det v x = 0 at hx
      exact neg_eq_zero.mp hx
  have hfanD : ∀ x ∈ segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v), Plane.det v x = 0 := by
    intro x hx
    rcases hx with hx|hx <;> obtain ⟨a,b,ha,hb,hab,hx⟩ := hx <;> rw [← hx] <;> simp [Plane.det] <;> ring
  refine ⟨Q,hclosed,hconvex,hzero,hinside,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    rcases le_total 0 (Plane.det v x) with hp|hn
    · exact mem_iUnion.mpr ⟨false,hx,hp⟩
    · exact mem_iUnion.mpr ⟨true,hx,by change 0 ≤ -Plane.det v x; linarith⟩
  · intro b c hbc
    apply Set.disjoint_left.mpr
    intro x hxb hxc
    rw [hInt b] at hxb
    rw [hInt c] at hxc
    cases b <;> cases c
    · exact hbc rfl
    · have hp : 0 < Plane.det v x := hxb.2
      have hn : 0 < -Plane.det v x := hxc.2
      linarith
    · have hn : 0 < -Plane.det v x := hxb.2
      have hp : 0 < Plane.det v x := hxc.2
      linarith
    · exact hbc rfl
  · intro b x hx
    rcases frontier_inter_subset (closedBall (0:Plane) R) {x | 0 ≤ L b x} hx with hball|hline
    · exact Or.inl ((frontier_closedBall (0:Plane) (ne_of_gt hR)) ▸ hball.1)
    · apply Or.inr
      have hxQ : x ∈ Q b := (hclosed b).closure_eq ▸ frontier_subset_closure hx
      exact kernelFan hxQ.1 (hker b x (frontier_le_subset_eq continuous_const (L b).continuous hline.2).symm)
  · intro b
    cases b
    · refine ⟨(1/2:ℝ) • Plane.perp v,?_⟩
      rw [hInt]
      constructor
      · simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),Plane.norm_perp,hv]
        linarith
      · change 0 < Plane.det v ((1/2:ℝ) • Plane.perp v)
        rw [Plane.det_smul_right,Plane.det_perp_self]
        exact mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hvne))
    · refine ⟨(-1/2:ℝ) • Plane.perp v,?_⟩
      rw [hInt]
      constructor
      · simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_neg (by norm_num : (-1/2:ℝ)<0),Plane.norm_perp,hv]
        linarith
      · change 0 < -Plane.det v ((-1/2:ℝ) • Plane.perp v)
        rw [Plane.det_smul_right,Plane.det_perp_self]
        nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hvne)]
  · intro b
    rw [(hclosed b).frontier_eq]
    refine ⟨hzero b,?_⟩
    rw [hInt b]
    rintro ⟨_,hh⟩
    simpa using hh
  · intro b
    apply Set.disjoint_left.mpr
    intro x hx hf
    rw [hInt b] at hx
    have hd := hfanD x hf
    cases b
    · have hp : 0 < Plane.det v x := hx.2
      linarith
    · have hn : 0 < -Plane.det v x := hx.2
      linarith
  · intro b
    refine ⟨L b,fun x hx => hx.2,?_⟩
    intro x hx hd
    exact kernelFan hx.1 (hker b x hd)
#print axioms actualFixedAxisHalfCells

/-- The canonical actual first exit followed by an old-avoiding target polygon.
The motion fixes the entire existing fan pointwise, not merely its labels. -/
private theorem actualOldAvoidingFixedConvexFanInsertion
    {J K L : Type} [Fintype L] (old : L → Plane)
    (Q : K → Set Plane) (v : J → Plane) (R : ℝ) (hR : 0 < R)
    (hclosed : ∀ k, IsClosed (Q k)) (hconv : ∀ k, Convex ℝ (Q k))
    (hzero : ∀ k, (0 : Plane) ∈ Q k)
    (hinside : ∀ k, Q k ⊆ closedBall (0 : Plane) R)
    (hcover : closedBall (0 : Plane) R ⊆ ⋃ k, Q k)
    (hdisj : Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l))))
    (hfront : ∀ k, frontier (Q k) ⊆ Metric.sphere (0 : Plane) R ∪ ⋃ j, segment ℝ 0 (v j))
    (hne : ∀ k, (interior (Q k)).Nonempty)
    (hcenter : ∀ k, (0 : Plane) ∈ frontier (Q k))
    (hfan : ∀ k, Disjoint (interior (Q k)) (⋃ j, segment ℝ 0 (v j)))
    (haxis : ∀ k (x : Plane), x 1 = 0 → x ∉ interior (Q k))
    (hv : ∀ j, ‖v j‖ = R)
    {a : Plane} (α : Path (0 : Plane) a) (hα : Function.Injective α)
    (ha : a ∉ closedBall (0 : Plane) R)
    (havoid : ∀ t : CurveComplex.Interval, 0 < t.val →
      α t ∉ ⋃ j, segment ℝ (0 : Plane) (v j)) :
    ∃ F : Plane ≃ₜ Plane, F 0 = 0 ∧
      (∀ x, x ∉ ball (0 : Plane) R → F x = x) ∧
      (∀ x ∈ ⋃ j, segment ℝ (0 : Plane) (v j), F x = x) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ F '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          segment ℝ 0 q ∩ {x : Plane | x 1 = 0} = {0} ∧
          ∀ l, segment ℝ 0 q ∩
            {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • old l} = {0} := by
  obtain ⟨c₀,k,hc₀,hc₁,hRexit,hb,hA,hAi,hBi⟩ :=
    actualFixedConvexFanFirstExit Q v R hR hclosed hconv hzero hinside hcover
      hdisj hfront hv α hα ha havoid
  obtain ⟨F,hF0,hfix,c,hc,hc1,q,hq,himage,hqaxis,hqold⟩ :=
    actualOldAvoidingConvexSectorSourcePrefix old (Q k) (hclosed k) (hconv k)
      (hne k) (isBounded_closedBall.subset (hinside k)) (haxis k) (hcenter k)
      α hα (fun hh => ha (hinside k hh)) c₀ hc₀ hA hb hAi
  have hfixBall : ∀ x, x ∉ ball (0 : Plane) R → F x = x := by
    intro x hx
    apply hfix
    intro hi
    have hh := interior_mono (hinside k) hi
    rw [interior_closedBall (0 : Plane) (ne_of_gt hR)] at hh
    exact hx hh
  have hfixFan : ∀ x ∈ ⋃ j, segment ℝ (0 : Plane) (v j), F x = x := by
    intro x hx
    apply hfix
    exact fun hi => Set.disjoint_left.mp (hfan k) hi hx
  exact ⟨F,hF0,hfixBall,hfixFan,c,hc,hc1,q,hq,himage,hqaxis,hqold⟩
#print axioms actualOldAvoidingFixedConvexFanInsertion

/-- Fixing a truncated genuine radius and the support exterior fixes its whole arm. -/
private theorem actualFixedTruncatedRadiusPreservesWholeArm
    (F : Plane ≃ₜ Plane) (q : Plane) (hq : q ≠ 0) (R : ℝ) (hR : 0 < R)
    (houtside : ∀ x, x ∉ ball (0 : Plane) R → F x = x)
    (hshort : ∀ x ∈ segment ℝ (0 : Plane) ((R / ‖q‖) • q), F x = x) :
    ∀ x ∈ segment ℝ (0 : Plane) q, F x = x := by
  intro x hx
  by_cases hb : x ∈ ball (0 : Plane) R
  · apply hshort
    rw [segment_eq_image] at hx ⊢
    obtain ⟨t,ht,hxt⟩ := hx
    simp only [smul_zero, zero_add] at hxt
    have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
    have hnorm : t * ‖q‖ < R := by
      rw [mem_ball, dist_zero_right, ← hxt, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg ht.1] at hb
      exact hb
    refine ⟨t * ‖q‖ / R, ⟨div_nonneg (mul_nonneg ht.1 (norm_nonneg q)) hR.le, ?_⟩, ?_⟩
    · exact (div_le_one hR).mpr hnorm.le
    · simp only [smul_zero, zero_add, smul_smul]
      have he : (t * ‖q‖ / R) * (R / ‖q‖) = t := by field_simp
      rw [he]
      exact hxt
  · exact houtside x hb
#print axioms actualFixedTruncatedRadiusPreservesWholeArm

/-- The two actual opposite anchor radii cover precisely the anchor axis in the ball. -/
private theorem actualAxisBallCoveredByOppositeArms
    (R : ℝ) (hR : 0 < R) {x : Plane} (hx : x ∈ closedBall (0 : Plane) R)
    (haxis : x 1 = 0) :
    x ∈ segment ℝ (0 : Plane) (Plane.mk R 0) ∪
      segment ℝ (0 : Plane) (-Plane.mk R 0) := by
  have hn : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hcoord : |x 0| ≤ R :=
    (show |x 0| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0).trans hn
  by_cases hs : 0 ≤ x 0
  · apply Or.inl
    rw [segment_eq_image]
    refine ⟨x 0 / R, ⟨div_nonneg hs hR.le,
      (div_le_one hR).mpr ((le_abs_self (x 0)).trans hcoord)⟩, ?_⟩
    simp only [smul_zero, zero_add]
    ext i
    fin_cases i
    · change (x 0 / R) * R = x 0
      field_simp
    · change (x 0 / R) * 0 = x 1
      simp [haxis]
  · apply Or.inr
    rw [segment_eq_image]
    refine ⟨-(x 0) / R, ⟨div_nonneg (by linarith) hR.le,
      (div_le_one hR).mpr ((neg_le_abs (x 0)).trans hcoord)⟩, ?_⟩
    simp only [smul_zero, zero_add]
    ext i
    fin_cases i
    · change (-(x 0) / R) * (-R) = x 0
      field_simp
    · change (-(x 0) / R) * (-0) = x 1
      simp [haxis]
#print axioms actualAxisBallCoveredByOppositeArms

/-- Actual opposite anchor radii on every cell boundary exclude the whole axis
from every cell interior; no global empty-disk assumption is needed. -/
private theorem actualOppositeAxisFanExcludesCellInterior
    (R : ℝ) (hR : 0 < R) (Q F : Set Plane)
    (hinside : Q ⊆ closedBall (0 : Plane) R)
    (hfan : Disjoint (interior Q) F)
    (hanchor : segment ℝ (0 : Plane) (Plane.mk R 0) ∪
      segment ℝ (0 : Plane) (-Plane.mk R 0) ⊆ F) :
    ∀ x : Plane, x 1 = 0 → x ∉ interior Q := by
  intro x hx hi
  have hb : x ∈ closedBall (0 : Plane) R := hinside (interior_subset hi)
  have hf : x ∈ F := hanchor (actualAxisBallCoveredByOppositeArms R hR hb hx)
  exact Set.disjoint_left.mp hfan hi hf
#print axioms actualOppositeAxisFanExcludesCellInterior

/-- Two actual supported source motions retain the prescribed closed support ball. -/
private theorem actualComposeSupportedMotionsClosedBall
    (G H : Plane ≃ₜ Plane) (R S : ℝ) (hR : 0 < R) (hS : 0 < S)
    (V : Set Plane) (hRV : closedBall (0 : Plane) R ⊆ V)
    (hSV : closedBall (0 : Plane) S ⊆ V)
    (hG0 : G 0 = 0) (hH0 : H 0 = 0)
    (hG : ∀ x, x ∉ ball (0 : Plane) R → G x = x)
    (hH : ∀ x, x ∉ ball (0 : Plane) S → H x = x) :
    0 < max R S ∧ closedBall (0 : Plane) (max R S) ⊆ V ∧
      (G.trans H) 0 = 0 ∧
      ∀ x, x ∉ ball (0 : Plane) (max R S) → (G.trans H) x = x := by
  refine ⟨lt_of_lt_of_le hR (le_max_left R S), ?_, ?_, ?_⟩
  · rcases le_total R S with hrs | hsr
    · simpa only [max_eq_right hrs] using hSV
    · simpa only [max_eq_left hsr] using hRV
  · change H (G 0) = 0
    rw [hG0,hH0]
  · intro x hx
    change H (G x) = x
    rw [hG x (fun hi => hx ((ball_subset_ball (le_max_left R S)) hi))]
    exact hH x (fun hi => hx ((ball_subset_ball (le_max_right R S)) hi))
#print axioms actualComposeSupportedMotionsClosedBall

/-- Actual three convex cells determined by the entire anchor axis and a genuine
nonhorizontal source radius. The extra radius is the already-produced source germ. -/
private theorem actualAxisAndRadiusConvexCells
    (R : ℝ) (hR : 0 < R) (e : Plane) (he : ‖e‖ = R) (heaxis : e 1 ≠ 0) :
    let F := (segment ℝ (0 : Plane) (Plane.mk R 0) ∪
      segment ℝ (0 : Plane) (-Plane.mk R 0)) ∪ segment ℝ (0 : Plane) e
    ∃ (K : Type) (Q : K → Set Plane),
      (∀ k, IsClosed (Q k)) ∧ (∀ k, Convex ℝ (Q k)) ∧
      (∀ k, (0 : Plane) ∈ Q k) ∧
      (∀ k, Q k ⊆ closedBall (0 : Plane) R) ∧
      (closedBall (0 : Plane) R ⊆ ⋃ k, Q k) ∧
      Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l))) ∧
      (∀ k, frontier (Q k) ⊆ Metric.sphere (0 : Plane) R ∪ F) ∧
      (∀ k, (interior (Q k)).Nonempty) ∧
      (∀ k, (0 : Plane) ∈ frontier (Q k)) ∧
      (∀ k, Disjoint (interior (Q k)) F) := by
  let a := Plane.mk R 0
  have ha : ‖a‖ = R := by
    simp [a, EuclideanSpace.norm_eq, Fin.sum_univ_two, Plane.mk,
      Real.sqrt_sq (le_of_lt hR)]
  obtain ⟨Q,hclosed,hconv,hzero,hinside,hcover,hdisj,hfront,hne,hcenter,hfan,hsupport⟩ :=
    actualFixedAxisHalfCells a R hR ha
  let v : Bool → Plane := fun b => if b then -a else a
  have hfanEq : (⋃ b, segment ℝ (0 : Plane) (v b)) =
      segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) (-a) := by
    ext x
    constructor
    · intro hx
      obtain ⟨b,hb⟩ := mem_iUnion.mp hx
      cases b
      · exact Or.inl hb
      · exact Or.inr hb
    · intro hx
      rcases hx with h | h
      · exact mem_iUnion.mpr ⟨false,h⟩
      · exact mem_iUnion.mpr ⟨true,h⟩
  have hv : ∀ b, ‖v b‖ = R := by intro b; cases b <;> simp [v,ha]
  have hfanAxis : ∀ x ∈ ⋃ b, segment ℝ (0 : Plane) (v b), x 1 = 0 := by
    intro x hx
    obtain ⟨b,hb⟩ := mem_iUnion.mp hx
    obtain ⟨r,t,hr,ht,hrt,hxt⟩ := hb
    have hv1 : v b 1 = 0 := by cases b <;> simp [v,a,Plane.mk]
    rw [← hxt]
    simp [hv1]
  have he0 : e ≠ 0 := by intro hh; apply heaxis; simp [hh]
  let α : Path (0 : Plane) ((2 : ℝ) • e) := Path.segment 0 ((2 : ℝ) • e)
  have hαt : ∀ t : CurveComplex.Interval, α t = (2 * t.val) • e := by
    intro t
    simp [α, Path.segment_apply, AffineMap.lineMap_apply_module, smul_smul]
    congr 1
    ring
  have hα : Function.Injective α :=
    Path.segment_injective_of_ne (by simpa using (smul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) he0).symm)
  have houtside : (2 : ℝ) • e ∉ closedBall (0 : Plane) R := by
    simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), he]
    linarith
  have havoid : ∀ t : CurveComplex.Interval, 0 < t.val →
      α t ∉ ⋃ b, segment ℝ (0 : Plane) (v b) := by
    intro t ht hh
    have hz := hfanAxis (α t) hh
    rw [hαt] at hz
    have hz' : (2 * t.val) * e 1 = 0 := hz
    exact heaxis ((mul_eq_zero.mp hz').resolve_left (by positivity))
  obtain ⟨c,k,hc,hc1,hn,hb,hArc,hAi,hproper⟩ :=
    actualFixedConvexFanFirstExit Q v R hR hclosed hconv hzero hinside hcover
      hdisj (by simpa only [hfanEq] using hfront) hv α hα houtside havoid
  have hce : α c = e := by
    rw [hαt, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), he] at hn
    have ht : 2 * c.val = 1 := by nlinarith
    rw [hαt, ht, one_smul]
  have heQ : e ∈ Q k := hclosed k |>.frontier_subset (hce ▸ hb)
  have heNot : e ∉ segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) (-a) := by
    intro hh
    exact heaxis (hfanAxis e (hfanEq.symm ▸ hh))
  obtain ⟨K',Q',hcl',hco',hz',hi',hcov',hd',hfr',hne',hce',hf',hs'⟩ :=
    actualFixedConvexFanInsertCells Q _ R hR hclosed hconv hzero hinside hcover
      hdisj hfront hne hcenter hfan hsupport k e heQ he heNot
      (by simpa only [hce] using hproper)
  exact ⟨K',Q',hcl',hco',hz',hi',hcov',hd',hfr',hne',hce',hf'⟩
#print axioms actualAxisAndRadiusConvexCells

/-- Actual loop-anchor second-arm insertion: no finite source-old contact premise. -/
private theorem actualAxisAndFirstRadiusRelativeSourceInsertion
    {L : Type} [Fintype L] (old : L → Plane)
    (q : Plane) (hqaxis : q 1 ≠ 0)
    (γ : CurveComplex.Interval → Plane) (hγ : IsClosedEmbedding γ) (hzero : γ 0 = 0)
    (haxis : ∀ t : CurveComplex.Interval, 0 < t.val → (γ t) 1 ≠ 0)
    (hfirst : ∀ t : CurveComplex.Interval, 0 < t.val → γ t ∉ segment ℝ (0 : Plane) q)
    (V : Set Plane) (hV : IsOpen V) (h0V : (0 : Plane) ∈ V) :
    ∃ F : Plane ≃ₜ Plane, ∃ R : ℝ, 0 < R ∧ closedBall (0 : Plane) R ⊆ V ∧
      R < ‖q‖ ∧ F 0 = 0 ∧ (∀ x, x ∉ ball (0 : Plane) R → F x = x) ∧
      (∀ x : Plane, x 1 = 0 → F x = x) ∧
      (∀ x ∈ segment ℝ (0 : Plane) q, F x = x) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ u : Plane, u ≠ 0 ∧ F '' (γ '' Icc 0 c) = segment ℝ 0 u ∧
          segment ℝ 0 u ∩ {x : Plane | x 1 = 0} = {0} ∧
          segment ℝ 0 u ∩ segment ℝ (0 : Plane) q = {0} ∧
          ∀ l, segment ℝ 0 u ∩
            {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • old l} = {0} := by
  have hq0 : q ≠ 0 := by intro he; apply hqaxis; simp [he]
  have hend : γ 1 ≠ 0 := by
    intro he
    have hh : (1 : CurveComplex.Interval) = 0 := hγ.injective (he.trans hzero.symm)
    have hv := congrArg Subtype.val hh
    norm_num at hv
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have han : 0 < ‖γ 1‖ := norm_pos_iff.mpr hend
  obtain ⟨ε,hε,hεV⟩ := Metric.isOpen_iff.mp hV 0 h0V
  let R := min ε (min ‖q‖ ‖γ 1‖) / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRε : R < ε := by
    have hh : min ε (min ‖q‖ ‖γ 1‖) ≤ ε := min_le_left _ _
    dsimp [R]; linarith
  have hRq : R < ‖q‖ := by
    have hh := (min_le_right ε (min ‖q‖ ‖γ 1‖)).trans (min_le_left ‖q‖ ‖γ 1‖)
    dsimp [R]; linarith
  have hRa : R < ‖γ 1‖ := by
    have hh := (min_le_right ε (min ‖q‖ ‖γ 1‖)).trans (min_le_right ‖q‖ ‖γ 1‖)
    dsimp [R]; linarith
  have hRV : closedBall (0 : Plane) R ⊆ V :=
    (closedBall_subset_ball hRε).trans hεV
  let e := (R / ‖q‖) • q
  have hscale : 0 < R / ‖q‖ := div_pos hR hqn
  have he : ‖e‖ = R := by
    simp only [e,norm_smul,Real.norm_eq_abs,abs_of_pos hscale]
    field_simp
  have heaxis : e 1 ≠ 0 := mul_ne_zero (ne_of_gt hscale) hqaxis
  let a := Plane.mk R 0
  let fan := (segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) (-a)) ∪
    segment ℝ (0 : Plane) e
  obtain ⟨K,Q,hcl,hco,hz,hi,hcov,hd,hfr,hne,hce,hf⟩ :=
    actualAxisAndRadiusConvexCells R hR e he heaxis
  let v : Fin 3 → Plane := fun j => if j = 0 then a else if j = 1 then -a else e
  have hv : ∀ j, ‖v j‖ = R := by
    intro j
    have ha : ‖a‖ = R := by
      simp [a, EuclideanSpace.norm_eq, Fin.sum_univ_two, Plane.mk,
        Real.sqrt_sq (le_of_lt hR)]
    fin_cases j <;> simp [v,ha,he]
  have hfanEq : (⋃ j, segment ℝ (0 : Plane) (v j)) = fan := by
    ext x
    constructor
    · intro hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      fin_cases j
      · exact Or.inl (Or.inl hj)
      · exact Or.inl (Or.inr hj)
      · exact Or.inr hj
    · intro hx
      rcases hx with (hx | hx) | hx
      · exact mem_iUnion.mpr ⟨0,hx⟩
      · exact mem_iUnion.mpr ⟨1,hx⟩
      · exact mem_iUnion.mpr ⟨2,hx⟩
  have hshortSubset : segment ℝ (0 : Plane) e ⊆ segment ℝ (0 : Plane) q := by
    apply (convex_segment (0 : Plane) q).segment_subset
    · exact left_mem_segment ℝ 0 q
    · rw [segment_eq_image]
      refine ⟨R / ‖q‖,⟨hscale.le,(div_le_one hqn).mpr hRq.le⟩,?_⟩
      simp [e]
  have haxisFan : ∀ x ∈ segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) (-a), x 1 = 0 := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨r,t,hr,ht,hrt,hxt⟩ := hx
      rw [← hxt]
      simp [a,Plane.mk]
    · obtain ⟨r,t,hr,ht,hrt,hxt⟩ := hx
      rw [← hxt]
      simp [a,Plane.mk]
  let α : Path (0 : Plane) (γ 1) := {
    toFun := γ
    continuous_toFun := hγ.continuous
    source' := hzero
    target' := rfl }
  have havoid : ∀ t : CurveComplex.Interval, 0 < t.val → α t ∉ ⋃ j, segment ℝ 0 (v j) := by
    intro t ht hh
    rw [hfanEq] at hh
    rcases hh with hh | hh
    · exact haxis t ht (haxisFan _ hh)
    · exact hfirst t ht (hshortSubset hh)
  let allold : Option L → Plane := fun l => Option.casesOn l q old
  obtain ⟨F,hF0,hfix,hfixfan,c,hc,hc1,u,hu,himage,huaxis,huold⟩ :=
    actualOldAvoidingFixedConvexFanInsertion allold Q v R hR hcl hco hz hi hcov hd
      (by simpa only [hfanEq] using hfr) hne hce
      (by simpa only [hfanEq] using hf)
      (fun k => actualOppositeAxisFanExcludesCellInterior R hR (Q k) fan (hi k) (hf k)
        (by exact subset_union_left)) hv α hγ.injective
      (by simpa only [mem_closedBall,dist_zero_right] using not_le.mpr hRa) havoid
  have hfixAxis : ∀ x : Plane, x 1 = 0 → F x = x := by
    intro x hx
    by_cases hb : x ∈ ball (0 : Plane) R
    · apply hfixfan
      rw [hfanEq]
      exact Or.inl (actualAxisBallCoveredByOppositeArms R hR (ball_subset_closedBall hb) hx)
    · exact hfix x hb
  have hfixLong : ∀ x ∈ segment ℝ (0 : Plane) q, F x = x :=
    actualFixedTruncatedRadiusPreservesWholeArm F q hq0 R hR hfix (by
      intro x hx
      apply hfixfan
      rw [hfanEq]
      exact Or.inr hx)
  have hmeet : segment ℝ (0 : Plane) u ∩ segment ℝ (0 : Plane) q = {0} := by
    apply Subset.antisymm
    · intro x hx
      have hxray : x ∈ {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • q} := by
        obtain ⟨r,t,hr,ht,hrt,hxt⟩ := hx.2
        exact ⟨t,ht,by simpa only [smul_zero,zero_add] using hxt.symm⟩
      exact huold none ▸ ⟨hx.1,hxray⟩
    · intro x hx
      have hx0 : x = 0 := hx
      subst x
      exact ⟨left_mem_segment ℝ 0 u,left_mem_segment ℝ 0 q⟩
  exact ⟨F,R,hR,hRV,hRq,hF0,hfix,hfixAxis,hfixLong,c,hc,hc1,u,hu,himage,huaxis,hmeet,
    fun l => huold (some l)⟩
#print axioms actualAxisAndFirstRadiusRelativeSourceInsertion

private theorem actualPlaneComplexNorm (z : Plane) :
    ‖CurveComplex.ArcFinitePosition.planeComplexLinearEquiv z‖ = ‖z‖ := by
  have hre : (CurveComplex.ArcFinitePosition.planeComplexLinearEquiv z).re = z 0 := rfl
  have him : (CurveComplex.ArcFinitePosition.planeComplexLinearEquiv z).im = z 1 := rfl
  rw [Complex.norm_def,Complex.normSq_apply,hre,him,EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two,Real.norm_eq_abs,pow_two]

/-- A single genuine rotation avoids all indexed old lines for a finite actual
source star; repeated old/source indices remain in the finite product. -/
private theorem actualFiniteSourceRotationAvoidsOldLines
    {J K : Type} [Fintype J] [Fintype K]
    (v : J → ℂ) (hv : ∀ j, v j ≠ 0) (w : K → ℂ) (hw : ∀ k, w k ≠ 0) :
    ∃ θ : ℝ, ∀ j k (r : ℝ), (Circle.exp θ : ℂ) * v j ≠ r • w k := by
  classical
  let signed : K × Bool → ℂ := fun kb => if kb.2 then -w kb.1 else w kb.1
  have hsigned : ∀ kb, signed kb ≠ 0 := by rintro ⟨k,b⟩; cases b <;> simp [signed,hw]
  let bad : Finset ℂ := Finset.univ.image (fun jk : J × (K × Bool) =>
    ((‖v jk.1‖ / ‖signed jk.2‖ : ℝ) : ℂ) * signed jk.2 / v jk.1)
  obtain ⟨θ,hθ,hθbad⟩ := CurveComplex.ArcFinitePosition.exists_angle_avoiding_finite_complex bad
  have hnonnegative : ∀ j kb (r : ℝ), 0 ≤ r →
      (Circle.exp θ : ℂ) * v j ≠ r • signed kb := by
    intro j kb r hr he
    have hn : ‖v j‖ = r * ‖signed kb‖ := by
      have hh := congrArg norm he
      simpa only [norm_mul,Circle.norm_coe,one_mul,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr] using hh
    have hwNorm : ‖signed kb‖ ≠ 0 := norm_ne_zero_iff.mpr (hsigned kb)
    have hrEq : r = ‖v j‖ / ‖signed kb‖ := (eq_div_iff hwNorm).mpr hn.symm
    have heBad : (Circle.exp θ : ℂ) =
        ((‖v j‖ / ‖signed kb‖ : ℝ) : ℂ) * signed kb / v j := by
      apply (eq_div_iff (hv j)).mpr
      rw [he,hrEq]
      rfl
    apply hθbad
    rw [heBad]
    exact Finset.mem_image.mpr ⟨(j,kb),Finset.mem_univ _,rfl⟩
  refine ⟨θ,?_⟩
  intro j k r he
  by_cases hr : 0 ≤ r
  · exact hnonnegative j (k,false) r hr (by simpa [signed] using he)
  · apply hnonnegative j (k,true) (-r) (by linarith)
    simpa [signed] using he
#print axioms actualPlaneComplexNorm
#print axioms actualFiniteSourceRotationAvoidsOldLines

/-- Actual source-only finite star with all new germ lines avoiding indexed old
rays. There is no fixed anchor reference: this is used in anchor-free endpoint disks. -/
private theorem actualOldAvoidingFreeSourceStarRadialization
    {J K : Type} [Fintype J] [Fintype K]
    (γ : J → CurveComplex.Interval → Plane)
    (hγ : ∀ j, IsClosedEmbedding (γ j)) (hzero : ∀ j, γ j 0 = 0)
    (hmeet : ∀ j k, j ≠ k → range (γ j) ∩ range (γ k) = {0})
    (old : K → Plane) (hold : ∀ k, old k ≠ 0)
    (V : Set Plane) (hV : IsOpen V) (h0V : (0 : Plane) ∈ V) :
    ∃ F : Plane ≃ₜ Plane, ∃ R : ℝ, 0 < R ∧ closedBall (0 : Plane) R ⊆ V ∧
      F 0 = 0 ∧ (∀ x, x ∉ ball (0 : Plane) R → F x = x) ∧
      ∃ cut : J → CurveComplex.Interval, ∃ vector : J → Plane,
        (∀ j, 0 < (cut j).val ∧ (cut j).val < 1 ∧ vector j ≠ 0 ∧
          F '' (γ j '' Icc 0 (cut j)) = segment ℝ 0 (vector j)) ∧
        ∀ j k, segment ℝ 0 (vector j) ∩
          {x : Plane | ∃ r : ℝ, 0 ≤ r ∧ x = r • old k} = {0} := by
  classical
  obtain ⟨star⟩ := CurveComplex.FiniteStarGeometry.finite_actual_star_radialization γ 0 hγ hzero hmeet V hV h0V
  obtain ⟨ε,hε,hεV⟩ := Metric.isOpen_iff.mp hV 0 h0V
  let S := ε/2
  have hS : 0 < S := by dsimp [S]; positivity
  have hSV : closedBall (0 : Plane) S ⊆ V :=
    (closedBall_subset_ball (by dsimp [S]; linarith)).trans hεV
  let ρ := min star.coreRadius (S/4)
  have hρ : 0 < ρ := lt_min star.core_pos (by dsimp [S]; positivity)
  have hρCore : ρ ≤ star.coreRadius := min_le_left _ _
  have hρS : ρ ≤ S/2 := (min_le_right _ _).trans (by linarith)
  let q : J → Plane := fun j => (ρ / ‖star.vector j‖) • star.vector j
  have hqn : ∀ j, ‖q j‖ = ρ := by
    intro j
    have hvn : 0 < ‖star.vector j‖ := norm_pos_iff.mpr (star.vector_nonzero j)
    simp only [q,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hρ hvn)]
    field_simp
  have hq0 : ∀ j, q j ≠ 0 := by
    intro j
    have hn : 0 < ‖star.vector j‖ := norm_pos_iff.mpr (star.vector_nonzero j)
    exact smul_ne_zero (ne_of_gt (div_pos hρ hn)) (star.vector_nonzero j)
  have hcut : ∀ j, ∃ c : CurveComplex.Interval, 0 < c.val ∧ c.val < 1 ∧
      star.H '' (γ j '' Icc 0 c) = segment ℝ 0 (q j) := by
    intro j
    let α : Path (0 : Plane) (γ j 1) := {
      toFun := γ j
      continuous_toFun := (hγ j).continuous
      source' := hzero j
      target' := rfl }
    have hfull : IsArcBetween (star.H '' range (γ j)) 0 (star.H (γ j 1)) := by
      have hh := (actualInjectivePathIsArc α (hγ j).injective).image_of_injOn
        (S := Set.univ) (subset_univ _) star.H.continuous.continuousOn star.H.injective.injOn
      change IsArcBetween (star.H '' range (γ j)) (star.H 0) (star.H (γ j 1)) at hh
      rw [star.fixes_center] at hh
      exact hh
    have hqsub : segment ℝ (0 : Plane) (q j) ⊆ segment ℝ 0 (star.vector j) := by
      apply (convex_segment (0 : Plane) (star.vector j)).segment_subset (left_mem_segment ℝ _ _)
      rw [segment_eq_image]
      have hn : 0 < ‖star.vector j‖ := norm_pos_iff.mpr (star.vector_nonzero j)
      refine ⟨ρ / ‖star.vector j‖,⟨(div_pos hρ hn).le,
        (div_le_one hn).mpr (hρCore.trans (star.core_lt_length j).le)⟩,?_⟩
      simp [q]
    have hsub : segment ℝ (0 : Plane) (q j) ⊆ star.H '' range (γ j) := by
      apply hqsub.trans
      rw [← zero_add (star.vector j),← star.prefix_image j]
      exact image_mono (image_subset_range _ _)
    have hend : star.H (γ j 1) ∉ closedBall (0 : Plane) star.coreRadius := by
      apply fun hh => Set.disjoint_left.mp (star.excludes_tails j) ?_ hh
      refine ⟨γ j 1,⟨1,?_,rfl⟩,rfl⟩
      exact (star.cut j).property.2
    have hqEnd : q j ≠ star.H (γ j 1) := by
      intro he
      apply hend
      rw [← he]
      simpa only [mem_closedBall,dist_zero_right,hqn j] using hρCore
    obtain ⟨c,hc,hc1,hci⟩ := actualSourcePrefixPullback α (hγ j).injective star.H
      (segment ℝ (0 : Plane) (q j)) (star.H '' range (γ j)) hfull
      (by simpa only [star.fixes_center] using isArcBetween_segment (Ne.symm (hq0 j)))
      Subset.rfl hsub (hsub (right_mem_segment ℝ 0 (q j)))
      (by simpa only [star.fixes_center] using hq0 j) hqEnd
    exact ⟨c,hc,hc1,hci⟩
  choose cut hcut0 hcut1 hcutimage using hcut
  let L := CurveComplex.ArcFinitePosition.planeComplexLinearEquiv
  obtain ⟨θ,hθ⟩ := actualFiniteSourceRotationAvoidsOldLines (fun j => L (q j))
    (fun j he => hq0 j (L.injective (by simpa using he))) (fun k => L (old k))
    (fun k he => hold k (L.injective (by simpa using he)))
  obtain ⟨P,hP0,hPout,hPnorm,hPinner⟩ :=
    CurveComplex.ArcFinitePosition.supported_plane_endpoint_rotation 0 S θ hS
  obtain ⟨H,hH⟩ := P.homeomorphism_at 1
  have hHfinal : P.finalMap = H := funext (fun x => (hH x).symm)
  have hH0 : H 0 = 0 := by rw [← hHfinal]; exact hP0 1
  have hHfix : ∀ x, x ∉ ball (0 : Plane) S → H x = x := by
    intro x hx
    rw [← hHfinal]
    apply hPout 1 x
    simpa only [sub_zero,actualPlaneComplexNorm] using (not_lt.mp (show ¬ ‖x‖ < S by
      simpa only [mem_ball,dist_zero_right] using hx))
  let A : Plane →ₗ[ℝ] Plane := {
    toFun := fun z => L.symm ((Circle.exp θ : ℂ) * L z)
    map_add' := by intro x y; simp [map_add,mul_add]
    map_smul' := by
      intro r x
      apply L.injective
      simp only [L.apply_symm_apply,map_smul]
      simp only [Complex.real_smul,RingHom.id_apply]
      ring }
  have hHpure : ∀ x, ‖x‖ ≤ S/2 → H x = A x := by
    intro x hx
    apply L.injective
    have hh := hPinner x (by simpa only [sub_zero,actualPlaneComplexNorm] using hx)
    rw [hHfinal] at hh
    simp only [sub_zero] at hh
    change L (H x) = L (L.symm ((Circle.exp θ : ℂ) * L x))
    rw [L.apply_symm_apply]
    exact hh
  have hsegmentNorm : ∀ j x, x ∈ segment ℝ (0 : Plane) (q j) → ‖x‖ ≤ S/2 := by
    intro j x hx
    obtain ⟨r,t,hr,ht,hrt,hxt⟩ := hx
    have ht1 : t ≤ 1 := by linarith
    rw [← hxt]
    simp only [smul_zero,zero_add,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht,hqn j]
    exact (mul_le_of_le_one_left hρ.le ht1).trans hρS
  have hHsegment : ∀ j, H '' segment ℝ (0 : Plane) (q j) = segment ℝ 0 (A (q j)) := by
    intro j
    calc
      H '' segment ℝ (0 : Plane) (q j) = A '' segment ℝ (0 : Plane) (q j) :=
        image_congr (fun x hx => hHpure x (hsegmentNorm j x hx))
      _ = segment ℝ 0 (A (q j)) := by
        change A.toAffineMap '' segment ℝ (0 : Plane) (q j) = _
        rw [image_segment]
        simp
  have hAq0 : ∀ j, A (q j) ≠ 0 := by
    intro j he
    have hh := congrArg L he
    have hc : (Circle.exp θ : ℂ) * L (q j) = 0 := by simpa [A] using hh
    exact hq0 j (L.injective (by simpa using (mul_eq_zero.mp hc).resolve_left (Circle.coe_ne_zero _)))
  let F := star.H.trans H
  obtain ⟨hR,hRV,hF0,hFfix⟩ := actualComposeSupportedMotionsClosedBall
    star.H H star.supportRadius S star.support_pos hS V star.support_subset hSV
      star.fixes_center hH0 star.fixes_exterior hHfix
  refine ⟨F,max star.supportRadius S,hR,hRV,hF0,hFfix,cut,(fun j => A (q j)),?_,?_⟩
  · intro j
    refine ⟨hcut0 j,hcut1 j,hAq0 j,?_⟩
    have himage : F '' (γ j '' Icc 0 (cut j)) = H '' (star.H '' (γ j '' Icc 0 (cut j))) := by
      change (H ∘ star.H) '' (γ j '' Icc 0 (cut j)) = _
      exact image_comp H star.H _
    rw [himage,hcutimage j,hHsegment j]
  · intro j k
    apply actualGermSegmentAvoidingNoncollinearRay
    intro r he
    apply hθ j k r
    have hh := congrArg L he
    simpa [A,map_smul] using hh
#print axioms actualOldAvoidingFreeSourceStarRadialization

end CurveComplex.HyperellipticModel
open Set Topology CurveComplex
end


section

namespace CurveComplex.HyperellipticModel
open Set Topology Metric Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem actualChartSourceCrossingDiskTransportToSpecifiedAnchor
    (M : HyperellipticModel E S) (a b target : EssentialMarkedArc M)
    (h : S ≃ₜ S) (hm : ∀ p, p ∈ M.cover.branch → h p = p)
    (ha : h '' a.val.image = target.val.image)
    (p : S) (hc : CrossesInDisk M a b p) :
    CrossesInDisk M target (b.transport h hm) (h p) := by
  obtain ⟨U,hU,hp,hmark,e,he0,hanchor,hb⟩ := hc
  let eU : U ≃ₜ (h '' U) := h.image U
  have hp' : h p ∈ h '' U := mem_image_of_mem h hp
  let f := eU.symm.trans e
  have hmark' : Disjoint (h '' U) (M.cover.branch : Set S) := by
    apply Set.disjoint_left.mpr
    rintro q ⟨z,hz,rfl⟩ hq
    have heq : h z = z := h.injective (hm (h z) hq)
    exact Set.disjoint_left.mp hmark hz (heq ▸ hq)
  refine ⟨h '' U,h.isOpenMap U hU,hp',hmark',f,?_,?_,?_⟩
  · have he : eU.symm ⟨h p,hp'⟩ = ⟨p,hp⟩ := by
      apply Subtype.ext
      exact h.symm_apply_apply p
    simpa only [f,Homeomorph.trans_apply,he] using he0
  · intro q
    let y := eU.symm q
    have hy : y.val = h.symm q.val := rfl
    have hmem : q.val ∈ h '' a.val.image ↔ y.val ∈ a.val.image := by
      rw [hy]
      exact Set.mem_image_iff_of_inverse h.symm_apply_apply h.apply_symm_apply
    rw [ha] at hmem
    exact hmem.trans (hanchor y)
  · intro q
    let y := eU.symm q
    have hy : y.val = h.symm q.val := rfl
    change q.val ∈ (b.val.transport h hm).image ↔ _
    rw [MarkedArc.transport_image]
    have hmem : q.val ∈ h '' b.val.image ↔ y.val ∈ b.val.image := by
      rw [hy]
      exact Set.mem_image_iff_of_inverse h.symm_apply_apply h.apply_symm_apply
    exact hmem.trans (hb y)



/-- Lift a genuine supported planar reference-preserving motion to the actual
marked surface; the entire literal anchor and its crossing count are preserved. -/
private theorem actualSupportedReferenceChartSourceMotion
    (M : HyperellipticModel E S) (anchor a : EssentialMarkedArc M)
    (hf : (crossings M anchor a).Finite)
    (ht : ∀ x ∈ crossings M anchor a, CrossesInDisk M anchor a x)
    (p : S) (hp : p ∈ M.cover.branch)
    (e : OpenPartialHomeomorph S Plane) (hpe : p ∈ e.source) (he0 : e p = 0)
    (hemarks : e.source ∩ (M.cover.branch : Set S) = {p})
    (R : ℝ) (hR : 0 < R) (hRT : closedBall (0 : Plane) R ⊆ e.target)
    (reference : Set Plane)
    (hanchor : ∀ x, x ∈ e.source → e x ∈ closedBall (0 : Plane) R →
      (x ∈ anchor.val.image ↔ e x ∈ reference))
    (F : Plane ≃ₜ Plane) (hF0 : F 0 = 0)
    (hfix : ∀ z, z ∉ ball (0 : Plane) R → F z = z)
    (href : F '' reference = reference) :
    ∃ H : AmbientIsotopy S,
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      ∃ g : S ≃ₜ S, ∃ hm : ∀ x, x ∈ M.cover.branch → g x = x,
        H.finalMap = g ∧ g '' anchor.val.image = anchor.val.image ∧
        (∀ x, x ∉ e.source → g x = x) ∧
        (∀ x, x ∈ e.source → g x ∈ e.source) ∧
        (∀ x, x ∈ e.source → e (g x) = F (e x)) ∧
        vertex M (a.transport g hm) = vertex M a ∧
        (a.transport g hm).val.map 0 = a.val.map 0 ∧
        (a.transport g hm).val.map 1 = a.val.map 1 ∧
        (crossings M anchor (a.transport g hm)).Finite ∧
        (∀ x ∈ crossings M anchor (a.transport g hm),
          CrossesInDisk M anchor (a.transport g hm) x) ∧
        (crossings M anchor (a.transport g hm)).ncard =
          (crossings M anchor a).ncard := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  obtain ⟨P,hPfinal,hP0,hPoutside⟩ := supported_pointed_plane_isotopy 0 R hR F hF0 hfix
  have hPclosed : ∀ t z, z ∉ closedBall (0 : Plane) R → P.map (t,z) = z := by
    intro t z hz
    exact hPoutside t z (fun hb => hz (ball_subset_closedBall hb))
  obtain ⟨K,H,hcoord,hHU,houtside⟩ := position_surface_chart_lift S e.source e.target
    e.open_source e.toHomeomorphSourceTarget (closedBall (0 : Plane) R)
    (isCompact_closedBall _ _) hRT P hPclosed
  have hcoord' (t : Interval) (x : e.source) : e (K.map (t,x)) = P.map (t,e x) := by
    simpa only [OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe] using hcoord t x
  have hpoint (t : Interval) (x : S) (hx : x ∈ e.source) :
      H.map (t,x) = e.symm (P.map (t,e x)) := by
    rw [hHU t ⟨x,hx⟩,← hcoord' t ⟨x,hx⟩]
    exact (e.left_inv (K.map (t,⟨x,hx⟩)).property).symm
  have hcenter : ∀ t, H.map (t,p) = p := by
    intro t
    rw [hpoint t p hpe,he0,hP0,← he0,e.left_inv hpe]
  have hmarks : ∀ t x, x ∈ M.cover.branch → H.map (t,x) = x := by
    intro t x hx
    by_cases hs : x ∈ e.source
    · have heq : x = p := by
        have hh : x ∈ e.source ∩ (M.cover.branch : Set S) := ⟨hs,hx⟩
        rw [hemarks] at hh
        exact hh
      subst x
      exact hcenter t
    · exact houtside t x hs
  obtain ⟨g,hg⟩ := H.homeomorphism_at 1
  have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
  have hm : ∀ x, x ∈ M.cover.branch → g x = x := by
    intro x hx
    rw [← hfinal]
    exact hmarks 1 x hx
  have hgsource : ∀ x, x ∈ e.source → g x ∈ e.source := by
    intro x hx
    rw [← hfinal]
    change H.map (1,x) ∈ e.source
    rw [hHU 1 ⟨x,hx⟩]
    exact (K.map (1,⟨x,hx⟩)).property
  have hgcoord : ∀ x, x ∈ e.source → e (g x) = F (e x) := by
    intro x hx
    rw [← hfinal]
    change e (H.map (1,x)) = F (e x)
    rw [hHU 1 ⟨x,hx⟩,hcoord' 1 ⟨x,hx⟩]
    exact congrFun hPfinal (e x)
  have hFbound : ∀ z, z ∈ closedBall (0 : Plane) R → F z ∈ closedBall (0 : Plane) R := by
    intro z hz
    by_contra hh
    have hfz : F (F z) = F z := hfix (F z) (fun hb => hh (ball_subset_closedBall hb))
    have heq : F z = z := F.injective hfz
    exact hh (heq.symm ▸ hz)
  have hRefMem : ∀ z, F z ∈ reference ↔ z ∈ reference := by
    intro z
    calc
      F z ∈ reference ↔ F z ∈ F '' reference := by rw [href]
      _ ↔ z ∈ reference := F.injective.mem_set_image
  have hgAnchor : ∀ x, g x ∈ anchor.val.image ↔ x ∈ anchor.val.image := by
    intro x
    by_cases hx : x ∈ e.source
    · by_cases hb : e x ∈ ball (0 : Plane) R
      · calc
          g x ∈ anchor.val.image ↔ e (g x) ∈ reference :=
            hanchor (g x) (hgsource x hx) (by rw [hgcoord x hx]; exact hFbound _ (ball_subset_closedBall hb))
          _ ↔ F (e x) ∈ reference := by rw [hgcoord x hx]
          _ ↔ e x ∈ reference := hRefMem (e x)
          _ ↔ x ∈ anchor.val.image := (hanchor x hx (ball_subset_closedBall hb)).symm
      · have heq : g x = x := by
          rw [← hfinal]
          change H.map (1,x) = x
          rw [hpoint 1 x hx,hPoutside 1 (e x) hb,e.left_inv hx]
        rw [heq]
    · have heq : g x = x := by
        rw [← hfinal]
        exact houtside 1 x hx
      rw [heq]
  have hAnchorImage : g '' anchor.val.image = anchor.val.image := by
    apply Subset.antisymm
    · rintro x ⟨y,hy,rfl⟩
      exact (hgAnchor y).mpr hy
    · intro x hx
      refine ⟨g.symm x,?_,g.apply_symm_apply x⟩
      apply (hgAnchor (g.symm x)).mp
      simpa only [g.apply_symm_apply] using hx
  have hclass : vertex M (a.transport g hm) = vertex M a := by
    apply Eq.symm
    apply Quotient.sound
    refine ⟨H,hmarks,?_⟩
    rw [hfinal]
    exact (MarkedArc.transport_image a.val g hm).symm
  have hcross : crossings M anchor (a.transport g hm) = g '' crossings M anchor a :=
    actual_crossings_transport_preserving_anchor_image anchor a g hm hAnchorImage
  refine ⟨H,hmarks,g,hm,hfinal,hAnchorImage,?_,hgsource,hgcoord,hclass,?_,?_,?_,?_,?_⟩
  · intro x hx
    rw [← hfinal]
    exact houtside 1 x hx
  · exact hm _ a.val.start_marked
  · exact hm _ a.val.end_marked
  · rw [hcross]
    exact hf.image _
  · intro x hx
    rw [hcross] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact actualChartSourceCrossingDiskTransportToSpecifiedAnchor M anchor a anchor g hm hAnchorImage y (ht y hy)
  · exact actual_crossings_ncard_transport_preserving_anchor_image anchor a g hm hAnchorImage
#print axioms actualSupportedReferenceChartSourceMotion
/-- Actual incident source germs avoid the literal anchor by finiteness of
anchor contacts only, even when all source-old overlaps are initially infinite. -/
private theorem actualFiniteAnchorContactIncidentSourceGerms
    (M : HyperellipticModel E S) (anchor a : EssentialMarkedArc M)
    (hf : (crossings M anchor a).Finite)
    (p : S) (hp : p ∈ M.cover.branch)
    (e : OpenPartialHomeomorph S Plane) (hpe : p ∈ e.source) (he0 : e p = 0)
    (δ : ℝ) (hδ : 0 < δ) (reference : Set Plane)
    (hanchor : ∀ x, x ∈ e.source → e x ∈ ball (0 : Plane) δ →
      (x ∈ anchor.val.image ↔ e x ∈ reference)) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrhalf : r < 1/2,
      let γ : Bool → Interval → Plane := fun b =>
        e ∘ a.val.map ∘ endpointGermParameter b r hr (by linarith)
      let incident : Bool → Prop := fun b => (if b then a.val.map 1 else a.val.map 0) = p
      (∀ b, incident b → ∀ t, a.val.map (endpointGermParameter b r hr (by linarith) t) ∈ e.source) ∧
      (∀ b, incident b → ∀ t, γ b t ∈ ball (0 : Plane) δ) ∧
      (∀ b, incident b → IsClosedEmbedding (γ b)) ∧
      (∀ b, incident b → γ b 0 = 0) ∧
      (∀ b, incident b → ∀ t : Interval, 0 < t.val → γ b t ∉ reference) ∧
      (∀ b c, incident b → incident c → b ≠ c → range (γ b) ∩ range (γ c) = {0}) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let C := crossings M anchor a
  let U := (e.source ∩ e ⁻¹' ball (0 : Plane) δ) ∩ Cᶜ
  have hU : IsOpen U := (e.isOpen_inter_preimage isOpen_ball).inter hf.isClosed.isOpen_compl
  have hpU : p ∈ U := ⟨⟨hpe,by simpa only [mem_preimage,he0,mem_ball,dist_self] using hδ⟩,
    fun hh => hh.1.2 hp⟩
  obtain ⟨r,hr,hrhalf,hstart,hend⟩ := uniform_actual_endpoint_germs M PUnit (fun _ => a) p U hU hpU
  have hr1 : r < 1 := by linarith
  let γ : Bool → Interval → Plane := fun b => e ∘ a.val.map ∘ endpointGermParameter b r hr hr1
  let incident : Bool → Prop := fun b => (if b then a.val.map 1 else a.val.map 0) = p
  have hlocal : ∀ b, incident b → ∀ t : Interval,
      a.val.map (endpointGermParameter b r hr hr1 t) ∈ U := by
    intro b hb t
    cases b
    · apply hstart PUnit.unit hb
      change r * t.val ≤ r
      nlinarith [t.property.2]
    · apply hend PUnit.unit hb
      change 1-r ≤ 1-r*t.val
      nlinarith [t.property.2]
  have hsource : ∀ b, incident b → ∀ t : Interval,
      a.val.map (endpointGermParameter b r hr hr1 t) ∈ e.source :=
    fun b hb t => (hlocal b hb t).1.1
  have hzero : ∀ b, incident b → γ b 0 = 0 := by
    intro b hb
    have hg0 : a.val.map (endpointGermParameter b r hr hr1 0) = p := by
      cases b <;> simpa [incident,endpointGermParameter] using hb
    change e (a.val.map (endpointGermParameter b r hr hr1 0)) = 0
    rw [hg0,he0]
  refine ⟨r,hr,hrhalf,hsource,(fun b hb t => (hlocal b hb t).1.2),?_,hzero,?_,?_⟩
  · intro b hb
    have hem := actual_endpoint_germ_embedding M a b r hr hr1
    have hcont : Continuous (γ b) := by
      apply continuousOn_univ.mp
      exact e.continuousOn.comp hem.continuous.continuousOn (fun t _ => hsource b hb t)
    exact hcont.isClosedEmbedding (fun t u he => hem.injective
      (e.injOn (hsource b hb t) (hsource b hb u) he))
  · intro b hb t ht hRef
    have hx := hlocal b hb t
    have hpos : 0 < (endpointGermParameter b r hr hr1 t).val ∧
        (endpointGermParameter b r hr hr1 t).val < 1 := by
      cases b <;> dsimp [endpointGermParameter] <;>
        constructor <;> nlinarith [t.property.1,t.property.2]
    have hmark : a.val.map (endpointGermParameter b r hr hr1 t) ∉ M.cover.branch := by
      intro hm
      rcases a.val.marked_only_at_ends _ hm with he | he
      · have hv := congrArg Subtype.val he
        change (endpointGermParameter b r hr hr1 t).val = 0 at hv
        linarith [hpos.1]
      · have hv := congrArg Subtype.val he
        change (endpointGermParameter b r hr hr1 t).val = 1 at hv
        linarith [hpos.2]
    have ha : a.val.map (endpointGermParameter b r hr hr1 t) ∈ anchor.val.image :=
      (hanchor _ hx.1.1 hx.1.2).mpr hRef
    exact hx.2 ⟨⟨ha,hmark⟩,⟨endpointGermParameter b r hr hr1 t,rfl⟩,hmark⟩
  · intro b c hb hc hbc
    let solo : Unit → EssentialMarkedArc M := fun _ => a
    have hd : ∀ i j : Unit, i ≠ j → Disjoint (arcInterior M (solo i)) (arcInterior M (solo j)) := by
      intro i j hij
      exact (hij (Subsingleton.elim _ _)).elim
    have hs := actual_normalized_star_intersection M solo hd p r hr hrhalf
      ((),b) ((),c) (fun he => hbc (congrArg (fun z : Unit × Bool => z.2) he))
      (by cases b <;> simpa [solo,incident,endpointGermParameter] using hb)
      (by cases c <;> simpa [solo,incident,endpointGermParameter] using hc)
    apply Subset.antisymm
    · rintro x ⟨⟨t,ht⟩,⟨u,hu⟩⟩
      have he : a.val.map (endpointGermParameter b r hr hr1 t) =
          a.val.map (endpointGermParameter c r hr hr1 u) :=
        e.injOn (hsource b hb t) (hsource c hc u) (ht.trans hu.symm)
      have hp' : a.val.map (endpointGermParameter b r hr hr1 t) = p := by
        have hm : a.val.map (endpointGermParameter b r hr hr1 t) ∈
            range (a.val.map ∘ endpointGermParameter b r hr hr1) ∩
              range (a.val.map ∘ endpointGermParameter c r hr hr1) :=
          ⟨⟨t,rfl⟩,⟨u,he.symm⟩⟩
        rw [hs] at hm
        exact hm
      change x = 0
      rw [← ht]
      change e (a.val.map (endpointGermParameter b r hr hr1 t)) = 0
      rw [hp',he0]
    · intro x hx
      have he : x = 0 := hx
      subst x
      exact ⟨⟨0,hzero b hb⟩,⟨0,hzero c hc⟩⟩
#print axioms actualFiniteAnchorContactIncidentSourceGerms

private theorem actualCountChartReferenceInsideUnitBallHasAnchorArm
    (anchorLoop : Bool) {z : Plane}
    (hz : z ∈ {x : Plane | x 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ x 0)})
    (hn : ‖z‖ < 1) :
    z ∈ segment ℝ (0 : Plane) (Plane.mk 1 0) ∨
      (anchorLoop = true ∧ z ∈ segment ℝ (0 : Plane) (Plane.mk (-1) 0)) := by
  have hz1 : z 1 = 0 := hz.1
  have hxBound : |z 0| < 1 := lt_of_le_of_lt
    (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z 0) hn
  by_cases hx : 0 ≤ z 0
  · apply Or.inl
    rw [segment_eq_image]
    refine ⟨z 0, ⟨hx, (lt_of_le_of_lt (le_abs_self _) hxBound).le⟩, ?_⟩
    simp only [smul_zero, zero_add]
    ext i
    fin_cases i
    · simp
    · simp [hz1]
  · have hloop : anchorLoop = true := hz.2.resolve_right hx
    apply Or.inr
    refine ⟨hloop, ?_⟩
    rw [segment_eq_image]
    refine ⟨-z 0, ⟨neg_nonneg.mpr (le_of_not_ge hx), ?_⟩, ?_⟩
    · exact (lt_of_le_of_lt (neg_le_abs _) hxBound).le
    · simp only [smul_zero, zero_add]
      ext i
      fin_cases i
      · simp
      · simp [hz1]


/-- The canonical normalized anchor fan gives the literal ray or whole axis
through every point of its actual small coordinate ball. -/
private theorem actualNormalizedAnchorFanLiteralReference
    (incident : Bool → Prop) (b₀ : Bool) (hb₀ : incident b₀)
    (v : Bool → Plane) (hselected : v b₀ = Plane.mk 1 0)
    (hopposite : incident (!b₀) → v (!b₀) = Plane.mk (-1) 0)
    (anchorLoop : Bool) (hloop : anchorLoop = true ↔ incident (!b₀))
    (δ : ℝ) (hδ : δ < 1) :
    ∀ z : Plane, ‖z‖ < δ →
      ((∃ b : Bool, incident b ∧ z ∈ segment ℝ (0 : Plane) (v b)) ↔
        z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ z 0)) := by
  have hpos : ∀ z ∈ segment ℝ (0 : Plane) (Plane.mk 1 0), z 1 = 0 ∧ 0 ≤ z 0 := by
    intro z hz
    obtain ⟨r,t,hr,ht,hrt,hzt⟩ := hz
    rw [← hzt]
    constructor
    · simp [Plane.mk]
    · simpa [Plane.mk] using ht
  have hneg : ∀ z ∈ segment ℝ (0 : Plane) (Plane.mk (-1) 0), z 1 = 0 := by
    intro z hz
    obtain ⟨r,t,hr,ht,hrt,hzt⟩ := hz
    rw [← hzt]
    simp [Plane.mk]
  intro z hz
  constructor
  · rintro ⟨b,hb,hseg⟩
    by_cases he : b = b₀
    · subst b
      rw [hselected] at hseg
      exact ⟨(hpos z hseg).1,Or.inr (hpos z hseg).2⟩
    · have he' : b = !b₀ := by cases b <;> cases b₀ <;> simp_all
      have hi : incident (!b₀) := he' ▸ hb
      rw [he',hopposite hi] at hseg
      exact ⟨hneg z hseg,Or.inl (hloop.mpr hi)⟩
  · intro hr
    rcases actualCountChartReferenceInsideUnitBallHasAnchorArm anchorLoop hr (hz.trans hδ) with hp | ⟨hl,hn⟩
    · refine ⟨b₀,hb₀,?_⟩
      simpa only [hselected] using hp
    · have hi : incident (!b₀) := hloop.mp hl
      refine ⟨!b₀,hi,?_⟩
      simpa only [hopposite hi] using hn
#print axioms actualNormalizedAnchorFanLiteralReference

/-- A genuinely supported homeomorphism cannot move a point out of a larger
coordinate ball whose closed support ball lies strictly inside it. -/
private theorem actualSupportedMotionStaysInLargerBall
    (F : Plane ≃ₜ Plane) (R δ : ℝ)
    (hfix : ∀ x, x ∉ ball (0 : Plane) R → F x = x)
    (hmargin : closedBall (0 : Plane) R ⊆ ball (0 : Plane) δ) :
    ∀ x, x ∈ ball (0 : Plane) δ → F x ∈ ball (0 : Plane) δ := by
  intro x hx
  by_cases hs : x ∈ closedBall (0 : Plane) R
  · apply hmargin
    by_contra hh
    have heq : F (F x) = F x := hfix (F x) (fun hb => hh (ball_subset_closedBall hb))
    have he : F x = x := F.injective heq
    exact hh (he.symm ▸ hs)
  · rw [hfix x (fun hb => hs (ball_subset_closedBall hb))]
    exact hx
#print axioms actualSupportedMotionStaysInLargerBall

end CurveComplex.HyperellipticModel
end


section
namespace CurveComplex.HyperellipticModel
open Set Topology Metric Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Actual incident source motion in a canonical normalized anchor/old fan chart.
Only the original radialization provider is used; no initial source-old finiteness. -/
private theorem actualCountPreservingSourceClearanceInNormalizedFanChart
    (M : HyperellipticModel E S) {I : Type} [Fintype I]
    (anchor a : EssentialMarkedArc M) (old : I → EssentialMarkedArc M)
    (hf : (crossings M anchor a).Finite)
    (ht : ∀ x ∈ crossings M anchor a, CrossesInDisk M anchor a x)
    (p : S) (hp : p ∈ M.cover.branch)
    (e : OpenPartialHomeomorph S Plane) (hpe : p ∈ e.source) (he0 : e p = 0)
    (hemarks : e.source ∩ (M.cover.branch : Set S) = {p})
    (δ : ℝ) (hδ : 0 < δ) (hδT : ball (0 : Plane) δ ⊆ e.target)
    (v : I × Bool → Plane)
    (hv : ∀ (i : I) (b : Bool), (if b then (old i).val.map 1 else (old i).val.map 0) = p → v (i,b) ≠ 0)
    (hwhole : ∀ (i : I) x, x ∈ e.source → e x ∈ ball (0 : Plane) δ →
      (x ∈ (old i).val.image ↔ ∃ b : Bool,
        (if b then (old i).val.map 1 else (old i).val.map 0) = p ∧
          e x ∈ segment ℝ (0 : Plane) (v (i,b))))
    (anchorReference : Option Bool)
    (hanchor : ∀ x, x ∈ e.source → e x ∈ ball (0 : Plane) δ →
      (x ∈ anchor.val.image ↔ e x ∈ anchorReference.elim ∅
        (fun anchorLoop => {z : Plane | z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ z 0)}))) :
    ∃ b : EssentialMarkedArc M,
      vertex M b = vertex M a ∧ b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
      (crossings M anchor b).Finite ∧
      (∀ x ∈ crossings M anchor b, CrossesInDisk M anchor b x) ∧
      (crossings M anchor b).ncard = (crossings M anchor a).ncard ∧
      (∀ t, a.val.map t ∉ e.source → b.val.map t = a.val.map t) ∧
      ∃ s : ℝ, ∃ hs : 0 < s, ∃ hshalf : s < 1/2,
        ∀ β : Bool, (if β then a.val.map 1 else a.val.map 0) = p →
          ∀ t : Interval, 0 < t.val →
            b.val.map (endpointGermParameter β s hs (by linarith) t) ∉ anchor.val.image ∧
            ∀ i, b.val.map (endpointGermParameter β s hs (by linarith) t) ∉ (old i).val.image := by
  classical
  let reference : Set Plane := anchorReference.elim ∅
    (fun anchorLoop => {z : Plane | z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ z 0)})
  obtain ⟨r,hr,hrhalf,hsource,hball,hemb,hzero,havoid,hmeet⟩ :=
    actualFiniteAnchorContactIncidentSourceGerms M anchor a hf p hp e hpe he0 δ hδ reference hanchor
  have hr1 : r < 1 := by linarith
  let incident : Bool → Prop := fun β => (if β then a.val.map 1 else a.val.map 0) = p
  let J := {β : Bool // incident β}
  letI : Fintype J := Fintype.ofFinite J
  let Old := {g : I × Bool // (if g.2 then (old g.1).val.map 1 else (old g.1).val.map 0) = p}
  letI : Fintype Old := Fintype.ofFinite Old
  let γ : J → Interval → Plane := fun j => e ∘ a.val.map ∘ endpointGermParameter j.val r hr hr1
  let oldV : Old → Plane := fun k => v k.val
  have hcard : Fintype.card J ≤ 2 := by
    exact (Fintype.card_subtype_le incident).trans (by decide)
  have hNormalized : ∃ F : Plane ≃ₜ Plane, ∃ R : ℝ,
      0 < R ∧ closedBall (0 : Plane) R ⊆ ball (0 : Plane) δ ∧ F 0 = 0 ∧
      (∀ x, x ∉ ball (0 : Plane) R → F x = x) ∧ F '' reference = reference ∧
      ∃ cut : J → Interval, ∃ w : J → Plane,
        (∀ j, 0 < (cut j).val ∧ (cut j).val < 1 ∧ w j ≠ 0 ∧
          F '' (γ j '' Icc 0 (cut j)) = segment ℝ 0 (w j)) ∧
        (∀ j x, x ∈ segment ℝ (0 : Plane) (w j) → x ∈ reference → x = 0) ∧
        ∀ j k, segment ℝ 0 (w j) ∩
          {x : Plane | ∃ r : ℝ, 0 ≤ r ∧ x = r • oldV k} = {0} := by
    cases anchorReference with
    | none =>
      obtain ⟨F,R,hR,hRV,hF0,hfix,cut,w,hcut,havoidOld⟩ :=
        actualOldAvoidingFreeSourceStarRadialization γ
          (fun j => hemb j.val j.property) (fun j => hzero j.val j.property)
          (fun j k hjk => hmeet j.val k.val j.property k.property
            (fun he => hjk (Subtype.ext he))) oldV (fun k => hv k.val.1 k.val.2 k.property)
          (ball (0 : Plane) δ) isOpen_ball (by simpa only [mem_ball,dist_self] using hδ)
      refine ⟨F,R,hR,hRV,hF0,hfix,?_,cut,w,hcut,?_,havoidOld⟩
      · simp only [reference,Option.elim_none,image_empty]
      · intro j x hx href
        exact href.elim
    | some anchorLoop =>
      obtain ⟨F,R,hR,hRV,hF0,hfix,hFref,cut,w,hcut,havoidRef,havoidOld⟩ :=
        actual_anchor_relative_short_endpoint_arms_radialization γ hcard
          (fun j => hemb j.val j.property) (fun j => hzero j.val j.property)
          (fun j k hjk => hmeet j.val k.val j.property k.property
            (fun he => hjk (Subtype.ext he))) anchorLoop
          (fun j t ht => havoid j.val j.property t ht)
          (ball (0 : Plane) δ) isOpen_ball (by simpa only [mem_ball,dist_self] using hδ)
          oldV (fun k => hv k.val.1 k.val.2 k.property)
      refine ⟨F,R,hR,hRV,hF0,hfix,hFref,cut,w,hcut,?_,havoidOld⟩
      intro j x hx href
      have hh : x ∈ ({0} : Set Plane) := by rw [← havoidRef j]; exact ⟨hx,href⟩
      exact hh
  obtain ⟨F,R,hR,hRV,hF0,hFfix,hFref,cut,w,hcut,hnewref,hnewold⟩ := hNormalized
  obtain ⟨H,hmarks,g,hm,hfinal,hAnchorImage,hgout,hgsource,hgcoord,hclass,hb0,hb1,hbf,hbt,hbc⟩ :=
    actualSupportedReferenceChartSourceMotion M anchor a hf ht p hp e hpe he0 hemarks
      R hR (hRV.trans hδT) reference
      (fun x hx hz => hanchor x hx (hRV hz)) F hF0 hFfix hFref
  let b := a.transport g hm
  have small (s : Finset J) : ∃ d : ℝ, 0 < d ∧ d < 1 ∧ ∀ j ∈ s, d < (cut j).val := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1/2,by norm_num,by norm_num,by simp⟩
    | @insert j s hj ih =>
      obtain ⟨d,hd,hd1,hds⟩ := ih
      refine ⟨min d ((cut j).val/2),lt_min hd (half_pos (hcut j).1),
        (min_le_left _ _).trans_lt hd1,?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with he | hi
      · subst i
        exact (min_le_right _ _).trans_lt (by linarith [(hcut j).1])
      · exact (min_le_left _ _).trans_lt (hds i hi)
  obtain ⟨d,hd,hd1,hds⟩ := small Finset.univ
  let s := r*d/2
  have hs : 0 < s := by dsimp [s]; positivity
  have hsr : s < r := by dsimp [s]; nlinarith
  have hshalf : s < 1/2 := hsr.trans hrhalf
  have hs1 : s < 1 := by linarith
  refine ⟨b,hclass,hb0,hb1,hbf,hbt,hbc,?_,s,hs,hshalf,?_⟩
  · intro t ht
    exact hgout _ ht
  · intro β hβ t ht
    let j : J := ⟨β,hβ⟩
    let u : Interval := ⟨(s/r)*t.val,⟨by positivity,by
      have hratio : s/r < 1 := (div_lt_one hr).mpr hsr
      nlinarith [t.property.1,t.property.2]⟩⟩
    have hu : 0 < u.val := by dsimp [u]; positivity
    have hucut : u.val ≤ (cut j).val := by
      have hratioval : s/r = d/2 := by dsimp [s]; field_simp
      have hud : u.val ≤ d/2 := by dsimp [u]; rw [hratioval]; nlinarith [t.property.2]
      exact hud.trans (by linarith [hds j (Finset.mem_univ j)])
    have hparam : endpointGermParameter β s hs hs1 t = endpointGermParameter β r hr hr1 u := by
      apply Subtype.ext
      cases β <;> dsimp [endpointGermParameter,u] <;> field_simp
    let z := endpointGermParameter β s hs hs1 t
    have hzsource : a.val.map z ∈ e.source := by
      dsimp only [z]
      rw [hparam]
      exact hsource β hβ u
    have hbsource : b.val.map z ∈ e.source := hgsource _ hzsource
    have hbcoord : e (b.val.map z) = F (γ j u) := by
      change e (g (a.val.map z)) = F (γ j u)
      rw [hgcoord _ hzsource]
      dsimp only [z]
      rw [hparam]
      rfl
    have hbball : e (b.val.map z) ∈ ball (0 : Plane) δ := by
      rw [hbcoord]
      exact actualSupportedMotionStaysInLargerBall F R δ hFfix hRV (γ j u) (hball β hβ u)
    have hbsegment : e (b.val.map z) ∈ segment ℝ (0 : Plane) (w j) := by
      rw [← (hcut j).2.2.2]
      refine ⟨γ j u,⟨u,⟨u.property.1,hucut⟩,rfl⟩,hbcoord.symm⟩
    have hzpos : 0 < z.val ∧ z.val < 1 := by
      cases β <;> dsimp [z,endpointGermParameter] <;>
        constructor <;> nlinarith [t.property.1,t.property.2]
    have hbne : e (b.val.map z) ≠ 0 := by
      intro he
      have heq : b.val.map z = p := e.injOn hbsource hpe (he.trans he0.symm)
      have hm' : b.val.map z ∈ M.cover.branch := heq.symm ▸ hp
      rcases b.val.marked_only_at_ends z hm' with he | he
      · have hh := congrArg Subtype.val he
        change z.val = 0 at hh
        linarith [hzpos.1]
      · have hh := congrArg Subtype.val he
        change z.val = 1 at hh
        linarith [hzpos.2]
    refine ⟨?_,?_⟩
    · intro hc
      have hRef : e (b.val.map z) ∈ reference := (hanchor _ hbsource hbball).mp hc
      exact hbne (hnewref j _ hbsegment hRef)
    · intro i hi
      obtain ⟨β',hincident,hseg⟩ := (hwhole i _ hbsource hbball).mp hi
      let k : Old := ⟨(i,β'),hincident⟩
      have hray : e (b.val.map z) ∈ {x : Plane | ∃ r : ℝ, 0 ≤ r ∧ x = r • oldV k} := by
        obtain ⟨r',t',hr',ht',hrt,hxt⟩ := hseg
        exact ⟨t',ht',by simpa only [smul_zero,zero_add] using hxt.symm⟩
      have hh : e (b.val.map z) ∈ ({0} : Set Plane) := by
        rw [← hnewold j k]
        exact ⟨hbsegment,hray⟩
      exact hbne hh
#print axioms actualCountPreservingSourceClearanceInNormalizedFanChart
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Topology Metric Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Instantiate the entire canonical old/anchor chart and the actual source
clearance at an incident anchor endpoint. No chart or successful motion is supplied. -/
private theorem actualAnchorIncidentEndpointSourceClearance
    (M : HyperellipticModel E S) {I : Type} [Fintype I]
    (anchor : EssentialMarkedArc M) (old : I → EssentialMarkedArc M)
    (haold : ∀ i, (crossings M anchor (old i)).Finite)
    (hold : ∀ i j, i ≠ j → (crossings M (old i) (old j)).Finite)
    (a : EssentialMarkedArc M) (hf : (crossings M anchor a).Finite)
    (ht : ∀ x ∈ crossings M anchor a, CrossesInDisk M anchor a x)
    (p : S) (β₀ : Bool) (hβ₀ : (if β₀ then anchor.val.map 1 else anchor.val.map 0) = p)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ b : EssentialMarkedArc M,
      vertex M b = vertex M a ∧ b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
      (crossings M anchor b).Finite ∧
      (∀ x ∈ crossings M anchor b, CrossesInDisk M anchor b x) ∧
      (crossings M anchor b).ncard = (crossings M anchor a).ncard ∧
      (∀ t, a.val.map t ∉ W → b.val.map t = a.val.map t) ∧
      ∃ s : ℝ, ∃ hs : 0 < s, ∃ hshalf : s < 1/2,
        ∀ β : Bool, (if β then a.val.map 1 else a.val.map 0) = p →
          ∀ t : Interval, 0 < t.val →
            b.val.map (endpointGermParameter β s hs (by linarith) t) ∉ anchor.val.image ∧
            ∀ i, b.val.map (endpointGermParameter β s hs (by linarith) t) ∉ (old i).val.image := by
  classical
  let c : Option I → EssentialMarkedArc M := fun i => Option.casesOn i anchor old
  have hp : p ∈ M.cover.branch := by
    cases β₀
    · exact hβ₀ ▸ anchor.val.start_marked
    · exact hβ₀ ▸ anchor.val.end_marked
  have hcfinite : ∀ i j : Option I, i ≠ j → (crossings M (c i) (c j)).Finite := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact haold j
    | some i =>
      cases j with
      | none => simpa only [c,ArcSurgery.crossings,inter_comm] using haold i
      | some j => exact hold i j (fun he => hij (congrArg Option.some he))
  obtain ⟨e,hpe,he0,heW,hemarks,r,hr,hrhalf,v,hvn,hselected,hopposite,hhalf,hmeet,hgerms,
    δ,hδ,hδT,hδv,hwhole,hcompact⟩ :=
    actual_marked_endpoint_source_fan_chart M c hcfinite p hp W hW hpW (none,β₀) hβ₀
  let incidentAnchor : Bool → Prop := fun β => (if β then anchor.val.map 1 else anchor.val.map 0) = p
  let anchorLoop := decide (incidentAnchor (!β₀))
  have hloop : anchorLoop = true ↔ incidentAnchor (!β₀) := by simp only [anchorLoop,decide_eq_true_eq]
  have hδ1 : δ < 1 := by
    have hh := hδv (none,β₀) hβ₀
    rw [hselected] at hh
    norm_num [EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk] at hh
    exact hh
  have hanchorRef : ∀ x, x ∈ e.source → e x ∈ ball (0 : Plane) δ →
      (x ∈ anchor.val.image ↔ e x 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ e x 0)) := by
    intro x hx hz
    have hn : ‖e x‖ < δ := by simpa only [mem_ball,dist_zero_right] using hz
    exact (hwhole none x hx hz).trans
      (actualNormalizedAnchorFanLiteralReference incidentAnchor β₀ hβ₀
        (fun β => v (none,β)) hselected hopposite anchorLoop hloop δ hδ1 (e x) hn)
  obtain ⟨b,hclass,hb0,hb1,hbf,hbt,hbc,hout,s,hs,hshalf,hclear⟩ :=
    actualCountPreservingSourceClearanceInNormalizedFanChart M anchor a c hf ht p hp e hpe he0
      hemarks δ hδ hδT v (fun i β hi => hvn (i,β) hi) hwhole (some anchorLoop) hanchorRef
  refine ⟨b,hclass,hb0,hb1,hbf,hbt,hbc,?_,s,hs,hshalf,?_⟩
  · intro t ht
    exact hout t (fun hh => ht (heW hh))
  · intro β hβ t ht
    have hh := hclear β hβ t ht
    exact ⟨hh.1,fun i => hh.2 (some i)⟩
#print axioms actualAnchorIncidentEndpointSourceClearance
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Topology Metric Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem actualMarkedPointOffArcOfNoIncident
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M) (p : S)
    (hp : p ∈ M.cover.branch)
    (hno : ∀ β : Bool, (if β then a.val.map 1 else a.val.map 0) ≠ p) :
    p ∉ a.val.image := by
  rintro ⟨t,ht⟩
  have hm : a.val.map t ∈ M.cover.branch := ht.symm ▸ hp
  rcases a.val.marked_only_at_ends t hm with he | he
  · subst t
    exact hno false ht
  · subst t
    exact hno true ht

/-- Actual endpoint source clearance in every incidence case, with the literal
anchor crossing set cardinality and crossing disks retained. -/
private theorem actualCountPreservingSourceClearanceAtMarkedPoint
    (M : HyperellipticModel E S) {I : Type} [Fintype I]
    (anchor : EssentialMarkedArc M) (old : I → EssentialMarkedArc M)
    (haold : ∀ i, (crossings M anchor (old i)).Finite)
    (hold : ∀ i j, i ≠ j → (crossings M (old i) (old j)).Finite)
    (a : EssentialMarkedArc M) (hf : (crossings M anchor a).Finite)
    (ht : ∀ x ∈ crossings M anchor a, CrossesInDisk M anchor a x)
    (p : S) (hp : p ∈ M.cover.branch)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ b : EssentialMarkedArc M,
      vertex M b = vertex M a ∧ b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
      (crossings M anchor b).Finite ∧
      (∀ x ∈ crossings M anchor b, CrossesInDisk M anchor b x) ∧
      (crossings M anchor b).ncard = (crossings M anchor a).ncard ∧
      (∀ t, a.val.map t ∉ W → b.val.map t = a.val.map t) ∧
      ∃ s : ℝ, ∃ hs : 0 < s, ∃ hshalf : s < 1/2,
        ∀ β : Bool, (if β then a.val.map 1 else a.val.map 0) = p →
          ∀ t : Interval, 0 < t.val →
            b.val.map (endpointGermParameter β s hs (by linarith) t) ∉ anchor.val.image ∧
            ∀ i, b.val.map (endpointGermParameter β s hs (by linarith) t) ∉ (old i).val.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  by_cases hincAnchor : ∃ β : Bool, (if β then anchor.val.map 1 else anchor.val.map 0) = p
  · obtain ⟨β,hβ⟩ := hincAnchor
    exact actualAnchorIncidentEndpointSourceClearance M anchor old haold hold a hf ht p β hβ W hW hpW
  · have hAnchorNo : ∀ β : Bool, (if β then anchor.val.map 1 else anchor.val.map 0) ≠ p := by
      intro β hβ
      exact hincAnchor ⟨β,hβ⟩
    have hpAnchor : p ∉ anchor.val.image := actualMarkedPointOffArcOfNoIncident M anchor p hp hAnchorNo
    by_cases hincOld : ∃ g : I × Bool,
        (if g.2 then (old g.1).val.map 1 else (old g.1).val.map 0) = p
    · obtain ⟨g₀,hg₀⟩ := hincOld
      let W' := W ∩ anchor.val.imageᶜ
      have hW' : IsOpen W' := hW.inter (isCompact_range anchor.val.continuous).isClosed.isOpen_compl
      have hpW' : p ∈ W' := ⟨hpW,hpAnchor⟩
      obtain ⟨e,hpe,he0,heW,hemarks,r,hr,hrhalf,v,hvn,hselected,hopposite,hhalf,hmeet,hgerms,
        δ,hδ,hδT,hδv,hwhole,hcompact⟩ :=
        actual_marked_endpoint_source_fan_chart M old hold p hp W' hW' hpW' g₀ hg₀
      have hanchorEmpty : ∀ x, x ∈ e.source → e x ∈ ball (0 : Plane) δ →
          (x ∈ anchor.val.image ↔ e x ∈ (none : Option Bool).elim ∅
            (fun anchorLoop => {z : Plane | z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ z 0)})) := by
        intro x hx hz
        exact iff_false_intro (heW hx).2
      obtain ⟨b,hclass,hb0,hb1,hbf,hbt,hbc,hout,s,hs,hshalf,hclear⟩ :=
        actualCountPreservingSourceClearanceInNormalizedFanChart M anchor a old hf ht p hp e hpe he0
          hemarks δ hδ hδT v (fun i β hi => hvn (i,β) hi) hwhole none hanchorEmpty
      refine ⟨b,hclass,hb0,hb1,hbf,hbt,hbc,?_,s,hs,hshalf,hclear⟩
      intro t ht
      exact hout t (fun hh => ht (heW hh).1)
    · have hOldNo : ∀ i (β : Bool), (if β then (old i).val.map 1 else (old i).val.map 0) ≠ p := by
        intro i β hβ
        exact hincOld ⟨(i,β),hβ⟩
      have hpOld : ∀ i, p ∉ (old i).val.image :=
        fun i => actualMarkedPointOffArcOfNoIncident M (old i) p hp (hOldNo i)
      let C := anchor.val.image ∪ ⋃ i, (old i).val.image
      have hC : IsCompact C := (isCompact_range anchor.val.continuous).union
        (isCompact_iUnion (fun i => isCompact_range (old i).val.continuous))
      have hpC : p ∈ Cᶜ := by
        rintro (ha | hold)
        · exact hpAnchor ha
        · obtain ⟨i,hi⟩ := mem_iUnion.mp hold
          exact hpOld i hi
      obtain ⟨r,hr,hrhalf,hstart,hend⟩ := uniform_actual_endpoint_germs M PUnit (fun _ => a)
        p Cᶜ hC.isClosed.isOpen_compl hpC
      have hr1 : r < 1 := by linarith
      refine ⟨a,rfl,rfl,rfl,hf,ht,rfl,(fun _ _ => rfl),r,hr,hrhalf,?_⟩
      intro β hβ t ht
      have hx : a.val.map (endpointGermParameter β r hr hr1 t) ∈ Cᶜ := by
        cases β
        · apply hstart PUnit.unit hβ
          change r * t.val ≤ r
          nlinarith [t.property.2]
        · apply hend PUnit.unit hβ
          change 1-r ≤ 1-r*t.val
          nlinarith [t.property.2]
      exact ⟨fun ha => hx (Or.inl ha),fun i hi => hx (Or.inr (mem_iUnion.mpr ⟨i,hi⟩))⟩
#print axioms actualCountPreservingSourceClearanceAtMarkedPoint
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Topology Metric Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem actualEndpointGermClearanceOriginalParameter
    (M : HyperellipticModel E S) (b : EssentialMarkedArc M) (Q : S → Prop)
    (β : Bool) (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hclear : ∀ u : Interval, 0 < u.val → Q (b.val.map (endpointGermParameter β s hs hs1 u))) :
    ∀ t : Interval, 0 < t.val → t.val < 1 →
      (if β then 1-s ≤ t.val else t.val ≤ s) → Q (b.val.map t) := by
  intro t ht0 ht1 hbound
  cases β
  · let u : Interval := ⟨t.val/s,⟨div_nonneg t.property.1 hs.le,(div_le_one hs).mpr hbound⟩⟩
    have hu : 0 < u.val := div_pos ht0 hs
    have hparam : endpointGermParameter false s hs hs1 u = t := by
      apply Subtype.ext
      change s * (t.val/s) = t.val
      field_simp
    simpa only [hparam] using hclear u hu
  · change 1-s ≤ t.val at hbound
    let u : Interval := ⟨(1-t.val)/s,⟨div_nonneg (by linarith) hs.le,
        (div_le_one hs).mpr (by linarith)⟩⟩
    have hu : 0 < u.val := div_pos (by linarith) hs
    have hparam : endpointGermParameter true s hs hs1 u = t := by
      apply Subtype.ext
      change 1 - s * ((1-t.val)/s) = t.val
      field_simp
      ring
    simpa only [hparam] using hclear u hu

private theorem actualCountPreservingBothSourceEndpointCollars
    (M : HyperellipticModel E S) {I : Type} [Fintype I]
    (anchor : EssentialMarkedArc M) (old : I → EssentialMarkedArc M)
    (haold : ∀ i, (crossings M anchor (old i)).Finite)
    (hold : ∀ i j, i ≠ j → (crossings M (old i) (old j)).Finite)
    (a : EssentialMarkedArc M) (hf : (crossings M anchor a).Finite)
    (ht : ∀ x ∈ crossings M anchor a, CrossesInDisk M anchor a x) :
    ∃ b : EssentialMarkedArc M,
      vertex M b = vertex M a ∧ b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
      (crossings M anchor b).Finite ∧
      (∀ x ∈ crossings M anchor b, CrossesInDisk M anchor b x) ∧
      (crossings M anchor b).ncard = (crossings M anchor a).ncard ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
        ∀ t : Interval, 0 < t.val → t.val < 1 → t.val ≤ δ ∨ 1-δ ≤ t.val →
          b.val.map t ∉ anchor.val.image ∧ ∀ i, b.val.map t ∉ (old i).val.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let Q : S → Prop := fun x => x ∉ anchor.val.image ∧ ∀ i, x ∉ (old i).val.image
  obtain ⟨b₀,hclass₀,hb₀0,hb₀1,hbf₀,hbt₀,hbc₀,hout₀,s₀,hs₀,hs₀half,hclear₀⟩ :=
    actualCountPreservingSourceClearanceAtMarkedPoint M anchor old haold hold a hf ht
      (a.val.map 0) a.val.start_marked univ isOpen_univ (mem_univ _)
  have hs₀1 : s₀ < 1 := by linarith
  have hstart : ∀ t : Interval, 0 < t.val → t.val < 1 → t.val ≤ s₀ → Q (b₀.val.map t) :=
    actualEndpointGermClearanceOriginalParameter M b₀ Q false s₀ hs₀ hs₀1 (hclear₀ false rfl)
  by_cases hloop : a.val.map 0 = a.val.map 1
  · have hend : ∀ t : Interval, 0 < t.val → t.val < 1 → 1-s₀ ≤ t.val → Q (b₀.val.map t) :=
      actualEndpointGermClearanceOriginalParameter M b₀ Q true s₀ hs₀ hs₀1 (hclear₀ true hloop.symm)
    refine ⟨b₀,hclass₀,hb₀0,hb₀1,hbf₀,hbt₀,hbc₀,s₀,hs₀,hs₀half,?_⟩
    intro t ht0 ht1 hcol
    rcases hcol with hs | he
    · exact hstart t ht0 ht1 hs
    · exact hend t ht0 ht1 he
  · let c₀ : Interval := ⟨s₀,⟨hs₀.le,hs₀1.le⟩⟩
    let C : Set S := b₀.val.map '' Icc (0 : Interval) c₀
    have hC : IsCompact C := isCompact_Icc.image b₀.val.continuous
    have hp1C : b₀.val.map 1 ∉ C := by
      rintro ⟨t,ht,hmap⟩
      rcases b₀.val.injective_except_loop_closure t 1 hmap with he | he | he
      · have hh := congrArg Subtype.val he
        have ht' : t.val ≤ s₀ := ht.2
        change t.val = 1 at hh
        linarith
      · have hends : b₀.val.map 0 = b₀.val.map 1 :=
          (congrArg b₀.val.map (show t = (0 : Interval) from he.1)).symm.trans hmap
        exact hloop (hb₀0.symm.trans (hends.trans hb₀1))
      · have hh := congrArg Subtype.val he.2
        norm_num at hh
    obtain ⟨b₁,hclass₁,hb₁0,hb₁1,hbf₁,hbt₁,hbc₁,hout₁,s₁,hs₁,hs₁half,hclear₁⟩ :=
      actualCountPreservingSourceClearanceAtMarkedPoint M anchor old haold hold b₀ hbf₀ hbt₀
        (b₀.val.map 1) b₀.val.end_marked Cᶜ hC.isClosed.isOpen_compl hp1C
    have hs₁1 : s₁ < 1 := by linarith
    have hend : ∀ t : Interval, 0 < t.val → t.val < 1 → 1-s₁ ≤ t.val → Q (b₁.val.map t) :=
      actualEndpointGermClearanceOriginalParameter M b₁ Q true s₁ hs₁ hs₁1 (hclear₁ true rfl)
    let δ := min s₀ s₁
    have hδ : 0 < δ := lt_min hs₀ hs₁
    have hδhalf : δ < 1/2 := (min_le_left _ _).trans_lt hs₀half
    refine ⟨b₁,hclass₁.trans hclass₀,hb₁0.trans hb₀0,hb₁1.trans hb₀1,hbf₁,hbt₁,
      hbc₁.trans hbc₀,δ,hδ,hδhalf,?_⟩
    intro t ht0 ht1 hcol
    rcases hcol with hs | he
    · have htcut : t.val ≤ s₀ := hs.trans (min_le_left _ _)
      have htC : b₀.val.map t ∈ C := ⟨t,⟨t.property.1,htcut⟩,rfl⟩
      have hsame : b₁.val.map t = b₀.val.map t := hout₁ t (fun hc => hc htC)
      rw [hsame]
      exact hstart t ht0 ht1 htcut
    · exact hend t ht0 ht1 ((by dsimp [δ] at he; linarith [min_le_right s₀ s₁]))
#print axioms actualEndpointGermClearanceOriginalParameter
#print axioms actualCountPreservingBothSourceEndpointCollars
end CurveComplex.HyperellipticModel
end


namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_count_preserving_both_endpoint_clearance
(M : HyperellipticModel E S) {J : Type} [Fintype J]
(anchor : EssentialMarkedArc M) (old : J → EssentialMarkedArc M)
(hanchor : ∀ j, (ArcSurgery.crossings M anchor (old j)).Finite)
(hpair : ∀ j k, j ≠ k →
  (ArcSurgery.crossings M (old j) (old k)).Finite)
(a : EssentialMarkedArc M)
(hfinite : (ArcSurgery.crossings M anchor a).Finite)
(htransverse : ∀ p ∈ ArcSurgery.crossings M anchor a,
  ArcSurgery.CrossesInDisk M anchor a p) :
∃ H : AmbientIsotopy S,
  (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
  ∃ g : S ≃ₜ S, ∃ hfix : ∀ x, x ∈ M.cover.branch → g x=x,
    H.finalMap=g ∧ ∃ b : EssentialMarkedArc M,
    ArcSurgery.vertex M b=ArcSurgery.vertex M a ∧
    b.val.map 0=a.val.map 0 ∧ b.val.map 1=a.val.map 1 ∧
    (ArcSurgery.crossings M (anchor.transport g hfix) b).Finite ∧
    (∀ p ∈ ArcSurgery.crossings M (anchor.transport g hfix) b,
      ArcSurgery.CrossesInDisk M (anchor.transport g hfix) b p) ∧
    (ArcSurgery.crossings M (anchor.transport g hfix) b).ncard ≤
      (ArcSurgery.crossings M anchor a).ncard ∧
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
      ∀ t : Interval, 0<t.val → t.val<1 →
        t.val≤δ ∨ 1-δ≤t.val →
        b.val.map t ∉ (anchor.transport g hfix).val.image ∧
        ∀ j, b.val.map t ∉ ((old j).transport g hfix).val.image := by
  obtain ⟨b,hclass,hb0,hb1,hbf,hbt,hbc,δ,hδ,hδhalf,hclear⟩ :=
    actualCountPreservingBothSourceEndpointCollars M anchor old hanchor hpair a hfinite htransverse
  let H : AmbientIsotopy S := {
    map := ⟨fun z => z.2,continuous_snd⟩
    homeomorphism_at := fun _ => ⟨Homeomorph.refl S,fun _ => rfl⟩
    at_zero := fun _ => rfl }
  refine ⟨H,(fun _ _ _ => rfl),Homeomorph.refl S,
    (fun _ _ => rfl),rfl,b,hclass,hb0,hb1,hbf,hbt,le_of_eq hbc,δ,hδ,hδhalf,hclear⟩

end CurveComplex.HyperellipticModel
