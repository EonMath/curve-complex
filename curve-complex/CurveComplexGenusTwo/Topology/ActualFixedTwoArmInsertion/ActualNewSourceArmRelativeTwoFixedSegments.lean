import CurveComplexGenusTwo.Topology.Smoothing.JordanSectorCrosscutExtensionHeader
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

theorem actual_new_source_arm_relative_to_two_fixed_segments
    {K : Type} [Fintype K]
    (v : Fin 2 → Plane) (hv : ∀ j, v j ≠ 0)
    (hfan : segment ℝ (0 : Plane) (v 0) ∩
      segment ℝ (0 : Plane) (v 1) = {0})
    (γ : Interval → Plane) (hγ : Topology.IsClosedEmbedding γ)
    (hzero : γ 0 = 0)
    (havoid : ∀ t : Interval, 0 < t.val →
      γ t ∉ segment ℝ (0 : Plane) (v 0) ∪
        segment ℝ (0 : Plane) (v 1))
    (oldVector : K → Plane) (hold : ∀ k, oldVector k ≠ 0)
    (V : Set Plane) (hV : IsOpen V) (h0V : (0 : Plane) ∈ V) :
    ∃ F : Plane ≃ₜ Plane, ∃ R : ℝ,
      0 < R ∧ closedBall (0 : Plane) R ⊆ V ∧
      R < ‖v 0‖ ∧ R < ‖v 1‖ ∧
      F 0 = 0 ∧ (∀ x, x ∉ ball (0 : Plane) R → F x = x) ∧
      (∀ x ∈ segment ℝ (0 : Plane) (v 0) ∪
        segment ℝ (0 : Plane) (v 1), F x = x) ∧
      ∃ cut : Interval, ∃ vector : Plane,
        0 < cut.val ∧ cut.val < 1 ∧ vector ≠ 0 ∧
        F '' (γ '' Icc 0 cut) = segment ℝ 0 vector ∧
        segment ℝ 0 vector ∩
          (segment ℝ (0 : Plane) (v 0) ∪
            segment ℝ (0 : Plane) (v 1)) = {0} ∧
        ∀ k, segment ℝ 0 vector ∩
          {z | ∃ s : ℝ, 0 ≤ s ∧ z = s • oldVector k} = {0} := by
  obtain ⟨R, hR, hRV, hRv0, hRv1, hRend⟩ :=
    actualChooseTwoArmSupportRadius v hv γ hγ hzero V hV h0V
  have hRv : ∀ j : Fin 2, R < ‖v j‖ := by
    intro j
    fin_cases j
    · exact hRv0
    · exact hRv1
  obtain ⟨cut, hc, hc1, hbSphere, hsector⟩ :=
    actualOriginalPrefixInOneActualSector v hv hfan γ hγ hzero havoid hR hRv hRend
  have hd : Plane.IsDirection (Plane.dir (v 0)) := Plane.isDirection_dir (hv 0)
  have hw : Plane.IsDirection (Plane.dir (v 1)) := Plane.isDirection_dir (hv 1)
  have hdw : Plane.dir (v 0) ≠ Plane.dir (v 1) :=
    actualTwoFixedDirectionsDistinct v hv hfan hR hRv
  rcases hsector with ⟨hbArc, hprefix⟩ | ⟨hbArc, hprefix⟩
  · have hPfixed :
        segment ℝ (0 : Plane) (R • Plane.dir (v 0)) ∪
          segment ℝ (0 : Plane) (R • Plane.dir (v 1)) ⊆
        segment ℝ (R • Plane.dir (v 0)) (0 : Plane) ∪
          segment ℝ (0 : Plane) (R • Plane.dir (v 1)) := by
      intro z hz
      rcases hz with hz0 | hz1
      · exact Or.inl (by simpa only [segment_symm] using hz0)
      · exact Or.inr hz1
    obtain ⟨F, vector, hF0, hfixBall, hfixArms,
      c, hc0, hc1, hvec, himage, hfixed, holdray⟩ :=
      actualNewSourceArmAtDirectedRadius oldVector v hv hR hRv γ hγ hzero
        hRend cut hc hbSphere hd hw hdw hbArc hprefix hPfixed
    exact ⟨F, R, hR, hRV, hRv0, hRv1, hF0, hfixBall, hfixArms,
      c, vector, hc0, hc1, hvec, himage, hfixed, holdray⟩
  · have hPfixed :
        segment ℝ (0 : Plane) (R • Plane.dir (v 0)) ∪
          segment ℝ (0 : Plane) (R • Plane.dir (v 1)) ⊆
        segment ℝ (R • Plane.dir (v 1)) (0 : Plane) ∪
          segment ℝ (0 : Plane) (R • Plane.dir (v 0)) := by
      intro z hz
      rcases hz with hz0 | hz1
      · exact Or.inr hz0
      · exact Or.inl (by simpa only [segment_symm] using hz1)
    obtain ⟨F, vector, hF0, hfixBall, hfixArms,
      c, hc0, hc1, hvec, himage, hfixed, holdray⟩ :=
      actualNewSourceArmAtDirectedRadius oldVector v hv hR hRv γ hγ hzero
        hRend cut hc hbSphere hw hd hdw.symm hbArc hprefix hPfixed
    exact ⟨F, R, hR, hRV, hRv0, hRv1, hF0, hfixBall, hfixArms,
      c, vector, hc0, hc1, hvec, himage, hfixed, holdray⟩

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
