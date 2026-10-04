import ClassificationSchoenflies.PlanarDiskCertificate
import ClassificationJordanCurve.Main
import Schoenflies.PolyArcRealize

open Set Metric

namespace ClassificationSchoenflies

private abbrev UnitDisk := closedBall (0 : Plane) 1

/-- A central diameter with its endpoints strictly inside the unit disk. -/
def centralHalfDiameter : Set Plane :=
  {z | z ∈ UnitDisk ∧ z 1 = 0 ∧ |z 0| ≤ (1 / 2 : ℝ)}

def standardArcCore : Set UnitDisk :=
  {z | (z : Plane) ∈ centralHalfDiameter}

/-- A regular neighborhood certificate remembers the arc as a pair, not merely
as a subset of some enclosing disk. -/
structure PlanarRegularArcDisk (A : Set Plane) where
  carrier : Set Plane
  pair : UnitDisk ≃ₜ carrier
  core_image : (fun z : UnitDisk => (pair z : Plane)) '' standardArcCore = A

theorem centralHalfDiameter_convex : Convex ℝ centralHalfDiameter := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · exact (convex_closedBall (0 : Plane) 1) hx.1 hy.1 ha hb hab
  · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, hx.2.1, hy.2.1, mul_zero, add_zero]
  · have hxa : |x 0| ≤ (1 / 2 : ℝ) := hx.2.2
    have hyb : |y 0| ≤ (1 / 2 : ℝ) := hy.2.2
    have hsum : |(a • x + b • y) 0| ≤ a * |x 0| + b * |y 0| := by
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      calc
        |a * x 0 + b * y 0| ≤ |a * x 0| + |b * y 0| := abs_add_le _ _
        _ = a * |x 0| + b * |y 0| := by rw [abs_mul, abs_of_nonneg ha, abs_mul, abs_of_nonneg hb]
    have hbound : a * |x 0| + b * |y 0| ≤ (1 / 2 : ℝ) := by
      nlinarith
    exact hsum.trans hbound

theorem centralHalfDiameter_nonempty : centralHalfDiameter.Nonempty := by
  refine ⟨0, ?_⟩
  simp [centralHalfDiameter, UnitDisk, Metric.mem_closedBall]

theorem centralHalfDiameter_norm_eq_abs {z : Plane} (hz : z ∈ centralHalfDiameter) :
    ‖z‖ = |z 0| := by
  have hsq : ‖z‖ ^ 2 = (z 0) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two, hz.2.1]
  rw [← sq_abs (z 0)] at hsq
  exact (sq_eq_sq₀ (norm_nonneg z) (abs_nonneg (z 0))).mp hsq

theorem centralHalfDiameter_subset_ball :
    centralHalfDiameter ⊆ ball (0 : Plane) 1 := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right, centralHalfDiameter_norm_eq_abs hz]
  linarith [hz.2.2]

theorem centralHalfDiameter_subset_interior :
    centralHalfDiameter ⊆ interior UnitDisk := by
  exact centralHalfDiameter_subset_ball.trans
    (interior_maximal ball_subset_closedBall isOpen_ball)

theorem isCompact_centralHalfDiameter : IsCompact centralHalfDiameter := by
  have hcoord : IsClosed {z : Plane | z 1 = 0} :=
    isClosed_eq (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1) continuous_const
  have hbound : IsClosed {z : Plane | |z 0| ≤ (1 / 2 : ℝ)} := by
    exact isClosed_le (continuous_abs.comp
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)) continuous_const
  have hclosed : IsClosed centralHalfDiameter := by
    change IsClosed (UnitDisk ∩ ({z : Plane | z 1 = 0} ∩
      {z : Plane | |z 0| ≤ (1 / 2 : ℝ)}))
    exact isClosed_closedBall.inter (hcoord.inter hbound)
  exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Plane) 1) hclosed (by
    intro z hz
    exact hz.1)

theorem isConnected_centralHalfDiameter : IsConnected centralHalfDiameter :=
  centralHalfDiameter_convex.isConnected centralHalfDiameter_nonempty

theorem standardArcCore_nonempty : standardArcCore.Nonempty := by
  obtain ⟨x, hx⟩ := centralHalfDiameter_nonempty
  exact ⟨⟨x, hx.1⟩, hx⟩

theorem isCompact_standardArcCore : IsCompact standardArcCore := by
  have hclosed : IsClosed standardArcCore :=
    isCompact_centralHalfDiameter.isClosed.preimage continuous_subtype_val
  exact IsCompact.of_isClosed_subset isCompact_univ hclosed (subset_univ _)

theorem standardArcCore_image_eq :
    ((↑) : UnitDisk → Plane) '' standardArcCore = centralHalfDiameter := by
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, standardArcCore]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hx.1⟩, hx, rfl⟩

theorem isConnected_standardArcCore : IsConnected standardArcCore := by
  refine ⟨?_, ?_⟩
  · exact standardArcCore_nonempty
  · have h : IsPreconnected (((↑) : UnitDisk → Plane) '' standardArcCore) := by
      rw [standardArcCore_image_eq]
      exact isConnected_centralHalfDiameter.isPreconnected
    exact Topology.IsInducing.subtypeVal.isPreconnected_image.mp h

/-- The standard core itself is a regular-arc disk, giving a concrete model
for the pair interface. -/
def centralHalfDiameterCertificate : PlanarRegularArcDisk centralHalfDiameter where
  carrier := UnitDisk
  pair := Homeomorph.refl UnitDisk
  core_image := by
    exact standardArcCore_image_eq

/-- An ambient planar straightening produces the full disk/core pair, with no
separate choice of disk homeomorphism. This is the precise downstream bridge
for a future relative arc-straightening theorem. -/
noncomputable def regularArcDisk_of_ambient (H : Plane ≃ₜ Plane)
    {A : Set Plane} (hcore : H '' centralHalfDiameter = A) :
    PlanarRegularArcDisk A where
  carrier := H '' UnitDisk
  pair := H.image UnitDisk
  core_image := by
    calc
      (fun z : UnitDisk => ((H.image UnitDisk) z : Plane)) '' standardArcCore =
          H '' (((↑) : UnitDisk → Plane) '' standardArcCore) := by
            simp only [Set.image_image]
            rfl
      _ = H '' centralHalfDiameter := by rw [standardArcCore_image_eq]
      _ = A := hcore

/-- Refine an enclosing disk to an exact arc/disk pair once the pulled-back
arc has been straightened by a self-homeomorphism of the closed disk. The
`disk` input is supplied by the polygonal enclosure certificate; `u` is the
one geometric construction that its current interface does not supply. -/
noncomputable def regularArcDisk_of_disk_straightening
    {A K : Set Plane} (hAK : A ⊆ K) (disk : UnitDisk ≃ₜ K)
    (u : UnitDisk ≃ₜ UnitDisk)
    (hu : u '' standardArcCore =
      {z : UnitDisk | (disk z : Plane) ∈ A}) : PlanarRegularArcDisk A where
  carrier := K
  pair := u.trans disk
  core_image := by
    calc
      (fun z : UnitDisk => ((u.trans disk) z : Plane)) '' standardArcCore =
          (fun z : UnitDisk => (disk z : Plane)) '' (u '' standardArcCore) := by
            rw [Set.image_image]
            rfl
      _ = (fun z : UnitDisk => (disk z : Plane)) ''
          {z : UnitDisk | (disk z : Plane) ∈ A} := by rw [hu]
      _ = A := by
        ext x
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact hz
        · intro hx
          refine ⟨disk.symm ⟨x, hAK hx⟩, ?_, ?_⟩
          · simpa using hx
          · simp

/-- For a fixed enclosing disk, producing an exact pair is equivalent to
straightening the pulled-back arc by a self-homeomorphism of that disk. -/
theorem exists_pair_map_iff_disk_straightening
    {A K : Set Plane} (hAK : A ⊆ K) (disk : UnitDisk ≃ₜ K) :
    (∃ e : UnitDisk ≃ₜ K,
      (fun z : UnitDisk => (e z : Plane)) '' standardArcCore = A) ↔
    (∃ u : UnitDisk ≃ₜ UnitDisk,
      u '' standardArcCore = {z : UnitDisk | (disk z : Plane) ∈ A}) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e.trans disk.symm, ?_⟩
    ext z
    constructor
    · rintro ⟨t, ht, htz⟩
      have hA : (e t : Plane) ∈ A := by
        rw [← he]
        exact ⟨t, ht, rfl⟩
      have hK : (e t : K) = disk z := by
        simpa using congrArg disk htz
      simpa [← hK] using hA
    · intro hz
      rw [← he] at hz
      obtain ⟨t, ht, htz⟩ := hz
      refine ⟨t, ht, ?_⟩
      apply disk.injective
      apply Subtype.ext
      simpa using htz
  · rintro ⟨u, hu⟩
    exact ⟨u.trans disk,
      (regularArcDisk_of_disk_straightening hAK disk u hu).core_image⟩


/-! ## Actual one-edge polygonal producer -/

private theorem similarity_image_segment {a b : Plane}
    (T : Plane ≃ₜ Plane) (c : ℝ) (hc : 0 < c)
    (hscale : ∀ z w, dist (T z) (T w) = c * dist z w) :
    T '' segment ℝ a b = segment ℝ (T a) (T b) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [mem_segment_iff_wbtw, ← dist_add_dist_eq_iff] at hx ⊢
    rw [hscale, hscale, hscale]
    nlinarith [hx]
  · intro y hy
    obtain ⟨x, rfl⟩ := T.surjective y
    refine ⟨x, ?_, rfl⟩
    rw [mem_segment_iff_wbtw, ← dist_add_dist_eq_iff] at hy ⊢
    rw [hscale, hscale, hscale] at hy
    nlinarith [hy]

private noncomputable def modelLeft : Plane := WithLp.toLp 2 ![(-1/2 : ℝ), 0]
private noncomputable def modelRight : Plane := WithLp.toLp 2 ![(1/2 : ℝ), 0]
private theorem modelLeft_mem_disk : modelLeft ∈ UnitDisk := by
  have hsq : ‖modelLeft‖ ^ 2 = (1 / 4 : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [modelLeft, Fin.sum_univ_two]
  have hle : ‖modelLeft‖ ≤ 1 := by nlinarith [norm_nonneg modelLeft]
  simpa only [UnitDisk, Metric.mem_closedBall, dist_zero_right] using hle
private theorem modelRight_mem_disk : modelRight ∈ UnitDisk := by
  have hsq : ‖modelRight‖ ^ 2 = (1 / 4 : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [modelRight, Fin.sum_univ_two]
  have hle : ‖modelRight‖ ≤ 1 := by nlinarith [norm_nonneg modelRight]
  simpa only [UnitDisk, Metric.mem_closedBall, dist_zero_right] using hle
private theorem centralHalfDiameter_eq_segment :
    centralHalfDiameter = segment ℝ modelLeft modelRight := by
  ext z
  rw [segment_eq_image_lineMap]
  constructor
  · intro hz
    let t : ℝ := z 0 + 1 / 2
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      rcases abs_le.mp hz.2.2 with ⟨hl, hr⟩
      constructor <;> dsimp [t] <;> linarith
    refine ⟨t, ht, ?_⟩
    ext i
    fin_cases i
    · simp [AffineMap.lineMap_apply_module, modelLeft, modelRight, t,
        smul_eq_mul]
      ring
    · simp [AffineMap.lineMap_apply_module, modelLeft, modelRight,
        hz.2.1]
  · rintro ⟨t, ht, rfl⟩
    have hball : (AffineMap.lineMap modelLeft modelRight) t ∈ UnitDisk :=
      (convex_closedBall (0 : Plane) 1).segment_subset
        modelLeft_mem_disk modelRight_mem_disk
        (by rw [segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩)
    refine ⟨hball, ?_, ?_⟩
    · simp [AffineMap.lineMap_apply_module, modelLeft, modelRight]
    · have hx : ((AffineMap.lineMap modelLeft modelRight) t) 0 = t - 1 / 2 := by
        simp [AffineMap.lineMap_apply_module, modelLeft, modelRight]
        ring
      rw [hx]
      apply abs_le.mpr
      constructor <;> rcases ht with ⟨ht0, ht1⟩ <;> linarith

private theorem exists_segment_ambient_straightening {a b : Plane} (hab : a ≠ b) :
    ∃ H : Plane ≃ₜ Plane, H '' centralHalfDiameter = segment ℝ a b := by
  obtain ⟨T, hscale, hTa, hTb⟩ := ClassificationJordanCurve.exists_similarity hab
  let D : Plane ≃ₜ Plane := Homeomorph.smulOfNeZero (1 / 2 : ℝ) (by norm_num)
  let S := T.trans D
  have hSa : S a = modelLeft := by
    rw [show S a = D (T a) from rfl, hTa]
    ext i
    fin_cases i <;> norm_num [D, modelLeft, Homeomorph.smulOfNeZero]
  have hSb : S b = modelRight := by
    rw [show S b = D (T b) from rfl, hTb]
    ext i
    fin_cases i <;> norm_num [D, modelRight, Homeomorph.smulOfNeZero]
  have hSscale : ∀ z w : Plane,
      dist (S z) (S w) = (1 / dist a b) * dist z w := by
    intro z w
    change dist ((1 / 2 : ℝ) • T z) ((1 / 2 : ℝ) • T w) = _
    rw [dist_smul₀, hscale]
    norm_num
    ring
  have hSseg : S '' segment ℝ a b = segment ℝ modelLeft modelRight := by
    rw [similarity_image_segment S (1 / dist a b)
      (one_div_pos.mpr (dist_pos.mpr hab)) hSscale]
    rw [hSa, hSb]
  refine ⟨S.symm, ?_⟩
  calc
    S.symm '' centralHalfDiameter = S.symm '' (S '' segment ℝ a b) := by
      rw [centralHalfDiameter_eq_segment, hSseg]
    _ = segment ℝ a b := by simp [Set.image_image]

/-- A straight polygonal arc has a regular disk/core pair, with its endpoints
strictly inside the disk. The ambient map is constructed from the proven
two-point similarity, rather than supplied as an assumption. -/
theorem exists_regularArcDisk_segment {a b : Plane} (hab : a ≠ b) :
    Nonempty (PlanarRegularArcDisk (segment ℝ a b)) := by
  obtain ⟨H, hH⟩ := exists_segment_ambient_straightening hab
  exact ⟨regularArcDisk_of_ambient H hH⟩

theorem exists_regularArcDisk_segment_interior {a b : Plane} (hab : a ≠ b) :
    ∃ N : PlanarRegularArcDisk (segment ℝ a b),
      segment ℝ a b ⊆ interior N.carrier := by
  obtain ⟨H, hH⟩ := exists_segment_ambient_straightening hab
  refine ⟨regularArcDisk_of_ambient H hH, ?_⟩
  change segment ℝ a b ⊆ interior (H '' UnitDisk)
  rw [← hH, ← H.image_interior]
  exact Set.image_mono centralHalfDiameter_subset_interior

/-- The one-edge certificate is an instance of the upstream polygonal-arc
presentation API. -/
theorem exists_regularArcDisk_segment_polyArc {a b : Plane} (hab : a ≠ b) :
    Schoenflies.IsPolyArcCarrier (segment ℝ a b) a b ∧
      ∃ N : PlanarRegularArcDisk (segment ℝ a b),
        segment ℝ a b ⊆ interior N.carrier := by
  exact ⟨Schoenflies.isPolyArcCarrier_segment hab,
    exists_regularArcDisk_segment_interior hab⟩

namespace PlanarRegularArcDisk

theorem arc_nonempty {A : Set Plane} (N : PlanarRegularArcDisk A) : A.Nonempty := by
  rw [← N.core_image]
  exact (standardArcCore_nonempty.image _)

theorem arc_compact {A : Set Plane} (N : PlanarRegularArcDisk A) : IsCompact A := by
  rw [← N.core_image]
  exact isCompact_standardArcCore.image
    (continuous_subtype_val.comp N.pair.continuous)

theorem arc_connected {A : Set Plane} (N : PlanarRegularArcDisk A) : IsConnected A := by
  rw [← N.core_image]
  exact isConnected_standardArcCore.image _
    (continuous_subtype_val.comp N.pair.continuous).continuousOn

end PlanarRegularArcDisk

private noncomputable def clip (x : ℝ) : ℝ := max (-(1 / 2 : ℝ)) (min x (1 / 2 : ℝ))
private noncomputable def squash (δ x : ℝ) : ℝ := clip x + δ * (x - clip x)
private theorem clip_left {x : ℝ} (h : x ≤ -(1 / 2 : ℝ)) : clip x = -(1 / 2 : ℝ) := by
  unfold clip
  have h2 : x ≤ (1 / 2 : ℝ) := by linarith
  rw [min_eq_left h2, max_eq_left h]
private theorem clip_middle {x : ℝ}
    (h1 : -(1 / 2 : ℝ) ≤ x) (h2 : x ≤ (1 / 2 : ℝ)) : clip x = x := by
  unfold clip
  rw [min_eq_left h2, max_eq_right h1]
private theorem clip_right {x : ℝ} (h : (1 / 2 : ℝ) ≤ x) : clip x = (1 / 2 : ℝ) := by
  unfold clip
  have h1 : -(1 / 2 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
  rw [min_eq_right h, max_eq_right h1]
private theorem clip_squash (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    clip (squash δ x) = clip x := by
  rcases le_total x (-(1/2 : ℝ)) with hl | hl
  · rw [clip_left hl]
    apply clip_left
    simp only [squash, clip_left hl]
    nlinarith
  · rcases le_total x (1/2 : ℝ) with hm | hr
    · rw [clip_middle hl hm]
      simp [squash, clip_middle hl hm]
    · rw [clip_right hr]
      apply clip_right
      simp only [squash, clip_right hr]
      nlinarith
private theorem squash_inverse (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    squash (1 / δ) (squash δ x) = x := by
  change clip (squash δ x) + (1 / δ) *
    (squash δ x - clip (squash δ x)) = x
  rw [clip_squash δ hδ x]
  rw [squash]
  have hne : δ ≠ 0 := ne_of_gt hδ
  field_simp
  ring
private noncomputable def squashHomeomorph (δ : ℝ) (hδ : 0 < δ) : ℝ ≃ₜ ℝ where
  toFun := squash δ
  invFun := squash (1 / δ)
  left_inv := squash_inverse δ hδ
  right_inv := by
    intro x
    simpa only [one_div_one_div] using squash_inverse (1 / δ) (one_div_pos.mpr hδ) x
  continuous_toFun := by
    unfold squash clip
    fun_prop
  continuous_invFun := by
    unfold squash clip
    fun_prop

private noncomputable def coordinateCompression (δ : ℝ) (hδ : 0 < δ) :
    Plane ≃ₜ Plane :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).toHomeomorph |>.trans
    ((Homeomorph.piCongrRight (fun i : Fin 2 =>
      if i = 0 then squashHomeomorph δ hδ
      else Homeomorph.smulOfNeZero δ (ne_of_gt hδ))).trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).toHomeomorph.symm)

private theorem coordinateCompression_apply (δ : ℝ) (hδ : 0 < δ) (z : Plane) :
    (coordinateCompression δ hδ z) 0 = squash δ (z 0) ∧
    (coordinateCompression δ hδ z) 1 = δ * z 1 := by
  constructor <;> rfl

private theorem clip_bounds (x : ℝ) :
    -(1 / 2 : ℝ) ≤ clip x ∧ clip x ≤ (1 / 2 : ℝ) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

private noncomputable def coreProjection (z : Plane) : Plane :=
  WithLp.toLp 2 ![clip (z 0), 0]

private theorem coreProjection_mem (z : Plane) : coreProjection z ∈ centralHalfDiameter := by
  have hc := clip_bounds (z 0)
  have hsq : ‖coreProjection z‖ ^ 2 = (clip (z 0)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [coreProjection, Fin.sum_univ_two]
  have hnorm : ‖coreProjection z‖ ≤ 1 := by
    nlinarith [norm_nonneg (coreProjection z), sq_nonneg (clip (z 0) + 1 / 2),
      sq_nonneg (clip (z 0) - 1 / 2)]
  exact ⟨by simpa [UnitDisk, Metric.mem_closedBall, dist_zero_right] using hnorm,
    by simp [coreProjection], by
      simp only [coreProjection, WithLp.ofLp_toLp, Matrix.cons_val_zero]
      exact abs_le.mpr hc⟩

private theorem coordinateCompression_dist_projection (δ : ℝ) (hδ : 0 < δ)
    (z : UnitDisk) :
    dist (coordinateCompression δ hδ (z : Plane)) (coreProjection z) ≤ 3 * δ := by
  have hz : ‖(z : Plane)‖ ≤ 1 := by
    have hp := z.property
    change dist (z : Plane) (0 : Plane) ≤ 1 at hp
    simpa only [dist_zero_right] using hp
  have hx : |(z : Plane) 0| ≤ 1 :=
    (PiLp.norm_apply_le (z : Plane) 0).trans hz
  have hy : |(z : Plane) 1| ≤ 1 :=
    (PiLp.norm_apply_le (z : Plane) 1).trans hz
  have hc := clip_bounds ((z : Plane) 0)
  have hsq : dist (coordinateCompression δ hδ (z : Plane)) (coreProjection z) ^ 2 =
      (δ * ((z : Plane) 0 - clip ((z : Plane) 0))) ^ 2 +
        (δ * (z : Plane) 1) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two, coreProjection, coordinateCompression_apply,
      squash, pow_two]
  have hdx : |(z : Plane) 0 - clip ((z : Plane) 0)| ≤ 3 / 2 := by
    rcases abs_le.mp hx with ⟨hx1,hx2⟩
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hdxsq : (((z : Plane) 0 - clip ((z : Plane) 0))) ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hdx)
      (show 0 ≤ (3 / 2 : ℝ) + |(z : Plane) 0 - clip ((z : Plane) 0)| by positivity)
    nlinarith [sq_abs ((z : Plane) 0 - clip ((z : Plane) 0))]
  have hysq : ((z : Plane) 1) ^ 2 ≤ (1 : ℝ) ^ 2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hy)
      (show 0 ≤ (1 : ℝ) + |(z : Plane) 1| by positivity)
    nlinarith [sq_abs ((z : Plane) 1)]
  have hm1 := mul_le_mul_of_nonneg_left hdxsq (sq_nonneg δ)
  have hm2 := mul_le_mul_of_nonneg_left hysq (sq_nonneg δ)
  nlinarith [sq_nonneg (dist (coordinateCompression δ hδ (z : Plane))
    (coreProjection z)), sq_nonneg δ]

private theorem coordinateCompression_core_fixed (δ : ℝ) (hδ : 0 < δ)
    {z : Plane} (hz : z ∈ centralHalfDiameter) :
    coordinateCompression δ hδ z = z := by
  ext i
  fin_cases i
  · have hcoord := (coordinateCompression_apply δ hδ z).1
    have hleft : -(1 / 2 : ℝ) ≤ z 0 := (abs_le.mp hz.2.2).1
    have hright : z 0 ≤ (1 / 2 : ℝ) := (abs_le.mp hz.2.2).2
    have heq : (coordinateCompression δ hδ z) 0 = z 0 := by
      rw [hcoord]
      simp [squash, clip_middle hleft hright]
    simpa using heq
  · have hcoord := (coordinateCompression_apply δ hδ z).2
    have heq : (coordinateCompression δ hδ z) 1 = z 1 := by
      rw [hcoord, hz.2.1]
      simp
    simpa using heq

private theorem coordinateCompression_core_image (δ : ℝ) (hδ : 0 < δ) :
    coordinateCompression δ hδ '' centralHalfDiameter = centralHalfDiameter := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [coordinateCompression_core_fixed δ hδ hz]
  · intro hx
    exact ⟨x, hx, coordinateCompression_core_fixed δ hδ hx⟩

/-- For any straight arc and any finite set disjoint from it, a regular
arc/disk pair can be made small enough to avoid that set. -/
theorem exists_regularArcDisk_segment_avoid_finite {a b : Plane} (hab : a ≠ b)
    (F : Finset Plane) (hF : Disjoint (segment ℝ a b) (F : Set Plane)) :
    ∃ N : PlanarRegularArcDisk (segment ℝ a b),
      segment ℝ a b ⊆ interior N.carrier ∧ Disjoint N.carrier (F : Set Plane) := by
  obtain ⟨H, hH⟩ := exists_segment_ambient_straightening hab
  let U : Set Plane := H ⁻¹' (F : Set Plane)ᶜ
  have hUopen : IsOpen U :=
    (F.finite_toSet.isClosed.isOpen_compl).preimage H.continuous
  have hCU : centralHalfDiameter ⊆ U := by
    intro z hz
    have hzA : H z ∈ segment ℝ a b := by
      rw [← hH]
      exact ⟨z, hz, rfl⟩
    exact Set.disjoint_left.mp hF hzA
  obtain ⟨ε, hε, hthick⟩ :=
    isCompact_centralHalfDiameter.exists_cthickening_subset_open hUopen hCU
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let G : Plane ≃ₜ Plane := coordinateCompression δ hδ
  let K : Plane ≃ₜ Plane := G.trans H
  have hKcore : K '' centralHalfDiameter = segment ℝ a b := by
    calc
      K '' centralHalfDiameter = H '' (G '' centralHalfDiameter) := by
        rw [Set.image_image]
        rfl
      _ = segment ℝ a b := by rw [coordinateCompression_core_image δ hδ, hH]
  refine ⟨regularArcDisk_of_ambient K hKcore, ?_, ?_⟩
  · change segment ℝ a b ⊆ interior (K '' UnitDisk)
    rw [← hKcore, ← K.image_interior]
    exact Set.image_mono centralHalfDiameter_subset_interior
  · apply Set.disjoint_left.mpr
    intro x hx hxF
    change x ∈ K '' UnitDisk at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hnear : G z ∈ cthickening ε centralHalfDiameter := by
      apply Metric.mem_cthickening_of_dist_le (G z) (coreProjection z) ε
        centralHalfDiameter (coreProjection_mem z)
      have hd := coordinateCompression_dist_projection δ hδ ⟨z, hz⟩
      change dist (G z) (coreProjection z) ≤ 3 * δ at hd
      dsimp [δ] at hd
      linarith
    have hnotF : H (G z) ∉ (F : Set Plane) := hthick hnear
    exact hnotF hxF

/-- Endpoint marks may belong to the finite marked set. All other marks are
kept out of the regular disk. -/
theorem exists_regularArcDisk_segment_avoid_other_marks {a b : Plane}
    (hab : a ≠ b) (F : Finset Plane)
    (hF : ∀ x ∈ F, x ∈ segment ℝ a b → x = a ∨ x = b) :
    ∃ N : PlanarRegularArcDisk (segment ℝ a b),
      segment ℝ a b ⊆ interior N.carrier ∧
      Disjoint N.carrier ((F.erase a).erase b : Set Plane) := by
  have hdisj : Disjoint (segment ℝ a b) ((F.erase a).erase b : Set Plane) := by
    apply Set.disjoint_left.mpr
    intro x hx hxF
    have hxb : x ≠ b := (Finset.mem_erase.mp hxF).1
    have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hxF).2).1
    have hxmem : x ∈ F :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hxF).2).2
    rcases hF x hxmem hx with rfl | rfl
    · exact hxa rfl
    · exact hxb rfl
  exact exists_regularArcDisk_segment_avoid_finite hab ((F.erase a).erase b) hdisj
end ClassificationSchoenflies
