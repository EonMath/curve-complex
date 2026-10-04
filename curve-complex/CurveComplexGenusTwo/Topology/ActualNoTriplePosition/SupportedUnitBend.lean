import CurveComplexGenusTwo.Topology.ActualNoTriplePosition.PlanarFanBend
import CurveComplexGenusTwo.Topology.ActualNoTriplePosition.RadialHorizontalCrossing
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedFiniteSurfaceReplacement
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Schoenflies

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

noncomputable section

/-- A genuine marked-surface arc replacement by the unit graph bend. The
chart hypothesis is the whole old trace in the square, as supplied by the
radial-core normalization after rescaling. -/
theorem actual_supported_unit_bend
    (M : HyperellipticModel E S) (c : EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane)
    (hmarks : Disjoint F.source (M.cover.branch : Set S))
    (hSquare : Plane.closedSquare 0 1 ⊆ F.target)
    (htrace : {x : S | x ∈ F.source ∧ F x ∈ Plane.closedSquare 0 1} ∩ c.val.image =
      {x : S | x ∈ F.source ∧ F x ∈
        segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)})
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ d : EssentialMarkedArc M,
      ArcSurgery.vertex M d = ArcSurgery.vertex M c ∧
      d.val.image =
        (c.val.image \
          {x : S | x ∈ F.source ∧ F x ∈
            segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}) ∪
          {x : S | x ∈ F.source ∧ F x ∈ bendGraph (1 / 2) 1 δ} := by
  let A : Set Plane := segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)
  let B : Set Plane := bendGraph (1 / 2) 1 δ
  have hne : Plane.mk (-1) 0 ≠ Plane.mk 1 0 := by
    intro he
    have h := congrArg (fun z : Plane => z 0) he
    norm_num [Plane.mk] at h
  have hA : IsArcBetween A (Plane.mk (-1) 0) (Plane.mk 1 0) :=
    Schoenflies.isArcBetween_segment hne
  have hB : IsArcBetween B (Plane.mk (-1) 0) (Plane.mk 1 0) :=
    unit_bend_is_arc δ
  obtain ⟨H,d,himage,hclass,hfix,hformula⟩ :=
    actual_marked_finite_surface_replacement M c Unit (fun _ => F)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim)
      (fun _ => hmarks) (fun _ => hSquare)
      A hA unit_horizontal_inside_square (fun _ => htrace)
      (fun _ => B) (fun _ => hB) (fun _ => unit_bend_inside_square δ hδ hδ1)
  refine ⟨d,hclass,?_⟩
  rw [hformula]
  ext x
  simp [A,B]

/-- The supported bend changes crossings only through the removed diameter
and inserted graph. This applies to every fixed comparison arc, including the
literal anchor. -/
theorem actual_supported_unit_bend_crossings_formula
    (M : HyperellipticModel E S) (c d b : EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane)
    (δ : ℝ)
    (himage : d.val.image =
      (c.val.image \
        {x : S | x ∈ F.source ∧ F x ∈
          segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}) ∪
        {x : S | x ∈ F.source ∧ F x ∈ bendGraph (1 / 2) 1 δ}) :
    crossings M d b =
      (crossings M c b \
        {x : S | x ∈ F.source ∧ F x ∈
          segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}) ∪
        ({x : S | x ∈ F.source ∧ F x ∈ bendGraph (1 / 2) 1 δ} ∩
          arcInterior M b) := by
  ext x
  by_cases hxmark : x ∈ (M.cover.branch : Set S)
  · simp [crossings, arcInterior, himage, hxmark]
  · simp only [crossings, arcInterior, himage, Set.mem_union,
      Set.mem_inter_iff, Set.mem_diff, Set.mem_setOf_eq]
    tauto

theorem actual_supported_unit_bend_nonincident_crossings
    (M : HyperellipticModel E S) (c d b : EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane) (δ : ℝ)
    (havoid : Disjoint F.source b.val.image)
    (himage : d.val.image =
      (c.val.image \
        {x : S | x ∈ F.source ∧ F x ∈
          segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}) ∪
        {x : S | x ∈ F.source ∧ F x ∈ bendGraph (1 / 2) 1 δ}) :
    crossings M d b = crossings M c b := by
  rw [actual_supported_unit_bend_crossings_formula M c d b F δ himage]
  ext x
  constructor
  · rintro (⟨hx,_⟩ | ⟨⟨hxF,_⟩,hxb⟩)
    · exact hx
    · exact False.elim (Set.disjoint_left.mp havoid hxF hxb.1)
  · intro hx
    left
    refine ⟨hx,?_⟩
    rintro ⟨hxF,_⟩
    exact Set.disjoint_left.mp havoid hxF hx.2.1

theorem actual_unit_square_support_compact
    (M : HyperellipticModel E S)
    (F : OpenPartialHomeomorph S Plane)
    (hSquare : Plane.closedSquare 0 1 ⊆ F.target) :
    IsCompact (F.symm '' Plane.closedSquare 0 1) := by
  exact (isCompact_closedSquare 0 1).image_of_continuousOn
    (F.continuousOn_symm.mono hSquare)

theorem actual_supported_unit_bend_agrees_outside_square
    (M : HyperellipticModel E S) (c d : EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane)
    (hSquare : Plane.closedSquare 0 1 ⊆ F.target)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (himage : d.val.image =
      (c.val.image \
        {x : S | x ∈ F.source ∧ F x ∈
          segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}) ∪
        {x : S | x ∈ F.source ∧ F x ∈ bendGraph (1 / 2) 1 δ}) :
    ∀ x, x ∉ F.symm '' Plane.closedSquare 0 1 →
      (x ∈ d.val.image ↔ x ∈ c.val.image) := by
  intro x hxK
  have hxnotSquare (hxF : x ∈ F.source) :
      F x ∉ Plane.closedSquare 0 1 := by
    intro hxSq
    exact hxK ⟨F x,hxSq,F.left_inv hxF⟩
  have hxnotA : x ∉ {y : S | y ∈ F.source ∧
      F y ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)} := by
    rintro ⟨hxF,hxA⟩
    exact hxnotSquare hxF ((unit_horizontal_segment_iff (F x)).1 hxA).1
  have hxnotB : x ∉ {y : S | y ∈ F.source ∧
      F y ∈ bendGraph (1 / 2) 1 δ} := by
    rintro ⟨hxF,hxB⟩
    exact hxnotSquare hxF (unit_bend_subset_closed_square δ hδ hδ1 hxB)
  rw [himage]
  simp only [Set.mem_union,Set.mem_diff,Set.mem_setOf_eq]
  tauto

theorem actual_supported_unit_bend_preserves_count
    (M : HyperellipticModel E S) (c d b : EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane)
    (δ : ℝ) (p q : S)
    (himage : d.val.image =
      (c.val.image \
        {x : S | x ∈ F.source ∧ F x ∈
          segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}) ∪
        {x : S | x ∈ F.source ∧ F x ∈ bendGraph (1 / 2) 1 δ})
    (hfinite : (crossings M c b).Finite)
    (hp : p ∈ crossings M c b)
    (hold : crossings M c b ∩
      {x : S | x ∈ F.source ∧ F x ∈
        segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)} = {p})
    (hnew : {x : S | x ∈ F.source ∧ F x ∈ bendGraph (1 / 2) 1 δ} ∩
      arcInterior M b = {q})
    (hq : q ∉ crossings M c b) :
    (crossings M d b).Finite ∧
      (crossings M d b).ncard = (crossings M c b).ncard := by
  let A : Set S := {x | x ∈ F.source ∧ F x ∈
    segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}
  have hremove : crossings M c b \ A = crossings M c b \ {p} := by
    ext x
    constructor
    · rintro ⟨hx,hxA⟩
      refine ⟨hx,?_⟩
      intro hxp
      subst x
      have hpa : p ∈ crossings M c b ∩ A := by
        rw [hold]
        exact Set.mem_singleton p
      exact hxA hpa.2
    · rintro ⟨hx,hxp⟩
      refine ⟨hx,?_⟩
      intro hxA
      have hxp' : x ∈ ({p} : Set S) := by
        rw [← hold]
        exact ⟨hx,hxA⟩
      exact hxp hxp'
  have hformula := actual_supported_unit_bend_crossings_formula M c d b F δ himage
  rw [hremove,hnew] at hformula
  have hqout : q ∉ crossings M c b \ {p} := fun h => hq h.1
  have hdfin : (crossings M d b).Finite := by
    rw [hformula]
    simpa [Set.union_comm] using (hfinite.sdiff).insert q
  refine ⟨hdfin,?_⟩
  rw [hformula]
  rw [Set.union_comm]
  change (insert q (crossings M c b \ {p})).ncard = _
  rw [Set.ncard_insert_of_notMem hqout hfinite.sdiff,
    Set.ncard_sdiff_singleton_add_one hp hfinite]

theorem actual_unit_bend_new_crossing_singleton
    (M : HyperellipticModel E S) (b : EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane)
    (hmarks : Disjoint F.source (M.cover.branch : Set S))
    (hSquare : Plane.closedSquare 0 1 ⊆ F.target)
    (v w : Plane) (hv : 0 < v 1) (hw : w 1 < 0)
    (hmodel : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ b.val.image ↔ F x ∈ segment ℝ (0 : Plane) v ∪
        segment ℝ (0 : Plane) w))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsmall : δ * |v 0| < (1 / 2 : ℝ) * v 1)
    (hinside : δ < v 1) :
    {x : S | x ∈ F.source ∧ F x ∈ bendGraph (1 / 2) 1 δ} ∩
      arcInterior M b = {F.symm (Plane.mk (δ * v 0 / v 1) δ)} := by
  let z : Plane := Plane.mk (δ * v 0 / v 1) δ
  have hupper := bendGraph_upper_segment_singleton (1 / 2) 1 δ
    (by norm_num) (by norm_num) hδ v hv hsmall hinside
  have hlower := bendGraph_lower_segment_disjoint (1 / 2) 1 δ
    (by norm_num) (by norm_num) hδ w hw
  have hBsq := unit_bend_subset_closed_square δ hδ hδ1
  have hzcontact : z ∈ bendGraph (1 / 2) 1 δ ∩ segment ℝ (0 : Plane) v := by
    rw [hupper]
    exact Set.mem_singleton z
  have hzTarget : z ∈ F.target := hSquare (hBsq hzcontact.1)
  have hzSource : F.symm z ∈ F.source := F.map_target hzTarget
  have hzValue : F (F.symm z) = z := F.right_inv hzTarget
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨⟨hxSource,hxB⟩,hxb⟩ := hx
    have hxmodel : F x ∈ segment ℝ (0 : Plane) v ∪
        segment ℝ (0 : Plane) w :=
      (hmodel x hxSource (hBsq hxB)).mp hxb.1
    have hxz : F x = z := by
      rcases hxmodel with hxv | hxw
      · exact Set.mem_singleton_iff.mp (hupper ▸ ⟨hxB,hxv⟩)
      · exact False.elim (Set.disjoint_left.mp hlower hxB hxw)
    have hxself : F.symm (F x) = x := F.left_inv hxSource
    exact Set.mem_singleton_iff.mpr (hxself ▸ congrArg F.symm hxz)
  · intro x hx
    have he : x = F.symm z := Set.mem_singleton_iff.mp hx
    subst x
    refine ⟨⟨hzSource,by rw [hzValue]; exact hzcontact.1⟩,?_⟩
    have hzb : F.symm z ∈ b.val.image :=
      (hmodel _ hzSource (by rw [hzValue]; exact hBsq hzcontact.1)).mpr
        (by rw [hzValue]; exact Or.inl hzcontact.2)
    exact ⟨hzb,fun hm => Set.disjoint_left.mp hmarks hzSource hm⟩

theorem actual_unit_bend_old_crossing_singleton
    (M : HyperellipticModel E S) (c b : EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane) (p : S)
    (hpF : p ∈ F.source) (hFp : F p = 0)
    (hmarks : Disjoint F.source (M.cover.branch : Set S))
    (v w : Plane) (hv : v 1 ≠ 0) (hw : w 1 ≠ 0)
    (haxis : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ c.val.image ↔ F x 1 = 0))
    (hmodel : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ b.val.image ↔ F x ∈ segment ℝ (0 : Plane) v ∪
        segment ℝ (0 : Plane) w)) :
    crossings M c b ∩
      {x : S | x ∈ F.source ∧ F x ∈
        segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)} = {p} := by
  have hzeroSquare : (0 : Plane) ∈ Plane.closedSquare 0 1 := by
    rw [Schoenflies.mem_closedSquare_zero_one]
    norm_num [Plane.supNorm]
  have hzeroA : (0 : Plane) ∈
      segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) := by
    rw [segment_eq_image']
    refine ⟨(1 / 2 : ℝ),by norm_num,?_⟩
    ext i
    fin_cases i <;> norm_num [Plane.mk]
  have hASquare : segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) ⊆
      Plane.closedSquare 0 1 := by
    intro z hz
    rw [Schoenflies.mem_closedSquare_zero_one]
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    have hcoord0 : (AffineMap.lineMap (Plane.mk (-1) 0) (Plane.mk 1 0) t) 0 = -1 + 2 * t := by
      simp [AffineMap.lineMap_apply_module,Plane.mk]
      ring
    have hcoord1 : (AffineMap.lineMap (Plane.mk (-1) 0) (Plane.mk 1 0) t) 1 = 0 := by
      simp [AffineMap.lineMap_apply_module,Plane.mk]
    change max |(AffineMap.lineMap (Plane.mk (-1) 0) (Plane.mk 1 0) t) 0|
      |(AffineMap.lineMap (Plane.mk (-1) 0) (Plane.mk 1 0) t) 1| ≤ 1
    rw [hcoord0,hcoord1,abs_zero]
    exact max_le (abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩) (by norm_num)
  apply Set.Subset.antisymm
  · rintro x ⟨hcross,hxA⟩
    have hxmodel : F x ∈ segment ℝ (0 : Plane) v ∪
        segment ℝ (0 : Plane) w :=
      (hmodel x hxA.1 (hASquare hxA.2)).mp hcross.2.1
    have hx0 : F x = 0 := by
      rcases hxmodel with hxv | hxw
      · exact Set.mem_singleton_iff.mp
          ((horizontal_segment_radial_intersection_zero v hv) ▸ ⟨hxA.2,hxv⟩)
      · exact Set.mem_singleton_iff.mp
          ((horizontal_segment_radial_intersection_zero w hw) ▸ ⟨hxA.2,hxw⟩)
    exact Set.mem_singleton_iff.mpr (F.injOn hxA.1 hpF (hx0.trans hFp.symm))
  · intro x hx
    have hxp : x = p := Set.mem_singleton_iff.mp hx
    subst x
    have hpmark : p ∉ (M.cover.branch : Set S) :=
      fun hm => Set.disjoint_left.mp hmarks hpF hm
    have hpc : p ∈ c.val.image :=
      (haxis p hpF (hFp ▸ hzeroSquare)).mpr (by rw [hFp]; rfl)
    have hpb : p ∈ b.val.image :=
      (hmodel p hpF (hFp ▸ hzeroSquare)).mpr
        (by rw [hFp]; exact Or.inl (left_mem_segment ℝ (0 : Plane) v))
    exact ⟨⟨⟨hpc,hpmark⟩,⟨hpb,hpmark⟩⟩,⟨hpF,hFp ▸ hzeroA⟩⟩

theorem actual_unit_bend_radial_crossing_set
    (M : HyperellipticModel E S) (c d b : EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane) (p : S)
    (hpF : p ∈ F.source) (hFp : F p = 0)
    (hmarks : Disjoint F.source (M.cover.branch : Set S))
    (hSquare : Plane.closedSquare 0 1 ⊆ F.target)
    (v w : Plane) (hv : 0 < v 1) (hw : w 1 < 0)
    (haxis : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ c.val.image ↔ F x 1 = 0))
    (hmodel : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ b.val.image ↔ F x ∈ segment ℝ (0 : Plane) v ∪
        segment ℝ (0 : Plane) w))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsmall : δ * |v 0| < (1 / 2 : ℝ) * v 1)
    (hinside : δ < v 1)
    (himage : d.val.image =
      (c.val.image \
        {x : S | x ∈ F.source ∧ F x ∈
          segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}) ∪
        {x : S | x ∈ F.source ∧ F x ∈ bendGraph (1 / 2) 1 δ}) :
    crossings M d b =
      (crossings M c b \ {p}) ∪
        {F.symm (Plane.mk (δ * v 0 / v 1) δ)} := by
  have hold := actual_unit_bend_old_crossing_singleton M c b F p hpF hFp
    hmarks v w (ne_of_gt hv) (ne_of_lt hw) haxis hmodel
  have hnew := actual_unit_bend_new_crossing_singleton M b F hmarks hSquare
    v w hv hw hmodel δ hδ hδ1 hsmall hinside
  rw [actual_supported_unit_bend_crossings_formula M c d b F δ himage,hnew]
  congr 1
  ext x
  constructor
  · rintro ⟨hx,hxA⟩
    refine ⟨hx,?_⟩
    intro hxp
    subst x
    have hpA : p ∈ crossings M c b ∩
        {y : S | y ∈ F.source ∧
          F y ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)} := by
      rw [hold]
      exact Set.mem_singleton p
    exact hxA hpA.2
  · rintro ⟨hx,hxp⟩
    refine ⟨hx,?_⟩
    intro hxA
    have hxP : x ∈ ({p} : Set S) := by
      rw [← hold]
      exact ⟨hx,hxA⟩
    exact hxp hxP

theorem actual_unit_square_old_crossing_unique
    (M : HyperellipticModel E S) (c b : EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane) (p : S)
    (hpF : p ∈ F.source) (hFp : F p = 0)
    (hmarks : Disjoint F.source (M.cover.branch : Set S))
    (hSquare : Plane.closedSquare 0 1 ⊆ F.target)
    (v w : Plane) (hv : 0 < v 1) (hw : w 1 < 0)
    (haxis : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ c.val.image ↔ F x 1 = 0))
    (hmodel : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ b.val.image ↔ F x ∈ segment ℝ (0 : Plane) v ∪
        segment ℝ (0 : Plane) w)) :
    ∀ q ∈ crossings M c b,
      q ∈ F.symm '' Plane.closedSquare 0 1 → q = p := by
  have hold := actual_unit_bend_old_crossing_singleton M c b F p hpF hFp
    hmarks v w (ne_of_gt hv) (ne_of_lt hw) haxis hmodel
  intro q hqcross hqK
  obtain ⟨z,hzSq,rfl⟩ := hqK
  have hzTarget : z ∈ F.target := hSquare hzSq
  have hqSource : F.symm z ∈ F.source := F.map_target hzTarget
  have hqValue : F (F.symm z) = z := F.right_inv hzTarget
  have hz0 : z 1 = 0 := by
    have h := (haxis _ hqSource (by rw [hqValue]; exact hzSq)).mp hqcross.1.1
    rwa [hqValue] at h
  have hzA : z ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) :=
    (unit_horizontal_segment_iff z).2 ⟨hzSq,hz0⟩
  have hqhold : F.symm z ∈ crossings M c b ∩
      {x : S | x ∈ F.source ∧
        F x ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)} :=
    ⟨hqcross,hqSource,by rw [hqValue]; exact hzA⟩
  exact Set.mem_singleton_iff.mp (hold ▸ hqhold)

theorem actual_unit_bend_preserves_radial_comparison_count
    (M : HyperellipticModel E S) (c d b : EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane) (p : S)
    (hpF : p ∈ F.source) (hFp : F p = 0)
    (hmarks : Disjoint F.source (M.cover.branch : Set S))
    (hSquare : Plane.closedSquare 0 1 ⊆ F.target)
    (v w : Plane) (hv : 0 < v 1) (hw : w 1 < 0)
    (haxis : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ c.val.image ↔ F x 1 = 0))
    (hmodel : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ b.val.image ↔ F x ∈ segment ℝ (0 : Plane) v ∪
        segment ℝ (0 : Plane) w))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsmall : δ * |v 0| < (1 / 2 : ℝ) * v 1)
    (hinside : δ < v 1)
    (himage : d.val.image =
      (c.val.image \
        {x : S | x ∈ F.source ∧ F x ∈
          segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}) ∪
        {x : S | x ∈ F.source ∧ F x ∈ bendGraph (1 / 2) 1 δ})
    (hfinite : (crossings M c b).Finite) :
    (crossings M d b).Finite ∧
      (crossings M d b).ncard = (crossings M c b).ncard := by
  let z : Plane := Plane.mk (δ * v 0 / v 1) δ
  let q : S := F.symm z
  have hold := actual_unit_bend_old_crossing_singleton M c b F p hpF hFp
    hmarks v w (ne_of_gt hv) (ne_of_lt hw) haxis hmodel
  have hp : p ∈ crossings M c b := by
    have h : p ∈ ({p} : Set S) := Set.mem_singleton p
    exact (hold.symm ▸ h).1
  have hnew := actual_unit_bend_new_crossing_singleton M b F hmarks hSquare
    v w hv hw hmodel δ hδ hδ1 hsmall hinside
  have hqnot : q ∉ crossings M c b := by
    intro hqcross
    have hzB : z ∈ bendGraph (1 / 2) 1 δ := by
      have hupper := bendGraph_upper_segment_singleton (1 / 2) 1 δ
        (by norm_num) (by norm_num) hδ v hv hsmall hinside
      have hz : z ∈ ({z} : Set Plane) := Set.mem_singleton z
      exact (hupper.symm ▸ hz).1
    have hzSquare : z ∈ Plane.closedSquare 0 1 :=
      unit_bend_subset_closed_square δ hδ hδ1 hzB
    have hzTarget : z ∈ F.target := hSquare hzSquare
    have hqSource : q ∈ F.source := F.map_target hzTarget
    have hqValue : F q = z := F.right_inv hzTarget
    have hqaxis := (haxis q hqSource (by rw [hqValue]; exact hzSquare)).mp hqcross.1.1
    rw [hqValue] at hqaxis
    change δ = 0 at hqaxis
    exact (ne_of_gt hδ) hqaxis
  exact actual_supported_unit_bend_preserves_count M c d b F δ p q himage
    hfinite hp hold hnew hqnot

/-- One actual bend preserves the count against an entire finite family,
including a literal anchor if it is one of the comparison labels. -/
theorem actual_unit_bend_finite_family_count
    (M : HyperellipticModel E S) {J : Type} [Fintype J]
    (c : EssentialMarkedArc M) (b : J → EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane) (p : S)
    (hpF : p ∈ F.source) (hFp : F p = 0)
    (hmarks : Disjoint F.source (M.cover.branch : Set S))
    (hSquare : Plane.closedSquare 0 1 ⊆ F.target)
    (v w : J → Plane) (hv : ∀ j, 0 < (v j) 1) (hw : ∀ j, (w j) 1 < 0)
    (haxis : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ c.val.image ↔ F x 1 = 0))
    (hmodel : ∀ j x, x ∈ F.source → F x ∈ Plane.closedSquare 0 1 →
      (x ∈ (b j).val.image ↔ F x ∈ segment ℝ (0 : Plane) (v j) ∪
        segment ℝ (0 : Plane) (w j)))
    (hfinite : ∀ j, (crossings M c (b j)).Finite) :
    ∃ d : EssentialMarkedArc M,
      vertex M d = vertex M c ∧
      ∀ j, (crossings M d (b j)).Finite ∧
        (crossings M d (b j)).ncard = (crossings M c (b j)).ncard := by
  obtain ⟨δ,hδ,hδsmall,hbounds⟩ :=
    exists_uniform_bend_height v (1 / 2) (1 / 2) (by norm_num) (by norm_num) hv
  have hδ1 : δ < 1 := by linarith
  have htrace : {x : S | x ∈ F.source ∧ F x ∈ Plane.closedSquare 0 1} ∩ c.val.image =
      {x : S | x ∈ F.source ∧ F x ∈
        segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)} := by
    ext x
    constructor
    · rintro ⟨⟨hx,hxSq⟩,hxc⟩
      exact ⟨hx,(unit_horizontal_segment_iff (F x)).2
        ⟨hxSq,(haxis x hx hxSq).mp hxc⟩⟩
    · rintro ⟨hx,hxA⟩
      obtain ⟨hxSq,hx0⟩ := (unit_horizontal_segment_iff (F x)).1 hxA
      exact ⟨⟨hx,hxSq⟩,(haxis x hx hxSq).mpr hx0⟩
  obtain ⟨d,hclass,himage⟩ := actual_supported_unit_bend M c F hmarks
    hSquare htrace δ hδ hδ1
  refine ⟨d,hclass,?_⟩
  intro j
  exact actual_unit_bend_preserves_radial_comparison_count M c d (b j) F p hpF hFp
    hmarks hSquare (v j) (w j) (hv j) (hw j) haxis (hmodel j)
    δ hδ hδ1 (hbounds j).1 (hbounds j).2 himage (hfinite j)

theorem actual_unit_bend_new_contacts_avoid_other_traces
    (M : HyperellipticModel E S) {J : Type} [Fintype J]
    (b : J → EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane)
    (hSquare : Plane.closedSquare 0 1 ⊆ F.target)
    (v w : J → Plane) (hv : ∀ j, 0 < (v j) 1) (hw : ∀ j, (w j) 1 < 0)
    (hmodel : ∀ j x, x ∈ F.source → F x ∈ Plane.closedSquare 0 1 →
      (x ∈ (b j).val.image ↔ F x ∈ segment ℝ (0 : Plane) (v j) ∪
        segment ℝ (0 : Plane) (w j)))
    (hdistinct : ∀ j k, j ≠ k →
      Disjoint (segment ℝ (0 : Plane) (v j) \ {0})
        (segment ℝ (0 : Plane) (v k) \ {0}))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsmall : ∀ j, δ * |(v j) 0| < (1 / 2 : ℝ) * (v j) 1 ∧ δ < (v j) 1) :
    ∀ j k, j ≠ k →
      F.symm (Plane.mk (δ * (v j) 0 / (v j) 1) δ) ∉ (b k).val.image := by
  intro j k hjk
  let z : Plane := Plane.mk (δ * (v j) 0 / (v j) 1) δ
  have hupper := bendGraph_upper_segment_singleton (1 / 2) 1 δ
    (by norm_num) (by norm_num) hδ (v j) (hv j) (hsmall j).1 (hsmall j).2
  have hzcontact : z ∈ bendGraph (1 / 2) 1 δ ∩ segment ℝ (0 : Plane) (v j) := by
    rw [hupper]
    exact Set.mem_singleton z
  have hzNonzero : z ≠ 0 := by
    intro he
    have h := congrArg (fun y : Plane => y 1) he
    change δ = 0 at h
    exact (ne_of_gt hδ) h
  have hzSquare : z ∈ Plane.closedSquare 0 1 :=
    unit_bend_subset_closed_square δ hδ hδ1 hzcontact.1
  have hzTarget : z ∈ F.target := hSquare hzSquare
  have hzSource : F.symm z ∈ F.source := F.map_target hzTarget
  intro hbk
  have hzModel : z ∈ segment ℝ (0 : Plane) (v k) ∪
      segment ℝ (0 : Plane) (w k) := by
    simpa only [F.right_inv hzTarget] using
      (hmodel k _ hzSource (by rw [F.right_inv hzTarget]; exact hzSquare)).mp hbk
  rcases hzModel with hzK | hzK
  · exact Set.disjoint_left.mp (hdistinct j k hjk)
      ⟨hzcontact.2,hzNonzero⟩ ⟨hzK,hzNonzero⟩
  · exact Set.disjoint_left.mp
      (bendGraph_lower_segment_disjoint (1 / 2) 1 δ
        (by norm_num) (by norm_num) hδ (w k) (hw k)) hzcontact.1 hzK

theorem actual_unit_bend_removes_center
    (M : HyperellipticModel E S) (c d : EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane) (p : S)
    (hpF : p ∈ F.source) (hFp : F p = 0)
    (δ : ℝ) (hδ : 0 < δ)
    (himage : d.val.image =
      (c.val.image \
        {x : S | x ∈ F.source ∧ F x ∈
          segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}) ∪
        {x : S | x ∈ F.source ∧ F x ∈ bendGraph (1 / 2) 1 δ}) :
    p ∉ d.val.image := by
  rw [himage]
  intro hp
  rcases hp with hp | hp
  · exact hp.2 ⟨hpF,by
      rw [hFp,segment_eq_image']
      refine ⟨(1 / 2 : ℝ),by norm_num,?_⟩
      ext i
      fin_cases i <;> norm_num [Plane.mk]⟩
  · exact unit_bend_avoids_zero δ hδ (hFp ▸ hp.2)

theorem actual_unit_bend_radial_new_contact_transverse
    (M : HyperellipticModel E S) (c d b : EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane)
    (hmarks : Disjoint F.source (M.cover.branch : Set S))
    (hSquare : Plane.closedSquare 0 1 ⊆ F.target)
    (v w : Plane) (hv : 0 < v 1) (hw : w 1 < 0)
    (haxis : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ c.val.image ↔ F x 1 = 0))
    (hmodel : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ b.val.image ↔ F x ∈ segment ℝ (0 : Plane) v ∪
        segment ℝ (0 : Plane) w))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsmall : δ * |v 0| < (1 / 2 : ℝ) * v 1)
    (hinside : δ < v 1)
    (himage : d.val.image =
      (c.val.image \
        {x : S | x ∈ F.source ∧ F x ∈
          segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}) ∪
        {x : S | x ∈ F.source ∧ F x ∈ bendGraph (1 / 2) 1 δ}) :
    CrossesInDisk M d b (F.symm (Plane.mk (δ * v 0 / v 1) δ)) := by
  let z : Plane := Plane.mk (δ * v 0 / v 1) δ
  let q : S := F.symm z
  have hnew := actual_unit_bend_new_crossing_singleton M b F hmarks hSquare
    v w hv hw hmodel δ hδ hδ1 hsmall hinside
  have hqnew : q ∈ {x : S | x ∈ F.source ∧
      F x ∈ bendGraph (1 / 2) 1 δ} ∩ arcInterior M b := by
    rw [hnew]
    exact Set.mem_singleton q
  have hqF : q ∈ F.source := hqnew.1.1
  have hqB : q ∈ b.val.image := hqnew.2.1
  have hzB : z ∈ bendGraph (1 / 2) 1 δ := by
    have hupper := bendGraph_upper_segment_singleton (1 / 2) 1 δ
      (by norm_num) (by norm_num) hδ v hv hsmall hinside
    have hz : z ∈ ({z} : Set Plane) := Set.mem_singleton z
    exact (hupper.symm ▸ hz).1
  have hqtarget : z ∈ F.target :=
    hSquare (unit_bend_subset_closed_square δ hδ hδ1 hzB)
  have hqvalue : F q = z := F.right_inv hqtarget
  have hqx : |F q 0| < (1 / 2 : ℝ) := by
    rw [hqvalue]
    change |δ * v 0 / v 1| < (1 / 2 : ℝ)
    rw [abs_div,abs_mul,abs_of_pos hδ,abs_of_pos hv]
    exact (div_lt_iff₀ hv).2 hsmall
  have hqy : F q 1 = δ := by rw [hqvalue]; rfl
  have hqy1 : F q 1 < 1 := by rw [hqy]; exact hδ1
  have hqn : ‖F q‖ < ‖v‖ := by
    rw [hqvalue]
    exact upper_ray_contact_norm_lt v hv δ hδ hinside
  exact actual_unit_bend_new_contact_transverse M c d b F q hmarks hqF
    v w hv hw δ hδ hqx hqy hqy1 hqn haxis hmodel himage hqB

theorem actual_unit_bend_finite_family_redraw
    (M : HyperellipticModel E S) {J : Type} [Fintype J]
    (c : EssentialMarkedArc M) (b : J → EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane) (p : S)
    (hpF : p ∈ F.source) (hFp : F p = 0)
    (hmarks : Disjoint F.source (M.cover.branch : Set S))
    (hSquare : Plane.closedSquare 0 1 ⊆ F.target)
    (v w : J → Plane) (hv : ∀ j, 0 < (v j) 1) (hw : ∀ j, (w j) 1 < 0)
    (haxis : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ c.val.image ↔ F x 1 = 0))
    (hmodel : ∀ j x, x ∈ F.source → F x ∈ Plane.closedSquare 0 1 →
      (x ∈ (b j).val.image ↔ F x ∈ segment ℝ (0 : Plane) (v j) ∪
        segment ℝ (0 : Plane) (w j)))
    (hdistinct : ∀ j k, j ≠ k →
      Disjoint (segment ℝ (0 : Plane) (v j) \ {0})
        (segment ℝ (0 : Plane) (v k) \ {0}))
    (hfinite : ∀ j, (crossings M c (b j)).Finite) :
    ∃ δ : ℝ, ∃ d : EssentialMarkedArc M,
      0 < δ ∧ δ < 1 ∧ vertex M d = vertex M c ∧
      (∀ j, δ * |(v j) 0| < (1 / 2 : ℝ) * (v j) 1 ∧ δ < (v j) 1) ∧
      d.val.image =
        (c.val.image \
          {x : S | x ∈ F.source ∧ F x ∈
            segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}) ∪
          {x : S | x ∈ F.source ∧ F x ∈ bendGraph (1 / 2) 1 δ} ∧
      p ∉ d.val.image ∧
      (∀ j, (crossings M d (b j)).Finite ∧
        (crossings M d (b j)).ncard = (crossings M c (b j)).ncard ∧
        crossings M d (b j) =
          (crossings M c (b j) \ {p}) ∪
            {F.symm (Plane.mk (δ * (v j) 0 / (v j) 1) δ)} ∧
        CrossesInDisk M d (b j)
          (F.symm (Plane.mk (δ * (v j) 0 / (v j) 1) δ))) ∧
      (∀ j k, j ≠ k →
        F.symm (Plane.mk (δ * (v j) 0 / (v j) 1) δ) ∉ (b k).val.image) := by
  obtain ⟨δ,hδ,hδsmall,hbounds⟩ :=
    exists_uniform_bend_height v (1 / 2) (1 / 2) (by norm_num) (by norm_num) hv
  have hδ1 : δ < 1 := by linarith
  have htrace : {x : S | x ∈ F.source ∧ F x ∈ Plane.closedSquare 0 1} ∩ c.val.image =
      {x : S | x ∈ F.source ∧ F x ∈
        segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)} := by
    ext x
    constructor
    · rintro ⟨⟨hx,hxSq⟩,hxc⟩
      exact ⟨hx,(unit_horizontal_segment_iff (F x)).2
        ⟨hxSq,(haxis x hx hxSq).mp hxc⟩⟩
    · rintro ⟨hx,hxA⟩
      obtain ⟨hxSq,hx0⟩ := (unit_horizontal_segment_iff (F x)).1 hxA
      exact ⟨⟨hx,hxSq⟩,(haxis x hx hxSq).mpr hx0⟩
  obtain ⟨d,hclass,himage⟩ := actual_supported_unit_bend M c F hmarks
    hSquare htrace δ hδ hδ1
  refine ⟨δ,d,hδ,hδ1,hclass,hbounds,himage,
    actual_unit_bend_removes_center M c d F p hpF hFp δ hδ himage,?_,?_⟩
  · intro j
    have hc := actual_unit_bend_preserves_radial_comparison_count M c d (b j)
      F p hpF hFp hmarks hSquare (v j) (w j) (hv j) (hw j) haxis
      (hmodel j) δ hδ hδ1 (hbounds j).1 (hbounds j).2 himage (hfinite j)
    exact ⟨hc.1,hc.2,
      actual_unit_bend_radial_crossing_set M c d (b j) F p hpF hFp
        hmarks hSquare (v j) (w j) (hv j) (hw j) haxis (hmodel j)
        δ hδ hδ1 (hbounds j).1 (hbounds j).2 himage,
      actual_unit_bend_radial_new_contact_transverse M c d
      (b j) F hmarks hSquare (v j) (w j) (hv j) (hw j)
      haxis (hmodel j) δ hδ hδ1 (hbounds j).1 (hbounds j).2 himage⟩
  · exact actual_unit_bend_new_contacts_avoid_other_traces M b F hSquare
      v w hv hw hmodel hdistinct δ hδ hδ1 hbounds

end
end CurveComplex.HyperellipticModel.ArcSurgery

#print axioms CurveComplex.HyperellipticModel.ArcSurgery.actual_supported_unit_bend
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.actual_unit_bend_preserves_radial_comparison_count
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.actual_unit_bend_finite_family_count
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.actual_unit_bend_radial_new_contact_transverse
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.actual_unit_bend_new_contacts_avoid_other_traces
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.actual_unit_bend_removes_center
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.actual_unit_bend_finite_family_redraw
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.actual_supported_unit_bend_nonincident_crossings
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.actual_unit_square_support_compact
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.actual_supported_unit_bend_agrees_outside_square
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.actual_unit_square_old_crossing_unique
