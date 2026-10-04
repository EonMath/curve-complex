import CurveComplexGenusTwo.Topology.TorusStrip.ProperLineSeparationCore
import Mathlib.Analysis.Normed.Affine.AddTorsor

open Set Metric Topology Schoenflies

namespace CurveComplexGenusTwo.Topology.PuncturedTorusCandidate

/-- A finite straight connector exists for arbitrary disjoint closed planar sets.
No periodicity, global minimum distance, or positive clearance is assumed. -/
theorem disjoint_closed_sets_have_straight_connector
    (K L : Set Plane) (hK : IsClosed K) (hL : IsClosed L)
    (hneK : K.Nonempty) (hneL : L.Nonempty) (hdis : Disjoint K L) :
    ∃ x ∈ K, ∃ y ∈ L, x ≠ y ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, AffineMap.lineMap x y t ∉ K ∪ L := by
  obtain ⟨q, hq⟩ := hneL
  obtain ⟨x, hx, hmin⟩ := hK.exists_infDist_eq_dist hneK q
  have hxq : x ≠ q := by
    intro he
    exact disjoint_left.mp hdis hx (he.symm ▸ hq)
  let f : ℝ → Plane := AffineMap.lineMap x q
  have hf : Continuous f := by dsimp [f]; fun_prop
  let T : Set ℝ := Icc 0 1 ∩ f ⁻¹' L
  have hT : IsCompact T := isCompact_Icc.inter_right (hL.preimage hf)
  have hTne : T.Nonempty := ⟨1, by simp [T, f, hq]⟩
  obtain ⟨r, hr, hrmin⟩ := hT.exists_isLeast hTne
  have hrpos : 0 < r := by
    apply lt_of_le_of_ne hr.1.1
    intro he
    have : x ∈ L := by simpa [f, ← he] using hr.2
    exact disjoint_left.mp hdis hx this
  have hfreeK : ∀ s ∈ Ioo (0 : ℝ) 1, f s ∉ K := by
    intro s hs hmem
    have hle : dist q x ≤ dist q (f s) := by
      rw [← hmin]
      exact infDist_le_dist_of_mem hmem
    have hd : dist q (f s) = (1 - s) * dist x q := by
      dsimp [f]
      rw [dist_right_lineMap, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
    rw [dist_comm q x, hd] at hle
    have hp : 0 < dist x q := dist_pos.mpr hxq
    nlinarith [hs.1]
  have hcomp (t : ℝ) : AffineMap.lineMap x (f r) t = f (t * r) := by
    dsimp [f]
    simp only [AffineMap.lineMap_apply_module]
    module
  refine ⟨x, hx, f r, hr.2, ?_, ?_⟩
  · intro he
    exact disjoint_left.mp hdis hx (he.symm ▸ hr.2)
  · intro t ht
    rw [hcomp]
    have htrpos : 0 < t * r := mul_pos ht.1 hrpos
    have htrlt : t * r < r := by nlinarith [ht.2]
    have htrone : t * r < 1 := htrlt.trans_le hr.1.2
    rintro (hmem | hmem)
    · exact hfreeK (t * r) ⟨htrpos, htrone⟩ hmem
    · exact not_le_of_gt htrlt (hrmin ⟨⟨htrpos.le, htrone.le⟩, hmem⟩)

/-- The endpoints retain actual parameters of both supplied proper lines. -/
theorem proper_disjoint_lines_have_straight_connector
    (F G : C(ℝ, Plane)) (hF : IsClosedEmbedding F) (hG : IsClosedEmbedding G)
    (hdis : Disjoint (range F) (range G)) :
    ∃ s t : ℝ, F s ≠ G t ∧
      ∀ u ∈ Ioo (0 : ℝ) 1, AffineMap.lineMap (F s) (G t) u ∉ range F ∪ range G := by
  obtain ⟨x, ⟨s, rfl⟩, y, ⟨t, rfl⟩, hne, hfree⟩ :=
    disjoint_closed_sets_have_straight_connector (range F) (range G)
      hF.isClosed_range hG.isClosed_range (range_nonempty F) (range_nonempty G) hdis
  exact ⟨s, t, hne, hfree⟩

/-- Every interior point of a boundary-to-boundary connector belongs to the
facing sides. This conclusion does not assume a preselected strip. -/
theorem straight_connector_in_facing_sides
    (K L U Uout V Vout : Set Plane)
    (hdis : Disjoint K L)
    (hU : IsOpen U) (hUout : IsOpen Uout)
    (hV : IsOpen V) (hVout : IsOpen Vout)
    (hUUout : Disjoint U Uout) (hVVout : Disjoint V Vout)
    (hUpart : U ∪ Uout = Kᶜ) (hVpart : V ∪ Vout = Lᶜ)
    (hLU : L ⊆ U) (hKV : K ⊆ V)
    (x y : Plane) (hx : x ∈ K) (hy : y ∈ L)
    (hfree : ∀ t ∈ Ioo (0 : ℝ) 1, AffineMap.lineMap x y t ∉ K ∪ L) :
    ∀ t ∈ Ioo (0 : ℝ) 1, AffineMap.lineMap x y t ∈ U ∩ V := by
  let f : ℝ → Plane := AffineMap.lineMap x y
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hsubU : f '' Ioc (0 : ℝ) 1 ⊆ U := by
    have hcover : f '' Ioc (0 : ℝ) 1 ⊆ U ∪ Uout := by
      rw [hUpart]
      rintro z ⟨t, ht, rfl⟩ hz
      by_cases he : t = 1
      · have : y ∈ K := by simpa [f, he] using hz
        exact disjoint_left.mp hdis this hy
      · exact hfree t ⟨ht.1, lt_of_le_of_ne ht.2 he⟩ (Or.inl hz)
    rcases (isPreconnected_Ioc.image f hf.continuousOn).subset_or_subset
        hU hUout hUUout hcover with h | h
    · exact h
    · have hyim : y ∈ f '' Ioc (0 : ℝ) 1 := ⟨1, by norm_num, by simp [f]⟩
      exact False.elim (disjoint_left.mp hUUout (hLU hy) (h hyim))
  have hsubV : f '' Ico (0 : ℝ) 1 ⊆ V := by
    have hcover : f '' Ico (0 : ℝ) 1 ⊆ V ∪ Vout := by
      rw [hVpart]
      rintro z ⟨t, ht, rfl⟩ hz
      by_cases he : t = 0
      · have : x ∈ L := by simpa [f, he] using hz
        exact disjoint_left.mp hdis hx this
      · exact hfree t ⟨lt_of_le_of_ne ht.1 (Ne.symm he), ht.2⟩ (Or.inr hz)
    rcases (isPreconnected_Ico.image f hf.continuousOn).subset_or_subset
        hV hVout hVVout hcover with h | h
    · exact h
    · have hxim : x ∈ f '' Ico (0 : ℝ) 1 := ⟨0, by norm_num, by simp [f]⟩
      exact False.elim (disjoint_left.mp hVVout (hKV hx) (h hxim))
  intro t ht
  exact ⟨hsubU ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩,
    hsubV ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩⟩

noncomputable def joinedProperLine (F G : C(ℝ, Plane)) (t : ℝ) : Plane :=
  if t ≤ 0 then F t else if t ≤ 1 then AffineMap.lineMap (F 0) (G 0) t else G (t - 1)

theorem joinedProperLine_left (F G : C(ℝ, Plane)) {t : ℝ} (ht : t ≤ 0) :
    joinedProperLine F G t = F t := by simp [joinedProperLine, ht]

theorem joinedProperLine_middle (F G : C(ℝ, Plane)) {t : ℝ} (ht : t ∈ Icc 0 1) :
    joinedProperLine F G t = AffineMap.lineMap (F 0) (G 0) t := by
  by_cases h : t ≤ 0
  · have he : t = 0 := le_antisymm h ht.1
    simp [joinedProperLine, he]
  · simp [joinedProperLine, h, ht.2]

theorem joinedProperLine_right (F G : C(ℝ, Plane)) {t : ℝ} (ht : 1 ≤ t) :
    joinedProperLine F G t = G (t - 1) := by
  have h0 : ¬t ≤ 0 := by linarith
  by_cases h : t ≤ 1
  · have he : t = 1 := le_antisymm h ht
    simp [joinedProperLine, he]
  · simp [joinedProperLine, h0, h]

theorem joinedProperLine_continuous (F G : C(ℝ, Plane)) :
    Continuous (joinedProperLine F G) := by
  have hmid : Continuous (fun t : ℝ =>
      if t ≤ 1 then AffineMap.lineMap (F 0) (G 0) t else G (t - 1)) := by
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    intro t ht
    simp only [id_eq] at ht
    simp [ht]
  apply Continuous.if_le F.continuous hmid continuous_id continuous_const
  intro t ht
  simp only [id_eq] at ht
  simp [ht]

theorem joinedProperLine_injective
    (F G : C(ℝ, Plane)) (hF : Function.Injective F) (hG : Function.Injective G)
    (hdis : Disjoint (range F) (range G))
    (hfree : ∀ t ∈ Ioo (0 : ℝ) 1,
      AffineMap.lineMap (F 0) (G 0) t ∉ range F ∪ range G) :
    Function.Injective (joinedProperLine F G) := by
  have hne : F 0 ≠ G 0 := fun he =>
    disjoint_left.mp hdis (mem_range_self 0) ⟨0, he.symm⟩
  have ordered (x y : ℝ) (hxy : x < y) : joinedProperLine F G x ≠ joinedProperLine F G y := by
    intro he
    by_cases hx0 : x ≤ 0
    · rw [joinedProperLine_left F G hx0] at he
      by_cases hy0 : y ≤ 0
      · rw [joinedProperLine_left F G hy0] at he
        exact hxy.ne (hF he)
      by_cases hy1 : y < 1
      · rw [joinedProperLine_middle F G ⟨(not_le.mp hy0).le, hy1.le⟩] at he
        exact hfree y ⟨not_le.mp hy0, hy1⟩ (Or.inl ⟨x, he⟩)
      · rw [joinedProperLine_right F G (not_lt.mp hy1)] at he
        exact disjoint_left.mp hdis (mem_range_self x) ⟨y - 1, he.symm⟩
    by_cases hx1 : x < 1
    · rw [joinedProperLine_middle F G ⟨(not_le.mp hx0).le, hx1.le⟩] at he
      by_cases hy1 : y < 1
      · rw [joinedProperLine_middle F G ⟨by linarith, hy1.le⟩] at he
        exact hxy.ne (AffineMap.lineMap_injective ℝ hne he)
      · rw [joinedProperLine_right F G (not_lt.mp hy1)] at he
        exact hfree x ⟨not_le.mp hx0, hx1⟩ (Or.inr ⟨y - 1, he.symm⟩)
    · rw [joinedProperLine_right F G (not_lt.mp hx1),
        joinedProperLine_right F G (by linarith)] at he
      have := hG he
      linarith
  intro x y he
  rcases lt_trichotomy x y with h | h | h
  · exact False.elim (ordered x y h he)
  · exact h
  · exact False.elim (ordered y x h he.symm)

theorem joinedProperLine_closedMap
    (F G : C(ℝ, Plane)) (hF : IsClosedMap F) (hG : IsClosedMap G) :
    IsClosedMap (joinedProperLine F G) := by
  intro A hA
  have heq : joinedProperLine F G '' A =
      F '' (A ∩ Iic 0) ∪
      AffineMap.lineMap (F 0) (G 0) '' (A ∩ Icc 0 1) ∪
      G '' ((fun t : ℝ => t - 1) '' (A ∩ Ici 1)) := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      by_cases h0 : t ≤ 0
      · exact Or.inl (Or.inl ⟨t, ⟨ht, h0⟩, (joinedProperLine_left F G h0).symm⟩)
      by_cases h1 : t ≤ 1
      · exact Or.inl (Or.inr ⟨t, ⟨ht, (not_le.mp h0).le, h1⟩,
          (joinedProperLine_middle F G ⟨(not_le.mp h0).le, h1⟩).symm⟩)
      · exact Or.inr ⟨t - 1, ⟨t, ⟨ht, (not_le.mp h1).le⟩, rfl⟩,
          (joinedProperLine_right F G (not_le.mp h1).le).symm⟩
    · rintro ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨u, ⟨t, ht, rfl⟩, rfl⟩)
      · exact ⟨t, ht.1, joinedProperLine_left F G ht.2⟩
      · exact ⟨t, ht.1, joinedProperLine_middle F G ht.2⟩
      · exact ⟨t, ht.1, joinedProperLine_right F G ht.2⟩
  rw [heq]
  refine ((hF _ (hA.inter isClosed_Iic)).union ?_).union ?_
  · have hcompact : IsCompact (A ∩ Icc (0 : ℝ) 1) := isCompact_Icc.inter_left hA
    exact (hcompact.image (by fun_prop)).isClosed
  · apply hG
    exact (Homeomorph.subRight (1 : ℝ)).isClosedMap _ (hA.inter isClosed_Ici)

/-- Splicing two chosen rays along the constructed connector gives a literal
proper embedded line, so its one-point compactification is a Jordan curve. -/
theorem joinedProperLine_closedEmbedding
    (F G : C(ℝ, Plane)) (hF : IsClosedEmbedding F) (hG : IsClosedEmbedding G)
    (hdis : Disjoint (range F) (range G))
    (hfree : ∀ t ∈ Ioo (0 : ℝ) 1,
      AffineMap.lineMap (F 0) (G 0) t ∉ range F ∪ range G) :
    IsClosedEmbedding (joinedProperLine F G) := by
  exact IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr
    ⟨joinedProperLine_continuous F G,
      joinedProperLine_injective F G hF.injective hG.injective hdis hfree,
      joinedProperLine_closedMap F G hF.isClosedMap hG.isClosedMap⟩

theorem positive_first_ray_avoids_joinedProperLine
    (F G : C(ℝ, Plane)) (hF : Function.Injective F)
    (hdis : Disjoint (range F) (range G))
    (hfree : ∀ t ∈ Ioo (0 : ℝ) 1,
      AffineMap.lineMap (F 0) (G 0) t ∉ range F ∪ range G)
    (x : ℝ) (hx : 0 < x) : F x ∉ range (joinedProperLine F G) := by
  rintro ⟨t, ht⟩
  by_cases ht0 : t ≤ 0
  · rw [joinedProperLine_left F G ht0] at ht
    have := hF ht
    linarith
  by_cases ht1 : t < 1
  · rw [joinedProperLine_middle F G ⟨(not_le.mp ht0).le, ht1.le⟩] at ht
    exact hfree t ⟨not_le.mp ht0, ht1⟩ (Or.inl ⟨x, ht.symm⟩)
  · rw [joinedProperLine_right F G (not_lt.mp ht1)] at ht
    exact disjoint_left.mp hdis (mem_range_self x) ⟨t - 1, ht⟩

/-- The ray-and-connector boundary now meets the actual Schoenflies API.
The inversion centre is constructed, not supplied as additional geometry. -/
theorem joinedProperLine_inversion_jordan
    (F G : C(ℝ, Plane)) (hF : IsClosedEmbedding F) (hG : IsClosedEmbedding G)
    (hdis : Disjoint (range F) (range G))
    (hfree : ∀ t ∈ Ioo (0 : ℝ) 1,
      AffineMap.lineMap (F 0) (G 0) t ∉ range F ∪ range G) :
    IsJordanCurve (insert (F 1) (invert (F 1) '' range (joinedProperLine F G))) := by
  let J : C(ℝ, Plane) := ⟨joinedProperLine F G, joinedProperLine_continuous F G⟩
  have hJ : IsClosedEmbedding J := joinedProperLine_closedEmbedding F G hF hG hdis hfree
  exact proper_line_inversion_isJordanCurve J hJ.isProperMap hJ.injective (F 1)
    (positive_first_ray_avoids_joinedProperLine F G hF.injective hdis hfree 1 (by norm_num))

end CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
