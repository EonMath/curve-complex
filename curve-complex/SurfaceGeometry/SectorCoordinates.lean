import BoundaryBandSupport
open Set Topology CurveComplex
open LeanEval.Topology.ClassificationOfSurfaces
namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry
namespace WholeFanProof
variable {V : Type} [Fintype V] [DecidableEq V] {F : Finset (Finset V)} {v : V}

theorem point_of_face (fan : OrderedBoundaryFan F v) (i : Fin fan.length)
    (q : GeometricRealization V F)
    (hq : q.val ∈ GeometricFace V {v, fan.vertex i.castSucc, fan.vertex i.succ}) :
    ∃ r s : Interval, q = fan.trianglePoint i r s := by
  classical
  have ha := fan.off_center i.castSucc
  have hb := fan.off_center i.succ
  have hab := fan.consecutive_vertices_ne i
  have hn := q.property.1.1
  have hsum : q.val v + q.val (fan.vertex i.castSucc) + q.val (fan.vertex i.succ) = 1 := by
    have hs := Finset.sum_subset (Finset.subset_univ
      ({v, fan.vertex i.castSucc, fan.vertex i.succ} : Finset V))
      (fun w _ hw => hq.2 w hw)
    simpa [ha, hb, hab, Ne.symm ha, Ne.symm hb, Ne.symm hab,
      q.property.1.2, add_assoc] using hs
  let r : Interval := ⟨1 - q.val v, by constructor <;> linarith [hn v, hn (fan.vertex i.castSucc), hn (fan.vertex i.succ)]⟩
  by_cases hr : (r : ℝ) = 0
  · refine ⟨r, 0, ?_⟩
    have hqa : q.val (fan.vertex i.castSucc) = 0 := by dsimp [r] at hr; linarith [hn (fan.vertex i.castSucc), hn (fan.vertex i.succ)]
    have hqb : q.val (fan.vertex i.succ) = 0 := by dsimp [r] at hr; linarith [hn (fan.vertex i.castSucc), hn (fan.vertex i.succ)]
    apply Subtype.ext
    funext w
    rw [fan.trianglePoint_coordinate]
    by_cases hw : v = w
    · subst w; simp [hr]; dsimp [r] at hr; linarith
    · by_cases haw : fan.vertex i.castSucc = w
      · subst w; simp [hr, Ne.symm ha, hqa]
      · by_cases hbw : fan.vertex i.succ = w
        · subst w; simp [hr, Ne.symm hb, hqb]
        · have hz := hq.2 w (by simp [Ne.symm hw, Ne.symm haw, Ne.symm hbw])
          simp [hr, hw, hz]
  · have hrpos : 0 < (r : ℝ) := lt_of_le_of_ne r.property.1 (Ne.symm hr)
    let s : Interval := ⟨q.val (fan.vertex i.succ) / (r : ℝ), by
      constructor
      · exact div_nonneg (hn _) r.property.1
      · rw [div_le_one hrpos]
        dsimp [r]; linarith [hn (fan.vertex i.castSucc)]⟩
    have hrs : (r : ℝ) * (s : ℝ) = q.val (fan.vertex i.succ) := by
      dsimp [s]; field_simp
    have hra : (r : ℝ) * (1 - (s : ℝ)) = q.val (fan.vertex i.castSucc) := by
      dsimp [r] at hrs ⊢; nlinarith
    refine ⟨r, s, ?_⟩
    apply Subtype.ext
    funext w
    by_cases hw : w = v
    · subst w; rw [fan.trianglePoint_center]; dsimp [r]; ring
    · by_cases haw : w = fan.vertex i.castSucc
      · subst w; rw [fan.trianglePoint_start, hra]
      · by_cases hbw : w = fan.vertex i.succ
        · subst w; rw [fan.trianglePoint_next, hrs]
        · rw [fan.trianglePoint_coordinate]
          have hz := hq.2 w (by simp [hw, haw, hbw])
          simp [Ne.symm hw, Ne.symm haw, Ne.symm hbw, hz]

theorem point_of_positive_center (fan : OrderedBoundaryFan F v)
    (q : GeometricRealization V F) (hq : 0 < q.val v) :
    ∃ (i : Fin fan.length) (r s : Interval), q = fan.trianglePoint i r s := by
  obtain ⟨i, hi⟩ := fan.support_at_positive_center q hq
  obtain ⟨r, s, hs⟩ := point_of_face fan i q hi
  exact ⟨i, r, s, hs⟩

theorem angular_cover (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : 0 ≤ x) (hxn : x ≤ (n : ℝ)) :
    ∃ (i : Fin n) (s : Interval), x = (i.val : ℝ) + (s : ℝ) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact ⟨0, ⟨x, hx, by simpa using hxn⟩, by simp⟩
    · by_cases hxn' : x ≤ (n : ℝ)
      · obtain ⟨i, s, hs⟩ := ih (by omega) hxn'
        exact ⟨i.castSucc, s, hs⟩
      · refine ⟨⟨n, by omega⟩, ⟨x - (n : ℝ), ?_, ?_⟩, ?_⟩
        · linarith
        · simp only [Nat.cast_add, Nat.cast_one] at hxn
          linarith
        · simp

theorem trianglePoint_eq_of_moment (fan : OrderedBoundaryFan F v)
    (i j : Fin fan.length) (r s s' : Interval)
    (hm : (r : ℝ) * ((i.val : ℝ) + (s : ℝ)) =
      (r : ℝ) * ((j.val : ℝ) + (s' : ℝ))) :
    fan.trianglePoint i r s = fan.trianglePoint j r s' := by
  by_cases hr : (r : ℝ) = 0
  · apply Subtype.ext
    funext w
    simp [fan.trianglePoint_coordinate, hr]
  have he : (i.val : ℝ) + (s : ℝ) = (j.val : ℝ) + (s' : ℝ) :=
    mul_left_cancel₀ hr hm
  have hforward : ∀ (i j : Fin fan.length) (s s' : Interval),
      i.val ≤ j.val → (i.val : ℝ) + (s : ℝ) = (j.val : ℝ) + (s' : ℝ) →
      fan.trianglePoint i r s = fan.trianglePoint j r s' := by
    intro i j s s' hij he
    by_cases hijeq : i = j
    · subst j
      have hss : s = s' := Subtype.ext (by linarith)
      rw [hss]
    have hlt : i.val + 1 ≤ j.val := by
      have hne : i.val ≠ j.val := by intro h; exact hijeq (Fin.ext h)
      omega
    have hlt' : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hlt
    have hs : (s : ℝ) = 1 := by linarith [s.property.2, s'.property.1]
    have hs' : (s' : ℝ) = 0 := by linarith [s.property.2, s'.property.1]
    have hidx : i.succ = j.castSucc := by
      apply Fin.ext
      have hreal : (i.val : ℝ) + 1 = (j.val : ℝ) := by linarith
      exact_mod_cast hreal
    apply Subtype.ext
    funext w
    rw [fan.trianglePoint_coordinate, fan.trianglePoint_coordinate]
    simp [hs, hs', hidx]
  by_cases hij : i.val ≤ j.val
  · exact hforward i j s s' hij he
  · exact (hforward j i s' s (by omega) he.symm).symm

theorem coordinate_injective (fan : OrderedBoundaryFan F v)
    (q q' : GeometricRealization V F) (hq : 0 < q.val v) (hq' : 0 < q'.val v)
    (he : (1 - q.val v, fan.linkMoment q) = (1 - q'.val v, fan.linkMoment q')) :
    q = q' := by
  obtain ⟨i, r, s, rfl⟩ := point_of_positive_center fan q hq
  obtain ⟨j, r', s', rfl⟩ := point_of_positive_center fan q' hq'
  have hc := congrArg Prod.fst he
  simp only [fan.trianglePoint_center, sub_sub_cancel] at hc
  have hr : r = r' := Subtype.ext hc
  subst r'
  apply trianglePoint_eq_of_moment fan
  have hm := congrArg Prod.snd he
  simpa only [fan.trianglePoint_linkMoment] using hm

theorem coordinate_bounds (fan : OrderedBoundaryFan F v)
    (q : GeometricRealization V F) (hq : 0 < q.val v) :
    0 ≤ 1 - q.val v ∧ 0 ≤ fan.linkMoment q ∧
      fan.linkMoment q ≤ (fan.length : ℝ) * (1 - q.val v) := by
  obtain ⟨i, r, s, rfl⟩ := point_of_positive_center fan q hq
  rw [fan.trianglePoint_center, fan.trianglePoint_linkMoment]
  simp only [sub_sub_cancel]
  refine ⟨r.property.1, mul_nonneg r.property.1
    (add_nonneg (Nat.cast_nonneg _) s.property.1), ?_⟩
  have hi : (i.val : ℝ) + 1 ≤ (fan.length : ℝ) := by exact_mod_cast i.isLt
  nlinarith [r.property.1, s.property.2]

theorem coordinate_surjective (fan : OrderedBoundaryFan F v)
    (r u : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hu : 0 ≤ u)
    (hul : u ≤ (fan.length : ℝ) * r) :
    ∃ q : GeometricRealization V F,
      (1 - q.val v, fan.linkMoment q) = (r, u) := by
  let ri : Interval := ⟨r, hr, hr1⟩
  by_cases hr0 : r = 0
  · have hu0 : u = 0 := by rw [hr0] at hul; nlinarith
    refine ⟨fan.trianglePoint ⟨0, fan.positive⟩ ri 0, ?_⟩
    rw [fan.trianglePoint_center, fan.trianglePoint_linkMoment]
    simp [ri, hr0, hu0]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    obtain ⟨i, s, hs⟩ := angular_cover fan.length fan.positive (u / r)
      (div_nonneg hu hr) ((div_le_iff₀ hrpos).mpr hul)
    refine ⟨fan.trianglePoint i ri s, ?_⟩
    rw [fan.trianglePoint_center, fan.trianglePoint_linkMoment]
    simp only [ri, sub_sub_cancel]
    congr 1
    rw [← hs]
    exact mul_div_cancel₀ _ hr0

theorem trianglePoint_face (fan : OrderedBoundaryFan F v) (i : Fin fan.length)
    (r s : Interval) :
    (fan.trianglePoint i r s).val ∈
      GeometricFace V {v, fan.vertex i.castSucc, fan.vertex i.succ} := by
  refine ⟨(fan.trianglePoint i r s).property.1, ?_⟩
  intro w hw
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  rw [fan.trianglePoint_coordinate]
  simp [Ne.symm hw.1, Ne.symm hw.2.1, Ne.symm hw.2.2]

theorem angle_extremes (n : ℕ) (i : Fin n) (s : Interval) :
    ((i.val : ℝ) + (s : ℝ) = 0 ∨ (i.val : ℝ) + (s : ℝ) = (n : ℝ)) ↔
      (i.val = 0 ∧ s = 0) ∨ (i.val + 1 = n ∧ s = 1) := by
  have hi : (i.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast i.isLt
  constructor
  · rintro (h | h)
    · have hiv : (i.val : ℝ) = 0 := by linarith [s.property.1, Nat.cast_nonneg (α := ℝ) i.val]
      exact Or.inl ⟨by exact_mod_cast hiv, Subtype.ext (by change (s : ℝ) = 0; linarith)⟩
    · have hiv : (i.val : ℝ) + 1 = (n : ℝ) := by linarith [s.property.2]
      exact Or.inr ⟨by exact_mod_cast hiv, Subtype.ext (by change (s : ℝ) = 1; linarith)⟩
  · rintro (⟨hi0, rfl⟩ | ⟨hin, rfl⟩)
    · left; simp [hi0]
    · right
      change (i.val : ℝ) + 1 = (n : ℝ)
      exact_mod_cast hin

theorem coordinate_boundary (fan : OrderedBoundaryFan F v)
    (q : GeometricRealization V F) (hq : 0 < q.val v) :
    q ∈ boundaryLocus F ↔
      fan.linkMoment q = 0 ∨ fan.linkMoment q = (fan.length : ℝ) * (1 - q.val v) := by
  obtain ⟨i, r, s, rfl⟩ := point_of_positive_center fan q hq
  have hr1 : (r : ℝ) < 1 := by rw [fan.trianglePoint_center] at hq; linarith
  by_cases hr0 : (r : ℝ) = 0
  · have hboundary : fan.trianglePoint i r s ∈ boundaryLocus F := by
      rw [fan.boundary_at_positive_center _ hq]
      left
      refine ⟨(fan.trianglePoint i r s).property.1, ?_⟩
      intro w hw
      have hvw : v ≠ w := by intro h; subst w; simp at hw
      rw [fan.trianglePoint_coordinate]
      simp [hr0, hvw]
    simp [hboundary, fan.trianglePoint_linkMoment, fan.trianglePoint_center, hr0]
  · have hrpos : 0 < (r : ℝ) := lt_of_le_of_ne r.property.1 (Ne.symm hr0)
    rw [fan.trianglePoint_boundary i r s hrpos hr1,
      fan.trianglePoint_linkMoment, fan.trianglePoint_center, sub_sub_cancel]
    have hz : (r : ℝ) * ((i.val : ℝ) + (s : ℝ)) = 0 ↔
        (i.val : ℝ) + (s : ℝ) = 0 := by simp [hr0]
    have hl : (r : ℝ) * ((i.val : ℝ) + (s : ℝ)) = (fan.length : ℝ) * (r : ℝ) ↔
        (i.val : ℝ) + (s : ℝ) = (fan.length : ℝ) := by
      rw [mul_comm (fan.length : ℝ), mul_right_inj' hr0]
    rw [hz, hl]
    exact (angle_extremes fan.length i s).symm

theorem coordinate_embedding (fan : OrderedBoundaryFan F v)
    (ε : ℝ) (hε : ε < (1 : ℝ) / 2) :
    IsEmbedding (fun q : {q : GeometricRealization V F | 1 - ε < q.val v} =>
      (1 - q.val.val v, fan.linkMoment q.val)) := by
  let C : Set (GeometricRealization V F) := {q | (1 : ℝ) / 2 ≤ q.val v}
  have hC : IsClosed C := isClosed_le continuous_const ((continuous_apply v).comp continuous_subtype_val)
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  have hc : Continuous (fun q : C => (1 - q.val.val v, fan.linkMoment q.val)) := by
    exact (continuous_const.sub ((continuous_apply v).comp
      (continuous_subtype_val.comp continuous_subtype_val))).prodMk
      (fan.continuous_linkMoment.comp continuous_subtype_val)
  have hi : Function.Injective (fun q : C => (1 - q.val.val v, fan.linkMoment q.val)) := by
    intro q q' he
    apply Subtype.ext
    exact coordinate_injective fan q.val q'.val
      (by have := q.property; dsimp [C] at this; linarith)
      (by have := q'.property; dsimp [C] at this; linarith) he
  have hsub : {q : GeometricRealization V F | 1 - ε < q.val v} ⊆ C := by
    intro q hq; change (1 : ℝ) / 2 ≤ q.val v; dsimp at hq; linarith
  exact (hc.isClosedEmbedding hi).isEmbedding.comp (IsEmbedding.inclusion hsub)

theorem interior_ray_boundary (n a r : ℝ) (ha : 0 < a) (han : a < n) :
    (r * a = 0 ∨ r * a = n * r) ↔ r = 0 := by
  constructor
  · intro h
    by_contra hr
    rcases h with h | h
    · exact (ne_of_gt ha) ((mul_eq_zero.mp h).resolve_left hr)
    · have he : a = n := mul_left_cancel₀ hr (by simpa [mul_comm n r] using h)
      linarith
  · rintro rfl; simp

theorem distinct_ray_collision (a b r r' : ℝ) (hab : a < b) :
    (r, r * a) = (r', r' * b) ↔ r = 0 ∧ r' = 0 := by
  constructor
  · intro he
    have hr : r = r' := congrArg Prod.fst he
    have hm : r * a = r' * b := congrArg Prod.snd he
    have hr0 : r = 0 := by
      by_contra hn
      have hab' : a = b := mul_left_cancel₀ hn (by simpa only [← hr] using hm)
      linarith
    exact ⟨hr0, hr ▸ hr0⟩
  · rintro ⟨rfl, rfl⟩; simp

end WholeFanProof
end CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry
