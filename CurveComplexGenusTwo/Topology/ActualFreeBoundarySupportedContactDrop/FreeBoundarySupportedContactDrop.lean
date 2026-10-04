import CurveComplexGenusTwo.Topology.ActualFreeBoundarySupportedContactDrop.FreeBoundaryContactDichotomy
import CurveComplexGenusTwo.Topology.ActualFreeBoundarySupportedContactDrop.RegionalSupportedRestriction
import CurveComplexGenusTwo.Topology.GeometricPosition.PointAvoidCurveV2

set_option maxHeartbeats 1600000

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies
open scoped NNReal
open RegionalEmbeddedFamily

/-- On an actually obtained same-side branch, shrink the support off the
WHOLE finite protected family and produce the actual Q-valued ambient move.
Graph clearance is output, derived from the actual disjoint moving family. -/
theorem source_actual_original_free_boundary_same_side_supported_contact_drop
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ (a b : C(Interval, ↥Q)),
      IsEmbedding a → IsEmbedding b →
      (a 0 ∈ B ∧ a 1 ∈ B ∧ b 0 ∈ B ∧ b 1 ∈ B) →
      (∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B ∧ b t ∉ B) →
      (¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
          IsEmbedding d ∧ d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            range a ∪ range c) →
      (¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
          IsEmbedding d ∧ d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            range b ∪ range c) →
      Disjoint ({a 0, a 1} : Set ↥Q) {b 0, b 1} →
      (range a ∩ range b).Finite →
      (∃ H : AmbientIsotopy ↥Q,
        (∀ t, (fun y => H.map (t, y)) '' B = B) ∧
        H.finalMap '' range a = range b) →
      ∀ (r s : Interval) (C : RegionalIsolatedContactChart Q a b r s),
        C.SameSide →
      ∀ (I : Type) [Fintype I] (d : I → C(Interval, ↥Q)),
        (∀ i, Disjoint (range b) (range (d i))) →
        ∃ D : SupportedContactDrop Q B a b (⋃ i, range (d i)) (a r),
          D.support ⊆ {y : ↥Q | y.val ∈ C.chart.source ∧
            C.chart y.val ∈ Plane.openSquare 0 1} := by
  classical
  intro Q B a b ha hb hend hint haess hbess hends hfinite hclass r s C hsame I _ d hd
  letI : ClosedSurface S := Classical.choice hS.2.1
  let E := C.chart
  let graph : Set S := ⋃ i, Set.range (fun t => (d i t).val)
  have hgraph : IsCompact graph := isCompact_iUnion
    (fun i => isCompact_range (continuous_subtype_val.comp (d i).continuous))
  have hpE : (a r).val ∈ E.source := by
    have hh : a r ∈ a '' Set.Icc C.aLeft C.aRight :=
      ⟨r, ⟨C.a_cuts.2.1.le, C.a_cuts.2.2.1.le⟩, rfl⟩
    rw [← C.whole_a_trace] at hh
    exact hh.1.1
  have hpgraph : (a r).val ∉ graph := by
    rintro ⟨_, ⟨i, rfl⟩, t, ht⟩
    have heq : d i t = a r := Subtype.ext ht
    exact Set.disjoint_left.mp (hd i)
      (show a r ∈ Set.range b from ⟨s, C.contact.symm⟩)
      (show a r ∈ Set.range (d i) from ⟨t, heq⟩)
  let W : Set Plane := (E.target ∩ E.symm ⁻¹' graphᶜ) ∩ Plane.openSquare 0 1
  have hW : IsOpen W :=
    (E.symm.isOpen_inter_preimage hgraph.isClosed.isOpen_compl).inter
      (Plane.isOpen_openSquare 0 1)
  have hzeroW : (0 : Plane) ∈ W := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← C.contact_at_origin]
      exact E.map_source hpE
    · change E.symm 0 ∉ graph
      rw [← C.contact_at_origin, E.left_inv hpE]
      exact hpgraph
    · exact mem_openSquare_zero_one.mpr (by
        change max |(0 : ℝ)| |(0 : ℝ)| < 1
        norm_num)
  obtain ⟨η, hη, hηW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hzeroW)
  let ρ : ℝ := η / 2
  let σ : ℝ := 3 * η / 4
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρσ : ρ < σ := by dsimp [ρ, σ]; linarith
  have hση : σ < η := by dsimp [σ]; linarith
  have hσW : Metric.closedBall (0 : Plane) σ ⊆ W := by
    intro z hz
    exact hηW (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt hση))
  have hρW : Metric.closedBall (0 : Plane) ρ ⊆ W :=
    (Metric.closedBall_subset_closedBall hρσ.le).trans hσW
  let U : Set S := {y | y ∈ E.source ∧ E y ∈ Metric.ball (0 : Plane) σ}
  let K0 : Set S := {y | y ∈ E.source ∧ E y ∈ Metric.closedBall (0 : Plane) ρ}
  have hU : IsOpen U := E.isOpen_inter_preimage Metric.isOpen_ball
  have hK0eq : K0 = E.symm '' Metric.closedBall (0 : Plane) ρ := by
    ext y
    constructor
    · rintro ⟨hy, hz⟩
      exact ⟨E y, hz, E.left_inv hy⟩
    · rintro ⟨z, hz, rfl⟩
      have hzt := (hρW hz).1.1
      exact ⟨E.map_target hzt, by rwa [E.right_inv hzt]⟩
  have hK0 : IsCompact K0 := by
    rw [hK0eq]
    exact (isCompact_closedBall _ _).image_of_continuousOn
      (E.continuousOn_symm.mono (fun z hz => (hρW hz).1.1))
  have hK0U : K0 ⊆ U := by
    rintro y ⟨hy, hz⟩
    exact ⟨hy, Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt hρσ)⟩
  have hUsquare : U ⊆ {y : S | y ∈ E.source ∧ E y ∈ Plane.openSquare 0 1} := by
    rintro y ⟨hy, hz⟩
    exact ⟨hy, (hσW (Metric.ball_subset_closedBall hz)).2⟩
  have hUinterior : U ⊆ interior Q := by
    intro y hy
    exact C.closed_support_interior
      ⟨(hUsquare hy).1, Plane.openSquare_subset_closedSquare 0 1 (hUsquare hy).2⟩
  have hUgraph : Disjoint U graph := by
    apply Set.disjoint_left.mpr
    intro y hy hyg
    have hh := (hσW (Metric.ball_subset_closedBall hy.2)).1.2
    change E.symm (E y) ∉ graph at hh
    rw [E.left_inv hy.1] at hh
    exact hh hyg
  have hfront : frontier Q =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R :=
    CoherentEndpointMotion.chart_deleted_disk_complement_frontier _ _ R hR htarget
  obtain ⟨ε, hε, hsign⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ t ∈ Set.Ioo C.bLeft C.bRight,
        0 ≤ ε * E (b t).val 1 ∧ (t ≠ s → 0 < ε * E (b t).val 1) := by
    have hbranch (ε : ℝ)
        (hl : ∀ t ∈ Set.Ioo C.bLeft s, 0 < ε * E (b t).val 1)
        (hr : ∀ t ∈ Set.Ioo s C.bRight, 0 < ε * E (b t).val 1) :
        ∀ t ∈ Set.Ioo C.bLeft C.bRight,
          0 ≤ ε * E (b t).val 1 ∧ (t ≠ s → 0 < ε * E (b t).val 1) := by
      intro t ht
      by_cases hts : t = s
      · subst t
        have hz : E (b s).val = 0 := C.contact.symm ▸ C.contact_at_origin
        simp [hz]
      · have hpos : 0 < ε * E (b t).val 1 := by
          rcases lt_or_gt_of_ne hts with hlt | hgt
          · exact hl t ⟨ht.1, hlt⟩
          · exact hr t ⟨hgt, ht.2⟩
        exact ⟨hpos.le, fun _ => hpos⟩
    rcases hsame with hpos | hneg
    · refine ⟨1, Or.inl rfl, hbranch 1 ?_ ?_⟩
      · simpa only [one_mul] using hpos.1
      · simpa only [one_mul] using hpos.2
    · refine ⟨-1, Or.inr rfl, hbranch (-1) ?_ ?_⟩
      · intro t ht; simpa only [neg_one_mul, neg_pos] using hneg.1 t ht
      · intro t ht; simpa only [neg_one_mul, neg_pos] using hneg.2 t ht
  have heps : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have heps2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  let v : Plane := Plane.mk 0 (ε / 2)
  have hv : ‖v‖ < 1 := by
    rcases hε with hε | hε <;>
      norm_num [v, hε, EuclideanSpace.norm_eq, Fin.sum_univ_two, Plane.mk]
  have hsmall (f : Plane → Plane)
      (c : ℝ≥0) (hc : (c : ℝ) < 1) (hf : LipschitzWith c f) :
      ∃ H : AmbientIsotopy Plane,
        ∀ t z, H.map (t, z) = z + (t : ℝ) • f z := by
    let F : Interval × Plane → Plane := fun p => p.2 + (p.1 : ℝ) • f p.2
    have hF : Continuous F := continuous_snd.add
      ((continuous_subtype_val.comp continuous_fst).smul
        (hf.continuous.comp continuous_snd))
    refine ⟨{map := ⟨F, hF⟩, homeomorphism_at := ?_, at_zero := ?_},
      fun _ _ => rfl⟩
    · intro t
      have happ : ApproximatesLinearOn (fun z => F (t, z))
          (ContinuousLinearEquiv.refl ℝ Plane : Plane →L[ℝ] Plane) Set.univ c := by
        intro z _ w _
        have heq : F (t, z) - F (t, w) - (z - w) =
            (t : ℝ) • (f z - f w) := by dsimp [F]; module
        change ‖F (t, z) - F (t, w) - (z - w)‖ ≤ _
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
        calc
          (t : ℝ) * ‖f z - f w‖ ≤ 1 * ‖f z - f w‖ :=
            mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
          _ ≤ c * ‖z - w‖ := by simpa [dist_eq_norm] using hf.dist_le_mul z w
      let e := happ.toHomeomorph (fun z => F (t, z)) (Or.inr (by simpa using hc))
      exact ⟨e, fun _ => rfl⟩
    · intro z; simp [F]
  let weight : Plane → ℝ := fun z => max (ρ - dist z 0) 0
  have hw0 : LipschitzWith 1 (fun z : Plane => ρ - dist z 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
      sub_sub_sub_cancel_left, abs_sub_comm] using abs_dist_sub_le z w (0 : Plane)
  have hw : LipschitzWith 1 weight := hw0.max_const 0
  let f : Plane → Plane := fun z => weight z • v
  have hf : LipschitzWith ‖v‖₊ f := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    change ‖weight z • v - weight w • v‖ ≤ ‖v‖ * dist z w
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have hh := hw.dist_le_mul z w
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hh
    exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (mul_comm _ _)
  obtain ⟨H, hH⟩ := hsmall f ‖v‖₊ hv hf
  have hHfix : ∀ t z, z ∉ Metric.closedBall (0 : Plane) ρ → H.map (t, z) = z := by
    intro t z hz
    rw [hH]
    have hh : ρ ≤ dist z 0 := (lt_of_not_ge hz).le
    simp only [f, weight, max_eq_right (sub_nonpos.mpr hh), zero_smul, smul_zero, add_zero]
  obtain ⟨L, G, hcoord, hGL, hGout⟩ := position_surface_chart_lift S
    E.source E.target E.open_source E.toHomeomorphSourceTarget
    (Metric.closedBall 0 ρ) (isCompact_closedBall _ _)
    (fun z hz => (hρW hz).1.1) H hHfix
  have hGfix : ∀ t y, y ∉ K0 → G.map (t, y) = y := by
    intro t y hy
    by_cases hys : y ∈ E.source
    · let z : E.source := ⟨y, hys⟩
      have hz : E y ∉ Metric.closedBall (0 : Plane) ρ := fun h => hy ⟨hys, h⟩
      have hL : L.map (t, z) = z := by
        apply E.toHomeomorphSourceTarget.injective
        apply Subtype.ext
        exact (hcoord t z).trans (hHfix t (E y) hz)
      rw [hGL t z, hL]
    · exact hGout t y hys
  obtain ⟨M, hMG, hMfix, hMfront⟩ := regional_ambient_isotopy_restricts_with_support
    Q K0 (hK0U.trans hUinterior) G hGfix
  let replacement : C(Interval, ↥Q) :=
    ⟨fun t => M.finalMap (b t),
      M.map.continuous.comp (continuous_const.prodMk b.continuous)⟩
  obtain ⟨e, he⟩ := M.homeomorphism_at 1
  have hemb : IsEmbedding M.finalMap := by
    convert e.isEmbedding using 1
    funext y
    exact (he y).symm
  have hreplacement : IsEmbedding replacement := hemb.comp hb
  have hBfix : ∀ t y, y ∈ B → M.map (t, y) = y := by
    intro t y hy
    apply hMfront
    rwa [hfront]
  have htrace : M.finalMap '' Set.range b = Set.range replacement :=
    (Set.range_comp M.finalMap b).symm
  have hMcoord (t : Interval) (y : ↥Q) (hy : y.val ∈ E.source) :
      (M.map (t, y)).val ∈ E.source ∧
      E (M.map (t, y)).val = H.map (t, E y.val) := by
    let z : E.source := ⟨y.val, hy⟩
    have hval : (M.map (t, y)).val = (L.map (t, z)).val :=
      (hMG t y).trans (hGL t z)
    refine ⟨hval.symm ▸ (L.map (t, z)).property, ?_⟩
    rw [hval]
    exact hcoord t z
  have hMmem (t : Interval) (y : ↥Q) :
      (M.map (t, y)).val ∈ K0 ↔ y.val ∈ K0 := by
    obtain ⟨h, hh⟩ := M.homeomorphism_at t
    constructor
    · intro hmy
      by_contra hy
      rw [hMfix t y hy] at hmy
      exact hy hmy
    · intro hy
      by_contra hmy
      have heq := hMfix t (M.map (t, y)) hmy
      have heq' : M.map (t, y) = y := h.injective (by simpa only [hh] using heq)
      exact hmy (heq'.symm ▸ hy)
  have haxis (y : ↥Q) (hy : y.val ∈ E.source)
      (hz : E y.val ∈ Plane.closedSquare 0 1) (hya : y ∈ Set.range a) :
      E y.val 1 = 0 := by
    have hh := C.whole_a_trace ▸ (show y ∈
      {y : ↥Q | y.val ∈ E.source ∧ E y.val ∈ Plane.closedSquare 0 1} ∩
        Set.range a from ⟨⟨hy, hz⟩, hya⟩)
    obtain ⟨t, ht, rfl⟩ := hh
    exact (C.anchor_diameter ▸
      (show E (a t).val ∈ (fun t : Interval => E (a t).val) ''
        Set.Icc C.aLeft C.aRight from ⟨t, ht, rfl⟩)).2
  have hpushpositive (t : Interval) (ht : (b t).val ∈ K0) :
      0 < ε * E (replacement t).val 1 := by
    have hzt := hρW ht.2
    have htraceb : b t ∈ b '' Set.Icc C.bLeft C.bRight :=
      C.whole_b_trace ▸ ⟨⟨ht.1, Plane.openSquare_subset_closedSquare 0 1 hzt.2⟩,
        Set.mem_range_self t⟩
    obtain ⟨q, hq, hqt⟩ := htraceb
    have hqt' : q = t := hb.injective hqt
    subst q
    have hbnot (q : Interval) (hqm : E (b q).val ∈ modelCurve) : t ≠ q := by
      intro heq
      rw [heq] at hzt
      have hh := mem_openSquare_zero_one.mp hzt.2
      change Plane.supNorm (E (b q).val) = 1 at hqm
      linarith
    have hti : t ∈ Set.Ioo C.bLeft C.bRight :=
      ⟨lt_of_le_of_ne hq.1 (Ne.symm (hbnot _ C.b_left_boundary)),
        lt_of_le_of_ne hq.2 (hbnot _ C.b_right_boundary)⟩
    have hz := (hMcoord 1 (b t) ht.1).2
    change E (replacement t).val = H.map (1, E (b t).val) at hz
    rw [hz, hH]
    simp only [f, v, Plane.add_apply, PiLp.smul_apply, Plane.mk, Fin.isValue,
      PiLp.toLp_apply, Set.Icc.coe_one, one_smul]
    change 0 < ε * (E (b t).val 1 + weight (E (b t).val) * (ε / 2))
    have hweight : 0 ≤ weight (E (b t).val) := le_max_right _ _
    by_cases hts : t = s
    · subst t
      have hz0 : E (b s).val = 0 := C.contact.symm ▸ C.contact_at_origin
      rw [hz0]
      simp only [PiLp.zero_apply, weight, dist_self, sub_zero, max_eq_left hρ.le]
      nlinarith [heps2]
    · have hpos := (hsign t hti).2 hts
      nlinarith [heps2]
  have hnocon : ∀ t, (b t).val ∈ K0 → replacement t ∉ Set.range a := by
    intro t ht haR
    have hm := (hMmem 1 (b t)).mpr ht
    have hzero := haxis (replacement t) hm.1
      (Plane.openSquare_subset_closedSquare 0 1 (hρW hm.2).2) haR
    have hp := hpushpositive t ht
    rw [hzero, mul_zero] at hp
    exact lt_irrefl _ hp
  let support : Set ↥Q := {y | y.val ∈ U}
  let compactSupport : Set ↥Q := {y | y.val ∈ K0}
  have hcomp : IsCompact compactSupport := by
    have hKQ : K0 ⊆ Q := (hK0U.trans hUinterior).trans interior_subset
    have heq : compactSupport =
        (fun y : K0 => (⟨y.val, hKQ y.property⟩ : ↥Q)) '' Set.univ := by
      ext y
      constructor
      · intro hy
        exact ⟨⟨y.val, hy⟩, trivial, Subtype.ext rfl⟩
      · rintro ⟨y, _, rfl⟩; exact y.property
    rw [heq]
    letI : CompactSpace K0 := isCompact_iff_compactSpace.mp hK0
    exact isCompact_univ.image (by fun_prop)
  have hretained : Set.range a ∩ Set.range replacement ⊆ Set.range a ∩ Set.range b := by
    rintro y ⟨hya, t, rfl⟩
    by_cases ht : (b t).val ∈ K0
    · exact (hnocon t ht hya).elim
    · have heq : replacement t = b t := hMfix 1 (b t) ht
      exact ⟨hya, ⟨t, heq.symm⟩⟩
  have hdeleted : a r ∉ Set.range replacement := by
    rintro ⟨t, ht⟩
    have hpK : (a r).val ∈ K0 := ⟨hpE, by
      rw [C.contact_at_origin]
      exact Metric.mem_closedBall_self hρ.le⟩
    have hbtK : (b t).val ∈ K0 := (hMmem 1 (b t)).mp (ht.symm ▸ hpK)
    exact hnocon t hbtK (ht.symm ▸ Set.mem_range_self r)
  have hstrict : (Set.range a ∩ Set.range replacement).ncard <
      (Set.range a ∩ Set.range b).ncard := by
    apply Set.ncard_lt_ncard _ hfinite
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hretained, ?_⟩
    intro heq
    have hp : a r ∈ Set.range a ∩ Set.range b :=
      ⟨Set.mem_range_self r, ⟨s, C.contact.symm⟩⟩
    exact hdeleted (heq.symm ▸ hp).2
  refine ⟨{
    support := support
    compactSupport := compactSupport
    support_open := hU.preimage continuous_subtype_val
    compact_support := hcomp
    compact_in_support := fun _ hy => hK0U hy
    support_interior := fun _ hy => hUinterior hy
    support_off_boundary := ?_
    support_off_graph := ?_
    contact_in_support := ?_
    contact_on_original := ⟨Set.mem_range_self r, ⟨s, C.contact.symm⟩⟩
    replacement := replacement
    replacement_embedded := hreplacement
    replacement_zero := hBfix 1 (b 0) hend.2.2.1
    replacement_one := hBfix 1 (b 1) hend.2.2.2
    replacement_interior := ?_
    motion := M
    boundary_setwise := ?_
    boundary_pointwise := hBfix
    graph_pointwise := ?_
    outside_compact_support := hMfix
    whole_moving_trace := htrace
    whole_trace_outside_support := ?_
    retained_contacts := hretained
    deleted_contact := hdeleted
    replacement_contacts_finite := hfinite.subset hretained
    strict_contact_decrease := hstrict }, fun _ hy => hUsquare hy⟩
  · apply Set.disjoint_left.mpr
    intro y hy hyB
    exact Set.disjoint_left.mp disjoint_interior_frontier (hUinterior hy)
      (hfront.symm ▸ hyB)
  · apply Set.disjoint_left.mpr
    rintro y hy ⟨_, ⟨i, rfl⟩, t, rfl⟩
    exact Set.disjoint_left.mp hUgraph hy ⟨_, ⟨i, rfl⟩, t, rfl⟩
  · exact hK0U ⟨hpE, by rw [C.contact_at_origin]; exact Metric.mem_closedBall_self hρ.le⟩
  · intro t ht hrt
    have heq : replacement t = b t := hemb.injective (hBfix 1 (replacement t) hrt)
    exact (hint t ht).2 (heq ▸ hrt)
  · intro t
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change M.map (t, z) ∈ B
      rwa [hBfix t z hz]
    · intro hy; exact ⟨y, hy, hBfix t y hy⟩
  · intro t y hy
    apply hMfix
    intro hK
    apply Set.disjoint_left.mp hUgraph (hK0U hK)
    rcases hy with ⟨_, ⟨i, rfl⟩, q, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, q, rfl⟩
  · ext y
    constructor
    · rintro ⟨⟨t, rfl⟩, hy⟩
      have hout : (b t).val ∉ K0 := by
        intro ht
        exact hy (hK0U ((hMmem 1 (b t)).mpr ht))
      have heq : replacement t = b t := hMfix 1 (b t) hout
      exact ⟨⟨t, heq.symm⟩, hy⟩
    · rintro ⟨⟨t, rfl⟩, hy⟩
      have heq : replacement t = b t := hMfix 1 (b t) (fun ht => hy (hK0U ht))
      exact ⟨⟨t, heq⟩, hy⟩



end CoherentEndpointMotion.FreeBoundaryContactRepair
