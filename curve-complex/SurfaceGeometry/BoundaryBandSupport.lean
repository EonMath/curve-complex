import FiniteBoundaryBandCore
open Set Topology CurveComplex
open LeanEval.Topology.ClassificationOfSurfaces
namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry

theorem cyclicNext_ne {m : ℕ} (hm : 3 ≤ m) (i : Fin m) :
    cyclicNext m hm i ≠ i := by
  intro h
  have hi := i.isLt
  have he := congrArg Fin.val h
  dsimp [cyclicNext] at he
  by_cases hlast : i.val + 1 = m
  · rw [hlast, Nat.mod_self] at he
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at he
    omega

theorem cyclicNext_twice_ne {m : ℕ} (hm : 3 ≤ m) (i : Fin m) :
    cyclicNext m hm (cyclicNext m hm i) ≠ i := by
  intro h
  have hi := i.isLt
  have he := congrArg Fin.val h
  dsimp [cyclicNext] at he
  by_cases hlast : i.val + 1 = m
  · rw [hlast, Nat.mod_self] at he
    rw [Nat.mod_eq_of_lt (by omega : 1 < m)] at he
    omega
  · have hsmall : i.val + 1 < m := by omega
    rw [Nat.mod_eq_of_lt hsmall] at he
    by_cases hlast2 : i.val + 1 + 1 = m
    · rw [hlast2, Nat.mod_self] at he
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at he
      omega

theorem edgeClock_whole_seam {m : ℕ} (hm : 3 ≤ m) (i : Fin m) :
    edgeClock m i 1 = edgeClock m (cyclicNext m hm i) 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  change Circle.exp (2 * Real.pi * ((i.val : ℝ) + 1) / m) =
    Circle.exp (2 * Real.pi * (((cyclicNext m hm i).val : ℝ) + 0) / m)
  simp only [add_zero]
  by_cases hlast : i.val + 1 = m
  · have hnext : (cyclicNext m hm i).val = 0 := by
      simp [cyclicNext, hlast]
    rw [hnext]
    have hcast : (i.val : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hlast
    rw [hcast]
    simp only [Nat.cast_zero, mul_zero, zero_div]
    rw [mul_div_cancel_right₀ _ hm0]
    exact Circle.exp_eq_exp.mpr ⟨1, by norm_num⟩
  · have hnext : (cyclicNext m hm i).val = i.val + 1 := by
      exact Nat.mod_eq_of_lt (by omega)
    rw [hnext]
    congr 1
    norm_num

theorem edgeClock_cover {m : ℕ} (hm : 3 ≤ m) (z : Circle) :
    ∃ (i : Fin m) (s : Interval), (s : ℝ) < 1 ∧ edgeClock m i s = z := by
  let a := toIcoMod Real.two_pi_pos 0 (Complex.arg (z : ℂ))
  have ha : 0 ≤ a ∧ a < 2 * Real.pi := toIcoMod_mem_Ico' Real.two_pi_pos _
  have hexp : Circle.exp a = z := by
    have hd := self_sub_toIcoMod_eq_mul Real.two_pi_pos 0 (Complex.arg (z : ℂ))
    apply Eq.trans _ (Circle.exp_arg z)
    apply Circle.exp_eq_exp.mpr
    refine ⟨-toIcoDiv Real.two_pi_pos 0 (Complex.arg (z : ℂ)), ?_⟩
    simp only [Int.cast_neg]
    dsimp [a] at *
    linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  let x : ℝ := a * m / (2 * Real.pi)
  have hx0 : 0 ≤ x := div_nonneg (mul_nonneg ha.1 hmpos.le) Real.two_pi_pos.le
  have hxlt : x < m := by
    dsimp [x]
    apply (div_lt_iff₀ Real.two_pi_pos).mpr
    nlinarith
  let i : Fin m := ⟨⌊x⌋₊, (Nat.floor_lt hx0).mpr hxlt⟩
  let s : Interval := ⟨x - (⌊x⌋₊ : ℝ),
    sub_nonneg.mpr (Nat.floor_le hx0), (Nat.self_sub_floor_lt_one x).le⟩
  refine ⟨i, s, Nat.self_sub_floor_lt_one x, ?_⟩
  have he : (i.val : ℝ) + (s : ℝ) = x := by dsimp [i,s]; ring
  unfold edgeClock
  rw [he]
  have hangle : 2 * Real.pi * x / m = a := by
    dsimp [x]
    field_simp
  rw [hangle]
  exact hexp

variable {V : Type} [Fintype V] [DecidableEq V] {F : Finset (Finset V)}

theorem BoundaryCycle.consecutive_vertices_ne (c : BoundaryCycle F) (i : Fin c.length) :
    c.vertex i ≠ c.vertex (cyclicNext c.length c.length_ge_three i) := by
  intro h
  exact cyclicNext_ne c.length_ge_three i (c.vertex_injective h).symm

theorem BoundaryCycle.consecutive_edge_mem (c : BoundaryCycle F) (i : Fin c.length) :
    {c.vertex i, c.vertex (cyclicNext c.length c.length_ge_three i)} ∈ boundaryEdges F := by
  exact ((c.component_edges_exact _).mpr ⟨i, rfl⟩).1

theorem BoundaryCycle.vertex_mem_boundary (c : BoundaryCycle F) (i : Fin c.length) :
    c.vertex i ∈ boundaryVertices F := by
  apply Finset.mem_biUnion.mpr
  exact ⟨_, c.consecutive_edge_mem i, by simp⟩

theorem BoundaryCycle.clock_mem_boundary (c : BoundaryCycle F)
    (i : Fin c.length) (s : Interval) :
    c.circle (edgeClock c.length i s) ∈ boundaryLocus F := by
  refine ⟨_, c.consecutive_edge_mem i, (c.circle _).property.1, ?_⟩
  intro v hv
  rw [c.circle_clock]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  simp [Ne.symm hv.1, Ne.symm hv.2]

theorem BoundaryCycle.range_subset_boundary (c : BoundaryCycle F) :
    range c.circle ⊆ boundaryLocus F := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨i,s,_,hz⟩ := edgeClock_cover c.length_ge_three z
  rw [← hz]
  exact c.clock_mem_boundary i s

theorem BoundaryCycle.clock_coordinate_start (c : BoundaryCycle F)
    (i : Fin c.length) (s : Interval) :
    (c.circle (edgeClock c.length i s)).val (c.vertex i) = 1 - (s : ℝ) := by
  rw [c.circle_clock]
  simp [Ne.symm (c.consecutive_vertices_ne i)]

theorem BoundaryCycle.clock_coordinate_next (c : BoundaryCycle F)
    (i : Fin c.length) (s : Interval) :
    (c.circle (edgeClock c.length i s)).val
      (c.vertex (cyclicNext c.length c.length_ge_three i)) = (s : ℝ) := by
  rw [c.circle_clock]
  simp [c.consecutive_vertices_ne i]

theorem BoundaryCycle.clock_positive_coordinate (c : BoundaryCycle F)
    (i : Fin c.length) (s : Interval) (v : V)
    (hpos : 0 < (c.circle (edgeClock c.length i s)).val v) :
    v = c.vertex i ∨ v = c.vertex (cyclicNext c.length c.length_ge_three i) := by
  by_contra h
  push Not at h
  rw [c.circle_clock] at hpos
  simp [Ne.symm h.1, Ne.symm h.2] at hpos

theorem BoundaryCycle.circle_injective (c : BoundaryCycle F) :
    Function.Injective c.circle := by
  intro z w h
  obtain ⟨i,s,hs,hz⟩ := edgeClock_cover c.length_ge_three z
  obtain ⟨j,r,hr,hw⟩ := edgeClock_cover c.length_ge_three w
  rw [← hz, ← hw] at h
  have hipos : 0 < (c.circle (edgeClock c.length i s)).val (c.vertex i) := by
    rw [c.clock_coordinate_start]
    linarith
  have hjpos : 0 < (c.circle (edgeClock c.length j r)).val (c.vertex j) := by
    rw [c.clock_coordinate_start]
    linarith
  have hij : i = j := by
    have hi := c.clock_positive_coordinate j r (c.vertex i) (h ▸ hipos)
    have hj := c.clock_positive_coordinate i s (c.vertex j) (h.symm ▸ hjpos)
    rcases hi with hi | hi
    · exact c.vertex_injective hi
    · rcases hj with hj | hj
      · exact (c.vertex_injective hj).symm
      · have hij := c.vertex_injective hi
        have hji := c.vertex_injective hj
        have h2 : cyclicNext c.length c.length_ge_three
            (cyclicNext c.length c.length_ge_three i) = i := by
          rw [← hji, ← hij]
        exact (cyclicNext_twice_ne c.length_ge_three i h2).elim
  subst j
  have he := congrArg (fun q : GeometricRealization V F =>
    q.val (c.vertex (cyclicNext c.length c.length_ge_three i))) h
  rw [c.clock_coordinate_next, c.clock_coordinate_next] at he
  have hsr : s = r := Subtype.ext he
  rw [← hz, ← hw, hsr]

theorem BoundaryCycle.circle_embedding (c : BoundaryCycle F) :
    IsEmbedding c.circle :=
  (c.circle.continuous.isClosedEmbedding c.circle_injective).isEmbedding

theorem boundaryEdge_card {e : Finset V} (he : e ∈ boundaryEdges F) :
    e.card = 2 := by
  obtain ⟨t, _, he⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp he).1
  exact (Finset.mem_powersetCard.mp he).2

theorem boundaryEdge_unique_triangle {e : Finset V} (he : e ∈ boundaryEdges F) :
    ∃! t : Finset V, t ∈ F ∧ e ⊆ t := by
  have hc := (Finset.mem_filter.mp he).2
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hc
  refine ⟨t, ?_, ?_⟩
  · have hm : t ∈ F.filter (fun t => e ⊆ t) := by rw [ht]; simp
    exact Finset.mem_filter.mp hm
  · intro u hu
    have hm : u ∈ F.filter (fun t => e ⊆ t) := Finset.mem_filter.mpr hu
    rw [ht] at hm
    exact Finset.mem_singleton.mp hm

theorem OrderedBoundaryFan.face_mem {v : V} (fan : OrderedBoundaryFan F v)
    (i : Fin fan.length) :
    {v,fan.vertex i.castSucc,fan.vertex i.succ} ∈ F := by
  exact ((fan.triangles_exact _).mpr ⟨i,rfl⟩).1

theorem OrderedBoundaryFan.support_at_positive_center {v : V}
    (fan : OrderedBoundaryFan F v) (q : GeometricRealization V F)
    (hq : 0 < q.val v) :
    ∃ i : Fin fan.length,
      q.val ∈ GeometricFace V {v,fan.vertex i.castSucc,fan.vertex i.succ} := by
  obtain ⟨t, ht, hsupport⟩ := q.property.2
  have hv : v ∈ t := by
    by_contra hv
    have hz := hsupport v hv
    linarith
  obtain ⟨i,rfl⟩ := (fan.triangles_exact t).mp ⟨ht,hv⟩
  exact ⟨i,q.property.1,hsupport⟩

theorem OrderedBoundaryFan.boundary_at_positive_center {v : V}
    (fan : OrderedBoundaryFan F v) (q : GeometricRealization V F)
    (hq : 0 < q.val v) :
    q ∈ boundaryLocus F ↔
      q.val ∈ GeometricFace V {v,fan.vertex 0} ∨
      q.val ∈ GeometricFace V {v,fan.vertex (Fin.last fan.length)} := by
  constructor
  · rintro ⟨e,he,hqface⟩
    have hv : v ∈ e := by
      by_contra hv
      have hz := hqface.2 v hv
      linarith
    rcases (fan.boundary_edges_exact e).mp ⟨he,hv⟩ with rfl | rfl
    · exact Or.inl hqface
    · exact Or.inr hqface
  · intro h
    rcases h with h | h
    · have he := ((fan.boundary_edges_exact _).mpr (Or.inl rfl)).1
      exact ⟨_,he,h⟩
    · have he := ((fan.boundary_edges_exact _).mpr (Or.inr rfl)).1
      exact ⟨_,he,h⟩

/-- Positive-center sectors of distinct vertices at levels above one half are disjoint. -/
theorem disjoint_positive_vertex_sectors {v w : V} (hvw : v ≠ w) :
    Disjoint {q : GeometricRealization V F | 1/2 < q.val v}
      {q : GeometricRealization V F | 1/2 < q.val w} := by
  rw [Set.disjoint_left]
  intro q hqv hqw
  have hnonneg : ∀ u, 0 ≤ q.val u := q.property.1.1
  have hsum : ∑ u, q.val u = 1 := q.property.1.2
  have hle : q.val v + q.val w ≤ 1 := by
    have ht := Finset.sum_le_sum_of_subset_of_nonneg
      (s := ({v,w} : Finset V)) (t := Finset.univ)
      (by intro u hu; simp) (by intro u _ _; exact hnonneg u)
    simpa [hvw,hsum] using ht
  dsimp at hqv hqw
  linarith

/-- A literal barycentric cone on one consecutive edge of the ordered link. -/
noncomputable def OrderedBoundaryFan.trianglePoint {v : V}
    (fan : OrderedBoundaryFan F v) (i : Fin fan.length) (r s : Interval) :
    GeometricRealization V F := by
  let x : V → ℝ := AffineMap.lineMap (k := ℝ) (Pi.single v (1 : ℝ) : V → ℝ)
    (AffineMap.lineMap (k := ℝ) (Pi.single (fan.vertex i.castSucc) (1 : ℝ) : V → ℝ)
      (Pi.single (fan.vertex i.succ) (1 : ℝ) : V → ℝ) (s : ℝ)) (r : ℝ)
  refine ⟨x, ?_, _, fan.face_mem i, ?_⟩
  · exact (convex_stdSimplex ℝ V).lineMap_mem (single_mem_stdSimplex ℝ v)
      ((convex_stdSimplex ℝ V).lineMap_mem
        (single_mem_stdSimplex ℝ _) (single_mem_stdSimplex ℝ _) s.property) r.property
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    dsimp [x]
    simp [AffineMap.lineMap_apply_module, Pi.single_apply,
      Ne.symm hw.1, Ne.symm hw.2.1, Ne.symm hw.2.2]

theorem OrderedBoundaryFan.trianglePoint_coordinate {v : V}
    (fan : OrderedBoundaryFan F v) (i : Fin fan.length) (r s : Interval) (w : V) :
    (fan.trianglePoint i r s).val w =
      (1 - (r : ℝ)) * (if v = w then 1 else 0) +
      (r : ℝ) * ((1 - (s : ℝ)) * (if fan.vertex i.castSucc = w then 1 else 0) +
        (s : ℝ) * (if fan.vertex i.succ = w then 1 else 0)) := by
  simp [OrderedBoundaryFan.trianglePoint, AffineMap.lineMap_apply_module,
    Pi.single_apply, eq_comm, mul_add]

theorem OrderedBoundaryFan.trianglePoint_center {v : V}
    (fan : OrderedBoundaryFan F v) (i : Fin fan.length) (r s : Interval) :
    (fan.trianglePoint i r s).val v = 1 - (r : ℝ) := by
  rw [fan.trianglePoint_coordinate]
  simp [fan.off_center]

theorem OrderedBoundaryFan.consecutive_vertices_ne {v : V}
    (fan : OrderedBoundaryFan F v) (i : Fin fan.length) :
    fan.vertex i.castSucc ≠ fan.vertex i.succ := by
  intro h
  have he := congrArg Fin.val (fan.injective h)
  simp only [Fin.val_castSucc, Fin.val_succ] at he
  omega

theorem OrderedBoundaryFan.trianglePoint_next {v : V}
    (fan : OrderedBoundaryFan F v) (i : Fin fan.length) (r s : Interval) :
    (fan.trianglePoint i r s).val (fan.vertex i.succ) = (r : ℝ) * (s : ℝ) := by
  rw [fan.trianglePoint_coordinate]
  simp [Ne.symm (fan.off_center i.succ), fan.consecutive_vertices_ne i]

theorem OrderedBoundaryFan.continuous_trianglePoint {v : V}
    (fan : OrderedBoundaryFan F v) (i : Fin fan.length) :
    Continuous (fun p : Interval × Interval => fan.trianglePoint i p.1 p.2) := by
  have hc : Continuous (fun p : Interval × Interval =>
      (fan.trianglePoint i p.1 p.2).val) := by
    apply continuous_pi
    intro w
    simp only [fan.trianglePoint_coordinate]
    fun_prop
  exact hc.subtype_mk _

theorem OrderedBoundaryFan.trianglePoint_collision {v : V}
    (fan : OrderedBoundaryFan F v) (i : Fin fan.length) (r s r' s' : Interval) :
    fan.trianglePoint i r s = fan.trianglePoint i r' s' ↔
      r = r' ∧ (r = 0 ∨ s = s') := by
  constructor
  · intro h
    have hc := congrArg (fun q : GeometricRealization V F => q.val v) h
    rw [fan.trianglePoint_center, fan.trianglePoint_center] at hc
    have hr : r = r' := Subtype.ext (by linarith)
    refine ⟨hr, ?_⟩
    subst r'
    by_cases hr0 : r = 0
    · exact Or.inl hr0
    · right
      have hn := congrArg (fun q : GeometricRealization V F =>
        q.val (fan.vertex i.succ)) h
      rw [fan.trianglePoint_next, fan.trianglePoint_next] at hn
      apply Subtype.ext
      exact mul_left_cancel₀ (by intro he; apply hr0; exact Subtype.ext he) hn
  · rintro ⟨rfl, h⟩
    rcases h with rfl | rfl
    · apply Subtype.ext
      funext w
      rw [fan.trianglePoint_coordinate, fan.trianglePoint_coordinate]
      change (1 - 0) * _ + 0 * _ = (1 - 0) * _ + 0 * _
      ring
    · rfl

theorem OrderedBoundaryFan.trianglePoint_start {v : V}
    (fan : OrderedBoundaryFan F v) (i : Fin fan.length) (r s : Interval) :
    (fan.trianglePoint i r s).val (fan.vertex i.castSucc) =
      (r : ℝ) * (1 - (s : ℝ)) := by
  rw [fan.trianglePoint_coordinate]
  simp [Ne.symm (fan.off_center i.castSucc),
    Ne.symm (fan.consecutive_vertices_ne i)]

/-- At positive radial depth and before the outer link, the only boundary
fibers of one fan triangle are the two extremal link rays. -/
theorem OrderedBoundaryFan.trianglePoint_boundary {v : V}
    (fan : OrderedBoundaryFan F v) (i : Fin fan.length) (r s : Interval)
    (hr : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    fan.trianglePoint i r s ∈ boundaryLocus F ↔
      (i.val = 0 ∧ s = 0) ∨ (i.val + 1 = fan.length ∧ s = 1) := by
  have hcenter : 0 < (fan.trianglePoint i r s).val v := by
    rw [fan.trianglePoint_center]
    linarith
  rw [fan.boundary_at_positive_center _ hcenter]
  have hs0 := s.property.1
  have hs1 := s.property.2
  constructor
  · intro h
    have hsupport : ∃ k : Fin (fan.length+1),
        (k = 0 ∨ k = Fin.last fan.length) ∧
        ∀ w ≠ v, 0 < (fan.trianglePoint i r s).val w → w = fan.vertex k := by
      rcases h with h | h
      · refine ⟨0, Or.inl rfl, ?_⟩
        intro w hw hp
        have hm : w ∈ ({v,fan.vertex 0} : Finset V) := by
          by_contra hm
          have hz := h.2 w hm
          linarith
        simpa [hw] using hm
      · refine ⟨Fin.last fan.length, Or.inr rfl, ?_⟩
        intro w hw hp
        have hm : w ∈ ({v,fan.vertex (Fin.last fan.length)} : Finset V) := by
          by_contra hm
          have hz := h.2 w hm
          linarith
        simpa [hw] using hm
    obtain ⟨k,hk,hkcoord⟩ := hsupport
    by_cases hs : s = 0
    · have hp : 0 < (fan.trianglePoint i r s).val (fan.vertex i.castSucc) := by
        rw [fan.trianglePoint_start,hs]
        simpa using hr
      have he := fan.injective (hkcoord _ (fan.off_center _) hp)
      have hval := congrArg Fin.val he
      rcases hk with rfl | rfl
      · left
        exact ⟨by simpa using hval,hs⟩
      · simp only [Fin.val_castSucc,Fin.val_last] at hval
        omega
    · have hspos : 0 < (s : ℝ) := by
        have hn : (s : ℝ) ≠ 0 := by intro h; apply hs; exact Subtype.ext h
        exact lt_of_le_of_ne hs0 (Ne.symm hn)
      have hp : 0 < (fan.trianglePoint i r s).val (fan.vertex i.succ) := by
        rw [fan.trianglePoint_next]
        exact mul_pos hr hspos
      have he := fan.injective (hkcoord _ (fan.off_center _) hp)
      have hval := congrArg Fin.val he
      rcases hk with rfl | rfl
      · simp only [Fin.val_succ,Fin.val_zero] at hval
        omega
      · right
        refine ⟨by simpa using hval, ?_⟩
        by_contra hsone
        have hslt : (s : ℝ) < 1 := lt_of_le_of_ne hs1
          (by intro h; apply hsone; exact Subtype.ext h)
        have hpstart : 0 < (fan.trianglePoint i r s).val (fan.vertex i.castSucc) := by
          rw [fan.trianglePoint_start]
          exact mul_pos hr (sub_pos.mpr hslt)
        have hstart := hkcoord _ (fan.off_center _) hpstart
        exact fan.consecutive_vertices_ne i (hstart.trans (congrArg fan.vertex he).symm)
  · rintro (⟨hi,hs⟩ | ⟨hi,hs⟩)
    · left
      refine ⟨(fan.trianglePoint i r s).property.1, ?_⟩
      intro w hw
      have hidx : i.castSucc = (0 : Fin (fan.length+1)) := Fin.ext hi
      rw [fan.trianglePoint_coordinate, hs, hidx]
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hw
      have hwv : v ≠ w := Ne.symm hw.1
      have hww : fan.vertex 0 ≠ w := Ne.symm hw.2
      simp [hwv,hww]
    · right
      refine ⟨(fan.trianglePoint i r s).property.1, ?_⟩
      intro w hw
      have hidx : i.succ = Fin.last fan.length := Fin.ext hi
      rw [fan.trianglePoint_coordinate, hs, hidx]
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hw
      have hwv : v ≠ w := Ne.symm hw.1
      have hww : fan.vertex (Fin.last fan.length) ≠ w := Ne.symm hw.2
      simp [hwv,hww]


/-- The affine index coordinate on the literal ordered link. -/
noncomputable def OrderedBoundaryFan.linkMoment {v : V}
    (fan : OrderedBoundaryFan F v) (q : GeometricRealization V F) : ℝ :=
  ∑ k : Fin (fan.length+1), (k.val : ℝ) * q.val (fan.vertex k)

theorem OrderedBoundaryFan.continuous_linkMoment {v : V}
    (fan : OrderedBoundaryFan F v) : Continuous fan.linkMoment := by
  unfold OrderedBoundaryFan.linkMoment
  apply continuous_finsetSum
  intro k hk
  exact continuous_const.mul ((continuous_apply (fan.vertex k)).comp continuous_subtype_val)

theorem OrderedBoundaryFan.trianglePoint_linkMoment {v : V}
    (fan : OrderedBoundaryFan F v) (i : Fin fan.length) (r s : Interval) :
    fan.linkMoment (fan.trianglePoint i r s) =
      (r : ℝ) * ((i.val : ℝ) + (s : ℝ)) := by
  unfold OrderedBoundaryFan.linkMoment
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have he := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at he
    omega
  have hterm (k : Fin (fan.length+1)) :
      (k.val : ℝ) * (fan.trianglePoint i r s).val (fan.vertex k) =
        (if k = i.castSucc then (i.val : ℝ) * (r : ℝ) * (1-(s : ℝ)) else 0) +
        (if k = i.succ then ((i.val : ℝ)+1) * (r : ℝ) * (s : ℝ) else 0) := by
    rw [fan.trianglePoint_coordinate]
    simp only [Ne.symm (fan.off_center k), ↓reduceIte, mul_zero, zero_add,
      fan.injective.eq_iff]
    by_cases hki : k = i.castSucc
    · subst k
      simp [hne, Ne.symm hne]
      ring
    · by_cases hkj : k = i.succ
      · subst k
        simp [hne, Ne.symm hne]
        ring
      · simp [hki,hkj,Ne.symm hki,Ne.symm hkj]
  simp only [hterm,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  ring

theorem OrderedBoundaryFan.trianglePoint_collision_halfOpen {v : V}
    (fan : OrderedBoundaryFan F v) (i j : Fin fan.length) (r s r' s' : Interval)
    (hs : (s : ℝ) < 1) (hs' : (s' : ℝ) < 1) :
    fan.trianglePoint i r s = fan.trianglePoint j r' s' ↔
      r = r' ∧ (r = 0 ∨ i = j ∧ s = s') := by
  constructor
  · intro h
    have hc := congrArg (fun q : GeometricRealization V F => q.val v) h
    rw [fan.trianglePoint_center, fan.trianglePoint_center] at hc
    have hr : r = r' := Subtype.ext (by linarith)
    refine ⟨hr,?_⟩
    subst r'
    by_cases hz : r = 0
    · exact Or.inl hz
    · right
      have hm := congrArg fan.linkMoment h
      rw [fan.trianglePoint_linkMoment,fan.trianglePoint_linkMoment] at hm
      have hrnz : (r : ℝ) ≠ 0 := by intro hr; apply hz; exact Subtype.ext hr
      have hi : (i.val : ℝ) + (s : ℝ) = (j.val : ℝ) + (s' : ℝ) :=
        mul_left_cancel₀ hrnz hm
      have hij : i = j := by
        have hijlt : (i.val : ℝ) < (j.val : ℝ)+1 := by linarith [s.property.1]
        have hjilt : (j.val : ℝ) < (i.val : ℝ)+1 := by linarith [s'.property.1]
        have hin : i.val < j.val+1 := by exact_mod_cast hijlt
        have hjn : j.val < i.val+1 := by exact_mod_cast hjilt
        exact Fin.ext (by omega)
      subst j
      exact ⟨rfl, Subtype.ext (by linarith)⟩
  · rintro ⟨rfl,h⟩
    rcases h with rfl | ⟨rfl,rfl⟩
    · apply Subtype.ext
      funext w
      rw [fan.trianglePoint_coordinate,fan.trianglePoint_coordinate]
      change (1-0)*_+0*_ = (1-0)*_+0*_
      ring
    · rfl

/-- Compactness of the literal zero circle gives a uniform closed inward
height contained in any prescribed open neighborhood. No embedding is assumed. -/
theorem BoundaryCycle.uniform_neighborhood_height (c : BoundaryCycle F)
    (G : C(Interval × Circle, GeometricRealization V F))
    (hzero : ∀ z, G (0,z) = c.circle z)
    (U : Set (GeometricRealization V F)) (hU : IsOpen U)
    (hcontains : range c.circle ⊆ U) :
    ∃ d : ℝ, 0 < d ∧ d < 1 ∧
      ∀ (t : Interval) (z : Circle), (t : ℝ) ≤ d → G (t,z) ∈ U := by
  have hz : ({0} : Set Interval) ×ˢ (univ : Set Circle) ⊆ G ⁻¹' U := by
    rintro ⟨t,z⟩ ⟨ht,_⟩
    have ht0 : t = 0 := Set.mem_singleton_iff.mp ht
    change G (t,z) ∈ U
    rw [ht0,hzero]
    exact hcontains ⟨z,rfl⟩
  obtain ⟨A,B,hA,_,h0,hB,hAB⟩ := generalized_tube_lemma
    isCompact_singleton isCompact_univ (hU.preimage G.continuous) hz
  have h0A : (0 : Interval) ∈ A := h0 (by simp)
  obtain ⟨e,he,hball⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds h0A)
  let d : ℝ := min (e/2) (1/2)
  have hd0 : 0 < d := lt_min (by linarith) (by norm_num)
  have hd1 : d < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hde : d < e := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨d,hd0,hd1,?_⟩
  intro t z ht
  apply hAB
  refine ⟨hball ?_,hB (by simp)⟩
  change dist t (0 : Interval) < e
  rw [Subtype.dist_eq]
  change dist (t : ℝ) 0 < e
  rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
  exact ht.trans_lt hde

/-- The five geometric properties determine all requested closed-edge patch data.
This lemma consumes a proved map; it is only record assembly. -/
theorem inwardBandOfGeometricMap (c : BoundaryCycle F)
    (U : Set (GeometricRealization V F))
    (G : C(Interval × Circle, GeometricRealization V F))
    (hG : IsEmbedding G)
    (hzero : ∀ z, G (0,z) = c.circle z)
    (hsupport : range G ⊆ U)
    (hboundary : ∀ (t : Interval) z, G (t,z) ∈ boundaryLocus F ↔ t = 0)
    (hopen : IsOpenEmbedding (fun z : Ioo (0 : ℝ) 1 × Circle =>
      G (⟨z.1.val,⟨z.1.property.1.le,z.1.property.2.le⟩⟩,z.2))) :
    Nonempty (BoundaryCycleInwardBand c U) := by
  let patch (i : Fin c.length) : C(Interval × Interval, GeometricRealization V F) :=
    G.comp { toFun := fun p => (p.1, edgeClock c.length i p.2)
             continuous_toFun := by unfold edgeClock; fun_prop }
  refine ⟨{
    band := G
    embedded := hG
    zero_clock := hzero
    supported := hsupport
    boundary_exact := hboundary
    positive_open := hopen
    patch := patch
    patch_clock := fun _ _ _ => rfl
    whole_seam := ?_
    exact_collision := ?_
    patch_cover := ?_ }⟩
  · intro i t
    change G (t, edgeClock c.length i 1) =
      G (t, edgeClock c.length (cyclicNext c.length c.length_ge_three i) 0)
    rw [edgeClock_whole_seam c.length_ge_three]
  · intro i j t s t' s'
    change G (t,edgeClock c.length i s) = G (t',edgeClock c.length j s') ↔ _
    rw [hG.injective.eq_iff, Prod.mk.injEq]
  · ext q
    constructor
    · rintro ⟨⟨t,z⟩,rfl⟩
      obtain ⟨i,s,_,hz⟩ := edgeClock_cover c.length_ge_three z
      refine mem_iUnion.mpr ⟨i, ?_⟩
      exact ⟨(t,s), by change G (t,edgeClock c.length i s) = G (t,z); rw [hz]⟩
    · intro hq
      obtain ⟨i,⟨⟨t,s⟩,rfl⟩⟩ := mem_iUnion.mp hq
      exact ⟨(t,edgeClock c.length i s), rfl⟩

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry
