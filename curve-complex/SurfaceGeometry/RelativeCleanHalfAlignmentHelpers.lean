import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryNullGeometry
import CurveComplexGenusTwo.Topology.ActualHarerCrossingAxes.ActualHarerCornerGeometryDefinitions
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualBoundaryProperArcStrip
import CurveComplexGenusTwo.Topology.ActualHarerDiskGluing.ActualHarerOptionalCollapseGluingProof
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeStripCrosscutMotion

open Set Topology CurveComplex Schoenflies

namespace CoherentEndpointMotion.RelativeCleanHalfAlignment

/-- The already available clean disk, joined side, proper strip, and H0b/H1
local data. This contains no exterior collar, enlarged disk, crosscut, or motion. -/
structure CleanHalfLocalData
    (S : Type) [TopologicalSpace S] (Q : Set S) (B : Set ↥Q)
    (a q : C(Interval, ↥Q)) where
  a_embedded : IsEmbedding a
  q_embedded : IsEmbedding q
  a_ends : a 0 ∈ B ∧ a 1 ∈ B
  q_ends : q 0 ∈ B ∧ q 1 ∈ B
  a_interior : ∀ u ∈ Ioo (0 : Interval) 1, a u ∉ B
  q_interior : ∀ u ∈ Ioo (0 : Interval) 1, q u ∉ B
  endpoint_separation : Disjoint ({a 0,a 1} : Set ↥Q) {q 0,q 1}
  finite_contacts : (range a ∩ range q).Finite
  M : FreeBoundaryNullGeometry.NullHalfBigonBoundary B a q
  e : C(Metric.closedBall (0 : Plane) 1, ↥Q)
  e_embedded : IsEmbedding e
  disk_boundary : e '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
    range M.first ∪ range M.second ∪ range M.boundarySide
  empty_interior : Disjoint (e '' {z | z.val ∈ Metric.ball (0 : Plane) 1})
    (range a ∪ range q)
  clean_contact : range e ∩ (range a ∩ range q) = {M.first 1}
  disk_a_trace : range e ∩ range a = range M.first
  disk_q_trace : range e ∩ range q = range M.second
  disk_B_trace : range e ∩ B = range M.boundarySide
  beta_relative_interior : M.boundarySide '' Ioo (0 : Interval) 1 ⊆
    interior (range e : Set ↥Q)
  sideArc : C(Interval, ↥Q)
  side_embedded : IsEmbedding sideArc
  side_range : range sideArc = range M.first ∪ range M.second
  side_zero : sideArc 0 = M.first 0
  side_one : sideArc 1 = M.second 0
  side_interior : ∀ u ∈ Ioo (0 : Interval) 1, sideArc u ∉ B
  G : Set ↥Q
  G_closed : IsClosed G
  disk_clear : Disjoint (range e) G
  W : Set ↥Q
  W_open : IsOpen W
  disk_in_W : range e ⊆ W
  W_clear : Disjoint W G
  F : C(Interval × Interval, ↥Q)
  p : Interval
  F_embedded : IsEmbedding F
  p_interior : p ∈ Ioo (0 : Interval) 1
  F_center : ∀ u, F (u,p) = sideArc u
  F_boundary : ∀ z, F z ∈ B ↔ z.1 = 0 ∨ z.1 = 1
  F_open : IsOpen (F '' {z | z.2 ∈ Ioo (0 : Interval) 1})
  l : Interval
  r : Interval
  band_order : 0 < l ∧ l < p ∧ p < r ∧ r < 1
  band_clear : F '' {z | z.2 ∈ Icc l r} ⊆ Gᶜ
  xi : Interval ≃ₜ Interval
  xi_original_clock : xi = Homeomorph.refl Interval ∨ xi = unitInterval.symmHomeomorph
  s : Interval
  t : Interval
  tail_order : 0 < s ∧ s < t ∧ t < 1
  q_initial : q (xi 0) = M.second 0
  q_corner : q (xi s) = M.first 1
  second_trace : range M.second = (fun u => q (xi u)) '' Icc 0 s
  tail_in_W : (fun u => q (xi u)) '' Icc 0 t ⊆ W
  tail_exterior : Disjoint ((fun u => q (xi u)) '' Ioc s t) (range e ∪ range a)
  a_corner_parameter : Interval
  a_corner : a a_corner_parameter = M.first 1
  axis_lo : Interval
  axis_hi : Interval
  cornerChart : OpenPartialHomeomorph S Plane
  axes : ActualHarerCornerGeometry.OrderedWholePairAxes
    (fun u => (a u).val) (fun u => (q u).val)
    a_corner_parameter (xi s) axis_lo axis_hi cornerChart
  axis_interior : cornerChart.source ⊆ interior Q
  axis_clear : ∀ y : ↥Q, y.val ∈ cornerChart.source → y ∉ G
  axis_beta_clear : Disjoint cornerChart.source (range (fun u => (M.boundarySide u).val))
  radius : ℝ
  radius_bounds : 0 < radius ∧ radius ≤ 1
  small_square : Plane.closedSquare 0 radius ⊆ cornerChart.target
  sigma : ℝ
  tau : ℝ
  signs : (sigma = -1 ∨ sigma = 1) ∧ (tau = -1 ∨ tau = 1)
  same_disk_quadrant : ∀ z : Plane, |z 0| < radius → |z 1| < radius →
    (cornerChart.symm z ∈ range (fun u => (M.first u).val) ↔
      z 1 = 0 ∧ 0 ≤ sigma * z 0) ∧
    (cornerChart.symm z ∈ range (fun u => (M.second u).val) ↔
      z 0 = 0 ∧ 0 ≤ tau * z 1) ∧
    (cornerChart.symm z ∈ range (fun u => (e u).val) ↔
      0 ≤ sigma * z 0 ∧ 0 ≤ tau * z 1)
  outgoing_axis_order : ∀ u, s < u → (q (xi u)).val ∈ cornerChart.source →
    0 < -tau * (cornerChart (q (xi u)).val) 1

/-- H2's actual relative collar and literal q-tail, followed by the actual disk
obtained by optional-collapse gluing with both flags false. -/
structure RelativeHalfCollar
    {S : Type} [TopologicalSpace S] {Q : Set S} {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q) where
  H : C(Interval × Interval, ↥Q)
  H_embedded : IsEmbedding H
  seam : ∀ u, H (u,0) = d.sideArc u
  endpoints_in_B : ∀ w, H (0,w) ∈ B ∧ H (1,w) ∈ B
  interior_off_B : ∀ u ∈ Ioo (0 : Interval) 1, ∀ w, H (u,w) ∉ B
  collar_in_W : range H ⊆ d.W
  disk_intersection : range H ∩ range d.e = range d.sideArc
  collision_kernel : ∀ u w u' w', H (u,w) = H (u',w') ↔ u = u' ∧ w = w'
  beta_collision : ∀ u w v, H (u,w) = d.M.boundarySide v ↔
    (u = 0 ∧ w = 0 ∧ v = 0) ∨ (u = 1 ∧ w = 0 ∧ v = 1)
  corner : Interval
  corner_interior : corner ∈ Ioo (0 : Interval) 1
  corner_on_side : d.sideArc corner = d.M.first 1
  eta : C(Interval, Interval × Interval)
  eta_embedded : IsEmbedding eta
  eta_zero : eta 0 = (corner,0)
  eta_one : (eta 1).2 = 1 ∧ (eta 1).1 ∈ Ioo (0 : Interval) 1
  eta_interior : ∀ u ∈ Ioo (0 : Interval) 1,
    eta u ∈ Ioo (0 : Interval) 1 ×ˢ Ioo (0 : Interval) 1
  eta_exact_parameter : ∀ u : Interval,
    H (eta u) = q (d.xi (Set.Icc.convexComb d.s d.t u))
  eta_trace : range (H.comp eta) = (fun u => q (d.xi u)) '' Icc d.s d.t
  whole_q_trace : (range d.e ∪ range H) ∩ range q =
    (fun u => q (d.xi u)) '' Icc 0 d.t
  enlargedDisk : C(Metric.closedBall (0 : Plane) 1, ↥Q)
  enlarged_embedded : IsEmbedding enlargedDisk
  enlarged_range : range enlargedDisk = range d.e ∪ range H
  enlarged_boundary : enlargedDisk '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
    range d.M.boundarySide ∪ range (fun w : Interval => H (0,w)) ∪
    range (fun w : Interval => H (1,w)) ∪ range (fun u : Interval => H (u,1))
  enlarged_B_trace : (range d.e ∪ range H) ∩ B =
    range d.M.boundarySide ∪ range (fun w : Interval => H (0,w)) ∪
      range (fun w : Interval => H (1,w))

/-- H3's actual square and two proper crosscuts. No motion is included. -/
structure RelativeHalfCrosscuts
    {S : Type} [TopologicalSpace S] {Q : Set S} {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q)
    (h : RelativeHalfCollar d) where
  E : C(Interval × Interval, ↥Q)
  E_embedded : IsEmbedding E
  E_range : range E = range d.e ∪ range h.H
  E_boundary : ∀ z, E z ∈ B ↔ z.1 = 0
  E_relative_open : IsOpen (E '' {z | z.1 < 1 ∧ z.2 ∈ Ioo (0 : Interval) 1})
  old : C(Interval, Interval × Interval)
  new : C(Interval, Interval × Interval)
  old_embedded : IsEmbedding old
  new_embedded : IsEmbedding new
  old_zero : (old 0).1 = 0
  new_zero : (new 0).1 = 0
  old_one : (old 1).1 = 1
  new_one : (new 1).1 = 1
  old_zero_width : (old 0).2 ∈ Ioo (0 : Interval) 1
  new_zero_width : (new 0).2 ∈ Ioo (0 : Interval) 1
  same_far_endpoint : old 1 = new 1
  far_width : (old 1).2 ∈ Ioo (0 : Interval) 1
  old_interior : ∀ u ∈ Ioo (0 : Interval) 1,
    old u ∈ Ioo (0 : Interval) 1 ×ˢ Ioo (0 : Interval) 1
  new_interior : ∀ u ∈ Ioo (0 : Interval) 1,
    new u ∈ Ioo (0 : Interval) 1 ×ˢ Ioo (0 : Interval) 1
  old_trace : range (E.comp old) = (fun u => q (d.xi u)) '' Icc 0 d.t
  new_clear_whole_a : Disjoint (range (E.comp new)) (range a)


/-- The actual corner has a strict interior parameter on the unchanged joined side. -/
theorem actual_side_corner_parameter
    {S : Type} [TopologicalSpace S] {Q : Set S} {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q) :
    ∃ c ∈ Ioo (0 : Interval) 1, d.sideArc c = d.M.first 1 := by
  have hm : d.M.first 1 ∈ range d.sideArc := by
    rw [d.side_range]
    exact Or.inl (mem_range_self 1)
  obtain ⟨c,hc⟩ := hm
  refine ⟨c,⟨?_,?_⟩,hc⟩
  · apply bot_lt_iff_ne_bot.mpr
    intro he
    change c = (0 : Interval) at he
    have hb : d.sideArc c ∈ B := by rw [he,d.side_zero]; exact d.M.first_zero_boundary
    exact d.M.corner_off_boundary (hc ▸ hb)
  · apply lt_top_iff_ne_top.mpr
    intro he
    change c = (1 : Interval) at he
    have hb : d.sideArc c ∈ B := by rw [he,d.side_one]; exact d.M.second_zero_boundary
    exact d.M.corner_off_boundary (hc ▸ hb)

/-- Whole beta collisions retain the literal initial and final parameters. -/
theorem actual_side_beta_collision
    {S : Type} [TopologicalSpace S] {Q : Set S} {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q) :
    ∀ u v, d.sideArc u = d.M.boundarySide v ↔
      (u = 0 ∧ v = 0) ∨ (u = 1 ∧ v = 1) := by
  intro u v
  constructor
  · intro he
    have hb : d.sideArc u ∈ B := he ▸ d.M.boundary_in_B v
    by_cases h0 : u = 0
    · left
      refine ⟨h0,?_⟩
      apply d.M.boundary_embedded.injective
      exact he.symm.trans ((congrArg d.sideArc h0).trans
        (d.side_zero.trans d.M.boundary_zero.symm))
    by_cases h1 : u = 1
    · right
      refine ⟨h1,?_⟩
      apply d.M.boundary_embedded.injective
      exact he.symm.trans ((congrArg d.sideArc h1).trans
        (d.side_one.trans d.M.boundary_one.symm))
    exact False.elim (d.side_interior u
      ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩ hb)
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact d.side_zero.trans d.M.boundary_zero.symm
    · exact d.side_one.trans d.M.boundary_one.symm

/-- The original disk is already bounded by the literal side and beta. -/
theorem actual_two_side_boundary
    {S : Type} [TopologicalSpace S] {Q : Set S} {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q) :
    d.e '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      range d.sideArc ∪ range d.M.boundarySide := by
  rw [d.disk_boundary,d.side_range]


/-- The affine interval map uses the literal ordered s,t from the packet. -/
theorem original_tail_affine_embedding
    {S : Type} [TopologicalSpace S] {Q : Set S} {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q) :
    IsEmbedding (Set.Icc.convexComb d.s d.t) := by
  refine ((Set.Icc.continuous_convexComb d.s d.t).isClosedEmbedding ?_).isEmbedding
  intro u v huv
  apply Subtype.ext
  have hs : (d.s : ℝ) < d.t := d.tail_order.2.1
  have he := congrArg (fun z : Interval => (z : ℝ)) huv
  simp only [Set.Icc.coe_convexComb] at he
  nlinarith

/-- Exact pointwise q parametrization already forces the eta path to embed. -/
theorem actual_eta_embedding
    {S : Type} [TopologicalSpace S] {Q : Set S} {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q)
    (H : C(Interval × Interval, ↥Q)) (eta : C(Interval, Interval × Interval))
    (hexact : ∀ u : Interval, H (eta u) = q (d.xi (Set.Icc.convexComb d.s d.t u))) :
    IsEmbedding eta := by
  refine (eta.continuous.isClosedEmbedding ?_).isEmbedding
  intro u v he
  apply (original_tail_affine_embedding d).injective
  apply d.xi.injective
  apply d.q_embedded.injective
  exact (hexact u).symm.trans ((congrArg H he).trans (hexact v))

/-- Pointwise equality pays the whole closed original-clock tail trace. -/
theorem actual_eta_trace
    {S : Type} [TopologicalSpace S] {Q : Set S} {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q)
    (H : C(Interval × Interval, ↥Q)) (eta : C(Interval, Interval × Interval))
    (hexact : ∀ u : Interval, H (eta u) = q (d.xi (Set.Icc.convexComb d.s d.t u))) :
    range (H.comp eta) = (fun u => q (d.xi u)) '' Icc d.s d.t := by
  change range (fun u => H (eta u)) = _
  rw [show (fun u => H (eta u)) =
      (fun u => q (d.xi u)) ∘ Set.Icc.convexComb d.s d.t from funext hexact]
  rw [range_comp,Path.range_subpathAux,uIcc_of_le d.tail_order.2.1.le]

/-- Injectivity plus the exact disk/side intersection forces literal beta collisions. -/
theorem actual_collar_beta_collision
    {S : Type} [TopologicalSpace S] {Q : Set S} {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q)
    (H : C(Interval × Interval, ↥Q)) (hH : IsEmbedding H)
    (hseam : ∀ u, H (u,0) = d.sideArc u)
    (hintersection : range H ∩ range d.e = range d.sideArc) :
    ∀ u w v, H (u,w) = d.M.boundarySide v ↔
      (u = 0 ∧ w = 0 ∧ v = 0) ∨ (u = 1 ∧ w = 0 ∧ v = 1) := by
  intro u w v
  constructor
  · intro he
    have hb : d.M.boundarySide v ∈ range d.e := by
      have hm : d.M.boundarySide v ∈ range d.e ∩ B :=
        d.disk_B_trace.symm ▸ mem_range_self v
      exact hm.1
    have hm : H (u,w) ∈ range d.sideArc :=
      hintersection ▸ ⟨mem_range_self (u,w),he ▸ hb⟩
    obtain ⟨u',hu'⟩ := hm
    have hp : (u',0) = (u,w) := hH.injective ((hseam u').trans hu')
    have hw : w = 0 := (congrArg Prod.snd hp).symm
    have hu : u' = u := congrArg Prod.fst hp
    have hs : d.sideArc u = d.M.boundarySide v := by
      rw [← hu]
      exact hu'.trans he
    rcases (actual_side_beta_collision d u v).mp hs with ⟨h0,hv⟩ | ⟨h1,hv⟩
    · exact Or.inl ⟨h0,hw,hv⟩
    · exact Or.inr ⟨h1,hw,hv⟩
  · rintro (⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩)
    · exact (hseam 0).trans ((actual_side_beta_collision d 0 0).mpr (Or.inl ⟨rfl,rfl⟩))
    · exact (hseam 1).trans ((actual_side_beta_collision d 1 1).mpr (Or.inr ⟨rfl,rfl⟩))

/-- The four-parameter collision iff follows from actual collar embedding. -/
theorem actual_collar_collision_kernel
    {X : Type} [TopologicalSpace X] (H : C(Interval × Interval, X))
    (hH : IsEmbedding H) :
    ∀ u w u' w', H (u,w) = H (u',w') ↔ u = u' ∧ w = w' := by
  intro u w u' w'
  constructor
  · intro he
    exact ⟨congrArg Prod.fst (hH.injective he),congrArg Prod.snd (hH.injective he)⟩
  · rintro ⟨rfl,rfl⟩
    rfl

/-- Optional-collapse gluing with both flags false pays all enlarged-disk geometry. -/
theorem actual_collar_glues_original_disk
    {S : Type} [TopologicalSpace S] {Q : Set S} [T2Space ↥Q] {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q)
    (H : C(Interval × Interval, ↥Q)) (hH : IsEmbedding H)
    (hseam : ∀ u, H (u,0) = d.sideArc u)
    (hintersection : range H ∩ range d.e = range d.sideArc) :
    ∃ e : C(Metric.closedBall (0 : Plane) 1, ↥Q), IsEmbedding e ∧
      range e = range d.e ∪ range H ∧
      e '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
        range d.M.boundarySide ∪ range (fun w : Interval => H (0,w)) ∪
        range (fun w : Interval => H (1,w)) ∪ range (fun u : Interval => H (u,1)) := by
  apply ActualHarerDiskGluing.actual_disk_attach_half_collar_with_optional_endpoint_collapse
    d.sideArc d.M.boundarySide d.e d.side_embedded d.M.boundary_embedded
    d.e_embedded (d.side_zero.trans d.M.boundary_zero.symm)
    (d.side_one.trans d.M.boundary_one.symm) (actual_two_side_boundary d)
    (fun u v he => (actual_side_beta_collision d u v).mp he) H false false
    (by simp) hseam ?_ hintersection
  intro u w u' w'
  simpa [ActualHarerDiskGluing.collapsedEndpoint] using
    actual_collar_collision_kernel H hH u w u' w'

/-- Properness of the literal collar and the input's whole disk-B trace pay the union trace. -/
theorem actual_enlarged_B_trace
    {S : Type} [TopologicalSpace S] {Q : Set S} {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q)
    (H : C(Interval × Interval, ↥Q))
    (hB : ∀ z, H z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) :
    (range d.e ∪ range H) ∩ B =
      range d.M.boundarySide ∪ range (fun w : Interval => H (0,w)) ∪
        range (fun w : Interval => H (1,w)) := by
  have hHB : range H ∩ B =
      range (fun w : Interval => H (0,w)) ∪ range (fun w : Interval => H (1,w)) := by
    ext y
    constructor
    · rintro ⟨⟨z,rfl⟩,hz⟩
      rcases (hB z).mp hz with h0 | h1
      · have he : z = (0,z.2) := Prod.ext h0 rfl
        exact Or.inl ⟨z.2,congrArg H he.symm⟩
      · have he : z = (1,z.2) := Prod.ext h1 rfl
        exact Or.inr ⟨z.2,congrArg H he.symm⟩
    · rintro (⟨w,rfl⟩ | ⟨w,rfl⟩)
      · exact ⟨mem_range_self (0,w),(hB (0,w)).mpr (Or.inl rfl)⟩
      · exact ⟨mem_range_self (1,w),(hB (1,w)).mpr (Or.inr rfl)⟩
  rw [union_inter_distrib_right,d.disk_B_trace,hHB,union_assoc]


/-- Whole q control reduces to excluding future q parameters from the actual collar.
The incoming side and the exact eta parametrization supply all of [0,t]. -/
theorem actual_enlarged_whole_q_trace
    {S : Type} [TopologicalSpace S] {Q : Set S} {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q)
    (H : C(Interval × Interval, ↥Q))
    (hseam : ∀ u, H (u,0) = d.sideArc u)
    (eta : C(Interval, Interval × Interval))
    (hexact : ∀ u : Interval, H (eta u) = q (d.xi (Set.Icc.convexComb d.s d.t u)))
    (hfuture : Disjoint ((fun u => q (d.xi u)) '' Ioi d.t) (range H)) :
    (range d.e ∪ range H) ∩ range q =
      (fun u => q (d.xi u)) '' Icc 0 d.t := by
  have htail : (fun u => q (d.xi u)) '' Icc d.s d.t ⊆ range H := by
    rw [← actual_eta_trace d H eta hexact]
    rintro y ⟨u,rfl⟩
    exact mem_range_self (eta u)
  ext y
  constructor
  · rintro ⟨hy,⟨v,rfl⟩⟩
    obtain ⟨u,hu⟩ := d.xi.surjective v
    have hclock : q (d.xi u) = q v := congrArg q hu
    have hut : u ≤ d.t := by
      rcases hy with he | hH
      · have hsecond : q v ∈ range d.M.second := d.disk_q_trace ▸ ⟨he,mem_range_self v⟩
        rw [d.second_trace] at hsecond
        obtain ⟨w,hw,hew⟩ := hsecond
        have hwu : w = u := d.xi.injective (d.q_embedded.injective (hew.trans hclock.symm))
        exact hwu ▸ hw.2.trans d.tail_order.2.1.le
      · apply le_of_not_gt
        intro htu
        exact disjoint_left.mp hfuture ⟨u,htu,hclock⟩ hH
    exact ⟨u,⟨bot_le,hut⟩,hclock⟩
  · rintro ⟨u,hu,rfl⟩
    refine ⟨?_,mem_range_self (d.xi u)⟩
    by_cases hus : u ≤ d.s
    · have hs : q (d.xi u) ∈ range d.M.second := by
        rw [d.second_trace]
        exact ⟨u,⟨hu.1,hus⟩,rfl⟩
      have hd : q (d.xi u) ∈ range d.e ∩ range q := d.disk_q_trace.symm ▸ hs
      exact Or.inl hd.1
    · exact Or.inr (htail ⟨u,⟨le_of_lt (lt_of_not_ge hus),hu.2⟩,rfl⟩)


/-- Assemble every field of the unchanged collar from actual H/eta geometry.
This is a checked consumer, not an existence premise of H2. -/
theorem assemble_actual_relative_collar
    {S : Type} [TopologicalSpace S] {Q : Set S} [T2Space ↥Q] {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q)
    (H : C(Interval × Interval, ↥Q)) (eta : C(Interval, Interval × Interval))
    (hH : IsEmbedding H)
    (hseam : ∀ u, H (u,0) = d.sideArc u)
    (hB : ∀ z, H z ∈ B ↔ z.1 = 0 ∨ z.1 = 1)
    (hW : range H ⊆ d.W)
    (hintersection : range H ∩ range d.e = range d.sideArc)
    (hetaone : (eta 1).2 = 1 ∧ (eta 1).1 ∈ Ioo (0 : Interval) 1)
    (hetainterior : ∀ u ∈ Ioo (0 : Interval) 1,
      eta u ∈ Ioo (0 : Interval) 1 ×ˢ Ioo (0 : Interval) 1)
    (hexact : ∀ u : Interval, H (eta u) = q (d.xi (Set.Icc.convexComb d.s d.t u)))
    (hfuture : Disjoint ((fun u => q (d.xi u)) '' Ioi d.t) (range H)) :
    Nonempty (RelativeHalfCollar d) := by
  classical
  obtain ⟨corner,hcorner,hcorner_on_side⟩ := actual_side_corner_parameter d
  obtain ⟨e,he,herange,heboundary⟩ := actual_collar_glues_original_disk d H hH hseam hintersection
  have heta0 : eta 0 = (corner,0) := by
    apply hH.injective
    rw [hexact,Set.Icc.convexComb_zero,d.q_corner,hseam,hcorner_on_side]
  refine ⟨{
    H := H
    H_embedded := hH
    seam := hseam
    endpoints_in_B := fun w => ⟨(hB (0,w)).mpr (Or.inl rfl),(hB (1,w)).mpr (Or.inr rfl)⟩
    interior_off_B := ?_
    collar_in_W := hW
    disk_intersection := hintersection
    collision_kernel := actual_collar_collision_kernel H hH
    beta_collision := actual_collar_beta_collision d H hH hseam hintersection
    corner := corner
    corner_interior := hcorner
    corner_on_side := hcorner_on_side
    eta := eta
    eta_embedded := actual_eta_embedding d H eta hexact
    eta_zero := heta0
    eta_one := hetaone
    eta_interior := hetainterior
    eta_exact_parameter := hexact
    eta_trace := actual_eta_trace d H eta hexact
    whole_q_trace := actual_enlarged_whole_q_trace d H hseam eta hexact hfuture
    enlargedDisk := e
    enlarged_embedded := he
    enlarged_range := herange
    enlarged_boundary := heboundary
    enlarged_B_trace := actual_enlarged_B_trace d H hB }⟩
  intro u hu w hh
  rcases (hB (u,w)).mp hh with h0 | h1
  · exact hu.1.ne' h0
  · exact hu.2.ne h1

theorem actual_disk_side_exterior_half_from_strip
    {X : Type} [TopologicalSpace X] [T2Space X]
    (B : Set X) (D : C(Interval × Interval,X)) (hD : IsEmbedding D)
    (E : C(Interval × Icc (-1:ℝ) 1,X)) (hE : IsEmbedding E)
    (hc : ∀ t, E (t,⟨0,by norm_num⟩) = D (t,0))
    (hEB : ∀ z, E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1)
    (hopen : IsOpen (E '' {z | -1 < z.2.val ∧ z.2.val < 1})) :
    ∃ L : C(Interval × Interval,X), IsEmbedding L ∧
      (∀ t, L (t,0) = D (t,0)) ∧ range L ⊆ range E ∧
      range L ∩ range D = range (fun t : Interval => D (t,0)) ∧
      (∀ z, L z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) := by
  let U : Set X := E '' {z | -1 < z.2.val ∧ z.2.val < 1}
  have hprod : (univ : Set Interval) ×ˢ ({0} : Set Interval) ⊆ D ⁻¹' U := by
    rintro ⟨t,w⟩ ⟨_,hw⟩
    obtain rfl := mem_singleton_iff.mp hw
    exact ⟨(t,⟨0,by norm_num⟩),by norm_num,hc t⟩
  obtain ⟨A,V,hA,hV,hIA,h0V,hAV⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton
      (hopen.preimage D.continuous) hprod
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton _))
  let δ : ℝ := min (r/2) (1/2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  let scale : Interval × Interval → Interval × Interval := fun z =>
    (z.1,⟨δ*(z.2:ℝ),by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ,hδ1]⟩)
  have hsc : Continuous scale := by dsimp [scale]; fun_prop
  have hthin (z : Interval × Interval) : D (scale z) ∈ U := by
    apply hAV
    refine ⟨hIA (mem_univ _),hrV ?_⟩
    rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
    change |δ*(z.2:ℝ)-0| < r
    rw [sub_zero,abs_of_nonneg (mul_nonneg hδ.le z.2.property.1)]
    exact (mul_le_of_le_one_right hδ.le z.2.property.2).trans_lt hδr
  let e := hE.toHomeomorph
  let k : C(Interval × Interval,Interval × Icc (-1:ℝ) 1) :=
    ⟨fun z => e.symm ⟨D (scale z),image_subset_range E _ (hthin z)⟩,
      e.symm.continuous.comp ((D.continuous.comp hsc).subtype_mk _)⟩
  have hEk (z) : E (k z) = D (scale z) :=
    congrArg Subtype.val (e.apply_symm_apply _)
  have hn (z : Interval × Interval) (hz : 0 < z.2) : ((k z).2:ℝ) ≠ 0 := by
    intro he
    have hw : (k z).2 = (⟨0,by norm_num⟩ : Icc (-1:ℝ) 1) := Subtype.ext he
    have hm : E (k z) = D ((k z).1,0) := by
      rw [show k z = ((k z).1,⟨0,by norm_num⟩) from Prod.ext rfl hw,hc]
    have hh := congrArg (fun z : Interval × Interval => (z.2:ℝ))
      (hD.injective (hm.symm.trans (hEk z)))
    change 0 = δ*(z.2:ℝ) at hh
    have hz' : (0:ℝ) < z.2 := hz
    exact (mul_pos hδ hz').ne' hh.symm
  have hp : IsPreconnected ((univ : Set Interval) ×ˢ Ioi (0:Interval)) :=
    isPreconnected_univ.prod isPreconnected_Ioi
  have hside := hp.mapsTo_Ioi_or_Iio
    (show Continuous (fun z => ((k z).2:ℝ)) from
      continuous_subtype_val.comp (continuous_snd.comp k.continuous)).continuousOn
    (fun z hz => hn z hz.2)
  let F : Set X := D '' {z | δ ≤ (z.2:ℝ)}
  have hF : IsClosed F := ((isClosed_le continuous_const
    (continuous_subtype_val.comp continuous_snd)).isCompact.image D.continuous).isClosed
  have hcenterF (t : Interval) : E (t,⟨0,by norm_num⟩) ∉ F := by
    rw [hc]
    rintro ⟨z,hz,he⟩
    have hh := congrArg (fun z : Interval × Interval => (z.2:ℝ)) (hD.injective he)
    change (z.2:ℝ) = 0 at hh
    change δ ≤ (z.2:ℝ) at hz
    rw [hh] at hz
    linarith
  obtain ⟨ρ,hρ,N,hN,hNF,hNform,hNcenter⟩ :=
    source_shrink_embedded_strip_in_open E hE Fᶜ hF.isOpen_compl hcenterF
  have build (σ : ℝ) (hσ : σ = -1 ∨ σ = 1)
      (hopp : ∀ z, 0 < z.2 → σ*((k z).2:ℝ) < 0) :
      ∃ L : C(Interval × Interval,X), IsEmbedding L ∧
        (∀ t, L (t,0) = D (t,0)) ∧ range L ⊆ range E ∧
        range L ∩ range D = range (fun t : Interval => D (t,0)) ∧
        (∀ z, L z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) := by
    have hσn : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hσ2 : σ*σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    let m : Interval × Interval → Interval × Icc (-1:ℝ) 1 := fun z =>
      (z.1,⟨σ*(z.2:ℝ),by rcases hσ with rfl | rfl <;>
        constructor <;> linarith [z.2.property.1,z.2.property.2]⟩)
    have hmc : Continuous m := by dsimp [m]; fun_prop
    have hmi : Function.Injective m := by
      intro z v he
      apply Prod.ext
      · simpa only [m] using congrArg Prod.fst he
      · apply Subtype.ext
        exact mul_left_cancel₀ hσn (congrArg (fun z => (z.2:ℝ)) he)
    let L : C(Interval × Interval,X) := ⟨N ∘ m,hN.continuous.comp hmc⟩
    have hL : IsEmbedding L := hN.comp (hmc.isClosedEmbedding hmi).isEmbedding
    have hL0 (t : Interval) : L (t,0) = D (t,0) := by
      change N (m (t,0)) = _
      rw [show m (t,0) = (t,⟨0,by norm_num⟩) from Prod.ext rfl (Subtype.ext (mul_zero σ)),hNcenter,hc]
    have hform (z) : L z = E (z.1,⟨ρ*(σ*(z.2:ℝ)),by
        rcases hσ with rfl | rfl <;> constructor <;>
        nlinarith [hρ.1,hρ.2,z.2.property.1,z.2.property.2]⟩) := hNform (m z)
    have hmeet (z : Interval × Interval) (hz : L z ∈ range D) : z.2 = 0 := by
      obtain ⟨v,hv⟩ := hz
      have hvδ : (v.2:ℝ) < δ := lt_of_not_ge (fun hh =>
        (hNF (mem_range_self (m z))) ⟨v,hh,hv⟩)
      let w : Interval := ⟨(v.2:ℝ)/δ,⟨div_nonneg v.2.property.1 hδ.le,
        (div_le_one hδ).mpr hvδ.le⟩⟩
      have hs : scale (v.1,w) = v := by
        apply Prod.ext
        · rfl
        apply Subtype.ext
        change δ*((v.2:ℝ)/δ) = (v.2:ℝ)
        field_simp [hδ.ne']
      have he : E (k (v.1,w)) = E (z.1,⟨ρ*(σ*(z.2:ℝ)),by
          rcases hσ with rfl | rfl <;> constructor <;>
          nlinarith [hρ.1,hρ.2,z.2.property.1,z.2.property.2]⟩) := by
        exact (hEk _).trans ((congrArg D hs).trans (hv.trans (hform z)))
      have hk := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => (z.2:ℝ)) (hE.injective he)
      by_cases hw0 : v.2 = 0
      · have hv0 : v = (v.1,0) := by
          apply Prod.ext
          · rfl
          · exact hw0
        have he' : E (z.1,⟨ρ*(σ*(z.2:ℝ)),by
            rcases hσ with rfl | rfl <;> constructor <;>
            nlinarith [hρ.1,hρ.2,z.2.property.1,z.2.property.2]⟩) = E (v.1,⟨0,by norm_num⟩) := by
          exact (hform z).symm.trans (hv.symm.trans
            ((congrArg D hv0).trans (hc v.1).symm))
        have hh := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => (z.2:ℝ)) (hE.injective he')
        apply Subtype.ext
        change (z.2:ℝ) = 0
        change ρ*(σ*(z.2:ℝ)) = 0 at hh
        exact ((mul_eq_zero.mp hh).resolve_left hρ.1.ne' |> mul_eq_zero.mp).resolve_left hσn
      · have hvpos : (0:ℝ) < v.2 := lt_of_le_of_ne v.2.property.1
          (fun he => hw0 (Subtype.ext he.symm))
        have hwpos : (0:Interval) < w := div_pos hvpos hδ
        have hh := hopp (v.1,w) hwpos
        rw [hk] at hh
        have hnon : 0 ≤ σ*(ρ*(σ*(z.2:ℝ))) := by
          rcases hσ with rfl | rfl <;> nlinarith [hρ.1,z.2.property.1]
        exact False.elim (not_lt_of_ge hnon hh)
    refine ⟨L,hL,hL0,?_,?_,?_⟩
    · rintro y ⟨z,rfl⟩
      rw [hform]
      exact mem_range_self _
    · ext y
      constructor
      · rintro ⟨⟨z,rfl⟩,hz⟩
        have h0 := hmeet z hz
        exact ⟨z.1,(hL0 z.1).symm.trans (congrArg L (Prod.ext rfl h0.symm))⟩
      · rintro ⟨t,rfl⟩
        exact ⟨⟨(t,0),hL0 t⟩,mem_range_self (t,0)⟩
    · intro z
      rw [hform,hEB]
  rcases hside with hside | hside
  · apply build (-1) (Or.inl rfl)
    intro z hz
    have hh := hside ⟨mem_univ _,hz⟩
    change 0 < ((k z).2:ℝ) at hh
    linarith
  · apply build 1 (Or.inr rfl)
    intro z hz
    have hh := hside ⟨mem_univ _,hz⟩
    change ((k z).2:ℝ) < 0 at hh
    simpa only [one_mul] using hh


/-- Normalize the literal F strip around p and narrow it into the supplied open W. -/
theorem actual_signed_side_strip_in_W
    {S : Type} [TopologicalSpace S] {Q : Set S} [T2Space ↥Q] {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q) :
    ∃ E : C(Interval × Icc (-1 : ℝ) 1,↥Q), IsEmbedding E ∧
      (∀ u, E (u,⟨0,by norm_num⟩) = d.sideArc u) ∧
      (∀ z, E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) ∧
      IsOpen (E '' {z | -1 < z.2.val ∧ z.2.val < 1}) ∧ range E ⊆ d.W := by
  let ε : ℝ := min ((d.p : ℝ)/2) ((1-(d.p : ℝ))/2)
  have hp : (0:ℝ) < d.p ∧ (d.p:ℝ) < 1 := d.p_interior
  have he : 0 < ε := lt_min (by linarith [hp.1]) (by linarith [hp.2])
  have hlo : ε ≤ (d.p : ℝ)/2 := min_le_left _ _
  have hhi : ε ≤ (1-(d.p : ℝ))/2 := min_le_right _ _
  have hwidth (w : Icc (-1:ℝ) 1) : 0 < (d.p:ℝ)+ε*w ∧ (d.p:ℝ)+ε*w < 1 := by
    constructor <;> nlinarith [w.property.1,w.property.2]
  let k : Interval × Icc (-1:ℝ) 1 → Interval × Interval := fun z =>
    (z.1,⟨(d.p:ℝ)+ε*z.2,⟨(hwidth z.2).1.le,(hwidth z.2).2.le⟩⟩)
  have hkc : Continuous k := by dsimp [k]; fun_prop
  have hki : Function.Injective k := by
    intro z v hv
    apply Prod.ext
    · simpa [k] using congrArg Prod.fst hv
    · apply Subtype.ext
      have hv' := congrArg (fun z : Interval × Interval => (z.2:ℝ)) hv
      change (d.p:ℝ)+ε*z.2 = (d.p:ℝ)+ε*v.2 at hv'
      nlinarith
  let E : C(Interval × Icc (-1:ℝ) 1,↥Q) := ⟨d.F ∘ k,d.F.continuous.comp hkc⟩
  have hE : IsEmbedding E := d.F_embedded.comp (hkc.isClosedEmbedding hki).isEmbedding
  have hc (u) : E (u,⟨0,by norm_num⟩) = d.sideArc u := by
    change d.F (k (u,⟨0,by norm_num⟩)) = _
    rw [show k (u,⟨0,by norm_num⟩) = (u,d.p) from Prod.ext rfl
      (Subtype.ext (by simp [k])),d.F_center]
  have hEB (z) : E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := d.F_boundary (k z)
  let U : Set (Interval × Interval) := {z | (d.p:ℝ)-ε < z.2 ∧ (z.2:ℝ) < d.p+ε}
  have hU : IsOpen U := (isOpen_lt continuous_const
    (continuous_subtype_val.comp continuous_snd)).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
  have hsub : U ⊆ {z : Interval × Interval | z.2 ∈ Ioo (0:Interval) 1} := by
    intro z hz
    change 0 < (z.2:ℝ) ∧ (z.2:ℝ) < 1
    exact ⟨by have hh := hz.1; linarith,
      by have hh := hz.2; linarith⟩
  obtain ⟨O,hO,hFO⟩ := d.F_embedded.isInducing.image_eq_isOpen_inter_range hU
  have hFO' : d.F '' U = O ∩ d.F '' {z | z.2 ∈ Ioo (0:Interval) 1} := by
    apply Subset.antisymm
    · intro y hy
      exact ⟨(hFO ▸ hy).1,image_mono hsub hy⟩
    · intro y hy
      rw [hFO]
      exact ⟨hy.1,image_subset_range d.F _ hy.2⟩
  have hopen : IsOpen (d.F '' U) := by rw [hFO']; exact hO.inter d.F_open
  have himage : E '' {z | -1 < z.2.val ∧ z.2.val < 1} = d.F '' U := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨k z,?_,rfl⟩
      change (d.p:ℝ)-ε < (d.p:ℝ)+ε*z.2 ∧ (d.p:ℝ)+ε*z.2 < d.p+ε
      constructor <;> nlinarith [hz.1,hz.2]
    · rintro ⟨z,hz,rfl⟩
      let w : Icc (-1:ℝ) 1 := ⟨((z.2:ℝ)-d.p)/ε,by
        constructor
        · apply (le_div_iff₀ he).mpr
          have hh := hz.1; linarith
        · apply (div_le_iff₀ he).mpr
          have hh := hz.2; linarith⟩
      have hw : -1 < w.val ∧ w.val < 1 := by
        dsimp [w]
        constructor
        · apply (lt_div_iff₀ he).mpr
          have hh := hz.1; linarith
        · apply (div_lt_iff₀ he).mpr
          have hh := hz.2; linarith
      refine ⟨(z.1,w),hw,?_⟩
      apply congrArg d.F
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change (d.p:ℝ)+ε*(((z.2:ℝ)-d.p)/ε) = (z.2:ℝ)
        field_simp [he.ne']
        <;> ring
  have hEopen : IsOpen (E '' {z | -1 < z.2.val ∧ z.2.val < 1}) := by rw [himage]; exact hopen
  have hcenterW (u) : E (u,⟨0,by norm_num⟩) ∈ d.W := by
    rw [hc]
    apply d.disk_in_W
    have hm : d.sideArc u ∈ range d.sideArc := mem_range_self u
    rw [d.side_range] at hm
    have hbd : d.sideArc u ∈ d.e '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} := by
      rw [d.disk_boundary]
      exact Or.inl hm
    exact image_subset_range d.e _ hbd
  obtain ⟨ρ,hρ,N,hN,hNW,hform,hcenter⟩ := source_shrink_embedded_strip_in_open
    E hE d.W d.W_open hcenterW
  let E' : C(Interval × Icc (-1:ℝ) 1,↥Q) := ⟨N,hN.continuous⟩
  have hNB (z) : E' z ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := by
    change N z ∈ B ↔ _
    rw [hform]
    exact hEB _
  have hNopen : IsOpen (E' '' {z | -1 < z.2.val ∧ z.2.val < 1}) := by
    -- A narrower signed strip has an open band by the same inducing argument.
    let V : Set (Interval × Icc (-1:ℝ) 1) := {z | -ρ < z.2.val ∧ z.2.val < ρ}
    have hV : IsOpen V := (isOpen_lt continuous_const
      (continuous_subtype_val.comp continuous_snd)).inter
        (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
    obtain ⟨A,hA,hEA⟩ := hE.isInducing.image_eq_isOpen_inter_range hV
    have hVsub : V ⊆ {z | -1 < z.2.val ∧ z.2.val < 1} := by
      intro z hz
      exact ⟨lt_of_le_of_lt (by linarith [hρ.2]) hz.1,hz.2.trans_le hρ.2⟩
    have hEq : E '' V = A ∩ E '' {z | -1 < z.2.val ∧ z.2.val < 1} := by
      apply Subset.antisymm
      · intro y hy
        exact ⟨(hEA ▸ hy).1,image_mono hVsub hy⟩
      · intro y hy
        rw [hEA]
        exact ⟨hy.1,image_subset_range E _ hy.2⟩
    have hImage : E' '' {z | -1 < z.2.val ∧ z.2.val < 1} = E '' V := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        refine ⟨(z.1,⟨ρ*z.2,by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]⟩),?_,(hform z).symm⟩
        change -ρ < ρ*z.2 ∧ ρ*z.2 < ρ
        constructor <;> nlinarith [hz.1,hz.2,hρ.1]
      · rintro ⟨z,hz,rfl⟩
        let w : Icc (-1:ℝ) 1 := ⟨z.2.val/ρ,by
          constructor
          · apply (le_div_iff₀ hρ.1).mpr; linarith [hz.1]
          · apply (div_le_iff₀ hρ.1).mpr; linarith [hz.2]⟩
        have hw : -1 < w.val ∧ w.val < 1 := by
          dsimp [w]
          constructor
          · apply (lt_div_iff₀ hρ.1).mpr; linarith [hz.1]
          · apply (div_lt_iff₀ hρ.1).mpr; linarith [hz.2]
        refine ⟨(z.1,w),hw,?_⟩
        change N (z.1,w) = _
        rw [hform]
        apply congrArg E
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          change ρ*(z.2.val/ρ) = z.2.val
          field_simp [hρ.1.ne']
    rw [hImage,hEq]
    exact hA.inter hEopen
  exact ⟨E',hN,fun u => (hcenter u).trans (hc u),hNB,hNopen,hNW⟩

/-- A genuine exterior collar of the whole unchanged side, in W, is constructible
without asking it to contain the outgoing q-tail. -/
theorem actual_original_side_exterior_collar
    {S : Type} [TopologicalSpace S] {Q : Set S} [T2Space ↥Q] {B : Set ↥Q}
    {a q : C(Interval, ↥Q)} (d : CleanHalfLocalData S Q B a q) :
    ∃ H : C(Interval × Interval,↥Q), IsEmbedding H ∧
      (∀ u, H (u,0) = d.sideArc u) ∧
      (∀ z, H z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) ∧
      range H ⊆ d.W ∧ range H ∩ range d.e = range d.sideArc := by
  obtain ⟨P,hP,hPr,hPt,hPo⟩ :=
    ActualHarerDiskGluing.actual_two_side_disk_constructs_prescribed_edge_square
      d.sideArc d.M.boundarySide d.e d.side_embedded d.M.boundary_embedded d.e_embedded
      (d.side_zero.trans d.M.boundary_zero.symm) (d.side_one.trans d.M.boundary_one.symm)
      (actual_two_side_boundary d) (fun u v he => (actual_side_beta_collision d u v).mp he)
  let flip := (Homeomorph.refl Interval).prodCongr unitInterval.symmHomeomorph
  let D : C(Interval × Interval,↥Q) := ⟨P ∘ flip,P.continuous.comp flip.continuous⟩
  have hD : IsEmbedding D := hP.comp flip.isEmbedding
  have hDcenter (u) : D (u,0) = d.sideArc u := by
    change P (u,unitInterval.symm 0) = _
    rw [unitInterval.symm_zero,hPt]
  have hDr : range D = range d.e := by
    change range (P ∘ flip) = _
    rw [flip.surjective.range_comp,hPr]
  obtain ⟨E,hE,hEc,hEB,hEopen,hEW⟩ := actual_signed_side_strip_in_W d
  obtain ⟨H,hH,hc,hHE,hinter,hB⟩ := actual_disk_side_exterior_half_from_strip B D hD E hE
    (fun u => (hEc u).trans (hDcenter u).symm) hEB hEopen
  refine ⟨H,hH,fun u => (hc u).trans (hDcenter u),hB,hHE.trans hEW,?_⟩
  rw [← hDr,hinter]
  congr 1
  funext u
  exact hDcenter u

end CoherentEndpointMotion.RelativeCleanHalfAlignment
