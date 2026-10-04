import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.BoundaryAmbientTransport
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalSquareFiniteContact
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualBoundaryProperArcStrip

namespace CoherentEndpointMotion
open CurveComplex Set Topology Schoenflies
open RegionalFinitePosition

/-- The frontier of the literal deleted chart disk is the literal chart
sphere. This identifies the existing regional position tools with the original
Q, without introducing a region or a fixed-endpoint homotopy assumption. -/
theorem chart_deleted_disk_complement_frontier
    {S : Type} [TopologicalSpace S] [T2Space S]
    (E : OpenPartialHomeomorph S Plane) (p : Plane) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall p R ⊆ E.target) :
    frontier (E.symm '' Metric.ball p R)ᶜ = E.symm '' Metric.sphere p R := by
  let D : Set S := E.symm '' Metric.ball p R
  let K : Set S := E.symm '' Metric.closedBall p R
  have hK : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    (E.continuousOn_symm.mono htarget)
  have hKs : K ⊆ E.source := by
    rintro y ⟨z,hz,rfl⟩
    exact E.map_target (htarget hz)
  have hDK : D ⊆ K := Set.image_mono Metric.ball_subset_closedBall
  have hDs : D ⊆ E.source := hDK.trans hKs
  have hI : E.IsImage D (Metric.ball p R) := by
    intro y hy
    constructor
    · intro hz
      exact ⟨E y,hz,E.left_inv hy⟩
    · rintro ⟨z,hz,rfl⟩
      rwa [E.right_inv (htarget (Metric.ball_subset_closedBall hz))]
  have hfs : frontier D ⊆ E.source :=
    frontier_subset_closure.trans ((hK.isClosed.closure_subset_iff.mpr hDK).trans hKs)
  have hh := hI.frontier.symm_image_eq
  rw [frontier_ball p hR.ne',inter_eq_right.mpr
    (Metric.sphere_subset_closedBall.trans htarget),inter_eq_right.mpr hfs] at hh
  rw [frontier_compl]
  exact hh.symm

/-- A short initial germ of an embedded arc can be made wholly disjoint from
a compact comparison arc when its initial endpoint is already disjoint. -/
theorem embedded_arc_initial_clean_germ
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (a b : C(Interval,X)) (hb : IsEmbedding b) (hb0 : b 0 ∉ range a)
    (B : Set X) (hbi : ∀ t ∈ Ioo (0 : Interval) 1, b t ∉ B) :
    ∃ k : C(Interval,X), IsEmbedding k ∧ k 0 = b 0 ∧
      (∀ t ∈ Ioo (0 : Interval) 1, k t ∉ B) ∧
      Disjoint (range a) (range k) := by
  have hW : IsOpen (b ⁻¹' (range a)ᶜ) :=
    (isCompact_range a.continuous).isClosed.isOpen_compl.preimage b.continuous
  obtain ⟨δ,hδ,hδW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hb0)
  let ε : ℝ := min δ 1 / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; linarith [min_le_left δ 1]
  have hε1 : ε < 1 := by dsimp [ε]; linarith [min_le_right δ 1]
  let τ (s : Interval) : Interval := ⟨ε*(s:ℝ),by
    constructor
    · exact mul_nonneg hε.le s.property.1
    · nlinarith [s.property.2]⟩
  have hτc : Continuous τ := by apply Continuous.subtype_mk; fun_prop
  have hτi : Function.Injective τ := by
    intro s t h
    apply Subtype.ext
    exact mul_left_cancel₀ hε.ne' (congrArg Subtype.val h)
  let k : C(Interval,X) := ⟨b ∘ τ,b.continuous.comp hτc⟩
  refine ⟨k,(k.continuous.isClosedEmbedding (hb.injective.comp hτi)).isEmbedding,
    congrArg b (Subtype.ext (by simp [τ])),?_,?_⟩
  · intro s hs
    apply hbi
    constructor
    · change (0:ℝ) < ε*(s:ℝ)
      exact mul_pos hε hs.1
    · change ε*(s:ℝ) < 1
      nlinarith [s.property.2]
  · apply Set.disjoint_left.mpr
    rintro z hz ⟨s,rfl⟩
    have hh : τ s ∈ Metric.ball (0:Interval) δ := by
      change dist (τ s) (0:Interval) < δ
      rw [Subtype.dist_eq,Real.dist_eq]
      change |ε*(s:ℝ)-0| < δ
      rw [sub_zero,abs_of_nonneg (mul_nonneg hε.le s.property.1)]
      nlinarith [s.property.2]
    exact hδW hh hz

/-- Endpoint separation supplies the two clean access germs needed by the
checked finite-contact construction. It requires no movie between a and b. -/
theorem square_finite_crosscut_from_separated_endpoints
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F : Set S) (D : C(Square,↥F)) (hD : IsEmbedding D)
    (a b : C(Interval,↥F)) (hb : IsEmbedding b)
    (hbi : ∀ s ∈ Ioo (0:Interval) 1, (b s).val ∉ frontier F)
    (hb0 : b 0 ∉ range a) (hb1 : b 1 ∉ range a)
    (hcenter : ∀ s, D (horizontalPoint s) = b s)
    (hback : ∀ z : Square, |z.val 1| < 1 → (D z).val ∉ frontier F →
      z.val ∈ Plane.openSquare 0 1)
    (hopen : IsOpen (D '' {z : Square | |z.val 1| < 1}))
    (hlocal : ∀ x ∈ Plane.openSquare 0 1, ∃ V : Set Plane,
      IsOpen V ∧ x ∈ V ∧ V ⊆ Plane.openSquare 0 1 ∧
      ∀ y ∈ V, x ≠ y → ∃ C ⊆ Plane.openSquare 0 1,
        IsArcBetween C x y ∧ (C ∩ squareObstacle D a).Finite) :
    ∃ C : Set Plane, IsArcBetween C (Plane.mk (-1) 0) (Plane.mk 1 0) ∧
      C \ {Plane.mk (-1) 0,Plane.mk 1 0} ⊆ Plane.openSquare 0 1 ∧
      {z : Square | z.val ∈ C ∧ D z ∈ range a}.Finite := by
  obtain ⟨k,hk,hk0,hki,hak⟩ := embedded_arc_initial_clean_germ a b hb hb0
    {y | y.val ∈ frontier F} hbi
  have hakfin : (range a ∩ range k).Finite := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hak]
    exact Set.finite_empty
  obtain ⟨u,L,hu,hL,hLU,hLA⟩ := square_access_of_clean_arc F D hD hback hopen a k hk
    hki hakfin (horizontalPoint 0) (by norm_num [horizontalPoint,Plane.mk])
    (hk0.trans (hcenter 0).symm)
  let br : C(Interval,↥F) := ⟨fun s => b (unitInterval.symm s),
    b.continuous.comp unitInterval.continuous_symm⟩
  have hbr : IsEmbedding br := by
    apply (br.continuous.isClosedEmbedding ?_).isEmbedding
    intro s t h
    exact unitInterval.symm_bijective.injective (hb.injective h)
  have hbri : ∀ s ∈ Ioo (0:Interval) 1, (br s).val ∉ frontier F := by
    intro s hs
    apply hbi
    change 0 < unitInterval.symm s ∧ unitInterval.symm s < 1
    constructor
    · change (0:ℝ) < 1-(s:ℝ)
      have h : (s:ℝ) < 1 := hs.2
      linarith
    · change (1:ℝ)-(s:ℝ) < 1
      have h : (0:ℝ) < s := hs.1
      linarith
  have hbr0 : br 0 = b 1 := by simp [br]
  obtain ⟨k',hk',hk'0,hk'i,hak'⟩ := embedded_arc_initial_clean_germ a br hbr
    (by rw [hbr0]; exact hb1) {y | y.val ∈ frontier F} hbri
  have hak'fin : (range a ∩ range k').Finite := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hak']
    exact Set.finite_empty
  obtain ⟨v,R,hv,hR,hRU,hRA⟩ := square_access_of_clean_arc F D hD hback hopen a k' hk'
    hk'i hak'fin (horizontalPoint 1) (by norm_num [horizontalPoint,Plane.mk])
    (hk'0.trans (hbr0.trans (hcenter 1).symm))
  have hp0 : (horizontalPoint 0).val = Plane.mk (-1) 0 := by
    ext i; fin_cases i <;> norm_num [horizontalPoint,Plane.mk]
  have hp1 : (horizontalPoint 1).val = Plane.mk 1 0 := by
    ext i; fin_cases i <;> norm_num [horizontalPoint,Plane.mk]
  rw [hp0] at hL hLU
  rw [hp1] at hR hRU
  obtain ⟨C,hC,hCi,hCA⟩ := finite_contact_arc_with_access (Plane.openSquare 0 1)
    (squareObstacle D a) L R (Plane.isOpen_openSquare 0 1)
    (Plane.convex_openSquare 0 1).isPreconnected hlocal
    (Plane.mk (-1) 0) (Plane.mk 1 0) u v
    (by intro h; have h := congrArg (fun z : Plane => z 0) h; norm_num [Plane.mk] at h)
    (by norm_num [mem_openSquare_zero_one,Plane.supNorm,Plane.mk])
    (by norm_num [mem_openSquare_zero_one,Plane.supNorm,Plane.mk]) hu hv hL hR hLU hRU hLA hRA
  refine ⟨C,hC,hCi,?_⟩
  apply (hCA.preimage Subtype.val_injective.injOn).subset
  intro z hz
  exact ⟨hz.1,⟨z.property,hz.2⟩⟩

/-- A finite crosscut in the actual square carrier is reached by an ambient
motion of F. Its entire frontier stays pointwise fixed, and the motion is
supported in the carrier's open interior. -/
theorem embedded_square_finite_position_ambient_motion
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F : Set S) (a b : C(Interval,↥F))
    (D : C(Square,↥F)) (hD : IsEmbedding D)
    (hcenter : ∀ s, D (horizontalPoint s) = b s)
    (hclear : ∀ z : Square, z.val ∈ Plane.openSquare 0 1 →
      (D z).val ∉ frontier F)
    (hopen : IsOpen (D '' {z : Square | |z.val 1| < 1}))
    (C : Set Plane)
    (hC : IsArcBetween C (Plane.mk (-1) 0) (Plane.mk 1 0))
    (hCi : C \ {Plane.mk (-1) 0,Plane.mk 1 0} ⊆ Plane.openSquare 0 1)
    (hfinite : {z : Square | z.val ∈ C ∧ D z ∈ range a}.Finite)
    (hb : IsEmbedding b)
    (hbends : (b 0).val ∈ frontier F ∧ (b 1).val ∈ frontier F)
    (hbi : ∀ s ∈ Ioo (0:Interval) 1, (b s).val ∉ frontier F) :
    ∃ q : C(Interval,↥F), ∃ H : AmbientIsotopy ↥F,
      IsEmbedding q ∧ q 0 = b 0 ∧ q 1 = b 1 ∧
      (∀ s ∈ Ioo (0:Interval) 1, (q s).val ∉ frontier F) ∧
      (∀ t y, y.val ∈ frontier F → H.map (t,y) = y) ∧
      H.finalMap '' range b = range q ∧
      (range a ∩ range q).Finite ∧
      (∀ t y, y ∉ range D → H.map (t,y) = y) := by
  letI : CompactSpace Square := isCompact_iff_compactSpace.mp
    (Schoenflies.isCompact_closedSquare (0 : Plane) (1 : ℝ))
  let W : Set Square := {z | z.val ∈ Plane.openSquare 0 1}
  have hW : IsOpen W := (Plane.isOpen_openSquare 0 1).preimage continuous_subtype_val
  obtain ⟨O,hO,himage⟩ := hD.isInducing.image_eq_isOpen_inter_range hW
  have hDW : IsOpen (D '' W) := by
    have heq : D '' W = O ∩ D '' {z : Square | |z.val 1| < 1} := by
      apply Set.Subset.antisymm
      · rintro y hy
        have hyO := (himage ▸ hy).1
        obtain ⟨z,hz,rfl⟩ := hy
        exact ⟨hyO,⟨z,lt_of_le_of_lt (le_max_right _ _)
          (mem_openSquare_zero_one.mp hz),rfl⟩⟩
      · rintro y ⟨hy,z,hz,rfl⟩
        rw [himage]
        exact ⟨hy,Set.mem_range_self z⟩
    rw [heq]
    exact hO.inter hopen
  let A := segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)
  have hA : IsArcBetween A (Plane.mk (-1) 0) (Plane.mk 1 0) :=
    isArcBetween_segment (by
      intro h
      have he := congrArg (fun z : Plane => z 0) h
      norm_num [Plane.mk] at he)
  have hAi : A \ {Plane.mk (-1) 0,Plane.mk 1 0} ⊆ Plane.openSquare 0 1 := by
    intro z hz
    have hzA : z ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) := hz.1
    rw [← horizontalPoint_range] at hzA
    obtain ⟨s,rfl⟩ := hzA
    apply horizontalPoint_open
    constructor
    · apply bot_lt_iff_ne_bot.mpr
      intro he
      exact hz.2 (Or.inl (by norm_num [he,horizontalPoint,Plane.mk]))
    · apply lt_top_iff_ne_top.mpr
      intro he
      exact hz.2 (Or.inr (by norm_num [he,horizontalPoint,Plane.mk]))
  obtain ⟨R,K,hR,hmove,hfar,hfix⟩ := position_crosscut_supported_isotopy A C
    (Plane.mk (-1) 0) (Plane.mk 1 0) hA hC
    (by norm_num [modelCurve,Plane.supNorm,Plane.mk])
    (by norm_num [modelCurve,Plane.supNorm,Plane.mk]) hAi hCi
  have hstay (t : Interval) (z : Plane) :
      K.map (t,z) ∈ Plane.closedSquare 0 1 ↔ z ∈ Plane.closedSquare 0 1 := by
    by_cases hz : z ∈ Plane.openSquare 0 1
    · have hKz : K.map (t,z) ∈ Plane.openSquare 0 1 := by
        by_contra hn
        obtain ⟨k,hk⟩ := K.homeomorphism_at t
        have heq : K.map (t,z) = z := k.injective (by
          rw [hk,hk]
          exact hfix t _ hn)
        exact hn (heq.symm ▸ hz)
      exact iff_of_true (Plane.openSquare_subset_closedSquare 0 1 hKz)
        (Plane.openSquare_subset_closedSquare 0 1 hz)
    · rw [hfix t z hz]
  let L : AmbientIsotopy Square := {
    map := ⟨fun z => ⟨K.map (z.1,z.2.val),(hstay z.1 z.2.val).mpr z.2.property⟩,
      (K.map.continuous.comp
        (continuous_fst.prodMk continuous_snd.subtype_val)).subtype_mk _⟩
    homeomorphism_at := by
      intro t
      obtain ⟨k,hk⟩ := K.homeomorphism_at t
      exact ⟨k.subtype (fun x => by simpa only [hk] using (hstay t x).symm),
        fun _ => Subtype.ext (hk _)⟩
    at_zero := by intro z; exact Subtype.ext (K.at_zero z.val) }
  have hLfix : ∀ t z, z ∉ W → L.map (t,z) = z := by
    intro t z hz
    exact Subtype.ext (hfix t z.val hz)
  obtain ⟨H,hHD,hHfix⟩ := embedded_cell_isotopy_extend D hD W hDW L hLfix
  have hHF (t : Interval) (y : ↥F) (hy : y.val ∈ frontier F) : H.map (t,y) = y := by
    apply hHfix
    rintro ⟨z,hz,he⟩
    exact hclear z hz (he.symm ▸ hy)
  have hHB (t : Interval) :
      (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
        {y : ↥F | y.val ∈ frontier F} := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      change H.map (t,z) ∈ {y : ↥F | y.val ∈ frontier F}
      rw [hHF t z hz]
      exact hz
    · intro hy
      exact ⟨y,hy,hHF t y hy⟩
  obtain ⟨e,he⟩ := H.homeomorphism_at 1
  let q : C(Interval,↥F) := (⟨e,e.continuous⟩ : C(↥F,↥F)).comp b
  have hq (s : Interval) : q s = H.finalMap (b s) := he (b s)
  refine ⟨q,H,e.isEmbedding.comp hb,?_,?_,?_,hHF,?_,?_,?_⟩
  · exact (hq 0).trans (hHF 1 (b 0) hbends.1)
  · exact (hq 1).trans (hHF 1 (b 1) hbends.2)
  · intro s hs hqB
    apply hbi s hs
    have heB : e '' {y : ↥F | y.val ∈ frontier F} =
      {y : ↥F | y.val ∈ frontier F} := by
      simpa only [← he] using hHB 1
    exact (boundary_preserving_homeomorph_mem _ e heB (b s)).mp hqB
  · rw [← Set.range_comp]
    congr 1
    funext s
    exact (hq s).symm
  · apply (hfinite.image D).subset
    rintro y ⟨hya,s,rfl⟩
    refine ⟨L.map (1,horizontalPoint s),⟨?_,?_⟩,?_⟩
    · change K.map (1,(horizontalPoint s).val) ∈ C
      rw [← hmove]
      refine ⟨(horizontalPoint s).val,?_,rfl⟩
      change (horizontalPoint s).val ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)
      rw [← horizontalPoint_range]
      exact Set.mem_range_self s
    · have hDq : D (L.map (1,horizontalPoint s)) = q s := by
        rw [← hHD,hcenter]
        exact (hq s).symm
      exact hDq.symm ▸ hya
    · rw [← hHD,hcenter]
      exact (hq s).symm
  · intro t y hy
    exact hHfix t y (fun h => hy (Set.image_subset_range D W h))

/-- The original proper-arc collars and separated endpoint germs produce an
actual Q-ambient finite-position motion. The class or homotopy relation of a
and b is not an input, and no finite-contact assumption is used. -/
theorem original_proper_arcs_separated_endpoints_finite_ambient_position
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆ (chartAt Plane x).target) :
    let Q : Set S := ((chartAt Plane x).symm '' Metric.ball ((chartAt Plane x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt Plane x).symm ''
      Metric.sphere ((chartAt Plane x) x) R}
    ∀ (a b : C(Interval,↥Q)), IsEmbedding a → IsEmbedding b →
      (a 0 ∈ B ∧ a 1 ∈ B ∧ b 0 ∈ B ∧ b 1 ∈ B) →
      (∀ s ∈ Ioo (0:Interval) 1, a s ∉ B ∧ b s ∉ B) →
      Disjoint ({a 0,a 1} : Set ↥Q) {b 0,b 1} →
      ∃ q : C(Interval,↥Q), ∃ H : AmbientIsotopy ↥Q,
        IsEmbedding q ∧ q 0 = b 0 ∧ q 1 = b 1 ∧
        (∀ s ∈ Ioo (0:Interval) 1, q s ∉ B) ∧
        (∀ t y, y ∈ B → H.map (t,y) = y) ∧
        H.finalMap '' range b = range q ∧ (range a ∩ range q).Finite := by
  classical
  intro Q B a b ha hb hends hi hsep
  letI : ClosedSurface S := Classical.choice hS.2.1
  have hfront : frontier Q = (chartAt Plane x).symm ''
      Metric.sphere ((chartAt Plane x) x) R :=
    chart_deleted_disk_complement_frontier (chartAt Plane x)
      ((chartAt Plane x) x) R hR htarget
  let pa : CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.ProperArc S x R :=
    ⟨a,ha,hends.1,hends.2.1,fun s hs => (hi s hs).1⟩
  let pb : CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.ProperArc S x R :=
    ⟨b,hb,hends.2.2.1,hends.2.2.2,fun s hs => (hi s hs).2⟩
  obtain ⟨Ea,hEa,hEacenter,hEaend,hEaint,hEaopen⟩ :=
    CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.source_actual_boundary_proper_arc_strip
      S x R g hg hS hR htarget pa
  obtain ⟨Eb,hEb,hEbcenter,hEbend,hEbint,hEbopen⟩ :=
    CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.source_actual_boundary_proper_arc_strip
      S x R g hg hS hR htarget pb
  have hEbclear : ∀ s ∈ Ioo (0:Interval) 1, ∀ w, (Eb (s,w)).val ∉ frontier Q := by
    intro s hs w
    rw [hfront]
    exact hEbint s hs w
  obtain ⟨D,hD,hcenter,hclear,hback,hopen,P,hPs,hP⟩ :=
    strip_square_package Q b Eb hEb hEbcenter
      (fun w => by rw [hfront]; exact hEbend w) hEbclear hEbopen
  let aS : C(Interval,S) := ⟨fun s => (a s).val,continuous_subtype_val.comp a.continuous⟩
  obtain ⟨A,hAs,hAt,hAcoord,hAaxis⟩ := source_embedded_strip_interior_chart
    (fun z => (Ea z).val) (IsEmbedding.subtypeVal.comp hEa) aS
    (fun s => congrArg Subtype.val (hEacenter s))
  have hAa : ∀ s ∈ Ioo (0:Interval) 1, (a s).val ∈ A.source := by
    intro s hs
    rw [hAs]
    exact ⟨(s,⟨0,by norm_num⟩),⟨hs.1,hs.2,by norm_num,by norm_num⟩,
      congrArg Subtype.val (hEacenter s)⟩
  have haends : (a 0).val ∈ frontier Q ∧ (a 1).val ∈ frontier Q := by
    rw [hfront]
    exact ⟨hends.1,hends.2.1⟩
  have hbends : (b 0).val ∈ frontier Q ∧ (b 1).val ∈ frontier Q := by
    rw [hfront]
    exact ⟨hends.2.2.1,hends.2.2.2⟩
  have hbi : ∀ s ∈ Ioo (0:Interval) 1, (b s).val ∉ frontier Q := by
    intro s hs
    rw [hfront]
    exact (hi s hs).2
  have hlocal := square_obstacle_local_axis Q D a hclear haends.1 haends.2
    P hPs hP A hAa (fun z hz hza => (hAaxis z hz).mp hza)
  have hno (y : ↥Q) (hyB : y ∈ B) (hyend : y ∈ ({b 0,b 1} : Set ↥Q)) :
      y ∉ range a := by
    rintro ⟨s,hs⟩
    by_cases hs0 : s = 0
    · exact Set.disjoint_left.mp hsep
        (hs ▸ (show a s ∈ {a 0,a 1} from Or.inl (congrArg a hs0))) hyend
    by_cases hs1 : s = 1
    · exact Set.disjoint_left.mp hsep
        (hs ▸ (show a s ∈ {a 0,a 1} from Or.inr (congrArg a hs1))) hyend
    exact (hi s ⟨bot_lt_iff_ne_bot.mpr hs0,lt_top_iff_ne_top.mpr hs1⟩).1
      (hs.symm ▸ hyB)
  obtain ⟨C,hC,hCi,hCA⟩ := square_finite_crosscut_from_separated_endpoints Q D hD
    a b hb hbi (hno (b 0) hends.2.2.1 (Or.inl rfl))
    (hno (b 1) hends.2.2.2 (Or.inr rfl)) hcenter hback hopen hlocal
  obtain ⟨q,H,hq,hq0,hq1,hqi,hHF,hmove,hfinite,_⟩ :=
    embedded_square_finite_position_ambient_motion Q a b D hD hcenter hclear hopen C
      hC hCi hCA hb hbends hbi
  refine ⟨q,H,hq,hq0,hq1,?_,?_,hmove,hfinite⟩
  · intro s hs
    change (q s).val ∉ (chartAt Plane x).symm ''
      Metric.sphere ((chartAt Plane x) x) R
    rw [← hfront]
    exact hqi s hs
  · intro t y hy
    exact hHF t y (hfront.symm ▸ hy)

end CoherentEndpointMotion
